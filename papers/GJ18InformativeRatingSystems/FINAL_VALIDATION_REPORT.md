# Final Validation Report: GJ18 Informative Rating Systems
Updated: 2026-09-06

## 1. Human Verdict

Formalized. The checked finite ordinal model covers score separation,
convergence, and Theorem 1's exponential ranking-error rate. Independent human
review has not yet been recorded.

## 2. Closeout Status

- Completion status: formalized.
- Normal scope: the finite ordinal model, pairwise and uniform-ranking
  objectives, convergence results, and Theorem 1's rate.
- Human review: independent sign-off has not yet been recorded.

## 3. Source and Scope

The source is Garg and Johari, *Designing Informative Rating Systems: Evidence
from an Online Labor Market*. The governing target is a finite
ordinal model with independent rating draws conditional on seller quality and
independent seller histories. The source's quality-only rating law and
pairwise-probability factorization support this reading. The public archival source is the [published article](https://doi.org/10.1287/msom.2020.0921).

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Theorem 1; Appendix Lemmas 1–2 | **Source clarifications:** [adjacent-pair indices and strict tails above the lowest rating](docs/GOVERNING_MODEL_CLARIFICATION.md#theorem-1-reading); [aggregate index](docs/GOVERNING_MODEL_CLARIFICATION.md#displayed-indices-and-finite-state-route). **Formalization gap:** connection to the [population recurrence](docs/GOVERNING_MODEL_CLARIFICATION.md#population-state-boundary). |
| Pairwise and uniform-ranking objectives | **Exact.** |

## 5. Remaining Boundaries and Gaps

Theorem 1 uses the declared iid rating model. Its connection to the printed
population-state recurrence remains unproved; see the
[model boundary](docs/GOVERNING_MODEL_CLARIFICATION.md#population-state-boundary).

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

The Appendix transfer uses a finite-support argument in the governing model
of Section 3. The variational calculation keeps extended-real intermediate
costs and proves finiteness at the final theorem boundary; see the
[governing-model clarification](docs/GOVERNING_MODEL_CLARIFICATION.md).

## 8. Proof Tricks Worth Reusing

For finite ordinal models, prove score separation by selecting actual support
endpoints rather than manufacturing terminal full support. Keep large-deviation
objects extended-real through minimization, then prove a finite representative
only at the final theorem boundary. Make joint-law completion a visible model
field, not an inference from a suggestive recurrence name.

## 9. Generalizations, Conjectures, and Extensions

Connecting the declared iid law to the population recurrence is deferred;
see Section 5.

## 10. Source Clarifications and Exact Readings

The [governing-model clarification](docs/GOVERNING_MODEL_CLARIFICATION.md)
gives the aggregate and adjacent-pair index fixes and restricts strict
cross-quality tail comparisons to ratings above the lowest level. It also
states the source’s [positive-sampling and independence readings](docs/GOVERNING_MODEL_CLARIFICATION.md#model-readings).

## 11. Paper Issues or Caveats

Section 10 links the local notation corrections; Section 7 describes the proof deviation.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) exposes the finite ordinal model,
score formulas, iid bridges, Appendix rate lemmas, convergence claims, and the
corrected finite-real Theorem 1 target. [ProofInterface.lean](ProofInterface.lean)
contains the paired checked endpoints. The governing iid completion is a
visible model input rather than an opaque product-law certificate.

## 13. Paper Assumption Provenance

Conditional iid ratings, independent seller histories, and positive sampling
rates express the source model and its asymptotic proof conventions. Three paper-local prerequisites
and five reused-library prerequisites have current matching judgments in the
[paper](FINAL_CLOSURE_RECEIPT.md) and
[library](FINAL_CLOSURE_RECEIPT.md) ledgers.

## 14. Displayed Formula Provenance

[The source map](audit/paper_statement_map.json) records the floor sample
count, corrected aggregate score, pairwise and uniform-ranking objectives,
uniform normalization, log-mgf, real and extended rate functions, Appendix
rates, and Theorem 1. The [governing-model memo](docs/GOVERNING_MODEL_CLARIFICATION.md)
explains the exact index and codomain corrections.

## 15. Library Lift Pass

Reusable finite-probability, ordinal-score, large-deviation, and finite-support
lemmas remain separate from the paper's horizon law and rating-system
objectives. The paper namespace retains source numbering and the corrected
model assembly.

## 16. DAG Audit

[The dependency DAG](docs/DependencyDAG.pdf) connects the finite model and
formula definitions through the Appendix rate results to Theorem 1. Its
retained 2026-09-04 visual inspection found the legend, labels, and directed
edges readable with no clipping or overlap.

## 17. Validation Checks

The current accepted graph binds three direct corrected-target judgments,
three matching paper prerequisites, and five matching library prerequisites.
The broader statement ledger records the checked formula and bridge rows. See
the [accepted graph](audit/obligation_evidence/current_accepted_graph.json) and
[closure receipt](FINAL_CLOSURE_RECEIPT.md). No new build or semantic review
was run for this document edit.

## 18. Paper Definitions Checked

Checked definitions include floor-counted seller histories, aggregate scores,
adjacent-pair and uniform-ranking objectives, the finite ordinal iid state law,
log moment-generating functions, and real/extended large-deviation rates.

## 19. Named Theorem Statements Checked

- Appendix Lemmas 1–2, the score-gap and complement-rate statements, are proved in the
  clarified iid model.
- Pairwise and uniform-ranking objectives converge to one under the stated
  separation conditions.
- The corrected finite-real Theorem 1 rate is proved with extended-real
  intermediate costs and a finite representative at the endpoint.

## 20. Paper-Facing Statement Validator Ledger

Direct corrected-target judgments are recorded in the
[source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md); the full
formula/bridge comparisons are in the
[statement ledger](FINAL_CLOSURE_RECEIPT.md), and correction provenance
is in the [source-fidelity ledger](FINAL_CLOSURE_RECEIPT.md).

## 21. Source-Coverage Audit Ledger

[The source map](audit/paper_statement_map.json) inventories the model,
formulas, Appendix claims, convergence statements, and Theorem 1. The
[coverage record](FINAL_CLOSURE_RECEIPT.md) binds the corrected model and
rate items to their reader-visible explanations. The accepted graph is the
current credential for the selected corrected surface.
