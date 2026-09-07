# Final Validation Report: Axioms for Learning from Pairwise Comparisons

Updated: 2026-08-26

## 1. Human Verdict

Formalized. The review surface covers every numbered definition, lemma, and
theorem in the NeurIPS 2020 main paper and both named claims in its official
supplement. All fourteen source presentations have transparent source-facing
Lean statements. The ten result claims have checked proof endpoints; the four
numbered definitions are reviewed directly as semantic declarations.

The formalization covers the finite pairwise-count likelihood model, MLE
existence and uniqueness, Pareto efficiency, monotonicity, the impossibility of
pairwise-majority consistency, and the impossibility of separability.

## 2. Closeout Status

- Completion status: formalized.
- Direct source-to-Spec review surface: ten results: four main-text lemmas,
  four main-text theorems, and two supplementary claims. Four definitions
  are reviewed separately as semantic prerequisites.
- Material paper-local and reusable-library definitions are reviewed under the
  same source-match standard; their exact declarations are recorded in
  `audit/library_semantic_review.json` by terminal closeout.
- Human review status: 0/10 result annotations recorded. Human review is
  encouraged but is not a release blocker and is never inferred from agent or
  machine checks.
- `FINAL_CLOSURE_RECEIPT.md` is the canonical machine closeout record after the
  terminal closeout transaction; this report is the researcher-facing summary.

## 3. Source and Scope

The source is Ritesh Noothigattu, Dominik Peters, and Ariel D. Procaccia,
[*Axioms for Learning from Pairwise Comparisons*](https://proceedings.neurips.cc/paper_files/paper/2020/hash/cdaa9b682e10c291d3bbadca4c96f5de-Abstract.html),
NeurIPS 2020.

The audit uses a combined copy of the official proceedings paper and official
supplement (SHA-256
`cbf69fcb0860f292056e7c8c3f1b7813b048877924ae6b6c037e84292d733163`)
and its byte-pinned layout-preserving transcript. The source-only inventory
independently reconciles Lemmas 2.1--2.4; Definitions 3.1, 4.1, 5.1, and 6.1;
Theorems 3.2, 4.2, 5.3, and 6.3; and supplementary Claims A.1 and C.1.

Exact source spans, semantic context, and proof routes are in
`audit/paper_statement_map.json`. Source-facing Lean statements are in
`PaperInterface.lean`; paired proof endpoints are in `ProofInterface.lean`.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Lemma 2.1 | **Exact.** |
| Lemma 2.2 | **Exact.** |
| Lemma 2.3 | **Quantifier corrected:** positive directed counts only between distinct alternatives; the source sup-norm bound follows. [Correction](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#lemma-23-distinct-alternatives). |
| Lemma 2.4 | **Exact.** |
| Definitions 3.1, 4.1; Theorems 3.2, 4.2 | **Exact.** |
| Definition 5.1; Theorem 5.3 | **Exact.** |
| Definition 6.1; Theorem 6.3 | **Exact.** |
| Supplementary Claims A.1 and C.1 | **Exact.** |

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

Theorems 5.3 and 6.3
replace continuity of the maximizer with a compact likelihood gap and an exact
rational perturbation under the source assumptions. [Proof details](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#counterexample-proofs-for-theorems-53-and-63).

## 8. Proof Tricks Worth Reusing

- Normalize one score coordinate while keeping all paper conclusions in
  shift-invariant score differences.
- Represent a source inverse by its unique inverse-image property when only an
  interior value is used.
- Use graph connectivity to turn equality of likelihood terms into equality
  of all normalized score coordinates.
- Replace a qualitative small-perturbation argument by a compact strict-gap
  estimate and exact integer scaling.
- Obtain the loser half of a monotonicity argument through count transposition
  and score negation rather than duplicating the full proof.

## 9. Generalizations, Conjectures, and Extensions

The reusable library now includes finite pairwise-count datasets, comparison
graphs, CDF-like pairwise links, fixed-reference MLEs, perfect-fit distances,
likelihood existence and uniqueness tools, score-exchange lemmas, and exact
counterexample constructions. These components are independent of the paper
namespace and can support later ranking and preference-learning work.

## 10. Source Clarifications and Corrections

Lemma 2.3’s positive-count premise ranges over distinct alternatives because diagonal counts are zero. The [memo](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#lemma-23-distinct-alternatives) gives this local clarification.

## 11. Paper Issues or Caveats

None.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) presents fourteen source items:
four semantic definitions and ten result claims. [ProofInterface.lean](ProofInterface.lean)
supplies one exact-type endpoint for each result; the four definitions remain
direct declarations rather than artificial theorem wrappers.

## 13. Paper Assumption Provenance

`Assumptions.lean` introduces no paper-local axiom. Four graph-selected
paper-model prerequisites have current matching judgments in the
[paper-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md). No
material reusable-library prerequisite is selected.

## 14. Displayed Formula Provenance

[The source map](audit/paper_statement_map.json) binds pairwise counts,
comparison graph, link/CDF likelihood, finite MLE, perfect fit, score bounds,
and the Pareto, monotonicity, majority-consistency, and separability formulas
to their source presentations.

## 15. Library Lift Pass

The reusable library contains the general pairwise-count dataset, graph,
likelihood, link, MLE, perfect-fit, and comparison-axiom machinery. Paper
numbering and explicit counterexample instances remain paper-local.

## 16. DAG Audit

[The dependency DAG](docs/DependencyDAG.pdf) places the model and supplementary
claims before the main results and shows the four axiom results depending on
the finite MLE foundation. The retained visual inspection found readable
labels, correct arrow direction, and no clipping or node overlap.

## 17. Validation Checks

The weak-order PMC definition and its Theorem 5.3 endpoint compile and pass
bounded independent source comparison. Their current closeout evidence is
being synchronized; the retained receipt describes its pinned prior tree.

Retained focused proof-interface and root builds passed. The current graph
records ten matching direct result judgments and four matching paper-model
prerequisites. The [accepted graph](audit/obligation_evidence/current_accepted_graph.json)
and [closure receipt](FINAL_CLOSURE_RECEIPT.md) bind the closeout surface; no
new Lean or semantic review was run for this document edit.

## 18. Paper Definitions Checked

The checked source definitions are the pairwise-comparison/MLE model,
Definition 3.1 Pareto efficiency, Definition 4.1 monotonicity, Definition 5.1
pairwise-majority consistency, and Definition 6.1 separability.

## 19. Named Theorem Statements Checked

- Lemmas 2.1--2.4: MLE existence, one-neighbor perfect fit, sup-norm control,
  strict concavity, and uniqueness.
- Theorems 3.2, 4.2, 5.3, and 6.3: Pareto and monotonicity guarantees and finite
  violations of majority consistency and separability.
- Supplementary Claims A.1 and C.1: coin-flip likelihood and the strict
  crossed-product inequality.

## 20. Paper-Facing Statement Validator Ledger

The ten direct comparisons are in the
[source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md); model
premises are in the [paper-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md),
and [source-proof fidelity](FINAL_CLOSURE_RECEIPT.md) records the
counterexample proof replacement.

## 21. Source-Coverage Audit Ledger

[The source map](audit/paper_statement_map.json) inventories all fourteen
named source presentations. The ten result rows have current matching direct
judgments, and the four definition rows are covered as semantic model
prerequisites. The accepted graph binds both groups without counting the
definitions as extra theorem claims.
