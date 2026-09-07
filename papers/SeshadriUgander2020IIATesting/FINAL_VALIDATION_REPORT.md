# Final Validation Report: Fundamental Limits of Testing IIA

Updated: 2026-09-06

## 1. Human Verdict

Formalized. The testing lower bound and selected supporting results are proved
with the source clarifications in Section 4.

## 2. Closeout Status

- Completion status: formalized.
- Scope: five main-text results and six selected appendix results.
- Human review: 0/11 result annotations recorded.

## 3. Source and Scope

The source is Arjun Seshadri and Johan Ugander,
[*Fundamental Limits of Testing the Independence of Irrelevant Alternatives in
Discrete Choice*](https://arxiv.org/abs/2001.07042v1), arXiv:2001.07042v1,
20 January 2020.

The selected results are Theorem 1, Lemmas 2–4, Corollary 1, Appendix Facts 5
and 7, Appendix Lemmas 6, 9–10, and Appendix Corollary 2. Appendix Lemma 8,
the standalone arbitrary-graph result attributed to Chu et al., is excluded
from this formalization. The selected conclusions instead use the paper's
bipartite cycle-decomposition argument.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Lemma 2 | **Exact.** |
| [Theorem 1](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#theorem-1-perturbation-range) | **Source clarification:** `2 mu(sigma) delta <= 1` keeps the proof’s perturbation in its defined range. |
| Lemmas 3–4; Appendix Fact 5; Appendix Lemma 6; Appendix Fact 7; Appendix Lemma 9 | **Exact.** |
| [Corollary 1; Appendix Lemma 10](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#appendix-comparison-incidence-bound) | **Restricted scope:** positive denominator for the rational branch and the valid real-log range. |
| [Appendix Corollary 2](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#all-even-subsets-endpoint) | **Changed statement:** valid range begins at `n=3`, not `n=2`. |

## 5. Remaining Boundaries and Gaps

None on the selected surface. Appendix Lemma 8 is excluded as described in
Section 3.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

Lemma 2 averages test errors over separated components without requiring
their mixture to remain separated. See the [replacement argument and cancellation example](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#lemma-2-mixture-reduction).

The [Le Cam coefficient](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#le-cam-coefficient-in-the-proof-of-theorem-1)
is corrected in Theorem 1's proof; the theorem's coefficient is unchanged.

## 8. Proof Tricks Worth Reusing

- Index observations by literal item/set incidences so balanced signs, graph
  edges, and probability coordinates share one finite carrier.
- Turn an informal alternating-cycle obstruction into a local loss lemma and
  sum it across an explicit edge-disjoint cycle packing.
- Represent independent cycle orientations by finite Boolean functions; this
  makes the Rademacher moment factorization behind Lemma 4 exact.
- Separate the logarithmic short-cycle phase from the complete Eulerian
  residual peeling, then compose their concrete edge-position equivalences.
- Prove finite risk inequalities before rearranging them into exact
  sample-complexity and testing-radius consequences.

## 9. Generalizations, Conjectures, and Extensions

No additional generalization is established here.

## 10. Source Clarifications and Exact Readings

The result table links the perturbation range, comparison-incidence denominator,
and all-even-subsets endpoint clarifications. The mixture and coefficient
proof changes have their main discussion in Section 7.

## 11. Paper Issues or Caveats

None beyond the domain qualifications in Section 10.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) presents 11 selected result claims
as transparent targets, and [ProofInterface.lean](ProofInterface.lean)
supplies one checked endpoint for each. Source definitions are reviewed at
their actual declarations. Appendix Lemma 8 remains a recorded scope exclusion
and receives no endpoint or premise credit.

## 13. Paper Assumption Provenance

[Assumptions.lean](Assumptions.lean) introduces no paper-local axiom. The 19
paper-local prerequisites and 11 reusable-library prerequisites all match
their selected source connections in the
[paper prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) and
[library ledger](FINAL_CLOSURE_RECEIPT.md). The cited Chu et al.
paper supplies context rather than an imported theorem or external proof
boundary.

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) routes the choice-system,
IIA, separation-testing, comparison-graph, cycle-decomposition, and balanced
perturbation definitions and the selected result formulas. Corrected lower
bounds and incidence/decomposition statements are recorded in the
[source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) and explained
in the [source clarification memo](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md).

## 15. Library Lift Pass

Reusable components include finite distributions and product tests,
choice-system distances and IIA projections, graph geodesic trees, bipartite
short-cycle extraction, pruning traces, parity accounting, simple-cycle
packings, and bounded Eulerian peelings. Paper numbering, the statistical
perturbation family, and source-facing theorem bundles remain paper-local.

## 16. DAG Audit

[DependencyDAG.tex](docs/DependencyDAG.tex) places source models and Appendix
support before the main results that consume them, separates main-text and
Appendix rows, and shows the native Appendix Lemma 9-to-Lemma 10 route. The
rendered [DependencyDAG.pdf](docs/DependencyDAG.pdf) was visually inspected;
labels, arrowheads, and the scope-exclusion note are legible, with no clipping
or overlap obscuring a dependency edge.

## 17. Validation Checks

The [focused-build receipt](FINAL_CLOSURE_RECEIPT.md) records a passing
proof-interface build. The [import-closure receipt](FINAL_CLOSURE_RECEIPT.md)
and [final closure receipt](FINAL_CLOSURE_RECEIPT.md) record the checked Lean
closure and terminal obligation graph.

## 18. Paper Definitions Checked

The checked definitions are the choice-system model, IIA model,
separation-testing model, comparison-graph Eulerian model,
cycle-decomposition model, and balanced perturbation model. Exact declaration
bodies and source routes appear in the
[statement map](audit/paper_statement_map.json) and prerequisite ledgers.

## 19. Named Theorem Statements Checked

| Source item | Transparent semantic target | Checked proof endpoint |
| --- | --- | --- |
| Lemma 2 | `lemma2_testing_reductionSpec` | `lemma2_testing_reduction` |
| Lemma 3 | `lemma3_chiSquare_mixtureSpec` | `lemma3_chiSquare_mixture` |
| Lemma 4 | `lemma4_cycle_chiSquareSpec` | `lemma4_cycle_chiSquare` |
| Theorem 1 | `theorem1_testing_lower_boundSpec` | `theorem1_testing_lower_bound` |
| Corollary 1 | `corollary1_global_lower_bound_correctedSpec` | `corollary1_global_lower_bound_corrected` |
| Fact 5 | `fact_convex_hull_denseSpec` | `fact_convex_hull_dense` |
| Lemma 6 | `lemma_iia_projection_invarianceSpec` | `lemma_iia_projection_invariance` |
| Fact 7 | `fact_entropy_cross_entropySpec` | `fact_entropy_cross_entropy` |
| Lemma 9 | `lemma_bipartite_cycle_decompositionSpec` | `lemma_bipartite_cycle_decomposition` |
| Lemma 10 | `lemma_comparison_incidence_decomposition_correctedSpec` | `lemma_comparison_incidence_decomposition_corrected` |
| Corollary 2 | `corollary_all_even_subsets_correctedSpec` | `corollary_all_even_subsets_corrected` |

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) contains
11 current judgments: seven matches and four corrected-target
matches. The [human review packet](docs/HUMAN_REVIEW_PACKET.pdf) is the
corresponding reader-facing surface.

## 21. Source-Coverage Audit Ledger

The [coverage ledger](FINAL_CLOSURE_RECEIPT.md) contains 18 items: 13
covered, four covered as corrected targets, and one scope exclusion for
Appendix Lemma 8. The [statement map](audit/paper_statement_map.json) records
the source locations and routes for all 18 presentations.
