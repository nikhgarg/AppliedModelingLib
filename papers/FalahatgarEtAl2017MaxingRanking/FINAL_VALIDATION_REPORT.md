# Final Validation Report: Maxing and Ranking with Few Assumptions

Updated: 2026-09-08

## 1. Human Verdict

The checked results cover maximum finding and ranking. Main Lemma 5, Theorem 6, and Supplemental Lemmas 15 and 17 formalize Algorithm 2's printed squared-log guard. The source output-size typo is recorded in Section 10.

## 2. Closeout Status

- Completion status: formalized.
- Human review: no annotations recorded.

## 3. Source and Scope

The authority is the NeurIPS 2017 paper *Maxing and Ranking with Few
Assumptions* by Moein Falahatgar, Yi Hao, Alon Orlitsky, Venkatadheeraj
Pichapati, and Vaishakh Ravindrakumar, together with its official supplement.
The complete 19-page official supplemental PDF contains the published main
paper followed by the appendices and is the canonical local source artifact.
Its retained text transcript has SHA-256
`22407a45267c62e11b46ea3a6c7c392099d91dae0c469274936b6a3461c59e09`;
the PDF has SHA-256
`b427a26a6cc1af082ce8b02c6f1dc6194329235b483b4542408788f33745a537`.

The mathematical inventory has 38 items:

- six source model/definition presentations;
- Algorithms 1--9; and
- 23 result presentations: the finite-SST existence claim, Main Lemma 1,
  Theorems 2, 6--9, Lemmas 3 and 5, Remark 4, Supplement Lemmas 10--21,
  and Supplement Theorem 22.

Main Theorem 9 and Supplement Theorem 22 display the same complete Borda-ranking
proposition. They remain separate transparent review rows because the source
does not explicitly call Theorem 22 a restatement. Proof-support declarations
remain outside the selected-result denominator. All 23 result presentations are
selected; Algorithms 2 and 3 are included as source-model rows.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Finite SST existence; Lemmas 1 and 3; Remark 4; Theorems 2 and 7–9; Supplemental Theorem 22 | **Exact.** |
| [Main Lemma 5; Supplemental Lemma 15](docs/SOURCE_CLARIFICATIONS.md#prune-output-size) | **Exact after correcting the endpoint typo:** output size `< 2n'` → `<= 2n'`. |
| Theorem 6; Supplemental Lemma 17 | **Exact.** |
| [Algorithm 7; Lemmas 19–20](docs/SOURCE_CLARIFICATIONS.md#algorithm-7-complementary-estimates-and-threshold) | **Exact after correcting typos:** complementary reverse estimate and `epsilon/2` threshold; the epsilon-ranking conclusion is unchanged. |
| Supplemental Lemmas 10–14, 16, 18, and 21 | **Exact.** |

## 5. Remaining Boundaries and Gaps

None.

Theorem 8
uses the cited PAC best-arm policy of Yuan Zhou, Xi Chen, and Jian Li,
*Optimal PAC Multiple Arm Identification with Applications to Crowdsourcing*
(ICML 2014). That result is proved natively in this repository and then applied
as a proved dependency. The Falahatgar paper-local bridge proves equality of
the full finite experiment laws and transfers both success and execution cost;
the cited theorem is neither an axiom nor an external proof boundary.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

- The finite SST ranking existence proof uses merge sorting in place of the source's induction sketch.
- Algorithm 7 uses complementary empirical estimates and the proof's `epsilon/2` margin; see the [algorithm note](docs/SOURCE_CLARIFICATIONS.md#algorithm-7-complementary-estimates-and-threshold).

## 8. Proof Tricks Worth Reusing

- Derive finite weak-order witnesses once, then keep them internal to the proof
  when the paper does not list them as theorem premises.
- Model adaptive comparison algorithms by fresh finite laws selected from the
  realized history, avoiding simultaneous certificates over unqueried pairs.
- Couple stopped algorithms and their resource trace in one finite PMF so that
  correctness and cost hold on the same high-probability event.
- For reductions to bandit algorithms, prove equality of full finite laws and
  lift it through adaptive histories rather than transferring only means.

## 9. Generalizations, Conjectures, and Extensions

The finite SST maximum/ranking bridge and the uniform-opponent Borda-bandit law
equivalence are reusable beyond this paper. The current extraction keeps the
paper-specific algorithms, thresholds, and source-rate arithmetic local while
using shared finite probability and PAC interfaces as mathematical
infrastructure.

## 10. Source Clarifications and Exact Readings

Prune permits output size exactly `2n'`. The [clarification memo](docs/SOURCE_CLARIFICATIONS.md) records this source typo and Algorithm 7's display corrections.

## 11. Paper Issues or Caveats

None.

## 12. Detailed Formalization Evidence

**Prune cardinality typo.** Main Lemma 5 and Supplement Lemma 15 say that the
output size is less than `2n'`. Section 3.2.2, Algorithm 2's stopping rule,
and Appendix Lemma 14 all use at most `2n'`; the algorithm can stop at
equality.

[PaperInterface.lean](PaperInterface.lean) retains 23 transparent result
specifications with paired endpoints in [ProofInterface.lean](ProofInterface.lean).
The [statement map](audit/paper_statement_map.json) selects all 23 result routes
and fifteen source-model rows.

## 13. Paper Assumption Provenance

The paper-facing interface has no standalone assumption declaration. Its source
conditions appear directly in the transparent specifications. The current
[prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) reuses all
twenty-two unchanged paper-prerequisite judgments against the scoped successor
graph. No library-prerequisite judgment is required.

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) records six
model/definition presentations, Algorithms 1--9, and all result presentations
with exact source anchors.
The current [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md)
records all 23 selected result judgments.

## 15. Library Lift Pass

The formalization reuses shared finite-PMF, concentration, adaptive-policy,
and approximate-preference interfaces. Paper-specific comparison laws,
algorithms, and numbered results remain paper-local. The imported
Zhou--Chen--Li best-arm dependency is separately attributed and proved rather
than treated as a paper assumption.

## 16. DAG Audit

[DependencyDAG.tex](docs/DependencyDAG.tex) and
[DependencyDAG.pdf](docs/DependencyDAG.pdf) display the complete source-shaped
result surface: finite SST existence; Compare and Lemmas 10--12; Theorem 2;
Pick-Anchor, Lemma 3, and Remark 4; Prune, Lemmas 13--15, and Main Lemma 5;
Lemmas 16--18 and Theorem 6; Theorem 7; Lemmas 19--20; and the Borda chain
through Lemma 21, Theorems 8--9, and Theorem 22. The Prune and OPT-Maximize
routes are source-routed. The current one-page rendering has
readable labels and arrows and no page clipping.

## 17. Validation Checks

The focused source-schedule and proof-interface builds pass. The semantic
ledgers, DAG, and human review packet cover the source-routed result surface.

## 18. Paper Definitions Checked

The source-routed definitions cover the finite no-draw comparison model; exact
and approximate preference, maximum, and ranking predicates; strong stochastic
transitivity; Borda scores and approximation objectives; the good-anchor
predicate; and Algorithms 1--9. The selected routes are in the
[statement map](audit/paper_statement_map.json).

## 19. Named Theorem Statements Checked

Twenty-three result specifications are selected across the main-paper and
supplement result chain. Multi-part
results retain their correctness and sample-complexity conclusions in the same
source-presentation-shaped target. The exact pairings are in
[PaperInterface.lean](PaperInterface.lean) and
[ProofInterface.lean](ProofInterface.lean).

## 20. Paper-Facing Statement Validator Ledger

The current [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md)
and [human review packet](docs/HUMAN_REVIEW_PACKET.pdf) describe the 23
selected results and their governing prerequisites. The packet is projected
from the scoped successor graph.

## 21. Source-Coverage Audit Ledger

The [statement map](audit/paper_statement_map.json) retains all 38 source
presentations: 23 selected result routes and fifteen source-model rows. No separate
`audit/paper_coverage_llm.json` is present.
