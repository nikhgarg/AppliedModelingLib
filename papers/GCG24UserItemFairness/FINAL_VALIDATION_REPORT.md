# Final Validation Report: User-item fairness tradeoffs in recommendations
Updated: 2026-09-08

## 1. Human Verdict

The formalization covers the named fairness tradeoff results and their Appendix D/E optimization arguments. With two opposing utility types, item fairness is least costly at a balanced population. Preference misestimation can be much more costly when full item fairness is imposed.

## 2. Closeout Status

- Completion status: `formalized`.
- Scope: the paper's named theoretical results, including Appendix D/E.
- Human review: not yet recorded.

## 3. Source and Scope

The source is [*User-Item Fairness Tradeoffs in Recommendations*
](https://openreview.net/pdf?id=ZOZjMs3JTs). The formalized surface is its
named definitions, lemmas, propositions, and theorems, including Appendix D/E.
Example 1 and the paper's empirical methods are outside this named-theory
surface and are not counted as formalized results.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Propositions 1--2 | **Exact.** |
| Theorem 3 | **Exact.** |
| [Theorem 4](docs/SOURCE_CLARIFICATIONS.md#theorem-4-population-masses-and-positive-tolerance-section-5-p-7-appendix-e-p-39) | **Exact after correcting the mass typo:** cold-start mass `1-beta` becomes `1-2 beta`, alongside two masses `beta`. |
| Appendix C Lemmas 1--2 | **Exact.** |
| Appendix D Lemmas 3--11 | **Exact.** |
| Appendix E Lemmas 12--14 and 16--17 | **Exact.** |
| [Appendix E Lemma 15](docs/APPENDIX_E_LEMMA15_SOURCE_NOTE.md#appendix-e-lemma-15-source-clarification) | **Exact after correcting the branch typo:** the center branch includes both mirrored known types, giving `lambda=1/(1+L_t)`. |

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

None.

## 9. Generalizations, Conjectures, and Extensions

No additional generalization is established here.

## 10. Source Clarifications and Exact Readings

Theorem 4's cold-start population mass changes from `1-beta` to `1-2 beta` so the three masses sum to one. Appendix E Lemma 15's center equation includes both mirrored types, giving `lambda=1/(1+L_t)`. See the [population note](docs/SOURCE_CLARIFICATIONS.md#theorem-4-population-masses-and-positive-tolerance-section-5-p-7-appendix-e-p-39) and [center-equation note](docs/APPENDIX_E_LEMMA15_SOURCE_NOTE.md#appendix-e-lemma-15-source-clarification).

## 11. Paper Issues or Caveats

None.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) contains 23 transparent
paper-facing result specifications, and [ProofInterface.lean](ProofInterface.lean)
supplies the corresponding checked endpoints. The main-text surface comprises
Propositions 1--2 and both clauses of Theorems 3--4; the remaining
specifications cover Appendix C Lemmas 1--2, Appendix D Lemmas 3--11, and
Appendix E Lemmas 12--17. The [final closure receipt](FINAL_CLOSURE_RECEIPT.md)
points to the accepted obligation graph.

## 13. Paper Assumption Provenance

[status.json](status.json) lists 12 source-condition declarations.
The [assumption ledger](FINAL_CLOSURE_RECEIPT.md) records 11 standalone
premise declarations as paper conditions. The twelfth,
`assumption_theorem4_universal_value_vector`, is an existential value-vector
property inside the Theorem 4 conclusion rather than a separate theorem
premise; its source route is recorded in the
[statement map](audit/paper_statement_map.json). The 25 paper-local model and
definition prerequisites all match their selected source connections in the
[prerequisite ledger](FINAL_CLOSURE_RECEIPT.md).

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) routes the displayed
recommendation, fairness, optimization, and misestimation formulas. Theorem 4's
normalized population uses masses `beta`, `beta`, and `1-2 beta`; Appendix
E Lemma 15 uses the corrected center value `lambda=1/(1+L_t)`. The exact
source comparisons are documented in the
[source clarification memo](docs/SOURCE_CLARIFICATIONS.md), the
[Lemma 15 note](docs/APPENDIX_E_LEMMA15_SOURCE_NOTE.md#appendix-e-lemma-15-source-clarification), and the
[source-fidelity ledger](FINAL_CLOSURE_RECEIPT.md).

## 15. Library Lift Pass

The [library semantic ledger](FINAL_CLOSURE_RECEIPT.md) selects no
material reusable-library prerequisite. Recommendation policies, fairness
objectives, symmetric reductions, and misestimation constructions remain
paper-local.

## 16. DAG Audit

The one-page [DependencyDAG.pdf](docs/DependencyDAG.pdf), generated from
[DependencyDAG.tex](docs/DependencyDAG.tex), was visually inspected at 144 dpi
on 2026-09-05. Its legend, nodes, labels, and directed edges are readable, with
no visible clipping or overlap. The dashed Example 1 node is an unformalized
illustration; the displayed result chains reach Theorems 3 and 4.

## 17. Validation Checks

The [focused-build receipt](FINAL_CLOSURE_RECEIPT.md) records a passing
paper build. The [import-closure receipt](FINAL_CLOSURE_RECEIPT.md)
records the checked Lean import surface, and the
[final closure receipt](FINAL_CLOSURE_RECEIPT.md) points to the accepted
obligation graph.

## 18. Paper Definitions Checked

The reviewed model surface covers recommendation utility, user and item
fairness, the price of fairness, the price of misestimation, the symmetric
optimization reductions, the opposing two-type model, and the true and
estimated three-type models used for Theorem 4. Exact declaration bodies and
source routes are recorded in the [statement map](audit/paper_statement_map.json)
and [prerequisite ledger](FINAL_CLOSURE_RECEIPT.md).

## 19. Named Theorem Statements Checked

- Propositions 1--2: symmetric linear-program reduction and existence of a
  symmetric optimum.
- Theorem 3: the price of item fairness decreases toward a balanced
  two-type population and increases away from it.
- Theorem 4: the universal no-fairness misestimation bound and the
  high-item-fairness tradeoff construction.
- Appendix C Lemmas 1--2, Appendix D Lemmas 3--11, and Appendix E Lemmas
  12--17: the supporting optimization statements summarized in Section 4.

Each item has a transparent specification in [PaperInterface.lean](PaperInterface.lean)
and a checked endpoint in [ProofInterface.lean](ProofInterface.lean).

## 20. Paper-Facing Statement Validator Ledger

The [current source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md)
contains 23 judgments: 22 matches and one corrected-target match for
Appendix E Lemma 15. [status.json](status.json) separately records that human
review remains 0 of 23 rows.

## 21. Source-Coverage Audit Ledger

The [coverage ledger](FINAL_CLOSURE_RECEIPT.md) contains 27 inventoried
named-theory items: 26 covered and one covered as a corrected target. The
corrected item is Appendix E Lemma 15; its counterexample support is recorded
in the [defect-support ledger](FINAL_CLOSURE_RECEIPT.md) and the
[Lemma 15 note](docs/APPENDIX_E_LEMMA15_SOURCE_NOTE.md#appendix-e-lemma-15-source-clarification). The complete source
inventory and route assignments are in the
[statement map](audit/paper_statement_map.json).
