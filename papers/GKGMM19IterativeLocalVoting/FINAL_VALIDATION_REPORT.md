# Final Validation Report: Iterative Local Voting for Collective Decision-making in Continuous Spaces
Updated: 2026-09-06

## 1. Human Verdict

Theorem 1's six cases, Theorem 2, and Proposition 1 are proved.

Theorem 3 is proved as a constrained alternative in general and as the
original statement under the explicit full-space condition.
[Clarification](docs/SOURCE_CLARIFICATIONS.md#theorem-3s-full-space-and-projected-readings).

## 2. Closeout Status
- Completion status: formalized.
- Mathematical proof surface: the ILV definitions; finite C1--C3 executions
  for Theorem 1 and finite-exponent Model B Theorem 2; concrete Definition 2
  joint-law Model A and Model B Proposition 1 executions; Proposition 2's
  coordinatewise median result; and both Theorem 3 endpoints.
- Proposition 1's Model A response is an explicit Borel weighted
  water-filling rule, proved to be an exact raw local maximizer. Specializing
  this joint-law theorem to a particular population is ordinary source-model
  instantiation, not an open selection or convergence premise.
- Source clarification: for Proposition 2, Model B means moving every active
  coordinate toward its ideal by the full coordinatewise `L∞` radius, as in
  the proposition's proof.
- Theorem 3: the checked zero-field conclusion uses an explicit full-space
  condition; projection onto a constrained set gives the stated alternative.
- Human review: independent sign-off has not yet been recorded.

## 3. Source and Scope
The source is Garg, Kamble, Goel, Marn, and Munagala, *Iterative Local Voting
for Collective Decision-making in Continuous Spaces*, JAIR 2019. The public
source is [the JAIR article](https://www.jair.org/index.php/jair/article/view/11358).
The checked probabilistic results concern finite-coordinate iid realizations
of the paper's models.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| [Theorem 1](docs/SOURCE_CLARIFICATIONS.md#appendix-c4-lemma-2-the-infinity-one-case) | **Exact:** all six norm/model cases; the `(infinity,1)` heading and exceptional event are corrected without changing the conclusion. |
| Theorem 2 | **Exact.** |
| [Proposition 1](docs/SOURCE_CLARIFICATIONS.md#proposition-1-and-appendix-c6-lemma-4) | **Exact:** convergence to the population minimizer set; the proof replaces an invalid ball identity by coordinate slabs. |
| [Proposition 2, Model B](docs/SOURCE_CLARIFICATIONS.md#proposition-2s-coordinatewise-model-b) | **Source clarification:** use the proof's coordinatewise response rule. |
| [Proposition 2, both models](docs/SOURCE_CLARIFICATIONS.md#proposition-2s-coordinatewise-model-b) | **Current proof restriction:** closure under one-coordinate replacement. It is stronger than C1; the broader convex-domain claim remains unproved, and necessity is unknown. |
| [Theorem 3](docs/SOURCE_CLARIFICATIONS.md#theorem-3s-full-space-and-projected-readings) | **Source clarification:** on a constrained space, the conclusion is zero field or no feasible aggregate direction. When every aggregate direction is feasible, this gives the printed zero-field conclusion. |
| [Appendix Theorem 5](docs/SOURCE_CLARIFICATIONS.md#definition-2-weights-and-appendix-theorem-5-bias) | **Formalization gap:** deterministic summable bias is proved; the source’s adapted random-bias statement remains unproved. The zero-bias main-text applications are covered. |
| Appendix Lemmas 1–4; Theorem 4 | **Exact.** |

## 5. Remaining Boundaries and Gaps

Proposition 2 beyond coordinate-replacement-closed sets remains unproved.

Appendix Theorem 5 is proved only for deterministic summable bias; the adapted random-bias statement is missing source coverage. This does not affect the zero-bias main-text executions.

## 6. Additional Assumptions Beyond Paper

Proposition 2 assumes a feasible set closed under one-coordinate replacement.
This geometric property is stronger
than C1's nonempty bounded closed convex domain. Its necessity for the
paper's claim is unresolved.

[The source clarification memo](docs/SOURCE_CLARIFICATIONS.md)
explains these distinctions and the deterministic-bias Appendix specialization.

## 7. Proof-Strategy Deviations
Appendix C.6 Lemma 4 identifies a block-crossing event with a full-vector
Euclidean ball, which is not valid with more than one coordinate block. The
needed linear-in-radius estimate instead follows from containment in a finite
union of coordinate slabs. C1 bounds the support and C3 bounds the density, supplying the required
linear-in-radius probability estimate and preserving Proposition 1; see the
[event correction](docs/SOURCE_CLARIFICATIONS.md#proposition-1-and-appendix-c6-lemma-4).

The `(infinity,1)` Model A appendix argument uses the corrected
crossing-or-near-tie exceptional event. Appendix Theorem 5 is used in its
set-valued minimizer form where uniqueness is unavailable. These changes
preserve the supported main-text branches.

## 8. Proof Tricks Worth Reusing
None.

## 9. Generalizations, Conjectures, and Extensions

A literal normalized-gradient Model B step under an L-infinity neighborhood can converge to a weighted median, rather than the ordinary median. The proof’s coordinatewise rule is the source clarification in Section 10. The unproved adapted-bias statement is a source coverage gap listed in Section 5.

## 10. Source Clarifications and Exact Readings

[The source clarifications](docs/SOURCE_CLARIFICATIONS.md) give the source
passages and exact mathematical changes. Theorem 3 distinguishes a constrained
space's projected conclusion from the full-space zero-field conclusion.
The memo also specifies the
[zero-gradient convention](docs/SOURCE_CLARIFICATIONS.md#algorithm-1s-query-and-projection).
Proposition 2's extra geometric condition is in Section 6; the Appendix C.6
event repair is in Section 7; the deterministic-bias specialization is in Section 5.

## 11. Paper Issues or Caveats

The statement scopes and proof replacements have their respective explanations in Sections 6, 7, and 9; the memo linked in Section 10 supplies the details.

## 12. Detailed Formalization Evidence

The review surface contains 11 source-claim specifications and one separately
tracked source condition. Each claim is displayed from its expanded semantic
`Spec` and is paired with a Lean-checked proof endpoint. The
[human review packet](docs/HUMAN_REVIEW_PACKET.pdf) presents the same surface
in dependency order. The interactive dashboard is an optional alternative to
reviewing the PDF.

The exact source anchors, semantic routes, Proposition 2 model convention, and
proof endpoints are recorded in the
[paper statement map](audit/paper_statement_map.json) and
[source-proof fidelity ledger](FINAL_CLOSURE_RECEIPT.md).

## 13. Paper Assumption Provenance

The only paper-facing assumption declaration is the bundled C1--C3 source
condition: the solution space is nonempty, bounded, closed, and convex; voters
have unique ideal points; and ideal points are independently sampled from a
distribution with bounded measurable density. The explicit statement scopes
in Section 6 remain visible independently of this bundled declaration. The
proved deterministic-bias specialization of Appendix Theorem 5 suffices for
the zero-bias main-text executions; its broader adapted-bias statement is not
claimed here.

## 14. Displayed Formula Provenance

The checked formulas include Algorithm 1's radius, neighborhood, projection,
update, and stopping rules; the Model A and Model B response rules; Definitions
1--3; the finite Holder-dual calculation used by Lemma 3; and the displayed
conditions and conclusions of the selected main-text and appendix results.
Their byte-pinned source locations and expanded Lean targets are recorded in
the [paper statement map](audit/paper_statement_map.json).

## 15. Library Lift Pass

The stochastic-convergence and finite-dimensional analytic components use
reusable EconCSLib and Mathlib declarations. Material library prerequisites
are expanded and source-reviewed under the same semantic standard as
paper-local declarations. The recursive premise audit reports no unresolved
certificate, replay, process, or broad-package boundary on the 11 selected
source claims.

## 16. DAG Audit

- Source: [DependencyDAG.tex](docs/DependencyDAG.tex)
- Rendered artifact: [DependencyDAG.pdf](docs/DependencyDAG.pdf)
- Visual inspection: the rendered one-page DAG was inspected on 2026-08-28;
  the formalized status, Proposition 1 closure, clarified Proposition 2 branch,
  and two Theorem 3 endpoints are legible, and node
  labels and arrows do not overlap.

## 17. Validation Checks

The closeout validation command set is:

```text
lake build GKGMM19IterativeLocalVoting.PaperInterface
lake build GKGMM19IterativeLocalVoting
python3 scripts/audit_repository.py --paper GKGMM19IterativeLocalVoting
python3 scripts/run_paper_closeout.py --paper GKGMM19IterativeLocalVoting --new-run
```

The focused `PaperInterface` build and the paper-root build pass. The canonical
closeout receipt records the exact repository audit, semantic receipts,
dependency closure, and clean-tree build used for release acceptance.

## 18. Paper Definitions Checked

- C1--C3 and the Algorithm 1 execution model.
- Algorithm 1 radius, neighborhood, projection, update, and stop condition.
- Model A and finite-coordinate Model B response rules.
- Definition 1 `L^p`-normed utilities, Definition 2 weighted Euclidean
  utilities, Definition 3 decomposable utilities, and Definition 4's
  directional local collective-decision condition.

## 19. Named Theorem Statements Checked

- Lemma 3: the finite-dimensional Holder-dual gradient-candidate norm formula.
- Proposition 1: concrete Definition 2 Model A and Model B convergence.
- Proposition 2: Model A and the proof's coordinatewise-boundary Model B
  process converge to the coordinatewise median set.
- Appendix Lemmas 1, 2, and 4 and Appendix Theorems 4 and 5.
- Theorem 1: all six finite-coordinate norm/model cases.
- Theorem 2: finite-exponent Model B Holder-dual cases.
- Theorem 3: the sampled projected source package, with the printed conclusion
  under the explicit full-space condition.

## 20. Paper-Facing Statement Validator Ledger

The source-to-Lean judgments are recorded in
[statement_match_llm.json](FINAL_CLOSURE_RECEIPT.md), and the source
inventory coverage judgments are recorded in
[paper_coverage_llm.json](FINAL_CLOSURE_RECEIPT.md). Human annotations are
kept separate and are not auto-closed by machine validation.

## 21. Source-Coverage Audit Ledger

The complete source inventory is recorded in
[paper_statement_map.json](audit/paper_statement_map.json). The human review
denominator is the 11 selected source-claim `Spec` rows plus the separately
tracked C1--C3 condition; repeated appendix presentations and internal proof
support do not create duplicate human-review claims. Every selected claim has
an exact byte-pinned source anchor, expanded Lean semantic target, and checked
proof endpoint.
