# Final Validation Report: EFX for Additive Chores: Nonexistence, Pareto Incompatibility, and Bi-Valued Existence

Updated: 2026-09-08

## 1. Human Verdict

The paper's named theoretical surface is formalized. The checked surface
includes the displayed fairness and allocation definitions, Theorems 1--3,
their named supporting propositions and lemmas, the general-agent insertion
remark, the explicit EFX witness used in Theorem 2, and the two named Appendix
A propositions. Independent reviewer annotations may be added through the
packet or dashboard, but are not a prerequisite for this formalization status.

## 2. Closeout Status

- Completion status: formalized.
- 24 source claims are in scope: six definitions, three theorems, six
  propositions, seven lemmas, one substantive remark, and one unlabeled
  mathematical claim.
- Every selected claim has a direct paper-facing semantic statement and a
  checked proof route. No theorem-level boundary remains within this scope.

## 3. Source and Scope

- Paper: Wentao He and Biaoshuai Tao, *EFX for Additive Chores:
  Nonexistence, Pareto Incompatibility, and Bi-Valued Existence*.
- Source version: [arXiv v2 (2026-07-09)](https://arxiv.org/abs/2606.08872v2).
- Formalized paper surface: the definitions of EF for chores, EFX for chores,
  Pareto-optimality, canonical allocation, canonical short/long labels, and
  super-canonical allocation; Theorems 1--3; the named propositions and
  lemmas supporting those results; the general-agent insertion remark; the
  explicit EFX witness in the Theorem 2 construction; and the named Appendix A
  propositions.
- Scope boundary: the complete source review also records two explanatory
  remarks about the general-
  $n$ construction and tightness as deep-audit material. They do not add a
  separate mathematical endpoint beyond Theorem 1 and its appendix route.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Theorem 1 | **Exact.** |
| Theorem 2 | **Exact.** |
| Theorem 3 | **Exact.** |
| Propositions 1–6; Lemmas 1–7; Remark 3 | **Exact.** |

## 5. Remaining Boundaries and Gaps

None within the selected named theoretical surface.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Structure Worth Reusing

Theorem 3 provides a useful finite-allocation pattern. First partition items
by their role in the instance, establish an EFX allocation for the central M2
piece, orient the remaining small-item structure in a balanced way, and then
insert or compose the M34 residue while preserving the relevant inequalities.
Theorem 2 illustrates the complementary obstruction pattern: derive
allocation-wide lower bounds from EFX, then exhibit a Pareto improvement that
the lower bounds rule out for an EFX allocation.

## 9. Generalizations, Conjectures, and Extensions

This closeout makes no existence claim for more than four agents beyond the
results stated in the source. Theorem 1 and Theorem 2 already quantify over
arbitrary $n \geq 4$; Theorem 3 is deliberately reported only in its stated
four-agent form.

## 10. Source Clarifications and Exact Readings

None identified in the audited source version.

## 11. Paper Issues or Caveats

None within the reviewed named theoretical surface.

## 12. Detailed Formalization Evidence

The current surface contains 24 source presentations: six definitions and 18
result claims. The result claims cover Theorems 1--3, their named propositions
and lemmas, the explicit EFX witness used in Theorem 2, and the general-agent
insertion claim. [PaperInterface.lean](PaperInterface.lean) contains the 18
transparent result specifications, and [ProofInterface.lean](ProofInterface.lean)
supplies their checked endpoints.

## 13. Paper Assumption Provenance

No standalone paper-facing assumption is selected. Three paper-local
definition prerequisites match their source connections in the
[prerequisite ledger](FINAL_CLOSURE_RECEIPT.md). The finite
chore set, nonnegative item costs, additive bundle costs, feasibility, and the
tri-valued and bi-valued domains appear directly in the expanded result
targets.

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) records exact source routes
for the allocation, cost, EF, EFX, Pareto, canonical, and super-canonical
definitions and for all supporting result presentations. The
[source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) records 18
direct matching result judgments.

## 15. Library Lift Pass

The three selected reusable declarations are the shared envy-free, EFX, and
Pareto-optimal predicates for chores. All three match their selected source
connections in the [library ledger](FINAL_CLOSURE_RECEIPT.md).
The canonical-allocation constructions and theorem-specific decomposition
remain paper-local.

## 16. DAG Audit

[DependencyDAG.tex](docs/DependencyDAG.tex) and
[DependencyDAG.pdf](docs/DependencyDAG.pdf) show the six definitions and the
Theorem 1, Theorem 2, and Theorem 3 result routes. The explicit Theorem 2 EFX
witness and the general-agent insertion claim appear as their own nodes. The
rendered DAG was visually inspected for legibility, clipping, and node-edge
overlap.

## 17. Validation Checks

The [focused-build receipt](FINAL_CLOSURE_RECEIPT.md) records a passing
paper build. The [import-closure receipt](FINAL_CLOSURE_RECEIPT.md)
and [final closure receipt](FINAL_CLOSURE_RECEIPT.md) record the checked Lean
closure and terminal obligation graph.

## 18. Paper Definitions Checked

The checked source definitions are envy-freeness for chores, EFX for chores,
Pareto optimality, canonical allocation, canonical short/long labels, and
super-canonical allocation. The exact source and Lean routes are recorded in
the [statement map](audit/paper_statement_map.json).

## 19. Named Theorem Statements Checked

- Theorem 1 and its supporting four-agent, A-free-bundle, and Appendix A
  propositions.
- Theorem 2, its explicit EFX allocation, the large-item proposition, and the
  EFX cost lower bound.
- Theorem 3 and the insertion, composition, canonical-allocation, balanced
  orientation, M2 allocation, and exceptional-residue lemmas.
- The general-agent insertion claim.

The 18 exact target/endpoint pairings are in
[PaperInterface.lean](PaperInterface.lean) and
[ProofInterface.lean](ProofInterface.lean).

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) contains
18 direct matches. The [human review packet](docs/HUMAN_REVIEW_PACKET.pdf)
presents the definitions and results in dependency order.

## 21. Source-Coverage Audit Ledger

The [coverage ledger](FINAL_CLOSURE_RECEIPT.md) contains 20 covered
named-theory items. The full 24-presentation inventory and route assignments
are recorded in the [statement map](audit/paper_statement_map.json).
