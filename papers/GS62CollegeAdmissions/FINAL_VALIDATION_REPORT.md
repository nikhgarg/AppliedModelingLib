# Final Validation Report: Gale--Shapley 1962

Updated: 2026-09-04

## 1. Human Verdict

The paper's selected named theoretical surface is formalized: the two printed
college-admissions definitions, the Section 3 marriage-instability definition,
and Theorems 1--2. The Section 4 conclusion that the waiting-list procedure
terminates in a stable assignment is also checked as the source result needed
to read Theorem 2. Independent reviewer annotations may be added through the
packet or dashboard, but are not a prerequisite for this formalization status.

## 2. Closeout Status

- Completion status: formalized.
- The reviewed surface consists of three definitions, two named theorems, and
  the Section 4 terminal-stability conclusion used by Theorem 2.
- Every selected claim has a direct paper-facing semantic statement and a
  checked proof route. No theorem-level boundary remains within this scope.

## 3. Source and Scope

- Paper: D. Gale and L. S. Shapley, *College Admissions and the Stability of
  Marriage*.
- Source version: *American Mathematical Monthly* 69(1), 1962, printed pages
  9--15 ([public record](https://www.jstor.org/stable/2312726)).
- Formalized paper surface: the two displayed college-admissions definitions
  on printed page 10, the Section 3 prose definition of unstable marriages,
  Theorem 1, Theorem 2, and the Section 4 conclusion that the waiting lists
  form a stable assignment at termination.
- Scope boundary: numerical examples, ranking tables, and unnumbered
  extensions are not named theoretical claims in this review surface.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Theorem 1 | **Exact:** finite stable-marriage existence for strict complete preferences by deferred acceptance. |
| Theorem 2 | **Stability notion clarified:** applicant optimality uses the full operational stability of Sections 4–5. [Reading](docs/SOURCE_CLARIFICATIONS.md#reading-used-for-theorem-2). |
| Section 4 | **Exact:** the simultaneous waiting-list procedure terminates with a stable assignment. |
| Printed definitions | **Exact:** the page-10 replacement-pair and optimality definitions, within their fixed-quota domain, and the separate marriage-instability definition. |

## 5. Remaining Boundaries and Gaps

None within the selected named theoretical surface.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Structure Worth Reusing

The source supplies two complementary reusable finite procedures. For Theorem
1, deferred acceptance maintains tentative partners while rejected applicants
continue proposing, and termination yields stability. For Theorem 2, define a
college to be possible for an applicant when some stable assignment sends the
applicant there, then use induction over the rejection steps to show that the
procedure never rejects an applicant from a possible college. This turns the
algorithmic trace into the applicant-optimality comparison.

## 9. Generalizations, Conjectures, and Extensions

This closeout makes no claim beyond the paper's stated marriage and
college-admissions results. In particular, it does not treat the paper's
unnumbered extensions or numerical examples as separately formalized theorems.

## 10. Source Clarifications and Exact Readings

Theorem 2 uses the full operational stability of Sections 4–5, including
vacancy blocks and mutual acceptability. Page 10's replacement-pair definition
remains a separate literal claim. The [memo](docs/SOURCE_CLARIFICATIONS.md#reading-used-for-theorem-2)
explains the distinction.

## 11. Paper Issues or Caveats

None within the reviewed named theoretical surface. The distinct scope of the
page-10 definition and the completed Sections 4--5 reading is a clarification,
not a caveat on either theorem.

## 12. Detailed Formalization Evidence

The checked surface comprises the page-10 definitions of unstable and optimal
college assignments, the Section 3 definition of an unstable marriage,
Theorem 1, the Section 4 terminal-stability conclusion used by Theorem 2, and
Theorem 2. [PaperInterface.lean](PaperInterface.lean) presents the six selected
claims, and [ProofInterface.lean](ProofInterface.lean) supplies the checked
proof endpoints.

## 13. Paper Assumption Provenance

The [statement map](audit/paper_statement_map.json) anchors the college
definitions to the fixed-quota model and the marriage and waiting-list results
to their source sections. The two retained paper-local prerequisites match
their source connections in the
[prerequisite ledger](FINAL_CLOSURE_RECEIPT.md). No standalone
paper-facing assumption declaration is selected.

## 14. Displayed Formula Provenance

No displayed algebraic formula is selected as a separate result. The two
page-10 definitions and the Section 3 instability definition are preserved as
their own source-facing targets, with exact locations and Lean routes in the
[statement map](audit/paper_statement_map.json).

## 15. Library Lift Pass

The [library semantic ledger](FINAL_CLOSURE_RECEIPT.md) selects no
material reusable-library prerequisite. The deferred-acceptance and
waiting-list models used for these results remain paper-local.

## 16. DAG Audit

[DependencyDAG.tex](docs/DependencyDAG.tex) was compiled to
[DependencyDAG.pdf](docs/DependencyDAG.pdf). The rendered PDF was visually
inspected for readable labels, logical reading order, arrowheads, and node or
edge overlap.

## 17. Validation Checks

The [focused-build receipt](FINAL_CLOSURE_RECEIPT.md) records a passing
paper build. The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md)
records six matching judgments, while the
[import-closure receipt](FINAL_CLOSURE_RECEIPT.md) and
[final closure receipt](FINAL_CLOSURE_RECEIPT.md) record the checked Lean
closure and terminal graph.

## 18. Paper Definitions Checked

The checked definitions are unstable college assignment, optimal stable
college assignment in the fixed-quota domain, and unstable marriage. The
waiting-list procedure model is retained as the source context for the
terminal-stability result and Theorem 2.

## 19. Named Theorem Statements Checked

- Theorem 1: existence of a stable marriage.
- Section 4 terminal-stability conclusion: the waiting-list procedure ends in
  a stable college assignment.
- Theorem 2: applicant optimality under the operational stability reading
  explained in the [source clarification memo](docs/SOURCE_CLARIFICATIONS.md).

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) contains
six direct matches. The [human review packet](docs/HUMAN_REVIEW_PACKET.pdf)
presents the same definitions and claims in dependency order.

## 21. Source-Coverage Audit Ledger

The [coverage ledger](FINAL_CLOSURE_RECEIPT.md) contains five covered
named-theory items: the three definitions and Theorems 1--2. The Section 4
terminal-stability conclusion is retained as a separate direct proof route for
Theorem 2 in the [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md).
The full model and route inventory is in the
[statement map](audit/paper_statement_map.json).
