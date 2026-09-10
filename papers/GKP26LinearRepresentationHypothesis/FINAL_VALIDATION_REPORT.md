# Final Validation Report: How Many Features Can a Language Model Store Under the Linear Representation Hypothesis?

Updated: 2026-09-09

## 1. Human Verdict

Partially formalized. The compressed-sensing, incoherence, and upper-bound results are proved on the stated domains. The lower-bound branch uses the cited Alon rank theorem as an external assumption.

## 2. Closeout Status

- Completion status: partially formalized.
- The development covers compressed sensing, incoherence, and capacity bounds, with the remaining proof boundaries below; human review is pending.

## 3. Source and Scope

Garg, Kleinberg, and Peng, [*How Many Features Can a Language Model Store Under the Linear Representation Hypothesis?*](https://arxiv.org/abs/2602.11246), arXiv v1 (2026). Scope includes the named main results and their cited rank-lemma support.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| [Theorem 1 — Compressed sensing](docs/SOURCE_CLARIFICATIONS.md#nondegenerate-parameter-domains) | **Exact with source clarification.** The finite construction covers the paper’s intended $k=O(\log m)$ regime. |
| Theorem 2 — Upper bound | **Exact.** |
| [Theorem 3 — Lower bound](docs/ALON_RANK_COROLLARY_SOURCE_NOTE.md) | **Exact for $0<\epsilon<1$, conditional on Lemma 7.** |
| Lemma 5 — Incoherence of random matrices, and its dimension consequence | **Exact.** |
| [Lemma 7 — Alon’s rank theorem](docs/ALON_RANK_COROLLARY_SOURCE_NOTE.md) | **Cited external theorem; assumed in Lean.** |
| [Corollary 8 — Rank bound after row scaling](docs/ALON_RANK_COROLLARY_SOURCE_NOTE.md) | **Exact conditional on Lemma 7.** |
| [Proposition 9 — Feature geometry construction](docs/SOURCE_CLARIFICATIONS.md#proposition-9-choosing-the-coherence-scale) | **Exact.** |
| [Proposition 11 — Norm-constrained feature geometry](docs/GEOMETRY2_DENOMINATOR_SOURCE_NOTE.md) | **Exact after correcting a denominator typo.** |
| [Theorem 12 — Threshold lower bound](docs/THRESHOLD_ACTIVATION_ASYMPTOTIC_SCOPE_MEMO.md) | **Exact conditional on Lemma 7.** |
| [Corollary 13 — Activation and bias](docs/THRESHOLD_ACTIVATION_ASYMPTOTIC_SCOPE_MEMO.md) | **Exact conditional on Lemma 7.** |

Theorem 3 retains its displayed lower restriction on $\epsilon$; the notes explain the nontrivial accuracy range and Proposition 11’s finite denominator change.

## 5. Remaining Boundaries and Gaps

[Lemma 7](docs/ALON_RANK_COROLLARY_SOURCE_NOTE.md), the cited Alon rank theorem, has not been proved in this Lean development. Theorem 3, Corollary 8, Theorem 12, and Corollary 13 use it as an external assumption.

## 6. Additional Assumptions Beyond Paper

The source-compatible accuracy conventions are explained in the [parameter-domain note](docs/SOURCE_CLARIFICATIONS.md#nondegenerate-parameter-domains).

## 7. Proof-Strategy Deviations

[Theorem 12 and Corollary 13](docs/THRESHOLD_ACTIVATION_ASYMPTOTIC_SCOPE_MEMO.md): supplement the printed submatrix argument with $k^2\leq42d$ from a trace/Frobenius bound on the intermediate range. This proves the full stated asymptotic regime conditional on Lemma 7.

## 8. Proof Tricks Worth Reusing

- Sign-split selection handles large negative as well as positive interference.
- Trace/Frobenius rank bounds can cover ranges missed by a submatrix argument.
- A finite Euclidean net and support-count union bound give restricted isometry.

## 9. Generalizations, Conjectures, and Extensions

None. The native proof of the cited rank theorem remains a formalization obligation, as recorded in Section 5.

## 10. Source Clarifications and Exact Readings

- [Proposition 9](docs/SOURCE_CLARIFICATIONS.md#proposition-9-choosing-the-coherence-scale): a smaller auxiliary coherence scale establishes the stated construction.
- [Proposition 11](docs/GEOMETRY2_DENOMINATOR_SOURCE_NOTE.md): the first denominator in parts (ii)–(iii) is $(1-\epsilon)^2$.
- [Parameter domains](docs/SOURCE_CLARIFICATIONS.md#nondegenerate-parameter-domains): the accuracy range and intended sparse regime for compressed sensing.

## 11. Paper Issues and Source Notes

Proposition 11’s denominator typo is explained in Section 10. The external proof boundary is listed in Section 5.

## 12. Detailed Formalization Evidence

The source-facing interface presents each of the 11 selected paper claims once
as a transparent semantic target. The exact cited Alon rank theorem is the sole
nonstandard axiom in the relevant closure; its scaling corollary and the
paper-local reductions from it are checked Lean derivations. The
[final closure receipt](FINAL_CLOSURE_RECEIPT.md) records the partial
obligation graph.

## 13. Paper Assumption Provenance

The [assumption ledger](FINAL_CLOSURE_RECEIPT.md) classifies the cited
Alon normalized-rank theorem as a partial proof boundary, matching Section 5.
The three paper-local semantic prerequisites match their source connections in
the [prerequisite ledger](FINAL_CLOSURE_RECEIPT.md). No other
standalone paper-facing assumption is listed.

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) routes the compressed
sensing, incoherence, geometry, rank, threshold, and activation formulas. The
two Proposition 11 denominator targets are recorded as
corrected targets in the
[source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) and explained
in the [denominator note](docs/GEOMETRY2_DENOMINATOR_SOURCE_NOTE.md). The
threshold and activation calculations are documented in the
[asymptotic-scope memo](docs/THRESHOLD_ACTIVATION_ASYMPTOTIC_SCOPE_MEMO.md).

## 15. Library Lift Pass

Reusable components include finite Euclidean nets, concentration bounds,
finite compressed-sensing recovery, rank normalization, and trace/Frobenius
rank inequalities. The [library ledger](FINAL_CLOSURE_RECEIPT.md)
records 19 direct matches and two corrected-target matches. A native
proof of the normalized Alon theorem remains future work.

## 16. DAG Audit

The [dependency DAG](docs/DependencyDAG.pdf) distinguishes native results from
the partial branch through the cited rank theorem, places source definitions
before their dependent results, and marks the lower, threshold, and
activation/bias conclusions as conditional on that theorem. Its
[TeX source](docs/DependencyDAG.tex) and rendered PDF were inspected for
readability, arrow direction, and overlap.

## 17. Validation Checks

The [focused-build receipt](FINAL_CLOSURE_RECEIPT.md) records a passing
paper build. The [import-closure receipt](FINAL_CLOSURE_RECEIPT.md)
and [final closure receipt](FINAL_CLOSURE_RECEIPT.md) retain the checked
dependency graph and its explicit Alon boundary.

## 18. Paper Definitions Checked

The checked source definitions are linear compressed-sensing dimension,
the linear recovery condition, and incoherence. Their paper-local and
reusable mathematical prerequisites are recorded in the
[statement map](audit/paper_statement_map.json),
[prerequisite ledger](FINAL_CLOSURE_RECEIPT.md), and
[library ledger](FINAL_CLOSURE_RECEIPT.md).

## 19. Named Theorem Statements Checked

The 11 selected targets cover the compressed-sensing construction, random
incoherence, the upper and lower bounds, Propositions 9 and 11, the
threshold theorem, the activation/bias corollary, and the cited-rank reduction
summarized in Section 4. The lower-bound branch remains conditional exactly as
stated in Sections 1 and 5.

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) contains
11 current judgments: nine matches and two corrected-target matches
for Proposition 11. [status.json](status.json) separately records that
human review remains 0 of 11 rows.

## 21. Source-Coverage Audit Ledger

The [coverage ledger](FINAL_CLOSURE_RECEIPT.md) contains 15 items: 11
covered, two support-only, and two covered as corrected targets. The
[statement map](audit/paper_statement_map.json) supplies the complete source
inventory and route assignments.
