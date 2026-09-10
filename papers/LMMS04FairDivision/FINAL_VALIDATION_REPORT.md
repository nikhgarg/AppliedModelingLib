# Final Validation Report: On Approximately Fair Allocations of Indivisible Goods

Updated: 2026-09-05 (current-protocol terminal-document refresh)

## 1. Human Verdict

The checked results give bounded-envy allocations, the positive-atom
continuous allocation result, two mechanism impossibilities, and truthfulness
in expectation of independent random allocation.

**Formalization gap:** Theorems 2.1, 2.3, and 4.2 have selected existence or
mechanism components proved, while their runtime, zero-atom, partition-size,
and high-probability rate clauses and Theorems 3.1--3.3 remain unproved.
[Details](#5-remaining-boundaries-and-gaps).

## 2. Closeout Status

- Completion status: partially formalized.
- Scope: six selected results or theorem components; exclusions are in Section 5.

## 3. Source and Scope

The source is *On Approximately Fair Allocations of Indivisible Goods* (EC 2004), recorded in the [source map](audit/paper_statement_map.json). The selected
source-facing scope comprises Lemma 2.2; Theorems 2.1, 2.3 (the positive-atom
branch), and 4.1; and the Theorem 4.2 proof component. The unproved source
claims outside that scope are stated in Section 5.

The Section-2 finite allocation and mechanism targets make finite,
nonempty-agent and finite-good carriers explicit. Theorem 2.3's selected route
takes finite measures, a positive atom bound, and common bounded-interval
support, and constructs finite high points and a finite residual partition. It is a constructive positive-`alpha`
branch; the source's zero-`alpha` invocation is separately disclosed above.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Lemma 2.2; Theorem 2.1 existence; Theorem 4.1 | **Exact.** |
| Theorem 2.1 runtime | **Deferred:** the value-oracle `O(m n^3)` clause remains outside the selected scope. |
| [Theorem 2.3; Lemma 2.4](docs/SOURCE_CLARIFICATIONS.md#lemma-24-choosing-a-progressing-endpoint) | **Restricted scope:** positive `alpha`; a finite progressing partition replaces the nonprogressing endpoint choice. The `alpha=0` branch and partition-count bound remain open. |
| Theorem 4.2 | **Restricted scope:** only truthfulness in expectation of independent uniform allocation; the high-probability envy rate remains open. |
| Theorems 3.1–3.3; Claim 3.4; Lemma 3.5 | **Deferred:** the Section 3 results remain outside the current formalization. |

## 5. Remaining Boundaries and Gaps

The following source claims remain outside the proved scope:

- Theorem 2.1's value-oracle `O(m n^3)` runtime clause.
- Theorem 2.3's `alpha = 0` cake-cutting branch, which cites an external
  envy-free allocation result.
- Lemma 2.4's stated `O(n/alpha)` simultaneous-partition cardinality
  conclusion. The checked high-point/residual construction is finite and
  suffices for the selected positive-`alpha` Theorem 2.3 endpoint, but it is
  not credited as a proof of this source asymptotic.
- Theorem 3.1's complete exponential-query lower bound.
- Theorem 3.2's cited Graham 1.4 scheduling theorem.
- Theorem 3.3's PTAS/FPTAS conclusion, including the missing fixed-dimension
  integer-program machine-runtime theorem.
- Claim 3.4 and Lemma 3.5 as unselected Section-3 source support.
- Theorem 4.2's sufficiently-large-`n`, high-probability Big-O envy rate.

No algorithm-correctness wrapper, certificate, finite concentration inequality,
or historical hard-family construction is counted as proof of these source
claims.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

Theorem 4.1 uses two players, two named goods, and eight eggs (ten goods total). The
printed proof illustrates the same impossibility argument with one hundred
eggs. This smaller checked witness is a proof-route reduction, not a new paper
assumption or a claim of archival proof identity.

## 8. Proof Tricks Worth Reusing

None.

## 9. Generalizations, Conjectures, and Extensions

The shortest substantive extension is reusable complexity infrastructure for
the fixed-dimension integer-program solver/runtime theorem, followed by a
source-faithful Section-3 assembly. Separately, an analytic cake-cutting route
would be needed to cover Theorem 2.3 at `alpha = 0`, and an asymptotic bridge
would be needed to credit Theorem 4.2's printed rate.

## 10. Source Clarifications and Exact Readings

The [source clarification memo](docs/SOURCE_CLARIFICATIONS.md#lemma-24-choosing-a-progressing-endpoint)
explains the nonprogressing printed endpoint choice and the checked
positive-alpha existence result, distinct from the unproved partition-size bound.

## 11. Paper Issues or Caveats

No additional paper issue is asserted beyond the partial-formalization
boundaries in Section 5 and the exact source-proof reading in Section 10.

## 12. Detailed Formalization Evidence

The direct ledger compares six byte-pinned source bundles with fully expanded
Lean propositions and records six matches. [PaperInterface.lean](PaperInterface.lean)
also exposes definitions and partial-support targets without promoting them to
selected source results. The [source-fidelity record](FINAL_CLOSURE_RECEIPT.md)
documents the corrected progressing-endpoint construction.

## 13. Paper Assumption Provenance

No added paper-facing assumption is used on the selected six-result surface.
Finite carriers and the positive-atom/common-interval hypotheses are explicit
source or selected-scope conditions. The current graph selects no separate
paper-assumption declaration or material library prerequisite.

## 14. Displayed Formula Provenance

[The source map](audit/paper_statement_map.json) binds envy, bounded envy,
maximum marginal value, allocation feasibility, the positive-atom partition,
mechanism truthfulness, and the Theorem 4.2 probability component. The
[clarification memo](docs/SOURCE_CLARIFICATIONS.md) separates the proved finite
construction from the unproved `O(n/alpha)` partition count.

## 15. Library Lift Pass

The selected endpoints use finite allocation, measure, and mechanism
infrastructure, but the accepted graph records no material reusable-library
review row. No new library extraction is claimed here.

## 16. DAG Audit

[The dependency DAG](docs/DependencyDAG.pdf) keeps the six selected
Section-2/Section-4 routes separate from nine visible proof boundaries. Its
retained visual inspection found the rendering legible and unclipped; no open
boundary is depicted as proved.

## 17. Validation Checks

Retained focused interface elaboration and the selected-surface closeout check
passed. The [accepted graph](audit/obligation_evidence/current_accepted_graph.json)
and [closure receipt](FINAL_CLOSURE_RECEIPT.md) credential only the explicitly
partial scope in Sections 3--5. No new Lean or semantic review was run for this
document edit.

## 18. Paper Definitions Checked

Checked definitions include envy, envy-freeness, bounded envy, maximum
marginal value, finite allocations, direct and randomized mechanisms,
truthfulness, and truthfulness in expectation.

## 19. Named Theorem Statements Checked

- Lemma 2.2 and Theorem 2.1's existence claim.
- Theorem 2.3's positive-atom finite construction.
- Theorem 4.1's two mechanism impossibilities.
- Theorem 4.2's truthfulness-in-expectation component.

The runtime, zero-atom, partition-count, Section 3, and high-probability envy
claims remain outside the credited surface as detailed in Section 5.

## 20. Paper-Facing Statement Validator Ledger

The six direct matches are recorded in the
[source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md). The
[source-fidelity ledger](FINAL_CLOSURE_RECEIPT.md) records the
progressing-endpoint repair; the accepted graph binds the exact selected proof
routes without expanding their scope.

## 21. Source-Coverage Audit Ledger

The [coverage ledger](FINAL_CLOSURE_RECEIPT.md) records thirty-seven
covered items and twelve conditional boundaries. The row-local ledger records
the corresponding matched and boundary judgments. [The source map](audit/paper_statement_map.json)
and Section 5 identify the unproved claims, so the accepted partial graph is
not presented as full-paper coverage.
