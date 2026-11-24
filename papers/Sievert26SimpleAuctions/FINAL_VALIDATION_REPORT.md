# Final Validation Report: Machine-Verified Two-Sided Bounds for Simple Multi-Item Auctions: 2.1946 <= c* <= 2.486 and an i.i.d. Lower Bound above 1.316

Updated: 2026-11-24

## 1. Human Verdict

The paper's named theoretical surface is formalized. All five named results—Theorems 1, 2, and 4, Corollary 3, and Proposition 5—and the Section 1 single-buyer independent additive auction definitions are fully proved with no remaining theorem-level boundaries, external assumptions, or source corrections. Independent human review annotations may be added through the review packet or dashboard, and are not a prerequisite for this formalization status.

## 2. Closeout Status

- Completion status: formalized.
- Every selected named theoretical claim in the paper has a direct paper-facing statement and a complete machine-checked proof route with no remaining proof boundaries.

## 3. Source and Scope

- Paper: Max Sievert, *Machine-Verified Two-Sided Bounds for Simple Multi-Item Auctions: 2.1946 <= c* <= 2.486 and an i.i.d. Lower Bound above 1.316*.
- Source version: [Zenodo v1.0.1 (DOI 10.5281/zenodo.24482558, 2026-11-23)](https://doi.org/10.5281/zenodo.24482558).
- Formalized paper surface: the Section 1 setting definitions (independent finitely supported item distributions on the nonnegative reals, separate-selling revenue, grand-bundle revenue, incentive-compatible and individually rational direct mechanisms, optimal revenue, and the universal approximation constant $c^*$), Theorem 1 (general lower bound above $2.1946$ witnessed by a deterministic mechanism), Theorem 2 (universal upper bound $1.1187\,\mathrm{SREV} + 1.367299\,\mathrm{BREV}$ and $2.486\max\{\mathrm{SREV}, \mathrm{BREV}\}$), Corollary 3 (two-sided bracket $2.1946 \le c^* \le 2.486$), Theorem 4 ($40$-item i.i.d. lower bound above $1.316$ witnessed by a deterministic two-part tariff with entry fee $9$ and item price $4$), and Proposition 5 ($100$-item i.i.d. bound $\ge 1.324907$ for the displayed equal-revenue tail distribution and the same deterministic two-part tariff).
- Scope boundary: the literature review, non-rigorous floating-point exploration of numerical limits, stylised financial auction illustration, table captions, and narrative commentary are outside normal named-theory coverage.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Theorem 1 | **Exact.** |
| Theorem 2 | **Exact.** |
| Corollary 3 | **Exact.** |
| Theorem 4 | **Exact.** |
| Proposition 5 | **Exact.** |

## 5. Remaining Boundaries and Gaps

None within the selected named theoretical surface.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Structure Worth Reusing

Two proof architectures in this development generalize cleanly to related Bayesian mechanism-design problems. For universal upper bounds, finite-support Lagrangian duality combines with a layer-cake integral representation, step-function Jensen weights, a multi-exponential Laplace bundle bound via certified linear tangents, and a directed-integer one-dimensional certificate evaluated directly by kernel reduction. For deterministic separation lower bounds, combining equal-revenue marginals with Kronecker-packed generating-function arithmetic and shifting tail bounds certifies separate-selling, grand-bundle, and two-part-tariff revenues exactly inside the proof assistant.

## 9. Generalizations, Conjectures, and Extensions

Theorem 2 is proved in its full finite-index-set form as stated in the source paper, and Proposition 5 is fully machine-checked in addition to Theorems 1, 2, and 4 and Corollary 3. No claim is made beyond the stated bounds: narrowing the universal constant $c^* \in [2.1946, 2.486]$ further or proving sharper i.i.d. separations for larger item counts remains open.

## 10. Source Clarifications and Exact Readings

None identified in the audited source version.

## 11. Paper Issues or Caveats

None within the reviewed named theoretical surface.

## 12. Detailed Formalization Evidence

The reviewed source surface consists of six source-facing setting definitions and five named results (Theorems 1, 2, and 4, Corollary 3, and Proposition 5). [PaperInterface.lean](PaperInterface.lean) exposes the five transparent result specifications (`general_lower_boundSpec`, `universal_upper_boundSpec`, `two_sided_bracketSpec`, `iid_lower_boundSpec`, `iid100_lower_boundSpec`) paired directly with their five exact-type theorem endpoints (`general_lower_bound`, `universal_upper_bound`, `two_sided_bracket`, `iid_lower_bound_thm`, `iid100_lower_bound`), all proved with zero `sorry`, zero `native_decide`, and standard axioms only. The [final closure receipt](FINAL_CLOSURE_RECEIPT.md) records the complete accepted obligation graph.

## 13. Paper Assumption Provenance

No standalone paper-facing assumption is declared in [Assumptions.lean](Assumptions.lean). Six paper-local semantic prerequisite definitions (`FinDist`, `SREV`, `BREV`, `Mechanism`, `REV`, `cStar`) match the Section 1 Setting definitions in the [prerequisite ledger](FINAL_CLOSURE_RECEIPT.md). All domain requirements (finite support, nonnegative values, probability normalization, IC/IR over all nonnegative valuation vectors, determinism, and explicit two-part-tariff payment rules) appear directly in the expanded specifications and definitions.

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) binds exact byte-pinned source anchors for the Section 1 Setting definitions and all five named results (`general_lower_bound`, `universal_upper_bound`, `two_sided_bracket`, `iid_lower_bound`, `iid100_lower_bound`). The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) records five direct matching judgments across all displayed inequalities, constants, quantifiers, and witness specifications.

## 15. Library Lift Pass

No existing `AppliedModelingLib` reusable declaration covers single-buyer independent finitely supported Bayesian multi-item auctions (`MechanismDesign.Auctions` currently covers digital goods and combinatorial auctions). Accordingly, the reusable library semantic prerequisite set is empty (`0` library prerequisites), and all auction primitives and kernel verifiers remain self-contained in the paper folder. Future library lift candidates include `FinDist`, `SREV`, `BREV`, `Mechanism`, `REV`, and the finite-support duality lemma.

## 16. DAG Audit

[DependencyDAG.tex](docs/DependencyDAG.tex) and [DependencyDAG.pdf](docs/DependencyDAG.pdf) display the Section 1 setting definitions (`FinDist`, `SREV`, `BREV`, `Mechanism`, `REV`, `c*`), all four independent main results (Theorems 1, 2, 4, and Proposition 5), and the direct dependency arrows feeding Corollary 3. The rendered PDF was visually inspected for label legibility, arrowhead clarity, reading order, and absence of node or edge overlap.

## 17. Validation Checks

The [focused-build receipt](FINAL_CLOSURE_RECEIPT.md) records a clean passing build of `Sievert26SimpleAuctions`. The [import-closure receipt](FINAL_CLOSURE_RECEIPT.md) and [final closure receipt](FINAL_CLOSURE_RECEIPT.md) record the checked Lean module closure, standard axiom closure, and terminal obligation graph.

## 18. Paper Definitions Checked

The six checked Section 1 setting definitions are `FinDist`, `SREV`, `BREV`, `Mechanism`, `REV`, and `cStar`, together with their supporting finite product helpers (`FinDist.tail`, `FinDist.rev`, `Profile`, `prob`, `value`, `bundleTail`, `Mechanism.rev`, `ValidConstants`). Their exact source anchors and Lean routes are recorded in the [statement map](audit/paper_statement_map.json).

## 19. Named Theorem Statements Checked

- Theorem 1 (`general_lower_boundSpec` / `general_lower_bound`): existence of $m$, independent finitely supported $D$, and a deterministic IC+IR mechanism witnessing $\mathrm{REV}(D) > 2.1946 \max\{\mathrm{SREV}(D), \mathrm{BREV}(D)\}$.
- Theorem 2 (`universal_upper_boundSpec` / `universal_upper_bound`): universal bound $\mathrm{REV}(D) \le 1.1187\,\mathrm{SREV}(D) + 1.367299\,\mathrm{BREV}(D)$ over all finite index sets $\iota$ and $\mathrm{REV}(D) \le 2.486\max\{\mathrm{SREV}(D), \mathrm{BREV}(D)\}$ over all `Fin m`.
- Corollary 3 (`two_sided_bracketSpec` / `two_sided_bracket`): $2.1946 \le c^* \le 2.486$.
- Theorem 4 (`iid_lower_boundSpec` / `iid_lower_bound_thm`): $40$-item i.i.d. separation $> 1.316$ witnessed by the deterministic two-part tariff with entry fee $9$ and item price $4$.
- Proposition 5 (`iid100_lower_boundSpec` / `iid100_lower_bound`): $100$-item i.i.d. exact bound $\ge 1.324907$ for the displayed tail distribution and deterministic two-part tariff $(9,4)$.

All five exact target/endpoint pairings are located in [PaperInterface.lean](PaperInterface.lean).

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) contains five direct `matches` judgments and six matching paper-local semantic prerequisite judgments. The [human review packet](docs/HUMAN_REVIEW_PACKET.pdf) presents the definitions and all five results for optional independent human inspection; [status.json](status.json) records that external human review stands at 0 of 5 rows.

## 21. Source-Coverage Audit Ledger

The [coverage ledger](FINAL_CLOSURE_RECEIPT.md) accounts for all six selected source items (one setting-definitions cluster and five named results). The complete source inventory, region partition, and route assignments are recorded in the [statement map](audit/paper_statement_map.json).
