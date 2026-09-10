# Final Validation Report: Designing Optimal Binary Rating Systems

Updated: 2026-09-09

## 1. Human Verdict

The paper's selected results on optimal binary rating systems, ranking
accuracy, and learning are formalized.

## 2. Closeout Status

- Completion status: formalized
- One-sentence recap: The selected rating-system optimization, ranking-rate,
  and learning results are proved.

## 3. Source and Scope

Garg and Johari, [*Designing Optimal Binary Rating Systems*](https://proceedings.mlr.press/v89/garg19a/garg19a.pdf),
AISTATS 2019 / PMLR 89, main paper and supplement. The scope includes the
named theoretical results and their governing definitions and algorithms.
Empirical plots and simulations are outside the formalization.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| [Theorem 3.1; Lemmas C.3–C.4](docs/SOURCE_CLARIFICATIONS.md#theorem-31-and-lemmas-c3c4-cross-bin-ranking-rates) | **Exact.** |
| Lemma 3.1 | **Exact.** |
| Algorithm 1 | **Exact after correcting typos.** [Formulas](docs/SOURCE_CLARIFICATIONS.md#local-formulas-and-proof-clarifications). |
| Theorem 3.2 | **Exact asymptotic runtime for $M>3$.** [Bound](docs/SOURCE_CLARIFICATIONS.md#theorem-32-an-explicit-grid-and-runtime-bound). |
| Lemmas B.1–B.2 | **Exact.** |
| Lemma B.3 | **Exact.** |
| Theorem B.1 | **Exact.** |
| Theorem C.1; Lemmas C.1–C.2 | **Exact.** |
| Lemmas C.5–C.9; Corollaries C.1–C.3 | **Exact with source clarification.** [Formulas](docs/SOURCE_CLARIFICATIONS.md#local-formulas-and-proof-clarifications). |
| Remark C.2 | **Changed statement:** coordinatewise separation replaces joint strict convexity. [Reason](docs/SOURCE_CLARIFICATIONS.md#local-formulas-and-proof-clarifications). |
| Lemmas C.10–C.12; Corollary C.4 | **Exact.** |

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

The [full-square uniform-convergence step](docs/SOURCE_CLARIFICATIONS.md#local-formulas-and-proof-clarifications) is replaced by separated-cell and
weighted essential-infimum arguments.

## 8. Proof Tricks Worth Reusing

- Separate finite Bernoulli-rate identities from continuum aggregation.
- Use endpoint-aware level vectors throughout equalization and optimization.
- Derive random conditional frequencies as a ratio of two Strong Law limits,
  then exploit finiteness for simultaneous convergence.
- Derive ranking stability from a strict limiting score gap.
- Prove an explicit source-optimizer gap lower bound before choosing the
  bisection grid, so runtime does not depend on an unknown optimum coordinate.

## 9. Generalizations, Conjectures, and Extensions

The source's whole-sequence and broader matching-function extensions of the
Theorem B.1 limit are conjectural context and are not promoted to paper claims.
The formalization includes the source multiplicative Theorem 3.2 extension as
a checked support theorem.

## 10. Source Clarifications and Exact Readings

The rate comparison uses pairs in distinct rating bins, the paper's intended
reading. The [memo](docs/SOURCE_CLARIFICATIONS.md#theorem-31-and-lemmas-c3c4-cross-bin-ranking-rates)
makes this domain explicit; it adds no matching-rate restriction.

The [memo](docs/SOURCE_CLARIFICATIONS.md#local-formulas-and-proof-clarifications) lists the endpoint, algorithm-variable, logarithm, and local lower-bound notation clarifications. Remark C.2 uses coordinatewise separation rather than joint strict convexity, which is incompatible with multiple diagonal minima.

## 11. Paper Issues or Caveats

None beyond the source clarifications in Section 10.

## 12. Detailed Formalization Evidence

The current mathematical statements and their proofs are in
[PaperInterface](PaperInterface.lean) and [ProofInterface](ProofInterface.lean).
The checked scope includes nonconstant and discontinuous matching functions
and the cross-bin ranking-rate objective.

## 13. Paper Assumption Provenance

The [source-fidelity ledger](FINAL_CLOSURE_RECEIPT.md) records the
source conditions and local proof clarifications.

## 14. Displayed Formula Provenance

The [source map](audit/paper_statement_map.json) binds archival formulas to
their exact source passages and Lean declarations. Section 10 records the
intended cross-bin reading of the rate objective.

## 15. Library Lift Pass

Reusable support covers Bernoulli large-deviation rates, finite optimization,
and nested bisection. The partition proof also establishes that changing cell
endpoint ownership preserves value integrals; rate infima use the actual cells.

## 16. DAG Audit

The [DAG source](docs/DependencyDAG.tex) and [rendered DAG](docs/DependencyDAG.pdf)
show the dependency structure. The PDF was rebuilt and
visually checked on September 6, 2026: labels, arrows, legend, and page bounds
are readable. The review packet presents the same selected statements and governing definitions.

## 17. Validation Checks

The current `ProofInterface` and `PartitionTieSelectionRegression` targets
compile. The regression checks include all cross-cell pairs and a discontinuous
matching function whose cell infimum depends on endpoint ownership. Independent
source reviews are current; the [closeout record](FINAL_CLOSURE_RECEIPT.md)
records acceptance for its pinned inputs.

```bash
lake build GJ19OptimalBinaryRatingSystems.ProofInterface
lake build GJ19OptimalBinaryRatingSystems.PartitionTieSelectionRegression
python3 scripts/closeout_reuse_plan.py --paper GJ19OptimalBinaryRatingSystems
python3 scripts/audit_repository.py --paper GJ19OptimalBinaryRatingSystems --paper-closeout --include-active --info-limit 0
```

## 18. Paper Definitions Checked

The source-facing definitions cover quality, matching, binary ratings,
pairwise ranking accuracy, the weighted objective, finite partitions, and
lexicographic optimization. The strict-partition and source-cell definitions
have passed independent source review.

## 19. Named Theorem Statements Checked

Section 4 gives the result-by-result comparison. A compiled statement is credited
only for its displayed scope; it does not establish an unresolved source claim.

## 20. Statement Review Evidence

The current selected review inputs and their retained independent evidence are
available here.

- [Source statement inventory](audit/paper_statement_map.json)
- [Source-to-statement review](FINAL_CLOSURE_RECEIPT.md)
- [Model and definition review](FINAL_CLOSURE_RECEIPT.md)
- [Reusable definitions review](FINAL_CLOSURE_RECEIPT.md)
- [Closeout record](FINAL_CLOSURE_RECEIPT.md)
- [Review packet awaiting refresh](docs/HUMAN_REVIEW_PACKET.pdf)

## 21. Source-Coverage Audit Ledger

The [source inventory](audit/paper_statement_map.json) retains named results,
model definitions, and their supporting source passages. Empirical plots and
simulations are outside the named-theory scope.
