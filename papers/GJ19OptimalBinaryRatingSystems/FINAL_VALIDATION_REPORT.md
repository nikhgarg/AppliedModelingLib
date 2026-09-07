# Final Validation Report: GJ19 Optimal Binary Rating Systems

Updated: 2026-09-05

## 1. Human Verdict

The formalization proves global value maximization and optimization of the
displayed rate formula across all tied optimal partitions for at least three
rating levels.

**Formalization gap:** Theorem 3.1 is proved for optimization of its displayed rate
formula for $M\geq3$; identifying that formula with the actual ranking-quality
exponent and proving Lemma C.4's same-objective equivalence remain unproved.
[Details](docs/SOURCE_CLARIFICATIONS.md#lemma-c4-the-two-objective-comparisons).

## 2. Closeout Status

- Completion status: **formalized**.
- The repaired partition comparison and source-cell interfaces compile.
- Selected statements and source definitions have current independent reviews.
- The complete source Theorem 3.1 remains uncredited, as explained in Section 5.

## 3. Source and Scope

The checked source is the AISTATS 2019 / PMLR 89 main paper and supplement in
`cited publication`, SHA-256
`59780d7a9ea09cccd9c6877103434757a6597212512958c6e22e60b189826e89`.
The public source is the
[PMLR paper PDF](https://proceedings.mlr.press/v89/garg19a/garg19a.pdf).
The inventory includes model definitions, formulas, algorithms, named results,
and proof-critical displays. Empirical plots and simulations are context rather
than Lean theorem targets.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Theorem 3.1; Lemmas C.3–C.4 | **Formalization gap:** the optimized finite-rate formula and auxiliary integral rates are not yet identified with the actual $W-W_k$ exponent. The two-level endpoint also remains outside the real-valued rate model. [Boundary](docs/SOURCE_CLARIFICATIONS.md#lemma-c4-the-two-objective-comparisons). |
| Lemma 3.1 | **Exact for the displayed adjacent-rate system.** |
| Algorithm 1 | **Typos fixed:** midpoint, endpoint-rate evaluation, and final helper argument. [Formulas](docs/SOURCE_CLARIFICATIONS.md#local-formulas-and-proof-clarifications). |
| Theorem 3.2 | **Same asymptotic runtime; restricted scope:** explicit constants in the paper's $O(M\log^2(M/\epsilon))$ rate; the displayed theorem covers $M>3$. [Bound](docs/SOURCE_CLARIFICATIONS.md#theorem-32-an-explicit-grid-and-runtime-bound). |
| Lemmas B.1–B.2 | **Exact.** |
| Lemma B.3 | **Exact.** |
| Theorem B.1 | **Exact.** |
| Theorem C.1; Lemmas C.1–C.2 | **Exact.** |
| Lemmas C.5–C.9; Corollaries C.1–C.3 | **Source clarifications:** endpoint $t_{M-1}=1$ and first endpoint rate $-g_1\log(1-t_1)$. [Formulas](docs/SOURCE_CLARIFICATIONS.md#local-formulas-and-proof-clarifications). |
| Remark C.2 | **Changed statement:** coordinatewise separation replaces joint strict convexity. [Reason](docs/SOURCE_CLARIFICATIONS.md#local-formulas-and-proof-clarifications). |
| Lemmas C.10–C.12; Corollary C.4 | **Exact.** |

## 5. Remaining Boundaries and Gaps

- [Theorem 3.1](docs/SOURCE_CLARIFICATIONS.md#lemma-c4-the-two-objective-comparisons): identify the optimized formula with the actual ranking-quality exponent. The finite real-valued rate model covers $M\ge3$; the two-level endpoint remains outside it.
- [Lemma C.4](docs/SOURCE_CLARIFICATIONS.md#lemma-c4-the-two-objective-comparisons): the equivalence for one ranking-quality gap remains unproved; the selected endpoint establishes two separate rate results.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

The [full-square uniform-convergence step](docs/SOURCE_CLARIFICATIONS.md#local-formulas-and-proof-clarifications) is replaced by separated-cell and
weighted essential-infimum arguments. The separate C.4 proof gap is described
in [Section 5](#5-remaining-boundaries-and-gaps).

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

The [memo](docs/SOURCE_CLARIFICATIONS.md#local-formulas-and-proof-clarifications) lists the endpoint, algorithm-variable, logarithm, and local lower-bound notation clarifications. Remark C.2 uses coordinatewise separation rather than joint strict convexity, which is incompatible with multiple diagonal minima.

<!-- BEGIN GENERATED SETTLED REVIEW CONTEXT -->
<!-- settled-review-context-sha256: e999d4299e64fbc4233223eb05b92cd959fce0c237ed18ee47925c9999ea119f -->
<!-- settled-review-context-presentation-sha256: e8bf8e5a250907e29df12b2c6047b6f3778aa1d42cfb75e8f783c55f87f25652 -->
### Source readings and additional assumptions

- In the KL footnote, reverse both logarithm ratios to obtain the standard nonnegative Bernoulli divergence used by the proof.
- The endpoint-normalized vector represents the optimal designs of Lemma 3.1; the paper also permits general step rules.
<!-- END GENERATED SETTLED REVIEW CONTEXT -->

## 11. Paper Issues or Caveats

Section 5 records the remaining exponent-identification and two-level endpoint gaps. Section 10 links the local source clarifications.

## 12. Detailed Formalization Evidence

The current mathematical statements and their proofs are in
[PaperInterface](PaperInterface.lean) and [ProofInterface](ProofInterface.lean).
The revised partition comparison and source-cell definitions compile, including
regressions with nonconstant and discontinuous matching functions. Historical
review records do not certify these changed interfaces.

## 13. Paper Assumption Provenance

The [source-fidelity ledger](FINAL_CLOSURE_RECEIPT.md) records the
source conditions and remaining proof obligations.

## 14. Displayed Formula Provenance

The [source map](audit/paper_statement_map.json) binds formulas to their exact
source passages and Lean declarations. Section 5 identifies the formulas whose
connection to the paper's ranking-quality objective remains unproved.

## 15. Library Lift Pass

Reusable support covers Bernoulli large-deviation rates, finite optimization,
and nested bisection. The partition proof also establishes that changing cell
endpoint ownership preserves value integrals; rate infima use the actual cells.

## 16. DAG Audit

The [DAG source](docs/DependencyDAG.tex) and [rendered DAG](docs/DependencyDAG.pdf)
show the dependency structure and remaining gaps. The PDF was rebuilt and
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
available here. The full-source gaps remain visible in Section 5.

- [Source statement inventory](audit/paper_statement_map.json)
- [Source-to-statement review](FINAL_CLOSURE_RECEIPT.md)
- [Model and definition review](FINAL_CLOSURE_RECEIPT.md)
- [Reusable definitions review](FINAL_CLOSURE_RECEIPT.md)
- [Historical closeout record](FINAL_CLOSURE_RECEIPT.md)
- [Review packet awaiting refresh](docs/HUMAN_REVIEW_PACKET.pdf)

## 21. Source-Coverage Audit Ledger

The [source inventory](audit/paper_statement_map.json) retains named results,
model definitions, and their supporting source passages. Empirical plots and
simulations are outside the named-theory scope. The unresolved theorem scope is
stated in Section 5; retained historical coverage judgments do not close it.
