# Final Validation Report: The Regulation of Queue Size by Levying Tolls

Updated: 2026-09-02

## 1. Human Verdict

Formalized. The selected theoretical surface of Naor's finite-capacity M/M/1
queueing model is fully proved: the stationary distribution and performance
formulas, private and social admission thresholds, the beneficial-toll
interval, the revenue-maximizing threshold, its toll, and the ordering of the
three thresholds. Each of the six source-facing claim groups has been checked
against the source and formally proved.

No paper-local mathematical caveat or open proof boundary was found. Additional
source material remains visible in the inventory as proof support or deep-only
context rather than being counted as separate theorem claims.

## 2. Closeout Status

- Completion status: formalized.
- Direct source review surface: six source claims.
- Human review status: no source-claim annotations have been recorded. Human
  review is encouraged but is not a release blocker and is never inferred from
  agent or machine checks.
- This report is the researcher-facing summary; the linked evidence artifacts
  record the detailed closeout checks.

## 3. Source and Scope

The source is P. Naor, [*The Regulation of Queue Size by Levying
Tolls*](https://www.jstor.org/stable/1909200), *Econometrica* 37(1), January
1969, pp. 15--24.

The audit uses the JSTOR scan and its reading-order text extraction. The
selected direct surface is Equations (3)--(31), organized into six mathematical
claim groups. The accompanying source record preserves the exact inventory,
source spans, and mathematical context.

The continuous crossing formulas for `v_0` and `v_r` remain inventoried as
proof support for the corresponding discrete threshold conclusions. The
unnumbered numerical comparison after the social-threshold discussion, the
qualitative extensions in the concluding remarks, and Table I are retained in
the source inventory outside the selected theorem denominator.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Equations (3)–(11) | **Exact:** stationary distribution and queue-flow identities. |
| Equations (12)–(16) | **Exact:** private admission threshold `n_s=floor(R mu/C)`. |
| Equations (17)–(25) | **Exact:** a social optimum exists no higher than the private threshold. |
| Equation (26) | **Exact:** the stated toll interval implements the social threshold. |
| Equations (27)–(31) | **Exact:** a revenue optimum exists no higher than the social threshold, with toll `R-C n_r/mu`. |

## 5. Remaining Boundaries and Gaps

None on the selected source surface. The continuous `v_0` and `v_r`
parametrizations are source-visible proof support, not hidden assumptions. The
formalized endpoints do not rely on an axiom, opaque theorem-shaped boundary,
unproved maximizer certificate, or assumed root-existence statement.

## 6. Additional Assumptions Beyond the Paper

None.

## 7. Proof-Strategy Deviations

The paper introduces real-valued crossing parameters `v_0` and `v_r`, then
identifies integer thresholds with their floors. The formalization proves the
same advertised discrete results directly:

- the exact one-step welfare difference is a positive factor times service
  value minus cumulative delay exposure;
- delay exposure is monotone, so its first crossing is globally optimal; and
- revenue is maximized on the finite social prefix, after which an exact
  one-step identity shows that it cannot increase.

This replaces the proof route without weakening or changing the source
conclusions. The printed crossing calculations remain in the audit inventory
and are not used as assumptions.

## 8. Proof Ideas Worth Reusing

- Finite geometric sums avoid artificial singularities and make stationary
  identities valid directly at traffic intensity one.
- Exact adjacent-threshold differences reduce global discrete optimization to
  a monotone crossing argument.
- Maximizing revenue on the finite social prefix, then proving tail
  monotonicity, produces a concrete finite maximizer without a compactness or
  attainment assumption.
- Separating customer income from transfer-inclusive combined income makes the
  role of toll revenue explicit while preserving the social objective.

## 9. Generalizations and Reusable Contributions

A reusable finite-capacity queueing library provides truncated-geometric
stationary laws, generator balance, generating polynomials, queue-length
moments, flow identities, and exact one-step welfare and revenue formulas. The
paper-specific formalization connects Naor's notation and threshold conventions
to those mathematical components.

The concluding claims about nonexponential service, heterogeneous rewards, and
traffic-dependent rewards are broader modeling directions. They are explicitly
inventoried but are not presented in the source as numbered theorem statements
for the finite M/M/1 analysis.

## 10. Source Clarifications and Exact Readings

None.

## 11. Paper Issues or Caveats

None.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) presents each of the six direct
source claims once as a transparent target, and
[ProofInterface.lean](ProofInterface.lean) supplies one checked endpoint for
each. The underlying definitions and proofs are in the paper-local queueing
files and the reusable queueing library; no claim receives credit from a
declaration name or result-bearing certificate.

## 13. Paper Assumption Provenance

[Assumptions.lean](Assumptions.lean) contains no paper-facing mathematical
assumption. The two material reusable-library prerequisites match their source
connections in the [library ledger](FINAL_CLOSURE_RECEIPT.md).
Source model conditions are visible in the expanded specifications.

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) records the six direct
formula groups spanning Equations (3)--(31), their model context, and two
supporting derivations. The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md)
records direct matches for all six selected targets.

## 15. Library Lift Pass

Reusable content includes finite-capacity birth--death rates, stationary
geometric mass, normalizers and weighted sums, generating polynomials,
admission and service flows, opportunity costs, transfer accounting, and
one-step welfare and revenue identities. Naor-specific grouping, source
numbering, and economic interpretation remain paper-local.

## 16. DAG Audit

[DependencyDAG.tex](docs/DependencyDAG.tex) orders the finite-admission model
and stationary identities before the private, social, revenue, and toll
results. Its compiled [DependencyDAG.pdf](docs/DependencyDAG.pdf) was visually
inspected on 2026-09-02; its model and result clusters are in dependency order,
with legible labels and no observed node, label, or edge overlap.

## 17. Validation Checks

The [focused-build receipt](FINAL_CLOSURE_RECEIPT.md) records a passing
proof-interface build. The [import-closure receipt](FINAL_CLOSURE_RECEIPT.md)
and [final closure receipt](FINAL_CLOSURE_RECEIPT.md) record the checked Lean
closure and terminal obligation graph.

## 18. Paper Definitions Checked

The queueing primitives used by the six expanded targets include the finite
admission threshold, stationary distribution, expected population, private
benefit, social welfare, revenue, opportunity cost, and toll. They are
reviewed within the direct formula routes and the two selected reusable
queueing prerequisites; the source map does not select a separate definition
row.

## 19. Named Theorem Statements Checked

| Source result | Lean semantic target | Lean proof endpoint |
| --- | --- | --- |
| Equations (3)--(4) | `finiteCapacityStationaryLawSpec` | `finiteCapacityStationaryLaw` |
| Equations (5)--(11) | `stationaryPerformanceSpec` | `stationaryPerformance` |
| Equations (12)--(16) | `selfOptimizingThresholdSpec` | `selfOptimizingThreshold` |
| Equations (17)--(25) | `socialOptimalThresholdSpec` | `socialOptimalThreshold` |
| Equation (26) | `socialTollImplementsOptimalThresholdSpec` | `socialTollImplementsOptimalThreshold` |
| Equations (27)--(31) | `socialAndRevenueThresholdOrderSpec` | `socialAndRevenueThresholdOrder` |

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) contains
six current matching judgments, one for each row in Section 19. The
[human review packet](docs/HUMAN_REVIEW_PACKET.pdf) is the corresponding
reader-facing review surface.

## 21. Source-Coverage Audit Ledger

The [coverage ledger](FINAL_CLOSURE_RECEIPT.md) records two unnumbered
source items as scope exclusions. The six selected equation groups are instead
covered by the [statement map](audit/paper_statement_map.json) and
[source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md). This report
does not treat the two exclusions as proved result rows.
