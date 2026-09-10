# Final Validation Report: Competitive Auctions and Digital Goods
Updated: 2026-09-09

## 1. Human Verdict

The selected auction revenue and truthfulness results are formalized.

## 2. Closeout Status

- Completion status: formalized
- One-sentence recap: The formalization covers sampling and weighted-pairing
  auctions, the revenue upper bound, and deterministic impossibility results.

## 3. Source and Scope

Goldberg, Hartline, and Wright, *Competitive Auctions and Digital Goods*.
The [public preliminary paper](https://www.cs.miami.edu/home/burt/learning/Csc597.052/docs/goldberg.pdf)
supplies the theorem numbering and selected auction models and results.
Lemma 8.1 and Theorem 8.2 use the later journal version's monotone-offer
condition, explained in the [source note](docs/SOURCE_CLARIFICATIONS.md#lemma-81-and-theorem-82).
The eight unnumbered Section 11 claims are outside the selected named-theory scope.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Theorem 4.1; Corollary 4.2; Theorems 7.1–7.2 | **Exact asymptotic bounds with domain clarification.** The finite logarithmic bounds use [largest normalized bid $h\geq2$ and, for the count bound, at least two bidders](docs/SOURCE_CLARIFICATIONS.md#logarithmic-domains). |
| Lemma 6.1 | **Exact.** |
| Exact-half sampling; bounded dual-price mechanism | **Exact with parity clarification.** [Round half-sizes down for odd inputs](docs/SOURCE_CLARIFICATIONS.md#randomization-and-bounded-supply); truthfulness and supply feasibility hold for all natural inputs, with exact halves for even inputs. |
| Theorem 6.2 | **Exact with count-parameter clarification.** The [winner-count parameter $\alpha$ is a natural number](docs/SOURCE_CLARIFICATIONS.md#randomization-and-bounded-supply); the stated probability and revenue bounds are proved for uniform half-sampling. |
| Lemma 8.1 | **Exact with the journal’s monotonicity condition.** [Allocation probability increases with the bid under the journal’s cross-bidder offer condition](docs/SOURCE_CLARIFICATIONS.md#lemma-81-and-theorem-82). |
| Theorem 8.2 | **Exact with the journal’s monotonicity condition.** [Expected revenue is at most the optimal fixed-price revenue](docs/SOURCE_CLARIFICATIONS.md#lemma-81-and-theorem-82), including arbitrary real offer distributions. |
| Theorem 9.1 | **Exact asymptotic conclusion with source clarification.** [Integer high-bid examples](docs/SOURCE_CLARIFICATIONS.md#randomization-and-bounded-supply) have $R/F\leq1/H$ and $F\geq\alpha H$, ruling out a constant competitive ratio for deterministic bid-independent auctions. |
| Lemma 9.2 | **Exact.** |
| Theorem 9.3 | **Exact asymptotic conclusion with source clarification.** [The same impossibility](docs/SOURCE_CLARIFICATIONS.md#randomization-and-bounded-supply) holds for every truthful deterministic auction in the paper’s set-of-bids model. |
| Bounded-supply rejection | **Exact with a selection-rule clarification.** If demand exceeds supply, [serve accepting bidders in a fixed order independent of their bids](docs/SOURCE_CLARIFICATIONS.md#randomization-and-bounded-supply). |

## 5. Remaining Boundaries and Gaps

None for the selected named-theory results. The eight unnumbered Section 11 claims remain outside that scope.

## 6. Additional Assumptions Beyond Paper

Lemma 8.1 and Theorem 8.2 use the [journal monotonicity condition](docs/SOURCE_CLARIFICATIONS.md#lemma-81-and-theorem-82) described in Section 10.

## 7. Proof-Strategy Deviations

The journal's inverse-CDF construction is read as the lower generalized
inverse, which handles jumps in the offer distribution. The
[source note](docs/SOURCE_CLARIFICATIONS.md#lemma-81-and-theorem-82) explains
why this preserves the marginals and revenue argument.

## 8. Proof Tricks Worth Reusing

Couple different offer distributions using one uniform random variable to compare their total expected revenue with a fixed-price benchmark.

## 9. Generalizations, Conjectures, and Extensions

The formalization additionally proves explicit finite bounds for the asymptotic results.

## 10. Source Clarifications and Exact Readings

The [memo](docs/SOURCE_CLARIFICATIONS.md) gives the logarithmic domains,
journal monotonicity condition, count and parity conventions, and integer
examples for the impossibility results.

The concrete randomized mechanisms use finite distributions; the general
auction model allows countable distributions. [Theorem 8.2 separately covers
arbitrary real offer distributions](docs/SOURCE_CLARIFICATIONS.md#randomization-and-bounded-supply).
The bounded dual-price competitive guarantee is conditional on the stated
sampling good-event bounds; the parity convention alone supplies no new
odd-input revenue guarantee.

## 11. Paper Issues or Caveats

The journal condition narrows the preliminary version’s claim about all truthful auctions; see Section 10. The remaining notes clarify domains and conventions.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) states the selected results and
[ProofInterface.lean](ProofInterface.lean) supplies their proofs. The selected
surface contains 37 model and definition items and 12 result contracts.

## 13. Paper Assumption Provenance

The [assumption ledger](FINAL_CLOSURE_RECEIPT.md) records the eight
paper conditions listed in [status.json](status.json), including the journal
monotone-offer condition.

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) links revenue, benchmark,
sampling, and bounded-supply formulas to their source passages and formal
statements.

## 15. Library Lift Pass

The real-distribution inverse-CDF argument supplies reusable probability
results. Auction benchmarks and source-specific mechanisms remain paper-local.

## 16. DAG Audit

The [dependency diagram](docs/DependencyDAG.pdf), generated from
[its source](docs/DependencyDAG.tex), shows how the auction model and benchmarks
support the revenue, sampling, and deterministic lower bounds. It was rendered
and visually checked on 2026-09-08.

## 17. Validation Checks

The [focused-build receipt](FINAL_CLOSURE_RECEIPT.md),
[import-closure receipt](FINAL_CLOSURE_RECEIPT.md), and
[closeout record](FINAL_CLOSURE_RECEIPT.md) record validation for their pinned
mathematical inputs.

## 18. Paper Definitions Checked

Checked definitions cover auction outcomes, truthfulness, bidder profit,
revenue and benchmarks, bid-independent and sampling mechanisms, and
unlimited- and bounded-supply models. The [statement map](audit/paper_statement_map.json)
records their source connections.

## 19. Named Theorem Statements Checked

Section 4 lists the selected named results using the preliminary paper's
numbering. The grouped first row covers the logarithmic revenue bounds;
Theorem 7.2 includes both the guarantee and its tightness construction.

## 20. Paper-Facing Statement Validator Ledger

The [source-to-statement review](FINAL_CLOSURE_RECEIPT.md)
contains six direct matches and six corrected-target matches for the 12 result
contracts. The [paper-model review](FINAL_CLOSURE_RECEIPT.md)
contains 73 prerequisite judgments. Their reader-facing interpretation is
summarized in Section 4.

## 21. Source-Coverage Audit Ledger

The 59-entry [statement map](audit/paper_statement_map.json) contains 49
selected source items, eight unnumbered Section 11 claims outside the selected
scope, and two proof-support entries.
