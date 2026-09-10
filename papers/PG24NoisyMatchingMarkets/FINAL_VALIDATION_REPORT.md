# Final Validation Report: Wisdom and Foolishness of Noisy Matching Markets

Updated: 2026-09-09

## 1. Human Verdict

The paper’s noise-attenuation and noise-amplification results are formalized.
The appendix’s one-draw tail estimates use a finite second moment, as detailed
below.

## 2. Closeout Status

- Completion status: formalized
- One-sentence recap: The four main theorems and their selected appendix
  results are proved under the stated conditions.

## 3. Source and Scope

The source is [*Wisdom and Foolishness of Noisy Matching Markets*](https://arxiv.org/abs/2402.16771) by Kenny Peng and Nikhil Garg. The checked source surface includes the basic and extended-coalition economies; value-law and capacity regularity; beta-max-concentrating and long-tailed noise; cutoff stability and match probability; Theorems 1--4; and the named appendix propositions and lemmas supporting them. Simulations, figures, examples, and narrative interpretation are outside this mathematical scope.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Theorems 1--4 [with the appendix proof corrections](docs/SOURCE_CLARIFICATIONS.md#other-appendix-proof-corrections) | **Exact.** |
| [Appendix Proposition 1](docs/SOURCE_CLARIFICATIONS.md#appendix-proposition-1-lower-tail-orientation-and-polynomial-rate), with its [one-draw rate condition](docs/SOURCE_CLARIFICATIONS.md#appendix-propositions-7ii-and-8-one-draw-chebyshev-condition) | **Exact after correcting the tail typo, under an additional regularity condition.** The polynomial lower-tail rate uses a finite second moment for one noise draw. |
| [Appendix Propositions 2 and 5; Appendix Lemma 6](docs/SOURCE_CLARIFICATIONS.md#other-appendix-proof-corrections) | **Exact after correcting typos.** The intermediate algebra and probability calculations are corrected. |
| [Appendix Proposition 3](docs/SOURCE_CLARIFICATIONS.md#appendix-propositions-3-and-4-the-high-cutoff-block-at-the-pivot) | **Exact after correcting the block-endpoint typo.** The high-cutoff block includes the pivot. |
| [Appendix Proposition 4](docs/SOURCE_CLARIFICATIONS.md#appendix-propositions-3-and-4-the-high-cutoff-block-at-the-pivot) | **Exact after correcting the block-endpoint typo.** The high-cutoff block includes the pivot. |
| Appendix Proposition 7(i) | **Exact.** |
| [Appendix Proposition 7(ii)](docs/SOURCE_CLARIFICATIONS.md#appendix-propositions-7ii-and-8-one-draw-chebyshev-condition) | **Exact under an additional regularity condition.** The near-one rate uses a finite second moment for one noise draw. |
| [Appendix Proposition 8](docs/SOURCE_CLARIFICATIONS.md#appendix-propositions-7ii-and-8-one-draw-chebyshev-condition) | **Exact under an additional regularity condition.** The lower-tail integral rate uses the same finite-second-moment condition. |
| [Appendix Proposition 9; Appendix Lemmas 11--13](docs/SOURCE_CLARIFICATIONS.md#other-appendix-proof-corrections) | **Exact.** |
| [Appendix Propositions 10, 14, and 15](docs/SOURCE_CLARIFICATIONS.md#appendix-propositions-10-14-and-15-actual-affordance-probabilities-and-local-inputs) | **Exact with source clarification.** |
| [Coalition conditional laws](docs/SOURCE_CLARIFICATIONS.md#coalition-conditional-laws) | **Exact.** |

## 5. Remaining Boundaries and Gaps

No proof gap remains in the selected scope. The additional condition for
three appendix results is stated in Section 6.

## 6. Additional Assumptions Beyond Paper

Appendix Proposition 1, Appendix Proposition 7(ii), and Appendix Proposition 8 use the explicit finite-second-moment condition for one iid noise draw. It supplies the one-draw Chebyshev calculation; beta-max concentration by itself controls maxima rather than this single-draw quantity. The [source clarifications](docs/SOURCE_CLARIFICATIONS.md#appendix-propositions-7ii-and-8-one-draw-chebyshev-condition) give the result-level scope. No additional condition is used for the four main theorem statements.

## 7. Proof-Strategy Deviations

The appendix proofs use corrected capacity algebra, event inclusions, natural-number rounding, atom-safe tails, and a finite long-tail-shift bridge for the all-real amplification conclusion. These repairs preserve the displayed conclusions; their result-level descriptions are in the [source clarifications](docs/SOURCE_CLARIFICATIONS.md).

## 8. Reusable Formal Infrastructure

The development uses reusable probability, finite-product, order-statistic, and cutoff-market infrastructure. It adds a reusable one-sided Chebyshev lower-tail bound for a real probability law with finite second moment; market-specific cutoff geometry and source corrections remain paper-local.

## 9. Generalizations, Conjectures, and Extensions

None.

## 10. Source Clarifications and Exact Readings

The [source clarifications](docs/SOURCE_CLARIFICATIONS.md) give the source anchors, corrected formulas, and result-level effects for every material correction or added condition in this report.

## 11. Paper Issues or Caveats

The three appendix rates above are formalized under the stated one-draw finite-second-moment condition. The source corrections do not alter the economic primitives or the main theorem conclusions.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) states the paper-facing results and [ProofInterface.lean](ProofInterface.lean) proves their endpoints. The [human review packet](docs/HUMAN_REVIEW_PACKET.pdf) presents the source statements, formalized targets, and proof endpoints together.

## 13. Paper Assumption Provenance

The basic and coalition market models, regularity conditions, noise conditions, cutoff characterization, and match-probability formula are checked directly against the source. The finite one-draw moment used by the three corrected appendix rates is described in Section 6.

## 14. Displayed Formula Provenance

The [source map](audit/paper_statement_map.json) records each selected result's source anchor and transparent paper-facing target. The [source clarifications](docs/SOURCE_CLARIFICATIONS.md) identify every material corrected formula.

## 15. Library Lift Pass

The reusable lower-tail Chebyshev inequality supports the paper's one-draw rate argument. Other probability and matching tools are ordinary reusable foundations; no external Lean formalization was imported.

## 16. DAG Audit

[DependencyDAG.tex](docs/DependencyDAG.tex) and [DependencyDAG.pdf](docs/DependencyDAG.pdf) organize the source models, named appendix results, and four main theorems without implementation-helper nodes. The rendered DAG was visually inspected for labels, arrowheads, reading order, and node or edge overlap.

## 17. Validation Checks

The closeout checks the complete paper-owned Lean module surface, each transparent source-to-Spec target, its proof endpoint, its prerequisite surface, and the absence of untrusted proof boundaries. The [closure receipt](FINAL_CLOSURE_RECEIPT.md) records the final accepted graph.

The targeted closeout command is `python3 scripts/run_paper_closeout.py --paper PG24NoisyMatchingMarkets` with the planner-issued identity.

## 18. Paper Definitions Checked

Checked definitions include the two market models, regularity and noise conditions, stable cutoffs, match probability, attenuation and amplification events, coalition value laws, and the finite rounding constructions used in the appendices.

## 19. Named Theorem Statements Checked

- Theorems 1--4: attenuation, amplification, and their coalition versions.
- Attenuation appendix: Proposition 1; Propositions 2--5; Lemma 6; and Propositions 7--8.
- Amplification appendix: Propositions 9--10; Lemmas 11--13; and Propositions 14--15.

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) records the independent direct reviews; the [paper-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) records the paper-model reviews; and [source-proof fidelity](FINAL_CLOSURE_RECEIPT.md) records the source corrections.

## 21. Source-Coverage Audit Ledger

The [source map](audit/paper_statement_map.json) retains the selected named result inventory, byte-pinned source anchors, and their transparent formalized targets.
