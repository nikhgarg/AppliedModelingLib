# Final Validation Report: Driver Surge Pricing
Updated: 2026-09-08

## 1. Human Verdict

The incentive-compatibility, renewal-reward, and pricing results are proved on
their stated domains, and Theorem 3's conclusion has a direct proof.

## 2. Closeout Status
- Completion status: `formalized`.
- Scope: the paper's named theoretical results.
- Human review: not yet recorded.

## 3. Source and Scope
- Paper: *Driver Surge Pricing*.
- Authors: Nikhil Garg and Hamid Nazerzadeh.
- Source version: *Management Science* (2022); arXiv v4 (2021).
- Public source: https://arxiv.org/abs/1905.07544

Scope: the paper's single-state and dynamic incentive-compatibility
definitions, threshold-policy and renewal-reward material, Lemmas 1--10,
the unnumbered Proposition in Section 3.1, and Theorems 1--4. Empirical and calibration material outside
those named theoretical claims is not part of this formalization.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Driver-surge model and incentive-compatibility definitions | **Exact.** |
| Lemmas 1--3 | **Exact.** |
| Theorem 1, the unnumbered Proposition in Section 3.1, and Lemma 4 | **Exact.** |
| [Lemma 5](docs/SOURCE_CLARIFICATIONS.md#policy-domain-and-endpoint-regularity) | **Exact.** [Source clarification](docs/SOURCE_CLARIFICATIONS.md#policy-domain-and-endpoint-regularity) |
| Lemmas 6--8 and 10 | **Exact.** |
| [Lemma 9](docs/SOURCE_CLARIFICATIONS.md#theorem-3-proof-route) | **Exact.** |
| Theorem 2 | **Exact.** |
| [Theorem 3](docs/SOURCE_CLARIFICATIONS.md#theorem-3-proof-route) | **Exact.** |
| [Theorem 4](docs/SOURCE_CLARIFICATIONS.md#policy-domain-and-endpoint-regularity) | **Exact.** |

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

The [printed Lemma 9](docs/SOURCE_CLARIFICATIONS.md#theorem-3-proof-route) chooses a feasible price ratio after fixing a non-surge
policy. Its conclusion is therefore policy-dependent, whereas the Theorem 3
argument needs one price to work uniformly over deviations. The checked proof
instead fixes a structured price before optimizing and handles the target-rate
range in two cases. The theorem's conclusion and source policy domain are
unchanged. The [proof-route memo](docs/THEOREM3_SOURCE_CLARIFICATION.md) explains
the quantifier order and the direct two-case argument.

## 8. Proof Tricks Worth Reusing
None.

## 9. Generalizations, Conjectures, and Extensions
No additional generalization is established here.

## 10. Source Clarifications and Exact Readings

The [Lemma 5 memo](docs/SOURCE_CLARIFICATIONS.md#policy-domain-and-endpoint-regularity)
records its endpoint reading. The [Lemma 9/Theorem 3 memo](docs/SOURCE_CLARIFICATIONS.md#theorem-3-proof-route)
records the price-policy proof route.

## 11. Paper Issues or Caveats

None.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) exposes the incentive-compatibility
definitions, renewal formulas, Lemmas 1--10, the unnumbered Proposition in Section 3.1, and Theorems
1--4 through eighteen transparent targets. [ProofInterface.lean](ProofInterface.lean)
supplies their checked endpoints, including the fixed-price-before-policy
Theorem 3 route.

## 13. Paper Assumption Provenance

The current [paper-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md)
records thirteen matching graph-selected prerequisites. No material
reusable-library prerequisite is selected for this surface.

## 14. Displayed Formula Provenance

[The source map](audit/paper_statement_map.json) binds earning rates, switching
probability, post-exit time fractions, threshold rewards, structured prices,
and derivative/response-shape formulas to their source spans. The
[clarification memo](docs/SOURCE_CLARIFICATIONS.md) records the Lemma 5
endpoint reading.

## 15. Library Lift Pass

The development separates generic renewal-reward and policy-comparison
arguments from paper-specific driver states, prices, and response functions.
No additional shared-library extraction is claimed by the accepted graph.

## 16. DAG Audit

[The dependency DAG](docs/DependencyDAG.pdf) orders the model, renewal lemmas,
policy-shape lemmas, and four theorems. Its retained 2026-09-05 visual
inspection found the nodes and directed dependencies legible and consistent
with the reviewed surface.

## 17. Validation Checks

The current graph records sixteen matching direct source-to-Spec judgments and
thirteen matching paper prerequisites. The paper-coverage ledger separately
records thirty items covered, four as support, and two with recorded boundaries.
Section 4 gives the current source-facing interpretation. The [accepted graph](audit/obligation_evidence/current_accepted_graph.json)
and [closure receipt](FINAL_CLOSURE_RECEIPT.md) bind the formalized surface.

## 18. Paper Definitions Checked

Checked definitions include surge states, single-state and dynamic incentive
compatibility, threshold policies, measured rewards, earning rates, switching
and exit times, structured prices, and the two-state feasible policy domain.

## 19. Named Theorem Statements Checked

- Lemmas 1--4 and the unnumbered Proposition in Section 3.1: renewal/time-share identities, affine
  single-state incentive compatibility, and threshold uniqueness.
- Lemmas 5--10: policy-shape and endpoint derivative comparisons.
- Theorems 1--4: the single-state, multiplicative, structured-pricing, and full
  two-state incentive results, including the Theorem 3 quantifier repair.

## 20. Paper-Facing Statement Validator Ledger

Direct judgments are in the [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md),
row-local comparisons in the [statement ledger](FINAL_CLOSURE_RECEIPT.md),
and premise judgments in the [paper-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md).
The [source-fidelity ledger](FINAL_CLOSURE_RECEIPT.md) records the
price/policy proof change and added domains.

## 21. Source-Coverage Audit Ledger

The [coverage ledger](FINAL_CLOSURE_RECEIPT.md) distinguishes thirty
covered items, four support-only items, and two source-convention readings
across the theoretical inventory. [The source map](audit/paper_statement_map.json)
links those items to the current interface; empirical and calibration material
remains outside the selected scope.
