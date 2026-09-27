# Final Validation Report: Distortion of AI Alignment: Does Preference Optimization Optimize for Preferences?

Updated: 2026-09-27

## 1. Human Verdict

The population and finite-sample bounds, lower-bound constructions, and policy
equivalences are proved on their stated domains. Theorem 6's exponential claim
is checked as an explicit large-temperature tail over a sequence of finite
instances, as its Appendix F.2 construction requires.

## 2. Closeout Status

- Completion status: formalized.

The formalization covers all fifteen named results and the Appendix F.3
DPO–RLHF equivalence, with the source clarifications and formula corrections below.

## 3. Source and Scope

The source is Paul Gölz, Nika Haghtalab, and Kunhe Yang,
[*Distortion of AI Alignment: Does Preference Optimization Optimize for
Preferences?*](https://arxiv.org/abs/2505.23749), NeurIPS 2025.

The governing source is the published conference version. The scope covers
Lemmas 1, 10, 11, and 15; Theorems 2, 3, 5, 6, 7, 9, and 12;
Corollaries 4 and 8; and Propositions 13 and 14. It also records the empirical
and population Borda definitions and the constrained RLHF and NLHF definitions.
Theorem 12 is the appendix formulation of Theorem 5; the table groups their
shared conclusion. Appendix F.3's DPO–RLHF equivalence is included separately.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Lemma 1; population Theorem 2 | **Exact.** |
| Finite-sample Theorem 2; Lemmas 10–11 | **Exact with source clarification.** An alternative with no sampled comparisons receives empirical Borda score zero. [Convention](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#empirical-borda-finite-zero-incidence-convention). |
| Theorem 3 | **Exact.** |
| Corollary 4 | **Exact with source clarification.** A pair with no sampled comparisons receives neutral margin zero. [Convention](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#corollary-4-finite-zero-incidence-convention). |
| Theorems 5 and 12 | **Exact supremum conclusion with source clarification:** strict sub-bounds from the parameterized construction replace an asserted maximum on an open interval. [Reading](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#theorem-5-and-theorem-12-optimization-notation). |
| Theorem 6 | **Exact with source clarification.** The number of alternatives grows with temperature along the sequence used to prove the exponential lower bound, as in Appendix F.2. [Reading](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#theorem-6-sequence-size). |
| Theorem 7; Corollary 8 | **Exact.** |
| Theorem 9 | **Exact.** |
| Proposition 13 | **Exact after correcting the KL sign:** the minimizing player has a positive KL penalty; constrained/regularized equivalence includes infinite weight. [Sign](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#proposition-13-kl-sign). |
| Proposition 14 | **Exact.** |
| Appendix F.3 | **Exact after restoring the normalization:** normalize the exponential tilt in the DPO–RLHF equivalence. [Formula](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#appendix-f3-dporlhf-equivalence). |
| Lemma 15 | **Exact.** |

## 5. Clarified Conditions and Source Corrections

No formalization gap remains in the selected scope. The [memo](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md)
explains the source clarifications and localized formula corrections in the table.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

Theorem 6 uses an explicit copy count and finite-likelihood argmax stability
in place of the Appendix F.2 arithmetic shortcuts. The [construction note](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#theorem-6-proof-arithmetic)
gives the repaired estimates and finite construction.

## 8. Proof Tricks Worth Reusing

- Keep the user population, alternative sampler, reference policy, and
  response dependence as separate typed objects.
- Convert population linearization into policy welfare bounds by finite PMF
  expectation rather than by a representative-user shortcut.
- Prove exact finite constants first; use them to discharge big-O source
  displays without introducing an asymptotic axiom.
- Compact finite-likelihood control plus strict population gaps gives an
  explicit route from literal iid reports to eventual MLE ordering.
- Finite KL duality handles both constrained/regularized directions and makes
  the zero-budget boundary visible.

## 9. Generalizations, Conjectures, and Extensions

The formalization additionally proves explicit finite bounds. For Theorem 6,
it supplies a concrete construction on the tail $\beta\geq10$, with
$m(\beta)\geq3$, establishing the source's asymptotic lower bound.

## 10. Source Clarifications and Corrections

The [memo](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md) records the
open-interval optimization reading, Proposition 13 KL sign, missing DPO/RLHF
normalizer, and the zero-incidence Borda and Maximal-Lotteries conventions.
Theorem 6's construction is discussed in Sections 7 and 9.

## 11. Paper Issues or Caveats

The localized corrections are listed in the result table and explained in the
memo linked in Section 10. No additional issue is recorded.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) presents 16 direct source contracts
as transparent targets: 15 named results and the corrected Appendix F.3
equivalence. [ProofInterface.lean](ProofInterface.lean) supplies one checked
endpoint for each target. Source definitions are reviewed through the
paper-local and library prerequisite ledgers rather than duplicated as result
claims.

## 13. Paper Assumption Provenance

[Assumptions.lean](Assumptions.lean) introduces no paper-local axiom. The 17
paper-local prerequisites and 11 reusable-library prerequisites all match
their selected source connections in the
[paper prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) and
[library ledger](FINAL_CLOSURE_RECEIPT.md).

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) routes the population
utility, Bradley--Terry, KL-policy, Borda, RLHF, NLHF, and distortion formulas
and definitions. The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md)
records direct matches for all 16 selected result targets. The Appendix F.3
normalization is explained in the
[source clarification memo](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md).

## 15. Library Lift Pass

Reusable components include finite population and policy welfare,
heterogeneous Bradley--Terry comparisons, Borda scores, policy-comparison
margins, finite KL balls and duality, constrained preference games, finite iid
concentration, pairwise MLE existence and stability, and correlated
Bradley--Terry fitting. Paper numbering and the explicit lower-bound
constructions remain paper-local.

## 16. DAG Audit

[DependencyDAG.tex](docs/DependencyDAG.tex) places source models and Appendix
support before the main results that consume them, distinguishes main-text and
Appendix nodes, and shows the Theorem 7-to-Corollary 4, Appendix F.3, and
Proposition 13/Theorem 7-to-Corollary 8 routes. The rendered
[DependencyDAG.pdf](docs/DependencyDAG.pdf) was visually inspected for readable
labels, correct arrow direction, and non-overlapping boxes and edges.

## 17. Validation Checks

The [focused-build receipt](FINAL_CLOSURE_RECEIPT.md) records a passing
paper-interface build. The [import-closure receipt](FINAL_CLOSURE_RECEIPT.md)
and [final closure receipt](FINAL_CLOSURE_RECEIPT.md) record the checked
dependency closure and terminal graph.

## 18. Paper Definitions Checked

The reviewed definitions cover the population utility and Bradley--Terry
comparison models, KL-constrained policies, empirical and population Borda
scores, RLHF and NLHF objectives, social-choice distortion, maximal lotteries,
and alignment distortion. Exact declaration bodies and routes are in the
[statement map](audit/paper_statement_map.json) and the two prerequisite
ledgers.

## 19. Named Theorem Statements Checked

| Source result | Transparent semantic target | Checked proof endpoint |
| --- | --- | --- |
| Lemma 1 | `lemma1Spec` | `lemma1_linearization` |
| Theorem 2 | `theorem2Spec` | `theorem2_borda_distortion` |
| Theorem 3 | `theorem3Spec` | `theorem3_voting_rule_lower_bound` |
| Corollary 4 | `corollary4Spec` | `corollary4_maximal_lottery` |
| Theorem 5 | `theorem5Spec` | `theorem5_borda_lower_bound` |
| Theorem 12 | `theorem12Spec` | `theorem12_borda_lower_bound` |
| Theorem 6 | `theorem6Spec` | `theorem6_rlhf_distortion` |
| Theorem 7 | `theorem7Spec` | `theorem7_nlhf_distortion` |
| Corollary 8 | `corollary8Spec` | `corollary8_regularized_nlhf` |
| Theorem 9 | `theorem9Spec` | `theorem9_correlated_sampling_unbounded` |
| Lemma 10 | `lemma10Spec` | `lemma10_empirical_win_rate_concentration` |
| Lemma 11 | `lemma11Spec` | `lemma11_borda_concentration` |
| Proposition 13 | `proposition13Spec` | `proposition13_nlhf_equivalence` |
| Proposition 14 | `proposition14Spec` | `proposition14_rlhf_equivalence` |
| Lemma 15 | `lemma15Spec` | `lemma15_infinite_sequence` |
| Appendix F.3 equivalence | `appendixF3DpoRlhfEquivalenceSpec` | `appendixF3_dpo_rlhf_equivalence` |

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) contains
16 current matching judgments, one per row in Section 19. The
[human review packet](docs/HUMAN_REVIEW_PACKET.pdf) is the corresponding
reader-facing review surface.

## 21. Source-Coverage Audit Ledger

The [coverage ledger](FINAL_CLOSURE_RECEIPT.md) contains 19 covered
source items. The broader [statement map](audit/paper_statement_map.json)
retains 33 result, model, definition, and supporting-claim entries with their
route assignments.
