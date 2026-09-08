# Final Validation Report: LG21 Test-Optional Policies

Updated: 2026-09-06

## 1. Human Verdict

The fairness and policy results are proved on the stated policy domains.

**Formalization gap:** Theorem 3.1 assumes stability against profitable group entry; voluntary Lemma 4.1 assumes maximal participation. Deriving these refinements from the paper’s equilibrium definition remains unproved.
[Details](docs/SOURCE_CLARIFICATIONS.md#equilibrium-timing-population-laws-and-active-branches).

## 2. Closeout Status

- Completion status: formalized.
- Scope: fifteen selected theoretical claims.
- Human review: no annotations recorded.

## 3. Source and Scope

- Paper: *Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps* (Liu and Garg, EAAMO 2021).
- Source version: [arXiv:2107.08922](https://arxiv.org/pdf/2107.08922), byte-pinned in `cited publication` with SHA-256 `11fb7a52959948847ce19d85adf97256a30c3f1575941ff6efec0e33bf908e1c`.
- Normal scope: named theoretical results and independently stated claim-level conditions they use. Simulations, examples, figures, proof narration, and standalone explanatory prose remain outside that scope.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Fairness definitions and implications; score-ignoring policy | **Exact.** |
| [Theorem 3.1](docs/SOURCE_CLARIFICATIONS.md#equilibrium-timing-population-laws-and-active-branches) | **Formalization gap:** assume stability against profitable group entry with recalibrated school estimates; deriving this from source equilibrium remains unproved. Necessity is unknown. |
| [Theorem 3.2](docs/SOURCE_CLARIFICATIONS.md#theorem-32-policy-scope-and-operational-blankness) | **Restricted scope:** deterministic reported output; the memo’s randomized counterexample refutes the unrestricted conclusion. Determinism is sufficient, not shown necessary. |
| [Theorem 3.2 summary](docs/SOURCE_CLARIFICATIONS.md#theorem-32-policy-scope-and-operational-blankness) | **Typo fixed:** “demographic” becomes “observable,” matching the argument. |
| [Lemma 4.1, voluntary regimes](docs/SOURCE_CLARIFICATIONS.md#equilibrium-timing-population-laws-and-active-branches) | **Formalization gap:** select self-enforcing participation that no admissible candidate can strictly enlarge. The source equilibrium definition has not been shown to imply this selection; necessity is unknown. |
| Proposition 4.2 | **Exact:** the Gaussian observed-score model allows any base-only policy for students without access. |
| [Proposition 4.3](docs/SOURCE_CLARIFICATIONS.md#lemma-41-and-proposition-43-calculations) | **Exact conclusion:** an unfair equilibrium in each regime refutes fairness, which the paper requires in every equilibrium. The variance comparison uses a direct calculation; voluntary equilibria use the Lemma 4.1 convention. |
| [Lemma 4.1 cutoff](docs/SOURCE_CLARIFICATIONS.md#lemma-41-and-proposition-43-calculations) | **Typo fixed:** `c=(qtilde-intercept)/slope` on the positive-slope domain. |
| [Theorem 4.4 and its reporting-conditioned generalization](docs/SOURCE_CLARIFICATIONS.md#equilibrium-timing-population-laws-and-active-branches) | **Exact for mandatory participation; restricted voluntary equilibria:** the latter use the same maximal-participation selection as Lemma 4.1. Necessity is unknown. |

## 5. Remaining Boundaries and Gaps

Theorem 3.1’s stability against recalibrated group entry and the voluntary Lemma 4.1 [maximal-participation restriction](docs/SOURCE_CLARIFICATIONS.md#equilibrium-timing-population-laws-and-active-branches) are not derived from the paper’s equilibrium definition. The corresponding conclusions for arbitrary source equilibria remain unproved. Selected equilibria do exist; the gap is extending the conclusions to the source equilibrium class.

The fixed-point argument also retains the analytic premises described in the [memo](docs/SOURCE_CLARIFICATIONS.md#theorem-31-nonreport-mixture-and-fixed-point); their source-model derivation remains open.

## 6. Additional Assumptions Beyond Paper

[Theorem 3.2](docs/SOURCE_CLARIFICATIONS.md#theorem-32-policy-scope-and-operational-blankness) restricts reported output to be deterministic; its randomized example shows that some restriction is needed, but not that determinism is necessary. The access law uses independence from the skill/noise block, beyond uncorrelated-access wording; necessity under the complete source model is unresolved. The equilibrium proof gaps have their main discussion in [Section 5](#5-remaining-boundaries-and-gaps).

## 7. Proof-Strategy Deviations

The [Theorem 3.1 nonreport-mixture correction](docs/SOURCE_CLARIFICATIONS.md#theorem-31-nonreport-mixture-and-fixed-point) and [Proposition 4.3 unconditional-variance calculation](docs/SOURCE_CLARIFICATIONS.md#lemma-41-and-proposition-43-calculations) are detailed in the memo.

## 8. Proof Tricks Worth Reusing

- Keep attained positive-mass branches separate from arbitrary conditional-law versions on null events.
- State each source claim once as a transparent specification, then prove that exact proposition through internal lemmas.
- Keep the pre-score taking choice distinct from the post-score reporting choice.

## 9. Generalizations, Conjectures, and Extensions

The positive-mass active-branch framework may be useful beyond Gaussian signals. No broader posterior calculation or unproved generalization is claimed here.

## 10. Source Clarifications and Exact Readings

The [memo](docs/SOURCE_CLARIFICATIONS.md) gives the nonreport-mixture and
[cutoff correction](docs/SOURCE_CLARIFICATIONS.md#lemma-41-and-proposition-43-calculations), the randomized-policy example and checked operational
blankness conclusion, and the unconditional Gaussian variance calculation.

## 11. Paper Issues or Caveats

The equilibrium coverage gaps are in Section 5. Section 6 distinguishes the supported randomized-output obstruction from conditions whose necessity is unknown.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) supplies the 15 selected transparent
source-facing result specifications, and [ProofInterface.lean](ProofInterface.lean)
supplies the corresponding checked endpoints. The selected surface covers the
fairness implication, hidden- and observed-access protocols, optional and
required reporting schedules, Theorems 3.1--3.2 and 4.4, and the
reporting-conditioned supporting claims.

## 13. Paper Assumption Provenance

The fifteen [paper prerequisites](FINAL_CLOSURE_RECEIPT.md)
and one [library prerequisite](FINAL_CLOSURE_RECEIPT.md) match
their selected source connections. Result-specific assumptions and the
equilibrium restrictions remain visible in the transparent specifications
and Sections 4–6.

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) routes the paper's access,
signal, reporting, fairness, cutoff, and equilibrium formulas, including 19
formula presentations and two equation presentations. The four clarified
Theorem 3.2 targets are identified in the
[source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) and explained
in the [source clarification memo](docs/SOURCE_CLARIFICATIONS.md).

## 15. Library Lift Pass

The reusable Gaussian signal-family primitive is source-screened in the
[library ledger](FINAL_CLOSURE_RECEIPT.md). Paper-specific
equilibrium, policy, access, reporting, and fairness statements remain in the
paper layer.

## 16. DAG Audit

[DependencyDAG.pdf](docs/DependencyDAG.pdf), generated from
[DependencyDAG.tex](docs/DependencyDAG.tex), distinguishes the source model,
hidden-access and observed-access result families, the reporting-conditioned
generalization, and open directions. The rendered PDF was visually inspected
for readability and arrow/box overlap.

## 17. Validation Checks

The [focused-build receipt](FINAL_CLOSURE_RECEIPT.md) records the
paper build, and the [import-closure receipt](FINAL_CLOSURE_RECEIPT.md)
records its Lean dependencies. The [closeout record](FINAL_CLOSURE_RECEIPT.md)
records acceptance evidence for its pinned inputs.

## 18. Paper Definitions Checked

The checked definitions cover access actions and observation regimes, the
hidden-access optional protocol, latent-skill, observable, demographic, and
test-blank fairness, the access estimator, distributional equality,
requirement policies, school information, the Gaussian student signal model,
and the cutoff and local-candidate models used by Theorems 3.1--3.2. Exact
routes are in the [statement map](audit/paper_statement_map.json).

## 19. Named Theorem Statements Checked

| Source presentation | Transparent specification | Proof endpoint |
| --- | --- | --- |
| Fairness implication chain | `fairness_implication_chainSpec` | `fairness_implication_chain_proof` |
| Lemma 4.1 | `lemma4_1_observed_access_strategy_proofness_source_coreSpec` | `lemma4_1_observed_access_strategy_proofness_source_core_proof` |
| Proposition 4.2 | `proposition4_2_all_observed_access_requirement_protocols_source_coreSpec` | `proposition4_2_all_observed_access_requirement_protocols_source_core_proof` |
| Proposition 4.3 | `proposition4_3_each_requirement_protocol_has_unfair_pbo_equilibriumSpec` | `proposition4_3_each_requirement_protocol_has_unfair_pbo_equilibrium_proof` |
| Reporting-conditioned generalization | `reporting_conditioned_generalizationSpec` | `reporting_conditioned_generalization_proof` |
| Theorem 3.1: fairness failure | `theorem3_1_hidden_access_pbo_fails_all_fairness_definitionsSpec` | `theorem3_1_hidden_access_pbo_fails_all_fairness_definitions_proof` |
| Theorem 3.1: optional reporting | `theorem3_1_optional_reporting_source_timedSpec` | `theorem3_1_optional_reporting_source_timed_proof` |
| Theorem 3.1: reporting required | `theorem3_1_report_required_source_timedSpec` | `theorem3_1_report_required_source_timed_proof` |
| Theorem 3.2: optional schedule | `theorem3_2_optional_reporting_clarified_modelSpec` | `theorem3_2_optional_reporting_clarified_model_proof` |
| Theorem 3.2: report-required schedule | `theorem3_2_report_required_clarified_modelSpec` | `theorem3_2_report_required_clarified_model_proof` |
| Theorem 4.4 | `theorem4_4_all_observed_access_requirement_protocolsSpec` | `theorem4_4_all_observed_access_requirement_protocols` |
| Threshold acceptance interpretation | `thompson_acceptance_interpretationSpec` | `thompson_acceptance_interpretation_proof` |
| Report-rule skill independence | `report_decision_skill_independenceSpec` | `report_decision_skill_independence_proof` |
| Ignoring-test-scores witness | `ignoring_test_scores_achieves_fairnessSpec` | `ignoring_test_scores_achieves_fairness_proof` |
| Theorem 3.2 observable summary | `theorem3_2_observable_summary_clarifiedSpec` | `theorem3_2_observable_summary_clarified_proof` |

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) contains
15 current judgments: 12 matches and three corrected-target matches
for the clarified Theorem 3.2 rows. The
[human review packet](docs/HUMAN_REVIEW_PACKET.pdf) presents the same selected
claim surface.

## 21. Source-Coverage Audit Ledger

The [statement map](audit/paper_statement_map.json) retains 81 source items,
including supporting model and formula presentations. Fifteen result claims,
fifteen paper prerequisites, and one library prerequisite form the current
selected semantic comparison; the same source scope appears in the packet.
