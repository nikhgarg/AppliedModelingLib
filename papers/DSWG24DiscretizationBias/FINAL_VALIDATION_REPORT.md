# Final Validation Report: DSWG24 Discretization Bias

Updated: 2026-09-07

## 1. Human Verdict

The formalization proves the zero-information, perfect-classifier, and
calibrated argmax-bias results, the tightness example, and the joint-decision
and optimization results. The standard event form of
calibration used in Theorem 1(iii) is recorded in the
[calibration reading](docs/SOURCE_CLARIFICATIONS.md#theorem-1iii-calibration-reading).

## 2. Closeout Status

- Completion status: formalized.
- Selected mathematical scope: Theorems 1–2, their model
  premises, and Appendix B.1 proof support.
- Empirical results and implementation code are outside the theorem targets.

## 3. Source and Scope

- Paper: *Addressing Discretization-Induced Bias in Demographic Prediction*.
- Authors: Evan Dong, Aaron Schein, Yixin Wang, and Nikhil Garg.
- Source version: ACM FAccT 2024 / PNAS Nexus 2025 published version.

The source inventory retains the main definitions, Equations (1)–(33),
Theorems 1–2, and Appendix B.1 proof support. Empirical results and
implementation code are not formal theorem targets.

- Public source: [arXiv:2405.16762](https://arxiv.org/pdf/2405.16762).

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Theorem 1(i)–(ii); Theorem 1(iii) tightness example | **Exact.** |
| Theorem 1(iii) general bound | **Exact.** Calibration uses the [standard score-event reading](docs/SOURCE_CLARIFICATIONS.md#theorem-1iii-calibration-reading) intended by the source proof. |
| Theorem 2(i)–(ii) | **Exact.** The source model and the formal statements both assume at least two labels. |
| [Theorem 2(iii), weighted clause](docs/SOURCE_CLARIFICATIONS.md#theorem-2iii-weighted-objective-wording) | **Statement clarified:** an optimal independent rule must agree almost surely with argmax; the proof also covers `gamma=0`. [Exact wording](docs/SOURCE_CLARIFICATIONS.md#theorem-2iii-weighted-objective-wording). |

## 5. Remaining Boundaries and Gaps

None for the configured theoretical scope. Empirical results and implementation
code are not formal theorem targets.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

The direct proof of Theorem 1(iii) uses the standard score-event form of
calibration; the [proof-route note](docs/SOURCE_CLARIFICATIONS.md#theorem-1iii-calibration-reading)
records the source reading and the direct inequality route.

## 8. Proof Tricks Worth Reusing

Separate transparent atomic proposition specifications from proof theorems,
and expose the dataset-dependent reference family directly before lifting a
one-sample improvement into an expected-fidelity statement.

## 9. Generalizations, Conjectures, and Extensions

No additional generalization is claimed by this closeout.

## 10. Source Clarifications and Exact Readings

Theorem 1(iii) uses the [standard score-event calibration identity](docs/SOURCE_CLARIFICATIONS.md#theorem-1iii-calibration-reading)
intended by the source proof.

Theorem 2(iii)'s weighted claim is read as: for `0<=gamma<1`, an independent
maximizer must agree almost surely with argmax. This neither requires
`gamma=1` for an agreeing rule nor asserts that agreement is sufficient for
optimality; see the [exact wording note](docs/SOURCE_CLARIFICATIONS.md#theorem-2iii-weighted-objective-wording).

<!-- BEGIN GENERATED SETTLED REVIEW CONTEXT -->
<!-- settled-review-context-sha256: 39238d334f8ea4ab69e81489bbdd2e3e3a0dae06309092adc5cf1b76418b73e9 -->
<!-- settled-review-context-presentation-sha256: 586908814402212e29be7b02a67990c4a302b9f95eaaddecad9625ef132cd516 -->
### Source readings and additional assumptions

- Calibration uses the standard conditional-expectation event identity intended by the source proof.
<!-- END GENERATED SETTLED REVIEW CONTEXT -->

## 11. Paper Issues or Caveats

The [Pareto vocabulary note](docs/SOURCE_CLARIFICATIONS.md#pareto-optimal-terminology)
separates the uncredited definition correspondence from the checked
Theorem 2(iii) comparisons.

## 12. Detailed Formalization Evidence

Canonical audit source:

- path: `publication text;
- line count: 2,379;
- SHA-256: `2370832850d19fc3e0b74c5471316b099bcab9f958c268ffcd9de9d38ef55295`.

The cited publication is the source reference for these anchors.txt` has SHA-256
`ab554d513936d2b898b72f87e2f70674ce12737065b04591a5a00c371a6fb5cf`
and a different line layout. It was not overwritten.

The selected `PaperInterface.lean` surface contains nine source-facing
specifications: the dataset-dependent reference-family definition and eight
result endpoints. The source map also retains displayed equations and Appendix
B.1 support without counting them as current direct judgments.

## 13. Paper Assumption Provenance

The current paper-prerequisite ledger contains eleven checked source/model
bindings: `bayesOptimal`, `datasetMostLikelyClass`, `isArgmaxRule`,
`calibrated`, `formalIndependentRule`, `isIndependentRule`, `isThompsonSamplingRule`,
`isTieBrokenArgmaxRule`, `maximizesEquation1`, `posteriorSimplex`, and
`referenceDistribution`. The selected result Specs retain the source
probability, posterior, support, finite-domain, and iid premises explicitly.

## 14. Displayed Formula Provenance

The [source map](audit/paper_statement_map.json) inventories Equations (1)–(33),
including the positive-support bias identities and the dataset-dependent
reference family. Intermediate proof equations remain source support; their
presence does not create an additional theorem judgment.

## 15. Library Lift Pass

The current semantic-review ledger has eleven paper prerequisites and no separate
library-prerequisite judgment rows. Reusable finite-probability and iid-event
infrastructure remains shared, while the policy modification and exact
reference-family statements stay paper-local.

## 16. DAG Audit

`docs/DependencyDAG.pdf` is generated from the current TeX source. It shows the
nine selected direct routes and records the source model's `K ≥ 2` premise for
Theorem 2(i)–(ii).
The rendered DAG was visually inspected on September 7, 2026; its labels and
arrows are legible and unclipped.

## 17. Validation Checks

The current non-accepting Lean graph has nine selected specifications, nine proof
contracts, forty-six paper declaration dependencies, and fourteen library declaration
dependencies. The current [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md)
contains nine matching judgments. The
[paper-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) contains
eleven matching judgments, and the
[library-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) contains none.
No semantic judgment was issued by this documentation refresh.

## 18. Paper Definitions Checked

The selected direct definition is the source dataset-dependent augmented
reference family `P_N^q`. The eleven current prerequisite judgments cover the
classifier, decision-rule, posterior-simplex, reference-simplex, and objective
predicates used by the selected results. Other retained definitions and
formulas remain visible as source context or proof support.

## 19. Named Theorem Statements Checked

The current direct result surface consists of Theorem 1(i), Theorem 1(ii), the
Theorem 1(iii) general bound and tightness witness, Theorem 2(i), Theorem 2(ii),
and two independently checkable clauses of Theorem 2(iii).

## 20. Statement Review Evidence

| Selected source item | Source-facing specification | Judgment |
| --- | --- | --- |
| `sourcePNq` | `nontrivial_reference_family_definitionSpec` | matches |
| `theorem1i_no_information_bias` | `theorem1i_no_information_biasSpec` | matches |
| `theorem1ii_prior_reference_zero_bias` | `theorem1ii_perfect_classifier_zero_biasSpec` | matches |
| `theorem1iii_argmax_bias_le_mae` | `theorem1iii_argmax_bias_le_maeSpec` | matches |
| `theorem1iii_tight_binary_example` | `theorem1iii_tight_binary_exampleSpec` | matches |
| `theorem2i_joint_rule_exists` | `theorem2i_joint_rule_existsSpec` | matches |
| `theorem2ii_argmax_accuracy_maximizing` | `theorem2ii_argmax_accuracy_maximizingSpec` | matches |
| `theorem2iii_non_argmax_not_pareto` | `theorem2iii_randomized_non_argmax_not_paretoSpec` | matches |
| `theorem2iii_weighted_objective_maximizer_agrees_argmax` | `theorem2iii_randomized_weighted_objective_maximizer_agrees_argmaxSpec` | matches |

These are the nine current rows in the saved source-to-Spec ledger. The table
reports that ledger; it does not issue or broaden any semantic judgment.

## 21. Source-Coverage Audit Ledger

The [source map](audit/paper_statement_map.json) retains 96 source records. Its
inventory summary records 39 direct source targets, nine source-premise
declarations, 48 proof-support items, and no unassigned source targets. The
nine selected semantic contracts and their judgments are listed in Section 20;
all other source records retain their explicit context, support, correction,
or scope disposition.
