# Final Validation Report: A No Free Lunch Theorem for Human-AI Collaboration

Updated: 2026-09-06

## 1. Human Verdict

Formalized. The checked proof establishes Theorem 1's advertised forward
no-free-lunch result, Proposition 6's mixture construction, Proposition 7,
Lemma 8, and Proposition 9. No selected named result has a remaining
mathematical boundary. Independent human review has not yet been recorded.

## 2. Closeout Status

- Completion status: formalized.
- Main result: every reliable collaboration strategy is non-collaborative in
  the stated calibrated-prediction model.
- Reviewed result surface: five source claims, each represented once by a
  transparent semantic specification and a distinct Lean-checked proof
  endpoint.
- Semantic prerequisites: twenty-one paper-local model and construction
  declarations; no material shared-library prerequisite is needed for this
  claim surface.
- Source inventory: fifty-three byte-pinned source presentations, including
  the model, named results, proof constructions, and six local source
  clarifications with checked dispositions.
- Human review: independent sign-off has not yet been recorded and is not
  inferred from the machine audit.

## 3. Source and Scope

The source is Peng, Garg, and Kleinberg, *A No Free Lunch Theorem for Human-AI
Collaboration*, AAAI 2025. The public source is the
[AAAI proceedings article](https://ojs.aaai.org/index.php/AAAI/article/view/33574).
The selected scope contains the probability model and collaboration strategy,
Definitions 1--4, Proposition 6, Proposition 7, Lemma 8, Proposition 9, and
Theorem 1. Expository examples and proof-local calculations remain visible in
the source inventory without becoming duplicate paper claims.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Theorem 1 | **Exact.** |
| Proposition 6 | **Typo fixed:** component-m weight is λ_m; joint-law mixture accuracies are the weighted sums. [Correction](docs/SOURCE_CLARIFICATIONS.md#mixtures-and-finite-partitions). |
| Lemma 8 | **Exact.** |
| Proposition 7 | **Exact.** |
| Proposition 9 | **Normalization corrected; witness explicit:** summed odds define the second setting, and mixture weights 7/8 and 1/8 prove fixed labeling on the half slice. [Construction](docs/SOURCE_CLARIFICATIONS.md#proposition-9s-two-settings). |

## 5. Remaining Boundaries and Gaps

None in the selected named-theory scope.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

The proof's qualitative “sufficiently close to one” mixture in [Proposition 9](docs/SOURCE_CLARIFICATIONS.md#proposition-9s-two-settings)
is replaced by the explicit checked weights `7/8` and `1/8`. This strengthens
proof transparency without changing the proposition.

## 8. Proof Tricks Worth Reusing

- State calibration as a measurable-event identity on the joint law.
- Construct mixtures before projecting them to accuracy equations.
- Prove a finite partition's predictor realization pointwise, then reuse that
  equality for calibration and strict-gap calculations.
- Replace a qualitative close-enough parameter choice with one explicit
  rational witness when the inequalities permit it.

## 9. Generalizations, Conjectures, and Extensions

The joint-law mixture and finite-partition realization lemmas are reusable for
other calibrated-prediction impossibility arguments. Extending the generic
partition recipe beyond finite measurable cell maps would require separate
conditional-expectation infrastructure and is outside this paper's proof.

## 10. Source Clarifications and Exact Readings

The memo gives the [loss/accuracy correction](docs/SOURCE_CLARIFICATIONS.md#loss-correctness-and-calibration), [component-weight typo and null-cell completion](docs/SOURCE_CLARIFICATIONS.md#mixtures-and-finite-partitions), and [Proposition 9 parameter/denominator fixes](docs/SOURCE_CLARIFICATIONS.md#proposition-9s-two-settings).

<!-- BEGIN GENERATED SETTLED REVIEW CONTEXT -->
<!-- settled-review-context-sha256: 908c66a18323f2577411dc8eec37a35e314fe673eefa40bc69c61257bd1e7fd9 -->
<!-- settled-review-context-presentation-sha256: 6d01ddf4fae5fae3315dbd54c89379fc93464fee062afaa9fb810c243f449df4 -->
### Source readings and additional assumptions

- The result-specific conditions and corrections are stated in the [clarification memo](docs/SOURCE_CLARIFICATIONS.md).
<!-- END GENERATED SETTLED REVIEW CONTEXT -->

## 11. Paper Issues or Caveats

None beyond the specific qualifications in Section 10.

## 12. Detailed Formalization Evidence

The canonical machine credential is the
[final closure receipt](FINAL_CLOSURE_RECEIPT.md), which points to the accepted
obligation graph. That graph contains five direct source claims, twenty-one
paper-local semantic prerequisite judgments, fifty-three typed source routes,
five exact specification-to-proof contracts, the focused build result, and
the complete Lean-owned dependency and axiom closure.

The [human review packet](docs/HUMAN_REVIEW_PACKET.pdf), regenerated on
2026-09-03 from the retained graph, presents the five current source claims and
all twenty-one paper-local semantic prerequisites in dependency order. Opening
the interactive dashboard is an optional alternative to reviewing the PDF;
human annotations remain separate and are never auto-closed by the machine
audit.

The [paper statement map](audit/paper_statement_map.json) is the complete
source-first inventory and typed route surface. Direct source-to-expanded-Spec
judgments are recorded in
[`audit/v11_raw_source_spec_screening.json`](FINAL_CLOSURE_RECEIPT.md),
and the paper-local prerequisite judgments are recorded in
[`audit/paper_semantic_prerequisites.json`](FINAL_CLOSURE_RECEIPT.md).

## 13. Model and Assumption Provenance

The probability carrier, predictor range and measurability, event calibration,
strategy and individual accuracy, reliability, non-collaboration, correctness
vocabulary, finite mixture, and finite partition construction are reviewed
through their expanded paper-local Lean declarations. They are not accepted by
name, file location, or wrapper equivalence. The semantic prerequisite ledger
contains twenty-one current matches and the accepted graph binds their Lean-owned
recursive dependencies.

## 14. Checked Proof Route and Source Findings

The checked proof route contains four especially important construction steps:

1. Proposition 6's full-joint-law mixture preserves component event mass,
   predictor values, and both accuracy equations.
2. The exact finite cell maps for Lemma 8 and both Proposition 9 settings
   realize the displayed predictors.
3. Proposition 7's uniform mixture produces a strict gap against every agent.
4. Proposition 9's explicit `7/8`--`1/8` mixture produces its final strict
   gap.

The source-proof fidelity ledger records eight findings. Six have explicit
quarantined Lean theorem routes: the loss/accuracy correction, the half-tie
counterexample, the Proposition 6 index repair, the false converse
counterexample, the positive-epsilon domain, and the repaired Proposition 9
normalizer. The calibration and finite-partition readings are explicit model
conventions with direct semantic declarations and checked witness coverage.

## 15. Library Review

No material shared-library declaration lies on this paper's semantic review
surface. The twenty-one material prerequisites are paper-local declarations.
Mathlib supplies foundational mathematics and measure theory; its ordinary
foundational primitives are terminal trust leaves rather than separate paper
claims.

## 16. DAG Audit

- Source: [DependencyDAG.tex](docs/DependencyDAG.tex)
- Rendered artifact: [DependencyDAG.pdf](docs/DependencyDAG.pdf)
- The graph shows the calibrated model, mixture and finite-partition
  constructions, Propositions 6, 7, and 9, Lemma 8, Theorem 1, and the source
  clarification lane without marking any result partial or caveated.
- Visual inspection: the rendered one-page DAG was inspected on 2026-09-03;
  all labels are legible, no arrow overlaps a node, and the unit-cube and
  nonempty-agent model reading is distinguishable from the non-caveat
  clarification lane.

## 17. Validation Checks

The closeout command set is:

```text
lake build PKG25NoFreeLunch
python3 scripts/closeout_reuse_plan.py --paper PKG25NoFreeLunch
python3 scripts/run_paper_closeout.py --paper PKG25NoFreeLunch --new-run
python3 scripts/final_closure_receipt.py --paper PKG25NoFreeLunch --check
```

The graph-native strict closeout consists of ten stages: artifact preflight,
exact-context acquisition, route-schema preflight, Lean-graph acquisition,
semantic-evidence preflight, focused paper build, primary paper gate, evidence
integrity, conclusion provenance, and final input check.

## 18. Paper Definitions Checked

- Collaboration setting, calibrated predictor, collaboration strategy, agent
  classifier and accuracy, and collaboration classifier and accuracy.
- Reliability and non-collaboration, including off-half deferral and constant
  half-slice behavior.
- Correctness, incorrectness, agreement, and disagreement.
- Full-joint-law mixture and finite measurable partition predictors.
- The finite witness mass, label, predictor, and cell-map constructions used by
  Lemma 8 and Proposition 9.

## 19. Named Theorem Statements Checked

- Theorem 1: reliability implies non-collaboration.
- Proposition 6: finite convex mixtures preserve agent and strategy
  accuracies.
- Proposition 7: reliability forces one fixed off-half deferral agent.
- Lemma 8: a bad interior profile yields a calibrated setting with the stated
  weak and strict accuracy gaps.
- Proposition 9: reliability plus fixed off-half deferral forces a fixed
  half-slice label.

## 20. Semantic Review Ledgers

The direct semantic screening compares each exact byte-pinned source claim to
the expanded transparent Lean specification. The prerequisite screening
compares every material paper-local declaration used by those specifications.
The accepted graph separately proves each specification's proof endpoint,
recursive dependency closure, axiom boundary, and focused build. No legacy
statement, assumption, coverage, source-record, or wrapper sidecar is a live
acceptance authority for this paper.

## 21. Source-Coverage Ledger

The statement map contains all fifty-three source presentations. Five named
results own direct semantic contracts; twenty-one material model and construction
components own direct semantic-declaration routes; repeated presentations,
proof-local support, context, and deep-audit material retain explicit typed
dispositions; and six source defects retain exact checked theorem evidence.
No normal-scope named result is omitted or counted twice.
