# Final Validation Report: An Algorithmic Framework for Bias Bounties

Updated: 2026-08-31

## 1. Human Verdict

Formalized. The named results establish certificate-based improvement, adaptive checking, monotone repair, training, and local search. Observation 4 uses almost-everywhere optimality for arbitrary population laws; Theorem 23 separates local optimality from positive-certificate value. Independent human review has not been recorded.

## 2. Closeout Status

- Completion status: formalized.
- Scope: the complete named theoretical surface in arXiv v4, cross-checked
  against the FAccT proceedings version.
- Main result: efficiently discoverable subgroup/model certificates
  characterize approximate Bayes optimality, drive bounded-loss improvement,
  and support adaptive checking, monotone repair, training, and local search.
- Human review: independent sign-off is not inferred from the machine audit
  and is not a release blocker.

## 3. Source and Scope

The paper is Ira Globus-Harris, Michael Kearns, and Aaron Roth, *An
Algorithmic Framework for Bias Bounties*, ACM Conference on Fairness,
Accountability, and Transparency 2022, DOI
[10.1145/3531146.3533172](https://doi.org/10.1145/3531146.3533172). The
governing mathematical source is
[arXiv:2201.10408v4](https://arxiv.org/abs/2201.10408v4), which the published
paper identifies as the up-to-date version.

The checked scope includes Definitions 1--3, 5, 7, and 17--19; Observation 4;
Theorems 8--12, 14, 16, 20, and 23; Remark 13; Lemmas 15, 21, and 22; the
certificate-optimization objective; and Algorithms 1--6. Repeated appendix
presentations are linked to the corresponding main-text claims rather than
counted as new results. The Bogotá network, deployment discussion,
experiments, figures, and empirical findings are outside the formalized
theory scope.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| [Definitions 1–3](docs/SOURCE_CLARIFICATIONS.md#conditional-group-loss-and-null-groups) | **Statement clarified:** mass-weighted loss is primitive; conditional group loss is zero on null groups. |
| [Observation 4](docs/SOURCE_CLARIFICATIONS.md#bayes-optimality-and-observation-4) | **Statement corrected:** almost-everywhere replaces pointwise optimality for arbitrary laws. Null-point changes refute the unrestricted pointwise claim; finite positive-mass support retains it. |
| Definitions 5 and 7; Theorem 8; Algorithm 1; Theorems 9–10; Remark 13 | **Exact.** |
| [Algorithm 2; Theorem 11](docs/SOURCE_CLARIFICATIONS.md#adaptive-certificate-checking) | **Same claimed sample rate; corrected finite statement:** explicit sparse-transcript failure bound and queried-prefix acceptance count. |
| [Algorithm 3; Theorem 12](docs/SOURCE_CLARIFICATIONS.md#adaptive-certificate-checking) | **Same claimed sample rate:** uses the corrected finite checker bound. |
| [Algorithm 4; Theorem 14](docs/SOURCE_CLARIFICATIONS.md#shared-state-in-algorithm-4) | **Algorithm repaired:** shared checker state and a restarted repair scan; the theorem's conclusions are retained. [Checker bound](docs/SOURCE_CLARIFICATIONS.md#adaptive-certificate-checking). |
| [Lemma 15](docs/SOURCE_CLARIFICATIONS.md#fresh-blocks-integer-rounds-and-the-lemma-15-typo) | **Typo fixed:** undefined `g_p` becomes the quantified group `g`. |
| [Algorithm 5; Theorem 16](docs/SOURCE_CLARIFICATIONS.md#fresh-blocks-integer-rounds-and-the-lemma-15-typo) | **Typo fixed; same asymptotic oracle/sample rate:** use the fresh block `D_t` and the integer-safe count `ceil(2/epsilon)`. |
| Definitions 17–19; Theorem 20; Lemmas 21–22 | **Exact.** |
| [Algorithm 6; Theorem 23 local-optimality clause](docs/SOURCE_CLARIFICATIONS.md#algorithm-6-and-theorem-23) | **Algorithm repaired:** two coordinate-gap tests replace full-sweep stopping; the theorem's local-optimality conclusion and response bound are retained. |
| [Theorem 23 positive-certificate clause](docs/SOURCE_CLARIFICATIONS.md#algorithm-6-and-theorem-23) | **Sufficient added condition:** positive initialization gives positivity. The zero-objective example refutes arbitrary-start positivity, but does not prove positive initialization necessary. |

## 5. Remaining Boundaries and Gaps

None in the selected theoretical scope. The empirical deployment, Bogotá
network construction, and experimental claims were not selected for theorem
formalization.

## 6. Additional Assumptions Beyond Paper

[Theorem 23](docs/SOURCE_CLARIFICATIONS.md#algorithm-6-and-theorem-23) adds positive initialization for its positive-certificate clause. This is sufficient; the zero-objective example shows that unrestricted initialization cannot guarantee positivity, not that positive initialization is the only repair.

## 7. Proof-Strategy Deviations

- Theorem 11 uses a corrected sparse-transcript count and Hoeffding union bound.
- [Lemma 22](docs/SOURCE_CLARIFICATIONS.md#lemma-22-proof-route) uses the exact disagreement-loss identity.
- Algorithm 6 tests both coordinate gaps at the same returned pair.

The [source memo](docs/SOURCE_CLARIFICATIONS.md) and [Algorithm 6 note](docs/ALGORITHM6_THEOREM23_CLARIFICATION.pdf) give the arguments.

## 8. Proof Tricks Worth Reusing

- Use the mass-weighted group-loss numerator as the primitive object. It avoids
  division at null groups and agrees with conditional group loss whenever the
  group has positive mass.
- Convert an almost-everywhere comparison into all measurable-group integral
  comparisons by testing the measurable set on which the comparison fails.
- Count adaptive transcripts by accepted positions and values rather than by
  every binary transcript.
- Represent an `argmax` as membership plus domination of every candidate; this
  exposes the full optimization claim without relying on a choice operator.
- Bound coordinate-improvement iterations by telescoping an objective with a
  known range.

## 9. Generalizations, Conjectures, and Extensions

The arbitrary-law reading of Observation 4 is described in Section 10. The
measure-theoretic group-loss and finite adaptive-count arguments can be reused
for other prediction models.

## 10. Source Clarifications and Exact Readings

Observation 4 becomes an almost-everywhere equivalence for arbitrary laws. Algorithms 4–5 make the shared checker/restart and fresh-block operations explicit; Lemma 15 changes `g_p` to `g`. See the [source memo](docs/SOURCE_CLARIFICATIONS.md) and [compact companion](docs/PUBLIC_FORMALIZATION_NOTE.pdf). Sections 6–7 discuss the other changes.

<!-- BEGIN GENERATED SETTLED REVIEW CONTEXT -->
<!-- settled-review-context-sha256: 1f0db158e7c8e947434d021d0381e0bded62a619d016e1fd43d2e4d160b77595 -->
<!-- settled-review-context-presentation-sha256: d3295c9ee0ac3c8e3696ee11edd691c0839961d19a9ec23ddc405edeadc1d403 -->
### Source readings and additional assumptions

- The mass-weighted group-loss numerator is the total primitive; conditional group loss is totalized to zero at mass zero, and every divided source display is recovered on positive-mass groups.
<!-- END GENERATED SETTLED REVIEW CONTEXT -->

## 11. Paper Issues or Caveats

The statement readings and positive-initialization scope are in Sections 6 and 10; the changed proof arguments are in Section 7.

## 12. Detailed Formalization Evidence

The current saved Lean graph contains 15 direct result contracts with separate
proof endpoints. The semantic ledgers cover those 15 results, 26 paper-local
prerequisites, and one shared-library prerequisite. The 31-item source
inventory distinguishes 15 result routes, 15 source-declaration routes, and
one deep-audit item. Definitions and algorithms are reviewed through their
actual declarations. The [final closure receipt](FINAL_CLOSURE_RECEIPT.md)
records the most recently completed terminal transaction; a successor
credential is issued only after the current strict closeout completes.

The [human review packet](docs/HUMAN_REVIEW_PACKET.pdf) presents the 15 source
result contracts and their 27 reviewed semantic prerequisites in dependency order. It
includes exact byte-pinned source excerpts, expanded Lean declarations, proof
endpoints, saved source-to-Lean judgments, and reviewer-owned checkboxes and
notes. Opening the interactive dashboard is an optional alternative to using
the PDF; human annotations are never manufactured or auto-closed.

The [paper statement map](audit/paper_statement_map.json) is the source-first
inventory and typed route surface. Direct source-to-expanded-specification
judgments are recorded in
[`audit/v11_raw_source_spec_screening.json`](FINAL_CLOSURE_RECEIPT.md),
paper-local prerequisite judgments in
[`audit/paper_semantic_prerequisites.json`](FINAL_CLOSURE_RECEIPT.md),
and the material library judgment in
[`audit/library_semantic_review.json`](FINAL_CLOSURE_RECEIPT.md).

## 13. Model and Assumption Provenance

No paper-facing assumption declaration is used as a proof substitute.
Conditions visible in theorem statements are source conditions or analytic
definedness conditions. The population law, models, groups, bounded loss,
group mass and loss, Bayes and approximate Bayes optimality, certificates,
adaptive transcripts, training state, ternary costs, empirical objectives, and
coordinate-response process are reviewed through their expanded declarations,
not inferred from names or wrappers.

## 14. Checked Proof Route and Source Findings

The checked proof route includes four central chains:

1. Theorem 8 converts certificate inequalities to approximate Bayes
   optimality, and Theorems 9--10 turn certificate value into a loss potential
   and finite update bound.
2. Theorem 11 supplies the adaptive checker event; Theorem 12 and Remark 13
   lift it to the update process, while Algorithm 4 and Theorem 14 preserve
   historical group guarantees in the shared adaptive state.
3. Lemma 15, the exact empirical argmax, and fresh-block Algorithm 5 supply
   Theorem 16's training guarantee.
4. Theorem 20 and Lemmas 21--22 supply the two best-response oracles;
   Algorithm 6 and Theorem 23 use them in a bounded two-gap potential process.

The source-proof fidelity ledger records eight source findings and two model
conventions, each with an explicit disposition. Counterexamples are included
for the unrestricted pointwise Observation 4 reading and the arbitrary-start
positive-certificate clause of Theorem 23.

## 15. Library Review

`AppliedModelingLib.Learning.Prediction.BoundedLoss` is the one material
shared-library declaration on the semantic review surface. Its exact Lean
declaration and paper-source connection are independently reviewed in the
library ledger and displayed in the human review packet. Mathlib's ordinary
measure-theoretic and finite foundations terminate as trusted foundational
leaves; they are not reclassified as paper claims.

## 16. DAG Audit

- Source: [DependencyDAG.tex](docs/DependencyDAG.tex)
- Rendered artifact: [DependencyDAG.pdf](docs/DependencyDAG.pdf)
- The graph presents the model and certificate layer, update and adaptive
  process, training route, cost-sensitive and ERM reductions, and two-gap
  local-search conclusion in source dependency order.
- The clarification lane identifies the source readings that affect those
  chains without marking the paper partial or caveated.
- The rendered DAG was visually inspected for legibility, clipping, and
  node-edge overlap.

## 17. Validation Checks

The closeout command set is:

```text
lake build GHKR22BiasBounties
python3 scripts/closeout_reuse_plan.py --paper GHKR22BiasBounties
python3 scripts/run_paper_closeout.py --paper GHKR22BiasBounties --new-run
python3 scripts/final_closure_receipt.py --paper GHKR22BiasBounties --check
```

The current planner reports reusable compiled inputs, current semantic review,
and current graph-native proof realizations. The remaining document preparation
updates the packet and report-to-memo bindings to that saved graph. The strict
transaction separately checks the focused build, primary paper gate, evidence
integrity, conclusion provenance, and final inputs before issuing its successor
closure credential.

## 18. Paper Definitions and Algorithms Checked

- Definitions 1--3, 5, and 7: subgroups, model and group loss, Bayes
  optimality, approximate Bayes optimality, and certificates.
- Algorithms 1--4: list update, adaptive certificate checking,
  falsify-and-update, and monotonicity-preserving historical repair.
- The certificate-optimization objective and Algorithm 5: full candidate
  argmax and fresh-block training.
- Definitions 17--19: derived certificates, ternary cost-sensitive
  minimization, and induced costs.
- Algorithm 6: two-gap alternating empirical risk minimization.

## 19. Named Theorem Statements Checked

- Observation 4: finite pointwise and arbitrary-population almost-everywhere
  Bayes/groupwise equivalence.
- Theorems 8--10: certificate characterization, list-update progress, and the
  accepted-update bound.
- Theorems 11--12 and Remark 13: adaptive checker fidelity,
  falsify-and-update, and submission-horizon complexity.
- Theorem 14: completion, query bound, and historical-group monotonicity.
- Lemma 15 and Theorem 16: VC uniform convergence and fresh-block training.
- Theorem 20 and Lemmas 21--22: ternary cost-sensitive and fixed-coordinate
  empirical-risk-minimization reductions.
- Theorem 23: two-sided local optimality, strict-improvement and response-round
  bounds, and positive-start certificate recovery.

## 20. Semantic Review Ledgers

The direct semantic screening compares each exact byte-pinned source claim to
the fully expanded transparent Lean specification. It records nine exact
matches and six matches to the clarified target. The paper-prerequisite
screening records 20 matches and six matches to clarified targets; the library
ledger records one match. The current saved Lean graph separately checks each
specification's exact proof endpoint and recursive dependency and axiom closure.
The focused build remains a separate strict-closeout check.

Historical wrapper, coverage, source-record, or reissue queues are not live
acceptance authorities. The current saved typed graph and its bound semantic
ledgers supply the evidence for the pending strict transaction.

## 21. Source-Coverage Ledger

The statement map contains 31 source presentations: 30 selected items and
contextual Remark 6 in the deep-audit inventory. Fifteen items own direct
semantic proof contracts: the 14 named results and the certificate-optimization
objective. The 15 selected definitions and algorithms own source semantic
declaration routes. Repeated appendix presentations are aliases of their
main-text claims, and every source finding has a typed clarification or defect
route. No normal-scope named result is omitted or counted twice.
