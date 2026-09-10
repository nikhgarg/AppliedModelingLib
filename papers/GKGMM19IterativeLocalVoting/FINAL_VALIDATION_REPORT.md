# Final Validation Report: Iterative Local Voting for Collective Decision-making in Continuous Spaces
Updated: 2026-09-09

## 1. Human Verdict

The formalization establishes convergence of iterative local voting in the
paper's utility models. The table below distinguishes Proposition 2's limit
on coupled domains and the feasibility condition used for Theorem 3.

## 2. Closeout Status

Completion status: **formalized**.

The main results and appendix support are proved in the scopes summarized below.

## 3. Source and Scope
The source is Garg, Kamble, Goel, Marn, and Munagala, *Iterative Local Voting
for Collective Decision-making in Continuous Spaces*, JAIR 2019. The public
source is [the JAIR article](https://www.jair.org/index.php/jair/article/view/11358).
The checked probabilistic results concern finite-coordinate iid realizations
of the paper's models.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| [Theorem 1](docs/SOURCE_CLARIFICATIONS.md#appendix-c4-lemma-2-the-infinity-one-case) | **Exact.** |
| Theorem 2 | **Exact.** |
| [Proposition 1](docs/SOURCE_CLARIFICATIONS.md#proposition-1-and-appendix-c6-lemma-4) | **Exact.** |
| [Proposition 2, Model B](docs/SOURCE_CLARIFICATIONS.md#proposition-2s-coordinatewise-model-b) | **Exact with source clarification.** Model B uses the proof's coordinatewise response; the next row states the convergence target for both models. |
| [Proposition 2, both models](docs/PROPOSITION2_C1_CORRECTION.md#c1-corrected-target) | **Exact on product domains; corrected on general convex domains.** The limit minimizes expected coordinatewise absolute distance over the feasible set, since the coordinatewise medians can be infeasible when constraints couple coordinates. |
| [Theorem 3](docs/THEOREM3_CONSTRAINED_SPACE_SOURCE_NOTE.md#the-two-formal-results) | **Exact under the explicit full-space condition; constrained alternative proved in general.** |
| [Appendix Theorem 5](docs/SOURCE_CLARIFICATIONS.md#appendix-theorem-5-random-bias) | **Exact with source clarification.** Bias may depend on past observations, with the measurability and adaptedness needed for the stated conditional expectations made explicit. |
| Appendix Lemmas 1–4; Theorem 4 | **Exact.** |

Proposition 2 is split into its response convention and convergence conclusion.
The final row groups the appendix support results; repeated appendix statements
of main results are covered by their main-text rows.

## 5. Remaining Boundaries and Gaps

Theorem 3's unrestricted zero-field conclusion remains outside the proof; see
the [feasibility condition in Section 6](#6-additional-assumptions-beyond-paper).

## 6. Additional Assumptions Beyond Paper

For Theorem 3's zero-field conclusion, the proof assumes that a positive step
in the limiting aggregate direction is feasible along the relevant tail of
the trajectory. Whether the paper's assumptions imply this condition, or a
different proof avoids it, is unresolved.
[Precise scope](docs/SOURCE_CLARIFICATIONS.md#theorem-3s-full-space-and-projected-readings).

## 7. Proof-Strategy Deviations

The probability estimates in Appendix Lemmas 2 and 4 use crossing-or-near-tie
events and unions of coordinate slabs, respectively. These give the stated
linear-in-radius bounds; the changes concern the proof rather than the
conclusions. See the [Lemma 2](docs/SOURCE_CLARIFICATIONS.md#appendix-c4-lemma-2-the-infinity-one-case)
and [Lemma 4](docs/SOURCE_CLARIFICATIONS.md#proposition-1-and-appendix-c6-lemma-4)
notes. The fuller explanations cover the
[active-coordinate crossing event](docs/APPENDIX_LEMMA2_LINF_L1_SOURCE_NOTE.md)
and [weighted-Euclidean response and event bound](docs/PROPOSITION1_WEIGHTED_EUCLIDEAN_SOURCE_NOTE.md).

Where the main proofs invoke Appendix Theorem 5 without a unique minimizer,
the formalization uses its [extension to nonunique minimizers](docs/APPENDIX_THEOREM5_MINIMIZER_SET_SOURCE_NOTE.md).

## 8. Proof Tricks Worth Reusing
None.

## 9. Generalizations, Conjectures, and Extensions

For Theorem 3, the [constrained-domain alternative](docs/THEOREM3_CONSTRAINED_SPACE_SOURCE_NOTE.md#the-two-formal-results)
states that the limiting aggregate field is zero or the tail feasibility
condition fails. This complements the zero-field result under that condition;
it does not assert a full boundary-equilibrium characterization.

The stochastic-convergence argument also proves convergence to a point in
the minimizer set when the minimizer is not unique. This covers the
nonunique median sets permitted by the paper's models.
[Minimizer-set argument](docs/APPENDIX_THEOREM5_MINIMIZER_SET_SOURCE_NOTE.md).

## 10. Source Clarifications and Exact Readings

Proposition 2 uses the
[coordinatewise Model B response from its proof](docs/SOURCE_CLARIFICATIONS.md#proposition-2s-coordinatewise-model-b).
The [response-rule explanation](docs/PROPOSITION2_MODEL_B_SOURCE_NOTE.md) compares it with the normalized-gradient rule.
Its [convex-domain correction](docs/PROPOSITION2_C1_CORRECTION.md#c1-corrected-target)
explains the constrained expected-distance target and when it equals the
coordinatewise median set.

The source memo also records the
[zero-gradient convention](docs/SOURCE_CLARIFICATIONS.md#algorithm-1s-query-and-projection)
and [stochastic-process conventions for Appendix Theorem 5](docs/SOURCE_CLARIFICATIONS.md#appendix-theorem-5-random-bias).
Theorem 3's additional condition is discussed in Section 6; the appendix
proof deviations are in Section 7.

## 11. Paper Issues or Caveats

The substantive statement differences are Proposition 2's constrained-domain
target (Section 10) and Theorem 3's feasibility condition (Section 6).

## 12. Detailed Formalization Evidence

The review surface contains 11 source-claim specifications and one separately
tracked source condition. Each claim is displayed from its expanded semantic
`Spec` and is paired with a Lean-checked proof endpoint. The
[human review packet](docs/HUMAN_REVIEW_PACKET.pdf) presents the same surface
in dependency order. The interactive dashboard is an optional alternative to
reviewing the PDF.

The exact source anchors, semantic routes, Proposition 2 model convention, and
proof endpoints are recorded in the
[paper statement map](audit/paper_statement_map.json) and
[source-proof fidelity ledger](FINAL_CLOSURE_RECEIPT.md).

## 13. Paper Assumption Provenance

The only paper-facing assumption declaration is the bundled C1--C3 source
condition: the solution space is nonempty, bounded, closed, and convex; voters
have unique ideal points; and ideal points are independently sampled from a
distribution with bounded measurable density. The explicit statement scopes
in Section 6 remain visible independently of this bundled declaration. The
proved adapted-bias endpoint for Appendix Theorem 5 includes the zero-bias
main-text executions as a specialization.

## 14. Displayed Formula Provenance

The checked formulas include Algorithm 1's radius, neighborhood, projection,
update, and stopping rules; the Model A and Model B response rules; Definitions
1--3; the finite Holder-dual calculation used by Lemma 3; and the displayed
conditions and conclusions of the selected main-text and appendix results.
Their byte-pinned source locations and expanded Lean targets are recorded in
the [paper statement map](audit/paper_statement_map.json).

## 15. Library Lift Pass

The stochastic-convergence and finite-dimensional analytic components use
reusable AppliedModelingLib and Mathlib declarations. Material library
prerequisites are included in the source review. The recorded recursive
premise audit identifies no unresolved library or hidden-premise boundary
for the 11 selected source claims.

## 16. DAG Audit

- Source: [DependencyDAG.tex](docs/DependencyDAG.tex)
- Rendered artifact: [DependencyDAG.pdf](docs/DependencyDAG.pdf)
- Visual inspection: the rendered one-page DAG was inspected on 2026-09-09;
  the formalized status, Proposition 1 closure, corrected Proposition 2 C1
  branch, Appendix Theorem 5 endpoint, and two Theorem 3 endpoints are legible, and node
  labels and arrows do not overlap.

## 17. Validation Checks

The recorded closeout includes successful focused interface and paper builds,
repository checks, source/semantic review, and the final independent review.
The [closure receipt](FINAL_CLOSURE_RECEIPT.md) identifies the accepted graph
and supporting validation records.

The final reader pass checks report structure, result coverage, memo bindings,
and rendered links separately from the unchanged mathematical evidence.

## 18. Paper Definitions Checked

- C1--C3 and the Algorithm 1 execution model.
- Algorithm 1 radius, neighborhood, projection, update, and stop condition.
- Model A and finite-coordinate Model B response rules.
- Definition 1 `L^p`-normed utilities, Definition 2 weighted Euclidean
  utilities, Definition 3 decomposable utilities, and Definition 4's
  directional local collective-decision condition.

## 19. Named Theorem Statements Checked

- Lemma 3: the finite-dimensional Holder-dual gradient-candidate norm formula.
- Proposition 1: concrete Definition 2 Model A and Model B convergence.
- Proposition 2: Model A and the proof's coordinatewise-boundary Model B
  process converge to feasible expected-`L1` minimizers on C1; product domains
  recover the ordinary coordinatewise median set.
- Appendix Lemmas 1, 2, and 4 and Appendix Theorems 4 and 5.
- Theorem 1: all six finite-coordinate norm/model cases.
- Theorem 2: finite-exponent Model B Holder-dual cases.
- Theorem 3: the sampled projected source package, with the printed conclusion
  under the explicit full-space condition.

## 20. Paper-Facing Statement Validator Ledger

The source-to-Lean judgments are recorded in
[statement_match_llm.json](FINAL_CLOSURE_RECEIPT.md), and the source
inventory coverage judgments are recorded in
[paper_coverage_llm.json](FINAL_CLOSURE_RECEIPT.md). Human annotations are
kept separate and are not auto-closed by machine validation.

## 21. Source-Coverage Audit Ledger

The complete source inventory is recorded in
[paper_statement_map.json](audit/paper_statement_map.json). The human review
denominator is the 11 selected source-claim `Spec` rows plus the separately
tracked C1--C3 condition; repeated appendix presentations and internal proof
support do not create duplicate human-review claims. Every selected claim has
an exact byte-pinned source anchor, expanded Lean semantic target, and checked
proof endpoint.
