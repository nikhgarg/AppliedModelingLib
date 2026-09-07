# Final Validation Report: Who is in Your Top Three?

Updated: 2026-09-06

## 1. Human Verdict

The formalization covers ordered-tier design invariance, pairwise and
aggregate convergence results, randomized approval rules, the Mallows special
case, and the exact dynamic program for two candidates' joint locations.
The dynamic program has a degree-six bound on arithmetic operations in its
stated unit-cost model.

Propositions 2 and 4 include their finite-sample bounds. The source
clarifications record the one-sided score-gap cases that make their rate
conventions explicit.

## 2. Closeout Status

- Completion status: formalized.
- Mathematical scope: the named definitions, theory, formulas, finite examples,
  and Mallows joint-location algorithm summarized in Section 4.
- The inventory contains 66 mathematical items. The technical evidence below
  records the declaration-level source correspondence and proof checks.
- The algorithm's complexity guarantee counts exact scalar arithmetic
  operations; it is not a rational bit-complexity or compiled-runtime claim.

## 3. Source and Scope

The canonical pinned source is
[arXiv:1906.08160](https://arxiv.org/pdf/1906.08160) / HCOMP 2019:

- archive: `cited publication`, SHA-256
  `667a8fb232a00e9161afc05cc6b68b3d8d950372531400e779388941fa68d41a`;
- extracted TeX: `cited publication`, SHA-256
  `be8a698dbe73835afaf8cd6079c7fc6a6a566fcaef25fc948c1e9be23771af32`.

The independent source inventory covers the finite ranking model, all three
definitions, all nine named theoretical results, displayed probability and
rate formulas, appendix proof steps, fixed mathematical examples, and the
advertised Mallows joint-location algorithm. Raw datasets, fitted empirical
estimates, figure pixels, and qualitative deployment recommendations are not
mathematical theorem targets. The Durham numerical comparison is nevertheless
checked exactly from the printed thousandths because it supports a source
mathematical claim.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Definitions 1–3 | **Exact.** |
| Proposition 1 | **Exact.** |
| [Proposition 2](docs/SOURCE_CLARIFICATIONS.md#proposition-2-pairwise-rate-and-finite-sample-bound) | **Exact.** |
| Proposition 3 | **Exact.** |
| [Proposition 4](docs/SOURCE_CLARIFICATIONS.md#proposition-4-outcome-rate-and-m2-bound) | **Exact.** |
| Theorems 1–2; Mallows corollary | **Exact.** |
| W-selection, Durham, and high-noise examples | **Exact.** |
| Joint-location dynamic program | **Exact.** |

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

- Compare a finite probabilistic recurrence with an independently defined
  `PMF.bind` process rather than proving a recurrence equal to itself.
- Track two candidates with `Option (Fin N)` locations so the same state type
  covers prefixes before and after each tracked insertion.
- Make unreachable saturated updates total, then keep correctness tied to the
  generative process rather than burdening every recurrence with partial-state
  side conditions.
- Count stages, target states, source states, and insertion choices separately;
  `card (Option (Fin N) x Option (Fin N)) = (N+1)^2` then yields the explicit
  `N^2 (N+1)^4 <= (N+1)^6` bound.
- For an iid centered finite score-gap walk, combine the strong law, martingale
  boundedness/convergence equivalences, and positive-mass atom recurrence to
  rule out eventual one-sided correctness. If every supported gap is zero,
  use the independent uniform tie coordinate directly.

## 9. Generalizations, Conjectures, and Extensions

The dynamic-program layer is source-independent enough to be a candidate for
future extraction into the reusable Mallows library. A sparse table over only
reachable states should improve the dense degree-six count, but no stronger
runtime theorem is claimed here. A separate rational or floating-point
implementation could connect exact semantics to executable numerical plots;
that would be an engineering extension rather than an unproved paper endpoint.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

None.

## 11. Paper Issues or Caveats

No source-theorem correction is claimed. The source's word “efficient” is
made precise by a degree-six dense arithmetic-operation bound for the exact
joint-location recurrence. Proposition 1 uses the source's uniform random tie
rule, including equality cases; it does not add a generic no-ties condition.

## 12. Detailed Formalization Evidence

The source-curated inventory retains 66 mathematical items. The current
selected source map retains 15 result contracts. Current review records cover
the selected statements and their governing definitions. Definitions and
algorithms are reviewed through their actual predicates, functions, and
execution rules.

The [source map](audit/paper_statement_map.json) connects the exact source
passages to the expanded statements and models. Each selected result has a
separate proof endpoint; the typed Lean graph checks its dependencies and
axiom closure. Section 20 links the current review ledgers.

## 13. Paper Assumption Provenance

The selected models expose score and probability laws, randomized weights,
ordered nonempty tiers, Mallows parameters, and valid approval cutoffs.
These source conditions are carried by the actual semantic prerequisites;
no algorithm-correctness conclusion is assumed.

## 14. Displayed Formula Provenance

The selected rate results retain the Chernoff expressions and finite-sample
bounds. The [source clarifications](docs/SOURCE_CLARIFICATIONS.md) state the
one-sided score-gap readings. The example and algorithm routes include the
printed Durham arithmetic, Mallows insertion probabilities, and pair-location
recurrence. Supporting formula presentations remain source context rather than
additional named result claims.

## 15. Library Lift Pass

The exact Mallows pair-location dynamic program and its PMF semantics are
natural candidates for the shared ranking library. No unresolved library
certificate supports a final paper conclusion.

## 16. DAG Audit

`docs/DependencyDAG.tex` shows the dynamic program as a green formalized
algorithm node downstream of the Mallows repeated-insertion support. The fixed
counterexample remains a separate green result because its mathematical proof
does not rely on trusting historical plotting code. The rendered
`docs/DependencyDAG.pdf` is rebuilt from that TeX source and visually inspected
after the update.

## 17. Validation Checks

The proof endpoints include the displayed rate and finite-sample clauses. The
[closeout record](FINAL_CLOSURE_RECEIPT.md) records build and acceptance
evidence for its pinned inputs. The targeted closeout command is
`python3 scripts/run_paper_closeout.py --paper GGSG19TopThree --plan-identity <current-plan-identity>`.

## 18. Paper Definitions Checked

The checked definitions include common limiting outcome, normalized rate,
feasible rate maximization, tier goals, approval mechanisms, Mallows laws, and
the repeated-insertion pair-location process and dynamic program.

## 19. Named Theorem Statements Checked

Propositions 1–4, Theorems 1–2, the Mallows no-randomization corollary, the
selected randomization results and counterexample, and the arbitrary-pair
dynamic-program correctness and operation bound have checked endpoints.

## 20. Statement Review Evidence

The current source-to-statement assessment and exact review targets are recorded
in the following artifacts. Mathematical scope and qualifications are explained
with their named results above.

- [Source statement inventory](audit/paper_statement_map.json)
- [Source-to-statement review](FINAL_CLOSURE_RECEIPT.md)
- [Model and definition review](FINAL_CLOSURE_RECEIPT.md)
- [Reusable definitions review](FINAL_CLOSURE_RECEIPT.md)
- [Canonical closeout record](FINAL_CLOSURE_RECEIPT.md)
- [Review packet](docs/HUMAN_REVIEW_PACKET.pdf)

## 21. Source-Coverage Audit Ledger

The 66-item source inventory distinguishes selected result contracts, source
models, repeated presentations, and proof support. The selected comparison
surface has 15 direct result judgments and 20 prerequisite judgments. Raw
empirical data and plots are outside normal theorem scope; the printed Durham
arithmetic is retained as a mathematical example.
