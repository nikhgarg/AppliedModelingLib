# Final Validation Report: MSVV07 AdWords

Updated: 2026-09-07

## 1. Human Verdict

The finite Balance accounting, lower bound, and Appendix constructions are
proved on the domains described below.

**Formalization gap:** Theorem 8's limit is proved when its finite-error term
vanishes; deriving that condition from the paper's small-bid regime remains
unproved.
[Details](docs/SOURCE_CLARIFICATIONS.md#finite-and-limiting-theorem-8-readings).

## 2. Closeout Status

- Completion status: formalized.
- Scope: finite and limiting AdWords results, the operational algorithm definitions, and corrected Appendix constructions.
- The source's Section 8 performance questions remain open proposals.
- The multiple-slot extension has proof code, but its dedicated source-model review is outside this closeout.

## 3. Source and Scope

The audited source is Mehta, Saberi, Vazirani, and Vazirani, *AdWords and
Generalized Online Matching*, JACM 54(5), 2007. The local journal text was read
source-first from the abstract through Appendix A. The exact source digest is
pinned in `audit/paper_statement_map.json` and
`audit/source_proof_fidelity.json`.
The public source is the [paper PDF](https://people.eecs.berkeley.edu/~vazirani/pubs/adwords.pdf).

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Section 3: GREEDY tight example, equal-bid BALANCE identity, and discrete tradeoff monotonicity/convergence | **Exact.** |
| Lemmas 1–3 | **Exact.** |
| Lemma 4 | **Exact.** |
| Lemmas 5–7 | **Exact.** |
| Theorem 9 | **Exact.** |
| [Theorem 8](docs/SOURCE_CLARIFICATIONS.md#finite-and-limiting-theorem-8-readings) | **Formalization gap:** the finite bound and limiting inequality under vanishing finite error are proved; deriving that limit condition from the paper's fixed-advertiser small-bid regime remains unproved. |
| [Theorem 8 suffix](docs/SOURCE_CLARIFICATIONS.md#theorem-8-finite-suffix-index) | **Typo fixed:** exponent `k-i` and unspent fraction `(k-i)/k`. |
| [Section 4 tightness](docs/SOURCE_CLARIFICATIONS.md#section-4-tightness) | **Formalization gap:** a fluid tightness construction is proved; the asserted finite instance is not constructed. |
| [Section 6 variants](docs/SOURCE_CLARIFICATIONS.md#section-6-variants) | **Current proof restrictions:** each possible charge is small relative to its winner’s budget; all bidders remain alive for the charge comparison. Necessity is unproved. Efficiency is a unit-cost operation count. |
| [Appendix A three-phase example](docs/SOURCE_CLARIFICATIONS.md#appendix-counterexample-three-phase-revenue) | **Formula corrected:** corrected phase revenue and residual service; the strict counterexample remains. |
| [`kappa>1` witness](docs/SOURCE_CLARIFICATIONS.md#the-kappa-witness-family) | **Exact:** an explicit continuous-limit family supplies the source existence claim; no fixed-positive-bid discretization bound is asserted. |
| Section 8 retained formulas and definitions | **Exact.** The weighted-bid runner is [uncredited](docs/SOURCE_CLARIFICATIONS.md#section-8-weighted-bid-proposal). |

## 5. Remaining Boundaries and Gaps

- [Theorem 8](docs/SOURCE_CLARIFICATIONS.md#finite-and-limiting-theorem-8-readings): connect the paper's fixed-advertiser discretization regime to the vanishing-error premise of the proved limiting inequality.
- [Section 4](docs/SOURCE_CLARIFICATIONS.md#section-4-tightness): the finite tight instance remains unconstructed; a fluid construction is proved.
- The Appendix executions are continuous limits without fixed-positive-bid discretization bounds. Section 8's performance guarantees are open questions in the source.

## 6. Additional Assumptions Beyond Paper

The [Section 6 comparison](docs/SOURCE_CLARIFICATIONS.md#section-6-variants)
uses an effective-charge bound for every possible winner and a unit-cost
arithmetic model. Necessity of these conditions for other proof routes is not
established. Theorem 8's remaining limit-condition bridge is listed in Section 5.

## 7. Proof-Strategy Deviations

The finite-to-limit and fluid proof routes are explained in the
[memo](docs/SOURCE_CLARIFICATIONS.md), including the distinction between a
continuous execution and a fixed positive discretization.

## 8. Proof Tricks Worth Reusing

- Separate finite accounting from the limiting competitive-ratio statement.
- Keep transformed-instance results auxiliary when the source's actual claim
  uses a different stochastic world or runner.
- Name the arithmetic oracle model for finite-max cost claims and derive its
  operation ledger from the same runner whose semantic winner theorem is used.
- Derive execution state from prior allocations; do not allow a certificate to
  stipulate the spend trajectory that is supposed to be proved.
- Check both phase totals and claimed exhaustion before treating a printed
  numerical ratio as a source theorem.

## 9. Generalizations, Conjectures, and Extensions

Optional extensions could refine the Appendix fluid certificate to a quantified
fixed-positive-`a` discretization theorem, analyze bit complexity for an
approximate implementation of the Balance scan, or investigate the Section 8
switching-distribution and many-representative RANKING proposals without
prejudging their open guarantees. None is required for source-level status.

## 10. Source Clarifications and Exact Readings

The [memo](docs/SOURCE_CLARIFICATIONS.md) gives the finite suffix correction,
the corrected three-phase revenue, and the explicit $\kappa>1$ witness with
both endpoint limits. The corrected execution preserves the strict
counterexample to the naive rule.

## 11. Paper Issues or Caveats

The localized corrections and their unchanged limiting conclusions are
explained in Section 10; no additional boundary is asserted here.

## 12. Detailed Formalization Evidence

`PaperInterface.lean` exposes the model/formula rows, the finite and continuous
tradeoff route, the occurrence runner and cost bounds, both displayed LP
families, Lemmas 1--7, Theorem 8 and its simple-proof accounting, Section 6,
Theorem 9, Section 8's proposal definitions, and all Appendix source claims.
`SourceRunner.lean` contains the source-shaped operational and accounting
bridges. `AppendixCounterexample.lean` contains the continuous within-phase
state, allocation-derived three-phase certificate, true revenue and optimum,
and derived `kappa` family. The older transformed-instance Section 8 theorem
remains auxiliary and receives no credit for the source's open stochastic
guarantee.

## 13. Paper Assumption Provenance

The [source-to-statement map](audit/paper_statement_map.json) records the
premises of each selected target. The [memo](docs/SOURCE_CLARIFICATIONS.md#finite-and-limiting-theorem-8-readings)
explains the finite and limiting small-bid conditions. Finite histories index
arrival occurrences, so repeated query words are allowed; Section 6
click-through rates lie in $[0,1]$.

## 14. Displayed Formula Provenance

The [source map](audit/paper_statement_map.json) binds the bid, spend,
revenue, feasibility, LP, tradeoff, competitive-ratio, and lower-bound formulas
to their source spans. The [memo](docs/SOURCE_CLARIFICATIONS.md) explains
Theorem 8's finite-index correction and the corrected Appendix execution and
revenue; the [current screening](FINAL_CLOSURE_RECEIPT.md)
records the corresponding source-to-Spec comparisons.

## 15. Library Lift Pass

Reusable AdWords definitions and main finite accounting infrastructure already
live in `AppliedModelingLib/Algorithms/Online/AdWords.lean`. The source-specific
occurrence runner, phase dynamics, and `kappa` construction remain paper-local;
no generic lift was justified in this pass.

## 16. DAG Audit

The [dependency DAG](docs/DependencyDAG.pdf) distinguishes the proved finite results, Theorem 8's remaining limit-condition bridge, and the source's open Section 8 questions. The Section 4 construction is identified as a fluid limit. The current PDF was compiled and visually inspected on September 7, 2026; labels and arrows are legible and unclipped.

## 17. Validation Checks

The current [direct source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) records 50 selected result judgments. The [paper-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) records 38 governing definitions and conditions, alongside 36 reusable-library prerequisites. The [closure receipt](FINAL_CLOSURE_RECEIPT.md) records the accepted graph and focused build for the completed closeout.

## 18. Paper Definitions Checked

The checked definitions include assignments, spend, revenue, feasibility,
small bids, fractional revenue/feasibility, the tradeoff function, MSVV ratio,
Balance score, assignability, occurrence-level runner state, current slabs,
bidder/query types, alpha/beta accounting, Section 6 next-price charges,
Section 8 switching and weight-update state, Theorem 9's hard distribution/payoff, and the Appendix
fluid inputs, allocations, derived state, and `kappa` family.

## 19. Named Theorem Statements Checked

- Lemmas 1--7: formalized. Theorem 8 has the finite bound and conditional limiting endpoint, with the remaining bridge described in Section 5.
- Displayed factor/tradeoff LP formulas, Lemma 3 witnesses, and the corrected
  dual-induced finite tradeoff and unspent-fraction formulas: formalized on the
  configured surface.
- Section 6 different-budget, nonexhaustive-optimum, next-price, CTR,
  and availability variants: formalized.
- Theorem 9 randomized-online lower bound: formalized.
- Qualitative finite-max efficiency: formalized in the explicit unit-cost
  feasibility/exact-score oracle model by an actual recursive scan and
  occurrence runner.
- Appendix phase arithmetic, positive residual, state-derived execution,
  optimal offline witness, true strict ratio, and derived `kappa > 1` family
  with both endpoint limits: formalized.
- Section 8 weighted-bid `1 - o(1)` result: source open question, not a theorem;
  the switching model, weighted-bid formula, updates, and replicated-RANKING
  definitions have checked source connections. The experimental weighted-bid
  runner is uncredited; see the [scope note](docs/SOURCE_CLARIFICATIONS.md#section-8-weighted-bid-proposal).
- Discrete slab runner, model-derived bidder/query type accounting, and greedy
  tightness example: formalized. Balance tightness is proved through the fluid construction; its finite instance remains open.

## 20. Statement and Validation Records

The current records are the [source-to-statement map](audit/paper_statement_map.json),
[source-to-Spec screening](FINAL_CLOSURE_RECEIPT.md),
[paper prerequisites](FINAL_CLOSURE_RECEIPT.md),
[library prerequisites](FINAL_CLOSURE_RECEIPT.md), and
[closure receipt](FINAL_CLOSURE_RECEIPT.md). They retain the exact statement
and validation evidence summarized above.

## 21. Source-Coverage Audit Ledger

The [source-to-statement map](audit/paper_statement_map.json) records the
selected claims, supporting source material, exclusions, and exact source
locations. The current validation records are linked in Section 20; the
[closure receipt](FINAL_CLOSURE_RECEIPT.md) records their binding to the
closed surface.
