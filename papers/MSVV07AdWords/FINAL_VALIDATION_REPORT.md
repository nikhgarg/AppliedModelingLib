# Final Validation Report: AdWords and Generalized On-line Matching

Updated: 2026-09-27

## 1. Human Verdict

The finite Balance accounting and tightness construction, lower bound, and
Appendix constructions are proved on the domains described below. Theorem 8 is
closed in its stated normalized setting—unit budgets and an offline allocation
that exhausts every bidder: its finite error is `3N/(m+1)`, which vanishes for
a fixed advertiser population.
[Details](docs/SOURCE_CLARIFICATIONS.md#finite-and-limiting-theorem-8-readings).

## 2. Closeout Status

- Completion status: formalized.
- Scope: finite and limiting AdWords results, the operational algorithm definitions, an explicit finite Section 4 tightness construction, and corrected Appendix constructions.
- The source's Section 8 performance questions remain open proposals.
- The multiple-slot extension has proof code, but its dedicated source-model review is outside this closeout.

## 3. Source and Scope

The audited source is Mehta, Saberi, Vazirani, and Vazirani, *AdWords and
Generalized Online Matching*, JACM 54(5), 2007. The local journal text was read
source-first from the abstract through Appendix A. The public source is the
[paper PDF](https://people.eecs.berkeley.edu/~vazirani/pubs/adwords.pdf).

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| [Theorem 8](docs/SOURCE_CLARIFICATIONS.md#finite-and-limiting-theorem-8-readings) | **Exact.** |
| [Theorem 9](docs/SOURCE_CLARIFICATIONS.md#theorem-9-query-split-lower-bound-model) | **Exact.** |
| Section 3: GREEDY tight example, equal-bid BALANCE identity, and discrete tradeoff monotonicity/convergence | **Exact.** |
| [Lemmas 1–2](docs/SOURCE_CLARIFICATIONS.md#sections-45-idealized-slab-lemmas) | **Exact with source clarification.** the source expressly idealizes exact type endpoints and nonstraddling payments; the idealized ledger derives both the summed Lemma 1 prefix inequality and Lemma 2's beta identity. |
| Lemma 3 | **Exact.** |
| Lemma 4 | **Exact.** |
| [Lemma 5](docs/SOURCE_CLARIFICATIONS.md#sections-45-idealized-slab-lemmas) | **Exact with source clarification.** its perturbed LP identity is exact for the source's stated idealized slab vector, which is derived rather than supplied. |
| [Lemma 6](docs/SOURCE_CLARIFICATIONS.md#sections-45-idealized-slab-lemmas) | **Exact with source clarification.** the actual Theorem 8 occurrence runner proves the query comparison with its explicit endpoint slab term, whose aggregate vanishes in the source limit. |
| [Lemma 7](docs/SOURCE_CLARIFICATIONS.md#section-5-lemma-7-finite-slab-accounting) | **Exact with source clarification.** for Theorem 8's dual-induced tradeoff, actual-run slab accounting gives finite weighted perturbation at most `2N/k`; the source's `1 - 1/e` limit is unchanged. |
| [Theorem 8 suffix](docs/SOURCE_CLARIFICATIONS.md#theorem-8-finite-suffix-index) | **Exact after correcting the suffix-index typo:** exponent `k-i` and unspent fraction `(k-i)/k`. |
| [Section 4 tightness](docs/SOURCE_CLARIFICATIONS.md#section-4-tightness) | **Exact.** |
| [Section 6 variants](docs/SOURCE_CLARIFICATIONS.md#section-6-variants) | **Exact under additional charge and all-alive conditions.** Each possible charge must be small relative to its winner’s budget; the efficiency bound counts unit-cost arithmetic operations. |
| [Appendix A three-phase example](docs/SOURCE_CLARIFICATIONS.md#appendix-counterexample-three-phase-revenue) | **Exact counterexample after correcting the revenue calculation:** corrected phase revenue and residual service; the strict counterexample remains. |
| [`kappa>1` witness](docs/SOURCE_CLARIFICATIONS.md#the-kappa-witness-family) | **Corrected target.** The printed discrete family is unspecified; the checked continuous-limit witness has the stated endpoint behavior but does not claim a finite discrete family. |
| Section 8 retained formulas and definitions | **Exact.** [uncredited](docs/SOURCE_CLARIFICATIONS.md#section-8-weighted-bid-proposal) |

The formalization additionally proves explicit finite bounds for Theorem 8 and
an explicit finite family attaining the Section 4 tightness limit.

## 5. Remaining Boundaries and Gaps

- Sections 4--5 use the source's express exact-type/no-straddling slab
  idealization; the actual Theorem 8 route records and bounds its finite
  endpoint effect. The Appendix executions are continuous limits without
  fixed-positive-bid discretization bounds. Section 8's performance guarantees
  are open questions in the source.

## 6. Additional Assumptions Beyond Paper

The [Section 6 comparison](docs/SOURCE_CLARIFICATIONS.md#section-6-variants)
uses an effective-charge bound for every possible winner and a unit-cost
arithmetic model. Necessity of these conditions for other proof routes is not
established.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

- Separate finite accounting from the limiting competitive-ratio statement.
- Keep transformed-instance results auxiliary when the source's claim concerns
  the original AdWords setting.
- State the arithmetic cost model behind a finite-time scan claim.
- Derive spending states from prior allocations rather than stipulating the
  trajectory in an auxiliary certificate.
- Check both phase totals and claimed exhaustion before treating a printed
  numerical ratio as a source theorem.

## 9. Generalizations, Conjectures, and Extensions

The explicit finite Theorem 8 error bound and Section 4 family strengthen the
paper's limiting statements. See the [finite bounds](docs/SOURCE_CLARIFICATIONS.md#finite-and-limiting-theorem-8-readings)
and [tightness construction](docs/SOURCE_CLARIFICATIONS.md#section-4-tightness).

Optional extensions could refine the Appendix fluid certificate to a quantified
fixed-positive-`a` discretization theorem, analyze bit complexity for an
approximate implementation of the Balance scan, or investigate the Section 8
switching-distribution and many-representative RANKING proposals without
prejudging their open guarantees. None is required for source-level status.

## 10. Source Clarifications and Exact Readings

The [memo](docs/SOURCE_CLARIFICATIONS.md) gives the Theorem 9 query-split
lower-bound model, the finite suffix correction, the finite Lemma 7 slab
reading used by Theorem 8, the source-compatible finite Section 4 construction,
the corrected three-phase revenue, and the explicit $\kappa>1$ witness with
both endpoint limits. The corrected Appendix execution preserves the strict
counterexample to the naive rule.

## 11. Paper Issues or Caveats

The localized corrections and their unchanged limiting conclusions are
explained in Section 10; no additional boundary is asserted here.

## 12. Detailed Formalization Evidence

The checked development covers the operational allocation and charging model,
the finite and continuous tradeoff routes, the occurrence-indexed accounting,
the displayed factor-revealing programs, Lemmas 1--7, Theorem 8 and its
simple-proof accounting, the finite Section 4 tightness construction, Section
6 variants, Theorem 9, Section 8 definitions, and the checked Appendix claims
and corrected target. Lemma 1 constructs the selected Balance scan winner;
Lemmas 2 and 5 derive their idealized beta identities from the source's stated
slab convention; and the actual Theorem 8 runner supplies the finite Lemma
6--7 accounting and competitive bound. Theorem 9 ranges over the finite
nonanticipating count policies induced by the source's repeated-query `q_ij`
fractions, including within-round splits rather than a collapsed-round choice.

## 13. Paper Assumption Provenance

The source-to-statement map records the paper's temporary unit-budget and
exhaustive-optimum normalization used in the Theorem 8 route, together with
the finite small-bids condition. The source AdWords domain supplies
nonnegative bids and positive budgets. Finite histories index arrival
occurrences, so repeated query words are allowed; Section 6 click-through
rates lie in $[0,1]$. For Theorem 9, the source hard family records a policy by
the counts assigned to each visible bidder in each repeated-query round, with
the source's round and bidder capacities.

## 14. Displayed Formula Provenance

The source map binds the bid, spend, revenue, feasibility, LP, tradeoff,
competitive-ratio, and lower-bound formulas to their source spans. The
[clarifications memo](docs/SOURCE_CLARIFICATIONS.md) explains the Section 4--5
idealized slab reading, the finite Lemma 6--7 accounting, the Theorem 9
query-split payoff, the finite suffix correction, and the corrected Appendix
execution and revenue.

## 15. Library Lift Pass

Reusable AdWords definitions and the main finite accounting infrastructure
live in the shared online-AdWords library. The source-specific occurrence
runner, phase dynamics, and Appendix witness family remain paper-local; no
additional generic lift was justified.

## 16. DAG Audit

The [dependency DAG](docs/DependencyDAG.pdf) separates the finite Balance
results, the finite tightness construction, the Theorem 8 slab-limit route,
and the source's open Section 8 questions. The terminal rendering is visually
inspected for readable labels, arrowheads, ordering, overlap, and clipping.

## 17. Validation Checks

The current selected surface contains 50 source-result routes. Its direct
source-to-Spec review and the prerequisite-reuse ledger are current for the
saved Lean graph; the report and memo coverage assessment binds each material
reader-facing clarification to its explanation.

## 18. Paper Definitions Checked

The checked definitions include assignments, spend, revenue, feasibility,
small bids, fractional revenue and feasibility, the tradeoff function, the
Balance score, occurrence-level runner state, slabs, bidder and query types,
alpha/beta accounting, Section 6 charges, Section 8 switching and weight
updates, Theorem 9's hard distribution, query-split allocation counts, and
payoff, and the Appendix fluid inputs, allocations, derived state, and
$\kappa$ family.

## 19. Named Theorem Statements Checked

- Lemma 3 and Lemma 4 are formalized as stated. Theorem 9 is formalized in the
  source's query-split repeated-round normal form.
- Lemmas 1--2 and Lemma 5 use the source's stated idealized slab convention;
  Lemma 6--7 are formalized for the actual Theorem 8 dual-induced tradeoff
  with the finite slab clarification in Section 10.
- Theorem 8 has a source-normalized finite bound and an automatic small-bids
  limit; the generic query-sum error theorem is auxiliary.
- Section 6 variants are formalized with the stated proof restrictions.
- The Appendix counterexamples are formalized with the stated finite-reading
  corrections.
- Section 8 performance guarantees remain source open questions; its retained
  model definitions are checked without crediting the open guarantee.

## 20. Statement and Validation Records

The source-to-statement map, source-to-Spec screening, prerequisite review,
and closure receipt retain the detailed statement and validation evidence
summarized above. Their current graph and document bindings distinguish source
clarifications, corrected finite calculations, and uncredited open proposals.

## 21. Source-Coverage Audit Ledger

The source-to-statement map records the selected claims, supporting source
material, exclusions, and source locations. The report table and clarification
memo provide the corresponding reader-facing disposition for every material
source reading.
