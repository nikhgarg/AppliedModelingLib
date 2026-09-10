# Final Adversarial Source Audit: PG23MonocultureMatching

## Overall status: PASS
- Reviewed final holistic audit surface identity: `9f5ab0ade280477b44af916c7a45a94d35d192d897157588926545ea8d75ebc7`
- Final audit scope: `complete_current_surface`

Reviewer: `context-isolated:/root/pg23_final_audit_703`.

This is an independent terminal source audit. I did not author or repair the
formalization, issue its semantic judgments, or read earlier final audits or
authoring histories. I read the final-audit template and current formalization
protocol, and validated `formalization-audit-protocol-2026-09-01`. The frozen
surface uses the historical schema-2 single-review contract; no panel or new
source-region partition is required.

## Material independently inspected

I read all 724 lines of `audit/cited publication`, including the model,
named main-text results, appendix statements and their surrounding proofs. I
also read the cited Azevedo--Leshno domain at
`cited publication:433-435` in its surrounding continuum
model context. I compared the source with all 13 current transparent result
targets, the 37 routed paper prerequisites, their retained definitions, the
selected proof endpoints, and their Lean-owned dependency and axiom records.
This was a complete source-first challenge, not a recheck confined to a repaired
lemma.

The planner receipt is
`reviewer-owned review storage/closeout_execution_plan.9efabbe1b6a99140c244bcac24951a2cd50315a6f39d500fe9832cfe0ef02666.json`.
Its final surface object has byte SHA-256
`d956ac93a8836b0c28ffb76a488b452d400d677540a705b73732640420f99553`;
the repository's review-material projection computes the reviewed identity
stated above. Its Lean review graph has SHA-256
`a25bb5a701162a181dd01ea253abebbf1226bc1d637aacc27a7cc28ce0169559`.
Every present content input in that receipt matched its current file hash.
All 85 source-anchor occurrences in the statement map were found verbatim in
their specified source artifacts.

I inspected `PaperInterface.lean`, the selected endpoints and supporting
routes in `ProofInterface.lean`, the actual favorite-affordable selectors and
source-stability route, and the graph's complete expanded semantic displays.
Those displays comprise 56 paper declarations and 36 retained library
declarations: 37 selected prerequisites and 55 supporting declarations.
The normal trusted frontier is Init, Lean, Std, Batteries, and Mathlib; the
graph reports no unregistered external root.

I read the typed statement map, the current 13-row source-to-Spec ledger, the
37-row paper-prerequisite ledger, the empty directly selected library ledger,
the assumption surface, the source-proof-fidelity record, and each current
corrected-target record and its pinned provenance. I also inspected the final
validation report, source clarification memo, dependency DAG, README, status
projection, and current human-review packet. All 13 expanded result displays
and all 92 governing declaration displays in the packet match the frozen
graph after whitespace normalization.

## Source-to-Lean challenge

The anchors below refer to `audit/cited publication`. The named Specs
are in `PaperInterface.lean`, with corresponding `_proof` endpoints in
`ProofInterface.lean`.

| Selected result | Independent comparison |
| --- | --- |
| Supply and Demand, lines 38-43; `review_lemma1_supplyDemandSpec` | The source matching includes exact capacities, measurable fibers, and open strict-improvement sets. Stability is absence of the source blocking pair. The target retains both directions and pointwise equality with favorite-affordable choice at a clearing vector, for arbitrary induced applicant-type probability laws. Positive equal capacities sum to the stated subunit supply. |
| Equal Cutoffs, lines 71-74; `review_lemma2_equalCutoffsSpec` | Both common-noise and iid-noise economies retain connected supports and the recorded score-level-null condition. Each conjunct gives existence, uniqueness against every clearing vector, and equality of every coordinate. The condition is visible and covered by the corrected-target record. |
| Probability Formula, lines 81-95; `review_proposition_probabilityFormulaSpec` | The matching events use weak affordability. Atomless noise justifies their equality with the printed strict common-noise and maximum-noise tails. The product law, finite positive college count, fixed-value domain, and both event conclusions agree. |
| Corollary 4, lines 100-105; `review_corollary4_monocultureCutoff_lt_polycultureCutoffSpec` | The conclusion is the correct direction, `Pmono < Ppoly`, with at least two colleges, equal total supply, literal clearing, connected supports, and the recorded nondegeneracy and boundary conditions. The adjacent unnumbered intuition sentence does not create a second claim. |
| CDF proposition, lines 159-166; `review_proposition_cdfIncreasing_connectedSupportSpec` | The generic probability law yields the value-law and noise-law clauses. Strict increase and range `(0,1)` hold on the support interior, also for every positive integer power. No endpoint CDF identity is assumed. |
| Positive interval mass, lines 176-185; `review_proposition_nonzeroMeasure_openIntervalSpec` | The target is the recorded correction: an open interval meeting the support interior has positive mass. It does not assert positive mass for a singleton. |
| Lattice proposition, lines 188-200; `review_proposition_latticeSpec` | The target covers the nonempty clearing carrier and its lattice order, and identifies bounds of nonempty clearing families with coordinatewise real suprema and infima. The proof transports the cited continuum result through a strictly increasing score normalization and establishes that clearing cutoffs lie in its invertible interior. The cited score-level-null antecedent is explicit. |
| Lemma 10, lines 324-340; `review_lemma10_threePartSpec` | The low/high bounds are eventual uniformly over values on the indicated sides of the adjusted cutoff, with the source `delta/3` separation. Convergence of that cutoff to `vS` is equivalent to the source's eventual `2 delta/3` bound for every positive delta. The proof derives the weak match-probability integral from literal clearing, then uses concentration and connected-support strict tail separation. It adds no atomlessness premise and assumes no cutoff-convergence conclusion. |
| Theorem 1, lines 539-558; `review_theorem1_wisdomSpec` | The two pointwise limits exclude the threshold itself, as the source does. Monoculture probability and welfare are invariant in the number of firms. The welfare limit is the efficient upper-tail integral and the monoculture comparison is strict. Atomless value/noise laws, score-level nullity, nondegenerate noise, and absolute integrability are exposed in the applicable clauses and covered by the recorded corrected target. |
| Theorem 2, lines 609-628; `review_theorem2_topChoiceSpec` | All three corrected clauses are present: weak top-choice dominance with a positive-mass strict region, every monoculture match at the top rank, and pointwise eventual overall-match advantage on a positive-mass region above the efficient threshold. Zero-based Lean rank represents the source's first choice. Atomlessness supports the literal weak-event formulation, and eventuality remains inside the value quantifier. |
| Differential Equal Cutoffs, lines 681-684; `review_lemma_equalCutoffs_differentialAccessSpec` | Both source economies draw the access count independently and restrict affordability to the highest-ranked active colleges. The two corrected conjuncts give existence, uniqueness, and common coordinates under the visible score-level-null and connected-support conditions. |
| Nash proposition, lines 689-691; `review_proposition_nash_differentialApplicationAccessSpec` | The frozen corrected target is expressly a finite ex-ante favorite-success payoff comparison with same-cardinality feasible deviations, ranking-monotone utility, an outside option, and application-set-invariant iid success indicators. The target and proof preserve exactly that scope; it is not treated as archival equivalence or as an unrestricted application game. |
| Theorem 3, lines 705-719; `review_theorem3_differentialApplicationAccessSpec` | Literal differential monoculture choice probability equals the baseline and is independent of the positive count. The proof derives baseline cutoff equality from clearing with atomless values. Polyculture uses `1 - Pr[X < P-v]^k`, preserving boundary atoms; count monotonicity is strict on the support interior. Fixing a ranking does not change the existence-of-an-affordable-college event. |

I checked the governing model declarations as mathematical definitions:
strict complete rankings and real score vectors; uniform ranking and independent
value/noise product laws; common versus iid noise; weak affordability and
favorite choice; matching fibers, capacity equality, openness, and blocking;
connected supports; expected finite maxima and concentration; the upper-tail
threshold; coordinatewise cutoff operations; and independent positive access
counts with top-ranked active application sets. The expected-maximum predicate
exposes finite expectation rather than silently using a totalized integral.
The value-threshold certificate records only the source tail equation, not a
result about convergence or welfare. Retained library definitions were expanded
and inspected rather than accepted by their names.

## Coverage, proof boundaries, and human artifacts

The current inventory has 28 source items: 13 asserted results and 15 governing
prerequisite items routed to 37 declarations. The semantic surface therefore
has 50 rows. Four result judgments are direct matches and nine use the
explicit corrected-target disposition. The 23 recorded deep-audit candidates
do not enter the result denominator. The 23 prose-definition presentations
comprise 12 normal definitions, 10 local-notation dispositions, and one repeated
definition; I found no omitted selected named result or duplicate result credit.

All 13 graph-owned Spec/proof relations are exact and proved. Every selected
endpoint has a checked axiom closure containing only `Classical.choice`,
`Quot.sound`, and `propext`, with no unsafe route or `sorry`. A text search over
the paper's Lean modules found no `sorry`, `admit`, or `axiom` token. The paper
entrypoint imports both interfaces. Legacy theorem packages in `Assumptions.lean`
do not become extra selected theorem premises, and no source conclusion is
discharged by a conclusion-bearing certificate argument.

The current report and memo disclose the support, regularity, welfare, and
finite-game qualifications; the packet gives archival source before the
corrected target and distinguishes the two judgment kinds. The DAG states
paper conclusions and their dependencies. The human denominator is 13, with
zero human annotations recorded; this audit does not fabricate any annotation.
The illustrative uniform example remains a narrative source note, not a
fourteenth checked paper claim.

This audit ran no build, issued no semantic judgments, and changed no source,
Lean, map, ledger, report, DAG, packet, or status file. Historical build and
acceptance artifacts are not used as current acceptance evidence. The strict
worker's subsequent full gate and credential issuance remain separate from
this audit; pending post-audit status text is not a missing pre-audit artifact.

## Findings and counts

- Blocking findings: **0**.
- Actionable semantic, proof-boundary, scope, or mathematical reporting findings: **0**.
- Selected result targets inspected: **13/13**.
- Routed prerequisite declarations inspected: **37/37**.
- Current semantic-review rows inspected: **50/50**.
- Full canonical source inspected: **724/724 lines**, plus cited governing context.

The frozen current surface supports PASS under its recorded corrected-target
dispositions and the protocol's main-text review intensity. This conclusion
does not assert the unqualified archival statements beyond those dispositions.
