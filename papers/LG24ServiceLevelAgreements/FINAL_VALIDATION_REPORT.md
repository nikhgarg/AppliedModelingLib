# Final Validation Report: LG24 Service Level Agreements
Updated: 2026-09-06

## 1. Human Verdict

**Formalized.** The five named propositions and two selected queueing/SLA
displays have closed proofs on the stated admitted-stream model. No paper-level
issue or additional assumption is recorded. Independent human review has not
yet been recorded.

## 2. Closeout Status

- Completion status: `formalized`.
- Scope: five named propositions, the stationary GPS response-tail display,
  and the all-request SLA rate-fraction display.
- Human review: not yet recorded.

## 3. Source and Scope

The source is the active private manuscript revision. The normal scope
is its five propositions: reciprocal capacity, extreme efficiency, extreme
equity, price of equity, and centralization gain. The stationary GPS
response-tail and all-request SLA rate-fraction displays are selected
supplemental targets. Algorithms, simulations, figures, captions, and ordinary
prose are not part of this formalization.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Proposition 2.1 (equivalent reciprocal-capacity representation) | **Exact.** |
| Propositions 2.2 and 2.3 (extreme efficiency and extreme equity) | **Exact.** |
| Proposition 2.4 (price of equity) | **Exact.** |
| Proposition 2.5 (centralization gain) | **Exact.** |
| Equation (1) (stationary response-time tail) | **Exact.** |
| Unnumbered all-request fraction consequence following Equation (2) | **Interpretation clarified:** stationary probability/intensity fraction, without a raw-arrival empirical-frequency limit. [Reading](docs/SOURCE_CLARIFICATIONS.md#meaning-of-the-all-request-fraction). |

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

None.

## 9. Generalizations, Conjectures, and Extensions

No additional generalization is established here.

## 10. Source Clarifications and Exact Readings

The [queueing memo](docs/SOURCE_CLARIFICATIONS.md#meaning-of-the-all-request-fraction) specifies the stationary probability/intensity interpretation of the all-request fraction; no raw-arrival empirical-frequency theorem is claimed.

## 11. Paper Issues or Caveats

None.

## 12. Detailed Formalization Evidence

The current review surface has ten transparent specification/proof pairs:
five named propositions, two queueing/SLA displays, and three supporting
optimization or relative-cost results. Their source-to-Lean judgments compare
the selected manuscript with the expanded mathematical definitions. Lean checks
the proof endpoints and their dependency closure.

The active queueing route constructs the stationary response tail from the
admitted-stream model. No tail certificate or stationarity witness is supplied
as a theorem premise.

## 13. Paper Assumption Provenance

No separate paper-facing assumption declaration is configured. The visible
premises of the active specifications are source model conditions or are
derived in Lean. In particular, neither a response certificate nor a
stationarity witness is a theorem-facing premise.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No paper-facing assumption declarations are configured. |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The selected response-tail and rate-fraction displays each have an exact
paper-facing `Spec` and theorem route. The tail is constructed from the active
source model; the rate fraction is derived from that tail rather than from a
separately supplied stochastic conclusion.

The supporting relative-centralization display also has its own specification
and proof. It uses the source's relative normalization and is available for an
arbitrary finite nonempty Borough domain; Proposition 2.5 separately requires
at least two Boroughs for its strict improvement.


## 15. Library Lift Pass

The optimization results use reusable finite minimization and algebraic tools.
The source-facing GPS/FCFS queue construction remains paper-local. Its active
proof route uses only the standard Lean logical axioms.

## 16. DAG Audit

The [dependency diagram](docs/DependencyDAG.pdf) ([TeX source](docs/DependencyDAG.tex)) follows the current five
propositions, the two selected queueing/SLA displays, and the supporting city
optimizer and relative-cost identities. Proposition 2.4 is the relative
all-request price-of-equity result; Proposition 2.5 is centralization.
The rendered PDF was visually inspected on 2026-09-06; its labels and nodes
are readable, with no clipping.

## 17. Validation Checks

All ten selected source-to-Lean comparisons are reviewed. The current
Lean-owned graph verifies their specification/proof pairings and contains no
placeholder proof or separate paper assumption. Strict closeout completed all
ten checks on 2026-09-06; the [closure receipt](FINAL_CLOSURE_RECEIPT.md)
records the accepted graph and focused build. Currentness can be checked with
`python3 scripts/final_closure_receipt.py --paper LG24ServiceLevelAgreements --check`.



## 18. Paper Definitions Checked

The paper-facing interface exposes the fixed-load feasibility, costs,
objectives, capacity-share and effective-load expressions used by the five
propositions. It also exposes the global SLA-subsystem steady condition, the
separate target-local margin, the stationary response-tail contract, and the
all-request response fraction needed for the selected displays. These are
source-facing vocabulary and formula context, not independent theorem credit.

## 19. Named Theorem Statements Checked

### Equivalent Reciprocal-Capacity Representation

**Paper statement.** The original fixed-load and reciprocal-capacity programs
have the same minimizers on the stated finite positive-feasibility domain.

**Lean interface.** `paper_prop_opt_reformulationSpec` and
`paper_prop_opt_reformulation` prove equality of the minimizer predicates for
every loss on the same domain.

**Status.** Formalized.

### Extreme Efficiency

**Paper statement.** The displayed square-root endpoint uniquely minimizes the
efficiency objective on the fixed-load feasible set.

**Lean interface.** `paper_prop_extreme_efficiencySpec` and
`paper_prop_extreme_efficiency` retain the source domain and the complete
minimizer-plus-uniqueness conclusion.

**Status.** Formalized.

### Extreme Equity

**Paper statement.** There is an efficiency-best equitable endpoint with a
common all-request cost within each category.

**Lean interface.** `paper_prop_extreme_equitySpec` and
`paper_prop_extreme_equity` prove the existential endpoint and its category
cost-level conclusion.

**Status.** Formalized.

### Price of Equity

**Paper statement.** The relative price has the printed Pearson identity,
bounds, zero characterizations, and capacity-scaling classification.

**Lean interface.** `paper_prop_price_of_equitySpec` and
`paper_prop_price_of_equity` prove all displayed clauses from the stated
finite fixed-load model.

**Status.** Formalized.

### Centralization Gain

**Paper statement.** With at least two Boroughs, city-level centralization has
the displayed strict-delay improvement and relative-gain comparison.

**Lean interface.** `paper_prop_centralizationSpec` and
`paper_prop_centralization` retain the nontrivial-Borough condition and prove
both source clauses.

**Status.** Formalized.

### Selected Queueing Displays

`paper_stationary_gps_response_tail` and
`paper_sla_from_stationary_gps_tail` respectively prove the selected stationary
tail and all-request Palm/intensity fraction under the visible source-model
conditions. Both are formalized; neither imports a cited-tail conclusion.

## 20. Paper-Facing Statement Validator Ledger

The current [source-to-Lean ledger](FINAL_CLOSURE_RECEIPT.md)
records ten matching independent agent comparisons. These include the expanded
model definitions governing each statement. No independent human row review
has been recorded.

| Source result | Specification/proof family |
| --- | --- |
| Proposition 2.1 | `paper_prop_opt_reformulation` |
| Proposition 2.2 | `paper_prop_extreme_efficiency` |
| Proposition 2.3 | `paper_prop_extreme_equity` |
| Proposition 2.4 | `paper_prop_price_of_equity` |
| Proposition 2.5 | `paper_prop_centralization` |
| Stationary GPS tail | `paper_stationary_gps_response_tail` |
| All-request SLA fraction | `paper_sla_from_stationary_gps_tail` |
| Relative price nonnegativity | `paper_relative_price_of_equity_nonnegative` |
| City efficiency endpoint | `paper_city_extreme_efficiency` |
| Relative centralization identity | `paper_relative_centralization_gain_identity` |

## 21. Source-Coverage Audit Ledger

The [source map](audit/paper_statement_map.json) and
[active-version map](DRAFT_VERSION_MAP.md) select the five propositions in the
current manuscript, the two queueing/SLA displays, and three supporting
results listed above. Each has one reviewed specification and proof route.
Definitions are inspected within their governing result's expanded comparison;
they do not add result credit. The [review packet](docs/HUMAN_REVIEW_PACKET.pdf)
collects those source-to-Lean comparisons for human assessment.
