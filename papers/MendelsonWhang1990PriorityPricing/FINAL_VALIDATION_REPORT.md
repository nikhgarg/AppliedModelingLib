# Final Validation Report: Optimal Incentive-Compatible Priority Pricing for the M/M/1 Queue

Updated: 2026-09-07

## 1. Human Verdict

Formalized. The selected surface covers Appendix (A-1) and Theorems 1--4 of
the stationary priority-pricing model. Theorem 3 uses the source's
stationary feasible-flow domain and its PTD schedule-and-assignment notion.

## 2. Closeout Status

- Completion status: formalized.
- Selected results: Appendix (A-1) and Theorems 1--4.
- Independent source-to-statement, prerequisite, and final adversarial
  reviews are complete; the accepted closeout is current.

## 3. Source and Scope

Haim Mendelson and Seungjin Whang, *Optimal Incentive-Compatible Priority
Pricing for the M/M/1 Queue*, *Operations Research* 38(5), 1990, pp. 870--883.
The selected results concern stationary priority queueing, marginal-externality
pricing, homogeneous and time-dependent priority pricing, and cheating
penalties.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Appendix (A-1) | **Exact.** |
| Theorem 1 | **Exact for interior domain.** The selected class has positive optimal arrival rate. [Condition](docs/SOURCE_CLARIFICATIONS.md#positive-flow-and-interior-reading). |
| Theorem 2 | **Exact for strict domain.** Every class has positive arrival rate. [Condition](docs/SOURCE_CLARIFICATIONS.md#effect-on-the-theorem-conclusions). |
| Theorem 3 | **Exact for strict domain.** Every class has positive arrival rate. [Condition](docs/SOURCE_CLARIFICATIONS.md#effect-on-the-theorem-conclusions). |
| Theorem 4 | **Exact for strict domain.** Every class has positive arrival rate. [Condition](docs/SOURCE_CLARIFICATIONS.md#effect-on-the-theorem-conclusions). |

## 5. Remaining Boundaries and Gaps

None for the selected current targets. The archival zero-flow formulations of
the strict conclusions are not claimed as strict results; the source
clarification explains the relevant adjacent-flow factor.

## 6. Additional Assumptions Beyond Paper

- **Theorem 1:** positive optimal arrival rate for the selected class. At zero
  flow the first-order condition can be one-sided; necessity of positivity
  for the identity is not established. [Details](docs/SOURCE_CLARIFICATIONS.md#positive-flow-and-interior-reading).
- **Theorems 2–4:** positive arrival rates for every class, for strict priority
  comparisons. An unused adjacent priority can permit indifference; full
  positivity is sufficient, not proved necessary in every case. [Details](docs/SOURCE_CLARIFICATIONS.md#effect-on-the-theorem-conclusions).

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

The PTD argument separates the expected direct charge of a reported priority
from the customer's own service-time law, then compares total expected costs
through a single penalty difference. This keeps incentive compatibility tied
to the schedule itself rather than to a preselected reported class.

## 9. Generalizations, Conjectures, and Extensions

A boundary extension could state weak best-response and weak penalty
conclusions at zero-flow priority levels. It is not needed for the selected
strict interior targets.

## 10. Source Clarifications and Exact Readings

The [source clarification memo](docs/SOURCE_CLARIFICATIONS.md) gives the
positive-flow interior reading for Theorem 1 and the strict-comparison reading
for Theorems 2--4.

## 11. Paper Issues or Caveats

The strict priority comparisons are interior statements. At an unused
adjacent priority level, the displayed comparison factor can vanish; this does
not affect the checked full-positive stationary result.

## 12. Detailed Formalization Evidence

The paper-facing interface has five transparent result targets with exact
proof endpoints: Appendix (A-1) and Theorems 1--4. The PTD optimality
definition is represented directly as source semantic context for Theorem 3.

## 13. Paper Assumption Provenance

The source model supplies stationary Poisson arrivals, positive exponential
service means, nonpreemptive priority, nonnegative flow, and strict offered
load stability. Theorem-specific positive-flow conditions are documented in
the source clarification memo.

## 14. Displayed Formula Provenance

The [source map](audit/paper_statement_map.json) records the stationary
queueing formula, marginal externality price, homogeneous and PTD prices, and
cheating penalty against their source passages.

## 15. Library Lift Pass

The reusable layer supplies stationary marked-Poisson inputs, selected-arrival
service laws, nonpreemptive-priority work accounting, and finite mean-wait
algebra. The pricing schedules and numbered theorem statements remain
paper-specific.

## 16. DAG Audit

The [dependency DAG](docs/DependencyDAG.pdf) follows the source order from the
queueing model and welfare objective through Theorem 1, the homogeneous route,
and the PTD route to Theorems 2--4. The PTD equilibrium criterion and Theorem
3 are shown as formalized nodes. The rendered DAG was visually inspected for
readable labels, arrowheads, reading order, and node or edge overlap.

## 17. Validation Checks

The selected source statements, semantic prerequisites, and complete paper
build have passed their recorded checks. Final adversarial review and strict
closeout are complete; see the [accepted record](FINAL_CLOSURE_RECEIPT.md).

## 18. Paper Definitions Checked

Checked definitions include stationary class input, priority queueing time,
the net-value objective, marginal externality, homogeneous and
time-dependent prices, expected total cost under a declared priority, the PTD
equilibrium criterion, and the cheating penalty.

## 19. Named Theorem Statements Checked

- Appendix (A-1): stationary mean queueing time.
- Theorem 1: marginal-externality pricing for a participating class.
- Theorem 2: homogeneous strict priority self-selection on the full-positive
  stationary interior.
- Theorem 3: PTD optimality, expected externality charge, and strict
  assigned-priority choice on the full-positive stationary interior.
- Theorem 4: truthful zero penalty and strict off-priority penalty growth on
  the full-positive stationary interior.

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) records
the current direct statement review. The paper and library prerequisite
ledgers record the source-semantic conditions used by those targets.

## 21. Source-Coverage Audit Ledger

The [source map](audit/paper_statement_map.json) retains five selected result
routes and the source definitions that provide their semantic context. The
result table in Section 4 and the source clarification memo record the only
material target qualifications.
