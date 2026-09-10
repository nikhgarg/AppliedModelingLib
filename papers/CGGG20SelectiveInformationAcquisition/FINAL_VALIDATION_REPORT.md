# Final Validation Report: Fair Allocation through Selective Information Acquisition

Updated: 2026-09-09

## 1. Human Verdict

The paper’s threshold-sufficiency results are formalized: after screening,
threshold allocation policies achieve the required utility, cost, and fairness
constraints.

## 2. Closeout Status

- Completion status: formalized
- One-sentence recap: Threshold policies suffice for the selected allocation
  problems, including the cost-aware and equality-constraint variants.

## 3. Source and Scope

Cai, Gaebler, Garg, and Goel, *Fair Allocation through Selective Information
Acquisition*, AIES 2020 / [arXiv v3](https://arxiv.org/abs/1911.02715v3).
The scope covers Theorem 2, Appendix Lemmas 4–5 and 7, Appendix Theorem 6,
and their model and threshold-policy definitions. The standalone linear
programs, empirical simulations, and runtime discussion are outside this scope.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Definition 1; Appendix Definition 3 | **Exact.** |
| Theorem 2; Appendix Theorem 6 and Lemma 7 | **Exact with source clarification.** Expected utilities [condition on the full vector of observed estimates used for allocation](docs/SOURCE_CLARIFICATIONS.md#full-vector-posterior-reading-for-allocation-policies), and the [equal-cost comparison covers every permitted threshold](docs/SOURCE_CLARIFICATIONS.md#appendix-theorem-6-threshold-domain-proof-route). |
| Appendix Lemma 4 | **Exact with source clarification.** [Reading](docs/SOURCE_CLARIFICATIONS.md#full-vector-posterior-reading-for-allocation-policies). |
| Appendix Lemma 5 | **Exact after correcting a typo.** [Interpolation](docs/SOURCE_CLARIFICATIONS.md#appendix-lemma-5-interpolation-display); [posterior reading](docs/SOURCE_CLARIFICATIONS.md#full-vector-posterior-reading-for-allocation-policies). |

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

Appendix Theorem 6 needs the equal-cost comparison for every possible
threshold. The proof extends that comparison to nonpositive cutoffs and both
infinite endpoints; see the [threshold proof note](docs/SOURCE_CLARIFICATIONS.md#appendix-theorem-6-threshold-domain-proof-route).

## 8. Proof Tricks Worth Reusing

None.

## 9. Generalizations, Conjectures, and Extensions

None.

## 10. Source Clarifications and Exact Readings

The [posterior reading](docs/SOURCE_CLARIFICATIONS.md#full-vector-posterior-reading-for-allocation-policies)
conditions utility estimates on all information observed by the allocation
rule. Appendix Lemma 5 has a [typo in its interpolation probability](docs/SOURCE_CLARIFICATIONS.md#appendix-lemma-5-interpolation-display);
correcting it preserves the stated utility and cost conclusions.

## 11. Paper Issues or Caveats

None.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) states the selected results;
[ProofInterface.lean](ProofInterface.lean) connects them to their proofs.

## 13. Paper Assumption Provenance

The positive-cost and exogenous-screening readings, and the full-vector
posterior reading used by full-vector allocation, are source clarifications.
They make the information and policy interpretation used by the displayed
model explicit; none is an additional economic assumption.

## 14. Displayed Formula Provenance

The linear-program displays support the allocation model. They are not
additional named theorems in the selected scope.

## 15. Library Lift Pass

The proof reuses Mathlib’s representation of a policy that depends only on
observed information.

## 16. DAG Audit

The [dependency diagram](docs/DependencyDAG.pdf) connects the screening and
allocation model to the threshold definitions, Appendix results, and Theorem 2.

## 17. Validation Checks

The paper build and independent mathematical review passed. The
[closeout record](FINAL_CLOSURE_RECEIPT.md) links the retained evidence.

## 18. Paper Definitions Checked

- Definition 1, Threshold Policy.
- Appendix Definition 3, Cost-Aware Threshold Policy.
- The shared screening-and-allocation model.

## 19. Named Theorem Statements Checked

### Theorem 2

**Paper statement.** A solution to the constrained problem can be replaced by
a threshold allocation after the screening policy is fixed.

**Status.** formalized.

### Appendix Lemma 4

**Paper statement.** A positive cost-aware threshold policy is not dominated at
equal cost or equal utility.

**Status.** formalized.

### Appendix Lemma 5

**Paper statement.** Achievable expected utility or expected cost targets can
be attained by cost-aware threshold policies.

**Status.** formalized; the source interpolation display is clarified in
Section 10.

### Appendix Theorem 6 and Appendix Lemma 7

**Paper statement.** Cost-aware threshold policies suffice, including when the
diversity inequalities are replaced by equality constraints.

**Status.** formalized.

## 20. Paper-Facing Statement Validator Ledger

The [statement review](FINAL_CLOSURE_RECEIPT.md) compares the
selected results with the paper; the [model review](FINAL_CLOSURE_RECEIPT.md)
checks their governing definitions and assumptions.

## 21. Source-Coverage Audit Ledger

The [source inventory](audit/paper_statement_map.json) covers the five named
results and their three governing model or definition records. The standalone
linear-program displays remain supporting material.
