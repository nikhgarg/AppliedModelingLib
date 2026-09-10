# Final Validation Report: Quantifying Spatial Under-reporting Disparities in Resident Crowdsourcing

Updated: 2026-09-09

## 1. Human Verdict

The paper’s reporting-process, likelihood, and estimation results are
formalized, including the first-report and waiting-time arguments.

## 2. Closeout Status

- Completion status: formalized
- One-sentence recap: The formalization establishes how incident and reporting
  rates determine observed reports and the likelihood used for estimation.

## 3. Source and Scope

- Paper: *Quantifying Spatial Under-reporting Disparities in Resident
  Crowdsourcing*.
- Authors: Zhi Liu, Uma Bhandaram, and Nikhil Garg.
- Source: [Nature Computational Science](https://doi.org/10.1038/s43588-023-00572-6),
  with the [official arXiv version](https://arxiv.org/pdf/2204.08620) used for
  stable public reading.

The mathematical scope covers the paper's incident-birth, lifetime, report,
first-report, observed-window, Poisson-regression, and zero-inflated models;
the selected named theoretical results; and the displayed formulas that define or
specialize their likelihoods. Empirical estimates, dataset reconstruction,
simulations, figures, software behavior, and the causal validity of the NYC
and Chicago administrative timestamps are not mathematical theorem targets.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Reporting delay | **Exact.** |
| Lemma 1 | **Exact with source clarification.** [First reports are counted by their reporting time](docs/SOURCE_CLARIFICATIONS.md#lemma-1-and-proposition-1-calendar-time-first-reports), including reports of incidents born before the observation window. |
| Proposition 1 | **Exact on the positive observed-rate domain.** [Positive observed rate](docs/SOURCE_CLARIFICATIONS.md#lemma-1-and-proposition-1-calendar-time-first-reports) permits two distinct positive incident rates to generate the same observed process. |
| Lemma 2; Appendix D.8.2 | **Exact with source clarification.** [Condition on an observed first report](docs/SOURCE_CLARIFICATIONS.md#lemma-2-conditioning-on-an-observed-first-report) and choose the observation start between that report and the horizon. |
| Theorem 1; Appendix Theorem 2 | **Exact with source clarification.** The continuous-time [selection probabilities are read as conditional densities](docs/SOURCE_CLARIFICATIONS.md#appendix-b2-likelihood-factorization-algebra). |
| Equation (3) | **Exact with source clarification.** [Rates may be zero and total exposure must be positive](docs/SOURCE_CLARIFICATIONS.md#equation-3-rate-estimation-convention), so zero observed reports give an attained maximum-likelihood estimate of zero. |
| Equations (2), (4)–(7), (33)–(34) | **Exact.** |

## 5. Remaining Boundaries and Gaps

None for the selected theoretical results.

## 6. Additional Assumptions Beyond Paper

Proposition 1’s construction uses a positive observed first-report rate.
Lemma 1 separately covers zero detection; see the [rate-domain note](docs/SOURCE_CLARIFICATIONS.md#lemma-1-and-proposition-1-calendar-time-first-reports).

## 7. Proof-Strategy Deviations

The [Appendix B.2 clarification](docs/SOURCE_CLARIFICATIONS.md#appendix-b2-likelihood-factorization-algebra)
gives the two local algebra corrections and explains why the stated likelihood
factorization is preserved.

## 8. Proof Tricks Worth Reusing

- Define the observed event in calendar time before applying Poisson thinning
  or marked displacement.
- Derive the zero-rate observed process as an explicit degenerate Poisson law
  instead of excluding the boundary with a strict-positivity convenience.
- Express a history-responsive observation end as one causal kernel on the
  visible prefix, keeping atoms such as deterministic caps within the model.
- Separate the Poisson count factor from a rate-independent start/endpoint
  factor before specializing to regression or zero inflation.

## 9. Generalizations, Conjectures, and Extensions

The checked first-report process uses stationary homogeneous incident births.
A nonstationary extension would require the corresponding nonhomogeneous
marked-displacement theorem. Covariate-indexed report intensities, other
duration laws, and alternate causal endpoint policies can reuse the same model
separation once their process laws and definedness conditions are supplied.

## 10. Source Clarifications and Exact Readings

The [memo](docs/SOURCE_CLARIFICATIONS.md) explains calendar-time first reports,
conditioning on the observed first report, continuous-time density notation,
and the local likelihood-formula corrections.

## 11. Paper Issues or Caveats

None beyond the clarifications above.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) states the selected results;
[ProofInterface.lean](ProofInterface.lean) connects them to their proofs.
The [source review](FINAL_CLOSURE_RECEIPT.md) and
[model review](FINAL_CLOSURE_RECEIPT.md) record their comparison
with the paper.

## 13. Paper Assumption Provenance

The source-defined premise families are:

- stationary Poisson incident births, an incident lifetime distribution, and
  pre-death reporting;
- a nonnegative locally integrable report intensity and a nonnegative
  normalized duration density for Lemma 1;
- a positive-rate homogeneous Poisson report process for the homogeneous
  results;
- Condition 1's rate-free selected-start kernel and conditional independence
  from the post-first-report path, presented by the source's rate-free
  conditional density at the observed start;
- Condition 2's rate-free causal endpoint law and its absolutely continuous
  density presentation;
- positive exposure and the valid parameter domains for Poisson and
  zero-inflated likelihoods.

The [model review](FINAL_CLOSURE_RECEIPT.md) records these
assumptions and their source locations.

## 14. Displayed Formula Provenance

| Paper item | Current disposition |
| --- | --- |
| Homogeneous reporting delay | Mean of the exponential report-delay law is `1/lambda`. |
| Equation (2) | Exact Poisson count mass. |
| Equation (3) | Count-over-exposure estimator and global maximum on the explicit domain. |
| Equations (4)--(5) | Exact exponential Poisson-regression link. |
| Equation (6) | Regression likelihood with a rate-independent residual. |
| Equation (7) | Structural-zero and ordinary-Poisson branches, plus the independent-family product. |
| Equations (30)--(31) | Corrected first post-start gap and residual multiplier used in the Appendix proof. |
| Equations (33)--(34) | Exact NYC and Chicago three-way minimum endpoint definitions. |

## 15. Library Lift Pass

The rate-times-exposure parameter and the forward homogeneous Poisson process
are the source-mapped reusable definitions. The process root specifies Poisson
increments at deterministic times; the finite observation model uses positive-rate
independent exponential gaps. Neither asserts a Poisson count law at an arbitrary
process-dependent random endpoint.
The full checked dependency graph also retains the exponential and Poisson
process models, observation windows, finite jump timelines, and their
measure-theoretic and probability foundations.

## 16. DAG Audit

The [Dependency DAG](docs/DependencyDAG.pdf) records the source models,
Conditions 1--2 and the checked Lemma 2/Appendix D.8.2 claim clusters,
likelihood consequences, city endpoint formulas, and the empirical scope boundary. The rendered PDF was
visually inspected after the scope update: labels and arrowheads are legible, reading
order is clear, and no node, edge, or legend overlaps another node.

## 17. Validation Checks

- The focused LBG proof-interface build passed for the current Lean surface.
- The ten selected proof contracts and their reporting-process roots have
  current semantic reviews. Lemma 2 and Appendix D.8.2 receive proof credit
  under the actual-first-report model;
  the [closeout record](FINAL_CLOSURE_RECEIPT.md) records acceptance for its
  pinned inputs.
- The human review packet is generated from that graph; the dependency DAG
  was compiled and visually inspected.

## 18. Paper Definitions Checked

The fourteen source-mapped paper prerequisites cover incident births and
lifetimes, reporting intensity and calendar-time first reports, the
nonidentifiability construction, selected starts and causal endpoints,
regression and zero-inflated likelihoods, and the NYC and Chicago observation
endpoints. Their exact source connections and declaration bodies are in the
[paper prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) and packet.

## 19. Named Theorem and Formula Statements Checked

| Paper claim | Transparent semantic target | Proof endpoint |
| --- | --- | --- |
| Homogeneous reporting-delay mean | `sourceHomogeneousReportingDelayMeanSpec` | `sourceHomogeneousReportingDelayMean` |
| Theorem 1 / Appendix Theorem 2 | `sourceTheorem1LikelihoodDecompositionSpec` | `sourceTheorem1LikelihoodDecomposition` |
| Equation (2) | `sourceEquation2PoissonCountPMFSpec` | `sourceEquation2PoissonCountPMF` |
| Equation (3) | `sourceEquation3MaximumLikelihoodEstimateSpec` | `sourceEquation3MaximumLikelihoodEstimate` |
| Equation (6) | `sourceEquation6PoissonRegressionLikelihoodSpec` | `sourceEquation6PoissonRegressionLikelihood` |
| Equation (7) | `sourceZeroInflatedLikelihoodExtensionSpec` | `sourceZeroInflatedLikelihoodExtension` |
| Lemma 1 | `sourceLemma1CalendarTimeDurationObservedProcessSpec` | `sourceLemma1CalendarTimeDurationObservedProcess` |
| Proposition 1 | `sourceProposition1CalendarTimeNonidentifiabilitySpec` | `sourceProposition1CalendarTimeNonidentifiability` |
| Lemma 2 | `sourceLemma2SelectedStartExponentialTailSpec` | `sourceLemma2SelectedStartExponentialTail` |
| Appendix D.8.2 shifted process | `sourcePostFirstJumpPoissonShiftSpec` | `sourcePostFirstJumpPoissonShift` |

## 20. Semantic Review Ledger

The selected surface has ten source claims, fourteen paper-specific semantic
prerequisites, and two material library prerequisites. Existing judgments are
reused only when their exact source and semantic inputs are unchanged. The changed
reporting-process roots have passed independent semantic review. The Lemma 2 and
D.8.2 endpoints are direct source-Spec-proof routes under the actual-first-report
model.

Human annotation is optional; no human review is fabricated or inferred from
semantic screening.

The exact statements, source inputs, reasons, and reviewer fields are available
in the linked JSON ledgers in Section 12 and in the
[human review packet](docs/HUMAN_REVIEW_PACKET.pdf).

## 21. Source-Coverage Audit Ledger

The ten selected direct claims form the paper-result review denominator. The source
map also retains model declarations, Appendix proof support, observed-data
context, and the link between Theorem 1 and its Appendix Theorem 2 restatement.
The fourteen paper prerequisites and two library prerequisites are
semantic inputs rather than additional paper-result rows.
