# Final Validation Report: LBG24 Spatial Underreporting

Updated: 2026-09-06

## 1. Human Verdict

The formalization covers the calendar-time first-report model, the likelihood
factorization in Theorem 1 and Appendix Theorem 2, Lemma 1, Proposition 1,
and the principal likelihood formulas.

**Formalization gap:** Lemma 2 and the Appendix D.8.2 shifted-process claim
remain uncredited, and their proof repair is deferred. Their current proofs
use incompatible arrival-time premises.
[Explanation](docs/SOURCE_CLARIFICATIONS.md#lemma-2-conditioning-on-an-observed-first-report).

## 2. Closeout Status

- Completion status: formalized.
- Selected source surface: eight result or formula claims and nine distinct
  model, definition, or condition presentations.
- Selected paper result identifiers: Theorem 1; Appendix Theorem 2; Lemma 1;
  Proposition 1; Equations (2)--(7), (30)--(31), (33)--(34); the homogeneous
  reporting-delay formula.
- Deferred and uncredited: Lemma 2 and the Appendix D.8.2 shifted-process claim.
- The [human review packet](docs/HUMAN_REVIEW_PACKET.pdf) presents the exact
  source and semantic Lean surface for optional annotation. The interactive
  dashboard is an optional alternative to the PDF.
- This researcher-facing report does not itself issue machine acceptance; the
  canonical closeout record is `FINAL_CLOSURE_RECEIPT.md`.

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
| Lemma 1 | **Process clarified:** first reports inside a calendar-time window form the thinned-and-displaced Poisson process, including zero detection. [Reading](docs/SOURCE_CLARIFICATIONS.md#lemma-1-and-proposition-1-calendar-time-first-reports). |
| Proposition 1 | **Restricted construction:** two reporting/incident-rate pairs share one positive observed first-report rate. [Domain](docs/SOURCE_CLARIFICATIONS.md#lemma-1-and-proposition-1-calendar-time-first-reports). |
| Lemma 2; Appendix D.8.2 | **Deferred; uncredited.** The current arrival-time premises are incompatible. [Conditioning](docs/SOURCE_CLARIFICATIONS.md#lemma-2-conditioning-on-an-observed-first-report). |
| Theorem 1; Appendix Theorem 2 | **Exact.** |
| Equation (3) | **Endpoint convention:** nonnegative rates and positive exposure include the zero-count maximum-likelihood estimate. [Domain](docs/SOURCE_CLARIFICATIONS.md#equation-3-rate-estimation-convention). |
| Equations (2), (4)–(7), (33)–(34) | **Exact.** |

## 5. Remaining Boundaries and Gaps

[Lemma 2 and Appendix D.8.2](docs/SOURCE_CLARIFICATIONS.md#lemma-2-conditioning-on-an-observed-first-report)
require a consistent model of conditioning on an observed first report.
The current premises combine an unconditional exponential first-arrival law
with a fixed finite upper bound on that arrival.
Both appendix claims remain outside the selected formalization surface;
their proof repair is deferred. The main likelihood-factorization proof uses
a separate causal observation model. This is a formalization gap, not a
counterexample to the paper's claims.

## 6. Additional Assumptions Beyond Paper

Proposition 1's checked construction uses a positive observed first-report
rate; Lemma 1 separately includes the zero-detection process. The
[memo](docs/SOURCE_CLARIFICATIONS.md#lemma-1-and-proposition-1-calendar-time-first-reports)
states this restriction.

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

The [memo](docs/SOURCE_CLARIFICATIONS.md) specifies calendar-time first reports and Equation (3)’s nonnegative-rate endpoint. Section 6 states Proposition 1’s positive-rate scope, and Section 7 links the two likelihood-algebra corrections.

<!-- BEGIN GENERATED SETTLED REVIEW CONTEXT -->
<!-- settled-review-context-sha256: d1e306b2b8f6bb3d93ebfaf3f886bc4e4b4b7111955cad3935d5102cd37b6066 -->
<!-- settled-review-context-presentation-sha256: 2b6c571267628ce0df39723bfe0208580453ab292e44fa0a3dd8d0231e8a2257 -->
### Source readings and additional assumptions

- **Additional assumptions.** The additional conditions have their main discussion in Section 6 and the [clarification memo](docs/SOURCE_CLARIFICATIONS.md).
- The result-specific conditions and corrections are stated in the [clarification memo](docs/SOURCE_CLARIFICATIONS.md).
<!-- END GENERATED SETTLED REVIEW CONTEXT -->

## 11. Paper Issues or Caveats

Section 5 records the formalization gap in Lemma 2 and Appendix D.8.2.

## 12. Detailed Formalization Evidence

The selected review surface contains eight transparent source-claim Specs, eight
paired proof endpoints, fourteen source-mapped paper prerequisites, and two
source-mapped reusable-library prerequisites. The compact source-facing surface is
[PaperInterface.lean](PaperInterface.lean), and the paired proof routes are
collected in [ProofInterface.lean](ProofInterface.lean).

The current machine-readable evidence is:

- [source statement map](audit/paper_statement_map.json);
- [raw-source-to-expanded-Spec screening](FINAL_CLOSURE_RECEIPT.md);
- [paper-prerequisite semantic review](FINAL_CLOSURE_RECEIPT.md);
- [library-prerequisite semantic review](FINAL_CLOSURE_RECEIPT.md).

Each of the eight selected source claims has one semantic target and one proof endpoint;
the proof endpoint is not counted as a second paper claim.

## 13. Paper Assumption Provenance

The source-defined premise families are:

- stationary Poisson incident births, an incident lifetime distribution, and
  pre-death reporting;
- a nonnegative locally integrable report intensity and a nonnegative
  normalized duration density for Lemma 1;
- a positive-rate homogeneous Poisson report process for the homogeneous
  results;
- Condition 1's rate-free selected-start kernel and conditional independence
  from the post-first-report path;
- Condition 2's rate-free causal endpoint law and its absolutely continuous
  density presentation;
- positive exposure and the valid parameter domains for Poisson and
  zero-inflated likelihoods.

The reporting-process roots have passed their independent semantic review. The incompatible
arrival-time premises described in Section 5 remain confined to the deferred,
uncredited Lemma 2 and Appendix D.8.2 claims.

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
Conditions 1--2, checked claim clusters and two uncredited appendix claims,
likelihood consequences, city endpoint formulas, and the empirical scope boundary. The rendered PDF was
visually inspected after the scope update: labels and arrowheads are legible, reading
order is clear, and no node, edge, or legend overlaps another node.

## 17. Validation Checks

- The focused LBG proof-interface build passed for the current Lean surface.
- The eight selected proof contracts and their reporting-process roots have
  current semantic reviews. Lemma 2 and Appendix D.8.2 receive no proof credit;
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
| Lemma 2 | Deferred; not selected | No proof credit |
| Appendix D.8.2 shifted process | Deferred; not selected | No proof credit |

## 20. Semantic Review Ledger

The selected surface has eight source claims, fourteen paper-specific semantic
prerequisites, and two material library prerequisites. Existing judgments are
reused only when their exact source and semantic inputs are unchanged. The changed
reporting-process roots have passed independent semantic review. The two deferred
appendix claims receive no source-coverage credit.

Human annotation is optional; no human review is fabricated or inferred from
semantic screening.

The exact statements, source inputs, reasons, and reviewer fields are available
in the linked JSON ledgers in Section 12 and in the
[human review packet](docs/HUMAN_REVIEW_PACKET.pdf).

## 21. Source-Coverage Audit Ledger

The eight selected direct claims form the paper-result review denominator. The source
map also retains model declarations, Appendix proof support, observed-data
context, and the link between Theorem 1 and its Appendix Theorem 2 restatement.
Lemma 2 and the Appendix D.8.2 claim remain visible as source claims with explicit
scope exclusions and no proof or coverage credit. The fourteen paper prerequisites
and two library prerequisites are
semantic inputs rather than additional paper-result rows.
