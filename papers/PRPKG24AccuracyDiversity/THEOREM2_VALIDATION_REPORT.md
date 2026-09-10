# Validation Report: PRPKG Theorem 2

## Scope

- Paper: *Reconciling the Accuracy-Diversity Trade-off in Recommendations*
- Source: `PRPKG24AccuracyDiversity.txt:537-553`
- Review surface: `papers/PRPKG24AccuracyDiversity/PaperInterface.lean`
- Correction record: `docs/THEOREM2_MODEL_CORRECTION_2026-07-27.md`

This is a source-fidelity report for Theorem 2, not a whole-paper closeout.
The four corrected endpoints are implemented and have current semantic,
source-record, and coverage receipts. The whole paper is formalized under the
corrected source target recorded in `FINAL_VALIDATION_REPORT.md`.

## Source Defect

The source header says the conditional values `X_i^(t)` are iid Bernoulli,
while also assigning `q_i = c*((i+1)+d)^(-alpha)`. When the displayed schedule
varies by rank, the coordinates cannot be identically distributed. The former
numeric product and sum objectives therefore did not by themselves establish
a literal source probability model.

This is correction `PRPKG24-THEOREM2-RANK-VARYING-IID-01`. The archival iid
wording is not claimed as formalized.

## Corrected Model and Checked Bridge

For each type and finite count `q`, the checked law is an independent product
of Boolean coordinates indexed by `Fin q`, with

```
P[X_i^(t) = 1] = c*((i+1)+d)^(-alpha).
```

`Theorem2RankBernoulliSource.lean` constructs this finite law with `pmfPi`,
proves its atom product formula, and proves:

- expected top-one value is `1 - product_i (1-q_i)`;
- expected all-consumed value is `sum_i q_i`; and
- the existing count objectives equal those literal expectations.

No cross-type independence is asserted or needed: conditional values are
evaluated only after selecting a preferred type.

The probability domain is visible: `c >= 0`, `d >= 0`, `alpha >= 0`, and
first-rank probability `q_1 <= 1`. Top-one universal-optimizer endpoints
also require `c > 0`, `q_1 < 1`, and positive type likelihoods. These exclude
the flat `c = 0` case and the `q_1 = 1` tie-degenerate case. Positive-alpha
all-consumed requires `c > 0` and `q_1 <= 1`; alpha zero uses the selected
likelihood-argmax all-on optimizer correction instead of a `1/0` exponent.

## Corrected Endpoints

| Source part | Paper-facing endpoint | Checked conclusion |
| --- | --- | --- |
| 2(i), `0 <= alpha < 1` | `theorem2_i_corrected_source_model_endpoint` | Literal rank-varying finite expectation plus uniform type shares. |
| 2(ii), `alpha = 1` | `theorem2_ii_corrected_source_model_endpoint` | Literal rank-varying finite expectation plus shares proportional to `p_t^(1/(1+c))`. |
| 2(iii), `alpha > 1` | `theorem2_iii_corrected_source_model_endpoint` | Literal rank-varying finite expectation plus shares proportional to `p_t^(1/alpha)`. |
| 2(iv), `alpha >= 0` | `theorem2_iv_corrected_source_model_endpoint` | Positive-alpha literal expectation plus power shares; alpha-zero literal expectation plus selected likelihood-argmax all-on optimum. |

Each endpoint conjoins the literal finite-law identity with the result, so a
numeric asymptotic theorem cannot receive source-model credit by name alone.

## Current Audit Disposition

Theorem 2(i)--(iv) are recorded as corrected source statements with
archival-equivalence disabled. The current source map and fidelity ledger retain
the correction ID, source anchors, corrected target, and this correction
record's pinned hash. Current v10 receipts support the formalized whole-paper
status; this theorem-specific report does not create a second status verdict.
