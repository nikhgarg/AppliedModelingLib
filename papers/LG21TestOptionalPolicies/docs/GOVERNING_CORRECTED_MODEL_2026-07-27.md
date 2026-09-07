# Governing Clarified Component: LG21 Theorem 3.2

## Authority and Scope

Recorded on 2026-07-27 from the repository user. This artifact governs the
approved **Theorem 3.2 component** of the LG21 remediation. It is evidence for
that component and for the local source-proof repairs listed below. The
whole-paper closeout incorporates this approved Theorem 3.2 target only after
the independent named-theory audit is current. This artifact neither claims
archival equivalence nor authorizes a material restriction of the Section 4
protocols.

The archival baseline is `cited publication`, SHA-256
`11fb7a52959948847ce19d85adf97256a30c3f1575941ff6efec0e33bf908e1c`.
The source permits randomized policies at lines 209--218. Its literal
arbitrary-randomized-policy Theorem 3.2 is therefore not claimed as a Lean
theorem: `PaperInterface.theorem3_2_gaussian_randomized_policy_counterexample`
checks a nondegenerate-Gaussian, observably fair, nonblank weak equilibrium for
that reading.

The approved component target is the explicit operational model in
`LG21ClarifiedTheorem32Model`. It is not an adapter from bare source Definition
1 data. Each supplied equilibrium/fibre carries the particular Definition 1,
fairness, law-link, probability, measurability, and expectation consequences
used by the proof. No checked declaration derives that record from every
archival Definition 1 equilibrium.

## Approved Theorem 3.2 Target

The two paper-facing component endpoints are:

- `PaperInterface.theorem3_2_optional_reporting_clarified_model`
- `PaperInterface.theorem3_2_report_required_clarified_model`

For each independent optional-reporting or report-required schedule, output on
the entire reported-score branch is deterministic, `dirac (f score)`. The
no-report/no-take branch remains an arbitrary common probability law. The
report-required Gaussian schedule has nonzero population and noise variances
and finite reporter expectations for every shifted Gaussian score law.
Blankness is operational: zero reporting/taking is blank by the approved
convention; otherwise the realized kernel equals the base law almost
everywhere.

This narrows the archive's arbitrary randomized policy class, makes finite
expectations explicit, and fixes the operational almost-everywhere reading. It
does not claim a derivation from bare Definition 1 or literal archival
equivalence.

## Local Repairs Recorded Here

These entries record checked local mathematics. They do not close a named
source result whose source-model bridge remains open.

| Correction ID | Archive anchor | Local correction | Boundary retained |
| --- | --- | --- | --- |
| `LG21-CORR-THEOREM31-NONREPORT-MIXTURE-2026-07-27` | `cited publication:1134-1172; cited publication:1233-1267` | The access-side no-report mass is `C * Pr(score < c) = C * (1 - A(c))`, with the corresponding normalized pooled estimate. | Theorem 3.1 still lacks a bridge from the source equilibrium/model to the conditional Lean routes. |
| `LG21-CORR-THEOREM31-CONTINUITY-2026-07-27` | `cited publication:1268-1390` | Gaussian lower-tail mass and first-moment continuity, denominator positivity, and endpoint signs are proved before the fixed-point step. | This repairs an analytic step only; it does not establish the source-wide Theorem 3.1 endpoint. |
| `LG21-CORR-THEOREM32-CLARIFIED-OPERATIONAL-MODEL-2026-07-27` | `cited publication:199-218; cited publication:256-395; cited publication:455-461; cited publication:1614-1778` | The approved deterministic reported-score, arbitrary base-law, finite-expectation, independent-schedule, operational-a.e. target stated above. | This is the only user-approved material model correction in this artifact. |
| `LG21-CORR-THEOREM32-DEMOGRAPHIC-TYPO-2026-07-27` | `cited publication:1770-1782` | The final summary word is read as `observable`, not `demographic`. | Hidden-access demographic fairness remains source-declared open. |
| `LG21-CORR-LEMMA41-TEST-CUTOFF-2026-07-27` | `cited publication:2183-2220; cited publication:2262-2310` | The raw score solving `intercept + slope * score = qTilde` is the affine inverse of `qTilde`. | This is a local equation correction and lower-tail diagnostic, not a proof of Lemma 4.1's all-taking endpoint. |
| `LG21-CORR-PROPOSITION43-MARGINAL-2026-07-27` | `cited publication:2495-2505` | A direct unconditional Gaussian precision gap replaces the invalid conditional-to-marginal inference. | The source population, behavior, and actual-law bridge for Proposition 4.3 remains open. |

## Boundaries of This Artifact

The following distinctions remain visible in the paper status, source map,
and proof-fidelity ledger.

1. **Theorem 3.1 source-model bridge.** The checked fixed-point and conditional
   routes do not yet derive the advertised every-equilibrium statement from one
   source Gaussian population, access process, and Definition 1 equilibrium.
2. **Section 4 operational convention.** Lemma 4.1's voluntary protocols are
   governed separately by
   `docs/GOVERNING_VOLUNTARY_ACTIVE_BRANCH_REFINEMENT_2026-07-31.md`. That
   memo makes the source's known-decision-function/unravelling reading
   explicit through source-timed self-enforcing positive-mass candidates and
   fibrewise maximal active branches. It proves selected actions only almost
   everywhere and never assigns a PBO or payoff to a null branch. It is not a
   Theorem 3.2 correction, an additional source assumption, or a claim that
   arbitrary static-RCD completions are unique.
3. **Section 4 actual-law route.** Under that recorded operational convention,
   the direct Proposition 4.2, Proposition 4.3, and Theorem 4.4 endpoints
   derive actual output-law comparisons from the selected actions. The legacy
   conditional all-protocol routes remain diagnostic support rather than the
   source-facing endpoints.

No future closeout may turn a finite off-path payoff into `-infinity`, silently
restrict the source to the mandatory protocol, or obtain source credit merely
by reusing a conditional wrapper.

## Checked Realization

`ClarifiedTheorem32Model.lean` is the governing component model surface. The
optional theorem is proved in
`Theorem32ContinuousDeterministicReporterRepair.lean`; the report-required
theorem is proved in `Theorem32ReportRequiredGaussianConclusion.lean`, using
checked Gaussian tilt, all-shift integrability, and convolution rigidity.

`PaperInterface.lean` retains the archival randomized-policy counterexample
and the legacy Section 4 conditional routes as diagnostics. Their presence is
not positive source-result evidence. The whole-paper closeout separately
requires a current semantic contract for the approved Theorem 3.2 model and a
current semantic receipt for the Section 4 convention; neither is supplied by
this document alone.
