# Formalization Status Policy

Public display guidance updated: 2026-09-06

`config/formalization_audit_protocol.json` is the normative machine-readable
policy matrix for the operational categories summarized here. This document
supplies the status rationale and defers to that protocol if current category
labels or rules conflict.

This policy separates three questions that were previously conflated:

1. Did Lean close the intended paper endpoint?
2. Does the formalized endpoint require a demonstrated source correction?
3. Is the source-to-Lean evidence ready for release certification?

The paper's mathematical status answers the first two questions. Certification
is a separate validation axis and does not change mathematical status.

## Public Display And Technical Status

The categories below describe technical mathematical status and audit
disposition. The public website uses a separate presentation: **Formalized**
with theorem-specific **Formalization gap:** notes for substantial uncovered
scope; LOS02 and LMMS04 retain their earlier **Partially formalized** labels.
See [the display policy](STATUS.md#public-website-display). A display label
does not grant semantic acceptance or erase an unresolved proof obligation.

The **Completion status** line in a public paper's final validation report uses
this same reader label and the same catalog exceptions. Private reports retain
their technical status. Report sections still identify the actual formalization
gaps and whether review or closeout is pending; the display rule does not change
`status.json`, semantic judgments, or release eligibility.

Reader reports use concise comparisons: **Exact**, **Source clarification**,
**Typo fixed**, **Additional assumption**, or **Formalization gap**, as the
source comparison warrants. Describe the original and formalized statements
precisely in the memo. An unproved implication is a formalization gap; do not
claim a condition is necessary without a counterexample or other proof.
Conditions derived from the model need no deviation note. Technical ledger
field names do not prescribe author-facing language.

## Technical Status Rule

### Formalized

Use `formalized` when Lean proves the declared central paper endpoints at the
intended semantic level. This status permits visible, proved, and disclosed:

- typographical, sign, indexing, and finite-constant corrections;
- routine explicit hypotheses that are reasonably implicit in the source
  model, including standard nondegeneracy and domain conditions;
- corrected intermediate lemmas or proof steps when the substantive advertised
  endpoint is unchanged and fully proved; and
- alternative proof routes and declared source-version choices.

Record such issues as source-correction, explicit-assumption, scope, or
proof-strategy notes. Keep `main_caveat` blank. A note can be mathematically
important without being status-changing.

### Formalized with caveat

Use `formalized with caveat` only when both conditions hold:

1. a central advertised source claim requires a demonstrated substantial correction
   that materially changes its mathematical or economic interpretation; and
2. Lean fully proves a corrected endpoint, including any counterexample or
   repair needed to justify the correction.

This category should be rare and may often be empty. The status is not a way to
publish an incomplete or weaker Lean target. A caveated paper must identify the
source defect, explain why it is substantive, state the corrected endpoint,
and point to the checked repair evidence.

### Partially formalized

Use `partially formalized` when a central source endpoint is not fully proved at
the intended semantic level. This includes:

- a materially weaker or narrower Lean theorem;
- an added assumption or restriction that is not a source assumption;
- a remaining certificate, replay, solver theorem, runtime theorem, semantic
  bridge, imported theorem, or source-record conclusion;
- an unproved concrete instantiation or tightness claim in a named proposition,
  even when the reusable generic upper bound is proved;
- a `sorry`, axiom-like placeholder, or other unresolved mathematical
  boundary; and
- a corrected target whose required derivation is not yet fully proved.

Human approval of an added non-source assumption does not turn an incomplete
source theorem into a caveated full formalization. It remains partial until the
original source endpoint is proved or the paper itself is corrected and the
corrected endpoint is fully closed.

## Issue-level status impact

Every source-proof defect in a completed paper's
`audit/source_proof_fidelity.json` ledger uses schema 2 and records one of:

- `formalized_note`: a minor correction, implicit condition, proof repair, or
  other disclosed issue that leaves the substantive advertised endpoint fully
  proved;
- `formalized_with_caveat`: a substantial central source-paper error with a
  fully proved corrected endpoint; or
- `partially_formalized`: an unresolved source endpoint, materially weaker
  formalization, or non-source restriction.

Each defect also records a nonempty `status_impact_rationale`. This is a
semantic judgment, not a mechanical consequence of whether the source text or
proof line changed.

The audit enforces these relationships:

- a plain `formalized` paper may contain only `formalized_note` defects;
- a `formalized with caveat` paper must contain at least one
  `formalized_with_caveat` defect;
- `formalized_with_caveat` impact requires a source-statement defect and a
  fully checked corrected statement;
- `partially_formalized` impact or an open proof obligation cannot coexist with
  either full-closeout status; and
- a completed paper's configured fidelity ledger must use schema 2.

A full-closeout paper must configure `review_surface.source_proof_fidelity_review`
when its v10 surface requires explicit source routes, its canonical source map
links a source defect, or its canonical fidelity ledger records a defect. A
zero-defect archival ledger alone does not force this migration. An explicit
v10 source-route closeout also requires current schema-2 source-record
semantic-model evidence over every generated expanded-type row. An unresolved
semantic-model dimension blocks both `formalized` and `formalized with caveat`.

When the canonical fidelity ledger exists, a full-closeout configuration must
use that ledger rather than a clean alternate. Every nonblank
`source_defect_id` in the canonical source map must resolve to a ledger defect.
Configured source-record paths must be current v10 artifacts; blank or duplicate
generated semantic-model keys are invalid rather than evidence that one review
row covers multiple model obligations.

`formalized_note` may document a source correction, an explicit source-model
convention, or an existing visible-premise note whose source endpoint is proved.
It cannot waive a `documented_additional_assumption`, `partial_boundary`, or
`not_paper_assumption` judgment. Those are partial-formalization evidence, even
when their row is listed in `formalized_note_rows`.

### Deep prose observations

In ordinary `named_theoretical_statements` mode, a schema-2 fidelity ledger may
also contain `deep_audit_observations`. This is a documentation-only lane for a
finding in unnumbered prose that remains outside the normal named-theory
surface. Each observation must give a stable id, a concrete `source_locator`,
concrete `affected_source_locators`, the source claim, finding, repair handoff,
and `normal_scope_disposition:
"unnumbered_prose_outside_named_theory"`. The ledger's pinned source artifact
and every local file-and-line span are checked; linked source-map rows must keep
their byte-pinned source excerpts.

Every observation must be linked through `deep_audit_observation_ids` to at
least one source row that the source-presentation selector itself classifies as
outside normal scope and whose `source_kind` is deep-only. A source-presented
named theorem, proposition, lemma, corollary, definition, or explicitly named
model condition cannot be recategorized as prose to enter this lane. Standalone
formulas and algorithms are deep-only under the normative scope policy. Deep observations are prohibited in
`deep_paper_with_all_prose_claims` mode and cannot carry a defect resolution,
corrected target, user scope exclusion, or `source_defect_ids`. They document
repair work without changing normal named-theory mathematical status.

## Decision procedure

For every discrepancy, decide in this order:

1. Pin the declared source version and exact target.
2. Ask whether Lean proves the intended central endpoint at the intended
   semantic level. If not, use `partially formalized`.
3. If the endpoint is fully proved, ask whether the issue changes its
   substantive claim. If not, use `formalized` plus a visible note.
4. If the substantive central claim requires a demonstrated source correction,
   ask whether the corrected endpoint is fully proved. If yes, use
   `formalized with caveat`; otherwise use `partially formalized`.
5. Report source pins, validator independence, saved human review, sidecar
   freshness, and release readiness under validation/certification evidence,
   not under mathematical status.

## Examples

| Situation | Mathematical status | Documentation |
|---|---|---|
| Printed sign or finite constant is corrected, and the substantive endpoint remains proved. | `formalized` | Source-correction note; `status_impact: formalized_note`. |
| A false auxiliary lemma is replaced by a valid route proving every downstream advertised theorem. | `formalized` | Counterexample and repair note; `status_impact: formalized_note`. |
| A standard nondegeneracy condition is made explicit and the degenerate behavior is checked. | `formalized` | Explicit-assumption or scope note; normally `status_impact: formalized_note` if recorded as a defect. |
| A central paper theorem is substantially false, and Lean proves and justifies the corrected theorem. | `formalized with caveat` | Caveat-repair memo; `status_impact: formalized_with_caveat`. |
| Lean proves an ex-post payoff condition but not the paper's full belief/history equilibrium theorem. | `partially formalized` | Name the missing semantic layer; `status_impact: partially_formalized` when tied to a ledger defect. |
| Lean needs a new non-source assumption to prove a restricted theorem. | `partially formalized` | Additional-assumption and remaining-boundary note. |
| Source pins or independent human review are missing, but all mathematics is closed. | Mathematical status unchanged | Mark certification incomplete. |

## Required closeout surfaces

Apply the same classification in:

- paper-local `status.json` and `main_caveat`;
- `FINAL_VALIDATION_REPORT.md` Sections 5, 6, 9, and 10;
- `audit/source_proof_fidelity.json` schema-2 defect entries;
- theorem nodes and notes in `docs/DependencyDAG.tex`; and
- detailed generated audit aggregates after synchronization. Public table
  labels and sparse notes follow the separate display policy above.

Do not use caveat language or `dag_caveat` styling for a `formalized_note`.
Do not move a remaining proof boundary into a source-correction note.
