# Paper README Status Vocabulary

Paper-local theorem ledgers use a controlled status vocabulary. Keep nuance in
the `Remaining assumptions / notes` cell, not in the `Status` cell.

Terminology rule: in this repository, a paper/result that is verified by Lean is
called `formalized`. Do not use `Verified in Lean` as a separate status label;
Lean verification is the mechanism, not a distinct paper-status category.

## Public Website Display

The public paper table uses **Formalized** for checked coverage and a sparse
**Formalization gap:** note for substantial additional assumptions,
simplifications, or unproved source-to-model bridges or conclusions. The note
names the affected result and the actual remaining work. It does not imply a
problem in the paper. Source-implied or derived premises and minor source
clarifications do not belong in these table notes.

The two existing public partial projects, LOS02 and LMMS04, retain **Partially
formalized** until their remaining scope is completed. The executable display
owner is `human_status_label` in `scripts/sync_paper_status.py`, with the
`preserve_partial_status` list and curated notes in `papers/catalog.json`.
This presentation does not change technical status, semantic evidence, or
closeout acceptance.

## Technical Result And Audit Status

The governing technical decision rule is
[`FORMALIZATION_STATUS_POLICY.md`](FORMALIZATION_STATUS_POLICY.md). Minor or
resolved source clarifications are notes on `formalized` work, a demonstrable
substantial source correction with a fully proved corrected endpoint is the
rare `formalized with caveat` case, and a weaker or incomplete Lean endpoint
is `partially formalized`.

Allowed technical result-row statuses:

- `formalized`: The listed Lean declaration(s) close the intended paper item.
  The remaining-assumptions cell must be `None` or start with `None;` followed
  only by notes about explicit paper assumptions already encoded as
  `Assumptions.lean` declarations, listed in `status.json`
  `review_surface.assumption_names`, and checked by `assumption_match_llm.json`.
  Corrected printed-proof steps, typos, finite-constant or sign repairs,
  standard implicit domain conditions, repaired auxiliary lemmas, or
  alternative proof routes that preserve the substantive advertised endpoint
  belong in proof/source notes and do not prevent plain `formalized`. Record a
  source-proof defect as `status_impact: formalized_note` and keep
  `main_caveat` blank.
  DAG style: use `dag_result` for theorem/proposition/corollary nodes,
  `dag_lemma` for lemma/support nodes, and `dag_model` for definition/model
  nodes.
- `formalized with caveat`: A central advertised source claim requires a
  demonstrated substantial correction, and Lean fully proves an endpoint that
  materially changes the claim's mathematical or economic interpretation.
  Record at least one schema-2 source-proof defect with
  `status_impact: formalized_with_caveat` and explain why the correction is
  substantive. Do not use this status for an added non-source assumption,
  narrower Lean model, incomplete semantic layer, or unresolved proof
  boundary; those are partial formalizations. Do not use it for a typo, minor
  constant/sign repair, routine implicit assumption, repaired auxiliary lemma,
  source-version choice, or failed generalization outside the paper model;
  those are notes on plain `formalized` work. DAG style: `dag_caveat`.
- `partially formalized`: Substantial definitions, helper lemmas, finite
  analogues, or boundary-dependent variants are formalized, but the full source
  item is not closed at the intended semantic level. Use this technical status for
  materially weaker/narrower Lean endpoints, added non-source assumptions or
  restrictions, and results that remain conditional on an explicit extra
  certificate, bridge theorem, external theorem, or hypothesis not yet
  discharged. Name that boundary in the notes rather than turning it into a
  caveat. DAG style: `dag_partial`, with `dag_conditional` reserved for visual
  boundary/certificate nodes when useful.
- `paper draft`: The source paper itself is still moving. Use this only in a
  non-public development workspace for an active draft whose source inventory, proof targets,
  and Lean wrappers may need to be remapped when a new draft arrives. This is
  not a public completion status. DAG style: use `dag_scaffold` for inventoried
  source regions and `dag_unformalized` for not-yet-started paper results.
- `scaffold`: Names, interfaces, or theorem shells exist, but no substantive
  source proof has been closed. DAG style: `dag_scaffold`.
- `not started`: No meaningful Lean artifact exists yet for the paper item.
  DAG style: `dag_unformalized`.
- `not formalized`: The item is intentionally not represented one-for-one, is
  out of scope, or is superseded by another formalized route. DAG style:
  `dag_unformalized`.

For every status other than `formalized`, the final column should state the
exact substantial correction, closed sub-result, remaining certificate, or
reason for deferral. Plain `formalized` rows may still carry concise source
correction or explicit-assumption notes, but those notes are not caveats.

The dependency DAG legend should expose this same vocabulary. For a formalized
node, the color additionally records the paper-object type: green for
theorems/results, yellow for lemmas/support, and blue for definitions/models.
For non-fully-closed statuses, the style records the status directly.

The default repository audit enforces this status vocabulary, checks that DAGs
input the shared TikZ preamble, and checks that the template legend mentions all
allowed statuses.
