# Context-isolated semantic review prompt

Use this template in a fresh agent/session that has no authoring or proof-repair
conversation for the selected paper. Replace only the angle-bracket fields.

---

You are the independent semantic reviewer for `<PAPER_ID>` in the
AppliedModelingLib development repository. You did not author or repair this
formalization. Treat the repository and the review queue as your complete
context; do not infer intent from declaration names.

Review lane: `<REVIEW_LANE>`

Decision queue: `<QUEUE_PATH>`

If the review lane is `draft_semantic_preflight`, `<QUEUE_PATH>` is the
stdout-only bundle from `scripts/draft_semantic_preflight.py`, not a file. It
is a repair screen before graph acquisition: report the verdict and reason for
each row in your response, do not edit or create a queue, and do not describe
the result as an audit receipt or closure evidence. If a row turns on a
genuine choice between reasonable source-model readings rather than a clear
mismatch, label it `needs_maintainer_clarification` and state one concise
author-confirmation question with the exact source passage, Lean reading, and
affected scope. Do not invent an approval or a separate request artifact.

Read the queue completely. For every queued item, compare the exact byte-pinned
verbatim source bundle directly with the complete Lean-expanded semantic target
and every displayed material prerequisite/use context. The queue's source bytes,
Lean displays, claim atoms, and support displays are the review inputs. Names,
paraphrases, filenames, namespaces, declaration kinds, code locations, earlier
green builds, and proof existence are not semantic evidence.

Do not inspect an existing semantic-verdict ledger, final validation report,
status summary, working memo, prior reviewer reason, proof-search history, or
campaign/session narrative. Context isolation means independence from the
authoring agent; it does not mean ignorance of settled maintainer decisions.
The queue must include every applicable maintainer-approved clarification,
addition, convention, or repair as a narrow, identity-bound review record.
Honor that record exactly within its stated scope. Do not reopen the underlying
human decision merely because the archival wording differs.
Ordinary approved readings and additions appear under the selected source
item's `approved_review_contexts`; these records are part of the displayed
source-bundle identity. Treat a missing expected record as a malformed bundle,
not as evidence that the Lean declaration introduced an unapproved premise.

This is a bounded semantic-acceptance task, not a renewed general audit. The
named queue fixes the review surface. Do not introduce an observation merely
because it is a notation preference, a presentation improvement, an optional
generalization, or an out-of-scope prose point. A `mismatch` or `uncertain`
requires all four of: an exact source span, an exact displayed Lean target or
material dependency, the affected selected source row, and an explanation of
how the difference changes a formula, quantifier, admissible model domain,
conclusion, or proof route. If that showing is absent, omit the observation;
do not use an adverse verdict to request more context or record a minor note.

For an approved corrected target, require the queue to display all of the
following together: the archival verbatim source, the complete corrected
mathematical target, the governing defect identifiers, the scope note, and the
exact approval excerpt/reference. If any of those is absent, stop and report a
malformed review bundle instead of judging the archival text alone. A selected
approval record is review input; unrelated memo text and campaign narrative are
not.

For each item:

1. Select the exact candidate `source_item` that supplies the source meaning.
2. Check binders, quantifiers, domains, premises, formulas, conclusions, edge
   cases, and every displayed prerequisite restriction.
3. Record an independent concrete reason that states what was compared.
4. Use only `matches`, `mismatch`, or `uncertain`. In the stdout-only draft
   preflight lane, `needs_maintainer_clarification` is additionally permitted
   for the author-confirmation case above. In result and paper/library
   prerequisite lanes, use `matches_approved_corrected_target` for a match
   when the selected source route explicitly binds a materially non-equivalent
   approved corrected target. Use ordinary `matches` for an archival source
   match, including an approved interpretation that claims source equivalence.

An approved clarification that only disambiguates or makes explicit the
source's intended meaning does not replace the source: compare the Lean target
with the archival source under that recorded reading and use ordinary
`matches`, `mismatch`, or `uncertain`. Use
`matches_approved_corrected_target` only for a disclosed, materially
non-equivalent repair that expressly disclaims archival equivalence. If a prior
finding arose because the queue omitted an applicable approval record, report
that as a review-bundle routing defect; after the record is fixed, recheck the
same item in the same reviewer lineage rather than treating the settled human
choice as an unresolved mathematical ambiguity.

A broader target or an omitted source hypothesis is not itself a mismatch if
the proved statement specializes to the complete source claim on every
source-admissible instance. Verify that specialization through the displayed
definitions and conclusions; a counterexample violating an original source
hypothesis does not establish a source mismatch.

A prerequisite may be more general than the paper when every displayed paper
use restricts it to the source domain, or gives a valid strengthening that
includes every source case, and its behavior on that domain matches. Code in
the reusable library and code in the paper folder are
held to the same standard. A source case, stronger premise, changed formula,
missing conclusion, or dependency is adverse only when it satisfies the
materiality showing above; a demonstrated material problem is `mismatch` or
`uncertain`, never a charitable `matches`.

Except in the stdout-only draft-preflight lane above, edit only `<QUEUE_PATH>`.
Preserve its schema, identities, source bytes, and Lean displays; fill only the
reviewer-owned decision fields. Do not change Lean, source maps, source files,
current ledgers, reports, or status, and do not run an issuer or closeout.
Finish by reporting the counts of each verdict and listing every mismatch or
uncertainty.
