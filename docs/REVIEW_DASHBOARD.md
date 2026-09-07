# Paper Review Dashboard

The dashboard is the human-facing tool for checking whether each
`PaperInterface.lean` statement matches the corresponding paper statement.
It is for statement validation, not proof search.

`PaperInterface.lean` is the semantic-review file. It contains exactly one
expanded transparent `<name>Spec : Prop` declaration per paper source claim;
it contains no thin theorem/lemma wrappers. `ProofInterface.lean` holds each
separately Lean-checked endpoint of exactly that Spec type. If a legacy
interface contains proof wrappers or helpers, migrate that paper before
calling its semantic review current.

A material paper-local model declaration or reusable `AppliedModelingLib` definition is
not a trusted name or a glossary entry. When Lean leaves a paper-local name in
a Spec display, the packet first opens that declaration's own body/signature,
then recursively reviews every remaining paper-local or library dependency.
Each paper-local prerequisite needs its selected byte-pinned source connection
and current source-to-target screening in
`audit/paper_semantic_prerequisites.json`; each reusable declaration needs the
analogous record in `audit/library_semantic_review.json`. The dashboard and
packet show these cards before the dependent source claim. They are prerequisite
review nodes, not duplicate paper claims or denominator rows.
Foundational Lean/Mathlib syntax and containers remain version-pinned closure
terminals; a paper must not pretend to source-match `Nat` or `Finset` itself.
If the dashboard row count is much larger than the paper's named definitions and
results, curate `review_surface.include_names` in `status.json` and move helper
or certificate endpoints out of `PaperInterface.lean` before asking for review.
The dashboard enforces two row-count prompts: more than 30 rows requires a
current `review_surface_llm.json` audit that checks whether all rows are
paper-facing, and 120 or more rows shows an oversized-surface warning even when
an audit exists.
At public-facing closeout, the repository audit is stricter: any paper marked
`formalized`, `formalized with caveat`, `partially formalized`, or
`conditional` needs an explicit current `review_surface_llm.json` pass, even if
the dashboard has 30 or fewer rows.

This document describes statement-review and diagnostic commands. They are not
a frozen-closeout command sequence. Once all paper inputs are frozen, begin
with `python3 scripts/closeout_reuse_plan.py --paper <Paper>` and execute only
its current `next_action`; the planner decides whether a dashboard refresh or
strict repository check is still needed.

## Start A Review

Use the paper-local launcher when possible:

```bash
papers/ABC24ShortTitle/review-dashboard.sh
```

Or run the shared script directly:

```bash
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --serve
```

Open one of the printed URLs. On WSL2, the paper-local launcher binds broadly
by default, prints both `127.0.0.1` and any detected WSL guest-IP fallback, and
tries to open those URLs in Windows. Keep the terminal open while it prints
startup status.

## Markup-Friendly Review Packet

For public review, the checked-in `docs/HUMAN_REVIEW_PACKET.tex` and rendered
`docs/HUMAN_REVIEW_PACKET.pdf` are the reviewer artifacts. They retain the
approved display of source excerpts and semantic Lean material prepared during
the source-grounded audit.

A clean public clone does not contain the audit workspace or cache needed to
recompute those semantic Lean displays. Its supported presentation-only rebuild
works from the existing checked-in TeX packet:

```bash
python3 scripts/review_dashboard_packet.py --paper ABC24ShortTitle --sanitize-existing --compile
```

This command rewrites only public presentation locators in the existing TeX
and compiles the PDF. It does not recompute or change the source excerpts,
semantic Lean displays, audit evidence, or saved reviewer judgments. A semantic
packet update must be prepared in the audit workspace/cache before the
checked-in reviewer artifact is replaced.

The packet presents recursively retained
paper-local model cards and material library prerequisites used by the selected
Specs. Every card shows its byte-pinned paper-source connection, Lean-owned
semantic target, exact Lean declaration, screening status, and reviewer
annotation. It then presents one row per paper source claim: the exact byte-pinned raw source
input (the displayed claim plus declared raw context), the expanded
`PaperInterface` Spec, the separately checked proof endpoint, its saved
source-to-Spec judgment, a \(\square\) **Matches source input** reviewer check,
and a blank annotation area. The same check and annotation area appear for
every material library-definition prerequisite. Map summaries and
Lean-to-TeX prose are excluded from both semantic comparison surfaces. The
packet is generated evidence display, not a human-review credential: after
returning an annotated PDF or TeX, reconcile the reviewer decisions into the
dashboard so that `paper_theorem_validations.jsonl` records the actual human
judgments.

The packet follows the paper's source-artifact publication policy. Preserve its
approved source excerpts; do not add source excerpts to a public export merely
because they appear in a local review packet. When an official arXiv TeX source
is explicitly approved for publication, its source map remains the authority
for that separate export decision.

## Reviewer Workflow

1. Select the paper.
2. Review each paper-local model card and each material library definition against its selected raw paper-source connection.
3. Compare each raw source input with the expanded Lean Spec.
4. Check the independently recorded source-to-Spec, source-to-paper-model, and source-to-library judgments when available.
5. Confirm the named proof endpoint is separate proof evidence, not a second claim.
6. Add notes for assumptions, source ambiguities, or mismatches.
7. Submit the paper-claim review row.

The dashboard includes search, status filters, slice filters, source-file
buttons, line numbers, and MathJax rendering for formula-like paper statements.
It reads the paper-local `status.json` `review_surface` section as the
machine-readable source of truth for curated review rows and slices.

## Optional Lean-To-TeX Drafts

The Lean-to-TeX draft column can be overridden by a paper-local
`audit/lean_to_tex_llm.json` file. Use this for stable,
context-free drafts generated from `PaperInterface.lean` alone, without reading
the source paper. The legacy paper-root and `.review_traces/lean_to_tex_llm.json`
locations are still read when no tracked `audit/` draft exists.

Lean-to-TeX is a display aid only. It is never shown to, or used by, the
source-to-Spec LLM judge. The required review lanes are:

1. The formalization agent writes one expanded paper-facing Spec in
   `PaperInterface.lean` and one exact-type proof endpoint in
   `ProofInterface.lean`.
2. For every material paper-local declaration retained after the Spec root is
   opened, Lean produces its own-body target and recursively inventories its
   remaining paper-local and reusable-library dependencies. The paper-local
   card must have an exact source connection and current hash-bound semantic
   judgment; a name or exact code alone is not enough.
3. For every material reusable library primitive used directly by a source-facing
   Spec or by a retained paper-local declaration,
   the formalization agent records an exact bounded library declaration and a
   source-map item (or a separately byte-pinned source-model/definition
   connector that is not an independently counted claim) in
   `audit/library_semantic_review.json`. An independent
   semantic reviewer receives only that source item's current ordered bundle of
   verbatim byte-pinned quotes and the exact expanded library declaration. It
   must not receive a glossary, identifier explanation, theorem label, or a
   Lean-to-TeX paraphrase. Its record is current only when both inputs' hashes
   and reviewer metadata are current.
4. An independent semantic LLM judge receives only the current ordered bundle
   of verbatim byte-pinned source quotes and the fully expanded Spec, then
   saves its result in `audit/statement_match_llm.json`.
5. A separate assumption-provenance LLM, given only the paper source text for
   the claimed assumptions and the assumption declarations from `Assumptions.lean`,
   judges whether every listed assumption is truly a paper/source model
   assumption rather than a proof shortcut. Save this in
   `assumption_match_llm.json`.

The library-review ledger has this source-facing shape (the exact declaration
body is read from the registered bounded Lean source location, never copied as
a paraphrase):

```json
{
  "schema": 1,
  "paper": "ABC24ShortTitle",
  "prompt_version": "library-statement-match-v1-verbatim-source-anchor-expanded-definition",
  "target_protocol": "expanded_library_definition_v1",
  "items": {
    "AppliedModelingLib.Namespace.LibraryDefinition": {
      "library_declaration": "AppliedModelingLib.Namespace.LibraryDefinition",
      "source_item": "source_map_item_key",
      "library_definition_sha256": "...",
      "source_input_bundle_sha256": "...",
      "judgment": "matches",
      "reason": "...",
      "validator": "independent reviewer",
      "validated_at": "2026-08-17T00:00:00Z"
    }
  }
}
```

For an uncommon library primitive, also record `label`,
`library_source_path`, `library_line_start`, and `library_line_end` in its
item. A standalone connector uses the same `source_anchor_evidence`,
`semantic_context_requirements`, and `source_location` fields as a source-map
item. This makes its exact Lean definition available to both review surfaces
without adding the preliminary source passage to the paper-claim denominator.

The statement match pass is full-theorem and formula-level, not just
result-label-level. Every displayed equation, inequality, iff, definition, or
source-defining formula that is part of a paper-facing result should have an
exact review row or an exact subclaim row. Broad rows that merely say a numbered
result's metrics, model, or source surface are formalized can hide sign errors,
missing normalizers, domain restrictions, omitted subparts, or premise
shortcuts. The Lean-to-TeX prompt should preserve every visible binder,
hypothesis, domain condition, equivalence/implication direction, and conclusion.
The judge prompt should explicitly ask whether all formula-bearing subclaims are
present and whether their hypotheses, subparts, quantifiers, signs, constants,
normalizations, inequality direction, domains, and conclusions match the
complete original paper statement. Conditional wrappers, source-row/certificate
packages, omitted conclusions, or weakened/strengthened statements must be
judged `mismatch` or `uncertain`.

Formula rows are still subject to proof provenance. A source-equation wrapper
is complete only when it is derived in Lean from the paper's source model
primitives or from separately validated paper assumptions. If the formula is
asserted as a source row, theorem premise, certificate field, capacity identity,
normalization, or other undischarged proof boundary, record it in
`Assumptions.lean`/`audit/assumption_match_llm.json` or mark the downstream endpoint
partial until it is derived.

The same rule applies to reusable library certificates. A library theorem may
require an explicit certificate or source-shaped package from its caller; that
is a good reusable API. But a paper-facing theorem is not complete merely
because it aliases that library theorem. The paper wrapper must construct the
certificate from paper primitives, or the certificate must be a validated paper
assumption. Otherwise the dashboard/report should show a partial or conditional
boundary. Use `python3 scripts/audit_repository.py --library-only --library-premise-audit` to
list reusable APIs with certificate/source-boundary parameters and to catch
paper rows that transitively depend on those APIs through helper layers.
The default repository audit also follows paper-local helper chains. A reviewed
row is blocked if any local helper it depends on, recursively, still consumes an
unvalidated certificate, source-row equation, hidden hypothesis, or
proof-boundary premise. Internally constructed certificates are fine; hidden
premise consumers are not. Axioms, constants, opaque declarations, and unsafe
declarations are review blockers.

If the semantic judge reports a mismatch or uncertainty, repair the source map
or the expanded Spec. The source input must remain raw byte-pinned text, and
the semantic target must remain the Spec; do not repair a verdict by changing a
paraphrase. Re-run the source-to-Spec judge after changing either surface.

Use this workflow in two modes:

- Initial target-setting pass: run near the beginning of a paper, after the
  source inventory and first `PaperInterface.lean` Spec skeleton, before
  investing in long proofs. This lightweight pass only establishes that the
  Lean Specs are the right formalization targets. Generate
  `audit/statement_match_llm.json` from the raw source-anchor bundles and
  full expanded Specs, then run
  `python3 scripts/review_dashboard.py --paper <paper> --statement-precheck`,
  then run `python3 scripts/review_dashboard.py --paper <paper>
  --assumption-precheck`. The statement judge is row-local; it does not certify
  that visible theorem premises are source assumptions or already-derived facts.
  Iterate on `PaperInterface.lean` until mismatches and premise-provenance
  findings are fixed. Do not update the final validation report,
  review-surface audit, DAG, or human-review log just for this early pass.
- Full review-boundary pass: use after a material `PaperInterface.lean` or
  source-surface change, before an active proof or review handoff. This includes
  the same raw-source-to-Spec judgment, plus the review-surface audit
  when row count requires it, the assumption-provenance pass when assumptions
  exist, the `Statement Translation Audit` section in
  `FINAL_VALIDATION_REPORT.md`, and the full `--precheck`. It is not a routine
  final-closeout predecessor: at public release or any other frozen closeout,
  the planner determines the exact current delta.

For both modes, every dashboard row needs one concrete source statement. If the
automatic TeX/text extraction is missing, over-broad, or pulls in surrounding
paragraphs, repair the source-facing statement text before asking the judge to
compare. Otherwise the judge may correctly return `uncertain` even when the Lean
target is mathematically right.

Declaration-keyed source statements belong in a source-inventory/report section,
not in generated audit output. The dashboard ignores `Statement Translation
Audit` when extracting source statements; that section is downstream evidence,
not source text for the next judge pass.

If all or nearly all rows are `uncertain`, treat that as a likely source
statement extraction or parser issue. Fix the source map, or record one
paper-wide source-map problem, before accepting a long row-by-row uncertain
list.

`lean_to_tex_llm.json` has schema:

```json
{
  "schema": 1,
  "paper": "PaperFolder",
  "prompt_version": "lean-to-tex-v3-strict-context-free-semantic-inputs",
  "translator": "gpt-5-codex",
  "translator_type": "model",
  "translated_at": "2026-06-13T12:00:00Z",
  "prompt_summary": [
    "Translate from the Lean statement alone, with no paper context.",
    "Preserve all visible binders, hypotheses, domains, named predicate/wrapper applications, directions, and conclusions.",
    "Do not replace named premises with theorem labels, source-like phrases, or proof-route summaries."
  ],
  "items": {
    "paper_theorem_name": {
      "tex_statement": "Context-free paper-style translation of the Lean statement.",
      "lean_statement_sha256": "required digest"
    }
  }
}
```

For older papers, item values may also be plain strings containing the
translation; the dashboard accepts both forms.

`audit/statement_match_llm.json` is tracked when used. Legacy paper-root files
are still read for older papers.
It has schema:

```json
{
  "schema": 1,
  "paper": "PaperFolder",
  "prompt_version": "statement-match-v10-semantic-fidelity-seat-stopping",
  "validator": "gpt-5-codex",
  "validator_type": "model",
  "validated_at": "2026-06-06T12:00:00Z",
  "prompt_summary": [
    "Compare the complete source statement against the Lean-to-TeX translation semantically.",
    "Require exact agreement on hypotheses, subparts, quantifiers, domains, constants, normalizations, signs, inequality directions, conclusions, and visible inputs.",
    "Do not approve by theorem label, phrase overlap, or source-looking Lean names.",
    "Expand or otherwise inspect named predicates/wrappers enough to decide whether every Lean premise is source-backed or derived."
  ],
  "comment": "Optional sidecar-wide validator note.",
  "items": {
    "paper_theorem_name": {
      "matches": true,
      "judgment": "matches",
      "reason": "The translated statement has the same hypotheses and conclusion.",
      "comment": "Optional validator-facing note.",
      "source_obligations": [
        {"id": "s0", "kind": "parameter", "statement": "The paper quantifies over the model domain.", "source_location": "Theorem 2, p. 4"},
        {"id": "s1", "kind": "assumption", "statement": "The paper's first hypothesis.", "source_location": "Theorem 2, p. 4"},
        {"id": "s2", "kind": "conclusion", "statement": "The paper's complete conclusion.", "source_location": "Theorem 2, p. 4"}
      ],
      "lean_obligations": [
        {"id": "l0", "kind": "parameter", "signature_ref": "b/0", "signature_atom_sha256": "required atom digest"},
        {"id": "l1", "kind": "assumption", "signature_ref": "b/1", "signature_atom_sha256": "required atom digest"},
        {"id": "l2", "kind": "conclusion", "signature_ref": "result", "signature_atom_sha256": "required atom digest"}
      ],
      "obligation_alignment": [
        {"source_id": "s0", "lean_id": "l0", "relation": "equivalent", "semantic_basis": "The quantified domains agree.", "bridge_statement": "The source and Lean model variables range over the same domain."},
        {"source_id": "s1", "lean_id": "l1", "relation": "equivalent", "semantic_basis": "The formulas agree after expanding notation.", "bridge_statement": "For every x, the source premise holds if and only if the expanded Lean premise holds."},
        {"source_id": "s2", "lean_id": "l2", "relation": "equivalent", "semantic_basis": "Every quantified conclusion clause is present.", "bridge_statement": "For every output, the Lean conclusion holds if and only if the complete source conclusion holds."}
      ],
      "unmatched_source_conclusions": [],
      "unmatched_source_inputs": [],
      "unjustified_lean_inputs": [],
      "unmatched_lean_conclusions": [],
      "lean_signature_sha256": "required canonical manifest digest",
      "lean_statement_sha256": "optional pretty-printed snapshot digest",
      "paper_statement_sha256": "required digest",
      "tex_statement_sha256": "required digest"
    }
  }
}
```

The JSON above abbreviates the v10 item shape. Every current item also requires
`semantic_scope_review`, including source-versus-Lean quantification, expanded
named definitions and recursive result dependencies, algorithm/runner/output
semantics, numeric semantics, discrete/container/stopping semantics, and all
five required fidelity-risk dimensions. A row whose source claims operational
complexity also needs a sibling `operational_complexity_review` with a concrete
worst-case recurrence and bound, representation and traversal costs, and
bit-complexity where relevant. Use the schema emitted by `scripts/new_paper.py`
and enforced by `scripts/review_dashboard.py`; do not copy this abbreviated
example as a complete sidecar.

Use `matches: false` or `"judgment": "mismatch"` for a failed check, and
`"judgment": "uncertain"` when the judge cannot decide. The canonical Lean
declaration-manifest digest plus paper and TeX statement digests are required for
a judgment to count as current; if any required digest is missing or no longer
matches the current row, the dashboard marks the saved LLM judgment as stale.
The raw Lean statement digest is an optional display snapshot. Every obligation must use an exact page,
theorem/equation, appendix, or source-file/line locator. Every alignment must
state the mathematical equivalence or implication in `bridge_statement`; a
declaration or obligation name is only a routing key.

For a `matches` verdict, the ledger must map every source conclusion to an
equivalent Lean conclusion, justify every Lean parameter and assumption from a
same-kind source obligation, account for every source input, and leave all four
gap lists empty. Every Lean obligation has exactly one `signature_ref` and the
current `signature_atom_sha256`; those refs must partition the current
Lean-generated manifest: every elaborated explicit, implicit, strict-implicit,
and instance binder plus the final conclusion is covered once.
The canonical `lean_signature_sha256` ignores binder and declaration names; raw
source and `#check` text remain display aids rather than coverage evidence. For `mismatch` or
`uncertain`, the four gap lists contain exactly the unmatched source-conclusion,
unmatched source-input, unjustified Lean-input, and unmatched Lean-conclusion
ids computed from the alignments. A conditional boundary may account for
explicit extra Lean inputs, but it cannot excuse an unmatched or weakened
source conclusion, a source-input mismatch, or an unmatched Lean conclusion.
These LLM checks do not count as human dashboard
reviews.

If Lean cannot elaborate a declaration or emit its declaration manifest, the row
fails closed. The dashboard never reconstructs this coverage from declaration
names or by parsing pretty-printed `#check` output.

Top-level `validator`, `validator_type`, `validated_at`, and `comment` fields
are defaults; an item entry may override them when a different model or agent
checked that specific row.

Audit sidecars fail closed. A sidecar counts only if it parses, uses the current
prompt version, carries current Lean/paper/TeX or source/dashboard digests as
applicable, records validator/model identity and a timestamp, and gives a
recognized success judgment for the current item. Blank template files, missing
files, failed judge runs, stale hashes, stale prompt versions, missing metadata,
unrecognized judgments, `uncertain`, and `mismatch` are alarms, not soft
evidence.

Status exports include a machine-readable `validators` ledger for each row.
Human dashboard reviews enter this ledger with `validator_type: "human"` and
the saved GitHub/user handle. Statement-match sidecars enter the same ledger
with the recorded model or agent name, timestamp, judgment, and comment. The
compact `validator_names` column is for tables; the detailed `validators` array
is the source of truth for dates, comments, sources, and stale flags.

`--precheck` reports statement-translation audit warnings separately from human
review rows. It flags missing Lean-to-TeX drafts, stale Lean-to-TeX drafts,
missing statement-judge entries, stale judge entries, mismatches, uncertain
judgments, and unknown judgment values. JSON exports include these paper-level
summaries under `statement_audits`.

`--statement-precheck` reports only the statement-translation audit lane, which
is useful for the initial target-setting pass. `--statement-check` is the same
check with a non-zero exit when any statement-audit row is missing, stale,
uncertain, mismatched, or otherwise invalid.

The repository audit enforces this for completed papers as well. A paper marked
`formalized` or `formalized with caveat` should not pass
`python3 scripts/audit_repository.py` if its statement-translation sidecars or
review-surface sidecar are stale, missing, uncertain, mismatched, or otherwise
flagged. Treat the dashboard check as the fast paper-local diagnostic and the
repository audit/CI as the backstop.

## Assumption Provenance

Paper-facing theorem hypotheses are allowed only when they are explicit source
assumptions. Do not hide a capacity equation, threshold identity, density row,
certificate, or proof convenience as an unreviewed theorem premise. Instead:

1. Add a named assumption declaration in paper-local `Assumptions.lean`,
   usually named `assumption_*`, `paper_assumption_*`, or
   `source_assumption_*`.
2. Use that named assumption in theorem signatures, for example
   `(h_model : assumption_source_model_conditions params)`.
   The theorem statement may reference the imported assumption; the assumption
   declaration itself should not live in `PaperInterface.lean` unless this is
   legacy code awaiting cleanup.
3. List every assumption declaration in paper-local `status.json`
   `review_surface.assumption_names`.
4. Save an independent source-assumption judgment in
   `audit/assumption_match_llm.json`.

For new proof work, prefer deriving the premise or using the named assumption
declaration directly in the theorem signature. For existing broad
paper-local audit ledgers, the repository audit also accepts exact
`-- audit-premise: <binder name> : <binder type>` markers attached to an
approved `Assumptions.lean` declaration. This is a migration aid for making
hidden source-model premises visible across `ProofInterface.lean` and
`PostPaperAudit.lean`; it should not become a way to accumulate proof-only
certificates.

`assumption_match_llm.json` has schema:

```json
{
  "schema": 1,
  "paper": "PaperFolder",
  "prompt_version": "assumption-provenance-v3-semantic-exact-premise-source",
  "validator": "gpt-5-codex",
  "validator_type": "model",
  "validated_at": "2026-06-06T12:00:00Z",
  "prompt_summary": [
    "Validate each assumption declaration and every exact audit-premise semantically.",
    "A premise is acceptable only when it is source text, a source model primitive, a theorem condition, or derived in Lean from source primitives.",
    "Do not approve by declaration name, theorem label, phrase overlap, or source-looking Lean predicate name."
  ],
  "comment": "Optional sidecar-wide validator note.",
  "items": {
    "assumption_source_model_conditions": {
      "judgment": "paper_condition",
      "reason": "The condition is stated in the model section or theorem statement.",
      "source_location": "Section 2, paragraph 3",
      "premise_judgments": {
        "hDomain : 0 < parameter": {
          "judgment": "source_text_model_primitive",
          "source_location": "Section 2, model paragraph",
          "reason": "The source model states the positive-parameter domain."
        },
        "hBridge : derived_formula = source_formula": {
          "judgment": "partial_boundary",
          "source_location": "Appendix proof, equation display",
          "reason": "The source uses this formula, but Lean has not yet derived it from the primitive model."
        }
      },
      "comment": "Optional validator-facing note.",
      "lean_statement_sha256": "required digest",
      "paper_statement_sha256": "required digest"
    }
  }
}
```

Use `"judgment": "paper_assumption"` for a standalone paper/model assumption,
`"paper_condition"` for a theorem-domain condition stated in the source model
or theorem statement, `"documented_caveat"` for a known source mismatch or
intentional source-statement repair, and `"partial_boundary"` for an
undischarged external/library/analytic/runtime/solver boundary that keeps the
paper partial. Use `"judgment": "not_paper_assumption"` when the row is a proof
assumption, certificate boundary, or derived formula that is not explicitly
assumed by the paper. Use `"judgment": "uncertain"` when the judge cannot
decide from the source text. The dashboard flags missing, stale, uncertain,
unknown, partial-boundary, and not-paper-assumption declarations under the
paper-level assumption panel.

Grouped assumption judgments are not enough. If `Assumptions.lean` contains
`-- audit-premise:` comments, every exact premise must appear under
`premise_judgments`. Use `source_text_model_primitive`, `source_text`, or
`paper_condition` only when the premise is explicitly a source/model/theorem
condition and cite the source location. Use `derived_from_source_primitives`
only when the Lean development already derives the premise from prior source
definitions. Use `partial_boundary` when the premise is visible but not yet
source-matched or derived; a paper with any `partial_boundary` premise must be
reported as partial, not fully formalized.

The assumption judge must not accept a formula merely because it appears in a
source proof, because a Lean helper can consume it, or because a named Lean
predicate sounds like source text. Displayed equations, capacity identities,
threshold cutoffs, normalizations, density or mass rows, source-row packages,
replay/certificate/process/bridge predicates, and witness objects are source
assumptions only if the source states them as assumptions or theorem
hypotheses. Otherwise they must either be derived in Lean from source
primitives or recorded as a partial boundary.

`--assumption-precheck` already performs the selected hidden-premise check. For
a named failure diagnosis, a maintainer may run the targeted repository child
with `--paper-closeout --no-closeout-state`; it does not establish closeout
acceptance. At a frozen closeout, the planner's strict worker owns that check.
The repository audit does not stop at the compact `PaperInterface.lean`
declaration text: it follows thin `abbrev`/`def` aliases into paper-local Lean
files and scans paper-facing declarations such as `paper_interface_*` across the
paper folder. Thus a certificate, threshold equation, capacity identity,
source-row package, or proof-boundary premise hidden in `ProofInterface.lean`
is still a review blocker unless it is derived or appears as a validated
paper-assumption declaration.

`--assumption-precheck` reports only this lane and also invokes the repository
hidden-premise audit for the selected paper. `--assumption-check` is the same
check with a non-zero exit when any assumption declaration is missing, stale,
uncertain, judged not to be a paper assumption, or any paper-facing theorem
premise is still not routed through `Assumptions.lean`. Full `--precheck`
includes this lane.

Because the hidden-premise lane expands Lean declarations, assumption checks may
need built `.olean` artifacts even when a paper has no explicit
`Assumptions.lean` rows. If a fresh checkout is slow locally, use the JSON
dashboard export only for triage and rely on the targeted paper closeout audit
before declaring the paper clean. Routine push/PR CI should not run the full
repository audit; reserve that gate for manual closeout or public-promotion
validation.

## Source-Record and Boundary-Input Audit

Row-local statement matching is not enough when a theorem signature mentions a
record, certificate, replay, process, bridge, source-row package, or broad model
predicate. During initial source/statement review, or to diagnose one named
source-record failure, the producer can generate the raw payload with:

```bash
python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper <PaperFolder> --out papers/<PaperFolder>/audit/source_record_audit.json
```

Do not run that producer by hand as a frozen-closeout prelude. Freeze the
paper inputs, use `closeout_reuse_plan.py`, and let its bounded raw preflight
reuse current evidence, request a judgment-only repair, or schedule the one raw
transition. Re-enter through the planner after a direct diagnostic.

The generated payload contains `prompt_version:
"source-record-v10-semantic-conclusion-boundary-contract"`, the current audit digest,
boundary-shaped visible theorem inputs, recursive source-record fields, and a
judge prompt. Save the independent LLM judgments in
`audit/source_record_match_llm.json` with the same prompt version and current
`source_record_audit_sha256`.

Each boundary-shaped theorem input must be classified by source evidence, a
Lean derivation, an approved external boundary, or an unresolved finding.
`validated_source_assumption` requires a source key/location/evidence.
`proved_from_primitives` requires a Lean constructor or derivation.
`visible_boundary_component` is only for recursive fields exactly unpacked from
visible theorem premises, and `derived_from_visible_boundary` is only for
recursive fields Lean derives from visible theorem premises; neither
classification is valid for a theorem-boundary input itself. A replay,
certificate, process, bridge, or source-row package cannot be approved by a
source-looking Lean name or final theorem label. A paper marked `formalized`
cannot retain an `approved_external_boundary` source-record judgment.
The v10 audit also compares visible proposition premises structurally with
the advertised result. A premise equivalent to, providing, or logically
composing advertised feasibility, cost, runtime, or optimality is
conclusion-bearing proof debt and cannot establish coverage for that same
source theorem, even after declarations or binders are renamed.

Version 10 additionally rejects semantic-world collapse: records or constructors
that are valid only for a fixed profile, rounded instance, selected witness,
one stopping rule, or one output projection cannot justify a source theorem
quantified over a broader world. The judge must trace recursive result
components and refinements back to source primitives or visible validated
boundaries. A renamed or repackaged conclusion remains conclusion-bearing.

For an `author_approved_corrected_model` closeout, the source-record audit is
necessary but not sufficient. The paper-local
`audit/corrected_model_semantic_contract.json` must bind the current audit and
formalization scope, the full canonicalized governing-correction content, every
generated expanded semantic item and its digest, every target result, and every
visible model or assumption condition. Mappings use fully qualified Lean
declarations and generated item digests, not final-component names. Each
detected model dimension needs a checkable source locator, a semantic
comparison, a disposition, and exact Lean evidence; a required bridge must be
found in the current imported paper-local declaration surface. A stale,
incomplete, ambiguous, or spelling-based contract cannot support a corrected
model status.

## Source-proof fidelity and status impact

Completed papers with a configured `audit/source_proof_fidelity.json` use
schema 2. Review the source proof by exact source locator and mathematical
claim, not by Lean declaration name. Each defect records `statement_impact`,
`resolution`, `status_impact`, and `status_impact_rationale`.

- `formalized_note` is a minor correction, routine implicit condition, or proof
  repair that leaves the substantive advertised endpoint fully proved.
- `formalized_with_caveat` is reserved for a substantial error in a central
  source-paper claim whose corrected endpoint is fully checked in Lean.
- `partially_formalized` marks an open obligation, added non-source restriction,
  or materially weaker semantic endpoint.

The paper status must agree with every issue-level impact. Certification and
human review remain separate axes.

## Review-Surface Audit

For any paper whose dashboard has more than 30 rows, run a separate LLM pass
before broad human review. Give that LLM the dashboard row names and paper-facing
summaries, but no proof context, and ask whether every row is a paper-facing
definition, formula, or named source statement that belongs in the human review
surface. Save the result in `audit/review_surface_llm.json`.

At 120 or more rows, the dashboard always shows an oversized-surface warning.
That warning is intentional: even if the LLM audit passes, a human should first
decide whether the paper truly has that many named paper-facing rows or whether
implementation helpers leaked into `PaperInterface.lean`.

`review_surface_llm.json` has schema:

```json
{
  "schema": 1,
  "paper": "PaperFolder",
  "validator": "gpt-5-codex",
  "validator_type": "model",
  "validated_at": "2026-06-06T12:00:00Z",
  "comment": "Optional sidecar-wide validator note.",
  "judgment": "passes",
  "reason": "The rows are exactly the paper-facing definitions and numbered results.",
  "review_rows": 42,
  "review_surface_sha256": "digest printed by the dashboard export/API",
  "items": {
    "paper_theorem_name": {
      "judgment": "keep",
      "reason": "Named source theorem."
    }
  }
}
```

Use `"judgment": "needs_curation"` when helper, diagnostic, certificate, or
proof-route rows should be removed from the human review surface. Use
`"judgment": "uncertain"` when the LLM cannot tell. If `review_rows` or
`review_surface_sha256` no longer matches the current dashboard rows, the
dashboard marks the audit stale. This audit does not increment human review
counts.

## Interface Size

Before asking a human to review a paper, shrink `PaperInterface.lean` to the
paper-facing definitions and named results. Put broad proof aliases in
`ProofInterface.lean` or another implementation-facing module, then expose the
curated source-facing review rows in paper-local `status.json`.

```bash
wc -l papers/<Paper>/PaperInterface.lean
rg -c '^(noncomputable\s+|private\s+|protected\s+)*(theorem|lemma|def|abbrev) ' papers/<Paper>/PaperInterface.lean
```

## Review Logs

By default, reviews are written under each paper folder:

```text
papers/<PaperName>/.review_traces/paper_theorem_validations.jsonl
```

Each row stores the reviewer handle, UTC timestamp, match decision, notes,
current Lean statement, paper-facing summary text, source-provenance metadata,
and SHA-256 digests. If a later `PaperInterface.lean` edit changes a reviewed
statement or a nontrivial source-deviation note, the dashboard flags that
review as stale.

When a `PaperInterface.lean` docstring is a literal source statement, mark it
with a dashboard-only line such as `Source status: direct paper statement` or
`Source status: direct paper formula`. When the displayed statement is edited
from the source, corrected, weakened, strengthened, or added as an audit row,
add `Source status: ...` and `Source note: ...` lines explaining the deviation.
The dashboard strips these lines out of the paper-statement text and surfaces
them separately as source-provenance badges.
For formula-bearing rows, the source-provenance note must identify whether the
formula is a direct paper formula, a corrected source formula, a derived formula
from source primitives, or an explicit paper assumption. Do not use a generic
numbered-result summary as the source statement for multiple displayed
formulas.

The repository is configured so that `paper_theorem_validations.jsonl` is
commit-eligible, while other `.review_traces` files such as local dashboard
logs, rendered statement caches, generated HTML, and parser caches remain
ignored. After a human review pass, inspect and commit the paper-local
`paper_theorem_validations.jsonl` file if those judgments should become part of
the repository history.

The dashboard's `Reviewed` count means rows in this review log. Treat it as
human review only when the rows were saved by a human reviewer. Agent source
audits should be kept in tracked paper docs such as `SOURCE_AUDIT.md` and
should not be written to `.review_traces/paper_theorem_validations.jsonl` just
to clear the dashboard counter.

The reviewer field is editable in the browser. By default it is prefilled from
`--user`, then GitHub identity (`GITHUB_ACTOR`-style environment variables or
the username authenticated in `gh`), then git config, then the OS username.
Use `--user` to force a reviewer handle. Summary views can be filtered with
`--status-user`.

## Checks And Exports

Run the launch-time freshness check without opening a browser when preparing a
statement review or diagnosing a dashboard problem:

```bash
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --precheck
```

It is not a routine frozen-closeout predecessor. For closeout, freeze inputs
and use the planner route described above.

Run non-interactive check mode. It exits with code 1 if any selected review is
missing, stale, or marked as not matching:

```bash
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --check
papers/ABC24ShortTitle/review-dashboard.sh --check
```

Export review status:

```bash
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --export-format json
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --export-format csv
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --export-format md
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --export-format validators-md
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --export-format json --status-user <github-user> --stale-only
```

Use `validators-md` to refresh the paper-facing validator table in
`FINAL_VALIDATION_REPORT.md`. It lists every dashboard/PaperInterface row, the
validators recorded for that row, and validator comments.

In server mode, machine-readable status is available at:

```text
GET /api/status
GET /api/status?paper=ABC24ShortTitle
GET /api/status?paper=...&slice=slice-01&stale_only=true&user=<github-user>
```

## Launcher Maintenance

New paper scaffolds created with `scripts/new_paper.py` include the paper-local
launcher automatically. For existing paper folders, refresh launchers and cached
paper-interface rows before an active review (not during a frozen closeout) with:

```bash
python3 scripts/bootstrap_review_launchers.py --write --refresh-cache
```
