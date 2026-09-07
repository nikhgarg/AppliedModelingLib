# Audit and Closeout

Current operational guide for semantic evidence, graph-native closeout, and
terminal verification. Read this file and validate the machine protocol before
starting, resuming, or changing a current closeout.

## Current authority and scope

1. Validate [`config/formalization_audit_protocol.json`](../../../config/formalization_audit_protocol.json)
   before changing audit scope, status, protocol/version, reuse, build
   selection, or closeout pacing:

   ```bash
   python3 scripts/formalization_protocol.py
   ```

   The machine policy wins over prose. A recorded historical closeout proves
   only its recorded transaction. An intentionally reopened paper enters the
   latest registered protocol.

2. The repository operates as audit/closeout system **v12**. Its current
   semantic lane retains the established **v11 raw-source-to-expanded-Spec**
   contracts and Lean declaration graph. The labels describe one route; do not
   bulk-rename artifacts or choose an older lane for a new closeout. v10
   source-record scans, statement/coverage sidecars, legacy receipts, and
   migration tools remain historical readers only. Never bootstrap, regenerate,
   watch, or require a retired carrier for a current graph-native transaction.

3. Normal source scope is independently presented named theory. A named
   appendix item receives one source-pinned Spec and one independent initial
   review, but repeated review and terminal adversarial work normally focus on
   main-text results and their governing semantic prerequisites. Supporting
   prose, derivations, equations, algorithms, figures, examples, simulations,
   empirical results, and useful unprinted generalizations are not automatic
   claim rows. Attach material support to its owning result; select additional
   material only when it governs a selected result or the maintainer explicitly
   chooses it. A supplementary result may be documented separately but cannot
   earn credit for a source claim.

4. One source-presented claim has one transparent `Spec : Prop` and one
   independently checked proof endpoint. The Spec displays all source-relevant
   binders, conditions, and conclusion; it must not be a theorem alias,
   `type_of`, polymorphic alias, or a helper that hides a material condition.
   Definitions, models, algorithms, assumptions, and conditions are
   source-semantic prerequisites, not duplicate theorem rows. Lean's loaded
   module graph, not Python parsing, names, paths, line numbers, or a status
   file, establishes ownership, dependencies, source routes, proof pairing, and
   axiom closure.

5. Paper-local and reusable-library material receives the same source-semantic
   treatment. A retained prerequisite needs a byte-pinned source connection,
   current raw-source-to-Lean judgment, exact Lean body/signature, and its
   graph-owned route. Ordinary Lean/Mathlib foundations terminate at the
   registered external boundary. A nonstandard axiom cited as a theorem is an
   external `partial_boundary`, never a paper condition or full-closeout proof.

6. An approved ordinary source reading belongs in
   `audit/source_proof_fidelity.json.model_conventions`, with stable ids on all
   affected source-map items. Approved added assumptions remain in the existing
   `accepted_additional_assumptions` record. Material non-equivalent repairs use
   the approved-corrected-target disposition. Synchronize
   `approved_review_contexts` through the scheduled projection; do not copy an
   authority into a queue or ask a reviewer to rediscover, ignore, or overturn
   an already settled reading. Before treating a point as newly ambiguous,
   inspect current reports, clarification/correction memos, proof-deviation
   notes, feedback, and approvals. Ask the maintainer only when new source or
   mathematics creates a real conflict.

## The one current route

### Start from the current state

For a new or resumed paper, follow the intake route in
[`intake-and-source-surface.md`](intake-and-source-surface.md). For an existing
paper, do not infer currentness from a green build, an old report, a dashboard,
a receipt filename, or remembered history.

First check whether the paper already selects a current accepted graph:

```bash
python3 scripts/final_closure_receipt.py --paper <PaperRoot> --check
```

The selected schema-2 obligation graph is the sole machine acceptance
credential. `FINAL_CLOSURE_RECEIPT.md` schema 6 is a readable non-accepting
pointer. A currently valid accepted graph is the terminal path: do not rebuild
a dashboard, reissue reviews, recreate a graph, or run prospective source
inventory merely because workflow, rendering, or compatible engine code has
changed.

Run the planner for the separate terminal-document check even when acceptance
is current. A missing report, memo assessment, DAG or current packet schedules
document repair while preserving the accepted graph and semantic judgments.

If the paper lacks a valid accepted graph, establish the provisional semantic
surface after any source-map, `PaperInterface`, or source-model repair:

```bash
python3 scripts/draft_semantic_preflight.py --paper <PaperRoot>
```

Give its stdout-only Lean-elaborated source/target bundle to a context-isolated
reviewer. This preflight is a repair screen, not evidence: it writes no graph,
queue, ledger, receipt, report, or status. Repair clear source/model/interface
mismatches before graph acquisition. For a genuine choice between reasonable
readings, ask one concise maintainer question with the exact source passage,
Lean reading, and affected scope, then record the answer through the
source-fidelity route above.

After the preflight is clean, freeze the paper inputs and begin only with:

```bash
python3 scripts/closeout_reuse_plan.py --paper <PaperRoot>
```

Execute the returned `next_action`, including any named source-inventory,
closure-recording, review-context synchronization, graph preparation, replan,
or document action. Do not call a lower-level producer, dashboard, raw
source-record transport, or historic recovery command merely because it looks
related. A new graph-native plan requires `semantic_route_schema: 2` before it
acquires a graph or emits a prerequisite queue. A planner that says an exact
input is missing, malformed, changed, or ambiguous fails closed; repair that
specific item rather than creating a second acceptance object.

### Freeze, graph, and review once

The current path has these fixed phases:

1. **Readiness and inventory.** The planner validates the tracked source tree,
   protocol, configured source/status/map inputs, route schema, and paper-root
   build closure. Follow `review_source_inventory_candidates` when emitted:
   read the full pinned source, classify source presentations, add exact
   locators for material additions, and explicitly record completion. Do not
   insert an empty candidate list merely to satisfy a schema.
2. **One Lean graph.** Acquire one typed Lean graph for the frozen paper.
   It owns the exact source-claim frontier, recursive paper/library
   prerequisites, declaration/source ownership, semantic targets, proof routes,
   and axiom closure. Select current inputs positively from the canonical
   configured paths; reports, DAGs, packets, dashboards, README/status
   renderings, conventional aliases, and historical sidecars are presentation
   products, never graph or semantic inputs. Retain the graph through ordinary
   repairs and use it for every downstream consumer in that transaction.
3. **Independent semantic review.** Issue each new or materially changed direct
   claim, paper prerequisite, and library prerequisite once against that graph.
   A reviewer must not have authored or materially repaired the interface,
   proofs, or relevant library declaration. Start from
   [`../templates/CONTEXT_ISOLATED_SEMANTIC_REVIEW_PROMPT.md`](../templates/CONTEXT_ISOLATED_SEMANTIC_REVIEW_PROMPT.md),
   substituting only paper, lane, and queue path. Give the reviewer the pinned
   source, complete expanded target, bounded material declaration code, and
   protocol, without authoring context, intended verdict, prior judgment, or
   proof-history rationale.
   A current-protocol migration receives the complete frozen direct-claim,
   paper-prerequisite, and library-prerequisite surface; it cannot use a
   changed-only worksheet to manufacture its first current review. Human review
   must never be fabricated or auto-closed; incomplete reviewer annotation is
   recorded transparently but is not itself a release blocker.
4. **Proof and build evidence.** Lean verifies exact Spec/endpoint relation,
   safe proof route, and axiom closure. The closeout build checks the complete
   tracked paper root. During proof repair, force a touched paper module with
   `lake build +<TouchedPaperModule>`; a bare paper target can reuse a stale
   artifact. The planner-selected closeout build must enumerate all tracked
   paper-owned Lean modules. Do not substitute a repository-wide build, stale
   `.olean`, or an isolated interface build for that evidence.
5. **Documents and terminal closeout.** Once semantic, realization, and build
   lanes are current, complete the planner's terminal documents and run the
   strict closeout action. The current strict worker executes every one of its
   ten gates from a single frozen context: artifact preflight, exact-context
   acquisition, route/schema preflight, Lean-context acquisition,
   current-evidence preflight, complete tracked-module elaboration, primary
   paper gate, evidence integrity, conclusion provenance, and final input
   check. A complete pass materializes one accepted obligation graph. Timings,
   traces, worker state, queues, caches, and staging bundles are non-accepting.
   Each final adversarial audit uses a fresh no-history reviewer distinct from
   authors, implementers, semantic reviewers, and every other panel member.
   Start each reviewer from
   [`../templates/FINAL_ADVERSARIAL_SOURCE_AUDIT_PROMPT.md`](../templates/FINAL_ADVERSARIAL_SOURCE_AUDIT_PROMPT.md)
   with the tracked paper, pinned source, current protocol, and closeout
   evidence, but no proposed status or campaign narrative. Policy-aware
   closeouts record each audit in
   `docs/FINAL_ADVERSARIAL_REVIEW_PANEL.json`: reviewer identities and audit
   paths must be distinct, every audit binds the same frozen one-review surface,
   and each reviewer attests independence from authoring, repair, and semantic
   judgment work. Increasing the required panel count preserves valid earlier
   audit entries for unchanged comparison material and schedules only the
   missing independent review. The count comes from the authenticated frozen
   review-policy assurance; mutable source-map prose or scheduling preferences
   are not authority at this gate. Historical contracts retain their original
   single-file, single-review semantics.

Within a frozen closeout, run an unchanged expensive lane at most once. A
material source/map/interface/proof change can require the planned successor
graph and affected review delta. A documentation, report, queue-format,
renderer, dashboard, or preflight-only change does not. After a rebuild,
follow its scheduled replan boundary rather than re-running the planner
speculatively.

### Reuse and currentness

Reuse is an exact semantic identity decision, never a matching declaration
name, item key, filename, path, line range, renderer output, whole-file hash,
checkout root, engine version, or cache hit. It binds the byte-pinned source
bundle, corrected-context/approval where applicable, Lean-emitted expanded
semantic target and atoms, transitive material Lean closure, typed Spec/proof
relation, source/paper/library judgment, build closure, protocol, and terminal
authority. A pure one-to-one navigation rename may reuse a matched judgment;
missing, changed, extra, duplicate, one-to-many, or many-to-one identity fails
closed.

The accepted graph is a content-addressed DAG of independently attested leaves:
source atom, Lean-owned target, source-to-Lean judgment, Spec-to-proof
realization, library judgment, and path-independent focused-build closure. It
is the only acceptance credential. Reports, DAGs, packets, dashboards, status
summaries, receipts, operational carriers, and aggregate projections are
derived products. They may regenerate without reopening unchanged semantic
evidence. Do not create engine-pair bridges, paper-specific aliases, raw-record
overlays, duplicate receipt containers, or a second graph to avoid a cheap
projection rebuild.

On every strict replay, re-run the cheap deterministic gates. Reuse only the
exact expensive graph and current identity-bound judgments after validation.
Persist a successful graph leaf before starting the next one, but never cache a
failed or partial strict-stage prefix as authority. Use one transaction's
Lean-owned import closure and source snapshot across discovery, review,
realization, build, and final mutation checking; never rediscover that closure
through a parser, dashboard, or secondary provider.

Currentness is portable. Absolute paths, temporary locations, processes,
hostnames, file metadata, line coordinates, display-only layout, and renderer
bytes are provenance or navigation, not semantic identities. An unchanged
source bundle and Lean semantic identity retain review across compatible engine
refactors. A changed source quote, target identity, typed route, proof boundary,
material library prerequisite, source convention, build input, toolchain, or
protocol reopens only its affected obligation descendants.

## Closeout discipline

- While a paper is in closeout, edit only an essential verified blocker: frozen
  source/map/interface/closure mismatch, proof failure, invalid evidence
  authority, or a tool defect preventing the scheduled worker from consuming
  authoritative evidence. Record why it is essential and whether it changes a
  receipt-bound input. Preserve completed lanes after a review-compatible fix
  and resume from the planner's successor.
- Defer every nonessential audit, performance, renderer, report, dashboard, or
  workflow improvement in
  `papers/<PaperRoot>/.review_traces/deferred_closeout_changes.md`, with date,
  paper/lane, proposed change, reason, and next safe boundary. Do not replan or
  rerun a paper merely to test a deferred improvement.
- Keep workflow/producer changes separate from paper evidence. A
  `review_compatible` engine registration, dashboard or report rendering,
  documentation, diagnostics, status projection, or retired-code deletion is
  not evidence and does not reopen a frozen or accepted paper. A real semantic
  protocol or producer change must identify its affected input class and reopen
  only that class.
- Record each active current-protocol migration's local stage timeline in the
  shared migration tracker: preflight, graph acquisition, review batches,
  frozen preflight, final adversarial audit, documents, focused build, and
  strict closeout. Use `not recorded` or `pre-ledger` for unknown historical
  times; do not infer them from files. Worker UTC timings remain non-accepting
  diagnostics. Begin its migration-ledger row before frozen preflight and
  finish it only after the accepted receipt; record local start/finish, newly
  issued semantic re-review rows and batches, and independent final-adversarial
  checks. Exclude reused judgments, graph acquisition, and routine builds from
  those churn metrics.
- Do not run concurrent Lake builds in one worktree. A full repository build,
  full audit-test suite, and `paper_target_registration.py build-all` are
  integration/release or broad shared-library gates, not ordinary paper
  closeout steps. Run focused owner tests for an audit-engine change and use
  `python3 scripts/run_isolated_audit_tests.py` for the full isolated suite
  when that broader check is justified.
- Use `--closeout-trace` and ignored cache/trace paths only for diagnosis;
  neither can add evidence or enter semantic invalidation. For a long-running
  manifest operation, use one persistent non-PTY process and its atomic
  ignored result artifact; tool output is progress, never result transport.

## Reader-facing products

The authoritative rules for reports, clarification memos, packets, DAGs,
public-note preservation, rendering, and public-link boundaries are in
[`human-facing-artifacts.md`](human-facing-artifacts.md). Do not duplicate them
here.

When the planner schedules terminal documents, use that reference to write the
report and DAG after semantic/realization/build evidence is current and before
terminal acceptance. In particular:

- `docs/REPORT_CONTEXT_SUMMARIES.json` is the display-only authority for
  generated settled-context prose in report Sections 1--11; do not mutate the
  underlying semantic `report_summary` merely to change reader copy.
- `docs/REPORT_MEMO_COVERAGE.json` is the explicit reader-explanation
  assessment for each material source correction or report-level mathematical
  claim. Follow the `REPORT_MEMO_COVERAGE` workflow and validation described in
  `human-facing-artifacts.md`; bind a reviewed readable memo, its current
  content hash, and each material claim rather than treating a report link or
  audit ledger as an explanation.

Reports, DAGs, packets, dashboards, and website/status projections are
required at their designated closeout or release stage, but their prose and
layout never invalidate an unchanged source, Lean graph, review judgment, or
accepted graph. Use `references/release-and-sync.md` and
`references/public-private-sync.md` for release. Do not publish, change
visibility, or push a private graph to public without explicit authorization.
