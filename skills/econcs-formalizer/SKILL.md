---
name: econcs-formalizer
description: Formalize economics, operations, algorithms, game theory, and applied-modeling papers in Lean. Use for paper intake and source inventories, source-faithful interfaces, formalization architecture, semantic audit and closeout, reusable-library extraction, human-facing validation artifacts, and private-to-public preparation. Pair with econcs-prover for active Lean proof construction and repair.
---

# AppliedModelingLib Formalizer

This skill is the lifecycle router. Detailed rules live in one authoritative
stage reference each; load the references for the active stage completely
before acting. Do not reconstruct a stage from campaign memory or from the
long-form handbook.

## Always-enforced invariants

- Read and validate `config/formalization_audit_protocol.json` before changing
  audit scope, versions, reuse, status, or closeout pacing. The machine policy
  overrides conflicting prose.
- Use exact source bytes and actual Lean semantics. Names, paraphrases,
  filenames, namespaces, line numbers, declaration kinds, and code location do
  not establish a source match.
- One source-presented claim has one transparent semantic `Spec` and one
  separately checked proof endpoint. Definitions, models, algorithms,
  assumptions, and conditions use the semantic-prerequisite lane rather than
  self-equality theorem rows.
- Normal scope does not promote standalone unnumbered prose observations into
  paper claims. Inventory them as deep-audit material unless they are visibly
  standalone named/theorem-like theory, supply a material clause or governing
  dependency of a selected result, or the maintainer explicitly selects them;
  supporting prose attaches to the owning result rather than adding a row. A
  final adversary may not fail closeout on default-out-of-scope prose or demand
  its formalization. If such prose was mistakenly selected, the repair is to
  correct its scope disposition, not to create a new theorem, caveat, or review
  row.
- Keep source coverage distinct from review intensity. A selected named
  appendix result remains organized in `PaperInterface` and receives one
  independent source-to-Lean review, but routine repeat review and the terminal
  adversarial challenge default to named main-text results and their governing
  semantic prerequisites. Promote an appendix item only when its statement or
  definition governs a main-text statement or definition, or the maintainer
  explicitly asks; do not promote it merely because a main-text proof imports
  or invokes it. Lean checks that proof dependency once the main-text
  interface is correct. Otherwise record a real appendix issue proportionately
  rather than churning the primary closeout. A
  post-validation report may narratively disclose a reader-relevant appendix,
  supporting-proof, or prose finding without making it a new checked row,
  blocker, or reissue trigger; omit incidental findings.
- Paper-local and reusable-library declarations receive the same material
  source-semantic treatment. Ordinary trusted foundations terminate at the
  registered external boundary; unusual or materially used concepts may be
  reviewed recursively by judgment.
- Lean-native graph utilities own declaration discovery, elaborated semantics,
  dependencies, ownership, proof routes, and axiom closure. Python orchestrates
  typed outputs and evidence; it must not parse Lean syntax to recreate those
  facts.
- A closeout acquires one typed Lean graph and one exact semantic-review pass,
  reuses them only by validated content identity, reruns cheap strict gates,
  and issues one canonical accepted graph. Human review may not be fabricated
  or auto-closed, but incomplete reviewer annotation is not a release blocker.
- A new graph-native closeout requires `semantic_route_schema: 2` before it
  acquires the Lean graph or emits a paper/library prerequisite queue. Route
  each source definition, model, algorithm, assumption, or condition to its
  actual material paper or library declaration explicitly. An older map is
  archival input, not permission to turn all transitive Lean helpers into
  source-less reviewer rows; migrate its typed routes first.
- For every current-protocol closeout, begin a migration-ledger row before the
  frozen preflight and finish it only after the accepted closure receipt. Record
  local start/finish times, the number of *new semantic re-review rows and
  batches* actually issued after activation, and the number of independent
  final-adversarial checks. Exclude reused judgments, graph acquisition, and
  ordinary builds. These are churn metrics: record superseded final reviews as
  well as the one that ultimately binds the accepted surface.
- Model allocation is an efficiency preference, never semantic evidence. When
  available, prefer a GPT-5.6 Terra coordinator with xhigh reasoning for the
  deterministic planner, queue handling, builds, regeneration, and migration
  loop, and delegate bounded context-isolated semantic review, the final
  adversarial audit, difficult Lean repair, or major audit-architecture
  judgment to GPT-5.6 Sol. Give an overridden reviewer a self-contained handoff
  without authoring context. Do not record model names as receipt authority,
  infer independence from the model choice, or weaken any gate when Sol is
  unavailable.
- Every newly issued source-to-Lean semantic judgment must come from a
  context-isolated reviewer that did not author or materially repair the
  interface or proofs. Give that reviewer the pinned source, complete expanded
  Lean target and material dependencies, and the review protocol, but no
  authoring conversation, intended verdict, prior judgment, or proof-history
  rationale.
- Context isolation removes the authoring session, not settled maintainer
  decisions. Before dispatch, bind every applicable approved clarification,
  addition, convention, or repair into the tracked source-map record and the
  identity-bound queue the reviewer sees. A material non-equivalent repair uses
  the approved-corrected-target disposition; an interpretation that merely
  makes the source's intended meaning explicit remains an ordinary source
  match. Never ask a fresh reviewer to rediscover, ignore, or silently overturn
  a maintainer decision that the repository has already settled.
- Put each ordinary approved source reading in
  `audit/source_proof_fidelity.json.model_conventions`, cite its stable
  `model_convention_ids` on every affected result and prerequisite source-map
  item, and keep approved extra assumptions in the existing
  `accepted_additional_assumptions` record. The v11 preparer must materialize
  those authorities as `approved_review_contexts`; do not hand-copy them into
  an LLM prompt. Queue generation, the dashboard, the human-review packet, and
  the generated Section 10 validation-report block then consume the same
  identity-bound records. A closeout must fail early if a cited authority is
  absent, malformed, stale, or missing from the final report. The closeout
  planner automatically schedules `sync_approved_review_contexts.py` before
  any reviewer queue when this projection is stale; follow that action rather
  than rediscovering prior decisions or editing a queue by hand.
- Start that reviewer from
  `templates/CONTEXT_ISOLATED_SEMANTIC_REVIEW_PROMPT.md`, substituting only the
  named paper, lane, and queue path. Do not improvise a new prompt for each
  paper.
- The final adversarial audit must use the number of distinct fresh no-history
  reviewers fixed by the paper's authenticated closeout policy. None may have
  authored or repaired the formalization or issued its semantic judgments.
  Give each the tracked paper, pinned source, current protocol, and frozen
  closeout surface, but no intended status or campaign narrative; its task is
  to falsify the proposed coverage, semantic, proof, boundary, and reporting
  claims. Preserve valid prior panel entries when only the required count rises.
- Start that reviewer from
  `templates/FINAL_ADVERSARIAL_SOURCE_AUDIT_PROMPT.md`; do not reconstruct its
  instructions from session memory.
- Reports, DAGs, packets, dashboards, website/status projections, and counts
  are derived human-facing products. They are required at their designated
  closeout or release stage but never invalidate unchanged semantic evidence.
- Do not publish, change paper visibility, or push a private commit graph to
  public without explicit user authorization.

## Lifecycle routing

| Stage or task | Read completely | Then use |
|---|---|---|
| New paper, resumed paper, source freeze, statement inventory, source coverage | `references/intake-and-source-surface.md` | `templates/FORMALIZATION_PLAN.md` when a plan is needed |
| Source-facing Specs, proof endpoints, prerequisite boundaries, corrections, assumptions, interface refactor | `references/formalization-architecture.md` | `skills/econcs-prover/SKILL.md` for the inner proof loop |
| Active theorem proving or repair | `references/formalization-architecture.md` and the relevant `references/proof-*.md` | `skills/econcs-prover/SKILL.md` |
| Reusable-library discovery, extraction, consolidation, facade, or API change | `references/shared-library-development.md` | `skills/lean-community-conventions/SKILL.md` for changed APIs |
| Audit planning, semantic review, graph reuse, closeout, receipt, retention | `references/audit-and-closeout.md` | the current planner/worker selected there |
| Final validation report, source memo, DAG, review packet, dashboard, website copy/counts | `references/human-facing-artifacts.md` | the current artifact generators selected there |
| Git/worktree coordination | `references/release-and-sync.md` | `skills/econcs-shared-worktree/SKILL.md` |
| Public/private projection, PR, or release | `references/release-and-sync.md` and `references/public-private-sync.md` | current projection and release guards |
| "Wiki this", session mining, or promotion of repeated lessons | `skills/econcs-session-insights/SKILL.md` | update the project wiki and executable skills only to the extent the user's wording authorizes |

When a task spans stages, follow lifecycle order and load only the newly
entered stage reference. Do not begin an expensive audit while source, map,
interface, or essential proof repair is still moving. Do not write final
human-facing artifacts until the semantic and proof surface is stable enough
for them to be current.

When the user bounds a pre-release repair pass, keep an explicit list of active
proof repairs and deferred items. Finish the authorized audit, architecture,
report, and closeout work; put newly discovered extensions or optional proof work
in the backlog rather than starting another proof campaign. A genuine blocker
still needs a precise disposition. Keep candidate preparation and publication
within the user's latest authorization; readiness work does not grant either.

## Context-free startup contract

Assume no unwritten campaign or session context. Establish the current stage
from tracked repository state, validate the machine protocol, and read the one
stage reference routed above before acting. For a new paper, enter through
`paper_contribution.py new` and complete the source-first intake route. For an
assigned existing-paper closeout, treat missing current artifacts as migration
work and begin with the planner below. Use paper-local working memos as clues
and closeout drafting aids, never as semantic evidence. During a protocol
migration, transfer their still-current substance into a newly generated report,
DAG, packet, and minimal supporting memo set before removing redundant legacy
copies; delete superseded autogenerated audit outputs rather than maintaining
parallel audit generations. Do not infer acceptance from old filenames, green
builds, reports, or remembered prior work.

Before treating an issue found during re-analysis as a new ambiguity or asking
the user to decide it again, inspect the paper's prior validation reports,
source-clarification/correction and proof-deviation memos, recorded feedback,
and approval records. Preserve an already settled human interpretation unless
new source or mathematical evidence contradicts it; if a conflict is real,
state the old decision and the new evidence precisely before asking. Narrative
artifacts locate prior decisions and reader-relevant substance, but do not
replace current source-to-Lean semantic evidence.

Before the first graph-backed closeout action after a source-map,
`PaperInterface`, or source-model repair, run:

```bash
python3 scripts/draft_semantic_preflight.py --paper <PaperRoot>
```

This prints an exact Lean-elaborated, source-mapped draft review bundle to
standard output. For every selected paper-local or library semantic
prerequisite, the bundle also carries Lean's exact source-owner declaration
body, module/path/range, and byte digest from the same frozen import snapshot.
This matters when a recursive or opaque declaration's elaborated type is not
enough to expose its step, stopping, sampling, or payoff semantics. Route that
declaration explicitly and review the raw source against its actual Lean body;
never substitute a name, a paraphrase, a Python reconstruction, or a
reviewer inference from a proof. It is deliberately non-evidence: it writes no graph,
decision queue, ledger, receipt, report, or status. Give it to a
context-isolated reviewer and repair every source/interface/model mismatch
before freezing the closeout surface. Do not treat a draft review response as a
semantic receipt or save it merely to satisfy a later gate. Once it is clean,
start the ordinary planner below and execute only its returned action. This
ordering prevents a provisional interface from spending or invalidating the
one graph-backed semantic-evidence transaction.

The draft preflight reads the current source map and asks Lean for the current
in-memory import boundary; it intentionally does **not** require a prior
current receipt or persist a replacement. Therefore it remains available
immediately after an interface or source-map edit, when the historical receipt
must be stale. It is a bounded repair screen: do not let it accumulate minor
observations or reopen settled, correctly projected maintainer clarifications.

If that preflight identifies a genuine choice between reasonable source-model
readings, pause before graph acquisition and ask the author/maintainer one
concise confirmation question: show the exact source passage, the Lean
reading, and its affected paper scope. On approval, record the reading in
`source_proof_fidelity.json.model_conventions`, route its stable id to every
affected source-map item, and synchronize `approved_review_contexts` before
the final independent review. On rejection, repair or weaken Lean. Do not ask
for confirmation on a clear mismatch, and do not create a separate request
ledger, receipt, or graph merely to document the question.

When the user says "wiki this," route to `econcs-session-insights`; do not make
ordinary formalization depend on reading raw session history. Reusable lessons
belong in the narrow owning skill, workflow code, or regression test. Wiki
examples, feedback ledgers, session history, and paper-source archives remain
private by default. Public skills contain self-contained general instructions
without private paper details and must work without the private wiki. Follow
`references/public-private-sync.md` when selecting skills for a release.

For closeout, begin with:

```bash
python3 scripts/closeout_reuse_plan.py --paper <PaperRoot>
```

Execute only the returned `next_action`. Invoke a lower-level producer,
sidecar refresh, or direct audit only when a named diagnostic or planner action
requires it; those commands do not independently establish acceptance.

## Proof-family references

Select only the relevant guide:

- `references/proof-strategies.md`
- `references/proof-foundations-math.md`
- `references/proof-foundations-probability.md`
- `references/proof-foundations-optimization.md`
- `references/proof-algorithms-complexity.md`
- `references/proof-algorithms-online.md`
- `references/proof-markets-social-choice.md`
- `references/proof-mechanism-design.md`
- `references/proof-recommender-systems.md`

`references/formalization-handbook.md` remains a searchable explanatory
long-form handbook, not a second rulebook. For closeout, use
`references/final-closure-receipt.md` for supplementary receipt details.
The stage references and
current machine protocol own normative decisions when older explanatory
material conflicts.

For external AI-formalization workflow research, consult
`skills/ai-formalization-workflows/SKILL.md` without letting it override this
repository's protocol.
