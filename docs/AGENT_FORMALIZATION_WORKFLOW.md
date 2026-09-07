# Agent Formalization Workflow

This file is for agents and maintainers. The top-level `README.md` is protected
hand-written human-facing project prose. Do not edit it unless the user gives
specific root-README instructions.

`config/formalization_audit_protocol.json` is the normative machine-readable
protocol for audit versions, source scope, reuse identity, builds,
assumption/correction categories, and proof-campaign pacing. This document
explains that protocol but does not override it. Historical paper reports may
accurately name older artifact schemas without changing the current protocol.
Validate the policy before changing workflow behavior:

```bash
python3 scripts/formalization_protocol.py
```

## Documentation Split

- Human-facing docs should be strategic, short, and readable without Lean
  expertise. The top-level `README.md`, paper-root
  `FINAL_VALIDATION_REPORT.md` files, `PaperInterface.lean`, and
  `docs/DependencyDAG.pdf` are the main human surfaces. Use
  `VALIDATION_MODEL.md` to explain status labels.
- Agent-facing docs may be detailed and operational. This file,
  `docs/ARCHITECTURE.md`, `docs/APPLIEDMODELINGLIB_DOMAIN_INDEX.md`, and
  `skills/econcs-formalizer/` contain workflow rules and implementation
  conventions. Use `skills/econcs-prover/` for active Lean theorem proving and
  proof repair.

Do not put long theorem ledgers, raw command transcripts, or proof-internal
details in the top-level README. Do not add generated blocks or generator
outputs there. If the user explicitly asks for a root README edit, make only
that edit. `python3 scripts/root_readme_policy.py` enforces the non-generated
README policy; content hash locks are intentionally not used.

## Starting A Paper

Ask the agent to use the `econcs-formalizer` skill for paper workflow and the
`econcs-prover` skill once theorem proof work starts. Give it the source PDF or
paper URL. A good first prompt is:

```text
Get context on this repo using the skill file. Then start formalizing
<paper title>. Build a source inventory first: every paper definition, named
lemma/proposition/theorem/corollary, source-labelled theorem-like claim, and
explicitly named source assumption/model condition.
Use `named_theoretical_statements` unless the user explicitly requests the
deep all-prose mode. Build a compact proof plan that records the next proof
seam, source assumptions, and dependencies before proving in Lean.
```

## Source Scope And Reuse Baseline

This baseline supersedes older workflow passages that ask for routine
cataloguing of all prose or whole-paper cache invalidation.

- A closeout map must explicitly declare `source_coverage_mode`. In normal
  `named_theoretical_statements` mode, the required surface is source-presented
  named theoretical statements: definitions, results, theorem-like claims,
  explicitly named assumptions/model conditions, and named appendix results.
  Standalone formulas, equations, algorithms, figures, captions, tables,
  numerical examples, simulations, empirical observations, and narrative prose
  are deep-audit material. A standalone display may still be inspected as a
  dependency of a selected named item, but it receives no independent normal
  coverage row.
- Complete normal-scope coverage with a source-only named-presentation index
  from a pinned UTF-8 text/TeX audit artifact. The receipt must record current
  artifact bytes, index digest, and any declarative source environment/heading
  mappings. A source map cannot certify its own completeness. An unknown
  named presentation blocks closeout until it is classified; a named open
  question is recorded with an explicit source-declared-open nonproof
  disposition, not silently ignored.
- Map keys, aliases, Lean declaration/function names, and raw pretty-printed
  declaration spelling are navigation only.
  Direct coverage requires a pinned source semantic item, a byte-validated
  source anchor, and one unique current fully elaborated Lean signature with
  the checked semantic contract. A rename or equivalent surface rewrite can
  rebind only through those unique semantic identities; refresh the raw text
  as trace evidence after matching, and fail closed on ambiguity.
- Cache reuse is per item. It requires the current audit schema, unchanged
  source semantic digest, byte validation of the current source quote on every
  normal source check, and a unique current Lean signature plus transitive
  elaborated proposition/type dependency context. Exact module artifacts are
  pinned only for opaque imported terminals whose bodies are unavailable to
  that graph; whole review-module artifacts, unrelated declarations, and
  theorem proof bodies do not invalidate an unchanged statement judgment.
  Its identity also pins the configured item and resolved qualified Lean route,
  plus the configuration/preflight and validator fingerprints. Re-run static
  configured-route validation before accepting a cached result; an unresolved,
  stale, or ambiguous route fails closed. Unrelated source edits and
  navigation-only moves do not reopen an unchanged item.
  Ordinary reads do not write sidecars; explicit refresh commands are the only
  cache writers.
- A legacy `paper-coverage-v4-semantic-proof-and-pinned-defect-support`
  sidecar is not current evidence and is never silently upgraded. Use
  `python3 scripts/semantic_audit_reuse.py --paper <paper> --migrate-legacy-v4-coverage
  --previous-source-map <pre-change-map> --previous-review-cache <pre-change-cache>`
  only when both historical snapshots are available. The migration is explicit
  and atomic: every legacy item must identify one prior source target by exact
  digest, retain the same full source semantic/anchor pin in the current map,
  and rebind each old review row to one current row with unchanged
  declaration-name-independent elaborated manifest structure, verified
  old/current signatures, and unchanged reviewed statement text. Source keys,
  row names, and Lean declaration names navigate snapshots only. Any missing,
  stale, changed, or ambiguous identity leaves the v4 file untouched for a
  fresh semantic audit.
- Proof work comes first after target setup. Update plans, reports, or DAGs at
  material source-scope/assumption repairs, handoff, paper transition, or
  closeout, rather than on a timer or after every helper lemma.
- When normal-scope review uncovers a real unnumbered prose defect, retain it
  in `audit/source_proof_fidelity.json` as a `deep_audit_observations` record
  instead of deleting or misclassifying it as a named theorem. Pin its source
  locator and affected locators to the ledger's canonical source artifact,
  state the claim, finding, and repair handoff, and link it only to
  byte-pinned `source_kind` deep-only map rows that the semantic source
  selector excludes from normal scope. This is unavailable in deep all-prose
  mode and can never carry a defect resolution, corrected target, or scope
  waiver. It records future work; it does not change named-theory status.

### Theorem-Realization V11

New papers and explicitly requested v11 upgrades set
`review_surface.require_v11_raw_source_spec_screening: true`. It becomes a
closeout gate for `formalized` and `formalized with caveat`, not an immediate
error for a `not started` statement skeleton. Before Lean drafting, independently
inventory every material source atom from exact pinned source-quote bytes. This
is source-side semantic work: theorem, binder, field, function, map-key, and
type names are navigation only.

A material repair of a trusted legacy-v10 paper instead needs a current
item-level v10 source and Lean review. It does not silently manufacture a v11
source-to-Spec migration. An explicit v11 marker always strengthens this rule.

For each selected endpoint at closeout, the current raw-source screening
compares every byte-pinned source atom with one transparent `Spec : Prop`.
The builder-issued Lean graph independently proves that the theorem/lemma has
exactly that Spec type and owns the complete recursive semantic, proof,
instance, and axiom closure. Do not issue a second
`source_spec_correspondence` worksheet, atom-to-component bridge ledger, or
terminal-node disposition ledger. No declaration, data, record, container,
carrier, or function shape receives automatic credit merely from its name or
kind; unresolved graph or semantic-review nodes fail closed in their owning
lane.

Reuse the source judgment and Lean graph only when their respective portable
semantic identities remain unchanged. Legacy correspondence records remain
readable under their recorded protocol but cannot silently become current v11
credentials.

The agent should think through the proof and formalization plan outside Lean
before proving, especially where the paper is underspecified. Keep that plan in
the private workspace as `FORMALIZATION_PLAN.md` and update it as the proof
route changes. Do not publish planning, handoff, or progress markdown in the
public paper folder unless the user explicitly asks for that artifact.
At the beginning of every paper audit or new formalization, the first plan
section should be an extended outside-Lean paper sanity pass: read the source,
check every named result and formula-bearing displayed claim for plausible
signs, constants, normalizations, quantifiers, domains, and dependencies. Also
ask which generalizations, conjectures, or extensions look trivial or
near-trivial once the source theorem chain is formalized. Write the initial
findings in `FORMALIZATION_PLAN.md`. Use those findings to choose the
formalization strategy. If the pass finds a likely source bug, missing
assumption, formula ambiguity, or issue that could change the theorem target,
tell the user early before encoding the printed formula as a proof premise.
Do not turn a routine equality/inequality ambiguity, including `=` versus
`<=`/`>=` or strict versus weak endpoints, into a long proof campaign by
default. Ask the user when available. Otherwise record the exact condition as a
visible additional assumption in the corrected theorem and post-formalization
report, continue with actionable work, and raise it at the next interaction;
do not silently credit the condition to the source.

That initial pass is a narrow start gate. Before deep Lean proof work, the plan
must record the sections from
`skills/econcs-formalizer/templates/FORMALIZATION_PLAN.md`, including:

- the source/version inventory, including official source, open source, local
  cache paths, and version mismatches;
- the source-only named-presentation receipt and the normal named-theory
  ledger, including every source-presented named definition, proposition,
  lemma, theorem, corollary, theorem-like claim, and explicitly named
  assumption/model condition; track standalone displays or algorithms only in
  deep mode or as dependencies of one of those selected items;
- the formula/dependency sanity pass, including density-vs-mass representation
  issues and which prior paper objects each result depends on;
- the source assumptions/dependencies and next proof seam; do not make a broad
  generalization/conjecture/extension scan a gate to beginning proof work;
- the shared-library reuse checkpoint for mathlib, cslib, optlib, potential
  upstream Lean sources from
  [`UPSTREAM_LEAN_SOURCES.md`](UPSTREAM_LEAN_SOURCES.md), and existing
  `AppliedModelingLib` APIs, including citation/provenance for any upstream material
  used or ported;
- the formal target map, including rows to fully prove, empirical/out-of-scope
  rows, and any explicit boundary that would remain if the paper cannot be
  closed immediately;
- the next proof target and its focused build command.

## Required Paper Artifacts

Each public paper folder should keep the root focused on executable paper code
and machine-readable status. It should contain:

- `.gitignore`
- `MainTheorems.lean`
- `PaperInterface.lean`
- `status.json`
- `review-dashboard.sh`
- `FINAL_VALIDATION_REPORT.md` when a paper has a final validation claim
- `FINAL_CLOSURE_RECEIPT.md` for a closed paper
- `docs/DependencyDAG.tex`
- `docs/DependencyDAG.pdf`
- `audit/*.json` for tracked source maps, statement reviews, and closure evidence
- locally cached source PDF, ignored by Git
- locally cached `pdftotext` extraction, when licensing permits

Private paper folders may additionally keep `README.md`,
`FORMALIZATION_PLAN.md`, handoff notes, source audits, and other progress
documents. Keep those private by default.

Completed papers should also have:

- `ProofInterface.lean`, containing the distinct theorem/lemma proof endpoints
  paired with the transparent Specs in `PaperInterface.lean`.
- `ProofLedger.lean` when an exhaustive source-numbered proof endpoint ledger is
  useful. Do not create new `PostPaperAudit.lean` or `AuditLedger.lean` files;
  they are not human-facing audit surfaces and should be consolidated into
  `ProofLedger.lean` during ordinary maintenance.
- `FINAL_VALIDATION_REPORT.md`, ending at Section 11, with the paper-facing
  disposition, definitions, named theorem statements, genuine deviations,
  assumptions, gaps, and caveats.
- A concise caveat-repair memo when the final status is `formalized with
  caveat` because of a substantial error in a central paper claim and a fully
  proved corrected endpoint. Prefer a TeX source plus rendered PDF with a 1--2
  page executive summary and deeper notes for each issue. The details should be
  human-facing proof text, not a Lean declaration inventory: quote or restate
  the old source equation/statement, give the exact replacement
  equation/statement, explain why the change is substantive, and include a
  short TeX derivation when the caveat is algebraic.
- A concise `docs/SOURCE_CLARIFICATIONS.md` only when a current mathematical
  source reading needs explanation. State the source anchor, current reading,
  and result-level effect; do not record audit chronology, proof-repair history,
  or Lean implementation detail there.

### Existing papers assigned for current closeout

A closeout assignment authorizes the routine current-protocol migration needed
to reach an accepted receipt. An older theorem-wrapper interface, or a missing
source map, `ProofInterface.lean`, `status.json`, audit ledger, DAG, packet,
report, or closure artifact is not by itself a blocker and is not the final
answer to the assignment. Read the pinned source and existing proofs, replace
the paper-facing surface with one complete transparent Spec per source claim,
create the exact-type proof endpoints and current source routes, repair the
proof/interface seam, generate all required evidence and human-facing files,
and continue to closeout.

Do not migrate the old interface one wrapper at a time. Its declarations are
proof-navigation candidates, not the source denominator. Reconstruct the
source-only named-presentation inventory first and record a table from each
source item to its one complete Spec plus any supporting implementation
endpoints. Multiple specializations, probability components, rate corollaries,
resource envelopes, or helper variants for one numbered source result normally
remain proof support unless the source presents them independently. A
one-Spec-per-old-wrapper rewrite must be rejected before freeze unless every
row has its own exact pinned source presentation.
An independently numbered appendix or supplement lemma remains a source claim
even when it is used only inside the proof of a main-text theorem. Put it in
the marked appendix/supplement section and keep it in the denominator; reserve
proof-support-only status for Lean-introduced helpers or source proof text that
is not independently presented as a named result.

Build the source inventory from one combined source-only review surface. Run
the deterministic named-heading scan as a hard floor, then—before using any
Lean declaration, old interface row, or source-map classification—give the
complete canonical source text to a reviewing agent. Record every additional
material remark, observation, note, example, or unlabelled result it finds by
exact source locator in the same `candidate_presentations` list. Explicitly
classify every mechanical and holistic candidate as a normal material claim or
deep-audit material; an empty list must still be recorded. This is an intake
completeness decision, not a source-to-Lean semantic verdict.
Inspect mixed prose blocks rather than treating a visible definition heading as
the end of the presentation. A sentence beside a definition may separately
assert existence, uniqueness, an implication, or another theorem-like fact;
that assertion is its own candidate when the source independently presents it.

Do this in one pre-audit migration pass: run the read-only structural diagnosis
once, collect the full deficiency list, refactor the complete source-facing
surface, obtain one focused build, and freeze it before semantic screening.
Thereafter execute only the closeout planner's named successor and repair only
the item it identifies. Do not alternate between partial interface edits and
whole-paper receipt generation. Request a user decision only for missing source
material, a substantive source ambiguity, a new assumption/correction, or a
proof obstruction that would change the agreed theorem—not for routine
protocol files or generated presentation artifacts.

After drafting the complete source-facing interface and before issuing semantic
judgments, run the first adversarial source-to-interface audit. Reread the full
source against the expanded Lean surface, repair the complete deficiency list,
and rebuild once. This is a repair pass, not acceptance evidence; do not mark
`docs/AGENT_SOURCE_AUDIT.md` as final here.

After the interface, proofs, prerequisites, machine evidence, and compiled
inputs are stable, let the closeout planner freeze their exact operational
transaction and project its location-neutral semantic audit surface. When it
schedules `perform_final_adversarial_source_audit`, reread the complete source
once more and write `docs/AGENT_SOURCE_AUDIT.md`, including this line for that
exact semantic surface:

    - Reviewed final holistic audit surface identity: `<sha256>`

Compare the final expanded Lean surface for omissions, candidate
misclassification, hidden strengthening or weakening, and semantic mismatch.
Green item-level gates, source-only intake, and the first adversarial repair
pass do not substitute for this final surface-bound check. Any source, status,
semantic-target, prerequisite, or proof-contract repair changes the surface and
requires the final audit to bind the replacement identity. Pure path, line,
module, declaration-name, build, or tool-routing changes do not require another
human audit when the planner proves the full semantic surface unchanged.

## What The Agent Should Keep Current

- `status.json`: paper-local source of truth for paper status, dashboard review
  rows/slices, interface metadata, and artifact paths. At a paper-local status
  freeze, run `python3 scripts/sync_paper_status.py --paper <paper>` and its
  `--check` form to render/check only that paper's owned README or legacy-note
  projection. Do not hand-edit those generated paper-local files or rows. The
  root `README.md` is not a generated status surface; the sync script enforces
  its protected lock. Do not run the aggregate generator after every status
  edit or as a paper-closeout prerequisite. Aggregate `papers/status.json`,
  `papers/human_status.json`, `docs/PAPER_STATUS.md`, and `site/index.html`
  projections belong to a separate integration, public-PR, or release boundary.
  The sync script defaults to tracked paper status files so local draft
  scaffolds do not pollute CI-facing generated tables; pass
  `--include-untracked` only when intentionally syncing a new untracked paper
  scaffold. In a dirty shared checkout, run an aggregate sync only from a clean
  integration worktree so it cannot publish another lane's intermediate status.
  A paper closeout receipt binds the paper-local status input; aggregate
  projections are not a second evidence gate.
- `status.json` `human_summary`: public-facing prose for the generated tables.
  If `human_summary_review.status` is `human_written` or `human_approved`, do
  not rewrite the summary unless a human explicitly asks for that exact edit.
  Audit scripts may require a nonempty summary for non-formalized papers, but
  should not pressure edit or shorten human-written or human-approved prose.
- Private `FORMALIZATION_PLAN.md`: lightweight outside-Lean proof scratchpad.
- `docs/DependencyDAG.tex`: proof map with every named result and definition-like
  paper object represented; status and caveat text should agree with
  `status.json`.
- `MainTheorems.lean`: implementation-level source-faithful wrappers.
- `PaperInterface.lean`: the single canonical human-review Lean surface and
  the only allowed `review_surface.source_file`, with readable paper
  definitions and named theorem statements.
- `AuditInterface.lean`: optional implementation/proof-support surface for
  bulky aliases and helper endpoints. It may be imported by
  `PaperInterface.lean`, but it must not be configured as the review surface.
- `ProofInterface.lean`: required current-protocol theorem endpoint surface,
  distinct from the one-row-per-source-claim semantic review surface.
- `ProofLedger.lean`: optional exhaustive proof endpoint ledger when useful;
  `PostPaperAudit.lean`/`AuditLedger.lean` files are not review surfaces and
  should be consolidated into `ProofLedger.lean` during ordinary maintenance.
- `FINAL_VALIDATION_REPORT.md`: final human report.
- `audit/*.json`: current source-to-Spec, source-coverage,
  prerequisite-semantic, assumption-provenance, proof-fidelity, and accepted-
  graph artifacts. Historical source-record sidecars may remain as provenance
  but are not a current closeout lane.

Completed papers with a configured source-proof fidelity ledger must use
schema 2. Every defect entry needs `status_impact` and
`status_impact_rationale`. Use the public status vocabulary in
[`STATUS.md`](STATUS.md) when a recorded impact controls a public paper label. Treat
`statement_impact` and `status_impact` as different questions: the former says
whether source proof text or a source statement changes; the latter says
whether the issue is a note, a substantial paper caveat, or evidence that the
formalization remains partial.

For a public release, follow
[`PUBLIC_RELEASE_CHECKLIST.md`](PUBLIC_RELEASE_CHECKLIST.md) after the
paper-local source-first closeout. The batch `--public-complete` diagnostics
select the visibility/status set;
they do not establish that a prepared public candidate is release-safe and do
not replace a paper-local source-first closeout.

Do not waive a named mathematical proposition as empirical description merely
because it applies a generic theorem to a dataset or concrete mechanism. Raw
measurements and figures may be non-theorem scope; the proposition's model
instantiation, exact/tight conclusion, and any algorithmic guarantee must be
proved or recorded as a partial boundary.

If the paper proof is imprecise, the agent should build a defensible proof
strategy, formalize that strategy, and record the deviation in the validation
report. It is better to prove a source-faithful theorem by a cleaner route than
to spend large amounts of time following an informal proof line-by-line, as long
as the theorem statement and assumptions are explicit.

## Post-Formalization Closeout

Before declaring a paper complete, run a library elevation pass over the
paper-local proof modules. Check whether any proof results, proof techniques,
certificate constructors, model-neutral definitions, or reusable primitives
should move into `AppliedModelingLib` for other papers to reuse. Elevate local/low-risk
items when the destination module is clear and the build can be checked. If the
move needs broader API design, keep the paper-facing wrapper in place and record
the candidate, destination module, and reusable proof idea in
`FINAL_VALIDATION_REPORT.md`.

Library certificate APIs are allowed and often preferable. A reusable theorem may
require an explicit certificate, witness, external-boundary hypothesis, or
source-row package from its caller. That makes the library theorem a conditional
tool, not a paper result by itself. A paper-facing theorem that calls such a
library API is fully formalized only if it constructs the certificate from the
paper source primitives inside Lean, or if the certificate is a validated
paper-source assumption. Otherwise the paper endpoint remains partial or
conditional. During closeout, run the combined axiom/premise/source-hygiene
audit when you need a repository-wide provenance snapshot, and write its
paper-by-paper report:

```bash
python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0 --write-report docs/RECURSIVE_PROVENANCE_AUDIT_<date>.md
```

Use `--include-active` when the paper under review is still listed as active;
otherwise it is fine to omit it. The generated report is the durable closeout
artifact for Lean axiom closure, broad/opaque paper-facing rows, direct visible
premises, source-row formula boundaries, and source-shaped reusable APIs. A
completed paper must have no theorem-status findings for its folder unless the
exact boundary is marked partial/conditional in `status.json`, the dependency
DAG, and the final validation report.
An added non-source assumption, narrower Lean model, or weaker semantic endpoint
is such a partial boundary even if the restricted theorem is internally proved.
Do not promote that case to `formalized with caveat`; reserve the caveat status
for a substantial source-paper error whose corrected endpoint is fully proved.
This audit checks tracked LLM sidecar freshness; it should not rerun LLM judges
for every paper. Refresh judge sidecars only for the target paper rows/records
that are stale, missing, or explicitly requested. An all-paper judge refresh is
a separate user request, not part of ordinary post-formalization closeout.

Also run
`python3 scripts/audit_repository.py --library-only --library-premise-audit --info-limit 0`
after reusable-library edits to fail source-shaped reusable APIs, hidden
proof-boundary section variables, axiom/opaque placeholders, and guarded debug
commands, and to list shared-library APIs with certificate/source-boundary
parameters. Then check that no completed paper wrapper still exposes one.
The same pass rejects reusable `Assumption`/`Hypothesis` declarations and
paper/source provenance wording in `AppliedModelingLib/*.lean`, and requires the
root-imported `AppliedModelingLib.LibraryDefinitionAudit` module for standard-name
definitions. When adding a standard wrapper such as a convexity, concavity,
order, metric, or probability notion, add a build-checked equivalence lemma in
that audit module against the mathlib or local canonical definition.
Use `--info-limit -1` when you need the complete direct library-boundary
inventory; CI uses `--info-limit 0` so only actionable errors/warnings appear.
The ordinary audit runs Lean-native `#print axioms` on paper-facing interface
rows to catch transitive global proof debt exactly. It separately checks
expanded `#check` statements and direct paper-local alias targets for visible
certificate/source-boundary premises. Ordinary inequalities, positivity, and
measurability side conditions are different: if they are visible in the
paper-facing statement, the statement/assumption judges validate them against
the source, and a caller may derive them from stronger visible source premises.
Do not use `axiom`, `constant`, `opaque`, or unsafe declarations to stand in
for missing source proofs.

Do not hide paper-source formulas inside reusable-library definitions. If a
formula is paper-source data used by a selected named result, expose it in that
result's transparent realization path or as an explicit certificate argument
to the reusable theorem. It needs its own `PaperInterface.lean` review row only
when it is independently presented as a named theoretical source statement;
standalone displays remain deep-only inventory items. If the formula is generic
and derived from library primitives, keep it generic and avoid
paper/result-specific names. The library premise audit rebuilds a fresh in-memory declaration index
on every run and reports direct certificate/source-boundary APIs and
source-shaped reusable definitions; do not check in a dependency index.
The reusable-library parser covers theorem, lemma, def, abbrev, structure,
class, and inductive declarations. A proof-boundary structure or package may
live in `AppliedModelingLib/`, but a paper-specific formula/window/row/source name should
not be baked into the reusable API.

The repository audit also includes a source-hygiene pass for generic code. It
discovers paper IDs and citation prefixes from the `papers/` folders, then
rejects those concrete references in reusable code, audit scripts, and generic
workflow docs. It also rejects paper theorem-number labels such as `Theorem 2`
or `Lemma 4.1` in `AppliedModelingLib/` comments. The check is intentionally standard-
based rather than function-name-based: paper metadata belongs in paper-local
files or data config, source theorem numbering belongs in paper interfaces and
validation reports, and reusable code should use domain or algorithm names.
If a term is genuinely an established algorithm/domain name, allow it in
`papers/audit_config.json`; do not add code-level one-off exceptions.

This hardened audit catches the recurring mechanical failure modes: hidden
source-row/certificate premises in paper wrappers, transitive proof debt via
Lean-native `#print axioms`, source-shaped reusable APIs, and hardcoded
paper references in generic code. It does not prove that every source formula is
mathematically correct by itself. That requires the outside-Lean formula sanity
pass, derivation of formula-bearing claims from primitives where possible, and
the statement/assumption judges for visible paper-facing text.

## Human Review Order

When the agent says a paper is done, inspect:

1. `FINAL_VALIDATION_REPORT.md`
2. `PaperInterface.lean`
3. `docs/DependencyDAG.pdf`
4. `status.json`
5. `ProofLedger.lean`, only if an exhaustive proof endpoint ledger is needed

The post-formalization audit must inspect the report and DAG before handoff.
Do not write those terminal products against a still-moving interface merely
to make intake look complete. Once the source map and paper interface are
stable, begin or resume closeout with:

```bash
python3 scripts/closeout_reuse_plan.py --paper <paper>
```

Execute only its current `next_action`. The planner first freezes source
inventory, acquires the Lean-owned graph, completes semantic review, establishes
source-to-Spec correspondence, and obtains the focused build. Only after those
lanes are current does `complete_terminal_closeout_documents` require the final
report and DAG. At that action, write `FINAL_VALIDATION_REPORT.md` and
`docs/DependencyDAG.tex` from the selected final surface, compile
`docs/DependencyDAG.pdf`, visually inspect it, and rerun the planner. Missing or
revised presentation products never invalidate the retained graph or semantic
judgments. When the planner subsequently schedules strict closeout, use the
exact `run_paper_closeout.py` command it prints. That worker revalidates the
targeted DAG/final-report and semantic closeout gate: completed or conditional
papers must name the DAG TeX/PDF artifacts, record visual inspection in the
`DAG Audit` or `DAG Status` section, include validation checks, and avoid stale
placeholder language such as `not checked` or `not run`.

A low-level audit, source-record producer, dashboard refresh, or sidecar
generator is not a routine frozen-closeout precursor. Run one only when the
planner schedules it or when a named failure requires that exact diagnostic;
then return to the planner rather than treating the diagnostic as acceptance.

The worker also finalizes closure inside the same passing strict transaction:
its issuer-protected runtime pass publishes the accepted graph and writes the
schema-6 human pointer before success is reported. A planner result with
`closeout_complete: true` has no further action. A serialized worker result
cannot be finalized later; if in-process publication failed, inspect the result
and rerun the exact current transaction. Unchanged Lean graph and semantic
judgments remain reusable, while the cheap gates and complete tracked-module
elaboration rerun.

The current planner never schedules a historical source-record raw reissue.
An unclosed paper without the v11 graph-native surface receives
`upgrade_to_current_protocol`; prepare that surface rather than manufacturing
a new legacy raw receipt. Existing accepted historical graphs remain valid
under their recorded protocol and are not reopened merely by this producer
retirement.

Prospective v11 planning uses exactly one source-intake authority. New intake
uses the reviewed source-inventory plan and its exact materialized source map;
an already-open migration may retain its selected tracked intake freeze. The
typed route preflight and builder-issued semantic transaction own all later
checks. The planner does not separately reopen the dashboard's legacy coverage
sidecar or reconstruct source-to-Spec cards from presentation rows.

Once the cheap protocol and saved-review-container checks pass, the planner
loads one current Lean graph checkpoint into one evidence snapshot transaction.
It retains that context and uses the graph's exact Spec, paper-prerequisite,
and reusable-library target projection for all semantic-review deltas and later
strict checks. Reviewer-material commands use `--v11-review-graph`; packet and
dashboard caches are generated later for presentation and are never target or
reuse authority. A missing graph schedules the single graph-preparation action
rather than falling back to packet bytes or a second Lean/context pass.

For a named failure diagnosis only, a maintainer may run the underlying audit
without creating a competing execution record:

```bash
python3 scripts/audit_repository.py --paper <paper> --paper-closeout --include-active --info-limit 0 --no-closeout-state
```

That direct diagnostic cannot establish closeout acceptance. Re-enter through
the planner after the diagnosis or any repair; do not treat a passing direct
child invocation as a replacement for a planner-issued receipt.

Agent/formalization readiness is separate from saved human dashboard review.
If Lean builds, statement/assumption validators are current, the
paper-closeout audit passes, DAG/report evidence is current, and generated
status files are synced, the paper may be reported as formalized even with
`0/N` saved human review entries. The final report must still disclose the
human review count; if a release requires human approval, track that as a
separate promotion gate rather than as Lean proof debt.

The human-facing files should let a reader compare the formalized statements to
the paper without opening lower proof files.

Do not add filename variants for the review surface. If `PaperInterface.lean`
has hundreds of declarations, it is too broad; move helper/proof endpoints into
`ProofInterface.lean` or `ProofLedger.lean` and keep the dashboard-facing
file small.
The dashboard surface should usually be close to the paper's named definitions
and named results. Slices help reviewers navigate a real source-facing surface;
they are not a substitute for removing helper endpoints from `PaperInterface.lean`.

## Validation Commands

For reusable library work during active paper development, stay targeted:

```bash
lake build <touched-library-module>
lake build +<touched-paper-module>
git diff --check
```

Do not run a broad/full repository build merely because a shared library file
changed while the paper is still in progress. Save broad builds for natural
stopping points: the paper is complete or being handed off, you are about to
commit/push a significant integration batch, preparing a public PR/release, or
the user explicitly asks for a broad integration check.

At integration, release, or an explicitly requested repository-wide stopping
point, broaden validation as appropriate:

```bash
lake build AppliedModelingLib
python3 scripts/sync_paper_status.py --check
python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0
git diff --check
```

The broad audit checks whether existing LLM-as-judge sidecars are current. It
does not require regenerating or rerunning judge sidecars for every paper unless
the user explicitly asks for an all-paper refresh.

For paper closeout or post-formalization work, begin with the planner:

```bash
python3 scripts/closeout_reuse_plan.py --paper <paper>
```

Follow only its dependency-ordered action. When it schedules
`complete_terminal_closeout_documents`, write and inspect the final report and
DAG, then replan. Treat the paper-specific DAG/report
findings from its strict worker as blockers for a completion claim, even if
unrelated global repository findings remain. Use a direct
`audit_repository.py --paper-closeout --no-closeout-state` invocation only to
diagnose a named failure; it is not a closeout result.

The unfiltered full repository audit is a closeout/public-promotion check. It
is available through manual CI dispatch and should not run on routine push/PR
CI for ordinary documentation or proof-development churn.

At paper closeout, pass every tracked paper-owned Lean module to one
single-threaded, dependency-aware rehashed Lake transaction:

```bash
env LEAN_NUM_THREADS=1 python3 scripts/private_paper_checkpoint.py <PaperRoot>
```

Use `lake build +<TouchedPaperModule>` as a faster proof-iteration check.
Passing one interface or root module alone is not a paper closeout build.

The full target:

```bash
lake build AppliedModelingLib
```

is an integration/public-release gate when that aggregate target is part of the
prepared release. It is not the default per-paper closeout command. During
private paper development and closeout, use the focused interface and complete
paper targets above; do not present a branch as public-ready until the release
integration target is green.

For statement-facing checks, prefer the paper-local launcher from the paper folder:

```bash
./review-dashboard.sh
```

On WSL2, the launcher binds broadly by default and prints multiple Windows
browser URLs when it can detect both localhost and the WSL guest IP. If the
browser does not pop or one URL fails, keep the terminal running and try the
other printed URL. Large interfaces may need several seconds before the first
page responds.

On startup it prints stale-check diagnostics against any existing logged reviews, so
you can refresh only the changed theorem checks and avoid re-validating unchanged items.
The dashboard also shows compact paper-source action links (open PDF/text file) for
quick jumps back to the source statement when needed.
Paper-side formulas are rendered with MathJax when they look like LaTeX.

## Current statement and semantic-review route

At the beginning of a paper, establish the complete source surface before
proof search:

1. Byte-pin one exact source version and complete the outside-Lean inventory,
   formula/dependency sanity check, scope selection, and working memo described
   by the intake stage guide.
2. Create actual source models and definitions plus one transparent complete
   `Spec : Prop` for each selected source claim in `PaperInterface.lean`.
   Put the distinct theorem/lemma endpoints in `ProofInterface.lean`; a
   temporary private `by sorry` is an honest target skeleton, never evidence.
3. Run the one non-certifying architecture pre-pass, repair role confusion,
   hidden result packages, and accidental implementation premises, then freeze
   the reviewed source map and interfaces before expensive proof work.
4. Let Lean acquire the complete selected declaration graph and recursive
   premise/proof/instance closure through the current planner route. Python may
   transport that typed result but must not rediscover Lean semantics from
   source text, names, declaration kinds, or regular expressions.
5. Give the semantic judge only the ordered byte-pinned source-anchor bundle,
   any explicitly pinned context needed to interpret it, and the fully expanded
   transparent Spec emitted from Lean. Never interpose a Lean-to-TeX
   translation, curator paraphrase, theorem label, wrapper theorem, or map
   summary as semantic evidence. Every source atom must be accounted for and
   every Lean premise/conclusion atom must be aligned or reported unresolved.
6. Apply the same direct semantic standard to every material paper-local and
   reusable-library prerequisite. Ordinary registered foundations may
   terminate at their trusted boundary; unusual or materially source-defining
   concepts remain recursively reviewable by judgment.
7. Put each genuine source assumption or external theorem boundary in the
   explicit assumption/provenance lane. A displayed formula, certificate,
   witness, source row, normalization, or proof convenience is not a source
   assumption merely because a helper accepts it.
8. After proof realization is complete, run the planner-scheduled independent
   holistic source audit over the full pinned source inventory, final expanded
   Specs, material prerequisites, proof routes, and classified exclusions.
   This is an adversarial completeness check, not a substitute for row-level
   semantic review.

Begin or resume this workflow with:

```bash
python3 scripts/closeout_reuse_plan.py --paper <paper>
```

Execute only the printed `next_action`. The planner reuses unchanged
authenticated graph and semantic-review objects, regenerates cheap derived
artifacts, schedules the final report/DAG only after evidence and realization
are current, and publishes acceptance only from its issuer-protected in-process
strict pass.

The dashboard and PDF packet are equivalent optional human-review
presentations of the current graph. Generate them only after the source map and
interfaces are stable enough to review:

```bash
python3 scripts/review_dashboard_packet.py --paper <paper> --write --compile
./papers/<paper>/review-dashboard.sh
```

Saved human annotations are reviewer-owned and may not be fabricated or
auto-closed. Their absence is not a Lean closeout blocker.

Do not generate `lean_to_tex_llm.json`, `statement_match_llm.json`,
`source_record_audit.json`, or `source_record_match_llm.json` for a new
current-protocol paper. Existing copies remain readable historical provenance
for papers closed under an older protocol; they are not current semantic
inputs, current scaffold outputs, or alternative acceptance credentials.

Pinned source artifacts remain ignored by default for redistribution safety. A
fresh checkout without the exact provisioned bytes cannot reproduce a
source-byte attestation and must report that input as unavailable rather than
accepting a recorded digest alone.

For a named diagnosis, use the exact diagnostic command printed by the planner.
A standalone dashboard/precheck, evidence audit, or repository audit is useful
for repair but cannot replace the planner-issued strict transaction.

## Maintenance Note

Use the narrowest focused paper build that exercises the active proof seam.
Repository-wide builds belong to release or integration milestones, not routine
paper closeouts. If a private paper thread temporarily breaks an aggregate
build, document the exact blocker in its private status rather than inferring
anything about unrelated paper audits.
