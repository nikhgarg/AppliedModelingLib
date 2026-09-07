# Detailed Formalization Handbook

This explanatory handbook is preserved from the former monolithic skill. It
contains long-form rationale, examples, historical failure modes, and search
terms; it is not a second operational rulebook. The stage references selected
by `../SKILL.md` and `config/formalization_audit_protocol.json` are normative.
When this handbook conflicts with either, follow the stage reference and
protocol. Search this file only when the router points here for additional
context. Do not load it by default.

Use this skill to turn economics-and-computation papers into maintainable Lean
code. Keep repository-specific status out of this file; in `AppliedModelingLib`, that
belongs in paper-local `status.json`, `docs/PAPER_STATUS.md`, and the website
status table.

For new Lean files, new shared-library APIs, new paper-facing declarations, and
code already being substantially rewritten, follow
`skills/lean-community-conventions/SKILL.md`. Apply those conventions
forward-looking only: do not start broad repository-wide renaming, formatting,
import, or documentation refactors during active proof work unless the user
explicitly asks for a cleanup pass. Paper-local source-indexed names may remain
when needed for source auditability; shared reusable APIs should follow the
convention style.

When updating skills from prior sessions or user corrections, use
`skills/econcs-session-insights/SKILL.md` as the provenance workflow. Promote
durable day-to-day formalization rules into the appropriate authoritative
stage reference or proof reference;
do not leave them as a parallel operational rulebook in the session-insights
skill.

When planning automation-heavy formalization workflows, multi-agent proof
campaigns, retrieval-grounded statement translation, or compiler-guided repair
loops, also consult `skills/ai-formalization-workflows/SKILL.md`. That skill is
a source-credited ledger of external AI-formalization workflow patterns; this
formalizer router and its stage references remain operational authority for the
repository.

When actively proving a theorem, closing a `sorry`/`admit`, or repairing a
broken Lean proof, use `skills/econcs-prover/SKILL.md` as the proof-production
companion. This skill owns paper workflow, source provenance, audit surfaces,
and closeout; the prover skill owns the local Lean error/search/repair loop.

When syncing `EconCSLib-private` and `EconCSLib-public`, preparing public PRs
from private work, copying generated DAG/report PDFs, or reconciling audit
sidecars across sibling checkouts, read
`skills/econcs-formalizer/references/public-private-sync.md` first. Use that
semantic sync workflow instead of raw repository merges or broad folder copies.
Inside `EconCSLib-private`, work on `main` by default unless the user explicitly
asks for a branch or a PR-style branch workflow. Do not create a private working
branch merely because the local branch is dirty or behind; first fetch/integrate
`main` or ask before taking a history-shaping action.

In the managed Codex environment, use the default non-login command shell
unless a login shell is specifically required. The current `exec_command`
schema does not expose a `login` parameter, so do not invent one; the user
configuration `allow_login_shell = false` is the durable control. The host's
Ubuntu `im-config` login hook invokes `systemd-cat` in non-graphical sessions
and otherwise emits unrelated `Failed to create stream fd` noise. This is an
execution-environment workaround, not Lean or audit evidence. Keep the
command's working directory and explicit environment arguments instead of
depending on shell-profile side effects.

The private repository pins that control in `.codex/config.toml` and injects
`SYSTEMD_LOG_TARGET=null`. The latter also keeps an explicitly nested
`bash -lc` quiet if a command bypasses Codex's login-shell gate; do not patch
the host's `im-config` files or user shell profiles for this repository issue.

Run semantic Lean overlays with `TMPDIR=.scratch/runtime-tmp` (or another
ignored runtime directory). Overlay helpers must not materialize temporary
`.lean` sources at the repository root. If a tool session is cancelled, first
confirm and terminate its child process tree before retrying; quiet output does
not establish that the original scan stopped.

Before declaring a paper done, read `audit-and-closeout.md`; before writing or
refreshing reader-facing artifacts, read `human-facing-artifacts.md`.

## Proof Campaign Pace

During an active proof campaign, the immediate gate is limited to the current
source-shaped target, its visible premises, and its `PaperInterface.lean`
statement skeleton. Run the scoped semantic and premise audit needed to make
that target honest, then prove it. Do not make broad plan prose, a rendered
DAG, status/report refreshes, whole-paper sidecar regeneration, or exploratory
generalization work a prerequisite for an otherwise actionable proof
obligation. Update those artifacts at a material source-scope, proof-boundary,
status, handoff, or closeout milestone. Where older checklist language sounds
like a larger pre-proof gate, this rule takes precedence.

## Semantic Campaign Guardrails

Apply these source-fidelity rules throughout a proof or audit campaign:

- Establish paper credit from pinned source semantics, expanded Lean
  propositions, and checked proof closure. Declaration, field, binder, map-key,
  and function names only locate material; they never establish a conclusion.
- Audit universal conditional behavior separately from the source's required
  existence, nonvacuity, uniqueness, or positive-mass outcome. A theorem over
  an empty candidate/action family, or one conditional on a supplied witness,
  does not establish a nonvacuous source result.
- For strategic or equilibrium claims, state the literal action space, timing,
  information, beliefs/PBO treatment, payoffs, and any equilibrium or
  transition refinement. Test null and off-path branches explicitly; do not let
  an arbitrary version or an unmodelled refinement silently select the outcome.
- A member-only, one-sided, or selected-deviation certificate is local evidence,
  not a whole-equilibrium proof. Check incumbent exits and candidate outsiders,
  including positive-mass deviations and the required strict/weak response
  relation, before using it for a paper-facing equilibrium conclusion.
- Reuse audit work only per item, under exact current source/anchor, elaborated
  Lean route and dependency, audit-schema/validator, and configured-reference
  fingerprints. Preflight every configured route before accepting either fresh
  or cached evidence; a stale, ambiguous, or unresolved route fails closed.
- Normal paper coverage is the named theoretical surface. Simulations,
  numerical examples, figures, captions, and ordinary prose are deep-audit
  material unless they are needed to interpret a selected named result.
- At a paper closeout, validate the frozen source-facing surface with the
  targeted closeout audit, which owns the paper-root build. Run a separate
  focused build first only when the reuse planner schedules it. Reserve
  repository-wide builds for integration or release milestones.

## Component 1: Workflow and Organization

Operational sequencing is normative in `references/audit-and-closeout.md`:
follow `closeout_reuse_plan.py` and its dependency-ordered actions through each
explicit replan, then use its exact strict-closeout argv. The current sequence overrides
older literal build/refresh/runner examples retained below for context.
The planner's compiled identity is exact bytes; filesystem stats are guarded
accelerators only, so an identical-byte rebuild does not reopen a closeout.
Operational and engine ledgers are outside paper evidence. Existing paper
receipts are never rewritten or rerun merely to adopt a closeout migration.

### 1.1 Core Rule

Formalize theorem seams, not PDFs. Start from the paper's precise definitions,
the main result to be checked, and the smallest reusable lemmas needed to close
that result.

When a paper source has already been downloaded into the repository, treat that
local TeX/text cache as the working source of truth. Do not keep repeating web
searches for the same source during proof work. If the source is missing and
the exact TeX/later-version convention is needed, first check sibling public,
private, recovered, and archived worktrees for an existing cache and copy it
into the active paper folder. Only download when no local cache exists. Record
where the local cache lives, then use that copy for subsequent source checks.
Prefer source TeX over PDF text extraction for displayed formulas, numbered
equations, theorem labels, and appendix proof steps; PDF text is often good
enough for orientation but too noisy to settle algebraic disputes.
Before asserting that the source has an issue, a theorem is fixed, or a
coauthor-facing edit is still needed, check the current authoritative source
cache for that paper. Old source-issue memos, validation reports, LLM sidecars,
session notes, and prior suggested-edits files are leads, not evidence about
the current draft or published source. State the distinction explicitly when
needed: "the repo memo records X" is weaker than "the current source still
contains X." If the source changed, classify the old finding as still present,
changed, removed, or not rechecked before repeating it.

Use `formalized` as the repository status word for Lean-checked paper results.
Lean verification is the mechanism, not a separate paper status. Do not answer
status questions with "verified in Lean" when the intended claim is
`formalized`; reserve "reviewed" for saved human dashboard review entries and
"validation" for the audit/checking workflow.
Treat `status.json` human-facing notes as human-authored copy, even when a
field is marked `draft`. Do not add, elaborate, summarize, or reframe
`human_summary`, public notes, website notes, or paper-table comments unless
the user explicitly asks for that exact prose change. If the user asks to
remove a phrase, remove only that phrase and preserve the remaining text. If
the user says a note should be empty, set the source field to the empty string
and regenerate script-owned surfaces from that source. Put technical audit
details in validation reports, handoffs, or machine-readable audit sidecars,
not in sparse public/paper notes.
Treat `formalized` as a strong provenance claim: every exposed paper result is
proved by Lean from imported Lean/mathlib/library declarations plus explicit
theorem parameters that are either discharged by the proof or recorded as
validated paper-source assumptions. The LLM-as-judge checks are audit evidence
that the exposed Lean statements and explicit assumptions match the source
paper, but they are not themselves Lean proofs, human review, or certification
of hidden premises. Before saying a whole paper is fully formalized, confirm
the Lean-native axiom audit (`#print axioms` via
`scripts/audit_repository.py`), the row-local statement checks, and the
visible-premise/source-assumption checks are current and clean for that paper.
Treat any user request for a
"Lean axiom" or "axiom dependency" check on a paper result as a request for
the recursive repository audit path, not a single ad hoc `#print axioms` call:
the audit must expand the paper-facing row, follow paper-local aliases and
relevant library declarations, then call Lean's axiom printer on the resulting
declarations and report hidden premises/certificate APIs along the path.
When the user explicitly approves closing a paper modulo one external theorem,
prefer a single theorem-shaped, paper-local axiom over a broad endpoint axiom.
The axiom should state the external library theorem or theorem bundle being
imported, such as a stochastic-convergence or fixed-dimension solver theorem,
while deterministic paper source semantics are still encoded as concrete source
model records and bridge theorems. The final audit must expose exactly the
named axiom, plus approved Lean foundations, and the paper status/report must
call the result conditional or axiom-boundary until that theorem is proved in
the library.
Treat source-formula correctness as a separate provenance obligation from
statement text matching. Lean can prove an internally consistent theorem whose
inputs already contain a wrong displayed formula; an LLM statement judge can
also miss that the formula was assumed rather than derived. For every
formula-bearing paper result, know where the formula enters the proof:
definition body, derived lemma, explicit validated source assumption, or
partial boundary. A result is not fully formalized merely because the final
wrapper has the right-looking theorem text.
Audit numeric semantics operator by operator. Record the source and Lean value
domains, coercions, division convention, rounding/truncation, normalization,
strictness, and treatment of zero denominators. Natural-number Euclidean or
floor division is not a formalization of rational/real division merely because
the expressions share a function or variable name. Before calling a checker the
paper's algorithm, prove an expanded equivalence to the exact source formula.
Bind every numeric review item to the exact source and Lean obligation ids, and
partition every other obligation into the explicit nonnumeric lists. A proved
equivalence must point to a reviewed Lean conclusion that explicitly contains
the relevant equality or iff, not merely to any conclusion of the theorem;
for a counterexample, a witness-specific exact-formula computation is sufficient
only for that witness and must be exposed in the paper-facing conclusion.
Audit discrete operations with the same precision: an immediate ranked
successor is not a next-active choice, eventual list occurrence, or support
after hiding other candidates. Require an unfolded definition or a Lean-checked
equivalence on the exact source domain. Complete the discrete obligation
partition even when no discrete operator is present; a prose absence claim may
not override a list operation visible in the elaborated Lean manifest.
Run a recursive abstraction-debt audit whenever a paper-facing row depends on a
record, certificate, replay, process, semantics object, source model, bridge,
package, or consequences bundle. Expand the theorem's visible premises and then
inspect every input semantically against the paper source model; names are only
routing hints and are never evidence by themselves. For each input, either
identify the exact paper primitive/source assumption it corresponds to, cite the
Lean-checked constructor theorem that derives it from those primitives, route it
through an approved external boundary, or mark the row conditional/partial.
For `Certificate`, `Replay`, `Process`, and `Bridge` inputs in particular, the
audit must ask for an instantiation path from the paper's primitive model, not
just a source-looking type name or theorem wrapper.
Inspect every constructor, field, and nested result-bearing predicate
transitively, recording the declaration or constructor body used as the
expansion basis. A statement-level `matches` judgment must fail closed until
that recursive expansion is complete. Bind each definition review to the Lean
obligations where it occurs and classify all remaining Lean obligations in the
explicit definition-free list; manifest-expanded local definitions cannot be
covered by an absence claim. Then inspect the fields of every such structure
recursively until each field is
classified as a proved Lean consequence, an imported shared-library theorem, a
validated paper-source formula/assumption, a recursively audited container
field, a derived consequence-record output, a non-propositional witness datum,
an approved external proof boundary, or unresolved proof debt. The
LLM-as-judge prompt for these rows must explicitly ask whether any theorem
input or field smuggles in the result being claimed, a displayed formula,
trajectory generation, convexity, continuity, equilibrium, response semantics,
replay/trace validity, transfer preservation, or convergence that should have
been derived. Rows whose proof merely projects an opaque field such as `trace`,
`replay`, `process`, `bridge`, `directionalField_eq`,
`convex_solutionSpace`, `response`, `isMax`, `convergence`, or `continuity` are
conditional on instantiating that field, even if Lean compiles and the
top-level theorem statement matches the paper. Mark those rows as source-model
boundaries or proof debt unless a separate reviewed row proves the field from
more primitive paper assumptions.
The recursive audit is a search for an eventual source-backed leaf, not a
permission to stop at an intermediate Lean package. If a paper-facing theorem
assumes a field that is not directly a source definition/model primitive, the
audit must point to the upstream theorem or nested field that derives it from
source primitives. If that chain cannot be followed because a structure is
missing, the maximum depth is reached, a cycle appears, or a nested container is
classified as an ordinary source assumption, treat it as an audit error: a Lean
statement is not backed by the source until the derivation chain reaches a
validated source assumption, a proved primitive consequence, or an explicitly
approved external boundary.
This recursive audit must be code-backed before closeout. The source-record
producer remains the source of that payload, including Lean `#check` output for
paper rows and structure fields, so the LLM judge sees actual kernel-checked
statements rather than a prose summary. During ordinary frozen closeout, do not
invoke that producer by hand: `closeout_reuse_plan.py` decides whether a current
raw receipt can be reused, needs a judgment-only repair, or needs its one
serialized raw transition. Invoke the producer directly only to diagnose a
named source-record failure or while deliberately developing the producer
itself; return to the planner before treating its output as current evidence.
The judge
must classify every source-record field as `proved_from_primitives`,
`validated_source_assumption`, `approved_source_convention`,
`approved_corrected_condition`, `approved_external_boundary`,
`visible_boundary_component`, `derived_from_visible_boundary`,
`nonpropositional_witness_data`, or `unresolved_assumed_math`; it may use
`container_recursively_audited` only for a
field whose type is another audited source/record/certificate and whose nested
fields are separately judged, and `derived_consequence_record` only for theorem
output records whose constructor proof is checked and whose premise records are
separately audited. Use `nonpropositional_witness_data` only for bare data
witnesses whose type is not proposition-valued and does not itself state a
formula, equality, recurrence, optimality, measurability, convergence,
continuity, response semantics, or trajectory semantics; the proof fields that
constrain those witnesses must still be audited separately. Do not accept
`matches` for a row whose decisive math appears only as a record field
projection.
Use `visible_boundary_component` only for recursive/internal fields exactly
unpacked from a visible theorem-boundary premise, and
`derived_from_visible_boundary` only for recursive/internal fields Lean derives
from visible theorem-boundary premises; neither classification may be used for a
theorem-boundary input itself.
For every v10 boundary input or conclusion dependency that the generator can
associate with a source contract, retain the generator-owned association of
the fully qualified Lean declaration and declaration hash to the exact
source-map identities. Never reconstruct that association from a row, binder,
or function name. A `validated_source_assumption` is archival source credit
only for a literal source condition. A visible convention instead uses
`approved_source_convention` with the exact current convention IDs and
canonical ledger-object digests; a condition under a corrected source target
uses `approved_corrected_condition` with the exact current corrected-target
hashes and governing source-defect IDs. These dispositions are compatible with
`formalized` only when their source-map association and fidelity-ledger pins
validate. `approved_external_boundary` remains a partial/conditional boundary,
not a substitute for either accepted class.
At closeout, conclusion provenance being `[]` is not enough: the targeted
paper-closeout audit may still fail on a stale saved
`source_record_audit_sha256`. Let the planner's bounded identity preflight
decide whether the exact current audit is reusable, needs a judgment-only
repair, or needs one serialized raw transition; do not invoke the target-paper
source-record producer by hand as a closeout predecessor. Regenerate the
canonical source-record audit only when `PaperInterface.lean`, source maps,
review configuration, imported declaration surfaces, source artifacts, or an
explicit generated-surface producer version changes the emitted semantic
obligation surface, or when cache validation fails during active diagnosis.
Validator, dashboard, migration, diagnostic, documentation, report, and
sidecar-summary edits alone must not trigger a raw scan. If a paper keeps a legacy root copy of
`source_record_audit.json`, synchronize it with the canonical `audit/` copy or
remove it according to the paper's existing sidecar policy; do not leave a
canonical/legacy divergence and call the paper post-audit clean.
Do not issue or consume a pairwise `partially formalized` -> `formalized`
compatibility receipt. Generate or reuse the canonical source-record audit at
the paper's final status. A historical transition artifact may remain in an
older paper as provenance recoverable at its issuing commit, but it is not a
current acceptance credential, a template for new work, a naming-based
equivalence, or a status bypass. Current closure follows the ordinary exact
source/declaration/signature/statement/atom identities.
At a real closeout/publication boundary, run the reuse planner and then its
exact printed `strict_closeout` argv, including its profile, plan identity, and
new-run disposition.
During active formalization on an unfinished paper, do not run that closeout
gate unless the user explicitly asks for post-validation; use targeted Lean
builds, placeholder scans, and row-scoped LLM-as-judge checks for the exact
changed statements, assumptions, or source-record fields. Do not start the full
dashboard/sidecar/final-report audit loop merely because a proof-surface row,
source record, or status entry changed while the paper is still known
unfinished. If a proof pass adds or changes source-record fields, run the
code-backed recursive audit or LLM judge only for those changed records/rows
when needed to prevent hidden assumptions, but defer full dashboard prechecks,
full statement sidecar regeneration, DAG/final-report audit updates, and
`--paper-closeout` until the paper is actually done or the user explicitly asks
for that validation phase. The eventual closeout gate must report missing,
stale, or unresolved `source_record_audit.json` /
`source_record_match_llm.json` sidecars as assumption/provenance findings.
In a proof-production campaign, prioritize actual Lean and mathematical proof
obligations. Update documentation only at a meaningful proof milestone,
closure, or handoff boundary, or when the user explicitly asks; do not refresh
DAGs, validation reports, generated status tables, broad audit sidecars, or
commit/push solely because an intermediate theorem changed.
While a concrete proof obligation is actionable, defer routine documentation
work; use checked theorem progress rather than status churn as the campaign's
default unit of work.
Separate scoped dependency closure from whole-paper completion in status
answers and documentation. A dependency paper can have the PG-needed continuum
or matching chain checked while the broader paper remains `paper draft`; say
"closed for the scoped dependency surface" rather than "done" unless the source
inventory, non-curated checked rows, remaining analytic bridges, and
post-formalization audit all support whole-paper `formalized` status.
Treat the configured review source as a closed review surface, not a scratch
file. It must be `PaperInterface.lean` for every paper. Large papers should
move implementation aliases, proof seams, and helper endpoints to
`AuditInterface.lean`, `ProofInterface.lean`, or implementation modules, but
the row-level dashboard and LLM-as-judge declarations must be exported directly
from `PaperInterface.lean`.
Every declaration exported from the configured review source must be classified
in `status.json` `review_surface.include_names`,
`review_surface.assumption_names`, or `review_surface.auxiliary_names`. Use
`auxiliary_names` only for proof-facing helpers intentionally excluded from
statement review, and never to hide a named paper theorem or a non-source
premise. If a helper theorem needs a
`...Certificate`, `...Model`, `...Semantics`, `...Bridge`, `...Package`,
`...Inputs`, `...Process`, or `...Consequences` premise that is not itself
derived from prior Lean code, keep it in
`ProofInterface.lean`/`MainTheorems.lean` unless it is a reviewed row or a
validated assumption/proof boundary. During active proof work, after a
configured review-source edit run targeted checks for the changed declarations
and premises; do not enter the full dashboard/sidecar workflow solely because
the review surface changed. At frozen closeout, the planner-issued strict gate
performs the current paper-wide semantic and hidden-premise validation. Use
`python3 scripts/review_dashboard.py --paper <paper-folder> --precheck` only to
diagnose a named dashboard failure before changing the surface; it is not a
routine closeout predecessor and a clean statement-judge sidecar alone is not
evidence that hidden premises or unreviewed helpers are absent.
Before creating a paper-local definition, record, theorem family, or reusable
`AppliedModelingLib/` primitive for a common proof seam, do a dependency and
shared-library context load. Search imported upstream libraries first:
`Mathlib/` for mathematical structures and theorems, `Cslib/` for computer
science and runtime notions, and `Optlib/` when it exists in the workspace or
Lake manifest for optimization-specific APIs. Prefer those definitions and
results over creating local replacements. If an upstream API almost fits, add a
thin bridge lemma or source-facing notation around it; only introduce a new
library primitive after recording why the upstream API is not adequate. For
overlapping EC, game-theory, social-choice, mechanism-design, optimization, or
proof-pattern seams, also scout the potential upstream Lean sources listed in
`docs/UPSTREAM_LEAN_SOURCES.md`, currently including
`elazarg/GameTheory`, `alexfleetcommander/lean-proofs`, and
`gametheoryinlean/EconCSLib`. Treat those as scouting sources unless
toolchain, license, API stability, and dependency approval have been checked.
If you use or port material from any upstream source, cite it with repository
URL, file/module path, commit or release when available, license status, and a
short description of what was reused; place that provenance near the resulting
Lean code or in the paper/formalization plan, and cite it in human-facing paper
text when the reuse affects the manuscript.
Search `AppliedModelingLib/` next for the domain noun and proof shape:
equilibrium/best-response/a.e.
exception, threshold/cutoff, CDF/quantile/PIT/tie-breaking, finite mixture,
Gaussian/admissions/testing, LP/certificate, ranking/social choice, auction, or
large-deviation. Open the most relevant shared files and reference notes before
adding local scaffolding. If a reusable API exists, import and specialize it.
This check belongs in the initial outside-of-Lean plan for every paper and
again whenever a proof loop starts building wrappers around a standard concept.
Also search related paper folders, especially completed or recently active
papers in the same domain, before adding paper-local machinery. Many reusable
algorithmic layers first appear inside a paper folder before being promoted to
`AppliedModelingLib/`; do not reinvent a simulator, runner, trace generator, dynamic
process, checker pattern, certificate, or source-model constructor until you
have searched sibling papers for the same domain nouns and declaration shapes.
If two papers need the same machinery, elevate the common core into the shared
library or route the current paper through the existing reusable paper layer as
an interim step, rather than creating parallel incompatible APIs. Record in the
outside-of-Lean plan which related paper folders were checked and why the chosen
API is the one to build on. If the user, notes, or repository history suggest a
specific same-domain paper already built the machinery, pause implementation and
inspect that paper plus its imports before adding new declarations.
For continuous equilibrium work in particular, check
`AppliedModelingLib.Foundations.Optimization.ChoiceEquilibriumAE`,
`StrategicEquilibrium`, and the admissions/testing probability modules before
defining a local equilibrium or distributional interface.
For continuous optimization or geometry work, assume mathlib probably already
has the basic objects: norms and distances on finite products, `WithLp`/`PiLp`,
inner-product and finite-dimensional spaces, Frechet/scalar derivatives,
convexity/concavity/extrema, projections, Holder inequalities, and special
function derivative rules. Search and reuse these before writing formula-level
norm, derivative, convexity, projection, or argmax APIs in `AppliedModelingLib/`.
The outside-of-Lean plan must contain a short "shared-library reuse checkpoint"
before any substantial proof campaign: list the shared declarations or modules
inspected, including relevant mathlib/cslib/optlib candidates, potential
upstream Lean sources from `docs/UPSTREAM_LEAN_SOURCES.md`, the API chosen, and
any near-miss that was intentionally not used. Include citation/provenance for
any upstream material used or ported. If that checkpoint is missing, add it
before continuing. If a proof loop starts
creating several local wrappers around a standard notion, pause and update this
checkpoint instead of continuing the wrapper stack. A reusable concept should
enter the paper proof through the shared API unless the plan explains the
source-specific obstruction.
In particular, do not use a syntactic recursive dependency scan as the primary
proof-debt test. Lean already knows the transitive proof dependencies of a
closed theorem: `#print axioms` must report only approved standard foundations
such as `propext`, `Classical.choice`, and `Quot.sound`. Use the expanded
`#check`/dashboard premise audit for visible theorem hypotheses, and use
source-shaped library/API hygiene to prevent paper formulas from being hidden
inside reusable definitions. The formula audit must be recursive: if a
paper-facing theorem uses a library definition or theorem whose parameters,
fields, or body encode a source displayed formula, the LLM-as-judge workflow
must inspect the expanded formula or a proved paper-local equivalence to it.
The statement judgment must contain a separate numeric-semantics review even
when the named wrapper unfolds: it must compare source and Lean domains,
coercions, arithmetic operators, rounding, normalization, and boundary cases.
Do not let an implementation-level Boolean inherit source fidelity from its
name or from agreement on unrelated test inputs. It must also contain the
parallel discrete-semantics review, with source and Lean order sensitivity made
explicit for successor, active-choice, occurrence, filtering, and support
operations. Both reviews must cover every source and Lean obligation by id.
This audit must include paper-local structures as well as reusable library
definitions. For every source-semantics record, add a brief field provenance
table in the paper plan, handoff, validator ledger, or status notes before
calling the row fully formalized. If the desired theorem should follow from
paper assumptions but currently follows only because a record field states the
needed fact, the correct next step is to refine the source model or prove a
constructor from primitive assumptions, not to let the record field pass through
the assumption judge as ordinary source text.
The source-record audit is not satisfied by a natural-language list of fields.
It must be generated from code that parses the review rows, recursively follows
record/certificate/source-model types, and feeds those row and field types back
through Lean. If the helper misses a local pattern, patch the helper or the
repository audit before accepting the LLM result. The LLM judge should see the
source text, Lean `#check` output, dependency path, and field provenance, and it
must answer the narrower question: is this mathematical source statement proved
by earlier Lean declarations, or is it merely assumed by a source field?
Do not allow "the library definition says it" to substitute for source-formula
validation. Ordinary source-visible theorem conditions such as positivity,
measurability, or ordering hypotheses should be validated by the
statement/assumption judges, but they are not the same thing as global proof
debt.
Do not rely on Lean declaration names, library names, source-map keys, or
dashboard row names as semantic evidence. If a source paper defines an object
with a standard name such as an algorithm, equilibrium concept, stochastic
process, or matching-market primitive, and a paper wrapper uses a reusable
library definition for that object, add a paper-local bridge/equivalence row
whose statement expands both sides enough for source comparison. In
`audit/paper_statement_map.json`, any source item that points directly to a
reusable `AppliedModelingLib/` declaration in `lean_declarations` or
`support_lean_declarations` must also list a paper-local bridge under one of
`semantic_bridge_declarations`, `paper_equivalence_declarations`,
`source_equivalence_declarations`, or `library_bridge_declarations`. The
repository audit treats missing bridge rows, unresolved bridge rows, bridge
rows hidden off the configured review/assumption surface, missing `Source
status:` bridge comments, and coverage reasons such as "matched by name",
"exact source-key", or "exactly matches current dashboard row name" as
provenance debt. The correct fix is a semantic paper-local
definition/equivalence checked by the statement judge, not renaming the Lean
declaration to look more source-like. For example, if a source theorem says
"Thompson sampling" or uses a known order-statistic/noise primitive, the paper
must prove or expose a source/library bridge stating that the imported
definition is the source's object; the audit must not accept the shared name as
evidence.
Classify every source-map item explicitly with `source_kind`. Definitions and
predicate vocabulary may use `definition` or `predicate_vocabulary`; theorem,
proposition, lemma, corollary, claim, and runtime items are claim-bearing and
must resolve to reviewed Lean theorem declarations. Use
`proof_lean_declarations` as the canonical route; a legacy
`lean_declarations` route is acceptable only when its elaborated declaration
kind is itself a theorem. A `def` or `abbrev` whose body is the desired proposition only
names the obligation and never proves it. This remains true when the declaration
has a theorem-looking name, and a theorem remains proof evidence when it has a
neutral name: inspect elaborated declaration kind and statement semantics, not
identifiers. Qualified declaration routes must resolve exactly rather than fall
back to an unrelated short name. Starter theorem rows may deliberately use
`by sorry` after their statements are audited, but they remain open proof
obligations until the placeholder is removed and cannot certify themselves.
If a paper theorem cannot be derived without an extra geometric/model premise,
do not force that premise through the source-assumption judge just to keep the
headline theorem. Expose the exact missing formula as a record-free predicate,
prove the strongest no-hidden-premise alternative (for example `conclusion ∨
¬ missing_formula`), and separately prove any exact restricted theorem whose
extra condition really discharges the formula. The paper report and statement
judge should mark the restricted theorem as a conditional boundary rather than
a match to the unrestricted source theorem.
The hardened repository audit is standard-based, not function-name-based. It
rebuilds declaration indexes each run, follows paper-local aliases for visible
premises, asks Lean for transitive axioms, scans reusable library declarations
for certificate/source-boundary APIs, rejects reusable `Assumption` or
`Hypothesis` declarations, rejects paper/source provenance wording in
`AppliedModelingLib/*.lean`, checks source inventories for name-only source coverage,
requires paper-local semantic bridges for direct source-map-to-library links,
requires those bridges to be reviewed rows with source-status provenance,
and checks generic code/docs for concrete paper IDs, citation prefixes, or
paper theorem-number labels. Put paper metadata in paper-local files or data
config; keep `AppliedModelingLib/`, audit scripts, and generic workflow docs
paper-neutral. If a citation-like term is truly an established algorithm/domain
name, record that as a data-configured allowlist entry rather than a code
exception. This audit reduces hidden-premise, name-matching, and generic-code
drift, but it still does not prove source formulas correct by itself; do the
outside-Lean formula sanity pass and derive formula-bearing claims from
primitives whenever possible.
Shared-library comments and docstrings are part of this generic surface: do
not describe reusable results as "Theorem 1", "Lemma 2", or by a paper ID even
when the result was extracted for a paper. Use paper-neutral mathematical
language such as "finite-product likelihood factorization" and leave the
paper-number crosswalk in the paper folder, final report, or status metadata.

Unless told otherwise, you do not have a time limit; keep going until you reach
the requested stopping condition or a clean theorem/compile boundary. Run the
full post-paper checklist, review-dashboard/audit workflow, and polished
`FINAL_VALIDATION_REPORT.md` update only when the paper is genuinely finished
or the user explicitly asks for post-validation. For intermediate progress on
an unfinished paper, use targeted Lean builds and a short status/handoff update
instead of spending tokens on the full audit/report cycle. Do not run the
closeout planner or its underlying strict audit for routine
progress on a paper that is still `partially formalized`, `conditional`, or
known to have remaining library/proof-boundary work, unless the user explicitly
requests closeout/post-validation or the next action is a public PR/release
handoff. In-progress checks should normally be limited to the edited Lean
targets, JSON/line-count sanity checks, placeholder scans, and optional
row-scoped LLM-as-judge checks for newly changed statements, assumptions, or
source-record fields. Defer dashboard prechecks and full sidecar/report
regeneration until the paper is actually done or the user requests
post-validation.

Do not confuse "keep going" with broad exploration or with optimizing for the
fastest next small lemma. Default to a top-down completion plan for the whole
paper. Start from the named paper results that remain unclosed, identify the
source-model or library layer that would discharge each visible certificate or
conditional premise, and order the work by the shortest route to full
paper-level closure. Use small theorem batches as the execution unit only
after that overall route is clear, and choose those batches because they remove
a paper-facing obstacle on the completion path. Avoid adding local helper
wrappers merely because they are easy unless they visibly reduce the final
theorem assumptions or turn a documented source-model gap into a proved bridge.

Once the top-down route is clear, move in tight compile/proof loops: identify
the current paper-facing theorem seam, make a coherent batch of edits, run only
the requested or necessary targeted build, and patch the compiler's concrete
line errors. Avoid rereading large files after you already know the relevant
structure; use `rg` for exact declaration names and narrow line windows around
compiler diagnostics.
In a paper-by-paper multi-agent campaign, assign one active owner per paper and
exclusive file ownership for delegated proof tasks. Record a paper transition
in the coordination surface before starting the next paper, and do not enter a
paper already owned by another agent. Because all agents share the worktree, do
not edit or build a file while its owner is mid-edit; ask the owner to stop at a
coherent compiling boundary first. When the user asks for a stopping point,
freeze new theorem scope and finish only the smallest coherent targeted-build
boundary needed for a trustworthy checkpoint.
If an active proof batch edits shared `AppliedModelingLib/` library code, still stay in
the targeted-build loop: build the touched library module or namespace root and
the active paper root that imports it. Do not run a broad/full repository build
merely because a shared library file changed while the paper is still in
progress. Save broad builds for natural stopping points: the paper is complete
or being handed off, you are about to commit/push a significant integration
batch, preparing a public PR/release, or the user explicitly asks for a broad
integration check.
Do not treat a fresh clean worktree build as part of the closeout requirement
when it would trigger a cold dependency or mathlib build. Closeout should use
the active warmed worktree for targeted Lean builds plus the status/dashboard
and repository audit checks. A temporary clean worktree is acceptable only for
cheap committed-state checks such as generated metadata, `git diff --check`, or
status-sync validation, or when CI/public release work explicitly requires it
and the needed dependency cache is already available.
Do not run concurrent `lake build` commands in the same worktree: Lean cache
writes can race on `.olean`/`.ilean` outputs and produce spurious missing-file
failures. Prefer one targeted Lean build at a time, especially in shared
multi-agent sessions.
For a proof-loop module check, force Lake to resolve a **module**, not a
similarly named `lean_lib`: use `lake build +PaperName.Module` (or a source
path ending in `.lean`), not bare `lake build PaperName.Module`. A bare target
can resolve to a library/default target and return success without elaborating
a newly added or newly imported source file. The paper status may retain a
human-readable aggregate library command for release context, but the active
checkpoint and handoff must record the forced module command that actually
compiled the changed interface. After a supposedly successful focused build,
confirm that the module's `.olean` exists under `.lake/build/lib/lean/` and is
newer than the source, or use `lake env lean -o /tmp/<Module>.olean
papers/<PaperName>/<Module>.lean` after materializing its imports. Never call
a cache replay or an unforced library target proof verification.
On Ubuntu-based systems where shell calls print
`Failed to create stream fd: Operation not permitted` before otherwise normal
output, prefer noninteractive command execution with no TTY and no login shell
when the tool supports it. In this Codex environment, keep the default
non-login shell and ensure `allow_login_shell = false` is set in the user
configuration; the current `exec_command` schema has no `login` field. Treat
the warning as environment noise only if the command's exit code and real
output are clean.

When another agent will pick up later, spend tokens on durable artifacts rather
than chat: a paper-local handoff note, README/audit links, exact declaration
names, validation status, and next command. Future agents should start from
those files instead of reconstructing context from conversation history.
A handoff intended for a less capable proof agent must also give the dependency
order, exact source anchors, current theorem signatures, forbidden shortcuts,
acceptance conditions, last passing build, and a copy-paste assignment prompt.
Write that handoff only at a real pause, transition, or closure boundary; do not
interrupt an actionable proof campaign to keep it continuously polished.
When reporting Codex token usage for a paper, workflow, or publication table,
avoid file-level overcounting. Parse only `~/.codex/sessions/**/*.jsonl`;
ignore prompt history files and plugin/test fixtures. In each rollout file,
the first `session_meta` is authoritative; later embedded `session_meta`
records may come from summarized context and must not overwrite the file's
identity. For unique-session counts, build a parent graph using
`source.subagent.thread_spawn.parent_thread_id` first and `forked_from_id`
second, then collapse to root session trees. Exclude guardian/auto-review
rollouts (`source.subagent.other = "guardian"` or model `codex-auto-review`)
from human formalization token tables unless explicitly reporting tooling
overhead. Report top-level/root-only usage separately from subagent-inclusive
actual API usage; do not mix a root session count with all-descendant token
totals without saying so. Subagent and resumed rollout files can embed a copied
parent transcript after the first `session_meta`; those copied records often
include parent `token_count` events and must not be charged again. For each
rollout, find the first own turn marker whose `turn_id` shares the session id's
leading timestamp group, then compute usage as the cumulative
`total_token_usage` after that boundary minus the last cumulative
`total_token_usage` before it. Cross-check that delta against summed
`last_token_usage` records after the same boundary. Cached input tokens are
already included in input tokens, so compute uncached input as
`input - cached`; charge reasoning tokens only through the output-token row. Do
not dedupe repeated parent/resume/subagent prompt context out of a
billable-usage estimate merely because a human regards it as repeated work:
each descendant model request still sends input tokens, and prompt caching only
moves matching prefixes to the cached-input rate. Replayed context in resumed
or subagent sessions is real API usage when it appears in the rollout's own
post-boundary usage logs, but if the goal is a human-facing "unique work"
estimate, label that separately instead of presenting it as raw billable usage.
For financial reconciliation, prefer the OpenAI Costs/Usage dashboard or Costs
API over local log reconstruction.
These are general accounting instructions. Keep actual session traces, user
messages, session identifiers, and unpublished usage/cost results private.
When the latest green endpoint is a source-sequence, source-certificate, or
analytic boundary rather than the actual paper distribution/object, say that
plainly in the private handoff/plan and public status/final report. Name the
exact identification bridge still missing; do not let a compiled certificate
wrapper read like the paper theorem is fully closed.
For a pause of several days or longer, create or refresh a paper-local
`START_HERE_NEXT_AGENT.md` that is shorter than the full handoff: current
validation commands, shared-worktree caveats, the exact active proof seam,
strongest reusable endpoints, and what not to work on next. Link it from the
private paper README/plan and front repository status so a future agent has one
obvious startup path. Keep this handoff private by default; link it from the
audit/final-validation report only during a paper-done or user-requested
post-validation pass.
For a week-scale pause after a long proof push, also create a dated
paper-local handoff such as `HANDOFF_YYYY-MM-DD_WEEK_PAUSE.md` and make
`START_HERE_NEXT_AGENT.md` point to it first. That week-pause note should name
the exact current theorem seam, the strongest bridge theorem to use next, the
closed layers future agents must not redo, the files intentionally touched, and
the validation command set. Keep it concise enough to be read before opening
large theorem files.
If the latest green declarations are support endpoints rather than closed
paper results, say so explicitly in the handoff and do not over-mark the DAG.
If a paper is being paused for a stronger future model, say that explicitly in
the private handoff/plan and in the front repository status entries. Name the
three or fewer exact proof seams that remain and the strongest public wrapper
or certificate for each. Do not leave vague optimistic status such as "one
bridge remains" when multiple paper-level proof campaigns are still open.
When a remaining seam is a large family of repetitive row/table
identifications, package those facts into a source-shaped structure and expose
a single packaged bridge before stopping. Handoffs should point future agents
at the package as the proof target instead of asking them to rediscover a dozen
flat premises. Do not overclaim the packaged bridge as closing the source
model; say exactly which row-identification package is still unproved.
When bounded, Pareto, or other tail-heavy recommendation proofs duplicate the
same exact power-law finite-optimality argument, extract the FOC core into a
generic theorem parameterized by the marginal exponent, target exponent, and
exact backward/forward marginal formulas. Keep the distribution-specific files
as thin instantiations, and leave the source theorem rows `partially
formalized` or `conditional` until the probability/order-statistic derivation
supplies those exact or asymptotic marginals. Use `formalized with caveat` only
if the final theorem is closed but intentionally differs from the source
statement.
Do not derive a scaled first-difference/drop hypothesis merely from a value or
loss asymptotic such as `A - h(q) ~ C q^(-η)`. That asymptotic alone does not
control finite differences without a regularity/monotonicity theorem strong
enough for the source. If the proof needs `(q+1)*((A-h q)-(A-h(q+1)))/(A-h q)
-> η`, expose it as an explicit scaled-drop hypothesis or prove a separate
source regular-variation lemma.
For concrete bounded order-statistic laws, prefer a direct source-specific
mean-table route when it is available. An exact gamma-ratio formula for fixed
ranks can prove both the value/loss asymptotic and the scaled-drop law
internally, then feed the existing scaled-marginal certificate without exposing
`scaled_drop` to callers. Keep the reusable gamma-ratio asymptotic in the
library and the paper-shaped mean table in the paper unless another paper needs
the same table.
When a concrete iid source table is proved pointwise/top-`k` equal to a
synthetic mean table that already has asymptotic certificates, add or reuse a
small library-level certificate transport lemma rather than replaying the
asymptotic proof. For top-`k` order-statistic sources, the reusable pattern is
to prove the expected-order-statistic mean sequence equality, lift it to
top-`k` sums, and transport `ScaledMarginalLimitCertificate` through eventual
marginal equality.

Follow `docs/FORMALIZATION_STATUS_POLICY.md`. Reserve `formalized with caveat`
for the rare case where the paper itself has a substantial error in a central
advertised claim and Lean fully proves a corrected endpoint that materially
changes the claim. An extra non-source assumption, narrower Lean model, or
weaker semantic endpoint means `partially formalized`, even when the restricted
Lean theorem is internally closed. If Lean also proves that a broader arbitrary
abstraction is false but the paper-facing source theorem is closed, mark the
paper theorem `formalized` and record the broader abstraction as a scope note
or out-of-scope failed generalization, not as a caveat on the paper result.
Do not use "proof-fidelity caveat" as status language when Lean proves the
unchanged source theorem by correcting typos, filling missing proof steps, or
using an alternative proof route. In that case the status is `formalized` with
blank `main_caveat`; put the details under proof-strategy deviations,
mathematical typos/source notes, post-formalization audit notes, or a focused
source-proof ledger.
Treat an error confined to an appendix display, intermediate derivation, or
supporting lemma as a `formalized_note` by default, even when a concrete
counterexample demonstrates the printed expression is false. It becomes a
paper-level caveat only with affirmative evidence that the error changes a
central advertised/main-text claim or leaves a substantive downstream endpoint
unclosed. Do not infer that impact merely from the appendix item being named or
from the correction changing a numerical value in isolation.
Keep mathematical status separate from audit-receipt freshness. A stale or
superseded coverage/source-record sidecar must be recorded and queued for
semantic revalidation; it prevents a claim of a fresh clean closeout, but it
does not by itself turn a completed source-facing proof into a caveat or a
partial formalization. Do not hide that distinction: state both the proof
status and the outstanding audit migration explicitly.
Use `conditional` internally, and `partially formalized` on public status
surfaces, for an incomplete proof boundary: a wrapper still takes an
explicit certificate, witness, imported theorem, shortcut predicate, or
paper-model hypothesis that should be derived from the source assumptions. Do
not call this a caveat merely because Lean has not yet connected the paper's
own assumptions or appendix derivation.
Use `partial_boundary` in assumption-provenance JSON for a visible external,
library, analytic, runtime, solver, or theorem-import boundary that remains
undischarged. This can be the top-level judgment for an `assumption_*`
declaration as well as an individual premise judgment. Do not downgrade it to
`documented_caveat` unless the source statement itself is false, missing a
needed non-source condition, or intentionally repaired in the Lean endpoint.
Use `documented_additional_assumption` for a non-source condition that a human
has approved as an explicit restriction. It forces `conditional` or
`partially formalized`; it cannot coexist with `formalized` or `formalized with
caveat`. Human approval may authorize publication, but it does not turn a
restricted endpoint into a full formalization of the source claim.
Use the following anonymous classification examples when deciding status and
report language:

| Situation | Classification | Public/report language |
|---|---|---|
| A central printed theorem is substantially false, its correction materially changes the paper's claim, and Lean fully proves the corrected endpoint. | `formalized with caveat`; record `status_impact: formalized_with_caveat`. | "Paper issue/caveat: the source statement needs <substantial repair>; Lean proves the corrected statement." |
| The paper/source model already implicitly or explicitly assumes the domain condition, such as positive capacity, more objects than slots, interior parameters, finite support, no ties, or a nondegenerate witness needed for an exact rather than at-most statement. | Not a caveat. Treat as a source theorem condition or source-model condition; use `paper_condition`, `source_text`, or `human_verified_source_implicit` in assumption/provenance sidecars. | "Additional/source condition: the theorem is stated with <condition>." Keep `main_caveat` blank if fully proved. |
| The user approves an extra non-source restriction needed for a central claim, but has not explicitly superseded the archived target. | `documented_additional_assumption`; status is `conditional` internally or `partially formalized` publicly, never either full-closeout status. | "Additional assumption: <restricted claim> is proved under <condition>; the source endpoint remains open." |
| The source has a likely typo, finite-bound slip, sign error, quantifier-window gap, or missing proof step, but Lean proves the substantive advertised theorem through a corrected intermediate statement and the correction does not materially change the endpoint. | Source-proof note or proof-strategy deviation, not a paper caveat; record `status_impact: formalized_note`. | Put it under mathematical typos/source notes, proof-strategy deviations, or the post-formalization audit; keep status `formalized` and `main_caveat` blank. |
| An appendix/intermediate lemma is globally false as printed, but Lean proves every substantive advertised downstream result by a different source-valid route and records the corrected condition plus counterexample. | Source-proof note with `status_impact: formalized_note`, unless the defect substantially changes a central advertised claim. | Keep status `formalized`; write a short math note with the source statement, actual Lean statement, counterexample, and downstream repair. |
| The source uses private data, empirical plots, implementation measurements, or descriptive program/class instantiations not needed for the mathematical theorem target. | Out of Lean theorem scope, not a caveat and not an additional assumption. | "Empirical/descriptive material is out of theorem scope." Do not list as remaining proof debt. |
| Lean currently assumes a solver theorem, convergence theorem, process law, runtime bound, certificate, source-record field, or bridge predicate that should be proved from paper primitives. | Proof/library boundary: `partial_boundary`, `conditional`, or `partially formalized` until proved; record `status_impact: partially_formalized` when tied to a source-proof defect. | "Full formalization requires proving <single boundary>." Do not call it a caveat. |
| A converse, bridge lemma, or source derivation is missing but looks provable from the current source assumptions. | Missing proof debt. | Either prove it, or mark a proof boundary. Do not call it a caveat merely because it is not proved yet. |

An explicit exception exists only when the user/author states that a corrected
model is the governing formalization target, rather than merely approving an
extra assumption. In that case, use an
`author_approved_corrected_model` formalization scope: pin the approval memo
and original archive, enumerate every correction and source anchor, set
`archival_equivalence_claimed: false`, map every expanded model field and
paper-facing target into a current semantic contract, and keep the archived
defects as visible deltas. Only then may `formalized` mean “formalized for the
author-approved corrected target”; it must never mean that the archived paper
was derived unchanged. This scope is a high-bar closeout mechanism, not a way
to erase ordinary additional assumptions.

The semantic contract must be structural and fail closed. Bind the complete,
canonicalized contents of every governing correction, not only correction IDs.
New corrected-model semantic contracts use schema 3 and include the schema-2
conditioning/calibration, expectation-definedness, and
null-cell-totalization/partition-scope dimensions; a historical schema-2
contract remains an archival record and cannot be relabeled as having reviewed
those later dimensions.
Regenerate the source-record audit from the current `PaperInterface.lean`, then
map every generated semantic-model item by its fully qualified declaration and
per-item digest. For every detected semantic dimension, record a checkable
source locator, a source-versus-Lean comparison, a disposition, and the exact
Lean evidence; any bridge declaration must be present in the current imported
paper-local Lean surface. Map each approved target result and each visible
model/assumption condition separately to its exact generated item, digest, and
fully qualified model-record binding. Author-approved corrections or additional
assumptions must also pin the approval artifact. Do not match a declaration,
record, field, or binder by its final component or any other spelling heuristic:
qualified identity and elaborated/expanded type structure are the evidence.
Missing, stale, ambiguous, or name-only mappings are a closeout failure, not a
reason to reuse an older LLM sidecar.

Empirical work is out of the Lean theorem surface only when it is independent of
the disputed theorem or algorithm. If an empirical table, reduction, bootstrap,
or aggregate used an implementation whose soundness, completeness, or runtime
claim has failed, trace that dependency row by row. Mark affected outputs as
requiring replay or cross-validation, but do not infer that reported numbers are
false merely from an algorithm-level counterexample. A credible replay must pin
the implementation revision, raw inputs or CVRs, preprocessing and adjudication
rules, candidate/tie maps, arithmetic and quota conventions, environment,
random seeds, and generated artifacts.

For a user-approved axiom boundary, keep the axiom in the paper folder's
`Assumptions.lean` or another paper-local assumptions file, give it a precise
`assumption_*` name, and validate it as `partial_boundary`. Do not put
paper-specific axioms in reusable `AppliedModelingLib/`, and do not hide paper formulas
inside a generic axiom that the recursive audit cannot identify.
Do not use `formalized with caveat` for source-quality notes, poor OCR, or an
audit observation that does not change the closed paper-facing theorem. Put that
note in the final report and leave the status `formalized`.
For such source notes, do not use `dag_caveat` styling or a caveat legend in
the dependency DAG. Keep the named theorem/lemma node in its ordinary
formalized style, mention the correction in concise paper-facing language, and
put the detailed statement/counterexample in the final report or a focused
math note.
For standalone public-facing source notes in a paper folder, follow the
KR/GKGMM note pattern rather than writing an agent handoff: include the paper
statement, the exact proof-step or statement issue, the statement proved in
Lean, why the correction appears, downstream impact, suggested repair options
if applicable, and Lean references. Avoid workflow boilerplate, old-session
history, and Lean declaration dumps beyond the few names a reader needs to
find the formalization. Recheck the current source cache before writing the
note, and link the note from the final validation report when it is part of the
paper's public source-quality record. Unless the user explicitly requests a
restricted coauthor artifact, do not label the note “author-facing”; begin
with its mathematical issue and present disposition.
For finite-size or premise-implication notes, start with a short `Status`
section that distinguishes a proof-premise gap from a counterexample to the
theorem statement. Include the exact printed premise, the finite condition
needed by the proof route, and a small numeric witness if the printed premise
does not imply the needed condition. State whether downstream theorem rows use
the corrected condition explicitly or avoid the proof route; do not let the
note read as a hidden caveat or as proof debt in unrelated results.
If the same source proof also has a local proof-detail repair that does not
change the exposed theorem statement, such as a missing sign split after an
absolute-value condition, describe it separately from the statement-changing
premise gap and say exactly which Lean lemma discharges it.
Frame these notes as implication failures (`printed premise P` does not imply
`proof-step premise Q`) unless you have an actual counterexample to the source
theorem. Explicitly name the affected paper-facing results and the nearby
results that are not affected, so the note does not accidentally
cast doubt on unrelated formalized endpoints.
If a focused source note for the same issue already exists under the paper's
`docs/` folder, revise that note instead of creating a duplicate. Keep the note
public-facing: a short summary first, then paper statement, proof-step issue,
Lean repair, downstream impact, and suggested source-text repair. Do not bury
the conclusion under declaration inventories, command logs, or agent handoff
history.
When the user asks for such a note as the main deliverable, keep the edit
focused on a `docs/*SOURCE_NOTE.md`-style artifact and commit that artifact;
do not trigger broad status/DAG/audit churn unless the note changes the actual
paper status or the user explicitly requests a closeout pass. If unrelated
proof work is dirty in the worktree, stage only the focused source note and
directly relevant skill/doc updates; leave the proof WIP unstaged unless the
user explicitly asks to checkpoint it too.
When a fully proved endpoint exposes a standard regularity condition needed to
interpret a source formula (for example continuity/positivity needed for a
Laplace-principle reading), classify it as a validation note if the user/source
review accepts that reading and the Lean theorem does not leave proof debt.
Record the condition in `Assumptions.lean` and the assumption sidecar with
`paper_condition`, `source_text`, or `human_verified_source_implicit` premise
judgments as appropriate; do not mark it `partial_boundary` or
`documented_caveat` unless it is actually an undischarged theorem import or a
source-statement repair.
When the paper itself defines a convention that selects, erases, normalizes, or
packages terms, do not re-label that convention as a caveat merely because an
alternative raw mathematical object would differ. Close the source-shaped
statement, record the convention in an agent-facing audit note if future agents
are likely to confuse it, and keep the public status and human verdict focused
on whether the paper-facing theorem is closed.
For generated status files, keep `main_caveat` blank on clean `formalized`
papers. Do not put provenance summaries such as "axiom audit clean",
"assumptions source-matched", "human verified", or "no hidden premises" in a
caveat field. Those are validation/report notes, not caveats. Use
`main_caveat` on `formalized with caveat` only for the substantial central
source-paper error that justifies that status. On partial work, the field may
name the explicit remaining boundary. Otherwise let the public table be sparse.
Before finalizing a public README, DAG, generated status surface, or validation
report, audit every `formalized with caveat` row. Run a focused grep such as
`rg -n "formalized with caveat|Formalized with caveat|dag_caveat|Caveat:"`
over the changed public paper/report/status files, then classify each hit. If
the issue is an unfinished theorem, external theorem import, runtime layer,
analytic derivation, missing library component, or other proof boundary that
does not close the intended source endpoint, use `partially formalized` or
`conditional` and describe the remaining boundary. Keep `formalized with
caveat` only for a substantial source-paper error in a central advertised
claim when Lean fully proves the corrected endpoint. Minor corrected statements
and added non-paper assumptions do not qualify: the former are formalized notes
when the substantive endpoint is unchanged, and the latter are partial.
If any named source endpoint still exposes an explicit certificate, witness,
external theorem, or paper-model hypothesis that has not been derived from the
paper's primitive assumptions, the whole paper is `partially formalized`, even
if most theorem infrastructure compiles. It may still be public, but the
paper README, DAG, generated status surfaces, and final report must all name
the exact remaining certificate or external-library boundary.
If a paper-facing theorem genuinely needs a source assumption, expose that
assumption as a first-class declaration in paper-local `Assumptions.lean`
rather than as an arbitrary theorem hypothesis. Name it `assumption_*`,
`paper_assumption_*`, or `source_assumption_*`, list it in `status.json`
`review_surface.assumption_names`, and validate it in
`assumption_match_llm.json` with an independent source-assumption judge. A
premise is allowed to remain in a `formalized` endpoint only if it is routed
through that assumption ledger and the judge confirms it is an actual
paper/source model assumption. Capacity equations, threshold identities,
density normalizers, selection-mass formulas, row packages, and certificate
fields are proof obligations unless the paper explicitly assumes them.
Use the strict prompt sidecars when doing this validation. `lean_to_tex_llm.json`
should record
`prompt_version: "lean-to-tex-v3-strict-context-free-semantic-inputs"` and
preserve every binder, hypothesis, domain, named predicate/wrapper application,
direction, and conclusion in the translation; it must not turn a named premise
into a theorem label, source-like phrase, or proof-route summary. Each row needs
the current `lean_statement_sha256`; missing digests are stale audit evidence,
not optional metadata.
All model/agent audit sidecars are fail-closed. A blank scaffold, parse error,
missing file, missing current `prompt_version`, missing current digest, missing
validator/model identity, missing timestamp, stale source inventory, stale
dashboard surface, unrecognized judgment, failed run, or item without an
explicit success verdict is an alarm and does not count as audit evidence. The
only passing state is a current sidecar whose version, digests, validator
metadata, and recognized success judgment match the current Lean/source inputs.
The sole statement/coverage-sidecar exception is the semantic-contract closeout
bridge. It is available only to a completed paper that opts into
`semantic_contract_schema: 1` and whose curated, byte-pinned source inventory
routes every ordinary claim-bearing item to a manually substantive,
anti-circular `Prop` Spec and an exact Lean-Meta-checked evidence theorem. An
explicit byte-pinned `user_approved_scope_exclusion` remains visibly
claim-bearing but receives no proof credit; every other claim needs the exact
contract. The bridge may replace only an absent or explicitly empty
non-evidence review-surface, statement, or coverage scaffold. It must never
hide a populated, stale, malformed, uncertain, or adverse sidecar, and it does
not relax source-record, semantic-model, corrected-target, source-anchor, or
assumption-provenance gates. Declaration names only route Lean Meta; they are
not semantic evidence.
Do not convert a missing or failed judge run into a warning merely because Lean
builds; Lean proves the encoded statement, while these sidecars audit whether
the encoded statement and visible assumptions match the paper.
At public-facing closeout, require an explicit current `review_surface_llm.json`
pass even for small dashboards. The 30-row threshold is an early workflow prompt
for broad human review, not an exemption from final review-surface evidence.
`statement_match_llm.json` should record
`prompt_version: "statement-match-v10-semantic-fidelity-seat-stopping"` and reject
omitted source subparts, extra non-source hypotheses, hidden strengthening
inside named predicates, formula-level changes, broad aggregates, source-row
packages, certificate/replay/process/bridge packages, and any input whose
semantics does not match a paper primitive or a Lean-derived consequence of
paper primitives. The statement judge must inspect named predicates/wrappers
semantically; phrase overlap and source-looking Lean names are not evidence.
Each item needs current Lean, paper, and TeX statement digests.
Each item must also carry an atom-by-atom semantic obligation ledger tied to
the machine-generated elaborated Lean declaration manifest:
`source_obligations`, `lean_obligations`, `obligation_alignment`,
`unmatched_source_conclusions`, `unmatched_source_inputs`,
`unjustified_lean_inputs`, and `unmatched_lean_conclusions`. Every Lean
obligation has a `signature_ref` and `signature_atom_sha256`; the refs must partition all elaborated
parameter/assumption binders plus the final conclusion, and the item records
the current `lean_signature_sha256`. A match must account for every source
conclusion and every Lean input. Source
obligations need exact locators, every alignment needs an explicit mathematical
`bridge_statement`, and all four gap lists must equal the unmatched obligation
ids. A conditional boundary may account for explicit extra Lean assumptions,
but it cannot excuse an unmatched or weakened source conclusion, unmatched
source input, or unmatched Lean conclusion. Ledger ids,
theorem names, field names, and wrapper names only route the comparison; they
cannot justify an alignment.
For every new v10 paper, enable `require_explicit_source_routes` in
`status.json`. Each statement-match row must list all canonical source items it
uses in `source_routes`, pin each item's statement digest and exact locator,
state its route kind, and record semantic scope/evidence. `direct` is only for
an exact equivalent paper-facing endpoint, never a convenient shared source
assumption. Composite Lean rows must pin every source component separately.
`source_component` is for a scoped construction component and needs a Lean
conclusion plus substantive scope/evidence, not a fabricated full-theorem
equivalence. `source_model_convention` is only for an explicit source item
whose `source_kind` is `model` or `assumption`; a theorem/lemma that depends on
model conventions remains a direct result route. `model_convention_ids` pin
those prerequisite dependencies and must never reclassify the theorem/lemma.
`defect_or_remark_support` is only for quarantined/support-only
material; and `proof_support` needs a substantive source-support scope and
never supplies direct endpoint credit. Only `direct` endpoint routes carry an
exact source-conclusion/Lean-conclusion equivalence; every other route still
needs an exact source pin and semantic scope/evidence. Source hashes,
locations, scope/evidence, and conclusion obligations are the evidence;
source-map declaration links are navigation only.
For every new or materially updated v10 closeout, also set
`review_surface.llm_statement_review.require_source_claim_atoms: true` and
top-level `source_claim_atoms_schema: 1` in the source map. Every canonical
theorem-like source item must carry a nonempty `source_claim_atoms` list. Each
atom has a stable id, one byte-resolvable `source_locator`, a substantive
source-facing `semantic_claim`, and one `reviewed_lean_route`. Build the atom
inventory from the pinned source statement before inspecting Lean, splitting
every independently source-visible commitment that can change the statement's
truth conditions, scope, quantification, or promised result. The source review
must check that this list is exhaustive; a single row-level match never excuses
an omitted clause. The
route only locates the separately audited proof: it must resolve uniquely to a
configured PaperInterface theorem/lemma result row. A definition, abbreviation,
structure, certificate, source model, assumption, hidden helper, or a
conclusion-carrying record cannot receive atom credit. Existing maps without
the versioned opt-in remain legacy-compatible until they are materially
refreshed, but do not create another v10 closeout without it.

**Theorem-realization v11.** For every new paper and explicit v11 upgrade, set
`review_surface.require_source_spec_correspondence: true`. This
is a closeout requirement, not an error for a `not started` skeleton. Before
writing Lean, independently inventory every material source atom from exact
pinned source-quote bytes; do not derive the inventory from theorem, binder,
field, function, map-key, or type names. At closeout, set
`source_spec_correspondence_schema: 1` and require all of the following for
each claim-bearing source endpoint:

- a transparent `Spec : Prop` whose paired theorem/lemma has exactly that type
  by Lean Meta, not merely a similar printed signature;
- an atom-to-elaborated-Spec correspondence that covers every source atom;
- a full Lean closure receipt that includes every application argument,
  including proof and typeclass/instance arguments; and
- an explicit disposition for every material closure terminal: a source atom,
  an approved source correction/additional assumption, a checked Lean
  derivation, or a version-pinned foundation basis.

There is no automatic exemption for a declaration, binder, type, data value,
record, container, carrier, or function shape. A human semantic bridge remains
independent source-review work, not a self-certifying prose field. Reuse a v11
receipt only when that item's atom content, exact source-quote pins, Spec
closure, narrow closure environment, and exact theorem type are unchanged;
unrelated paper edits must not reopen it. Legacy v10 evidence stays readable but
never acquires a v11 realization credential by relabeling or cache projection.

For every direct (or approved-corrected-target) route to a source definition or
predicate vocabulary item, complete `source_definition_semantics_review`.
Compare the expanded legal domains, source outside-domain behavior versus any
Lean totalization, and the actual operational object; then separately review
every advertised property. This catches, for example, summing payments from
non-winners when the source defines sale-price revenue, treating an
unnormalized or undefined formula as a probability law, or exposing a selector
without its advertised optimality/attainment property. A total Lean function,
source-looking name, or map key is not evidence. If the source definition has
no extra advertised property, record the substantive absence basis. A full
definition endpoint must use a direct route rather than a `source_component`
route that evades this item-level gate.
When a source statement is false or needs a user-approved visible convention,
do not overwrite that archival statement or route it as `direct`. Mark its map
item `corrected_source_statement`, retain the archival text, and create a
hashed `corrected_target` that names the governing source-statement defect,
all added conventions, regularity, or domain restrictions, a pinned archival
quote, and `archival_equivalence_claimed: false`. Review Lean only against that
corrected target through `approved_corrected_target` and use only
`covered_corrected_target` coverage with archival and corrected hashes, the
approval-artifact hash, and exact governing defect ids. The review row's paper
statement must itself be the corrected target. An approved convention makes a
new explicit target eligible for proof; it never turns false archival wording
into proof credit. This comparison is semantic and source-pinned, never based
on a Lean declaration, wrapper, or function name.
A `corrected_source_statement` has exactly one complete PaperInterface
theorem/lemma endpoint in `lean_declarations`; if its target has several
clauses, state their conjunction in that one endpoint. Aliases,
`proof_lean_declarations`, support declarations, and semantic bridges are
navigation or proof support only: they must never receive corrected-target
text, source-route credit, or coverage credit. Put helper proof rows in
`support_lean_declarations`, never `proof_lean_declarations`.
The same separation applies when an archival source claim is true but the
available theorem proves it together with a stronger derived package. Do not
call that full conjunction a literal source match. Create a source-core
projection with its own transparent `Prop` Spec and direct PaperInterface
endpoint containing exactly the source-facing claim and required model bridge;
route the source map's `lean_declarations` and `semantic_contract` only to
that core endpoint. Keep the stronger theorem in
`checked_strengthening_declarations`/`support_lean_declarations`, label it as
a checked strengthening, and record its relationship to the source core with
the same byte-pinned source anchors. A source-core split is driven by the
expanded propositions and pinned source text, never by theorem or function
names. It is not a source correction and does not need a defect id merely
because the proof establishes more than the paper said.
For a full closeout, explicit v10 source routes require current schema-2
`semantic_model_review` evidence for every generated expanded-type model row.
The source-record audit and match sidecar must be current at the item level; an
open `mismatch_or_open` or `documented_partial_boundary` model dimension blocks
both full statuses, including `formalized with caveat`. Do not use a source
route pin, declaration spelling, or a current statement judgment as a surrogate
for this model comparison.
For a full-closeout paper with both `source_curated: true` in a nonempty
canonical source map and a canonical source-proof ledger, configure the current
v10 semantic/source lanes even when that ledger has zero defects: explicit
source routes in `llm_statement_review`, source-first coverage,
`llm_source_record_review`, schema-2 `semantic_model_review`, and the canonical
`source_proof_fidelity_review` pointer. An uncurated historical zero-defect
ledger may remain archival, but a curated inventory, live defect, correction,
or source route cannot be hidden behind legacy review metadata.
For a full closeout, the configured fidelity ledger must resolve to the
canonical paper-local ledger when one exists; do not substitute a cleaner
alternate file. Every nonblank `source_defect_id` in the canonical source map
must resolve to exactly recorded ledger debt. Use the configured current
source-record audit and judgment paths, require the v10
semantic-conclusion-boundary-contract prompt, and reject blank or duplicate
generated semantic-model judgment keys.
One judgment must not certify multiple expanded model rows.
The paper-coverage sidecar must use those exact routes: a theorem endpoint uses
`direct`, a scoped ordinary source component may use `source_component`, and a
`model`/`assumption` source item may use `source_model_convention`, always with
the exact source item, digest, and locator. A green row for a different source
item is not transitive coverage. The fast inventory fingerprint must include
statement text, source note, defect ids, source provenance, all
direct/proof/support route declarations, and every dependency pin such as
`model_convention_ids`. It deliberately omits ordinary top-level
`source_status` bookkeeping, but must bind a normalized effective route policy
when a selected item becomes support-only, quarantined, or crosses a legacy
phrase-route transition. Free status prose and dependency IDs never assign a
route role. Update the coverage sidecar whenever any of those semantic policy
fields changes, before spending time on a Lean manifest refresh. A
`FINAL_VALIDATION_REPORT.md` prose edit may
rebind the cached display statements cheaply; it must still invalidate affected
row-local statement judgments, but it must not force unchanged Lean declaration
manifests to be extracted again. Lean interface, source artifact, source-map,
or review-surface-selection changes remain fail-closed cache invalidators.
Every current v10 item also needs `semantic_scope_review`. Work from unfolded
definitions, not identifiers. Record whether the source and Lean conclusions
range over one fixed profile, every legal profile, an existential profile, or
a mixed scope. Inventory every result-bearing named predicate; when an iff or
membership predicate unfolds to the same advertised fact on an independently
supplied object, mark it `self_characterizing` and never use it as source
conclusion evidence. For algorithmic rows, separately classify source claim
level and Lean claim level as existence, noncomputable existence, executable,
or polynomial time. Record the source runner, Lean runner, and their outputs as
semantic worlds. Paper credit requires either the same formalized runner with a
runner-derived result, or an equality/refinement/simulation plus an exposed
result-preservation bridge in the Lean conclusion. A conjunction containing
runner success and an independent characterization is not a bridge. Polynomial
credit additionally requires an explicit complexity conclusion and the
arithmetic/input representation model.
Every row must complete the versioned `fidelity_risk_review` nested in
`semantic_scope_review`. Audit five dimensions from expanded semantics, not
declaration or function names:

- **Output shape:** compare the source result arity and component meanings with
  the actual runner output, including terminal components, `dropLast`-style
  projections, and any reconstructed trace.
- **Adversarial action space:** for every universal prefix/suffix/reordering or
  completion family, prove the legal family is nonvacuous under its carrier and
  capacity conditions and check duplicate interactions with the original
  object. A validity filter may not silently erase the advertised actions.
- **Coherent extrema:** do not combine per-candidate or per-coordinate maxima or
  minima unless one coherent admissible witness realizes the combined values.
  Bind algorithm credit to an actual-runner result or a checked
  refinement/result-preservation theorem.
- **Cardinality and fibers:** distinguish an exact syntax-family cardinality
  from the number of nonempty realized semantic fibers. Equality across those
  objects requires a definitionally evident or Lean-proved surjection.
- **Execution claim scope:** compare source and Lean input domains,
  state-transition coverage, termination conditions, numeric representation,
  and local versus end-to-end cost scope. A restricted input class, one local
  transition, partial termination argument, or local work count may not be
  promoted to an advertised global executable or polynomial claim without a
  checked global bridge. New reviews use the domain-neutral v3 execution fields;
  legacy v2 records remain valid under their recorded fields.

For each applicable dimension, cite source and elaborated-Lean obligation ids,
record the expanded source/Lean semantics and their relation, and bind a match
to an exposed Lean conclusion. Record a substantive semantic absence basis for
every inapplicable dimension. An algorithmic row must always make the execution
scope dimension applicable.
Complexity review must follow the executable's transitive semantic operational
dependency graph across every branch reachable over the claimed input domain.
Extensional equality, refinement, simulation, or result preservation establishes
correctness, not a runtime bound. For a cached or memoized executor, show that no
reachable recursive branch evaluates the old semantic closure or oracle after
materialization; function and declaration names such as `cached`, `memoized`, or
`fast` are routing only, not evidence. Charge traversal and enumeration length
(including duplicates), every materialization or rebuild,
representation/container primitives, and exact rational numerator/denominator
bit growth. Any excluded item requires withholding the corresponding full
runtime match. Require a worst-case recurrence or equivalent bound across all
reachable branches. When closure elimination is material, use a cost-threaded
executor or generated IR/C evidence pinned by source and artifact digests to the
exact audited build, with a semantic source binding; absence of a symbol name is
not evidence after renaming or inlining.
Account separately for scalar recurrence work, matching/decomposition,
source-executor evaluation, exact-arithmetic bit growth, and literal output
materialization. A construction that emits `B` ballots or other objects has an
`Omega(B)` output-size lower bound. A scan linear in numeric `B` may be only
pseudopolynomial when `B` is binary encoded. Call such a result output-sensitive
or pseudopolynomial unless the declared input encoding, evaluator cost, and all
transitive work justify a polynomial bit-complexity theorem.
Every exact `matches` judgment whose source and Lean claim levels are
`polynomial_time` must include `operational_complexity_review` with
`schema_version:
"operational-complexity-review-v1-transitive-work-accounting"`. The dashboard
must reject a missing review, incomplete reachable-branch graph, missing
worst-case recurrence or bound, unpinned material closure evidence, and any
work-accounting item marked `missing` or `excluded_by_claim`.
For assumptions,
`assumption_match_llm.json` should record
`prompt_version: "assumption-provenance-v3-semantic-exact-premise-source"`. Every exact
`-- audit-premise:` entry needs its own `premise_judgments` row with either a
source location, a Lean-derived provenance judgment, or an explicit
partial-boundary/not-source finding; a declaration-level judgment alone is not
evidence.
`formalized_note_rows` may preserve a corrected source statement, explicit
source convention, or existing visible-premise note only after the advertised
endpoint is proved. They never waive `documented_additional_assumption`,
`partial_boundary`, or `not_paper_assumption`; record those as partial work and
repair the source endpoint instead of relabeling the row.
For source-record provenance, `source_record_match_llm.json` should record
`prompt_version: "source-record-v10-semantic-conclusion-boundary-contract"`. The judge must
classify every boundary-shaped visible theorem input and every recursive field
from `source_record_audit.json`; a replay/certificate/process/bridge/source-row
input cannot be approved unless the sidecar gives specific source evidence, a
Lean constructor/derivation from primitives, an approved external boundary, or
an unresolved finding. Do not count old unversioned source-record sidecars as
current.
Treat generated review candidates as non-evidence even when their current
hashes and fields look complete. A whole sidecar or an individual item marked
`candidate_only`, `not_evidence`,
`must_not_be_written_to_repository_sidecar`, or `non_evidence_scaffold`, or
identified as a candidate/proposal artifact or validator type, must be rejected
by the loader. Do not convert it by merely deleting those markers or rewriting
its pins. Freeze the review surface, regenerate the audit, revalidate every
changed source-contract item, complete every required semantic-model judgment,
and write a new record with an accurate reviewer/validator attribution. A
single-agent review may say so, but must not claim independent certification.
A direct source-to-Lean statement match may suppress duplicate review only for
an ordinary premise. It never discharges a semantically identified
conclusion-bearing input, including a caller-supplied model/package record. A
builder that returns a fresh record of the same type does not establish that it
is the caller's record; require field-level source provenance or an explicit
equality/reconstruction bridge in the reviewed statement. When one judgment
key occurs both as an ordinary boundary and as a richer conclusion-dependency
surface, give the reviewer the richer surface once and require the current
aggregate v10 audit digest rather than reusing a boundary-only item digest.
For new papers, retain schema-2 `review_surface.semantic_model_review` from the
scaffold. Its generated `semantic_model_comparison` rows are a required second
lane over alpha-normalized expanded binders, result domains, and recursively
reached model-field types. Expand transparent local type aliases, structure
parameter domains, and records introduced only through result quantifiers;
neutral namespace, wrapper, field, or binder spelling is not a reason to omit
them. A local opaque/constant/axiom type surface requires a checked
carrier/refinement bridge before it can be treated as ordinary model data. For
each requested dimension, the sidecar must give an exact source
locator, a concrete source-vs-Lean comparison, Lean evidence, and a verdict. A
carrier whose source cardinal parameter is encoded by a transformation such as
`Fin (n + c)` must also have an explicit, proved source-to-Lean parameter
translation in the paper interface and source map; a familiar type name or a
cardinality inferred from local notation is not evidence. When a strict
conclusion needs distinct, non-endpoint, or interior carrier elements, derive
the exact cardinality threshold and witness from the source; a bare phrase such
as `n candidates` does not supply `N >= 3`. A
detected finite/ordered probability surface requires a
separate endpoint-support/cutoff check. For every formula used as a transformed
density, likelihood, kernel, or probability law, check nonnegativity,
normalization, the Jacobian/sign factor, and the entire declared parameter
domain: an algebraic scaling formula is not a law outside the domain where
those facts are proved. A detected law requires a checked bridge from source
state evolution to any iid/product law; if either model sorts, rank-labels,
relabels, or otherwise canonicalizes samples, the bridge must include the
pushforward and outcome-equivariance argument rather than only matching
marginals or invoking exchangeability informally. A detected extended rate
requires a bridge covering `WithTop`/eventually-zero/boundary cases. The
generated source-record item now makes these two recurrent checks
machine-required without looking at local names. When
`carrier_and_domain.requires_cardinality_boundary_analysis_when_detected` is
true, the judgment must contain `cardinality_boundary_analysis` with a verdict,
the source and Lean cardinal domains, the smallest/endpoint cases checked, the
strictness witness or semantic reason none is needed, and Lean boundary
evidence. When
`joint_law_and_state_evolution.requires_transformed_law_analysis_when_detected`
is true, it must contain `transformed_law_analysis` with a verdict, source and
Lean operations, the complete parameter-domain/endpoints account,
normalization/pushforward evidence, outcome-equivariance or a semantic
no-relabeling account, and a Lean semantic bridge. The absence of a transform
or strictness requirement is itself a source-vs-Lean claim that must be
explained; it cannot be inferred from a function or theorem name. When
`joint_law_and_state_evolution.requires_distribution_parameterization_analysis_when_detected`
is true, it must also contain `distribution_parameterization_analysis`: write
the literal source and Lean parameterizations separately, including each
scale/rate/precision/standard-deviation/variance convention, the valid
parameter domains, the exact parameter-translation formula, and a checked law
equality/equivalence or pushforward plus outcome-preservation scope. A bare
claim that parameters are positively reparameterized, or a matching Lean
declaration name, is not evidence that the source and Lean probability laws
are equivalent. Use `mismatch_or_open` or `documented_partial_boundary` until
that bridge is proved; do not silently absorb the factor into a theorem
statement. When a source compares two accuracies, scales, or parameters, the
same analysis must state whether both Lean laws arise from one shared,
parameter-independent base law or latent source and give a checked coupling
bridge. Two individually valid smooth laws are not a source RUM family merely
because they use the same function name or each matches one parameter value.
For a detected measure/kernel/carrier-transport surface, require a separate
`source_carrier_coherence_analysis`. It must identify the source random-
variable carrier and Lean random-variable carrier, state whether stagewise
coordinates are views of one shared draw or separately resampled clocks, and
cite a checked joint-law/coupling/disintegration bridge. It must classify the
measure honestly: a generated product, restriction, tilt, or scalar-weighted
likelihood measure is not a source-data pushforward merely because Lean proves
an equality involving it. When the source claims a rate-free residual or a
rate-indexed law, a fixed-rate Lean instance is insufficient: require one
common rate-indexed family, shared policy/data coordinates, and a checked
cross-rate bridge. These are source-vs-Lean semantic checks over expanded
measure/kernel operations, never an inference from declaration, field, or
function names.
When the source fixes unit variance or unit standard deviation, the same
analysis must additionally cite a checked source-to-Lean moment, variance, or
standard-deviation theorem for the chosen base law. A rate/scale formula or a
comment that `sqrt 2` is the unit-variance Laplace rate is not enough. If that
calibration theorem is absent, retain the item as `mismatch_or_open` even when
the score-law transport itself is correct.
If there is no cross-parameter source family, record that fact explicitly.
Schema 2
also makes every expanded probability-law (or unexpanded local
model-carrier) surface answer three separate questions with a source locator,
expanded Lean evidence, and a checked bridge: **conditioning/calibration**
must distinguish pointwise, a.e., positive-fiber, and measurable-event
semantics, including null/atomless fibers; **expectation definedness** must
state the law, integrand, measurability, integrability or extended-value
convention; and **null-cell totalization/partition scope** must distinguish
finite, countable, and arbitrary partitions, prove the relevant
measurable/disjoint/cover conditions, and expose the zero-mass denominator
branch. A finite positive-mass calculation is not an arbitrary-partition
theorem. `not_applicable` is invalid when the generated expanded surface
detects the shape; an absence claim must be a concrete source-vs-Lean semantic
comparison, not a name-based assertion. This is deliberately keyed by
elaborated type structure, not local function, field, binder, or theorem names.
For algorithmic, search, and optimization rows, the source-record audit must
also inspect expanded semantics rather than names: the literal legal action
space; whether profiles are ordered tuples, multisets, or bounded stocks; the
actual executor used to evaluate the target; the success and failure branch
scope; and the distinction between a noncomputable selector, an
executable implementation, and a complexity theorem. A name such as
`search`, `optimal`, or `source` is not evidence for any of those properties.
The audit must also compare visible proposition premises structurally with the
advertised result. A caller-supplied premise that is equivalent to, provides,
or is a logical component of advertised feasibility, cost, runtime, or
optimality is conclusion-bearing proof debt; it cannot give the same source
theorem coverage, even when the premise and theorem are renamed.
A premise `h : check input = true` remains caller-supplied proof debt when the
check unfolds to `decide` over the required theorem, route, certificate, or
other result-bearing proposition.  A separate reflection theorem makes that
debt visible but does not discharge it.  For an honest total result, define a
data selector whose `Option`/`match`/`if` is evaluated internally, then state an
unconditional theorem about the selector's actual returned value.  Expose its
success/fallback equations and nontriviality separately, and review a separate
exact semantic reflection row.  A theorem whose result type itself branches on
`if h : check input = true` is still conditional proof debt.  Credit the
reflection row only as a checker specification: a false branch or empty safe
fallback does not prove that the proposed nonfallback output is accepted, and
a noncomputable classical decision is not executable or runtime evidence.  Do
not evade this rule by rewriting the same hidden implication as a disjunction;
the statement judge must expand and classify the branch condition semantically.
Do not call an `Option` selector complete from decidability, a reflection lemma,
or `some`-soundness alone. On the advertised literal source domain, prove that
every returned value is legal and satisfies the actual source executor, and
prove that `none` excludes every feasible source witness. If completeness is
first established only for a canonical or winner-complete normal form, prove a
source-domain normal-form reduction before exporting the result; otherwise name
the narrower scope. The construction/success direction must consume only
internally evaluated finite checks, not retain the competitor whose existence
was used to prove check necessity. Prove fixed-budget completeness before
minimality, and add the least-budget scan only after fixed-budget reflection is
closed.
Unfold result-bearing predicates during this pass. Delta-expand every
`Prop`-valued theorem binder head, including definitions and abbreviations in
paper-local imported modules whose proposition result is inferred rather than
written as `: Prop`; never select aliases for expansion by their declaration,
binder, namespace, or function names. If an imported premise expands to an
intermediate proposition and a declaration in the reviewed proof's semantic
dependency closure converts it into the advertised result, classify the
premise as conclusion-bearing even when the two proposition texts are not
syntactically equal. The command-line provenance gate must also fail closed
whenever the recursive boundary audit records a semantic result relation but
omits that input from its conclusion-dependency list. Keep regression fixtures
that vary innocuous alias, binder, and bridge names so this behavior cannot
silently regress to name-based detection.

Treat source-runner state,
Lean-runner state, returned profiles, and independently characterized profiles
as different semantic worlds until a checked equality, simulation, refinement,
or preservation proposition connects them. Do not infer runner provenance from
a success conjunct. Check fixed-profile versus all-profile quantification, and
keep noncomputable existence, executable construction, and polynomial runtime
as separate obligations.
Apply the same five fidelity-risk questions during the recursive source-record
pass. Explicitly test output projection/arity, action-space inhabitedness and
duplicate validity, joint witness realizability for combined extrema,
surjectivity for syntax-family/realized-fiber equalities, and the local versus
global scope of inputs, transitions, termination, arithmetic, and runtime
evidence.
When a repair depends on an executable/runtime, initial preprocessing,
counterexample, or refinement bridge, use the opt-in source-map
`semantic_contract_schema: 1`. A claim-bearing item must identify a reviewed
transparent Prop specification and a reviewed theorem/lemma that proves the
exact specification or its exact negation. Use only `semantic_shape: plain`:
specialized runtime, preprocessing, and refinement labels are rejected until
the audit implements corresponding structural checks. Never infer a contract
from function names. Under this schema, give every source-map item an explicit
`claim_bearing` Boolean and every true item a contract. Route every `repaired_in_lean`
source-proof defect through `source_defect_ids` using the ledger's stable unique
defect id. Do not treat a starter `by sorry` theorem as its own evidence
contract.
For a named evidence-integrity diagnosis during remediation, run
`python3 scripts/audit_evidence_integrity.py --paper <paper> --include-source-obligations`
to list current `unresolved_assumed_math` source-record items under the
current audit digest. This is the handoff queue for remaining visible proof
obligations; it deliberately ignores stale historical judgments and does not
infer obligations from declaration names. It is not a routine frozen-closeout
precursor: the planner-issued strict worker runs the acceptance lane in-process.
Keep event semantics exact when auditing or repairing proof obligations:
open/strict events (`>`, `Ioi`, strict upper tails) are not interchangeable
with closed/non-strict events (`>=`, `Ici`) unless Lean proves the boundary has
zero mass or the source explicitly supplies that regularity. Do not treat a
closed-tail quantile/bracket lower bound as a strict-tail lower bound by naming
or informal similarity.
The helper expands both `abbrev` and reducible `def` type aliases, follows
imported repository records, and classifies generic carriers from their
`Type`/`Sort` binder kinds. Declaration, field, constructor, and carrier names
are routing metadata only; consistent renaming must leave the provenance
verdict unchanged.
A `source_record_match_llm.json` entry classified as
`approved_external_boundary` is not compatible with a fully `formalized` paper
endpoint unless that endpoint is explicitly outside the claimed proof surface.
It is valid evidence for a partial/conditional row only after the same boundary
appears in `status.json`, the DAG, and the final validation report. If a
source-record audit separates bare witness data from a proposition-valued
validity or replay predicate, treat the bare witness as possible source-model
data and the validity/replay/process-preservation predicate as proof debt until
it is derived from paper primitives or recorded as the intentional partial
boundary.
Remember the visibility limit of the LLM assumption lane. It sees configured
`Assumptions.lean` declarations and exact `-- audit-premise:` rows; it does not
automatically certify arbitrary structure fields, library definition bodies, or
helper theorem premises excluded from the review surface. If a source formula is
encoded inside a record field or library definition, recursively inspect that
field/body or prove a paper-local equivalence before calling the premise
derived. If a theorem premise is outside the reviewed/assumption/auxiliary
classification, treat that as an audit failure, not as a harmless helper.
Check the expanded Lean signature, not only the source text of the wrapper.
Unused proof arguments and broad row bundles can print as anonymous top-level
arrows such as `SomeRows ... -> theorem_conclusion`, with no binder name for a
regex to catch. Premise checks must classify the head of each visible anonymous
premise type and either discharge it, route it through a named
`Assumptions.lean` declaration with `-- audit-premise:` comments, or mark the
endpoint partial/conditional. Prefer exposing the smallest component source
assumptions and constructing broad row bundles internally; do not leave a
single aggregate `PublicRows`/`SourceRows` premise as the paper-facing
provenance boundary when its fields are separately reviewable.
Keep the expanded dashboard cache current before using it as display and
scheduling input during active statement review: after changing
`PaperInterface.lean` aliases or theorem signatures, run
`python3 scripts/review_dashboard.py --paper <paper-folder> --refresh-cache`.
At a frozen closeout, do not refresh it by hand; the planner schedules the
refresh only when the current item-level evidence requires it.
The expanded dashboard statement is the visible review surface for ordinary
scalar theorem conditions such as positivity, interval membership, or displayed
paper inequalities. It is not enough for certificate/source-row/external
boundary packages: those must still be constructed internally, exposed as
validated paper assumptions, or marked partial/conditional.
For analytic or algorithmic theorem boundaries, first construct the concrete
source-model record from visible paper primitives, then prove a bridge from
that record plus the theorem-shaped external axiom to the endpoint
consequences. Avoid axiomatizing the endpoint consequence package itself,
because that hides whether the paper's source semantics actually feed the
external theorem.
Do not rely on "source row" wrappers or theorem parameters to smuggle formulas
into a closed proof. A displayed formula, defining equation, threshold equation,
normalization, selection-mass identity, distribution law, recurrence, or
capacity condition counts as derived only when Lean proves it from the source
model primitives or it is listed as a source assumption and validated at premise
granularity. If such a formula is merely supplied to the theorem, the endpoint
is conditional/partial no matter how faithful the statement text looks.
This rule applies to every formula, not only admissions cutoffs or normal
integrals: signs, constants, denominators, support/domain restrictions,
normalizers, mixture equations, recurrence steps, equilibrium inequalities,
objective decompositions, and probability-law identities all need either a Lean
derivation from primitives or explicit source-assumption provenance.
When a source statement defines an outcome in two stages, audit the selector
law, the conditional outcome law, and the composed objective/expectation as
three separately source-anchored clauses. Generate this obligation from a
source-pinned semantic contract, even when the Lean endpoint has only a scalar
equality and no visible probability constructor. Acceptance requires a checked
two-stage finite-expectation bridge or a checked joint-law factorization; a
matching declaration name, PMF helper, or outer-objective equality alone is not
evidence that the conditional experiment is the source experiment.
This applies through the reusable library as well as paper-local files. A
library theorem may take an explicit certificate, witness, or formula package;
that is a good API because Lean forces callers to provide it. A paper-facing
row is closed when its expanded statement no longer exposes such a premise and
`#print axioms` on the row reports only approved standard foundations. Do not
mark a row partial merely because its proof calls internal library lemmas with
certificate-shaped names when those certificates are constructed by closed Lean
theorems. Do not bake paper-source displayed formulas into `AppliedModelingLib/`
definitions or implicit instances to make the call site look unconditional;
make source formulas explicit parameters/certificate fields or keep them in the
paper folder.
If a reusable definition itself contains a formula that came from one paper,
the library audit cannot prove the formula correct by naming convention alone.
Make the library definition paper-neutral and expose the paper-specific
identification as a caller-supplied theorem/certificate or a paper-local
derivation. This keeps transitive dependencies honest: all source-dependent
facts used by a paper-facing theorem must either appear in that theorem's
expanded premise/provenance surface or be constructed internally from proved
primitives.
After editing reusable library code, run
`python3 scripts/audit_repository.py --library-only --library-premise-audit`.
This fails source-shaped reusable API names, hidden proof-boundary section
variables, axiom/opaque placeholders, and guarded debug commands, and reports
direct certificate-boundary APIs as informational findings. The
library parser covers theorem, lemma, def, abbrev, structure, class, and
inductive declarations; do not assume a proof-boundary structure is invisible
to the audit just because it is not a theorem. If the audit flags a
source-shaped reusable name, either rename it to a paper-neutral abstraction,
make the source formula an explicit argument, or move it back to the paper
folder.
Use `--info-limit -1` when you need the complete library-boundary inventory.
CI should use `--info-limit 0` so only actionable errors/warnings appear in
logs.
When private GitHub Actions fails but `gh` cannot read logs because local
authentication is stale, reproduce the workflow commands locally before
guessing at the failure: `scripts/sync_paper_status.py --check`, the
library-premise audit, and the relevant `lake build`. Run the full repository
audit only when the failure came from the manual closeout workflow path or the
user explicitly asks for closeout validation. Treat a clean local reproduction
as the basis for a scoped CI fix, and report that remote logs were unavailable.
Keep CI fast by separating metadata/workflow churn from proof changes. A
skill-only commit should not run full Lean CI; configure workflow
`paths-ignore` for `skills/**` and commit proof-affecting changes separately.
Use GitHub Actions `concurrency` with `cancel-in-progress: true` for Lean CI so
superseded pushes on the same branch do not burn a full build. In the workflow,
run fast source-only checks such as `scripts/sync_paper_status.py --check` and
the library premise audit before `leanprover/lean-action`; that fails status or
provenance drift before the expensive Lean build starts. Keep the full
repository closeout audit behind `workflow_dispatch`, not routine push/PR CI,
unless the branch is specifically being promoted or released.
Do not block your own work by watching GitHub CI unless the next action
actually depends on the result, such as merging a PR, cutting a public release,
or diagnosing a known failure. For routine pushes, confirm that the run started
or was intentionally skipped, record the run if useful, and keep working.
Treat suffix-named structures such as `...Certificate`, `...Oracle`,
`...Window`, `...Package`, `...Process`, `...Regularity`, and `...Invariant` as
proof-boundary evidence even when they are not named `hcert`. Do not keep these
as namespace/section-level `variable`s in reusable code; pass them explicitly to
each theorem/definition that consumes them so callers cannot inherit the
premise silently. Generic data predicates such as `feasible : α → Prop` or
`move : α → α → Prop` may remain section variables when they are just model
parameters, not proof evidence.
Apply the same visible-premise rule inside the paper folder. If a paper-facing
theorem, its expanded `#check` statement, or a direct paper-local alias target
still takes a certificate, hidden hypothesis, source-row equation, or
proof-boundary premise, that premise must be derived, routed through
`Assumptions.lean`, or marked partial/conditional. If a helper constructs the
certificate internally and the final paper-facing theorem no longer takes it as
an input, the certificate is discharged; confirm that with `#print axioms`
rather than a lexical dependency scan. Do not use `axiom`, `constant`,
`opaque`, or unsafe declarations to stand in for the missing derivation unless
the user explicitly approved one named theorem-shaped external boundary axiom
and the paper is reported as conditional/axiom-boundary. Even then, do not use
an endpoint-consequence axiom when a concrete source model plus an external
theorem statement would expose more of the real proof obligation.
Do not leave those proof obligations as the default proof shape. If an
explicit certificate, row package, or extra hypothesis is introduced to unblock
a build, treat it as a temporary checkpoint: immediately name the closure lemma
that would derive it from the source model, attack that lemma before moving to
new paper results, and keep the downstream theorem partial/conditional until
the certificate is either discharged internally or promoted to a validated
paper-assumption declaration. The normal proof loop should reduce the number of
visible certificates and extra hypotheses, not accumulate them.
For a final `formalized` paper, `scripts/audit_repository.py` should not report
hidden-premise, source-row, opaque-alias, broad-aggregate, stale-LLM-sidecar, or
missing-source-provenance findings for that paper's review surface. If the
global audit reports unrelated active-paper warnings, filter to the paper under
review and make the final claim only for papers whose own warnings are clean or
explicitly classified as non-theorem packaging notes.
If a certificate/interface structure is constructed internally and the final
paper-facing theorem no longer takes it as an input, that certificate is
discharged. Do not imply additional certificates are needed; for fully
formalized papers, status comments may be empty.
If a named paper theorem is closed but a downstream corollary or application
that uses it is still conditional, split the status/DAG entries. The named
paper theorem should stay green with its actual statement; the conditional
application should get its own row or node. Do not let a harder follow-on
endpoint make the source theorem look unformalized.

In AppliedModelingLib, paper-local `papers/<Paper>/status.json` files are the source of
truth for paper status, compact `human_summary` notes, human-review row counts,
`PaperInterface.lean` metadata, review-surface slices, and artifact paths.
New unfinished paper folders should also be listed in
`papers/audit_config.json` `active_papers` while the review surface and LLM
sidecars are still being developed. `scripts/new_paper.py` does this during
intake. If a paper was created manually, add it to that list before a private
push; this prevents routine repository-wide statement/coverage checks from
forcing full dashboard sidecars before the proof surface is stable. Remove the
paper from `active_papers` only during final closeout/public-release prep, after
the paper-local statement, coverage, assumption, DAG, and validation-report
artifacts are current enough to pass the non-active audit gates.
After changing any of that metadata, run `python3 scripts/sync_paper_status.py`
at a status milestone. That command regenerates the detailed
`papers/status.json`, the compact human-facing `papers/human_status.json`,
`docs/PAPER_STATUS.md`, and the status table in `site/index.html`. Do not
hand-edit those generated status outputs. README files are human-facing prose
surfaces, not generated status surfaces by default. Humans may edit them
directly, but agents must not edit any README unless the user gives specific
README instructions. `sync_paper_status.py` only refreshes paper-folder README
entrypoints with `--sync-readmes`, which agents should use only after explicit
README instructions. The sync script defaults to tracked paper status
files so untracked draft scaffolds do not pollute generated CI-facing tables;
use `--include-untracked` only when intentionally syncing a new untracked
paper scaffold. During routine proof iteration, do not run the status sync just
because Lean LOC changed or a small proof seam was added; defer
generated table/doc refreshes until a named paper result closes, a status note
changes, a final report/handoff is prepared, or the user explicitly asks. If
docs/site/table text is wrong, fix the paper-local `status.json`
and rerun the sync script at that milestone; if README prose needs to change,
wait for explicit README instructions. If a generated table needs
display-only publication wording that differs from local provenance, use
`papers/catalog.json` `publication_overrides` and leave paper-local
`source_version` fields as the source/provenance record. Publication overrides
are display metadata only and never authorize repository export. Every
paper-local status must explicitly set `repository_visibility` to `public` or
`private_only`; release selectors fail closed on omission.
If stale paper-local documentation or status is distorting the proof plan,
causing closed work to be rediscovered, or could lead a human to stop the right
proof campaign from an obsolete status belief, update the smallest non-README
handoff/status fields immediately, and ask before editing README prose. Still
defer repository-wide generated docs/site/table refreshes until the next real
milestone unless those
generated files are the misleading decision source.
Keep `sync_paper_status.py` metadata-only and fast by default. It should not
import dashboard code, run Lean previews, refresh LLM sidecars, or perform
closeout checks unless an explicit opt-in flag such as `--dashboard-audit` is
used. CI should run `scripts/sync_paper_status.py --check` as an early source
check; if that step times out or fails before Lean, first suspect stale
generated status or an accidental slow import in the sync path, not a proof
failure.
Use `human_summary` for the short public-facing note in generated tables.
Formalized papers should usually have an empty summary; add text only for a
reader-relevant source-version, proof-route, or caveat note. Human-review counts
mean saved dashboard rows by a human reviewer over the curated source-facing
review surface: `reviewed_rows / total_rows`. Do not use raw
`PaperInterface.lean` declaration counts as human-facing dashboard totals when
proof-support endpoints can be excluded with `review_surface.include_names`,
`assumption_names`, or `auxiliary_names`. Agent source audits, validation
reports, and compile checks do not increment human review.
Website status tables should expose human review and row-local
LLM-as-judge statement translation, not paper-level source coverage. Keep
paper-level source-inventory coverage in validation reports, audit JSON, and
`docs/PAPER_STATUS.md`; do not surface it as a public website table column.
For a partial or conditional public entry, make `human_summary` one concise
sentence: name the paper-facing results already closed and the exact remaining
external/library/model certificate. Avoid Lean declaration names, helper-layer
names, route history, and process words; a reader should understand the status
from the source theorem labels and the mathematical boundary alone.
If `status.json` includes `human_summary_review.status = "human_approved"` or
`"human_written"`, preserve the summary verbatim unless a human explicitly asks
for that summary to be edited. Automation may require a nonempty summary for
non-formalized papers, but it should not rewrite human-written or
human-approved prose merely to shorten, polish, or normalize it.
When doing an all-public-paper audit or syncing public status into the paper
or website, derive the paper list from the active public checkout's tracked
paper-local `status.json` files, `papers/human_status.json`, or the sync
script output. Do not rely on a manually remembered list of "public papers";
selected public partials are easy to omit, and private/in-progress papers are
easy to leak. Run the aggregate status sync in the checkout whose outputs will
be committed, because private and public aggregate tables intentionally differ.
If the command is run from the private incubator, still derive the public-paper
audit set from the sibling public checkout. A broad private `papers/status.json`
loop is useful for incubator triage, but failures on private-only papers are
not public-release blockers unless those papers are intentionally being moved
into the public repo.
If the user asks for DAG regeneration, commit, or push at the next milestone,
treat the milestone as a green named theorem seam plus the relevant targeted
builds and hygiene checks, not as every helper alias. At that milestone, refresh
only the affected DAG/status artifacts, inspect the rendered DAG if it changed,
stage an explicit path list, commit once, and push without adding a routine
rebase unless the user asked for one or a true publication/library milestone
requires it.
Do not churn status metadata during tight proof loops. Treat status syncs as
publication/checkpoint work, not as a per-build or per-proof maintenance step.
Update paper-local `status.json` and run the sync only at coherent milestones:
new scaffold intake, a theorem/status row changing, a review-surface change, a
final report/handoff/publication pass, or an explicit user request. For
ordinary proof edits, formula wrappers, small library lemmas, and compiler-fix
iterations, rely on targeted `lake build` checks and update status once the
batch has a stable boundary. This includes mechanical metadata such as
`line_count`, `declaration_rows`, `review_rows`, `total_rows`, and review-slice
lists: do not chase those counts after each interface helper or proof wrapper.
Let them be temporarily stale during active development and reconcile them in a
single pass at the next real review, report, commit, publication, or handoff
boundary.
If stale documentation or status metadata is actively distorting the proof
plan, causing the agent to redo closed work, or likely to make a human shut down
the right proof campaign based on obsolete status beliefs, update the smallest
paper-local docs/status fields immediately. This is a proof-planning fix, not
routine documentation churn; keep it narrow and defer generated aggregate syncs
unless the changed field is the aggregate source of truth for the current
decision.
When CI fails only because generated status files, launcher scripts, or other
metadata are out of sync, treat the repair as a status-fix lane: regenerate the
owned metadata, run the cheap checks that failed (`sync_paper_status.py
--check`, launcher bootstrap checks, and similarly fast repository scripts),
then commit and push the scoped fix. Do not block that push on a full Lean
rebuild unless the touched files changed theorem code, imports, source-record
semantics, or closeout status.
Keep broader human-facing document churn low for the same reason. During an
active proof session, do not refresh READMEs, DAGs, final-validation reports,
website tables, or public status summaries for every helper lemma or small
interface wrapper. Batch those edits for real session boundaries,
publication/checkpoint milestones, explicit user requests, or roughly
once-a-day progress rollups. Short private scratch notes or paper-local
handoffs are still appropriate when they materially help the next proof step;
the constraint is on outward-facing documentation churn, not on useful working
memory.

When a proof is blocked, think outside Lean as needed, patch the mathematical
argument yourself, and then implement the patched proof in Lean. Do not stop at
identifying the gap unless the target theorem is false or the needed assumption
is mathematically indispensable.

If a paper proof is imprecise, think hard outside Lean to create a precise proof
strategy, implement that strategy in Lean, and record the issue in the live
README or handoff. Carry it into the paper's final report only during the
paper-done or user-requested post-validation pass.
If a paper's printed finite constant appears wrong or under-justified, separate
the exact finite claim from its downstream use. Prove and expose the corrected
finite bound with the constant Lean can justify; document the sharper printed
constant as a source deviation or conditional sharp bridge only if the exact
finite result is itself a named target. If later paper results only need a
vanishing/asymptotic bound such as `O(1/N)`, route them through the corrected
bound and say plainly that downstream consumers are unaffected by the finite
constant discrepancy.
Even when such a finite claim is a named theorem, lemma, appendix result, or
preliminary proposition, do not let an inessential sharp constant block the
paper's main theorem path. Prove the strongest corrected version justified by
the source and Lean, expose it under a name that signals the correction, and
document exactly how it deviates from the printed statement. Treat the printed
constant as an open sharp variant only when a downstream result genuinely
depends on that exact constant.

When the right proof strategy is unclear, think deeply outside Lean before
editing. If a written scratch argument would help, create a short `.txt`,
`.tex`, or `.md` sketch in the paper folder; keep it only as detailed as needed
to unlock the Lean proof. Do not create a sketch when it would be ceremony
rather than useful proof planning. After the strategy is clear, execute it in
Lean and keep moving.

If a proof loop has produced several wrappers, adapters, or public aliases
without shrinking the visible theorem assumptions, stop before adding another
layer. Write or update a short outside-Lean plan that names the current target
declaration, the theorem application that should close it, and classifies each
remaining visible premise as a source assumption, a derivable row/lemma, a
definitional surface mismatch, or a real semantic gap. Prefer proving the
missing row-identification lemma or choosing the right concrete source surface
over adding more wrappers. Resume Lean only after the plan names the next small
build target and why each exposed premise should be discharged, bundled, or kept.
For proof-facing certificates, "kept" is a temporary decision, not the default
end state: either prove the certificate constructor now, expose the premise as
a validated source assumption, or mark the exact source theorem partial. Do not
start a new theorem while the current theorem still has an easy-to-state
undischarged certificate or row hypothesis.
Treat wrappers as proof progress only when the final paper-facing theorem type
gets closer to the paper statement: fewer visible certificates, fewer unproved
row hypotheses, or a more faithful source surface. If an already-stronger
compiled endpoint exists under a secondary name, rewire/promote the public
paper-facing alias before adding new helper layers. Use `#check` or a temporary
scratch theorem to inspect the actual theorem type; do not infer remaining
work from long declaration names or README prose alone.
If `#check` shows that the remaining premises are exactly the paper's displayed
source assumptions, do not try to "prove" them away by inventing a stronger
model unless the paper claims that derivation. Treat them as legitimate theorem
inputs. If the remaining premises are source-model identification rows that the
paper derives in an appendix, make that row package the active proof boundary
and name it explicitly. For appendix restatements such as "Theorem N (Theorem
M)" or "Proposition N (Proposition M)", do not create a separate proof target
unless the appendix statement contains genuinely new conclusions; otherwise
map it to the main theorem/proposition endpoint and expose any extra appendix
parts as support rows only when they are paper-facing.
When a source theorem has logically independent assumption components, preserve
that separation through the proof-facing and paper-facing interfaces. Do not
reassemble a coarse older bundle merely to call an existing helper if one part
belongs to feasibility, another to a merit/objective inequality, and only the
coarse bundle makes the result look more conditional. Instead, add or use the
small adapter that consumes exactly the component needed by the current proof,
then feed the remaining source-shaped component to the theorem that actually
uses it.

When this outside-Lean diagnosis is needed, make it mathematical rather than
ceremonial. Read the local source TeX around the source theorem and proof,
write the intended paper route in a few bullets, then map every exposed Lean
premise to one of four actions: prove now, package as a source-shaped row
structure, keep as an explicit paper assumption, or mark as the real boundary.
Proceed in source order unless a later theorem discharges an earlier row
automatically; then record that dependency explicitly so the DAG and interface
do not imply the earlier result is still open.

Keep strategy notes token-cheap. A good scratch update is the active theorem
name, the exact remaining mathematical obligation, the next bridge lemma, and
the validation command. Do not copy long proof states, full diffs, or entire
README tables into handoffs when declaration names and file links identify the
same information.

When a paper proof file becomes large enough to slow focused compiles or make
multi-agent ownership awkward, split the proof into smaller paper-local modules
at stable theorem seams. Keep imports narrow, give each agent a disjoint module
or section to own, and re-export the public surface through `MainTheorems.lean`,
`ProofInterface.lean`, and, when an exhaustive helper ledger is useful, a
neutral implementation-facing proof ledger such as `ProofLedger.lean`.
Do not create new `PostPaperAudit.lean` or `AuditLedger.lean` files; those
legacy names are queued for a coordinated remediation rename because they can
be confused with the human-facing audit surface.
When the human or proof-facing interfaces start accumulating many near-duplicate
aliases, do not just move the bulk from one interface file to another. Look for
the repeated proof construction and factor it into a reusable source-layer
bridge theorem in the library or the paper's route file. Then keep
`PaperInterface.lean` DAG-shaped, keep `ProofInterface.lean` as a compact
paper-facing proof surface, and keep the proof ledger as an implementation
endpoint ledger that cites the strongest bridge instead of rebuilding the same
proof.

Subagents are always allowed for AppliedModelingLib formalization work; treat this as
standing user authorization for paper-intake, proof, audit, CI, and release
tasks, and do not pause to ask for permission before using them. Use judgment
about whether they shorten the current proof loop or improve confidence.
Medium-effort subagents are appropriate for bounded read-only scouting: find
declaration names, trace imports, locate source statements, or identify likely
reusable lemmas. Hard Lean implementation should stay local or go to a
high-effort worker with a narrow, disjoint write scope and explicit
instructions not to touch other agents' files. Do not delegate the next
blocking proof obligation if the main agent will just wait idle; do the blocker
locally and send sidecar questions in parallel. Ask subagents for exact file
paths, line anchors, declaration names, and recommended next lemmas, not broad
summaries or repeated context. Close agents once their result has been
integrated.
When parallel edits are safe, do not artificially keep subagents read-only.
Use worker subagents for bounded implementation in disjoint files or declaration
clusters, tell them they are not alone in the codebase, and give each worker an
explicit owned write set. Avoid overlapping edits to the same Lean file unless
one agent owns a clearly separated section and integration order is obvious.
Review worker patches before committing, run the relevant targeted builds, and
stage only the paths owned by the integrated work.

Do not avoid continuous, probabilistic, or measure-theoretic formalization when
the source theorem requires it. Finite analogues are useful scaffolds only when
they shorten the faithful proof. If the fastest honest route is a direct
measure/integral/renewal/CTMC statement, build that statement directly and keep
the paper-facing wrapper source-level.
When a proof pattern appears in two papers, or is clearly standard for future
EconCS papers, move the mathematical core into the library before adding more
paper-local wrappers. Common examples are selected-below-reference a.e.
contradictions, accepted-set reward add/remove algebra, two-point pooled
estimate comparisons, monotone capacity cutoffs with region characterizations,
score-induced ranking laws, and ranking-law pushforwards from continuous
random utility models. Keep theorem-numbered names in the paper file as thin
adapters over those shared declarations.
For continuous strategy/type-space games, treat strategy, equilibrium,
best-response, uniqueness, policy-optimality, and indifference-boundary claims
as almost-everywhere statements under the relevant type or information law by
default, not as pointwise statements. Use a pointwise statement only when the
paper explicitly needs pointwise behavior, the state space is genuinely
finite/discrete, or the pointwise result is a stronger helper that is
immediately bridged to the paper-facing a.e. theorem. If indifference cutoffs,
support boundaries, or off-support types are null events, state the theorem
a.e. and prove separate boundary-null/no-atoms lemmas rather than adding
artificial pointwise tie behavior. Load
`references/proof-foundations-probability.md` for measure-zero/boundary-null
routes and `references/proof-mechanism-design.md` for Gaussian strategy-game
a.e. equilibrium patterns.

For a named source-game theorem whose equilibrium or best-response comparison
ranges over feasible actions and evaluates an action through a posterior,
conditional expectation, belief, or observation-contingent payoff, audit
off-path totality before accepting the statement. The question is semantic:
for every feasible action, identify its observation branches, determine which
can have zero probability under the candidate profile, and establish either a
source-defined value on those branches, positive probability, infeasibility of
the action, or an explicit source restriction of the equilibrium domain. A
finite payoff/belief supplied only by a Lean `if`, default value, or chosen
conditional version is an additional model completion, not a harmless
measure-zero convention, when the source still compares that deviation.
Record this with the byte-pinned
`semantic_context_requirements.kind: strategic_observation_totality` contract
in the source statement map so the v10 source-record audit creates the
signature-bound `strategic_observation_totality` review dimension. Do not
select or waive the check based on a theorem, equilibrium-predicate, strategy,
posterior, field, binder, or function name. If the source leaves the off-path
value unspecified, mark the named result partial or seek an explicit source
correction; do not silently substitute a mandatory-action or on-path-only
model.

For this context's schema-3 contract, pin the conditioning population itself
(including any source subgroup, access event, or restriction), the complete
selected action/observation event, and every prior action or state-history
component that selects it. The response must separately establish measurability
and null handling for that event. If the Lean route uses an RCD or
disintegration, state its base marginal and almost-everywhere fibre scope, and
keep the paper-facing conclusion at that a.e. scope; a chosen conditional
version cannot be used as a pointwise source fact. A positive measurable-event
conditional integral is acceptable only after the selected event and its
positive mass are source-pinned and Lean-checked. When one result uses more
than one conditionalization mode, declare each mode in the contract's
duplicate-free `conditionalization_scopes` list and give distinct source-vs-Lean
evidence for every mode; do not collapse an event conditional and an a.e. RCD
into one vague conditional-value claim. These are semantic
source-to-Lean comparisons, not declaration-name checks.

When Lean exposes a contradiction or apparently false source statement, do not
immediately mark the paper theorem false. Pause the Lean loop briefly: reread
the source PDF/TeX around the exact theorem and proof paragraph, think through
the intended mathematical statement outside Lean, write a short paper-local
proof plan, and then implement the repaired route. If the source really appears
to assert the false statement, surface that issue to the human before rewriting
the theorem status; otherwise treat the correction as a faithful formalization
repair and continue. Common repairs include replacing an over-strong pointwise
claim by a law-level or almost-everywhere statement, adding a missing
nondegeneracy/support assumption, separating a displayed formula from a
derivation-corrected formula, or weakening an auxiliary abstraction while
preserving the paper-facing theorem.

When source model assumptions are ambiguous, search beyond the local PDF before
deciding whether a Lean field is a paper convention or an extra certificate.
Look for public TeX/source archives, author-hosted PDFs, conference and journal
versions, and source repositories. Record when no public TeX/source is found.
Later versions may clarify conventions such as anonymity, tie-breaking, or
masked-vector models, but do not silently switch the paper target to a later
version. If the later version becomes the source of truth, update the paper
identity, theorem inventory, numbering, DAG, README, status rows, and final
report together.

Keep theorem-specific proof tactics out of this always-loaded file. Use the
reference routing table at the end: CTMC/reward-rate details live in
`references/proof-foundations-probability.md`; dynamic-game/PBE certificate
details live in `references/proof-mechanism-design.md`; market and social
choice details live in `references/proof-markets-social-choice.md`.
Do not present a finite source-event, finite schedule, trace/replay, or
strict-realized-profile equilibrium endpoint as a full continuous
type-distribution PBE theorem. Such endpoints can be useful source-facing
partial progress, especially when they expose the named strategy, exact trace,
and outcome/payoff equality, but the full source theorem remains partial until
the continuous type law, belief consistency, global PBE semantics, and
PBE-to-local-best-response bridge are formalized or explicitly approved as a
boundary. If a continuous theorem is reduced to a local best-response
certificate, keep that certificate out of the fully formalized status unless a
Lean constructor derives it from the continuous source game.
When updating a public skill, retain the reusable method without importing
private paper or session provenance. A publicly released paper or formalization
may be cited as an example when the cited content is already public. Keep
unpublished audit findings, private declaration families, repair history, and
non-public source excerpts in the paper evidence or private wiki.

When a displayed formula conflicts with its surrounding derivation, do not
silently overwrite the paper statement. Keep the literal source formula and the
derivation-corrected formula as separate named definitions or wrappers, prove
the corrected bridge from the surrounding source equations when possible, and
record the discrepancy in the paper handoff during active work and in the final
report during post-validation. Only mark a paper-facing theorem as closed for
the exact statement Lean actually proves.

For rounding, discretization, PTAS, or finite-search proofs, track scale changes
explicitly. If the source rounds values using one baseline scale but defines a
new average, budget, or normalization after rounding, do not force an exact
normalization back to the original scale. Build a two-scale interface: one
parameter for the value grid and a separate parameter for the rounded
instance's average/window, plus the finite count-cap or boundedness lemma that
makes the search space finite. Keep any one-scale theorem as a clearly marked
staging lemma until a source-faithful two-scale bridge exists.

When starting a new paper, briefly inspect the repository's already-formalized
papers in the same EC area and ask which proof moves should become general
library tools. Do not force a detached library project before proving the paper,
but if a lemma, interface, or theorem is likely to be useful to another EC paper,
build it in `AppliedModelingLib` while formalizing the current result.
When a proof needs the "top `k`" elements of an arbitrary finite profile, prefer
building a ranking/top-prefix interface on the original domain over reindexing
the whole mechanism. Reindexing is often harder because selected argmaxes,
sampled subprofiles, or chosen witnesses may not be definitionally equivariant;
a source-shaped top-prefix family usually preserves the paper argument with
less transport machinery.

When starting a paper or beginning a serious paper audit, do an extended
outside-Lean paper sanity pass before deep Lean implementation. Read the local
source cache, inspect every named result and formula-bearing displayed claim,
and ask whether the signs, constants, normalizations, quantifiers, domains, and
proof dependencies look mathematically correct. Also ask which generalizations,
conjectures, or extensions look trivial or near-trivial once the source theorem
chain is formalized: weakened assumptions, immediate corollaries, stronger
conclusions, or natural extensions that should be revisited after the source
claims are closed. Separately think through the formal proof strategy: the main
theorem chain, likely reusable library seams, underspecified paper steps,
necessary assumptions or certificates, and fallback proof paths. Write the
target-relevant initial learnings in `FORMALIZATION_PLAN.md` under an `Initial
Outside-Lean Paper Audit` section before proving that target. This is a
source-target setup gate, not a requirement to finish broad documentation,
DAG rendering, or exploratory work first. Use
`templates/FORMALIZATION_PLAN.md` as the section/checklist template when
creating or refreshing a paper plan. The plan must explicitly contain:

- source/version inventory: official source, open/cached source, local PDF/text
  cache paths, and any source mismatch between publication versions;
- source theorem ledger: every named definition, proposition, theorem, lemma,
  corollary, algorithm, and theorem-like displayed formula that could become a
  Lean review row, with source locations when available;
- formula/dependency sanity pass: signs, constants, denominators,
  normalizations, quantifiers, domains, density-vs-mass interpretation, and
  which earlier paper objects each result depends on;
- easy generalization/conjecture/extension scan: assumptions that may be
  trivially weakened, immediate corollaries or stronger conclusions, natural
  conjectures/extensions that look trivial, nontrivial, or false, and which
  ones should wait until the source theorem chain is stable;
- shared-library reuse checkpoint: mathlib/cslib/optlib, potential upstream
  Lean sources, and AppliedModelingLib modules or declarations inspected, the API chosen,
  citation/provenance for any upstream material used or ported, and near-misses
  that explain any new reusable library definitions;
- formal target map: which source rows will be fully proved now, which rows are
  empirical or out of theorem scope, and which candidate boundaries would be
  explicit assumptions/certificates if the paper cannot be closed immediately;
- execution checklist: concrete start-to-closeout tasks for source intake,
  reusable-library work, scaffold replacement, proof closure or downgrade,
  status/DAG/report updates, audits, and unresolved source/library debt.

Use `.txt`/`.tex` only when that is genuinely more convenient for a detailed
derivation, and link or summarize it from the plan. Keep the artifact
functional rather than polished: it is a scratchpad for thinking and early risk
detection. If this pass finds a likely source bug, missing assumption, formula
ambiguity, continuous-density encoding issue, or strategy-changing issue, alert
the user early instead of silently encoding the printed formula as a source
row. Then start executing the plan in Lean. As the formal proof progresses,
edit the plan to record strategy changes, patched source gaps, discharged seams,
and remaining blockers.
For a post-validation or post-formalization audit pass, keep
`FORMALIZATION_PLAN.md` as the working scratchpad unless the user explicitly
asks to retire it. Put the durable human-facing audit in a separate paper-local
artifact such as `docs/POST_FORMALIZATION_AUDIT.md`, `SOURCE_AUDIT.md`, or
`FINAL_VALIDATION_REPORT.md`. The audit artifact should distinguish publication
venue from the exact formalized source version, list source-named results with
statuses, summarize DAG and review-surface checks, and record library
extraction outcomes plus any deferred extraction candidates.
For public-release or public-paper audit passes, add a short outside-Lean
source-reasoning report for each paper, or a single rollup with one section per
paper. That report should say what source formulas/results were sanity-checked,
which possible issues were considered, whether each issue is already caught by
Lean/status/assumption/statement audits, and which issues remain uncaught by
the existing workflow. Treat uncaught issues as workflow bugs: either add a
generic checker, add a required review-surface row, or explicitly document why
the issue cannot be mechanically checked. Also check that
`FINAL_VALIDATION_REPORT.md` whole-paper verdict lines agree with
`status.json`; stale report prose is documentation drift even when the
machine-readable status is correct.
During that initial planning pass, also identify defensible partial
formalization boundaries. For each candidate boundary, say which named results
would be fully closed, which source assumptions or analytic layers would remain
explicit, why the boundary is scientifically useful, and what later work would
turn it into a fuller formalization. Surface those options to the human user
early and ask for their thoughts before committing to a long proof route.

For long or fragile proofs, keep a theorem-specific scratch plan beside the
paper files and use it actively, not as decoration. A good plan records current
Lean endpoints, the exact mathematical gap, the next two or three bridge lemmas,
why each bridge should be true, and which assumptions are source assumptions
versus temporary certificate fields. Put domain-specific certificate patterns in
the relevant proof reference file, not here.
When a long session ends before validation, write a paper-local handoff note
before stopping. Include the files touched, the latest unvalidated theorem
families, the intended proof route, exact next validation command, and likely
fragile Lean points. Link that handoff from the private paper README/plan so a
future agent does not need chat context. Do not publish that handoff or update
the post-paper audit report/final validation report for this intermediate stop
unless the paper is done or the user explicitly requested post-validation.
After validation succeeds, immediately update the handoff/status language from
"unvalidated" to the exact command that passed. Do not leave stale caveats that
force the next agent to rerun work just to learn whether the current additions
compile.
For dynamic-game, PBE, strategy, payoff, or schedule-certificate proof details,
load `references/proof-mechanism-design.md` instead of putting theorem-specific
guidance here.

Follow the original paper's proof structure as closely as is practical. Preserve
named definitions, lemmas, propositions, and theorem numbers in Lean declaration
names, docstrings, and status rows. When deviating from the paper proof
because Lean needs a reusable intermediate lemma or a cleaner finite/discrete
interface, make the deviation explicit and keep the paper-facing wrapper close
to the original named result.

When a source proof explicitly routes a theorem through named paper lemmas or a
named proof-line corollary, prefer formalizing that named route when it is
reasonably available. Do not spend unbounded time following the exact proof line
by line if a different or more precise argument proves the same paper-facing
statement cleanly. In that case, keep the named theorem/lemma structure in the
README, DAG, audit wrappers, and declaration names where practical; state the
same theorem; and record the route change in the live README/handoff. During
the paper-done or user-requested post-validation pass, carry it into
`FINAL_VALIDATION_REPORT.md` under `Proof-Strategy Deviations`. Do not replace
a named-lemma path with a looser certificate, alternate theorem, or broad
abstraction unless the resulting paper-facing endpoint still states the source
result or the source route is false, imprecise, or genuinely inapplicable. If
an auxiliary certificate is temporarily useful, keep it as a clearly marked
staging device, then immediately pursue the constructor/elimination proof that
removes it from the paper-facing theorem. A certificate endpoint is useful
scaffolding only if the next proof steps are closing it or proving downstream
results that do not depend on it being assumed.

For stable-matching/deferred-acceptance papers, load
`references/proof-markets-social-choice.md` after the first status pass. It
contains the matching-specific assumptions, strict-preference notation checks,
DA infrastructure guidance, manipulation-rank warning, and source-repair notes.

For STV/RCV, ranked-choice voting, Thiele, or multi-member district papers,
load `references/proof-markets-social-choice.md` before building paper-local
models. Start with reusable voting semantics under
`AppliedModelingLib/SocialChoice/Voting`, then keep paper folders as source-versioned
thin wrappers and explicit empirical/simulation-boundary ledgers.
Before adding any new STV/RCV simulator, generated trace, full-election-run,
candidate-removal runner, Algorithm A/3/7 checker, or concrete algorithm type,
search the existing voting library and same-domain paper folders first. In
particular, inspect existing RCV developments and their shared declarations for
`STVTrace`, `generatedTrace`, `replaysFrom`,
`minimalGroupElimination`, `canonicalProfileGroupElimination`, and
source-run/checker APIs. Reuse or thinly wrap that machinery unless the plan
records a concrete reason it cannot express the source algorithm.

For papers with computational-complexity, hardness, approximation-hardness, or
randomized-class claims, load `references/proof-algorithms-complexity.md` after
the first status pass. It contains the workflow for separating Lean-checked
reductions and solver transfers from external machine-level class semantics.

### 1.2 Library Layering Rule: Textbook vs. Audit Trail

Think of the repository as having two distinct roles: **`AppliedModelingLib` is the textbook. The `papers/` directory is the audit trail.**

- **`AppliedModelingLib/` (The Textbook):** Put generic, abstracted EC/CS/econ results here. If a definition, algorithm, or theorem is foundational enough that a graduate student should know it, or if a second paper might build on it (e.g., Gale-Shapley, Nash equilibrium, LP duality), it belongs in the core library.
  - **Abstraction:** Code here should be highly abstracted and stripped of
    paper-specific notation. Use generic types (`α`, `β`) and follow
    `skills/lean-community-conventions/SKILL.md` for reusable API naming,
    style, and documentation.
  - **Ownership:** Main library modules own reusable primitives: allocations, valuations, mechanisms, rankings, PMFs, finite expectations, graph/path lemmas, and generic algorithm correctness patterns.

- **`papers/` (The Audit Trail):** Each paper-specific folder is a formalization artifact proving that the specific claims in a specific PDF are true.
  - **Notation Fidelity:** Translate paper-specific notation (e.g., exactly matching the paper's index variables like `u`, `j`, `t`) into the shared primitives.
  - **Paper-Facing Wrappers:** Write theorems whose signatures match the paper *exactly*. These should be thin wrappers that call the generic library theorems. (e.g., `theorem roth82_theorem_1 : ... := AppliedModelingLib.Markets.Matching.da_is_stable`).
  - **Local Ledger:** Keep the paper's specific narrative flow in `MainTheorems.lean`, `README.md`, and `docs/DependencyDAG.tex`.
  - **Upstreaming Workflow:** It is normal to build everything inside a `papers/` folder initially. Once a proof is stable, **upstream** the generalized math into `AppliedModelingLib`, leaving only the thin wrappers and paper-specific stepping stones behind.

- **Standard for Upstreaming:** To prevent "upstream bloat," use the "Second Paper" test: **Move a result to `AppliedModelingLib` if a second paper or another likely applied-modeling formalization would plausibly need it.** Foundationally reusable math (like Gale-Shapley, Nash equilibrium, LP duality, threshold mechanisms, monotone single-parameter allocation consequences, or finite-expectation/probability interfaces) passes this test; hyper-specific algebraic lemmas or messy intermediate steps used only for one paper's specific narrative should remain in that paper's folder.
- If two papers could use a lemma after renaming variables, it belongs in the generic library.
- If a proof starts with a paper-local lemma and it becomes generic, extract it before building more paper-specific code on top of it.
- It is fine, and often faster overall, to create reusable library material while proving a paper when the abstraction directly closes the active paper seam and is likely to serve the broader EC community. Avoid speculative polish, but do not avoid general infrastructure just because the current paper could be hacked locally.
- In a multi-paper extraction pass, classify each lifted declaration before
  committing: already cross-paper, future-facing generic, or paper-local wrapper
  that should remain as audit trail. Do not expect paper LOC to fall in direct
  proportion to library LOC; source-facing theorem names, status rows, and thin
  adapters should stay in `papers/` even when the proof body moved. The useful
  cleanup signal is repeated proof construction replaced by shared imports and
  one-line adapters, plus green builds for all papers that import the lifted
  API.
- After a library extraction pass, update the discoverability surface before
  calling the pass complete: the reusable module docstring, any aggregate import
  docstring, `docs/APPLIEDMODELINGLIB_DOMAIN_INDEX.md`, and the relevant roadmap or
  extraction-plan index. Update this skill when the extraction creates a new
  workflow rule or a module future agents should check first.
- During library provenance refactors, avoid ambiguous pairs where a local
  package theorem and a full-order/source-facing package constructor share the
  same Lean declaration name. Use distinct paper-neutral names for different
  abstraction levels, such as local window versus full-order window, so the
  build and downstream wrappers cannot silently call the wrong package.
- Reusable library theorems may require explicit certificates, witnesses,
  external-boundary hypotheses, or source-shaped row packages from their
  callers. This is often the right API because Lean then forces every paper
  wrapper either to construct the certificate or remain conditional. Do not ban
  such library certificates. Instead, never mark a paper theorem `formalized`
  while the paper-facing wrapper still exposes the certificate unless that
  certificate is a validated paper-source assumption. During closeout and public
  PR preparation, run
  `python3 scripts/audit_repository.py --library-only --library-premise-audit` and inspect any
  library certificate/source-boundary APIs used by completed paper wrappers.
  This audit builds a fresh in-memory declaration index each run and reports
  direct certificate/source-boundary APIs and source-shaped reusable names; it
  should not be replaced by a checked-in index. Use it with the paper-facing
  `#print axioms` audit and expanded-statement review rather than as a
  substitute for Lean's dependency information. When extracting to the library,
  use generic definitions and explicit certificate parameters; avoid
  paper-specific formula constants, implicit certificate parameters, implicit
  instances, or names that make a source formula look like a generic theorem.
  If a paper statement uses a reusable library object to stand for a
  source-defined algorithm/model/process, prove a paper-local semantic bridge
  row, include that bridge in the configured review or assumption surface, give
  it a `Source status:` comment, and list it in
  `audit/paper_statement_map.json`; never let the source inventory or coverage
  audit point at the library object by name alone.
  For standard mechanism-design facts such as VCG truthfulness, an explicit
  certificate predicate may be the reusable definition of a VCG-style
  mechanism. Do not remove that binder unless the library already provides a
  concrete mechanism plus a Lean-checked constructor for the certificate; if no
  constructor exists, keep the binder visible and classify it as a source/library
  abstraction or partial boundary according to the paper's status.
- Reusable `Assumption`/`Hypothesis` declarations are not allowed in
  `AppliedModelingLib/`; true paper assumptions live in paper-local `Assumptions.lean`.
  Shared modules should describe generic mathematical APIs, not paper/source
  provenance. When adding a standard-name wrapper such as a convexity,
  concavity, order, metric, or probability notion, add a build-checked theorem
  in `AppliedModelingLib.LibraryDefinitionAudit` showing equivalence to the mathlib or
  local canonical definition, and keep that module imported by `AppliedModelingLib.lean`.
- After a reusable-library provenance refactor or API rename, run a targeted
  validation matrix before calling it done: `rg` for stale old names, build each
  touched library module, build downstream paper libraries that import the API,
  and then build aggregate `AppliedModelingLib`. If the refactor changes a heavily used
  generic certificate API, also build at least one representative downstream
  paper that exercises dot notation and paper-local adapters for that API.
- For domain-specific proof seams, use the proof-reference routing table below
  instead of adding theorem-family details to this always-loaded workflow file.
  The relevant reference should name reusable modules and declarations that
  future proof agents should check first.
- For LP-heavy papers, prefer a paper-local equality-form, certificate, or BFS-witness interface when that is enough to follow the paper proof and close named results. Build a generic LP/simplex/duality layer only when the current theorem truly needs it or a second paper will immediately reuse it; otherwise keep the optimization boundary narrow and auditable in the paper folder.
- Keep paper-module imports as narrow as practical. Avoid importing aggregate
  roots such as `AppliedModelingLib` from paper-local proof files when a leaf module like
  `AppliedModelingLib.Foundations.Probability.FiniteExpectation` or
  `AppliedModelingLib.Foundations.Math.FiniteSigns` suffices; aggregate imports can make
  targeted paper builds depend on unrelated dirty library areas such as auctions.
  When narrowing imports, add the exact missing leaf import at the file that uses
  the declaration rather than restoring a broad root import.
- Treat a focused paper build that unexpectedly compiles unrelated library
  areas as an import-hygiene signal before debugging those unrelated files.
  Identify the declaration owner with `rg`, import that leaf module directly,
  and re-run the targeted `lake build Paper.Module`; do not broaden imports just
  to make the immediate elaboration error disappear.
- When a focused paper build fails in a shared library file that was not touched
  in the current task and other agents may be active, wait about one minute and
  rerun once before intervening. If the same shared-library failure persists,
  patch the minimal local problem yourself, rebuild, and move on; do not leave
  the paper blocked indefinitely on likely concurrent shared-library work.
- If the failure is `failed to open file ... .olean: No such file or directory`
  immediately after Lake claims the dependency was built, treat it first as
  shared build-artifact churn. Check for active `lake`/`lean` jobs with `ps`,
  let concurrent local builds finish, then materialize the missing dependency
  target directly (for example `lake build AppliedModelingLib.Foundations.Probability.BivariateGaussian`)
  before rerunning the paper target. Do not debug theorem code until the same
  paper module reaches elaboration and reports an actual Lean error.
- After adding a declaration to an imported paper module and exposing it through
  `PaperInterface.lean`, rebuild the imported module or the paper target before
  relying on `lake env lean PaperInterface.lean`; direct Lean checks can read
  the previous `.olean` and report a false unknown-identifier error for a fresh
  public alias.
- For compile-repair passes, let the first `lake build PaperName` produce the
  error queue, then patch the first coherent cluster of errors by line number.
  Do not inspect the whole theorem file. Constructor-pattern errors are often
  fixed by checking the inductive declaration and matching only explicit
  constructor parameters; field-projection errors are often fixed by projecting
  from the certificate wrapper rather than an embedded base model.
- When committing from a dirty multi-agent worktree, stage only explicit path
  lists. Use `git status --short -- path...` and `git diff --stat -- path...`
  before staging. If Git cannot create `.git/index.lock` because another agent
  is using Git or the filesystem is temporarily read-only, pause; once clear,
  retry the same scoped path list. Never use broad `git add .` in this repo.
  Do not use `git reset` to repair staging or commits in a shared worktree;
  it can move or unstage other agents' work. Do not use `git restore`,
  `git restore --staged`, checkout-based file rewinds, or any "restage the
  index" recovery workflow in a dirty shared worktree; these can silently
  disturb another agent's staged or unstaged files. If a commit accidentally
  includes extra work, prefer a follow-up corrective commit, an explicitly
  scoped new commit for the remaining owned files, or direct coordination with
  the user/other agent. If unrelated paths are already staged, commit your
  owned paths with an explicit pathspec, e.g. `git commit -m "..." -- path1
  path2`, so the unrelated staged entries remain untouched. Normal first-time
  `git add path...` of files you just edited is fine; index surgery to repair
  mistakes is not.
- For private checkpoint commits on an unfinished paper, do not refresh
  aggregate paper status, global site tables, or unrelated paper audit sidecars
  merely because one paper changed. Run
  `python3 scripts/private_paper_checkpoint.py <paper-folder> --include-path <shared-path>`
  with every shared library/script/skill file that belongs in the commit; the
  helper includes the paper folder and root paper module automatically. Then
  stage only the command's printed path list. Commit paper-local
  `status.json`, source-record sidecars, dashboard sidecars, and final-report
  notes only for the selected paper unless the user explicitly asks for a broad
  status/audit refresh or a public-release handoff.
- For an immediate unfinished-paper checkpoint, stop delegated agents at their
  next compiling owned-file boundary, then run targeted builds, a scoped
  placeholder/trust scan, `git diff --check`, and an explicit-path diff. Include
  every owned paper file and shared-library dependency required by the boundary,
  but do not stage generated README/status churn or unrelated concurrent work.
  Verify the relevant shared-library directory explicitly even when it is clean,
  so "including library changes" does not become an assumption that such changes
  exist.
- If private `main` is dirty and divergent because other agents are working,
  make an explicit-path local commit without rebasing or resetting that shared
  worktree. Fetch private `origin/main`, create an isolated detached worktree at
  the fetched tip, cherry-pick the owned commit there, run the cheap or targeted
  committed-state checks, and push `HEAD:main` without force. If the push races,
  fetch and repeat the isolated integration. Never use a blind force push or
  reshape dirty shared `main` merely to publish a checkpoint.
- Before pushing a checkpoint that adds a new paper folder or intentionally
  edits paper-local `status.json`, run the cheap CI-facing metadata checks
  without entering the full closeout loop:
  `python3 scripts/bootstrap_review_launchers.py --paper <paper> --write` if a
  launcher is missing, then `python3 scripts/sync_paper_status.py` and
  `python3 scripts/sync_paper_status.py --check`. For unfinished active papers,
  keep the paper in `papers/audit_config.json` `active_papers` so routine
  repository-wide statement/coverage checks skip it until closeout. This is
  metadata hygiene for a push, not permission to refresh DAGs, validation
  reports, broad LLM sidecars, or global audits during active proof work.
- If the user asks to "just fix status" or says not to worry about a full
  rebuild, stop after these cheap status checks and push the status repair.
  Report any long-running Lean Action as still pending if relevant, but do not
  chase it in that turn.
- Before editing a paper lane, identify which repository you are in and which
  paper set it exposes. Typical local sibling names are `EconCSLib-private`
  for the public-based private incubator and `EconCSLib-public` or
  `EconCSLib` for the public release repository. Older standalone private
  history belongs in the archive repository. Confirm with `pwd`,
  `git remote -v`, and `find papers -maxdepth 1 -type d | sort`; do not infer
  privacy from the repository title alone.
- Treat any older `EconCSLean` checkout as a legacy private working copy unless
  the user explicitly says otherwise. If it points at the same
  `EconCSLib-private` remote, do not start new work there by default; inspect it
  only to recover or migrate old dirty changes, then continue in the canonical
  `EconCSLib-private` or `EconCSLib-public` sibling. If `EconCSLean` is dirty,
  consider it a migration queue, not a backup and not an automatically synced
  source of truth.
- Route paper work by public status. If the requested paper exists only in the
  private incubator, do the work in the private repo unless the user explicitly
  asks to publish it. Do not add private paper rows, DAGs, reports, titles, or
  source material to public-facing docs without explicit approval. If the
  requested paper exists in the public repo, use the public repo as the primary
  worktree for public contributions and update only that public paper folder,
  its root module, reusable public library files, and public status/docs.
- In the private incubator, default to working and committing on private `main`;
  do not maintain private topic branches unless the user explicitly asks for one
  or there is a concrete isolation need. If a private branch already exists for
  routine paper work, merge its committed history back into private `main` at the
  next clean checkpoint instead of leaving it open. Use separate topic branches
  for public PR preparation in the public repository, not as the normal private
  workflow.
- When the user scopes a task to private only, perform no edits, generated-file
  refreshes, builds, commits, pushes, or PR work in a public sibling. Reading an
  authoritative public source may be used only when needed for provenance; it
  does not authorize changing the public checkout. Keep all task artifacts and
  Git operations in private `main` unless the user explicitly changes scope.
- Work in private `main` unless the user explicitly requests another branch.
  Update it with `git pull --ff-only origin main`; do not rewrite or force-push
  private history merely to align it with public. Fetch public refs for
  comparison, then incorporate a needed public change through an explicit,
  reviewed private sync commit. Public PR preparation always starts in a
  separate clean public clone from public `origin/main`; it never pushes,
  merges, filters, or cherry-picks private `HEAD`.
- When a paper exists in both private and public, choose one primary worktree
  for the current task and keep all builds, dashboard refreshes, reports, DAGs,
  and commits in that same repo. Use the public repo as primary for public
  partials, external-contribution work, and pull-request preparation. Use the
  private repo as primary for unpublished papers, private planning, or work
  that may expose not-yet-approved paper content. Mirror between repos only as
  an explicit, path-scoped sync step; never assume that editing one sibling
  automatically updates the other.
- For a brand-new paper, default to the private incubator unless the user says
  the paper should be public from the start. Starting privately preserves
  exploratory history, failed proof plans, local source caches, and unfinished
  assumptions without exposing them. If the paper is a classic/public benchmark
  or an already-approved public contribution, it may start directly in the
  public repo. In either case, create the standard paper folder and root module
  in that primary repo, keep reusable paper-independent lemmas in `AppliedModelingLib/`,
  and only move the paper to the public repo after its status is either
  `formalized`/`formalized with caveat` or an explicitly approved
  `partially formalized` public seam.
- When a filtered public repository sibling is being maintained, mirror
  public-safe formalization artifacts and skill updates there in the same
  checkpoint: README/status rows, concise final reports, DAG sources/rendered
  DAGs when tracked, review-slice configuration, scripts needed by the public
  review workflow, and the detailed public skill bundle. Keep private incubator
  folders, unpublished paper attempts, and private planning surfaces out of
  public diagrams and public-facing status text.
- When publishing work that was developed in the private incubator, do not raw
  merge, cherry-pick, or push the private branch into the public repository.
  Create a `release/` branch in a separate clean public clone from current
  public `origin/main`, then apply only an allowlisted patch from private. Every
  allowlist entry must name one exact file; directory entries are forbidden.
  Enumerate shared-library files, already-public paper files, public
  workflow/skill/template files, and generated public status/site files. In the
  private repo, commit only the public-paper/workflow/skill paths requested by
  the user; leave
  unpublished paper folders and their generated/private status deltas out of
  that commit. In the public repo, regenerate aggregate status files from the
  public checkout instead of copying private aggregate tables wholesale. Use a
  binary/full-index patch for PDFs, for example
  `git diff --binary --full-index public/main..origin/main -- <allowlisted paths>
  --output=/tmp/public-filter.patch`, then `git apply` it in the public
  checkout. Do not include source-paper PDFs, extracted source-paper text
  caches, or unpacked source archives in a public-PR allowlist, even when the
  paper folder itself is approved for public partial release; reports should
  cite the source URL and describe local ignored caches instead. Before
  committing, inspect `git diff --name-only main..HEAD` and reject the branch if
  any private paper folder, private-only plan, source cache, scaffold row, or
  unpublished status entry appears. A human reviewer must then create the
  guard's fixed external approval artifact, pinning the candidate and public
  base commits, allowlist and guard SHA256 values, and private source commits.
  Run the canonical private `scripts/public_release_candidate_guard.py` with
  only the public candidate and approval-pinned allowlist arguments; copied
  blobs must byte-match their allowlisted paths at private commits reachable
  from private `origin/main`, while deletions and destination-generated
  aggregates use explicit non-copy provenance. The guard fixes both remotes and
  refs and rejects repositories that share Git storage.
- Public-release leakage checks must be path-sensitive. Grep the changed public
  surface for private paper identifiers, private paper titles, and new scaffold
  IDs. Existing historical mentions outside the changed path set do not justify
  new leakage. Regenerate public status from paper-local
  `status.json`, run `python3 scripts/sync_paper_status.py --check`,
  `python3 scripts/audit_repository.py`, placeholder scans on changed Lean
  paper folders, and the relevant `lake build` targets before pushing. When the
  filtered branch is approved, fast-forward public `main` to that audited
  commit rather than redoing the merge from private.
  If public or private CI fails in the status aggregate step before Lean, treat
  it as a generated-status consistency failure: rerun
  `scripts/sync_paper_status.py --check` in the exact checkout whose CI failed,
  regenerate status there if needed, commit the generated outputs from that
  checkout, and push. Do not copy aggregate tables across the private/public
  split or infer a theorem/proof failure from a pre-Lean status check.
- Public promotion audits should run both statement and assumption validation
  for every public paper row, including intentionally public partial papers.
  Conditional-boundary rows are acceptable only when the same boundary is named
  in the paper-local `status.json`, statement/assumption sidecars, README or
  validation report, and DAG if the row appears there. Do not "fix" an
  intentional conditional result by weakening the table text to look fully
  formalized, and do not treat a public partial as invisible just because it is
  not a finished paper.
- Before moving work from a private incubator into the public repository, run a
  release-hygiene pass. Public commits should not contain source-paper PDFs,
  extracted source-paper `.txt` caches, unpacked publisher/arXiv source
  archives, ignored dashboard caches, or private/in-progress paper rows unless
  the project intentionally publishes that partial formalization. Planning,
  proof-plan, handoff, audit, and citation-provenance `.txt` notes are fine to
  track when they are written by the project and do not reproduce the source
  paper text. Use `git ls-files 'papers/*/*.txt'` and `git check-ignore -v`
  before public commits if the distinction is unclear.
- Public partials are acceptable when their remaining seams are valuable and
  explicit. Do not hide partiality by publishing an all-green DAG, an empty
  caveat column, or a final report that only says the code compiles.
- After any broad library-extraction or paper-thinning pass, run a preservation
  audit before declaring the pass done. Compare the current private repo against
  the archive or the pre-extraction ref used for recovery. Check that no
  archived paper folder disappeared, no archived `.lean` file disappeared, and
  any large paper-local LOC drop is explained by wrappers moving to
  `ProofInterface.lean` or reusable library modules, not by deleting proof
  declarations. If `PaperInterface.lean` was thinned, every removed archive
  declaration name must either still be declared elsewhere in current Lean code
  or point to an underlying target declaration that still exists. If a removed
  interface alias cannot be resolved this way, treat it as proof-surface loss
  and restore or deliberately replace it before committing.
- Preservation audits must compile the actual private paper targets, not only
  the default public aggregate. Explicitly build every private/in-progress
  paper target and any new scaffolds when they are part of the pass. Strip
  comments before scanning for actual `sorry`, `admit`,
  `axiom`, or `unsafe` tokens; do not count ordinary arithmetic `by omega` or
  prose comments as proof gaps. Push private and public remotes only after both
  the content-preservation check and the relevant builds/audits pass.
- Before inviting broad public contributions, keep the public repo's legal and
  contribution surface explicit: code is released under the chosen repository
  license, currently Apache-2.0, while cached source PDFs/text extractions may
  be omitted or treated separately for source-publication licensing reasons.
  Maintain issue templates for new paper formalizations, statement mismatches,
  external certificate boundaries, library-upstreaming candidates, and dashboard
  review requests.

### 1.2.1 Paper Link Intake Protocol

When the user provides only a paper link and asks for autonomous
formalization, execute the standard intake before deep proof work:

- Download/cache the exact source PDF locally in a new or existing
  `papers/[AuthorInitials][2DigitYear][Descriptor]/` folder, then create an
  adjacent source-text extraction with `pdftotext` for search. Treat the PDF,
  extracted source text, and unpacked TeX/source archive as local reference
  caches: useful for proof work, but not public repository artifacts unless
  redistribution rights have been checked. In public checkouts, source-text
  caches should be ignored; do not commit them just because `pdftotext` made
  proof search easier. Record `source_artifact_path` and the verified byte
  digest for semantic audit, but remember that ignored bytes are a local
  attestation: fresh CI is not source-certified unless a secured job provisions
  or reproducibly fetches the exact artifact and verifies the digest. Never pass
  the evidence gate from an URL or recorded hash alone.
- Download the published-version BibTeX into `citation.bib` during intake.
  Prefer the official published-source citation export, such as a publisher,
  conference, OpenReview, or journal site. Do not use arXiv BibTeX when a
  published version exists. If the official export is unavailable, use Google
  Scholar. If Scholar is blocked or unavailable, use OpenAlex as a backup to
  locate the exact published record, then use a real BibTeX export/translator
  for that record; OpenAlex JSON alone is not a BibTeX source. Do not
  hand-write or repair BibTeX metadata. Record provenance in
  `citation_source.txt`.
- If the paper link is arXiv, also download/cache the arXiv source archive
  (`e-print`) during intake and unpack it beside the PDF/text cache. Prefer
  the TeX source for theorem statements, displayed equations, notation, labels,
  and appendix references; use PDF extraction mainly for quick search and for
  confirming page context.
- If the local PDF/text cache already exists in the paper folder, use those
  local files. If an arXiv source cache exists, use it too. Do not search the
  web again, re-download the paper, or re-run extraction unless the cached
  source version is missing, corrupted, or known to be the wrong version. If a
  public filtered checkout omits the cache, recreate it locally from the
  recorded source URL and keep the generated cache out of Git.
- When `pdftotext` output is garbled for formulas, stop trying to reconstruct
  the formula from layout text. Read the cached TeX source directly and cite
  the source line/macro in the paper-facing comment or plan note when it
  changes the Lean statement.
- Read the abstract, introduction, model section, and theorem statements first;
  then search the cached text for every named `Definition`, `Lemma`,
  `Proposition`, `Theorem`, `Corollary`, and appendix result.
- Before deep proof work, build a source-block map: one row per paper-facing
  definition, displayed formula, named result, and proof-critical appendix
  claim, with source location, dependencies, intended Lean declaration, status,
  and likely library APIs. Use this map to drive the DAG, paper-facing skeleton,
  and review dashboard. Keep public theorem signatures stable once proof work
  begins; if translation is wrong, repair the statement early rather than
  letting proof search drift the target.
- Create the paper folder contract artifacts immediately: local `.gitignore`,
  `status.json`, `MainTheorems.lean`, `PaperInterface.lean`,
  `docs/DependencyDAG.tex`, and the private `FORMALIZATION_PLAN.md` scratchpad.
  Public paper folders should not track paper-local README/planning/handoff
  markdown unless the user explicitly asks for it.
- Draft paper-facing theorem signatures before building a helper tower. If the
  direct statement is too hard, create an explicit bridge theorem whose name and
  assumptions describe the remaining gap.
- Run a retrieval-grounding pass before inventing a new model or helper API:
  search Mathlib, Cslib, Optlib when present, and existing `AppliedModelingLib/` modules
  for the source concept and proof role. Prefer existing formal concepts; if a
  paper-local encoding is necessary, add a small equivalence or sanity theorem
  before using it downstream.
- During intake, classify reusable primitives by library area. Upstream only
  seams that pass the second-paper test, such as finite PMF/Markov kernels/MDPs,
  probability inequalities, monotonicity/comparison lemmas, allocation
  primitives, or mechanism interfaces.
- Keep a live private status table or plan from the first scaffold onward. The
  public source of truth is `status.json`; each row must distinguish
  source-faithful wrappers, auxiliary analogues, conditional wrappers, and
  unstarted paper results.

### 1.2.2 Draft Paper Intake and Drift Protocol

Use this protocol when the source paper is still being written or the user says
new drafts may arrive while formalization is in progress.

- Mark the paper-local `status.json` as `paper draft`, not `scaffold`,
  `partially formalized`, or `formalized`. This status is private/incubator
  language for a moving source, not a public completion claim. Keep it out of
  public-facing tables unless the user explicitly wants to expose draft work.
- Record a `draft_policy` object in `status.json` with the current source file,
  text cache, date or version label, PDF/text/source digests, and a required
  new-draft remapping checklist. The digest is part of the source contract:
  if it changes, old source-match and coverage judgments do not automatically
  apply.
- For Overleaf-backed drafts, clone or fetch the Overleaf repository only when
  the user instructs you to do so, then treat the cached checkout as source
  material. Record the local clone path, remote URL, commit, commit date, and
  authoritative TeX entrypoint in `status.json` and `DRAFT_VERSION_MAP.md`;
  list non-authoritative entrypoints separately so future agents do not prove
  against the wrong version. By default, do not edit manuscript, bibliography,
  figure, style, or source files in the Overleaf checkout and do not push to
  Overleaf. If the user wants draft feedback, create or update only a separate
  suggested-edits file whose filename includes `codex`, for example
  `codex-suggested-edits.tex`; do this unless the user explicitly authorizes
  another Overleaf edit.
- Treat a `codex` suggested-edits file as a coauthor-facing repair document,
  not an audit log. It should start with how to use the file and an executive
  repair order, then proceed issue by issue. Include a short color key near the
  top if red markup is used, for example that red text marks suggested
  manuscript changes or replacement formula fragments. Do not include
  Codex-facing workflow boilerplate such as "Codex should only edit this file";
  keep operational constraints in the skill, status files, or handoff notes.
  For each issue, state an explicit `Paper location` line with the current
  section/subsection/appendix location, classify whether it is a theorem repair,
  appendix proof alignment, notation/convention mismatch, formula typo, prose
  overstatement, simulation scope label, or source/build cleanup, explain why
  the issue matters, and give the narrow manuscript edit to make. Provide
  actual drop-in replacement text where possible; merge replacement text into
  the issue-by-issue workflow rather than duplicating it in a later section.
- Before finalizing or refreshing a `codex` suggested-edits file, build a
  complete source-issue reconciliation ledger. Inventory every current issue
  source available in the paper folder: main/broader/source-issue memos,
  caveat-summary TeX, final validation report "Paper Issues" and "Other Source
  Notes" sections, `DRAFT_VERSION_MAP.md`, `docs/AGENT_SOURCE_AUDIT.md`,
  `status.json` caveat fields, and Lean review/audit rows whose names or
  comments mention caveat, source discrepancy, printed formula, corrected
  formula, typo, source repair, or external assumption. Verify each item
  against the current source cache. For every item, record exactly one status:
  `included` with the suggested-edits section, `omitted_by_user` with the
  user's explicit instruction, `resolved_in_current_source`, `stale_or_not_current`,
  or `not_coauthor_facing` with a reason. Do not finish the suggested-edits pass
  until every current issue is either included or explicitly omitted by the
  user.
- Treat smaller proof-text typos, appendix-only repairs, prose qualifications,
  figure/simulation scope labels, and issues that do not block Lean compilation
  as eligible suggested-edits items. Do not omit an issue merely because it is
  outside the compact theorem DAG, not a headline caveat, or already handled by
  a corrected Lean endpoint. Conversely, if the user says to remove or ignore an
  item, preserve that instruction in the reconciliation ledger so regeneration
  does not reintroduce it.
- In suggested-edits files, make the changed words and formula fragments visually
  obvious. Use red macros such as `\red{...}` or `\mred{...}` for the exact
  inserted or corrected material, while leaving unchanged context uncolored.
  This is especially useful when a replacement paragraph mostly preserves the
  original wording. If a user says an item is not actually a main-text problem,
  remove or downgrade that issue rather than preserving the old audit framing.
  If the user asks to remove a finding, remove that finding only; do not
  silently remove a distinct source issue with similar terminology unless the
  current source check shows it is stale too.
- For tiny edits, avoid full-phrase replacements that look identical to the
  source except for one repeated word, sign, or subscript. Write the edit as an
  explicit action such as "delete the second occurrence of `model`" or "replace
  the plus sign by a minus sign", then show only the corrected fragment in red.
  The goal is that a coauthor can see the delta without doing a character-level
  diff.
- Separate main-text correctness from appendix/proof-text repair. If the main
  theorem statement is correct under a global paper assumption but an appendix
  proof derives the wrong direction, frame the suggestion as appendix proof
  alignment, not as a main-text theorem flaw. Conversely, if a displayed formula
  or theorem statement is wrong, name that directly and give the corrected
  formula. Do not recommend repeated downstream edits when the intended repair
  is one upstream definition or notation change.
- For threshold characterizations over a feasible interval, do not force an
  interior or endpoint range such as `(0,1]` unless the source proof establishes
  the needed endpoint signs. A source-faithful repair can be to weaken the
  threshold to a real number: thresholds above the feasible interval mean the
  comparison always holds on the interval, and thresholds at or below the lower
  endpoint mean it never holds. Prefer that weakening over inventing a new
  endpoint assumption when it preserves the paper's intended iff statement.
- Smaller source-edit suggestions still need context. Do not leave them as a
  bare punch list. For each small edit, explain the source-local location, the
  failure mode it prevents for a reader or formalization, whether it changes the
  model or only the display/prose, and the quick consistency check after the
  edit. Mark these as local cleanup rather than formalization blockers unless
  they change a paper-facing theorem or proof dependency.
- Before refreshing a suggested-edits note from an older audit, re-check the
  current draft source. Remove stale findings that are no longer present, such
  as old abstract planning text or previously missing bibliography keys, rather
  than preserving them for history. Include source/build hygiene items only when
  they are still current and coauthor-facing; do not mix private agent workflow
  reminders into the suggested-edits document.
- Do not include meta provenance notes in the coauthor-facing suggested-edits
  document, such as "Current-source note", "these notes were refreshed against
  the current source", "older issue memo", or "the old invalid proof step is
  already commented out". Put that audit history in the reconciliation ledger,
  `DRAFT_VERSION_MAP.md`, `docs/AGENT_SOURCE_AUDIT.md`, or handoff notes. The
  suggested-edits file should state the current substantive conclusion and the
  actionable manuscript change.
- Standalone suggested-edits documents should avoid fragile internal
  cross-references. Prefer prose such as "the smaller source edits section
  below" over `Section~\ref{...}`. If internal labels are truly needed, compile
  in a clean output directory and verify there are no unresolved references, but
  do not rely on stale Overleaf/local auxiliary files.
- Build suggested-edits PDFs outside the Overleaf checkout, for example with
  `latexmk -outdir=/tmp/...`, and copy back only the `.tex` file unless the user
  asks for compiled artifacts. If auxiliary files are accidentally generated in
  the Overleaf checkout, remove only those generated artifacts. Do not commit or
  push the Overleaf repository unless the user explicitly requests that target.
- Keep cached draft PDFs, extracted text, and source archives ignored/local
  unless redistribution rights are explicit. Track source-safe artifacts such as
  `citation_source.txt`, `DRAFT_VERSION_MAP.md`, `FORMALIZATION_PLAN.md`,
  `audit/paper_statement_map.json`, and `docs/AGENT_SOURCE_AUDIT.md`.
- Build the first `audit/paper_statement_map.json` from the draft source itself,
  using stable source-item IDs that do not depend only on theorem numbering.
  Numbered aliases are useful, but the stable key should survive renumbering.
- Create `DRAFT_VERSION_MAP.md` at intake. On each new draft, map every old
  source item to the new source as one of `unchanged`, `renumbered`,
  `reworded_same_math`, `statement_changed`, `deleted`, or `new`. Do this
  before continuing proof work.
- For each existing Lean-facing row, record whether it still targets the current
  draft statement. If the source item is `statement_changed`, `deleted`, or
  `uncertain`, mark the Lean row stale and rerun statement-match and
  source-coverage audits after repairing the row. Do not assume that an old
  proof remains source-faithful because the Lean file still compiles.
- In living drafts, a holistic agent audit should usually say `DRAFT INTAKE` or
  `DRAFT DRIFT REVIEW`, not `PASS`, until the Lean review surface has been
  compared against the current draft. The audit must still be source-first and
  should flag source typos, ambiguous notation, missing constants, external
  theorem boundaries, and proof targets that are likely to shift.
- If a draft theorem has an obvious typo or mathematical convention mismatch,
  record it as a draft issue in the source map and plan before formalizing. Do
  not silently prove the corrected statement under the original theorem label;
  either wait for the draft to change or make the correction explicit in the
  paper-facing row and audit.
- Do not run full closeout or public-promotion checks for a `paper draft`
  folder. Run targeted builds and source-map checks while proving, and reserve
  final validation, human dashboard review, and public PR preparation for the
  point when the user says the draft version should be treated as stable.

### 1.3 Paper Folder Contract

Each paper-specific folder should be auditable by a human who wants to compare
the Lean statements against the paper.

- **Required Template Structure:** Every public paper folder must keep the root
  focused on Lean/status files and put human/audit artifacts in subfolders:
  1. A `status.json` file holding the paper status and dashboard metadata.
  2. A `docs/DependencyDAG.tex` proof roadmap and rendered
     `docs/DependencyDAG.pdf`.
  3. Final adversarial audit documents selected by the recorded contract:
     historical schemas use `docs/AGENT_SOURCE_AUDIT.md`; policy-aware
     closeouts also use `docs/FINAL_ADVERSARIAL_REVIEW_PANEL.json` and distinct
     paper-local audit documents for any additional required reviewers.
  4. A `FINAL_VALIDATION_REPORT.md` when the paper has a final validation
     claim.
  5. `audit/*.json` for tracked LLM/source-audit sidecars.
  6. A `MainTheorems.lean` file holding the paper-facing wrappers.
  7. A `PaperInterface.lean` file holding the compact human-facing definitions
     and named theorem statements.
  8. A local `.gitignore` file.
- **Local Gitignores:** Every paper folder *must* contain its own `.gitignore`
  that ignores local source PDFs and LaTeX auxiliaries such as `*.aux`, `*.log`,
  `*.fls`, `*.fdb_latexmk`, and `*.synctex.gz`, but it must not hide the rendered
  dependency DAG. If the folder uses a broad `*.pdf` ignore for source PDFs, add
  an explicit `!docs/DependencyDAG.pdf` exception. The overall repo `.gitignore` may
  contain generic LaTeX auxiliary patterns and source-cache patterns with
  explicit exceptions for project-written planning/audit/handoff/citation notes.
  Do not add a blanket paper-local `*.txt` ignore if it would hide useful
  planning documents.
- **Reproducible PDF/text/source cache:** A copy of the source PDF must be
  downloaded once and kept in the local paper folder so humans and agents can
  read exactly what is being reproduced. Immediately run
  `pdftotext Source.pdf Source.txt` or an equivalent paper-named extraction in
  the same folder and use that cached text file for named-statement searches.
  For arXiv papers, also cache and unpack the TeX source archive once; use it as
  the authoritative source for formulas when PDF extraction is ambiguous or
  garbled. These PDF, extracted-text, and source-archive caches are working
  artifacts, not public repository content by default. Keep them local/ignored
  in public checkouts unless redistribution rights have been checked.
  Project-written `.txt` planning notes, handoffs, and audit notes are private
  by default. Public paper folders should track only source-safe citation notes,
  final reports, DAG/proof artifacts, Lean files, `status.json`, and audit JSON
  sidecars unless the user explicitly asks for another progress artifact. Work
  from local caches when they exist; do not repeatedly search the web or re-run
  extraction unless the source PDF or source archive changes.
- Public filtered checkouts may omit ignored source PDFs, extracted text caches,
  and unpacked source archives. During final validation, do not claim a local
  PDF/text/source cache exists unless it is actually in the checkout; state the
  public source URL and any local ignored cache used for the audit, and treat
  repository-audit missing-source-cache warnings as public-release packaging
  notes rather than theorem gaps.
- **Private README/Plan Requirements:** If a private paper `README.md` or
  `FORMALIZATION_PLAN.md` exists, it must clearly identify the exact source
  version of the paper (for example arXiv version `vX` or conference year) and
  provide URLs. Public-facing source/version information belongs in
  `status.json` and `FINAL_VALIDATION_REPORT.md`.
- **DAG Node Wording:** `docs/DependencyDAG.tex` is a proof roadmap for humans, not
  a formalization changelog. Once a node is marked formalized, its text should
  state or briefly summarize the paper claim. Do not fill green nodes with
  implementation notes such as helper families, algebra rewrites, or "closed"
    status language; keep those details in private status/proof notes or the
    final report. Partial/conditional nodes may mention the missing proof
  obligation, but should still foreground the paper statement. During a pause
  or handoff pass, audit the DAG for this specifically: if a node reads like a
  session log, rewrite it before rendering.
  Visual DAG nodes must be paper-facing, not Lean-code-facing: do not put Lean
  declaration/function/theorem names, record names, helper identifiers,
  wildcard declaration families, or `\texttt{...}` code labels in DAG node
  text. A node should say "Theorem 1 likelihood decomposition" or "compact
  process/stopping certificate", not a Lean identifier such as
  `theorem1_...`, `Theorem2PrimitiveSourceModel`, or
  `HomogeneousPoisson...`. Put Lean names in README/status/final-report audit
  rows, not in the visual DAG.
  Compatibility routes, older sufficient endpoints, alternate proof attempts,
  and implementation-only wrappers are not DAG node content once the
  paper-facing result is represented. Record them in the README or final
  validation report if they matter for auditability.
- Add one central Lean file for paper-facing theorem statements, conventionally
  named `MainTheorems.lean`, `PaperTheorems.lean`, or the existing paper root if
  the folder already has a root module. This file should state and prove only
  the main theorem wrappers and import the detailed proof files.
- Main theorem definitions/functions in that central file should mirror the
  paper statement closely enough that a human can inspect just this file and
  verify the intended theorem was formalized. Use paper theorem numbers/names in
  docstrings and keep wrappers thin.
- If `MainTheorems.lean` is becoming a large implementation file, add narrow
  proof-route files instead of appending more proof bodies there. A route file
  should own one stable declaration cluster or named proof path and be imported
  by the central theorem file. Splitting is allowed and often desirable when it
  will reduce repeated proof-loop rebuilds, localize expensive imports, or give
  concurrent agents disjoint ownership. Avoid risky mass moves just to split a
  file; move a cluster only after its imports and targeted build are already
  stable, and keep `MainTheorems.lean` as the re-exported paper ledger.
- Any proof-facing interface or route file is an implementation bridge. Keep it
  thin and source-shaped, and keep `PaperInterface.lean` as the human review
  surface.
- Every paper folder has exactly one canonical human-review Lean surface:
  `PaperInterface.lean`. Do not introduce filename variants such as
  `HumanReview.lean`, `ReviewInterface.lean`, or paper-specific alternatives.
  If an older `PaperInterface.lean` has grown into a broad proof/API surface,
  rename that broad file to an implementation-facing name such as
  `ProofInterface.lean`, update imports, and replace `PaperInterface.lean` with
  a compact review surface.
- `PaperInterface.lean` is the file consumed by the human review dashboard. It
  should be declaration-ordered by paper section and should expose only the
  paper-facing definitions, formatted paper objects, and named theorem
  statements (with assumptions and short paper-context comments). It should not
  contain helper families, proof-seam checks, algebraic plumbing, or endpoint
  changelogs; put those in `MainTheorems.lean`, `ProofInterface.lean`, or
  a neutral proof-ledger file such as `ProofLedger.lean`.
- Prefer source-shaped final models over proof-adapter structures in
  `PaperInterface.lean`, then audit broad paper-module exports so old adapters
  do not reappear as public endpoints.
- Keep the interface row count close to the paper's named definitions and
  results. Do not expose every theorem-route variant, support wrapper,
  diagnostic, certificate, or PMF/law specialization as its own dashboard row.
  If a proof pass makes `PaperInterface.lean` grow far beyond the source's
  named result list, trim it before refreshing the dashboard or calling the
  paper ready for review.
  As a concrete dashboard rule, more than 30 rows requires a no-paper-context
  LLM review-surface audit saved as `review_surface_llm.json`, checking whether
  every row is genuinely paper-facing and should be present. At 120 or more rows,
  the dashboard should warn even if an audit exists; treat that as a prompt to
  curate `PaperInterface.lean` or `status.json` `review_surface.include_names`
  before broad human review.
  Do not overcorrect by shrinking a substantial completed paper to only a few
  formula rows. A final review surface should cover all main source theorem
  blocks, key displayed formulas, named algorithms/conditions, and named
  appendix pieces that support the paper claim. LLM-as-judge legibility and source coverage are
  more important than a small row count: adding rows is correct when it makes a
  source-visible claim explicit enough for semantic checking. If a large paper
  naturally needs many source-facing rows, keep them and improve slices,
  source statements, and row grouping instead of hiding paper content.
  A dashboard with hundreds of rows is a warning that implementation endpoints
  may have leaked into the human interface, not a reason to delete
  source-visible content. Curate the source-facing definitions/results in the
  paper-local `status.json` `review_surface`, and move broad proof aliases to
  `ProofInterface.lean`; use slices to keep a large but legitimate review
  surface navigable.
  Final reports should cite the post-filter human-review row count and describe
  how the source inventory is covered. If the count is still in the hundreds,
  audit whether rows are source-facing; keep them when they are needed for
  complete source coverage.
- Before asking for dashboard review, run a statement-surface audit: every
  dashboard row should be a paper-facing definition, formula, or named source
  statement; the total should be close to the paper's named result inventory.
  If there are more than 30 rows, perform the independent LLM surface audit and
  save the verdict, row count, and dashboard digest in `review_surface_llm.json`.
  Include validator provenance in that sidecar: `validator`, `validator_type`,
  `validated_at`, and `comment`, using the same conventions as
  `statement_match_llm.json`.
  If there are many extra rows or the LLM says `needs_curation`, first trim
  `PaperInterface.lean`, then narrow `status.json` `review_surface.include_names`;
  do not use slices to legitimize a bloated human review file.
- Do not confuse row-local validation with paper-level coverage. A clean
  `statement_match_llm.json` only says that existing dashboard rows match their
  supplied source statements; it does not say that every paper statement is
  represented. Maintain an explicit `audit/paper_statement_map.json` inventory of the
  source paper's definitions, displayed/source-defining formulas, theorem
  blocks, named subclaims, and appendix results that are intended formalization
  targets. Then populate `paper_coverage_llm.json` with an independent
  source-to-row judgment: each inventory item should be `covered` by one or more
  dashboard row names, `conditional_boundary` when the row-level statement judge
  records an explicit boundary assumption, `covered_by_support` when a named
  source proof-route lemma is formalized in support declarations but omitted
  from the compact dashboard, `partially_covered`, `missing`, or explicitly
  `out_of_scope`/`not_a_paper_target` with a reason. Before rebuilding an
  expensive Lean manifest cache, run the cheap key-and-digest gate
  `python3 scripts/review_dashboard.py --paper <paper-folder> --source-inventory-check`.
  It catches missing or orphaned coverage records and stale source statements
  without parsing Lean; it is not a substitute for the semantic row-link check.
  Then run
  `python3 scripts/review_dashboard.py --paper <paper-folder> --paper-coverage-precheck`.
  Compactness is not a valid reason to mark an in-scope named theoretical
  target out of scope. In normal `named_theoretical_statements` mode,
  source-presented definitions, explicitly named assumptions/model conditions,
  theorem-like claims, lemmas, propositions, theorems, corollaries, and named
  appendix results should have review-legible dashboard rows with row-local
  statement judgments. Standalone formulas, equations, and algorithms do not
  become normal independent rows merely because they are numbered; retain them
  for deep audit or as dependencies of a selected named item. Ordinary examples
  and remarks are likewise deep-only. An unlabelled condition needed by a
  selected result is retained as that result's dependency.
  Scope the inventory from the source presentation and its pinned text, never
  from a Lean declaration, function name, map key, or title similarity. Every
  source-labelled definition, lemma, proposition, theorem, corollary, named
  claim, and theorem-like displayed result remains a required formalization
  target. A source label decides this rule; a Lean name such as `theorem42` or
  an inventory key cannot manufacture or remove a formal source target.

  **Current source-scope policy.** A closeout must explicitly declare
  `source_coverage_mode`. The normal mode is
  `named_theoretical_statements`: source-presented named definitions, results,
  theorem-like claims, explicitly named assumptions/model conditions, and named
  appendix results. Standalone formulas, equations, algorithms, narrative
  prose, captions, figures, tables, numerical examples, simulations, empirical
  observations, examples, and remarks are not normal independent rows. Audit
  them only in explicit `deep_paper_with_all_prose_claims` mode, except when a
  display is needed as a dependency of a selected named item. An unlabelled
  condition needed to establish a selected item remains that item's dependency,
  not a new normal-scope result.

  Normal closeout needs an independent source-only named-presentation index
  over a pinned UTF-8 text/TeX audit artifact, with a current receipt digest.
  The map cannot certify its own completeness. Declare any nonstandard source
  environment or visible heading meaning in that receipt; a discovered but
  unclassified named presentation blocks closeout. A named conjecture or open
  question is catalogue-visible and needs an explicit source-declared-open
  nonproof disposition. It is never silently treated as a theorem or omitted.

  Source map keys, `source_kind`, `claim_bearing`, aliases, and Lean names do
  not establish or suppress source coverage. Reconcile a discovered source
  presentation only through its canonical source span and exact byte-pinned
  anchor, then bind it to one unique current elaborated Lean signature and
  semantic contract. Existing legacy `user_approved_scope_exclusion` metadata
  may remain historical evidence, but it is not the ordinary normal-mode route
  for prose that the source did not present as an independent named result.
  For public-facing statuses (`formalized` or `partially formalized`), the
  audit requires an explicit source inventory; heuristic source-text extraction
  is only a seeding aid and must not satisfy closeout by itself.
  The inventory must be resolvable in the repo where the audit runs: if raw
  source text/PDF cannot be tracked publicly, put a compact source statement or
  paraphrase plus citation/location directly in `audit/paper_statement_map.json`
  rather than pointing to a private `source.txt`.
  If you create the map with
  `scripts/seed_paper_statement_map_from_dashboard.py`, mark it as
  `source_inventory_kind: "dashboard_seeded_preliminary"` and
  `source_curated: false`. That map is useful for making the coverage machinery
  concrete, but it is not evidence that the paper source has been exhaustively
  inventoried. A very large count can mean the dashboard contains many
  formula/proof-support rows, not that the paper has that many named source
  statements; for example, an 80+ row source inventory should trigger a source
  curation pass that separates named paper statements from subformula/support
  rows.
  Before preparing a public PR, replace any dashboard-seeded preliminary map
  with a curated source inventory whenever the row count is inflated by
  alternative theorem routes, kernel/probability support lemmas, or
  implementation sanity checks. Keep explicit boundary assumptions in
  `review_surface.assumption_names` and `assumption_match_llm.json`; do not
  count those rows as ordinary source statements in `audit/paper_statement_map.json`
  unless the paper itself states them as theorem targets.
  After changing the review surface or assumption-source metadata, refresh the
  paper dashboard cache, regenerate `paper_coverage_llm.json`, rerun the
  assumption-provenance audit, and refresh `source_record_audit.json` plus
  `source_record_match_llm.json` whenever the audit digest or prompt version is
  stale.
- Treat source-to-Lean coverage as a chained audit, not two unrelated green
  checks. A source item marked `covered` in `paper_coverage_llm.json` must link
  to concrete `review_rows`, and those rows must have current row-local LLM
  correctness judgments in `statement_match_llm.json`, even when the row is an
  assumption row. The statement-match judgment must be for the exact current
  dashboard paper statement of the linked row; the script checks the saved
  paper-statement digest automatically, so a green judgment for an old or
  different statement does not count. `assumption_match_llm.json` is a separate
  provenance/boundary lane for whether an assumption is source-derived or a
  partial formalization boundary. Run
  `python3 scripts/review_dashboard.py --paper <paper-folder> --source-to-lean-precheck`
  before claiming a paper is complete; use `--source-to-lean-check` as the
  blocking version once any intentional support-only legacy rows have been
  promoted or reclassified. A theorem/lemma/proposition/corollary source item
  covered only by `support_declarations` is a warning sign: promote it to a
  source-facing `PaperInterface.lean` row with Lean-to-TeX and statement-match
  judgments, or mark the paper status/coverage boundary honestly.
  The repository audit treats required source-visible targets marked
  `out_of_scope`/`not_a_paper_target` as failures. A legacy
  `user_approved_scope_exclusion` remains visible historical evidence, but
  normal named-theory scope does not require an exclusion record for ordinary
  prose that was never selected as a named source presentation. If the
  dashboard grows, make it more navigable with slices and clear source-facing
  statements rather than shrinking away named paper content.
- Treat paper coverage as five separate LLM-as-judge lanes:
  1. **Source inventory lane.** Read the source PDF/TeX/text (or a previously
     recorded source inventory with source locations) and write
     `audit/paper_statement_map.json` from paper statements, not from Lean names.
     Mark source-derived inventories as `source_inventory_kind:
     "source_curated"` and `source_curated: true`. Include source evidence such
     as theorem/equation number, section, source-cache line, or a compact quote
     or paraphrase. If an item is intentionally out of scope, record that
     explicitly rather than omitting it silently.
  2. **Source-to-dashboard lane.** A separate judge reads each source inventory
     item and the candidate human-dashboard rows, then records in
     `paper_coverage_llm.json` whether the source item is `covered`,
     `conditional_boundary`, `covered_by_support`, `partially_covered`,
     `missing`, or `out_of_scope`. The sidecar must use `audit_kind:
     "source_to_dashboard_llm"` (or `"source_to_dashboard_agent"`),
     `source_grounded: true`, linked `review_rows` for dashboard coverage,
     `support_declarations` for support-only coverage, `source_evidence`, and a
     nontrivial match reason. Exact name/alias matches from
     `scripts/seed_paper_coverage.py` are only `audit_kind:
     "exact_key_scaffold"` and must not pass a closeout audit.
     The seed command never refreshes Lean manifests: on an absent or stale
     local row cache it stops visibly. Use
     `--all-uncertain-bootstrap` to make a no-row, name-independent
     `all_uncertain_bootstrap` scaffold before the first paper-only cache
     refresh. That scaffold is intentionally non-evidence and must be replaced
     by a source-grounded semantic judgment after current rows are available.
     Every explicit `source_kind` must use the repository enum. An unknown
     nonempty value is an audit error; it must not create a custom lane that
     evades theorem-proof or review-row requirements.
  3. **Quarantined-defect support lane.** A source item with `source_status:
     "quarantined_source_defect"` is never directly proved. If it is classified
     `support_only`, populate `audit/defect_support_match_llm.json` with a
     separate source-grounded semantic judgment for every defect and support
     route used. Each positive judgment must exact-hash pin the canonical source
     item, the complete validated `source_proof_fidelity.json` defect record,
     the retained raw Lean statement snapshot, and its name-independent
     elaborated semantic signature. Raw spelling is trace evidence rather than
     reuse identity. It must partition
     every signature atom and explain how all parameters/assumptions form a
     valid witness or source-model condition and how the conclusion
     counterexamples/refutes the exact `source_claim`. Declaration names and
     theorem/lemma kind are routing only. `True`, reflexive equality/equivalence,
     vacuous implications, stale hashes, and unaccounted inputs provide no
     defect-support credit.
  4. **Row-local statement lane.** Generate `lean_to_tex_llm.json` from Lean
     statements alone, then have another judge compare that translation against
     the dashboard row's paper statement text in `statement_match_llm.json`.
     Every row-local judgment must save Lean, TeX, and paper-statement digests;
     the source-to-Lean audit uses those digests to ensure the judge checked
     the same statement that the linked row currently claims to cover. This
     answers whether a dashboard row says what its displayed paper statement
     says; it does not answer whether all source statements are represented.
  5. **Joined source-to-Lean lane.** The dashboard script joins
     `paper_coverage_llm.json` to the row-local correctness files and emits
     `row_statement_match_links`/`row_correctness_*` JSON records with source
     digests, row digests, row names, validators, timestamps, and stale flags.
     Inspect these records when debugging a false completion: the paper is not
     actually source-to-Lean clean unless every covered source statement either
     has passing linked row correctness judgments for the same current row
     statements, or is explicitly and honestly marked as conditional/out of
     scope/support-only.
- Paper-facing definitions in `PaperInterface.lean` must show their actual
  Lean definition bodies, not only their function types or an opaque imported
  library name. If a dashboard row for a definition renders as only
  `A -> B -> ...` or `ℝ -> ...`, stop and fix the interface/dashboard before
  asking a human to review it. A reviewer should be able to compare the paper's
  displayed formula directly against the Lean formula in that row.
  When the reusable implementation must remain an imported definition or short
  alias, add a source-equation wrapper theorem in `PaperInterface.lean` such as
  `_formula`, `_iff`, `_fields`, `_rule`, `_content`, or `_matches`, and include
  that wrapper in `status.json` `review_surface.include_names` instead of the
  opaque alias. The wrapper must make the formula visible, but visibility is
  not proof provenance: it is closed only when the formula is derived in Lean
  from source model primitives or from separately validated paper assumptions.
  If the wrapper asserts a displayed equation, inequality, iff, definition, or
  source-defining formula as a theorem premise, certificate field, or source
  row, the downstream endpoint is partial until that premise is derived or
  routed through `Assumptions.lean` and approved by the source-assumption judge.
  The repository audit checks this failure mode when an included alias has an
  available source-equation wrapper.
  The dashboard/audit parser treats `paper_...` declarations in
  `PaperInterface.lean` as review rows even if their docstrings are removed or
  converted to ordinary comments. Do not keep auxiliary `paper_...` aliases in
  `PaperInterface.lean` merely to support downstream proof code. Move or omit
  them, and expose only the source-shaped wrapper row, such as a finite-vector
  objective wrapper or an explicit `_fields` wrapper, in the review surface.
  Every displayed or source-defining formula used by a paper-facing result
  should have an exact formula/subclaim row. Do not collapse several displayed
  formulas or subclaims into a broad numbered-result row such as a metric
  package, source surface, or model summary when claiming full validation.
  The independent judge must be able to compare the full theorem scope, not just
  the label or endpoint shape: signs, constants, domains, all quantifiers,
  inequality direction, normalizing factors, hypotheses, subparts, conclusions,
  and iff/implication direction for each formula-bearing row. A `matches` verdict
  is allowed only when the row is equivalent to the full source statement, or to
  a source subpart explicitly identified as such. If a Lean row omits a source
  subpart, adds a non-source condition, weakens/strengthens the conclusion, hides
  a displayed formula in a source-row package, or represents several displayed
  formulas with one broad aggregate, the judge must return `mismatch` or
  `uncertain`.
  When an LLM-as-judge row is `uncertain`, inspect the actual Lean statement
  before accepting the uncertainty. If the Lean row is only a function
  signature, imported alias, structure name, or conclusion predicate, fix
  `PaperInterface.lean` by exposing the equation, fields, iff, or theorem
  conclusion. If the Lean row is already source-shaped but the TeX draft erased
  binder context such as `W` versus `W'`, regenerate the Lean-to-TeX draft and
  then rerun the judge; do not change a correct Lean statement to satisfy a bad
  draft.
  Treat source-equation-wrapper findings from `scripts/audit_repository.py` as
  review-surface blockers: if an included alias has a paper-facing `_formula`,
  `_iff`, `_fields`, `_rule`, `_content`, or `_matches` wrapper available, the
  dashboard row should expose that wrapper, not the opaque alias.
  Treat stale Lean-to-TeX or statement-judge sidecars the same way: stale
  sidecars do not change a Lean proof, but they invalidate the current
  source-match claim until regenerated and rechecked. After renaming aliases,
  splitting aggregate rows, or changing source-provenance docstrings, refresh
  the uncached dashboard cache, regenerate tracked sidecars from that current
  cache/surface, remove obsolete keys, and run the paper's statement precheck
  before carrying the result into a report, generated status table, or public PR.
  Broad aggregate rows are not acceptable substitutes for formula-level review.
  If one Lean declaration summarizes several paper formulas or subclaims, expose
  separate paper-facing rows for the exact formulas/subclaims and include those
  rows in `status.json`; keep the aggregate theorem in the audit ledger only if
  it is useful for proof coverage.
- Every dashboard row should label source provenance in the `PaperInterface.lean`
  docstring. Use dashboard-only lines such as `Source status: direct paper
  statement`, `Source status: direct paper formula`, `Source status: corrected
  source statement`, or `Source status: added audit row`; for any corrected,
  edited, weakened, strengthened, or added row, include a `Source note: ...`
  line that states exactly how it differs from the paper. The dashboard strips
  those lines from the statement text and displays them as badges/notes. Treat a
  missing source-deviation note as a review-surface bug, not as a harmless
  documentation omission.
- Every non-derived paper-facing theorem premise should appear as a named
  assumption declaration in paper-local `Assumptions.lean`, imported by
  `PaperInterface.lean` when a theorem signature references it. Add the
  declaration to `status.json` `review_surface.assumption_names` and run
  `python3 scripts/review_dashboard.py --paper <paper-folder> --assumption-precheck`
  at review boundaries. If the assumption judge is missing, stale, uncertain,
  or says `not_paper_assumption`, the downstream theorem is conditional/partial
  until that premise is derived or the source assumption is documented. Do not
  hide proof certificates, source-row equations, threshold identities, or
  normalizer formulas inside theorem parameters to avoid this workflow; those
  are either Lean proof obligations to close or explicit paper assumptions to
  validate.
  `scripts/audit_repository.py` expands review-surface declarations, checks
  direct paper-local `abbrev`/`def` aliases, scans paper-facing declarations
  outside `PaperInterface.lean`, and runs Lean-native `#print axioms` on
  paper-facing rows. Moving a certificate to `ProofInterface.lean` does not
  make a completed theorem closed if the expanded paper-facing statement still
  exposes that certificate. The dashboard `--assumption-precheck` path also
  invokes these premise and axiom checks for the selected paper, so it may
  report unresolved proof premises even when the explicit assumption table has
  zero rows. If that audit flags an alias target, first refresh the dashboard
  cache and inspect whether the premise is an ordinary scalar condition already
  visible in the expanded statement or a true certificate/source-boundary
  package. Scalar paper conditions belong in the statement and
  statement-validation lane; certificate/source-boundary packages must be
  discharged, exposed as validated paper assumptions, or downgraded to
  conditional/partial.
  The checker must inspect anonymous top-level arrows in expanded declarations
  as well as named binders. A premise whose type head is a certificate, row
  package, regularity bundle, capacity/cutoff formula package, or source
  boundary is still a visible proof obligation even if Lean prints it without a
  name. Conversely, avoid false positives from ordinary source equations that
  mention a constant with a certificate-like name inside the formula; classify
  the premise type head, then use exact premise comments in `Assumptions.lean`
  to show how the assumption judge reviewed it. Use Lean's axiom printer, not a
  custom recursive text scan, for transitive proof dependencies.
  At closeout/public-promotion boundaries run the combined recursive
  provenance audit:
  `python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0 --write-report docs/RECURSIVE_PROVENANCE_AUDIT_<date>.md`.
  Use `--include-active` when the paper being closed is in the active-paper
  allowlist; otherwise it may be omitted. Treat the generated Markdown as the
  durable closeout ledger for Lean axiom closure, broad/opaque paper-facing
  rows, source-row formula boundaries, visible premises, and source-shaped
  reusable-library APIs. A paper can be marked `formalized` only
  if this report has no theorem-status findings for that paper, except findings
  already resolved by deriving the premise from primitives or by routing it
  through a source-validated `Assumptions.lean` declaration. If a visible
  premise finding remains, the paper/result is partial or conditional and the
  same boundary must appear in `status.json`, the DAG, and the final validation
  report.
  Also run
  `python3 scripts/audit_repository.py --library-only --library-premise-audit --info-limit 0`
  after reusable library edits; that pass reports direct certificate/source
  boundary APIs and rejects source-shaped reusable definitions. Use it together
  with the paper-interface axiom audit, not as a replacement for Lean's own
  transitive dependency check.
- Keep proof-linkage declarations such as `paper_definition_eq_library_name`,
  bare aliases for generic predicates, and other implementation checks out of
  `PaperInterface.lean`. Put them in `ProofInterface.lean` or another
  proof-facing file so the dashboard asks humans to review only source-facing
  definitions and named results.
- For new papers, create `PaperInterface.lean` during intake from the scaffold,
  not only after the proof is complete. Keep it synchronized with the proof plan
  and DAG so the eventual human review file grows with the formalization.
- Use a statement-first private skeleton. After source inventory, write every
  in-scope named paper-facing theorem/result with its complete source-shaped Lean
  type and a temporary `by sorry` proof body. Do not replace the hole with an
  axiom, theorem package, certificate, or added assumption. Build and audit the
  types first, freeze their current canonical declaration-manifest and semantic
  dependency digests in the plan, then
  replace the holes without changing those types. Any signature change makes
  the saved statement judgment stale. This `sorry` exception is only for the
  private target-setting phase; closeout still requires zero proof holes.
- Treat source inventory plus statement review as an explicit intake freeze.
  Before proof work, byte-pin the complete normal named-theory inventory,
  source premise/conclusion atoms, exact `Spec` types, dependency order, and
  owning module/agent for each obligation. This is where omissions and hidden
  premises should be found; closeout should not be a second paper-discovery
  phase.
  New scaffolds persist the curator decisions in
  `audit/v11_source_map_preparation_config.json`; the preparation command
  derives the canonical exact anchors and inventory identities in
  `paper_statement_map.json`. Do not create a second `intake_freeze.json`
  authority. Historical papers whose tracked status already selects that
  container retain direct validation under its recorded contract, while the
  trusted pre-rollout cohort remains grandfathered. Never add or delete a
  historical marker to switch lanes or rerun an audit merely for conformance.
- While that initial statement review and manifest are fully current, run
  `python3 scripts/semantic_audit_reuse.py --paper <paper-folder>
  --bootstrap-current --write` once. It records the entry-local semantic pins
  needed for later item reuse. It is not authority to replace a stale pin and
  does not repeat the human judgment.
- Bare `scripts/new_paper.py` deliberately does not refresh the dashboard
  cache. Run `python3 scripts/review_dashboard.py --paper <paper-folder>
  --refresh-cache` once only after the intake inventory and
  `PaperInterface.lean` skeleton are stable. An early scaffold cache is expected
  to become stale and creates no reusable semantic evidence.
- Do not refresh or precheck the review dashboard after every small
  declaration-level edit. During active proof work, keep moving with Lean
  builds and source-facing docs; refresh the dashboard at natural review
  boundaries instead: after a coherent batch of `PaperInterface.lean`
  statement changes, before a human review session, before final handoff, or
  before declaring a paper/proof phase complete.
- If you only added or adjusted a few paper-facing declarations and are leaving
  a short interim stopping point, it is enough to record the changed
  declaration names in the README/plan/handoff and defer dashboard refresh to
  the next review boundary.
- The launcher checks freshness against the logged trace on startup; if an old
  check is out of date, it warns you and you can immediately re-save checks.
  If interface docstrings or source-facing statement text changed, expect old
  human review rows to become stale. Do not edit or rewrite the review log to
  clear that state; leave the dashboard warning and tell the reviewer which
  rows need to be resaved.
- Reserve the dashboard word "reviewed" for actual human review-log entries.
  The dashboard counter means "a validation row was saved"; if an agent writes
  entries, the UI will still increment the counter, but that is not human
  review. Do not populate `.review_traces/paper_theorem_validations.jsonl` with
  agent-generated entries just to clear `0/N reviewed` or `need attention`.
  For agent validation, write a tracked source-audit artifact such as
  `SOURCE_AUDIT.md`, label it clearly as an agent audit, and report the
  dashboard human-review state separately.
- Human review logs are intentionally commit-eligible: `.gitignore` should keep
  `.review_traces` caches/logs local while unignoring
  `.review_traces/paper_theorem_validations.jsonl`. After an actual human
  review pass, inspect and commit the paper-local JSONL log if those judgments
  should become part of repository history; do not commit generated dashboard
  HTML, cache JSON, rendered statement images, or `review-dashboard.log`.
- The human review-log `user` field should default to the authenticated GitHub
  username, while remaining editable in the browser. Preserve the default order:
  explicit `--user`, GitHub environment variables, authenticated `gh` username,
  git config, then OS username.
- It also shows compact paper-source action links (open PDF/text file), so the
  reviewer can quickly jump back to source wording when needed.
- Paper-facing formulas that look like LaTeX are rendered in the dashboard so
  theorem statements are easier to read without full Lean familiarity.
- Near the beginning of a new paper, run the smaller statement target-setting
  pass before serious proof work. After the source inventory and first compact
  `PaperInterface.lean` skeleton exist, give each theorem row a temporary
  private `by sorry` body, build it, and run
  `python3 scripts/audit_conclusion_provenance.py --paper <paper-folder> --json`
  before proof work. Then generate `lean_to_tex_llm.json` from Lean statements
  alone, generate `statement_match_llm.json` from only the source statement
  plus that translation, then run
  `python3 scripts/review_dashboard.py --paper <paper-folder> --statement-precheck`.
  Use `--statement-check` instead when a nonzero exit is useful for automation.
  Then run `python3 scripts/review_dashboard.py --paper <paper-folder>
  --assumption-precheck` before treating the matched statements as certified
  targets. The statement judge is row-local and will not catch a source-domain
  premise that was split out of a definition into theorem hypotheses unless the
  expanded dashboard cache has been refreshed and the premise is visible in that
  statement.
  If `--statement-check` fails here, treat it as target-setting feedback: fix
  `PaperInterface.lean` or the extracted source statement before building long
  proofs around that row. If `--assumption-precheck` reports hidden premises,
  derive them, move true paper assumptions to `Assumptions.lean`, or mark the
  endpoint partial/conditional before calling the target ready.
  Once a row matches and premise provenance clears, record its v6 canonical
  Lean declaration-manifest digest in `FORMALIZATION_PLAN.md`. Proof implementation must
  replace `sorry` while preserving that signature. A changed signature must be
  translated and judged again before further proof work.
  Use automated semantic-alignment checks as triage, not certification. A high
  match score or `matches` judgment is evidence that a human should inspect the
  row less urgently; it is not proof that the theorem is source-faithful. A low,
  stale, or inconsistent alignment result should block deep proof work on that
  row until the source statement, Lean declaration, or visible assumptions are
  repaired. Give special attention to quantifier order, implication direction,
  constants/factors, domains/support assumptions, equivalence-vs-one-way
  statements, asymptotic notation, and hypotheses moved from definitions into
  theorem parameters.
  This early pass deliberately skips workflow scaffolding: do not update the
  DAG, final validation report, human-review log, or review-surface audit just
  because the target-setting pass ran. Its purpose is to catch wrong theorem
  targets before proofs are built around them.
- For both the early target-setting pass and the full review-boundary pass, make
  sure each dashboard row has one concrete source statement. If automatic
  TeX/text extraction is missing, over-broad, or includes surrounding
  exposition, repair the paper-facing statement text before running the judge.
  Put declaration-keyed source statements in a source-inventory/report section,
  not in generated audit output. `Statement Translation Audit` is downstream
  evidence and must never become the source text for a later judge pass.
  Report parsers should treat all Markdown heading levels (`##` through
  `######`) as section boundaries and ignore generated audit sections such as
  `Statement Translation Audit`; if source statements start looking like
  validator rows, stale flags, or `uncertain` comments, fix the parser or final
  report section order before regenerating LLM sidecars.
  If nearly every row is `uncertain`, assume a parser/source-statement mapping
  failure until proven otherwise: fix the source extraction or record a
  paper-wide source-map issue, instead of leaving every row individually
  uncertain as if each theorem were separately ambiguous. When a parser failure
  is the real problem, the dashboard/report should expose one paper-wide parser
  or source-map status rather than a table that makes every theorem look
  independently uncertain.
  A judge result of `uncertain` means the statement target is not certified yet;
  do not rewrite it as "formalized with caveat" or "partial formalization"
  unless the mathematical formalization itself has that status.
  In generated public tables, keep `LLM-as-judge statement translation` as a
  translation/equivalence status column, not an assumption-provenance column.
  Raw judge rows with `resolution: conditional_boundary` should render as
  paper-facing `formalization-boundary statement rows`; do not label them
  "additional assumptions" unless they are genuine non-paper hypotheses in the
  separate assumptions section.
  If the same public table also shows a human-review denominator, the LLM row
  summary must reconcile with that denominator: report statement-translation
  rows and explicit source-condition/assumption rows as separate components
  instead of showing an unexplained smaller statement-only total.
- Use the dashboard's normalized `statement_digest` values for sidecar digests,
  not raw SHA-256 of unnormalized strings. Lean-statement sidecar hashes must
  be source-stable: hash the source declaration text exposed by the review
  surface (`interface_source` / raw paper-facing declaration), not optional
  rendered `#check` preview text. The preview is useful for humans, but it can
  differ between a warm local checkout and a cold CI checkout if Lean preview
  subprocesses time out or fall back to raw signatures. New tracked
  `lean_to_tex_llm.json` entries should include `lean_statement_sha256`; new
  `statement_match_llm.json` entries should include Lean, paper, and TeX
  statement digests so stale target checks work.
- At a statement-review boundary, run the exact statement-translation workflow:
  1. Curate `PaperInterface.lean` first. In normal mode it should contain
     paper-facing definitions, explicitly named assumptions/model conditions,
     and named source results that a reviewer or LLM-as-judge should inspect.
     Do not include standalone formulas/equations, algorithms, proof plumbing,
     examples, remarks, empirical sections, helper lemmas, or library-internal
     facts unless the user explicitly selected deep all-prose audit mode or the
     item is needed to express a selected named result.
     Completeness beats compactness: do not hide named source content only
     because it makes the review surface longer.
     If row-level dashboard or LLM audit declarations make this first-read file
     too large for human review, move proof plumbing and broad helper endpoints
     to `AuditInterface.lean`, `ProofInterface.lean`, or implementation
     modules, then keep paper-facing wrapper statements in `PaperInterface.lean`.
     Do not point `status.json` `review_surface.source_file` away from
     `PaperInterface.lean`, and do not set `paper_interface.audit_surface_path`.
  2. If the dashboard has more than 30 rows, run a no-paper-context surface
     pass over the row list and save `review_surface_llm.json`. The pass asks
     only whether each row belongs on the human-facing paper surface. At 120 or
     more rows, treat the surface as a warning even if an audit exists; improve
     slices, source statements, and row grouping, but do not remove
     source-visible content that the coverage audit needs. More rows are fine
     when they make the review surface more legible to the LLM-as-judge and the
     source inventory confirms that they cover paper claims.
  3. Build or refresh `audit/paper_statement_map.json` from the source paper itself,
     not from the Lean row list. It should be a canonical source inventory with
     aliases only as lookup aids. Then generate `paper_coverage_llm.json` with
     a separate paper-level judge that asks whether each source inventory item
     is represented by one or more current dashboard rows. This is the only
     LLM-as-judge lane that answers "did we include every paper statement?";
     the row-local statement judge below cannot answer that question.
     A dashboard-seeded map is only a temporary scaffold; before citing it as
     paper coverage, compare it against the source PDF/TeX and either add
     missing named statements, mark support-only proof-route lemmas as
     `covered_by_support` with explicit `support_declarations`, mark rows that
     match only under a declared proof boundary as `conditional_boundary`, or
     mark genuinely non-target source material as `out_of_scope` only in an
     explicit deep all-prose audit. Do not use any disposition to suppress
     source-visible named material merely because adding rows would make the
     dashboard longer.
  4. Generate `lean_to_tex_llm.json` from the Lean statements alone, with no
     paper text and no proof context. Use one item per current dashboard row.
     The translator prompt must be literal rather than explanatory: preserve
     every visible binder, variable, hypothesis, domain restriction, premise,
     equivalence/implication direction, and conclusion in mathematical form. It
     must not compress the statement into a theorem label, omit conditions, or
     turn a conditional theorem into an unconditional prose summary. For new
     tracked sidecars, use object entries:
     `{ "tex_statement": "...", "lean_statement_sha256": "..." }`. Legacy plain
     string entries are accepted, but object entries make stale-draft checks
     possible.
  5. Generate `statement_match_llm.json` with a separate judge that sees only
     the original paper statement and the Lean-to-TeX draft, not the Lean proof
     or surrounding paper. The paper statement supplied to the judge must be the
     complete source theorem/definition/formula text or an explicitly named
     source subpart, including all preconditions and subclaims needed to decide
     equivalence. Do not feed the judge a theorem title, generated report
     summary, or selected excerpt as the paper side. Each entry should include
     `judgment`, `reason`,
     `lean_statement_sha256`, `paper_statement_sha256`, and
     `tex_statement_sha256`. Valid judgments are `matches`, `uncertain`, and
     `mismatch`. The sidecar should also record validator provenance: put the
     model or agent name in `validator` (for example `gpt-5-codex`), set
     `validator_type` to `model` or `agent`, record `validated_at`, and use
     `comment` for any validator-facing note that should appear in the status
     export. Top-level validator/comment fields are defaults; item entries can
     override them when a different model or agent checked a specific row.
     Keep the raw `judgment` strict. If a paper row is a known, user-approved
     conditional result because it depends on an external/library theorem,
     analytic theorem, solver, runtime model, or other explicit proof boundary,
     do not mark it `matches`. Mark the raw row `mismatch` and add
     `resolution: "conditional_boundary"`, plus `boundary_type`,
     `boundary_names`, `conditional_premises` when applicable, and
     `resolution_reason`. This records an intentional mismatch/known external
     dependency without hiding the source-statement gap. Any visible extra
     theorem premise accepted this way must appear in `conditional_premises`;
     otherwise the hidden-premise audit should keep reporting it as unresolved.
     The judge prompt must be exact-formula and full-theorem aware: it should
     reject broad aggregate rows when the paper has displayed equations,
     inequalities, iff statements, definitions, or source-defining formulas that
     are not exposed as their own row or subclaim. Ask it to compare every
     hypothesis, source assumption, domain, quantifier, subpart, conclusion,
     sign, constant, normalizing factor, inequality direction, and iff/
     implication direction. The judge pass is recursive for formula-bearing
     terms: if the Lean row refers to a paper-local or reusable-library
     definition that encodes a displayed source formula, provide the expanded
     formula or a proved paper-local equivalence as part of the Lean-side
     material to be judged. It must mark `mismatch` or `uncertain` if the Lean
     draft is conditional when the paper statement is unconditional, omits a
     paper conclusion, changes a theorem from equivalence to one direction, uses
     a source-row/certificate package instead of the displayed formula, hides a
     source formula inside a generic library definition, or proves only a
     helper/endpoint that is not the full paper statement.
     Also scan the source proof, not just the theorem heading, for stochastic
     qualifiers such as "with probability 1", "almost surely", "with high
     probability", "probability tends to 1", or "probability zero". If the proof
     closes the named result only through such a probabilistic event statement,
     include that qualifier in `audit/paper_statement_map.json` and judge any
     deterministic Lean wrapper as conditional unless Lean also models the
     probability space/event and proves the qualifier.
     For rows that mention records/certificates/source models, first generate
     or refresh `source_record_audit.json` with the skill helper. Feed the
     relevant row and field entries, including Lean `#check` output, to the
     judge. The judge must verify that each mathematical source statement in
     those fields is proved from primitive Lean declarations, explicitly
     validated as a paper source assumption, or intentionally marked as an
     external boundary. A field projection is evidence that the statement was
     assumed in the record, not evidence that it was proved.
     The same rule applies when a theorem result hides a Type-valued package
     behind `Nonempty C`, `∃ c : C, ...`, raw `Exists`, a transparent
     proposition wrapper, or a local Prop constructor that stores `C`. Such a
     row may be listed as support, but it is not canonical proof evidence for
     a paper result merely because `C` contains the desired proof fields.
     Expose paper-facing theorem/lemma endpoints
     whose conclusions state the relevant field-level propositions (or an
     explicit proposition-level conjunction), and route the source claim to
     those endpoints. Make this decision from the expanded logical wrapper and
     recursively expanded field types, never from names such as `Certificate`,
     `Package`, or a field name.
     Source-record audit payloads must be reproducible across machines. Store
     source files as repo-relative paths, never as `/home/...` absolute paths,
     because those paths enter the audit prompt/digest surface and can make a
     fresh CI checkout report stale `source_record_audit_sha256` values even
     when the Lean statements are unchanged. After touching the source-record
     helper, source maps, `PaperInterface.lean`, or source-record-bearing
     theorem signatures, regenerate both the code-backed
     `source_record_audit.json` payload and the matching
     `source_record_match_llm.json` sidecar for the affected rows before using
     them as evidence. The helper must distinguish source assumptions declared
     in `Assumptions.lean` from ordinary paper-interface rows; otherwise an
     assumption can be falsely judged as a theorem translation. During active
     proof work, run targeted script/unit checks and regenerate only the
     affected audit payloads needed for the changed rows. Run the full
     repository audit only at closeout/public-promotion time or when the user
     explicitly asks for post-validation.
     When prompt versions, digest fields, or cache schemas change, verify the
     audit path in both uncached and cached modes. Cached review rows must
     rehydrate all Lean, paper, TeX, source-record, and premise digests used by
     `--source-to-lean-check`; a green uncached check with a cached digest
     failure usually means the cache loader or schema migration is stale, not
     that the paper proof changed. Patch the audit script, bump the cache schema
     if needed, run `python3 -m py_compile` on changed scripts, and rerun the
     paper-local checks.
     Reuse evidence at the generated-item level, never by broadly declaring a
     paper stale after a parser, diagnostic, or cache implementation change.
     Preserve the prior canonical raw source-record receipt before a semantic
     item-receipt schema migration. Reuse a prior judgment only when its exact
     generated item has a current full semantic descriptor match: expanded Lean
     obligation, source-route role and content, elaborated endpoint, scoped
     context, and proof-fidelity record. A missing prior raw receipt makes a
     legacy judgment a revalidation seed, not automatically current evidence.
     Historical papers may still contain a byte-pinned differential overlay.
     `scripts/source_record_differential_revalidation.py` is now a reader only:
     it may preserve only a *unique*, exact descriptor-identical generated
     group and must authenticate the current canonical raw receipt before
     accepting it. Do not issue a new differential overlay. Graph-native
     closeout instead reuses independently content-addressed current judgment
     leaves whose exact source atom, expanded Lean target, semantic context,
     and proof-fidelity coordinates remain unchanged; changed or ambiguous
     leaves return to review. Historical input/field groups remain local to
     their expanded obligation, source content/route role, context, and
     proof-fidelity scope, while semantic-model groups retain the full result
     surface. No path may match via a judgment key, theorem/declaration name,
     binder, or shared storage spelling.
     The descriptor and group semantics themselves belong to
     `scripts/source_record_obligation_groups.py`, not to that historical
     reader. Every current consumer and every retained historical reader must
     call this one transport-independent authority. Do not copy its
     normalizers into a planner, dashboard, receipt adapter, or new transport.
     A module extraction is nonsemantic only after the serialized descriptor
     preimages and digests agree across the complete tracked raw corpus and
     malformed/unknown group surfaces retain fail-closed tests.
     For the exceptional complete-manual-revalidation route, use
     `scripts/source_record_current_revalidation.py` only after a reviewer has
     inspected the current v10 raw surface. Its attestation must bind the exact
     prior sidecar bytes, current aggregate raw receipt, complete generated
     item surface, and exact generated-key ledger; shared source-target and
     semantic-model validators must still pass. Move legacy narrow item pins
     to historical provenance, then regenerate an exact schema-5 pin set only
     from the attested current raw item groups; never relabel a schema-4 pin as
     schema-5 evidence. The aggregate receipt remains authoritative for an
     ambiguous multi-descriptor key. This is a manual semantic review boundary,
     not an automatic migration or a name-based reuse path.
     Never use declaration/binder spelling, a shared digest, or a renamed key
     to infer that two audit obligations are the same.
     A recursive record field may inherit source provenance only through an
     explicitly enumerated structural field path rooted at one exact directly
     routed parent source statement. The generated receipt must pin the parent
     route, root input type, convention/source scope, and every record-field
     edge. Do not infer field credit from a helper name, a shared leaf type, a
     support-only route, or an unscoped broad model package.
     The expensive raw source-record cache is keyed to explicit
     generated-surface semantic versions, source artifacts, Lean dependencies,
     and paper-local semantic inputs. Bump a producer version when a change can
     alter emitted obligations or receipts; do not invalidate every paper for a
     validator, dashboard, migration, diagnostic, or documentation-only edit.
     When a producer repair affects only a recognizable printed-source grammar
     or source-map relation, attach its version only when that paper's current
     source material exercises the feature. Base that predicate on source
     content and coverage mode, never map keys, declaration names, or binders;
     preserve exact current receipts for papers outside that semantic surface.
  5. Treat `mismatch` or `uncertain` as a problem with the formalized statement
     unless the translation is plainly wrong. Usually the fix is to make the
     `PaperInterface.lean` declaration more paper-facing and self-contained,
     then rerun both LLM passes.
     When refreshing stale sidecars after editing `PaperInterface.lean`, do not
     try to clear CI by lengthening preview timeouts, relying on ignored
     dashboard caches, or copying hashes from a warm checkout. Regenerate the
     tracked sidecars from the current uncached review surface and store the
     source-stable Lean declaration digest. During active diagnosis, a cache-free
     paper-local summary or `--statement-check` can isolate a statement lane. At
     frozen closeout, begin with the planner rather than chaining dashboard and
     repository commands by hand. If local dashboard checks pass but CI reports every row stale for a
     paper, suspect environment-dependent preview hashing first; fix the digest
     source rather than fighting the build cache.
     If stale rows appear after a public/private copy or a CI checkout while
     the Lean code is unchanged, first refresh the uncached dashboard surface
     and tracked LLM sidecars from that checkout. Do not copy ignored dashboard
     caches from another machine or assume stale sidecars are human-review
     failures; human review can be unreviewed, but only generated model/agent
     sidecars become stale.
     If only prompt/audit code changed and the Lean/source statements are
     unchanged, refresh the digest metadata from the current checkout and keep
     the validator judgments verbatim only after confirming the normalized
     source statement, Lean declaration text, and boundary metadata are
     identical. Never rewrite a `mismatch` or `uncertain` to `matches` merely
     because a digest or prompt version changed.
  6. Record statement-translation results in the final report's validator
     surfaces, not in an ad-hoc extra report heading. Summarize row counts,
     match/uncertain/mismatch counts, stale status, and surface-audit status in
     sections 1 and 11 as needed, then fill section 15
     `Paper-Facing Statement Validator Ledger` from the validators export. This
     is agent audit evidence, not human review.
  7. Before an active statement-review handoff, use
     `python3 scripts/review_dashboard.py --paper <paper-folder> --precheck`
     only to diagnose a named stale or invalid statement-audit row. At frozen
     closeout, do not make that precheck a routine predecessor: freeze the
     inputs, run `closeout_reuse_plan.py`, and execute only its current
     `next_action`. Remaining `uncertain`, unresolved `mismatch`, and `mismatch` rows with
     `resolution: "conditional_boundary"` must be explicitly listed in the
     final validation report. A conditional-boundary mismatch may be accepted
     only if the same boundary is named in `status.json`, the DAG/report caveat,
     and the assumption/proof-boundary metadata.
- At a post-paper closeout boundary, run LLM-as-judge freshness and provenance
  checks before committing or pushing. A user request such as "post paper
  workflow", "audits", "finish the paper", or "commit and push after closeout"
  is sufficient trigger for the target paper's machine prechecks, but it is not
  a request to rerun LLM judges for every paper in the repository. The Python
  precheck/audit code should verify that tracked sidecars are present, current,
  non-stale, and non-flagged. Regenerate LLM sidecars only for the target paper
  rows/records that are missing, stale, structurally changed, or explicitly
  requested. Do not launch all-paper LLM-as-judge refreshes unless the user
  specifically asks for an all-paper judge refresh. This is not an in-progress
  proof check: if the paper is still known to be unfinished or waiting on
  library work, skip the closeout pass unless the user explicitly asks for it,
  and report targeted build/status results instead. The target-paper closeout
  pass must:
  - refresh the uncached dashboard row surface for the paper;
  - ensure every `PaperInterface.lean` declaration is classified: reviewed rows
    in `review_surface.include_names`, paper assumptions in
    `assumption_names`, and all proof-facing helper declarations in
    `auxiliary_names`; auxiliary slice buckets may be added solely to satisfy
    audit/readiness row-count checks, but they do not make those helpers part of
    the visible human dashboard;
  - run the no-paper-context review-surface judge for the target paper only
    when the row count exceeds the surface threshold and
    `review_surface_llm.json` is missing/stale/flagged, or when explicitly
    requested;
  - refresh the explicit source statement inventory in `audit/paper_statement_map.json`
    when the target paper source inventory changed, then run
    `--source-inventory-check` before the dashboard cache refresh so a missing
    source item or orphaned coverage record does not trigger needless Lean
    signature extraction. When the cache is current, use targeted
    `--statement-check` and `--paper-coverage-check` before any rebuild. Once
    the source map, interface, and status surface are stable, refresh the
    target-paper cache once, then use the full coverage precheck to verify
    `paper_coverage_llm.json` against current dashboard row names. Let the
    manifest tool use bounded chunk retry and per-row fallback for outliers;
    do not restart a whole-surface extraction. For a
    public-facing status, a missing explicit inventory is a closeout blocker
    even if the dashboard has few rows or all existing rows have clean statement
    judgments;
  - verify `lean_to_tex_llm.json` for every current non-assumption review row
    using source-stable declaration digests, and regenerate only missing/stale
    target-paper translations;
  - generate the code-backed recursive source-record audit for every row whose
    statement or visible premises mention a record/certificate/process/source model,
    and save it as `source_record_audit.json` or a dated equivalent;
  - keep the recursive audit conservative but precise: if it reports a missing
    source-shaped type solely because a primitive enum/base carrier name ends in
    a trigger suffix such as `Model`, add that name to the audit helper's
    non-source-record whitelist instead of adding a fake source judgment;
    similarly, do not classify ordinary source predicates as provenance
    packages merely because their names end in `Bound` or `Bounds` (for example
    `MarginalBound`); those belong to row-local statement matching unless they
    are inside a certificate/source-record/process/replay/bridge structure;
  - verify `statement_match_llm.json` with the strict full-statement,
    exact-formula, recursive-definition prompt metadata described above,
    including the source-record audit entries for rows that depend on such
    structures; rerun only missing/stale/flagged target-paper rows unless the
    user asks for a broader refresh;
  - inspect source-record classifications before setting the status: any
    remaining `approved_external_boundary`, `unresolved_assumed_math`, stale
    source-record digest, or missing source-record judgment makes the affected
    row partial/conditional unless a Lean constructor has discharged it or the
    status claim explicitly excludes that source item;
  - verify `assumption_match_llm.json` for every name in
    `review_surface.assumption_names`, including both source assumptions and
    any user-approved proof-boundary axiom names from `proof_boundary_names`;
    regenerate only missing/stale/flagged target-paper assumption judgments;
  - classify proof-boundary axioms as `partial_boundary`, not as source
    assumptions, and give item-level `premise_judgments` for each exact
    `-- audit-premise` line in `Assumptions.lean`;
  - treat `resolution: "conditional_boundary"` in `statement_match_llm.json` as
    a provenance suppression only for the same current review row, only with the
    current prompt version plus validator/timestamp metadata, and only for
    non-completed statuses. A `formalized` paper must still discharge or
    source-record-validate every certificate/source-model/replay/process
    premise rather than relying on a conditional row mismatch;
  - update `docs/DependencyDAG.tex`, render and visually inspect
    `docs/DependencyDAG.pdf`, and record that DAG audit evidence in both
    `FINAL_VALIDATION_REPORT.md` and `docs/POST_FORMALIZATION_AUDIT.md`;
  - complete the final adversarial review contract selected by the planner's
    frozen surface. Each required policy-aware reviewer independently reads the
    complete selected terminal source/Lean material, uses a distinct audit
    document, and records its identity, exact surface attestation, audit hash,
    and independence in `docs/FINAL_ADVERSARIAL_REVIEW_PANEL.json`. The first
    audit remains `docs/AGENT_SOURCE_AUDIT.md`; a historical surface without
    policy assurance keeps only its recorded single-file contract. Do not start
    from dashboard rows or treat row-local LLM sidecars as the audit. Give PASS
    only when the reviewer's own source/inventory/interface analysis agrees,
    and preserve valid earlier panel entries if only reviewer count rises. The
    current machine markers and scope rules live in
    `references/audit-and-closeout.md` and its linked prompt, not this handbook;
  - before the final freeze, resolve every already-known unresolved `mismatch`,
    `mismatch` with `resolution: "conditional_boundary"`, `uncertain`, stale,
    missing, or broad-surface finding and record real mathematical boundaries
    in the final report. Use a target-paper precheck only to diagnose one such
    named failure; it is not a routine final verification pass.
  After editing `status.json`, review-surface row lists, sidecar hashes, or the
  final report, use the planner's bounded identity preflight to decide whether
  a source-record judgment-only repair or raw transition is actually needed.
  A report, dashboard, sidecar-summary, or other nonsemantic edit must reuse
  its current raw receipt. Do not rerun dashboard/source-record prechecks or
  update `review_status_export.json` merely to recreate an intermediate
  receipt. Freeze those artifacts, then run `closeout_reuse_plan.py` and
  execute only its current `next_action`. When it schedules strict closeout,
  use the exact printed argv. This targeted
  repository audit includes the DAG/final-report closeout gate; do not claim
  post-formalization completion while it reports a paper-specific missing or
  stale artifact. After a passing closeout, do not rerun the precheck or update
  an input behind the frozen receipt.
  Do not mark these sidecars as `matches` merely to clear a dashboard. If the
  Lean row is conditional while the paper row is unconditional, if a formula is
  hidden behind a source-model/certificate/library definition, or if the paper
  statement supplied to the judge is only a title or partial excerpt, record
  `mismatch` or `uncertain` and either fix the paper interface or carry the
  explicit conditional status into `status.json`, the DAG, and the final
  report. For an approved conditional row, use `resolution:
  "conditional_boundary"` instead of changing the raw `mismatch` judgment.
  The assumption precheck may count those named `conditional_premises` as
  accepted conditional-premise findings; do not treat unlisted hidden premises
  as covered by the boundary.
- Command recipe: use `--statement-precheck` or `--statement-check` for the
  beginning-of-paper target-setting pass; use `--precheck` or `--check` for an
  active full review boundary or named diagnosis. These commands are not a
  frozen-closeout batch: after inputs are frozen, use the planner and its one
  scheduled current delta. The statement-only commands intentionally ignore
  human-review counters and review-surface row-count warnings.
- Do not treat sidecar freshness as a dashboard-only convention. For completed
  papers, the planner-issued strict audit should fail when statement-translation
  or review-surface sidecars are stale, missing, uncertain, mismatched, or
  otherwise flagged. Run paper-local dashboard checks only for diagnosis, then
  re-enter through the planner before marking the paper closed.
- Assumption provenance checks can invoke Lean hidden-premise expansion even for
  papers with no explicit `Assumptions.lean` rows. In an uncached checkout this
  may be slower than a JSON export; use the export only to triage row status,
  and require the full audit/CI result before claiming there are no hidden
  premise or certificate boundaries.
- The dashboard displays the current Lean statement, the Lean-to-TeX draft, and
  the independent LLM match judgment. These LLM checks are pre-human-review
  evidence only; they do not increment `human_review.reviewed_rows`, and they
  do not replace a saved human dashboard review. Status exports include a
  `validators` ledger per row: human dashboard reviews use the saved GitHub/user
  handle with `validator_type: human`, while model/agent statement-match checks
  use the model or agent name from `statement_match_llm.json`. Keep the human
  review counter human-only; use the validator ledger for mixed human/model
  provenance, dates, judgments, stale flags, and comments.
- Do not conflate agent/formalization release readiness with human dashboard
  completion. A paper can be marked `formalized` for public status when Lean
  builds, statement/assumption validators are current, the paper-closeout audit
  passes, DAG/report evidence is current, and generated status surfaces are in
  sync, even if `0/N` saved human reviews remain. In that case the final report
  must say that human dashboard review is pending; if the user or release
  policy requires human approval, treat that as a separate promotion gate, not
  as a Lean proof gap.
- `./review-dashboard.sh` always regenerates the lightweight heuristic
  Lean-to-TeX preview from the current declarations on launch. Treat that as a
  fallback preview only. The independent statement-review workflow still
  requires stable tracked `lean_to_tex_llm.json` and `statement_match_llm.json`
  sidecars.
- On WSL2, the launcher binds broadly by default, prints localhost and any
  detected WSL guest-IP fallback, and tries to open the candidate URLs in a
  Windows browser. If one URL fails, keep the terminal running and try the
  other printed URL.
- To add `review-dashboard.sh` to existing paper folders that already have
  `PaperInterface.lean` but not the launcher yet, run:

  `python3 scripts/bootstrap_review_launchers.py --write`
- **CRITICAL MANDATE - NO HIDDEN DEFINITIONS:** A human reviewer cannot verify a theorem if its core terms are opaque references to generic library modules (e.g., `AppliedModelingLib.Statistics.priorWeightedVariance`). The `PaperInterface.lean` file MUST expose the exact mathematical formulas for the paper's definitions. Do this by defining paper-specific `abbrev`s or `def`s at the top of the interface that spell out the raw formulas exactly as they appear in the paper, and then use those local definitions in your paper-facing theorem statements or prove they equal the generic terms. A reviewer must see the actual math equations inside this single file without needing to open imported generic modules. The same rule applies recursively through library definitions: if a reusable definition carries a paper-specific displayed formula, either expose the formula in `PaperInterface.lean` or prove and review a paper-local equivalence to it. The LLM judge sidecars must check this expanded formula surface, not just the library identifier. Keep neutral proof-ledger files for theorem endpoint aliases and proof-seam coverage, not standalone proof-facing formula duplicates.
  When a paper-facing theorem depends on those formulas, state the theorem over
  the local paper definitions where practical, even if the proof immediately
  discharges the claim by `simpa` through a reusable library theorem. It is not
  enough for the formulas to appear in earlier dashboard rows while theorem
  rows still expose only opaque library terms.
  Include for each entry:
  1. the declaration name,
  2. a compact paper-style statement in comments,
  3. the key assumptions,
  4. and source location when a declaration is not a plain wrapper.
  A completed index should show the full paper-facing sequence and the final
  paper-level theorem explicitly.
- Add a structured folder `README.md` theorem-status table with columns like:
  paper theorem/definition, Lean declaration, status, file, and remaining
  assumptions/notes. Status cells MUST use the controlled vocabulary from
  `docs/STATUS.md`: `formalized`, `formalized with caveat`,
  `partially formalized`, `conditional`, `scaffold`, `not started`, or
  `not formalized`.
- **Paper Directory and Namespace Convention:** All new paper folders, modules, and internal namespaces MUST be named using the format `[AuthorInitials][2DigitYear][Descriptor]` in PascalCase (for example, `ABC12RepresentativeTitle`). This guarantees collision-proof Lean namespaces while immediately communicating the citation. All paper implementations sit within the `papers/` directory.
- **One citation per paper folder:** Do not use aggregate folders for award lists, reading lists, or multi-paper campaigns. Split them into one `[AuthorInitials][2DigitYear][Descriptor]` folder per source paper, each with its own source PDF/text cache, README, DAG, and `MainTheorems.lean`. If an aggregate module already exists, keep it only as a compatibility import or handoff note and move paper-facing status into the citation-specific folders.
- **Initial dependency plan; terminal Dependency DAG:** At the beginning of a
  paper, before deep proof work, inventory the selected source definitions,
  assumptions, and named results and record their dependency order in the
  source map and working formalization plan. Do not create terminal
  `docs/DependencyDAG.tex` or `docs/DependencyDAG.pdf` during intake. After the
  Lean-owned graph, semantic reviews, complete tracked-module elaboration, and
  proof realization are current, the closeout planner schedules
  `complete_terminal_closeout_documents`; only then render and visually inspect
  the paper-facing DAG from the final reviewed surface. This keeps early proof
  architecture explicit without repeatedly rewriting a purportedly final DAG.
  - All paper DAGs MUST `\input` the shared preamble located at `docs/tikz/dag_preamble.tex`.
  - Use the exact node styles defined in the preamble and status vocabulary:
    `formalized` uses `dag_result` (green theorem/result), `dag_lemma`
    (yellow lemma/support), or `dag_model` (blue definition/model) depending
    on node type; `formalized with caveat` uses `dag_caveat` (red diamond);
    `partially formalized` uses `dag_partial` (yellow dashed); `conditional`
    uses `dag_conditional` (orange rounded); `scaffold` uses `dag_scaffold`
    (gray dotted); and `not started`/`not formalized` use
    `dag_unformalized` (gray dashed).
  - **Green-node semantics:** A green result means the displayed paper-facing
    theorem/lemma/definition has been fully formalized under its stated Lean
    assumptions. It does not mean every lemma used in the paper's prose proof
    is independently closed. If the formal proof reaches the result by a
    different formalized path and does not need a paper lemma that remains
    partial/open, the result may be green, but the DAG must not show that
    partial/open lemma as a required solid input. Either omit that non-used
    dependency, mark it as a dashed paper-route/caveat edge, or say in the node
    or README that the paper proof input was bypassed by an alternate formal
    route.
  - If a theorem still requires an unproved assumption, certificate, or earlier
    paper lemma to obtain the paper-level statement, it is **not green**. Use
    `dag_conditional`, `dag_partial`, or `dag_caveat` as appropriate, and make
    the remaining assumption explicit in the node text and README row.
  - The whole-paper verdict must be visually consistent with the DAG. If the
    paper README, generated status tables, or final report says the paper is
    partially formalized, at least the corresponding theorem endpoints must
    appear as partial/conditional/caveated nodes. An all-green DAG is
    inconsistent with a partial paper verdict unless the partial item is not
    represented by any
    paper-facing node, in which case the DAG inventory is incomplete.
  - **Edge semantics:** Solid `dag_arrow` edges are Lean-checked dependencies in the
    formalized proof path. Dashed `dag_dashed_arrow` edges are for paper-roadmap
    dependencies, unresolved/conditional inputs, caveat links, or dependency
    paths that are not yet fully discharged. A dashed edge into a green result
    is allowed only when it is clearly non-required for the formal proof or
    explicitly documented as a bypassed paper route; otherwise the target node
    should not be green.
    For a paper marked fully `formalized`, prefer using only solid arrows in the
    final human-facing DAG unless the diagram has a local legend/note that makes
    a non-conditional dashed meaning impossible to misread.
  - **Paper-route vs formal-route discipline:** If formalization discovers that
    a paper lemma is misstated, too strong, or unnecessary for a later theorem,
    do not silently collapse the distinction. Record the source issue in the
    README during active work and in the validation report only during
    post-validation. Keep the affected paper lemma partial/caveated, and mark
    any later theorem green only if Lean proves that theorem through a fully
    formalized alternate route or through weaker assumptions already discharged.
    If the later theorem merely assumes the problematic lemma, it is
    conditional/caveated, not green.
  - **DAG status sanity check before committing:** Reread the rendered DAG as a
    skeptical reviewer would. Every source-named proposition, theorem,
    corollary, and major definition from the paper inventory must appear; do
    not replace a missing named result with a broad topical or implementation
    bucket. Source-inventory helper formula rows, source parameters, and
    algorithm-condition rows may be grouped under the relevant definition,
    algorithm, theorem, or proposition node when they are not standalone paper
    theorems; the final report or audit note should say so when the grouping is
    not obvious. A green node that is fed by a caveat, partial result, or
    conditional bridge must either state a theorem whose Lean assumptions
    visibly include that limitation, or the incoming edge must be dashed and
    clearly non-required. If the downstream source theorem is still only proved
    through certificates, finite analogues, positive-base restrictions,
    two-sided support, or other undisclosed hypotheses, mark the downstream
    theorem conditional/partial rather than green.
  - **Do not use scope notes as theorem inventory:** A prose scope note may
    clarify a diagram, but it must never be the only place where named source
    results appear. Every named Definition, Lemma, Proposition, Theorem,
    Corollary, and appendix result in `audit/paper_statement_map.json` or the source
    inventory must be represented by a visible DAG node. Grouping is allowed
    for tightly related results, but the grouped node header must explicitly
    name the included source results, for example `\textbf{Cor. C.1-C.2;
    Lemmas C.6-C.8}`. At closeout, compare the source inventory against DAG
    node headers and treat any result that appears only in a scope note as
    missing from the DAG.
  - **Blueprint/source-map consistency:** Treat the DAG as a human-readable
    view over the source-block map, not as the source of truth. Before closeout
    or any public-facing handoff, cross-check three inventories: source-block
    map, `PaperInterface.lean`/review dashboard rows, and DAG nodes/edges. Every
    source-named paper result should have exactly one paper-facing row or an
    explicit reason for omission, every paper-facing row should trace back to a
    source block, and every required source dependency should either appear as
    an edge or be documented as an intentionally omitted redundant edge. If a
    script or table can generate the node/edge inventory, prefer that over
    maintaining duplicate hand-written lists; still inspect the rendered DAG for
    readability.
- **DAG Formatting and Clarity Mandates:**
  - **Visual Iteration Requirement:** After every substantive DAG edit, render the DAG, inspect the visual output, and keep adjusting layout until you can explicitly confirm that it looks clean with no box, legend, note, edge, or label overlap. Do not claim the DAG is done if you have not visually checked it or if any overlap remains.
  - **Minimum Node Spacing:** Keep visible whitespace between neighboring DAG
    nodes. As a default floor, leave at least about `0.6cm` between node
    bounding boxes and use larger gaps for dense text boxes, long labels, or
    high-traffic edge lanes. If arrows must pass between nodes, reserve a clear
    routing lane rather than squeezing the arrow through text or nearly touching
    boxes.
  - **Stable Topology Requirement:** The initial DAG should contain the paper's full named-result structure: all named Definitions, Lemmas, Propositions, Theorems, Corollaries, and appendix results, with dependency arrows reflecting the paper proof architecture. After that initial roadmap is created, routine progress updates should normally change only node status/style/text, not add new boxes or arrows. Add or remove boxes/arrows only when the initial named-result inventory was incomplete or a genuine paper dependency was discovered to be missing/wrong; if topology changes, rerender and re-check for overlap.
  - The DAG must encode formalization status and node type explicitly by using the preamble styles.
  - **Node Content:** Node text MUST begin with a bolded header indicating the Theorem/Lemma/Definition name and, if available, its location in the paper (e.g., `\textbf{Theorem 1 (Section 4)} \\ Description` or `\textbf{Lemma 12 (App. E)} \\ Symmetry reduction`). Provide a brief, readable description on the following line(s).
    Do not include internal source-TeX labels, Lean declaration names, helper
    theorem names, or citation keys in DAG node text. Labels such as
    `thm:...`, `lem:...`, and `source_...` belong in `PaperInterface.lean`,
    README rows, audit ledgers, or final reports, not in the visual DAG.
    Before accepting a DAG, mechanically scan the node text for `\texttt`,
    underscores, CamelCase record/theorem identifiers, and Lean-style prefixes
    such as `theorem1_`; any remaining instance must be paper notation rather
    than an implementation name.
    Treat this as a closeout audit requirement, not a cosmetic preference. If
    the DAG communicates through Lean function names, certificate type names, or
    implementation route labels, the paper is not public-ready until the DAG is
    rewritten in source-paper language and rerendered.
  - **Closed theorem text stays short:** Once a theorem is closed, the theorem
    node should describe the source theorem's statement, not the Lean proof
    machinery that closed it. Do not fill a closed theorem box with internal
    helper names, certificate layers, construction details, or a list of every
    bridge lemma. Also omit old compatibility/sufficient routes and alternate
    proof attempts from the visual node. Put those details in private proof
    notes, proof comments, or the final report during post-validation.
    Include the actual source-facing conclusion or a faithful short formula
    summary in the DAG node itself so a human can recognize the paper result
    without opening the Lean file. For example, a closed Gaussian lemma node
    should say that the posterior estimate has the displayed weighted-mean
    formula and normal law, not merely that "Gaussian algebra was proved."
  - **Source notes are not DAG caveats:** Do not put source-inventory,
    source-version, or source-convention explanations into the DAG as large
    note boxes when the paper result is otherwise closed. The visual DAG should
    show source-facing theorem nodes, reusable/library dependencies, and genuine
    unresolved boundaries. Put source-version crosswalks, convention notes,
    proof-route commentary, and source-inventory details in
    `FINAL_VALIDATION_REPORT.md`, `docs/POST_FORMALIZATION_AUDIT.md`, status files,
    or short captions instead. A DAG note box can make a closed result look
    caveated, so use one only when it identifies an actual remaining assumption,
    source gap, or unresolved proof boundary.
  - **Keep theorem families together:** Parts of the same source theorem
    (`Theorem 2(i)`, `Theorem 2(ii)`, `Theorem 2(iii)`) should be visually
    grouped in the same column, row, or labeled cluster. Do not scatter theorem
    parts around auxiliary boxes in a way that makes the source theorem hard to
    read as one result.
  - **Named results are mandatory; auxiliaries are subordinate:** Every named
    paper Definition/Lemma/Proposition/Theorem/Corollary must appear unless the
    source inventory confirms there are none of that kind. Paper-unnamed
    implementation layers, reusable Lean primitives, certificate packages,
    feature-map plumbing, and finite analogues should usually not be primary
    DAG nodes. Add them only when they are the exact remaining caveat or are
    needed to make the named-result dependency legible, and keep them visually
    subordinate to the source-named theorem/lemma nodes.
  - **Legend:** You MUST include a Legend using the shared helper macro from the preamble, e.g., `\daglegend{(legRes)(legLem)(legDef)(legOpen)}{Legend}`. Place legend nodes concisely at the top. For caveat entries inside the legend, use `dag_caveat_legend` rather than combining `dag_caveat` with `dag_template_legend`; the full-size red diamond is for graph nodes and makes the legend oversized.
  - **Rendered inspection is required:** After changing a DAG, render the PDF
    and inspect an image conversion. Check for legend/source-node overlap, arrow
    collisions that obscure labels, stale caveat/open-boundary styling, and
    Lean declaration names in node text. Do not rely on successful LaTeX
    compilation as proof that the DAG is human-facing.
  - **Edge Routing (No Overlaps):** Use explicit positioning (`node distance`, `below=of`, `right=of`, `xshift`, `yshift`) carefully. **Prefer straight paths or simple orthogonal routing (`|-`, `-|`) whenever possible without overlap.** Use a column-based layout (the preamble standardizes horizontal spacing at `3cm` or `4cm` depending on the specific diagram needs) to ensure paths are clear and text boxes do not collide. Only use complex curves (`to[out=..., in=...]`) or bends when absolutely necessary to route around an immediate obstacle. Use `dag_arrow` and `dag_dashed_arrow` from the preamble for styling.
  - For dense paper DAGs, prioritize a visually auditable named-result topology
    over drawing every redundant instantiation arrow. If a theorem node already
    states that it satisfies particular definitions or conditions, it is
    acceptable to omit duplicate long cross-edges when those edges would create
    text or box overlap; keep the exact status and remaining assumptions in the
    node text and `status.json`/final report.
- Keep the DAG updated after every major paper update (for example: a named
  paper theorem/lemma closed, a dependency refactor that changes proof flow, or
  a status transition in the controlled status/DAG vocabulary).
- Keep the paper DAG paper-facing. Its primary nodes should be the source's
  named definitions, lemmas, propositions, theorems, and corollaries. Do not
  replace a source theorem with internal implementation layers such as finite
  analogues, certificate packages, or continuous instantiation steps unless the
  source itself is organized that way. Put those engineering layers in private
  proof notes, proof comments, or the final report, and use the DAG to show how the
  paper's named results relate and which of them are formalized, conditional,
  caveated, or open.
  Do not include empirical, numerical, simulation, benchmark, data-study, or
  reproducibility-artifact sections as DAG nodes. The DAG is a proof/theorem
  roadmap, not a full paper outline. If the source paper has a substantial
  empirical or numerical section, mention that scope explicitly in the README or
  final validation/formalization report and say it is not a Lean theorem target.
  If the source has only a few named results, keep the DAG correspondingly
  simple; do not compensate by adding a large set of paper-unnamed Lean helper
  nodes.
  Even when the working proof closes a finite analogue first, the DAG should
  still show the corresponding source theorem node with the honest paper-level
  status; finite versions belong in Lean helper names, README rows, or proof
  comments, not as replacement DAG nodes.
- If a finite analogue, certificate endpoint, or regularity-heavy wrapper is
  the current strongest Lean result, do not mark the source theorem
  `formalized with caveat` just because the wrapper compiles. Use `conditional`
  for the wrapper and `partially formalized` for the source theorem until the
  extra hypotheses are derived from the paper's primitive assumptions.
- A downstream theorem node may use the green `dag_result` style only when its
  paper-facing statement is closed without remaining paper assumptions. If Lean
  currently proves only wrappers conditional on certificates, no-gap hypotheses,
  selected-BFS assumptions, or witness existence, use `dag_conditional` for the
  wrapper and add a separate `dag_unformalized` node for the full paper theorem.
  The node text must name the exact open certificates or witnesses.
- For probabilistic papers, distinguish the source's random-variable/probability
  statement from any density, CDF, or integral representation used in the proof.
  If Lean closes the integral or closed-form layer but has not yet proved the
  measure-theoretic bridge from `Pr[...]` to that integral (for example, an
  independence/Fubini/density derivation), keep the theorem conditional in
  `status.json`, the DAG, and the final report, and explicitly name the
  probability-to-integral bridge that remains.
- For stochastic-process convergence results, do not translate a source proof
  that concludes "with probability 1" into a deterministic per-path theorem
  unless the paper explicitly proves the deterministic statement. If Lean has
  only the post-concentration skeleton, expose the remaining boundary as the
  exact concentration/escape theorem (for example, Hoeffding plus almost-sure
  escape), not as a hidden drift or direction-field field.
- For sequential weighted without-replacement or "first distinct draw" models,
  load `references/proof-foundations-probability.md`; for matching-specific
  weighted-list details, also load `references/proof-markets-social-choice.md`.
- When a proof step invokes an external cited analytic theorem that is not in
  Mathlib, encode that input as a named paper-local hypothesis or definition
  (for example, a `Sampford...Bound` assumption), prove the source's downstream
  reduction from that exact hypothesis, and keep `status.json`/DAG conditional
  until the cited theorem itself or an acceptable imported library theorem is
  formalized.
- When such a cited theorem is later formalized locally, immediately update
  `status.json` and the DAG to remove that exact assumption while preserving
  any broader remaining bridge. For example, if a scalar density/integral layer is now
  unconditional but the source theorem is still a probability statement, mark
  the scalar layer as closed and keep only the probability-to-integral bridge as
  the theorem-level blocker.
- In this repository's public `papers/[Paper]/docs/DependencyDAG.tex` layout,
  the shared preamble input is
  `\input{../../../docs/tikz/dag_preamble.tex}`. Render from the paper `docs/`
  folder (`cd papers/<Paper>/docs && latexmk -pdf DependencyDAG.tex`) or use
  `scripts/compile_dependency_dags.sh`; running `latexmk
  papers/<Paper>/docs/DependencyDAG.tex` from the repo root resolves the
  preamble relative to the wrong directory and wastes a build cycle. Verify the
  DAG renders after changing the preamble path or moving a paper folder.
- In restricted environments, MiKTeX may finish TeX output and then fail while
  writing its user cache with `Failed to create stream fd: Operation not
  permitted`. Do not report that as a clean render. Re-run the same focused
  `latexmk -g -pdf` command with the required cache-write permission, then
  distinguish any real TeX error from the sandbox-only cache failure in the
  validation receipt.
- Use the shared DAG header helpers instead of manual coordinate shifts:
  `\dagPaperMetadata` for the top-left source block,
  `\dagPaperLegendRightOfMetadata{...}` for the legend row to its right, and
  `\begin{dagPaperBody}...\end{dagPaperBody}` for relative-positioned graph
  nodes below the header. Avoid the old
  `dagPaperMetadata.north east -| 0,0` pattern; it places the legend back at
  the page origin and causes overlap. After rendering, check the standalone
  crop: if graph nodes extend left of the metadata block, add a local
  `xshift` inside `dagPaperBody`; the metadata should remain the visual
  top-left anchor, with the legend to its right and the graph below.
- If a theorem is only conditional, the private README/plan and public
  `status.json`/final report must name the exact certificate or assumption
  declaration that remains. Do not describe it vaguely as "technical details".
- Distinguish certificate interfaces from certificate assumptions. A
  paper-local certificate/interface structure is just a formal proof boundary:
  it is an **assumption** only when the paper-facing theorem still takes an
  inhabitant or hypothesis as an explicit input. It is **discharged** when the
  paper folder constructs the witness/certificate and the final paper-facing
  wrapper applies it internally. `status.json`/DAG/final-report status must say which case holds.
  Auxiliary explicit-input variants are fine, but they must not make the source
  theorem look closed unless there is also a closed wrapper that no longer
  exposes those inputs.
- Use source-numbered paper declaration names only for statements that are
  source-faithful. If Lean proves an auxiliary finite analogue, certificate
  interface, or deliberately weakened bridge, name it as an auxiliary
  declaration (for example `paper_aux_*` or a name that explicitly says
  `finite_analogue`) and mark the source theorem as partial/open in
  `status.json` and the DAG.
- The private paper `README.md` or `FORMALIZATION_PLAN.md` is the live status
  ledger and handoff document for partial progress. A
  `FINAL_VALIDATION_REPORT.md` is not a handoff note; it is
  the concise human assessment created only when making a final claim
  about a paper, or when the user explicitly asks for post-validation of a
  completed proof phase. It must answer whether the paper is formalized, what
  additional assumptions were needed, whether mistakes were found, and whether
  the Lean proof followed the paper strategy or used a different route. Keep it
  short and paper-facing; move long operational ledgers, status-report
  transcripts, source-line inventories, and verbose boundary details to
  `docs/POST_FORMALIZATION_AUDIT.md`, private source-audit/handoff notes,
  a neutral proof-ledger file, or the private README/plan as appropriate. When
  creating or updating a final validation report, also update the paper README,
  `docs/PAPER_STATUS.md`, and the website status table so the public entry
  points match the paper-local verdict.
- For paper-specific status questions, `status.json`,
  `docs/DependencyDAG.tex`, paper-facing theorem files, private status notes
  when present, and current targeted Lean build are the source of truth. Older
  author-wide notes or campaign reports are historical/secondary and may be
  stale; never use them to override paper-local status/DAG plus successful
  build.
- Report paper status by evidence layer rather than collapsing all green Lean
  into one verdict: (1) internal arithmetic/model lemmas, (2) constructed
  replay or executor theorem, (3) success and failure/completeness contract,
  (4) direct `PaperInterface.lean` export and import-path build, (5) current
  semantic/audit metadata and human review, and (6) empirical replay when the
  paper makes data-derived claims. A compiling implementation module is internal
  progress until the source-shaped statement is exported from
  `PaperInterface.lean`; say explicitly when `status.json` or audit sidecars lag
  the code checkpoint. Do not use an invented percentage to hide these distinct
  boundaries.
- **Post-paper audit protocol:** Before claiming that a paper is done, create
  or update a paper-local final audit. Do this even if status, DAG, report,
  or successful build already exists; those artifacts are not a substitute for
  the importable audit ledger. The audit must check all four artifacts:
  the source paper via local ignored cache or source URL, `status.json`,
  `docs/DependencyDAG.tex`, and the
  paper-facing Lean file(s).
  Before running this closeout, refresh the active workflow instructions from
  the repository you are publishing from, especially after another agent or
  recent pull changed audit scripts or skills. Compare the prior receipt's
  canonical structured review-protocol digest: prose, refactors, diagnostics,
  and performance changes do not reopen it, while a changed retained semantic
  audit version does. If
  the current gate requires an independent holistic source audit, source-record
  sidecar, rendered-DAG inspection note, or other paper-local artifact, create
  that artifact and rerun the targeted closeout audit before opening or updating
  a public PR.
  - Source check: search the cached text for every named paper `Definition`,
    `Lemma`, `Proposition`, `Theorem`, and `Corollary` using a concrete search
    such as `rg -n "THEOREM|Theorem|LEMMA|Lemma|COROLLARY|Corollary|PROPOSITION|Proposition|DEFINITION|Definition" <cached-text>`.
    If a public checkout omits the cache, recreate an ignored local extraction
    from the recorded source URL before the audit rather than committing the
    generated paper text. List the source line or section in the audit report,
    and say explicitly if no numbered definitions/propositions were found.
  - Status check: every named source item must have a row using the controlled
    status vocabulary from `docs/STATUS.md`, and every non-`formalized` row must
    name the exact remaining declaration, certificate, or reason for deferral.
  - DAG check: every named result node must have a style consistent with the
    status row. Solid arrows mean Lean-checked dependencies; dashed arrows
    mean paper-route/context links or unresolved dependencies. A green node with
    a dashed incoming edge is allowed only if the status/audit says the dashed
    edge is not required by the formal proof.
  - Lean check: create a compiling neutral proof ledger such as
    `ProofLedger.lean` or an equivalent ledger
    in the paper folder. It must be importable from the paper root module and
    expose one source-numbered audit theorem per final paper endpoint. Prefer
    raw assumption lists in the audit theorem signatures; if a paper-model
    structure is used, the docstring must state the exact paper convention that
    the structure packages. The theorem body should be a thin call to the
    paper-facing declaration, so a human can inspect the endpoint in one file.
    Do not mark the paper complete until the root module imports this ledger.
  - One-stop endpoint check: for each main theorem, expose at least one audit
    wrapper whose conclusion is the paper-level result a human expects to read,
    not only internal component lemmas. If the proof naturally produces an iff,
    certificate, or witness, also add direct wrappers such as named-witness
    existence, `∃!` uniqueness, bundled conclusion endpoints, and componentwise
    equality statements for opaque structures. For dynamic games or mechanisms
    with named strategies/witnesses, also add pointwise behavior equivalences,
    pairwise uniqueness/equality consequences, named-witness outcome wrappers,
    and any useful generic certificate constructors plus the generic theorem
    conclusion obtained from those constructors. Keep assumptions/certificates
    in the signature only when they are genuine remaining paper obligations, and
    name them explicitly in `status.json` and the DAG.
  - Report check: when the closeout planner schedules
    `complete_terminal_closeout_documents`, create or update
    `FINAL_VALIDATION_REPORT.md` in the paper folder. It must state whether the paper is formalized, the exact source
    version, the named-result inventory, any deliberate model conventions or
    proof-route deviations, the commands run, and links to status, DAG, and
    audit ledger. If the report needs detailed source line mappings, helper
    theorem inventories, source-facing surface listings, or important-boundary
    implementation notes to preserve context, move those details into
    `docs/POST_FORMALIZATION_AUDIT.md` or private audit notes and summarize only the
    human-relevant conclusion in the final report.
  - Build check: after updating the audit, elaborate every tracked paper-owned
    module through `private_paper_checkpoint.py` and
    render the DAG from the paper folder. Also run a placeholder grep over the
    claimed paper and library files, a stale-status grep over `status.json`/DAG/
    final report, and `git diff --check`. Do not mark the audit complete until
    all required commands succeed.
- **Post-formalization library elevation pass:** Once a paper theorem closes,
  scan the proof for reusable primitives, proof results, and proof techniques
  that belong in `AppliedModelingLib` rather than the paper namespace. Good candidates
  include model-neutral definitions, algorithm trace APIs, invariants,
  side-symmetry lemmas, finite-cardinality bridges, monotonicity/termination
  facts, reusable certificate constructors, common proof decompositions, and
  tactic patterns that would help another paper. Run this pass deliberately as
  part of closeout: elevate stable reusable APIs/results before final validation
  when the extraction is local and low-risk. If the extraction would require a
  broader naming/API design pass, leave the paper-facing wrapper in place and
  record concrete migration candidates, likely destination modules, and the
  proof technique worth preserving in the final report.
- In a proof campaign, prioritize closing the active proof seam over routine
  documentation churn. Update paper-local plans, reports, and status only at a
  material source-scope or assumption repair, named-result closure, handoff,
  paper transition, closeout, or explicit user request. Do not interrupt proof
  work merely because time elapsed. At those boundaries, do not leave a paper
  with stale `scaffold`, `conditional`, or remaining-assumption text: either
  close the seam or record the exact blocker and next theorem to attack.
- Do not update the author-wide formalization report file
  `docs/GARG_AUTHOR_FORMALIZATION_REPORT.md` during routine intermediate work.
  Update it only when the paper is finished, when stopping, or when you are
  moving on to another paper.
- Commit at paper-scale checkpoints, not every small lemma. Prefer committing
  when a named theorem/proposition/lemma from the paper is proven or when
  moving on from a paper; otherwise keep related intermediate proof work
  together in the working tree. A local commit does not automatically require a
  rebase or generated-status refresh. A routine private proof checkpoint can be
  pushed without rebasing first; do not insert a rebase just because you are
  about to push. Rebase only at major milestones such as when a paper is
  finished, before publication/PR work, after meaningful public library/API
  changes, or on explicit request.
- Prioritize finishing the theorem over creating frequent checkpoints. Once the
  finite scaffold is stable, spend effort on the hard remaining bridge rather
  than packaging every helper lemma as a separate commit or documentation pass.
  Commit only when a substantial named result is genuinely closed, when moving
  papers, or when the user explicitly asks for a checkpoint.
- When a finite version of a theorem is the requested milestone, finish the
  finite public endpoint first and validate it through the paper interface.
  Only then refresh the paper-local status source, README/proof-plan/final
  report, DAG source and rendered PDF, and any skill lessons, then make one
  milestone commit and push. The documentation should state which finite
  hypotheses remain and should not imply the infinite or unconstrained source
  theorem is closed.
- Detailed lemmas may live in many files, but the central theorem file should be
  the stable public interface for that paper.

### 1.4 Context Budget and Resume Protocol

Resume from the current public interface, not from the commit history. For long
formalization campaigns, the fastest reliable map is the status docs, the paper
README theorem table, the paper-facing theorem file, and targeted declaration
search.

- Start every resumed task with `git status --short --branch`, then read the
  current repo/paper status note and the paper folder README. Protect unrelated
  dirty files, and let the documented current seam define the first theorem to
  inspect.
- If shell startup prints `Failed to create stream fd: Operation not permitted`
  before otherwise successful command output, treat it as an Ubuntu
  `im-config`/`systemd-cat` login-shell warning, not a repo failure. On Ubuntu
  images this can come from `/etc/profile.d/im-config_wayland.sh` sourcing
  `/usr/share/im-config/initializer`, whose `systemd-cat` logging fails under
  sandboxed non-systemd sessions. Confirm with `bash -l -c true` if needed.
  Configure Codex once at the user level with
  `allow_login_shell = false` in `~/.codex/config.toml`; current Codex versions
  then default omitted `login` fields to non-login and reject `login:true`.
  A session already running when the setting changes must still pass
  `login:false` explicitly. Do not patch `im-config` or spend proof-debugging
  time on this environment warning.
- Use a five-minute resume path before opening large Lean files: read the
  paper handoff/README current-target section, `rg` the exact public wrapper
  and remaining assumption names, inspect only those theorem neighborhoods, and
  run the targeted build if the status is uncertain. This usually recovers
  context faster than reading thousands of lines or replaying chat history.
- Use targeted `rg` searches for the strongest paper-facing wrapper, the exact
  remaining certificate/assumption named in the README, and the internal lemma
  that feeds it. Avoid scanning broad proof files or docs until those anchors are
  identified.
- For huge diffs or dirty worktrees, use path-limited `git diff --stat`,
  `git status --short -- <paths>`, and narrow `git diff -- <paths>` first. Do
  not print whole-repo diffs unless the task is explicitly repository-wide.
- Treat successfully compiling declarations and current status tables as the
  source of truth for "what is done." Use commit history only for provenance,
  rename recovery, or checking what changed since a known checkpoint. If history
  is needed, keep it bounded: `git log --oneline -n 10`, `git show --stat
  <recent>`, or a narrow path-limited diff. Do not use open-ended commit
  archaeology as the default way to regain context.
- After a long interruption or a user asks whether anything was lost, perform
  the three cheap checks: worktree status, targeted declaration search, and a
  targeted `lake build <active-module>`. Do not replay old proof search unless
  those checks reveal a real gap.
- When reading context, batch independent cheap shell reads with parallel tool
  calls, but keep each output scoped: `sed` around named declarations, `rg -n`
  for exact theorem names, and `git diff --stat` before full diffs. Prefer one
  well-sized context read over many failed micro-reads when preparing an edit.
- Before saying a paper is "done" or "fully formalized," perform a paper-local
  validation pass: read `status.json` and any private theorem-status notes,
  inspect the DAG
  status for the named main results, check the paper-facing theorem file for
  the strongest closed wrappers, run the targeted `lake build <module>`, and
  search only the target Lean files for real proof placeholders such as
  `sorry`, `admit`, or `axiom`, for example
  `rg -n "sorry|admit|axiom" papers/<Paper> --glob '*.lean'`. Ignore cached
  PDF text, markdown prose, skill files, and comments when doing placeholder
  searches; otherwise ordinary instructional text creates false positives.
  If auxiliary certificate/BFS/interface theorems still take explicit inputs,
  verify that the final source wrapper does not expose them before calling the
  source theorem closed.
- After closing a paper seam, run a stale-status grep over `status.json`, the
  DAG, private status notes when present, and, during post-validation, final
  report before committing, for example:
  `rg "Previous status|not formalized|partially formalized|conditional|none for|source wrappers partial" papers/<Paper>`.
  Stale ledger wording is often the only remaining "gap" after Lean is green.
  Keep legend entries if the template includes them, but no actual paper node
  should advertise an obsolete status.
- Before editing, state the one active seam in local notes or the handoff doc:
  public theorem wrapper, internal lemma/certificate being attacked, exact
  remaining assumption, and the build command that validates the slice.
- Before building a large helper tower, write or locate the paper-facing wrapper
  and the exact bridge theorem that would close it. If the bridge is too hard,
  make the helper an explicitly named auxiliary result and record the bridge as
  the remaining seam; do not let a reduced analogue masquerade as the source
  theorem.
- Do not revisit closed layers first. Search for the strongest current endpoint
  and the precise "remaining" text, then work on that next bridge. In this repo,
  `status.json`, private status notes, and aggregate status docs should say
  which algebra, symmetry, probability, or model-integration layers are already
  closed.
- When stopping or moving papers, document "do not redo" information: closed
  theorem layers, the current endpoint, the next bridge, known traps, and the
  last passing build command. This prevents future agents from spending tokens
  re-deriving the same orientation.
- If the user asks to stop soon, first pick a named theorem/lemma endpoint that
  can be made green quickly, finish that wrapper, and run the targeted module
  plus paper-root builds. Only then update `status.json`, the DAG, and private
  handoff notes. Do not
  start a fresh hard proof branch just before documenting a handoff.
- Before committing a pause handoff, expose any newly closed internal theorem
  through the paper-facing wrapper layer if it is part of the source proof
  audit. Otherwise the next agent has to rediscover that the lemma exists
  internally. Update `status.json`, the DAG, and private status notes from
  those public wrapper names rather than from private proof-local names.

### 1.5 Workflow

1. Orient before editing.
   Read the repo README, roadmap, architecture notes, and paper-specific
   handoff documents. Identify the public theorem target and the smallest local
   lemma that moves it forward.
   For a brand-new paper, first establish the source coverage mode, source-only
   named-presentation inventory, compact `PaperInterface.lean` skeleton,
   source assumptions/dependencies, and the next proof seam. A full dependency
   DAG is useful at a handoff or closeout, but is not a gate before the first
   proof step and should not be repeatedly updated during ordinary proof work.
   Keep the source-block map limited to source presentation, location,
   dependencies, target signature, and proof status. Use it to select the next
   proof seam, not to substitute planning for proof progress.
   Before drafting that skeleton, classify every presentation by semantic role.
   Use one complete Spec plus a distinct endpoint for each result and the
   actual declaration for each definition, algorithm, model, assumption, or
   condition. Then run the non-certifying semantic-architecture pre-pass in the
   main skill and repair role/category errors and source-model bypasses before
   intake freeze or evidence issuance.

2. Context Efficiency vs. Edit Accuracy (File Reading Strategy).
   Do not over-optimize context limits by reading tiny chunks of files (e.g., using `sed` to read 15-20 lines) if you are about to use the `replace` tool. Micro-reading frequently drops necessary surrounding whitespace or context, causing the `replace` tool to fail repeatedly with "0 occurrences found". The cost of spinning in a multi-turn failure loop is far higher than the cost of reading the entire file once. Use `read_file` to ingest small-to-medium files completely, or use `grep -C 20` to get substantial context, ensuring you capture exact, copy-pasteable blocks for your `old_string`.

3. Stabilize the build first.
   Run targeted `lake build <module>` commands before making broad changes. Fix
   dependency, import, or cache problems before interpreting downstream proof
   errors.
   During proof work, use a compiler-guided repair loop: make one candidate
   statement or proof edit, run the narrowest Lean check that exercises it,
   inspect the first concrete error and goal state, then repair locally under
   the fixed paper-facing signature whenever the source translation is already
   correct. If the same failure recurs, split out the missing lemma, retrieve a
   similar proof/API, or record the failed route in the handoff rather than
   repeatedly changing the public theorem target.

3. Choose the model level that closes the theorem fastest.
   EC papers often have useful finite entry points: finite agents, items,
   actions, rankings, allocations, mechanisms, PMFs, and finite sums. Use those
   when they expose the key combinatorics cleanly. But do not force a finite
   analogue first if the paper theorem is genuinely continuous, stochastic, or
   measure-theoretic and the direct source statement is shorter, more faithful,
   or necessary to finish the paper. In that case, state the continuous objects
   directly: measures, Bochner or Lebesgue integrals, almost-everywhere claims,
   densities, stopping/renewal assumptions, CTMC transition probabilities, and
   long-run reward limits should be first-class Lean targets rather than
   deferred prose. For proof-specific tactics, load the relevant reference in
   Component 2 instead of putting those techniques in this main workflow file.
   The priority order is: close the paper-facing theorem faithfully, choose the
   quickest model level that makes the proof work, and extract reusable tools
   only when they clearly help this proof or a near-term second paper. A finite
   scaffold is a tool, not a required first phase.

4. Extract shared primitives into the main library.
   Reusable finite expectations, policies, allocations, valuations, mechanisms,
   rankings, conditional expectations, graph lemmas, and sign lemmas should live
   in main library modules, not buried in one paper folder. Keep only
   paper-specific definitions and wrappers in paper namespaces.
   Build the reusable abstraction at the point it accelerates the active paper:
   do not spend a session polishing general infrastructure whose first real use
   is still speculative.

5. Make every paper pay library rent.
   When a proof needs a reusable object, add the general version once and reuse
   it. Avoid parallel versions of allocations, randomized policies, mechanisms,
   expectations, graph reachability, or inequality certificates in each paper
   folder.

6. Prefer compileable partial progress.
   The statement-first intake phase deliberately uses `by sorry` so exact paper
   targets can be elaborated, semantically audited, and frozen before proof
   engineering. After that freeze, if the full main theorem is not ready, add
   definitions, local invariants, certificate structures, and conditional
   theorems that compile; do not add new proof holes outside the audited
   skeleton.
   Treat this as a checkpoint discipline, not a destination. After a
   conditional theorem compiles, the next default task is to discharge its
   certificate/hypothesis inputs by deriving them from the source model or to
   route true paper assumptions through `Assumptions.lean` and the
   assumption judge. Do not keep building more conditional wrappers around the
   same open premise.
   If Lean exposes that a paper lemma is false as stated, do not silently weaken
   the paper-facing declaration to make progress. State the paper version, prove
   the strongest true nearby lemma separately, and add a small compiled
   counterexample theorem when possible. Mark the README/status row as a
   validation issue with the exact failed hypothesis or inequality.

7. Document exact theorem seams.
   When stopping mid-proof, record the module, theorem, assumptions still
   missing, commands run, the next lemma to prove, and any closed layers that
   should not be revisited. Future agents should not have to rediscover the
   proof state. Include useful failed proof attempts, Lean error patterns, and
   successful repair lemmas when they would help future retrieval or prevent the
   same dead end. If a paper is plausibly beyond the current model's effective
   proof-search capacity, make that explicit in the private handoff and public
   status:
   name the reduced target, record failed/counterexample-search evidence, and
   mark it as a future stronger-model pickup instead of leaving an ambiguous
   stale conditional theorem. Also update the paper README, `docs/PAPER_STATUS.md`,
   and the website status table in the same pass so the public project front
   door matches the paper-local pause verdict.

8. Verify narrowly, then broadly.
   First build the touched module. Then build the parent paper root. Run full
   `lake build` for release/integration checks.

9. For long-running branches with many sessions, avoid broad history archaeology.
   A fast resume loop is: (`git status --short --branch`), inspect the paper
   README + paper-facing theorem file, verify the latest build command in the handoff
   doc, and only then do targeted `rg`/`lake build` steps.

10. For author-wide paper campaigns, maintain a running markdown report.
   Record every paper screened, the source version, venue, author-position
   decision, theorem-status decision, declarations added, blocker if any, build
   command, and commit hash. Do not advance from a paper until either its main
   theorem interface is closed without `sorry`/conditional assumptions or the
   report states the precise bug/too-hard reason blocking faithful
   formalization.
   Update this report only at paper completion, at explicit handoff boundaries,
   or when stopping/resuming across papers.

### 1.6 Build Hygiene and Source Control Safety

**CRITICAL MANDATE - CONCURRENT AGENT SAFETY:**
- Assume there could be other agents or human users simultaneously working on different files within the same repository.
- **NEVER** use aggressive global resets like `git reset --hard`, `git clean -fd`, or `git checkout .` unless explicitly instructed to do so by the user. These commands will permanently destroy work being done by other concurrent agents.
- **NEVER** use `git reset` of any kind in a dirty shared worktree unless the
  user explicitly requests that exact operation. Even soft or mixed resets can
  disturb other agents' staged work or branch position. Use scoped `git add`,
  path-limited commits, or follow-up corrective commits instead.
- **NEVER** use `git restore`, `git restore --staged`, checkout-based file
  rewinds, or index restaging as a recovery move in a dirty shared worktree.
  If staging or commit scope is wrong, leave the index alone and recover with a
  follow-up commit or explicit coordination. Only use ordinary scoped
  `git add path...` for files you intentionally edited.
- Use the native `apply_patch` editing tool for manual source edits. Do not
  invoke `apply_patch` through a shell command, and do not use heredoc/sed/perl
  write tricks for ordinary Lean, README, or skill edits; those paths obscure
  exactly what changed and are easy to misapply in a dirty multi-agent tree.
- Before committing, inspect `git status --short` and `git diff --name-only`.
  Stage explicit paths only, normally the active paper files plus any intended
  skill/docs updates. Do not stage unrelated dirty dependency repairs made only
  to let a local build proceed unless you intentionally take ownership of that
  library change.

- Lake reuses `.olean` artifacts when sources, imports, Lean version, and
  dependency artifacts are unchanged.
- After changing `lean-toolchain`, `lakefile.toml`, or dependency revisions,
  expect substantial rebuilds.
- If generated artifacts produce invalid headers or impossible import errors,
  clean generated dependency outputs and rebuild rather than patching random
  downstream files.
- If a direct module build succeeds but downstream imports still report that
  newly-added declarations are unknown, suspect a stale module artifact before
  doing proof search. Confirm with a cheap declaration check such as
  `strings .lake/build/lib/lean/Path/To/Module.ilean | rg declarationName`.
  If it is stale, remove only that module's generated artifacts
  (`.olean`, `.ilean`, matching `.hash` files, and the corresponding `.c`/hash
  under `.lake/build/ir/`) and rebuild the target module. Avoid broad
  `lake clean` in concurrent-agent worktrees because it wastes time and can
  invalidate other agents' caches.
- If a long build is interrupted, already-finished modules usually remain
  cached; rerunning resumes from remaining work.
- Do not start a long build of a downstream module when you are about to edit
  one of its dependencies. Build the touched dependency first, then the paper
  root after the dependency is stable.
- Do not infer that downstream files are broken until the direct imported module
  builds.
- If a focused paper build fails because an unrelated imported module is dirty,
  first ask whether a narrower import would avoid that dependency. If a small
  local repair to the unrelated file is unavoidable to continue the build,
  document it in the handoff and leave it unstaged unless the active paper
  truly depends on that repaired theorem.
- For deterministic heartbeat failures in one large proof, first replace heavy
  terminal `linarith`/`nlinarith`/`ring` calls with explicit named inequalities
  and a short contradiction chain. If the proof is still too large, use
  `set_option maxHeartbeats <n> in` scoped to that single declaration with a
  one-line comment explaining why. Do not raise repository-wide heartbeat
  limits or linter settings to mask one theorem.
- Existing warnings are not build failures unless the user asks for lint cleanup
  or the project enforces warning-free builds.
- `declaration uses sorry` messages are proof-debt warnings, not style-linter
  noise. Do not add lakefile options to hide them; either close the `sorry`s or
  keep build output scoped/tail-filtered so repeated known warnings do not fill
  the context window. During statement-first intake, record exactly which
  audited skeleton rows own those warnings. At closeout, no warning may remain.
- If build logs are dominated by repeated non-actionable linter warnings,
  quiet only those specific style/noise linters in `lakefile.toml` (e.g.,
  `weak.linter.style.whitespace = false`) and record why. Do not disable proof
  checking or hide theorem errors.
- To save context during iteration, redirect targeted builds to a temporary log
  and print only the tail on failure or completion, e.g.:

```bash
lake build ABC24ShortTitle.MainTheorems >/tmp/econcs-build.log 2>&1
status=$?
tail -80 /tmp/econcs-build.log
exit $status
```

- Prefer `lake build <touched-root-module>` over full `lake build` until the
  paper slice is ready for integration.
- After shared-library edits during active paper proof work, build the touched
  library module and the active paper root. Do not broaden to full `lake build`
  until a natural stopping point: paper completion/handoff, commit/push of an
  integration batch, public PR/release preparation, or explicit user request.
- Do not start a fresh worktree or cold-cache build merely to validate closeout.
  Use the warmed worktree's targeted paper build and the required audit scripts;
  rely on CI for a clean-environment check when a public PR or release needs
  one.
- After splitting out a proof-route file, build that route module first, then
  the parent theorem root such as `PaperName.MainTheorems`. Do not broaden to a
  full `lake build` until the route import boundary is stable or the task is at
  a release/integration checkpoint.
- Do not rerun Lean after Markdown-only edits unless the user needs a fresh
  end-to-end checkpoint. After Lean edits, build the touched module first; after
  documentation edits, use `git diff --check` and stale-text `rg` instead.

### 1.7 Paper Triage

Prefer first-pass formalizations with:

- finite objects and finite sums,
- constructive algorithms with simple invariants,
- clean equilibrium, allocation, matching, ranking, or auction definitions,
- reusable primitives likely to help later papers,
- theorem statements decomposable into local lemmas.

Usually defer or isolate papers whose first main result depends on the following, unless expanding a completed core or instructed otherwise:

- large complexity-theory reductions,
- heavy measure theory or asymptotics,
- external solvers without certificate interfaces,
- long empirical pipelines,
- broad economic existence theorems before the finite library is mature.

### 1.8 Handoff Checklist

Before ending work, update a repo note or paper handoff with:

- build commands that passed or failed,
- active theorem seam,
- assumptions imported from the paper,
- shared abstractions added,
- next lemma a future agent should prove,
- closed layers and traps future agents should not re-open,
- whether commit history is needed for the next resume; usually it should not be
  if the status docs and README are current.
- enough exact declaration names that the next agent can start with `rg` rather
  than rereading the proof session transcript.

### 1.10 Token Efficiency and Mathlib Discovery

**CRITICAL MANDATE - DO NOT GUESS MATHLIB LEMMAS:**
When you need a Mathlib lemma (e.g., for `Filter.Tendsto`, `Finset.sum`, or topological limits), **DO NOT guess its exact camelCase or snake_case name in a loop.** This wastes massive amounts of tokens and context window.
Instead:
1. Create a minimal `/tmp/test.lean` file that imports only the touched module
   or the narrow Mathlib leaf you are testing.
2. State the exact theorem you want to prove.
3. Use the `exact?` or `apply?` tactics inside the proof.
4. Run `lake env lean /tmp/test.lean` to let Lean's internal search engine give you the exact lemma name.
5. If `exact?` fails, search the local `.lake/packages/mathlib` repository
   using `rg` for keywords, or use `Moogle` / LeanSearchClient if configured.
6. If the scratch proof requires a new import, add the narrow leaf import at
   the file that uses the declaration; do not recover by importing aggregate
   roots such as `Mathlib` or `AppliedModelingLib`.

Never enter a cycle of modifying a single line in a shell command just to test slightly different lemma names. Stop, use `exact?`, and proceed efficiently.

### 1.11 Post-Formalization Closeout

- The required Lean receipt for a paper closeout is the paper root target, and
  the consolidated strict closeout owns it. Run `env LEAN_NUM_THREADS=1 lake
  build <Paper>` separately only when the reuse planner schedules it or when
  diagnosing a build failure. During an edit loop, `lake build
  <Paper>.PaperInterface` is a useful narrower check, but it is not the closeout
  receipt. Do not replace the paper-root build with a package or repository
  build unless a paper-specific dependency outside that target requires it;
  record the reason and extra target in the validation receipt. Full builds are
  integration/release checks or an explicit user request. The detailed rule
  lives in `references/audit-and-closeout.md`.
- Re-read `PaperInterface.lean` and check each named
  definition/theorem/corollary against the paper statement.
- Run the paper-local review workflow from within the paper folder only when an
  active human statement review or named dashboard diagnosis is needed:
  `./review-dashboard.sh` records checks and uncertain matches in the dashboard.
  If you changed interface statements after earlier checks, the launcher surfaces
  stale warnings so you can refresh only affected items. Use
  `./review-dashboard.sh --check` for that review/diagnostic lane, not as a
  routine frozen-closeout predecessor; the planner owns the final strict gate.
- For non-final proof loops and short pauses, do not treat dashboard refresh as
  required validation. A successful focused Lean build plus a precise handoff
  note is the right stopping boundary; run dashboard refresh/precheck only when
  the next action is human review, release/finalization, or a broader audit.
- Batch a strict post-audit in dependency order. First freeze the source
  inventory, `PaperInterface.lean`, and `status.json` review surface. Then
  derive every affected statement, coverage, review-surface, and source-record
  sidecar from that one stable surface. Edit the final report/DAG after those
  artifacts. Run `closeout_reuse_plan.py` after all cache-hashed paper files are
  stable, and refresh the dashboard only when its dependency-ordered actions
  schedule that work. Do not spend repeated full manifest rebuilds after each
  JSON or Markdown edit.
- During active remediation or after a named failure, use a cheap-to-expensive
  gate ladder and stop at the first non-current layer: (1) focused `lake build`
  and the named conclusion-provenance diagnostic after Lean edits;
  (2) row-local statement, source-to-Lean, coverage, and assumption prechecks;
  (3) recursive source-record regeneration only after the declaration and
  review surface are stable; (4) final report-summary refresh and status sync;
  and (5) one repository closeout reconciliation. At a frozen closeout entry,
  skip this manual ladder: the planner is the first command and schedules the
  required work. For a paper still marked
  partial, `--paper-closeout` deliberately exits nonzero for its documented
  source-target queue. Its useful result is that *only* those exact queue and
  coverage findings remain; stale counts, unconfigured declarations, sidecar
  drift, and hidden-premise findings still require repair. A zero exit is
  possible only after the source-proof queue is empty.
- Treat the row-local strict commands as diagnostics, not four additional
  acceptance runs. Once the interface and all sidecars are stable, run the
  reuse planner, perform only its conditional cache/manifest actions, and use
  its exact strict-closeout argv. Do not then repeat `--statement-check`,
  `--source-to-lean-check`,
  `--paper-coverage-check`, and `--assumption-check` unless the consolidated
  closeout identifies that lane. A prompt-version change is checked against
  current sidecars even when cached rows are reused, so migrate stale ledgers
  before paying for another manifest elaboration.
- Run one manifest-heavy command at a time. Capture and poll its process/session
  id until completion; quiet Lean output is not evidence that the command was
  lost. Before restarting, check whether the original process is still active.
  Do not bundle multiple long dashboard/source-record commands into one shell
  invocation because losing one session handle causes duplicate elaboration.
  `source_record_audit.py` first validates an exact current receipt without
  taking the repository lock; this fast path performs no Lean scan and does
  not mutate canonical evidence. The repository-local lock is reserved for a
  stale-source regeneration or a canonical summary write, and isolated Lean
  passes default to `LEAN_NUM_THREADS=1`. An exit code `4` means another
  source-record pass owns that lock: wait for it or inspect its process before
  retrying; never start a second copy to obtain another stream.
  The detached closeout launcher additionally owns per-paper ignored execution
  state at `.review_traces/paper_closeout_worker.json` and a complete adjacent
  launch-specific log. A live state rejects a duplicate worker; the worker
  survives loss of the chat or terminal transport. Launch only the planner's
  exact identity-addressed command, including `--plan-identity`; a bare runner
  command cannot start work. This state is operational only, changes no paper
  receipt identity, and never supplies an acceptance capability.
- Do not substitute `python3 scripts/audit_repository.py --paper
  <paper-folder> --include-active` for the closeout command. Without
  `--paper-closeout` it also runs repository-wide hygiene checks, which is
  useful for a global handoff but obscures a target-paper result and needlessly
  costs small agents time.
- After changing local `status.json`, run `python3 scripts/sync_paper_status.py
  --paper <paper-folder>` and its `--check` form before the expensive closeout
  gate. These commands read/write only the selected paper's owned README or
  legacy note and never traverse aggregate status/site inputs. In particular, keep
  `paper_interface.line_count`, review-surface classification, and
  `human_review.total_rows` synchronized with the actual interface for release
  navigation. A line-count, row-count, or presentation-layout mismatch is an
  advisory regeneration task, not a reason to replan or repeat semantic/build
  evidence. Review-surface membership, assumption classification, proof routes,
  build target, and formalization status remain strict closeout controls.
  The strict closeout reads paper-local `status.json` and deliberately ignores
  aggregate drift. Run the unscoped status sync only at integration, public PR,
  or release time; do not let another paper's generated drift block a target
  paper whose focused gates are clean.
- A known-incomplete theorem component is an auxiliary proof building block,
  not a source-facing review row. Put it in
  `review_surface.auxiliary_names`; retain the full source target as
  `partially_covered`; and list the component only under
  `support_lean_declarations`/`support_declarations`. Do not leave it in
  `include_names`, `aliases`, or direct source-declaration routing, and do not
  call its certificate/optimality/support inputs source assumptions.
- After the final review-surface change, regenerate the recursive source-record
  audit before editing `source_record_match_llm.json`. Re-pin only the current
  required keys using both the audit digest and each item digest, and remove
  direct-ledger-covered or otherwise obsolete judgments. A partial paper may
  retain its declared source-proof queue, but missing/stale source-record items,
  hidden premises, or an auxiliary component leaking into the review surface are
  audit defects that must be fixed rather than counted as expected partial work.
- When the required statement-audit prompt changes (currently v10), first
  classify the change by its *semantic* effect. A rubric, source-interpretation,
  conclusion-disposition, or required-evidence change requires fresh review of
  every affected generated item. A prompt tag, serialization, cache, diagnostic,
  or presentation-only change does not. For a v10 migration, regenerate the
  current reviewed surface and reproject a prior judgment only when its exact
  normalized source statement, expanded Lean obligation, source-route role and
  content, conclusion disposition, scoped context, and prompt semantic contract
  are identical. Bind the preserved judgment to fresh v10 provenance; never
  call an old tag current merely by copying its hash. Any missing, changed, or
  ambiguous item receives a fresh review. Do not invalidate an entire
  `statement_match_llm.json` ledger solely because its version label changed,
  and do not use row names, declaration names, or judgment keys to decide reuse.
- In a shared worktree, do not run a cache rebuild and a source-record audit in
  parallel. They both inspect the same evolving manifest and can make each
  other stale. Use focused Lean builds during proof edits, then serialize the
  final manifest refresh and recursive audit.
- Confirm every final paper-facing declaration is fully formalized with no
  hidden placeholders; no unresolved `sorry`, scaffold wrappers, or unnamed
  gaps should remain in the claimed result chain.
  Use declaration-aware searches for this check: plain `rg "axiom|opaque"` can
  match comments such as "not an opaque input." Prefer anchored patterns for
  `axiom`/`opaque` declarations plus explicit `sorry`/`admit` holes, then
  inspect any remaining textual matches before treating them as proof debt.
- When a statement looks stuck because a source paper leaves a routine domain
  condition implicit, identify the mathematical assumption instead of adding
  wrappers around the obstruction. Human papers often silently rely on positive
  denominators, nonzero measure/mass, bounded support, integrability, nonempty
  feasible sets, interior capacity, full support, or quantities being bounded
  away from zero. Add it as a source premise only when the cited source
  semantics explicitly state it or reasonably imply it. Otherwise derive it or
  leave the full source result as a source-target gap with partial status. A
  human-approved non-source restriction is a documented additional assumption,
  not a caveat. Never relabel a missing conclusion as a conditional boundary
  merely because that would make the theorem easier.
- Do not turn a routine ambiguity about a paper's intended equality or
  inequality convention into a long proof campaign by default. Paper prose
  commonly leaves these conventions implicit, so a `=` versus `<=`/`>=`
  discrepancy is not by itself evidence of a material theorem defect. This
  includes
  `=` versus `<=`/`>=`, strict versus weak inequalities, whether a rate is
  strictly positive or merely nonnegative, whether a support endpoint is
  included, and whether a finite carrier is nonempty. Ask
  the user/author for the intended correction when they are available. When
  they are not available, record the exact condition as a visible additional
  assumption in the corrected-model theorem and post-formalization report,
  continue with the actionable proof work, and raise it at the next user
  interaction. Do not silently attribute the condition to the source or change
  the literal-source status until the user confirms it; once confirmed, record
  it as an author-approved governing correction with its source anchor and
  Lean field/premise.
- If a result uses a documented additional assumption, ensure its premise and
  source/caveat rationale are explicit in both the theorem statement and
  `status.json`, with exact declaration names and no vague wording.
- Produce a final human-facing report in the paper folder alongside the DAG
  artifacts (TikZ source and rendered image). This report is not for routine
  handoff or an implementation inventory. It is the concise final assessment a
  human should read to decide whether the paper's definitions and named theorem
  statements were represented correctly.
- If the final status is `formalized with caveat` because Lean exposes a
  substantial error in a central source-paper claim and fully proves its
  corrected endpoint, also create a concise caveat-repair memo. Prefer a tracked
  TeX source plus rendered PDF: start with a 1--2 page executive summary, then
  give a deeper note for each issue in human-facing proof language. Explain why
  the change is substantive; do not fill the memo with Lean declaration names.
  For algebraic/formula caveats, state the old source equation, the exact
  replacement equation, the source theorem/proposition locations affected, and
  a short TeX derivation explaining why the replacement is correct. Update that
  memo when the human gives feedback.
- In the source-proof/source-caveat pass, audit proof prose as well as theorem boxes. Trace
  normalized quantities through the next comparison whenever a source symbol
  could mean an admitted-class share, group-conditional admission probability,
  probability mass, capacity-normalized share, or objective contribution. If a
  proof line compares a quantity under the wrong normalization but the final
  Lean theorem uses the correct source theorem statement, record this as a
  proof-text/source-notation repair in a source-proof note and final report. Use
  a caveat memo only if the repaired endpoint is itself the claimed Lean result.
  Do not call the Lean theorem wrong unless the formalized statement itself
  depends on the bad comparison. For example, if `tau_g` is defined as `pi_g`
  times a selected mass divided by total capacity, then `tau_g` is an
  admitted-class share. Underrepresentation is `tau_B < pi_B` or an equivalent
  group-conditional-rate comparison, not raw `tau_B < tau_A` unless equal
  population shares or another explicit normalization has been assumed. When
  the Lean endpoint uses `tau_B < pi_B`, classify the raw-comparison sentence as
  a proof-text repair only.
- Formula-bearing reviewed rows in `PaperInterface.lean` must have an explicit
  `Source status:` line in the paper-facing comment. Use short labels such as
  `Source status: derived from source primitives.`, `Source status: paper
  theorem from source conditions.`, or `Source status: formalized source note.`
  Do this before regenerating sidecars; the closeout audit treats missing
  provenance lines as errors for formalized papers.
- Do not put broad package constructors, certificate records, or imported
  wrapper aliases in the reviewed surface merely because they are useful
  summary endpoints. If a row returns a package/record/consequence type rather
  than displaying the source formula or theorem subclaim directly, classify it
  as auxiliary unless the report and source-map make the package fields
  explicit and the audit accepts the row. Keep reviewed rows on displayed paper
  formulas, named theorem endpoints, and exact source conditions.
- Treat the final validation report itself as an audit target. Before final
  handoff, reread the report as a human reviewer would: it must be paper-facing,
  short enough to inspect, organized around source definitions and named theorem
  boxes, explicit about what remains for human dashboard review, and free of
  stale blocked-command language. If it reads like a helper-theorem ledger,
  proof-script changelog, or shell transcript, rewrite it before claiming
  post-validation is complete.
  Put source-convention details, source-record field inventories, and
  warnings meant mainly to prevent future agent confusion in
  `docs/POST_FORMALIZATION_AUDIT.md` or another agent-facing note. Include them in
  the human-facing final report only when they change the theorem statement,
  require an additional assumption, identify a source-paper issue, or explain a
  real remaining boundary.
  The report and DAG are also machine-audited closeout artifacts. A paper at a
  final closeout status, including an intentionally conditional/approved-boundary
  closeout, must have a current DAG audit/status section, validation checks
  section, explicit `docs/DependencyDAG.tex` and `docs/DependencyDAG.pdf` evidence,
  rendered/visual inspection notes, and the targeted
  planner-emitted strict closeout command. Run that audit after editing the
  report or DAG at closeout; do not
  rely on prose memory that those checks happened. Use `--paper-closeout` for
  completion claims so unrelated paper-folder maintenance cannot mask this
  paper's status, but do not apply this paragraph to an unfinished active paper
  merely because it is temporarily conditional or partially formalized.
  Follow the current report template order, not an older partially reorganized
  report. In particular, keep the paper-interface review sections at the end:
  `Paper Definitions Checked`, `Named Theorem Statements Checked`, and
  `Paper-Facing Statement Validator Ledger`. Do not leave placeholders or
  pointers saying where those sections belong; move the text into template
  order and fill the validator ledger from the dashboard export.
  In a public-repo batch cleanup, audit reports one by one and run an exact
  heading-order check across every `papers/*/FINAL_VALIDATION_REPORT.md` before
  committing. Also scan for pointer prose such as `See the verdict...`,
  `where those sections belong`, `to be filled`, `TODO`, or `TBD`; every
  template section should contain final human-facing content, even if that
  content is simply `None`.
- Write the final validation report in paper language, not Lean-internal
  implementation language. Near the top it must answer five questions directly:
  what has been proved, whether formalization found anything wrong or ambiguous
  in the paper, whether any qualitatively different proof/modeling route was
  needed, what remains for Lean versus human review, and which generalizations,
  conjectures, or extensions look trivial or near-trivial after formalization.
  Keep the "what has been proved" answer outcome-focused. If every source
  definition and named result is closed, say concisely that the paper is fully
  formalized. Do not fill this section with process statements such as
  `Theorem X no longer takes external witnesses` or `the representation is now
  derived internally`; those are implementation-route notes, not final
  human-facing proof claims.
- Human-facing documentation should describe current status, not the route by
  which that status was reached. In DAGs, READMEs, final validation reports,
  generated status summaries, and coauthor-facing memos, avoid history markers
  such as `no longer`, `previously`, `now`, `formerly`, `superseded`,
  `restored`, or `old route`, unless the historical comparison is itself a
  source-paper caveat or an explicit user-requested retrospective. A human
  reviewer should see the current theorem statement, current proof status,
  current caveats, and current remaining boundary. Do not turn a formalization
  report or post-formalization audit into an implementation chronology. Put
  implementation history, abandoned routes, and route-change notes only in
  Codex-facing handoffs, proof-plan scratchpads, or commit messages when they
  genuinely help future agents.
- Include a Lean footprint in every final validation report: total lines across
  paper-local `.lean` files, the line count of `PaperInterface.lean`, and the
  number of human-review rows/declarations exposed there. Use this to make the
  scale of the proof and the size of the review surface clear to humans.
  The total paper-local `.lean` line count is the full proof footprint and is
  the value exported as `lean_loc`/`Full proof LOC`; it is intentionally
  different from the smaller `PaperInterface.lean` line count. Never use the
  interface line count as the paper proof LOC in generated manuscript, docs, or
  website tables.
- Include a short "proof tricks worth reusing" section in the final report.
  This should be a durable engineering summary, not theorem-specific proof
  chatter: name the modeling choices, proof decomposition, and Lean tactics or
  library seams that saved time or would have saved time if used earlier.
- Run a proof-level library-lift pass before final handoff. Inspect the
  paper-local proof modules for thin wrappers around `AppliedModelingLib`, generic
  lemmas that are not paper-specific, reusable certificate constructors,
  proof-result patterns, and techniques that would serve another paper. Extract
  small, targeted generic lemmas/results immediately when the destination is
  clear and the build can be checked; otherwise record the candidate,
  destination module, and reusable proof idea in the final report. Do not
  perform a risky broad move during final closeout.
  After extraction, rebuild both the new leaf modules and the paper target that
  imported or inspired them. If a paper-local proof relies on unfolding a raw
  arithmetic formula or `if` expression, keep the source-shaped local formula
  in the paper namespace and make the shared API a reusable sibling rather than
  replacing the local declaration with an opaque one-step alias.
- Run a skill-update pass as a required post-formalization step. If the paper
  taught a reusable workflow lesson, update this skill or its reference files
  before final handoff; if it did not, state that explicitly in the final
  report or handoff. Put durable process rules in this always-loaded file only
  if they apply across papers, and put theorem-family, domain, or proof-pattern
  details in the appropriate reference file.
- Include a final DAG audit in the final report. Confirm the DAG was rendered
  and visually inspected, note any topology changes, and state whether the DAG
  has missing/extra paper-facing boxes, node-overlap, label-overlap, or
  arrow-through-text issues.
- Before writing that report, do a statement-surface pass outside Lean: list
  every paper definition/object and every named result in source order, decide
  which Lean declaration should be the reader-facing statement for each one,
  and note any source imprecision or proof deviation. Keep this plan current as
  proof work progresses; do not wait until the end to reconstruct the theorem
  inventory from helper lemmas.
- Before final handoff or publish, require current tracked LLM sidecars for the
  curated target-paper surface. `lean_to_tex_llm.json`,
  `statement_match_llm.json`, `paper_coverage_llm.json`,
  `defect_support_match_llm.json` whenever a quarantined source item uses
  support-only counterexample/refutation routes,
  `review_surface_llm.json` when threshold-triggered, and
  `assumption_match_llm.json` for all `assumption_names` and
  `proof_boundary_names` must be present and non-stale according to the Python
  prechecks. This does not require rerunning judges for unchanged rows or for
  unrelated papers. If any target-paper sidecar is missing, stale, or
  reports `uncertain`/`mismatch`/`partial_boundary`, the final report must list
  the exact rows and the paper status must remain conditional/partial as
  appropriate. For a strict statement `mismatch` that is intentionally accepted
  because of an external/library/analytic boundary, the sidecar must keep
  `judgment: "mismatch"` and add `resolution: "conditional_boundary"` with the
  named boundary and conditional premises; the final report should count it
  separately from unresolved mismatches. Do not treat a green Lean build or a
  clean `#print axioms` pass as a substitute for these LLM-as-judge artifacts.
- For completed papers, ensure `PaperInterface.lean` is compact enough for a
  human review session. As a default audit threshold, it should normally have
  tens of declarations, not hundreds; if it needs slices to be navigable, it is
  probably serving the wrong role. It should mirror the DAG: paper definitions
  first, with the actual formulas visible in the file, then direct theorem
  statements matching the paper. It must not be only an alias list, witness
  tuple, or pointer layer to `MainTheorems.lean`; a human should be able to read
  this file alone and check that the encoded definitions and theorem statements
  reflect the source text. Proofs may be short calls into the implementation
  layer. Keep exhaustive aliases and auxiliary seams in a neutral proof-ledger
  file, not in the interface.
- In `PaperInterface.lean`, aim for one declaration per paper definition or
  formatted paper object, and one declaration per named result or numbered part
  of a named result. If a theorem box has parts (i)--(iii), separate direct
  declarations are acceptable when they mirror those source parts and avoid
  noisy tuple witnesses.
- Before launching the dashboard, do a quick size check:
  `wc -l papers/<Paper>/PaperInterface.lean` and
  `rg -c '^(noncomputable\\s+|private\\s+|protected\\s+)*(theorem|lemma|def|abbrev) ' papers/<Paper>/PaperInterface.lean`.
  If the declaration count is in the hundreds, split implementation endpoints
  out before asking a human to review it.
- If `PaperInterface.lean` starts to grow, split broad proof/API aliases into
  `ProofInterface.lean` or implementation modules. Curate the review rows and
  optional slices in paper-local `status.json` under `review_surface`, then run
  `python3 scripts/sync_paper_status.py --paper <paper-folder>` and its `--check`
  form. Defer aggregate status/site generation to integration or release, and
  refresh the ignored dashboard cache once at the next human-review or
  planner-scheduled boundary. Do not confuse "0/N reviewed" with stale or failed Lean validation; it
  only means no human review entries have been saved.
  Final human review should normally expose a compact source-facing surface,
  not every proof endpoint. Do not report an unfiltered declaration count such
  as hundreds of rows as the human dashboard surface in a final validation
  report; fix the interface first and report the curated count.
- Treat any proof-ledger file as an exhaustive importable implementation
  ledger, not the readable paper interface. Its header should say that
  explicitly and point to `PaperInterface.lean` for the DAG-shaped human-facing
  surface. It should contain source-numbered theorem aliases, named-result
  wrappers, and supporting proof-seam endpoints when those seams are useful for
  checking the named claims. Do not add standalone proof-facing formula aliases
  when the formulas already appear in `PaperInterface.lean` or are only
  internal implementation plumbing. Do not create new `PostPaperAudit.lean` or
  `AuditLedger.lean` files; existing files with those names are legacy rename
  targets.
- For papers already marked `Formalized` or `Formalized with caveat`, backfill
  the same post-paper surface instead of leaving older
  validation artifacts in place: a readable `PaperInterface.lean`, an
  exhaustive neutral proof endpoint ledger when useful, a compact final
  validation report, and synchronized paper README/status-table text.
- Confirm the paper root module imports `PaperInterface.lean`. Legacy
  implementation proof ledgers such as `PostPaperAudit.lean` may remain
  importable while awaiting the coordinated rename, but do not make their root
  imports a closeout requirement. When a neutral proof ledger is retained, it
  should have one source-numbered theorem alias or wrapper for each final
  named endpoint.
- During final export curation, audit every broad paper module re-export as
  well as `PaperInterface.lean`. A completed paper can still look conditional
  to downstream users if `MainTheorems.lean` re-exports old proof-adapter
  models, coupled-outcome variants, or source-bridge staging theorems as part
  of the paper surface. Keep those declarations in the reusable library or
  audit ledger when useful, but expose the source-shaped final theorem in the
  paper module and status artifacts.
- Do a full DAG finalization pass before handoff:
  - Cross-check the DAG against the source paper and `PaperInterface.lean`.
    Add missing paper-facing definition/lemma/proposition/theorem/corollary or
    appendix-remark boxes, and remove implementation-only boxes unless they are
    the exact remaining caveat or a documented paper-facing bridge.
  - Re-read every node as human prose. Green/formalized nodes should summarize
    the paper claim, not how the Lean proof was implemented. Caveat or
    conditional nodes should name the exact remaining semantic issue.
    A reviewer should be able to understand the mathematical result from the
    green box itself without recognizing any paper-internal TeX label or Lean
    declaration name.
    Do not write status words such as "closed", "proved", "formalized", or
    "verified" inside green node bodies; the node color/style already carries
    that information. Likewise, avoid vague "open" text in partial/conditional
    nodes: name the missing theorem, model construction, or library ingredient
    needed to finish the paper result.
  - Do not split one source-numbered proposition/theorem/corollary into
    multiple green boxes merely because the Lean proof has formula, finite,
    certificate, or boundary helper layers. Use one green paper-facing node for
    the source result, with its paper number and a short statement of the
    actual mathematical conclusion. Make helper layers yellow/model nodes only
    when they are needed to explain real dependencies, and never duplicate the
    same numbered result across helper, formula, and final-result green boxes.
  - Before accepting a rendered DAG, run a label/duplication audit: grep the
    TeX for source labels and Lean names such as `thm:`, `lem:`, `source_`,
    and long declaration fragments; count occurrences of each numbered
    result header; and visually confirm every green result node states the
    paper-facing conclusion rather than the implementation route.
    Run this DAG audit as part of the post-formalization closeout command path.
    Do not wait for a human to ask whether the DAG and validation report satisfy
    the workflow; if the paper is being claimed complete or public-ready, the
    DAG, rendered PDF, status rows, and final report must already have passed
    this paper-facing audit.
  - Use the shared DAG template's node-type styles, not just status color:
    `dag_model` for definitions/model layers, `dag_lemma` for lemmas/supporting
    lemma clusters, and `dag_result` for theorems, propositions, corollaries,
    and final paper-facing results. Keep the legend consistent with the styles
    actually used in the diagram.
  - Check edge semantics. Solid arrows are Lean-checked dependencies; dashed
    arrows are caveats, bypassed paper routes, or non-required context. Remove
    redundant arrows if they make the diagram harder to inspect.
  - Render from the paper folder and visually inspect the PDF or a PNG
    conversion. Fix overlap between boxes, legends, labels, metadata, and
    arrows; preserve visible whitespace between neighboring nodes and clear
    routing lanes between columns.
- Batch all report and DAG closeout edits, freeze them, then run
  `closeout_reuse_plan.py --paper <paper-folder>` and execute its current
  `next_action` once. If an input is edited after receipt publication, replan
  once after the edits are again frozen; do not close out after each edit. Run
  this only
  once the paper is at a real closeout/publication boundary or the user has
  explicitly requested post-validation. Do not run this command just because an
  unfinished paper reached a clean compile point; use targeted builds,
  placeholder scans, and row-scoped judge checks for active formalization work.
  Treat its
  PaperInterface/proof-ledger and
  DAG/report closeout findings as part of the final audit: no tuple witness
  interfaces, no standalone proof-facing formula aliases in the audit ledger,
  no stale `Lean witness` report language, no completed-paper status rows that
  hide caveats in prose, and no missing/stale DAG audit, final validation
  report, rendered DAG PDF, or visual-inspection evidence.
  Also run the unfiltered `python3 scripts/audit_repository.py` before broad
  repository handoff when you need global hygiene, but the paper-specific
  targeted command is the mandatory post-formalization gate for the paper being
  closed. If the unfiltered audit reports findings from other papers, record
  them separately; do not downgrade or delay a paper whose `--paper-closeout`
  audit and paper-local validation gates pass.
  Do not use this global audit as an excuse to rerun LLM-as-judge workflows for
  every paper. It may check tracked sidecar freshness and report stale/missing
  evidence, but judge reruns should stay scoped to the paper being closed unless
  the user explicitly asks for an all-paper refresh.
  Also run `python3 scripts/audit_repository.py --library-only --library-premise-audit` when a
  completed paper uses recently added or extracted library APIs. Informational
  library certificate findings are not errors by themselves, but any completed
  paper wrapper that still exposes one of those certificate/source-boundary
  parameters must either construct it internally, route it through validated
  paper assumptions, or be downgraded to partial/conditional.
  Keep the paper validation report paper-local: record audit findings that
  affect the paper being reported, but do not put unrelated global repository
  errors or other active-paper warnings into that paper's validation report.
  Mention unrelated global audit failures in the agent final/status message or
  a separate repository-maintenance note instead.
- Update the paper-local `status.json` at the same time as the DAG and final
  report, using the exact caveats from the final report. Then
  run `python3 scripts/sync_paper_status.py --paper <paper-folder>` and its
  `--check` form for paper-owned output. Run the unscoped aggregate/site sync
  only at integration, public-PR, or release time. Do not manually edit generated table rows,
  and do not let any public
  status surface keep stale "partial" or "active" wording after a paper-local
  validation report says a paper is formalized.
- Use one status vocabulary per artifact. At paper and repository level,
  `formalized` is the status for a paper/result whose Lean statement and proof
  compile with its caveats documented. Lean verification is the mechanism, not a
  separate status category. Do not use `Verified in Lean`, `Verified`, or
  `Verified with caveat` as paper-status labels, and do not title a status
  section `verification status`; use `Formalized`, `Formalized with caveat`,
  `Partially formalized`, or the paper-local lowercase equivalents from
  `docs/STATUS.md`.
- For source-version differences, make the primary paper target explicit and
  describe later-version wording as a refinement or correction to a specific
  result. Avoid blended labels such as `conference/journal` when they obscure
  the target, and avoid process jargon such as `crosswalk` in public-facing
  reports; say directly that the folder formalizes the source paper, with the
  named theorem checked against the refined wording from the later version.
- **CRITICAL MANDATE: Never lie by omission.** Your validation report MUST list all major theorems, propositions, and sections from the paper. If a result or section was deferred, skipped, or is otherwise unformalized, you MUST list it in the report, mark its status as `not formalized`, and explain why it was deferred. Always be honest and complete regarding the paper's contents.
- The report must first present the paper interface: the definitions and
  formatted mathematical objects the reader needs to inspect, even when the
  source did not number them as "Definition." Examples include bias, aggregate
  posterior, calibration, objective functions, equilibrium notions, allocation
  rules, or any paper-specific named/boxed notation. Give each definition in
  paper notation plus its single main reader-facing Lean declaration, preferably
  from `PaperInterface.lean`.
- Then state each named theorem/proposition/corollary once, matching the paper
  text at theorem-box granularity. Do not expand one source theorem into dozens
  of auxiliary lemmas in the human report. Put only one direct Lean interface
  statement declaration under each paper-facing result, ideally from
  `PaperInterface.lean`. If a source theorem has separately numbered clauses,
  list each clause as its own paper-facing result with one declaration. Keep
  auxiliary implementation inventories in the Lean audit ledger, README, or
  proof files.
- The report must summarize: source version checked, named-result completion
  status (including unformalized items), additional assumptions introduced
  beyond the paper, proof-strategy deviations from the paper, and any suspected
  paper errors or inconsistencies found during formalization.
- Keep Lean declaration inventories out of the final report except for the
  single direct paper-interface declaration needed to identify each source
  result. Do not put comma-separated helper declarations, source declaration
  lists, theorem aliases, or proof-seam inventories in final-report status
  tables. Put helper theorem ledgers, alias lists, and proof-seam inventories in
  a neutral proof-ledger file, the README theorem ledger, or `SOURCE_AUDIT.md`.
- If the final report starts reading like an implementation ledger, split it:
  keep the report as a short human assessment of the source claims, proof
  deviations, findings, reusable lessons, DAG, and validation checks; move
  source-line mappings to `SOURCE_AUDIT.md` and declaration inventories to
  a neutral proof-ledger file or the README.
- Distinguish agent audit from human review. A report may say an agent
  source-audited every row, but it must not say rows were "reviewed" or imply
  dashboard completion unless a human actually saved those dashboard reviews.
- If no extra assumptions, deviations, or caveats were needed/found, state that
  explicitly in the report rather than leaving sections implicit.
- Keep the report human-facing. Do not include routine shell commands such as
  `rg -n ...` scans or full build command blocks unless the exact invocation is
  essential to understanding a caveat. Summarize validation/build checks in prose
  instead. If the report is getting long because it lists every helper theorem,
  stop and replace that section by a short paper-definition/theorem interface
  plus one main declaration name for each paper-facing theorem or definition.
- The report should read top-down for a researcher who cares about the paper,
  not Lean. Put the human verdict, closeout status, source/scope, a short
  researcher summary of checked results, remaining mathematical boundaries,
  extra assumptions, proof-strategy deviations, reusable proof ideas, easy
  generalizations/conjectures/extensions, and paper issues/caveats before any
  proof ledger. Put validation evidence, audit
  commands, row counts, generated ledgers, declaration inventories, and proof
  plumbing near the end. Do not place hidden-premise audit blocks, command
  transcripts, validator ledgers, or long Lean-centered proof inventories
  before `Detailed Formalization Evidence`.
- Do not paste standalone generated-audit prose into the final validation
  report. In particular, do not add a generated-audit front-matter section or
  dated generated-audit blockquotes. If the result matters to the reader,
  summarize it once in ordinary language under `Validation Checks` or
  `Paper Assumption Provenance`.
- Do not title the front proof summary `What Has Been Proven`. In practice that
  heading invites long implementation ledgers. Use `Researcher Summary of
  Checked Results` for the short paper-facing summary and
  `Detailed Formalization Evidence` later for Lean/provenance detail.
- Put `Updated: YYYY-MM-DD` directly below the report title, using the date of
  the report's latest substantive refresh.
- Avoid repetition. Do not include both a long top verdict and a long final
  verdict saying the same thing. Put a short `Completion status: ...` line in
  `Closeout Status` immediately after `Human Verdict`, and keep the explanation
  in `Human Verdict`.
- The `Human Verdict` section must be a two-to-four sentence executive summary
  for a non-Lean reader. It should state the formalization status, the main
  remaining mathematical/library boundary if any, whether a paper-correctness
  issue is being claimed, and whether human dashboard sign-off exists. Do not
  put Lean declaration names, validator row counts, audit digests, source-record
  inventories, command outputs, proof adapter names, or Lean footprint numbers
  in this section; put those details in the later source, assumption, DAG,
  statement-validator, and validation-command sections.
- The `Proof-Strategy Deviations` section is only for human-facing
  mathematical departures from the paper's proof route or theorem statement.
  Do not list source-record packages, deterministic certificate plumbing, proof
  adapter names, declaration inventories, audit architecture, dashboard parser
  changes, or other Lean implementation route notes there. If the only
  differences are explicit formalization boundaries, say `None beyond the
  formalization boundaries already recorded above` and point to the assumptions
  or remaining-gaps sections.
- Put likely source typos, missing constants, sign-convention inconsistencies,
  source-version corrections, and theorem-statement repairs in `Mathematical
  Typos or Other Fixes Suggested in the Source Paper`. Write these as short
  human-facing mathematical notes and avoid Lean declaration names. When the
  evidence is only a nonblocking source-proof note, say that directly instead of
  claiming a paper-level caveat.
- Use `Paper Issues or Caveats` for the status-facing conclusion after those
  source-fix notes: for example, whether the paper has a real caveat, whether a
  source-quality note is nonblocking, or whether no paper-level caveat is being
  claimed. Include the section even when the body is `None found.`.
- Avoid wide Markdown tables for definition inventories when the notation or
  declaration names are long. Use a concise bullet checklist instead, with the
  paper notation first and the Lean interface declaration second.

Keep this closeout workflow in that single reference file for now rather than
splitting it across multiple files. If the closeout reference later becomes too
large, split only DAG-specific visual/layout rules into a future
`references/dependency-dags.md`.

## Component 2: Proof Reference Routing

Do not load one giant theorem-proving playbook. When starting a nontrivial Lean
proof, read only the reference for the library layer being touched; if the proof
crosses layers, read at most the generic foundation reference and one domain
reference.

| Touched code | Read |
|---|---|
| `AppliedModelingLib/Foundations/Math/*`, graph/counting/rounding/sign lemmas | `references/proof-foundations-math.md` |
| `AppliedModelingLib/Foundations/Probability/*`, finite PMFs, Markov kernels/chains, CTMCs, renewal-reward, reward-rate, concentration, measure inequalities, continuous densities, RUM/noise laws, order statistics, large deviations | `references/proof-foundations-probability.md` |
| `AppliedModelingLib/Foundations/Optimization/*`, argmax/existence/objective wrappers | `references/proof-foundations-optimization.md` |
| `AppliedModelingLib/Applications/RecommenderSystems/*`, accuracy/diversity, producer fairness, count allocation | `references/proof-recommender-systems.md` |
| `AppliedModelingLib/Algorithms/Online/*`, online allocation/matching, regret/Yao | `references/proof-algorithms-online.md` |
| `AppliedModelingLib/MechanismDesign/Auctions/*`, digital goods, GSP, combinatorial auctions | `references/proof-mechanism-design.md` |
| `AppliedModelingLib/Markets/*` or `AppliedModelingLib/SocialChoice/*`, matching, fair division, rankings, social choice | `references/proof-markets-social-choice.md` |

`references/proof-strategies.md` is only a short router/index for these files.
Do not load detailed proof references for routine README/DAG/status edits or
simple wrapper repairs.
When updating this skill from proof work, put reusable tactics and theorem
patterns in the relevant `references/proof-*.md` file. Keep `SKILL.md` limited
to workflow, routing, folder contracts, validation, and context/source-control
rules. Before committing a public skill update, scan `SKILL.md` and every
exported reference for private-only paper identifiers, unpublished findings,
non-public source excerpts, private or local links, and dependencies on wiki
examples, feedback ledgers, or session history. Public references must be
self-contained. They may use examples from publicly released papers or
formalizations when the cited facts and declarations are already public.
