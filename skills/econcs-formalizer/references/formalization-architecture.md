# Formalization Architecture

Authoritative rules for source-facing Specs, proof endpoints, semantic
prerequisites, statement fidelity, corrections and assumptions, review-packet
structure, and proof-campaign pacing. Use `skills/econcs-prover/SKILL.md` for
the inner compiler-guided proof loop.

- Every paper has `PaperInterface.lean`. It is the human and machine source
  review surface. Source results appear once as expanded semantic Specs;
  source definitions, algorithms, models, assumptions, and conditions appear
  as the actual full Lean declarations consumed by those Specs. Every source
  result also has a corresponding exact-type proof endpoint, normally kept in
  `ProofInterface.lean` outside the semantic review surface.
- Keep the paper import graph acyclic by role. Lower mathematical model and
  implementation modules must not import `PaperInterface.lean` or
  `ProofInterface.lean`; import the lowest module that actually owns the
  needed definition or theorem. `PaperInterface.lean` may consume those lower
  modules to state the source Specs, and `ProofInterface.lean` may consume both
  the semantic interface and proof implementations to expose exact-type proof
  endpoints. A complete paper build is the authority for this property: do
  not add a Python import parser or a second paper-specific cycle rule merely
  to predict what Lean and Lake already reject.
- A fresh closeout is role-typed. A source result uses one proposition-shaped
  semantic Spec paired with a distinct theorem/lemma endpoint in `proves` or
  `refutes` mode. A source definition, algorithm, model, assumption, or
  condition instead uses the existing paper/library semantic-prerequisite lane
  to compare the verbatim source directly with the complete Lean declaration
  that downstream Specs actually use. Do not manufacture a theorem whose only
  content is that a definition equals itself, and do not create a source-shaped
  declaration that the audited result graph does not consume. Under
  `semantic_route_schema: 2`, preflight enforces both rules and requires every
  such source item to be bound to an actual prerequisite declaration. Code
  location is irrelevant: paper-local and reusable-library declarations have
  the same source-match obligation. Historical accepted graphs remain
  verifiable under their recorded contract; migrate them only when that paper
  next enters a substantive closeout.
- Pass every explicitly routed source-semantic declaration to the native Lean
  graph as one root set. Never decide its paper/library review lane from its
  namespace, declaration kind, filename, or a `Type`-shaped signature. Lean
  resolves the review owner and loaded owning module, and the returned paper
  and reusable-library sections must jointly contain every requested root.
  An unsupported external owner fails closed until it has an explicit source
  contract; Python must not guess one. Historical presentation-only packet
  code may retain a clearly labelled namespace partition, but it cannot feed a
  current graph, judgment, evidence leaf, or acceptance decision.
## Statement Fidelity

Paper credit comes from source semantics, expanded Lean propositions, and
proof closure. Never infer fidelity from declaration, field, binder, function,
record, or map-key names.

- When repairing a false or underspecified result, state each added premise at
  the lowest available semantic layer. First seek a condition on the paper's
  model primitives and their algebraic, probabilistic, or behavioral
  relations. Treat supports selected for a proof, covers, matchings,
  certificates, couplings, and similar witnesses as derived objects, and prove
  the bridge from the primitive premise to those objects. If the weakest
  theorem currently proved genuinely assumes such a witness, label it as a
  proof-level conditional rather than calling it a primitive model condition;
  also record any stronger, interpretable primitive assumptions known to imply
  it. Never suggest that a proof witness follows from the original model merely
  because the source proof silently chose one consistently.
- Before adding a new premise to rescue the intended conclusion, test whether
  the source assumptions instead prove a universal dichotomy: the intended
  conclusion holds, or the competing object fails a desirable property already
  expressible in the paper's model (for example, identification, feasibility,
  stability, or efficiency). Prefer that primitive adverse conclusion to a new
  proof-witness assumption when it gives the scientifically meaningful repair.
  State the paper-facing dichotomy first and derive any support, cover,
  matching, or certificate formulation only inside the proof architecture.
- Put every material premise and conclusion in the elaborated
  `PaperInterface.lean` type or a transparent audited `Spec : Prop`.
- Inspect that expanded public proposition for implementation-only binders.
  A local `Finset` proof may need `DecidableEq`, but the paper-facing statement
  must not acquire `DecidableEq`, computability, or another typeclass premise
  unless the source model actually requires it. Prefer local `classical` in
  the specification or proof and recompile the interface plus paper root after
  removing such an artifact. This is a material source-fidelity change: freeze
  again and refresh the affected raw evidence before resuming closeout review.
- Do not hide conclusions in caller-supplied certificates, records, witnesses,
  runs, equilibria, selectors, convergence packages, or source-row equations.
- Distinguish conditional behavior from existence, nonvacuity, uniqueness,
  positive mass, termination, feasibility, and optimality.
- For algorithms, audit the executable transition semantics, tie-breaking,
  terminal outcomes, quantifier order, and complexity claim through the
  transitive closure. In particular, preserve whether one algorithm is chosen
  uniformly before unknown model or instance data. Never let an arbitrary
  record field stand in for the procedure's comparison count, runtime,
  stopping rule, or output without a Lean-checked operational relation.
- For equilibrium and strategic claims, state action spaces, timing,
  information, beliefs/PBOs, payoffs, off-path/null behavior, and refinement.
  A selected or one-sided deviation check is not a whole-equilibrium proof.
- For measure-theoretic statements, make pointwise versus almost-everywhere
  conclusions and null-set conventions explicit. Do not spend a long campaign
  on harmless zero-mass conventions when the user has approved the source
  convention; record the interpretation.
- Use a proven library for established voting, optimization, matching, or
  algorithmic semantics when available. Do not replace an existing executable
  STV/RCV model with an ad hoc paper-local surrogate.

The semantic audit must traverse elaborated expressions, implicit arguments,
typeclass inputs, conjunctions/iff/implications, transparent definitions,
record fields, constructors, and imported dependencies. Syntactic token scans
and name-pattern detectors are diagnostics only.

Apply that rule identically to paper-local and reusable-library declarations.
For a paper-local `structure` or `inductive`, Lean must emit the elaborated
outer type together with every constructor type; an outer `Type ...` signature
alone is not a semantic target. Discover the declaration and its recursive
dependencies through Lean, then use exact source ranges only to present the
reviewed code. Never let the file location decide how much mathematical
content receives semantic review.

Treat each claimed source-row/`PaperInterface` association as an exact semantic
binding. Ordered arrays are presentation only: never zip rows by position, and
never repair missing source semantics by copying a Lean type, binder, or
statement. Explicit one-to-many coverage must be represented explicitly. A
transparent `Spec : Prop` may mediate direct structural comparison and route
selection, but only the reviewed theorem's elaborated type and closed proof can
earn theorem proof credit.

For every v11 source-to-Lean semantic judgment, the source input is exactly
the byte-pinned `source_anchor_evidence` quote bundle for that source item,
followed only by separately byte-pinned
`semantic_context_requirements` quote bundles. Each context entry must state
one permitted role—definition, model, model construction, scope, prior stated
result, or stated antecedent—so it can interpret a displayed claim but cannot
smuggle in a proof derivation or inferred strengthening. The map's
`statement`, `semantic_claim`, title, source-route explanation, and any
generated Lean-to-TeX prose are navigation or reviewer-output metadata, never
semantic input.
Record one deterministic source-input-bundle identity, and bind it to the
judgment, each direct route, and each direct endpoint obligation. If the
displayed result relies on construction, definition, or stated-antecedent
context not in the result excerpt, add exact context excerpts before judging;
do not infer it from a paraphrase. If available source context only describes a
stronger construction than the displayed endpoint, formalize the displayed
endpoint as a separate Spec and use the construction in its Lean proof; do not
call the stronger construction a direct match. Compare that raw source bundle
directly with the expanded transparent `Spec` and the complete Lean-emitted
claim-atom list. The list must identify every parameter, every proposition-
valued assumption, and exactly one terminal conclusion; bind its name-
independent semantic digest and the full atom-aware review target to the
judgment. Never infer those roles by reparsing Lean display text in Python. A
paired theorem `T : TSpec` is
proof evidence only: Lean Meta must verify the exact type/proof relation, but
no LLM row may compare the source to that wrapper separately.

A `Spec` is not expanded merely because Lean can unfold it elsewhere. If the
displayed declaration replaces the paper's material domain, construction,
definition, or conclusion with a paper-local predicate/function name, record
the row as `uncertain` rather than asking an LLM to infer the hidden body. Move
the condition into the one source-facing Spec, or add a separately source-faced
Spec for the displayed endpoint. A direct `matches` verdict requires the raw
source bundle and the visible Spec code alone to support the comparison.

The same rule applies to a material reused library definition, including one
reached through a retained paper-local prerequisite rather than directly by a
selected Spec. A paper may
reuse its Lean implementation, but not outsource the semantic audit to its
name. Before source claims that depend on it, show the Lean-produced root
semantic target, the exact bounded library declaration, its selected raw
source connection, and the current hash-bound source-to-library judgment in
the dashboard and human-review packet. A transparent library `def` must be
delta-reduced at that root; compiler-generated helpers under the same root
are expanded rather than made into fake cards, while a reusable dependency
left in the target receives its own card. If Lean marks the root opaque or
non-reducible, show the elaborated signature with exact code and state that
there is no delta expansion. The source connection must be a map item or an
explicit byte-pinned source-anchor bundle with the same raw-input rules as a
paper Spec; a source-map summary, docstring, or library prose does not count.
If no exact paper source connection is available, mark the prerequisite
pending/uncertain and do not let a paper-level `matches` verdict silently
treat it as established. Add uncommon material primitives to the ledger with
their bounded library source path and lines. Do not create a second paper
claim just to restate the library definition, and do not source-match
foundation terminals such as `Nat` or `Finset`.

By default, stop recursive semantic expansion at a Lean-certified erasure or
at a declaration owned by one of the few version-pinned packages in
`config/trusted_foundation_packages.json`. Package ownership is a default
stopping policy, not an unconditional semantic waiver. The registry is
package-level by design: do **not** create a declaration allowlist or routine
semantic-review rows for `Real`, `Set`, `Finset.sum`, ordinary topology, or
their transitive Mathlib internals. Lean must verify the actual package/module
origin against the locked toolchain and dependency state; Python may only
carry or check that result. A reviewer may override this default for a bounded
subtree when an unusual imported concept has a material convention that must
be exposed to compare the paper with Lean.

Package trust accepts the implementation correctness of version-pinned Lean/
Std/Mathlib and treats conventional mathematics as the default stopping point,
but never hides its use in the paper claim. The expanded source-
facing Spec must retain the chosen type, operator, set, order, topology, and
all material arguments, so the direct raw-source judgment still checks choices
such as finite versus arbitrary sets, strict versus weak inequalities, and open
versus closed balls. Do not attempt to revalidate Mathlib's construction of the
real numbers or the semantics of finite sums during each closeout. When a
major or unusual Mathlib notion has a material convention that is not
transparent from its name alone, promote it to a bounded usage-alignment
expansion. Start with its exact elaborated signature and a canonical public
specification theorem or definition display; recursively open material
semantic dependencies only as far as needed to make the paper's intended use
checkable, then stop again at conventional foundations. This is a reviewer
judgment based on occurrence role and convention risk, not package membership.

`Cslib`, `AppliedModelingLib`, and paper modules are prohibited from the foundation
registry. Review only their material domain declarations on the bounded
semantic frontier; do not promote proof helpers or implementation internals to
semantic rows. Reuse a current source/Lean judgment by canonical semantic
identity and exact source bundle wherever the code lives. An unfamiliar
external package fails closed for one explicit classification rather than
launching a transitive audit: review its material declaration, record an exact
pinned theorem boundary, or deliberately revise the small package policy. A
cited or imported theorem must be proved natively, imported with pinned
provenance and an exact reviewed statement, or exposed as an explicit
assumption boundary.

For repository-owned dependencies, let Lean distinguish an explicit semantic
root from a recursively encountered proof value. A theorem selected by an
exact source route remains a review row regardless of its declaration kind or
location. An ordinary proved theorem reached only as a proof argument is not a
second source concept: omit that proof value from the human semantic frontier,
but recursively traverse its complete proposition type and retain every
material definition, predicate, structure, and operation occurring there.
Keep the theorem in the proof, import, build, and axiom closure. Never apply
this erasure to an axiom or opaque boundary, and never infer it in Python from
a name, namespace, result sort, or pretty-printed type. The native Lean graph
must make the distinction, and an ambiguity fails closed.

Apply the repository rule in `docs/ARCHITECTURE.md`: no accepting audit path
parses Lean source in Python or shell code. Lean Meta obtains declarations,
owners, ranges, elaborated expressions, transparent reductions, dependencies,
proof relations, and axiom closure from Lean's environment and APIs. Python
may validate and bind the complete typed response but may not reconstruct or
classify Lean semantics from text, regexes, names, namespaces, line numbers,
declaration kinds, particular typeclasses, result sorts, or paper-specific
shapes. Non-routed transparent workspace definitions are delta-reduced by
Lean into the containing semantic target; their semantics is reviewed there
rather than waived or given a type-specific exception. If a required fact is
absent, extend the small Lean query or fail closed; never add a source-parser
fallback. Lexical scouting is permitted only before a draft elaborates and is
never evidence.

For the Lean-side reducer, a failed `unfoldDefinition?` on an applied
transparent occurrence is not permission to classify or suppress the
declaration. Ask Lean to unfold the elaborated head constant and reapply the
original arguments under the same bound. This covers stuck compiler
auxiliaries generically while keeping every branch in the containing semantic
display; a genuinely nontransparent remainder stays visible or fails closed.
Always give that reducer the union of exact paper-local and reusable-library
source-semantic roots. Code location cannot decide whether a routed concept is
expanded: each explicit root stays named in its dependents and is shown once
as its own full semantic card.

Always materialize a non-evidence frontier preview before starting LLM review.
It must report that no automatic unbounded implementation tree was generated
for trusted Lean/Std/Mathlib packages, while separately counting bounded
Mathlib usage-alignment roots and their recursively opened rows. If the new total queue is unexpectedly large (by
default more than 200 rows, or far larger than the direct material graph
suggests), stop and diagnose a graph classification error before asking an LLM
to review anything. Check module ownership, structure/projection owners,
compiler-generated descendants, proof-only occurrences, unnecessary
foundation usage cards or expansion depth, and missing reusable-judgment reuse. An explicit
review-budget override may authorize a genuinely large paper surface; it may
never omit a material row or convert a domain declaration into a foundation.

Do not infer a foundation disposition from the AppliedModelingLib-only library queue.
Use the `foundation_frontier_preview` emitted by the compiled declaration
graph: it is the only current preview that searches the normalized Spec for
registered package occurrences, explicit promotions, paper/domain roots,
unregistered imports, and erased proof values. The preview is not evidence.
Fresh graph construction must stop on an unregistered imported material root,
and an unfamiliar notion that remains too opaque to compare is `uncertain`
until it is explicitly promoted. Never manufacture a passing zero count from
a discovery lane that did not search the relevant package.

Use one iterative rule for unusual foundation concepts. First inspect Lean's
compact non-evidence list of foundation constants materially retained by each
expanded claim. Treat conventional uses inside the ordinary source-to-Spec
judgment. For a major or unusual imported notion whose convention matters,
select its exact qualified declaration as a promoted semantic root in the
paper's review-surface configuration. Lean must display that root's exact
signature/definition and direct material dependencies; promote a child only if
its meaning is still needed, and repeat until conventional leaves are reached.
Before LLM review, report the promoted-root count, total recursive rows,
maximum depth, and reusable prior judgments. Use the existing
`library_semantic_review.json` judgment and dashboard/packet card for each
promoted definition—never a new foundation-specific receipt or duplicate paper
claim. If the source comparison still depends on an opaque imported name,
return `uncertain` and request another promotion.

Use a role-and-convention judgment, not a namespace or type test, when deciding
whether to promote. A foundation occurrence is normally conventional when its
textbook meaning is stable, its material arguments and use are visible in the
expanded claim, and choosing another standard convention could not change the
source-to-Lean comparison. Promote an unusual concept when its representation
or convention might matter—for example an unordered-pair encoding,
open-versus-closed or finite-versus-infinite variants, an asymptotic filter and
quantifier order, a probability/event interpretation, an extended-value
convention, or a specialized imported construction. These are prompts, not a
hardcoded list. Recursively inspect only the material semantic children needed
to understand that concept, and stop again when the remaining leaves are
ordinary foundations. If reasonable reviewers could disagree, promotion is
the safer choice; a queue-size warning is a diagnostic for accidental
over-expansion, never a reason to conceal a genuinely useful recursive check.

The closeout gate, not only the dashboard, enforces both source-semantic
lanes. Every selected source claim has exactly one direct
`def <name>Spec : Prop := ...` route and one current `matches` entry in
`audit/v11_raw_source_spec_screening.json`; a theorem/lemma, an `abbrev`, a
helper-only body, a duplicate source claim sharing a Spec, an `uncertain`
verdict, a stale byte-pinned paper-source bundle, or a changed Lean-elaborated
semantic target blocks closeout. A hash of the pretty-printed or source-sliced
`Spec` declaration is provenance, not semantic acceptance identity: comments,
formatting, file moves, and a change in source-range extraction must not force
semantic re-review when Lean proves the elaborated target and claim atoms
unchanged. A changed parameter/assumption/conclusion role does invalidate the
judgment even if similar pretty-printed tokens remain. Every material library
declaration explicitly selected as a source-semantic root in
`library_semantic_prerequisite_sources` must be registered with a bounded
declaration location and a current `matches` entry in
`audit/library_semantic_review.json`; an unregistered selected root is a gate
failure, not a dashboard omission. Lean retains the complete recursive
reusable closure for elaboration, proof, import, and axiom checks, but a
proof-only helper without an explicit source connection is not a synthetic
source-review card. The ledger must not duplicate the graph's per-root
dependency map: that map is a regenerable projection with no reviewer
authority. Reissue either ledger only after an
explicit reviewer decision, using the deterministic writers:

```bash
python3 scripts/reissue_v11_raw_source_spec_screening.py --paper <PaperRoot> \
  --decisions papers/<PaperRoot>/audit/v11_raw_source_spec_reissue_decisions_YYYY-MM-DD.json \
  --validator "<reviewer>" --v11-review-graph --write
python3 scripts/reissue_paper_semantic_prerequisites.py --paper <PaperRoot> \
  --decisions papers/<PaperRoot>/audit/paper_semantic_prerequisite_reissue_decisions_YYYY-MM-DD.json \
  --validator "<reviewer>" --v11-review-graph --write
python3 scripts/reissue_library_semantic_review.py --paper <PaperRoot> \
  --decisions papers/<PaperRoot>/audit/library_semantic_reissue_decisions_YYYY-MM-DD.json \
  --validator "<reviewer>" --v11-review-graph --write
```

Before emitting or issuing any semantic-review queue, acquire the one current
non-accepting v11 review graph through the closeout planner:

```bash
python3 scripts/closeout_reuse_plan.py --paper <PaperRoot> \
  --prepare-v11-lean-review-graph
```

The graph transaction—not a dashboard, human-review packet, or packet display
cache—is the sole current writer input for all three review roles. Historical
packets and dashboards remain readable presentation and forensic artifacts,
but an intentionally reopened paper is reviewed against the latest graph
rather than a compatibility reconstruction of its old writer path.

For a fresh or changed v11 source-to-Spec surface, emit its non-evidence
decision work queue from that graph:

```bash
python3 scripts/reissue_v11_raw_source_spec_screening.py --paper <PaperRoot> \
  --emit-current-template --v11-review-graph
```

That queue must display the fully expanded target plus the numbered parameter,
assumption, and conclusion roles emitted by Lean, and bind the canonical claim-
atom and claim-manifest identities. Inspect those exact materials before
filling a verdict. Do not duplicate the large canonical Lean AST in the queue,
and do not issue a schema-3 screen from an older queue that lacks the two
identity bindings.

Every semantic-review work queue must also bind the exact declaration source
that the reviewer saw until receipt issuance. Reject an issuance-time source
change even when the Lean display digest happens to remain unchanged. After
issuance, semantic currentness follows the Lean-elaborated target and claim
identities, so formatting, comments, paths, and line-number changes do not by
themselves demand another review.

For a fresh or changed paper-prerequisite surface, emit the non-evidence
decision work queue from the same graph. Do the same for the reusable-library
surface:

```bash
python3 scripts/reissue_paper_semantic_prerequisites.py --paper <PaperRoot> \
  --emit-template papers/<PaperRoot>/audit/paper_semantic_prerequisite_reissue_decisions_YYYY-MM-DD.json \
  --v11-review-graph --changed-only
python3 scripts/reissue_library_semantic_review.py --paper <PaperRoot> \
  --emit-template papers/<PaperRoot>/audit/library_semantic_reissue_decisions_YYYY-MM-DD.json \
  --v11-review-graph --changed-only
```

During an upgrade or repair, add `--changed-only`. The reissuer may omit a
prior row from the new queue only after proving that its Lean-produced
semantic-target digest and exact byte-pinned source-bundle digest are
unchanged; it preserves that row's original verdict, reason, reviewer, and
date while mechanically refreshing navigation metadata. A new, missing, or
changed identity remains in the queue and still requires an explicit decision.
This is generic semantic reuse, not an engine-version bridge.

The generated candidate source items come from typed source routes and
Lean-produced dependency edges. They are navigation suggestions, not semantic
decisions. Inspect the exact source bytes and full Lean display, select each
source connection, and fill every blank judgment and reason before running the
reissuer. An ambiguous or unrouted declaration must remain visibly unresolved
until that review is done; never select the first candidate merely to satisfy
the schema.

Dependency propagation can identify only a downstream result that uses a
shared model declaration even when a different source item states that
declaration directly. In that case, do not judge against the incidental
passage. Record the exact declaration-to-source-item route under
`paper_semantic_prerequisite_sources` in the paper's
`audit/v11_source_map_preparation.json`, rerun `prepare_v11_source_map.py`, and
re-emit the blank queue. The preparer requires a current source item, and the
queue requires the declaration to belong to Lean's current prerequisite
surface. This routing override supplies no verdict and must not force a new
Lean discovery pass when the compiled interface is unchanged.

Those writers recompute byte identities but never decide a semantic match.
For library rows, a missing decision may reuse the existing verdict only when
the writer proves the exact byte-pinned source bundle and Lean-produced
semantic-target identities unchanged; it then refreshes routing and navigation
metadata mechanically while preserving the original reviewer and date. A new
or changed semantic identity still requires an explicit reviewer decision. Do
not edit hashes by hand or carry an old `matches` decision forward merely
because the declaration name survived.
The writers launch no independent Lean discovery or build. They consume the
same exact current graph held by the planner process, so a decision queue and
receipt cannot drift onto a second discovery surface within one closeout.
Preparing the graph and the later focused closeout build remain required; a
packet cache is never evidence or permission to reuse a verdict.

If the archival source statement is demonstrably false and the paper instead
has an approved, fully proved corrected target, never record that as
`matches`. Keep the archival bytes and statement, mark the map item
`corrected_source_statement`, pin its distinct approved corrected target and
the governing defect, and record only
`matches_approved_corrected_target`. That exceptional verdict is valid only
when both target record and its approval hash are current and it explicitly
disclaims archival equivalence. In the dashboard and human-review packet,
show the archival byte-pinned source first and then the full approved corrected
target, its archival anchor, and its recorded basis; label the reviewer
checkbox as matching the approved corrected target, never the archival text.
A source typo or clarification that preserves
the same endpoint should remain an ordinary `matches` review with the precise
clarification recorded separately.

Obtain that direct-library inventory from Lean Meta after the selected Specs
and every retained paper-local prerequisite elaborate. Python may serialize
the resulting coordinates and verify their hashes, but Lean must also emit the
unique source-presented review owner, source module/range, exact declaration
display, and direct semantic children. Python must not maintain a separate
library glossary, field-projection/constructor owner table, historical line
registry, or qualified-name parser for a current graph-backed closeout. It may
derive human labels as presentation metadata only. If Lean cannot produce a
complete sorted inventory with unique owners and usable source ranges, fail
the library lane rather than fall back to lexical scanning or repository-wide
declaration discovery.

The human PaperInterface, dashboard, and packet show one source claim per
expanded `Spec`, in source/DAG order, with the paired theorem named once as
the verified proof endpoint. Where the paper itself distinguishes main text
from an appendix or supplement, declare presentation sections that exactly
partition the canonical source-claim surface: `Main-text source claims` comes
first and `Appendix and supplement source claims` follows under its own marked
heading. The declared sections may add headings but must preserve the approved
source/DAG linearization: never put a definition below a claim that uses it.
If an appendix-only source item is a prerequisite of a main-text claim, keep
that prerequisite earlier in the human surface rather than forcing it down.
This changes human reading order only: appendix claims remain source claims,
receive the same semantic review, and remain in the denominator. Keep material
prerequisite cards before both sections in dependency order. Do not
show a map summary beside a raw quote as a second source statement, a
Lean-to-TeX paraphrase as a comparison target, or a second wrapper row.
Human-facing source and Lean columns must contain the actual raw excerpts and
expanded proposition respectively.
Treat each raw source excerpt as literal evidence in the dashboard: exclude
its rendered element from MathJax/TeX processing, including dollar-delimited
math, so source environments such as `\\begin{definition}` remain visible
verbatim rather than becoming renderer errors. A displayed source excerpt may
be typeset only in a separately labelled non-verbatim explanatory rendering;
it is never the semantic comparison target.
Render material prerequisite cards in dependency-first order across both
paper-local and reusable-library declarations: a reusable library card comes
before a paper-local card that uses it, and either comes before every source
claim that depends on it. On a paper-local prerequisite card, show the raw
source connection and its one Lean-expanded semantic target; do not repeat the
underlying declaration source as a second Lean statement. A reusable-library
card additionally shows its exact bounded Lean declaration, because that code
is the independently screened reusable implementation rather than a second
paper claim.
Every material library card is individually reviewable: provide a
matches/mismatch/uncertain control and notes field, and record its annotation
in a prerequisite-scoped ledger distinct from the paper-claim review ledger.
Its review status never changes the paper source-claim denominator. Retain
paper-local semantic prerequisites in their current audit ledger and validate
them with the same raw-source discipline, but do not place implementation
scaffolding on the default human packet/dashboard surface unless an explicit
technical-trace review is requested.
For a role-typed v11 map, select claim rows from the typed route set and obtain
their displayed statements from Lean's exact packet targets. Do not reparse
`PaperInterface.lean` in Python merely to rediscover Spec names or silently
drop a routed claim when that parser misses it. Starting from every selected
Spec, follow Lean-reported `direct_paper_declarations` transitively until the
paper-prerequisite frontier closes. Render every resulting material
paper-local prerequisite with its own raw source connection and reviewer card;
do not compute those rows and then omit them from the packet or dashboard.
Implementation scaffolding outside that Lean-reported semantic frontier remains
off the default human surface.
Do not maintain detached `Assumptions.lean` wrapper declarations as a second
semantic lane when the v11 Specs already expose those premises and the
paper-prerequisite graph exposes every material model structure. Such wrappers
may remain as documentation, but `review_surface.assumption_names` must list
only declarations genuinely used by the configured proof/review surface.
Removing an unused duplicate wrapper does not remove the premise from the
claim-atom, raw-source, prerequisite, proof, or build checks.
Do not create an unmarked human-review packet until the paper has explicitly
activated its v11 raw-source-to-Spec surface and source map. An earlier
interface may be rendered only as a prominently labelled draft diagnostic; it
is never a review or closeout artifact.
The packet is intentionally compact: one numbered row, no repeated declaration
title or type/kind fields, raw source input, one Spec, one separately named
proof endpoint, a recorded source-to-Spec verdict/reason, and a usable
annotation box. Start every source claim and every material prerequisite card on a
fresh page and normally keep it to one page. When the exact raw source bundle
including required semantic context, or the fully expanded Spec, genuinely
does not fit, continue that same item without inserting another row; never
replace the omitted material with a paraphrase. Do
not put validator branding, receipt dates, stale flags, or implementation
history in every row; those belong in the sidecar or final closure receipt.
Keep the packet's `How to use` note equally direct: tell the reviewer to
compare the exact source excerpts with the expanded specification and annotate
the row. Do not explain proof-endpoint deduplication, internal receipts,
dependency closure, focused builds, or the audit architecture there.
Put a linked table of contents at the top of both the packet and dashboard.
It lists dependency-ordered prerequisite cards and the main-text/appendix
source-claim sections, with each item linking to its card; the dashboard link
must also open its enclosing paper and collapsed card before scrolling. At the
top of every packet, add short fresh-fork/clone instructions for opening that
paper's dashboard from the repository root (`lake exe cache get` on a new
clone, then `python3 scripts/review_dashboard.py --paper <Paper> --serve` and
the printed localhost URL). Keep this operational note short and separate from
the mathematical review instructions.

For a `Spec`/proof contract, Lean Meta must establish exact elaborated
proposition equivalence and traverse the paper-local transparent dependency
graph. Python may validate artifact pins and display diagnostics, but it must
not recursively normalize binders or expression trees to grant semantic proof
credit. Batch these Lean checks per review module and reuse the artifact-pinned
verdict for every downstream consumer.

For a global algorithmic claim, audit the exact input domain, state transition,
terminal outcomes, termination, and numeric representation. Require coherent
joint witnesses, nonempty valid families, and surjectivity where syntax is
claimed to represent the semantic domain. A local/refinement theorem needs a
checked global bridge before it can establish the advertised endpoint.

For a runtime claim, inspect the executable's transitive semantic operational
dependency graph across every branch reachable over the claimed input domain.
Show that no reachable branch still evaluates an old semantic closure or oracle;
function and declaration names are routing only. When eliminating closure work
is material, require a cost-threaded executor or generated IR/C evidence pinned
by source and artifact digests to the audited build, plus a worst-case recurrence
that charges traversal, duplication, rebuilding, representation, and arithmetic
bit growth.

## Corrections And Assumptions

Apply the categories in the normative protocol:

- Classify mathematical disposition separately from severity. A printed clause
  can be literally false and require correction while the correction remains
  minor because it preserves the algorithm, iterates, oracle model, primitive
  assumptions, model-class generality, qualitative theorem, and asymptotic
  rate. Before calling a repair substantive, state exactly which of those
  objects or guarantees changes. A pairwise terminal check for the same
  alternating procedure, an integer-safe count, or an explicit premise needed
  only to call an otherwise unchanged local optimum a positive certificate
  normally belongs with typos and clarifications, not a paper-level caveat.
- Analyze coupled edits clause by clause. Do not label an entire algorithm or
  theorem substantive merely because one conclusion needs a small premise.
  Separate an arbitrary-start guarantee that remains true from a narrower
  positive-output clause, and state plainly what remains unchanged.
- When a minor clarification is mathematically easy to misunderstand, keep it
  in the ordinary typo/clarification summary and also write a short standalone
  paper-local memo. Explain the paper's existing algorithm, the exact reason
  the printed test or clause is insufficient, the smallest repair, the
  resulting theorem, the unchanged guarantees and generality, and precise
  source locations. Do not inflate its status to justify the separate memo.

- An implicit source condition or equilibrium refinement made explicit is a
  formalization note when it expresses the paper's model. Call it a
  **clarification** in human-facing prose, not a correction. Record it in the
  theorem statement and post-formalization report; it is not automatically a
  caveat or extra assumption.
- Reserve **correction**, **corrected**, and **repair** for a demonstrable
  false source formula, statement, or proof step, or for an explicitly approved
  replacement target. Do not use those words merely because the formalization
  makes an intended model condition or convention explicit.
- A genuine non-source condition is an additional assumption. Keep it visible
  in Lean and the report and never attribute it silently to the paper; the
  original source endpoint remains partial.
- A minor typo, equality/inequality convention, appendix slip, or proof repair
  that preserves the advertised endpoint is a `formalized_note`, not a caveat.
- A substantive corrected target needs explicit approval, defect IDs, pinned
  archival and corrected statements, and `archival_equivalence_claimed: false`.
- Interpret **human-approved** conservatively. The governing user decision must
  identify the exact mathematical replacement unambiguously, including every
  changed constant, inequality, branch condition, quantifier, domain, and
  algorithmic step that matters. General permission to continue, close or
  publish a paper, accept clarifications, or use a broadly described
  "corrected target" does not approve one particular repair among several
  mathematically distinct choices. A report sentence, agent-authored summary,
  status label, or approval of a larger campaign is not a substitute. If the
  cited user language could govern more than one plausible replacement, keep
  the target unapproved and ask for the narrow decision; never retrofit an old
  broad comment to a newly specified formula.
- Re-analysis is not permission to erase or repeatedly re-litigate a decision
  the user already settled. Before presenting a source reading, null-set
  convention, proof deviation, typo disposition, or status choice as open,
  inspect the paper's earlier validation reports, clarification/correction
  memos, proof-deviation notes, recorded feedback, and approval records. Carry
  forward an exact prior decision when the mathematical target is unchanged.
  For a substantive corrected target, use narrative files to locate the
  governing approval and retain its exact scope; do not promote an agent's old
  prose summary into approval or silently override it with a fresh guess.
- If the repository proves a cited auxiliary theorem natively and the current
  paper result consumes that checked theorem, describe it in the validation
  report as a **proved dependency**. It is not an external boundary, caveat, or
  partial-formalization marker merely because the result first appeared in a
  different paper.
- Freeze source-proof-fidelity links before issuing the terminal coverage
  receipt. Direct source-item `source_defect_ids` are cross-references owned by
  the source-proof-fidelity validator: adding or renaming only those links does
  not change the raw source statement or its source-to-Lean judgment and must
  not trigger another LLM review. The validator must still prove that every
  repaired defect reaches an exact Lean-checked semantic contract. By
  contrast, `corrected_target.governing_defect_ids` are part of the approved
  replacement target and remain semantic invalidators.
- Per-item coverage identity schema 6 embodies that ownership boundary. A
  schema-5 row remains directly readable when its exact prior identity is
  unchanged. For an in-flight schema-5 row whose only map edit is the addition
  of validated direct defect cross-references, migrate the generated identity
  only after an exact old/current projection comparison and a zero-finding
  source-proof-fidelity check; preserve the judgment, source pins, Lean row
  signatures, validator, and verdict. Do not rerun an LLM or create an
  engine-pair compatibility bridge. New receipts use schema 6 directly.
- “Formalized with caveat” is reserved for a material accepted boundary, not a
  difference of opinion, routine regularity, null-region convention, typo, or
  proof-strategy repair.

When `=` versus `<=`/`>=`, strict versus weak, or a similar source convention is
ambiguous, ask the user if available. Otherwise make the truth-preserving
condition visible, record it, continue actionable proof work, and raise it at
the next interaction.

## Proof Campaign Pace

After the statement and visible premises are audited, prioritize mathematical
obligations. Do not interrupt an actionable proof campaign for broad audit-code
expansion, rendered DAGs, status prose, repeated semantic extraction, or
whole-paper regeneration.

Update documentation at these boundaries only:

- material source-scope or source-version change;
- assumption/correction decision;
- meaningful proof boundary or blocker;
- handoff or paper transition;
- paper closeout.

At a blocker, leave the strongest compiling paper-facing statement with
`sorry`, exact source anchors, dependency order, forbidden shortcuts,
acceptance conditions, and a copy-paste assignment prompt. This is more useful
to a less capable model than a narrative progress log.
