# Formalization Notes

This file preserves the previous hand-written paper-folder README content.
The paper-folder `README.md` is now a generated status overview.

# Agentic Delegation and the Language Frontier of Software Developers

## Source Version

- Paper: *Agentic Delegation and the Language Frontier of Software Developers*
- Authors: Alexander Quispe and Kevin Xu
- Version formalized: arXiv 2605.25438v2, 2026-07-07
- Official URL: https://arxiv.org/abs/2605.25438
- Public PDF: https://arxiv.org/pdf/2605.25438.pdf

Without a statement spec, a downloaded PDF is cached as `source.pdf` and ignored
by Git. A statement spec's SHA-256-verified source bytes are copied to a stable
paper-local `source-audited.*` path recorded in `audit/paper_statement_map.json`.
These artifacts are ignored by default. Unignore one only after an explicit
redistribution-rights review; machines without the private bytes must leave the
source-evidence gate unresolved rather than accepting the digest alone.
The extracted text cache is `source.txt` when `pdftotext` succeeds, and is also
ignored by Git in public workspaces unless redistribution rights have been
checked separately.

## Paper-Facing Ledger

- Implementation theorem file: `QX26AgenticDelegation/MainTheorems.lean`
- Human-facing theorem file: `QX26AgenticDelegation/PaperInterface.lean`
- Machine-readable status source: `QX26AgenticDelegation/status.json`
- Private outside-Lean proof plan: `QX26AgenticDelegation/docs/FORMALIZATION_PLAN.md`
- Final validation report: `QX26AgenticDelegation/FINAL_VALIDATION_REPORT.md`
- Dependency DAG: `QX26AgenticDelegation/docs/DependencyDAG.tex`
- Rendered DAG: `QX26AgenticDelegation/docs/DependencyDAG.pdf`
- LLM/source audit sidecars: `QX26AgenticDelegation/audit/*.json`

`PaperInterface.lean` should be readable on its own: expose source formulas,
transparent statement specifications, and theorem/lemma proof routes there,
with short closed proofs that call into `MainTheorems.lean`. Do not mark a row
`formalized` unless the Lean declaration is closed and the remaining assumptions
cell is `None`.
Keep the dashboard surface curated but complete for source-labelled formal
material: definitions, formulas, propositions, theorems/corollaries, named
claims, and main-text lemmas that a reviewer or LLM-as-judge should inspect.
Do not omit source-visible named material merely to keep the dashboard compact.
Appendix theorems/corollaries should be represented; appendix lemmas are a
judgment call, but if they carry paper-facing mathematical content needed for
the formalized claim, expose review-legible rows rather than hiding them in a
broad support bundle. Catalog unnumbered prose assertions separately. They are
claim-bearing but, under the standing user-approved scope policy, are not
independent theorem targets unless explicitly opted in; retain exact source
anchors and a `user_approved_scope_exclusion` record rather than silently
omitting them or using Lean declaration names to decide scope.

Use the controlled status vocabulary from `../../docs/STATUS.md`. Public-facing
rows should use `partially formalized` for results that still depend on an
external theorem, certificate, or proof boundary, and should name that boundary
in the final column rather than using `conditional` as a separate status label.
Keep theorem/table content synchronized with `DependencyDAG.tex` node styles and
`MainTheorems.lean` declarations before marking a row `formalized`. Keep
`status.json` as the source of truth for review rows, artifact paths, and the
paper's top-level public status.

At the start of the paper, fill in the target-relevant part of
`docs/FORMALIZATION_PLAN.md`'s `Initial Outside-Lean Paper Audit` section. Read
the source closely enough to establish the current source-shaped target,
visible assumptions, formula risks, and likely proof seam. This is a compact
source-target setup gate, not a reason to delay an actionable proof for a full
DAG, status/report refresh, or exploratory work. Alert the user early about a
material source defect or missing assumption.
Before drafting Lean, independently inventory every material source atom from
the exact pinned source quote bytes. The inventory is source-side work: do not
derive it from theorem, binder, field, function, or source-map names. After that
inventory and the first compact `PaperInterface.lean` statement skeleton exist,
give every in-scope theorem/formula claim one transparent
`<name>Spec : Prop := <complete source-shaped statement>` in
`PaperInterface.lean`, with its separate
`theorem/lemma <name> : <name>Spec := by sorry` endpoint in
`ProofInterface.lean`. Audit the specification, not the theorem name; Lean
Meta must later confirm that the proof declaration has exactly that type. Do
not put a desired conclusion in `Assumptions.lean`, a record field, or a
helper theorem to avoid the hole. `scripts/new_paper.py` accepts these targets
through `--statement-spec`; without that source-pinned input it intentionally
generates an empty interface rather than a fake `True` target. Audit each
skeleton row's statement and premise provenance before
treating it as a source-faithful target; perform broader source-record and
report work at the next material audit boundary. Then run the statement
target-setting pass:
populate
`audit/lean_to_tex_llm.json`, populate `audit/statement_match_llm.json`, and run
`python3 scripts/review_dashboard.py --paper QX26AgenticDelegation --statement-precheck`.
Also populate `audit/paper_statement_map.json` for the normal source surface,
then run the paper-level coverage pass and save `audit/paper_coverage_llm.json`.
Normal scope is source-named theory: visibly numbered or named definitions,
results, claims, formulas/equations, algorithms, assumptions/model conditions,
and named appendix items. Figures, captions, tables, numerical examples,
simulations, empirical material, and ordinary prose need an explicit deep-paper
audit; map keys and Lean names never decide scope. This source-to-row accounting
is separate from the row-local statement judge.
For a source-game theorem with a best-response/equilibrium comparison over
feasible actions and a posterior, conditional expectation, belief, or
observation-contingent payoff, add a byte-pinned
`semantic_context_requirements` entry of kind
`strategic_observation_totality`. The v10 audit will then require a
source/signature-bound review of zero-probability/off-path observation branches,
the source conditioning population, any selected sequential action history, event
measurability/null handling, and every declared conditionalization mode, including
any a.e. RCD/disintegration fibre/base scope.
Do not call a Lean default conditional value source-faithful unless the source
itself totalizes it or explicitly removes that branch/action from the
equilibrium comparison.
For any source row that asserts a conditional expectation, Bayesian/PBO belief,
or conditional law, add a byte-pinned `semantic_context_requirements` entry of
kind `conditioning_information`. Its contract must enumerate the source
observed components, ordered action-selection stages, raw-vs-selected law
population, and positive-event/pointwise/a.e. conditionalization scope. The
source-record review will require an exact source/signature-bound Lean-side
comparison for each component and stage; a raw posterior, coarser observed map,
or pointwise reading of an a.e. RCD is not a direct source match.
For a source model whose stated primitives are meant to imply a process, cycle,
execution trace, or conditional-law conclusion, add a byte-pinned
`semantic_context_requirements` entry of kind `source_model_derivation`. Its
schema-2 contract must enumerate the source primitive components and the derived
conclusion, with a separate exact `source_location` and byte-pinned
`source_anchor_evidence` for every component and for the conclusion itself. The
source-record review will require a current source/signature-bound mapping for
every primitive and a checked Lean derivation route. If the generated expanded
surface structurally detects a caller-supplied model-construction package, the
current generic auditor is deliberately fail-closed: record only
`documented_partial_boundary`; a declaration name or free-text derivation route
cannot restore a direct match. Recovering that direct route requires a separate
machine-generated primitive-level Lean derivation receipt with a clean expanded
input surface. A record field that merely supplies the process/cycle/trace/law
is an open partial-formalization boundary, not a source-faithful direct match.
If a source item is represented using a reusable library definition/theorem,
do not point the inventory directly at the reusable declaration as evidence.
Add a paper-local bridge/equivalence declaration, put that declaration on the
reviewed or assumption surface, add a `Source status:` line to its
paper-facing comment, and list it in the inventory under
`semantic_bridge_declarations`, `paper_equivalence_declarations`,
`source_equivalence_declarations`, or `library_bridge_declarations`. The
repository audit rejects hidden bridge helpers and name-only matches.
Then run `python3 scripts/review_dashboard.py --paper QX26AgenticDelegation
--assumption-precheck`: the statement judge is row-local and does not certify
that theorem premises are source assumptions or derived facts. Use this pass
only to correct theorem targets and premise provenance; do not update the DAG,
final validation report, human-review log, or review-surface audit just because
this early check ran. Freeze the current v11 Lean declaration manifest/digest for
every matched specification/proof route in the plan before proof work. Replace
each `sorry` without changing the elaborated specification or its paired proof
type; any signature change invalidates the statement audit and must repeat this
phase. Draft `sorry`s are never permitted at closeout. At formalized closeout,
enable the v11 source-to-Spec correspondence: bind every source atom to the
current elaborated Spec surface, inspect the entire Lean closure including proof
and instance arguments, and give every material closure terminal a source atom,
approved source correction/additional assumption, checked Lean derivation, or
version-pinned foundation disposition. There are no automatic data, container,
or name-based exemptions. Reuse this evidence only per unchanged item identity:
source atoms, Spec closure, narrow closure environment, and exact theorem type;
legacy v10 evidence remains readable but is not a v11 credential.

At review boundaries, populate `audit/statement_match_llm.json` with one
judgment per source claim. The only source-side input is the exact ordered
bundle of byte-pinned `source_anchor_evidence` quotes plus any separately
byte-pinned `semantic_context_requirements` quotes. The only Lean-side input is
the fully expanded transparent `...Spec : Prop`. Do not give the judge a
source-map summary, source-claim paraphrase, theorem label, Lean-to-TeX
translation, explanation, or thin proof wrapper. The receipt records
`source_input_protocol: verbatim_source_anchor_bundle_v1`, its bundle digest,
`lean_target_protocol: expanded_paperinterface_spec_v1`, the semantic Spec
declaration, and the expanded-Spec digest. A row may be judged `matches` only
if those exact raw inputs are semantically equivalent, including all
hypotheses, subparts, quantifiers, domains, constants, normalizations, signs,
inequality directions, conclusions, and visible inputs. Every input premise
must be accounted for as a paper primitive/source assumption, a Lean-derived
consequence of those primitives, or an explicit conditional boundary. Inspect
named Lean predicates/wrappers semantically; never approve from labels or
phrase overlap. A Lean-to-TeX rendering is optional display metadata, never an
input to or prerequisite for this semantic judgment. If the expanded Spec is a
conditional wrapper, source-row package,
certificate/replay/process/bridge package, omitted subclaim,
weakened/strengthened statement, hidden strengthening inside a named predicate,
or broad aggregate for several displayed formulas, the judge must mark
`mismatch` or `uncertain`. Include raw-source-input and expanded-Spec digests
plus the judge model/agent name, validator type, validation timestamp, and any
validator comment. If the judge flags a mismatch
   or uncertainty, iterate on the Lean statement before treating it as the paper
   theorem target. At an active statement-review handoff, use
`python3 scripts/review_dashboard.py --paper QX26AgenticDelegation --precheck` only to
diagnose missing/stale statement-audit rows. It is not a frozen-closeout
predecessor: after report, status, map, and DAG inputs are frozen, start with
`python3 scripts/closeout_reuse_plan.py --paper QX26AgenticDelegation` and execute only its
current `next_action`.
For every `source_routes` entry, pin the canonical source item, current source
statement digest, and exact locator, then record semantic scope/evidence in the
obligation ledger. Use `direct` only for an exact equivalent paper-facing
endpoint with an exact source-conclusion/Lean-conclusion equivalence. List each
scoped composite component as `source_component`; it needs semantic evidence
and a Lean conclusion, not a fabricated full-theorem equivalence.
`source_model_convention` is only for an explicit model reading, and
`defect_or_remark_support` only for a quarantined defect or support-only prose.
Use `proof_support` only with a substantive source-support scope; it never
supplies endpoint coverage. Names are navigation only, not route evidence.
All audit sidecars are fail-closed. Blank scaffolded files, missing prompt
versions, stale prompt versions, missing current digests, missing
validator/model identity, missing timestamps, unrecognized judgments, failed
judge runs, and items without explicit success verdicts remain audit alarms
until rerun against the current Lean/source inputs.
If any paper-facing theorem takes a hypothesis that is not proved from prior
Lean declarations, declare that hypothesis in `Assumptions.lean`, list it in
`status.json` `review_surface.assumption_names`, and populate
`audit/assumption_match_llm.json` with an independent judgment that it is a true
paper/source model assumption rather than a proof shortcut.
When a source proof route is used, maintain `audit/source_proof_fidelity.json`.
Inventory every discovered proof-text defect by source locator, mathematical
claim, repair obligation, and acceptance condition. A corrected proof line is
never a source assumption: prove its replacement derivation or leave an
explicit proof boundary. This ledger is semantic evidence, not a Lean-name map.
If a defective printed result is quarantined and a Lean counterexample or
refutation is used as support, populate `audit/defect_support_match_llm.json`
with an independent semantic judgment. It must freeze the exact defect record,
source statement, Lean statement, elaborated signature, and every signature
atom; a theorem name, theorem kind, or tautology such as `True` is not defect
support. Rerun the source-to-Lean precheck after either source or Lean changes.
The repository audit follows paper-local helper chains recursively: a theorem
is not closed if any helper it depends on still consumes an unvalidated
certificate, source-row equation, hidden hypothesis, or proof-boundary premise.
Do not use `axiom`, `constant`, `opaque`, or unsafe declarations to bypass that
provenance boundary.
If the dashboard has more than 30 rows, also populate `audit/review_surface_llm.json`
with a no-paper-context LLM audit that checks whether every dashboard row is a
paper-facing definition, formula, or named statement. At 120 or more rows, treat
the dashboard as oversized and curate `PaperInterface.lean` or
`status.json.review_surface.include_names` before broad human review.
For public-facing closeout, populate a current `audit/review_surface_llm.json` even
when the dashboard has 30 or fewer rows; the row threshold is an early review
prompt, not a final-audit exemption. During active source-map repair, use
`python3 scripts/review_dashboard.py --paper QX26AgenticDelegation --paper-coverage-precheck`
to diagnose missing, stale, partial, or uncertain coverage. Do not rerun that
precheck as a frozen-closeout precursor: the planner determines whether an
unchanged coverage receipt is reusable or which current item needs repair.
For efficiency, run `--source-inventory-check` first after a source-map change;
when the cache is current, use targeted `--statement-check` and
`--paper-coverage-check` before rebuilding manifests. Once the source map,
interface, and status surface are stable, refresh the target-paper cache once
during active review, or let the planner schedule it at frozen closeout. Let the
manifest tool use its bounded chunk retry and per-row fallback; do not restart a
whole-surface manifest extraction for a few failing declarations.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Proposition 1 (Frontier expansion) (Proposition 1; page 13 of arXiv 2605.25438v2 PDF; Appendix A.3 page 59) | `Proposition1_frontierExpansionSpec` -> `Proposition1_frontierExpansion` | statement specification + proof stub | `PaperInterface.lean` | The transparent `...Spec : Prop` is the statement-audit target; the proof body is `by sorry`; raw-source-to-expanded-Spec judgment and premise provenance pending |
| Proposition 2 (Activation band for unfamiliar languages) (Proposition 2; page 13 of arXiv 2605.25438v2 PDF; Equation (8); Appendix A.4 page 60) | `Proposition2_activationBandSpec` -> `Proposition2_activationBand` | statement specification + proof stub | `PaperInterface.lean` | The transparent `...Spec : Prop` is the statement-audit target; the proof body is `by sorry`; raw-source-to-expanded-Spec judgment and premise provenance pending |
| Proposition 3 (Dynamic cumulative-language effect) (Proposition 3; page 15 of arXiv 2605.25438v2 PDF; Equation (10); Appendix A.6 pages 61-62) | `Proposition3_dynamicCumulativeSpec` -> `Proposition3_dynamicCumulative` | statement specification + proof stub | `PaperInterface.lean` | The transparent `...Spec : Prop` is the statement-audit target; the proof body is `by sorry`; raw-source-to-expanded-Spec judgment and premise provenance pending |
| Proposition 4 (Specialist and ability heterogeneity) (Proposition 4; Appendix A.5 page 60 of arXiv 2605.25438v2 PDF; Equation (22)) | `Proposition4_specialistHeterogeneitySpec` -> `Proposition4_specialistHeterogeneity` | statement specification + proof stub | `PaperInterface.lean` | The transparent `...Spec : Prop` is the statement-audit target; the proof body is `by sorry`; raw-source-to-expanded-Spec judgment and premise provenance pending |
| Proposition 5 (Repository expansion) (Proposition 5; Appendix A.8 page 63 of arXiv 2605.25438v2 PDF) | `Proposition5_repositoryExpansionSpec` -> `Proposition5_repositoryExpansion` | statement specification + proof stub | `PaperInterface.lean` | The transparent `...Spec : Prop` is the statement-audit target; the proof body is `by sorry`; raw-source-to-expanded-Spec judgment and premise provenance pending |

## Intake Checklist

- [ ] Confirm the official PDF URL, version, and bibliographic fields.
- [ ] Extract/confirm all named definitions, lemmas, and theorems in source order.
- [ ] Fill in `docs/FORMALIZATION_PLAN.md` with the initial outside-Lean paper audit,
      formula/result sanity check, proof strategy, and likely hard seams before
      deep Lean work.
- [ ] Record the shared-library reuse checkpoint: mathlib, cslib, optlib,
      potential upstream Lean sources, and `EconCSLib` modules/declarations
      inspected; API chosen; near-misses.
- [ ] For every source-defined object represented by a reusable library
      definition/theorem, plan a paper-local semantic bridge/equivalence row;
      do not rely on matching Lean/library names as source evidence.
- [ ] Cite upstream material used or ported: repository URL, file/module path,
      commit or release when available, license status, and what was reused.
- [ ] Record the formal target map: rows to prove, empirical/out-of-scope rows,
      and any explicit boundary that would remain if the paper cannot close now.
- [ ] Replace the initial placeholder with one transparent exact source-shaped
      `<name>Spec : Prop` plus one theorem/lemma `<name> : <name>Spec` per
      in-scope paper-facing claim, using `by sorry` only as the temporary private
      proof body.
- [ ] Independently inventory every material source atom against exact pinned
      source quote bytes before consulting Lean; do not use identifiers or type
      shape as a substitute for source semantics.
- [ ] Run source-record/conclusion-provenance on the complete skeleton before
      any proof implementation; resolve circular or conclusion-bearing inputs.
- [ ] Run the raw-source-to-expanded-Spec statement target-setting pass and fix
      mismatched theorem targets before serious proof work. Review one
      transparent `Spec` per source claim, retain the paired theorem only as
      the proof endpoint, and record/freeze every canonical signature digest.
- [ ] Complete the five fidelity-risk dimensions semantically; bind each
      applicable match to a Lean conclusion, and never use declaration or
      function names as the evidence.
- [ ] Run the assumption/hidden-premise precheck before proof work; do
      not treat row-local statement matches as globally certified targets until
      premise provenance also clears.
- [ ] Run the source-record/boundary-input audit if any reviewed theorem uses a
      record, certificate, replay, process, bridge, source-row, or broad package
      premise.
- [ ] Audit each source proof route used and update
      `audit/source_proof_fidelity.json`; never normalize a proof-text defect
      into a source assumption.
- [ ] Confirm `scripts/audit_conclusion_provenance.py --paper QX26AgenticDelegation` reports
      no circular constructor, missing configured row, recursion failure, or
      unclassified conclusion-bearing input for the frozen skeleton. The full
      repository closeout audit is intentionally deferred while `sorry`s remain.
- [ ] Before a full status, complete v11 source-to-Spec correspondence: each
      atom binds to the elaborated Spec surface; the theorem type is exactly the
      transparent Spec; the closure includes proof/instance arguments; and every
      material terminal has a source, approved correction/additional assumption,
      checked derivation, or version-pinned foundation disposition.
- [ ] Create or update `docs/DependencyDAG.tex` at a paper milestone or
      closeout; do not rerender it for every proof-row edit.
- [ ] Replace the `PaperInterface.lean` placeholder before adding review rows;
      add `MainTheorems.lean` proof implementations only after the statement
      signatures are audited and frozen.
- [ ] Keep `PaperInterface.lean` and `status.json` `review_surface` limited to
      source-facing definitions and named statements.
- [ ] Route every non-derived paper-facing theorem premise through
      `Assumptions.lean`, then run the assumption-provenance LLM judge.
- [ ] If the dashboard has more than 30 rows, run the LLM review-surface audit;
      if it has 120 or more rows, curate the interface before broad review.
- [ ] Run the byte-pinned raw-source-to-expanded-Spec semantic judgment before
      asking for human dashboard review. A Lean-to-TeX translation may be kept
      as optional display metadata but must not be used as semantic evidence.
- [ ] Update `status.json`, then run `python3 scripts/sync_paper_status.py
      --paper QX26AgenticDelegation`. Defer the unscoped aggregate/site sync to integration
      or release.
- [ ] Rebuild `docs/DependencyDAG.pdf` and verify visually at a paper milestone
      or closeout when the DAG changed.

## Post-Formalization Checklist

- [ ] Run a library elevation pass over paper-local proof modules and record
      reusable candidates or completed extractions in `FINAL_VALIDATION_REPORT.md`.
- [ ] Update `docs/DependencyDAG.tex`, rerender `docs/DependencyDAG.pdf`, inspect the
      rendered diagram, and record the DAG audit evidence in both
      `FINAL_VALIDATION_REPORT.md` and `docs/POST_FORMALIZATION_AUDIT.md`.
- [ ] After the report/DAG/status updates, run
      `python3 scripts/closeout_reuse_plan.py --paper QX26AgenticDelegation`, follow its
      dependency-ordered actions through any explicit replan, and execute its
      exact `strict_closeout` argv.
      This audit includes the DAG/final-report closeout gate; resolve all
      findings for this paper before claiming the post-formalization workflow is
      complete.
- [ ] Do not run a second repository-wide provenance audit after a passing
      consolidated closeout. Use a standalone provenance command only to
      diagnose the named failing lane or at an explicit integration/release
      boundary.
