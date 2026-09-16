# Formalization Plan: Agentic Delegation and the Language Frontier of Software Developers

This is a working scratchpad for outside-Lean proof thinking. Keep it short and
useful; it is not the final validation report. Once the current source-shaped
target and audited `PaperInterface.lean` skeleton are present, prioritize the
next proof obligation; update this document at material boundaries rather than
after routine proof steps.

- Namespace: `QX26AgenticDelegation`

## Initial Outside-Lean Paper Audit

- Source version / local files inspected: arXiv 2605.25438v2, 2026-07-07; pinned PDF SHA-256 cddc048711c43022d5fd01b995bfb1114c728c8c879b809b5fdc354a391d3c35
- Source/version mismatch notes: none (version string matches statement spec)
- Complete named-result ledger status: five proposition Specs in PaperInterface (Props 1–5); empirical ATT Eqs. 11–13 out of scope
- Formula sanity check:
  - Signs, constants, normalizations, quantifiers, domains: closed-form CARA CE (Eqs. 14–15) kept paper-local; activity `Z=1[V≥0]`
  - Density vs mass / likelihood-kernel representation issues: none on the five Specs (no probability space in the mathlib-level statements)
  - Dependency map between named source results: Prop 1 ≺ Prop 2 band; Prop 3 uses hazards; Prop 4 uses Ass 3; Prop 5 uses Prop 1 monotone activity
  - Formula-bearing displayed claims that need derivation, not source-row assumptions: Eqs. 1–8, 10, 14–15, 20–22
- Named result sanity check:
  - Results that look correct as stated: Props 1–5 algebraic cores
  - Suspected bugs, missing assumptions, or ambiguous wording: none on the five Specs
- Source-proof fidelity ledger (`audit/source_proof_fidelity.json`):
  - Proof scopes reviewed by source locator and mathematical claim:
  - Source proof defects, if any, with repair obligation and acceptance condition:
  - Proof-only defects kept out of `Assumptions.lean`:
- Shared-library reuse checkpoint:
  - Mathlib declarations/modules inspected: Real, Finset.sum, max/min, pow_le_pow_left₀
  - Cslib declarations/modules inspected: none used
  - Optlib declarations/modules inspected: none
  - Other potential upstream sources inspected: standalone QX26AgenticDelegation Lake package
  - Upstream sources used or ported, with citation/provenance: standalone Model/MainTheorems (same arXiv version)
  - Existing `EconCSLib` declarations/modules inspected: Probability.Gaussian, Optimization.Argmax, Math.ThresholdCharacterization
  - API chosen and near-misses: reused `EconCSLib.Decision.IsPointwiseMax`; kept closed-form CE (Gaussian/ThresholdCharacterization do not fit without new bridges)
  - Source-defined objects that will use reusable library definitions, and the
    planned paper-local semantic bridge/equivalence rows: none beyond IsPointwiseMax
- Proof strategy consequences:
  - Source proof route to follow:
  - Cleaner Lean route or reusable library route:
  - Major issues already reported to the user:
- Algorithmic complexity audit, when applicable:
  - Transitive operational dependency graph over every reachable branch and old semantic closure/oracle dependencies:
  - Worst-case recurrence and bound over the stated input-size measure:
  - Traversal/enumeration lengths, duplicates, and materialization/rebuild charges:
  - Representation/container primitives and rational bit-growth work accounting; missing/excluded work withholds a runtime match:
  - Pinned evidence when closure elimination is material: artifact/source hashes and semantic binding to generated IR/C or a cost-threaded executor:

## Source Inventory

- Definitions / formatted paper objects:
- Named lemmas / propositions / theorems / corollaries:
- Named assumptions / model conditions used by those results:
- Deep-only prose, standalone formulas, algorithms, figures, simulations, and
  computational examples (record scope disposition; do not create normal-mode
  proof targets merely because they are numbered or displayed):

## Intake Freeze Boundary

Do not begin the main proof campaign until this boundary is complete. The
purpose is to discover missing conclusions and hidden premises while changing
the statement skeleton is still cheap, rather than during final closeout.

- [ ] Exact source version and every source artifact used by the normal-scope
      inventory are byte-pinned.
- [ ] The independent normal-scope inventory contains every named theoretical
      definition, result, and source assumption, with explicit dispositions for
      exclusions. Navigation names are not coverage evidence.
- [ ] Every selected result has source-first premise/conclusion atoms, exact
      anchors, and one complete transparent `Spec : Prop` in `PaperInterface`.
- [ ] The proof-obligation dependency order below is acyclic and assigns one
      owning module to each result; concurrent agents do not share an item.
- [ ] One focused manifest/statement/source-record review has frozen the exact
      statement identities. After this point, a proof-body-only edit reopens
      proof closure and compilation, not the human statement judgment.
- [ ] That fully current initial review has written entry-local reuse pins with
      `semantic_audit_reuse.py --bootstrap-current --write`; this is a one-time
      identity seal, not a stale-evidence override or a new human judgment.
- [ ] The dashboard cache is created once after this freeze, never during bare
      scaffold creation.

### Proof-obligation order

| Order | Source-semantic item | Dependencies | Owning module / agent | Statement frozen | Proof status |
|---:|---|---|---|---|---|
| 1 | Fill from the independent source inventory | none | | no | pending |

## Initial Proof Strategy

- Main theorem chain:
- Likely reusable `EconCSLib` seams:
- Paper steps that look underspecified or analytically hard:
- Formal target map:
  - Rows to fully prove now:
  - Empirical/descriptive rows out of formal theorem scope:
  - Explicit assumption/certificate boundaries, if any:
- Planned fallback route if the source proof is too informal:

## Audited Statement Skeleton

Before drafting Lean, independently inventory every material source atom against
the exact pinned source quote bytes. Then replace the generated placeholder with
every in-scope paper-facing theorem/formula statement as a transparent
`<name>Spec : Prop`, followed by `theorem/lemma <name> : <name>Spec := by sorry`.
Audit and freeze the specification's canonical declaration-manifest digest; Lean
Meta must confirm the paired proof route has exactly that elaborated proposition.
The inactive source-map `semantic_contract_template` records only the
spec/proof pairing to promote after source review and proof completion. Never
treat the `by sorry` route, an identifier, or a type/container label as active
semantic contract or proof evidence.

At formalized closeout, complete v11 source-to-Spec correspondence. Bind every
source atom to the current elaborated Spec surface, traverse the full Lean
closure including proof and instance arguments, and give every material closure
terminal a source atom, approved source correction/additional assumption,
checked Lean derivation, or version-pinned foundation disposition. Reuse a
receipt only when that item's source-atom content, Spec closure, narrow closure
environment, and exact theorem type are unchanged. Legacy v10 evidence remains
readable but does not satisfy this v11 credential.

Partition every source and Lean obligation through both the numeric and
discrete semantics reviews. Record coercion, division, rounding, normalization,
strictness, and zero-denominator behavior separately. Distinguish immediate
successor, next active choice, eventual occurrence, restricted support, and
first occurrence literally. Bind any proved equivalence to an explicit
equality/iff Lean conclusion on the reviewed obligations.

For every `source_routes` entry, pin the source item, current statement digest,
exact locator, route kind, and semantic scope/evidence. `direct` is only for an
exact equivalent paper-facing endpoint with an exact source-conclusion/Lean-
conclusion equivalence. A `corrected_source_statement` retains archival text
and has exactly one complete PaperInterface endpoint in `lean_declarations`;
state all repaired clauses as one explicit conjunction there. Aliases, proof
helpers, support declarations, and semantic bridges cannot carry the repaired
target, source-route credit, or coverage credit. A composite row lists each scoped component as
`source_component`, using a Lean conclusion as evidence without claiming a
full-theorem equivalence. `source_model_convention` is for an explicit model
reading, `defect_or_remark_support` for quarantined/support-only material, and
`proof_support` only for a substantive support scope that never gives endpoint
credit. Names route review but never establish it.

| Source item / locator | Spec -> proof route | v10 declaration-manifest SHA-256 | Statement verdict | Premise provenance | Proof body |
|---|---|---|---|---|---|
| Proposition 1 (Frontier expansion) / Proposition 1; page 13 of arXiv 2605.25438v2 PDF; Appendix A.3 page 59 | `Proposition1_frontierExpansionSpec` -> `Proposition1_frontierExpansion` | pending | pending | pending | `by sorry` |
| Proposition 2 (Activation band for unfamiliar languages) / Proposition 2; page 13 of arXiv 2605.25438v2 PDF; Equation (8); Appendix A.4 page 60 | `Proposition2_activationBandSpec` -> `Proposition2_activationBand` | pending | pending | pending | `by sorry` |
| Proposition 3 (Dynamic cumulative-language effect) / Proposition 3; page 15 of arXiv 2605.25438v2 PDF; Equation (10); Appendix A.6 pages 61-62 | `Proposition3_dynamicCumulativeSpec` -> `Proposition3_dynamicCumulative` | pending | pending | pending | `by sorry` |
| Proposition 4 (Specialist and ability heterogeneity) / Proposition 4; Appendix A.5 page 60 of arXiv 2605.25438v2 PDF; Equation (22) | `Proposition4_specialistHeterogeneitySpec` -> `Proposition4_specialistHeterogeneity` | pending | pending | pending | `by sorry` |
| Proposition 5 (Repository expansion) / Proposition 5; Appendix A.8 page 63 of arXiv 2605.25438v2 PDF | `Proposition5_repositoryExpansionSpec` -> `Proposition5_repositoryExpansion` | pending | pending | pending | `by sorry` |

Signature changes after a `matches` verdict invalidate the row and require a
fresh audit. Replacing `sorry` without changing the type does not.

## Planned Verification And Invalidation

Use these boundaries throughout the paper so closeout is execution of a plan,
not a new discovery pass.

| Material change | Reopen |
|---|---|
| One source item's semantic content or byte anchor | That item's source, coverage, statement, and dependent proof obligations |
| One `Spec` type or elaborated semantic dependency | That statement item and its dependent proof closure |
| Proof body only, theorem type unchanged | Focused compilation and proof closure only |
| Report, README, status prose, or DAG only | Presentation/status consistency only |
| Audit producer or protocol | Only lanes whose pinned producer/protocol identity changed; first run the reuse planner |

Planned commands, in order:

1. Intake seal, once the complete statement review is current: `python3
   scripts/semantic_audit_reuse.py --paper QX26AgenticDelegation --bootstrap-current
   --write`.
2. Proof loop: `lake build QX26AgenticDelegation.PaperInterface` or the narrower touched
   proof module.
3. Freeze closeout presentation inputs once: final report, status, source map,
   and Dependency DAG source/PDF. Run `python3 scripts/sync_paper_status.py
   --paper QX26AgenticDelegation`; defer aggregate/site status to integration or release.
4. Closeout readiness: `python3 scripts/closeout_reuse_plan.py --paper QX26AgenticDelegation`.
   Execute its `next_action`. If the frozen plan gives that action an explicit
   state-qualified successor, continue through that successor to its required
   replan boundary; do not rerun the planner between a cache-miss build and its
   one manifest refresh. A cache miss never erases unchanged semantic judgments.
   An exact current compiled cache skips a redundant standalone build, while a
   rebuilt artifact must be replanned before strict closeout.
5. Consolidated closeout, once the planner exposes it: run the exact
   `strict_closeout` argv/command printed by the plan. It carries a
   non-authoritative operational plan identity, preventing an accidental
   duplicate of the same completed execution. Do not invoke
   `run_paper_closeout.py` from a handwritten command: its planner-issued
   identity and any `--new-run` disposition are required.
   This command records ignored operational state under `.review_traces`; if
   the terminal stream disappears, inspect that state instead of starting a
   duplicate run.
6. Run a repository-wide status/site refresh only at an integration or release
   boundary, not as part of every paper proof closeout.

## Reusable-Library TODO

- Library APIs to use directly:
- Small reusable lemmas to add now:
- Larger reusable components to defer:
- Library-audit risks:

## Execution Checklist

- [ ] Download/cache source PDFs and text extracts, with redistribution notes.
- [ ] Complete the normal named-theory inventory and record deep-only
      dispositions separately.
- [ ] During active source-map repair, run `--source-inventory-check` before a
      necessary manifest refresh. With a current cache, use targeted
      statement/coverage checks; after the source map, interface, and status
      surface are stable, refresh once and let bounded manifest retry/fallback
      handle outliers. At frozen closeout, do not repeat those commands by
      default: let the planner schedule the required delta.
- [ ] Fill the formal target map and declare any intended boundary/certificate.
- [ ] Build or select reusable library APIs before adding paper-local wrappers.
- [ ] Replace the paper scaffold with complete source-facing Lean definitions,
      transparent `<name>Spec : Prop` statements, and theorem/lemma routes typed
      exactly by those specifications; use `by sorry` only for temporary private
      proof bodies.
- [ ] Independently inventory every material source atom from exact pinned quote
      bytes before Lean review. At full closeout, bind those atoms to the
      elaborated Spec and account for every material closure terminal, including
      proof and instance arguments; no declaration, data, or container category
      is an automatic exemption.
- [ ] Run recursive source-record/conclusion-provenance checks and raw
      byte-pinned-source-to-expanded-Spec matching on every skeleton claim;
      record and freeze each signature digest. The paired theorem is only proof
      evidence, not a second semantic match.
- [ ] Complete numeric and discrete obligation partitions; do not claim absence
      when the elaborated manifest exposes arithmetic or list operations.
- [ ] Complete the applicable fidelity-risk dimensions from expanded semantics:
      output/conclusion shape, action or input space, witness/optimization
      semantics, cardinality/quantification, and, for executable results,
      input scope, state transitions, termination, numeric representation, cost,
      and the global-claim bridge.
- [ ] For every runtime claim, audit the transitive operational dependency graph
      over every reachable branch; refinement alone is not cost evidence. Give a
      worst-case recurrence and bound, and completely account for traversal,
      duplicates, materialization, representation primitives, and rational bit
      growth. Missing or excluded work withholds a runtime match; materially
      eliminated closure dependencies need artifact/source hashes and semantic
      binding to generated IR/C or a cost-threaded executor.
- [ ] Review every source proof route used; record source proof defects as
      mathematical repair obligations, never as source assumptions.
- [ ] Prove all rows marked in-scope, or downgrade them with an explicit
      boundary note.
- [ ] Replace every skeleton `sorry` without changing its audited specification
      or theorem type; rerun statement audit whenever either changes.
- [ ] At closeout, update README, status, DAG, and validation report from the
      same row list.
- [ ] At closeout, freeze the paper inputs and run the reuse planner. Let its
      ordered actions own the targeted paper build, audits,
      placeholder/provenance checks, and DAG validation; do not pre-run those
      gates just to recreate an intermediate receipt.
- [ ] Record any unresolved source bug, assumption, or library debt.

## Active Scratchpad

- Current Lean endpoint:
- Exact current mathematical gap:
- Next bridge lemmas to try:
- Informal proof sketch / recurrence / construction:

## Deviations And Assumptions

- Source imprecision or proof deviation to report later:
- Genuine paper assumptions to declare in `Assumptions.lean`:
- Temporary certificate fields to discharge:
- Validation/audit checks that must inspect these assumptions:
