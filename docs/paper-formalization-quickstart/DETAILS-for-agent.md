# Paper Formalization Details

## Prompt Variants

New paper intake:

```text
Do new paper intake for <paper title>, and your goal is to fully formalize it.
Use <arXiv URL>. The official source is <official URL> for documentation.
Start with source/version inventory, named-result ledger, formula sanity pass,
source-role classification, shared-library reuse checkpoint, and
FORMALIZATION_PLAN.md. Draft one complete Spec plus a distinct proof endpoint
for each source result; draft actual declarations for definitions, algorithms,
models, assumptions, and conditions. Run the skill's non-certifying semantic-
architecture pre-pass and refactor its findings before intake freeze or any
semantic evidence issuance.
```

Resume a paper:

```text
Resume <PaperFolder>. First read the skill, the paper README,
FINAL_VALIDATION_REPORT.md, PaperInterface.lean, FORMALIZATION_PLAN.md, and the
current status.json. Tell me the exact remaining proof boundary, then keep
going until the paper is formalized or the boundary is reduced to one named
library theorem/certificate.
```

Public partial target:

```text
Clean this up as a public partial formalization. Derive everything possible
from source-model primitives. The only remaining work should be the smallest
explicit boundary: <one sentence>. Make the README, DAG, status, and final
report human-facing.
```

## Intake Checklist

- Record `Paper`, `Authors`, `Version formalized`, `Official URL`, and
  `Public PDF` in the paper README.
- Prefer source TeX for formulas, theorem labels, equation numbers, appendix
  proof steps, and version disputes. Use PDF text mainly for orientation.
- Fill the initial `FORMALIZATION_PLAN.md` before deep proof work: source
  inventory, named-result ledger, formula/dependency sanity pass, reusable API
  checkpoint, formal target map, and fallback boundaries.
- Classify every selected source presentation by semantic role before choosing
  a Lean shape. Results get one complete transparent `Spec : Prop` plus a
  distinct proof/refutation endpoint. Definitions, algorithms, governing
  models, assumptions, and conditions get their actual complete declarations,
  which every semantically governed result Spec must actually use. A genuinely
  standalone named definition may remain an independently reviewed standalone
  declaration; do not attach it as a vacuous premise to an unrelated result.
- Run the skill's non-certifying semantic-architecture pre-pass on the proposed
  interface and Lean-produced dependency view. Resolve role errors, omitted
  clauses, fake wrappers, dead duplicates, and source-model bypasses before
  intake freeze. Its output is diagnostic planning material, never audit
  evidence.
- Build a small paper-facing interface first. A broad package row or
  source-looking certificate is not a substitute for matching each visible
  source result or for exposing the actual source definition/model it uses.

## During Proof Work

- Search Mathlib, CSLib, Optlib, potential upstream Lean sources listed in
  [`../UPSTREAM_LEAN_SOURCES.md`](../UPSTREAM_LEAN_SOURCES.md), and existing
  `AppliedModelingLib` APIs before creating a local wrapper around a standard concept.
- If you use or port upstream material, cite the repository, file/module path,
  commit or release when available, license status, and what was reused.
- Keep `PaperInterface.lean` readable: definitions and named source results
  belong there; implementation helpers belong in `MainTheorems.lean`,
  `ProofInterface.lean`, or local proof files.
- A paper result is fully formalized only when non-derived premises are either
  proved from source primitives or listed as validated paper-source
  assumptions. Hidden certificate, replay, process, bridge, or source-record
  fields should be audited recursively.
- Subagents are allowed for scouting, independent proof regions, audit cleanup,
  CI, and release tasks. Ask them for exact files, declarations, and next
  lemmas, not broad summaries.
- Do not run the full closeout workflow just because an unfinished paper
  changed. Use targeted `lake build` commands and row-scoped checks until a
  real closeout or handoff point.

## Human-Facing Standards

- Put current status first. Avoid history markers like "no longer done" in
  human-facing docs.
- Write one-sentence status summaries when possible, for example: "Full
  formalization requires a homogeneous Poisson process and stopping-time
  derivation."
- DAGs should be paper-facing and visually readable. Avoid Lean declaration
  names, oversized boxes, and overlapping arrows.
- Reports should start with what a paper author or researcher needs: verdict,
  paper issues or none found, additional assumptions or proof boundaries,
  proof-strategy deviations, and reusable proof ideas.
- Do not call a source assumption a caveat. Use kind, precise caveat language
  only for real theorem-facing source discrepancy, ambiguity, added non-source
  assumption, or proof-boundary issues.
- Do not call a corrected printed proof route a caveat when Lean proves the
  same source theorem endpoint. Record it as a proof correction, typo, or
  alternative proof in the post-formalization audit/final report.
- For public tables, avoid separate `conditional` terminology; use
  `partially formalized` and name the exact remaining boundary.

## Closeout Checklist

At real completion or public-partial handoff, update:

- `README.md`
- `PaperInterface.lean`
- `DependencyDAG.tex` and rendered DAG if tracked
- `status.json`
- `FINAL_VALIDATION_REPORT.md`
- reusable-library notes or extracted APIs, when applicable

Then run the relevant checks from the repository root:

```bash
PAPER=ABC24ShortTitle
python3 scripts/sync_paper_status.py --paper "$PAPER"
python3 scripts/paper_contribution.py check "$PAPER"
```

For a one-paper public-ready branch, commit the paper-owned paths and run
`python3 scripts/paper_contribution.py prepare-pr "$PAPER" --base upstream/main`.
That contributor lane does not refresh aggregates or audit existing papers.
Only shared/integration changes use the broader release checks listed in
[`../AGENT_FORMALIZATION_WORKFLOW.md`](../AGENT_FORMALIZATION_WORKFLOW.md).
