# Public/Private Repository Sync

Use this reference whenever work has to move between `EconCSLib-private` and
`EconCSLib-public`, or when the user asks to keep both repositories in sync.

## Core Rule

Do a semantic, path-scoped sync. Do not raw-merge the private repository into
the public repository, and do not assume that a Git merge is safe just because
the folder names overlap. The private repo may contain unpublished paper
folders, local source caches, private planning notes, generated status rows for
private papers, and newer experimental audit code. The public repo must contain
only public-safe code, public paper artifacts, public workflow docs, and
generated surfaces regenerated from the public checkout.

## Preventing Divergence

Treat sync as a standing maintenance workflow, not a prompt to publish more
private work. The default direction is that private worktrees incorporate the
public repository after public PRs land, so private development stays based on
the current public library and workflow. Moving work from private to public is a
separate release/contribution decision that should happen only when the user or
maintainer explicitly asks for a public-safe PR.

- Use clean worktrees from remote refs when either checkout is dirty. Do not
  base sync decisions on a stale local working tree; compare `origin/main` and
  `public/main` or freshly pulled `main` refs.
- Keep a source-of-truth map before copying: shared Lean library code, scripts,
  CI, templates, and public-safe skill references should match across repos
  unless there is an explicitly recorded private experiment; generated
  aggregate surfaces are checkout-local; private paper folders, source caches,
  and paper-specific proof notes stay private.
- When a public PR lands, update the private superset promptly unless private
  intentionally has a newer experiment for the same path. This keeps private
  work aligned with the public base without implying that private papers should
  be promoted.
- When a useful private change appears, first ask whether it is intended for a
  public-safe contribution. If not, keep it private. If yes, prepare a narrow
  PR branch against public `main`; contributors should assume they do not have
  push access to public and should use ordinary fork/branch PR mechanics.
- Prefer ref-to-ref checks over visual inspection. After a sync, run direct
  diffs for shared paths such as `AppliedModelingLib/`, `scripts/`, synced docs, synced
  skill references, and public paper folders. Investigate every remaining
  modified (`M`) diff under public paper folders; only private-only deletes,
  checkout-local generated aggregates, and intentionally sanitized skill/docs
  differences should remain.
- Preserve useful methods, proof strategies, diagnostic checks, and public API
  guidance when preparing skills for release. Public papers and released
  formalizations may remain concrete examples. A reference to a public paper
  does not authorize publishing its private formalization findings or repair
  history. Generalize those details while retaining the actionable lesson;
  do not remove useful mathematical guidance merely to remove provenance.
- Keep wiki examples, feedback ledgers, session provenance, and maintenance
  history private by default. Sanitizing an example for private retention does
  not authorize publishing it. Promote its general lesson into a self-contained
  public skill; do not copy unpublished findings or statements, private user
  quotations, or session identifiers. Public skills must work without access
  to the private wiki or feedback ledger. Publishing a private wiki example
  needs a separate, explicit export decision; ordinary public-paper examples
  do not require that additional workflow.
- Review every exported skill reference, template, and bundled example, not
  only `SKILL.md`. Check that examples and links use public material;
  a file living under `skills/` is not evidence that it is public-safe. Record
  exact export paths and keep private provenance out of the candidate.
- Record the outcome in commits/PR bodies: what public changes were reflected
  into private, whether any explicitly requested public-safe contribution was
  prepared, which generated files were regenerated rather than copied, and which
  remaining diffs are intentional.

## Sync Direction

- Public to private: copy public `main` changes that affect shared library code,
  scripts, public-safe skills, templates, CI/workflows, and public paper folders
  into the private checkout unless private has an intentionally newer semantic
  version. Regenerate private aggregate status/site files in the private
  checkout after copying.
- Private to public: do this only for an explicitly requested public-safe
  release or contribution. Start from current public `main` in a separate clean
  public clone on a `release/` branch, then copy only allowlisted paths. Never
  push, merge, filter, or cherry-pick private `HEAD` into public. Use exact
  paths, not broad `papers/` or `skills/` copies. Regenerate public aggregate
  status/site files in the public checkout.
- If both repos changed the same generated artifact, prefer the artifact whose
  inputs are newest and whose validation was run in the checkout that will
  publish it. Do not decide by filename alone.

## Latest-Wins Policy

For public-safe paths, prefer the latest semantically valid artifact:

- Lean source, scripts, and skill references: prefer the newer audited workflow
  or proof code, but check for private-only identifiers before copying to
  public.
- DAG PDFs, validation reports, and generated paper artifacts: use the newest
  version that matches the current paper status and source surface. If a PDF is
  copied, copy its TeX/source input when that input is tracked and public-safe.
- LLM-as-judge sidecars (`audit/lean_to_tex_llm.json`,
  `audit/statement_match_llm.json`, `audit/paper_coverage_llm.json`,
  `audit/assumption_match_llm.json`, `audit/source_record_match_llm.json`): use
  the sidecar that matches the current Lean declarations, current source
  inventory, current prompt version, and current digest fields. A newer
  timestamp is not enough.
- Source records (`audit/source_record_audit.json`,
  `audit/paper_statement_map.json`): use the version generated from the current
  Lean/source inventory. Validate the exact item identities first; regenerate
  only rows whose current source/map/Lean semantic surface fails that check, not
  merely because the destination checkout is cold or a timestamp differs.
- Paper-local status metadata: human-review totals should count the curated
  source-facing review rows, not every proof helper or API declaration exposed
  during implementation. Prefer explicit `review_surface.include_names`,
  `assumption_names`, and `auxiliary_names` to make the dashboard surface
  auditable before regenerating aggregate files.
- Publication display metadata: if public/private generated tables need clean
  publication wording that differs from local source provenance, add or update
  `papers/catalog.json` `publication_overrides`. Do not erase paper-local
  `source_version` provenance such as source archives, TeX/formula sources, or
  internal source-version notes just to clean a rendered table.
  `publication_overrides` is academic display metadata only. It never selects a
  paper for repository export. Every paper status must explicitly declare
  `repository_visibility: public` or `private_only`, and all public-release
  selectors must fail closed when that field is absent or unknown.
- Public website/status notes should be sparse. For fully formalized papers,
  leave `human_summary` / public-note fields empty by default unless there is a
  real public-facing reason to explain a caveat, remaining boundary, unusual
  source version, or important scope distinction. Put validation details,
  source-record counts, proof-organization notes, dashboard status, and
  implementation route explanations in final reports, audit notes, or sidecars,
  not in the public table note column. When a note should disappear, set the
  source field to the empty string and regenerate generated surfaces.
- The public website status table should stay compact and source-driven. Do not
  add a separate `LLM-as-judge statement translation` column; mention
  LLM-as-judge coverage in the surrounding prose instead. Use `Lines of Code`
  for proof LOC and `Note` for the website note header. Keep markdown docs free
  to use fuller labels such as `Public note` when useful.
- The website library-components table is generated from
  `papers/catalog.json` `library_components`. Treat that table as a partition
  of tracked `AppliedModelingLib/**/*.lean` files: folded rows are fine, but the row LOC
  totals should add up to the actual library LOC in that checkout with no
  duplicate-counted or missing Lean files. Put Foundations rows first, then
  application/domain rows in descending LOC order unless there is a stronger
  reader-facing reason. Name the prose column `Content`, and cover the important
  concepts in each area with concise lists rather than explaining one example
  in depth or listing internal implementation details.
- Aggregate files (`papers/status.json`, `papers/human_status.json`,
  `docs/PAPER_STATUS.md`, `site/index.html`, and per-paper generated
  `README.md` entrypoints): never copy across the public/private boundary.
  Regenerate them in the destination checkout. The root `README.md` is
  hand-written prose; do not copy, regenerate, or edit it unless the user gives
  specific root-README instructions.

## Source Artifacts

Source-paper PDFs, extracted source text, publisher archives, and arXiv source
archives may be tracked in the private repository when they are the pinned
evidence for a paper or needed for a durable private handoff. Add exact source
paths only (using `git add -f` when cache-ignore rules apply); keep dashboard
caches and unneeded local variants ignored. Do not copy source bytes into a
public candidate by default. Such publication requires the user's explicit
permission for the exact artifacts, independently of their private tracking or
redistribution status. Public reports should cite the source URL and, if
needed, describe a local source cache. Planning, handoff, audit, and
citation-provenance notes written by the project may be tracked when they do
not reproduce source-paper text.

A public candidate is therefore a **structural** validation environment for
licensed source evidence. It must retain the canonical source path/provenance
and digest plus the paper's final closure receipt, but it must not contain the
underlying source bytes. Missing bytes there mean that the candidate cannot
independently recompute source excerpts; they do not make a private source
review, receipt, or audit stale. Treat that condition as a non-certifying
structural warning. Reissue a source review only after a private, byte-checked
material change to the source, source map, Lean interface/proof closure, or
governing protocol—not to fill an intentionally private public checkout.

## Cache Discipline

Do not trust a warm checkout for public validation. Ignored
`.review_traces/paper_interface_cache.json` files can make
`review_dashboard.py --statement-check` pass locally while a fresh CI checkout
fails. This is destination-checkout cache validation, not a normal frozen-paper
closeout sequence. Before treating copied sidecars as current:

1. Compare the tracked item identities first. If the destination needs a
   dashboard manifest to validate a changed or cache-missing row, run
   `python3 scripts/review_dashboard.py --paper <paper> --refresh-cache` once
   in that checkout. Do not refresh merely because this checklist is being read.
   For a source-present frozen paper closeout, use
   `closeout_reuse_plan.py` instead and execute only its scheduled action.
2. Regenerate tracked LLM sidecars from that current review surface only if a
   configured row's semantic identity, Lean/source statement digest, prompt
   version, or source-record audit digest changed. Row names are navigation,
   not a regeneration condition.
3. Verify from a fresh or cache-free checkout when preparing a public PR that
   touches review sidecars.
4. If local and CI disagree, trust the fresh checkout/CI and inspect ignored
   cache files before editing proof code.

## Safe Copy Procedure

1. Inventory both repos:
   `git status -sb`, `git log --oneline -5`, `git remote -v`, and
   `find papers -maxdepth 1 -type d | sort`.
2. Build a path-level diff by category: shared library, scripts, skills,
   public paper folder, private-only paper folder, DAG/report PDFs, LLM
   sidecars, source caches, and generated aggregate surfaces.
3. For each path, record the chosen direction and reason in a release-specific
   exact-file allowlist. Directory entries are forbidden. Copied blobs must
   cite an exact private source commit and
   byte-match that path at that commit; public-base deletions and the four
   destination-generated aggregate files use explicit non-copy provenance. A
   reviewed in-place edit to an existing public-base file uses
   `public_base_edit`, with exact SHA256 digests for both the public-base and
   candidate blobs; it cannot authorize an addition, deletion, rename, or Git
   mode/type change. The reviewer approval's allowlist SHA256 transitively pins
   both blob digests. A reviewed public-only file that is absent from the public
   base uses `public_base_addition`, pins the exact candidate blob SHA256, and
   is accepted only as a Git addition. If byte-identical content at the same
   path and Git mode exists in any reviewed private source commit, the guard
   requires `private_blob` instead; a genuinely public-specific rendering at a
   shared pathname still requires independent review. Record the release decision as `public newer`, `private
   newer`, `destination regenerated`, `private-only`, `source-cache private`,
   or `public-safe PR`.
4. Copy with an explicit path list or `rsync --files-from`, never a broad
   repository-wide copy.
5. Regenerate aggregate status in the destination checkout.
6. Run the relevant validation in the destination checkout:
   `python3 scripts/sync_paper_status.py --check`,
   `python3 scripts/audit_repository.py --library-only --library-premise-audit --info-limit 0`,
   relevant `review_dashboard.py` checks, and targeted `lake build`.
7. Run leakage checks before public commits:
   `git diff --name-only` plus searches for private paper IDs, raw source
   caches, `.review_traces`, `.txt` source extracts, and private planning paths.
8. Commit the complete public export as one squashed commit whose sole parent
   is the exact fetched public base. Use explicit pathspecs; do not merge or
   stack private commits, because intermediate history is also published. For
   public changes, prepare a PR; do not assume direct push access.
   During local candidate review, keep the `release/` branch editable. Apply
   feedback to maintained private sources where applicable, refresh only the
   reviewed exported files, regenerate destination aggregates, and renew the
   allowlist blob pins and candidate checks. Consolidate the revised export to
   one release commit before validating it; a prior guard pass does not cover
   later edits. Preparing an editable candidate does not authorize publication.
9. Open the PR after the candidate guard passes; no approval artifact is needed
   merely to request review. Only when a maintainer is ready to merge the
   accepted PR does that maintainer create
   `~/.config/econcslib/public-release-approval.json` outside both repositories.
   It pins the exact candidate and public-base commits, allowlist and guard
   SHA256 values, and sorted private source commits. This path is fixed in the
   guard and cannot be overridden by CLI. Its containing directory/file modes
   are `0700`/`0600`; symlinks and group/world-writable approval paths fail.
10. From the clean committed public candidate, invoke the canonical private
   guard:
   `python3 <private-repo>/scripts/public_release_candidate_guard.py --repo "$PWD"
   --allowlist <reviewed-allowlist.json>` before opening the PR. Do not execute a guard from the
   candidate itself. Do not proceed while it reports a visibility,
   trust-anchor, ancestry, provenance, forbidden-path, or Lean
   dependency-closure error. The guard fixes public and private refs/remotes,
   authenticates its containing private checkout, requires canonical fetch and
   push URLs, and rejects shared Git common/object stores. Immediately before
   merging, the maintainer reruns it with `--authoritative` to validate the
   approval pin.

## What Not To Do

- Do not raw-merge private `main` into public `main`.
- Do not copy `papers/status.json`, `papers/human_status.json`,
  `docs/PAPER_STATUS.md`, root `README.md`, or `site/index.html` across repos.
  The root `README.md` is human-owned prose; agents should edit it only after
  explicit root-README instructions.
- Do not copy `.review_traces` caches, local source PDFs/text, or unpacked
  source archives into public by default.
- Do not keep stale LLM sidecars because a warm local checkout passes.
- Do not resolve conflicts by always choosing `ours` or `theirs`; decide by
  source status, current Lean surface, current audit schema, and public-safety.
