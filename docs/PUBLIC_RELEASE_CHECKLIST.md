# Public Release Checklist

Use this checklist before announcing a public release or inviting broad
external contributions. Checked boxes record the 2026-06-03 release only; a
new release must rerun every applicable item against its exact candidate.

## Repository State

- [x] The intended public branch is clear. Public release docs, the Pages site
      source, and the Pages workflow live on `main`.
- [x] Non-public development work is not converted into the public repository.
- [ ] The candidate was created on a `release/` branch in a separate clean
      public clone from the recorded `origin/main` commit. No private `HEAD`,
      private branch, private Git directory, or filtered private history was
      pushed or merged into the public repository.
- [ ] The complete export is one squashed release commit whose sole parent is
      the exact recorded public base; there are no stacked or merge commits.
- [ ] Every paper status explicitly sets `repository_visibility` to `public`
      or `private_only`; the public candidate contains only `public` paper
      records. Academic publication metadata was not used as export authority.
- [ ] The release allowlist records one exact file path, provenance mode,
      rationale, and affirmative public-safety review for every exported path,
      with no directory or unused entries. `private_blob` and
      `private_projection` entries pin an exact private source commit;
      projections and public-base edits/additions pin the digests required by
      their modes. Public-generated files and deletions use their explicit
      non-copy modes and do not claim a private source commit.
- [ ] The trusted private guard passes for the clean one-commit candidate and
      exact allowlist. This is the required candidate/PR check and does not
      require a separate approval artifact.
- [ ] Before a maintainer merges the accepted PR to `main`, the maintainer
      places the schema-2 approval at the guard's fixed
      `~/.config/econcslib/public-release-approval.json` path outside both
      repositories. It pins the exact candidate and public-base commits,
      allowlist, guard, and deterministic private trusted-tooling bundle SHA256
      values, and sorted private source commits. The tooling digest covers all
      non-test production files under the executed private `scripts/` directory,
      including imported and executed guard helpers.
      Its directory/file modes are `0700`/`0600`, and neither is a symlink.
- [ ] `python3 scripts/lean_import_closure.py --candidate index` passes after
      staging, so no tracked entrypoint imports an untracked or unstaged Lean
      module.
- [ ] From the clean committed candidate, run the trusted private copy before
      opening a PR:
      `python3 <private-repo>/scripts/public_release_candidate_guard.py --repo "$PWD"
      --allowlist <reviewed-allowlist.json>` passes. Every copied candidate blob
      must byte-match its allowlisted path at the recorded private commit;
      deletions and public-generated aggregate files use their explicit
      non-copy provenance modes. Both repositories use their canonical
      `origin` fetch and push URLs, do not share a Git object store, and every
      private source commit is reachable from private `origin/main`.
- [ ] Immediately before merging an accepted PR, the maintainer reruns that
      command with `--authoritative`; this verifies the maintainer's pinned
      approval record as well as the candidate checks.
- [x] `lake build AppliedModelingLib` passes from a clean public checkout.
- [x] The top-level `README.md` describes the public repository, not the private
      incubator.
- [x] `docs/PAPER_STATUS.md` matches the paper folders included in the public
      repository.
- [x] Each public `papers/<PaperName>/status.json` is current, and
      `python3 scripts/sync_paper_status.py --check` confirms that the generated
      `papers/status.json`, `papers/human_status.json`, and
      `docs/PAPER_STATUS.md`, `site/index.html`, and paper-local generated
      `README.md` entrypoints are in sync. Refresh paper READMEs only through
      this generator; do not edit them manually. The root `README.md` is
      human-written and is not a generator output.
- [x] The generated `docs/PAPER_STATUS.md` and site status tables
      summarize the same public paper set, statuses, review counts, Lean LOC,
      and sparse notes as `papers/human_status.json`.
- [ ] Public labels and sparse notes follow [the current display policy](STATUS.md#public-website-display):
      `Formalized`, with substantial theorem-specific `Formalization gap:`
      notes when needed, and the two retained `Partially formalized` projects.
      Do not publish `Verified in Lean` as a separate category.
- [x] `python3 scripts/audit_repository.py` reports 0 errors. In a structural
      public checkout, use `--allow-missing-source-bytes`; warnings for omitted
      licensed source PDFs are acceptable there. This mode neither replaces
      source-present private receipt validation nor issues a fresh
      source-certification claim.
- [x] `CONTRIBUTING.md` states the current contribution policy and contact
      email.
- [x] `CITATION.cff` has the current repository title, author, and release date.
- [x] A repository license has been chosen and added as `LICENSE` before
      soliciting broad external code contributions.
- [x] The GitHub repository description is set. The homepage field points to
      `https://gargnikhil.com/EconCSLib/`.

## Paper Folder Readiness

Each public paper folder should have:

- [ ] `PaperInterface.lean` as the compact human-facing theorem surface;
- [ ] `Assumptions.lean` if any paper-facing theorem premise remains as an
      explicit source/model assumption;
- [ ] `FINAL_VALIDATION_REPORT.md` or an equivalent validation summary;
- [ ] a current schema-6 `FINAL_CLOSURE_RECEIPT.md` selecting the paper's
      schema-2 `audit/obligation_evidence/current_accepted_graph.json`. Validate
      it in the source-present private checkout with
      `python3 scripts/final_closure_receipt.py --paper <Paper> --check` before
      export. The public candidate retains only the selected pointer, referenced
      accepted-graph pack, referenced Lean-import-closure preimage, and receipt;
      the trusted private release guard validates that structural transport;
- [ ] `docs/DependencyDAG.tex` and a rendered `docs/DependencyDAG.pdf`;
- [ ] checked-in `docs/HUMAN_REVIEW_PACKET.tex` and rendered
      `docs/HUMAN_REVIEW_PACKET.pdf` as the reviewer artifacts. A clean public
      clone may perform only this presentation-only rebuild of existing TeX:
      `python3 scripts/review_dashboard_packet.py --paper <Paper>
      --sanitize-existing --compile`. It rewrites public presentation locators
      and compiles the PDF; it does not recompute semantic Lean displays,
      source excerpts, or audit evidence without the audit workspace/cache.
      The packet is a review aid, not a substitute for saved human dashboard
      judgments.
- [ ] a current `status.json`, including human-review row counts,
      `review_surface` rows/slices, `assumption_names` for any paper-model
      assumptions, artifact paths, and any PaperInterface maintenance issue;
- [ ] `audit/assumption_match_llm.json` whenever paper-facing theorem premises remain
      as source/model assumptions rather than derived Lean facts;
- [ ] a passing `lake build <PaperTarget>` command; and
- [ ] no tracked source PDFs, extracted source-paper text caches,
      review-dashboard caches, private planning/handoff markdown, or generated
      build artifacts other than intentional public proof/DAG PDFs in `docs/`.
      The sole source exception is a canonical official arXiv `.tex` artifact
      at `papers/<Paper>/source/<file>.tex`, whose candidate bytes exactly
      match the source-map SHA-256 and whose source URL is an arXiv `abs` or
      `e-print` URL. The release guard verifies this exception; archives,
      scans, PDFs, and other extracted source files remain private.

## Preparing A Completed Private Paper

- [ ] Confirm the paper is ready for public review.
- [ ] Confirm its status explicitly says `repository_visibility: public`.
- [ ] Select its current-tree files and reusable library changes through the
      reviewed release allowlist. Do not export private development history.
- [ ] Apply only the reviewed current-tree patch to a clean branch based on
      public `origin/main`.
- [ ] Update paper-local `status.json`, run `python3 scripts/sync_paper_status.py`,
      and then update surrounding site prose, roadmap, or release notes only if
      needed. Do not edit the root `README.md` unless the user gives specific
      root-README instructions.

## GitHub Pages Readiness

- [x] Run `python3 scripts/sync_paper_status.py --check` to confirm the site
      status table matches `papers/human_status.json` and
      `docs/PAPER_STATUS.md`.
- [x] The Pages workflow is tracked as `.github/workflows/pages.yml`.
- [x] Confirm the Pages workflow completes and the Pages URL serves the site.
- [x] Enable HTTPS enforcement for GitHub Pages.

## After The Public Update: Repository And Site Rename

The selected destination is `nikhgarg/AppliedModelingLib` and
`https://gargnikhil.com/AppliedModelingLib/`. Follow the
[name and URL migration plan](PAGES_PUBLISHING.md#planned-name-and-url-migration).

- [ ] Rename the existing public repository, retaining its history and forks.
- [ ] Update the Pages repository gate, release-guard public identity and tests,
      generated links, homepage metadata, and current documentation.
- [ ] Verify the native site under `/AppliedModelingLib/`.
- [ ] Publish `/EconCSLib/` redirects from the personal website, preserving
      fragments, queries, and applicable old deep links. Do not create a new
      `nikhgarg/EconCSLib` repository, which would break Git redirects.
- [ ] Verify the old Git URL still fetches and give fork owners the upstream
      remote-update instructions. Existing forks require no recreation.
