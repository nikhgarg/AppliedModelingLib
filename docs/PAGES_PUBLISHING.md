# GitHub Pages Publishing Plan

This document records how to publish the project site when the paper and public
repository are ready.

## Current State

- The public GitHub repository `nikhgarg/EconCSLib` exists and is public.
- The workflow file is tracked as `.github/workflows/pages.yml` and deploys
  from `site/` on pushes to `main` that touch the site or workflow.
- The workflow uses `actions/configure-pages` with `enablement: true` and
  publishes the existing Pages site through GitHub Actions.
- GitHub Pages is deployed at `https://gargnikhil.com/EconCSLib/`.
- Reviewed formalization PDFs are checked into the public paper folders;
  source-paper PDFs remain excluded unless redistribution is reviewed separately.
- The default branch is `main`; broad announcement should wait until final
  paper/status review.

## Planned Name And URL Migration

The maintainer selected this destination on 2026-09-06:

- Repository: `nikhgarg/AppliedModelingLib`.
- Native project site: `https://gargnikhil.com/AppliedModelingLib/`.
- Legacy site: `/EconCSLib/` redirects to `/AppliedModelingLib/`.

Prepare and validate an editable public release candidate first. Perform the
rename after the reviewed public update is pushed; repository renaming and
deployment are separate publication steps.

1. Rename the existing public repository through GitHub Settings. Keep its
   history and fork network; do not replace it with a new repository. GitHub
   redirects old repository URLs and Git operations, but project Pages URLs
   need their own redirect. Never reuse `nikhgarg/EconCSLib` for a redirect
   repository, because that disables the repository redirects.
2. Coordinate the rename with the Pages workflow: the transition gate allows
   exactly `nikhgarg/EconCSLib` and `nikhgarg/AppliedModelingLib`; use only the
   new name after migration. Update the exact public
   repository identity in the release guard and its tests, generated GitHub
   link owners, repository metadata, and maintained documentation. Keep the
   development repository identity unchanged. Preserve historical evidence and the
   separate `gametheoryinlean/EconCSLib` links.
3. Deploy `site/` from the renamed repository. The personal user site already
   uses `gargnikhil.com`; project sites inherit that domain and use their
   repository name as the path. Do not set a project CNAME to
   `gargnikhil.com/AppliedModelingLib`: a custom domain is a hostname, not a path.
   Current CSS and icon links are relative; test them under the new path.
4. Add the legacy redirect to the personal website source repository
   (`_nikhgarg.github.io_source`), so its normal build owns it. Use an
   `EconCSLib/index.html` redirect to the new canonical URL, preserving the
   query and fragment. Handle any previously served deeper paths with explicit
   redirect pages or a narrowly scoped `/EconCSLib/` branch in the existing
   `404.html`. Leave unrelated 404 behavior intact. GitHub Pages static redirect
   pages are browser redirects; a true HTTP 301/308 would require a redirect
   service or proxy, which is not part of the selected migration.
5. Verify the new homepage, CSS/icon, paper links, old root and fragment links,
   and any old deep links. Verify Git fetch through the old repository URL and
   the same fork parent after the rename. Update the repository homepage to
   `https://gargnikhil.com/AppliedModelingLib/` and publish the short contributor
   instructions below.

Existing fork owners keep their fork and update its local upstream remote:

```bash
git remote set-url upstream https://github.com/nikhgarg/AppliedModelingLib.git
git fetch upstream
```

For a direct clone, update `origin` instead. The remote name depends on the
clone; inspect `git remote -v` first. Fork contents still need normal syncing;
a rename does not automatically merge the new release into contributors' work.

References: [GitHub repository renames](https://docs.github.com/en/repositories/creating-and-managing-repositories/renaming-a-repository)
and [custom domains across project sites](https://docs.github.com/en/pages/configuring-a-custom-domain-for-your-github-pages-site/about-custom-domains-and-github-pages#using-a-custom-domain-across-multiple-repositories).

## Before Publishing

1. Decide whether the paper PDF should be linked externally or added as a final
   reviewed public artifact.
2. Review `site/index.html` for accurate contact text and non-generated prose.
3. Run `python3 scripts/sync_paper_status.py --check` to confirm
   `papers/status.json`, `papers/human_status.json`, `docs/PAPER_STATUS.md`,
   and the generated site status table are in sync. Use `papers/status.json`
   for detailed audit metadata.
4. Confirm the root `README.md` was not edited unless the user gave
   specific root-README instructions. Human README edits are allowed
   directly and do not require a lock-file refresh.
5. Run `python3 scripts/audit_repository.py` and confirm there are 0 errors.
6. Preview the static site locally, for example:

   ```bash
   python3 -m http.server 8765 --directory site
   ```

   Then check the home page.
7. Push the reviewed public release branch or merge it into public `main`
   through the [public release checklist](PUBLIC_RELEASE_CHECKLIST.md).
8. Confirm the Pages workflow deploys successfully.
9. Set the repository homepage URL to the Pages URL once the first deploy
   succeeds.

## Updating After Publication

Treat the site as a summary layer. The source of truth remains:

- paper-local `papers/<PaperName>/status.json` files for status and review
  metadata;
- generated `papers/human_status.json` for compact public status;
- generated `papers/status.json` for detailed aggregate status;
- generated status tables in `docs/PAPER_STATUS.md` and `site/index.html` for
  human summaries;
- paper-local `FINAL_VALIDATION_REPORT.md` files for detailed caveats; and
- `CONTRIBUTING.md` for the contribution policy.

When a paper status changes, update the paper-local `status.json`, run
`python3 scripts/sync_paper_status.py`, then update site prose only if
surrounding non-generated text needs to change. Do not update root README prose
unless the user gives specific root-README instructions.
