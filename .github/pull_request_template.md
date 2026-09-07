## Contribution Scope

- [ ] One-paper contribution
- [ ] Integration contribution (shared library, tooling, protocol, workflow,
      multiple papers, or broad documentation)

Paper folder, if applicable: `<PaperName>`

Exact source version: `<venue/date/arXiv version>`

Claimed status: `<paper draft / not started / not formalized / partially formalized / formalized / formalized with caveat>`

## Summary

Describe the checked paper results or shared change. For a paper, identify every
additional assumption, source correction, or remaining proof boundary.

## One-Paper Boundary

- [ ] Changes are limited to `papers/<PaperName>/**`,
      `papers/<PaperName>.lean`, and the exact additive Lake registration.
- [ ] No aggregate output is included: `papers/status.json`,
      `papers/human_status.json`, `docs/PAPER_STATUS.md`, or `site/index.html`.
- [ ] No source PDF, TeX archive, extracted text, dashboard cache, or other
      unlicensed/local artifact is committed.
- [ ] `PaperInterface.lean` contains the paper-facing definitions and named
      theoretical statements, not proof plumbing or source-looking aliases.

For an integration contribution, explain why broader scope is required:

## Validation

For a one-paper contribution, commands run:

```text
python3 scripts/paper_contribution.py doctor
python3 scripts/paper_contribution.py check ABC24ShortTitle --fast
python3 scripts/paper_contribution.py check ABC24ShortTitle
python3 scripts/paper_contribution.py prepare-pr ABC24ShortTitle --base upstream/main
```

- [ ] The full paper check ran locally with the exact pinned source bytes
      present. (Required for every one-paper PR; not applicable to integration
      PRs.)
- [ ] `prepare-pr` accepted the branch against the stated base. (One-paper PRs
      only.)

For an integration contribution, list the targeted and broad checks appropriate
to the shared paths instead of running `prepare-pr`:

Additional commands or relevant output:

## Review Entry Points

- Validation report: `papers/<PaperName>/FINAL_VALIDATION_REPORT.md`
- Paper interface: `papers/<PaperName>/PaperInterface.lean`
- Dependency DAG: `papers/<PaperName>/docs/DependencyDAG.tex`
- Paper README: `papers/<PaperName>/README.md`

Pull-request CI derives scope from the Git diff. Selecting the one-paper box
does not waive integration checks for shared or unrelated changes.
