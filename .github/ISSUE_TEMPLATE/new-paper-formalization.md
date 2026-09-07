---
name: New paper formalization
about: Propose or track a new paper formalization.
title: "[New paper] "
labels: paper-formalization
assignees: ""
---

## Paper

- Title:
- Authors:
- Source version / venue:
- Public URL:
- Proposed folder name:

## Scope

- Named definitions/results to target:
- Intended status for first public PR: not started / not formalized / partially formalized / formalized:
- Known source caveats or ambiguous assumptions:

## Artifacts

- [ ] `python3 scripts/paper_contribution.py doctor` passes
- [ ] source-pinned statement spec prepared with `paper_contribution.py init-spec`
- [ ] `README.md`
- [ ] `FORMALIZATION_PLAN.md`
- [ ] `DependencyDAG.tex`
- [ ] `DependencyDAG.pdf`
- [ ] `docs/AGENT_SOURCE_AUDIT.md`
- [ ] `FINAL_VALIDATION_REPORT.md`
- [ ] `MainTheorems.lean`
- [ ] `PaperInterface.lean`
- [ ] `papers/<PaperName>/status.json`
- [ ] focused Lake target registered by `paper_contribution.py new`
- [ ] paper-scoped full check passes

Do not attach or commit source PDFs/text caches unless redistribution rights
have been checked separately.

Do not refresh `papers/status.json`, `papers/human_status.json`,
`docs/PAPER_STATUS.md`, or `site/index.html` for a one-paper contribution;
maintainers regenerate those projections in a separate aggregate-only PR.
