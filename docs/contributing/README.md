# Contributor Guide

Use this page as the public entrypoint for contributing to AppliedModelingLib. Detailed
audit-engine and release documents are maintainer references; a one-paper
contributor does not need to read them or audit existing work.

## Add Or Repair One Paper

From a branch based on `upstream/main`:

```bash
python3 scripts/paper_contribution.py doctor
PAPER=ABC24ShortTitle
PAPER_URL=https://arxiv.org/abs/2401.01234
SOURCE_VERSION='arXiv v1, 2024-01-03'
SOURCE_ARTIFACT=".scratch/$PAPER/source.pdf"
STATEMENT_SPEC=".scratch/$PAPER/statement-spec.json"
mkdir -p ".scratch/$PAPER"
# Copy or download the exact source version here before continuing.
test -f "$SOURCE_ARTIFACT"
python3 scripts/paper_contribution.py init-spec \
  "$SOURCE_ARTIFACT" \
  --version "$SOURCE_VERSION" \
  --output "$STATEMENT_SPEC"
```

**STOP before `new`.** Edit `$STATEMENT_SPEC`, replace every `REPLACE ...`
value and `replace_with_lean_name`, and add one target for every named result in
scope. This guard must print nothing and succeed:

```bash
! grep -nE 'REPLACE|replace_with_lean_name' "$STATEMENT_SPEC"
```

Only then continue:

```bash
python3 scripts/paper_contribution.py new "$PAPER_URL" \
  --folder "$PAPER" --title "A Short Formalization Example" \
  --authors "Ada Author and Bao Collaborator" \
  --version "$SOURCE_VERSION" \
  --statement-spec "$STATEMENT_SPEC"
python3 scripts/paper_contribution.py check "$PAPER" --fast
python3 scripts/sync_paper_status.py --paper "$PAPER"
python3 scripts/paper_contribution.py check "$PAPER"
git add -- "papers/$PAPER" "papers/$PAPER.lean" lakefile.toml
git commit -m "Formalize $PAPER"
python3 scripts/paper_contribution.py prepare-pr "$PAPER" --base upstream/main
```

The exact source bytes and statement spec are local inputs under the ignored
`.scratch/` tree. Never stage or commit either file.

The full `check` requires the pinned source bytes locally and is the acceptance
boundary. Pull-request CI checks only `<PaperName>` in structural public-checkout
mode and never substitutes for the local source audit.

The scaffold starts `private_only`. Before the synchronization shown above,
change it to `public` only after the paper is approved for publication.
`prepare-pr` requires a clean committed worktree;
it does not include uncommitted source or statement-spec files.

Read the [new contributor workflow](../NEW_CONTRIBUTOR_WORKFLOW.md) for source
hygiene, private development, statement specs, and the meaning of each check.

For an existing paper, skip `init-spec` and `new`. Start from its
`FINAL_VALIDATION_REPORT.md`, `PaperInterface.lean`, and pinned source version;
then use the same fast check, paper-local sync, full check, commit, and
`prepare-pr` sequence. An existing-paper PR does not change `lakefile.toml`.

## What A One-Paper Pull Request Owns

| Allowed | Not paper-scoped |
|---|---|
| `papers/<PaperName>/**` | another paper folder |
| `papers/<PaperName>.lean` | `AppliedModelingLib/`, `scripts/`, `skills/`, or `config/` |
| exact additive Lake target for `<PaperName>` | workflow or audit-protocol changes |
| | aggregate status/docs/site outputs |

Specifically, do not include `papers/status.json`, `papers/human_status.json`,
`docs/PAPER_STATUS.md`, or `site/index.html`. Maintainers regenerate them in a
cheap aggregate-only follow-up after merge with
`python3 scripts/sync_paper_status.py --aggregate-only`. That lane verifies the
four generated projections without initializing Lean or transferring
existing-paper audit responsibility to the contributor.

## Other Contribution Types

Reusable library, audit tooling, protocol, workflow, multi-paper, or broad
documentation changes use the integration lane because they can affect more
than one formalization. See [`CONTRIBUTING.md`](../../CONTRIBUTING.md) for the
repository contract and describe both targeted and broader validation in the
pull request.

For a completed paper, reviewers begin with `FINAL_VALIDATION_REPORT.md`,
`PaperInterface.lean`, `README.md`, and `docs/DependencyDAG.tex`. Those files
should explain the source version, exact checked statements, assumptions,
corrections, and any remaining boundary without requiring inspection of proof
internals.
