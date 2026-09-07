# New Contributor Workflow

This guide is for a contributor adding or repairing one paper formalization
without taking responsibility for existing papers. The stable entrypoint is
`scripts/paper_contribution.py`; the individual audit scripts are maintainer
interfaces, not prerequisites for learning the contribution flow.

## Scope Guarantee

A one-paper pull request owns only:

- `papers/<PaperName>/**`
- `papers/<PaperName>.lean`
- one exact additive `[[lean_lib]]` registration for `<PaperName>` in
  `lakefile.toml`

It does not own or update:

- `papers/status.json`
- `papers/human_status.json`
- `docs/PAPER_STATUS.md`
- `site/index.html`
- any other paper folder or audit evidence

The paper-scoped check and pull-request CI build and audit only `<PaperName>`.
Existing paper state cannot make that lane fail. A change to shared library,
tooling, audit protocol, workflow, or multiple papers instead uses the
integration lane.

## 1. Create A Public-Based Working Branch

Fork the public repository on GitHub, then clone the fork and retain the project
repository as `upstream`:

```bash
git clone https://github.com/example-contributor/EconCSLib.git
cd EconCSLib
git remote add upstream https://github.com/nikhgarg/EconCSLib.git
git fetch upstream
git switch -c paper/abc24-short-title upstream/main
```

Do not push unfinished or sensitive work to a public fork. Work locally, in
your own private repository, or in a private collaboration space until the
branch is safe for public review. A public fork has public Git history.
Never commit source PDFs, TeX archives, or extracted source text and then delete
them: those bytes remain in public history. The paper lane checks the entire
candidate history and blocks recognizable source-artifact paths and binary
formats. It cannot determine the copyright status of arbitrarily renamed text,
so if any third-party source bytes entered the branch, rebuild it from clean
commits.

Before substantial work, coordinate the exact paper version and intended scope
with Nikhil Garg at ngarg@cornell.edu.

## 2. Check The Local Environment

From the repository root, run:

```bash
python3 scripts/paper_contribution.py doctor
```

The command checks the required Python and Lean/Lake environment and reports
optional source-extraction or DAG-rendering tools separately. Resolve required
failures before scaffolding; an unavailable optional tool should not be
mistaken for a Lean failure.

## 3. Pin The Source And Draft The Statement Spec

Keep the exact source PDF, TeX archive, or transcript outside the repository.
Obtain the exact version before starting. The example assumes the bytes already
exist at `$SOURCE_ARTIFACT`; do not run `init-spec` until the `test` succeeds.

```bash
PAPER=ABC24ShortTitle
SOURCE_VERSION='arXiv v1, 2024-01-03'
WORK_DIR="${HOME}/econcslib-review/$PAPER"
SOURCE_ARTIFACT="$WORK_DIR/paper.pdf"
STATEMENT_SPEC="$WORK_DIR/statement-spec.json"
mkdir -p "$WORK_DIR"
# Copy or download the exact source version here before continuing.
test -f "$SOURCE_ARTIFACT"
python3 scripts/paper_contribution.py init-spec \
  "$SOURCE_ARTIFACT" \
  --version "$SOURCE_VERSION" \
  --output "$STATEMENT_SPEC"
```

The specification records the exact source version and SHA-256 identity. Edit
its `targets` list with the paper-facing named results you intend to formalize,
including source locations, literal source statements, Lean declaration names,
and proposed Lean types. This file is a local scaffold input; do not add a
root-level `statement-spec.json` to the pull request.

**STOP here before running `new`.** Replace every `REPLACE ...` value and
`replace_with_lean_name` in `$STATEMENT_SPEC`, and add one complete target
object per named result in scope. The guard below must print nothing and
succeed:

```bash
! grep -nE 'REPLACE|replace_with_lean_name' "$STATEMENT_SPEC"
```

The source bytes must also remain uncommitted unless redistribution rights have
been checked. Neither `$SOURCE_ARTIFACT` nor `$STATEMENT_SPEC` belongs in Git;
the scaffold commits only source identity and review evidence.

## 4. Scaffold The Paper

Use the citation-style folder convention, such as `ABC24ShortTitle`:

```bash
PAPER_URL=https://arxiv.org/abs/2401.01234
python3 scripts/paper_contribution.py new "$PAPER_URL" \
  --folder "$PAPER" \
  --title "A Short Formalization Example" \
  --authors "Ada Author and Bao Collaborator" \
  --version "$SOURCE_VERSION" \
  --statement-spec "$STATEMENT_SPEC"
```

The command creates the paper folder and root import, adds only the focused Lake
library registration, and validates the source-pinned statement skeleton. It
does not add the paper to broad default targets or regenerate repository-wide
status files.

`--statement-spec` is optional. Without it, `PaperInterface.lean` starts empty;
the scaffold never invents a theorem placeholder. Freeze and audit exact
paper-facing theorem types before serious proof work.

### Existing Paper Repair

For an existing paper, skip Sections 3-4 and do not edit `lakefile.toml`.
Confirm the pinned source version in its validation report, work only in its
paper folder and root import, and continue with the checks below.

## 5. Work Inside The Paper Boundary

The main human-facing files are:

1. `papers/<PaperName>/PaperInterface.lean`: source definitions and named
   theoretical statements in paper order.
2. `papers/<PaperName>/FINAL_VALIDATION_REPORT.md`: source version, verdict,
   assumptions, corrections, boundaries, and validation evidence.
3. `papers/<PaperName>/README.md`: paper metadata and result ledger.
4. `papers/<PaperName>/docs/DependencyDAG.tex`: paper-facing dependency map.
5. `papers/<PaperName>/status.json`: machine-readable paper-local status.

Keep proof plumbing in `MainTheorems.lean`, `ProofInterface.lean`, or smaller
paper-local modules. `PaperInterface.lean` must expose the actual audited
statements, not merely aliases with source-looking names.

Every theorem premise must be derived in Lean or exposed as a source-backed
paper assumption. Do not replace a missing proof with a certificate, source-row
package, record field, or assumption that already contains the conclusion.

Normal paper coverage concerns named theoretical content: definitions, lemmas,
propositions, theorems, and corollaries. Figures, captions, computational
examples, and empirical results enter only an explicitly requested deep
all-prose review.

If reusable library work becomes necessary, put it in a separate integration
pull request when practical. Adding `AppliedModelingLib/`, tooling, workflow, protocol,
or another paper path to this branch intentionally escalates validation beyond
the one-paper lane.

## 6. Use Fast Checks During Proof Work

Run the fast path after statement or proof milestones:

```bash
python3 scripts/paper_contribution.py check ABC24ShortTitle --fast
```

After committing, you can also catch pull-request scope mistakes by naming the
comparison base:

```bash
python3 scripts/paper_contribution.py check ABC24ShortTitle \
  --fast --base upstream/main
```

With `--base`, the command requires a clean worktree and checks the committed
base-to-`HEAD` candidate; uncommitted edits are deliberately excluded. The
fast check validates the paper-owned structure and focused Lean surface. It
does not claim source-grounded closeout, refresh aggregate files, or inspect
existing paper audits.

For an existing paper, an uncommitted development check compiles any imported
paper modules but defers the extra trusted-base graph comparison. The committed
`--base` check and `prepare-pr` compare Lean-emitted module closures and reject
new cross-paper dependencies. Modules already reachable at the base are build
dependencies, not papers the contributor must audit.

## 7. Run The Local Acceptance Check

At completion, keep the pinned source bytes available locally and run the full
paper check while developing:

```bash
python3 scripts/sync_paper_status.py --paper ABC24ShortTitle
python3 scripts/paper_contribution.py check ABC24ShortTitle
```

This full paper-scoped check is the acceptance boundary. It uses the repository
closeout planner and its current reusable evidence, so unchanged items are not
needlessly regenerated. It checks only the selected paper and its imported Lean
dependencies.

The command asks the planner to resolve status and saved source-evidence
readiness before compiling. Do not prebuild the paper or invoke dashboard and
repository-audit children by hand: a source-delta or eligibility stop should
finish before Lean work, and a cold cache has exactly one planner-scheduled
paper build.

Do not remove the source bytes and substitute a structural public-checkout
check for this step. A formalization is not source-audited merely because its
Lean proofs compile.

## 8. Prepare And Open The Pull Request

Publication is a project decision, not something scaffolding grants. Once the
paper is approved for a public PR, set `repository_visibility` in the
paper-local `status.json` to `public`, render only that paper's owned README,
and commit the candidate. Do not run the aggregate status generator.

```bash
python3 scripts/sync_paper_status.py --paper ABC24ShortTitle
git add -- papers/ABC24ShortTitle papers/ABC24ShortTitle.lean lakefile.toml
git commit -m "Formalize ABC24ShortTitle"
```

Then prepare the clean branch against current public main:

```bash
git fetch upstream
git rebase upstream/main
python3 scripts/paper_contribution.py prepare-pr ABC24ShortTitle \
  --base upstream/main
```

`prepare-pr` verifies the one-paper path boundary, reruns the source-present
paper check against the exact committed candidate, and prints its paper and
base identity. It rejects aggregate status/site files,
unrelated papers, shared code, and non-additive Lake changes from the scoped
lane.

After the branch contains only public-safe material:

```bash
git push -u origin paper/abc24-short-title
```

Open a pull request against `nikhgarg/EconCSLib:main` and complete
`.github/pull_request_template.md`.

## Pull-Request CI

CI derives contribution scope from the Git diff; labels and checkboxes cannot
waive it. For a valid one-paper pull request, CI:

- builds the complete focused `<PaperName>` Lake target;
- runs the paper-scoped structural and audit gates;
- validates source receipts in public-checkout mode when licensed source bytes
  are absent; and
- does not build, refresh, or audit existing papers.

The structural source-receipt check is intentionally weaker than the
source-present local closeout. Maintainers may ask for the local check result or
additional source review, but they should not ask a one-paper contributor to
repair unrelated repository state.

An integration PR may run broader builds and audits because it changes shared
behavior. Move such work out of the paper-only branch when a narrow separation
is possible.

After merge, maintainers use
`python3 scripts/sync_paper_status.py --aggregate-only` in a separate branch.
The resulting four-file pull request has its own cheap trusted lane: no Lean
setup, builds, or semantic audit reruns. Contributors are not responsible for
that mechanical follow-up.

## Contribution License

Unless explicitly marked otherwise, contributed Lean code, scripts,
documentation, and site source are accepted under the Apache License, Version
2.0. Source papers are third-party works and are not covered by that license.
