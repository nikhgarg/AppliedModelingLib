# AppliedModelingLib Lean Community Convention Adoption Plan

This plan applies Lean community and mathlib conventions to AppliedModelingLib without
turning active paper proof work into broad style churn.

## Source Baseline

Primary Lean community sources:

- "Did you prove it?": <https://leanprover-community.github.io/did_you_prove_it.html>
- "Contributing to mathlib": <https://leanprover-community.github.io/contribute/index.html>
- "How to contribute to mathlib": <https://leanprover-community.github.io/contribute/how-to-contribute.html>
- "Mathlib's values": <https://leanprover-community.github.io/contribute/values.html>
- "Mathlib naming conventions": <https://leanprover-community.github.io/contribute/naming.html>
- "Library Style Guidelines": <https://leanprover-community.github.io/contribute/style.html>
- "Documentation style": <https://leanprover-community.github.io/contribute/doc.html>
- "Pull request title and description conventions":
  <https://leanprover-community.github.io/contribute/commit.html>
- "Pull Request Review Guide": <https://leanprover-community.github.io/contribute/pr-review.html>

## Principles For AppliedModelingLib

1. Mathlib-style cleanup is valuable, but proof correctness and source
   provenance remain higher priority for active paper work.
2. Apply strict mathlib conventions first to shared `AppliedModelingLib/` library code.
   Paper folders may preserve source-facing names when that improves auditability,
   but exported library APIs should move toward mathlib style.
3. Do not rename public paper-facing declarations casually. If a paper-facing
   name is intentionally source-indexed, keep it or add a mathlib-style alias
   only if it helps reuse.
4. Every cleanup pass should be small enough to review and should avoid changing
   theorem statements unless the change is explicitly part of the plan.
5. Use these conventions for local quality. Do not plan to upstream AI-written
   or AI-assisted AppliedModelingLib code to mathlib.
6. Apply conventions forward. New library files, new paper files, new shared
   APIs, and substantially rewritten code should follow the convention skill.
   Existing code should not be broadly refactored only for style.

## Phase 1: Forward Convention Gate

Create a lightweight manual checklist for new and substantially touched Lean
code, then later automate parts of it:

- Proof claim:
  - target builds with `lake build`;
  - theorem file is imported by the target;
  - `#print axioms` for main claims has only expected standard axioms, unless an
    explicit paper boundary is documented;
  - statement matches the claimed paper/library theorem.
- Naming:
  - file names `UpperCamelCase.lean` for library modules;
  - theorem names `snake_case`;
  - structures/classes/types/propositions `UpperCamelCase`;
  - values/functions `lowerCamelCase`;
  - theorem names use conclusion-first and `_of_` hypotheses where appropriate.
- Style:
  - 100-character line target;
  - `:= by` on same line;
  - explicit argument/return types for declarations;
  - `where` syntax for instances/structures;
  - docstrings on library-facing fields.
- Docs:
  - module docstring present for shared library files;
  - definitions and major theorems documented;
  - raw URLs in angle brackets;
  - declaration names in backticks.

Deliverable: add this checklist to the new-paper, active-proof edit, and
library-extraction routines after the draft skill has been reviewed. The gate is
forward-looking; it should not trigger broad refactors of old files.

## Phase 2: Inventory Existing Deviations

Run a non-mutating inventory before refactoring:

- Find library files without module docstrings or with missing copyright/module
  headers.
- Find long declaration names that encode paper titles or theorem numbers in
  shared library code.
- Find helper lemmas in `AppliedModelingLib/` whose names include paper-specific words.
- Find files with many lines over 100 characters.
- Find library-facing structures/classes with undocumented fields.
- Find repeated `erw`, extra `rfl`, heartbeat bumps, or local transparency
  hacks that indicate missing API.

Output should be a review report, not an immediate mass rename.
Inventory findings are backlog items. Do not apply them during active proof work
unless the affected declaration is already being changed for mathematical
reasons.

## Phase 3: Apply To New Code First

For new shared library modules and new paper-facing Lean files:

- Start from a mathlib-style file skeleton.
- Keep imports minimal and alphabetized inside public/private groups.
- Add a module docstring with main definitions, main statements, implementation
  notes, references, and tags when relevant.
- Use mathlib naming conventions from the start.
- Provide a small API around every new definition: simp lemmas, ext/inj lemmas
  where natural, monotonicity or measurability lemmas where relevant, and
  examples of intended use when the API is subtle.

This phase avoids churn and prevents new divergence.

## Phase 4: Refactor Shared Library APIs

Refactor only after inventory identifies high-value targets and the user or
maintainer has agreed that the current work is a cleanup boundary:

- Rename shared declarations toward mathlib naming.
- Move paper-facing wrappers out of `AppliedModelingLib/` and into paper folders.
- Split large files when import placement or compile time would improve.
- Add docstrings and module docs to shared files that are already reused across
  multiple papers.
- Add missing API lemmas rather than relying on repeated unfolding, `erw`, or
  long local proof scripts.

Each refactor should build affected papers and preserve paper-facing theorem
statements unless explicitly approved.

## Phase 5: Mathlib-Style Local Review

For any AppliedModelingLib contribution that should be especially close to mathlib style:

- Break into small PRs: single-lemma fixes, doc fixes, or narrow API additions
  first.
- Write PR titles using the Lean community convention.
- Keep the work in AppliedModelingLib as a downstream project.
- Ensure a human reviewer can understand every statement, definition, proof, and
  design choice.
- Do not open mathlib PRs with AI-written or AI-assisted AppliedModelingLib code.

## Automation Candidates

Later scripts can check:

- library `.lean` file names not in `UpperCamelCase`;
- lines over 100 characters in `AppliedModelingLib/`;
- missing module docstrings in shared library files;
- missing docstrings for structures/classes/defs in shared library files;
- theorem names in library files containing source-paper numbers;
- `set_option maxHeartbeats` and related performance overrides;
- new `abbrev`, `irreducible`, or `opaque` declarations for review;
- uses of `$` in Lean files;
- whether main paper claims have an associated `#print axioms` audit record.

Automation should report findings first. Do not auto-rename declarations without
a human-reviewed migration plan.

## Review Cadence

- New code: apply the checklist immediately.
- Substantially edited code: apply the checklist to the edited declarations and
  nearby API surface.
- Active paper proof work: defer broad convention cleanup until a real proof
  boundary.
- Library extraction: run the naming/style/doc checklist before publishing or
  public release.
- Public PR preparation: include a convention pass for changed shared library
  files only, unless the PR is explicitly a style cleanup.
