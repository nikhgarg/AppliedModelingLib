---
name: lean-community-conventions
description: Apply Lean community and mathlib conventions to AppliedModelingLib Lean code, documentation, proof claims, PRs, and local library work. Use when writing or reviewing Lean declarations, naming theorem APIs, preparing mathlib-style files, auditing proof claims, or planning convention cleanup against Lean community guidelines.
---

# Lean Community Conventions

Use this skill when AppliedModelingLib work should move toward Lean community and
mathlib conventions. It is not a full copy of the Lean community guides; it is the
working checklist for local code review and cleanup.

## Sources

- Lean community, "Did you prove it?":
  <https://leanprover-community.github.io/did_you_prove_it.html>
- Lean community, "Contributing to mathlib":
  <https://leanprover-community.github.io/contribute/index.html>
- Lean community, "How to contribute to mathlib":
  <https://leanprover-community.github.io/contribute/how-to-contribute.html>
- Lean community, "Mathlib's values":
  <https://leanprover-community.github.io/contribute/values.html>
- Lean community, "Mathlib naming conventions":
  <https://leanprover-community.github.io/contribute/naming.html>
- Lean community, "Library Style Guidelines":
  <https://leanprover-community.github.io/contribute/style.html>
- Lean community, "Documentation style":
  <https://leanprover-community.github.io/contribute/doc.html>
- Lean community, "Pull request title and description conventions":
  <https://leanprover-community.github.io/contribute/commit.html>
- Lean community, "Pull Request Review Guide":
  <https://leanprover-community.github.io/contribute/pr-review.html>

Scope note: AppliedModelingLib uses these pages as local style and proof-quality
guidance. AI-written or AI-assisted AppliedModelingLib code should not be contributed
back to mathlib.

Adoption policy: apply this style to new Lean files, new shared-library APIs,
new paper-facing declarations, and code that is already being substantially
rewritten. Do not start broad repository-wide renaming, formatting, import, or
documentation refactors just to conform existing code. Record old-code
deviations in a cleanup plan and fix them only at a deliberate cleanup,
library-extraction, or publication boundary.

Paper-local source-indexed declaration names are allowed when they are the
clearest audit path back to a source paper. Shared reusable APIs should use
mathlib-style names.

For the local adoption plan, load
`references/econcs-adoption-plan.md`.

## Proof-Claim Gate

Before saying a Lean result is verified, check the Lean community proof gate:

1. The code is in a Lean repository, not a standalone file.
2. The repository or target builds with `lake build`.
3. The file containing the theorem is imported by the build target.
4. `#print axioms theorem_name` has only the standard Lean axioms expected for
   mathlib-style classical mathematics: `propext`, `Classical.choice`, and
   `Quot.sound`, or a subset.
5. The formal statement actually matches the mathematical claim.

For AppliedModelingLib paper formalizations, distinguish two claims:

- **Lean-closed theorem:** passes the proof-claim gate for its formal statement.
- **Paper-derived theorem:** additionally has all nonstandard model,
  certificate, source-row, and boundary assumptions traced to paper assumptions,
  earlier derived lemmas, or explicit partial-formalization boundaries.

Do not let a successful Lean proof hide a mismatch between the statement and the
paper claim.

## Naming Checklist

Use mathlib capitalization conventions for new library-facing declarations:

- Files: `UpperCamelCase.lean` unless there is a rare object-specific exception.
- Types, structures, classes, inductives, and propositions-as-objects:
  `UpperCamelCase`.
- Proofs and theorem/lemma declarations: `snake_case`.
- Ordinary data and values: `lowerCamelCase`.
- Functions are named like their return values.
- Acronyms move as a group, using the case expected by the first character.
- American English spelling in declaration names.

Theorem names should describe the conclusion first. Use `_of_` to include
hypotheses when needed, in the order the hypotheses appear. Prefer standard
tokens:

- `iff`, `not`, `exists`, `forall`, `mem`, `union`, `inter`, `compl`
- `zero`, `one`, `add`, `mul`, `sub`, `neg`, `inv`, `pow`, `sum`, `prod`
- `lt`, `le`, `gt`, `ge`, with `gt`/`ge` mainly for swapped argument order
- `pos`, `neg`, `nonpos`, `nonneg` instead of spelling out `zero_lt`,
  `lt_zero`, `le_zero`, `zero_le`

Structural lemma patterns:

- Extensionality: `.ext` with `@[ext]`; equivalence form `.ext_iff`.
- Injectivity: `f_injective` for `Function.Injective f`; `f_inj` for
  bidirectional equalities such as `f x = f y <-> x = y`.
- If a lemma is local-only, name or document it as auxiliary, usually with
  `aux`, and keep it near its use.

## Style Checklist

For new or heavily edited library-facing Lean files:

- Keep lines at or under 100 characters.
- Use Unicode mathematical symbols when they improve readability, avoiding
  invisible, direction-changing, or combining-control characters.
- Put top-level commands flush-left; do not indent the contents of namespaces or
  sections merely because a namespace/section is open.
- Put spaces around `:`, `:=`, and infix operators.
- Put `:= by` at the end of the theorem statement line; do not place `by` on a
  line by itself.
- Indent proofs by two spaces; multi-line theorem statement continuations by
  four spaces.
- Give explicit argument types and return types for declarations when practical.
- Prefer arguments left of the colon over quantified/implication conclusions
  when the proof begins by introducing those variables.
- Use `where` syntax for structure and instance terms.
- Give each structure/class field a docstring when it is library-facing.
- Separate declarations by one blank line, except for tight groups of similar
  one-line declarations.
- Prefer one tactic invocation per line unless a short one-line proof or a
  single mathematical idea is clearer.
- Use focusing dots for side goals.
- Avoid `$`; use `<|` or `|>` where needed.
- Treat repeated `erw`/extra `rfl` after `simp` or `rw` as an API smell: consider
  adding the missing API lemma.

Performance and API design:

- Think about transparency. Default `def` is usually preferable; use `abbrev`,
  irreducibility, or structure wrappers only with a clear reason.
- Benchmark or at least inspect performance for changes to imports, classes,
  instances, `simp` lemmas, definitions, or nontrivial refactors.
- Avoid raising heartbeat limits as a long-term fix for fragile code.

## Documentation Checklist

For library-facing files:

- Include copyright header, `module`, grouped `public import`s, grouped
  `import`s, and a module docstring.
- Keep imports alphabetized within public/private import blocks when practical.
- Module docstrings should have a title and summary. Add sections for main
  definitions/statements, notation, implementation notes, references, and tags
  when useful.
- Every definition and major theorem needs a docstring; docstrings on
  mathematical lemmas are encouraged.
- Docstrings should explain mathematical meaning and can slightly abstract away
  implementation details when that helps users.
- Keep Lean comments and docstrings mathematical and local. Do not record
  project chronology, retired proof layers, or rejected approaches there.
  Formalization reports and audits are not a destination for that implementation
  history either: they should state current source-relevant mathematics only.
  If the history is genuinely needed for future work, keep it in a private
  handoff or commit message.
- Put Lean declaration names and variables in backticks.
- Put raw URLs in angle brackets.
- Use `#lint`, `#lint only docBlame`, or `#lint only docBlame docBlameThm` as a
  targeted check before mathlib-style cleanup is called complete.

## Local PR Checklist

For AppliedModelingLib PRs that should resemble mathlib-style review:

- Prefer small, self-contained PRs.
- Make sure the target builds; CI can do full builds, but local targeted builds
  should be clean.
- Use conventional PR titles:
  `<type>(<optional-scope>): <subject>`, with types such as `feat`, `fix`,
  `doc`, `style`, `refactor`, `test`, `chore`, `perf`, and `ci`.
- PR subjects and bodies use imperative present tense, no initial capitalization
  for the subject, and no trailing period.
- Put discussion/questions after `---` if they should not enter git history.

## Local Review Routine

When reviewing an AppliedModelingLib file for convention alignment:

1. Run the proof-claim gate for paper-facing claims.
2. Scan filenames, declaration names, theorem names, and namespace placement.
3. Scan style: line length, theorem indentation, `:= by`, explicit types,
   structure/instance `where`, and one-blank-line declaration separation.
4. Scan docs: file module docstring, docstrings for definitions/major theorems,
   cross references, and warnings for auxiliary or special-use declarations.
5. Scan API shape: weak hypotheses, strong conclusions, useful simp/ext/inj
   lemmas, import placement, and performance-sensitive declarations.
6. Record issues as a cleanup plan instead of mixing broad renaming/refactor
   churn into active paper proof work.
