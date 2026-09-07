# Lean Style and Organization

This repository follows Mathlib-style conventions where they fit an EC paper
formalization library.

## Module organization

- Use `UpperCamelCase.lean` file names for Lean modules.
- Put reusable results under `AppliedModelingLib/`; put source-faithful paper wrappers
  under `papers/[Paper]/`.
- Keep imports narrow. Library modules and paper proof files should import the
  leaf modules that own the declarations they use, not aggregate roots such as
  `AppliedModelingLib` unless the file is itself an aggregate import file.
- Every new reusable `AppliedModelingLib` module should start with a module docstring
  containing a title, a short summary, and a `## Main declarations` list.
- Paper-facing ledgers should also have a module docstring, but the content
  should describe the source paper interface rather than internal helper code.

Run `python3 scripts/audit_repository.py --strict-style` when doing an
organization pass. The default audit stays conservative so active paper work is
not blocked by legacy modules that predate these conventions.

For theorem ergonomics and human-facing ledgers, use
[`THEOREM_ERGONOMICS.md`](THEOREM_ERGONOMICS.md) as the working
checklist before any status updates.

## Declaration names

- Structures, classes, inductive types, and named predicates use
  `UpperCamelCase`.
- Functions and data terms use `lowerCamelCase`.
- Theorems, lemmas, and proof terms use `snake_case`.
- Generic library theorem names should describe the mathematical conclusion,
  using Mathlib-style suffixes such as `_eq`, `_le`, `_lt`, `_iff`, `_of_...`,
  and `_mono`.
- Paper-facing declarations may include paper identifiers or theorem numbers
  when that improves auditability, but reusable `AppliedModelingLib` declarations should
  not carry paper-specific names.

## API shape

- Prefer generic finite/discrete interfaces first, then paper-local wrappers.
- Use namespaces to group projections and theorems around their primary object
  when dot notation will make downstream code easier to search.
- If a theorem is intended as a rewrite lemma, state it in the orientation that
  should usually be used by `rw`/`simp`.
- Keep certificate structures separate from certificate assumptions: an
  interface is reusable library API, while an undischarged paper hypothesis
  belongs in the paper wrapper and README/DAG status.
