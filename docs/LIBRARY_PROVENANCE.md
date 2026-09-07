# Shared Library Provenance

`AppliedModelingLib/` may expose reusable theorems that take explicit certificates,
witnesses, external-boundary hypotheses, or source-shaped row packages. These
are valid library APIs: they force every caller to provide the missing evidence
as an argument.

The intended reusable-library shape is:

1. Generic definitions and theorems live in `AppliedModelingLib/`.
2. Any formula, row package, or certificate that comes from a paper source is an
   explicit theorem argument or certificate field, not a hidden library constant.
3. Paper code either constructs that argument from source primitives in Lean or
   exposes it as a validated paper assumption.

Do not bake a paper-specific displayed formula into a reusable library
definition and then prove generic consequences of that definition. If a formula
is generic and derived from library primitives, keep it in the library with a
generic name. If it is paper-source data, keep it in the paper folder or make it
an explicit certificate parameter.

For paper status, the rule is stricter. A paper-facing theorem that calls a
certificate-taking library theorem is fully formalized only when the paper code
constructs that certificate from the paper's source primitives, or when the
certificate is exposed as a validated source assumption in `Assumptions.lean`
and `assumption_match_llm.json`. If the certificate remains a theorem argument,
the paper endpoint is partial or conditional.

The same rule applies inside a paper folder at the visible interface. If a
reviewed theorem, its expanded `#check` statement, or a direct paper-local
alias target still takes a certificate, hidden hypothesis, source-row equation,
or proof-boundary premise, that premise is part of the reviewed theorem unless
it is routed through a validated assumption. If a helper constructs the
certificate internally from already proved facts, the premise is discharged;
confirm transitive proof debt with Lean's `#print axioms` rather than a
syntactic dependency scan. Axioms, constants, opaque declarations, and unsafe
declarations are not acceptable ways to discharge such evidence.

Ordinary theorem side conditions are different from provenance boundaries. If a
paper-facing theorem visibly states a source condition, the row-local statement
judge validates that condition against the source. The repository audit checks
the expanded paper-facing signatures and direct aliases for
certificate/source-row/external-boundary premises; it should not treat every
derived inequality or measurability side condition in a helper as a hidden
paper assumption.

Run this audit during closeout and public PR preparation:

```bash
python3 scripts/audit_repository.py --library-only --library-premise-audit
```

The command fails on reusable-library hygiene errors and lists reusable-library
declarations with certificate/source-boundary parameters. Informational library
findings are not proof failures by themselves; they are a checklist for paper
wrappers. Completed paper wrappers should not expose those parameters unless
they are validated paper assumptions.

The command prints only the first batch of informational findings by default.
Use `--info-limit -1` for the full direct certificate-boundary inventory, or
`--info-limit 0` in CI when only errors and warnings should appear in the log.

The library-only audit checks more than theorem names:

- It scans theorem, lemma, def, abbrev, structure, class, and inductive
  declarations in `AppliedModelingLib/`.
- It rejects source-shaped reusable API names such as paper/displayed/source
  formula, source row, threshold, branch, or window declarations. Rename these
  to a paper-neutral abstraction, make the source formula an explicit argument,
  or move the source-specific definition into the paper folder.
- It rejects reusable `Assumption`/`Hypothesis` declarations and paper/source
  provenance wording in `AppliedModelingLib/*.lean`. Paper-source provenance belongs in
  paper-local `Assumptions.lean`, validation reports, and source-audit notes;
  shared modules should describe generic mathematical APIs.
- It requires `AppliedModelingLib.LibraryDefinitionAudit` to be imported by the root
  library target. That module contains build-checked equivalence lemmas for
  standard-name wrappers, so a drift such as an incorrectly stated Jensen
  convexity definition fails at Lean build time rather than relying on prose.
- It rejects section-level `variable` declarations that hide proof-boundary
  premises such as certificates, witnesses, assumptions, boundary packages, or
  regularity/window packages. Ordinary generic data predicates may remain
  section variables; proof-boundary evidence should be an explicit theorem or
  definition parameter so callers cannot inherit it silently.
- It rejects axioms, constants, opaque declarations, unsafe proof declarations,
  and guarded `#check`/`#eval` lines in reusable code.
- It rejects concrete paper folder IDs and citation prefixes in reusable code
  and rejects paper theorem-number labels in shared Lean comments. The checker
  discovers paper terms from `papers/` and uses data-configured allowlists for
  established algorithm/domain names, so it is not a hardcoded function-name
  denylist.

This is a static audit over current Lean source. It builds an in-memory
declaration index every run; no checked-in dependency index is used or allowed,
because that would go stale. It complements, but does not replace, the
paper-local statement, assumption, hidden-premise, and Lean-native axiom
prechecks. The default paper audit runs `#print axioms` on paper-facing rows to
catch transitive global proof debt exactly, and checks expanded signatures for
visible premises.

The source-hygiene pass is a guardrail against generic-code drift, not a proof
of source correctness. It prevents paper-specific formulas, theorem numbering,
and citation labels from becoming invisible reusable-library assumptions. A
formula-bearing paper result still needs either a Lean derivation from the
paper primitives, an explicit validated source assumption, or a documented
partial/caveat boundary.

For status, unresolved visible boundary findings or unapproved `#print axioms`
findings are errors for `formalized` papers. They may be warnings for a paper
intentionally marked `partially formalized`, but the paper-local `status.json`,
`FINAL_VALIDATION_REPORT.md`, README, and DAG must name the boundary rather
than presenting an all-green proof surface.

CI runs the same library-only command before the default repository audit, with
informational findings suppressed.
