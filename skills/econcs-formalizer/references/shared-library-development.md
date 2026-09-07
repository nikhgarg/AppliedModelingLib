# Shared-Library Development

Use this reference when deciding whether mathematics belongs in the reusable
library, locating an existing API before proving a paper-local replacement,
extracting a reusable result, or changing a shared interface.

## Required orientation

Read these live repository documents before changing shared ownership:

- `docs/APPLIEDMODELINGLIB_DOMAIN_INDEX.md` for current discoverability and narrow
  supported imports;
- `docs/ARCHITECTURE.md` for repository layers and workflow boundaries; and
- `docs/PROBABILITY_LIBRARY_ROADMAP.md` and
  `docs/OPTIMIZATION_LIBRARY_ROADMAP.md` for domain APIs and planned extensions.

Use `skills/lean-community-conventions/SKILL.md` for new or substantially
changed Lean APIs. Use the relevant `proof-*.md` reference for domain-specific
theorem discovery.

## Find before proving

1. Search by mathematical concept, theorem shape, and namespace, not only the
   paper's terminology.
2. Inspect the exact declaration and its actual consumers. A matching name is
   not a semantic match, and a different name is not evidence of duplication.
3. Import the smallest leaf or curated family facade that owns the needed API.
   Broad root and foundations aggregates are interactive preludes, not default
   paper imports.
4. If the library has the right mathematical contract, reuse it and expose any
   material paper-source connection through the ordinary semantic-prerequisite
   lane. Audit treatment does not depend on the code location.

## Extraction and consolidation

- Put a declaration in mathematical `Foundations` only when its contract is
  application-independent and no foundational import points upward into a
  field or application layer.
- Preserve meaningful domain names as transparent aliases or thin structures
  when the same carrier has different field semantics. Sharing `X -> PMF Y`,
  for example, does not erase the distinction between an MDP policy, a
  recommender policy, and a human-feedback policy.
- Consolidate definitions only after comparing Lean-elaborated types,
  transparent values, totalization conventions, and all consumers. Prove the
  specialization or equivalence explicitly.
- Do not build a parser for Lean declarations or infer semantics from syntax,
  declaration kind, filename, namespace, or line number. Use Lean-native
  environment and Meta utilities for declarations, types, values,
  dependencies, ownership, and semantic identity.
- Avoid universal structures, coercion layers, or typeclass surfaces that add
  more proof and elaboration burden than the duplication they remove.

## Safe shared changes

Before a physical move, namespace change, or consolidation, record the exact
declaration and consumer inventory through the repository's Lean-native graph
tools. Validate moved declarations entry by entry. A pure relocation may reuse
semantic review through unique checked semantic identity; a changed
mathematical contract receives targeted review. Do not add pairwise engine
compatibility bridges solely to preserve old routes.

Keep the move's comparison denominator bounded, but expand transparent
semantics over the complete Lean-loaded project closure. A helper moved outside
the selected batch must not become an opaque qualified name merely because a
diagnostic tool selected fewer modules to report. Acquire that closure through
the shared immutable build-input provider and let Lean own dependency and
declaration discovery. Do not expose a caller override for a partial semantic
workspace, add a second Python/Lake reachability preflight, or parse Lean source
to reproduce information the native inventory already validates.

During a live paper closeout, make only an essential shared change needed for
that closeout. Defer unrelated library cleanup until after acceptance so the
expensive graph and semantic pass do not churn within the transaction.

Run focused leaf, facade, dependent-library, and representative paper builds.
For a reorganization campaign, do not migrate older papers until the final
hierarchy and namespace are stable; migrate each paper once and then remove
temporary compatibility imports.
