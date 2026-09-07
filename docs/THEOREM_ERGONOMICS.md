# Theorem Ergonomics and Front-Facing Declaration Standards

These conventions are for all source-specific wrappers and reusable declarations
that will be inspected by humans first, and Lean second.

## 1) Paper-facing declaration shape

For `PaperInterface.lean` and `MainTheorems.lean`-style files:

- Put the compact human-facing surface in `PaperInterface.lean`: source
  definitions/formulas and named theorem statements in the same order as the
  paper text.
- Put implementation-level source wrappers and proof plumbing in
  `MainTheorems.lean`.
- Keep the dashboard surface small: one row per paper-facing definition or
  named result, plus only genuinely source-facing auxiliary definitions. Move
  helper variants, certificates, proof-seam aliases, and diagnostic endpoints
  to `ProofInterface.lean`, `PostPaperAudit.lean`, or implementation modules.
- Keep source notation explicit, even when generic wrappers exist in `AppliedModelingLib`.
- Prefer source names in docstrings and comments:
  - “Lemma X”, “Theorem 3.1”, “Proposition A”, etc.
- Keep each source item anchored by a concrete declaration with a stable name.
- If a declaration is scaffold-only, name it clearly as placeholder and keep its
  status as `scaffold` / `not started`.

## 2) Declaration quality bar

- Use `## Main declarations` in module docstrings for every paper-facing ledger
  and reusable `AppliedModelingLib` module.
- Place all assumptions on theorem arguments, not in informal side comments.
- For paper-facing declarations, every theorem argument that is an assumption
  rather than a derived object must reference an explicit paper assumption
  declaration in paper-local `Assumptions.lean`. List those declarations
  in `status.json` `review_surface.assumption_names` and validate them with
  `assumption_match_llm.json`.
- Do not pass threshold equations, capacity identities, density formulas,
  selection-mass rows, external certificates, or proof-route witnesses as
  hidden theorem hypotheses. If they are not explicit paper/source model
  assumptions, derive them in Lean or mark the endpoint conditional/partial.
- The repository audit follows `PaperInterface.lean` `abbrev`/`def` aliases
  into all paper-local Lean files and scans paper-facing declaration names
  outside the interface. Moving a certificate or row hypothesis into
  `ProofInterface.lean` does not make a completed paper theorem closed.
- Keep theorem names in `snake_case` in reusable modules and avoid paper-identifer
  prefixes there.
- Keep wrappers for source theorems in source order and use a clear section split:
  definitions → lemmas/corollaries → main theorems.

## 3) Status protocol

- Do not mark a ledger row `formalized` unless:
  - declaration exists,
  - assumptions list is `None` or every remaining assumption is an explicit,
    reviewed paper assumption declaration,
  - and the proof route is source-faithful.
- Use `formalized with caveat` only when the Lean theorem adds something on top
  of the source statement, such as an extra assumption, restriction, corrected
  statement, or indispensable source mismatch. A failed broader abstraction
  outside the paper model is a scope note, not a caveat on a closed paper
  theorem.
- Use `conditional` only when an unresolved hypothesis or bridge is required.
- Reserve `scaffold` / `not started` rows for placeholders.

## 4) Visual DAG protocol

For each paper DAG:

- Keep the metadata block at the top of the figure.
- Keep paper nodes on grid points to make visual inspections fast.
- If you change layout, re-render and inspect a rendered image before merging.
- Do not encode proof debt only in node labels; use paper status text too.

## 5) Quick human verification loop

Before claiming progress:

1. Update `FORMALIZATION_PLAN.md` with any proof-route deviation or new
   outside-Lean strategy that affected the implementation.
2. Update `DependencyDAG.tex` for topology and status.
3. Update `MainTheorems.lean` source wrappers.
4. Update `PaperInterface.lean` so a human can verify source definitions and
   named theorem statements without opening proof files.
5. At review boundaries, run the independent statement check: translate each
   current Lean statement to LaTeX/prose using an LLM with no paper context,
   preserving every visible binder, hypothesis, domain condition,
   named predicate/wrapper application, equivalence/implication direction, and
   conclusion. Then have an independent semantic LLM judge compare that translation against the
   complete original paper statement with no Lean context. A match requires
   semantic equivalence of the hypotheses, subparts, quantifiers, domains,
   constants, normalizations, signs, inequality directions, conclusions, and
   visible inputs. The judge must inspect named Lean predicates/wrappers and
   must not approve by theorem label, phrase overlap, or source-looking name;
   conditional wrappers, hidden strengthening inside named predicates, omitted
   subclaims, source-row/certificate/replay/process/bridge packages, or broad
   aggregates must be judged mismatch or uncertain. If it does not match,
   iterate on the Lean statement before treating the declaration as the target
   theorem.
6. Update paper status surfaces with matching declaration names.
7. Compile the paper folder and the shared `smoke check` file.
8. Run the repository audit with strict style when declarations are finalized.
   At closeout/public-promotion boundaries use
   `python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0`
   so source-hygiene, visible-premise, library-boundary, and Lean-native axiom
   checks run together.

## 6) Reusable declaration discoverability

- Keep library-style theorem names short, snake_case, and grouped by intent:
  - `..._mono`, `..._eq`, `..._iff`, `..._of_...`, `..._implies_...`.
- Keep paper-logic wrappers in paper folders and generic helpers in `AppliedModelingLib/`.
- Add one-line comments when a theorem is a convenience shell over a lower-level
  lemma so downstream users know where to inspect proof details.

## 7) Human verification checklist

- For each new reusable theorem set, add a one-line `#check` in
  `examples/SmokeChecks.lean` (or a nearby sibling file) with the target name.
- Add a matching import path check in `scripts/check_smoke.py` when the module
  is added as part of a new user-facing API surface.
- Keep each paper folder metadata/lemma declaration pair next to each other in
  review order so a human can verify the semantic meaning before reading proofs.
