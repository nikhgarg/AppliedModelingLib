# Validation Model

Public status guidance updated: 2026-09-06

`config/formalization_audit_protocol.json` is the normative machine-readable
source for current audit versions, coverage scope, reuse identity, build
selection, and correction/assumption categories. This document explains the
validation model and defers to that protocol when older prose or historical
artifact labels conflict with it.

AppliedModelingLib separates three questions that are easy to conflate.

## 1. What Lean Checks

Lean checks that the formal proof terms establish the displayed Lean theorem
statements from the imported library declarations and explicit theorem
hypotheses. A successful Lean build is therefore evidence about the formal
statements in the repository.

Lean does not, by itself, decide whether a theorem statement is the right
translation of a source-paper statement.

During private paper intake, a theorem may deliberately have an audited
source-shaped type and a temporary `by sorry` body. That establishes only a
**statement-audited skeleton**: Lean has elaborated the target, but has not
checked a proof. The canonical declaration-manifest digest freezes the reviewed
type, definition/abbreviation values, and name-free repository-local reducible
dependency closure so proof work cannot silently change them. Current v11
review compares verbatim source anchors with Lean's expanded transparent Spec,
including its assumptions, conclusions, and source-connected prerequisites. A
paper is Lean-closed only after every such
body is replaced and the dependency closure contains no `sorryAx`.

## 2. What Human Review Checks

Human statement review is the review path for the source-to-Lean translation
boundary. A reviewer compares a source-paper definition, formula, theorem, or
subclaim against the corresponding Lean statement and records a dashboard
judgment.

Human-review records should identify the reviewer, timestamp, source statement,
Lean declaration, verdict, and notes. Public counts should be read as counts of
saved dashboard judgments, not as a general claim that a whole paper has been
independently reviewed.

## 3. What LLM Audit Checks

LLM-as-judge passes are audit evidence. They help find missing source claims,
hidden theorem premises, stale row mappings, mismatched formulas, and review
surface problems. The standard lanes are:

- Lean-to-text translation from the Lean statement alone;
- source-vs-translation statement matching;
- assumption-provenance matching;
- source-inventory-to-dashboard coverage;
- recursive source-record and boundary-input classification;
- source-proof fidelity and checked defect support; and
- holistic source/DAG/source-json comparison.

These lanes are intentionally separate. Row-local statement matching cannot
establish paper coverage, and source-coverage matching cannot establish that
each Lean row has the exact same hypotheses and conclusion as the source.

Current statement judgments use an obligation ledger rather than a bare
`matches` label. The ledger enumerates source and Lean assumptions and
conclusions, requires every source conclusion to be recovered, and requires
every Lean assumption to be source-backed or derived by an explicit semantic
bridge. Names, ids, and raw pretty-printed declaration spelling only route or
document entries; renaming a theorem, field, wrapper, or record must not change
the verdict after a unique elaborated semantic match.

The current semantic lane is source-to-expanded-Spec review v11. Lean's
builder-issued graph separately checks the Spec/proof relation, dependency
closure, and endpoint safety. The closeout planner first validates any retained
accepted receipt; otherwise it requires the current graph-native contract or
returns a migration action. Earlier v10 sidecars remain historical evidence.
Their version labels must never be changed to manufacture a migration.

Paper-coverage and declaration-manifest schemas have independent version
numbers. Reuse requires the exact applicable semantic and source identities,
not matching names or a prior successful build. A proof-body change requires
current proof-closure evidence even when the semantic statement is unchanged.

Historical legacy-v10 transition evidence used either the original trusted-Git-tree
authority or a centrally configured immutable material-identity manifest. The
portable manifest contains no paper-name or declaration-name credit: those
strings are navigation labels only. A current closeout is grandfathered only
when its source-item identity uniquely locates one manifest entry and its full
material identity matches that entry. The full identity binds the source
items, elaborated statements, per-item source/statement/dependency/model
associations, selected targets, corrections, scope, available validator
schemas, and the semantic protocol identity. The validator rejects an absent,
duplicate, ambiguous, stale, or mismatched entry and then requires v11.

The manifest's exact file bytes are SHA-256-pinned in the normative protocol.
Its engine schema and the bytes of the generic projection engine are pinned as
well. The protocol identity deliberately excludes the transition authority,
manifest digest, manifest itself, and generated repository aggregates, which
prevents a self-hash cycle. Manifest validation reads only ordinary files in
the candidate checkout; it does not require private Git objects. Generate it
only from an explicit candidate root and explicit completed-paper folder list
with `scripts/legacy_v10_trust_ledger.py`; folder and paper labels in that list
locate inputs but never contribute semantic credit.

The conclusion-provenance lane likewise expands every reachable
proposition-bearing theorem-input record, compares proposition types modulo
bound-variable renaming, rejects sibling-record repackaging, and follows local
constructor dependencies. It follows both `abbrev` and reducible `def` type
aliases, including imported repository records, and recognizes generic data
carriers from their `Type`/`Sort` binder kinds rather than their identifier
spelling. Unknown non-data inputs fail closed. Suffixes such as `Certificate`,
`Assumptions`, or `Run` may appear in diagnostics but do not authorize or reject
a premise. The static record walker also fails closed on a theorem binder headed
by a paper/repository-local reducible type family that it cannot normalize (for
example a conditional type returning a record on one branch). This is
conservative: expose a direct audited type/alias or add Lean-Meta expansion;
free-text classification cannot clear the unresolved dependency.

These automated checks remain triage, not semantic certification. A structural
ledger can prove that every obligation was considered; it cannot prove that an
agent transcribed the source formula correctly or that free-text
`semantic_basis` and `bridge_statement` claims are mathematically true. The
validator rejects missing and explicitly name-only bridge prose, but truth of
the remaining prose still requires an independently pinned source comparison
and ultimately human review.

The source-side atom list has the same limit. It is curated from the pinned full
statement rather than mechanically derived from mathematical prose, so a full
statement digest does not itself prove that `source_obligations` contains every
subclaim. Require a distinct source curator and statement judge and have the
human reviewer compare the atom list against the complete pinned excerpt, not
only against the listed atoms.

Producer identity is another explicit trust boundary. The evidence-integrity
audit pairwise-rejects recorded overlap among formalizer, source curator, Lean
translator, statement judge, and coverage judge, but historical sidecars do not
consistently identify every role. These are also free-form, unauthenticated
attestations; the tool cannot prove who actually performed the work. Record the
identities distinctly at closeout and treat absent or overlapping attestations
as pending human certification, even when the structural checks pass.

Pinned source artifacts are private-by-default inputs, not ordinary checkout
contents. `source-audited*` is ignored to avoid accidentally publishing source
TeX or archives. A fresh CI checkout is therefore non-certifying for the source
pin unless the exact bytes are securely provisioned or fetched and then
SHA-256-verified. An artifact may be force-tracked only after an explicit
redistribution-rights review. Missing bytes must leave release source evidence
red; the recorded digest alone is not a substitute.

Ordinary public-checkout CI may use
`audit_evidence_integrity.py --allow-missing-source-bytes`. That mode still
requires a safe canonical relative path and SHA-256 but emits a non-certifying
warning when licensed bytes are absent. Never use it for a strict release or
human/independent source-certification claim.

LLM audit status should report `missing`, `stale`, `uncertain`, `mismatch`,
`conditional_boundary`, and related statuses directly. Those statuses are not
human review and should not be counted as human dashboard sign-off.

## 4. Public Status Reading

The public display policy is in
[`STATUS.md`](STATUS.md#public-website-display). Public labels summarize checked
coverage; the report gives the exact source comparison and remaining scope.
Technical mathematical status and closeout acceptance remain separate.

Read public paper status as:

- `Formalized`: the repository contains checked formalized results. Read the
  report's named-result comparisons for their precise coverage.
- `Formalization gap:` in a note: substantial additional assumptions,
  simplifications, or unproved bridges or conclusions in the formalization.
  The note names the affected theorem and remaining scope. It does not claim
  that the paper needs a correction. Minor source clarifications and conditions
  implied by the source do not need a public table note.
- `Partially formalized`: the retained public designation for LOS02 and LMMS04,
  whose broader formalizations remain unfinished.
- `Human review`: saved dashboard rows reviewed by a human.
- `LLM audit`: tracked machine-readable sidecars checking statement matching,
  coverage, assumption provenance, source records, and holistic coverage.

No single column is a complete trust label. The final validation report should
give the combined status in plain language.

For configured schema-2 source-proof fidelity ledgers, each defect also states
its issue-level `status_impact`: `formalized_note`,
`formalized_with_caveat`, or `partially_formalized`. The audit checks that these
issue judgments agree with the paper status. The field distinguishes the
severity of the mathematical issue from `statement_impact`, which only records
whether the source proof line or source statement is affected.

For source certification, plain `Formalized` is not enough. The exact source
artifact must be pinned by digest, every source item and theorem premise must
have a resolvable locator, independent producer/judge attestations must be
recorded. A claim of complete human statement review additionally requires
complete saved human judgments. A zero human-review count is not itself a
machine-closeout or public-release blocker; the report must disclose it.
Because source artifacts are normally untracked, this byte attestation is
available when CI securely provisions or reproducibly fetches and hash-checks
the exact artifact, or redistribution review permits tracking it. A normal fresh
checkout without those bytes is structurally testable but not source-certified.
State unavailable source-byte verification and incomplete human review on
their respective evidence axes rather than treating them as mathematical gaps.
