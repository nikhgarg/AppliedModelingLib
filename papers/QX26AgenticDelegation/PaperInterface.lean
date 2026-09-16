import QX26AgenticDelegation.Model
import QX26AgenticDelegation.MainTheorems
import QX26AgenticDelegation.Assumptions

/-!
# Human-Facing Paper Interface: Agentic Delegation and the Language Frontier of Software Developers

This is the compact Lean file a human should read after formalization to check
whether the paper's definitions and named theorem statements were represented
correctly. Keep the row-level dashboard and LLM audit statements in this file
for every paper. Move implementation details, proof aliases, and bulky helper
lemmas behind imported modules such as `AuditInterface.lean`, but expose the
audited paper-facing statements directly here; do not use
`paper_interface.audit_surface_path`.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- A material reusable `EconCSLib` primitive may remain a reference here only
  after `audit/library_semantic_review.json` records its exact bounded library
  declaration and an explicit byte-pinned paper-source connection. The
  dashboard and human-review packet show and source-check that declaration
  before the dependent Spec; a library name, docstring, or glossary is not a
  semantic bridge. Do not add a duplicate paper claim merely to restate it.
- If a named theorem needs a hypothesis that is not derived from earlier Lean
  declarations, declare that hypothesis in `Assumptions.lean` and list it in
  `status.json` `review_surface.assumption_names`.
- Then state the named results directly, with assumptions visible in each
  theorem signature by referencing named paper assumptions imported from
  `Assumptions.lean`.
- In the statement-first phase, write every complete source-facing statement as
  a transparent `<name>Spec : Prop` here, exactly once. Put the paired
  theorem/lemma of that exact type in `ProofInterface.lean`; its temporary
  proof body may be `by sorry` only in a private draft. This separation keeps
  the human semantic surface free of thin wrapper declarations.
- Before drafting that Lean surface, independently inventory every material
  source atom from exact pinned source quote bytes. Do not infer source atoms
  from declaration, binder, field, function, or source-map names.
- Run raw-source-to-expanded-Spec statement matching plus recursive
  premise/conclusion provenance on the skeleton. The semantic comparison uses
  only byte-pinned source quotes (and separately pinned source context) against
  the expanded transparent Spec; map summaries and proof wrappers are not
  semantic inputs. Then freeze each canonical Lean declaration-manifest digest.
- In the proof phase, replace the `ProofInterface.lean` `sorry` with a short
  proof that calls into `MainTheorems.lean` or lower proof files without
  changing the specification or theorem type. Any specification/type change
  invalidates the freeze and requires a fresh statement audit.
- At formalized closeout, complete the v11 realization receipt: Lean Meta checks
  the theorem has exactly the transparent Spec type; each source atom is bound
  to the elaborated Spec surface; closure traversal includes proof and instance
  arguments; and every material terminal has a source, approved correction or
  additional assumption, checked derivation, or version-pinned foundation
  disposition. No data, container, or identifier-based exemption is allowed.
- The transparent `...Spec` is the sole semantic-review target for its source
  claim. The paired theorem/lemma is a proof endpoint whose exact Spec type is
  verified by Lean Meta, not a duplicate source-to-Lean comparison row.
- Keep proof endpoints, exhaustive endpoint aliases, and proof-seam checks in
  `ProofInterface.lean`, implementation modules, or `ProofLedger.lean`, not
  here. Do not create new `PostPaperAudit.lean` or `AuditLedger.lean` files;
  those names are legacy.

## Named Results

Each entry has one semantic-review target (`Spec`) and one proof endpoint (the
paired theorem/lemma). The human dashboard and review packet present that pair
once rather than treating the two declarations as duplicate paper claims.

- `Proposition1_frontierExpansionSpec` -> `Proposition1_frontierExpansion`: Proposition 1 (Frontier expansion), Proposition 1; page 13 of arXiv 2605.25438v2 PDF; Appendix A.3 page 59.
- `Proposition2_activationBandSpec` -> `Proposition2_activationBand`: Proposition 2 (Activation band for unfamiliar languages), Proposition 2; page 13 of arXiv 2605.25438v2 PDF; Equation (8); Appendix A.4 page 60.
- `Proposition3_dynamicCumulativeSpec` -> `Proposition3_dynamicCumulative`: Proposition 3 (Dynamic cumulative-language effect), Proposition 3; page 15 of arXiv 2605.25438v2 PDF; Equation (10); Appendix A.6 pages 61-62.
- `Proposition4_specialistHeterogeneitySpec` -> `Proposition4_specialistHeterogeneity`: Proposition 4 (Specialist and ability heterogeneity), Proposition 4; Appendix A.5 page 60 of arXiv 2605.25438v2 PDF; Equation (22).
- `Proposition5_repositoryExpansionSpec` -> `Proposition5_repositoryExpansion`: Proposition 5 (Repository expansion), Proposition 5; Appendix A.8 page 63 of arXiv 2605.25438v2 PDF.
-/

namespace QX26AgenticDelegation

/--
Proposition 1 (Frontier expansion)

Paper statement: For every developer, language, date, and opportunity realization, Z^2_{ik,t} ≥ Z^1_{ik,t}, hence N^2_{it} ≥ N^1_{it} path by path.

Source location: Proposition 1; page 13 of arXiv 2605.25438v2 PDF; Appendix A.3 page 59
Source status: pinned statement-spec transcription; independent source audit pending

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def Proposition1_frontierExpansionSpec : Prop :=
  ∀ (V_S V_C V_D : Real), (if 0 ≤ max V_S V_C then (1 : Real) else 0) ≤ (if 0 ≤ max (max V_S V_C) V_D then (1 : Real) else 0) ∧ ∀ (n : Nat) (V_S V_C V_D : Fin n → Real), Finset.sum (Finset.univ : Finset (Fin n)) (fun k => if 0 ≤ max (V_S k) (V_C k) then (1 : Real) else 0) ≤ Finset.sum (Finset.univ : Finset (Fin n)) (fun k => if 0 ≤ max (max (V_S k) (V_C k)) (V_D k) then (1 : Real) else 0)

/--
Proposition 2 (Activation band for unfamiliar languages)

Paper statement: Consider an unfamiliar language satisfying Assumption 1. If B_{ik,t} > 0, then Z^2_{ik,t} - Z^1_{ik,t} = 1[T^D_{ik,t} ≤ ω_{ik,t} < T^S_{ik,t}].

Source location: Proposition 2; page 13 of arXiv 2605.25438v2 PDF; Equation (8); Appendix A.4 page 60
Source status: pinned statement-spec transcription; independent source audit pending

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def Proposition2_activationBandSpec : Prop :=
  (∀ (T_S gamma s rC : Real), gamma * s - rC ≤ 0 → min T_S (T_S - (gamma * s - rC)) = T_S) ∧ (∀ (omega T_D T_S : Real), T_D < T_S → ((if 0 ≤ omega - T_D then (1 : Real) else 0) - (if 0 ≤ omega - T_S then (1 : Real) else 0) = 1 ↔ T_D ≤ omega ∧ omega < T_S))

/--
Proposition 3 (Dynamic cumulative-language effect)

Paper statement: For an initially unfamiliar language, let p^g_{ik} be the per-period first-use hazard under generation g. If p^2_{ik} ≥ p^1_{ik}, the expected cumulative-language effect at event-time horizon s is ΔC_i(s) = ∑_{k∈U_i} [(1-p^1_{ik})^{s+1} - (1-p^2_{ik})^{s+1}] ≥ 0, which in the closed-frontier benchmark p^1_{ik}=0 < p^2_{ik} is strictly increasing and concave over the observed horizon.

Source location: Proposition 3; page 15 of arXiv 2605.25438v2 PDF; Equation (10); Appendix A.6 pages 61-62
Source status: pinned statement-spec transcription; independent source audit pending

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def Proposition3_dynamicCumulativeSpec : Prop :=
  ∀ {K : Type*} (U : Finset K) (p1 p2 : K → Real) (s : Nat), (∀ k, k ∈ U → 0 ≤ p1 k ∧ p1 k ≤ p2 k ∧ p2 k ≤ 1) → 0 ≤ Finset.sum U (fun k => (1 - p1 k) ^ (s + 1) - (1 - p2 k) ^ (s + 1))

/--
Proposition 4 (Specialist and ability heterogeneity)

Paper statement: Under Assumption 3, expected expansion into initially unfamiliar languages is E[E_i | a_i, U_i] = U_i p_i(a_i, A), where E_i ≡ ∑_{k∈U_i} (Z^2_{ik} - Z^1_{ik}). It is increasing in the stock of unfamiliar-language candidates U_i and in general ability a_i. The largest extensive-margin gains accrue to high-ability specialists.

Source location: Proposition 4; Appendix A.5 page 60 of arXiv 2605.25438v2 PDF; Equation (22)
Source status: pinned statement-spec transcription; independent source audit pending

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def Proposition4_specialistHeterogeneitySpec : Prop :=
  ∀ {K : Type*} (U : Finset K) (delta : K → Real) (p : Real), (∀ k, k ∈ U → delta k = p) → Finset.sum U delta = (U.card : Real) * p

/--
Proposition 5 (Repository expansion)

Paper statement: Suppose each repository requires at least one programming language and carries an entry cost that is weakly decreasing when the developer can activate that language. If agentic delegation weakly expands the active-language set, then the expected number of repositories the developer can contribute to weakly increases. It increases strictly when some repositories require languages in the delegation activation band.

Source location: Proposition 5; Appendix A.8 page 63 of arXiv 2605.25438v2 PDF
Source status: pinned statement-spec transcription; independent source audit pending

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def Proposition5_repositoryExpansionSpec : Prop :=
  ∀ {Repo Lang : Type*} (ell : Repo → Lang) (c1 c2 : Repo → Real) (hc : ∀ r, c2 r ≤ c1 r) (Omega : Repo → Real) (Z1 Z2 : Lang → Prop) (hZ : ∀ k, Z1 k → Z2 k), ∀ r, c1 r ≤ Omega r ∧ Z1 (ell r) → c2 r ≤ Omega r ∧ Z2 (ell r)

end QX26AgenticDelegation
