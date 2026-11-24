# Agent Source Audit: Sievert26SimpleAuctions

## Overall status: PASS
- Reviewed final holistic audit surface identity: `a2b2feeb41c3da7b9ee422f84b39d252100c0ab43d66ea590f6758b3c98eb692`
- Final audit scope: `complete_current_surface`

Independent final adversarial audit performed by `independent-final-adversarial-auditor-2026-11-24` with no authoring, repair, or semantic-judgment history on this paper. The audit inspected the complete byte-pinned source manuscript, the planner-issued schema-3 final holistic audit surface (`.lake/closeout-objects/sha256/6f/6f199eeeb05e62234dd5bfcffcb3786d4cdca236373024faba49220d4b392a7b.json`), the Lean review graph (`.lake/closeout-objects/sha256/1a/1a7b4984df0167f4b18f530a3c8d11e7d76a3b2d30c6db44f5299e1e5014b75f.json`), all 31 tracked Lean files, the typed statement map and semantic ledgers, and all terminal human-facing artifacts.

## Frozen Surface and Policy Assurance

- **Schema and surface binding**: Schema 3 (`final-holistic-policy-aware-source-and-lean-semantic-surface-v3`). Recomputing `final_holistic_audit_surface_sha256` directly from the frozen surface artifact reproduces `a2b2feeb41c3da7b9ee422f84b39d252100c0ab43d66ea590f6758b3c98eb692`.
- **Frozen `review_policy_assurance`**: `schema: 1`, `source_scope: "all_named_theory"`, `repeat_final_scope: "main_primary"`, `required_final_adversary_count: 1`.
- **Byte-pinned source corpus and region partition**: `source-audited.tex` (21,267 bytes, 233 lines, SHA-256 `97fea30c6a68dc12ea843d2c704adbd20d58d74edb528db3c71e2ee3f217073c`) is partitioned exhaustively into one `main_text` region (lines 1–233, quote SHA-256 `084a0f7680b5562c681b9415017f15fe7df273c5472b5ea18eccfbf05e446471`). Every source item and prose definition maps into `main_text`; no appendix or supplement exists in the source.
- **Terminal review projection**: All 11 `terminal_review.semantic_review_rows` (6 `paper_prerequisite` rows and 5 `source_result` rows) match the frozen `audit/paper_semantic_prerequisites.json` and `audit/v11_raw_source_spec_screening.json` digests, claim atoms, source input bundles, and `v11_lean_review_graph` proof contracts. All 42 `content_inputs` in the closeout execution plan match the current workspace files (with LF-normalized agreement on root `lake-manifest.json` and `lean-toolchain`).

## Independent Source-First Inventory

Reading all 233 lines of `source-audited.tex` independently of Lean declarations yields the complete normal-scope theoretical surface:

- **Source version and digest**: Max Sievert, *Machine-Verified Two-Sided Bounds for Simple Multi-Item Auctions: $2.1946 \le c^* \le 2.486$ and an i.i.d.\ Lower Bound above $1.316$*, Zenodo v1.0.1 (DOI `10.5281/zenodo.24482558`, November 23, 2026); `source-audited.tex`, SHA-256 `97fea30c6a68dc12ea843d2c704adbd20d58d74edb528db3c71e2ee3f217073c`.
- **Governing setting definitions (Section 1, lines 51–58)**: Independent finitely supported probability distributions on $\mathbb{R}_{\ge 0}$ (`FinDist`), separate-selling revenue $\mathrm{SREV}(D)$, grand-bundle revenue $\mathrm{BREV}(D)$, direct IC+IR mechanisms $M = (\mathrm{alloc}_M, \mathrm{pay}_M)$ on $\mathbb{R}_{\ge 0}^m$, optimal revenue $\mathrm{REV}(D)$, and universal constant $c^*$. All six are mapped under `setting_definitions` (`inventory_role: source_semantic_declaration`) and reviewed individually as paper-local semantic prerequisites without inflating the 5-row result denominator.
- **Named theoretical results (Section 1, lines 59–92; shared counter `theorem` / `corollary` / `proposition`)**:
  1. **Theorem 1** (`thm:lb`, lines 59–65): General Lower Bound — existence of $m \in \mathbb{N}$ and independent finitely supported $D_1, \dots, D_m$ on $\mathbb{R}_{\ge 0}$ with $\mathrm{REV}(D) > 2.1946 \max\{\mathrm{SREV}(D), \mathrm{BREV}(D)\}$, witnessed by a deterministic mechanism.
  2. **Theorem 2** (`thm:ub`, lines 67–76): Universal Upper Bound — for every finite index set $\iota$ and $D : \iota \to \mathrm{FinDist}$, $\mathrm{REV}(D) \le 1.1187\,\mathrm{SREV}(D) + 1.367299\,\mathrm{BREV}(D)$, and in particular for every $m \in \mathbb{N}$ and $D : \mathrm{Fin}\,m \to \mathrm{FinDist}$, $\mathrm{REV}(D) \le 2.486 \max\{\mathrm{SREV}(D), \mathrm{BREV}(D)\}$.
  3. **Corollary 3** (`cor:bracket`, lines 78–80): Two-Sided Bracket — $2.1946 \le c^* \le 2.486$.
  4. **Theorem 4** (`thm:iid`, lines 82–88): i.i.d.\ Lower Bound — existence of $m$ (specifically $m = 40$) and finitely supported $F$ on $\mathbb{R}_{\ge 0}$ with $\mathrm{REV}(F^{\otimes m}) > 1.316 \max\{\mathrm{SREV}(F^{\otimes m}), \mathrm{BREV}(F^{\otimes m})\}$, witnessed by a deterministic two-part tariff (entry fee $9$, item price $4$).
  5. **Proposition 5** (`prop:iid100`, lines 90–92): 100-item i.i.d.\ Exact Rational Bound — for $n = 100$ i.i.d.\ items with $\Pr[X \ge k] = \frac{3}{25 \max(k, 4)}$ for $1 \le k \le 13$ and $0$ for $k > 13$, the deterministic mechanism with entry fee $9$ and item price $4$ satisfies $\mathrm{REV} / \max\{\mathrm{SREV}, \mathrm{BREV}\} \ge 1.324907$.
- **Out-of-scope / supporting material verified non-omitted**: Abstract summary (lines 33–43), Section 1 literature review, Table 1 summary, and scope note explicitly disclaiming continuous-distribution discretization (lines 45–49, 94–119), Sections 2–4 proof overviews (lines 120–164, supporting proof context for Theorems 1, 2, 4 and Proposition 5), Section 5 non-rigorous float experiments and stylised financial illustration (lines 166–175), Section 6 reproducibility note (lines 177–179), and Bibliography (lines 181–233). No theorem, lemma, proposition, corollary, remark, or standalone named claim is omitted.

## Adversarial Lean Interface and Proof Verification

Every source definition and result was challenged against `Basic.lean`, `Bracket.lean`, `PaperInterface.lean`, `Assumptions.lean`, and all proof modules:

- **Model primitives and edge cases (`Basic.lean`, `Bracket.lean`)**:
  - `FinDist` enforces `val_nonneg`, `prob_nonneg`, and `prob_sum = 1` (ruling out empty support `size = 0`). Duplicate support values or zero-mass points aggregate additively across `FinDist.tail`, `bundleTail`, and `Mechanism.rev`, matching pushforward laws exactly.
  - `FinDist.rev`, `BREV`, and `REV` use `Real.sSup` over nonempty, bounded-above sets (`FinDist.rev_bdd`, `BREV_bdd`, `REV_bdd`, zero mechanism in `Reindex.lean`), and `cStar := sInf ValidConstants` operates on a nonempty, bounded-below set (`Bracket.lean`). No `sSup`/`sInf` junk-value edge cases occur, including at `m = 0` or zero valuations.
  - `Mechanism` faithfully encodes `alloc : (ι → ℝ) → ι → ℝ` with values in `[0, 1]` and IC/IR over all nonnegative valuation vectors `v, v' : ι → ℝ`.
- **Result specifications (`PaperInterface.lean`)**:
  - `general_lower_boundSpec` / `general_lower_bound`: Exact match to Theorem 1, asserting both the strict `REV` inequality and a deterministic IC+IR witness `M` with `∀ v i, M.alloc v i = 0 ∨ M.alloc v i = 1` and `2.1946 * max (SREV D) (BREV D) < M.rev D`.
  - `universal_upper_boundSpec` / `universal_upper_bound`: Exact match to Theorem 2, quantifying universally over finite index types `ι : Type` (`[Fintype ι]`, instantiating `DecidableEq` classically without changing values since `Fintype` is a `Subsingleton`) for `1.1187 * SREV D + 1.367299 * BREV D`, and over `m : ℕ`, `D : Fin m → FinDist` for `2.486 * max (SREV D) (BREV D)`. Decimal literals in Lean elaborate as exact rationals in `ℝ`.
  - `two_sided_bracketSpec` / `two_sided_bracket`: Exact match to Corollary 3 (`2.1946 ≤ cStar ∧ cStar ≤ 2.486`).
  - `iid_lower_boundSpec` / `iid_lower_bound_thm`: Exact match to Theorem 4 (`m = 40`, `> 1.316` for both `REV` and `M.rev`, deterministic `M` with exact two-part tariff payment rule entry fee `9`, item price `4`). Independently checked mathematically that determinism + IC + IR + the exact payment formula `if 9 ≤ ∑ max (v i - 4) 0 then 9 + ∑ (if 4 ≤ v i then 4 else 0) else 0` uniquely forces the two-part tariff allocation rule on every nonnegative valuation vector $v \in \mathbb{R}_{\ge 0}^{40}$, including indifference boundaries.
  - `iid100_lower_boundSpec` / `iid100_lower_bound`: Exact match to Proposition 5 (`n = 100`). The integer-support clause `∀ i, ∃ k : ℕ, F.val i = k` combined with exact tails `3 / (25 * max k 4)` for `1 ≤ k ≤ 13` and `0` for `k > 13` uniquely pins down the probability distribution on `{0, 4, …, 13}` (consistent with Section 4 lines 158, 164), making existential and universal law formulations mathematically equivalent while ruling out vacuous satisfaction. Explicit `0 < max (SREV) (BREV)` rules out division-by-zero traps, and both `M.rev / max(SREV, BREV) ≥ 1.324907` and `REV / max(SREV, BREV) ≥ 1.324907` are proved for the same uniquely forced deterministic two-part tariff.
- **Proof realization, assumptions, and kernel soundness**:
  - `Assumptions.lean` declares zero assumptions; `library_semantic_review.json` is empty (`0` reusable library prerequisites; all external dependencies terminate in Lean/Mathlib foundations `Init`, `Std`, `Batteries`, `Mathlib`).
  - Scanned all 31 Lean files: zero `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque`, or `partial`. All computational checks (`KernelRun.lean`, `CertRun.lean`, `IIDKernel.lean`, `IID100Kernel.lean`) execute inside the Lean kernel via `decide +kernel`.
  - All five `semantic_contracts` in `v11_lean_review_graph` confirm `matches: true`, `mode: "proves"`, `evidence_axiom_closure: ["Classical.choice", "Quot.sound", "propext"]`, `evidence_axiom_closure_checked: true`, `evidence_is_unsafe: false`, `evidence_value_has_sorry: false`.
  - Internal proof certificate structures (`Data`, `UCert`, `IIDData`, `IID100Data`, with 1846 grid cells and 35 $\alpha$-steps in `CertData.lean`) are fully discharged internally by kernel-verified instances and never leak into `PaperInterface.lean`.

## Human-Facing Artifacts and Denominator Verification

- **Denominator**: Exactly 5 claimed results in `status.json`, `paper_statement_map.json`, `FINAL_VALIDATION_REPORT.md`, and `HUMAN_REVIEW_PACKET.tex`/`pdf`, with 6 setting definitions properly classified as semantic prerequisites rather than result rows.
- **Final validation report (`FINAL_VALIDATION_REPORT.md`)**: Passes `scripts.final_validation_report_sections`, `scripts.final_validation_report_status`, and `scripts.report_memo_coverage`. Full title matches the source; Sections 1–11 stay strictly human-facing without Lean identifiers or audit chronology; Section 4 matches printed numbering (Theorems 1, 2, 4, Corollary 3, Proposition 5) with exact dispositions; Sections 12–21 accurately report counts, scope, and public-safe closeout links.
- **Dependency DAG (`docs/DependencyDAG.tex`, `docs/DependencyDAG.pdf`)**: Visually inspected rendered PDF. All six setting definitions and five named results appear cleanly with accurate mathematics, crisp arrowheads, clear reading order, and zero node or edge overlaps.
- **Human review packet (`docs/HUMAN_REVIEW_PACKET.tex`, `docs/HUMAN_REVIEW_PACKET.pdf`)**: Visually inspected all 17 rendered pages. Displays all 8 governing declarations, 6 paper-specific semantic prerequisites, and 5 main-text source claims with intact Unicode math glyphs and verbatim alignment to `PaperInterface.lean` and the semantic ledgers.
- **Status and README (`status.json`, `README.md`)**: `formalization_status: "formalized"`, `assumption_policy: "strict"`, `main_caveat: "None."`, `human_review: 0/5`, and `README.md` (`Publication details not listed` per `sync_paper_status.py` for an uncatalogued private paper) are consistent. (Non-blocking display note: `status.json` currently records derived non-acceptance `paper_interface.line_count: 141` versus 139 lines in `PaperInterface.lean`; this field is explicitly excluded from acceptance projection and refreshed automatically by `closeout_status_projection.py`.)

## Findings

- **Substantive / blocking findings**: None.
- **Audit result**: `PASS` over the complete current policy-selected surface (`complete_current_surface`) bound to `a2b2feeb41c3da7b9ee422f84b39d252100c0ab43d66ea590f6758b3c98eb692`.
