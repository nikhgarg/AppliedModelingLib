import Sievert26SimpleAuctions.MainTheorems

/-!
# Human-Facing Paper Interface: Machine-Verified Two-Sided Bounds for Simple Multi-Item Auctions

Source: Max Sievert, *Machine-Verified Two-Sided Bounds for Simple Multi-Item Auctions:
2.1946 <= c* <= 2.486 and an i.i.d. Lower Bound above 1.316*, Zenodo v1.0.1
(DOI `10.5281/zenodo.24482558`, 2026-11-23).

## Source-facing definitions (paper.tex, Section 1 Setting, lines 51-58)
- `FinDist`: finitely supported probability distribution on `ℝ≥0` (`Basic.lean`).
- `SREV`: optimal separate-selling revenue (`Basic.lean`).
- `BREV`: optimal grand-bundle revenue (`Basic.lean`).
- `Mechanism`: incentive-compatible and individually rational (possibly randomized) direct mechanism (`Basic.lean`).
- `REV`: supremum expected revenue over all IC+IR mechanisms (`Basic.lean`).
- `cStar`: universal approximation constant `inf { c | ∀ m D, REV(D) ≤ c * max(SREV(D), BREV(D)) }` (`Bracket.lean`).

## Named results (paper.tex, Section 1, lines 59-92)
- `general_lower_boundSpec` / `general_lower_bound`: Theorem 1 (lines 59-65).
- `universal_upper_boundSpec` / `universal_upper_bound`: Theorem 2 (lines 67-76).
- `two_sided_bracketSpec` / `two_sided_bracket`: Corollary 3 (lines 78-80).
- `iid_lower_boundSpec` / `iid_lower_bound_thm`: Theorem 4 (lines 82-88).
- `iid100_lower_boundSpec` / `iid100_lower_bound`: Proposition 5 (lines 90-92).
-/

namespace Sievert26SimpleAuctions

/--
Theorem 1 (General Lower Bound), `paper.tex:59-65`.

There exist `m : ℕ` and independent finitely supported distributions `D : Fin m → FinDist`
on `ℝ≥0` such that `REV(D) > 2.1946 * max(SREV(D), BREV(D))`, witnessed by a deterministic
IC+IR mechanism.
-/
def general_lower_boundSpec : Prop :=
  ∃ (m : ℕ) (D : Fin m → FinDist),
    (2.1946 : ℝ) * max (SREV D) (BREV D) < REV D ∧
    ∃ M : Mechanism (Fin m),
      (∀ v i, M.alloc v i = 0 ∨ M.alloc v i = 1) ∧
      (2.1946 : ℝ) * max (SREV D) (BREV D) < M.rev D

/-- Exact proof endpoint for Theorem 1 (`general_lower_boundSpec`). -/
theorem general_lower_bound : general_lower_boundSpec :=
  lower_bound_with_det

/--
Theorem 2 (Universal Upper Bound), `paper.tex:67-76`.

For every finite index set `ι` and family `D : ι → FinDist`,
`REV(D) ≤ 1.1187 * SREV(D) + 1.367299 * BREV(D)`.
In particular, for every `m : ℕ` and `D : Fin m → FinDist`,
`REV(D) ≤ 2.486 * max(SREV(D), BREV(D))`.
-/
def universal_upper_boundSpec : Prop :=
  by
  classical
  exact
    (∀ (ι : Type) [Fintype ι] (D : ι → FinDist),
      REV D ≤ (1.1187 : ℝ) * SREV D + (1.367299 : ℝ) * BREV D) ∧
    (∀ (m : ℕ) (D : Fin m → FinDist),
      REV D ≤ (2.486 : ℝ) * max (SREV D) (BREV D))

/-- Exact proof endpoint for Theorem 2 (`universal_upper_boundSpec`). -/
theorem universal_upper_bound : universal_upper_boundSpec := by
  classical
  refine ⟨fun ι _ D => upper_bound_two D, fun m D => ?_⟩
  have h := upper_bound m D
  have hnum : (2486 / 1000 : ℝ) = (2.486 : ℝ) := by norm_num
  rwa [hnum] at h

/--
Corollary 3 (Two-Sided Bracket), `paper.tex:78-80`.

`2.1946 ≤ c* ≤ 2.486`.
-/
def two_sided_bracketSpec : Prop :=
  (2.1946 : ℝ) ≤ cStar ∧ cStar ≤ (2.486 : ℝ)

/-- Exact proof endpoint for Corollary 3 (`two_sided_bracketSpec`). -/
theorem two_sided_bracket : two_sided_bracketSpec := by
  have h := cStar_mem
  have hnum : (2486 / 1000 : ℝ) = (2.486 : ℝ) := by norm_num
  rwa [hnum] at h

/--
Theorem 4 (i.i.d. Lower Bound), `paper.tex:82-88`.

There exist `m : ℕ` (specifically `m = 40`) and a finitely supported distribution `F`
on `ℝ≥0` such that `REV(F^{⊗ 40}) > 1.316 * max(SREV(F^{⊗ 40}), BREV(F^{⊗ 40}))`,
witnessed by the deterministic two-part tariff with entry fee `9` and item price `4`.
-/
def iid_lower_boundSpec : Prop :=
  ∃ F : FinDist,
    (1.316 : ℝ) * max (SREV fun _ : Fin 40 => F) (BREV fun _ : Fin 40 => F) <
      REV (fun _ : Fin 40 => F) ∧
    ∃ M : Mechanism (Fin 40),
      (∀ v i, M.alloc v i = 0 ∨ M.alloc v i = 1) ∧
      (∀ v, M.pay v =
        if (9 : ℝ) ≤ ∑ i : Fin 40, max (v i - 4) 0 then
          9 + ∑ i : Fin 40, if (4 : ℝ) ≤ v i then (4 : ℝ) else 0
        else 0) ∧
      (1.316 : ℝ) * max (SREV fun _ : Fin 40 => F) (BREV fun _ : Fin 40 => F) <
        M.rev (fun _ : Fin 40 => F)

/-- Exact proof endpoint for Theorem 4 (`iid_lower_boundSpec`). -/
theorem iid_lower_bound_thm : iid_lower_boundSpec :=
  iid_lower_bound_with_mech

/--
Proposition 5 (100-item i.i.d. Exact Rational Bound), `paper.tex:90-92`.

For `n = 100` i.i.d. items with `Pr[X ≥ k] = 3 / (25 * max(k, 4))` for `1 ≤ k ≤ 13`
and `0` for `k > 13`, the deterministic mechanism with entry fee `9` and item price `4`
satisfies `REV / max(SREV, BREV) ≥ 1.324907`.
-/
def iid100_lower_boundSpec : Prop :=
  ∃ F : FinDist,
    (∀ i : Fin F.size, ∃ k : ℕ, F.val i = (k : ℝ)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ 13 → F.tail (k : ℝ) = (3 : ℝ) / (25 * max (k : ℝ) 4)) ∧
    (∀ k : ℕ, 13 < k → F.tail (k : ℝ) = 0) ∧
    ∃ M : Mechanism (Fin 100),
      (∀ v i, M.alloc v i = 0 ∨ M.alloc v i = 1) ∧
      (∀ v, M.pay v =
        if (9 : ℝ) ≤ ∑ i : Fin 100, max (v i - 4) 0 then
          9 + ∑ i : Fin 100, if (4 : ℝ) ≤ v i then (4 : ℝ) else 0
        else 0) ∧
      0 < max (SREV fun _ : Fin 100 => F) (BREV fun _ : Fin 100 => F) ∧
      (1.324907 : ℝ) ≤
        M.rev (fun _ : Fin 100 => F) /
          max (SREV fun _ : Fin 100 => F) (BREV fun _ : Fin 100 => F) ∧
      (1.324907 : ℝ) ≤
        REV (fun _ : Fin 100 => F) /
          max (SREV fun _ : Fin 100 => F) (BREV fun _ : Fin 100 => F)

/-- Exact proof endpoint for Proposition 5 (`iid100_lower_boundSpec`). -/
theorem iid100_lower_bound : iid100_lower_boundSpec :=
  iid100_lower_bound_proof

end Sievert26SimpleAuctions
