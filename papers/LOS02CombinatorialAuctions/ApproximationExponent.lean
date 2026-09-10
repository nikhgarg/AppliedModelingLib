import LOS02CombinatorialAuctions.FiniteGraphTableEncoding
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theorem 6.1 approximation-exponent transport

The source proof of Theorem 6.1 invokes clique inapproximability and uses that
its reduction has at most quadratically many goods.  This module isolates the
elementary real-power comparison needed to transfer that cited clique ratio to
the auction ratio.  It does not state or assume the cited hardness theorem.
-/

namespace LOS02CombinatorialAuctions

/-- When the reduction has at most quadratically many goods, the source's
`k ^ (-1 / 2 + epsilon)` auction ratio is at least the corresponding
`|V| ^ (-1 + 2 * epsilon)` clique ratio. -/
theorem clique_ratio_le_goods_ratio
    (vertexCount goodsCount : Nat)
    (hgoods : 1 ≤ goodsCount)
    (hgoods_le : goodsCount ≤ vertexCount * vertexCount)
    (epsilon : ℝ)
    (hepsilon : epsilon ≤ 1 / 2) :
    (vertexCount : ℝ) ^ (-1 + 2 * epsilon) ≤
      (goodsCount : ℝ) ^ (-1 / 2 + epsilon) := by
  let exponent : ℝ := -1 / 2 + epsilon
  have hexponent_nonpos : exponent ≤ 0 := by
    dsimp [exponent]
    linarith
  have hexponents : -1 + 2 * epsilon = 2 * exponent := by
    dsimp [exponent]
    ring
  have hvertex_nonneg : 0 ≤ (vertexCount : ℝ) := by
    positivity
  have hgoods_pos : 0 < (goodsCount : ℝ) := by
    exact_mod_cast hgoods
  have hgoods_le_square : (goodsCount : ℝ) ≤ (vertexCount : ℝ) ^ (2 : ℝ) := by
    calc
      (goodsCount : ℝ) ≤ ((vertexCount * vertexCount : Nat) : ℝ) := by
        exact_mod_cast hgoods_le
      _ = (vertexCount : ℝ) ^ (2 : ℝ) := by
        norm_num [Nat.cast_mul, pow_two]
  calc
    (vertexCount : ℝ) ^ (-1 + 2 * epsilon) =
        ((vertexCount : ℝ) ^ (2 : ℝ)) ^ exponent := by
      rw [hexponents]
      exact Real.rpow_mul hvertex_nonneg 2 exponent
    _ ≤ (goodsCount : ℝ) ^ exponent :=
      Real.rpow_le_rpow_of_nonpos hgoods_pos hgoods_le_square hexponent_nonpos

end LOS02CombinatorialAuctions
