import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace AppliedModelingLib
namespace Sequence

/--
Elementary epsilon definition of convergence for real sequences indexed by
natural numbers.
-/
def SeqTendsTo (x : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → |x k - L| ≤ δ

/--
If `x k` is eventually at most `y k + δ` for every positive `δ`, and the
two real sequences converge to `X` and `Y`, then `X ≤ Y`.
-/
theorem le_of_seqTendsTo_eventually_le_add
    {x y : ℕ → ℝ} {X Y : ℝ}
    (hx : SeqTendsTo x X)
    (hy : SeqTendsTo y Y)
    (happrox :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k → x k ≤ y k + δ) :
    X ≤ Y := by
  by_contra hnot
  have hlt : Y < X := lt_of_not_ge hnot
  have hgap_pos : 0 < X - Y := sub_pos.mpr hlt
  let η := (X - Y) / 4
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  obtain ⟨Nx, hNx⟩ := hx η hη_pos
  obtain ⟨Ny, hNy⟩ := hy η hη_pos
  obtain ⟨Na, hNa⟩ := happrox η hη_pos
  let K := max Nx (max Ny Na)
  have hxK : |x K - X| ≤ η :=
    hNx K (Nat.le_max_left Nx (max Ny Na))
  have hyK : |y K - Y| ≤ η := by
    exact hNy K
      (Nat.le_trans (Nat.le_max_left Ny Na)
        (Nat.le_max_right Nx (max Ny Na)))
  have haK : x K ≤ y K + η := by
    exact hNa K
      (Nat.le_trans (Nat.le_max_right Ny Na)
        (Nat.le_max_right Nx (max Ny Na)))
  have hX_le_x : X ≤ x K + η := by
    have hleft := (abs_le.mp hxK).1
    linarith
  have hy_le_Y : y K ≤ Y + η := by
    have hright := (abs_le.mp hyK).2
    linarith
  have hle : X ≤ Y + 3 * η := by
    linarith
  have hlt_final : Y + 3 * η < X := by
    dsimp [η]
    linarith
  exact (not_lt_of_ge hle) hlt_final

/--
Multiplication by a nonnegative constant preserves real sequence convergence.
-/
theorem SeqTendsTo.const_mul_of_nonneg
    {x : ℕ → ℝ} {X c : ℝ}
    (hx : SeqTendsTo x X) (hc : 0 ≤ c) :
    SeqTendsTo (fun k => c * x k) (c * X) := by
  intro δ hδ
  have hscale_pos : 0 < c + 1 := by
    linarith
  have hη_pos : 0 < δ / (c + 1) :=
    div_pos hδ hscale_pos
  obtain ⟨N, hN⟩ := hx (δ / (c + 1)) hη_pos
  refine ⟨N, ?_⟩
  intro k hk
  have hxk := hN k hk
  have hright_nonneg : 0 ≤ δ / (c + 1) :=
    le_of_lt hη_pos
  have hscale_le : c ≤ c + 1 := by
    linarith
  have hmul_bound :
      c * (δ / (c + 1)) ≤ (c + 1) * (δ / (c + 1)) :=
    mul_le_mul_of_nonneg_right hscale_le hright_nonneg
  calc
    |c * x k - c * X| = |c * (x k - X)| := by
        rw [mul_sub]
    _ = |c| * |x k - X| := by
        rw [abs_mul]
    _ = c * |x k - X| := by
        rw [abs_of_nonneg hc]
    _ ≤ c * (δ / (c + 1)) :=
        mul_le_mul_of_nonneg_left hxk hc
    _ ≤ (c + 1) * (δ / (c + 1)) := hmul_bound
    _ = δ := by
        rw [mul_comm, div_mul_cancel₀ δ hscale_pos.ne']

end Sequence
end AppliedModelingLib
