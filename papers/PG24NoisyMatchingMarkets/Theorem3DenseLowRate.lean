import PG24NoisyMatchingMarkets.Theorem3DenseBlockIndex
import Mathlib.Tactic

/-!
# PG24 Theorem 3 dense-branch low-endpoint rate

The low endpoint first controls a maximum over an exact rounded dense block,
then turns that block crossing probability into a one-college tail bound and
uses a finite union bound over the coalition.  This file proves the scalar
rate left by those two finite probability steps.  In particular, the ceiling
in the dense block cardinality remains visible.
-/

open Filter Topology

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
For the beta-only dense-cluster exponent, the full-coalition union-bound
factor times the beta variance rate of one rounded dense block tends to zero.

The expression is exactly the factor that remains after the finite geometric
block-to-single-draw reduction: `(C + 1) * m^(-beta) / m`, where
`m = ceil(C^denseClusterExponent)`.
-/
theorem theorem3DenseCluster_unionBoundRate_tendsto_zero
    {beta : ℝ} (hbeta : 0 < beta) :
    Tendsto
      (fun C : ℕ =>
        (((C + 1 : ℕ) : ℝ) *
          Real.rpow
            (theorem3DenseWindowCount C
              (theorem3DenseClusterExponent beta) : ℝ) (-beta)) /
          (theorem3DenseWindowCount C
            (theorem3DenseClusterExponent beta) : ℝ))
      atTop (nhds 0) := by
  let exponent : ℝ := theorem3DenseClusterExponent beta
  let m : ℕ → ℕ := fun C => theorem3DenseWindowCount C exponent
  have hm_lower : ∀ᶠ C : ℕ in atTop,
      Real.rpow (C : ℝ) exponent ≤ (m C : ℝ) := by
    filter_upwards with C
    exact theorem3DenseWindowCount_real_le C exponent
  have hrate_eq :
      1 + exponent * (-beta - 1) = theorem3DenseHighErrorExponent beta := by
    dsimp only [exponent]
    simp only [theorem3DenseClusterExponent,
      theorem3DenseHighErrorExponent, theorem3DenseWindowExponent,
      theorem3CoalitionScale]
    have hdenom : 1 + beta ≠ 0 := by linarith
    field_simp [hdenom]
    ring
  have hrate_neg : 1 + exponent * (-beta - 1) < 0 := by
    rw [hrate_eq]
    exact theorem3DenseHighErrorExponent_neg hbeta
  have hrate_pos : 0 < -(1 + exponent * (-beta - 1)) := by
    linarith
  have hpower_zero :
      Tendsto
        (fun C : ℕ => 2 * Real.rpow (C : ℝ)
          (1 + exponent * (-beta - 1)))
        atTop (nhds 0) := by
    have hpow : Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ)
          (1 + exponent * (-beta - 1)))
        atTop (nhds 0) :=
      by
        simpa [Function.comp_def] using
          ((tendsto_rpow_neg_atTop hrate_pos).comp
            tendsto_natCast_atTop_atTop)
    simpa using hpow.const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    hpower_zero ?_ ?_
  · filter_upwards with C
    have hm_nonneg : 0 ≤ (m C : ℝ) := Nat.cast_nonneg _
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hm_nonneg _))
      hm_nonneg
  · filter_upwards [hm_lower, eventually_ge_atTop 1] with C hm_lower_C hC_one
    have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
    have hC_real_pos : 0 < (C : ℝ) := by
      exact_mod_cast hC_pos
    have hm_pos : 0 < (m C : ℝ) := by
      have hpow_pos : 0 < Real.rpow (C : ℝ) exponent :=
        Real.rpow_pos_of_pos hC_real_pos _
      exact lt_of_lt_of_le hpow_pos hm_lower_C
    have hneg_exponent : -beta - 1 ≤ 0 := by linarith
    have hinverse_le :
        Real.rpow (m C : ℝ) (-beta - 1) ≤
          Real.rpow (Real.rpow (C : ℝ) exponent) (-beta - 1) :=
      Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hC_real_pos _) hm_lower_C hneg_exponent
    have hsplit_m :
        Real.rpow (m C : ℝ) (-beta - 1) =
          Real.rpow (m C : ℝ) (-beta) / (m C : ℝ) := by
      have hm_one : Real.rpow (m C : ℝ) (1 : ℝ) = (m C : ℝ) :=
        Real.rpow_one _
      calc
        Real.rpow (m C : ℝ) (-beta - 1) =
            Real.rpow (m C : ℝ) ((-beta) - 1) := by ring
        _ = Real.rpow (m C : ℝ) (-beta) /
            Real.rpow (m C : ℝ) (1 : ℝ) :=
          Real.rpow_sub hm_pos (-beta) (1 : ℝ)
        _ = Real.rpow (m C : ℝ) (-beta) / (m C : ℝ) := by
          rw [hm_one]
    have hcompose :
        Real.rpow (Real.rpow (C : ℝ) exponent) (-beta - 1) =
          Real.rpow (C : ℝ) (exponent * (-beta - 1)) := by
      exact (Real.rpow_mul (le_of_lt hC_real_pos)
        exponent (-beta - 1)).symm
    have hC_succ_le : (((C + 1 : ℕ) : ℝ)) ≤ 2 * (C : ℝ) := by
      have hnat : C + 1 ≤ 2 * C := by omega
      exact_mod_cast hnat
    have hright_nonneg :
        0 ≤ Real.rpow (m C : ℝ) (-beta - 1) :=
      Real.rpow_nonneg (le_of_lt hm_pos) _
    have hscaled_le :
        ((C + 1 : ℕ) : ℝ) *
            Real.rpow (m C : ℝ) (-beta - 1) ≤
          (2 * (C : ℝ)) *
            Real.rpow (m C : ℝ) (-beta - 1) :=
      mul_le_mul_of_nonneg_right hC_succ_le hright_nonneg
    calc
      (((C + 1 : ℕ) : ℝ) * Real.rpow (m C : ℝ) (-beta)) /
          (m C : ℝ) =
          ((C + 1 : ℕ) : ℝ) *
            Real.rpow (m C : ℝ) (-beta - 1) := by
              rw [hsplit_m]
              ring
      _ ≤ (2 * (C : ℝ)) *
          Real.rpow (m C : ℝ) (-beta - 1) := hscaled_le
      _ ≤ (2 * (C : ℝ)) *
          Real.rpow (Real.rpow (C : ℝ) exponent) (-beta - 1) :=
        mul_le_mul_of_nonneg_left hinverse_le (by positivity)
      _ = 2 * Real.rpow (C : ℝ)
          (1 + exponent * (-beta - 1)) := by
        rw [hcompose]
        have hC_one_rpow : Real.rpow (C : ℝ) (1 : ℝ) = (C : ℝ) :=
          Real.rpow_one _
        calc
          (2 * (C : ℝ)) *
              Real.rpow (C : ℝ) (exponent * (-beta - 1)) =
            2 * ((C : ℝ) *
              Real.rpow (C : ℝ) (exponent * (-beta - 1))) := by
              ring
          _ = 2 * (Real.rpow (C : ℝ) (1 : ℝ) *
              Real.rpow (C : ℝ) (exponent * (-beta - 1))) := by
              rw [hC_one_rpow]
          _ = 2 * Real.rpow (C : ℝ)
              (1 + exponent * (-beta - 1)) := by
              exact congrArg (fun x : ℝ => 2 * x)
                (Real.rpow_add hC_real_pos (1 : ℝ)
                  (exponent * (-beta - 1))).symm

end

end PG24NoisyMatchingMarkets
