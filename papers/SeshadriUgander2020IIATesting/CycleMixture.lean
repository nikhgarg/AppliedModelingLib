import SeshadriUgander2020IIATesting.Rademacher

/-!
# The cycle-orientation mixture from Lemma 4

For a fixed cycle decomposition, the only random choice in the source
construction is one independent orientation per cycle.  This file isolates
the resulting finite Rademacher calculation.  A cycle of length `l i`
contributes `l i * a i * a' i` to the inner product of two oriented sign
vectors; the bound below is exactly the exponential estimate in Lemma 4.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace CycleMixture

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The inner product of two orientations of an edge-disjoint cycle
decomposition.  The factor `length i` records the number of incidences in
cycle `i`. -/
def orientationInner (length : ι → ℕ) (a a' : ι → Bool) : ℝ :=
  ∑ i, (length i : ℝ) * Rademacher.sign (a i) * Rademacher.sign (a' i)

/-- Source's cycle-dispersion statistic
`α(σ) = (1 / d) * Σᵢ |σᵢ|²`. -/
noncomputable def cycleDispersion (d : ℕ) (length : ι → ℕ) : ℝ :=
  (1 / (d : ℝ)) * ∑ i, (length i : ℝ) ^ 2

/-- The orientation average with an arbitrary scalar in the exponent. -/
theorem orientation_average_exp_le (c : ℝ) (length : ι → ℕ) :
    (1 / (4 : ℝ) ^ Fintype.card ι) *
        (∑ a : ι → Bool, ∑ a' : ι → Bool,
          Real.exp (c * orientationInner length a a')) ≤
      Real.exp ((c ^ 2 / 2) * ∑ i, (length i : ℝ) ^ 2) := by
  have h := Rademacher.orientation_average_exp_le_exp_half_sum_sq
    (fun i => c * (length i : ℝ))
  convert h using 1
  · apply congrArg (fun z => (1 / (4 : ℝ) ^ Fintype.card ι) * z)
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro a' _
    congr 1
    rw [orientationInner, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Lemma 4 in the paper's `N, ε, d, α(σ)` notation. -/
theorem orientation_average_exp_le_source_exponent (N : ℕ) (ε : ℝ)
    (d : ℕ) (hd : 0 < d) (length : ι → ℕ) :
    (1 / (4 : ℝ) ^ Fintype.card ι) *
        (∑ a : ι → Bool, ∑ a' : ι → Bool,
          Real.exp (((N : ℝ) * ε ^ 2 / (d : ℝ)) *
            orientationInner length a a')) ≤
      Real.exp (((N : ℝ) ^ 2 * ε ^ 4 / (2 * (d : ℝ))) *
        cycleDispersion d length) := by
  calc
    (1 / (4 : ℝ) ^ Fintype.card ι) *
        (∑ a : ι → Bool, ∑ a' : ι → Bool,
          Real.exp (((N : ℝ) * ε ^ 2 / (d : ℝ)) *
            orientationInner length a a')) ≤
        Real.exp ((((N : ℝ) * ε ^ 2 / (d : ℝ)) ^ 2 / 2) *
          ∑ i, (length i : ℝ) ^ 2) :=
      orientation_average_exp_le ((N : ℝ) * ε ^ 2 / (d : ℝ)) length
    _ = Real.exp (((N : ℝ) ^ 2 * ε ^ 4 / (2 * (d : ℝ))) *
        cycleDispersion d length) := by
      congr 1
      unfold cycleDispersion
      have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
      field_simp

end CycleMixture

end SeshadriUgander2020IIATesting
