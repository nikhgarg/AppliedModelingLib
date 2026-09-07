import SeshadriUgander2020IIATesting.CycleDecomposition

/-!
# Lemma 4: chi-square control for an oriented cycle decomposition

This combines the exact finite-mixture calculation of Lemma 3 with the
cycle-orientation averaging calculation.  The only combinatorial input is an
explicit `CycleDecomposition` witness, whose edge partition and Eulerian
balance are checked in `CycleDecomposition.lean`.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace ChoiceSystem

variable {F : ChoiceFrame}

namespace CycleDecomposition

variable (D : CycleDecomposition F)

/-- There are `2^|σ|` independent orientations of a decomposition, and the
square of that cardinality is the `4^|σ|` normalization in Lemma 4. -/
theorem orientation_family_card_sq :
    ((Finset.univ : Finset (D.Cycle → Bool)).card : ℝ) ^ 2 =
      (4 : ℝ) ^ Fintype.card D.Cycle := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]

/-- Source Lemmas 3--4 combined: the product-sample mixture over all
independent cycle orientations has chi-square distance bounded by the
paper's `N² ε⁴ α(σ)/(2d)` exponent. -/
theorem chiSquare_oriented_family_add_one_le (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) (N : ℕ) :
    FiniteDistribution.chiSquare
      (FiniteDistribution.mixtureOfProducts (Finset.univ : Finset (D.Cycle → Bool))
        Finset.univ_nonempty
        (fun a => asFiniteDistribution (perturb (D.orientedSign a) ε hε_nonneg hε_le_one)) N)
      (FiniteDistribution.product (asFiniteDistribution (uniform F)) N) + 1 ≤
      Real.exp (((N : ℝ) ^ 2 * ε ^ 4 / (2 * (F.incidenceCount : ℝ))) *
        CycleMixture.cycleDispersion F.incidenceCount D.length) := by
  have hχ := chiSquare_perturb_family_add_one_le
    (F := F) (B := (Finset.univ : Finset (D.Cycle → Bool)))
    Finset.univ_nonempty (fun a => D.orientedSign a) ε hε_nonneg hε_le_one N
  calc
    FiniteDistribution.chiSquare
        (FiniteDistribution.mixtureOfProducts (Finset.univ : Finset (D.Cycle → Bool))
          Finset.univ_nonempty
          (fun a => asFiniteDistribution (perturb (D.orientedSign a) ε hε_nonneg hε_le_one)) N)
        (FiniteDistribution.product (asFiniteDistribution (uniform F)) N) + 1 ≤
        (1 / ((Finset.univ : Finset (D.Cycle → Bool)).card : ℝ) ^ 2) *
          ∑ a : D.Cycle → Bool, ∑ a' : D.Cycle → Bool,
            Real.exp ((N : ℝ) *
              (ε ^ 2 / (F.incidenceCount : ℝ) *
                CycleMixture.orientationInner D.length a a')) := by
      simpa [signInner_orientedSign] using hχ
    _ = (1 / (4 : ℝ) ^ Fintype.card D.Cycle) *
          ∑ a : D.Cycle → Bool, ∑ a' : D.Cycle → Bool,
            Real.exp (((N : ℝ) * ε ^ 2 / (F.incidenceCount : ℝ)) *
              CycleMixture.orientationInner D.length a a') := by
      rw [D.orientation_family_card_sq]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro a' _
      congr 1
      ring
    _ ≤ Real.exp (((N : ℝ) ^ 2 * ε ^ 4 / (2 * (F.incidenceCount : ℝ))) *
        CycleMixture.cycleDispersion F.incidenceCount D.length) :=
      CycleMixture.orientation_average_exp_le_source_exponent N ε F.incidenceCount
        F.incidenceCount_pos D.length

end CycleDecomposition

end ChoiceSystem

end SeshadriUgander2020IIATesting
