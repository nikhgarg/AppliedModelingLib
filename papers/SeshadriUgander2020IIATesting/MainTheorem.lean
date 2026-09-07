import SeshadriUgander2020IIATesting.CycleChiSquare

/-!
# Theorem 1's statistical conclusion

The paper obtains a testing-risk lower bound by combining Le Cam's binary
testing inequality, the finite `TV`--chi-square inequality, and Lemmas 3--4.
This file formalizes that combination.  The Le Cam premise is kept explicit:
the subsequent file on finite tests will prove it for the paper's minimax
risk definition, while this module already checks every source-specific
constant and the `ε = 2 μ(σ) δ` substitution.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace FiniteDistribution

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The exact scalar consequence of Le Cam and chi-square control. -/
theorem risk_lower_from_lecam_and_chiSquare (p q : FiniteDistribution α)
    (hq_pos : ∀ x, 0 < q.mass x) (risk exponent : ℝ)
    (hLeCam : 1 / 2 - (1 / 2 : ℝ) * totalVariation p q ≤ risk)
    (hchi : chiSquare p q + 1 ≤ Real.exp exponent) :
    1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp exponent - 1) ≤ risk := by
  have htv := totalVariation_le_half_sqrt_chiSquare p q hq_pos
  have hchi_nonneg : 0 ≤ chiSquare p q := by
    rw [chiSquare_eq_sum_sq_sub_div p q hq_pos]
    exact Finset.sum_nonneg fun x _ => div_nonneg (sq_nonneg _) (hq_pos x).le
  have hchi_le : chiSquare p q ≤ Real.exp exponent - 1 := by linarith
  have hexp_sub_nonneg : 0 ≤ Real.exp exponent - 1 := hchi_nonneg.trans hchi_le
  have hsqrt : Real.sqrt (chiSquare p q) ≤ Real.sqrt (Real.exp exponent - 1) :=
    Real.sqrt_le_sqrt hchi_le
  linarith

end FiniteDistribution

namespace ChoiceSystem

variable {F : ChoiceFrame}

namespace CycleDecomposition

variable (D : CycleDecomposition F)

/-- The sample-product uniform null has strictly positive mass everywhere,
as required by the chi-square-to-TV step. -/
theorem product_uniform_mass_pos (N : ℕ) (sample : Fin N → F.Observation) :
    0 < (FiniteDistribution.product (asFiniteDistribution (uniform F)) N).mass sample := by
  apply FiniteDistribution.product_mass_pos
  intro o
  exact uniform_mass_pos F o

/-- Theorem 1's risk conclusion at an arbitrary valid perturbation size
`ε`, conditional only on the standard Le Cam reduction for the test under
consideration. -/
theorem risk_lower_oriented_cycles (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hε_le_one : ε ≤ 1) (N : ℕ) (risk : ℝ)
    (hLeCam :
      1 / 2 - (1 / 2 : ℝ) * FiniteDistribution.totalVariation
        (FiniteDistribution.mixtureOfProducts (Finset.univ : Finset (D.Cycle → Bool))
          Finset.univ_nonempty
          (fun a => asFiniteDistribution
            (perturb (D.orientedSign a) ε hε_nonneg hε_le_one)) N)
        (FiniteDistribution.product
          (asFiniteDistribution (uniform F)) N) ≤ risk) :
    1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp (((N : ℝ) ^ 2 * ε ^ 4 /
          (2 * (F.incidenceCount : ℝ))) *
          CycleMixture.cycleDispersion F.incidenceCount D.length) - 1) ≤ risk := by
  apply FiniteDistribution.risk_lower_from_lecam_and_chiSquare
    (p := FiniteDistribution.mixtureOfProducts
      (Finset.univ : Finset (D.Cycle → Bool)) Finset.univ_nonempty
      (fun a => asFiniteDistribution
        (perturb (D.orientedSign a) ε hε_nonneg hε_le_one)) N)
    (q := FiniteDistribution.product
      (asFiniteDistribution (uniform F)) N)
  · exact product_uniform_mass_pos (F := F) N
  · exact hLeCam
  · exact D.chiSquare_oriented_family_add_one_le ε hε_nonneg hε_le_one N

/-- Substituting the separation-selected value `ε = 2 μ δ` produces the
`8 μ⁴ α N² δ⁴ / d` exponent printed in Theorem 1. -/
theorem source_exponent_after_epsilon_substitution (μ δ : ℝ) (N : ℕ) :
    ((N : ℝ) ^ 2 * (2 * μ * δ) ^ 4 / (2 * (F.incidenceCount : ℝ))) *
        CycleMixture.cycleDispersion F.incidenceCount D.length =
      (8 * μ ^ 4 * CycleMixture.cycleDispersion F.incidenceCount D.length *
        (N : ℝ) ^ 2 * δ ^ 4) / (F.incidenceCount : ℝ) := by
  have hd : (F.incidenceCount : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt F.incidenceCount_pos
  field_simp
  ring

end CycleDecomposition

end ChoiceSystem

end SeshadriUgander2020IIATesting
