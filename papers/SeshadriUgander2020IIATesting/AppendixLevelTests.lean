import SeshadriUgander2020IIATesting.Testing

/-!
# Level-`α` testing reformulation

Source: Seshadri--Ugander (2020), Appendix, "Equivalent reformulation with
level α tests."  The source's minimax statement follows from the operational
per-test lower bound by separating Type-I and Type-II errors.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace FiniteDistribution

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Type-I error of a finite binary test under its null distribution. -/
noncomputable def typeIError (p : FiniteDistribution α) (φ : Test α) : ℝ :=
  ∑ x ∈ rejectionSet φ, p.mass x

/-- Type-II error of a finite binary test under one alternative. -/
noncomputable def typeIIError (q : FiniteDistribution α) (φ : Test α) : ℝ :=
  ∑ x ∈ (rejectionSet φ)ᶜ, q.mass x

theorem binaryError_eq_half_typeI_add_half_typeII
    (p q : FiniteDistribution α) (φ : Test α) :
    binaryError p q φ = (1 / 2 : ℝ) * typeIError p φ +
      (1 / 2 : ℝ) * typeIIError q φ := rfl

/-- A lower bound on equal-prior error, together with a level bound, gives a
lower bound on Type-II error. -/
theorem typeIIError_lower_of_binaryError_lower_of_typeI_le
    (p q : FiniteDistribution α) (φ : Test α) (lower level : ℝ)
    (herror : lower ≤ binaryError p q φ)
    (htypeI : typeIError p φ ≤ level) :
    2 * lower - level ≤ typeIIError q φ := by
  rw [binaryError_eq_half_typeI_add_half_typeII] at herror
  linarith

end FiniteDistribution

namespace ChoiceSystem

variable {F : ChoiceFrame}

/-- Operational level-`α` consequence of the paper's product-testing lower
bound: every level-`α` test has a separated alternative with the displayed
Type-II error. -/
theorem exists_typeIIError_ge_of_productTestingLowerBound
    (N : ℕ) (δ lower level : ℝ)
    (hbound : ProductTestingLowerBound (F := F) N δ lower)
    (φ : FiniteDistribution.Test (Fin N → F.Observation))
    (hlevel : FiniteDistribution.typeIError
      (FiniteDistribution.product (asFiniteDistribution (uniform F)) N) φ ≤ level) :
    ∃ q : ChoiceSystem F, SeparatedFromIIA q δ ∧
      2 * lower - level ≤ FiniteDistribution.typeIIError
        (FiniteDistribution.product (asFiniteDistribution q) N) φ := by
  obtain ⟨q, hseparated, herror⟩ := hbound φ
  refine ⟨q, hseparated, ?_⟩
  exact FiniteDistribution.typeIIError_lower_of_binaryError_lower_of_typeI_le
    _ _ φ lower level herror hlevel

namespace CycleDecomposition

variable (D : CycleDecomposition F)

/-- Appendix level-`α` corollary of the source theorem, with the same explicit
small-separation premise needed by the orientation construction. -/
theorem theorem1_levelAlpha_typeII_lower
    (W : D.AlternatingCycleWitness) (δ level : ℝ) (hδ_nonneg : 0 ≤ δ)
    (hsmall : 2 * D.cycleMean * δ ≤ 1) (N : ℕ)
    (φ : FiniteDistribution.Test (Fin N → F.Observation))
    (hlevel : FiniteDistribution.typeIError
      (FiniteDistribution.product (asFiniteDistribution (uniform F)) N) φ ≤ level) :
    ∃ q : ChoiceSystem F, SeparatedFromIIA q δ ∧
      1 - level - (1 / 2 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * D.cycleMean ^ 4 * CycleMixture.cycleDispersion
              F.incidenceCount D.length * (N : ℝ) ^ 2 * δ ^ 4) /
            (F.incidenceCount : ℝ)) - 1) ≤
        FiniteDistribution.typeIIError
          (FiniteDistribution.product (asFiniteDistribution q) N) φ := by
  let lower : ℝ :=
    1 / 2 - (1 / 4 : ℝ) *
      Real.sqrt (Real.exp
        ((8 * D.cycleMean ^ 4 * CycleMixture.cycleDispersion
            F.incidenceCount D.length * (N : ℝ) ^ 2 * δ ^ 4) /
          (F.incidenceCount : ℝ)) - 1)
  obtain ⟨q, hseparated, htypeII⟩ :=
    exists_typeIIError_ge_of_productTestingLowerBound (F := F) N δ lower level
      (by
        simpa [lower] using D.theorem1_productTestingLowerBound W δ hδ_nonneg hsmall N)
      φ hlevel
  refine ⟨q, hseparated, ?_⟩
  dsimp [lower] at htypeII
  linarith

end CycleDecomposition

end ChoiceSystem

end SeshadriUgander2020IIATesting
