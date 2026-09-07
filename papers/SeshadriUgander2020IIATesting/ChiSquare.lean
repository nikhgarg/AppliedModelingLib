import SeshadriUgander2020IIATesting.FiniteProbability

/-!
# Chi-square calculations for balanced perturbations

Source: Lemma 3.  This file specializes the finite-mixture identity to
`q_{b,ε}` and proves the exact one-observation cross-moment calculation that
leaves only the signed inner product `bᵀb'`.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace ChoiceSystem

variable {F : ChoiceFrame}

/-- View a finite choice system as the finite distribution on its incidence
support used by the product-sample calculations. -/
noncomputable def asFiniteDistribution (q : ChoiceSystem F) :
    FiniteDistribution F.Observation where
  mass := q.mass
  nonneg := q.nonneg
  sum_one := q.sum_one

/-- The signed dot product `bᵀb'` from source Lemma 3. -/
def signInner (b b' : BalancedSign F) : ℝ :=
  ∑ o : F.Observation, b.sign o * b'.sign o

/-- Exact one-observation likelihood-ratio cross moment for two source
perturbations. The individual linear terms vanish by the two sign balances. -/
theorem perturb_crossMoment_uniform (b b' : BalancedSign F) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) :
    FiniteDistribution.crossMoment
      (asFiniteDistribution (perturb b ε hε_nonneg hε_le_one))
      (asFiniteDistribution (perturb b' ε hε_nonneg hε_le_one))
      (asFiniteDistribution (uniform F)) =
        1 + ε ^ 2 / (F.incidenceCount : ℝ) * signInner b b' := by
  have hincidence : (F.incidenceCount : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (ChoiceFrame.incidenceCount_pos F)
  unfold FiniteDistribution.crossMoment asFiniteDistribution
  change ∑ o : F.Observation,
      ((1 + ε * b.sign o) / (F.incidenceCount : ℝ)) *
          ((1 + ε * b'.sign o) / (F.incidenceCount : ℝ)) /
            (1 / (F.incidenceCount : ℝ)) = _
  have hpointwise : ∀ o : F.Observation,
      ((1 + ε * b.sign o) / (F.incidenceCount : ℝ)) *
          ((1 + ε * b'.sign o) / (F.incidenceCount : ℝ)) /
            (1 / (F.incidenceCount : ℝ)) =
          (1 + ε * b.sign o + ε * b'.sign o +
            ε ^ 2 * (b.sign o * b'.sign o)) / (F.incidenceCount : ℝ) := by
    intro o
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun o _ => hpointwise o), ← Finset.sum_div]
  change (∑ o : F.Observation,
    (1 + ε * b.sign o + ε * b'.sign o +
      ε ^ 2 * (b.sign o * b'.sign o))) / (F.incidenceCount : ℝ) = _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ChoiceFrame.observation_card]
  simp_rw [← Finset.mul_sum]
  rw [b.sum_sign_eq_zero, b'.sum_sign_eq_zero]
  unfold signInner
  field_simp
  ring

/-- Source Lemma 3 after substituting the balanced-perturbation cross moment,
but before applying `(1+x)^N ≤ exp(Nx)`. -/
theorem chiSquare_perturb_family_add_one_eq {β : Type} (B : Finset β)
    (hB : B.Nonempty) (b : β → BalancedSign F) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) (N : ℕ) :
    FiniteDistribution.chiSquare
      (FiniteDistribution.mixtureOfProducts B hB
        (fun z => asFiniteDistribution (perturb (b z) ε hε_nonneg hε_le_one)) N)
      (FiniteDistribution.product (asFiniteDistribution (uniform F)) N) + 1 =
      (1 / (B.card : ℝ) ^ 2) * ∑ z ∈ B, ∑ z' ∈ B,
        (1 + ε ^ 2 / (F.incidenceCount : ℝ) * signInner (b z) (b z')) ^ N := by
  rw [FiniteDistribution.chiSquare_mixtureOfProducts_add_one]
  apply congrArg (fun t => (1 / (B.card : ℝ) ^ 2) * t)
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro z' hz'
  rw [perturb_crossMoment_uniform]

theorem one_add_perturb_inner_nonneg (b b' : BalancedSign F) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) :
    0 ≤ 1 + ε ^ 2 / (F.incidenceCount : ℝ) * signInner b b' := by
  rw [← perturb_crossMoment_uniform b b' ε hε_nonneg hε_le_one]
  apply FiniteDistribution.crossMoment_nonneg
  intro o
  exact uniform_mass_pos F o

/-- Source Lemma 3, including its final exponential upper bound. -/
theorem chiSquare_perturb_family_add_one_le {β : Type} (B : Finset β)
    (hB : B.Nonempty) (b : β → BalancedSign F) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) (N : ℕ) :
    FiniteDistribution.chiSquare
      (FiniteDistribution.mixtureOfProducts B hB
        (fun z => asFiniteDistribution (perturb (b z) ε hε_nonneg hε_le_one)) N)
      (FiniteDistribution.product (asFiniteDistribution (uniform F)) N) + 1 ≤
      (1 / (B.card : ℝ) ^ 2) * ∑ z ∈ B, ∑ z' ∈ B,
        Real.exp ((N : ℝ) *
          (ε ^ 2 / (F.incidenceCount : ℝ) * signInner (b z) (b z'))) := by
  rw [chiSquare_perturb_family_add_one_eq B hB b ε hε_nonneg hε_le_one N]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro z hz
    apply Finset.sum_le_sum
    intro z' hz'
    apply FiniteDistribution.one_add_pow_le_exp_nat_mul
    exact one_add_perturb_inner_nonneg (b z) (b z') ε hε_nonneg hε_le_one
  · positivity

end ChoiceSystem

end SeshadriUgander2020IIATesting
