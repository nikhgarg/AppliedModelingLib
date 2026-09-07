import SeshadriUgander2020IIATesting.Separation

/-!
# Elementary finite probability algebra

The paper works entirely with finite supports.  This layer supplies the
product-sample distributions and finite chi-square expression used in Lemmas
3--4, without importing asymptotic probability machinery.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

/-- A real-valued probability mass function on a finite support. -/
structure FiniteDistribution (α : Type) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_one : ∑ x, mass x = 1

namespace FiniteDistribution

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The mass of an ordered independent sample of length `N`. -/
noncomputable def sampleMass (mass : α → ℝ) (N : ℕ) (sample : Fin N → α) : ℝ :=
  ∏ i, mass (sample i)

theorem sampleMass_nonneg (mass : α → ℝ) (hmass_nonneg : ∀ x, 0 ≤ mass x)
    (N : ℕ) (sample : Fin N → α) : 0 ≤ sampleMass mass N sample := by
  unfold sampleMass
  exact Finset.prod_nonneg fun i _ => hmass_nonneg (sample i)

theorem sum_sampleMass (mass : α → ℝ) (hmass_sum_one : ∑ x, mass x = 1)
    (N : ℕ) : ∑ sample : Fin N → α, sampleMass mass N sample = 1 := by
  unfold sampleMass
  calc
    ∑ sample : Fin N → α, ∏ i, mass (sample i) = (∑ x, mass x) ^ N :=
      (Fintype.sum_pow mass N).symm
    _ = 1 := by rw [hmass_sum_one, one_pow]

/-- The `N`-sample product distribution. -/
noncomputable def product (q : FiniteDistribution α) (N : ℕ) :
    FiniteDistribution (Fin N → α) where
  mass := sampleMass q.mass N
  nonneg := sampleMass_nonneg q.mass q.nonneg N
  sum_one := sum_sampleMass q.mass q.sum_one N

theorem product_mass (q : FiniteDistribution α) (N : ℕ) (sample : Fin N → α) :
    (product q N).mass sample = ∏ i, q.mass (sample i) := rfl

theorem product_mass_pos (q : FiniteDistribution α) (hq_pos : ∀ x, 0 < q.mass x)
    (N : ℕ) (sample : Fin N → α) : 0 < (product q N).mass sample := by
  rw [product_mass]
  exact Finset.prod_pos fun i _ => hq_pos (sample i)

/-- Finite total-variation distance. -/
noncomputable def totalVariation (p q : FiniteDistribution α) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |p.mass x - q.mass x|

/-- The finite chi-square expression used in source Section 5. The second
argument is strictly positive wherever the later source lemmas use it. -/
noncomputable def chiSquare (p q : FiniteDistribution α) : ℝ :=
  ∑ x, p.mass x ^ 2 / q.mass x - 1

/-- A uniform mixture over a nonempty finite family of finite distributions.
This is the source's marginal mixture `q̄_ε`: one component is drawn once,
then all `N` observations are drawn from that component. -/
noncomputable def uniformMixture {β : Type} (B : Finset β) (hB : B.Nonempty)
    (q : β → FiniteDistribution α) : FiniteDistribution α where
  mass x := (∑ b ∈ B, (q b).mass x) / (B.card : ℝ)
  nonneg x := by
    apply div_nonneg
    · exact Finset.sum_nonneg fun b hb => (q b).nonneg x
    · positivity
  sum_one := by
    rw [← Finset.sum_div, Finset.sum_comm]
    simp only [FiniteDistribution.sum_one]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (B.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hB
    field_simp

theorem uniformMixture_mass {β : Type} (B : Finset β) (hB : B.Nonempty)
    (q : β → FiniteDistribution α) (x : α) :
    (uniformMixture B hB q).mass x =
      (∑ b ∈ B, (q b).mass x) / (B.card : ℝ) := rfl

/-- The mixture of `N`-sample product distributions, as distinguished from
the product distribution of a one-sample mixture. -/
noncomputable def mixtureOfProducts {β : Type} (B : Finset β) (hB : B.Nonempty)
    (q : β → FiniteDistribution α) (N : ℕ) : FiniteDistribution (Fin N → α) :=
  uniformMixture B hB fun b => product (q b) N

/-- The one-observation likelihood-ratio cross moment appearing in the proof
of source Lemma 3. -/
noncomputable def crossMoment (r s p : FiniteDistribution α) : ℝ :=
  ∑ x, r.mass x * s.mass x / p.mass x

theorem crossMoment_nonneg (r s p : FiniteDistribution α)
    (hp_pos : ∀ x, 0 < p.mass x) : 0 ≤ crossMoment r s p := by
  unfold crossMoment
  apply Finset.sum_nonneg
  intro x hx
  exact div_nonneg (mul_nonneg (r.nonneg x) (s.nonneg x)) (hp_pos x).le

/-- The elementary exponential step in source Lemma 3. -/
theorem one_add_pow_le_exp_nat_mul (x : ℝ) (hx_nonneg : 0 ≤ 1 + x) (N : ℕ) :
    (1 + x) ^ N ≤ Real.exp ((N : ℝ) * x) := by
  calc
    (1 + x) ^ N ≤ (Real.exp x) ^ N :=
      pow_le_pow_left₀ hx_nonneg (by simpa [add_comm] using Real.add_one_le_exp x) N
    _ = Real.exp ((N : ℝ) * x) := (Real.exp_nat_mul x N).symm

/-- Independent samples turn the one-observation cross moment into its `N`th
power. This is the iid factorization in the proof of source Lemma 3. -/
theorem product_crossMoment (r s p : FiniteDistribution α) (N : ℕ) :
    ∑ sample : Fin N → α,
      (product r N).mass sample * (product s N).mass sample /
        (product p N).mass sample = (crossMoment r s p) ^ N := by
  calc
    ∑ sample : Fin N → α,
        (product r N).mass sample * (product s N).mass sample /
          (product p N).mass sample =
        ∑ sample : Fin N → α,
          ∏ i, r.mass (sample i) * s.mass (sample i) / p.mass (sample i) := by
      apply Finset.sum_congr rfl
      intro sample _
      rw [product_mass, product_mass, product_mass, Finset.prod_div_distrib,
        Finset.prod_mul_distrib]
    _ = (crossMoment r s p) ^ N := by
      rw [crossMoment]
      exact (Fintype.sum_pow (fun x => r.mass x * s.mass x / p.mass x) N).symm

/-- Exact finite-mixture identity behind source Lemma 3, before the source
upper-bounds `(1 + x)^N` by an exponential. -/
theorem chiSquare_mixtureOfProducts_add_one {β : Type} (B : Finset β)
    (hB : B.Nonempty) (q : β → FiniteDistribution α) (p : FiniteDistribution α)
    (N : ℕ) :
    chiSquare (mixtureOfProducts B hB q N) (product p N) + 1 =
      (1 / (B.card : ℝ) ^ 2) *
        ∑ b ∈ B, ∑ b' ∈ B, (crossMoment (q b) (q b') p) ^ N := by
  have hpointwise : ∀ sample : Fin N → α,
      ((∑ b ∈ B, (product (q b) N).mass sample) / (B.card : ℝ)) ^ 2 /
          (product p N).mass sample =
        (1 / (B.card : ℝ) ^ 2) *
          ∑ b ∈ B, ∑ b' ∈ B,
            (product (q b) N).mass sample * (product (q b') N).mass sample /
              (product p N).mass sample := by
    intro sample
    rw [pow_two]
    have hsum := Finset.sum_mul_sum B B
      (fun b => (product (q b) N).mass sample)
      (fun b => (product (q b) N).mass sample)
    have hfactor :
        (∑ b ∈ B, ∑ b' ∈ B,
          (product (q b) N).mass sample * (product (q b') N).mass sample *
            ((product p N).mass sample)⁻¹) =
          (∑ b ∈ B, ∑ b' ∈ B,
            (product (q b) N).mass sample * (product (q b') N).mass sample) *
            ((product p N).mass sample)⁻¹ := by
      symm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
    calc
      ((∑ b ∈ B, (product (q b) N).mass sample) / (B.card : ℝ)) *
          ((∑ b ∈ B, (product (q b) N).mass sample) / (B.card : ℝ)) /
            (product p N).mass sample =
          ((∑ b ∈ B, (product (q b) N).mass sample) *
            (∑ b ∈ B, (product (q b) N).mass sample)) *
              ((B.card : ℝ)⁻¹ * (B.card : ℝ)⁻¹ *
                ((product p N).mass sample)⁻¹) := by
            simp only [div_eq_mul_inv]
            ring
      _ = (∑ b ∈ B, ∑ b' ∈ B,
          (product (q b) N).mass sample * (product (q b') N).mass sample) *
            ((B.card : ℝ)⁻¹ * (B.card : ℝ)⁻¹ *
              ((product p N).mass sample)⁻¹) := by rw [hsum]
      _ = (1 / (B.card : ℝ) ^ 2) *
          ∑ b ∈ B, ∑ b' ∈ B,
            (product (q b) N).mass sample * (product (q b') N).mass sample /
              (product p N).mass sample := by
            simp only [div_eq_mul_inv]
            rw [hfactor, ← inv_pow, pow_two]
            ring
  unfold chiSquare
  rw [sub_add_cancel]
  change (∑ sample : Fin N → α,
      ((∑ b ∈ B, (product (q b) N).mass sample) / (B.card : ℝ)) ^ 2 /
        (product p N).mass sample) = _
  rw [Finset.sum_congr rfl (fun sample _ => hpointwise sample), ← Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b' hb'
  exact product_crossMoment (q b) (q b') p N

/-- The centered finite-support form of chi-square divergence.  Strict
positivity of the reference law is exactly what makes every quotient in this
identity well-defined. -/
theorem chiSquare_eq_sum_sq_sub_div (p q : FiniteDistribution α)
    (hq_pos : ∀ x, 0 < q.mass x) :
    chiSquare p q = ∑ x, (p.mass x - q.mass x) ^ 2 / q.mass x := by
  unfold chiSquare
  calc
    (∑ x, p.mass x ^ 2 / q.mass x) - 1 =
        ∑ x, (p.mass x ^ 2 / q.mass x - 2 * p.mass x + q.mass x) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        p.sum_one, q.sum_one]
      ring
    _ = ∑ x, (p.mass x - q.mass x) ^ 2 / q.mass x := by
      apply Finset.sum_congr rfl
      intro x _
      have hq : q.mass x ≠ 0 := (hq_pos x).ne'
      field_simp
      ring

/-- The elementary finite chi-square-to-total-variation inequality used in
the transition from Lemma 4 to Theorem 1. -/
theorem totalVariation_sq_le_chiSquare_div_four (p q : FiniteDistribution α)
    (hq_pos : ∀ x, 0 < q.mass x) :
    (totalVariation p q) ^ 2 ≤ chiSquare p q / 4 := by
  have hcs := Finset.sq_sum_div_le_sum_sq_div (R := ℝ) Finset.univ
    (fun x => |p.mass x - q.mass x|) (g := fun x => q.mass x)
    (fun x _ => hq_pos x)
  have hsum_abs_sq : (∑ x, |p.mass x - q.mass x|) ^ 2 ≤ chiSquare p q := by
    calc
      (∑ x, |p.mass x - q.mass x|) ^ 2 =
          (∑ x, |p.mass x - q.mass x|) ^ 2 / ∑ x, q.mass x := by
        rw [q.sum_one]
        ring
      _ ≤ ∑ x, |p.mass x - q.mass x| ^ 2 / q.mass x := hcs
      _ = ∑ x, (p.mass x - q.mass x) ^ 2 / q.mass x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [sq_abs]
      _ = chiSquare p q := (chiSquare_eq_sum_sq_sub_div p q hq_pos).symm
  calc
    (totalVariation p q) ^ 2 =
        (1 / 4 : ℝ) * (∑ x, |p.mass x - q.mass x|) ^ 2 := by
      unfold totalVariation
      ring
    _ ≤ (1 / 4 : ℝ) * chiSquare p q :=
      mul_le_mul_of_nonneg_left hsum_abs_sq (by norm_num)
    _ = chiSquare p q / 4 := by ring

/-- Square-root form of the finite chi-square-to-TV inequality. -/
theorem totalVariation_le_half_sqrt_chiSquare (p q : FiniteDistribution α)
    (hq_pos : ∀ x, 0 < q.mass x) :
    totalVariation p q ≤ Real.sqrt (chiSquare p q) / 2 := by
  have hsq := totalVariation_sq_le_chiSquare_div_four p q hq_pos
  have hchi : 0 ≤ chiSquare p q := by
    rw [chiSquare_eq_sum_sq_sub_div p q hq_pos]
    exact Finset.sum_nonneg fun x _ => div_nonneg (sq_nonneg _) (hq_pos x).le
  have htv : 0 ≤ totalVariation p q := by
    unfold totalVariation
    positivity
  have hsqrt : (Real.sqrt (chiSquare p q)) ^ 2 = chiSquare p q :=
    Real.sq_sqrt hchi
  nlinarith [Real.sqrt_nonneg (chiSquare p q)]

/-- Any finite event changes in mass by at most total variation.  This is the
finite signed-mass calculation behind Le Cam's testing inequality. -/
theorem abs_sum_sub_mass_le_totalVariation (p q : FiniteDistribution α)
    (A : Finset α) :
    |∑ x ∈ A, (p.mass x - q.mass x)| ≤ totalVariation p q := by
  classical
  let f : α → ℝ := fun x => p.mass x - q.mass x
  let g : α → ℝ := fun x => |f x|
  have htotal : ∑ x, f x = 0 := by
    simp only [f, Finset.sum_sub_distrib, p.sum_one, q.sum_one]
    ring
  have hpart : (∑ x ∈ A, f x) + ∑ x ∈ Aᶜ, f x = 0 := by
    rw [A.sum_add_sum_compl]
    exact htotal
  have habs_part : (∑ x ∈ A, g x) + ∑ x ∈ Aᶜ, g x = ∑ x, g x :=
    A.sum_add_sum_compl g
  have hA_pos : (∑ x ∈ A, f x) ≤ ∑ x ∈ A, g x := by
    apply Finset.sum_le_sum
    intro x hx
    exact le_abs_self _
  have hA_neg : (∑ x ∈ A, -f x) ≤ ∑ x ∈ A, g x := by
    apply Finset.sum_le_sum
    intro x hx
    exact neg_le_abs _
  have hAc_pos : (∑ x ∈ Aᶜ, f x) ≤ ∑ x ∈ Aᶜ, g x := by
    apply Finset.sum_le_sum
    intro x hx
    exact le_abs_self _
  have hAc_neg : (∑ x ∈ Aᶜ, -f x) ≤ ∑ x ∈ Aᶜ, g x := by
    apply Finset.sum_le_sum
    intro x hx
    exact neg_le_abs _
  have hAc_eq : (∑ x ∈ Aᶜ, f x) = -(∑ x ∈ A, f x) := by
    linarith
  have hm_le_Ac : (∑ x ∈ A, f x) ≤ ∑ x ∈ Aᶜ, g x := by
    calc
      (∑ x ∈ A, f x) = ∑ x ∈ Aᶜ, -f x := by
        rw [Finset.sum_neg_distrib, hAc_eq]
        ring
      _ ≤ ∑ x ∈ Aᶜ, g x := hAc_neg
  have hnegm_le_Ac : -(∑ x ∈ A, f x) ≤ ∑ x ∈ Aᶜ, g x := by
    rw [← hAc_eq]
    exact hAc_pos
  have hnegm_le_A : -(∑ x ∈ A, f x) ≤ ∑ x ∈ A, g x := by
    rw [← Finset.sum_neg_distrib]
    exact hA_neg
  unfold totalVariation
  change |∑ x ∈ A, f x| ≤ (1 / 2 : ℝ) * ∑ x, g x
  rw [abs_le]
  constructor <;> linarith

end FiniteDistribution

end SeshadriUgander2020IIATesting
