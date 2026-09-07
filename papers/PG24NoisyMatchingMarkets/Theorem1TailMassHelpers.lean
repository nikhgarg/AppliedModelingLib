import Mathlib.Tactic

/-!
# PG24 Theorem 1 tail-mass exponent helpers

This module records the exponent arithmetic used in the PG24 Theorem 1
attenuation proof (`source_tex/proof-attenuating.tex`, Proposition `thm1v2`).
It is intentionally semantic: the declarations are about the source constants
and rate identities, not about names of existing theorem wrappers.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

open Filter

/-- Denominator shared by the PG24 Theorem 1 source exponents. -/
def theorem1TailDenom (β γ : ℝ) : ℝ :=
  3 * β * γ + 2 * β + 5 * γ + 6

/-- Source polynomial rate `K(β, γ)` from Proposition `thm1v2`. -/
def theorem1TailK (β γ : ℝ) : ℝ :=
  (2 * β * γ) / theorem1TailDenom β γ

/-- Source exponent `phi_1`, used for the cutoff-window width. -/
def theorem1TailPhi1 (β γ : ℝ) : ℝ :=
  -(2 * β) / theorem1TailDenom β γ

/-- Source exponent `phi_2`, used for the dense-cluster size. -/
def theorem1TailPhi2 (β γ : ℝ) : ℝ :=
  (5 * γ + 6) / theorem1TailDenom β γ

/-- Source exponent `phi_3`, used for the early-cutoff split. -/
def theorem1TailPhi3 (β γ : ℝ) : ℝ :=
  1 - (2 * β * γ) / theorem1TailDenom β γ

/-- Source exponent `phi_4`, used in the large-gap case. -/
def theorem1TailPhi4 (β γ : ℝ) : ℝ :=
  -β / 2 + (β * γ) / theorem1TailDenom β γ

theorem theorem1TailDenom_pos {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) :
    0 < theorem1TailDenom β γ := by
  unfold theorem1TailDenom
  nlinarith [mul_pos hβ hγ]

theorem theorem1TailK_pos {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) :
    0 < theorem1TailK β γ := by
  unfold theorem1TailK
  have hnum : 0 < 2 * β * γ := by
    nlinarith [mul_pos hβ hγ]
  exact div_pos hnum (theorem1TailDenom_pos hβ hγ)

/-- The PG24 polynomial scale `(N+1 : R)` tends to infinity. -/
theorem theorem1Tail_nat_succ_cast_tendsto_atTop :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

/--
A uniform negative-power upper bound is eventually below every positive
tolerance.  This is the analytic step used after the source proof supplies an
`O(C^{-rate})` tail-mass estimate.
-/
theorem theorem1Tail_eventually_forall_lt_of_uniform_rpow_neg_bound
    {α : ℕ → Type*} {f : ∀ N : ℕ, α N → ℝ}
    {A rate : ℝ} {N0 : ℕ}
    (hrate : 0 < rate)
    (hbound :
      ∀ N : ℕ, N0 ≤ N →
        ∀ a : α N,
          f N a ≤ A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-rate)) :
    ∀ tol : ℝ, 0 < tol →
      ∀ᶠ N : ℕ in atTop, ∀ a : α N, f N a < tol := by
  intro tol htol
  have hpow :
      Tendsto
        (fun N : ℕ => Real.rpow (((N + 1 : ℕ) : ℝ)) (-rate))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hrate).comp
      theorem1Tail_nat_succ_cast_tendsto_atTop
  have hupper_zero :
      Tendsto
        (fun N : ℕ => A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-rate))
        atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow : Tendsto
      (fun N : ℕ => A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-rate))
      atTop (nhds (A * 0)))
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-rate) < tol :=
    hupper_zero (isOpen_Iio.mem_nhds htol)
  filter_upwards [eventually_ge_atTop N0, hsmall] with N hN hsmallN a
  exact lt_of_le_of_lt (hbound N hN a) hsmallN

/--
Specialization of the uniform negative-power bridge to the source rate
`K(β, γ)`.
-/
theorem theorem1Tail_eventually_forall_lt_of_uniform_K_bound
    {α : ℕ → Type*} {f : ∀ N : ℕ, α N → ℝ}
    {A β γ : ℝ} {N0 : ℕ}
    (hβ : 0 < β) (hγ : 0 < γ)
    (hbound :
      ∀ N : ℕ, N0 ≤ N →
        ∀ a : α N,
          f N a ≤
            A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-(theorem1TailK β γ))) :
    ∀ tol : ℝ, 0 < tol →
      ∀ᶠ N : ℕ in atTop, ∀ a : α N, f N a < tol :=
  theorem1Tail_eventually_forall_lt_of_uniform_rpow_neg_bound
    (hrate := theorem1TailK_pos hβ hγ) hbound

theorem theorem1TailPhi1_neg {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) :
    theorem1TailPhi1 β γ < 0 := by
  unfold theorem1TailPhi1
  have hnum : -(2 * β) < 0 := by
    nlinarith
  exact div_neg_of_neg_of_pos hnum (theorem1TailDenom_pos hβ hγ)

theorem theorem1TailPhi2_pos {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) :
    0 < theorem1TailPhi2 β γ := by
  unfold theorem1TailPhi2
  have hnum : 0 < 5 * γ + 6 := by
    nlinarith
  exact div_pos hnum (theorem1TailDenom_pos hβ hγ)

theorem theorem1TailPhi2_lt_one {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) :
    theorem1TailPhi2 β γ < 1 := by
  have hden_pos := theorem1TailDenom_pos hβ hγ
  have hnum_lt : 5 * γ + 6 < theorem1TailDenom β γ := by
    unfold theorem1TailDenom
    nlinarith [mul_pos hβ hγ]
  have hlt := div_lt_div_of_pos_right hnum_lt hden_pos
  have hden_ne : theorem1TailDenom β γ ≠ 0 := ne_of_gt hden_pos
  simpa [theorem1TailPhi2, hden_ne] using hlt

theorem theorem1Tail_one_sub_phi2_pos {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) :
    0 < 1 - theorem1TailPhi2 β γ := by
  nlinarith [theorem1TailPhi2_lt_one hβ hγ]

theorem theorem1TailPhi3_sub_one_eq_neg_K (β γ : ℝ) :
    theorem1TailPhi3 β γ - 1 = -theorem1TailK β γ := by
  unfold theorem1TailPhi3 theorem1TailK
  ring

theorem theorem1Tail_one_sub_phi3_eq_K (β γ : ℝ) :
    1 - theorem1TailPhi3 β γ = theorem1TailK β γ := by
  unfold theorem1TailPhi3 theorem1TailK
  ring

theorem theorem1Tail_gamma_mul_phi1_eq_neg_K (β γ : ℝ) :
    γ * theorem1TailPhi1 β γ = -theorem1TailK β γ := by
  unfold theorem1TailPhi1 theorem1TailK
  ring

theorem theorem1Tail_case1_chebyshev_exp_eq_neg_K {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) :
    1 - 2 * theorem1TailPhi1 β γ -
        (1 + β) * theorem1TailPhi2 β γ =
      -theorem1TailK β γ := by
  have hden_ne : theorem1TailDenom β γ ≠ 0 :=
    ne_of_gt (theorem1TailDenom_pos hβ hγ)
  unfold theorem1TailPhi1 theorem1TailPhi2 theorem1TailK
  field_simp [hden_ne]
  unfold theorem1TailDenom
  ring

theorem theorem1Tail_case1_interval_exp_eq_neg_K (β γ : ℝ) :
    γ * theorem1TailPhi1 β γ = -theorem1TailK β γ :=
  theorem1Tail_gamma_mul_phi1_eq_neg_K β γ

theorem theorem1Tail_case1_capacity_exp_eq_neg_K (β γ : ℝ) :
    theorem1TailPhi3 β γ - 1 = -theorem1TailK β γ :=
  theorem1TailPhi3_sub_one_eq_neg_K β γ

theorem theorem1Tail_phi1_add_phi3_sub_phi2_eq_beta_gamma_div {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) :
    theorem1TailPhi1 β γ + theorem1TailPhi3 β γ -
        theorem1TailPhi2 β γ =
      (β * γ) / theorem1TailDenom β γ := by
  have hden_ne : theorem1TailDenom β γ ≠ 0 :=
    ne_of_gt (theorem1TailDenom_pos hβ hγ)
  unfold theorem1TailPhi1 theorem1TailPhi2 theorem1TailPhi3
  field_simp [hden_ne]
  unfold theorem1TailDenom
  ring

theorem theorem1TailPhi4_lt_gap_exp {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) :
    theorem1TailPhi4 β γ <
      theorem1TailPhi1 β γ + theorem1TailPhi3 β γ -
        theorem1TailPhi2 β γ := by
  rw [theorem1Tail_phi1_add_phi3_sub_phi2_eq_beta_gamma_div hβ hγ]
  unfold theorem1TailPhi4
  nlinarith

theorem theorem1Tail_beta_add_two_phi4_eq_K (β γ : ℝ) :
    β + 2 * theorem1TailPhi4 β γ = theorem1TailK β γ := by
  unfold theorem1TailPhi4 theorem1TailK theorem1TailDenom
  ring

theorem theorem1Tail_case2_chebyshev_exp_eq_neg_K (β γ : ℝ) :
    -β - 2 * theorem1TailPhi4 β γ = -theorem1TailK β γ := by
  have h := theorem1Tail_beta_add_two_phi4_eq_K β γ
  linarith

theorem theorem1Tail_case2_gap_exp_eq_neg_K {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) :
    -2 * theorem1TailPhi1 β γ - 2 * theorem1TailPhi3 β γ +
        2 * theorem1TailPhi2 β γ =
      -theorem1TailK β γ := by
  have hden_ne : theorem1TailDenom β γ ≠ 0 :=
    ne_of_gt (theorem1TailDenom_pos hβ hγ)
  unfold theorem1TailPhi1 theorem1TailPhi2 theorem1TailPhi3 theorem1TailK
  field_simp [hden_ne]
  unfold theorem1TailDenom
  ring

/--
Bundled identities for the dense-interval case in the source proof:
capacity mass, Chebyshev/union-bound error, and Holder interval mass all have
the same exponent `-K`.
-/
theorem theorem1Tail_case1_source_exponents {β γ : ℝ} (hβ : 0 < β)
    (hγ : 0 < γ) :
    theorem1TailPhi3 β γ - 1 = -theorem1TailK β γ ∧
    1 - 2 * theorem1TailPhi1 β γ -
        (1 + β) * theorem1TailPhi2 β γ =
      -theorem1TailK β γ ∧
    γ * theorem1TailPhi1 β γ = -theorem1TailK β γ :=
  ⟨theorem1Tail_case1_capacity_exp_eq_neg_K β γ,
    theorem1Tail_case1_chebyshev_exp_eq_neg_K hβ hγ,
    theorem1Tail_case1_interval_exp_eq_neg_K β γ⟩

/--
Bundled identities for the large-gap case in the source proof: the Chebyshev
tail and high-match gap terms both have exponent `-K`.
-/
theorem theorem1Tail_case2_source_exponents {β γ : ℝ} (hβ : 0 < β)
    (hγ : 0 < γ) :
    -β - 2 * theorem1TailPhi4 β γ = -theorem1TailK β γ ∧
    -2 * theorem1TailPhi1 β γ - 2 * theorem1TailPhi3 β γ +
        2 * theorem1TailPhi2 β γ =
      -theorem1TailK β γ :=
  ⟨theorem1Tail_case2_chebyshev_exp_eq_neg_K β γ,
    theorem1Tail_case2_gap_exp_eq_neg_K hβ hγ⟩

end

end PG24NoisyMatchingMarkets
