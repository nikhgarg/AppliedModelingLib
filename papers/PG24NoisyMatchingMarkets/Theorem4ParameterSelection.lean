import PG24NoisyMatchingMarkets.MainTheorems

/-!
# Theorem 4 Parameter Selection

Elementary parameter choices used by the PG24 Theorem 4 capacity route.
These lemmas make explicit that the static exponential supply gap follows from
the source model's `totalSupply < 1` after selecting a sufficiently large tail
scale; it is not an additional economic assumption.
-/

open Filter Topology

namespace PG24NoisyMatchingMarkets

/--
For every positive split mass and aggregate supply strictly below one, a
positive tail scale makes the split-index exponential crossing target exceed
aggregate supply.
-/
theorem exists_positive_tail_scale_of_totalSupply_lt_one
    {delta totalSupply : ℝ}
    (hdelta_pos : 0 < delta) (htotalSupply_lt_one : totalSupply < 1) :
    ∃ tau : ℝ, 0 < tau ∧
      totalSupply < 1 - Real.exp (-(delta * tau)) := by
  have htarget_pos : 0 < 1 - totalSupply := by
    linarith
  have hmul_atTop :
      Tendsto (fun tau : ℝ => delta * tau) atTop atTop :=
    Tendsto.const_mul_atTop hdelta_pos tendsto_id
  have harg_atBot :
      Tendsto (fun tau : ℝ => -(delta * tau)) atTop atBot := by
    simpa only [Function.comp_apply] using
      (tendsto_neg_atTop_atBot.comp hmul_atTop)
  have hexp_zero :
      Tendsto (fun tau : ℝ => Real.exp (-(delta * tau))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp harg_atBot
  have heventually_small :
      ∀ᶠ tau : ℝ in atTop,
        Real.exp (-(delta * tau)) < 1 - totalSupply :=
    hexp_zero (isOpen_Iio.mem_nhds htarget_pos)
  have hboth :
      ∀ᶠ tau : ℝ in atTop,
        0 < tau ∧ Real.exp (-(delta * tau)) < 1 - totalSupply := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), heventually_small] with
      tau htau_pos hsmall
    exact ⟨htau_pos, hsmall⟩
  rcases hboth.exists with ⟨tau, htau_pos, hsmall⟩
  exact ⟨tau, htau_pos, by linarith⟩

/--
The same parameter choice can be expressed in the slack form used by the
long-tail quantile bridge: `tau = (1 - slack) * sigma`.  Thus a strict
quantile slack below one does not add a separate static-gap assumption.
-/
theorem exists_positive_sigma_tau_of_totalSupply_lt_one
    {delta totalSupply slack : ℝ}
    (hdelta_pos : 0 < delta) (htotalSupply_lt_one : totalSupply < 1)
    (hslack_lt_one : slack < 1) :
    ∃ sigma tau : ℝ,
      0 < sigma ∧ 0 < tau ∧ tau = (1 - slack) * sigma ∧
        totalSupply < 1 - Real.exp (-(delta * tau)) := by
  rcases exists_positive_tail_scale_of_totalSupply_lt_one
    hdelta_pos htotalSupply_lt_one with ⟨tau, htau_pos, hgap⟩
  let sigma : ℝ := tau / (1 - slack)
  have hfactor_pos : 0 < 1 - slack := by
    linarith
  have hsigma_pos : 0 < sigma := by
    exact div_pos htau_pos hfactor_pos
  have htau_eq : tau = (1 - slack) * sigma := by
    dsimp [sigma]
    field_simp [ne_of_gt hfactor_pos]
  exact ⟨sigma, tau, hsigma_pos, htau_pos, htau_eq, hgap⟩

/--
After choosing a positive tail scale, the Theorem 4 endpoint-error parameter
can be chosen positive and at most one.  This separates the large-`sigma`
capacity choice from the small-`epsilon` long-tail approximation choice.
-/
theorem exists_positive_epsilon_le_one_of_exp_error_lt
    {tol sigma : ℝ}
    (htol_pos : 0 < tol) (hsigma_pos : 0 < sigma) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧
        1 - Real.exp (-(2 * epsilon * sigma)) < tol := by
  let epsilon : ℝ := min (tol / (4 * sigma)) (1 / 2)
  have hquot_pos : 0 < tol / (4 * sigma) := by
    positivity
  have hepsilon_pos : 0 < epsilon := by
    exact lt_min hquot_pos (by norm_num)
  have hepsilon_le_one : epsilon ≤ 1 := by
    exact le_trans (min_le_right _ _) (by norm_num)
  have hepsilon_le_quot : epsilon ≤ tol / (4 * sigma) :=
    min_le_left _ _
  have hscaled_le : 2 * epsilon * sigma ≤ tol / 2 := by
    have hmul_le :
        2 * epsilon * sigma ≤ 2 * (tol / (4 * sigma)) * sigma := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hepsilon_le_quot (by norm_num))
          hsigma_pos.le
    have hrewrite : 2 * (tol / (4 * sigma)) * sigma = tol / 2 := by
      field_simp [ne_of_gt hsigma_pos]; ring
    rwa [hrewrite] at hmul_le
  have hscaled_lt : 2 * epsilon * sigma < tol := by
    linarith
  have herror_le :
      1 - Real.exp (-(2 * epsilon * sigma)) ≤ 2 * epsilon * sigma := by
    have h := Real.one_sub_le_exp_neg (2 * epsilon * sigma)
    linarith
  exact ⟨epsilon, hepsilon_pos, hepsilon_le_one,
    lt_of_le_of_lt herror_le hscaled_lt⟩

/--
The capacity and endpoint-error parameters required by the Theorem 4 route
can be selected jointly from the source-level strict supply condition and
strict slack/error tolerances.  This packages only derived choices, not new
model assumptions.
-/
theorem exists_theorem4_capacity_and_error_parameters_of_totalSupply_lt_one
    {delta totalSupply slack tol : ℝ}
    (hdelta_pos : 0 < delta) (htotalSupply_lt_one : totalSupply < 1)
    (hslack_lt_one : slack < 1) (htol_pos : 0 < tol) :
    ∃ sigma tau epsilon : ℝ,
      0 < sigma ∧ 0 < tau ∧ tau = (1 - slack) * sigma ∧
        totalSupply < 1 - Real.exp (-(delta * tau)) ∧
          0 < epsilon ∧ epsilon ≤ 1 ∧
            1 - Real.exp (-(2 * epsilon * sigma)) < tol := by
  rcases exists_positive_sigma_tau_of_totalSupply_lt_one
    hdelta_pos htotalSupply_lt_one hslack_lt_one with
    ⟨sigma, tau, hsigma_pos, htau_pos, htau_eq, hcapacity⟩
  rcases exists_positive_epsilon_le_one_of_exp_error_lt htol_pos hsigma_pos with
    ⟨epsilon, hepsilon_pos, hepsilon_le_one, herror⟩
  exact ⟨sigma, tau, epsilon, hsigma_pos, htau_pos, htau_eq, hcapacity,
    hepsilon_pos, hepsilon_le_one, herror⟩

end PG24NoisyMatchingMarkets
