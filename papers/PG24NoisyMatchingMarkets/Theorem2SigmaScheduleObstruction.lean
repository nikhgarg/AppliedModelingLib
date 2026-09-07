import PG24NoisyMatchingMarkets.Theorem2QuantifierRepair

/-!
# PG24 Theorem 2 sigma-schedule obstruction

The sigma-existence argument in `source_tex/proof-amplifying.tex:109-145`
selects sigma large enough that

`S < (1 - epsilon) * (1 - exp (-epsilon * (1 - epsilon) * sigma))`.

At supply `S = 1 / 2`, that displayed selection condition itself forces
`epsilon * sigma` to stay away from zero.  Thus it cannot justify the
vanishing independent-product error asserted after `equiv-lt` without a
different quantitative argument.
-/

open Filter Topology

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
The appendix's displayed sigma-selection inequality at `S = 1 / 2` forces a
nonvanishing epsilon-sigma product.  This is a direct formal consequence of
the inequality used in the contradiction proof, not an added premise for the
paper theorem.
-/
theorem theorem2_source_sigma_selection_forces_quarter_product
    {epsilon sigma : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsigma_pos : 0 < sigma)
    (hselection :
      (1 : ℝ) / 2 <
        (1 - epsilon) *
          (1 - Real.exp (-(epsilon * (1 - epsilon) * sigma))) ) :
    (1 : ℝ) / 4 < epsilon * sigma := by
  by_contra hnot
  have hproduct_le : epsilon * sigma ≤ (1 : ℝ) / 4 :=
    le_of_not_gt hnot
  have hfactor_nonneg : 0 ≤ 1 - epsilon := by
    linarith
  have hfactor_le_one : 1 - epsilon ≤ 1 := by
    linarith
  have hproduct_nonneg : 0 ≤ epsilon * sigma :=
    mul_nonneg hepsilon_pos.le hsigma_pos.le
  have hscaled_nonneg : 0 ≤ epsilon * (1 - epsilon) * sigma := by
    rw [show epsilon * (1 - epsilon) * sigma =
      (epsilon * sigma) * (1 - epsilon) by ring]
    exact mul_nonneg hproduct_nonneg hfactor_nonneg
  have hscaled_le_product :
      epsilon * (1 - epsilon) * sigma ≤ epsilon * sigma := by
    rw [show epsilon * (1 - epsilon) * sigma =
      (epsilon * sigma) * (1 - epsilon) by ring]
    calc
      (epsilon * sigma) * (1 - epsilon) ≤ (epsilon * sigma) * 1 :=
        mul_le_mul_of_nonneg_left hfactor_le_one hproduct_nonneg
      _ = epsilon * sigma := by ring
  have hscaled_le_quarter :
      epsilon * (1 - epsilon) * sigma ≤ (1 : ℝ) / 4 :=
    hscaled_le_product.trans hproduct_le
  have hquarter_exp :
      (3 : ℝ) / 4 ≤ Real.exp (-(1 : ℝ) / 4) := by
    have h := Real.add_one_le_exp (-(1 : ℝ) / 4)
    linarith
  have hexp_order :
      Real.exp (-(1 : ℝ) / 4) ≤
        Real.exp (-(epsilon * (1 - epsilon) * sigma)) := by
    apply Real.exp_monotone
    linarith
  have herror_nonneg :
      0 ≤ 1 - Real.exp (-(epsilon * (1 - epsilon) * sigma)) := by
    have hexp_le_one :
        Real.exp (-(epsilon * (1 - epsilon) * sigma)) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have herror_le_quarter :
      1 - Real.exp (-(epsilon * (1 - epsilon) * sigma)) ≤ (1 : ℝ) / 4 := by
    linarith
  have hselection_le_quarter :
      (1 - epsilon) *
          (1 - Real.exp (-(epsilon * (1 - epsilon) * sigma))) ≤
        (1 : ℝ) / 4 := by
    calc
      (1 - epsilon) *
          (1 - Real.exp (-(epsilon * (1 - epsilon) * sigma))) ≤
          1 * (1 - Real.exp (-(epsilon * (1 - epsilon) * sigma))) :=
        mul_le_mul_of_nonneg_right hfactor_le_one herror_nonneg
      _ = 1 - Real.exp (-(epsilon * (1 - epsilon) * sigma)) := by ring
      _ ≤ (1 : ℝ) / 4 := herror_le_quarter
  linarith

/--
No epsilon-sigma schedule satisfying the appendix's displayed sigma-selection
condition at supply `1 / 2` can have product tending to zero.  Consequently,
the existential sigma statement in the source cannot be turned into the
paper's vanishing-error limit by this selection argument alone.
-/
theorem theorem2_source_sigma_selection_product_not_tendsto_zero
    {epsilon sigma : ℕ → ℝ}
    (hepsilon : ∀ᶠ n : ℕ in atTop, 0 < epsilon n ∧ epsilon n ≤ 1)
    (hsigma : ∀ᶠ n : ℕ in atTop, 0 < sigma n)
    (hselection : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 2 <
        (1 - epsilon n) *
          (1 - Real.exp (-(epsilon n * (1 - epsilon n) * sigma n)))) :
    ¬ Tendsto (fun n : ℕ => epsilon n * sigma n) atTop (nhds 0) := by
  intro hproduct
  have hsmall : ∀ᶠ n : ℕ in atTop,
      epsilon n * sigma n < (1 : ℝ) / 4 :=
    hproduct (isOpen_Iio.mem_nhds (by norm_num))
  rcases (hepsilon.and (hsigma.and (hselection.and hsmall))).exists with
    ⟨n, hepsilon_n, hsigma_n, hselection_n, hsmall_n⟩
  have hlower := theorem2_source_sigma_selection_forces_quarter_product
    hepsilon_n.1 hepsilon_n.2 hsigma_n hselection_n
  linarith

/--
The same obstruction applies directly to the independent-product error in
`equiv-lt`: under the appendix's displayed sigma-selection inequality, that
error cannot tend to zero at supply `1 / 2`.
-/
theorem theorem2_source_sigma_selection_exp_error_not_tendsto_zero
    {epsilon sigma : ℕ → ℝ}
    (hepsilon : ∀ᶠ n : ℕ in atTop, 0 < epsilon n ∧ epsilon n ≤ 1)
    (hsigma : ∀ᶠ n : ℕ in atTop, 0 < sigma n)
    (hselection : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 2 <
        (1 - epsilon n) *
          (1 - Real.exp (-(epsilon n * (1 - epsilon n) * sigma n)))) :
    ¬ Tendsto
      (fun n : ℕ => 1 - Real.exp (-(2 * epsilon n * sigma n)))
      atTop (nhds 0) := by
  intro herror
  have hpositive : 0 < 1 - Real.exp (-(1 : ℝ) / 2) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      1 - Real.exp (-(2 * epsilon n * sigma n)) <
        (1 - Real.exp (-(1 : ℝ) / 2)) / 2 :=
    herror (isOpen_Iio.mem_nhds (div_pos hpositive (by norm_num)))
  rcases (hepsilon.and (hsigma.and (hselection.and hsmall))).exists with
    ⟨n, hepsilon_n, hsigma_n, hselection_n, hsmall_n⟩
  have hproduct := theorem2_source_sigma_selection_forces_quarter_product
    hepsilon_n.1 hepsilon_n.2 hsigma_n hselection_n
  have harg : -(1 : ℝ) / 2 > -(2 * epsilon n * sigma n) := by
    nlinarith
  have hexp :
      Real.exp (-(2 * epsilon n * sigma n)) < Real.exp (-(1 : ℝ) / 2) := by
    exact Real.exp_lt_exp.mpr harg
  have hlower :
      1 - Real.exp (-(1 : ℝ) / 2) <
        1 - Real.exp (-(2 * epsilon n * sigma n)) := by
    linarith
  linarith

end

end PG24NoisyMatchingMarkets
