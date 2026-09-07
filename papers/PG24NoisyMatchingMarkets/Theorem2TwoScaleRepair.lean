import PG24NoisyMatchingMarkets.MainTheorems

/-!
# PG24 Theorem 2 two-scale parameter repair

The split fraction used for the small-firm capacity estimate and the endpoint
accuracy used in the long-tail comparison have different quantifier order in
the appendix.  The lemmas below keep those parameters separate: after a
fixed split has produced any finite positive `sigma`, the endpoint error is
chosen smaller than `1 / sigma`.
-/

open Filter Topology

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
For a split schedule `delta` and an arbitrary finite endpoint scale `sigma`,
choose the endpoint error after observing `sigma`.  The absolute value makes
the choice valid without an a priori upper bound on the source witness.
-/
def theorem2_twoScaleEndpointError
    (delta sigma : ℕ → ℝ) (n : ℕ) : ℝ :=
  delta n / (1 + |sigma n|)

/--
After the capacity argument has fixed a positive finite `sigma`, the endpoint
comparison error can be selected separately so that its product with `sigma`
has any prescribed tolerance.  This is the finite two-stage choice used by
the long-tail ratio lemma.
-/
theorem theorem2_exists_endpoint_error_after_scale
    {tol sigma : ℝ}
    (htol_pos : 0 < tol) (hsigma_pos : 0 < sigma) :
    ∃ endpoint : ℝ,
      0 < endpoint ∧ endpoint ≤ 1 ∧
        1 - Real.exp (-(2 * endpoint * sigma)) < tol := by
  let endpoint : ℝ := min (tol / (4 * sigma)) (1 / 2)
  have hquot_pos : 0 < tol / (4 * sigma) := by positivity
  have hendpoint_pos : 0 < endpoint := by
    exact lt_min hquot_pos (by norm_num)
  have hendpoint_le_one : endpoint ≤ 1 := by
    exact le_trans (min_le_right _ _) (by norm_num)
  have hendpoint_le_quot : endpoint ≤ tol / (4 * sigma) :=
    min_le_left _ _
  have hscaled_le : 2 * endpoint * sigma ≤ tol / 2 := by
    have hmul_le :
        2 * endpoint * sigma ≤ 2 * (tol / (4 * sigma)) * sigma := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hendpoint_le_quot (by norm_num))
          hsigma_pos.le
    have hrewrite : 2 * (tol / (4 * sigma)) * sigma = tol / 2 := by
      field_simp [ne_of_gt hsigma_pos]
      ring
    rwa [hrewrite] at hmul_le
  have hscaled_lt : 2 * endpoint * sigma < tol := by linarith
  have hgap_le :
      1 - Real.exp (-(2 * endpoint * sigma)) ≤ 2 * endpoint * sigma := by
    have h := Real.one_sub_le_exp_neg (2 * endpoint * sigma)
    linarith
  exact ⟨endpoint, hendpoint_pos, hendpoint_le_one,
    lt_of_le_of_lt hgap_le hscaled_lt⟩

/--
The small-block capacity contradiction chooses its scale after the split
fraction.  Its strict feasibility condition is `totalSupply < 1 - delta`,
which is available once the split is sufficiently small because the source
model has `totalSupply < 1`.
-/
theorem theorem2_exists_capacity_scale_after_split
    {delta totalSupply : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1)
    (htotalSupply_lt : totalSupply < 1 - delta) :
    ∃ sigma : ℝ, 0 < sigma ∧
      totalSupply <
        (1 - delta) *
          (1 - Real.exp (-(delta * (1 - delta) * sigma))) := by
  have hfactor_pos : 0 < 1 - delta := by linarith
  have hslack_pos : 0 < (1 - delta) - totalSupply := by linarith
  have htarget_pos : 0 < ((1 - delta) - totalSupply) / (1 - delta) :=
    div_pos hslack_pos hfactor_pos
  have harg_atBot : Tendsto (fun tau : ℝ => -tau) atTop atBot :=
    tendsto_neg_atTop_atBot
  have hexp_zero : Tendsto (fun tau : ℝ => Real.exp (-tau)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp harg_atBot
  have hsmall : ∀ᶠ tau : ℝ in atTop,
      Real.exp (-tau) < ((1 - delta) - totalSupply) / (1 - delta) :=
    hexp_zero (isOpen_Iio.mem_nhds htarget_pos)
  have hboth : ∀ᶠ tau : ℝ in atTop,
      0 < tau ∧
        Real.exp (-tau) < ((1 - delta) - totalSupply) / (1 - delta) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall] with
      tau htau_pos hsmall_tau
    exact ⟨htau_pos, hsmall_tau⟩
  rcases hboth.exists with ⟨tau, htau_pos, hsmall_tau⟩
  let sigma : ℝ := tau / (delta * (1 - delta))
  have hdenom_pos : 0 < delta * (1 - delta) :=
    mul_pos hdelta_pos hfactor_pos
  have hsigma_pos : 0 < sigma := by
    exact div_pos htau_pos hdenom_pos
  have hscaled : delta * (1 - delta) * sigma = tau := by
    dsimp [sigma]
    field_simp [ne_of_gt hdenom_pos]
  refine ⟨sigma, hsigma_pos, ?_⟩
  rw [hscaled]
  have hscaled_small :
      (1 - delta) * Real.exp (-tau) < (1 - delta) - totalSupply := by
    calc
      (1 - delta) * Real.exp (-tau) <
          (1 - delta) * (((1 - delta) - totalSupply) / (1 - delta)) :=
        mul_lt_mul_of_pos_left hsmall_tau hfactor_pos
      _ = (1 - delta) - totalSupply := by
        field_simp [ne_of_gt hfactor_pos]
  nlinarith

/--
The two independent choices in the repaired appendix can be made in the
source order: choose a capacity scale from the split, then choose the
long-tail endpoint accuracy after that scale.  No bound on `sigma` is assumed.
-/
theorem theorem2_exists_twoScale_capacity_endpoint_parameters
    {delta totalSupply tol : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1)
    (htotalSupply_lt : totalSupply < 1 - delta) (htol_pos : 0 < tol) :
    ∃ sigma endpoint : ℝ,
      0 < sigma ∧
      totalSupply <
        (1 - delta) *
          (1 - Real.exp (-(delta * (1 - delta) * sigma))) ∧
      0 < endpoint ∧ endpoint ≤ 1 ∧
        1 - Real.exp (-(2 * endpoint * sigma)) < tol := by
  rcases theorem2_exists_capacity_scale_after_split
      hdelta_pos hdelta_lt_one htotalSupply_lt with
    ⟨sigma, hsigma_pos, hcapacity⟩
  rcases theorem2_exists_endpoint_error_after_scale htol_pos hsigma_pos with
    ⟨endpoint, hendpoint_pos, hendpoint_le_one, hgap⟩
  exact ⟨sigma, endpoint, hsigma_pos, hcapacity,
    hendpoint_pos, hendpoint_le_one, hgap⟩

theorem theorem2_twoScaleEndpointError_nonneg
    {delta sigma : ℕ → ℝ} {n : ℕ}
    (hdelta : 0 ≤ delta n) :
    0 ≤ theorem2_twoScaleEndpointError delta sigma n := by
  unfold theorem2_twoScaleEndpointError
  exact div_nonneg hdelta (by positivity)

theorem theorem2_twoScaleEndpointError_le_split
    {delta sigma : ℕ → ℝ} {n : ℕ}
    (hdelta : 0 ≤ delta n) :
    theorem2_twoScaleEndpointError delta sigma n ≤ delta n := by
  unfold theorem2_twoScaleEndpointError
  have hdenom : 1 ≤ 1 + |sigma n| := by
    linarith [abs_nonneg (sigma n)]
  calc
    delta n / (1 + |sigma n|) ≤ delta n / 1 :=
      div_le_div_of_nonneg_left hdelta (by norm_num) hdenom
    _ = delta n := by ring

theorem theorem2_twoScaleEndpointError_tendsto_zero
    {delta sigma : ℕ → ℝ}
    (hdelta_nonneg : ∀ n, 0 ≤ delta n)
    (hdelta_zero : Tendsto delta atTop (nhds 0)) :
    Tendsto (theorem2_twoScaleEndpointError delta sigma) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ hdelta_zero
  · filter_upwards with n
    exact theorem2_twoScaleEndpointError_nonneg (hdelta_nonneg n)
  · filter_upwards with n
    exact theorem2_twoScaleEndpointError_le_split (hdelta_nonneg n)

theorem theorem2_twoScaleEndpointError_mul_scale_le_split
    {delta sigma : ℕ → ℝ} {n : ℕ}
    (hdelta : 0 ≤ delta n) (hsigma : 0 ≤ sigma n) :
    theorem2_twoScaleEndpointError delta sigma n * sigma n ≤ delta n := by
  unfold theorem2_twoScaleEndpointError
  have hdenom_pos : 0 < 1 + |sigma n| := by positivity
  have hsigma_le : sigma n ≤ 1 + |sigma n| := by
    calc
      sigma n ≤ |sigma n| := le_abs_self _
      _ ≤ 1 + |sigma n| := by linarith
  have hratio_le_one : sigma n / (1 + |sigma n|) ≤ 1 :=
    (div_le_one hdenom_pos).mpr hsigma_le
  calc
    (delta n / (1 + |sigma n|)) * sigma n =
        delta n * (sigma n / (1 + |sigma n|)) := by ring
    _ ≤ delta n * 1 :=
      mul_le_mul_of_nonneg_left hratio_le_one hdelta
    _ = delta n := by ring

theorem theorem2_twoScaleEndpointError_mul_scale_tendsto_zero
    {delta sigma : ℕ → ℝ}
    (hdelta_nonneg : ∀ n, 0 ≤ delta n)
    (hsigma_nonneg : ∀ n, 0 ≤ sigma n)
    (hdelta_zero : Tendsto delta atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ => theorem2_twoScaleEndpointError delta sigma n * sigma n)
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ hdelta_zero
  · filter_upwards with n
    exact mul_nonneg
      (theorem2_twoScaleEndpointError_nonneg (hdelta_nonneg n))
      (hsigma_nonneg n)
  · filter_upwards with n
    exact theorem2_twoScaleEndpointError_mul_scale_le_split
      (hdelta_nonneg n) (hsigma_nonneg n)

/-- The two-scale endpoint choice makes the independent-product error vanish. -/
theorem theorem2_twoScale_exp_gap_tendsto_zero
    {delta sigma : ℕ → ℝ}
    (hdelta_nonneg : ∀ n, 0 ≤ delta n)
    (hsigma_nonneg : ∀ n, 0 ≤ sigma n)
    (hdelta_zero : Tendsto delta atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ =>
        1 - Real.exp
          (-(2 * theorem2_twoScaleEndpointError delta sigma n * sigma n)))
      atTop (nhds 0) := by
  have hproduct := theorem2_twoScaleEndpointError_mul_scale_tendsto_zero
    hdelta_nonneg hsigma_nonneg hdelta_zero
  have harg : Tendsto
      (fun n : ℕ =>
        -(2 * theorem2_twoScaleEndpointError delta sigma n * sigma n))
      atTop (nhds 0) := by
    have hbase :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2)).mul
        hproduct
    simpa [mul_assoc] using hbase.neg
  have hexp : Tendsto
      (fun n : ℕ =>
        Real.exp
          (-(2 * theorem2_twoScaleEndpointError delta sigma n * sigma n)))
      atTop (nhds 1) := by
    simpa [Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp harg
  simpa using (tendsto_const_nhds.sub hexp : Tendsto
    (fun n : ℕ => (1 : ℝ) -
      Real.exp
        (-(2 * theorem2_twoScaleEndpointError delta sigma n * sigma n)))
    atTop (nhds ((1 : ℝ) - 1)))

/--
The lower source-window error after separating the split fraction `delta`
from the long-tail comparison error `endpoint`.  This is the expression in
`proof-amplifying.tex:58-78`: only the independent-product term uses the
post-`sigma` endpoint parameter.
-/
noncomputable def theorem2_twoScaleLowerError
    (alpha delta endpoint sigma : ℝ) : ℝ :=
  (1 + alpha) * delta +
    (1 - Real.exp (-(2 * endpoint * sigma)))

/--
The upper source-window error with the same two-scale separation.  The small
firm term still depends on the split fraction through `sqrt delta`.
-/
noncomputable def theorem2_twoScaleUpperError
    (totalSupply alpha delta endpoint sigma : ℝ) : ℝ :=
  delta + (1 - Real.exp (-(2 * endpoint * sigma))) +
    alpha * Real.sqrt delta /
      (1 - totalSupply - delta -
        (1 - Real.exp (-(2 * endpoint * sigma))))

theorem theorem2_twoScaleLowerError_tendsto_zero
    {delta sigma : ℕ → ℝ} (alpha : ℝ)
    (hdelta_nonneg : ∀ n, 0 ≤ delta n)
    (hsigma_nonneg : ∀ n, 0 ≤ sigma n)
    (hdelta_zero : Tendsto delta atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ =>
        theorem2_twoScaleLowerError alpha (delta n)
          (theorem2_twoScaleEndpointError delta sigma n) (sigma n))
      atTop (nhds 0) := by
  have hgap := theorem2_twoScale_exp_gap_tendsto_zero
    hdelta_nonneg hsigma_nonneg hdelta_zero
  have hlinear : Tendsto
      (fun n : ℕ => (1 + alpha) * delta n) atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul hdelta_zero : Tendsto
        (fun n : ℕ => (1 + alpha) * delta n)
        atTop (nhds ((1 + alpha) * 0)))
  simpa [theorem2_twoScaleLowerError, mul_assoc] using hlinear.add hgap

theorem theorem2_twoScaleUpperDenominator_tendsto
    {delta sigma : ℕ → ℝ} (totalSupply : ℝ)
    (hdelta_nonneg : ∀ n, 0 ≤ delta n)
    (hsigma_nonneg : ∀ n, 0 ≤ sigma n)
    (hdelta_zero : Tendsto delta atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ =>
        1 - totalSupply - delta n -
          (1 - Real.exp
            (-(2 * theorem2_twoScaleEndpointError delta sigma n * sigma n))))
      atTop (nhds (1 - totalSupply)) := by
  have hgap := theorem2_twoScale_exp_gap_tendsto_zero
    hdelta_nonneg hsigma_nonneg hdelta_zero
  have hbase : Tendsto
      (fun n : ℕ => 1 - totalSupply - delta n)
      atTop (nhds (1 - totalSupply)) := by
    simpa using
      (tendsto_const_nhds.sub hdelta_zero : Tendsto
        (fun n : ℕ => (1 - totalSupply) - delta n)
        atTop (nhds ((1 - totalSupply) - 0)))
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc] using
    hbase.sub hgap

theorem theorem2_twoScaleUpperError_tendsto_zero
    {totalSupply alpha : ℝ} {delta sigma : ℕ → ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hdelta_nonneg : ∀ n, 0 ≤ delta n)
    (hsigma_nonneg : ∀ n, 0 ≤ sigma n)
    (hdelta_zero : Tendsto delta atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ =>
        theorem2_twoScaleUpperError totalSupply alpha (delta n)
          (theorem2_twoScaleEndpointError delta sigma n) (sigma n))
      atTop (nhds 0) := by
  have hgap := theorem2_twoScale_exp_gap_tendsto_zero
    hdelta_nonneg hsigma_nonneg hdelta_zero
  have hsqrt : Tendsto
      (fun n : ℕ => Real.sqrt (delta n)) atTop (nhds 0) := by
    simpa [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hdelta_zero
  have hnum : Tendsto
      (fun n : ℕ => alpha * Real.sqrt (delta n)) atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul hsqrt : Tendsto
        (fun n : ℕ => alpha * Real.sqrt (delta n))
        atTop (nhds (alpha * 0)))
  have hden := theorem2_twoScaleUpperDenominator_tendsto totalSupply
    hdelta_nonneg hsigma_nonneg hdelta_zero
  have hden_ne : 1 - totalSupply ≠ 0 := by linarith
  have hquot : Tendsto
      (fun n : ℕ =>
        alpha * Real.sqrt (delta n) /
          (1 - totalSupply - delta n -
            (1 - Real.exp
              (-(2 * theorem2_twoScaleEndpointError delta sigma n * sigma n)))))
      atTop (nhds 0) := by
    simpa using
      (hnum.div hden hden_ne : Tendsto
        (fun n : ℕ =>
          alpha * Real.sqrt (delta n) /
            (1 - totalSupply - delta n -
              (1 - Real.exp
                (-(2 * theorem2_twoScaleEndpointError delta sigma n * sigma n)))))
        atTop (nhds (0 / (1 - totalSupply))))
  simpa [theorem2_twoScaleUpperError, add_assoc, mul_assoc] using
    (hdelta_zero.add hgap).add hquot

end

end PG24NoisyMatchingMarkets
