import PRPKG24AccuracyDiversity.SeparableAsymptotic
import PRPKG24AccuracyDiversity.FiniteDiscreteOrderStats
import AppliedModelingLib.Foundations.Probability.Exponential

namespace PRPKG24AccuracyDiversity

open scoped BigOperators

/--
Real harmonic numbers, indexed so `harmonicReal q = ∑_{j=1}^q 1 / j`.

For a rate-`lambda` exponential distribution, the expected maximum of `q`
i.i.d. draws is `harmonicReal q / lambda`; this file formalizes the exact
top-one oracle used by the exponential branch of Theorem 1.
-/
noncomputable def harmonicReal (q : ℕ) : ℝ := AppliedModelingLib.Probability.Exponential.harmonicReal q

theorem harmonicReal_zero : harmonicReal 0 = 0 := by
  simpa [harmonicReal] using
    AppliedModelingLib.Probability.Exponential.harmonicReal_zero

theorem harmonicReal_succ (q : ℕ) :
    harmonicReal (q + 1) = harmonicReal q + (1 : ℝ) / ((q + 1 : ℕ) : ℝ) := by
  simpa [harmonicReal] using
    AppliedModelingLib.Probability.Exponential.harmonicReal_succ q

theorem harmonicReal_eq_harmonic (q : ℕ) :
    harmonicReal q = (harmonic q : ℝ) := by
  simpa [harmonicReal] using
    AppliedModelingLib.Probability.Exponential.harmonicReal_eq_harmonic q

/--
Analytic survival function for the maximum of `q` rate-`lambda` exponential
draws, after substituting the exponential CDF on the nonnegative line.
-/
noncomputable def exponentialMaxSurvival
    (lambda : ℝ) (q : ℕ) (x : ℝ) : ℝ := AppliedModelingLib.Probability.Exponential.maxSurvivalOfRate lambda q x

theorem exponentialMaxSurvival_eq_formula
    (lambda : ℝ) (q : ℕ) (x : ℝ) :
    exponentialMaxSurvival lambda q x =
      1 - (1 - Real.exp (-(lambda * x))) ^ q := rfl

/--
Binomial expansion of the exponential maximum survival function into finitely
many exponential-tail terms.
-/
theorem exponentialMaxSurvival_expansion
    (lambda : ℝ) (q : ℕ) (x : ℝ) :
    exponentialMaxSurvival lambda q x =
      - ∑ m ∈ Finset.range q,
          (-1 : ℝ) ^ (m + q) *
            (Real.exp (-(lambda * x))) ^ (q - m) *
            (q.choose m : ℝ) := by
  simpa [exponentialMaxSurvival] using
    AppliedModelingLib.Probability.Exponential.maxSurvivalOfRate_expansion
      lambda q x

theorem exponentialMaxSurvival_one
    (lambda x : ℝ) :
    exponentialMaxSurvival lambda 1 x =
      Real.exp (-(lambda * x)) := by
  simpa [exponentialMaxSurvival] using
    AppliedModelingLib.Probability.Exponential.maxSurvivalOfRate_one
      lambda x

/--
Termwise integral for the positive powers appearing in the exponential maximum
survival expansion.
-/
theorem exponentialSurvivalPower_integral
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {n : ℕ} (hn : 0 < n) :
    ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-(lambda * x))) ^ n =
      1 / ((n : ℝ) * lambda) :=
  AppliedModelingLib.Probability.Exponential.integral_exp_neg_mul_pow_Ioi
    lambda hlambda_pos hn

/--
All-`q` survival-integral reduction for the exponential maximum formula.  The
right side is the finite alternating binomial sum that remains to identify with
`H_q/lambda`.
-/
theorem exponentialMaxSurvival_integral_eq_finite_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (q : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), exponentialMaxSurvival lambda q x =
      - ∑ m ∈ Finset.range q,
          ((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
            (1 / (((q - m : ℕ) : ℝ) * lambda)) := by
  simpa [exponentialMaxSurvival] using
    AppliedModelingLib.Probability.Exponential.maxSurvivalOfRate_integral_eq_finite_sum
      lambda hlambda_pos q

/--
The finite alternating binomial sum produced by the survival-integral expansion
collapses to the harmonic expected-maximum value `H_q/lambda`.
-/
theorem exponentialMaxSurvival_finite_sum_eq_harmonicValue
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (q : ℕ) :
    - ∑ m ∈ Finset.range q,
        ((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
          (1 / (((q - m : ℕ) : ℝ) * lambda)) =
      AppliedModelingLib.Probability.Exponential.expectedMaxValueOfRate lambda q :=
  AppliedModelingLib.Probability.Exponential.maxSurvivalOfRate_finite_sum_eq_expectedMaxValueOfRate
    lambda hlambda_pos q

/--
All-`q` analytic maximum-survival integral for the exponential distribution:
integrating `1 - (1 - exp (-lambda*x))^q` over the nonnegative line gives the
exact harmonic value `H_q/lambda`.
-/
theorem exponentialMaxSurvival_integral_eq_harmonicValue
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (q : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), exponentialMaxSurvival lambda q x =
      AppliedModelingLib.Probability.Exponential.expectedMaxValueOfRate lambda q := by
  simpa [exponentialMaxSurvival] using
    AppliedModelingLib.Probability.Exponential.maxSurvivalOfRate_integral_eq_expectedMaxValueOfRate
      lambda hlambda_pos q

/-- Positive-rate exponential model used by the top-one harmonic checkpoint. -/
def exponentialDistributionModel
    (lambda : ℝ) (hlambda_pos : 0 < lambda) :
    AppliedModelingLib.Probability.Exponential.Model where
  rate := lambda
  rate_pos := hlambda_pos

/--
Product-measure maximum survival for `q` iid rate-`lambda` exponential draws.
For `x >= 0`, the finite maximum survival is the analytic expression
`1 - (1 - exp (-lambda*x))^q`.
-/
theorem exponentialProductMaxSurvival_eq_formula
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] {x : ℝ} (hx : 0 ≤ x) :
    1 - (((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
        {sample : Fin q → ℝ |
          AppliedModelingLib.Probability.Exponential.finiteSampleMax sample ≤ x}).toReal =
      exponentialMaxSurvival lambda q x := by
  let M := exponentialDistributionModel lambda hlambda_pos
  have h := M.iidMaxSurvival_eq_maxSurvivalOfRate (q := q) hx
  simpa [M, exponentialDistributionModel, exponentialMaxSurvival] using h

/-- Expected maximum of `q` rate-`lambda` exponential draws. -/
noncomputable def exponentialTopOneHarmonicValue (lambda : ℝ) (q : ℕ) : ℝ :=
  AppliedModelingLib.Probability.Exponential.expectedMaxValueOfRate lambda q

/--
Survival-integral form of the iid product-measure maximum checkpoint.  The
integrand is the real probability that the sample maximum exceeds `x`; the
integral over `x > 0` is the harmonic value `H_q/lambda`.
-/
theorem exponentialProductMaxSurvival_integral_eq_harmonicValue
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ x in Set.Ioi (0 : ℝ),
        (1 - (((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
          {sample : Fin q → ℝ |
            AppliedModelingLib.Probability.Exponential.finiteSampleMax sample ≤ x}).toReal) =
      exponentialTopOneHarmonicValue lambda q := by
  calc
    ∫ x in Set.Ioi (0 : ℝ),
        (1 - (((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
          {sample : Fin q → ℝ |
            AppliedModelingLib.Probability.Exponential.finiteSampleMax sample ≤ x}).toReal)
        = ∫ x in Set.Ioi (0 : ℝ), exponentialMaxSurvival lambda q x := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          exact exponentialProductMaxSurvival_eq_formula
            lambda hlambda_pos (q := q) (le_of_lt hx)
    _ = exponentialTopOneHarmonicValue lambda q := by
          simpa [exponentialTopOneHarmonicValue] using
            exponentialMaxSurvival_integral_eq_harmonicValue
              lambda hlambda_pos q

/--
Layer-cake tail-integral side of the iid product-measure maximum checkpoint.
The integrand is `μ.real {sample | x < max sample}`, which is the form used by
mathlib's layer-cake theorem for nonnegative random variables.
-/
theorem exponentialProductMaxTailIntegral_eq_harmonicValue
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ x in Set.Ioi (0 : ℝ),
        ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.Exponential.finiteSampleMax sample} =
      exponentialTopOneHarmonicValue lambda q := by
  let M := exponentialDistributionModel lambda hlambda_pos
  have h := M.iidProductMeasure_finiteSampleMax_tailIntegral_eq_expectedMaxValue
    (q := q)
  simpa [M, exponentialDistributionModel, exponentialTopOneHarmonicValue,
    AppliedModelingLib.Probability.Exponential.Model.expectedMaxValue] using h

/--
Conditional layer-cake bridge to the literal Bochner expectation of the finite
iid maximum.  The exponential library already proves the required
a.e.-nonnegativity; the remaining hypothesis is integrability of the finite
maximum under the product measure.
-/
theorem exponentialProductMaxIntegral_eq_harmonicValue_of_integrable
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q]
    (h_int : MeasureTheory.Integrable
      (AppliedModelingLib.Probability.Exponential.finiteSampleMax (q := q))
      ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)) :
    ∫ sample,
        AppliedModelingLib.Probability.Exponential.finiteSampleMax sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopOneHarmonicValue lambda q := by
  let M := exponentialDistributionModel lambda hlambda_pos
  have h :=
    M.iidProductMeasure_finiteSampleMax_integral_eq_expectedMaxValue_of_integrable
      (q := q) h_int
  simpa [M, exponentialDistributionModel, exponentialTopOneHarmonicValue,
    AppliedModelingLib.Probability.Exponential.Model.expectedMaxValue] using h

/--
Literal Bochner expectation of the maximum of `q` iid rate-`lambda`
exponential draws.
-/
theorem exponentialProductMaxIntegral_eq_harmonicValue
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ sample,
        AppliedModelingLib.Probability.Exponential.finiteSampleMax sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopOneHarmonicValue lambda q := by
  let M := exponentialDistributionModel lambda hlambda_pos
  have h :=
    M.iidProductMeasure_finiteSampleMax_integral_eq_expectedMaxValue
      (q := q)
  simpa [M, exponentialDistributionModel, exponentialTopOneHarmonicValue,
    AppliedModelingLib.Probability.Exponential.Model.expectedMaxValue] using h

theorem exponentialTopOneHarmonicValue_one (lambda : ℝ) :
    exponentialTopOneHarmonicValue lambda 1 = 1 / lambda := by
  simpa [exponentialTopOneHarmonicValue] using
    AppliedModelingLib.Probability.Exponential.expectedMaxValueOfRate_one lambda

/--
Measure-facing base case for the exponential top-one branch: for one draw from
the rate-`lambda` exponential model, the survival integral of the model CDF is
the `H_1/lambda` harmonic value.
-/
theorem exponentialTopOneHarmonic_singleDraw_survival_integral
    (lambda : ℝ) (hlambda_pos : 0 < lambda) :
    ∫ x in Set.Ioi (0 : ℝ),
        (1 - ProbabilityTheory.cdf
          (exponentialDistributionModel lambda hlambda_pos).measure x) =
      exponentialTopOneHarmonicValue lambda 1 := by
  let M := exponentialDistributionModel lambda hlambda_pos
  have h := M.singleDrawSurvivalIntegral_eq_expectedMaxValue
  simpa [M, exponentialDistributionModel, exponentialTopOneHarmonicValue,
    AppliedModelingLib.Probability.Exponential.Model.expectedMaxValue] using h

/-- Common top-one oracle with the exact exponential maximum formula. -/
noncomputable def exponentialTopOneHarmonicOracle (T : ℕ) (lambda : ℝ) :
    TopKValueOracle T := TopKValueOracle.common T (exponentialTopOneHarmonicValue lambda)

theorem exponentialTopOneHarmonic_forward_marginal
    (lambda : ℝ) (q : ℕ) :
    exponentialTopOneHarmonicValue lambda (q + 1) -
        exponentialTopOneHarmonicValue lambda q =
      (1 / lambda) * ((1 : ℝ) / ((q + 1 : ℕ) : ℝ)) := by
  simpa [exponentialTopOneHarmonicValue] using
    AppliedModelingLib.Probability.Exponential.expectedMaxValueOfRate_forward_marginal
      lambda q

theorem exponentialTopOneHarmonic_backward_marginal
    (lambda : ℝ) {q : ℕ} (hq : 0 < q) :
    exponentialTopOneHarmonicValue lambda q -
        exponentialTopOneHarmonicValue lambda (q - 1) =
      (1 / lambda) * ((1 : ℝ) / (q : ℝ)) := by
  simpa [exponentialTopOneHarmonicValue] using
    AppliedModelingLib.Probability.Exponential.expectedMaxValueOfRate_backward_marginal
      lambda hq

/--
Harmonic-number asymptotic behind the paper's exponential top-one log
approximation.

The exact oracle differs from `(1/lambda) * log q` by a convergent constant
term `(1/lambda) * Euler-Mascheroni`.
-/
theorem exponentialTopOneHarmonicValue_sub_log_tendsto
    (lambda : ℝ) :
    Filter.Tendsto
      (fun q : ℕ =>
        exponentialTopOneHarmonicValue lambda q -
          (1 / lambda) * Real.log q)
      Filter.atTop
      (nhds ((1 / lambda) * Real.eulerMascheroniConstant)) := by
  simpa [exponentialTopOneHarmonicValue] using
    AppliedModelingLib.Probability.Exponential.expectedMaxValueOfRate_sub_log_tendsto
      lambda

theorem reciprocal_ratio_lt_of_scaled_ratio_lt
    {p_src p_dst x y : ℝ}
    (hp_src : 0 < p_src) (hp_dst : 0 < p_dst)
    (hx : 0 < x) (hy : 0 < y)
    (hscaled : y / p_dst < x / p_src) :
    p_src / x < p_dst / y := by
  have hrecip :
      1 / (x / p_src) < 1 / (y / p_dst) :=
    one_div_lt_one_div_of_lt (div_pos hy hp_dst) hscaled
  have hleft : 1 / (x / p_src) = p_src / x := by
    field_simp [ne_of_gt hx, ne_of_gt hp_src]
  have hright : 1 / (y / p_dst) = p_dst / y := by
    field_simp [ne_of_gt hy, ne_of_gt hp_dst]
  simpa [hleft, hright] using hrecip

/--
The finite-prefix error used for the exact top-one exponential FOC proof.

For positive likelihoods, `exponentialTopOneHarmonicError likelihood N * N`
is the constant `∑_t 1 / p_t + 1` for all positive `N`, and the displayed
error is therefore `O(1/N)`.
-/
noncomputable def exponentialTopOneHarmonicError {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 0 else
    ((∑ t : ItemType T, 1 / (likelihood t ^ (1 : ℝ))) + 1) / (N : ℝ)

theorem exponentialTopOneHarmonicError_nonneg {T : ℕ}
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (N : ℕ) :
    0 ≤ exponentialTopOneHarmonicError likelihood N := by
  by_cases hN : N = 0
  · simp [exponentialTopOneHarmonicError, hN]
  · have hS_nonneg :
        0 ≤ ∑ t : ItemType T, 1 / (likelihood t ^ (1 : ℝ)) :=
      Finset.sum_nonneg
        (fun t _ => div_nonneg zero_le_one
          (le_of_lt (by
            simpa [Real.rpow_one] using hlike_pos t)))
    have hN_pos : 0 < (N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hN
    have hnum_nonneg :
        0 ≤ (∑ t : ItemType T, 1 / (likelihood t ^ (1 : ℝ))) + 1 :=
      add_nonneg hS_nonneg zero_le_one
    rw [exponentialTopOneHarmonicError, if_neg hN]
    exact div_nonneg hnum_nonneg (le_of_lt hN_pos)

theorem exponentialTopOneHarmonicError_tends_to_zero {T : ℕ}
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    AppliedModelingLib.Math.TendsToZero
      (exponentialTopOneHarmonicError likelihood) := by
  let S : ℝ := (∑ t : ItemType T, 1 / (likelihood t ^ (1 : ℝ))) + 1
  have hsum_nonneg :
      0 ≤ ∑ t : ItemType T, 1 / (likelihood t ^ (1 : ℝ)) :=
    Finset.sum_nonneg
      (fun t _ => div_nonneg zero_le_one
        (le_of_lt (by
          simpa [Real.rpow_one] using hlike_pos t)))
  have hS_pos : 0 < S := by
    dsimp [S]
    linarith
  refine AppliedModelingLib.Math.TendsToZero_of_nonneg_le_const_div
    (exponentialTopOneHarmonicError likelihood) hS_pos
    (exponentialTopOneHarmonicError_nonneg likelihood hlike_pos) ?_
  intro N hN
  have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
  simp [exponentialTopOneHarmonicError, hN_ne, S]

noncomputable def exponentialTopOneHarmonicSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (lambda : ℝ)
    (hlambda_pos : 0 < lambda)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    PairwiseScaledSublinearFOCCertificate
      (fun _ =>
        (exponentialTopOneHarmonicOracle T lambda).toConsumptionModel
          likelihood 1)
      (fun t : ItemType T => likelihood t ^ (1 : ℝ))
      (gammaLikelihoodProfile likelihood 1) where
  weight_pos := by
    intro t
    simpa [Real.rpow_one] using hlike_pos t
  targetShare_eq := by
    intro t
    have hnorm_pos :
        0 < ∑ i : ItemType T, likelihood i ^ (1 : ℝ) :=
      Finset.sum_pos
        (fun i _ => by simpa [Real.rpow_one] using hlike_pos i)
        Finset.univ_nonempty
    exact gammaLikelihoodProfile_targetShare_eq likelihood 1 t
      (ne_of_gt hnorm_pos)
  error := exponentialTopOneHarmonicError likelihood
  error_nonneg := exponentialTopOneHarmonicError_nonneg likelihood hlike_pos
  error_tends_to_zero :=
    exponentialTopOneHarmonicError_tends_to_zero likelihood hlike_pos
  large_gap_backward_lt_forward := by
    intro N a hN _hopt src dst hgap
    let weight : ItemType T → ℝ := fun t => likelihood t ^ (1 : ℝ)
    let S : ℝ := (∑ t : ItemType T, 1 / weight t) + 1
    have hweight_pos : ∀ t, 0 < weight t := by
      intro t
      dsimp [weight]
      simpa [Real.rpow_one] using hlike_pos t
    have hS_pos : 0 < S := by
      dsimp [S]
      have hsum_nonneg :
          0 ≤ ∑ t : ItemType T, 1 / weight t :=
        Finset.sum_nonneg
          (fun t _ => div_nonneg zero_le_one (le_of_lt (hweight_pos t)))
      linarith
    have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
    have hN_real_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN_ne
    have hgapS :
        S <
          (a.count src : ℝ) / weight src -
            (a.count dst : ℝ) / weight dst := by
      have hmul :
          exponentialTopOneHarmonicError likelihood N * (N : ℝ) = S := by
        simp [exponentialTopOneHarmonicError, hN_ne, S, weight,
          hN_real_ne]
      simpa [hmul, weight] using hgap
    have hdst_nonneg :
        0 ≤ (a.count dst : ℝ) / weight dst :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt (hweight_pos dst))
    have hsrc_div_pos : 0 < (a.count src : ℝ) / weight src := by
      linarith
    have hsrc_pos : 0 < a.count src := by
      by_contra hnot
      have hzero : a.count src = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hzero] at hsrc_div_pos
      simp at hsrc_div_pos
    have hinv_dst_lt_S : 1 / weight dst < S := by
      have hinv_le_sum :
          1 / weight dst ≤ ∑ t : ItemType T, 1 / weight t :=
        Finset.single_le_sum
          (fun t _ => div_nonneg zero_le_one (le_of_lt (hweight_pos t)))
          (Finset.mem_univ dst)
      dsimp [S]
      linarith
    have hscaled_add :
        ((a.count dst : ℝ) + 1) / weight dst <
          (a.count src : ℝ) / weight src := by
      have hsum_lt :
          (a.count dst : ℝ) / weight dst + 1 / weight dst <
            (a.count src : ℝ) / weight src := by
        linarith
      have hadd :
          ((a.count dst : ℝ) + 1) / weight dst =
            (a.count dst : ℝ) / weight dst + 1 / weight dst := by
        ring
      simpa [hadd] using hsum_lt
    have hqsrc_real_pos : 0 < (a.count src : ℝ) := by
      exact_mod_cast hsrc_pos
    have hqdst_succ_pos :
        0 < ((a.count dst + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos (a.count dst)
    have hratio_weight :
        weight src / (a.count src : ℝ) <
          weight dst / ((a.count dst + 1 : ℕ) : ℝ) := by
      have hscaled' :
          ((a.count dst + 1 : ℕ) : ℝ) / weight dst <
            (a.count src : ℝ) / weight src := by
        simpa [Nat.cast_add, Nat.cast_one] using hscaled_add
      exact reciprocal_ratio_lt_of_scaled_ratio_lt
        (hweight_pos src) (hweight_pos dst)
        hqsrc_real_pos hqdst_succ_pos hscaled'
    have hratio_like :
        likelihood src / (a.count src : ℝ) <
          likelihood dst / ((a.count dst + 1 : ℕ) : ℝ) := by
      simpa [weight, Real.rpow_one] using hratio_weight
    have hmarginal :
        likelihood src *
            ((1 / lambda) * ((1 : ℝ) / (a.count src : ℝ))) <
          likelihood dst *
            ((1 / lambda) * ((1 : ℝ) /
              ((a.count dst + 1 : ℕ) : ℝ))) := by
      calc
        likelihood src *
            ((1 / lambda) * ((1 : ℝ) / (a.count src : ℝ))) =
            (1 / lambda) * (likelihood src / (a.count src : ℝ)) := by
              ring
        _ < (1 / lambda) *
            (likelihood dst / ((a.count dst + 1 : ℕ) : ℝ)) :=
              mul_lt_mul_of_pos_left hratio_like (one_div_pos.mpr hlambda_pos)
        _ = likelihood dst *
            ((1 / lambda) * ((1 : ℝ) /
              ((a.count dst + 1 : ℕ) : ℝ))) := by
              ring
    unfold ConsumptionModel.weightedBackwardMarginal
      ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
      AppliedModelingLib.Allocation.marginal TopKValueOracle.toConsumptionModel
    rw [dif_neg hsrc_pos.ne']
    simp only [exponentialTopOneHarmonicOracle, TopKValueOracle.common_expectedTopSum]
    rw [exponentialTopOneHarmonic_backward_marginal lambda hsrc_pos,
      exponentialTopOneHarmonic_forward_marginal]
    exact hmarginal

theorem nat_min_eq_sum_tail_indicators_real (k n : ℕ) :
    ((min k n : ℕ) : ℝ) =
      ∑ r ∈ Finset.Icc 1 k, if r ≤ n then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
  have hfilter :
      (Finset.Icc 1 k).filter (fun r : ℕ => r ≤ n) =
        Finset.Icc 1 (min k n) := by
    ext r
    simp [and_left_comm, and_assoc]
  rw [hfilter]
  simp

/--
Expected top-`k` value for the exponential order-statistic formula, recorded
through its exact marginal increments.

For a rate-`lambda` exponential distribution, adding the `(q+1)`st draw
contributes `(1/lambda) * min(k,q+1)/(q+1)` to the expected sum of the largest
`k` draws. Summing these increments gives the finite top-`k` oracle used by the
general exponential branch.
-/
noncomputable def exponentialTopKOrderStatisticValue
    (lambda : ℝ) (k q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range q,
    (1 / lambda) *
      (((min k (j + 1) : ℕ) : ℝ) / (((j + 1 : ℕ) : ℝ)))

@[simp] theorem exponentialTopKOrderStatisticValue_zero
    (lambda : ℝ) (k : ℕ) :
    exponentialTopKOrderStatisticValue lambda k 0 = 0 := by
  simp [exponentialTopKOrderStatisticValue]

theorem exponentialTopKOrderStatistic_forward_marginal
    (lambda : ℝ) (k q : ℕ) :
    exponentialTopKOrderStatisticValue lambda k (q + 1) -
        exponentialTopKOrderStatisticValue lambda k q =
      (1 / lambda) *
        (((min k (q + 1) : ℕ) : ℝ) / (((q + 1 : ℕ) : ℝ))) := by
  simp [exponentialTopKOrderStatisticValue, Finset.sum_range_succ]

theorem exponentialTopKOrderStatistic_backward_marginal
    (lambda : ℝ) (k : ℕ) {q : ℕ} (hq : 0 < q) :
    exponentialTopKOrderStatisticValue lambda k q -
        exponentialTopKOrderStatisticValue lambda k (q - 1) =
      (1 / lambda) *
        (((min k q : ℕ) : ℝ) / (q : ℝ)) := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  nth_rewrite 1 [← hpred]
  rw [exponentialTopKOrderStatistic_forward_marginal]
  simp [hpred]

theorem exponentialTopKOrderStatisticValue_eq_sum_Icc
    (lambda : ℝ) (k q : ℕ) :
    exponentialTopKOrderStatisticValue lambda k q =
      ∑ j ∈ Finset.Icc 1 q,
        (1 / lambda) *
          (((min k j : ℕ) : ℝ) / (j : ℝ)) := by
  induction q with
  | zero =>
      simp [exponentialTopKOrderStatisticValue]
  | succ q ih =>
      calc
        exponentialTopKOrderStatisticValue lambda k (q + 1)
            = exponentialTopKOrderStatisticValue lambda k q +
                (1 / lambda) *
                  (((min k (q + 1) : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ)) := by
              rw [← exponentialTopKOrderStatistic_forward_marginal]
              ring
        _ =
            (∑ j ∈ Finset.Icc 1 q,
              (1 / lambda) *
                (((min k j : ℕ) : ℝ) / (j : ℝ))) +
              (1 / lambda) *
                (((min k (q + 1) : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ)) := by
              rw [ih]
        _ =
            ∑ j ∈ Finset.Icc 1 (q + 1),
              (1 / lambda) *
                (((min k j : ℕ) : ℝ) / (j : ℝ)) := by
              rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ q + 1)]

theorem exponentialTopKOrderStatisticValue_eq_tail_harmonic_sum
    (lambda : ℝ) (k q : ℕ) :
    exponentialTopKOrderStatisticValue lambda k q =
      (1 / lambda) *
        ∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q, (1 / (j : ℝ)) := by
  classical
  rw [exponentialTopKOrderStatisticValue_eq_sum_Icc]
  calc
    ∑ j ∈ Finset.Icc 1 q,
        (1 / lambda) *
          (((min k j : ℕ) : ℝ) / (j : ℝ))
        =
        (1 / lambda) *
          ∑ j ∈ Finset.Icc 1 q,
            (((min k j : ℕ) : ℝ) * (1 / (j : ℝ))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
    _ =
        (1 / lambda) *
          ∑ j ∈ Finset.Icc 1 q,
            ((∑ r ∈ Finset.Icc 1 k,
                if r ≤ j then (1 : ℝ) else 0) * (1 / (j : ℝ))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [← nat_min_eq_sum_tail_indicators_real k j]
    _ =
        (1 / lambda) *
          ∑ j ∈ Finset.Icc 1 q,
            ∑ r ∈ Finset.Icc 1 k,
              if r ≤ j then (1 / (j : ℝ)) else 0 := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro r _hr
          by_cases hrj : r ≤ j <;> simp [hrj]
    _ =
        (1 / lambda) *
          ∑ r ∈ Finset.Icc 1 k,
            ∑ j ∈ Finset.Icc 1 q,
              if r ≤ j then (1 / (j : ℝ)) else 0 := by
          rw [Finset.sum_comm]
    _ =
        (1 / lambda) *
          ∑ r ∈ Finset.Icc 1 k,
            ∑ j ∈ Finset.Icc r q, (1 / (j : ℝ)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro r hr
          have hr_one : 1 ≤ r := (Finset.mem_Icc.mp hr).1
          rw [← Finset.sum_filter]
          have hfilter :
              (Finset.Icc 1 q).filter (fun j : ℕ => r ≤ j) =
                Finset.Icc r q := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_Icc]
            constructor
            · intro h
              exact ⟨h.2, h.1.2⟩
            · intro h
              exact ⟨⟨le_trans hr_one h.1, h.2⟩, h.1⟩
          rw [hfilter]

theorem exponentialTopKOrderStatistic_min_ratio_nonneg
    (k q : ℕ) :
    0 ≤ (((min k (q + 1) : ℕ) : ℝ) / (((q + 1 : ℕ) : ℝ))) := div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem exponentialTopKOrderStatistic_min_ratio_antitone_succ
    (k q : ℕ) :
    (((min k (q + 2) : ℕ) : ℝ) / (((q + 2 : ℕ) : ℝ))) ≤
      (((min k (q + 1) : ℕ) : ℝ) / (((q + 1 : ℕ) : ℝ))) := by
  by_cases hlarge : q + 2 ≤ k
  · have hmin_left : min k (q + 2) = q + 2 := min_eq_right hlarge
    have hmin_right : min k (q + 1) = q + 1 :=
      min_eq_right (by omega)
    rw [hmin_left, hmin_right]
    field_simp
    norm_num
  · by_cases hmid : q + 1 ≤ k
    · have hk_eq : k = q + 1 := by omega
      subst k
      have hmin_left : min (q + 1) (q + 2) = q + 1 := min_eq_left (by omega)
      have hmin_right : min (q + 1) (q + 1) = q + 1 := min_eq_left le_rfl
      rw [hmin_left, hmin_right]
      have hden_left : (((q + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hden_right : (((q + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [hden_left, hden_right]
      exact_mod_cast Nat.le_succ (q + 1)
    · have hk_le_succ : k ≤ q + 1 := by omega
      have hmin_left : min k (q + 2) = k := min_eq_left (by omega)
      have hmin_right : min k (q + 1) = k := min_eq_left hk_le_succ
      rw [hmin_left, hmin_right]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg k)
        (by positivity : (0 : ℝ) < (((q + 1 : ℕ) : ℝ)))
        (by exact_mod_cast Nat.le_succ (q + 1))

theorem exponentialTopKOrderStatistic_min_ratio_strict_antitone_succ_of_le
    {k q : ℕ} (hk_pos : 0 < k) (hk_le : k ≤ q + 1) :
    (((min k (q + 2) : ℕ) : ℝ) / (((q + 2 : ℕ) : ℝ))) <
      (((min k (q + 1) : ℕ) : ℝ) / (((q + 1 : ℕ) : ℝ))) := by
  have hmin_left : min k (q + 2) = k := min_eq_left (by omega)
  have hmin_right : min k (q + 1) = k := min_eq_left hk_le
  rw [hmin_left, hmin_right]
  exact div_lt_div_of_pos_left
    (by exact_mod_cast hk_pos : (0 : ℝ) < (k : ℝ))
    (by positivity : (0 : ℝ) < (((q + 1 : ℕ) : ℝ)))
    (by exact_mod_cast Nat.lt_succ_self (q + 1))

theorem exponentialTopKOrderStatistic_forward_marginal_nonneg
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (k q : ℕ) :
    0 ≤
      exponentialTopKOrderStatisticValue lambda k (q + 1) -
        exponentialTopKOrderStatisticValue lambda k q := by
  rw [exponentialTopKOrderStatistic_forward_marginal]
  exact mul_nonneg (le_of_lt (one_div_pos.mpr hlambda_pos))
    (exponentialTopKOrderStatistic_min_ratio_nonneg k q)

theorem exponentialTopKOrderStatistic_forward_marginal_antitone_succ
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (k q : ℕ) :
    exponentialTopKOrderStatisticValue lambda k (q + 2) -
        exponentialTopKOrderStatisticValue lambda k (q + 1) ≤
      exponentialTopKOrderStatisticValue lambda k (q + 1) -
        exponentialTopKOrderStatisticValue lambda k q := by
  rw [exponentialTopKOrderStatistic_forward_marginal,
    exponentialTopKOrderStatistic_forward_marginal]
  exact mul_le_mul_of_nonneg_left
    (exponentialTopKOrderStatistic_min_ratio_antitone_succ k q)
    (le_of_lt (one_div_pos.mpr hlambda_pos))

theorem exponentialTopKOrderStatistic_forward_marginal_strict_antitone_succ_of_le
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {k q : ℕ} (hk_pos : 0 < k) (hk_le : k ≤ q + 1) :
    exponentialTopKOrderStatisticValue lambda k (q + 2) -
        exponentialTopKOrderStatisticValue lambda k (q + 1) <
      exponentialTopKOrderStatisticValue lambda k (q + 1) -
        exponentialTopKOrderStatisticValue lambda k q := by
  rw [exponentialTopKOrderStatistic_forward_marginal,
    exponentialTopKOrderStatistic_forward_marginal]
  exact mul_lt_mul_of_pos_left
    (exponentialTopKOrderStatistic_min_ratio_strict_antitone_succ_of_le
      hk_pos hk_le)
    (one_div_pos.mpr hlambda_pos)

theorem exponentialTopKOrderStatisticValue_eq_linear_of_le
    (lambda : ℝ) {k q : ℕ} (hqk : q ≤ k) :
    exponentialTopKOrderStatisticValue lambda k q =
      (1 / lambda) * (q : ℝ) := by
  unfold exponentialTopKOrderStatisticValue
  calc
    ∑ j ∈ Finset.range q,
        (1 / lambda) *
          (((min k (j + 1) : ℕ) : ℝ) / (((j + 1 : ℕ) : ℝ)))
        = ∑ _j ∈ Finset.range q, (1 / lambda) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hj_succ_le_q : j + 1 ≤ q := Finset.mem_range.mp hj
          have hj_succ_le_k : j + 1 ≤ k := le_trans hj_succ_le_q hqk
          have hmin : min k (j + 1) = j + 1 :=
            min_eq_right hj_succ_le_k
          have hden : (((j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
          rw [hmin]
          field_simp [hden]
    _ = (1 / lambda) * (q : ℝ) := by
          simp [Finset.card_range, mul_comm]

theorem exponentialTopKOrderStatisticValue_eq_harmonic_of_k_le
    (lambda : ℝ) {k q : ℕ} (hk_pos : 0 < k) (hkq : k ≤ q) :
    exponentialTopKOrderStatisticValue lambda k q =
      (1 / lambda) * ((k : ℝ) * (1 + harmonicReal q - harmonicReal k)) := by
  induction q, hkq using Nat.le_induction with
  | base =>
      have hlinear :=
        exponentialTopKOrderStatisticValue_eq_linear_of_le
          (lambda := lambda) (k := k) (q := k) (le_rfl)
      calc
        exponentialTopKOrderStatisticValue lambda k k
            = (1 / lambda) * (k : ℝ) := hlinear
        _ = (1 / lambda) *
              ((k : ℝ) * (1 + harmonicReal k - harmonicReal k)) := by
              ring
  | succ q hkq ih =>
      have hmin : min k (q + 1) = k := min_eq_left (by omega)
      calc
        exponentialTopKOrderStatisticValue lambda k (q + 1)
            = exponentialTopKOrderStatisticValue lambda k q +
                (1 / lambda) *
                  (((min k (q + 1) : ℕ) : ℝ) /
                    (((q + 1 : ℕ) : ℝ))) := by
              rw [← exponentialTopKOrderStatistic_forward_marginal]
              ring
        _ = (1 / lambda) * ((k : ℝ) * (1 + harmonicReal q - harmonicReal k)) +
              (1 / lambda) *
                (((min k (q + 1) : ℕ) : ℝ) /
                  (((q + 1 : ℕ) : ℝ))) := by
              rw [ih]
        _ = (1 / lambda) *
              ((k : ℝ) * (1 + harmonicReal (q + 1) - harmonicReal k)) := by
              rw [hmin, harmonicReal_succ]
              ring

theorem exponentialTopKOrderStatisticValue_pred_card
    (lambda : ℝ) (hlambda_pos : 0 < lambda) {q : ℕ} [NeZero q] :
    exponentialTopKOrderStatisticValue lambda (q - 1) q =
      (1 / lambda) * (q : ℝ) - 1 / ((q : ℝ) * lambda) := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hlinear :
      exponentialTopKOrderStatisticValue lambda (q - 1) (q - 1) =
        (1 / lambda) * ((q - 1 : ℕ) : ℝ) :=
    exponentialTopKOrderStatisticValue_eq_linear_of_le
      (lambda := lambda) (k := q - 1) (q := q - 1) le_rfl
  have hmarg :
      exponentialTopKOrderStatisticValue lambda (q - 1) q -
          exponentialTopKOrderStatisticValue lambda (q - 1) (q - 1) =
        (1 / lambda) *
          (((min (q - 1) q : ℕ) : ℝ) / (q : ℝ)) :=
    exponentialTopKOrderStatistic_backward_marginal
      (lambda := lambda) (k := q - 1) hqpos
  have hmin : min (q - 1) q = q - 1 := min_eq_left (Nat.pred_le q)
  have hpred_cast : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
    have hpred_succ : q - 1 + 1 = q :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hqpos)
    rw [← hpred_succ]
    norm_num
  have hvalue :
      exponentialTopKOrderStatisticValue lambda (q - 1) q =
        (1 / lambda) * ((q - 1 : ℕ) : ℝ) +
          (1 / lambda) * (((q - 1 : ℕ) : ℝ) / (q : ℝ)) := by
    rw [hmin] at hmarg
    linarith
  rw [hvalue, hpred_cast]
  have hq_ne : (q : ℝ) ≠ 0 := by positivity
  have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda_pos
  field_simp [hq_ne, hlambda_ne]
  ring

theorem exponentialTopKOrderStatisticValue_sub_log_tendsto
    (lambda : ℝ) (k : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        exponentialTopKOrderStatisticValue lambda k q -
          ((1 / lambda) * (k : ℝ)) * Real.log q)
      Filter.atTop
      (nhds
        (((1 / lambda) * (k : ℝ)) *
          (1 + Real.eulerMascheroniConstant - harmonicReal k))) := by
  by_cases hk_zero : k = 0
  · subst k
    simpa [exponentialTopKOrderStatisticValue] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
        Filter.atTop (nhds 0))
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_zero
    let c : ℝ := (1 / lambda) * (k : ℝ)
    have hbase :
        Filter.Tendsto
          (fun q : ℕ => harmonicReal q - Real.log q)
          Filter.atTop (nhds Real.eulerMascheroniConstant) := by
      have h := Real.tendsto_harmonic_sub_log
      refine h.congr' ?_
      filter_upwards with q
      rw [harmonicReal_eq_harmonic]
    have hlim :
        Filter.Tendsto
          (fun q : ℕ =>
            c * (1 - harmonicReal k) +
              c * (harmonicReal q - Real.log q))
          Filter.atTop
          (nhds
            (c * (1 - harmonicReal k) +
              c * Real.eulerMascheroniConstant)) :=
      tendsto_const_nhds.add (hbase.const_mul c)
    have htarget :
        Filter.Tendsto
          (fun q : ℕ =>
            c * (1 - harmonicReal k) +
              c * (harmonicReal q - Real.log q))
          Filter.atTop
          (nhds
            (((1 / lambda) * (k : ℝ)) *
              (1 + Real.eulerMascheroniConstant - harmonicReal k))) := by
      convert hlim using 1
      · dsimp [c]
        ring_nf
    refine htarget.congr' ?_
    filter_upwards [Filter.eventually_atTop.2 ⟨k, fun q hq => hq⟩] with q hq
    have hvalue :=
      exponentialTopKOrderStatisticValue_eq_harmonic_of_k_le
        (lambda := lambda) hk_pos hq
    symm
    calc
      exponentialTopKOrderStatisticValue lambda k q -
          ((1 / lambda) * (k : ℝ)) * Real.log q
          = c * (1 + harmonicReal q - harmonicReal k) -
              c * Real.log q := by
            rw [hvalue]
            dsimp [c]
            ring
      _ = c * (1 - harmonicReal k) +
            c * (harmonicReal q - Real.log q) := by
            ring

theorem exponentialTopKOrderStatistic_min_ratio_le
    {k q : ℕ} (hk_pos : 0 < k) :
    ((k : ℝ) / (((q + k : ℕ) : ℝ))) ≤
      (((min k (q + 1) : ℕ) : ℝ) / (((q + 1 : ℕ) : ℝ))) := by
  by_cases hsmall : q + 1 ≤ k
  · have hmin : min k (q + 1) = q + 1 := min_eq_right hsmall
    have hden_pos : 0 < (((q + k : ℕ) : ℝ)) := by
      exact_mod_cast Nat.add_pos_right q hk_pos
    have hle : (k : ℝ) ≤ ((q + k : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left k q
    rw [hmin]
    have hsucc_ne : (((q + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hsucc_ne]
    exact hle
  · have hk_le_succ : k ≤ q + 1 := by omega
    have hmin : min k (q + 1) = k := min_eq_left hk_le_succ
    have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
    have hden_left_pos : 0 < (((q + k : ℕ) : ℝ)) := by
      exact_mod_cast Nat.add_pos_right q hk_pos
    have hden_right_pos : 0 < (((q + 1 : ℕ) : ℝ)) := by positivity
    have hden_le : (((q + 1 : ℕ) : ℝ)) ≤ (((q + k : ℕ) : ℝ)) := by
      exact_mod_cast Nat.add_le_add_left (Nat.succ_le_iff.mpr hk_pos) q
    rw [hmin]
    exact div_le_div_of_nonneg_left hk_nonneg hden_right_pos hden_le

/-- Common top-`k` oracle with the exact exponential order-statistic marginals. -/
noncomputable def exponentialTopKOrderStatisticOracle
    (T : ℕ) (lambda : ℝ) (k : ℕ) : TopKValueOracle T := TopKValueOracle.common T (exponentialTopKOrderStatisticValue lambda k)

theorem exponentialTopKOrderStatisticOracle_has_nonnegative_marginals
    (T : ℕ) (lambda : ℝ) (k : ℕ) (hlambda_pos : 0 < lambda) :
    (exponentialTopKOrderStatisticOracle T lambda k).HasNonnegativeMarginalsAt
      k := by
  intro t q
  rw [TopKValueOracle.marginalTopK_apply]
  simp only [exponentialTopKOrderStatisticOracle,
    TopKValueOracle.common_expectedTopSum]
  exact exponentialTopKOrderStatistic_forward_marginal_nonneg
    lambda hlambda_pos k q

theorem exponentialTopKOrderStatisticOracle_has_diminishing_returns
    (T : ℕ) (lambda : ℝ) (k : ℕ) (hlambda_pos : 0 < lambda) :
    (exponentialTopKOrderStatisticOracle T lambda k).HasDiminishingReturnsAt
      k := by
  intro t q
  rw [TopKValueOracle.marginalTopK_apply,
    TopKValueOracle.marginalTopK_apply]
  simp only [exponentialTopKOrderStatisticOracle,
    TopKValueOracle.common_expectedTopSum]
  exact exponentialTopKOrderStatistic_forward_marginal_antitone_succ
    lambda hlambda_pos k q

theorem exponentialTopKOrderStatisticConsumptionModel_has_nonnegative_marginals
    {T : ℕ} (likelihood : ItemType T → ℝ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda) :
    ((exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
      likelihood k).HasNonnegativeMarginals :=
  TopKValueOracle.toConsumptionModel_has_nonnegative_marginals
    (exponentialTopKOrderStatisticOracle T lambda k) likelihood k
    (exponentialTopKOrderStatisticOracle_has_nonnegative_marginals
      T lambda k hlambda_pos)

theorem exponentialTopKOrderStatisticConsumptionModel_has_diminishing_returns
    {T : ℕ} (likelihood : ItemType T → ℝ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda) :
    ((exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
      likelihood k).HasDiminishingReturns :=
  TopKValueOracle.toConsumptionModel_has_diminishing_returns
    (exponentialTopKOrderStatisticOracle T lambda k) likelihood k
    (exponentialTopKOrderStatisticOracle_has_diminishing_returns
      T lambda k hlambda_pos)

/--
Finite sample top-`k` sum for a concrete vector of iid exponential draws.

This is the measure-facing random variable whose expectation should eventually
be connected to `exponentialTopKOrderStatisticValue`.
-/
noncomputable def exponentialFiniteSampleTopKSum {q : ℕ}
    (k : ℕ) (sample : Fin q → ℝ) : ℝ := topKSumOn k sample

theorem exponentialFiniteSampleTopKSum_nonneg {q : ℕ}
    (k : ℕ) (sample : Fin q → ℝ) :
    0 ≤ exponentialFiniteSampleTopKSum k sample := topKSumOn_nonneg k sample

theorem sample_le_finiteSampleMax {q : ℕ} [NeZero q]
    (sample : Fin q → ℝ) (i : Fin q) :
    sample i ≤ AppliedModelingLib.Probability.Exponential.finiteSampleMax sample := by
  unfold AppliedModelingLib.Probability.Exponential.finiteSampleMax
  exact Finset.le_sup' sample (Finset.mem_univ i)

theorem exponentialFiniteSampleTopKSum_le_k_mul_finiteSampleMax
    {q : ℕ} [NeZero q] (k : ℕ) (sample : Fin q → ℝ)
    (hmax_nonneg :
      0 ≤ AppliedModelingLib.Probability.Exponential.finiteSampleMax sample) :
    exponentialFiniteSampleTopKSum k sample ≤
      (k : ℝ) * AppliedModelingLib.Probability.Exponential.finiteSampleMax sample :=
   topKSumOn_le_card_mul_of_forall_le
    k sample hmax_nonneg (sample_le_finiteSampleMax sample)

theorem exponentialFiniteSampleTopKSum_one_eq_finiteSampleMax
    {q : ℕ} [NeZero q] (sample : Fin q → ℝ)
    (hmax_nonneg :
      0 ≤ AppliedModelingLib.Probability.Exponential.finiteSampleMax sample) :
    exponentialFiniteSampleTopKSum 1 sample =
      AppliedModelingLib.Probability.Exponential.finiteSampleMax sample := by
  apply le_antisymm
  · simpa using
      exponentialFiniteSampleTopKSum_le_k_mul_finiteSampleMax
        (k := 1) sample hmax_nonneg
  · obtain ⟨i, _hi, hmax_eq⟩ :=
      Finset.exists_mem_eq_sup'
        (s := (Finset.univ : Finset (Fin q)))
        Finset.univ_nonempty sample
    have hsingle_card : ({i} : Finset (Fin q)).card ≤ 1 := by
      simp
    have hcandidate :
        sample i ≤ exponentialFiniteSampleTopKSum 1 sample := by
      have h :=
        sum_le_topKSumOn (ι := Fin q) 1 sample ({i} : Finset (Fin q))
          hsingle_card
      simpa [exponentialFiniteSampleTopKSum] using h
    rw [AppliedModelingLib.Probability.Exponential.finiteSampleMax, hmax_eq]
    exact hcandidate

theorem exponentialFiniteSampleTopKSum_eq_sum_of_card_le
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (hqk : q ≤ k) (h_nonneg : ∀ i, 0 ≤ sample i) :
    exponentialFiniteSampleTopKSum k sample = ∑ i, sample i := by
  apply le_antisymm
  · unfold exponentialFiniteSampleTopKSum topKSumOn
    refine Finset.sup'_le (topKCandidateSets_nonempty (Fin q) k)
      (fun s => ∑ i ∈ s, sample i) ?_
    intro s _hs
    have hsub : s ⊆ (Finset.univ : Finset (Fin q)) := by
      intro i _hi
      simp
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _hi_univ _hi_not_s => h_nonneg i)
  · have hcard : (Finset.univ : Finset (Fin q)).card ≤ k := by
      simpa using hqk
    simpa [exponentialFiniteSampleTopKSum] using
      sum_le_topKSumOn (ι := Fin q) k sample
        (Finset.univ : Finset (Fin q)) hcard

theorem exponentialFiniteSampleTopKSum_zero
    {q : ℕ} (sample : Fin q → ℝ) :
    exponentialFiniteSampleTopKSum 0 sample = 0 := by
  apply le_antisymm
  · unfold exponentialFiniteSampleTopKSum topKSumOn
    refine Finset.sup'_le (topKCandidateSets_nonempty (Fin q) 0)
      (fun s => ∑ i ∈ s, sample i) ?_
    intro s hs
    have hcard : s.card ≤ 0 := by
      simpa [topKCandidateSets] using hs
    have hs_empty : s = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    simp [hs_empty]
  · simpa [exponentialFiniteSampleTopKSum] using
      topKSumOn_nonneg (ι := Fin q) 0 sample

theorem exponentialFiniteSampleTopKSum_pred_card_eq_sum_sub_min
    {q : ℕ} [NeZero q] (sample : Fin q → ℝ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    exponentialFiniteSampleTopKSum (q - 1) sample =
      (∑ i : Fin q, sample i) -
        AppliedModelingLib.Probability.Exponential.finiteSampleMin sample := by
  apply le_antisymm
  · unfold exponentialFiniteSampleTopKSum topKSumOn
    refine Finset.sup'_le (topKCandidateSets_nonempty (Fin q) (q - 1))
      (fun s => ∑ i ∈ s, sample i) ?_
    intro s hs
    have hs_card : s.card ≤ q - 1 := by
      simpa [topKCandidateSets] using hs
    have hmissing : ∃ j : Fin q, j ∉ s := by
      by_contra hnone
      push Not at hnone
      have huniv_subset : (Finset.univ : Finset (Fin q)) ⊆ s := by
        intro i _hi
        exact hnone i
      have hq_le : q ≤ s.card := by
        simpa using Finset.card_le_card huniv_subset
      have hq_pos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      omega
    obtain ⟨j, hj_not_mem⟩ := hmissing
    have hmin_le :
        AppliedModelingLib.Probability.Exponential.finiteSampleMin sample ≤ sample j :=
      AppliedModelingLib.Probability.Exponential.finiteSampleMin_le_sample sample j
    have hinsert_subset :
        insert j s ⊆ (Finset.univ : Finset (Fin q)) := by
      intro i _hi
      simp
    have hsum_insert_le :
        (∑ i ∈ insert j s, sample i) ≤ ∑ i : Fin q, sample i :=
      Finset.sum_le_sum_of_subset_of_nonneg hinsert_subset
        (fun i _hi_univ _hi_not_insert => h_nonneg i)
    have hsum_add_le :
        (∑ i ∈ s, sample i) +
            AppliedModelingLib.Probability.Exponential.finiteSampleMin sample ≤
          ∑ i : Fin q, sample i := by
      calc
        (∑ i ∈ s, sample i) +
            AppliedModelingLib.Probability.Exponential.finiteSampleMin sample ≤
            (∑ i ∈ s, sample i) + sample j := by
              linarith
        _ = ∑ i ∈ insert j s, sample i := by
              rw [Finset.sum_insert hj_not_mem]
              ring
        _ ≤ ∑ i : Fin q, sample i := hsum_insert_le
    exact (le_sub_iff_add_le).2 hsum_add_le
  · obtain ⟨iMin, _hiMin, hmin_eq⟩ :=
      Finset.exists_mem_eq_inf'
        (s := (Finset.univ : Finset (Fin q)))
        Finset.univ_nonempty sample
    let sDrop : Finset (Fin q) := (Finset.univ : Finset (Fin q)).erase iMin
    have hsDrop_card : sDrop.card ≤ q - 1 := by
      have hcard : sDrop.card = q - 1 := by
        simp [sDrop]
      exact le_of_eq hcard
    have hcandidate :
        (∑ i ∈ sDrop, sample i) ≤
          exponentialFiniteSampleTopKSum (q - 1) sample := by
      simpa [exponentialFiniteSampleTopKSum, sDrop] using
        sum_le_topKSumOn (ι := Fin q) (q - 1) sample sDrop hsDrop_card
    have hmin_eq' :
        AppliedModelingLib.Probability.Exponential.finiteSampleMin sample = sample iMin := by
      simpa [AppliedModelingLib.Probability.Exponential.finiteSampleMin] using hmin_eq
    have hsum_drop :
        (∑ i ∈ sDrop, sample i) =
          (∑ i : Fin q, sample i) -
            AppliedModelingLib.Probability.Exponential.finiteSampleMin sample := by
      have htotal :
          sample iMin + (∑ i ∈ sDrop, sample i) =
            ∑ i : Fin q, sample i := by
        simpa [sDrop] using
          (Finset.add_sum_erase
            (s := (Finset.univ : Finset (Fin q))) (f := sample)
            (a := iMin) (Finset.mem_univ iMin))
      linarith
    simpa [hsum_drop] using hcandidate

theorem exponentialSuccessIndexSet_eq_pi
    {q : ℕ} (x : ℝ) (s : Finset (Fin q)) :
    {sample : Fin q → ℝ |
        successIndexSet (fun y : ℝ => x < y) sample = s} =
      Set.pi Set.univ
        (fun i : Fin q => if i ∈ s then Set.Ioi x else Set.Iic x) := by
  ext sample
  constructor
  · intro hs i _hi
    have hiff :=
      (successIndexSet_eq_iff
        (p := fun y : ℝ => x < y) sample s).1 hs i
    by_cases his : i ∈ s
    · simp [his, hiff.2 his]
    · have hle : sample i ≤ x :=
        le_of_not_gt (fun hgt => his (hiff.1 hgt))
      simp [his, hle]
  · intro hpi
    refine (successIndexSet_eq_iff
      (p := fun y : ℝ => x < y) sample s).2 ?_
    intro i
    constructor
    · intro hgt
      by_contra his
      have hmem := hpi i trivial
      simp [his] at hmem
      linarith
    · intro his
      have hmem := hpi i trivial
      simpa [his] using hmem

theorem exponentialSuccessIndexSet_measurableSet
    {q : ℕ} (x : ℝ) (s : Finset (Fin q)) :
    MeasurableSet
      {sample : Fin q → ℝ |
        successIndexSet (fun y : ℝ => x < y) sample = s} := by
  rw [exponentialSuccessIndexSet_eq_pi x s]
  refine MeasurableSet.pi Set.countable_univ ?_
  intro i _hi
  by_cases his : i ∈ s <;> simp [his]

theorem exponentialSuccessIndexSet_card_measurableSet
    {q : ℕ} (x : ℝ) (j : ℕ) :
    MeasurableSet
      {sample : Fin q → ℝ |
        (successIndexSet (fun y : ℝ => x < y) sample).card = j} := by
  let exactSets : Finset (Finset (Fin q)) :=
    (Finset.univ : Finset (Fin q)).powersetCard j
  have hcard_set :
      {sample : Fin q → ℝ |
        (successIndexSet (fun y : ℝ => x < y) sample).card = j} =
        ⋃ s ∈ exactSets,
          {sample : Fin q → ℝ |
            successIndexSet (fun y : ℝ => x < y) sample = s} := by
    ext sample
    constructor
    · intro hcard
      refine Set.mem_iUnion.2
        ⟨successIndexSet (fun y : ℝ => x < y) sample, ?_⟩
      refine Set.mem_iUnion.2 ⟨?_, rfl⟩
      exact Finset.mem_powersetCard.mpr
        ⟨by intro i _hi; simp, hcard⟩
    · intro hmem
      rcases Set.mem_iUnion.mp hmem with ⟨s, hs_mem⟩
      rcases Set.mem_iUnion.mp hs_mem with ⟨hs_exact, hs_eq⟩
      have hs_card : s.card = j :=
        (Finset.mem_powersetCard.mp hs_exact).2
      have hs_eq' :
          successIndexSet (fun y : ℝ => x < y) sample = s := hs_eq
      change (successIndexSet (fun y : ℝ => x < y) sample).card = j
      rw [hs_eq', hs_card]
  rw [hcard_set]
  exact Finset.measurableSet_biUnion exactSets
    (fun s _hs => exponentialSuccessIndexSet_measurableSet x s)

theorem exponentialSuccessIndexSet_card_ge_measurableSet
    {q : ℕ} (x : ℝ) (r : ℕ) :
    MeasurableSet
      {sample : Fin q → ℝ |
        r ≤ (successIndexSet (fun y : ℝ => x < y) sample).card} := by
  let exactCounts : Finset ℕ := Finset.Icc r q
  have htail_set :
      {sample : Fin q → ℝ |
        r ≤ (successIndexSet (fun y : ℝ => x < y) sample).card} =
        ⋃ j ∈ exactCounts,
          {sample : Fin q → ℝ |
            (successIndexSet (fun y : ℝ => x < y) sample).card = j} := by
    ext sample
    constructor
    · intro hge
      let j := (successIndexSet (fun y : ℝ => x < y) sample).card
      have hj_le_q : j ≤ q := by
        simpa [j, Finset.card_univ] using
          (successIndexSet (fun y : ℝ => x < y) sample).card_le_univ
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      refine Set.mem_iUnion.2 ⟨?_, rfl⟩
      exact Finset.mem_Icc.mpr ⟨by simpa [j] using hge, hj_le_q⟩
    · intro hmem
      rcases Set.mem_iUnion.mp hmem with ⟨j, hj_mem⟩
      rcases Set.mem_iUnion.mp hj_mem with ⟨hj_exact, hj_eq⟩
      exact le_trans (Finset.mem_Icc.mp hj_exact).1 (by simpa using hj_eq.symm.le)
  rw [htail_set]
  exact Finset.measurableSet_biUnion exactCounts
    (fun j _hj => exponentialSuccessIndexSet_card_measurableSet x j)

theorem exponentialSuccessCount_measurable
    {q : ℕ} (x : ℝ) :
    Measurable
      (fun sample : Fin q → ℝ =>
        (successIndexSet (fun y : ℝ => x < y) sample).card) := by
  refine measurable_to_countable' ?_
  intro j
  simpa [Set.preimage, Set.mem_setOf_eq, Set.mem_singleton_iff] using
    exponentialSuccessIndexSet_card_measurableSet (q := q) x j

theorem exponentialSuccessCount_real_measurable
    {q : ℕ} (x : ℝ) :
    Measurable
      (fun sample : Fin q → ℝ =>
        ((successIndexSet (fun y : ℝ => x < y) sample).card : ℝ)) :=
   (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (exponentialSuccessCount_measurable (q := q) x)

theorem exponentialSuccessCount_min_real_measurable
    {q : ℕ} (x : ℝ) (k : ℕ) :
    Measurable
      (fun sample : Fin q → ℝ =>
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)) := by
  let countFun : (Fin q → ℝ) → ℕ :=
    fun sample => (successIndexSet (fun y : ℝ => x < y) sample).card
  let minFun : ℕ → ℕ := fun n => min k n
  have hmin : Measurable minFun := measurable_of_countable minFun
  have hcast : Measurable (fun n : ℕ => (n : ℝ)) :=
    measurable_of_countable (fun n : ℕ => (n : ℝ))
  exact hcast.comp (hmin.comp (exponentialSuccessCount_measurable (q := q) x))

theorem exponentialProductMeasure_successIndexSet_eq_real
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (s : Finset (Fin q)) :
    ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
        {sample : Fin q → ℝ |
          successIndexSet (fun y : ℝ => x < y) sample = s} =
      (Real.exp (-(lambda * x))) ^ s.card *
        (1 - Real.exp (-(lambda * x))) ^ (q - s.card) := by
  let M := exponentialDistributionModel lambda hlambda_pos
  haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
    M.isProbabilityMeasure_measure
  have hset :
      {sample : Fin q → ℝ |
          successIndexSet (fun y : ℝ => x < y) sample = s} =
        Set.pi Set.univ
          (fun i : Fin q => if i ∈ s then Set.Ioi x else Set.Iic x) := by
    ext sample
    constructor
    · intro hs i _hi
      have hiff :=
        (successIndexSet_eq_iff
          (p := fun y : ℝ => x < y) sample s).1 hs i
      by_cases his : i ∈ s
      · simp [his, hiff.2 his]
      · have hle : sample i ≤ x :=
          le_of_not_gt (fun hgt => his (hiff.1 hgt))
        simp [his, hle]
    · intro hpi
      refine (successIndexSet_eq_iff
        (p := fun y : ℝ => x < y) sample s).2 ?_
      intro i
      constructor
      · intro hgt
        by_contra his
        have hmem := hpi i trivial
        simp [his] at hmem
        linarith
      · intro his
        have hmem := hpi i trivial
        simpa [his] using hmem
  have hmeasure :
      (M.iidProductMeasure q)
          {sample : Fin q → ℝ |
            successIndexSet (fun y : ℝ => x < y) sample = s} =
        ∏ i : Fin q,
          M.measure (if i ∈ s then Set.Ioi x else Set.Iic x) := by
    rw [AppliedModelingLib.Probability.Exponential.Model.iidProductMeasure, hset,
      MeasureTheory.Measure.pi_pi]
  rw [MeasureTheory.Measure.real, hmeasure, ENNReal.toReal_prod]
  calc
    ∏ i : Fin q,
        (M.measure (if i ∈ s then Set.Ioi x else Set.Iic x)).toReal =
      ∏ i : Fin q,
        if i ∈ s then
          Real.exp (-(lambda * x))
        else
          1 - Real.exp (-(lambda * x)) := by
        refine Finset.prod_congr rfl ?_
        intro i _hi
        by_cases his : i ∈ s
        · have htail := M.measure_Ioi_toReal hx
          simpa [his, M, exponentialDistributionModel] using htail
        · have hcdf := M.measure_Iic_toReal hx
          simpa [his, M, exponentialDistributionModel] using hcdf
    _ =
      (Real.exp (-(lambda * x))) ^ s.card *
        (1 - Real.exp (-(lambda * x))) ^ (q - s.card) := by
        simpa [Finset.card_univ] using
          prod_ite_mem_eq_pow_mul_pow
            (s := s)
            (q := Real.exp (-(lambda * x)))
            (rho := 1 - Real.exp (-(lambda * x)))

theorem exponentialProductMeasure_successIndexSet_card_eq_real
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (j : ℕ) :
    ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
        {sample : Fin q → ℝ |
          (successIndexSet (fun y : ℝ => x < y) sample).card = j} =
      (Nat.choose q j : ℝ) *
        (Real.exp (-(lambda * x))) ^ j *
          (1 - Real.exp (-(lambda * x))) ^ (q - j) := by
  let M := exponentialDistributionModel lambda hlambda_pos
  haveI : MeasureTheory.IsProbabilityMeasure (M.iidProductMeasure q) :=
    M.isProbabilityMeasure_iidProductMeasure q
  let exactSets : Finset (Finset (Fin q)) :=
    (Finset.univ : Finset (Fin q)).powersetCard j
  have hcard_set :
      {sample : Fin q → ℝ |
        (successIndexSet (fun y : ℝ => x < y) sample).card = j} =
        ⋃ s ∈ exactSets,
          {sample : Fin q → ℝ |
            successIndexSet (fun y : ℝ => x < y) sample = s} := by
    ext sample
    constructor
    · intro hcard
      have hcard' :
          (successIndexSet (fun y : ℝ => x < y) sample).card = j := hcard
      refine Set.mem_iUnion.2 ⟨successIndexSet (fun y : ℝ => x < y) sample, ?_⟩
      refine Set.mem_iUnion.2 ⟨?_, rfl⟩
      exact Finset.mem_powersetCard.mpr
        ⟨by intro i _hi; simp, hcard'⟩
    · intro hmem
      rcases Set.mem_iUnion.mp hmem with ⟨s, hs_mem⟩
      rcases Set.mem_iUnion.mp hs_mem with ⟨hs_exact, hs_eq⟩
      have hs_card : s.card = j :=
        (Finset.mem_powersetCard.mp hs_exact).2
      have hs_eq' :
          successIndexSet (fun y : ℝ => x < y) sample = s := hs_eq
      change (successIndexSet (fun y : ℝ => x < y) sample).card = j
      rw [hs_eq', hs_card]
  have hdisj :
      (↑exactSets : Set (Finset (Fin q))).PairwiseDisjoint
          (fun s =>
            {sample : Fin q → ℝ |
              successIndexSet (fun y : ℝ => x < y) sample = s}) := by
      intro s _hs t _ht hne
      change Disjoint
        {sample : Fin q → ℝ |
          successIndexSet (fun y : ℝ => x < y) sample = s}
        {sample : Fin q → ℝ |
          successIndexSet (fun y : ℝ => x < y) sample = t}
      rw [Set.disjoint_left]
      intro sample hs ht
      exact hne (hs.symm.trans ht)
  have hmeas :
      ∀ s ∈ exactSets,
        MeasurableSet
          {sample : Fin q → ℝ |
            successIndexSet (fun y : ℝ => x < y) sample = s} := by
    intro s _hs
    exact exponentialSuccessIndexSet_measurableSet x s
  calc
    ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
        {sample : Fin q → ℝ |
          (successIndexSet (fun y : ℝ => x < y) sample).card = j}
        =
        (M.iidProductMeasure q).real
            (⋃ s ∈ exactSets,
              {sample : Fin q → ℝ |
                successIndexSet (fun y : ℝ => x < y) sample = s}) := by
            rw [hcard_set]
    _ =
        ∑ s ∈ exactSets,
          (M.iidProductMeasure q).real
            {sample : Fin q → ℝ |
              successIndexSet (fun y : ℝ => x < y) sample = s} :=
          MeasureTheory.measureReal_biUnion_finset hdisj hmeas
    _ =
        ∑ s ∈ exactSets,
          (Real.exp (-(lambda * x))) ^ s.card *
            (1 - Real.exp (-(lambda * x))) ^ (q - s.card) := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          exact exponentialProductMeasure_successIndexSet_eq_real
            lambda hlambda_pos x hx s
    _ =
        ∑ _s ∈ exactSets,
          (Real.exp (-(lambda * x))) ^ j *
            (1 - Real.exp (-(lambda * x))) ^ (q - j) := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          have hs_card : s.card = j :=
            (Finset.mem_powersetCard.mp hs).2
          simp [hs_card]
    _ =
      (Nat.choose q j : ℝ) *
        (Real.exp (-(lambda * x))) ^ j *
          (1 - Real.exp (-(lambda * x))) ^ (q - j) := by
        simp [exactSets, Finset.card_powersetCard, Finset.card_univ, mul_assoc]

theorem exponentialProductMeasure_successIndexSet_card_ge_real
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (r : ℕ) :
    ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
        {sample : Fin q → ℝ |
          r ≤ (successIndexSet (fun y : ℝ => x < y) sample).card} =
      ∑ j ∈ Finset.Icc r q,
        (Nat.choose q j : ℝ) *
          (Real.exp (-(lambda * x))) ^ j *
            (1 - Real.exp (-(lambda * x))) ^ (q - j) := by
  let M := exponentialDistributionModel lambda hlambda_pos
  haveI : MeasureTheory.IsProbabilityMeasure (M.iidProductMeasure q) :=
    M.isProbabilityMeasure_iidProductMeasure q
  let exactCounts : Finset ℕ := Finset.Icc r q
  have htail_set :
      {sample : Fin q → ℝ |
        r ≤ (successIndexSet (fun y : ℝ => x < y) sample).card} =
        ⋃ j ∈ exactCounts,
          {sample : Fin q → ℝ |
            (successIndexSet (fun y : ℝ => x < y) sample).card = j} := by
    ext sample
    constructor
    · intro hge
      let j := (successIndexSet (fun y : ℝ => x < y) sample).card
      have hj_le_q : j ≤ q := by
        simpa [j, Finset.card_univ] using
          (successIndexSet (fun y : ℝ => x < y) sample).card_le_univ
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      refine Set.mem_iUnion.2 ⟨?_, rfl⟩
      exact Finset.mem_Icc.mpr ⟨by simpa [j] using hge, hj_le_q⟩
    · intro hmem
      rcases Set.mem_iUnion.mp hmem with ⟨j, hj_mem⟩
      rcases Set.mem_iUnion.mp hj_mem with ⟨hj_exact, hj_eq⟩
      exact le_trans (Finset.mem_Icc.mp hj_exact).1 (by simpa using hj_eq.symm.le)
  have hdisj :
      (↑exactCounts : Set ℕ).PairwiseDisjoint
          (fun j =>
            {sample : Fin q → ℝ |
              (successIndexSet (fun y : ℝ => x < y) sample).card = j}) := by
    intro j _hj k _hk hne
    change Disjoint
      {sample : Fin q → ℝ |
        (successIndexSet (fun y : ℝ => x < y) sample).card = j}
      {sample : Fin q → ℝ |
        (successIndexSet (fun y : ℝ => x < y) sample).card = k}
    rw [Set.disjoint_left]
    intro sample hj hk
    exact hne (hj.symm.trans hk)
  have hmeas :
      ∀ j ∈ exactCounts,
        MeasurableSet
          {sample : Fin q → ℝ |
            (successIndexSet (fun y : ℝ => x < y) sample).card = j} := by
    intro j _hj
    exact exponentialSuccessIndexSet_card_measurableSet x j
  calc
    ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
        {sample : Fin q → ℝ |
          r ≤ (successIndexSet (fun y : ℝ => x < y) sample).card}
        =
        (M.iidProductMeasure q).real
          (⋃ j ∈ exactCounts,
            {sample : Fin q → ℝ |
              (successIndexSet (fun y : ℝ => x < y) sample).card = j}) := by
          rw [htail_set]
    _ =
        ∑ j ∈ exactCounts,
          (M.iidProductMeasure q).real
            {sample : Fin q → ℝ |
              (successIndexSet (fun y : ℝ => x < y) sample).card = j} :=
          MeasureTheory.measureReal_biUnion_finset hdisj hmeas
    _ =
      ∑ j ∈ exactCounts,
        (Nat.choose q j : ℝ) *
          (Real.exp (-(lambda * x))) ^ j *
            (1 - Real.exp (-(lambda * x))) ^ (q - j) := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact exponentialProductMeasure_successIndexSet_card_eq_real
          lambda hlambda_pos x hx j

theorem exponentialProductMeasure_successCount_min_integral_eq_finite_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    ∫ sample,
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∑ j ∈ Finset.Icc 0 q,
        ((min k j : ℕ) : ℝ) *
          ((Nat.choose q j : ℝ) *
            (Real.exp (-(lambda * x))) ^ j *
              (1 - Real.exp (-(lambda * x))) ^ (q - j)) := by
  let M := exponentialDistributionModel lambda hlambda_pos
  let μ := M.iidProductMeasure q
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    M.isProbabilityMeasure_iidProductMeasure q
  let exactCounts : Finset ℕ := Finset.Icc 0 q
  let countFun : (Fin q → ℝ) → ℕ :=
    fun sample => (successIndexSet (fun y : ℝ => x < y) sample).card
  let countEvent : ℕ → Set (Fin q → ℝ) :=
    fun j => {sample : Fin q → ℝ | countFun sample = j}
  have hdecomp :
      (fun sample : Fin q → ℝ => ((min k (countFun sample) : ℕ) : ℝ)) =
        fun sample : Fin q → ℝ =>
          ∑ j ∈ exactCounts,
            (countEvent j).indicator
              (fun _sample : Fin q → ℝ => ((min k j : ℕ) : ℝ)) sample := by
    funext sample
    have hcount_le_q : countFun sample ≤ q := by
      simpa [countFun, Finset.card_univ] using
        (successIndexSet (fun y : ℝ => x < y) sample).card_le_univ
    have hcount_mem : countFun sample ∈ exactCounts :=
      Finset.mem_Icc.mpr ⟨Nat.zero_le _, hcount_le_q⟩
    rw [Finset.sum_eq_single_of_mem (a := countFun sample) hcount_mem]
    · simp [countEvent]
    · intro j _hj hj_ne
      have hnot : sample ∉ countEvent j := by
        intro hj
        exact hj_ne (by simpa [countEvent] using hj.symm)
      simp [hnot]
  calc
    ∫ sample,
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
        ∫ sample, ((min k (countFun sample) : ℕ) : ℝ) ∂μ := by
          simp [M, μ, countFun]
    _ =
        ∫ sample,
          ∑ j ∈ exactCounts,
            (countEvent j).indicator
              (fun _sample : Fin q → ℝ => ((min k j : ℕ) : ℝ)) sample
            ∂μ := by
          rw [hdecomp]
    _ =
        ∑ j ∈ exactCounts,
          ∫ sample,
            (countEvent j).indicator
              (fun _sample : Fin q → ℝ => ((min k j : ℕ) : ℝ)) sample
            ∂μ :=
          MeasureTheory.integral_finset_sum exactCounts
            (fun j _hj =>
              (MeasureTheory.integrable_const (((min k j : ℕ) : ℝ))).indicator
                (by
                  simpa [countEvent, countFun] using
                    exponentialSuccessIndexSet_card_measurableSet
                      (q := q) x j))
    _ =
        ∑ j ∈ exactCounts,
          ((min k j : ℕ) : ℝ) *
            (μ.real
              {sample : Fin q → ℝ |
                (successIndexSet (fun y : ℝ => x < y) sample).card = j}) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [MeasureTheory.integral_indicator_const]
          · simp [countEvent, countFun, mul_comm]
          · simpa [countEvent, countFun] using
              exponentialSuccessIndexSet_card_measurableSet (q := q) x j
    _ =
      ∑ j ∈ Finset.Icc 0 q,
        ((min k j : ℕ) : ℝ) *
          ((Nat.choose q j : ℝ) *
            (Real.exp (-(lambda * x))) ^ j *
              (1 - Real.exp (-(lambda * x))) ^ (q - j)) := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        rw [exponentialProductMeasure_successIndexSet_card_eq_real
          lambda hlambda_pos x hx j]

theorem exponentialProductMeasure_successCount_min_integral_eq_tail_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (k : ℕ) :
    ∫ sample,
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∑ r ∈ Finset.Icc 1 k,
        ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
          {sample : Fin q → ℝ |
            r ≤ (successIndexSet (fun y : ℝ => x < y) sample).card} := by
  let M := exponentialDistributionModel lambda hlambda_pos
  let μ := M.iidProductMeasure q
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    M.isProbabilityMeasure_iidProductMeasure q
  let countFun : (Fin q → ℝ) → ℕ :=
    fun sample => (successIndexSet (fun y : ℝ => x < y) sample).card
  let tailEvent : ℕ → Set (Fin q → ℝ) :=
    fun r => {sample : Fin q → ℝ | r ≤ countFun sample}
  have hdecomp :
      (fun sample : Fin q → ℝ => ((min k (countFun sample) : ℕ) : ℝ)) =
        fun sample : Fin q → ℝ =>
          ∑ r ∈ Finset.Icc 1 k,
            (tailEvent r).indicator
              (fun _sample : Fin q → ℝ => (1 : ℝ)) sample := by
    funext sample
    rw [nat_min_eq_sum_tail_indicators_real k (countFun sample)]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    by_cases hr_le : r ≤ countFun sample
    · simp [tailEvent, hr_le]
    · simp [tailEvent, hr_le]
  calc
    ∫ sample,
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
        ∫ sample, ((min k (countFun sample) : ℕ) : ℝ) ∂μ := by
          simp [M, μ, countFun]
    _ =
        ∫ sample,
          ∑ r ∈ Finset.Icc 1 k,
            (tailEvent r).indicator
              (fun _sample : Fin q → ℝ => (1 : ℝ)) sample
          ∂μ := by
          rw [hdecomp]
    _ =
        ∑ r ∈ Finset.Icc 1 k,
          ∫ sample,
            (tailEvent r).indicator
              (fun _sample : Fin q → ℝ => (1 : ℝ)) sample
          ∂μ :=
          MeasureTheory.integral_finset_sum (Finset.Icc 1 k)
            (fun r _hr =>
              (MeasureTheory.integrable_const (1 : ℝ)).indicator
                (by
                  simpa [tailEvent, countFun] using
                    exponentialSuccessIndexSet_card_ge_measurableSet
                      (q := q) x r))
    _ =
        ∑ r ∈ Finset.Icc 1 k,
          μ.real (tailEvent r) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          rw [MeasureTheory.integral_indicator_const]
          · simp [tailEvent, mul_comm]
          · simpa [tailEvent, countFun] using
              exponentialSuccessIndexSet_card_ge_measurableSet
                (q := q) x r
    _ =
      ∑ r ∈ Finset.Icc 1 k,
        ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
          {sample : Fin q → ℝ |
            r ≤ (successIndexSet (fun y : ℝ => x < y) sample).card} := by
        simp [M, μ, tailEvent, countFun]

theorem exponentialProductMeasure_successCount_min_integral_eq_tail_binomial_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    ∫ sample,
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∑ r ∈ Finset.Icc 1 k,
        ∑ j ∈ Finset.Icc r q,
          (Nat.choose q j : ℝ) *
            (Real.exp (-(lambda * x))) ^ j *
              (1 - Real.exp (-(lambda * x))) ^ (q - j) := by
  rw [exponentialProductMeasure_successCount_min_integral_eq_tail_sum
    lambda hlambda_pos x k]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  exact exponentialProductMeasure_successIndexSet_card_ge_real
    lambda hlambda_pos x hx r

theorem exponentialBinomialMass_integral_eq_alternating_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q j : ℕ} (hj_pos : 0 < j) (hjq : j ≤ q) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Nat.choose q j : ℝ) *
          (Real.exp (-(lambda * x))) ^ j *
            (1 - Real.exp (-(lambda * x))) ^ (q - j) =
      (Nat.choose q j : ℝ) *
        ∑ m ∈ Finset.range (q - j + 1),
          ((-1 : ℝ) ^ (m + (q - j)) *
            ((q - j).choose m : ℝ)) *
            (1 / (((q - m : ℕ) : ℝ) * lambda)) := by
  let n := q - j
  let c : ℝ := (Nat.choose q j : ℝ)
  let e : ℝ → ℝ := fun x => Real.exp (-(lambda * x))
  have hcongr :
      ∫ x in Set.Ioi (0 : ℝ),
          c * e x ^ j * (1 - e x) ^ n =
        ∫ x in Set.Ioi (0 : ℝ),
          ∑ m ∈ Finset.range (n + 1),
            (c * ((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ))) *
              (e x ^ j * e x ^ (n - m)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _hx
    dsimp
    rw [sub_pow]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m _hm
    ring
  rw [show q - j = n by rfl]
  rw [hcongr]
  rw [MeasureTheory.integral_finset_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hm_le_n : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hqm_pos : 0 < q - m := by
      omega
    have hpow :
        ∀ x : ℝ, e x ^ j * e x ^ (n - m) = e x ^ (q - m) := by
      intro x
      rw [← pow_add]
      congr 1
      omega
    calc
      ∫ x in Set.Ioi (0 : ℝ),
          (c * ((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ))) *
            (e x ^ j * e x ^ (n - m)) =
          ∫ x in Set.Ioi (0 : ℝ),
            (c * ((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ))) *
              e x ^ (q - m) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
            intro x _hx
            dsimp
            rw [hpow x]
      _ =
          (c * ((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ))) *
            ∫ x in Set.Ioi (0 : ℝ), e x ^ (q - m) := by
            rw [MeasureTheory.integral_const_mul]
      _ =
          (c * ((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ))) *
            (1 / (((q - m : ℕ) : ℝ) * lambda)) := by
            rw [AppliedModelingLib.Probability.Exponential.integral_exp_neg_mul_pow_Ioi
              lambda hlambda_pos hqm_pos]
      _ =
          c *
            (((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ)) *
              (1 / (((q - m : ℕ) : ℝ) * lambda))) := by
            ring
  · intro m hm
    have hm_le_n : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hqm_pos : 0 < q - m := by
      omega
    have hbase :
        MeasureTheory.Integrable
          (fun x : ℝ => e x ^ (q - m))
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      simpa [e] using
        AppliedModelingLib.Probability.Exponential.integrableOn_exp_neg_mul_pow_Ioi
          lambda hlambda_pos hqm_pos
    have hterm :
        MeasureTheory.Integrable
          (fun x : ℝ =>
            (c * ((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ))) *
              e x ^ (q - m))
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      hbase.const_mul _
    refine hterm.congr ?_
    filter_upwards with x
    have hpow : e x ^ j * e x ^ (n - m) = e x ^ (q - m) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]

theorem alternating_choose_div_add_eq_inv_mul_choose
    (n : ℕ) {j : ℕ} (hj_pos : 0 < j) :
    (∑ t ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ t * (n.choose t : ℝ)) /
          (((j + t : ℕ) : ℝ))) =
      1 / (((j : ℕ) : ℝ) * ((n + j).choose n : ℝ)) := by
  induction n generalizing j with
  | zero =>
      simp
  | succ n ih =>
      have hrec :
          (∑ t ∈ Finset.range (n + 2),
              ((-1 : ℝ) ^ t * ((n + 1).choose t : ℝ)) /
                (((j + t : ℕ) : ℝ))) =
            (∑ t ∈ Finset.range (n + 1),
              ((-1 : ℝ) ^ t * (n.choose t : ℝ)) /
                (((j + t : ℕ) : ℝ))) -
            (∑ t ∈ Finset.range (n + 1),
              ((-1 : ℝ) ^ t * (n.choose t : ℝ)) /
                ((((j + 1) + t : ℕ) : ℝ))) := by
        rw [Finset.sum_range_succ']
        have htail :
            (∑ t ∈ Finset.range (n + 1),
                ((-1 : ℝ) ^ (t + 1) *
                    ((n + 1).choose (t + 1) : ℝ)) /
                  (((j + (t + 1) : ℕ) : ℝ))) =
              (∑ t ∈ Finset.range (n + 1),
                ((-1 : ℝ) ^ (t + 1) * (n.choose t : ℝ)) /
                  (((j + (t + 1) : ℕ) : ℝ))) +
              (∑ t ∈ Finset.range (n + 1),
                ((-1 : ℝ) ^ (t + 1) * (n.choose (t + 1) : ℝ)) /
                  (((j + (t + 1) : ℕ) : ℝ))) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro t _ht
          rw [Nat.choose_succ_succ]
          norm_num
          ring
        rw [htail]
        have hfirst :
            (∑ t ∈ Finset.range (n + 1),
                ((-1 : ℝ) ^ t * (n.choose t : ℝ)) /
                  (((j + t : ℕ) : ℝ))) =
              1 / ((j : ℝ)) +
                (∑ t ∈ Finset.range (n + 1),
                  ((-1 : ℝ) ^ (t + 1) * (n.choose (t + 1) : ℝ)) /
                    (((j + (t + 1) : ℕ) : ℝ))) := by
          rw [Finset.sum_range_succ']
          rw [Finset.sum_range_succ]
          simp
          ring_nf
        rw [hfirst]
        have hden :
            (∑ t ∈ Finset.range (n + 1),
                ((-1 : ℝ) ^ t * (n.choose t : ℝ)) /
                  ((((j + 1) + t : ℕ) : ℝ))) =
              (∑ t ∈ Finset.range (n + 1),
                ((-1 : ℝ) ^ t * (n.choose t : ℝ)) /
                  (((j + (t + 1) : ℕ) : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro t _ht
          have hnat : (j + 1) + t = j + (t + 1) := by omega
          simpa [hnat]
        rw [hden]
        have hneg :
            (∑ t ∈ Finset.range (n + 1),
                ((-1 : ℝ) ^ (t + 1) * (n.choose t : ℝ)) /
                  (((j + (t + 1) : ℕ) : ℝ))) =
              - (∑ t ∈ Finset.range (n + 1),
                ((-1 : ℝ) ^ t * (n.choose t : ℝ)) /
                  (((j + (t + 1) : ℕ) : ℝ))) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro t _ht
          rw [pow_succ]
          ring
        rw [hneg]
        simp [Nat.choose_zero_right]
        abel
      rw [hrec, ih hj_pos, ih (Nat.succ_pos j)]
      have hC0_pos : 0 < (((n + j).choose n : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega : n ≤ n + j)
      have hB_pos : 0 < (((n + j + 1).choose n : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega : n ≤ n + j + 1)
      have hD_pos : 0 < (((n + j + 1).choose (n + 1) : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega : n + 1 ≤ n + j + 1)
      have hj_ne : ((j : ℕ) : ℝ) ≠ 0 := by positivity
      have hjs_ne : (((j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hC0_ne : (((n + j).choose n : ℕ) : ℝ) ≠ 0 := ne_of_gt hC0_pos
      have hB_ne : (((n + j + 1).choose n : ℕ) : ℝ) ≠ 0 := ne_of_gt hB_pos
      have hD_ne : (((n + j + 1).choose (n + 1) : ℕ) : ℝ) ≠ 0 :=
        ne_of_gt hD_pos
      have hchoose_right :
          (((n + j).choose n : ℕ) : ℝ) * (((n + j + 1 : ℕ) : ℝ)) =
            (((n + j + 1).choose n : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ)) := by
        have hnat := Nat.choose_mul_succ_eq (n + j) n
        have hsub : n + j + 1 - n = j + 1 := by omega
        exact_mod_cast (by simpa [hsub] using hnat)
      have hchoose_succ :
          (((n + j + 1 : ℕ) : ℝ)) * (((n + j).choose n : ℕ) : ℝ) =
            (((n + j + 1).choose (n + 1) : ℕ) : ℝ) *
              (((n + 1 : ℕ) : ℝ)) := by
        have hnat := Nat.add_one_mul_choose_eq (n + j) n
        exact_mod_cast hnat
      have hC1_eq :
          (((n + (j + 1)).choose n : ℕ) : ℝ) =
            (((n + j + 1).choose n : ℕ) : ℝ) := by
        congr 2
      have hC2_eq :
          ((((n + 1) + j).choose (n + 1) : ℕ) : ℝ) =
            (((n + j + 1).choose (n + 1) : ℕ) : ℝ) := by
        congr 2
        omega
      rw [hC1_eq, hC2_eq]
      have hN_ne : (((n + j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hn1_ne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hBden :
          (((j + 1 : ℕ) : ℝ) * (((n + j + 1).choose n : ℕ) : ℝ)) =
            (((n + j).choose n : ℕ) : ℝ) *
              (((n + j + 1 : ℕ) : ℝ)) := by
        rw [mul_comm]
        exact hchoose_right.symm
      have hDden :
          (((n + j + 1).choose (n + 1) : ℕ) : ℝ) *
              (((n + 1 : ℕ) : ℝ)) =
            (((n + j + 1 : ℕ) : ℝ)) *
              (((n + j).choose n : ℕ) : ℝ) :=
        hchoose_succ.symm
      have hN_sub :
          (((n + j + 1 : ℕ) : ℝ)) - ((j : ℕ) : ℝ) =
            (((n + 1 : ℕ) : ℝ)) := by
        norm_num
        ring
      calc
        1 / (((j : ℕ) : ℝ) * (((n + j).choose n : ℕ) : ℝ)) -
            1 / (((j + 1 : ℕ) : ℝ) *
              (((n + j + 1).choose n : ℕ) : ℝ)) =
          1 / (((j : ℕ) : ℝ) * (((n + j).choose n : ℕ) : ℝ)) -
            1 / ((((n + j).choose n : ℕ) : ℝ) *
              (((n + j + 1 : ℕ) : ℝ))) := by
            rw [hBden]
        _ =
            (((n + 1 : ℕ) : ℝ)) /
              (((j : ℕ) : ℝ) * (((n + j).choose n : ℕ) : ℝ) *
                (((n + j + 1 : ℕ) : ℝ))) := by
            field_simp [hj_ne, hC0_ne, hN_ne]
            nlinarith
        _ =
            1 / (((j : ℕ) : ℝ) *
              (((n + j + 1).choose (n + 1) : ℕ) : ℝ)) := by
            field_simp [hj_ne, hC0_ne, hD_ne, hN_ne, hn1_ne]
            nlinarith [hDden]

theorem alternating_choose_reverse_div_add_eq_inv_mul_choose
    (n : ℕ) {j : ℕ} (hj_pos : 0 < j) :
    (∑ m ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ)) /
          (((j + (n - m) : ℕ) : ℝ))) =
      1 / (((j : ℕ) : ℝ) * ((n + j).choose n : ℝ)) := by
  let f : ℕ → ℝ := fun t =>
    ((-1 : ℝ) ^ t * (n.choose t : ℝ)) /
      (((j + t : ℕ) : ℝ))
  calc
    (∑ m ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ)) /
          (((j + (n - m) : ℕ) : ℝ))) =
        ∑ m ∈ Finset.range (n + 1), f (n - m) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          have hm_le : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
          have hpow :
              (-1 : ℝ) ^ (m + n) = (-1 : ℝ) ^ (n - m) := by
            rw [show m + n = (n - m) + 2 * m by omega]
            rw [pow_add, pow_mul]
            norm_num
          have hchoose :
              ((n.choose (n - m) : ℕ) : ℝ) =
                ((n.choose m : ℕ) : ℝ) := by
            exact_mod_cast Nat.choose_symm hm_le
          simp [f, hpow, hchoose]
    _ = ∑ t ∈ Finset.range (n + 1), f t := by
          simpa using Finset.sum_range_reflect f (n + 1)
    _ = 1 / (((j : ℕ) : ℝ) * ((n + j).choose n : ℝ)) := by
          simpa [f] using alternating_choose_div_add_eq_inv_mul_choose
            n hj_pos

theorem exponentialBinomialMass_integral_eq_inv_lambda_mul_inv
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q j : ℕ} (hj_pos : 0 < j) (hjq : j ≤ q) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Nat.choose q j : ℝ) *
          (Real.exp (-(lambda * x))) ^ j *
            (1 - Real.exp (-(lambda * x))) ^ (q - j) =
      (1 / lambda) * (1 / ((j : ℕ) : ℝ)) := by
  rw [exponentialBinomialMass_integral_eq_alternating_sum
    lambda hlambda_pos hj_pos hjq]
  have hj_ne : ((j : ℕ) : ℝ) ≠ 0 := by positivity
  have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda_pos
  have hchoose_pos : 0 < ((Nat.choose q j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos hjq
  have hchoose_ne : ((Nat.choose q j : ℕ) : ℝ) ≠ 0 := ne_of_gt hchoose_pos
  have hsum :
      (∑ m ∈ Finset.range (q - j + 1),
          ((-1 : ℝ) ^ (m + (q - j)) * ((q - j).choose m : ℝ)) *
            (1 / (((q - m : ℕ) : ℝ) * lambda))) =
        (1 / lambda) *
          (∑ m ∈ Finset.range (q - j + 1),
            ((-1 : ℝ) ^ (m + (q - j)) * ((q - j).choose m : ℝ)) /
              (((j + ((q - j) - m) : ℕ) : ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hm_le : m ≤ q - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hden_nat : q - m = j + ((q - j) - m) := by omega
    have hden_ne :
        (((j + ((q - j) - m) : ℕ) : ℝ)) ≠ 0 := by positivity
    rw [hden_nat]
    field_simp [hlambda_ne, hden_ne]
  rw [hsum]
  have halt :
      (∑ m ∈ Finset.range (q - j + 1),
        ((-1 : ℝ) ^ (m + (q - j)) * ((q - j).choose m : ℝ)) /
          (((j + ((q - j) - m) : ℕ) : ℝ))) =
        1 / (((j : ℕ) : ℝ) * ((Nat.choose q j : ℕ) : ℝ)) := by
    have hbase :=
      alternating_choose_reverse_div_add_eq_inv_mul_choose
        (q - j) (j := j) hj_pos
    have hchoose_symm :
        Nat.choose ((q - j) + j) (q - j) = Nat.choose q j := by
      rw [Nat.sub_add_cancel hjq]
      exact Nat.choose_symm hjq
    simpa [hchoose_symm] using hbase
  rw [halt]
  field_simp [hj_ne, hchoose_ne]

theorem exponentialBinomialMass_integrable_Ioi
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q j : ℕ} (hj_pos : 0 < j) (hjq : j ≤ q) :
    MeasureTheory.Integrable
      (fun x : ℝ =>
        (Nat.choose q j : ℝ) *
          (Real.exp (-(lambda * x))) ^ j *
            (1 - Real.exp (-(lambda * x))) ^ (q - j))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  let n := q - j
  let c : ℝ := (Nat.choose q j : ℝ)
  let e : ℝ → ℝ := fun x => Real.exp (-(lambda * x))
  have hpoint :
      ∀ x : ℝ,
        c * e x ^ j * (1 - e x) ^ n =
          ∑ m ∈ Finset.range (n + 1),
            (c * ((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ))) *
              e x ^ (q - m) := by
    intro x
    rw [sub_pow]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hm_le_n : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hpow : e x ^ j * e x ^ (n - m) = e x ^ (q - m) := by
      rw [← pow_add]
      congr 1
      dsimp [n]
      omega
    calc
      c * e x ^ j *
          ((-1 : ℝ) ^ (m + n) * 1 ^ m * e x ^ (n - m) *
            (n.choose m : ℝ)) =
        (c * ((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ))) *
          (e x ^ j * e x ^ (n - m)) := by
          ring
      _ =
        (c * ((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ))) *
          e x ^ (q - m) := by
          rw [hpow]
  have hsum_integrable :
      MeasureTheory.Integrable
        (fun x : ℝ =>
          ∑ m ∈ Finset.range (n + 1),
            (c * ((-1 : ℝ) ^ (m + n) * (n.choose m : ℝ))) *
              e x ^ (q - m))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine MeasureTheory.integrable_finset_sum (Finset.range (n + 1)) ?_
    intro m hm
    have hm_le_n : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hqm_pos : 0 < q - m := by
      dsimp [n] at hm_le_n
      omega
    have hbase :
        MeasureTheory.Integrable
          (fun x : ℝ => e x ^ (q - m))
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      simpa [e] using
        AppliedModelingLib.Probability.Exponential.integrableOn_exp_neg_mul_pow_Ioi
          lambda hlambda_pos hqm_pos
    exact hbase.const_mul _
  refine hsum_integrable.congr ?_
  filter_upwards with x
  dsimp [c, e, n]
  exact (hpoint x).symm

theorem integral_Ioi_indicator_lt_eq
    (a : ℝ) (ha : 0 ≤ a) :
    ∫ x in Set.Ioi (0 : ℝ), (if x < a then (1 : ℝ) else 0) = a := by
  have hindicator :
      (fun x : ℝ => if x < a then (1 : ℝ) else 0) =
        (Set.Iio a).indicator (fun _x : ℝ => (1 : ℝ)) := by
    funext x
    by_cases hx : x < a <;> simp [hx]
  rw [hindicator, MeasureTheory.setIntegral_indicator measurableSet_Iio]
  have hset : Set.Ioi (0 : ℝ) ∩ Set.Iio a = Set.Ioo (0 : ℝ) a := by
    ext x
    simp [and_comm]
  rw [hset, MeasureTheory.setIntegral_const]
  simp [Real.volume_real_Ioo_of_le ha]

theorem thresholdIndicator_integrable_Ioi (a : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => if x < a then (1 : ℝ) else 0)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hindicator :
      (fun x : ℝ => if x < a then (1 : ℝ) else 0) =
        (Set.Iio a).indicator (fun _x : ℝ => (1 : ℝ)) := by
    funext x
    by_cases hx : x < a <;> simp [hx]
  rw [hindicator]
  have hfinite :
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) (Set.Iio a) ≠ ⊤ := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iio]
    have hset : Set.Iio a ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) a := by
      ext x
      simp [and_comm]
    rw [hset, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  exact (MeasureTheory.integrableOn_const
    (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (s := Set.Iio a) (C := (1 : ℝ)) hfinite).integrable_indicator
      measurableSet_Iio

theorem successCount_real_eq_sum_indicators
    {ι : Type*} [Fintype ι] (sample : ι → ℝ) (x : ℝ) :
    ((successIndexSet (fun y : ℝ => x < y) sample).card : ℝ) =
      ∑ i : ι, if x < sample i then (1 : ℝ) else 0 := by
  classical
  unfold successIndexSet
  calc
    (((Finset.univ.filter (fun i : ι => x < sample i)).card : ℕ) : ℝ)
        = ∑ i ∈ Finset.univ.filter (fun i : ι => x < sample i),
            (1 : ℝ) := by
          simp
    _ = ∑ i : ι, if x < sample i then (1 : ℝ) else 0 := by
          rw [Finset.sum_filter]

theorem successCount_real_measurable_fintype
    {ι : Type*} [Fintype ι] (sample : ι → ℝ) :
    Measurable
      (fun x : ℝ =>
        ((successIndexSet (fun y : ℝ => x < y) sample).card : ℝ)) := by
  classical
  have hsum_meas :
      Measurable
        (fun x : ℝ => ∑ i : ι, if x < sample i then (1 : ℝ) else 0) := by
    refine Finset.measurable_sum (s := (Finset.univ : Finset ι)) ?_
    intro i _hi
    have hindicator :
        (fun x : ℝ => if x < sample i then (1 : ℝ) else 0) =
          (Set.Iio (sample i)).indicator (fun _x : ℝ => (1 : ℝ)) := by
      funext x
      by_cases hx : x < sample i <;> simp [hx]
    rw [hindicator]
    exact measurable_const.indicator measurableSet_Iio
  convert hsum_meas using 1
  ext x
  exact successCount_real_eq_sum_indicators sample x

theorem successCount_integrable_fintype
    {ι : Type*} [Fintype ι] (sample : ι → ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ =>
        ((successIndexSet (fun y : ℝ => x < y) sample).card : ℝ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  classical
  have hsum_int :
      MeasureTheory.Integrable
        (fun x : ℝ => ∑ i : ι, if x < sample i then (1 : ℝ) else 0)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    MeasureTheory.integrable_finset_sum
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (Finset.univ : Finset ι)
      (fun i _hi => thresholdIndicator_integrable_Ioi (sample i))
  exact hsum_int.congr
    (Filter.Eventually.of_forall
      (fun x => (successCount_real_eq_sum_indicators sample x).symm))

theorem successCount_min_real_measurable_fintype
    {ι : Type*} [Fintype ι] (k : ℕ) (sample : ι → ℝ) :
    Measurable
      (fun x : ℝ =>
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)) := by
  have hcount :=
    successCount_real_measurable_fintype (sample := sample)
  have hmin :
      Measurable
        (fun x : ℝ =>
          min (k : ℝ)
            ((successIndexSet (fun y : ℝ => x < y) sample).card : ℝ)) :=
    measurable_const.min hcount
  convert hmin using 1
  ext x
  rw [Nat.cast_min]

theorem successCount_min_integrable_fintype
    {ι : Type*} [Fintype ι] (k : ℕ) (sample : ι → ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ =>
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  let countFun : ℝ → ℝ :=
    fun x => ((successIndexSet (fun y : ℝ => x < y) sample).card : ℝ)
  have hcount_int :
      MeasureTheory.Integrable countFun
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [countFun] using successCount_integrable_fintype (sample := sample)
  have hmin_aestrong :
      MeasureTheory.AEStronglyMeasurable
        (fun x : ℝ =>
          ((min k
            (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (successCount_min_real_measurable_fintype
      (k := k) (sample := sample)).aestronglyMeasurable
  exact hcount_int.mono_nonneg hmin_aestrong
    (Filter.Eventually.of_forall (fun x => by
      exact_mod_cast Nat.zero_le
        (min k (successIndexSet (fun y : ℝ => x < y) sample).card)))
    (Filter.Eventually.of_forall (fun x => by
      dsimp [countFun]
      exact_mod_cast min_le_right k
        (successIndexSet (fun y : ℝ => x < y) sample).card))

theorem successCount_min_real_measurable_prod
    {q : ℕ} (k : ℕ) :
    Measurable
      (fun z : (Fin q → ℝ) × ℝ =>
        ((min k
          (successIndexSet (fun y : ℝ => z.2 < y) z.1).card : ℕ) : ℝ)) := by
  classical
  have hcount_sum :
      (fun z : (Fin q → ℝ) × ℝ =>
        ((successIndexSet (fun y : ℝ => z.2 < y) z.1).card : ℝ)) =
        fun z : (Fin q → ℝ) × ℝ =>
          ∑ i : Fin q, if z.2 < z.1 i then (1 : ℝ) else 0 := by
    funext z
    exact successCount_real_eq_sum_indicators z.1 z.2
  have hcount_meas :
      Measurable
        (fun z : (Fin q → ℝ) × ℝ =>
          ((successIndexSet (fun y : ℝ => z.2 < y) z.1).card : ℝ)) := by
    have hsum_meas :
        Measurable
          (fun z : (Fin q → ℝ) × ℝ =>
            ∑ i : Fin q, if z.2 < z.1 i then (1 : ℝ) else 0) := by
      refine Finset.measurable_sum (s := (Finset.univ : Finset (Fin q))) ?_
      intro i _hi
      have hset :
          MeasurableSet
            {z : (Fin q → ℝ) × ℝ | z.2 < z.1 i} :=
        measurableSet_lt measurable_snd
          ((measurable_pi_apply (X := fun _ : Fin q => ℝ) i).comp
            measurable_fst)
      have hindicator :
          (fun z : (Fin q → ℝ) × ℝ =>
            if z.2 < z.1 i then (1 : ℝ) else 0) =
            {z : (Fin q → ℝ) × ℝ | z.2 < z.1 i}.indicator
              (fun _z : (Fin q → ℝ) × ℝ => (1 : ℝ)) := by
        funext z
        by_cases hz : z.2 < z.1 i <;> simp [hz]
      rw [hindicator]
      exact measurable_const.indicator hset
    convert hsum_meas using 1
  have hmin :
      Measurable
        (fun z : (Fin q → ℝ) × ℝ =>
          min (k : ℝ)
            ((successIndexSet (fun y : ℝ => z.2 < y) z.1).card : ℝ)) :=
    measurable_const.min hcount_meas
  convert hmin using 1
  ext z
  rw [Nat.cast_min]

theorem successCount_integral_eq_sum_fintype
    {ι : Type*} [Fintype ι] (sample : ι → ℝ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    ∫ x in Set.Ioi (0 : ℝ),
        ((successIndexSet (fun y : ℝ => x < y) sample).card : ℝ) =
      ∑ i : ι, sample i := by
  classical
  have hcount :
      ∀ x : ℝ,
        ((successIndexSet (fun y : ℝ => x < y) sample).card : ℝ) =
          ∑ i : ι, if x < sample i then (1 : ℝ) else 0 := by
    intro x
    exact successCount_real_eq_sum_indicators sample x
  have h_integrable :
      ∀ i ∈ (Finset.univ : Finset ι),
        MeasureTheory.Integrable
          (fun x : ℝ => if x < sample i then (1 : ℝ) else 0)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro i _hi
    exact thresholdIndicator_integrable_Ioi (sample i)
  calc
    ∫ x in Set.Ioi (0 : ℝ),
        ((successIndexSet (fun y : ℝ => x < y) sample).card : ℝ)
        =
        ∫ x in Set.Ioi (0 : ℝ),
          ∑ i : ι, if x < sample i then (1 : ℝ) else 0 := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x _hx
          exact hcount x
    _ =
        ∑ i : ι,
          ∫ x in Set.Ioi (0 : ℝ),
            (if x < sample i then (1 : ℝ) else 0) :=
          MeasureTheory.integral_finset_sum
            (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (Finset.univ : Finset ι) h_integrable
    _ = ∑ i : ι, sample i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact integral_Ioi_indicator_lt_eq (sample i) (h_nonneg i)

theorem successCount_integral_eq_sum
    {q : ℕ} (sample : Fin q → ℝ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    ∫ x in Set.Ioi (0 : ℝ),
        ((successIndexSet (fun y : ℝ => x < y) sample).card : ℝ) =
      ∑ i : Fin q, sample i := by
  simpa using successCount_integral_eq_sum_fintype
    (sample := sample) h_nonneg

theorem successCount_subtype_card_le_min_successCount
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (s : Finset (Fin q)) (hs_card : s.card ≤ k) (x : ℝ) :
    (successIndexSet
      (fun y : ℝ => x < y)
      (fun i : {i : Fin q // i ∈ s} => sample i)).card ≤
        min k (successIndexSet (fun y : ℝ => x < y) sample).card := by
  classical
  let subCount : Finset {i : Fin q // i ∈ s} :=
    successIndexSet
      (fun y : ℝ => x < y)
      (fun i : {i : Fin q // i ∈ s} => sample i)
  let allCount : Finset (Fin q) :=
    successIndexSet (fun y : ℝ => x < y) sample
  have hsub_le_all : subCount.card ≤ allCount.card := by
    refine Finset.card_le_card_of_injOn
      (fun i : {i : Fin q // i ∈ s} => (i : Fin q)) ?_ ?_
    · intro i hi
      simpa [subCount, allCount, successIndexSet] using hi
    · intro i _hi j _hj hij
      exact Subtype.ext hij
  have hsub_le_s : subCount.card ≤ s.card := by
    have hsub_le_univ :
        subCount.card ≤ Fintype.card {i : Fin q // i ∈ s} := by
      simpa [Finset.card_univ] using subCount.card_le_univ
    have hcard_subtype :
        Fintype.card {i : Fin q // i ∈ s} = s.card := by
      simpa using (Fintype.card_coe s)
    simpa [hcard_subtype] using hsub_le_univ
  simpa [subCount, allCount] using
    le_min (le_trans hsub_le_s hs_card) hsub_le_all

theorem successCount_subtype_real_le_min_successCount
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (s : Finset (Fin q)) (hs_card : s.card ≤ k) (x : ℝ) :
    ((successIndexSet
      (fun y : ℝ => x < y)
      (fun i : {i : Fin q // i ∈ s} => sample i)).card : ℝ) ≤
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ) :=
  by
  exact_mod_cast
    successCount_subtype_card_le_min_successCount
      k sample s hs_card x

theorem finset_sum_le_integral_min_successCount
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (s : Finset (Fin q)) (hs_card : s.card ≤ k)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    (∑ i ∈ s, sample i) ≤
      ∫ x in Set.Ioi (0 : ℝ),
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ) := by
  classical
  let subSample : {i : Fin q // i ∈ s} → ℝ := fun i => sample i
  let subCountFun : ℝ → ℝ :=
    fun x =>
      ((successIndexSet (fun y : ℝ => x < y) subSample).card : ℝ)
  let minCountFun : ℝ → ℝ :=
    fun x =>
      ((min k
        (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
  have hsub_int :
      MeasureTheory.Integrable subCountFun
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [subCountFun, subSample] using
      successCount_integrable_fintype (sample := subSample)
  have hmin_int :
      MeasureTheory.Integrable minCountFun
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [minCountFun] using
      successCount_min_integrable_fintype (k := k) (sample := sample)
  have hmono :
      ∫ x, subCountFun x
          ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) ≤
        ∫ x, minCountFun x
          ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.integral_mono hsub_int hmin_int ?_
    intro x
    simpa [subCountFun, minCountFun, subSample] using
      successCount_subtype_real_le_min_successCount
        k sample s hs_card x
  have hsub_layer :
      ∫ x in Set.Ioi (0 : ℝ), subCountFun x =
        ∑ i : {i : Fin q // i ∈ s}, sample i := by
    simpa [subCountFun, subSample] using
      successCount_integral_eq_sum_fintype
        (sample := subSample)
        (fun i : {i : Fin q // i ∈ s} => h_nonneg i)
  have hsum_subtype :
      (∑ i : {i : Fin q // i ∈ s}, sample i) =
        ∑ i ∈ s, sample i := by
    simpa using
      (Finset.sum_coe_sort
        (s := s) (f := fun i : Fin q => sample i))
  calc
    (∑ i ∈ s, sample i) =
        ∑ i : {i : Fin q // i ∈ s}, sample i := hsum_subtype.symm
    _ = ∫ x in Set.Ioi (0 : ℝ), subCountFun x := hsub_layer.symm
    _ ≤ ∫ x in Set.Ioi (0 : ℝ), minCountFun x := hmono
    _ =
      ∫ x in Set.Ioi (0 : ℝ),
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ) := by
        rfl

theorem exponentialFiniteSampleTopKSum_le_integral_min_successCount
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    exponentialFiniteSampleTopKSum k sample ≤
      ∫ x in Set.Ioi (0 : ℝ),
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ) := by
  classical
  unfold exponentialFiniteSampleTopKSum topKSumOn
  refine Finset.sup'_le (topKCandidateSets_nonempty (Fin q) k)
    (fun s => ∑ i ∈ s, sample i) ?_
  intro s hs
  have hs_card : s.card ≤ k := by
    simpa [topKCandidateSets] using hs
  exact finset_sum_le_integral_min_successCount
    k sample s hs_card h_nonneg

theorem exponentialFiniteSampleTopKSum_exists_maximizer
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ) :
    ∃ s : Finset (Fin q),
      s.card ≤ k ∧
        exponentialFiniteSampleTopKSum k sample = ∑ i ∈ s, sample i := by
  classical
  obtain ⟨s, hs_mem, hs_eq⟩ :=
    Finset.exists_mem_eq_sup'
      (s := topKCandidateSets (Fin q) k)
      (H := topKCandidateSets_nonempty (Fin q) k)
      (f := fun s => ∑ i ∈ s, sample i)
  have hs_card : s.card ≤ k := by
    simpa [topKCandidateSets] using hs_mem
  refine ⟨s, hs_card, ?_⟩
  unfold exponentialFiniteSampleTopKSum topKSumOn
  exact hs_eq

theorem exponentialFiniteSampleTopKSum_maximizer_missing_nonpos_of_card_lt
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (s : Finset (Fin q)) (hs_card : s.card ≤ k)
    (hmax : exponentialFiniteSampleTopKSum k sample = ∑ i ∈ s, sample i)
    (hs_card_lt : s.card < k) {j : Fin q} (hj_not_mem : j ∉ s) :
    sample j ≤ 0 := by
  by_contra hnot
  have hj_pos : 0 < sample j := lt_of_not_ge hnot
  let sInsert : Finset (Fin q) := insert j s
  have hsInsert_card : sInsert.card ≤ k := by
    have hcard : sInsert.card = s.card + 1 := by
      simp [sInsert, hj_not_mem]
    omega
  have hcandidate :
      (∑ i ∈ sInsert, sample i) ≤
        exponentialFiniteSampleTopKSum k sample := by
    simpa [exponentialFiniteSampleTopKSum, sInsert] using
      sum_le_topKSumOn (ι := Fin q) k sample sInsert hsInsert_card
  have hsum_insert :
      (∑ i ∈ sInsert, sample i) =
        (∑ i ∈ s, sample i) + sample j := by
    rw [Finset.sum_insert hj_not_mem]
    ring
  rw [hmax, hsum_insert] at hcandidate
  linarith

theorem exponentialFiniteSampleTopKSum_maximizer_missing_le_selected
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (s : Finset (Fin q)) (hs_card : s.card ≤ k)
    (hmax : exponentialFiniteSampleTopKSum k sample = ∑ i ∈ s, sample i)
    {i j : Fin q} (hi_mem : i ∈ s) (hj_not_mem : j ∉ s) :
    sample j ≤ sample i := by
  by_contra hnot
  have hlt : sample i < sample j := lt_of_not_ge hnot
  let sSwap : Finset (Fin q) := insert j (s.erase i)
  have hj_not_erase : j ∉ s.erase i := by
    simp [hj_not_mem]
  have hsSwap_card : sSwap.card ≤ k := by
    have hcard : sSwap.card = s.card := by
      have hs_card_pos : 0 < s.card := Finset.card_pos.mpr ⟨i, hi_mem⟩
      simp [sSwap, hj_not_erase, hi_mem]
      omega
    simpa [hcard] using hs_card
  have hcandidate :
      (∑ a ∈ sSwap, sample a) ≤
        exponentialFiniteSampleTopKSum k sample := by
    simpa [exponentialFiniteSampleTopKSum, sSwap] using
      sum_le_topKSumOn (ι := Fin q) k sample sSwap hsSwap_card
  have herase_sum :
      sample i + (∑ a ∈ s.erase i, sample a) =
        ∑ a ∈ s, sample a :=
    Finset.add_sum_erase s sample hi_mem
  have hsum_swap :
      (∑ a ∈ sSwap, sample a) =
        (∑ a ∈ s, sample a) - sample i + sample j := by
    calc
      (∑ a ∈ sSwap, sample a) =
          sample j + ∑ a ∈ s.erase i, sample a := by
            rw [Finset.sum_insert hj_not_erase]
      _ = (∑ a ∈ s, sample a) - sample i + sample j := by
            linarith
  rw [hmax, hsum_swap] at hcandidate
  linarith

theorem successCount_subtype_card_eq_filter
    {q : ℕ} (sample : Fin q → ℝ)
    (s : Finset (Fin q)) (x : ℝ) :
    (successIndexSet
      (fun y : ℝ => x < y)
      (fun i : {i : Fin q // i ∈ s} => sample i)).card =
        (s.filter (fun i : Fin q => x < sample i)).card := by
  classical
  let subCount : Finset {i : Fin q // i ∈ s} :=
    successIndexSet
      (fun y : ℝ => x < y)
      (fun i : {i : Fin q // i ∈ s} => sample i)
  have hmap :
      subCount.map (Function.Embedding.subtype fun i : Fin q => i ∈ s) =
        s.filter (fun i : Fin q => x < sample i) := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_map.mp hi with ⟨a, ha, hval⟩
      have hgt : x < sample a := by
        simpa [subCount, successIndexSet] using ha
      have his : (a : Fin q) ∈ s := a.property
      rw [← hval]
      simp [his, hgt]
    · intro hi
      have his : i ∈ s := (Finset.mem_filter.mp hi).1
      have hgt : x < sample i := (Finset.mem_filter.mp hi).2
      refine Finset.mem_map.mpr ⟨⟨i, his⟩, ?_, rfl⟩
      simpa [subCount, successIndexSet] using hgt
  calc
    subCount.card = (subCount.map
        (Function.Embedding.subtype fun i : Fin q => i ∈ s)).card := by
      rw [Finset.card_map]
    _ = (s.filter (fun i : Fin q => x < sample i)).card := by
      rw [hmap]

theorem exponentialFiniteSampleTopKSum_maximizer_min_successCount_le_subtype_count
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (s : Finset (Fin q)) (hs_card : s.card ≤ k)
    (hmax : exponentialFiniteSampleTopKSum k sample = ∑ i ∈ s, sample i)
    {x : ℝ} (hx_pos : 0 < x) :
    min k (successIndexSet (fun y : ℝ => x < y) sample).card ≤
      (successIndexSet
        (fun y : ℝ => x < y)
        (fun i : {i : Fin q // i ∈ s} => sample i)).card := by
  classical
  let allCount : Finset (Fin q) :=
    successIndexSet (fun y : ℝ => x < y) sample
  let selectedCount : Finset (Fin q) :=
    s.filter (fun i : Fin q => x < sample i)
  have hselected_subset_all : selectedCount ⊆ allCount := by
    intro i hi
    have hgt : x < sample i := (Finset.mem_filter.mp hi).2
    simpa [allCount, successIndexSet] using hgt
  have hsub_card :
      (successIndexSet
        (fun y : ℝ => x < y)
        (fun i : {i : Fin q // i ∈ s} => sample i)).card =
        selectedCount.card := by
    simpa [selectedCount] using successCount_subtype_card_eq_filter sample s x
  rw [hsub_card]
  by_contra hnot
  have hlt : selectedCount.card <
      min k (successIndexSet (fun y : ℝ => x < y) sample).card :=
    Nat.lt_of_not_ge hnot
  have hlt_k : selectedCount.card < k :=
    lt_of_lt_of_le hlt (min_le_left _ _)
  have hlt_all : selectedCount.card < allCount.card := by
    simpa [allCount] using lt_of_lt_of_le hlt (min_le_right _ _)
  have hmissing :
      ∃ j ∈ allCount, j ∉ selectedCount := by
    by_contra hnone
    push Not at hnone
    have hall_subset : allCount ⊆ selectedCount := by
      intro j hj
      exact hnone j hj
    have hcard_le : allCount.card ≤ selectedCount.card :=
      Finset.card_le_card hall_subset
    omega
  rcases hmissing with ⟨j, hj_all, hj_not_selected⟩
  have hj_gt : x < sample j := by
    simpa [allCount, successIndexSet] using hj_all
  have hj_pos : 0 < sample j := lt_trans hx_pos hj_gt
  have hj_not_mem : j ∉ s := by
    intro hj_mem
    exact hj_not_selected (by simp [selectedCount, hj_mem, hj_gt])
  by_cases hs_lt : s.card < k
  · have hj_nonpos :=
      exponentialFiniteSampleTopKSum_maximizer_missing_nonpos_of_card_lt
        k sample s hs_card hmax hs_lt hj_not_mem
    linarith
  · have hs_card_eq : s.card = k := by
      omega
    have hselected_subset_s : selectedCount ⊆ s := by
      intro i hi
      exact (Finset.mem_filter.mp hi).1
    have hselected_lt_s : selectedCount.card < s.card := by
      simpa [hs_card_eq] using hlt_k
    have hselected_missing :
        ∃ i ∈ s, i ∉ selectedCount := by
      by_contra hnone
      push Not at hnone
      have hs_subset_selected : s ⊆ selectedCount := by
        intro i hi
        exact hnone i hi
      have hcard_le : s.card ≤ selectedCount.card :=
        Finset.card_le_card hs_subset_selected
      omega
    rcases hselected_missing with ⟨i, hi_mem, hi_not_selected⟩
    have hi_not_gt : ¬ x < sample i := by
      intro hi_gt
      exact hi_not_selected (by simp [selectedCount, hi_mem, hi_gt])
    have hi_le : sample i ≤ x := le_of_not_gt hi_not_gt
    have hmissing_le_selected :=
      exponentialFiniteSampleTopKSum_maximizer_missing_le_selected
        k sample s hs_card hmax hi_mem hj_not_mem
    linarith

theorem integral_min_successCount_le_exponentialFiniteSampleTopKSum
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    (∫ x in Set.Ioi (0 : ℝ),
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)) ≤
      exponentialFiniteSampleTopKSum k sample := by
  classical
  obtain ⟨s, hs_card, hmax⟩ :=
    exponentialFiniteSampleTopKSum_exists_maximizer k sample
  let subSample : {i : Fin q // i ∈ s} → ℝ := fun i => sample i
  let subCountFun : ℝ → ℝ :=
    fun x =>
      ((successIndexSet (fun y : ℝ => x < y) subSample).card : ℝ)
  let minCountFun : ℝ → ℝ :=
    fun x =>
      ((min k
        (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
  have hsub_int :
      MeasureTheory.Integrable subCountFun
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [subCountFun, subSample] using
      successCount_integrable_fintype (sample := subSample)
  have hmin_int :
      MeasureTheory.Integrable minCountFun
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [minCountFun] using
      successCount_min_integrable_fintype (k := k) (sample := sample)
  have hmono :
      ∫ x, minCountFun x
          ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) ≤
        ∫ x, subCountFun x
          ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.integral_mono_ae hmin_int hsub_int ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hreal :
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ) ≤
          ((successIndexSet (fun y : ℝ => x < y) subSample).card : ℝ) := by
      exact_mod_cast
        exponentialFiniteSampleTopKSum_maximizer_min_successCount_le_subtype_count
          k sample s hs_card hmax hx
    simpa [minCountFun, subCountFun, subSample] using hreal
  have hsub_layer :
      ∫ x in Set.Ioi (0 : ℝ), subCountFun x =
        ∑ i : {i : Fin q // i ∈ s}, sample i := by
    simpa [subCountFun, subSample] using
      successCount_integral_eq_sum_fintype
        (sample := subSample)
        (fun i : {i : Fin q // i ∈ s} => h_nonneg i)
  have hsum_subtype :
      (∑ i : {i : Fin q // i ∈ s}, sample i) =
        ∑ i ∈ s, sample i := by
    simpa using
      (Finset.sum_coe_sort
        (s := s) (f := fun i : Fin q => sample i))
  calc
    ∫ x in Set.Ioi (0 : ℝ),
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
        =
        ∫ x in Set.Ioi (0 : ℝ), minCountFun x := by
          rfl
    _ ≤ ∫ x in Set.Ioi (0 : ℝ), subCountFun x := hmono
    _ = ∑ i : {i : Fin q // i ∈ s}, sample i := hsub_layer
    _ = ∑ i ∈ s, sample i := hsum_subtype
    _ = exponentialFiniteSampleTopKSum k sample := hmax.symm

theorem exponentialFiniteSampleTopKSum_eq_integral_min_successCount
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    exponentialFiniteSampleTopKSum k sample =
      ∫ x in Set.Ioi (0 : ℝ),
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ) :=
   le_antisymm
    (exponentialFiniteSampleTopKSum_le_integral_min_successCount
      k sample h_nonneg)
    (integral_min_successCount_le_exponentialFiniteSampleTopKSum
      k sample h_nonneg)

theorem exponentialFiniteSampleTopKSum_measurable {q : ℕ} (k : ℕ) :
    Measurable (exponentialFiniteSampleTopKSum (q := q) k) := by
  classical
  unfold exponentialFiniteSampleTopKSum topKSumOn
  let hmeas :=
    Finset.measurable_sup'
      (s := topKCandidateSets (Fin q) k)
      (topKCandidateSets_nonempty (Fin q) k)
      (fun s _hs =>
        Finset.measurable_sum (s := s)
          (fun i _hi => measurable_pi_apply (X := fun _ : Fin q => ℝ) i))
  convert hmeas using 1
  ext sample
  rw [Finset.sup'_apply]

theorem exponentialFiniteSampleTopKSum_integrable
    (M : AppliedModelingLib.Probability.Exponential.Model)
    {q : ℕ} [NeZero q] (k : ℕ) :
    MeasureTheory.Integrable
      (exponentialFiniteSampleTopKSum (q := q) k)
      (M.iidProductMeasure q) := by
  let μ := M.iidProductMeasure q
  let maxFun : (Fin q → ℝ) → ℝ :=
    AppliedModelingLib.Probability.Exponential.finiteSampleMax
  have hmax_int :
      MeasureTheory.Integrable maxFun μ := by
    simpa [μ, maxFun] using
      M.iidProductMeasure_finiteSampleMax_integrable (q := q)
  have hbound_int :
      MeasureTheory.Integrable
        (fun sample : Fin q → ℝ => (k : ℝ) * maxFun sample) μ :=
    hmax_int.const_mul (k : ℝ)
  refine MeasureTheory.Integrable.mono' hbound_int
    (exponentialFiniteSampleTopKSum_measurable (q := q) k).aestronglyMeasurable ?_
  filter_upwards [M.iidProductMeasure_finiteSampleMax_nonnegative_ae (q := q)]
    with sample hmax_nonneg
  have htop_nonneg :
      0 ≤ exponentialFiniteSampleTopKSum k sample :=
    exponentialFiniteSampleTopKSum_nonneg k sample
  have hbound :
      exponentialFiniteSampleTopKSum k sample ≤
        (k : ℝ) * maxFun sample := by
    simpa [maxFun] using
      exponentialFiniteSampleTopKSum_le_k_mul_finiteSampleMax
        (q := q) k sample hmax_nonneg
  have hbound_nonneg : 0 ≤ (k : ℝ) * maxFun sample :=
    mul_nonneg (Nat.cast_nonneg k) (by simpa [maxFun] using hmax_nonneg)
  simpa [Real.norm_eq_abs, abs_of_nonneg htop_nonneg,
    abs_of_nonneg hbound_nonneg] using hbound

theorem thresholdMinSuccessCount_prod_integrable
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    MeasureTheory.Integrable
      (fun z : (Fin q → ℝ) × ℝ =>
        ((min k
          (successIndexSet (fun y : ℝ => z.2 < y) z.1).card : ℕ) : ℝ))
      (((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).prod
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
  let M := exponentialDistributionModel lambda hlambda_pos
  let μ := M.iidProductMeasure q
  let ν := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let f : (Fin q → ℝ) × ℝ → ℝ :=
    fun z =>
      ((min k
        (successIndexSet (fun y : ℝ => z.2 < y) z.1).card : ℕ) : ℝ)
  have hf_meas : Measurable f := by
    simpa [f] using successCount_min_real_measurable_prod (q := q) k
  have hsections :
      ∀ᵐ sample ∂μ,
        MeasureTheory.Integrable (fun x : ℝ => f (sample, x)) ν := by
    filter_upwards with sample
    simpa [f, ν] using
      successCount_min_integrable_fintype (k := k) (sample := sample)
  have hinner_eq :
      (fun sample : Fin q → ℝ =>
          ∫ x, ‖f (sample, x)‖ ∂ν) =ᵐ[μ]
        fun sample : Fin q → ℝ =>
          exponentialFiniteSampleTopKSum k sample := by
    filter_upwards [M.iidProductMeasure_all_nonnegative_ae q] with sample h_nonneg
    have hnorm :
        ∫ x, ‖f (sample, x)‖ ∂ν =
          ∫ x, f (sample, x) ∂ν := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      have hnonneg : 0 ≤ f (sample, x) := by
        dsimp [f]
        exact_mod_cast Nat.zero_le
          (min k (successIndexSet (fun y : ℝ => x < y) sample).card)
      simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      ∫ x, ‖f (sample, x)‖ ∂ν =
          ∫ x, f (sample, x) ∂ν := hnorm
      _ =
          ∫ x in Set.Ioi (0 : ℝ),
            ((min k
              (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ) := by
            rfl
      _ = exponentialFiniteSampleTopKSum k sample :=
            (exponentialFiniteSampleTopKSum_eq_integral_min_successCount
              k sample (fun i => h_nonneg i)).symm
  have hinner_int :
      MeasureTheory.Integrable
        (fun sample : Fin q → ℝ => ∫ x, ‖f (sample, x)‖ ∂ν) μ :=
    (exponentialFiniteSampleTopKSum_integrable M k).congr hinner_eq.symm
  have hf_int :
      MeasureTheory.Integrable f (μ.prod ν) :=
    (MeasureTheory.integrable_prod_iff hf_meas.aestronglyMeasurable).2
      ⟨hsections, hinner_int⟩
  simpa [M, μ, ν, f] using hf_int

theorem exponentialFiniteSampleTopKSum_integral_eq_thresholdLayerCakeIntegral
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∫ sample,
        (∫ x in Set.Ioi (0 : ℝ),
          ((min k
            (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ))
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q := by
  let M := exponentialDistributionModel lambda hlambda_pos
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [M.iidProductMeasure_all_nonnegative_ae q] with sample h_nonneg
  exact exponentialFiniteSampleTopKSum_eq_integral_min_successCount
    k sample (fun i => h_nonneg i)

theorem thresholdLayerCakeIntegral_integral_swap
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        (∫ x in Set.Ioi (0 : ℝ),
          ((min k
            (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ))
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∫ x in Set.Ioi (0 : ℝ),
        (∫ sample,
          ((min k
            (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q) := by
  let M := exponentialDistributionModel lambda hlambda_pos
  let μ := M.iidProductMeasure q
  let ν := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    M.isProbabilityMeasure_iidProductMeasure q
  let f : (Fin q → ℝ) → ℝ → ℝ :=
    fun sample x =>
      ((min k
        (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
  have hf_int :
      MeasureTheory.Integrable (Function.uncurry f) (μ.prod ν) := by
    simpa [M, μ, ν, f, Function.uncurry] using
      thresholdMinSuccessCount_prod_integrable lambda hlambda_pos (q := q) k
  simpa [M, μ, ν, f] using
    (MeasureTheory.integral_integral_swap (μ := μ) (ν := ν) (f := f) hf_int)

theorem exponentialFiniteSampleTopKSum_integral_eq_tail_binomial_integral
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∫ x in Set.Ioi (0 : ℝ),
        (∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q,
            (Nat.choose q j : ℝ) *
              (Real.exp (-(lambda * x))) ^ j *
                (1 - Real.exp (-(lambda * x))) ^ (q - j)) := by
  calc
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
        ∫ sample,
          (∫ x in Set.Ioi (0 : ℝ),
            ((min k
              (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ))
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q :=
          exponentialFiniteSampleTopKSum_integral_eq_thresholdLayerCakeIntegral
            lambda hlambda_pos k
    _ =
        ∫ x in Set.Ioi (0 : ℝ),
          (∫ sample,
            ((min k
              (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
            ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q) :=
          thresholdLayerCakeIntegral_integral_swap lambda hlambda_pos k
    _ =
      ∫ x in Set.Ioi (0 : ℝ),
        (∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q,
            (Nat.choose q j : ℝ) *
              (Real.exp (-(lambda * x))) ^ j *
                (1 - Real.exp (-(lambda * x))) ^ (q - j)) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        exact exponentialProductMeasure_successCount_min_integral_eq_tail_binomial_sum
          lambda hlambda_pos x (le_of_lt hx) k

theorem exponentialFiniteSampleTopKSum_integral_eq_tail_harmonic_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      (1 / lambda) *
        ∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q, (1 / (j : ℝ)) := by
  rw [exponentialFiniteSampleTopKSum_integral_eq_tail_binomial_integral
    lambda hlambda_pos k]
  calc
    ∫ x in Set.Ioi (0 : ℝ),
        (∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q,
            (Nat.choose q j : ℝ) *
              (Real.exp (-(lambda * x))) ^ j *
                (1 - Real.exp (-(lambda * x))) ^ (q - j)) =
        ∑ r ∈ Finset.Icc 1 k,
          ∫ x in Set.Ioi (0 : ℝ),
            (∑ j ∈ Finset.Icc r q,
              (Nat.choose q j : ℝ) *
                (Real.exp (-(lambda * x))) ^ j *
                  (1 - Real.exp (-(lambda * x))) ^ (q - j)) :=
          MeasureTheory.integral_finset_sum (Finset.Icc 1 k)
            (fun r hr =>
              MeasureTheory.integrable_finset_sum (Finset.Icc r q)
                (fun j hj =>
                  exponentialBinomialMass_integrable_Ioi
                    lambda hlambda_pos
                    (by
                      have hr_pos : 0 < r :=
                        Nat.lt_of_lt_of_le (by omega : 0 < 1)
                          (Finset.mem_Icc.mp hr).1
                      exact Nat.lt_of_lt_of_le hr_pos (Finset.mem_Icc.mp hj).1)
                    (Finset.mem_Icc.mp hj).2))
    _ =
        ∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q,
            ∫ x in Set.Ioi (0 : ℝ),
              (Nat.choose q j : ℝ) *
                (Real.exp (-(lambda * x))) ^ j *
                  (1 - Real.exp (-(lambda * x))) ^ (q - j) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          exact MeasureTheory.integral_finset_sum (Finset.Icc r q)
            (fun j hj =>
              exponentialBinomialMass_integrable_Ioi
                lambda hlambda_pos
                (by
                  have hr_pos : 0 < r :=
                    Nat.lt_of_lt_of_le (by omega : 0 < 1)
                      (Finset.mem_Icc.mp hr).1
                  exact Nat.lt_of_lt_of_le hr_pos (Finset.mem_Icc.mp hj).1)
                (Finset.mem_Icc.mp hj).2)
    _ =
        ∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q,
            (1 / lambda) * (1 / (j : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact exponentialBinomialMass_integral_eq_inv_lambda_mul_inv
            lambda hlambda_pos
            (by
              have hr_pos : 0 < r :=
                Nat.lt_of_lt_of_le (by omega : 0 < 1)
                  (Finset.mem_Icc.mp hr).1
              exact Nat.lt_of_lt_of_le hr_pos (Finset.mem_Icc.mp hj).1)
            (Finset.mem_Icc.mp hj).2
    _ =
      (1 / lambda) *
        ∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q, (1 / (j : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro r _hr
        rw [Finset.mul_sum]

theorem exponentialFiniteSampleTopKSum_integral_eq_orderStatisticValue
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopKOrderStatisticValue lambda k q := by
  rw [exponentialFiniteSampleTopKSum_integral_eq_tail_harmonic_sum
    lambda hlambda_pos k]
  rw [exponentialTopKOrderStatisticValue_eq_tail_harmonic_sum]

theorem exponentialFiniteSampleTopKSum_one_integral_eq_harmonicValue
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) 1 sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopOneHarmonicValue lambda q := by
  let M := exponentialDistributionModel lambda hlambda_pos
  calc
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) 1 sample
          ∂M.iidProductMeasure q =
        ∫ sample,
          AppliedModelingLib.Probability.Exponential.finiteSampleMax sample
            ∂M.iidProductMeasure q := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [M.iidProductMeasure_finiteSampleMax_nonnegative_ae (q := q)]
        with sample hmax_nonneg
      exact exponentialFiniteSampleTopKSum_one_eq_finiteSampleMax sample hmax_nonneg
    _ = exponentialTopOneHarmonicValue lambda q := by
      simpa [M] using
        exponentialProductMaxIntegral_eq_harmonicValue lambda hlambda_pos (q := q)

theorem exponentialFiniteSampleTopKSum_card_le_integral_eq_orderStatisticValue
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] {k : ℕ} (hqk : q ≤ k) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopKOrderStatisticValue lambda k q := by
  let M := exponentialDistributionModel lambda hlambda_pos
  have hcoord_nonneg :
      ∀ i : Fin q,
        (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[M.measure] (fun x : ℝ => x) :=
    fun _ => M.ae_nonnegative
  have hsample_nonneg :
      (fun _ : Fin q → ℝ => fun _ : Fin q => (0 : ℝ)) ≤ᵐ[
          M.iidProductMeasure q] fun sample => sample := by
    let μ : Fin q → MeasureTheory.Measure ℝ := fun _ => M.measure
    haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
      M.isProbabilityMeasure_measure
    have hsigma_single : MeasureTheory.SigmaFinite M.measure := inferInstance
    have hsigma :
        ∀ i : Fin q, MeasureTheory.SigmaFinite (μ i) :=
      fun _ => hsigma_single
    have hpi :
        (fun _ : Fin q → ℝ => fun _ : Fin q => (0 : ℝ)) ≤ᵐ[
            MeasureTheory.Measure.pi μ]
          fun sample => sample :=
      @MeasureTheory.Measure.ae_le_pi
        (Fin q) (fun _ : Fin q => ℝ) inferInstance
        (fun _ => inferInstance) μ hsigma (fun _ : Fin q => ℝ)
        (fun _ => inferInstance) (fun _ (_ : ℝ) => (0 : ℝ))
        (fun _ x => x) hcoord_nonneg
    simpa [AppliedModelingLib.Probability.Exponential.Model.iidProductMeasure, M, μ]
      using hpi
  have htop_eq_sum :
      (fun sample : Fin q → ℝ => exponentialFiniteSampleTopKSum k sample) =ᵐ[
          M.iidProductMeasure q]
        fun sample => ∑ i : Fin q, sample i := by
    filter_upwards [hsample_nonneg] with sample h_nonneg
    exact exponentialFiniteSampleTopKSum_eq_sum_of_card_le
      k sample hqk (fun i => h_nonneg i)
  have hmean :
      M.expectedMaxValue 1 = 1 / lambda := by
    simpa [M, exponentialDistributionModel,
      AppliedModelingLib.Probability.Exponential.Model.expectedMaxValue] using
      AppliedModelingLib.Probability.Exponential.expectedMaxValueOfRate_one lambda
  calc
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂M.iidProductMeasure q =
        ∫ sample,
          (∑ i : Fin q, sample i) ∂M.iidProductMeasure q :=
      MeasureTheory.integral_congr_ae htop_eq_sum
    _ = (q : ℝ) * M.expectedMaxValue 1 :=
              M.iidProductMeasure_sum_integral_eq_card_mul_expectedMaxValue_one q
    _ = (1 / lambda) * (q : ℝ) := by
      rw [hmean]
      ring
    _ = exponentialTopKOrderStatisticValue lambda k q :=
      (exponentialTopKOrderStatisticValue_eq_linear_of_le lambda hqk).symm

theorem exponentialFiniteSampleTopPredCard_integral_eq_orderStatisticValue
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) (q - 1) sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopKOrderStatisticValue lambda (q - 1) q := by
  let M := exponentialDistributionModel lambda hlambda_pos
  have htop_eq :
      (fun sample : Fin q → ℝ =>
        exponentialFiniteSampleTopKSum (q := q) (q - 1) sample) =ᵐ[
          M.iidProductMeasure q]
        fun sample =>
          (∑ i : Fin q, sample i) -
            AppliedModelingLib.Probability.Exponential.finiteSampleMin sample := by
    filter_upwards [M.iidProductMeasure_all_nonnegative_ae q] with sample h_nonneg
    exact exponentialFiniteSampleTopKSum_pred_card_eq_sum_sub_min
      sample (fun i => h_nonneg i)
  have hsum_int :
      MeasureTheory.Integrable
        (fun sample : Fin q → ℝ => ∑ i : Fin q, sample i)
        (M.iidProductMeasure q) := by
    refine MeasureTheory.integrable_finset_sum Finset.univ ?_
    intro i _hi
    exact M.iidProductMeasure_eval_integrable i
  have hmin_int :
      MeasureTheory.Integrable
        (AppliedModelingLib.Probability.Exponential.finiteSampleMin (q := q))
        (M.iidProductMeasure q) :=
    M.iidProductMeasure_finiteSampleMin_integrable
  have hmean :
      M.expectedMaxValue 1 = 1 / lambda := by
    simpa [M, exponentialDistributionModel,
      AppliedModelingLib.Probability.Exponential.Model.expectedMaxValue] using
      AppliedModelingLib.Probability.Exponential.expectedMaxValueOfRate_one lambda
  calc
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) (q - 1) sample
          ∂M.iidProductMeasure q =
        ∫ sample,
          ((∑ i : Fin q, sample i) -
            AppliedModelingLib.Probability.Exponential.finiteSampleMin sample)
          ∂M.iidProductMeasure q :=
      MeasureTheory.integral_congr_ae htop_eq
    _ = ∫ sample,
          (∑ i : Fin q, sample i) ∂M.iidProductMeasure q -
        ∫ sample,
          AppliedModelingLib.Probability.Exponential.finiteSampleMin sample
            ∂M.iidProductMeasure q :=
      MeasureTheory.integral_sub hsum_int hmin_int
    _ = (q : ℝ) * M.expectedMaxValue 1 -
        1 / ((q : ℝ) * M.rate) := by
      rw [M.iidProductMeasure_sum_integral_eq_card_mul_expectedMaxValue_one q,
        M.iidProductMeasure_finiteSampleMin_integral_eq_expectedMinValue (q := q)]
    _ = (1 / lambda) * (q : ℝ) - 1 / ((q : ℝ) * lambda) := by
      rw [hmean]
      simp [M, exponentialDistributionModel]
      ring
    _ = exponentialTopKOrderStatisticValue lambda (q - 1) q :=
      (exponentialTopKOrderStatisticValue_pred_card
        lambda hlambda_pos (q := q)).symm

theorem exponentialFiniteSampleTopKSum_zero_integral_eq_orderStatisticValue
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (q : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) 0 sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopKOrderStatisticValue lambda 0 q := by
  calc
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) 0 sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
        ∫ _sample : Fin q → ℝ,
          (0 : ℝ)
            ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q := by
      refine MeasureTheory.integral_congr_ae ?_
      exact Filter.Eventually.of_forall (fun sample =>
        exponentialFiniteSampleTopKSum_zero sample)
    _ = 0 := by
      simp
    _ = exponentialTopKOrderStatisticValue lambda 0 q := by
      unfold exponentialTopKOrderStatisticValue
      simp

/-- The exact asymptotic marginal scale for the exponential top-`k` oracle. -/
noncomputable def exponentialTopKOrderStatisticScale
    (lambda : ℝ) (k q : ℕ) : ℝ := (1 / lambda) * ((k : ℝ) / (((q + 1 : ℕ) : ℝ)))

noncomputable def exponentialTopKOrderStatisticScaledMarginalLimitCertificate
    (T : ℕ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k) :
    TopKScaledMarginalLimitCertificate
      (exponentialTopKOrderStatisticOracle T lambda k) k
      (exponentialTopKOrderStatisticScale lambda k)
      (fun _ : ItemType T => (1 : ℝ)) where
  scale_pos_eventually := by
    filter_upwards with q
    exact mul_pos (one_div_pos.mpr hlambda_pos)
      (div_pos (by exact_mod_cast hk_pos) (by positivity))
  weight_pos := by
    intro t
    norm_num
  marginal_ratio_tendsto := by
    intro t
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_atTop.2 ⟨k, fun q hq => hq⟩] with q hq
    have hmin : min k (q + 1) = k := min_eq_left (by omega)
    have hscale_pos : 0 < exponentialTopKOrderStatisticScale lambda k q :=
      mul_pos (one_div_pos.mpr hlambda_pos)
        (div_pos (by exact_mod_cast hk_pos) (by positivity))
    have hscale_ne :
        exponentialTopKOrderStatisticScale lambda k q ≠ 0 :=
      ne_of_gt hscale_pos
    have hden_ne :
        (lambda⁻¹ * ((k : ℝ) / ((q : ℝ) + 1))) ≠ 0 := by
      simpa [exponentialTopKOrderStatisticScale, Nat.cast_add, Nat.cast_one]
        using hscale_ne
    simp [AppliedModelingLib.Probability.TopKExpectationOracle.marginalTopK,
      topKExpectationOracleOfTopKValueOracle,
      exponentialTopKOrderStatisticOracle,
      exponentialTopKOrderStatisticScale,
      exponentialTopKOrderStatistic_forward_marginal, hmin]
    field_simp [hden_ne]

/-- Finite-prefix error for the general top-`k` exponential FOC proof. -/
noncomputable def exponentialTopKOrderStatisticError {T : ℕ}
    (likelihood : ItemType T → ℝ) (k N : ℕ) : ℝ :=
  if N = 0 then 0 else
    ((∑ t : ItemType T, (k : ℝ) / (likelihood t ^ (1 : ℝ))) + 1) / (N : ℝ)

theorem exponentialTopKOrderStatisticError_nonneg {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (N : ℕ) :
    0 ≤ exponentialTopKOrderStatisticError likelihood k N := by
  by_cases hN : N = 0
  · simp [exponentialTopKOrderStatisticError, hN]
  · have hS_nonneg :
        0 ≤ ∑ t : ItemType T, (k : ℝ) / (likelihood t ^ (1 : ℝ)) :=
      Finset.sum_nonneg
        (fun t _ => div_nonneg (Nat.cast_nonneg k)
          (le_of_lt (by
            simpa [Real.rpow_one] using hlike_pos t)))
    have hN_pos : 0 < (N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hN
    have hnum_nonneg :
        0 ≤ (∑ t : ItemType T, (k : ℝ) / (likelihood t ^ (1 : ℝ))) + 1 :=
      add_nonneg hS_nonneg zero_le_one
    rw [exponentialTopKOrderStatisticError, if_neg hN]
    exact div_nonneg hnum_nonneg (le_of_lt hN_pos)

theorem exponentialTopKOrderStatisticError_tends_to_zero {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    AppliedModelingLib.Math.TendsToZero
      (exponentialTopKOrderStatisticError likelihood k) := by
  let S : ℝ :=
    (∑ t : ItemType T, (k : ℝ) / (likelihood t ^ (1 : ℝ))) + 1
  have hsum_nonneg :
      0 ≤ ∑ t : ItemType T, (k : ℝ) / (likelihood t ^ (1 : ℝ)) :=
    Finset.sum_nonneg
      (fun t _ => div_nonneg (Nat.cast_nonneg k)
        (le_of_lt (by
          simpa [Real.rpow_one] using hlike_pos t)))
  have hS_pos : 0 < S := by
    dsimp [S]
    linarith
  refine AppliedModelingLib.Math.TendsToZero_of_nonneg_le_const_div
    (exponentialTopKOrderStatisticError likelihood k) hS_pos
    (exponentialTopKOrderStatisticError_nonneg likelihood k hlike_pos) ?_
  intro N hN
  have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
  simp [exponentialTopKOrderStatisticError, hN_ne, S]

noncomputable def exponentialTopKOrderStatisticSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    PairwiseScaledSublinearFOCCertificate
      (fun _ =>
        (exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
          likelihood k)
      (fun t : ItemType T => likelihood t ^ (1 : ℝ))
      (gammaLikelihoodProfile likelihood 1) where
  weight_pos := by
    intro t
    simpa [Real.rpow_one] using hlike_pos t
  targetShare_eq := by
    intro t
    have hnorm_pos :
        0 < ∑ i : ItemType T, likelihood i ^ (1 : ℝ) :=
      Finset.sum_pos
        (fun i _ => by simpa [Real.rpow_one] using hlike_pos i)
        Finset.univ_nonempty
    exact gammaLikelihoodProfile_targetShare_eq likelihood 1 t
      (ne_of_gt hnorm_pos)
  error := exponentialTopKOrderStatisticError likelihood k
  error_nonneg :=
    exponentialTopKOrderStatisticError_nonneg likelihood k hlike_pos
  error_tends_to_zero :=
    exponentialTopKOrderStatisticError_tends_to_zero likelihood k hlike_pos
  large_gap_backward_lt_forward := by
    intro N a hN _hopt src dst hgap
    let weight : ItemType T → ℝ := fun t => likelihood t ^ (1 : ℝ)
    let S : ℝ := (∑ t : ItemType T, (k : ℝ) / weight t) + 1
    have hweight_pos : ∀ t, 0 < weight t := by
      intro t
      dsimp [weight]
      simpa [Real.rpow_one] using hlike_pos t
    have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
    have hN_real_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN_ne
    have hgapS :
        S <
          (a.count src : ℝ) / weight src -
            (a.count dst : ℝ) / weight dst := by
      have hmul :
          exponentialTopKOrderStatisticError likelihood k N * (N : ℝ) = S := by
        simp [exponentialTopKOrderStatisticError, hN_ne, S, weight,
          hN_real_ne]
      simpa [hmul, weight] using hgap
    have hS_pos : 0 < S := by
      have hsum_nonneg :
          0 ≤ ∑ t : ItemType T, (k : ℝ) / weight t :=
        Finset.sum_nonneg
          (fun t _ => div_nonneg (Nat.cast_nonneg k)
            (le_of_lt (hweight_pos t)))
      dsimp [S]
      linarith
    have hdst_nonneg :
        0 ≤ (a.count dst : ℝ) / weight dst :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt (hweight_pos dst))
    have hsrc_div_pos : 0 < (a.count src : ℝ) / weight src := by
      linarith
    have hsrc_pos : 0 < a.count src := by
      by_contra hnot
      have hzero : a.count src = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hzero] at hsrc_div_pos
      simp at hsrc_div_pos
    have hk_over_dst_lt_S : (k : ℝ) / weight dst < S := by
      have hterm_nonneg :
          ∀ t : ItemType T, 0 ≤ (k : ℝ) / weight t := by
        intro t
        exact div_nonneg (Nat.cast_nonneg k) (le_of_lt (hweight_pos t))
      have hle_sum :
          (k : ℝ) / weight dst ≤ ∑ t : ItemType T, (k : ℝ) / weight t :=
        Finset.single_le_sum
          (fun t _ => hterm_nonneg t) (Finset.mem_univ dst)
      dsimp [S]
      linarith
    have hscaled_add :
        ((a.count dst : ℝ) + (k : ℝ)) / weight dst <
          (a.count src : ℝ) / weight src := by
      have hsum_lt :
          (a.count dst : ℝ) / weight dst + (k : ℝ) / weight dst <
            (a.count src : ℝ) / weight src := by
        linarith
      have hadd :
          ((a.count dst : ℝ) + (k : ℝ)) / weight dst =
            (a.count dst : ℝ) / weight dst + (k : ℝ) / weight dst := by
        ring
      simpa [hadd] using hsum_lt
    have hqsrc_real_pos : 0 < (a.count src : ℝ) := by
      exact_mod_cast hsrc_pos
    have hqdst_add_k_pos :
        0 < (((a.count dst + k : ℕ) : ℝ)) := by
      exact_mod_cast Nat.add_pos_right (a.count dst) hk_pos
    have hratio_weight :
        weight src / (a.count src : ℝ) <
          weight dst / (((a.count dst + k : ℕ) : ℝ)) := by
      have hscaled' :
          (((a.count dst + k : ℕ) : ℝ)) / weight dst <
            (a.count src : ℝ) / weight src := by
        simpa [Nat.cast_add] using hscaled_add
      exact reciprocal_ratio_lt_of_scaled_ratio_lt
        (hweight_pos src) (hweight_pos dst)
        hqsrc_real_pos hqdst_add_k_pos hscaled'
    have hratio_like :
        likelihood src / (a.count src : ℝ) <
          likelihood dst / (((a.count dst + k : ℕ) : ℝ)) := by
      simpa [weight, Real.rpow_one] using hratio_weight
    have hmin_ratio_le :=
      exponentialTopKOrderStatistic_min_ratio_le
        (k := k) (q := a.count dst) hk_pos
    have hcore :
        (((min k (a.count src) : ℕ) : ℝ) *
            (likelihood src / (a.count src : ℝ))) <
          (((min k (a.count dst + 1) : ℕ) : ℝ) *
            (likelihood dst / (((a.count dst + 1 : ℕ) : ℝ)))) := by
      have hsrc_min_le_k :
          (((min k (a.count src) : ℕ) : ℝ)) ≤ (k : ℝ) := by
        exact_mod_cast min_le_left k (a.count src)
      have hsrc_ratio_pos :
          0 < likelihood src / (a.count src : ℝ) :=
        div_pos (hlike_pos src) hqsrc_real_pos
      have hdst_nonneg_like : 0 ≤ likelihood dst := le_of_lt (hlike_pos dst)
      calc
        (((min k (a.count src) : ℕ) : ℝ) *
            (likelihood src / (a.count src : ℝ)))
            ≤ (k : ℝ) * (likelihood src / (a.count src : ℝ)) :=
              mul_le_mul_of_nonneg_right hsrc_min_le_k
                (le_of_lt hsrc_ratio_pos)
        _ < (k : ℝ) *
            (likelihood dst / (((a.count dst + k : ℕ) : ℝ))) :=
              mul_lt_mul_of_pos_left hratio_like (by exact_mod_cast hk_pos)
        _ ≤ (((min k (a.count dst + 1) : ℕ) : ℝ) *
            (likelihood dst / (((a.count dst + 1 : ℕ) : ℝ)))) := by
              calc
                (k : ℝ) *
                    (likelihood dst / (((a.count dst + k : ℕ) : ℝ)))
                    = likelihood dst *
                        ((k : ℝ) / (((a.count dst + k : ℕ) : ℝ))) := by
                      ring
                _ ≤ likelihood dst *
                    ((((min k (a.count dst + 1) : ℕ) : ℝ)) /
                      (((a.count dst + 1 : ℕ) : ℝ))) :=
                      mul_le_mul_of_nonneg_left hmin_ratio_le
                        hdst_nonneg_like
                _ = (((min k (a.count dst + 1) : ℕ) : ℝ) *
                    (likelihood dst /
                      (((a.count dst + 1 : ℕ) : ℝ)))) := by
                      ring
    have hmarginal :
        likelihood src *
            ((1 / lambda) *
              (((min k (a.count src) : ℕ) : ℝ) /
                (a.count src : ℝ))) <
          likelihood dst *
            ((1 / lambda) *
              (((min k (a.count dst + 1) : ℕ) : ℝ) /
                (((a.count dst + 1 : ℕ) : ℝ)))) := by
      calc
        likelihood src *
            ((1 / lambda) *
              (((min k (a.count src) : ℕ) : ℝ) /
                (a.count src : ℝ)))
            = (1 / lambda) *
                ((((min k (a.count src) : ℕ) : ℝ) *
                  (likelihood src / (a.count src : ℝ)))) := by
              ring
        _ < (1 / lambda) *
                ((((min k (a.count dst + 1) : ℕ) : ℝ) *
                  (likelihood dst /
                    (((a.count dst + 1 : ℕ) : ℝ))))) :=
              mul_lt_mul_of_pos_left hcore
                (one_div_pos.mpr hlambda_pos)
        _ = likelihood dst *
            ((1 / lambda) *
              (((min k (a.count dst + 1) : ℕ) : ℝ) /
                (((a.count dst + 1 : ℕ) : ℝ)))) := by
              ring
    unfold ConsumptionModel.weightedBackwardMarginal
      ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
      AppliedModelingLib.Allocation.marginal TopKValueOracle.toConsumptionModel
    rw [dif_neg hsrc_pos.ne']
    simp only [exponentialTopKOrderStatisticOracle,
      TopKValueOracle.common_expectedTopSum]
    rw [exponentialTopKOrderStatistic_backward_marginal lambda k hsrc_pos,
      exponentialTopKOrderStatistic_forward_marginal]
    exact hmarginal

end PRPKG24AccuracyDiversity
