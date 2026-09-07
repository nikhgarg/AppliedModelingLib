import AppliedModelingLib.Foundations.Probability.IIDLargeDeviations
import AppliedModelingLib.Foundations.Probability.FiniteHerbst
import AppliedModelingLib.Foundations.Probability.FiniteSampleVariance
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Finite Bennett moment bounds

This module proves the finite-support moment bound underlying Bennett and
empirical-Bernstein concentration.  The central score is only required to be
bounded above by one; unlike a Hoeffding bound, the resulting exponent retains
its second-moment factor.
-/

open scoped BigOperators Topology

namespace AppliedModelingLib

noncomputable section

/-- The exponential-series tail after its constant and linear terms. -/
private theorem finiteBennett_exp_tail_hasSum (x : ℝ) : HasSum (fun n : ℕ =>
    x ^ (n + 2) / ((n + 2).factorial : ℝ)) (Real.exp x - 1 - x) := by
  let f : ℕ → ℝ := fun n => x ^ n / (n.factorial : ℝ)
  have hsum : HasSum f (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [f, div_eq_mul_inv, smul_eq_mul, mul_comm] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have htail : HasSum (fun n => f (n + 2))
      (Real.exp x - ∑ i ∈ Finset.range 2, f i) := by
    apply (hasSum_nat_add_iff 2).2
    convert hsum using 1
    ring
  convert htail using 1
  norm_num [Finset.sum_range_succ, f]
  ring

/-- The factorial coefficients in the exponential tail dominate the geometric
coefficients with ratio one third. -/
private theorem finiteBennett_two_mul_three_pow_le_factorial_add_two (n : ℕ) :
    2 * 3 ^ n ≤ (n + 2).factorial := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        2 * 3 ^ (n + 1) = 3 * (2 * 3 ^ n) := by ring
        _ ≤ 3 * (n + 2).factorial := Nat.mul_le_mul_left 3 ih
        _ ≤ (n + 3) * (n + 2).factorial :=
          Nat.mul_le_mul_right (n + 2).factorial (by omega)
        _ = (n + 3).factorial := (Nat.factorial_succ (n + 2)).symm
        _ = (n + 1 + 2).factorial := rfl

/-- The Bennett exponential remainder is bounded by its standard rational
majorant on the interval `0 <= t < 3`. -/
private theorem finiteBennett_exp_remainder_le_rational
    {t : ℝ} (ht : 0 ≤ t) (ht_three : t < 3) :
    Real.exp t - 1 - t ≤ t ^ 2 / (2 * (1 - t / 3)) := by
  let ratio : ℝ := t / 3
  have hratio_nonneg : 0 ≤ ratio := by
    dsimp [ratio]
    positivity
  have hratio_lt_one : ratio < 1 := by
    dsimp [ratio]
    rw [div_lt_one₀]
    · exact ht_three
    · norm_num
  have hratio_norm : ‖ratio‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hratio_nonneg]
    exact hratio_lt_one
  have hgeometric : HasSum (fun n : ℕ => ratio ^ n) (1 - ratio)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hratio_norm
  have hterm : ∀ n : ℕ,
      t ^ (n + 2) / ((n + 2).factorial : ℝ) ≤
        (t ^ 2 / 2) * ratio ^ n := by
    intro n
    have hfactorial_nat := finiteBennett_two_mul_three_pow_le_factorial_add_two n
    have hfactorial : (2 : ℝ) * 3 ^ n ≤ ((n + 2).factorial : ℝ) := by
      exact_mod_cast hfactorial_nat
    have hdenominator_pos : 0 < (2 : ℝ) * 3 ^ n := by positivity
    calc
      t ^ (n + 2) / ((n + 2).factorial : ℝ) ≤
          t ^ (n + 2) / ((2 : ℝ) * 3 ^ n) :=
        div_le_div_of_nonneg_left (pow_nonneg ht _) hdenominator_pos hfactorial
      _ = (t ^ 2 / 2) * ratio ^ n := by
        dsimp [ratio]
        rw [show n + 2 = 2 + n by omega, pow_add, div_pow]
        field_simp
  have htail := finiteBennett_exp_tail_hasSum t
  have hscaled : HasSum (fun n : ℕ => (t ^ 2 / 2) * ratio ^ n)
      ((t ^ 2 / 2) * (1 - ratio)⁻¹) :=
    hgeometric.mul_left _
  have hle := Summable.tsum_le_tsum hterm htail.summable hscaled.summable
  rw [htail.tsum_eq, hscaled.tsum_eq] at hle
  calc
    Real.exp t - 1 - t ≤ (t ^ 2 / 2) * (1 - ratio)⁻¹ := hle
    _ = t ^ 2 / (2 * (1 - t / 3)) := by
      dsimp [ratio]
      field_simp

/-- For a nonnegative `t` and any `y <= 1`, the exponential is bounded by its
linear term plus the Bennett quadratic remainder. -/
theorem finiteBennett_exp_le_one_add_self_add_remainder_sq
    {t y : ℝ} (ht : 0 ≤ t) (hy : y ≤ 1) :
    Real.exp (t * y) ≤ 1 + t * y + (Real.exp t - 1 - t) * y ^ 2 := by
  by_cases hy0 : 0 ≤ y
  · have hterm : ∀ n : ℕ,
        (t * y) ^ (n + 2) / ((n + 2).factorial : ℝ) ≤
          y ^ 2 * (t ^ (n + 2) / ((n + 2).factorial : ℝ)) := by
      intro n
      have hy_pow : y ^ (n + 2) ≤ y ^ 2 := by
        rw [show n + 2 = 2 + n by omega, pow_add]
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hy0 hy) (sq_nonneg y)).trans_eq
          (by ring)
      have hnum : t ^ (n + 2) * y ^ (n + 2) ≤
          y ^ 2 * t ^ (n + 2) := by
        calc
          t ^ (n + 2) * y ^ (n + 2) ≤ t ^ (n + 2) * y ^ 2 :=
            mul_le_mul_of_nonneg_left hy_pow (pow_nonneg ht _)
          _ = y ^ 2 * t ^ (n + 2) := by ring
      calc
        (t * y) ^ (n + 2) / ((n + 2).factorial : ℝ) =
            t ^ (n + 2) * y ^ (n + 2) / ((n + 2).factorial : ℝ) := by
              rw [mul_pow]
        _ ≤ y ^ 2 * t ^ (n + 2) / ((n + 2).factorial : ℝ) :=
          (div_le_div_iff_of_pos_right
            (by positivity : 0 < ((n + 2).factorial : ℝ))).2 hnum
        _ = y ^ 2 * (t ^ (n + 2) / ((n + 2).factorial : ℝ)) := by ring
    have hsumxy : HasSum (fun n : ℕ =>
        (t * y) ^ (n + 2) / ((n + 2).factorial : ℝ))
        (Real.exp (t * y) - 1 - t * y) :=
      finiteBennett_exp_tail_hasSum (t * y)
    have hsumt : HasSum (fun n : ℕ =>
        t ^ (n + 2) / ((n + 2).factorial : ℝ))
        (Real.exp t - 1 - t) :=
      finiteBennett_exp_tail_hasSum t
    have hle := Summable.tsum_le_tsum hterm hsumxy.summable
      ((hsumt.mul_left (y ^ 2)).summable)
    rw [tsum_mul_left, hsumxy.tsum_eq, hsumt.tsum_eq] at hle
    linarith
  · have hyneg : y < 0 := lt_of_not_ge hy0
    let u : ℝ := -(t * y)
    have hu : 0 ≤ u := by
      dsimp [u]
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos ht hyneg.le)
    let r : ℝ := 1 + u + u ^ 2 / 2
    let q : ℝ := 1 - u + u ^ 2 / 2
    have hr_pos : 0 < r := by
      dsimp [r]
      positivity
    have hr : r ≤ Real.exp u := by
      dsimp [r]
      exact Real.quadratic_le_exp_of_nonneg hu
    have hproduct : 1 ≤ q * r := by
      dsimp [q, r]
      nlinarith [sq_nonneg (u ^ 2)]
    have hnegative_exp : Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
      calc
        Real.exp (-u) = 1 / Real.exp u := by rw [one_div, Real.exp_neg]
        _ ≤ 1 / r := one_div_le_one_div_of_le hr_pos hr
        _ ≤ q := (div_le_iff₀ hr_pos).2 hproduct
        _ = 1 - u + u ^ 2 / 2 := by rfl
    have hcoef : t ^ 2 / 2 ≤ Real.exp t - 1 - t := by
      nlinarith [Real.quadratic_le_exp_of_nonneg ht]
    have hsq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
    calc
      Real.exp (t * y) = Real.exp (-u) := by
        congr 1
        dsimp [u]
        ring
      _ ≤ 1 - u + u ^ 2 / 2 := hnegative_exp
      _ = 1 + t * y + (t ^ 2 / 2) * y ^ 2 := by
        dsimp [u]
        ring
      _ ≤ 1 + t * y + (Real.exp t - 1 - t) * y ^ 2 := by
        gcongr

/-- Bennett's finite-support MGF inequality for a centered score bounded above
by one. -/
theorem finiteMGF_centered_le_exp_remainder_mul_secondMoment
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) (score : α → ℝ) {step : ℝ}
    (hstep : 0 ≤ step) (hupper : ∀ outcome, score outcome ≤ 1)
    (hcentered : pmfExp law score = 0) :
    Probability.finiteMGF law score step ≤
      Real.exp ((Real.exp step - 1 - step) *
        pmfExp law (fun outcome => score outcome ^ 2)) := by
  have hpoint : ∀ outcome,
      Real.exp (step * score outcome) ≤
        1 + step * score outcome +
          (Real.exp step - 1 - step) * score outcome ^ 2 := by
    intro outcome
    exact finiteBennett_exp_le_one_add_self_add_remainder_sq hstep (hupper outcome)
  have haverage : Probability.finiteMGF law score step ≤
      pmfExp law (fun outcome =>
        1 + step * score outcome +
          (Real.exp step - 1 - step) * score outcome ^ 2) := by
    exact pmfExp_le_pmfExp_of_forall_le law _ _ hpoint
  calc
    Probability.finiteMGF law score step ≤
        pmfExp law (fun outcome =>
          1 + step * score outcome +
            (Real.exp step - 1 - step) * score outcome ^ 2) := haverage
    _ = 1 + (Real.exp step - 1 - step) *
        pmfExp law (fun outcome => score outcome ^ 2) := by
      rw [pmfExp_add, pmfExp_add, pmfExp_const, pmfExp_const_mul,
        pmfExp_const_mul, hcentered]
      ring
    _ ≤ Real.exp ((Real.exp step - 1 - step) *
        pmfExp law (fun outcome => score outcome ^ 2)) := by
      simpa [add_comm] using
        Real.add_one_le_exp ((Real.exp step - 1 - step) *
          pmfExp law (fun outcome => score outcome ^ 2))

/-- The usual sub-gamma relaxation of the finite Bennett MGF bound.  The
restriction `step < 3` is exactly the domain of the rational exponential
remainder majorant. -/
theorem finiteMGF_centered_le_exp_subgamma
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) (score : α → ℝ) {step : ℝ}
    (hstep : 0 ≤ step) (hstep_three : step < 3)
    (hupper : ∀ outcome, score outcome ≤ 1)
    (hcentered : pmfExp law score = 0) :
    Probability.finiteMGF law score step ≤
      Real.exp ((step ^ 2 / (2 * (1 - step / 3))) *
        pmfExp law (fun outcome => score outcome ^ 2)) := by
  have hBennett := finiteMGF_centered_le_exp_remainder_mul_secondMoment
    law score hstep hupper hcentered
  have hsecond_nonneg : 0 ≤ pmfExp law (fun outcome => score outcome ^ 2) :=
    pmfExp_nonneg_of_forall_nonneg law _ (fun outcome => sq_nonneg _)
  have hremainder := finiteBennett_exp_remainder_le_rational hstep hstep_three
  have hexponent :
      (Real.exp step - 1 - step) *
          pmfExp law (fun outcome => score outcome ^ 2) ≤
        (step ^ 2 / (2 * (1 - step / 3))) *
          pmfExp law (fun outcome => score outcome ^ 2) :=
    mul_le_mul_of_nonneg_right hremainder hsecond_nonneg
  exact hBennett.trans (Real.exp_le_exp.mpr hexponent)

/-- The sub-gamma MGF bound for a sum of finitely many iid centered scores.
The variance proxy is the one-draw second moment, and the factor `n` comes
solely from exact finite-product MGF factorization. -/
theorem finiteIidScoreSum_mgf_le_exp_subgamma
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (law : PMF α) (score : α → ℝ) {step : ℝ}
    (hstep : 0 ≤ step) (hstep_three : step < 3)
    (hupper : ∀ outcome, score outcome ≤ 1)
    (hcentered : pmfExp law score = 0) :
    pmfExp (pmfProduct (Fin n) α law)
        (fun sample => Real.exp (step * Probability.finiteIidScoreSum score sample)) ≤
      Real.exp ((n : ℝ) * (step ^ 2 / (2 * (1 - step / 3))) *
        pmfExp law (fun outcome => score outcome ^ 2)) := by
  let varianceProxy : ℝ := pmfExp law (fun outcome => score outcome ^ 2)
  let exponent : ℝ := (step ^ 2 / (2 * (1 - step / 3))) * varianceProxy
  have hone := finiteMGF_centered_le_exp_subgamma
    law score hstep hstep_three hupper hcentered
  change Probability.finiteMGF law score step ≤ Real.exp exponent at hone
  calc
    pmfExp (pmfProduct (Fin n) α law)
        (fun sample => Real.exp (step * Probability.finiteIidScoreSum score sample)) =
        (Probability.finiteMGF law score step) ^ n := by
          simpa using Probability.iid_sum_mgf (ι := Fin n) law score step
    _ ≤ (Real.exp exponent) ^ n :=
      pow_le_pow_left₀ (Probability.finiteMGF_nonneg law score step) hone n
    _ = Real.exp ((n : ℝ) * (step ^ 2 / (2 * (1 - step / 3))) *
        pmfExp law (fun outcome => score outcome ^ 2)) := by
      rw [← Real.exp_nat_mul]
      dsimp [exponent, varianceProxy]
      ring_nf

/-- A finite iid Bennett--Bernstein Chernoff bound at an arbitrary admissible
positive dual parameter.  The next theorem performs the standard explicit
optimization of this display. -/
theorem pmfProb_finiteIidScoreSum_upperTail_le_exp_subgamma
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (law : PMF α) (score : α → ℝ) {threshold step : ℝ}
    (hstep : 0 < step) (hstep_three : step < 3)
    (hupper : ∀ outcome, score outcome ≤ 1)
    (hcentered : pmfExp law score = 0) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample => threshold < Probability.finiteIidScoreSum score sample) ≤
      Real.exp (-step * threshold +
        (n : ℝ) * (step ^ 2 / (2 * (1 - step / 3))) *
          pmfExp law (fun outcome => score outcome ^ 2)) := by
  let sumScore : (Fin n → α) → ℝ :=
    fun sample => Probability.finiteIidScoreSum score sample
  let exponent : ℝ := (n : ℝ) * (step ^ 2 / (2 * (1 - step / 3))) *
    pmfExp law (fun outcome => score outcome ^ 2)
  have hmgf := finiteIidScoreSum_mgf_le_exp_subgamma
    (n := n) law score hstep.le hstep_three hupper hcentered
  change Probability.finiteMGF (pmfProduct (Fin n) α law) sumScore step ≤
    Real.exp exponent at hmgf
  have hlog : Probability.finiteLogMGF (pmfProduct (Fin n) α law) sumScore step ≤
      exponent := by
    unfold Probability.finiteLogMGF
    exact (Real.log_le_iff_le_exp
      (Probability.finiteMGF_pos (pmfProduct (Fin n) α law) sumScore step)).mpr hmgf
  calc
    pmfProb (pmfProduct (Fin n) α law) (fun sample => threshold < sumScore sample) ≤
        Real.exp (-step * threshold +
          Probability.finiteLogMGF (pmfProduct (Fin n) α law) sumScore step) :=
      pmfProb_upperTail_le_exp_neg_mul_add_finiteLogMGF
        (pmfProduct (Fin n) α law) sumScore threshold step hstep
    _ ≤ Real.exp (-step * threshold + exponent) := by
      gcongr

/-- The explicitly optimized finite iid Bennett--Bernstein upper tail.  The
condition on `varianceProxy` isolates the nondegenerate case; a zero proxy is
handled from the support identities of the particular statistic. -/
theorem pmfProb_finiteIidScoreSum_upperTail_le_exp_neg
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (law : PMF α) (score : α → ℝ) {logFactor : ℝ}
    (hlogFactor : 0 < logFactor)
    (hupper : ∀ outcome, score outcome ≤ 1)
    (hcentered : pmfExp law score = 0)
    (hvariance : 0 < (n : ℝ) * pmfExp law (fun outcome => score outcome ^ 2)) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          Real.sqrt (2 * ((n : ℝ) *
            pmfExp law (fun outcome => score outcome ^ 2)) * logFactor) +
            logFactor / 3 <
            Probability.finiteIidScoreSum score sample) ≤
      Real.exp (-logFactor) := by
  let varianceProxy : ℝ :=
    (n : ℝ) * pmfExp law (fun outcome => score outcome ^ 2)
  let root : ℝ := Real.sqrt (2 * logFactor / varianceProxy)
  let step : ℝ := root / (1 + root / 3)
  have hroot_sq : root ^ 2 = 2 * logFactor / varianceProxy := by
    dsimp [root]
    rw [Real.sq_sqrt]
    positivity
  have hroot_pos : 0 < root := by
    rw [Real.sqrt_pos]
    dsimp [varianceProxy]
    exact div_pos (by positivity) hvariance
  have hdenominator_pos : 0 < 1 + root / 3 := by positivity
  have hstep : 0 < step := div_pos hroot_pos hdenominator_pos
  have hstep_three : step < 3 := by
    apply (div_lt_iff₀ hdenominator_pos).2
    nlinarith
  have hvariance_root_sq : varianceProxy * root ^ 2 = 2 * logFactor := by
    rw [hroot_sq]
    field_simp [hvariance.ne']
    exact div_self hvariance.ne'
  have htail := pmfProb_finiteIidScoreSum_upperTail_le_exp_subgamma
    (n := n) law score (threshold := varianceProxy * root + logFactor / 3)
      hstep hstep_three hupper hcentered
  have hproduct :
      (n : ℝ) * (step ^ 2 / (2 * (1 - step / 3))) *
          pmfExp law (fun outcome => score outcome ^ 2) =
        varianceProxy * (step ^ 2 / (2 * (1 - step / 3))) := by
    dsimp [varianceProxy]
    ring
  rw [hproduct] at htail
  have hthreshold : varianceProxy * root =
      Real.sqrt (2 * varianceProxy * logFactor) := by
    calc
      varianceProxy * root =
          varianceProxy * Real.sqrt ((2 * logFactor) / varianceProxy) := by rfl
      _ = Real.sqrt (varianceProxy * (2 * logFactor)) :=
        Probability.mul_sqrt_div_eq_sqrt_mul_of_pos hvariance
          (by positivity : 0 < 2 * logFactor)
      _ = Real.sqrt (2 * varianceProxy * logFactor) := by
        congr 1
        ring
  rw [hthreshold] at htail
  have hexponent :
      -step * (varianceProxy * root + logFactor / 3) +
        varianceProxy * (step ^ 2 / (2 * (1 - step / 3))) = -logFactor := by
    dsimp [step]
    field_simp [hdenominator_pos.ne']
    nlinarith [hvariance_root_sq]
  have hexponent' :
      -step * (Real.sqrt (2 * varianceProxy * logFactor) + logFactor / 3) +
        varianceProxy * (step ^ 2 / (2 * (1 - step / 3))) = -logFactor := by
    rw [← hthreshold]
    exact hexponent
  calc
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample => Real.sqrt (2 * varianceProxy * logFactor) + logFactor / 3 <
          Probability.finiteIidScoreSum score sample) ≤
        Real.exp (-step * (Real.sqrt (2 * varianceProxy * logFactor) + logFactor / 3) +
          varianceProxy * (step ^ 2 / (2 * (1 - step / 3)))) := htail
    _ = Real.exp (-logFactor) := by rw [hexponent']

/-- The nondegenerate fixed-sample empirical-mean form of the finite
Bennett--Bernstein bound.  Its confidence radius is written over the common
denominator `n`, which is algebraically the familiar
`sqrt (2 * variance * logFactor / n) + logFactor / (3 * n)` form. -/
theorem pmfProb_finiteSampleMean_upperTail_le_exp_neg
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) {logFactor : ℝ}
    (hn : 0 < n) (hlogFactor : 0 < logFactor)
    (hunit : ∀ outcome, 0 ≤ statistic outcome ∧ statistic outcome ≤ 1)
    (hvariance : 0 < pmfVariance law statistic) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          pmfExp law statistic +
              (Real.sqrt (2 * (n : ℝ) * pmfVariance law statistic * logFactor) +
                logFactor / 3) / (n : ℝ) <
            finiteRealSampleMean (statistic ∘ sample)) ≤
      Real.exp (-logFactor) := by
  let mean : ℝ := pmfExp law statistic
  let centered : α → ℝ := fun outcome => statistic outcome - mean
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmean_nonneg : 0 ≤ mean := by
    dsimp [mean]
    exact pmfExp_nonneg_of_forall_nonneg law statistic (fun outcome =>
      (hunit outcome).1)
  have hupper : ∀ outcome, centered outcome ≤ 1 := by
    intro outcome
    calc
      centered outcome = statistic outcome - mean := rfl
      _ ≤ statistic outcome := sub_le_self _ hmean_nonneg
      _ ≤ 1 := (hunit outcome).2
  have hcentered : pmfExp law centered = 0 := by
    dsimp [centered]
    rw [pmfExp_sub, pmfExp_const]
    dsimp [mean]
    ring
  have hvariance' : 0 < (n : ℝ) *
      pmfExp law (fun outcome => centered outcome ^ 2) := by
    dsimp [centered, mean]
    change 0 < (n : ℝ) * pmfVariance law statistic
    exact mul_pos hn_real hvariance
  have htail := pmfProb_finiteIidScoreSum_upperTail_le_exp_neg
    (n := n) law centered hlogFactor hupper hcentered hvariance'
  have hsum_centered (sample : Fin n → α) :
      Probability.finiteIidScoreSum centered sample =
        Probability.finiteIidScoreSum statistic sample - (n : ℝ) * mean := by
    unfold Probability.finiteIidScoreSum
    dsimp [centered]
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hsample_mean (sample : Fin n → α) :
      finiteRealSampleMean (statistic ∘ sample) =
        Probability.finiteIidScoreSum statistic sample / (n : ℝ) := by
    rw [finiteRealSampleMean_eq_div]
    unfold Probability.finiteIidScoreSum
    rfl
  let radiusNumerator : ℝ :=
    Real.sqrt (2 * (n : ℝ) * pmfVariance law statistic * logFactor) + logFactor / 3
  have htail_event : ∀ sample : Fin n → α,
      radiusNumerator < Probability.finiteIidScoreSum centered sample ↔
        mean + radiusNumerator / (n : ℝ) <
          finiteRealSampleMean (statistic ∘ sample) := by
    intro sample
    rw [hsum_centered, hsample_mean]
    have hleft : mean + radiusNumerator / (n : ℝ) =
        ((n : ℝ) * mean + radiusNumerator) / (n : ℝ) := by
      field_simp [hn_real.ne']
    rw [hleft]
    constructor <;> intro h
    · apply (div_lt_div_iff₀ hn_real hn_real).2
      apply mul_lt_mul_of_pos_right _ hn_real
      linarith
    · have h' := (div_lt_div_iff₀ hn_real hn_real).1 h
      have hsum := lt_of_mul_lt_mul_right h' hn_real.le
      linarith
  have hsecond : pmfExp law (fun outcome => centered outcome ^ 2) =
      pmfVariance law statistic := by
    rfl
  have hradius :
      Real.sqrt (2 * ((n : ℝ) *
          pmfExp law (fun outcome => centered outcome ^ 2)) * logFactor) +
        logFactor / 3 = radiusNumerator := by
    rw [hsecond]
    dsimp [radiusNumerator]
    congr 1
    ring_nf
  rw [hradius] at htail
  rw [pmfProb_congr _ htail_event] at htail
  simpa [radiusNumerator, mean] using htail

/-- The nondegenerate lower empirical-mean form of the finite
Bennett--Bernstein bound.  It is the orientation used in Maurer--Pontil's
empirical Bernstein theorem. -/
theorem pmfProb_finiteSampleMean_lowerTail_le_exp_neg
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) {logFactor : ℝ}
    (hn : 0 < n) (hlogFactor : 0 < logFactor)
    (hunit : ∀ outcome, 0 ≤ statistic outcome ∧ statistic outcome ≤ 1)
    (hvariance : 0 < pmfVariance law statistic) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          finiteRealSampleMean (statistic ∘ sample) <
            pmfExp law statistic -
              (Real.sqrt (2 * (n : ℝ) * pmfVariance law statistic * logFactor) +
                logFactor / 3) / (n : ℝ)) ≤
      Real.exp (-logFactor) := by
  let mean : ℝ := pmfExp law statistic
  let centered : α → ℝ := fun outcome => mean - statistic outcome
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmean_le_one : mean ≤ 1 := by
    dsimp [mean]
    exact pmfExp_le_of_forall_le law statistic 1 (fun outcome =>
      (hunit outcome).2)
  have hupper : ∀ outcome, centered outcome ≤ 1 := by
    intro outcome
    calc
      centered outcome = mean - statistic outcome := rfl
      _ ≤ mean := sub_le_self _ (hunit outcome).1
      _ ≤ 1 := hmean_le_one
  have hcentered : pmfExp law centered = 0 := by
    dsimp [centered]
    rw [pmfExp_sub, pmfExp_const]
    dsimp [mean]
    ring
  have hsecond : pmfExp law (fun outcome => centered outcome ^ 2) =
      pmfVariance law statistic := by
    dsimp [centered, mean]
    unfold pmfVariance
    apply pmfExp_congr
    intro outcome
    ring
  have hvariance' : 0 < (n : ℝ) *
      pmfExp law (fun outcome => centered outcome ^ 2) := by
    rw [hsecond]
    exact mul_pos hn_real hvariance
  have htail := pmfProb_finiteIidScoreSum_upperTail_le_exp_neg
    (n := n) law centered hlogFactor hupper hcentered hvariance'
  have hsum_centered (sample : Fin n → α) :
      Probability.finiteIidScoreSum centered sample =
        (n : ℝ) * mean - Probability.finiteIidScoreSum statistic sample := by
    unfold Probability.finiteIidScoreSum
    dsimp [centered]
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hsample_mean (sample : Fin n → α) :
      finiteRealSampleMean (statistic ∘ sample) =
        Probability.finiteIidScoreSum statistic sample / (n : ℝ) := by
    rw [finiteRealSampleMean_eq_div]
    unfold Probability.finiteIidScoreSum
    rfl
  let radiusNumerator : ℝ :=
    Real.sqrt (2 * (n : ℝ) * pmfVariance law statistic * logFactor) + logFactor / 3
  have htail_event : ∀ sample : Fin n → α,
      radiusNumerator < Probability.finiteIidScoreSum centered sample ↔
        finiteRealSampleMean (statistic ∘ sample) <
          mean - radiusNumerator / (n : ℝ) := by
    intro sample
    rw [hsum_centered, hsample_mean]
    have hright : mean - radiusNumerator / (n : ℝ) =
        ((n : ℝ) * mean - radiusNumerator) / (n : ℝ) := by
      field_simp [hn_real.ne']
    rw [hright]
    constructor <;> intro h
    · apply (div_lt_div_iff_of_pos_right hn_real).2
      linarith
    · have hsum := (div_lt_div_iff_of_pos_right hn_real).1 h
      linarith
  have hradius :
      Real.sqrt (2 * ((n : ℝ) *
          pmfExp law (fun outcome => centered outcome ^ 2)) * logFactor) +
        logFactor / 3 = radiusNumerator := by
    rw [hsecond]
    dsimp [radiusNumerator]
    congr 1
    ring_nf
  rw [hradius] at htail
  rw [pmfProb_congr _ htail_event] at htail
  simpa [radiusNumerator, mean] using htail

/-- A zero finite-PMF variance forces the statistic to equal its mean on every
positive-mass atom. -/
theorem pmfVariance_eq_zero_forces_support_eq_mean
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) (statistic : α → ℝ)
    (hvariance : pmfVariance law statistic = 0) :
    ∀ outcome, 0 < (law outcome).toReal →
      statistic outcome = pmfExp law statistic := by
  intro outcome hmass
  have hsum : ∑ atom : α,
      (law atom).toReal * (statistic atom - pmfExp law statistic) ^ 2 = 0 := by
    simpa [pmfVariance, pmfExp] using hvariance
  have hterm : (law outcome).toReal *
      (statistic outcome - pmfExp law statistic) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun atom _ =>
      mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))).mp hsum outcome
      (Finset.mem_univ _)
  have hsquare : (statistic outcome - pmfExp law statistic) ^ 2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left hmass.ne'
  nlinarith

/-- In the degenerate population-variance case, a positive-radius upper
empirical-mean failure has zero probability under the finite iid product. -/
theorem pmfProb_finiteSampleMean_upperTail_eq_zero_of_pmfVariance_eq_zero
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) {logFactor : ℝ}
    (hn : 0 < n) (hlogFactor : 0 < logFactor)
    (hvariance : pmfVariance law statistic = 0) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          pmfExp law statistic +
              (Real.sqrt (2 * (n : ℝ) * pmfVariance law statistic * logFactor) +
                logFactor / 3) / (n : ℝ) <
            finiteRealSampleMean (statistic ∘ sample)) = 0 := by
  let mean : ℝ := pmfExp law statistic
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsupport := pmfVariance_eq_zero_forces_support_eq_mean
    law statistic hvariance
  apply pmfProb_eq_zero_of_no_mass
  intro sample hfailure
  by_contra hproduct_zero
  have hproduct_pos : 0 < (pmfProduct (Fin n) α law sample).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hproduct_zero)
  have hcoordinate_mass : ∀ index : Fin n, 0 < (law (sample index)).toReal := by
    intro index
    by_contra hnot_pos
    have hcoordinate_zero : (law (sample index)).toReal = 0 :=
      le_antisymm (le_of_not_gt hnot_pos) ENNReal.toReal_nonneg
    have hproduct_zero' : (pmfProduct (Fin n) α law sample).toReal = 0 := by
      rw [pmfProduct_apply_toReal]
      exact Finset.prod_eq_zero (Finset.mem_univ index) hcoordinate_zero
    exact hproduct_pos.ne' hproduct_zero'
  have hsample_mean : finiteRealSampleMean (statistic ∘ sample) = mean := by
    rw [finiteRealSampleMean_eq_div]
    have hsum : ∑ index : Fin n, (statistic ∘ sample) index = (n : ℝ) * mean := by
      simp only [Function.comp_apply]
      calc
        ∑ index : Fin n, statistic (sample index) = ∑ _index : Fin n, mean := by
          apply Finset.sum_congr rfl
          intro index _
          exact hsupport (sample index) (hcoordinate_mass index)
        _ = (n : ℝ) * mean := by simp [nsmul_eq_mul]
    rw [hsum]
    field_simp [hn_real.ne']
  rw [hvariance, hsample_mean] at hfailure
  have hpositive_radius : 0 < (logFactor / 3) / (n : ℝ) := by
    exact div_pos (div_pos hlogFactor (by norm_num)) hn_real
  dsimp [mean] at hfailure
  norm_num at hfailure
  linarith

/-- In the degenerate population-variance case, a positive-radius lower
empirical-mean failure has zero probability under the finite iid product. -/
theorem pmfProb_finiteSampleMean_lowerTail_eq_zero_of_pmfVariance_eq_zero
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) {logFactor : ℝ}
    (hn : 0 < n) (hlogFactor : 0 < logFactor)
    (hvariance : pmfVariance law statistic = 0) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          finiteRealSampleMean (statistic ∘ sample) <
            pmfExp law statistic -
              (Real.sqrt (2 * (n : ℝ) * pmfVariance law statistic * logFactor) +
                logFactor / 3) / (n : ℝ)) = 0 := by
  let mean : ℝ := pmfExp law statistic
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsupport := pmfVariance_eq_zero_forces_support_eq_mean
    law statistic hvariance
  apply pmfProb_eq_zero_of_no_mass
  intro sample hfailure
  by_contra hproduct_zero
  have hproduct_pos : 0 < (pmfProduct (Fin n) α law sample).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hproduct_zero)
  have hcoordinate_mass : ∀ index : Fin n, 0 < (law (sample index)).toReal := by
    intro index
    by_contra hnot_pos
    have hcoordinate_zero : (law (sample index)).toReal = 0 :=
      le_antisymm (le_of_not_gt hnot_pos) ENNReal.toReal_nonneg
    have hproduct_zero' : (pmfProduct (Fin n) α law sample).toReal = 0 := by
      rw [pmfProduct_apply_toReal]
      exact Finset.prod_eq_zero (Finset.mem_univ index) hcoordinate_zero
    exact hproduct_pos.ne' hproduct_zero'
  have hsample_mean : finiteRealSampleMean (statistic ∘ sample) = mean := by
    rw [finiteRealSampleMean_eq_div]
    have hsum : ∑ index : Fin n, (statistic ∘ sample) index = (n : ℝ) * mean := by
      simp only [Function.comp_apply]
      calc
        ∑ index : Fin n, statistic (sample index) = ∑ _index : Fin n, mean := by
          apply Finset.sum_congr rfl
          intro index _
          exact hsupport (sample index) (hcoordinate_mass index)
        _ = (n : ℝ) * mean := by simp [nsmul_eq_mul]
    rw [hsum]
    field_simp [hn_real.ne']
  rw [hvariance, hsample_mean] at hfailure
  have hpositive_radius : 0 < (logFactor / 3) / (n : ℝ) := by
    exact div_pos (div_pos hlogFactor (by norm_num)) hn_real
  dsimp [mean] at hfailure
  norm_num at hfailure
  linarith

/-- The finite fixed-sample Bennett--Bernstein empirical-mean tail, including
the zero-population-variance case. -/
theorem pmfProb_finiteSampleMean_upperTail_le_exp_neg_of_unit
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) {logFactor : ℝ}
    (hn : 0 < n) (hlogFactor : 0 < logFactor)
    (hunit : ∀ outcome, 0 ≤ statistic outcome ∧ statistic outcome ≤ 1) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          pmfExp law statistic +
              (Real.sqrt (2 * (n : ℝ) * pmfVariance law statistic * logFactor) +
                logFactor / 3) / (n : ℝ) <
            finiteRealSampleMean (statistic ∘ sample)) ≤
      Real.exp (-logFactor) := by
  by_cases hvariance : pmfVariance law statistic = 0
  · rw [pmfProb_finiteSampleMean_upperTail_eq_zero_of_pmfVariance_eq_zero
      law statistic hn hlogFactor hvariance]
    exact Real.exp_nonneg _
  · exact pmfProb_finiteSampleMean_upperTail_le_exp_neg
      law statistic hn hlogFactor hunit
        (lt_of_le_of_ne (pmfVariance_nonneg law statistic) (Ne.symm hvariance))

/-- The finite fixed-sample lower Bennett--Bernstein empirical-mean tail,
including the zero-population-variance case. -/
theorem pmfProb_finiteSampleMean_lowerTail_le_exp_neg_of_unit
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) {logFactor : ℝ}
    (hn : 0 < n) (hlogFactor : 0 < logFactor)
    (hunit : ∀ outcome, 0 ≤ statistic outcome ∧ statistic outcome ≤ 1) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          finiteRealSampleMean (statistic ∘ sample) <
            pmfExp law statistic -
              (Real.sqrt (2 * (n : ℝ) * pmfVariance law statistic * logFactor) +
                logFactor / 3) / (n : ℝ)) ≤
      Real.exp (-logFactor) := by
  by_cases hvariance : pmfVariance law statistic = 0
  · rw [pmfProb_finiteSampleMean_lowerTail_eq_zero_of_pmfVariance_eq_zero
      law statistic hn hlogFactor hvariance]
    exact Real.exp_nonneg _
  · exact pmfProb_finiteSampleMean_lowerTail_le_exp_neg
      law statistic hn hlogFactor hunit
        (lt_of_le_of_ne (pmfVariance_nonneg law statistic) (Ne.symm hvariance))

/-- The number of ordered index pairs with `i < j` in `Fin n`. -/
private theorem finiteBennett_sum_pair_lt_indicator (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  classical
  cases n with
  | zero => norm_num
  | succ n =>
      have hinner (i : Fin (n + 1)) :
          (∑ j : Fin (n + 1), if i < j then (1 : ℝ) else 0) =
            ((n + 1 - 1 - i : ℕ) : ℝ) := by
        calc
          (∑ j : Fin (n + 1), if i < j then (1 : ℝ) else 0) =
              ∑ j ∈ Finset.Ioi i, (1 : ℝ) := by
                rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
          _ = ((Finset.Ioi i).card : ℝ) := by simp
          _ = ((n + 1 - 1 - i : ℕ) : ℝ) := by simp
      calc
        (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), if i < j then (1 : ℝ) else 0) =
            ∑ i : Fin (n + 1), ((n + 1 - 1 - i : ℕ) : ℝ) := by
              apply Finset.sum_congr rfl
              intro i _
              exact hinner i
        _ = ∑ i ∈ Finset.range (n + 1), ((n + 1 - 1 - i : ℕ) : ℝ) := by
          rw [← Fin.sum_univ_eq_sum_range]
        _ = ∑ i ∈ Finset.range (n + 1), (i : ℝ) :=
          Finset.sum_range_reflect (fun i : ℕ => (i : ℝ)) (n + 1)
        _ = ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) / 2 := by
          have hgauss := Finset.sum_range_id_mul_two (n + 1)
          have hgauss_real :
              (∑ i ∈ Finset.range (n + 1), (i : ℝ)) * 2 =
                ((n + 1 : ℕ) : ℝ) * (n : ℝ) := by
            calc
              (∑ i ∈ Finset.range (n + 1), (i : ℝ)) * 2 =
                  ((∑ i ∈ Finset.range (n + 1), i : ℕ) : ℝ) * 2 := by
                    rw [Nat.cast_sum]
              _ = (((∑ i ∈ Finset.range (n + 1), i : ℕ) * 2 : ℕ) : ℝ) := by
                    norm_num
              _ = (((n + 1) * ((n + 1) - 1) : ℕ) : ℝ) :=
                    congrArg Nat.cast hgauss
              _ = ((n + 1 : ℕ) : ℝ) * (n : ℝ) := by norm_num
          norm_num [Nat.cast_add] at hgauss_real ⊢
          linarith

/-- The literal Maurer--Pontil pairwise variance is unbiased under a finite
iid product. -/
theorem pmfExp_finiteSamplePairwiseVariance_eq_pmfVariance
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n) :
    pmfExp (pmfProduct (Fin n) α law)
        (fun sample => finiteSamplePairwiseVariance (statistic ∘ sample)) =
      pmfVariance law statistic := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let pairEnergy : ℝ :=
    pmfPairExp law law (fun first second => (statistic first - statistic second) ^ 2)
  have hpairEnergy : pairEnergy = 2 * pmfVariance law statistic := by
    dsimp [pairEnergy]
    have hvariance := pmfVariance_eq_half_pmfPairExp_sq_sub law statistic
    linarith
  have hterm (i j : Fin n) :
      pmfExp productLaw (fun sample =>
        if i < j then (statistic (sample i) - statistic (sample j)) ^ 2 else 0) =
        if i < j then pairEnergy else 0 := by
    by_cases hij : i < j
    · have hdistinct : i ≠ j := ne_of_lt hij
      simp only [hij, ↓reduceIte]
      dsimp [productLaw, pairEnergy]
      exact pmfExp_pmfProduct_two_eval law hdistinct
        (fun first second => (statistic first - statistic second) ^ 2)
    · simp [hij]
  have hordered :
      pmfExp productLaw (fun sample =>
        finiteSampleOrderedPairSqSum (statistic ∘ sample)) =
        ∑ i : Fin n, ∑ j : Fin n, if i < j then pairEnergy else 0 := by
    unfold finiteSampleOrderedPairSqSum
    calc
      pmfExp productLaw (fun sample =>
          ∑ i : Fin n, ∑ j : Fin n,
            if i < j then ((statistic ∘ sample) i - (statistic ∘ sample) j) ^ 2 else 0) =
          ∑ i : Fin n, pmfExp productLaw (fun sample =>
            ∑ j : Fin n,
              if i < j then ((statistic ∘ sample) i - (statistic ∘ sample) j) ^ 2 else 0) :=
            pmfExp_univ_sum productLaw _
      _ = ∑ i : Fin n, ∑ j : Fin n, pmfExp productLaw (fun sample =>
            if i < j then (statistic (sample i) - statistic (sample j)) ^ 2 else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [pmfExp_univ_sum]
            apply Finset.sum_congr rfl
            intro j _
            rfl
      _ = ∑ i : Fin n, ∑ j : Fin n, if i < j then pairEnergy else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact hterm i j
  have hpair_sum :
      (∑ i : Fin n, ∑ j : Fin n, if i < j then pairEnergy else 0) =
        ((n : ℝ) * ((n : ℝ) - 1) / 2) * pairEnergy := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, if i < j then pairEnergy else 0) =
          ∑ i : Fin n, ∑ j : Fin n,
            (if i < j then (1 : ℝ) else 0) * pairEnergy := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              by_cases hij : i < j <;> simp [hij]
      _ = ∑ i : Fin n,
          (∑ j : Fin n, if i < j then (1 : ℝ) else 0) * pairEnergy := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
      _ = (∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0) *
          pairEnergy := by
            rw [Finset.sum_mul]
      _ = ((n : ℝ) * ((n : ℝ) - 1) / 2) * pairEnergy := by
            rw [finiteBennett_sum_pair_lt_indicator]
  have hden_pos : 0 < (n : ℝ) * ((n : ℝ) - 1) := by
    have hn_real : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
    exact mul_pos (by linarith) (by linarith)
  calc
    pmfExp (pmfProduct (Fin n) α law)
        (fun sample => finiteSamplePairwiseVariance (statistic ∘ sample)) =
        pmfExp productLaw (fun sample =>
          finiteSampleOrderedPairSqSum (statistic ∘ sample) /
            ((n : ℝ) * ((n : ℝ) - 1))) := by rfl
    _ = pmfExp productLaw (fun sample =>
        finiteSampleOrderedPairSqSum (statistic ∘ sample)) /
          ((n : ℝ) * ((n : ℝ) - 1)) := by
            rw [show (fun sample : Fin n → α =>
              finiteSampleOrderedPairSqSum (statistic ∘ sample) /
                ((n : ℝ) * ((n : ℝ) - 1))) =
              fun sample => finiteSampleOrderedPairSqSum (statistic ∘ sample) *
                (1 / ((n : ℝ) * ((n : ℝ) - 1))) by
                funext sample
                ring]
            rw [pmfExp_mul_const]
            ring
    _ = (((n : ℝ) * ((n : ℝ) - 1) / 2) * pairEnergy) /
          ((n : ℝ) * ((n : ℝ) - 1)) := by rw [hordered, hpair_sum]
    _ = pmfVariance law statistic := by
      rw [hpairEnergy]
      field_simp [hden_pos.ne']
      exact mul_div_cancel_left₀ _ (mul_ne_zero_iff.mp hden_pos.ne').2

/-- The usual unbiased finite sample variance has population expectation equal
to the population variance under a finite iid product. -/
theorem pmfExp_finiteSampleUnbiasedVariance_eq_pmfVariance
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n) :
    pmfExp (pmfProduct (Fin n) α law)
        (fun sample => finiteSampleUnbiasedVariance (statistic ∘ sample)) =
      pmfVariance law statistic := by
  calc
    pmfExp (pmfProduct (Fin n) α law)
        (fun sample => finiteSampleUnbiasedVariance (statistic ∘ sample)) =
        pmfExp (pmfProduct (Fin n) α law)
          (fun sample => finiteSamplePairwiseVariance (statistic ∘ sample)) := by
            apply pmfExp_congr
            intro sample
            exact (finiteSamplePairwiseVariance_eq_unbiasedVariance
              (statistic ∘ sample) hn).symm
    _ = pmfVariance law statistic :=
      pmfExp_finiteSamplePairwiseVariance_eq_pmfVariance law statistic hn

end

end AppliedModelingLib
