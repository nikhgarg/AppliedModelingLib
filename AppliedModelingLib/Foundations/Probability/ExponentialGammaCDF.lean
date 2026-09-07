import AppliedModelingLib.Foundations.Probability.ExponentialGammaConvolution

/-!
# Integer-shape Gamma/Erlang CDFs

This module proves the finite Erlang-series CDF formula for every positive
integer-shape Gamma law. Together with the existing convolution theorem for
canonical exponential interarrivals, it supplies the analytic input for the
renewal-count-to-Poisson marginal calculation.
-/

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-- The finite exponential-series factor in an integer-shape Gamma tail. -/
def erlangTailPolynomial (n : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), z ^ k / (k.factorial : ℝ)

theorem erlangTailPolynomial_succ (n : ℕ) (z : ℝ) :
    erlangTailPolynomial (n + 1) z =
      erlangTailPolynomial n z + z ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  simp [erlangTailPolynomial, Finset.sum_range_succ, Nat.add_assoc]

/-- Differentiating one additional finite-series term recovers the preceding
Erlang tail polynomial. -/
theorem hasDerivAt_erlangTailPolynomial_succ (n : ℕ) (z : ℝ) :
    HasDerivAt (erlangTailPolynomial (n + 1)) (erlangTailPolynomial n z) z := by
  induction n with
  | zero =>
      have hfun : erlangTailPolynomial 1 = fun u : ℝ => 1 + u := by
        funext u
        simp [erlangTailPolynomial, Finset.sum_range_succ]
      rw [hfun]
      have hzero : erlangTailPolynomial 0 z = 1 := by
        simp [erlangTailPolynomial]
      rw [hzero]
      have hfun' : (fun u : ℝ => 1 + u) = (fun _ : ℝ => 1) + id := by
        funext u
        rfl
      rw [hfun']
      convert (hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_id z) using 1
      all_goals norm_num
  | succ n ih =>
      rw [erlangTailPolynomial_succ]
      have hterm : HasDerivAt
          (fun u : ℝ => u ^ (n + 2) / ((n + 2).factorial : ℝ))
          (((n + 2 : ℕ) : ℝ) * z ^ (n + 1) / ((n + 2).factorial : ℝ)) z := by
        simpa [Nat.succ_eq_add_one] using
          ((hasDerivAt_id z).pow (n + 2)).div_const ((n + 2).factorial : ℝ)
      have hadd := ih.add hterm
      convert hadd using 1
      · ext u
        simpa [Nat.add_assoc] using (erlangTailPolynomial_succ (n + 1) u)
      · congr 1
        have hfac : ((n + 2).factorial : ℝ) =
            ((n + 2 : ℕ) : ℝ) * ((n + 1).factorial : ℝ) := by
          exact_mod_cast Nat.factorial_succ (n + 1)
        rw [hfac]
        have hfac_ne : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
        have hsucc_ne : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hfac_ne, hsucc_ne]

/-- The survival-function candidate for an integer-shape Gamma law. -/
def erlangTail (n : ℕ) (rate t : ℝ) : ℝ :=
  Real.exp (-(rate * t)) * erlangTailPolynomial n (rate * t)

/-- Its derivative is the negative integer-shape Gamma density. -/
theorem hasDerivAt_erlangTail
    (n : ℕ) (rate t : ℝ) :
    HasDerivAt (erlangTail n rate)
      (-(rate ^ (n + 1) / (n.factorial : ℝ) * t ^ n *
        Real.exp (-(rate * t)))) t := by
  cases n with
  | zero =>
      unfold erlangTail
      have hpoly0 : erlangTailPolynomial 0 = fun _ : ℝ => 1 := by
        funext z
        simp [erlangTailPolynomial]
      rw [hpoly0]
      have hlin : HasDerivAt (fun s : ℝ => -(rate * s)) (-rate) t := by
        convert ((hasDerivAt_id t).const_mul rate).neg using 1
        all_goals ring
      have hexp := hlin.exp
      convert hexp.mul (hasDerivAt_const t (1 : ℝ)) using 1
      all_goals norm_num
      ring
  | succ n =>
      unfold erlangTail
      have hlin : HasDerivAt (fun s : ℝ => rate * s) rate t := by
        convert (hasDerivAt_id t).const_mul rate using 1
        all_goals simp
      have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(rate * s)))
          (Real.exp (-(rate * t)) * (-rate)) t := by
        exact hlin.neg.exp
      have hpoly : HasDerivAt
          (fun s : ℝ => erlangTailPolynomial (n + 1) (rate * s))
          (erlangTailPolynomial n (rate * t) * rate) t := by
        exact (hasDerivAt_erlangTailPolynomial_succ n (rate * t)).comp t hlin
      convert hexp.mul hpoly using 1
      rw [erlangTailPolynomial_succ]
      have hfac : ((n + 1).factorial : ℝ) =
          ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) := by
        exact_mod_cast Nat.factorial_succ n
      rw [hfac]
      have hfac_ne : (n.factorial : ℝ) ≠ 0 := by positivity
      have hsucc_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
      ring_nf

/-- The Gamma density at a positive integer shape is its polynomial-times-
exponential form on the nonnegative half-line. -/
theorem gammaPDFReal_nat_succ_of_nonneg
    (n : ℕ) (rate t : ℝ) (ht : 0 ≤ t) :
    ProbabilityTheory.gammaPDFReal ((n + 1 : ℕ) : ℝ) rate t =
      rate ^ (n + 1) / (n.factorial : ℝ) * t ^ n *
        Real.exp (-(rate * t)) := by
  rw [ProbabilityTheory.gammaPDFReal, if_pos ht]
  have hpower : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by
    push_cast
    ring
  rw [Real.rpow_natCast, hpower, Real.rpow_natCast]
  have hshape : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
    push_cast
    ring
  rw [hshape, Real.Gamma_nat_eq_factorial n]

/-- The candidate CDF complementary to the Erlang survival polynomial. -/
def erlangCDFCandidate (n : ℕ) (rate t : ℝ) : ℝ :=
  1 - erlangTail n rate t

/-- The real density of the Gamma law with integer shape `n + 1`. -/
def erlangDensity (n : ℕ) (rate t : ℝ) : ℝ :=
  rate ^ (n + 1) / (n.factorial : ℝ) * t ^ n *
    Real.exp (-(rate * t))

/-- Its derivative is the integer-shape Gamma density. -/
theorem hasDerivAt_erlangCDFCandidate
    (n : ℕ) (rate t : ℝ) :
    HasDerivAt (erlangCDFCandidate n rate) (erlangDensity n rate t) t := by
  unfold erlangCDFCandidate erlangDensity
  convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_erlangTail n rate t) using 1
  all_goals ring

theorem erlangTailPolynomial_zero (n : ℕ) : erlangTailPolynomial n 0 = 1 := by
  induction n with
  | zero => simp [erlangTailPolynomial]
  | succ n ih =>
      rw [erlangTailPolynomial_succ, ih]
      simp

theorem erlangTail_zero (n : ℕ) (rate : ℝ) : erlangTail n rate 0 = 1 := by
  unfold erlangTail
  rw [mul_zero, neg_zero, Real.exp_zero, one_mul, erlangTailPolynomial_zero]

theorem continuous_erlangDensity (n : ℕ) (rate : ℝ) :
    Continuous (erlangDensity n rate) := by
  unfold erlangDensity
  fun_prop

theorem erlangDensity_nonneg (n : ℕ) {rate t : ℝ}
    (hr : 0 ≤ rate) (ht : 0 ≤ t) : 0 ≤ erlangDensity n rate t := by
  unfold erlangDensity
  positivity

theorem integral_erlangDensity_Icc_eq_erlangCDFCandidate
    (n : ℕ) (rate t : ℝ) (ht : 0 ≤ t) :
    ∫ x in Set.Icc 0 t, erlangDensity n rate x = erlangCDFCandidate n rate t := by
  have hinterval : ∫ x in 0..t, erlangDensity n rate x =
      erlangCDFCandidate n rate t - erlangCDFCandidate n rate 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _
      exact hasDerivAt_erlangCDFCandidate n rate x
    · exact (continuous_erlangDensity n rate).intervalIntegrable 0 t
  have hzero : erlangCDFCandidate n rate 0 = 0 := by
    simp [erlangCDFCandidate, erlangTail_zero]
  rw [hzero, sub_zero] at hinterval
  calc
    ∫ x in Set.Icc 0 t, erlangDensity n rate x =
        ∫ x in Set.Ioc 0 t, erlangDensity n rate x := integral_Icc_eq_integral_Ioc
    _ = ∫ x in Set.uIoc 0 t, erlangDensity n rate x := by rw [Set.uIoc_of_le ht]
    _ = ∫ x in 0..t, erlangDensity n rate x := by
      rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
      simp [ht]
    _ = erlangCDFCandidate n rate t := hinterval

theorem gammaPDF_nat_succ_of_nonneg_ennreal
    (n : ℕ) (rate t : ℝ) (ht : 0 ≤ t) :
    ProbabilityTheory.gammaPDF ((n + 1 : ℕ) : ℝ) rate t =
      ENNReal.ofReal (erlangDensity n rate t) := by
  unfold ProbabilityTheory.gammaPDF erlangDensity
  rw [gammaPDFReal_nat_succ_of_nonneg n rate t ht]

theorem erlangCDFCandidate_nonneg
    (n : ℕ) {rate t : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ t) :
    0 ≤ erlangCDFCandidate n rate t := by
  rw [← integral_erlangDensity_Icc_eq_erlangCDFCandidate n rate t ht]
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact erlangDensity_nonneg n hr hx.1

theorem lintegral_erlangDensity_Icc_eq_erlangCDFCandidate
    (n : ℕ) {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    ∫⁻ x in Set.Icc 0 t, ENNReal.ofReal (erlangDensity n rate x) =
      ENNReal.ofReal (erlangCDFCandidate n rate t) := by
  refine (ENNReal.toReal_eq_toReal_iff' ?_ ENNReal.ofReal_ne_top).mp ?_
  · exact ne_of_lt <|
      MeasureTheory.IntegrableOn.setLIntegral_lt_top
        ((continuous_erlangDensity n rate).continuousOn.integrableOn_Icc)
  rw [← integral_eq_lintegral_of_nonneg_ae]
  · rw [ENNReal.toReal_ofReal_eq_iff.2
      (erlangCDFCandidate_nonneg n hr.le ht)]
    exact integral_erlangDensity_Icc_eq_erlangCDFCandidate n rate t ht
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact erlangDensity_nonneg n hr.le hx.1
  · exact (continuous_erlangDensity n rate).aestronglyMeasurable

theorem lintegral_gammaPDF_nat_succ_Iic_eq_erlangCDFCandidate
    (n : ℕ) {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    ∫⁻ x in Set.Iic t,
      ProbabilityTheory.gammaPDF ((n + 1 : ℕ) : ℝ) rate x =
      ENNReal.ofReal (erlangCDFCandidate n rate t) := by
  rw [lintegral_Iic_eq_lintegral_Iio_add_Icc _ ht,
    ProbabilityTheory.lintegral_gammaPDF_of_nonpos (le_refl 0), zero_add]
  rw [setLIntegral_congr_fun measurableSet_Icc
    (g := fun x => ENNReal.ofReal (erlangDensity n rate x))
    (by
      intro x hx
      exact gammaPDF_nat_succ_of_nonneg_ennreal n rate x hx.1)]
  exact lintegral_erlangDensity_Icc_eq_erlangCDFCandidate n hr ht

/-- At nonnegative time `t`, an integer-shape Gamma measure has the finite
Erlang CDF `1 - exp (-rate * t) * sum_{k=0}^n (rate*t)^k/k!`. -/
theorem gammaMeasure_nat_succ_Iic_eq_erlangCDFCandidate
    (n : ℕ) {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate (Set.Iic t) =
      ENNReal.ofReal (erlangCDFCandidate n rate t) := by
  rw [ProbabilityTheory.gammaMeasure,
    MeasureTheory.withDensity_apply _ measurableSet_Iic]
  exact lintegral_gammaPDF_nat_succ_Iic_eq_erlangCDFCandidate n hr ht

theorem gammaMeasure_nat_succ_Iic_eq_erlangCDF
    (n : ℕ) {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate (Set.Iic t) =
      ENNReal.ofReal
        (1 - Real.exp (-(rate * t)) *
          ∑ k ∈ Finset.range (n + 1), (rate * t) ^ k / (k.factorial : ℝ)) := by
  simpa [erlangCDFCandidate, erlangTail, erlangTailPolynomial] using
    gammaMeasure_nat_succ_Iic_eq_erlangCDFCandidate n hr ht

theorem cdf_gammaMeasure_nat_succ_eq_erlangCDFCandidate
    (n : ℕ) {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    ProbabilityTheory.cdf
      (ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate) t =
      erlangCDFCandidate n rate t := by
  rw [ProbabilityTheory.cdf_gammaMeasure_eq_lintegral (by positivity) hr,
    lintegral_gammaPDF_nat_succ_Iic_eq_erlangCDFCandidate n hr ht,
    ENNReal.toReal_ofReal_eq_iff.2 (erlangCDFCandidate_nonneg n hr.le ht)]

/-- The CDF of a Gamma law of integer shape `n + 1` is the finite Erlang
series at every nonnegative time. -/
theorem cdf_gammaMeasure_nat_succ_eq_erlangCDF
    (n : ℕ) {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    ProbabilityTheory.cdf
      (ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate) t =
      1 - Real.exp (-(rate * t)) *
        ∑ k ∈ Finset.range (n + 1), (rate * t) ^ k / (k.factorial : ℝ) := by
  simpa [erlangCDFCandidate, erlangTail, erlangTailPolynomial] using
    cdf_gammaMeasure_nat_succ_eq_erlangCDFCandidate n hr ht

end
end PoissonProcess
end Probability
end AppliedModelingLib
