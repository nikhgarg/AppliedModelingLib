import KR21Monoculture.RUM

open AppliedModelingLib Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace KR21Monoculture

/-!
# Appendix C Formula Surface

This module exposes the displayed Appendix-C formulas themselves, rather than
crediting a final theorem for intermediate algebra.  The endpoints retain the
source's cutoff, score-gap, and strict-event conditions.  For the Gaussian
calculation, the C.8 prefactor is stated in its algebraically corrected form:
the printed prefactor does not factor the checked C.8 derivative into the C.9
bracket.
-/

/--
Appendix C (C.3), Laplace form: the strict source-event conditional
probability is exactly the density/CDF ratio used in the three-case proof.
-/
theorem equationC3_laplace_strict_conditional_ratio_eq_density_cdf
    {lam xi xj a : ℝ} (hlam : 0 < lam) :
    theorem7LaplacianProductStrictConditionalRatioAt lam xi xj a =
      (∫ x : ℝ in Set.Iic a,
        theorem7LaplacePDF lam xi x * theorem7LaplaceCDFClosedForm lam xj x) /
        (theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a) := by
  simpa [theorem7LaplacianPDFCDFRatioAt, theorem7LaplacianPairIntegrand] using
    theorem7LaplacianProductStrictConditionalRatioAt_eq_pdf_cdf
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam

/--
Appendix C (C.3), Gaussian form: the strict source-event conditional
probability is exactly the Gaussian density/CDF ratio.
-/
theorem equationC3_gaussian_strict_conditional_ratio_eq_density_cdf
    (xi xj a : ℝ) :
    theorem8GaussianProductStrictConditionalRatioAt xi xj a =
      (∫ x : ℝ in Set.Iic a,
        theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) /
        (theorem8GaussianCDF xi a * theorem8GaussianCDF xj a) := by
  simpa [theorem8GaussianPDFCDFRatioAt] using
    theorem8GaussianProductStrictConditionalRatioAt_eq_pdf_cdf xi xj a

/--
Appendix C (C.4), literal right-tail Laplace expression.  This is the source
expression after the case-3 quotient-rule reduction, with its stated
conditions `lambda > 0`, `x_j < x_i`, and `x_i < a`.
-/
theorem equationC4_laplace_case3_expression_pos
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi < a) :
    0 <
      Real.exp (-lam * (2 * a - xi - xj)) - 8 +
        4 * Real.exp (-lam * (a - xi)) -
        Real.exp (-2 * lam * (a - xi)) +
        (4 + 2 * lam * (xi - xj)) *
          (1 + Real.exp (-lam * (xi - xj))) -
        (4 + 2 * lam * (xi - xj)) *
          Real.exp (-lam * (a - xj)) := by
  let z : ℝ := lam * (xi - xj)
  let r : ℝ := Real.exp (-lam * (a - xi))
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos hlam (sub_pos.mpr hx)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (Real.exp_pos _).le
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (Real.exp_lt_one_iff.mpr (by
      have : 0 < lam * (a - xi) := mul_pos hlam (sub_pos.mpr ha)
      linarith)).le
  have hcore := paper_theorem7_laplacian_case3_derivative_poly_core hz hr0 hr1
  have hquad :
      Real.exp (-lam * (2 * a - xi - xj)) =
        Real.exp (-z) * r ^ 2 := by
    dsimp [z, r]
    calc
      Real.exp (-lam * (2 * a - xi - xj)) =
          Real.exp
            (-lam * (xi - xj) +
              (-lam * (a - xi) + -lam * (a - xi))) := by
            congr 1
            ring
      _ = Real.exp (-lam * (xi - xj)) *
          Real.exp (-lam * (a - xi) + -lam * (a - xi)) := by
            rw [Real.exp_add]
      _ = Real.exp (-lam * (xi - xj)) *
          (Real.exp (-lam * (a - xi)) * Real.exp (-lam * (a - xi))) := by
            rw [Real.exp_add]
      _ = Real.exp (-lam * (xi - xj)) *
          Real.exp (-lam * (a - xi)) ^ 2 := by ring
      _ = Real.exp (-(lam * (xi - xj))) *
          Real.exp (-lam * (a - xi)) ^ 2 := by
            rw [show -lam * (xi - xj) = -(lam * (xi - xj)) by ring]
  have htail :
      Real.exp (-lam * (a - xj)) = Real.exp (-z) * r := by
    dsimp [z, r]
    rw [← Real.exp_add]
    congr 1
    ring
  have hsq :
      Real.exp (-2 * lam * (a - xi)) = r ^ 2 := by
    dsimp [r]
    calc
      Real.exp (-2 * lam * (a - xi)) =
          Real.exp (-lam * (a - xi) + -lam * (a - xi)) := by
            congr 1
            ring
      _ = Real.exp (-lam * (a - xi)) * Real.exp (-lam * (a - xi)) := by
            rw [Real.exp_add]
      _ = Real.exp (-lam * (a - xi)) ^ 2 := by ring
  have hsource :
      Real.exp (-lam * (2 * a - xi - xj)) - 8 +
          4 * Real.exp (-lam * (a - xi)) -
          Real.exp (-2 * lam * (a - xi)) +
          (4 + 2 * lam * (xi - xj)) *
            (1 + Real.exp (-lam * (xi - xj))) -
          (4 + 2 * lam * (xi - xj)) *
            Real.exp (-lam * (a - xj)) =
        -(r ^ 2 * (1 - Real.exp (-z)) +
          r * (2 * Real.exp (-z) * z + 4 * Real.exp (-z) - 4) +
          (4 - 2 * Real.exp (-z) * z - 4 * Real.exp (-z) - 2 * z)) := by
    rw [hquad, htail, hsq]
    dsimp [z, r]
    ring_nf
  rw [hsource]
  linarith

/--
Appendix C (C.5), Gaussian conditional ratio after the source normalizes to
variance `1/2` and writes the density and CDF through `erf`.
-/
theorem equationC5_gaussian_density_cdf_ratio_eq_erf_integral
    (xi xj a : ℝ) :
    theorem8GaussianPDFCDFRatioAt xi xj a =
      (2 / Real.sqrt Real.pi) *
        (∫ x : ℝ in Set.Iic a,
          Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) /
        ((1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj))) := by
  simpa [theorem8GaussianDensityCDFIntegralRatioAt] using
    theorem8GaussianPDFCDFRatioAt_eq_densityCDF xi xj a

/--
Appendix C (C.5), exact quotient-rule factorization in the source cutoff
coordinate.  The derivative of the actual strict-event conditional ratio is
a positive factor times the literal displayed C.5 expression.
-/
theorem equationC5_gaussian_strict_conditional_ratio_hasDerivAt_factorization
    (xi xj a : ℝ) :
    HasDerivAt
      (fun u => theorem8GaussianProductStrictConditionalRatioAt xi xj u)
      ((2 / Real.sqrt Real.pi) /
        ((1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj))) ^ 2 *
        ((1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj)) *
            Real.exp (-((a - xi) ^ 2)) * (1 + theorem8Erf (a - xj)) -
          (∫ x : ℝ in Set.Iic a,
            Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) *
            (2 / Real.sqrt Real.pi) *
            ((1 + theorem8Erf (a - xi)) * Real.exp (-((a - xj) ^ 2)) +
              (1 + theorem8Erf (a - xj)) *
                Real.exp (-((a - xi) ^ 2))))) a := by
  let delta : ℝ := xi - xj
  let t : ℝ := a - xi
  let c : ℝ := 2 / Real.sqrt Real.pi
  let A : ℝ := 1 + theorem8Erf t
  let B : ℝ := 1 + theorem8Erf (t + delta)
  let p : ℝ := Real.exp (-(t ^ 2))
  let q : ℝ := Real.exp (-((t + delta) ^ 2))
  let J : ℝ := theorem8GaussianJ theorem8Erf delta t
  let I : ℝ := ∫ x : ℝ in Set.Iic a,
    Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))
  have hA : 0 < A := by
    dsimp [A]
    exact theorem8Erf_one_add_pos t
  have hB : 0 < B := by
    dsimp [B]
    exact theorem8Erf_one_add_pos (t + delta)
  have hden_prod_ne : A * B ≠ 0 :=
    (mul_pos hA hB).ne'
  have hA_deriv :
      HasDerivAt (fun u => 1 + theorem8Erf u) (c * p) t := by
    dsimp [c, p]
    simpa using (theorem8Erf_hasDerivAt t).const_add (1 : ℝ)
  have hshift_fun : HasDerivAt (fun u : ℝ => u + delta) 1 t := by
    simpa using (hasDerivAt_id t).add_const delta
  have hB_deriv :
      HasDerivAt (fun u => 1 + theorem8Erf (u + delta)) (c * q) t := by
    dsimp [c, q]
    simpa [one_mul] using
      ((theorem8Erf_hasDerivAt (t + delta)).comp t hshift_fun).const_add (1 : ℝ)
  have hJ_deriv :
      HasDerivAt
        (fun u => theorem8GaussianJ theorem8Erf delta u)
        (p * theorem8Erf (t + delta)) t := by
    dsimp [p]
    exact theorem8GaussianJ_hasDerivAt_concrete delta t
  have hnum_deriv :
      HasDerivAt
        (fun u =>
          (1 + theorem8Erf u) +
            c * theorem8GaussianJ theorem8Erf delta u)
        (c * p * B) t := by
    have hraw := hA_deriv.add (hJ_deriv.const_mul c)
    convert hraw using 1
    dsimp [B]
    ring
  have hden_deriv :
      HasDerivAt
        (fun u => (1 + theorem8Erf u) * (1 + theorem8Erf (u + delta)))
        (c * p * B + A * (c * q)) t := by
    have hraw := hA_deriv.mul hB_deriv
    simpa [A, B] using hraw
  have hratio :
      HasDerivAt
        (fun u =>
          theorem8GaussianConditionalIntegralRatio theorem8Erf
            (theorem8GaussianJ theorem8Erf delta) delta u)
        (((c * p * B) * (A * B) -
            (A + c * J) * (c * p * B + A * (c * q))) /
          (A * B) ^ 2) t := by
    have hdiv := hnum_deriv.div hden_deriv hden_prod_ne
    simpa [theorem8GaussianConditionalIntegralRatio, A, B, J] using hdiv
  have hlinear : HasDerivAt (fun u : ℝ => u - xi) 1 a := by
    simpa using (hasDerivAt_id a).sub_const xi
  have hratioAt :
      HasDerivAt (fun u => theorem8GaussianConditionalIntegralRatioAt xi xj u)
        (((c * p * B) * (A * B) -
            (A + c * J) * (c * p * B + A * (c * q))) /
          (A * B) ^ 2) a := by
    simpa [theorem8GaussianConditionalIntegralRatioAt, delta] using
      hratio.comp a hlinear
  have hstrict :
      HasDerivAt
        (fun u => theorem8GaussianProductStrictConditionalRatioAt xi xj u)
        (((c * p * B) * (A * B) -
            (A + c * J) * (c * p * B + A * (c * q))) /
          (A * B) ^ 2) a :=
    hratioAt.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => by
      exact (theorem8GaussianProductStrictConditionalRatioAt_eq_pdf_cdf xi xj u).trans
        ((theorem8GaussianPDFCDFRatioAt_eq_densityCDF xi xj u).trans
          (theorem8GaussianDensityCDFIntegralRatioAt_eq_conditional xi xj u)))
  have hI : I = Real.sqrt Real.pi / 2 * A + J := by
    dsimp [I, A, J, t, delta]
    simpa using theorem8Gaussian_integral_shift_split xi xj a
  have hIc : I * c = A + c * J := by
    rw [hI]
    dsimp [c]
    have hsqrt : Real.sqrt Real.pi ≠ 0 :=
      Real.sqrt_ne_zero'.mpr Real.pi_pos
    field_simp [hsqrt]
  have hderiv_eq :
      (((c * p * B) * (A * B) -
          (A + c * J) * (c * p * B + A * (c * q))) /
        (A * B) ^ 2) =
        c / (A * B) ^ 2 *
          (A * B ^ 2 * p - I * c * (A * q + B * p)) := by
    rw [hIc]
    ring
  have hshift_arg : a - xi + (xi - xj) = a - xj := by ring
  convert hstrict.congr_deriv hderiv_eq using 1
  dsimp [c, A, B, p, q, I, t, delta, J]
  rw [hshift_arg]
  ring

/--
Appendix C (C.5), the derivative sign of the actual strict-event conditional
ratio is equivalent to the literal displayed inequality.  The equivalence is
obtained from the preceding positive-factor formula.
-/
theorem equationC5_gaussian_strict_conditional_ratio_derivative_pos_iff
    (xi xj a : ℝ) :
    ∃ d,
      HasDerivAt
        (fun u => theorem8GaussianProductStrictConditionalRatioAt xi xj u) d a ∧
      (0 < d ↔
        0 <
          (1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj)) *
              Real.exp (-((a - xi) ^ 2)) * (1 + theorem8Erf (a - xj)) -
            (∫ x : ℝ in Set.Iic a,
              Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) *
              (2 / Real.sqrt Real.pi) *
              ((1 + theorem8Erf (a - xi)) * Real.exp (-((a - xj) ^ 2)) +
                (1 + theorem8Erf (a - xj)) *
                  Real.exp (-((a - xi) ^ 2)))) := by
  let K : ℝ :=
    (2 / Real.sqrt Real.pi) /
      ((1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj))) ^ 2
  let S : ℝ :=
    (1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj)) *
        Real.exp (-((a - xi) ^ 2)) * (1 + theorem8Erf (a - xj)) -
      (∫ x : ℝ in Set.Iic a,
        Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) *
        (2 / Real.sqrt Real.pi) *
        ((1 + theorem8Erf (a - xi)) * Real.exp (-((a - xj) ^ 2)) +
          (1 + theorem8Erf (a - xj)) * Real.exp (-((a - xi) ^ 2)))
  have hA : 0 < 1 + theorem8Erf (a - xi) :=
    theorem8Erf_one_add_pos (a - xi)
  have hB : 0 < 1 + theorem8Erf (a - xj) :=
    theorem8Erf_one_add_pos (a - xj)
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (by positivity)
      (sq_pos_of_pos (mul_pos hA hB))
  refine ⟨K * S, ?_, ?_⟩
  · simpa [K, S] using
      equationC5_gaussian_strict_conditional_ratio_hasDerivAt_factorization xi xj a
  · constructor
    · intro h
      rcases (mul_pos_iff.mp h) with hpos | hneg
      · exact hpos.2
      · linarith [hK, hneg.1]
    · intro h
      exact mul_pos hK h

/--
Appendix C (C.5), the same derivative-sign equivalence written directly for
the displayed Gaussian `erf` integral ratio.  This removes the named
conditional-ratio wrapper from the source-facing formula surface.
-/
theorem equationC5_gaussian_erf_ratio_derivative_pos_iff
    (xi xj a : ℝ) :
    ∃ d,
      HasDerivAt
        (fun u =>
          (2 / Real.sqrt Real.pi) *
            (∫ x : ℝ in Set.Iic u,
              Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) /
            ((1 + theorem8Erf (u - xi)) * (1 + theorem8Erf (u - xj)))) d a ∧
      (0 < d ↔
        0 <
          (1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj)) *
              Real.exp (-((a - xi) ^ 2)) * (1 + theorem8Erf (a - xj)) -
            (∫ x : ℝ in Set.Iic a,
              Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) *
              (2 / Real.sqrt Real.pi) *
              ((1 + theorem8Erf (a - xi)) * Real.exp (-((a - xj) ^ 2)) +
                (1 + theorem8Erf (a - xj)) *
                  Real.exp (-((a - xi) ^ 2)))) := by
  obtain ⟨d, hd, hsign⟩ :=
    equationC5_gaussian_strict_conditional_ratio_derivative_pos_iff xi xj a
  refine ⟨d, ?_, hsign⟩
  have hfun :
      (fun u => theorem8GaussianProductStrictConditionalRatioAt xi xj u) =
        (fun u =>
          (2 / Real.sqrt Real.pi) *
            (∫ x : ℝ in Set.Iic u,
              Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) /
            ((1 + theorem8Erf (u - xi)) * (1 + theorem8Erf (u - xj)))) := by
    funext u
    calc
      theorem8GaussianProductStrictConditionalRatioAt xi xj u =
          theorem8GaussianPDFCDFRatioAt xi xj u :=
        theorem8GaussianProductStrictConditionalRatioAt_eq_pdf_cdf xi xj u
      _ = _ := equationC5_gaussian_density_cdf_ratio_eq_erf_integral xi xj u
  rw [← hfun]
  exact hd

/--
Appendix C (C.5), literal derivative-sign inequality after the substitution to
the normalized Gaussian density.  This is stated in the source coordinates,
including its original one-dimensional integral.
-/
theorem equationC5_gaussian_derivative_sign_inequality
    {xi xj a : ℝ} (hx : xj < xi) :
    0 <
      (1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj)) *
          Real.exp (-((a - xi) ^ 2)) * (1 + theorem8Erf (a - xj)) -
        (∫ x : ℝ in Set.Iic a,
          Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) *
          (2 / Real.sqrt Real.pi) *
          ((1 + theorem8Erf (a - xi)) * Real.exp (-((a - xj) ^ 2)) +
            (1 + theorem8Erf (a - xj)) * Real.exp (-((a - xi) ^ 2))) := by
  let t : ℝ := a - xi
  let delta : ℝ := xi - xj
  let A : ℝ := 1 + theorem8Erf t
  let B : ℝ := 1 + theorem8Erf (t + delta)
  let p : ℝ := Real.exp (-(t ^ 2))
  let q : ℝ := Real.exp (-((t + delta) ^ 2))
  let J : ℝ := theorem8GaussianJ theorem8Erf delta t
  let I : ℝ := ∫ x : ℝ in Set.Iic a,
    Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))
  let c : ℝ := 2 / Real.sqrt Real.pi
  let N : ℝ := A * B ^ 2 * p
  let D : ℝ := A * q + B * p
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hc6 :=
    paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J_unconditional
      (δ := delta) hdelta t
  have hA : 0 < A := by
    dsimp [A]
    exact theorem8Erf_one_add_pos t
  have hB : 0 < B := by
    dsimp [B]
    exact theorem8Erf_one_add_pos (t + delta)
  have hp : 0 < p := by
    dsimp [p]
    exact Real.exp_pos _
  have hq : 0 < q := by
    dsimp [q]
    exact Real.exp_pos _
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos (mul_pos hA hq) (mul_pos hB hp)
  have hc6' : 0 < N / D - A - c * J := by
    simpa [N, D, A, B, p, q, c, J, theorem8GaussianC6LHS,
      theorem8GaussianC6RationalTerm, theorem8GaussianJ] using hc6
  have hmain : 0 < N - (A + c * J) * D := by
    calc
      0 < (N / D - A - c * J) * D := mul_pos hc6' hD
      _ = N - (A + c * J) * D := by
        field_simp [hD.ne']
        ring
  have hI : I = Real.sqrt Real.pi / 2 * A + J := by
    dsimp [I, A, J, t, delta]
    simpa using theorem8Gaussian_integral_shift_split xi xj a
  have hIc : I * c = A + c * J := by
    rw [hI]
    dsimp [c]
    have hsqrt : Real.sqrt Real.pi ≠ 0 :=
      Real.sqrt_ne_zero'.mpr Real.pi_pos
    field_simp [hsqrt]
  rw [← hIc] at hmain
  have hshift : a - xi + (xi - xj) = a - xj := by ring
  convert hmain using 1
  dsimp [N, I, c, D, A, B, p, q, t, delta, J]
  rw [hshift]
  ring

/--
Appendix C (C.6), the literal reduced Gaussian expression is positive for a
strictly positive source score gap.
-/
theorem equationC6_gaussian_reduced_expression_pos
    {delta t : ℝ} (hdelta : 0 < delta) :
    0 <
      ((1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
          Real.exp (-(t ^ 2))) /
        ((1 + theorem8Erf t) * Real.exp (-((t + delta) ^ 2)) +
          (1 + theorem8Erf (t + delta)) * Real.exp (-(t ^ 2))) -
        (1 + theorem8Erf t) -
        (2 / Real.sqrt Real.pi) *
          (∫ x : ℝ in Set.Iic t,
            Real.exp (-(x ^ 2)) * theorem8Erf (x + delta)) := by
  simpa [theorem8GaussianC6LHS, theorem8GaussianC6RationalTerm,
    theorem8GaussianJ] using
    (paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J_unconditional
      (δ := delta) hdelta t)

/--
Appendix C (C.7), the C.6 rational term tends to zero at the left tail.
-/
theorem equationC7_gaussian_rational_term_tendsto_atBot_zero
    (delta : ℝ) :
    Filter.Tendsto
      (fun t =>
        ((1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
            Real.exp (-(t ^ 2))) /
          ((1 + theorem8Erf t) * Real.exp (-((t + delta) ^ 2)) +
            (1 + theorem8Erf (t + delta)) * Real.exp (-(t ^ 2))))
      Filter.atBot (nhds 0) := by
  simpa [theorem8GaussianC6RationalTerm] using
    theorem8GaussianC6RationalTerm_tendsto_atBot_zero_concrete delta

/--
Appendix C (C.7), after the remaining two terms are transported to their
left-tail limits, the full C.6 expression tends to zero.
-/
theorem equationC7_gaussian_reduced_expression_tendsto_atBot_zero
    (delta : ℝ) :
    Filter.Tendsto
      (fun t =>
        ((1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
            Real.exp (-(t ^ 2))) /
          ((1 + theorem8Erf t) * Real.exp (-((t + delta) ^ 2)) +
            (1 + theorem8Erf (t + delta)) * Real.exp (-(t ^ 2))) -
          (1 + theorem8Erf t) -
          (2 / Real.sqrt Real.pi) *
            (∫ x : ℝ in Set.Iic t,
              Real.exp (-(x ^ 2)) * theorem8Erf (x + delta)))
      Filter.atBot (nhds 0) := by
  simpa [theorem8GaussianC6LHS, theorem8GaussianC6RationalTerm,
    theorem8GaussianJ] using
    (theorem8GaussianC6LHS_tendsto_atBot_zero
      (erf := theorem8Erf) (J := theorem8GaussianJ theorem8Erf delta)
      (δ := delta)
      (theorem8GaussianC6RationalTerm_tendsto_atBot_zero_concrete delta)
      theorem8Erf_tendsto_one_add_atBot_zero
      (theorem8GaussianJ_tendsto_atBot_zero_of_integrableOn
        (theorem8GaussianJ_integrableOn_concrete delta)))

/--
Appendix C (C.8), the literal derivative of the C.6 expression before the
factorization step.
-/
theorem equationC8_gaussian_reduced_expression_hasDerivAt
    (delta t : ℝ) :
    HasDerivAt
      (fun u =>
        ((1 + theorem8Erf u) * (1 + theorem8Erf (u + delta)) ^ 2 *
            Real.exp (-(u ^ 2))) /
          ((1 + theorem8Erf u) * Real.exp (-((u + delta) ^ 2)) +
            (1 + theorem8Erf (u + delta)) * Real.exp (-(u ^ 2))) -
          (1 + theorem8Erf u) -
          (2 / Real.sqrt Real.pi) *
            (∫ x : ℝ in Set.Iic u,
              Real.exp (-(x ^ 2)) * theorem8Erf (x + delta)))
      (deriv (fun u =>
          ((1 + theorem8Erf u) * (1 + theorem8Erf (u + delta)) ^ 2 *
              Real.exp (-(u ^ 2))) /
            ((1 + theorem8Erf u) * Real.exp (-((u + delta) ^ 2)) +
              (1 + theorem8Erf (u + delta)) * Real.exp (-(u ^ 2)))) t -
        (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) -
        (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) * theorem8Erf (t + delta)) t := by
  simpa [theorem8GaussianC6LHS, theorem8GaussianC6RationalTerm,
    theorem8GaussianJ, theorem8GaussianC8Derivative] using
    theorem8GaussianC6LHS_hasDerivAt_concrete_C8 delta t

/--
Corrected Appendix-C C.8 factorization.  The source's displayed prefactor is
not used here; this explicit factor is the one that actually multiplies the
C.9 bracket to give the C.8 derivative.
-/
theorem equationC8_corrected_factorization
    (delta t : ℝ) :
    deriv (fun u =>
        ((1 + theorem8Erf u) * (1 + theorem8Erf (u + delta)) ^ 2 *
            Real.exp (-(u ^ 2))) /
          ((1 + theorem8Erf u) * Real.exp (-((u + delta) ^ 2)) +
            (1 + theorem8Erf (u + delta)) * Real.exp (-(u ^ 2)))) t -
      (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) -
      (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) * theorem8Erf (t + delta) =
      ((2 * (1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
          Real.exp ((t + delta) ^ 2)) /
        (Real.sqrt Real.pi *
          (((theorem8Erf t + 1) * Real.exp (t ^ 2) +
            (theorem8Erf (t + delta) + 1) *
              Real.exp ((t + delta) ^ 2)) ^ 2))) *
        (((1 + theorem8Erf t) / Real.exp (-(t ^ 2))) *
          (delta * Real.sqrt Real.pi +
            (((1 + theorem8Erf (t + delta)) /
              Real.exp (-((t + delta) ^ 2)))⁻¹)) - 1) := by
  simpa [theorem8GaussianC8Derivative, theorem8GaussianC8PositiveFactor,
    theorem8GaussianC9Bracket, theorem8GaussianG] using
    theorem8GaussianC8Derivative_factorization delta t

/-- The checked C.8 prefactor is strictly positive at every real gap and cutoff. -/
theorem equationC8_corrected_prefactor_pos
    (delta t : ℝ) :
    0 <
      (2 * (1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
          Real.exp ((t + delta) ^ 2)) /
        (Real.sqrt Real.pi *
          (((theorem8Erf t + 1) * Real.exp (t ^ 2) +
            (theorem8Erf (t + delta) + 1) *
              Real.exp ((t + delta) ^ 2)) ^ 2)) := by
  have hA : 0 < 1 + theorem8Erf t := theorem8Erf_one_add_pos t
  have hB : 0 < 1 + theorem8Erf (t + delta) :=
    theorem8Erf_one_add_pos (t + delta)
  have hnum :
      0 < 2 * (1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
          Real.exp ((t + delta) ^ 2) := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) hA) (sq_pos_of_pos hB))
      (Real.exp_pos _)
  have hsum :
      0 <
        (theorem8Erf t + 1) * Real.exp (t ^ 2) +
          (theorem8Erf (t + delta) + 1) * Real.exp ((t + delta) ^ 2) := by
    exact add_pos
      (mul_pos (by simpa [add_comm] using hA) (Real.exp_pos _))
      (mul_pos (by simpa [add_comm] using hB) (Real.exp_pos _))
  exact div_pos hnum
    (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (sq_pos_of_pos hsum))

/--
The prefactor printed immediately after C.8 in the source.  It is retained
only for the checked mismatch witness below; it is not an accepted proof
endpoint.
-/
noncomputable def sourcePrintedC8Prefactor (delta t : ℝ) : ℝ :=
  (2 * (1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) *
      Real.exp (4 * t ^ 2)) /
    (Real.sqrt Real.pi *
      (((theorem8Erf t + 1) * Real.exp (t ^ 2) +
        (theorem8Erf (t + delta) + 1) *
          Real.exp ((t + delta) ^ 2)) ^ 2))

/--
The source's displayed C.8 prefactor is not the corrected factor even at the
concrete point `(delta,t)=(1,0)`.  This witnesses the source-proof formula
defect without treating the malformed display as a theorem.
-/
theorem sourcePrintedC8Prefactor_ne_corrected_at_one_zero :
    sourcePrintedC8Prefactor 1 0 ≠
      theorem8GaussianC8PositiveFactor theorem8Erf 1 0 := by
  have herf0 : theorem8Erf 0 = 0 := by
    simp [theorem8Erf]
  have herf1_pos : 0 < theorem8Erf 1 := by
    have hlt := theorem8Erf_strictMono (show (0 : ℝ) < 1 by norm_num)
    rw [herf0] at hlt
    linarith
  let B : ℝ := 1 + theorem8Erf 1
  let E : ℝ := Real.exp (1 : ℝ)
  have hB : 1 < B := by
    dsimp [B]
    linarith
  have hE : 1 < E := by
    dsimp [E]
    exact Real.one_lt_exp_iff.mpr (by norm_num)
  have hBpos : 0 < B := by linarith
  have hEpos : 0 < E := by linarith
  have hden_pos :
      0 < Real.sqrt Real.pi * (1 + B * E) ^ 2 := by
    exact mul_pos (Real.sqrt_pos.mpr Real.pi_pos)
      (sq_pos_of_pos (by positivity))
  intro heq
  have heq' := congrArg (fun x : ℝ => x *
      (Real.sqrt Real.pi * (1 + B * E) ^ 2)) heq
  dsimp [sourcePrintedC8Prefactor, theorem8GaussianC8PositiveFactor] at heq'
  rw [herf0] at heq'
  have hshift : (0 : ℝ) + 1 = 1 := by norm_num
  rw [hshift] at heq'
  have hEsource : Real.exp ((1 : ℝ) ^ 2) = E := by
    dsimp [E]
    norm_num
  have hden_raw :
      Real.sqrt Real.pi *
          (1 * Real.exp ((0 : ℝ) ^ 2) +
            (theorem8Erf 1 + 1) * Real.exp ((1 : ℝ) ^ 2)) ^ 2 =
        Real.sqrt Real.pi * (1 + B * E) ^ 2 := by
    rw [show (0 : ℝ) ^ 2 = 0 by ring, Real.exp_zero, hEsource]
    dsimp [B]
    ring
  have hBsource : 1 + theorem8Erf 1 = B := rfl
  rw [hden_raw, hEsource, hBsource] at heq'
  norm_num at heq'
  field_simp [hden_pos.ne'] at heq'
  have hBE : 1 < B * E := by nlinarith
  rcases heq' with h | h | h
  · nlinarith
  · rw [h] at hden_pos
    norm_num at hden_pos
  · nlinarith

private theorem concrete_mills_to_gaussian_g :
    theorem8MillsToGRelation theorem8MillsRatio (theorem8GaussianG theorem8Erf)
      (Real.sqrt (Real.pi / 2)) (Real.sqrt 2) := by
  exact theorem8MillsToGRelation_of_value_relation
    (by positivity : Real.sqrt (Real.pi / 2) ≠ 0)
    theorem8MillsRatio_value_relation

/--
Corrected Appendix-C C.9 bracket.  The first factor multiplies the entire
parenthesized expression; this is the bracket that the checked C.8 derivative
factorization actually yields.
-/
theorem equationC9_corrected_gaussian_bracket_pos
    {delta t : ℝ} (hdelta : 0 < delta) :
    0 <
      ((1 + theorem8Erf t) / Real.exp (-(t ^ 2))) *
        (delta * Real.sqrt Real.pi +
          (((1 + theorem8Erf (t + delta)) /
            Real.exp (-((t + delta) ^ 2)))⁻¹)) - 1 := by
  have hcont :
      ContinuousOn
        (fun u => (theorem8GaussianG theorem8Erf u)⁻¹)
        (Set.Icc t (t + delta)) :=
    theorem8GaussianG_inv_continuousOn theorem8Erf_continuous
      (fun u => theorem8Erf_one_add_pos u) _
  simpa [theorem8GaussianC9Bracket, theorem8GaussianG] using
    (paper_theorem8_c9_positive_of_sampford_mills
      (R := theorem8MillsRatio) (g := theorem8GaussianG theorem8Erf)
      (c := Real.sqrt (Real.pi / 2)) (q := Real.sqrt 2)
      (t := t) (δ := delta) hdelta
      (theorem8GaussianG_pos (theorem8Erf_one_add_pos t))
      (by positivity : 0 < Real.sqrt (Real.pi / 2))
      (by positivity : 0 < Real.sqrt 2)
      paper_theorem8_mills_constants_mul
      concrete_mills_to_gaussian_g theorem8SampfordMillsBound_concrete hcont)

/--
Appendix C (C.10), stated at the paper's concrete function
`g(t)=(1+erf(t))/exp(-t^2)`: every derivative of `1/g` is strictly larger
than `-sqrt(pi)`.  The proof includes the concrete Mills-ratio bound rather
than leaving Sampford as an unrecorded assumption.
-/
theorem equationC10_gaussian_g_inv_derivative_lower_bound
    (t : ℝ) :
    ∃ d,
      HasDerivAt
        (fun u =>
          (((1 + theorem8Erf u) / Real.exp (-(u ^ 2)))⁻¹)) d t ∧
        -Real.sqrt Real.pi < d := by
  simpa [theorem8GaussianG] using
    (paper_theorem8_c10_of_sampford_mills
      (R := theorem8MillsRatio) (g := theorem8GaussianG theorem8Erf)
      (c := Real.sqrt (Real.pi / 2)) (q := Real.sqrt 2)
      (by positivity : 0 < Real.sqrt (Real.pi / 2))
      (by positivity : 0 < Real.sqrt 2)
      paper_theorem8_mills_constants_mul
      concrete_mills_to_gaussian_g theorem8SampfordMillsBound_concrete t)

end KR21Monoculture
