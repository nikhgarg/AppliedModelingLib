import AppliedModelingLib.Foundations.Probability.PoissonParameterKernel
import AppliedModelingLib.Foundations.Probability.PoissonProcess
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Elementary Poisson moments

Low-level moment identities for Mathlib's `poissonMeasure`.  These belong
below any particular Poisson-process construction so forward, Palm, and
equilibrium models can all use the same integrability and expectation facts.
-/

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open MeasureTheory
open scoped ProbabilityTheory ENNReal NNReal

noncomputable section

/-- The first moment of the real Poisson mass series. -/
theorem hasSum_poisson_firstMoment (x : ℝ) :
    HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ) * n) x := by
  have hbase : HasSum (fun n : ℕ => Real.exp (-x) * x ^ n / (n.factorial : ℝ)) 1 := by
    convert (NormedSpace.expSeries_div_hasSum_exp x).mul_left (Real.exp (-x)) using 1
    · simp_rw [mul_div_assoc]
    · rw [← Real.exp_eq_exp_ℝ]
      rw [← Real.exp_add]
      ring_nf
      norm_num
  have hshift : HasSum (fun n : ℕ =>
      x * (Real.exp (-x) * x ^ n / (n.factorial : ℝ))) x := by
    simpa using hbase.mul_left x
  refine (hasSum_nat_add_iff' 1).mp ?_
  convert hshift.congr_fun (fun n => ?_) using 1 <;> simp
  field_simp
  simp only [Nat.factorial_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

/-- The second factorial moment of the real Poisson mass series. -/
theorem hasSum_poisson_secondFactorialMoment (x : ℝ) :
    HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ) *
        (n : ℝ) * ((n : ℝ) - 1)) (x ^ 2) := by
  have hbase : HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ)) 1 := by
    convert (NormedSpace.expSeries_div_hasSum_exp x).mul_left (Real.exp (-x)) using 1
    · simp_rw [mul_div_assoc]
    · rw [← Real.exp_eq_exp_ℝ]
      rw [← Real.exp_add]
      ring_nf
      norm_num
  have hshift : HasSum (fun n : ℕ =>
      x ^ 2 * (Real.exp (-x) * x ^ n / (n.factorial : ℝ))) (x ^ 2) := by
    simpa using hbase.mul_left (x ^ 2)
  refine (hasSum_nat_add_iff' 2).mp ?_
  convert hshift.congr_fun (fun n => ?_) using 1
  · norm_num [Finset.sum_range_succ]
  · have hfactorial : (n + 2).factorial =
        (n + 2) * (n + 1) * n.factorial := by
      calc
        (n + 2).factorial = (n + 2) * (n + 1).factorial := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using Nat.factorial_succ (n + 1)
        _ = (n + 2) * (n + 1) * n.factorial := by
          rw [show n + 1 = Nat.succ n by omega, Nat.factorial_succ]
          simp only [Nat.succ_eq_add_one]
          ring
    rw [hfactorial, pow_add]
    norm_num [Nat.cast_mul, Nat.cast_add]
    field_simp
    ring

/-- The second moment of the real Poisson mass series. -/
theorem hasSum_poisson_secondMoment (x : ℝ) :
    HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 2)
      (x ^ 2 + x) := by
  have hfactorial := hasSum_poisson_secondFactorialMoment x
  have hfirst := hasSum_poisson_firstMoment x
  convert hfactorial.add hfirst using 1
  funext n
  ring

/-- The third factorial moment of the real Poisson mass series. -/
theorem hasSum_poisson_thirdFactorialMoment (x : ℝ) :
    HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ) *
        (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) (x ^ 3) := by
  have hbase : HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ)) 1 := by
    convert (NormedSpace.expSeries_div_hasSum_exp x).mul_left (Real.exp (-x)) using 1
    · simp_rw [mul_div_assoc]
    · rw [← Real.exp_eq_exp_ℝ]
      rw [← Real.exp_add]
      ring_nf
      norm_num
  have hshift : HasSum (fun n : ℕ =>
      x ^ 3 * (Real.exp (-x) * x ^ n / (n.factorial : ℝ))) (x ^ 3) := by
    simpa using hbase.mul_left (x ^ 3)
  refine (hasSum_nat_add_iff' 3).mp ?_
  convert hshift.congr_fun (fun n => ?_) using 1
  · norm_num [Finset.sum_range_succ]
  · have hfactorial : (n + 3).factorial =
        (n + 3) * (n + 2) * (n + 1) * n.factorial := by
      calc
        (n + 3).factorial = (n + 3) * (n + 2).factorial := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using Nat.factorial_succ (n + 2)
        _ = (n + 3) * (n + 2) * (n + 1) * n.factorial := by
          rw [show n + 2 = Nat.succ (n + 1) by omega, Nat.factorial_succ,
            show n + 1 = Nat.succ n by omega, Nat.factorial_succ]
          simp only [Nat.succ_eq_add_one]
          ring
    rw [hfactorial, pow_add]
    norm_num [Nat.cast_mul, Nat.cast_add]
    field_simp
    ring

/-- The fourth factorial moment of the real Poisson mass series. -/
theorem hasSum_poisson_fourthFactorialMoment (x : ℝ) :
    HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ) *
        (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3)) (x ^ 4) := by
  have hbase : HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ)) 1 := by
    convert (NormedSpace.expSeries_div_hasSum_exp x).mul_left (Real.exp (-x)) using 1
    · simp_rw [mul_div_assoc]
    · rw [← Real.exp_eq_exp_ℝ]
      rw [← Real.exp_add]
      ring_nf
      norm_num
  have hshift : HasSum (fun n : ℕ =>
      x ^ 4 * (Real.exp (-x) * x ^ n / (n.factorial : ℝ))) (x ^ 4) := by
    simpa using hbase.mul_left (x ^ 4)
  refine (hasSum_nat_add_iff' 4).mp ?_
  convert hshift.congr_fun (fun n => ?_) using 1
  · norm_num [Finset.sum_range_succ]
  · have hfactorial : (n + 4).factorial =
        (n + 4) * (n + 3) * (n + 2) * (n + 1) * n.factorial := by
      calc
        (n + 4).factorial = (n + 4) * (n + 3).factorial := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using Nat.factorial_succ (n + 3)
        _ = (n + 4) * (n + 3) * (n + 2) * (n + 1) * n.factorial := by
          rw [show n + 3 = Nat.succ (n + 2) by omega, Nat.factorial_succ,
            show n + 2 = Nat.succ (n + 1) by omega, Nat.factorial_succ,
            show n + 1 = Nat.succ n by omega, Nat.factorial_succ]
          simp only [Nat.succ_eq_add_one]
          ring
    rw [hfactorial, pow_add]
    norm_num [Nat.cast_mul, Nat.cast_add]
    field_simp
    ring

/-- The third moment of the real Poisson mass series. -/
theorem hasSum_poisson_thirdMoment (x : ℝ) :
    HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 3)
      (x ^ 3 + 3 * x ^ 2 + x) := by
  have hfactorial := hasSum_poisson_thirdFactorialMoment x
  have hsecond := hasSum_poisson_secondFactorialMoment x
  have hfirst := hasSum_poisson_firstMoment x
  have hsum := hfactorial.add ((hsecond.mul_left 3).add hfirst)
  convert hsum using 1
  · funext n
    ring
  · ring

/-- The fourth moment of the real Poisson mass series. -/
theorem hasSum_poisson_fourthMoment (x : ℝ) :
    HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 4)
      (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x) := by
  have hfactorial := hasSum_poisson_fourthFactorialMoment x
  have hthird := hasSum_poisson_thirdFactorialMoment x
  have hsecond := hasSum_poisson_secondFactorialMoment x
  have hfirst := hasSum_poisson_firstMoment x
  have hsum := hfactorial.add ((hthird.mul_left 6).add
    ((hsecond.mul_left 7).add hfirst))
  convert hsum using 1
  · funext n
    ring
  · ring

/-- The fourth centered moment of the real Poisson mass series. -/
theorem hasSum_poisson_centeredFourthMoment (x : ℝ) :
    HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ) * ((n : ℝ) - x) ^ 4)
      (x + 3 * x ^ 2) := by
  have hbase : HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ)) 1 := by
    convert (NormedSpace.expSeries_div_hasSum_exp x).mul_left (Real.exp (-x)) using 1
    · simp_rw [mul_div_assoc]
    · rw [← Real.exp_eq_exp_ℝ]
      rw [← Real.exp_add]
      ring_nf
      norm_num
  have hfourth := hasSum_poisson_fourthMoment x
  have hthird := hasSum_poisson_thirdMoment x
  have hsecond := hasSum_poisson_secondMoment x
  have hfirst := hasSum_poisson_firstMoment x
  let mass : ℕ → ℝ := fun n => Real.exp (-x) * x ^ n / (n.factorial : ℝ)
  have hsum : HasSum (fun n : ℕ =>
      ((mass n * (n : ℝ) ^ 4 - (4 * x) * (mass n * (n : ℝ) ^ 3)) +
          (6 * x ^ 2) * (mass n * (n : ℝ) ^ 2) -
            (4 * x ^ 3) * (mass n * (n : ℝ))) + (x ^ 4) * mass n)
      ((((x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x) -
          (4 * x) * (x ^ 3 + 3 * x ^ 2 + x)) +
            (6 * x ^ 2) * (x ^ 2 + x) - (4 * x ^ 3) * x) + x ^ 4 * 1) := by
    dsimp [mass]
    exact (((hfourth.sub (hthird.mul_left (4 * x))).add
      (hsecond.mul_left (6 * x ^ 2))).sub (hfirst.mul_left (4 * x ^ 3))).add
        (hbase.mul_left (x ^ 4))
  have hpoint : (fun n : ℕ =>
      ((mass n * (n : ℝ) ^ 4 - (4 * x) * (mass n * (n : ℝ) ^ 3)) +
          (6 * x ^ 2) * (mass n * (n : ℝ) ^ 2) -
            (4 * x ^ 3) * (mass n * (n : ℝ))) + (x ^ 4) * mass n) =
      (fun n : ℕ => Real.exp (-x) * x ^ n / (n.factorial : ℝ) *
        ((n : ℝ) - x) ^ 4) := by
    funext n
    dsimp [mass]
    ring
  have hlimit :
      (((x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x) -
          (4 * x) * (x ^ 3 + 3 * x ^ 2 + x)) +
            (6 * x ^ 2) * (x ^ 2 + x) - (4 * x ^ 3) * x) + x ^ 4 * 1 =
        x + 3 * x ^ 2 := by
    ring
  rw [hpoint, hlimit] at hsum
  exact hsum

/-- A Poisson count has an integrable real-valued first moment. -/
theorem integrable_natCast_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  simpa [Real.norm_eq_abs, abs_of_nonneg] using
    (hasSum_poisson_firstMoment (r : ℝ)).summable

/-- A Poisson count has an integrable squared real value. -/
theorem integrable_natCast_sq_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) ^ 2) (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  simpa [Real.norm_eq_abs, sq_nonneg] using
    (hasSum_poisson_secondMoment (r : ℝ)).summable

/-- A Poisson count has an integrable cubed real value. -/
theorem integrable_natCast_cube_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) ^ 3) (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity) _)] using
    (hasSum_poisson_thirdMoment (r : ℝ)).summable

/-- The real expectation of a Poisson random variable is its parameter. -/
theorem integral_id_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ∂ProbabilityTheory.poissonMeasure r = r := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  simpa [smul_eq_mul] using (hasSum_poisson_firstMoment (r : ℝ)).tsum_eq

/-- The real second moment of a Poisson random variable is `r² + r`. -/
theorem integral_natCast_sq_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ^ 2 ∂ProbabilityTheory.poissonMeasure r =
      (r : ℝ) ^ 2 + r := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  simpa [smul_eq_mul] using (hasSum_poisson_secondMoment (r : ℝ)).tsum_eq

/-- The real third moment of a Poisson random variable is `r³ + 3r² + r`. -/
theorem integral_natCast_cube_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ^ 3 ∂ProbabilityTheory.poissonMeasure r =
      (r : ℝ) ^ 3 + 3 * (r : ℝ) ^ 2 + r := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  simpa [smul_eq_mul] using (hasSum_poisson_thirdMoment (r : ℝ)).tsum_eq

/-- Mixing a Poisson count over a finite law of parameters preserves the
conditional third-moment formula. -/
theorem integral_natCast_cube_poissonParameterKernel_comp (μ : Measure ℝ≥0)
    [IsFiniteMeasure μ]
    (hcount : Integrable (fun count : ℕ => (count : ℝ) ^ 3)
      (poissonParameterKernel ∘ₘ μ)) :
    ∫ count : ℕ, (count : ℝ) ^ 3 ∂poissonParameterKernel ∘ₘ μ =
      ∫ parameter : ℝ≥0, (parameter : ℝ) ^ 3 +
        3 * (parameter : ℝ) ^ 2 + parameter ∂μ := by
  have hmeas : AEStronglyMeasurable (fun count : ℕ => (count : ℝ) ^ 3)
      (poissonParameterKernel ∘ₘ μ) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hpairs : Integrable (fun pair : ℝ≥0 × ℕ => (pair.2 : ℝ) ^ 3)
      (μ ⊗ₘ poissonParameterKernel) := by
    apply (Measure.integrable_compProd_snd_iff hmeas).mpr
    simpa using hcount
  calc
    ∫ count : ℕ, (count : ℝ) ^ 3 ∂poissonParameterKernel ∘ₘ μ =
        ∫ pair : ℝ≥0 × ℕ, (pair.2 : ℝ) ^ 3 ∂(μ ⊗ₘ poissonParameterKernel) := by
      calc
        ∫ count : ℕ, (count : ℝ) ^ 3 ∂poissonParameterKernel ∘ₘ μ =
            ∫ count : ℕ, (count : ℝ) ^ 3 ∂(μ ⊗ₘ poissonParameterKernel).snd := by
              rw [Measure.snd_compProd]
        _ = ∫ pair : ℝ≥0 × ℕ, (pair.2 : ℝ) ^ 3
            ∂(μ ⊗ₘ poissonParameterKernel) := by
              change ∫ count : ℕ, (count : ℝ) ^ 3 ∂Measure.map Prod.snd
                (μ ⊗ₘ poissonParameterKernel) = _
              simpa [Function.comp_def] using
                (integral_map measurable_snd.aemeasurable
                  (by fun_prop : AEStronglyMeasurable
                    (fun count : ℕ => (count : ℝ) ^ 3)
                    ((μ ⊗ₘ poissonParameterKernel).snd)))
    _ = ∫ parameter : ℝ≥0, ∫ count : ℕ, (count : ℝ) ^ 3
        ∂poissonParameterKernel parameter ∂μ := by
      exact Measure.integral_compProd hpairs
    _ = ∫ parameter : ℝ≥0, (parameter : ℝ) ^ 3 +
        3 * (parameter : ℝ) ^ 2 + parameter ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with parameter
      exact integral_natCast_cube_poissonMeasure parameter

/-- A Poisson count centered at its parameter is integrable. -/
theorem integrable_natCast_sub_parameter_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) - r)
      (ProbabilityTheory.poissonMeasure r) := by
  exact (integrable_natCast_poissonMeasure r).sub (integrable_const _)

/-- A Poisson count centered at its parameter has mean zero. -/
theorem integral_natCast_sub_parameter_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) - r) ∂ProbabilityTheory.poissonMeasure r = 0 := by
  rw [integral_sub (integrable_natCast_poissonMeasure r) (integrable_const _),
    integral_id_poissonMeasure, integral_const]
  simp

/-- A Poisson count centered at its parameter has integrable square. -/
theorem integrable_natCast_sub_parameter_sq_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => ((n : ℝ) - r) ^ 2)
      (ProbabilityTheory.poissonMeasure r) := by
  have hsq := integrable_natCast_sq_poissonMeasure r
  have hlinear := (integrable_natCast_poissonMeasure r).const_mul (2 * (r : ℝ))
  have hpoly : (fun n : ℕ => ((n : ℝ) - r) ^ 2) =
      (fun n : ℕ => (n : ℝ) ^ 2 - (2 * (r : ℝ)) * n + (r : ℝ) ^ 2) := by
    funext n
    ring
  rw [hpoly]
  exact (hsq.sub hlinear).add (integrable_const _)

/-- A Poisson count centered at its parameter has integrable fourth power. -/
theorem integrable_natCast_sub_parameter_fourth_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => ((n : ℝ) - r) ^ 4)
      (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  refine (hasSum_poisson_centeredFourthMoment (r : ℝ)).summable.congr ?_
  intro n
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ((n : ℝ) - (r : ℝ)) ^ 4)]

/-- The centered real Poisson count has second moment equal to its parameter. -/
theorem integral_natCast_sub_parameter_sq_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) - r) ^ 2 ∂ProbabilityTheory.poissonMeasure r = r := by
  have hsq := integrable_natCast_sq_poissonMeasure r
  have hlinear := (integrable_natCast_poissonMeasure r).const_mul (2 * (r : ℝ))
  have hpoly : (fun n : ℕ => ((n : ℝ) - r) ^ 2) =
      (fun n : ℕ => (n : ℝ) ^ 2 - (2 * (r : ℝ)) * n + (r : ℝ) ^ 2) := by
    funext n
    ring
  rw [hpoly]
  change ∫ n : ℕ, ((fun n : ℕ => (n : ℝ) ^ 2) -
    (fun n : ℕ => (2 * (r : ℝ)) * n)) n + (r : ℝ) ^ 2
      ∂ProbabilityTheory.poissonMeasure r = r
  have hsub :
      ∫ n : ℕ, ((fun n : ℕ => (n : ℝ) ^ 2) -
          (fun n : ℕ => (2 * (r : ℝ)) * n)) n
        ∂ProbabilityTheory.poissonMeasure r =
        (∫ n : ℕ, (n : ℝ) ^ 2 ∂ProbabilityTheory.poissonMeasure r) -
          ∫ n : ℕ, (2 * (r : ℝ)) * n ∂ProbabilityTheory.poissonMeasure r := by
    simpa using integral_sub hsq hlinear
  rw [integral_add (hsq.sub hlinear) (integrable_const _),
    hsub, integral_natCast_sq_poissonMeasure,
    integral_const_mul, integral_id_poissonMeasure,
    integral_const]
  simp
  ring

/-- A Poisson count has an integrable square after centering at any fixed
real value. -/
theorem integrable_natCast_sub_constant_sq_poissonMeasure (r : ℝ≥0) (center : ℝ) :
    Integrable (fun n : ℕ => ((n : ℝ) - center) ^ 2)
      (ProbabilityTheory.poissonMeasure r) := by
  have hsq := integrable_natCast_sq_poissonMeasure r
  have hlinear := (integrable_natCast_poissonMeasure r).const_mul (2 * center)
  have hpoly : (fun n : ℕ => ((n : ℝ) - center) ^ 2) =
      (fun n : ℕ => (n : ℝ) ^ 2 - (2 * center) * n + center ^ 2) := by
    funext n
    ring
  rw [hpoly]
  exact (hsq.sub hlinear).add (integrable_const _)

/-- The square about an arbitrary fixed center is its Poisson variance plus
the squared displacement of the mean from that center. -/
theorem integral_natCast_sub_constant_sq_poissonMeasure (r : ℝ≥0) (center : ℝ) :
    ∫ n : ℕ, ((n : ℝ) - center) ^ 2 ∂ProbabilityTheory.poissonMeasure r =
      (r : ℝ) + ((r : ℝ) - center) ^ 2 := by
  have hsq := integrable_natCast_sq_poissonMeasure r
  have hlinear := (integrable_natCast_poissonMeasure r).const_mul (2 * center)
  have hpoly : (fun n : ℕ => ((n : ℝ) - center) ^ 2) =
      (fun n : ℕ => (n : ℝ) ^ 2 - (2 * center) * n + center ^ 2) := by
    funext n
    ring
  rw [hpoly]
  change ∫ n : ℕ, ((fun n : ℕ => (n : ℝ) ^ 2) -
    (fun n : ℕ => (2 * center) * n)) n + center ^ 2
      ∂ProbabilityTheory.poissonMeasure r = _
  have hsub :
      ∫ n : ℕ, ((fun n : ℕ => (n : ℝ) ^ 2) -
          (fun n : ℕ => (2 * center) * n)) n
        ∂ProbabilityTheory.poissonMeasure r =
        (∫ n : ℕ, (n : ℝ) ^ 2 ∂ProbabilityTheory.poissonMeasure r) -
          ∫ n : ℕ, (2 * center) * n ∂ProbabilityTheory.poissonMeasure r := by
    simpa using integral_sub hsq hlinear
  rw [integral_add (hsq.sub hlinear) (integrable_const _), hsub,
    integral_natCast_sq_poissonMeasure, integral_const_mul,
    integral_id_poissonMeasure, integral_const]
  simp
  ring

/-- The fourth centered moment of a Poisson count is its parameter plus
three times its squared parameter. -/
theorem integral_natCast_sub_parameter_fourth_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) - r) ^ 4 ∂ProbabilityTheory.poissonMeasure r =
      (r : ℝ) + 3 * (r : ℝ) ^ 2 := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  simpa [smul_eq_mul] using
    (hasSum_poisson_centeredFourthMoment (r : ℝ)).tsum_eq

end

end PoissonProcess
end Probability
end AppliedModelingLib
