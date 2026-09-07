import AppliedModelingLib.Foundations.Math.Asymptotics
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Beta

open Filter Topology MeasureTheory
open scoped BigOperators

namespace AppliedModelingLib
namespace Math

/--
Real beta closed form when the second argument is a positive integer.

This is the real-valued wrapper around mathlib's complex
`Complex.betaIntegral_eval_nat_add_one_right`, useful for order-statistic
integrals whose beta parameter is a natural shift.
-/
theorem beta_nat_add_one_right_real
    {u : ℝ} (hu : 0 < u) (n : ℕ) :
    ProbabilityTheory.beta u ((n : ℝ) + 1) =
      (Nat.factorial n : ℝ) / ∏ j ∈ Finset.range (n + 1), (u + j) := by
  rw [ProbabilityTheory.beta_eq_betaIntegralReal
    u ((n : ℝ) + 1) hu (by positivity)]
  have hcomplex :=
    Complex.betaIntegral_eval_nat_add_one_right
      (u := (u : ℂ)) (by simpa using hu) n
  have hcomplex' :
      Complex.betaIntegral (u : ℂ) (((n : ℝ) + 1 : ℝ) : ℂ) =
        (Nat.factorial n : ℂ) /
          ∏ j ∈ Finset.range (n + 1), ((u : ℂ) + j) := by
    simpa [Nat.cast_add, Nat.cast_one] using hcomplex
  rw [hcomplex']
  have hprod :
      (∏ j ∈ Finset.range (n + 1), ((u : ℂ) + j)) =
        ((∏ j ∈ Finset.range (n + 1), (u + j) : ℝ) : ℂ) := by
    simp [Complex.ofReal_prod, Complex.ofReal_add]
  have hnum : (Nat.factorial n : ℂ) = ((Nat.factorial n : ℝ) : ℂ) := by
    norm_num
  change
      ((Nat.factorial n : ℂ) /
          ∏ j ∈ Finset.range (n + 1), ((u : ℂ) + j)).re =
        (Nat.factorial n : ℝ) /
          ∏ j ∈ Finset.range (n + 1), (u + j)
  calc
    ((Nat.factorial n : ℂ) /
        ∏ j ∈ Finset.range (n + 1), ((u : ℂ) + j)).re
        = (((Nat.factorial n : ℝ) : ℂ) /
            ((∏ j ∈ Finset.range (n + 1), (u + j) : ℝ) : ℂ)).re := by
            rw [hprod, hnum]
    _ = (Nat.factorial n : ℝ) /
          ∏ j ∈ Finset.range (n + 1), (u + j) := by
            rw [Complex.div_ofReal_re]
            simp

/--
Real beta integral over `(0, 1)`.

Mathlib defines the beta integral complex-valued over `0..1`; this wrapper is
the real-valued interval form usually needed by order-statistic calculations.
-/
theorem integral_Ioo_zero_one_rpow_mul_one_sub_rpow_eq_beta
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Set.Ioo (0 : ℝ) 1, x ^ (a - 1) * (1 - x) ^ (b - 1) =
      ProbabilityTheory.beta a b := by
  have hInt :
      Integrable
        (fun x : ℝ =>
          (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1))
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    convert Complex.betaIntegral_convergent (u := a) (v := b)
      (by simpa) (by simpa)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]
  rw [ProbabilityTheory.beta_eq_betaIntegralReal a b ha hb,
    Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  calc
    ∫ x in Set.Ioc (0 : ℝ) 1, x ^ (a - 1) * (1 - x) ^ (b - 1)
        = ∫ x in Set.Ioc (0 : ℝ) 1,
            RCLike.re
              ((x : ℂ) ^ ((a : ℂ) - 1) *
                (1 - (x : ℂ)) ^ ((b : ℂ) - 1)) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
            norm_cast
            rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
              Complex.re_mul_ofReal, Complex.ofReal_re]
            all_goals linarith [hx.1, hx.2]
    _ = RCLike.re
          (∫ x in Set.Ioc (0 : ℝ) 1,
            (x : ℂ) ^ ((a : ℂ) - 1) *
              (1 - (x : ℂ)) ^ ((b : ℂ) - 1)) := by
            exact integral_re hInt

/--
Real beta kernel integrability on `(0, 1)`.

This is the integrability companion to
`integral_Ioo_zero_one_rpow_mul_one_sub_rpow_eq_beta`; finite order-statistic
tail sums need it before exchanging finite sums and integrals.
-/
theorem integrableOn_Ioo_zero_one_rpow_mul_one_sub_rpow
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn
      (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1))
      (Set.Ioo (0 : ℝ) 1) := by
  have hInt :
      Integrable
        (fun x : ℝ =>
          (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1))
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    convert Complex.betaIntegral_convergent (u := a) (v := b)
      (by simpa) (by simpa)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]
  have hRealIoc :
      Integrable
        (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1))
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [← integrable_congr ?_]
    · exact hInt.re
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc]
        with x hx
      norm_cast
      rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
        Complex.re_mul_ofReal, Complex.ofReal_re]
      all_goals linarith [hx.1, hx.2]
  exact (integrableOn_Ioc_iff_integrableOn_Ioo
    (μ := MeasureTheory.volume)
    (f := fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1))
    (a := 0) (b := 1)).1 hRealIoc

/--
Natural-power beta integral over `(0, 1)`.

This is the form used by continuous-uniform order-statistic tails.
-/
theorem integral_Ioo_zero_one_pow_mul_one_sub_pow_eq_beta_nat
    (m n : ℕ) :
    ∫ x in Set.Ioo (0 : ℝ) 1, x ^ m * (1 - x) ^ n =
      ProbabilityTheory.beta (((m : ℝ) + 1)) (((n : ℝ) + 1)) := by
  have h :=
    integral_Ioo_zero_one_rpow_mul_one_sub_rpow_eq_beta
      (a := ((m : ℝ) + 1)) (b := ((n : ℝ) + 1))
      (by positivity) (by positivity)
  simpa [Nat.cast_add, Nat.cast_one] using h

/--
Natural-power beta-kernel integrability over `(0, 1)`.
-/
theorem integrableOn_Ioo_zero_one_pow_mul_one_sub_pow
    (m n : ℕ) :
    IntegrableOn
      (fun x : ℝ => x ^ m * (1 - x) ^ n)
      (Set.Ioo (0 : ℝ) 1) := by
  simpa using
    integrableOn_Ioo_zero_one_rpow_mul_one_sub_rpow
      (a := ((m : ℝ) + 1)) (b := ((n : ℝ) + 1))
      (by positivity) (by positivity)

/--
Power-substituted beta kernel over `(0, 1)`.

For `s > 0`, substituting `u = x ^ s` in the right-hand integral gives the
left-hand gamma/beta kernel.  This is useful for bounded upper-tail laws with
mass `x ^ β`, where `s = 1 / β`.
-/
theorem integral_Ioo_zero_one_rpow_power_kernel_eq_s_mul_beta
    {s beta : ℝ} (hs_pos : 0 < s) (hbeta_pos : 0 < beta)
    (hsbeta : s * beta = 1) (j n : ℕ) :
    ∫ y in Set.Ioo (0 : ℝ) 1, (y ^ beta) ^ j * (1 - y ^ beta) ^ n =
      s * ProbabilityTheory.beta ((j : ℝ) + s) ((n : ℝ) + 1) := by
  let g : ℝ → ℝ := fun y =>
    (Set.Ioo (0 : ℝ) 1).indicator
      (fun z : ℝ => (z ^ beta) ^ j * (1 - z ^ beta) ^ n) y
  have hsubst :=
    integral_comp_rpow_Ioi_of_pos (g := g) (hp := hs_pos)
  have hright :
      (∫ y in Set.Ioi (0 : ℝ), g y) =
        ∫ y in Set.Ioo (0 : ℝ) 1,
          (y ^ beta) ^ j * (1 - y ^ beta) ^ n := by
    dsimp [g]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioo]
    exact MeasureTheory.setIntegral_congr_set
      (by
        filter_upwards with y
        apply propext
        constructor
        · intro hy
          exact ⟨hy.1, hy.2.2⟩
        · intro hy
          exact ⟨hy.1, hy⟩)
  have hleft :
      (∫ x in Set.Ioi (0 : ℝ), (s * x ^ (s - 1)) • g (x ^ s)) =
        s * ∫ x in Set.Ioo (0 : ℝ) 1,
          x ^ (((j : ℝ) + s) - 1) * (1 - x) ^ n := by
    let kernel : ℝ → ℝ := fun x =>
      s * (x ^ (((j : ℝ) + s) - 1) * (1 - x) ^ n)
    have hraw :
        (∫ x in Set.Ioi (0 : ℝ), (s * x ^ (s - 1)) • g (x ^ s)) =
          ∫ x in Set.Ioi (0 : ℝ),
            (Set.Ioo (0 : ℝ) 1).indicator kernel x := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx_pos_set
      have hx_pos : 0 < x := hx_pos_set
      have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
      by_cases hx_lt_one : x < 1
      · have hx_mem : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx_pos, hx_lt_one⟩
        have hxpow_mem : x ^ s ∈ Set.Ioo (0 : ℝ) 1 := by
          exact ⟨Real.rpow_pos_of_pos hx_pos s,
            Real.rpow_lt_one hx_nonneg hx_lt_one hs_pos⟩
        have hxpow_beta : (x ^ s) ^ beta = x := by
          rw [← Real.rpow_mul hx_nonneg]
          rw [hsbeta, Real.rpow_one]
        have hmul :
            x ^ (s - 1) * x ^ j =
              x ^ (((j : ℝ) + s) - 1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hx_pos]
          ring_nf
        have hprod :
            x ^ j * (x ^ (s - 1) * (1 - x) ^ n) =
              x ^ (((j : ℝ) + s) - 1) * (1 - x) ^ n := by
          calc
            x ^ j * (x ^ (s - 1) * (1 - x) ^ n)
                = (x ^ (s - 1) * x ^ j) * (1 - x) ^ n := by ring
            _ = x ^ (((j : ℝ) + s) - 1) * (1 - x) ^ n := by rw [hmul]
        simp [g, kernel, hx_mem, hxpow_mem, hxpow_beta, smul_eq_mul]
        calc
          s * x ^ (s - 1) * (x ^ j * (1 - x) ^ n)
              = s * (x ^ j * (x ^ (s - 1) * (1 - x) ^ n)) := by ring
          _ = s * (x ^ (((j : ℝ) + s) - 1) * (1 - x) ^ n) := by
            rw [hprod]
      · have hxpow_not_mem : x ^ s ∉ Set.Ioo (0 : ℝ) 1 := by
          intro hxmem
          have hxpow_lt_one : x ^ s < 1 := hxmem.2
          have hx_le_one : x ≤ 1 := by
            by_contra hx_not_le
            have hx_gt_one : 1 < x := lt_of_not_ge hx_not_le
            have hxpow_gt_one : 1 < x ^ s := by
              simpa using Real.one_lt_rpow hx_gt_one hs_pos
            exact not_lt_of_ge hxpow_gt_one.le hxpow_lt_one
          exact hx_lt_one (lt_of_le_of_ne hx_le_one (by
            intro hx_eq
            subst x
            simp at hxmem))
        have hx_not_mem : x ∉ Set.Ioo (0 : ℝ) 1 := fun hxmem => hx_lt_one hxmem.2
        simp [g, kernel, hxpow_not_mem, hx_not_mem, smul_eq_mul]
    calc
      (∫ x in Set.Ioi (0 : ℝ), (s * x ^ (s - 1)) • g (x ^ s))
          = ∫ x in Set.Ioi (0 : ℝ),
              (Set.Ioo (0 : ℝ) 1).indicator kernel x := hraw
      _ = ∫ x in Set.Ioo (0 : ℝ) 1, kernel x := by
          rw [MeasureTheory.setIntegral_indicator measurableSet_Ioo]
          exact MeasureTheory.setIntegral_congr_set
            (by
              filter_upwards with x
              apply propext
              constructor
              · intro hx
                exact ⟨hx.1, hx.2.2⟩
              · intro hx
                exact ⟨hx.1, hx⟩)
      _ = s * ∫ x in Set.Ioo (0 : ℝ) 1,
            x ^ (((j : ℝ) + s) - 1) * (1 - x) ^ n := by
          dsimp [kernel]
          rw [MeasureTheory.integral_const_mul]
  calc
    ∫ y in Set.Ioo (0 : ℝ) 1, (y ^ beta) ^ j * (1 - y ^ beta) ^ n
        = ∫ y in Set.Ioi (0 : ℝ), g y := hright.symm
    _ = ∫ x in Set.Ioi (0 : ℝ), (s * x ^ (s - 1)) • g (x ^ s) := hsubst.symm
    _ = s * ∫ x in Set.Ioo (0 : ℝ) 1,
          x ^ (((j : ℝ) + s) - 1) * (1 - x) ^ n := hleft
    _ = s * ProbabilityTheory.beta ((j : ℝ) + s) ((n : ℝ) + 1) := by
      have hbeta_int :=
        integral_Ioo_zero_one_rpow_mul_one_sub_rpow_eq_beta
          (a := (j : ℝ) + s) (b := (n : ℝ) + 1)
          (by positivity) (by positivity)
      have hkernel :
          (∫ x in Set.Ioo (0 : ℝ) 1,
              x ^ (((j : ℝ) + s) - 1) * (1 - x) ^ n) =
            ∫ x in Set.Ioo (0 : ℝ) 1,
              x ^ (((j : ℝ) + s) - 1) *
                (1 - x) ^ (((n : ℝ) + 1) - 1) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
        intro x hx
        rw [show ((n : ℝ) + 1) - 1 = (n : ℝ) by ring]
        simp [Real.rpow_natCast]
      rw [hkernel, hbeta_int]

/--
Integrability companion for
`integral_Ioo_zero_one_rpow_power_kernel_eq_s_mul_beta`.
-/
theorem integrableOn_Ioo_zero_one_rpow_power_kernel
    {beta : ℝ} (hbeta_pos : 0 < beta) (j n : ℕ) :
    IntegrableOn
      (fun x : ℝ => (x ^ beta) ^ j * (1 - x ^ beta) ^ n)
      (Set.Ioo (0 : ℝ) 1) := by
  have hmeas :
      AEStronglyMeasurable
        (fun x : ℝ => (x ^ beta) ^ j * (1 - x ^ beta) ^ n)
        volume := by
    exact (by fun_prop :
      Measurable (fun x : ℝ => (x ^ beta) ^ j * (1 - x ^ beta) ^ n)
    ).aestronglyMeasurable
  refine Measure.integrableOn_of_bounded
    (μ := volume) (s := Set.Ioo (0 : ℝ) 1)
    (by simp [Real.volume_Ioo]) hmeas (M := 1) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with x hx
  have hx_nonneg : 0 ≤ x := le_of_lt hx.1
  have hxpow_nonneg : 0 ≤ x ^ beta := Real.rpow_nonneg hx_nonneg beta
  have hxpow_le_one : x ^ beta ≤ 1 :=
    (Real.rpow_lt_one hx_nonneg hx.2 hbeta_pos).le
  have hone_sub_nonneg : 0 ≤ 1 - x ^ beta := by linarith
  have hone_sub_le_one : 1 - x ^ beta ≤ 1 := by linarith
  have hleft_nonneg : 0 ≤ (x ^ beta) ^ j := pow_nonneg hxpow_nonneg j
  have hleft_le_one : (x ^ beta) ^ j ≤ 1 :=
    pow_le_one₀ hxpow_nonneg hxpow_le_one
  have hright_nonneg : 0 ≤ (1 - x ^ beta) ^ n :=
    pow_nonneg hone_sub_nonneg n
  have hright_le_one : (1 - x ^ beta) ^ n ≤ 1 :=
    pow_le_one₀ hone_sub_nonneg hone_sub_le_one
  have hprod_nonneg :
      0 ≤ (x ^ beta) ^ j * (1 - x ^ beta) ^ n :=
    mul_nonneg hleft_nonneg hright_nonneg
  have hprod_le_one :
      (x ^ beta) ^ j * (1 - x ^ beta) ^ n ≤ 1 := by
    calc
      (x ^ beta) ^ j * (1 - x ^ beta) ^ n
          ≤ 1 * 1 := mul_le_mul hleft_le_one hright_le_one
            hright_nonneg (by norm_num)
      _ = 1 := by ring
  have hnorm :
      ‖(x ^ beta) ^ j * (1 - x ^ beta) ^ n‖ =
        (x ^ beta) ^ j * (1 - x ^ beta) ^ n := by
    rw [Real.norm_eq_abs, abs_of_nonneg hprod_nonneg]
  rw [hnorm]
  exact hprod_le_one

/-- Telescoping sum over a natural-number interval. -/
theorem sum_Icc_sub_succ
    (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Icc a b, (f j - f (j + 1)) =
      f a - f (b + 1) := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp
  | succ b ih =>
      by_cases hle : a ≤ b
      · rw [Finset.sum_Icc_succ_top (by omega : a ≤ b + 1), ih hle]
        ring
      · have ha : a = b + 1 := by omega
        subst a
        simp

/--
Binomial coefficient times the complementary factorial, expressed as a gamma
ratio.
-/
theorem nat_choose_mul_gamma_sub_add_one_eq_gamma_div_gamma
    {q j : ℕ} (hjq : j ≤ q) :
    (Nat.choose q j : ℝ) *
        Real.Gamma (((q - j : ℕ) : ℝ) + 1) =
      Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((j : ℝ) + 1) := by
  have hchoose_nat := Nat.choose_mul_factorial_mul_factorial hjq
  have hchoose_real :
      (Nat.choose q j : ℝ) * (Nat.factorial j : ℝ) *
          (Nat.factorial (q - j) : ℝ) =
        (Nat.factorial q : ℝ) := by
    exact_mod_cast hchoose_nat
  have hj_fact_ne : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  rw [Real.Gamma_nat_eq_factorial q, Real.Gamma_nat_eq_factorial j,
    Real.Gamma_nat_eq_factorial (q - j)]
  field_simp [hj_fact_ne]
  ring_nf at hchoose_real ⊢
  exact hchoose_real

/--
The binomial coefficient times the beta kernel from a continuous-uniform
order-statistic tail is the constant `1/(q+1)`.
-/
theorem nat_choose_mul_beta_nat_sub_add_one_eq_inv_succ
    {q j : ℕ} (hjq : j ≤ q) :
    (Nat.choose q j : ℝ) *
        ProbabilityTheory.beta
          (((q - j : ℕ) : ℝ) + 1)
          (((j : ℕ) : ℝ) + 1) =
      1 / (((q : ℕ) : ℝ) + 1) := by
  have hchoose :=
    nat_choose_mul_gamma_sub_add_one_eq_gamma_div_gamma
      (q := q) (j := j) hjq
  have hbeta_arg :
      (((q - j : ℕ) : ℝ) + 1) + (((j : ℕ) : ℝ) + 1) =
        ((q : ℕ) : ℝ) + 2 := by
    rw [Nat.cast_sub hjq]
    ring
  have hG_j_ne : Real.Gamma (((j : ℕ) : ℝ) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hG_q_ne : Real.Gamma (((q : ℕ) : ℝ) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hq_ne : ((q : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  unfold ProbabilityTheory.beta
  rw [hbeta_arg]
  rw [show ((q : ℕ) : ℝ) + 2 = (((q : ℕ) : ℝ) + 1) + 1 by ring]
  rw [Real.Gamma_add_one hq_ne]
  calc
    (Nat.choose q j : ℝ) *
        (Real.Gamma (((q - j : ℕ) : ℝ) + 1) *
          Real.Gamma (((j : ℕ) : ℝ) + 1) /
            ((((q : ℕ) : ℝ) + 1) *
              Real.Gamma (((q : ℕ) : ℝ) + 1)))
        =
        ((Nat.choose q j : ℝ) *
          Real.Gamma (((q - j : ℕ) : ℝ) + 1)) *
            Real.Gamma (((j : ℕ) : ℝ) + 1) /
              ((((q : ℕ) : ℝ) + 1) *
                Real.Gamma (((q : ℕ) : ℝ) + 1)) := by
          ring
    _ =
        (Real.Gamma (((q : ℕ) : ℝ) + 1) /
          Real.Gamma (((j : ℕ) : ℝ) + 1)) *
            Real.Gamma (((j : ℕ) : ℝ) + 1) /
              ((((q : ℕ) : ℝ) + 1) *
                Real.Gamma (((q : ℕ) : ℝ) + 1)) := by
          rw [hchoose]
    _ = 1 / (((q : ℕ) : ℝ) + 1) := by
          field_simp [hG_j_ne, hG_q_ne, hq_ne]

/--
The fixed-`j` gamma-ratio difference that makes the Pareto beta tail sum
telescoping.
-/
theorem gamma_ratio_sub_succ_eq_delta_mul_gamma_div
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    {j : ℕ} (hj : 1 ≤ j) :
    Real.Gamma ((j : ℝ) - δ) / Real.Gamma (j : ℝ) -
        Real.Gamma (((j + 1 : ℕ) : ℝ) - δ) /
          Real.Gamma ((j + 1 : ℕ) : ℝ)
      =
      δ * Real.Gamma ((j : ℝ) - δ) /
        Real.Gamma ((j + 1 : ℕ) : ℝ) := by
  have hj_real : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hj_pos : 0 < (j : ℝ) := by exact_mod_cast hj
  have harg_pos : 0 < (j : ℝ) - δ := by linarith
  have hG_j_ne : Real.Gamma (j : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos hj_pos).ne'
  have hj_ne : (j : ℝ) ≠ 0 := ne_of_gt hj_pos
  have hG_arg_ne : Real.Gamma ((j : ℝ) - δ) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg_pos).ne'
  have hG_arg_succ :
      Real.Gamma (((j + 1 : ℕ) : ℝ) - δ) =
        ((j : ℝ) - δ) * Real.Gamma ((j : ℝ) - δ) := by
    rw [show (((j + 1 : ℕ) : ℝ) - δ) =
          ((j : ℝ) - δ) + 1 by
        rw [Nat.cast_add, Nat.cast_one]
        ring]
    exact Real.Gamma_add_one (ne_of_gt harg_pos)
  have hG_j_succ :
      Real.Gamma ((j + 1 : ℕ) : ℝ) =
        (j : ℝ) * Real.Gamma (j : ℝ) := by
    rw [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by
      rw [Nat.cast_add, Nat.cast_one]]
    exact Real.Gamma_add_one hj_ne
  rw [hG_arg_succ, hG_j_succ]
  field_simp [hG_j_ne, hj_ne, hG_arg_ne]
  ring

/--
A binomial-beta summand in the Pareto upper-tail expectation is a telescoping
gamma-ratio difference.
-/
theorem choose_mul_delta_mul_beta_eq_gamma_ratio_mul_diff
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    {q j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ q) :
    (Nat.choose q j : ℝ) *
        (δ *
          ProbabilityTheory.beta
            ((j : ℝ) - δ)
            (((q - j : ℕ) : ℝ) + 1))
      =
      (Real.Gamma ((q : ℝ) + 1) /
          Real.Gamma ((q : ℝ) + 1 - δ)) *
        (Real.Gamma ((j : ℝ) - δ) / Real.Gamma (j : ℝ) -
          Real.Gamma (((j + 1 : ℕ) : ℝ) - δ) /
            Real.Gamma ((j + 1 : ℕ) : ℝ)) := by
  have hj_real : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hqj_real : (j : ℝ) ≤ (q : ℝ) := by exact_mod_cast hjq
  have harg_j_pos : 0 < (j : ℝ) - δ := by linarith
  have harg_q_pos : 0 < (q : ℝ) + 1 - δ := by linarith
  have harg_q_ne : Real.Gamma ((q : ℝ) + 1 - δ) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg_q_pos).ne'
  have hG_j_succ_ne : Real.Gamma ((j : ℝ) + 1) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hchoose :=
    nat_choose_mul_gamma_sub_add_one_eq_gamma_div_gamma
      (q := q) (j := j) hjq
  have hdiff :=
    gamma_ratio_sub_succ_eq_delta_mul_gamma_div
      hδ_pos hδ_lt_one hj
  rw [hdiff]
  rw [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by
    rw [Nat.cast_add, Nat.cast_one]]
  unfold ProbabilityTheory.beta
  have hbeta_arg :
      (j : ℝ) - δ + (((q - j : ℕ) : ℝ) + 1) =
        (q : ℝ) + 1 - δ := by
    have hsub_cast : ((q - j : ℕ) : ℝ) = (q : ℝ) - (j : ℝ) := by
      exact Nat.cast_sub hjq
    rw [hsub_cast]
    ring
  rw [hbeta_arg]
  calc
    (Nat.choose q j : ℝ) *
        (δ *
          (Real.Gamma ((j : ℝ) - δ) *
            Real.Gamma (((q - j : ℕ) : ℝ) + 1) /
              Real.Gamma ((q : ℝ) + 1 - δ)))
        =
        ((Nat.choose q j : ℝ) *
          Real.Gamma (((q - j : ℕ) : ℝ) + 1)) *
          (δ * Real.Gamma ((j : ℝ) - δ) /
            Real.Gamma ((q : ℝ) + 1 - δ)) := by
          field_simp [harg_q_ne]
    _ =
        (Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((j : ℝ) + 1)) *
          (δ * Real.Gamma ((j : ℝ) - δ) /
            Real.Gamma ((q : ℝ) + 1 - δ)) := by
          rw [hchoose]
    _ =
        Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((q : ℝ) + 1 - δ) *
          (δ * Real.Gamma ((j : ℝ) - δ) /
            Real.Gamma ((j : ℝ) + 1)) := by
          field_simp [harg_q_ne, hG_j_succ_ne]

/--
Closed form for the finite beta tail that appears in scale-one Pareto
upper-order-statistic expectations.

The proof is the standard telescoping identity
`δ Γ(j-δ)/Γ(j+1) = Γ(j-δ)/Γ(j) - Γ(j+1-δ)/Γ(j+1)`.
-/
theorem one_add_sum_choose_mul_delta_mul_beta_eq_gamma_ratio
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    {r q : ℕ} (hrq : r ≤ q) :
    1 +
        ∑ j ∈ Finset.Icc (r + 1) q,
          (Nat.choose q j : ℝ) *
            (δ *
              ProbabilityTheory.beta
                ((j : ℝ) - δ)
                (((q - j : ℕ) : ℝ) + 1))
      =
      (Real.Gamma ((r : ℝ) + 1 - δ) /
          Real.Gamma ((r : ℝ) + 1)) *
        (Real.Gamma ((q : ℝ) + 1) /
          Real.Gamma ((q : ℝ) + 1 - δ)) := by
  by_cases hrlt : r < q
  · let Gq : ℝ :=
      Real.Gamma ((q : ℝ) + 1) /
        Real.Gamma ((q : ℝ) + 1 - δ)
    let A : ℕ → ℝ := fun j =>
      Real.Gamma ((j : ℝ) - δ) / Real.Gamma (j : ℝ)
    have hsum :
        ∑ j ∈ Finset.Icc (r + 1) q,
          (Nat.choose q j : ℝ) *
            (δ *
              ProbabilityTheory.beta
                ((j : ℝ) - δ)
                (((q - j : ℕ) : ℝ) + 1))
          =
        ∑ j ∈ Finset.Icc (r + 1) q,
          Gq * (A j - A (j + 1)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj_lower : 1 ≤ j := by
        have h := (Finset.mem_Icc.mp hj).1
        omega
      have hj_upper : j ≤ q := (Finset.mem_Icc.mp hj).2
      dsimp [Gq, A]
      exact choose_mul_delta_mul_beta_eq_gamma_ratio_mul_diff
        hδ_pos hδ_lt_one hj_lower hj_upper
    have htel :
        ∑ j ∈ Finset.Icc (r + 1) q, (A j - A (j + 1)) =
          A (r + 1) - A (q + 1) :=
      sum_Icc_sub_succ A (by omega : r + 1 ≤ q)
    have hGq_den_pos : 0 < (q : ℝ) + 1 - δ := by
      have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
      linarith
    have hGq_den_ne : Real.Gamma ((q : ℝ) + 1 - δ) ≠ 0 :=
      (Real.Gamma_pos_of_pos hGq_den_pos).ne'
    have hGq_num_pos : 0 < (q : ℝ) + 1 := by positivity
    have hGq_num_ne : Real.Gamma ((q : ℝ) + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos hGq_num_pos).ne'
    have hA_r_num_pos : 0 < (r : ℝ) + 1 - δ := by
      have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
      linarith
    have hA_r_num_ne : Real.Gamma ((r : ℝ) + 1 - δ) ≠ 0 :=
      (Real.Gamma_pos_of_pos hA_r_num_pos).ne'
    have hA_r_den_ne : Real.Gamma ((r : ℝ) + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity)).ne'
    rw [hsum, ← Finset.mul_sum, htel]
    dsimp [Gq, A]
    simp_rw [Nat.cast_add, Nat.cast_one]
    field_simp [hGq_den_ne, hGq_num_ne, hA_r_num_ne, hA_r_den_ne]
    ring_nf
  · have hr_eq : r = q := by omega
    subst r
    have hnum_pos : 0 < (q : ℝ) + 1 - δ := by
      have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
      linarith
    have hnum_ne : Real.Gamma ((q : ℝ) + 1 - δ) ≠ 0 :=
      (Real.Gamma_pos_of_pos hnum_pos).ne'
    have hden_ne : Real.Gamma ((q : ℝ) + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity)).ne'
    simp
    field_simp [hnum_ne, hden_ne]

/-- Telescoping sum over a natural-number interval, in forward-difference form. -/
theorem sum_Icc_succ_sub
    (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Icc a b, (f (j + 1) - f j) =
      f (b + 1) - f a := by
  have h := sum_Icc_sub_succ (fun j => -f j) hab
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    Finset.sum_neg_distrib] using h

/--
The fixed-`j` gamma-ratio difference that makes the bounded beta lower-tail
sum telescoping.
-/
theorem gamma_ratio_add_succ_sub_eq_s_mul_gamma_div
    {s : ℝ} (hs_pos : 0 < s) {j : ℕ} (hj : 1 ≤ j) :
    Real.Gamma (((j + 1 : ℕ) : ℝ) + s) /
          Real.Gamma ((j + 1 : ℕ) : ℝ) -
        Real.Gamma ((j : ℝ) + s) / Real.Gamma (j : ℝ)
      =
      s * Real.Gamma ((j : ℝ) + s) /
        Real.Gamma ((j + 1 : ℕ) : ℝ) := by
  have hj_pos : 0 < (j : ℝ) := by exact_mod_cast hj
  have harg_pos : 0 < (j : ℝ) + s := by positivity
  have hG_j_ne : Real.Gamma (j : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos hj_pos).ne'
  have hj_ne : (j : ℝ) ≠ 0 := ne_of_gt hj_pos
  have hG_arg_ne : Real.Gamma ((j : ℝ) + s) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg_pos).ne'
  have hG_arg_succ :
      Real.Gamma (((j + 1 : ℕ) : ℝ) + s) =
        ((j : ℝ) + s) * Real.Gamma ((j : ℝ) + s) := by
    rw [show (((j + 1 : ℕ) : ℝ) + s) =
          ((j : ℝ) + s) + 1 by
        rw [Nat.cast_add, Nat.cast_one]
        ring]
    exact Real.Gamma_add_one (ne_of_gt harg_pos)
  have hG_j_succ :
      Real.Gamma ((j + 1 : ℕ) : ℝ) =
        (j : ℝ) * Real.Gamma (j : ℝ) := by
    rw [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by
      rw [Nat.cast_add, Nat.cast_one]]
    exact Real.Gamma_add_one hj_ne
  rw [hG_arg_succ, hG_j_succ]
  field_simp [hG_j_ne, hj_ne, hG_arg_ne]
  ring

/--
A binomial-beta summand in the bounded reflected-power lower-tail expectation
is a telescoping gamma-ratio difference.
-/
theorem choose_mul_s_mul_beta_add_eq_gamma_ratio_mul_diff
    {s : ℝ} (hs_pos : 0 < s)
    {q j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ q) :
    (Nat.choose q j : ℝ) *
        (s *
          ProbabilityTheory.beta
            ((j : ℝ) + s)
            (((q - j : ℕ) : ℝ) + 1))
      =
      (Real.Gamma ((q : ℝ) + 1) /
          Real.Gamma ((q : ℝ) + 1 + s)) *
        (Real.Gamma (((j + 1 : ℕ) : ℝ) + s) /
            Real.Gamma ((j + 1 : ℕ) : ℝ) -
          Real.Gamma ((j : ℝ) + s) / Real.Gamma (j : ℝ)) := by
  have hqj_real : (j : ℝ) ≤ (q : ℝ) := by exact_mod_cast hjq
  have harg_j_pos : 0 < (j : ℝ) + s := by positivity
  have harg_q_pos : 0 < (q : ℝ) + 1 + s := by positivity
  have harg_q_ne : Real.Gamma ((q : ℝ) + 1 + s) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg_q_pos).ne'
  have hG_j_succ_ne : Real.Gamma ((j : ℝ) + 1) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hchoose :=
    nat_choose_mul_gamma_sub_add_one_eq_gamma_div_gamma
      (q := q) (j := j) hjq
  have hdiff :=
    gamma_ratio_add_succ_sub_eq_s_mul_gamma_div hs_pos hj
  rw [hdiff]
  rw [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by
    rw [Nat.cast_add, Nat.cast_one]]
  unfold ProbabilityTheory.beta
  have hbeta_arg :
      (j : ℝ) + s + (((q - j : ℕ) : ℝ) + 1) =
        (q : ℝ) + 1 + s := by
    have hsub_cast : ((q - j : ℕ) : ℝ) = (q : ℝ) - (j : ℝ) := by
      exact Nat.cast_sub hjq
    rw [hsub_cast]
    ring
  rw [hbeta_arg]
  calc
    (Nat.choose q j : ℝ) *
        (s *
          (Real.Gamma ((j : ℝ) + s) *
            Real.Gamma (((q - j : ℕ) : ℝ) + 1) /
              Real.Gamma ((q : ℝ) + 1 + s)))
        =
        ((Nat.choose q j : ℝ) *
          Real.Gamma (((q - j : ℕ) : ℝ) + 1)) *
          (s * Real.Gamma ((j : ℝ) + s) /
            Real.Gamma ((q : ℝ) + 1 + s)) := by
          field_simp [harg_q_ne]
    _ =
        (Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((j : ℝ) + 1)) *
          (s * Real.Gamma ((j : ℝ) + s) /
            Real.Gamma ((q : ℝ) + 1 + s)) := by
          rw [hchoose]
    _ =
        Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((q : ℝ) + 1 + s) *
          (s * Real.Gamma ((j : ℝ) + s) /
            Real.Gamma ((j : ℝ) + 1)) := by
          field_simp [harg_q_ne, hG_j_succ_ne]

/--
Closed form for the finite beta lower tail that appears in bounded
reflected-power order-statistic endpoint-loss expectations.

The proof is the standard telescoping identity
`s Γ(j+s)/Γ(j+1) = Γ(j+1+s)/Γ(j+1) - Γ(j+s)/Γ(j)`, with the `j = 0`
summand supplying the initial gamma-ratio term.
-/
theorem sum_choose_mul_s_mul_beta_add_eq_gamma_ratio
    {s : ℝ} (hs_pos : 0 < s)
    {r q : ℕ} (hrq : r ≤ q) :
    ∑ j ∈ Finset.Icc 0 r,
          (Nat.choose q j : ℝ) *
            (s *
              ProbabilityTheory.beta
                ((j : ℝ) + s)
                (((q - j : ℕ) : ℝ) + 1))
      =
      (Real.Gamma ((r : ℝ) + 1 + s) /
          Real.Gamma ((r : ℝ) + 1)) *
        (Real.Gamma ((q : ℝ) + 1) /
          Real.Gamma ((q : ℝ) + 1 + s)) := by
  let Gq : ℝ :=
    Real.Gamma ((q : ℝ) + 1) /
      Real.Gamma ((q : ℝ) + 1 + s)
  let A : ℕ → ℝ := fun j =>
    if j = 0 then 0 else Real.Gamma ((j : ℝ) + s) / Real.Gamma (j : ℝ)
  have hterm :
      ∀ j ∈ Finset.Icc 0 r,
        (Nat.choose q j : ℝ) *
            (s *
              ProbabilityTheory.beta
                ((j : ℝ) + s)
                (((q - j : ℕ) : ℝ) + 1)) =
          Gq * (A (j + 1) - A j) := by
    intro j hj
    have hjq : j ≤ q := le_trans (Finset.mem_Icc.mp hj).2 hrq
    by_cases hj_zero : j = 0
    · subst j
      have hq_ne : Real.Gamma ((q : ℝ) + 1 + s) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by positivity)).ne'
      have hGs_ne : Real.Gamma s ≠ 0 :=
        (Real.Gamma_pos_of_pos hs_pos).ne'
      have hGsucc :
          Real.Gamma (1 + s) = s * Real.Gamma s := by
        rw [show 1 + s = s + 1 by ring]
        exact Real.Gamma_add_one hs_pos.ne'
      dsimp [Gq, A]
      simp [hGsucc]
      unfold ProbabilityTheory.beta
      have hbeta_arg : s + (((q : ℕ) : ℝ) + 1) = (q : ℝ) + 1 + s := by
        ring
      rw [hbeta_arg]
      field_simp [hq_ne, hGs_ne]
    · have hj_one : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj_zero)
      simpa [Gq, A, hj_zero] using
        choose_mul_s_mul_beta_add_eq_gamma_ratio_mul_diff
          hs_pos hj_one hjq
  have hsum :
      ∑ j ∈ Finset.Icc 0 r,
          (Nat.choose q j : ℝ) *
            (s *
              ProbabilityTheory.beta
                ((j : ℝ) + s)
                (((q - j : ℕ) : ℝ) + 1))
        =
        ∑ j ∈ Finset.Icc 0 r, Gq * (A (j + 1) - A j) := by
    exact Finset.sum_congr rfl hterm
  have htel :
      ∑ j ∈ Finset.Icc 0 r, (A (j + 1) - A j) =
        A (r + 1) - A 0 :=
    sum_Icc_succ_sub A (by omega : 0 ≤ r)
  have hGq_den_ne : Real.Gamma ((q : ℝ) + 1 + s) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hGq_num_ne : Real.Gamma ((q : ℝ) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hA_r_num_ne : Real.Gamma (((r + 1 : ℕ) : ℝ) + s) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hA_r_den_ne : Real.Gamma ((r + 1 : ℕ) : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [hsum, ← Finset.mul_sum, htel]
  dsimp [Gq, A]
  simp
  ring

/-- A number in `(0,1)` is not an integer pole of `Gamma` after negation. -/
theorem gamma_neg_delta_ne_zero_of_pos_lt_one
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) :
    Real.Gamma (-δ) ≠ 0 := by
  refine Real.Gamma_ne_zero ?_
  intro m hm
  cases m with
  | zero =>
      norm_num at hm
      linarith
  | succ m =>
      have hm_ge_one : (1 : ℝ) ≤ (m.succ : ℝ) := by
        exact_mod_cast Nat.succ_pos m
      have hneg_le : -((m.succ : ℝ)) ≤ -1 := by linarith
      have hgt : -1 < -δ := by linarith
      linarith

/--
Wendel-style upper bound for a positive gamma ratio.

For `0 < s < 1`, log-convexity of `Γ` on `[x,x+1]` gives
`Γ(x+s)/Γ(x) ≤ x^s`.
-/
theorem gamma_add_ratio_le_rpow
    {x s : ℝ} (hx : 0 < x) (hs_pos : 0 < s) (hs_lt_one : s < 1) :
    Real.Gamma (x + s) / Real.Gamma x ≤ x ^ s := by
  have hs_left_pos : 0 < 1 - s := by linarith
  have hx_succ_pos : 0 < x + 1 := by linarith
  have hΓ_pos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hconv :=
    Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
      (s := x) (t := x + 1) (a := 1 - s) (b := s)
      hx hx_succ_pos hs_left_pos hs_pos (by ring)
  have harg : (1 - s) * x + s * (x + 1) = x + s := by ring
  rw [harg, Real.Gamma_add_one hx.ne'] at hconv
  have hΓpow :
      Real.Gamma x ^ (1 - s) * Real.Gamma x ^ s = Real.Gamma x := by
    rw [← Real.rpow_add hΓ_pos]
    ring_nf
    rw [Real.rpow_one]
  have hrhs :
      Real.Gamma x ^ (1 - s) * (x * Real.Gamma x) ^ s =
        Real.Gamma x * x ^ s := by
    rw [Real.mul_rpow hx.le hΓ_pos.le]
    calc
      Real.Gamma x ^ (1 - s) * (x ^ s * Real.Gamma x ^ s)
          = (Real.Gamma x ^ (1 - s) * Real.Gamma x ^ s) * x ^ s := by
              ring
      _ = Real.Gamma x * x ^ s := by rw [hΓpow]
  rw [hrhs] at hconv
  exact (div_le_iff₀ hΓ_pos).2
    (by simpa [mul_comm, mul_left_comm, mul_assoc] using hconv)

/--
Wendel-style lower bound for a positive gamma ratio.

For `0 < s < 1`, applying the upper bound to `x+s` and shift `1-s` gives
`x/(x+s)^(1-s) ≤ Γ(x+s)/Γ(x)`.
-/
theorem rpow_div_le_gamma_add_ratio
    {x s : ℝ} (hx : 0 < x) (hs_pos : 0 < s) (hs_lt_one : s < 1) :
    x / (x + s) ^ (1 - s) ≤ Real.Gamma (x + s) / Real.Gamma x := by
  have hs_left_pos : 0 < 1 - s := by linarith
  have hx_add_pos : 0 < x + s := by positivity
  have hpow_pos : 0 < (x + s) ^ (1 - s) :=
    Real.rpow_pos_of_pos hx_add_pos (1 - s)
  have hΓx_pos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hΓxs_pos : 0 < Real.Gamma (x + s) :=
    Real.Gamma_pos_of_pos hx_add_pos
  have hupper :=
    gamma_add_ratio_le_rpow
      (x := x + s) (s := 1 - s) hx_add_pos hs_left_pos (by linarith)
  have harg : x + s + (1 - s) = x + 1 := by ring
  rw [harg, Real.Gamma_add_one hx.ne'] at hupper
  have hmul : x * Real.Gamma x ≤ (x + s) ^ (1 - s) * Real.Gamma (x + s) := by
    exact (div_le_iff₀ hΓxs_pos).1 hupper
  rw [div_le_iff₀ hpow_pos]
  calc
    x ≤ ((x + s) ^ (1 - s) * Real.Gamma (x + s)) / Real.Gamma x := by
          exact (le_div_iff₀ hΓx_pos).2 hmul
    _ = Real.Gamma (x + s) / Real.Gamma x * (x + s) ^ (1 - s) := by
          field_simp [hΓx_pos.ne']

/--
Shifted upper bound for the reciprocal gamma ratio.

For `1 < x` and `0 < s < 1`,
`Γ(x)/Γ(x+s) ≤ (x-1)^(-s)`.  This combines Wendel's lower gamma-ratio bound
with weighted AM-GM:
`(x+s)^(1-s) * (x-1)^s ≤ x`.
-/
theorem gamma_div_gamma_add_le_pred_rpow_neg
    {x s : ℝ} (hx : 1 < x) (hs_pos : 0 < s) (hs_lt_one : s < 1) :
    Real.Gamma x / Real.Gamma (x + s) ≤ (x - 1) ^ (-s) := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hx_pred_pos : 0 < x - 1 := sub_pos.mpr hx
  have hx_add_pos : 0 < x + s := by positivity
  have hs_left_nonneg : 0 ≤ 1 - s := by linarith
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have hΓx_pos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx_pos
  have hΓxs_pos : 0 < Real.Gamma (x + s) :=
    Real.Gamma_pos_of_pos hx_add_pos
  have hratio_lower :
      x / (x + s) ^ (1 - s) ≤ Real.Gamma (x + s) / Real.Gamma x :=
    rpow_div_le_gamma_add_ratio hx_pos hs_pos hs_lt_one
  have hrecip :
      Real.Gamma x / Real.Gamma (x + s) ≤ (x + s) ^ (1 - s) / x := by
    have hleft_pos : 0 < x / (x + s) ^ (1 - s) := by
      exact div_pos hx_pos (Real.rpow_pos_of_pos hx_add_pos (1 - s))
    have hright_pos : 0 < Real.Gamma (x + s) / Real.Gamma x :=
      div_pos hΓxs_pos hΓx_pos
    have hinv :=
      one_div_le_one_div_of_le hleft_pos hratio_lower
    calc
      Real.Gamma x / Real.Gamma (x + s)
          = 1 / (Real.Gamma (x + s) / Real.Gamma x) := by
              field_simp [hΓx_pos.ne', hΓxs_pos.ne']
      _ ≤ 1 / (x / (x + s) ^ (1 - s)) := hinv
      _ = (x + s) ^ (1 - s) / x := by
              field_simp [hx_pos.ne',
                (Real.rpow_pos_of_pos hx_add_pos (1 - s)).ne']
  have hamgm :
      (x + s) ^ (1 - s) * (x - 1) ^ s ≤ x := by
    have h :=
      Real.geom_mean_le_arith_mean2_weighted
        hs_left_nonneg hs_nonneg hx_add_pos.le hx_pred_pos.le
        (by ring : (1 - s) + s = 1)
    have harith :
        (1 - s) * (x + s) + s * (x - 1) = x - s ^ 2 := by ring
    calc
      (x + s) ^ (1 - s) * (x - 1) ^ s
          ≤ (1 - s) * (x + s) + s * (x - 1) := h
      _ = x - s ^ 2 := harith
      _ ≤ x := by nlinarith [sq_nonneg s]
  have hpow_pred_pos : 0 < (x - 1) ^ s :=
    Real.rpow_pos_of_pos hx_pred_pos s
  have hupper :
      (x + s) ^ (1 - s) / x ≤ (x - 1) ^ (-s) := by
    rw [Real.rpow_neg hx_pred_pos.le]
    rw [div_le_iff₀ hx_pos]
    calc
      (x + s) ^ (1 - s) ≤ x / (x - 1) ^ s := by
            exact (le_div_iff₀ hpow_pred_pos).2 hamgm
      _ = ((x - 1) ^ s)⁻¹ * x := by ring
  exact le_trans hrecip hupper

/--
Shifted upper bound for reciprocal gamma ratios with an arbitrary
natural-plus-fractional shift.

The fractional part is allowed to be zero; the proof then uses only the gamma
recurrence.  This is the reusable extension of Wendel's `0 < s < 1` bound
needed by order-statistic arguments whose decay exponent is not in `(0,1)`.
-/
theorem gamma_div_gamma_add_nat_add_le_pred_rpow_neg
    {x δ : ℝ} (n : ℕ) (hx : 1 < x)
    (hδ_nonneg : 0 ≤ δ) (hδ_lt_one : δ < 1) :
    Real.Gamma x / Real.Gamma (x + ((n : ℝ) + δ)) ≤
      (x - 1) ^ (-((n : ℝ) + δ)) := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hx_pred_pos : 0 < x - 1 := sub_pos.mpr hx
  induction n with
  | zero =>
      by_cases hδ_zero : δ = 0
      · subst δ
        simp [(Real.Gamma_pos_of_pos hx_pos).ne']
      · have hδ_pos : 0 < δ :=
          lt_of_le_of_ne hδ_nonneg (Ne.symm hδ_zero)
        simpa using
          gamma_div_gamma_add_le_pred_rpow_neg hx hδ_pos hδ_lt_one
  | succ n ih =>
      let η : ℝ := (n : ℝ) + δ
      have hη_nonneg : 0 ≤ η := by dsimp [η]; positivity
      have harg_pos : 0 < x + η := by positivity
      have hΓx_pos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx_pos
      have hΓarg_pos : 0 < Real.Gamma (x + η) :=
        Real.Gamma_pos_of_pos harg_pos
      have hΓsucc :
          Real.Gamma (x + (((n + 1 : ℕ) : ℝ) + δ)) =
            (x + η) * Real.Gamma (x + η) := by
        have harg :
            x + (((n + 1 : ℕ) : ℝ) + δ) = (x + η) + 1 := by
          dsimp [η]
          norm_num
          ring
        rw [harg, Real.Gamma_add_one harg_pos.ne']
      have hratio_eq :
          Real.Gamma x / Real.Gamma (x + (((n + 1 : ℕ) : ℝ) + δ)) =
            (Real.Gamma x / Real.Gamma (x + η)) / (x + η) := by
        rw [hΓsucc]
        field_simp [harg_pos.ne', hΓarg_pos.ne']
      have hden_recip :
          1 / (x + η) ≤ 1 / (x - 1) := by
        exact one_div_le_one_div_of_le hx_pred_pos (by linarith)
      have hratio_nonneg :
          0 ≤ Real.Gamma x / Real.Gamma (x + η) :=
        (div_pos hΓx_pos hΓarg_pos).le
      have hpow_nonneg : 0 ≤ (x - 1) ^ (-η) :=
        Real.rpow_nonneg hx_pred_pos.le _
      have hmul :
          (Real.Gamma x / Real.Gamma (x + η)) * (1 / (x + η)) ≤
            (x - 1) ^ (-η) * (1 / (x - 1)) :=
        mul_le_mul ih hden_recip (by positivity) hpow_nonneg
      calc
        Real.Gamma x / Real.Gamma (x + (((n + 1 : ℕ) : ℝ) + δ))
            = (Real.Gamma x / Real.Gamma (x + η)) * (1 / (x + η)) := by
                rw [hratio_eq]
                ring
        _ ≤ (x - 1) ^ (-η) * (1 / (x - 1)) := hmul
        _ = (x - 1) ^ (-(((n + 1 : ℕ) : ℝ) + δ)) := by
              have hsucc_eta :
                  (((n + 1 : ℕ) : ℝ) + δ) = η + 1 := by
                dsimp [η]
                norm_num
                ring
              have hpow_pos : 0 < (x - 1) ^ η :=
                Real.rpow_pos_of_pos hx_pred_pos η
              rw [hsucc_eta]
              rw [Real.rpow_neg hx_pred_pos.le η,
                Real.rpow_neg hx_pred_pos.le (η + 1)]
              rw [Real.rpow_add hx_pred_pos η 1, Real.rpow_one]
              dsimp [η]
              norm_num
              field_simp [hx_pred_pos.ne', hpow_pos.ne']

/--
Shifted lower bound for reciprocal gamma ratios with an arbitrary
natural-plus-fractional shift.

For `0 ≤ δ < 1`, `Γ(x)/Γ(x+n+δ)` is bounded below by the same power law with
the base shifted to `x+n`.  Together with
`gamma_div_gamma_add_nat_add_le_pred_rpow_neg`, this gives two-sided shifted
power envelopes for every positive gamma-ratio shift.
-/
theorem rpow_neg_add_nat_le_gamma_div_gamma_add_nat_add
    {x δ : ℝ} (n : ℕ) (hx : 0 < x)
    (hδ_nonneg : 0 ≤ δ) (hδ_lt_one : δ < 1) :
    (x + (n : ℝ)) ^ (-((n : ℝ) + δ)) ≤
      Real.Gamma x / Real.Gamma (x + ((n : ℝ) + δ)) := by
  induction n with
  | zero =>
      by_cases hδ_zero : δ = 0
      · subst δ
        simp [(Real.Gamma_pos_of_pos hx).ne']
      · have hδ_pos : 0 < δ :=
          lt_of_le_of_ne hδ_nonneg (Ne.symm hδ_zero)
        have hxδ_pos : 0 < x + δ := by positivity
        have hΓx_pos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
        have hΓxδ_pos : 0 < Real.Gamma (x + δ) :=
          Real.Gamma_pos_of_pos hxδ_pos
        have hupper :
            Real.Gamma (x + δ) / Real.Gamma x ≤ x ^ δ :=
          gamma_add_ratio_le_rpow hx hδ_pos hδ_lt_one
        have hratio_pos : 0 < Real.Gamma (x + δ) / Real.Gamma x :=
          div_pos hΓxδ_pos hΓx_pos
        have hxpow_pos : 0 < x ^ δ := Real.rpow_pos_of_pos hx δ
        have hinv := one_div_le_one_div_of_le hratio_pos hupper
        simpa using
          (calc
            x ^ (-δ) = 1 / x ^ δ := by
              rw [Real.rpow_neg hx.le δ]
              ring
            _ ≤ 1 / (Real.Gamma (x + δ) / Real.Gamma x) := hinv
            _ = Real.Gamma x / Real.Gamma (x + δ) := by
              field_simp [hΓx_pos.ne', hΓxδ_pos.ne', hxpow_pos.ne'])
  | succ n ih =>
      let η : ℝ := (n : ℝ) + δ
      have hη_nonneg : 0 ≤ η := by dsimp [η]; positivity
      have hxη_pos : 0 < x + η := by positivity
      have hx_n_pos : 0 < x + (n : ℝ) := by positivity
      have hx_n_succ_pos : 0 < x + ((n + 1 : ℕ) : ℝ) := by positivity
      have hΓx_pos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
      have hΓarg_pos : 0 < Real.Gamma (x + η) :=
        Real.Gamma_pos_of_pos hxη_pos
      have hΓsucc :
          Real.Gamma (x + (((n + 1 : ℕ) : ℝ) + δ)) =
            (x + η) * Real.Gamma (x + η) := by
        have harg :
            x + (((n + 1 : ℕ) : ℝ) + δ) = (x + η) + 1 := by
          dsimp [η]
          norm_num
          ring
        rw [harg, Real.Gamma_add_one hxη_pos.ne']
      have hratio_eq :
          Real.Gamma x / Real.Gamma (x + (((n + 1 : ℕ) : ℝ) + δ)) =
            (Real.Gamma x / Real.Gamma (x + η)) / (x + η) := by
        rw [hΓsucc]
        field_simp [hxη_pos.ne', hΓarg_pos.ne']
      have hpow_mono :
          (x + ((n + 1 : ℕ) : ℝ)) ^ (-η) ≤
            (x + (n : ℝ)) ^ (-η) := by
        exact Real.rpow_le_rpow_of_nonpos hx_n_pos (by norm_num) (by linarith)
      have hden_recip :
          1 / (x + ((n + 1 : ℕ) : ℝ)) ≤ 1 / (x + η) := by
        have hle : x + η ≤ x + ((n + 1 : ℕ) : ℝ) := by
          dsimp [η]
          rw [Nat.cast_add, Nat.cast_one]
          linarith
        exact one_div_le_one_div_of_le hxη_pos hle
      have htarget_eq :
          (x + ((n + 1 : ℕ) : ℝ)) ^ (-(((n + 1 : ℕ) : ℝ) + δ)) =
            (x + ((n + 1 : ℕ) : ℝ)) ^ (-η) *
              (1 / (x + ((n + 1 : ℕ) : ℝ))) := by
        have hsucc_eta :
            (((n + 1 : ℕ) : ℝ) + δ) = η + 1 := by
          dsimp [η]
          norm_num
          ring
        have hpow_pos : 0 < (x + ((n + 1 : ℕ) : ℝ)) ^ η :=
          Real.rpow_pos_of_pos hx_n_succ_pos η
        rw [hsucc_eta]
        rw [Real.rpow_neg hx_n_succ_pos.le η,
          Real.rpow_neg hx_n_succ_pos.le (η + 1)]
        rw [Real.rpow_add hx_n_succ_pos η 1, Real.rpow_one]
        dsimp [η]
        norm_num
        field_simp [hx_n_succ_pos.ne', hpow_pos.ne']
      have hmul_left :
          (x + ((n + 1 : ℕ) : ℝ)) ^ (-η) *
              (1 / (x + ((n + 1 : ℕ) : ℝ))) ≤
            (x + (n : ℝ)) ^ (-η) * (1 / (x + η)) :=
        mul_le_mul hpow_mono hden_recip (by positivity)
          (Real.rpow_nonneg hx_n_pos.le _)
      have hmul_right :
          (x + (n : ℝ)) ^ (-η) * (1 / (x + η)) ≤
            (Real.Gamma x / Real.Gamma (x + η)) * (1 / (x + η)) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      calc
        (x + ((n + 1 : ℕ) : ℝ)) ^
            (-(((n + 1 : ℕ) : ℝ) + δ))
            =
            (x + ((n + 1 : ℕ) : ℝ)) ^ (-η) *
              (1 / (x + ((n + 1 : ℕ) : ℝ))) := htarget_eq
        _ ≤ (x + (n : ℝ)) ^ (-η) * (1 / (x + η)) := hmul_left
        _ ≤ (Real.Gamma x / Real.Gamma (x + η)) * (1 / (x + η)) :=
          hmul_right
        _ = Real.Gamma x / Real.Gamma (x + (((n + 1 : ℕ) : ℝ) + δ)) := by
          rw [hratio_eq]
          ring

/--
Shifted upper bound for reciprocal gamma ratios with an arbitrary positive
shift.

This packages the natural-plus-fractional recurrence wrapper using
`Nat.floor`; it is the all-positive-shift replacement for
`gamma_div_gamma_add_le_pred_rpow_neg`.
-/
theorem gamma_div_gamma_add_le_pred_rpow_neg_of_pos
    {x s : ℝ} (hx : 1 < x) (hs_pos : 0 < s) :
    Real.Gamma x / Real.Gamma (x + s) ≤ (x - 1) ^ (-s) := by
  let n : ℕ := Nat.floor s
  let δ : ℝ := s - n
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have hn_le : (n : ℝ) ≤ s := by
    dsimp [n]
    exact Nat.floor_le hs_nonneg
  have hs_lt_succ : s < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one s
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    linarith
  have hδ_lt_one : δ < 1 := by
    dsimp [δ]
    linarith
  have hs_eq : (n : ℝ) + δ = s := by
    dsimp [δ]
    ring
  simpa [hs_eq] using
    gamma_div_gamma_add_nat_add_le_pred_rpow_neg
      (x := x) (δ := δ) n hx hδ_nonneg hδ_lt_one

/--
Shifted lower bound for reciprocal gamma ratios with an arbitrary positive
shift.

The coarser base `(x+s)` is often the convenient finite envelope for
order-statistic marginal comparisons.
-/
theorem rpow_neg_add_shift_le_gamma_div_gamma_add
    {x s : ℝ} (hx : 0 < x) (hs_pos : 0 < s) :
    (x + s) ^ (-s) ≤ Real.Gamma x / Real.Gamma (x + s) := by
  let n : ℕ := Nat.floor s
  let δ : ℝ := s - n
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have hn_le : (n : ℝ) ≤ s := by
    dsimp [n]
    exact Nat.floor_le hs_nonneg
  have hs_lt_succ : s < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one s
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    linarith
  have hδ_lt_one : δ < 1 := by
    dsimp [δ]
    linarith
  have hs_eq : (n : ℝ) + δ = s := by
    dsimp [δ]
    ring
  have hx_n_pos : 0 < x + (n : ℝ) := by positivity
  have hpow_shift :
      (x + s) ^ (-s) ≤ (x + (n : ℝ)) ^ (-s) := by
    exact Real.rpow_le_rpow_of_nonpos hx_n_pos (by linarith) (by linarith)
  have hgamma :=
    rpow_neg_add_nat_le_gamma_div_gamma_add_nat_add
      (x := x) (δ := δ) n hx hδ_nonneg hδ_lt_one
  exact le_trans hpow_shift (by simpa [hs_eq] using hgamma)

/--
Finite gamma recurrence product for a shift `-δ` with `0 < δ < 1`.

This rewrites Euler's `GammaSeq (-δ)` product into the gamma-ratio form often
needed for fixed-rank order-statistic tails.
-/
theorem gamma_neg_delta_prod_range_eq_gamma_div
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (q : ℕ) :
    (∏ j ∈ Finset.range (q + 1), (-δ + (j : ℝ))) =
      Real.Gamma ((q : ℝ) + 1 - δ) / Real.Gamma (-δ) := by
  have hG_ne : Real.Gamma (-δ) ≠ 0 :=
    gamma_neg_delta_ne_zero_of_pos_lt_one hδ_pos hδ_lt_one
  induction q with
  | zero =>
      have hδ_ne : -δ ≠ 0 := by linarith
      rw [Finset.prod_range_one, Nat.cast_zero, add_zero, zero_add,
        show (1 : ℝ) - δ = -δ + 1 by ring]
      rw [Real.Gamma_add_one hδ_ne]
      field_simp [hG_ne]
  | succ q ih =>
      rw [Finset.prod_range_succ, ih]
      rw [show -δ + (((q + 1 : ℕ) : ℝ)) = (q : ℝ) + 1 - δ by
        rw [Nat.cast_add, Nat.cast_one]
        ring]
      have harg_pos : 0 < (q : ℝ) + 1 - δ := by
        have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
        linarith
      have harg_ne : (q : ℝ) + 1 - δ ≠ 0 := ne_of_gt harg_pos
      rw [show ((q.succ : ℕ) : ℝ) + 1 - δ =
            ((q : ℝ) + 1 - δ) + 1 by
              rw [Nat.cast_succ]
              ring,
        Real.Gamma_add_one harg_ne]
      field_simp [hG_ne]

/--
Finite gamma recurrence product for a positive shift.

This rewrites Euler's `GammaSeq s` product into the gamma-ratio form needed by
bounded beta/order-statistic tails.
-/
theorem gamma_pos_prod_range_eq_gamma_div
    {s : ℝ} (hs : 0 < s) (q : ℕ) :
    (∏ j ∈ Finset.range (q + 1), (s + (j : ℝ))) =
      Real.Gamma ((q : ℝ) + 1 + s) / Real.Gamma s := by
  have hG_ne : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos hs).ne'
  induction q with
  | zero =>
      rw [Finset.prod_range_one, Nat.cast_zero, add_zero,
        show (0 : ℝ) + 1 + s = s + 1 by ring]
      rw [Real.Gamma_add_one hs.ne']
      field_simp [hG_ne]
  | succ q ih =>
      rw [Finset.prod_range_succ, ih]
      rw [show s + (((q + 1 : ℕ) : ℝ)) = (q : ℝ) + 1 + s by
        rw [Nat.cast_add, Nat.cast_one]
        ring]
      have harg_pos : 0 < (q : ℝ) + 1 + s := by positivity
      have harg_ne : (q : ℝ) + 1 + s ≠ 0 := ne_of_gt harg_pos
      rw [show ((q.succ : ℕ) : ℝ) + 1 + s =
            ((q : ℝ) + 1 + s) + 1 by
              rw [Nat.cast_succ]
              ring,
        Real.Gamma_add_one harg_ne]
      field_simp [hG_ne]

/-- Gamma-ratio asymptotic: `Γ(q+1) / Γ(q+1-δ) ~ q^δ`. -/
theorem gamma_ratio_nat_add_one_sub_asymptoticEquivalent
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) :
    AsymptoticEquivalent
      (fun q : ℕ =>
        Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((q : ℝ) + 1 - δ))
      (fun q : ℕ => (q : ℝ) ^ δ) := by
  rw [AsymptoticEquivalent]
  have hG_ne : Real.Gamma (-δ) ≠ 0 :=
    gamma_neg_delta_ne_zero_of_pos_lt_one hδ_pos hδ_lt_one
  have hseq :
      Filter.Tendsto
        (fun q : ℕ => Real.GammaSeq (-δ) q / Real.Gamma (-δ))
        Filter.atTop (nhds 1) := by
    have h := (Real.GammaSeq_tendsto_Gamma (-δ)).div_const (Real.Gamma (-δ))
    simpa [hG_ne] using h
  refine Filter.Tendsto.congr' ?_ hseq
  filter_upwards [Filter.eventually_gt_atTop 0] with q hq
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq_nonneg : 0 ≤ (q : ℝ) := le_of_lt hq_pos
  have hqpow_ne : (q : ℝ) ^ δ ≠ 0 :=
    (Real.rpow_pos_of_pos hq_pos δ).ne'
  have hqdelta_neg : (q : ℝ) ^ (-δ) = ((q : ℝ) ^ δ)⁻¹ := by
    exact Real.rpow_neg hq_nonneg δ
  have hden_pos : 0 < (q : ℝ) + 1 - δ := by
    linarith
  have hden_gamma_ne : Real.Gamma ((q : ℝ) + 1 - δ) ≠ 0 :=
    (Real.Gamma_pos_of_pos hden_pos).ne'
  rw [Real.GammaSeq, gamma_neg_delta_prod_range_eq_gamma_div hδ_pos hδ_lt_one q,
    ← Real.Gamma_nat_eq_factorial q, hqdelta_neg]
  field_simp [hG_ne, hden_gamma_ne, hqpow_ne]

/-- Gamma-ratio asymptotic: `Γ(q+1) / Γ(q+1+s) ~ q^(-s)`. -/
theorem gamma_ratio_nat_add_one_add_asymptoticEquivalent
    {s : ℝ} (hs : 0 < s) :
    AsymptoticEquivalent
      (fun q : ℕ =>
        Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((q : ℝ) + 1 + s))
      (fun q : ℕ => (q : ℝ) ^ (-s)) := by
  rw [AsymptoticEquivalent]
  have hG_ne : Real.Gamma s ≠ 0 :=
    (Real.Gamma_pos_of_pos hs).ne'
  have hseq :
      Filter.Tendsto
        (fun q : ℕ => Real.GammaSeq s q / Real.Gamma s)
        Filter.atTop (nhds 1) := by
    have h := (Real.GammaSeq_tendsto_Gamma s).div_const (Real.Gamma s)
    simpa [hG_ne] using h
  refine Filter.Tendsto.congr' ?_ hseq
  filter_upwards [Filter.eventually_gt_atTop 0] with q hq
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq_nonneg : 0 ≤ (q : ℝ) := le_of_lt hq_pos
  have hqpow_ne : (q : ℝ) ^ s ≠ 0 :=
    (Real.rpow_pos_of_pos hq_pos s).ne'
  have hqpow_neg : (q : ℝ) ^ (-s) = ((q : ℝ) ^ s)⁻¹ := by
    exact Real.rpow_neg hq_nonneg s
  have hden_pos : 0 < (q : ℝ) + 1 + s := by positivity
  have hden_gamma_ne : Real.Gamma ((q : ℝ) + 1 + s) ≠ 0 :=
    (Real.Gamma_pos_of_pos hden_pos).ne'
  rw [Real.GammaSeq, gamma_pos_prod_range_eq_gamma_div hs q,
    ← Real.Gamma_nat_eq_factorial q, hqpow_neg]
  field_simp [hG_ne, hden_gamma_ne, hqpow_ne]

/--
Finite-difference bridge from a value asymptotic and an explicit scaled-drop
limit.

If `value q ~ C*q^δ` and
`(q+1) * (value (q+1)-value q) / value q -> δ`, then the finite difference has
the natural scale `(q+1)^(-(1-δ))` and limit `C*δ`.
-/
theorem scaled_difference_limit_of_value_asymptotic_and_scaled_drop
    {value : ℕ → ℝ} {δ C : ℝ}
    (hC_ne : C ≠ 0)
    (hvalue :
      AsymptoticEquivalent
        value
        (fun q : ℕ => C * ((q : ℝ) ^ δ)))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) * ((value (q + 1) - value q) / value q)))
        Filter.atTop (nhds δ)) :
    Filter.Tendsto
      (fun q : ℕ =>
        (value (q + 1) - value q) /
          (((q + 1 : ℕ) : ℝ) ^ (-(1 - δ))))
      Filter.atTop (nhds (C * δ)) := by
  rw [AsymptoticEquivalent] at hvalue
  have hscale :
      Filter.Tendsto
        (fun q : ℕ =>
          ((q : ℝ) ^ δ) /
            (((q + 1 : ℕ) : ℝ) *
              (((q + 1 : ℕ) : ℝ) ^ (-(1 - δ)))))
        Filter.atTop (nhds 1) := by
    have hratio :
        Filter.Tendsto
          (fun q : ℕ => (q : ℝ) / (((q + 1 : ℕ) : ℝ)))
          Filter.atTop (nhds 1) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (1 : ℝ))
    have hrpow :
        Filter.Tendsto
          (fun q : ℕ => (((q : ℝ) / (((q + 1 : ℕ) : ℝ))) ^ δ))
          Filter.atTop (nhds 1) := by
      have h := hratio.rpow_const (p := δ)
        (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
      simpa using h
    refine Filter.Tendsto.congr' ?_ hrpow
    filter_upwards [Filter.eventually_gt_atTop 0] with q hq
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    have hq_succ_pos : 0 < (((q + 1 : ℕ) : ℝ)) := by positivity
    have hq_succ_nonneg : 0 ≤ (((q + 1 : ℕ) : ℝ)) := le_of_lt hq_succ_pos
    have hden_eq :
        (((q + 1 : ℕ) : ℝ) *
          (((q + 1 : ℕ) : ℝ) ^ (-(1 - δ)))) =
          (((q + 1 : ℕ) : ℝ) ^ δ) := by
      nth_rewrite 1 [← Real.rpow_one (((q + 1 : ℕ) : ℝ))]
      rw [← Real.rpow_add hq_succ_pos]
      ring_nf
    rw [hden_eq]
    rw [Real.div_rpow hq_nonneg hq_succ_nonneg]
  have hprod :
      Filter.Tendsto
        (fun q : ℕ =>
          ((((q + 1 : ℕ) : ℝ) *
              ((value (q + 1) - value q) / value q)) *
            (value q / (C * ((q : ℝ) ^ δ)))) *
            (C *
              (((q : ℝ) ^ δ) /
                (((q + 1 : ℕ) : ℝ) *
                  (((q + 1 : ℕ) : ℝ) ^ (-(1 - δ)))))))
        Filter.atTop (nhds (C * δ)) := by
    have h := (hdrop.mul hvalue).mul (hscale.const_mul C)
    simpa [mul_assoc, one_mul, mul_comm, mul_left_comm, mul_right_comm] using h
  have hvalue_ne_eventually : ∀ᶠ q in Filter.atTop, value q ≠ 0 := by
    filter_upwards
      [hvalue.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with q hratio_ne
    intro hzero
    rw [hzero] at hratio_ne
    simp at hratio_ne
  refine Filter.Tendsto.congr' ?_ hprod
  filter_upwards
    [hvalue_ne_eventually, Filter.eventually_gt_atTop 0] with q hvalue_ne hq
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqpow_ne : ((q : ℝ) ^ δ) ≠ 0 :=
    (Real.rpow_pos_of_pos hq_pos δ).ne'
  have hq_succ_pos : 0 < (((q + 1 : ℕ) : ℝ)) := by positivity
  have hscale_ne : (((q + 1 : ℕ) : ℝ) ^ (-(1 - δ))) ≠ 0 :=
    (Real.rpow_pos_of_pos hq_succ_pos (-(1 - δ))).ne'
  have hq_succ_ne : (((q + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hq_succ_pos
  field_simp [hvalue_ne, hqpow_ne, hq_succ_ne, hscale_ne, hC_ne]

end Math
end AppliedModelingLib
