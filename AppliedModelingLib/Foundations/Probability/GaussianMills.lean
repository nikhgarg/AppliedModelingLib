import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gaussian Mills-Ratio Facts

Reusable one-dimensional analytic facts about the unnormalized Gaussian Mills
ratio

`R(t) = exp(t^2 / 2) * ∫_t^∞ exp(-x^2 / 2) dx`.

were first needed for Sampford's Mills-ratio derivative inequality.  The
declarations here are paper-neutral so admissions/testing formalizations can
reuse the same analytic bridge.

## Main declarations

- `gaussianMillsRatio`
- `gaussianMillsRatio_hasDerivAt`
- `gaussianSampfordLowerComparison_lt_millsRatio`
- `gaussianMillsQuadraticBound_concrete`
- `gaussianSampfordMillsBound_concrete`
- `gaussianMillsHazard`
- `gaussianMillsHazard_deriv_lt_one`
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace AppliedModelingLib
namespace Probability

noncomputable section

/--
Unnormalized Gaussian upper-tail integral appearing in the Mills ratio.
-/
def gaussianMillsTail (t : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi t, Real.exp (-(x ^ 2) / 2)

/--
Unnormalized Gaussian Mills ratio,
`R(t) = exp(t^2 / 2) * ∫_t^∞ exp(-x^2 / 2) dx`.
-/
def gaussianMillsRatio (t : ℝ) : ℝ :=
  Real.exp (t ^ 2 / 2) * gaussianMillsTail t

/-- Derivative of the unnormalized Gaussian tail integral. -/
theorem gaussianMillsTail_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianMillsTail (-(Real.exp (-(t ^ 2) / 2))) t := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2)
  have hfint : Integrable f := by
    have hbase := integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by norm_num)
    convert hbase using 1
    ext x
    dsimp [f]
    ring_nf
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hIic_eq (u : ℝ) :
      (∫ x : ℝ in Iic u, f x) =
        (∫ x : ℝ in Iic (0 : ℝ), f x) + ∫ x : ℝ in (0 : ℝ)..u, f x := by
    have hfi0 : IntegrableOn f (Iic (0 : ℝ)) := hfint.integrableOn
    have hfiu : IntegrableOn f (Iic u) := hfint.integrableOn
    have hsub := intervalIntegral.integral_Iic_sub_Iic
      (f := f) (a := (0 : ℝ)) (b := u) hfi0 hfiu
    linarith
  have hIic_deriv : HasDerivAt
      (fun u : ℝ => ∫ x : ℝ in Iic u, f x) (f t) t := by
    have hderiv : HasDerivAt
        (fun u : ℝ =>
          (∫ x : ℝ in Iic (0 : ℝ), f x) + ∫ x : ℝ in (0 : ℝ)..u, f x)
        (f t) t := by
      exact (hcont.integral_hasStrictDerivAt (0 : ℝ) t).hasDerivAt.const_add
        (∫ x : ℝ in Iic (0 : ℝ), f x)
    refine hderiv.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun u => hIic_eq u
  have htail_eq : (fun u : ℝ => gaussianMillsTail u) =ᶠ[nhds t]
      (fun u : ℝ => (∫ x : ℝ, f x) - ∫ x : ℝ in Iic u, f x) := by
    exact Eventually.of_forall fun u => by
      have hsum := intervalIntegral.integral_Iic_add_Ioi
        (f := f) (b := u) (μ := volume) hfint.integrableOn hfint.integrableOn
      dsimp [gaussianMillsTail]
      dsimp [f] at hsum ⊢
      linarith
  exact hIic_deriv.const_sub (∫ x : ℝ, f x) |>.congr_of_eventuallyEq htail_eq

/-- The Gaussian tail integral in the Mills ratio tends to zero at `+∞`. -/
theorem gaussianMillsTail_tendsto_atTop_zero :
    Tendsto gaussianMillsTail atTop (nhds 0) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2)
  have hfint : Integrable f := by
    have hbase := integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by norm_num)
    convert hbase using 1
    ext x
    dsimp [f]
    ring_nf
  have hanti : Antitone (fun t : ℝ => Ioi t) := by
    intro a b hab x hx
    exact hab.trans_lt hx
  have hInter : (⋂ t : ℝ, Ioi t) = ∅ := by
    ext x
    constructor
    · intro hx
      have hxlt : x < x := by
        simpa using (mem_iInter.mp hx x)
      exact (lt_irrefl x hxlt).elim
    · intro hx
      simp at hx
  have htail :=
    tendsto_setIntegral_of_antitone
      (μ := volume) (s := fun t : ℝ => Ioi t) (f := f)
      (fun _ => measurableSet_Ioi) hanti ⟨(0 : ℝ), hfint.integrableOn⟩
  simpa [gaussianMillsTail, f, hInter] using htail

/-- Riccati derivative identity for the concrete Gaussian Mills ratio. -/
theorem gaussianMillsRatio_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianMillsRatio (t * gaussianMillsRatio t - 1) t := by
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (u ^ 2 / 2))
      (t * Real.exp (t ^ 2 / 2)) t := by
    have hinner : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
      simpa using ((hasDerivAt_id t).pow 2).div_const (2 : ℝ)
    convert hinner.exp using 1
    ring
  have htail := gaussianMillsTail_hasDerivAt t
  have hprod := hexp.mul htail
  unfold gaussianMillsRatio gaussianMillsTail at hprod ⊢
  convert hprod using 1
  rw [mul_neg, sub_eq_add_neg]
  congr 1
  · rw [← mul_assoc]
  · rw [← Real.exp_add]
    rw [show t ^ 2 / 2 + -(t ^ 2) / 2 = 0 by ring]
    rw [Real.exp_zero]

/--
Derivative of the Mills-ratio derivative expression. Equivalently,
`R''(t) = (t^2 + 1)R(t)-t`.
-/
theorem gaussianMillsRatio_derivExpr_hasDerivAt (t : ℝ) :
    HasDerivAt
      (fun u => u * gaussianMillsRatio u - 1)
      (((t ^ 2 + 1) * gaussianMillsRatio t) - t) t := by
  have hmul :=
    (hasDerivAt_id t).mul (gaussianMillsRatio_hasDerivAt t)
  have hsub := hmul.sub_const (1 : ℝ)
  convert hsub using 1
  simp [id]
  ring

/--
Sampford's lower comparison function for the Gaussian Mills ratio.
-/
def gaussianSampfordLowerComparison (t : ℝ) : ℝ :=
  (Real.sqrt (t ^ 2 + 4) - t) / 2

/-- Sampford's comparison function is positive. -/
theorem gaussianSampfordLowerComparison_pos (t : ℝ) :
    0 < gaussianSampfordLowerComparison t := by
  unfold gaussianSampfordLowerComparison
  have hsqrt_gt_abs : |t| < Real.sqrt (t ^ 2 + 4) := by
    rw [Real.lt_sqrt (abs_nonneg t)]
    nlinarith [sq_abs t]
  have ht_lt : t < Real.sqrt (t ^ 2 + 4) :=
    (le_abs_self t).trans_lt hsqrt_gt_abs
  linarith

/--
For nonnegative arguments, Sampford's lower comparison is bounded by `1`.
-/
theorem gaussianSampfordLowerComparison_le_one_of_nonneg {t : ℝ}
    (ht : 0 ≤ t) :
    gaussianSampfordLowerComparison t ≤ 1 := by
  unfold gaussianSampfordLowerComparison
  have hsqrt_le : Real.sqrt (t ^ 2 + 4) ≤ t + 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  linarith

/-- Sampford's comparison function is the positive root of `x^2 + t*x - 1 = 0`. -/
theorem gaussianSampfordLowerComparison_quadratic_eq (t : ℝ) :
    (gaussianSampfordLowerComparison t) ^ 2 +
        t * gaussianSampfordLowerComparison t - 1 = 0 := by
  unfold gaussianSampfordLowerComparison
  have hsqrt_sq : (Real.sqrt (t ^ 2 + 4)) ^ 2 = t ^ 2 + 4 := by
    exact Real.sq_sqrt (by nlinarith [sq_nonneg t])
  nlinarith

/-- Derivative of Sampford's lower comparison function. -/
theorem gaussianSampfordLowerComparison_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianSampfordLowerComparison
      ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2) t := by
  have hinner : HasDerivAt (fun u : ℝ => u ^ 2 + 4) (2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).add_const (4 : ℝ) using 1
    simp [id]
  have hpos : t ^ 2 + 4 ≠ 0 := by
    positivity
  have hsqrt := hinner.sqrt hpos
  have hsub := hsqrt.sub (hasDerivAt_id t)
  have hdiv := hsub.div_const (2 : ℝ)
  unfold gaussianSampfordLowerComparison
  convert hdiv using 1
  have hsqrt_ne : Real.sqrt (t ^ 2 + 4) ≠ 0 := by
    exact (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])).ne'
  field_simp [hsqrt_ne]

/-- The comparison function is larger than the reciprocal derivative denominator. -/
theorem gaussianSampfordLowerComparison_inv_sqrt_lt (t : ℝ) :
    (Real.sqrt (t ^ 2 + 4))⁻¹ < gaussianSampfordLowerComparison t := by
  let L := gaussianSampfordLowerComparison t
  let s := Real.sqrt (t ^ 2 + 4)
  have hLpos : 0 < L := gaussianSampfordLowerComparison_pos t
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hroot : L ^ 2 + t * L - 1 = 0 :=
    gaussianSampfordLowerComparison_quadratic_eq t
  have hs_eq : s = 2 * L + t := by
    dsimp [L, s, gaussianSampfordLowerComparison]
    ring
  have hLs : L * s = 1 + L ^ 2 := by
    rw [hs_eq]
    nlinarith
  have hone : 1 < L * s := by
    rw [hLs]
    nlinarith [sq_pos_of_ne_zero hLpos.ne']
  exact (inv_lt_iff_one_lt_mul₀ hspos).2 hone

/-- The derivative correction term in Sampford's comparison proof is positive. -/
theorem gaussianSampfordLowerComparison_sq_add_deriv_pos (t : ℝ) :
    0 <
      (gaussianSampfordLowerComparison t) ^ 2 +
        ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2) := by
  let L := gaussianSampfordLowerComparison t
  let s := Real.sqrt (t ^ 2 + 4)
  have hLpos : 0 < L := gaussianSampfordLowerComparison_pos t
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hderiv_eq : ((t / s - 1) / 2) = -L / s := by
    dsimp [L, s, gaussianSampfordLowerComparison]
    field_simp [hspos.ne']
    ring
  have hinv_lt : s⁻¹ < L := gaussianSampfordLowerComparison_inv_sqrt_lt t
  have hgap : 0 < L - s⁻¹ := sub_pos.mpr hinv_lt
  calc
    0 < L * (L - s⁻¹) := mul_pos hLpos hgap
    _ = L ^ 2 + ((t / s - 1) / 2) := by
      rw [hderiv_eq]
      field_simp [hspos.ne']
      ring

/--
Sampford gap.  Multiplying `gaussianSampfordGap t > 0` by `exp(t^2/2)`
gives `gaussianSampfordLowerComparison t < gaussianMillsRatio t`.
-/
def gaussianSampfordGap (t : ℝ) : ℝ :=
  gaussianMillsTail t -
    gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)

/-- Derivative of the Sampford lower-bound gap. -/
theorem gaussianSampfordGap_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianSampfordGap
      (-(Real.exp (-(t ^ 2) / 2) *
          ((gaussianSampfordLowerComparison t) ^ 2 +
            ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2)))) t := by
  let L := gaussianSampfordLowerComparison
  let E : ℝ → ℝ := fun u => Real.exp (-(u ^ 2) / 2)
  have htail := gaussianMillsTail_hasDerivAt t
  have hL : HasDerivAt L
      ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2) t := by
    simpa [L] using gaussianSampfordLowerComparison_hasDerivAt t
  have hE : HasDerivAt E (-(t * E t)) t := by
    have hinner : HasDerivAt (fun u : ℝ => -(u ^ 2) / 2) (-t) t := by
      convert (((hasDerivAt_id t).pow 2).neg.div_const (2 : ℝ)) using 1
      ring_nf
      simp [id]
    convert hinner.exp using 1
    all_goals
      dsimp [E]
      ring
  have hprod := hL.mul hE
  have hsub := htail.sub hprod
  unfold gaussianSampfordGap gaussianMillsTail
  dsimp [L, E] at hsub ⊢
  convert hsub using 1
  have hroot :
      -((gaussianSampfordLowerComparison t) ^ 2) =
        t * gaussianSampfordLowerComparison t - 1 := by
    have h := gaussianSampfordLowerComparison_quadratic_eq t
    nlinarith
  have hroot_mul :
      Real.exp (t ^ 2 * (-1 / 2)) *
          (-((gaussianSampfordLowerComparison t) ^ 2)) =
        Real.exp (t ^ 2 * (-1 / 2)) *
          (t * gaussianSampfordLowerComparison t - 1) := by
    rw [hroot]
  ring_nf
  ring_nf at hroot_mul
  nlinarith

/-- The Sampford gap has strictly negative derivative. -/
theorem gaussianSampfordGap_deriv_neg (t : ℝ) :
    let d :=
      -(Real.exp (-(t ^ 2) / 2) *
          ((gaussianSampfordLowerComparison t) ^ 2 +
            ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2)))
    d < 0 := by
  dsimp
  have hpos :=
    gaussianSampfordLowerComparison_sq_add_deriv_pos t
  exact neg_neg_of_pos (mul_pos (Real.exp_pos _) hpos)

/-- The Gaussian exponential factor decays at `+∞`. -/
theorem gaussianExpFactor_tendsto_atTop_zero :
    Tendsto (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) atTop (nhds 0) := by
  have harg :
      Tendsto (fun t : ℝ => (-(1 / 2 : ℝ)) * t ^ 2)
        atTop atBot := by
    exact tendsto_neg_const_mul_pow_atTop (n := 2) (by norm_num) (by norm_num)
  refine (Real.tendsto_exp_atBot.comp harg).congr' ?_
  filter_upwards with t
  have hpow : (-(t ^ 2) / 2 : ℝ) = (-(1 / 2 : ℝ)) * t ^ 2 := by
    ring
  simpa [Function.comp_apply, hpow]

/-- Sampford's gap tends to zero at `+∞`. -/
theorem gaussianSampfordGap_tendsto_atTop_zero :
    Tendsto gaussianSampfordGap atTop (nhds 0) := by
  have hprod :
      Tendsto
        (fun t : ℝ =>
          gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2))
        atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ gaussianExpFactor_tendsto_atTop_zero
    · exact Eventually.of_forall fun t =>
        mul_nonneg (le_of_lt (gaussianSampfordLowerComparison_pos t))
          (le_of_lt (Real.exp_pos _))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact mul_le_of_le_one_left (le_of_lt (Real.exp_pos _))
        (gaussianSampfordLowerComparison_le_one_of_nonneg ht)
  simpa [gaussianSampfordGap] using
    gaussianMillsTail_tendsto_atTop_zero.sub hprod

/--
If the Sampford gap tends to zero at `+∞`, then it is positive everywhere
because its derivative is strictly negative.
-/
theorem gaussianSampfordGap_pos_of_tendsto_atTop_zero
    (hlim : Tendsto gaussianSampfordGap atTop (nhds 0)) :
    ∀ t, 0 < gaussianSampfordGap t := by
  have hanti : StrictAnti gaussianSampfordGap := by
    refine strictAnti_of_hasDerivAt_neg
      (f' := fun x =>
        -(Real.exp (-(x ^ 2) / 2) *
          ((gaussianSampfordLowerComparison x) ^ 2 +
            ((x / Real.sqrt (x ^ 2 + 4) - 1) / 2)))) ?_ ?_
    · exact gaussianSampfordGap_hasDerivAt
    · intro x
      exact gaussianSampfordGap_deriv_neg x
  intro t
  have hnext_nonneg : 0 ≤ gaussianSampfordGap (t + 1) := by
    refine le_of_tendsto_of_tendsto hlim tendsto_const_nhds ?_
    filter_upwards [eventually_ge_atTop (t + 1)] with y hy
    by_cases hy_eq : y = t + 1
    · simp [hy_eq]
    · have hlt : t + 1 < y := lt_of_le_of_ne hy (Ne.symm hy_eq)
      exact le_of_lt (hanti hlt)
  have hstrict : gaussianSampfordGap (t + 1) < gaussianSampfordGap t := by
    exact hanti (by linarith)
  linarith

/-- Positivity of the Sampford gap gives the explicit lower Mills-ratio bound. -/
theorem gaussianSampfordLowerComparison_lt_millsRatio_of_gap_pos
    (hgap : ∀ t, 0 < gaussianSampfordGap t) :
    ∀ t, gaussianSampfordLowerComparison t < gaussianMillsRatio t := by
  intro t
  have hgap_t := hgap t
  have htail_lt :
      gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2) <
        gaussianMillsTail t := by
    simpa [gaussianSampfordGap, sub_pos] using hgap_t
  have hmul := mul_lt_mul_of_pos_left htail_lt (Real.exp_pos (t ^ 2 / 2))
  unfold gaussianMillsRatio
  calc
    gaussianSampfordLowerComparison t
        = Real.exp (t ^ 2 / 2) *
            (gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)) := by
          have hexp :
              Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2) / 2) = 1 := by
            rw [← Real.exp_add]
            have : t ^ 2 / 2 + -(t ^ 2) / 2 = 0 := by ring
            rw [this, Real.exp_zero]
          calc
            gaussianSampfordLowerComparison t =
                gaussianSampfordLowerComparison t *
                  (Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2) / 2)) := by
              rw [hexp]
              ring
            _ = Real.exp (t ^ 2 / 2) *
                (gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)) := by
              ring
    _ < Real.exp (t ^ 2 / 2) * gaussianMillsTail t := hmul

/-- Once the explicit gap limit is known, Sampford's lower bound follows. -/
theorem gaussianSampfordLowerComparison_lt_millsRatio_of_gap_tendsto_atTop_zero
    (hlim : Tendsto gaussianSampfordGap atTop (nhds 0)) :
    ∀ t, gaussianSampfordLowerComparison t < gaussianMillsRatio t :=
  gaussianSampfordLowerComparison_lt_millsRatio_of_gap_pos
    (gaussianSampfordGap_pos_of_tendsto_atTop_zero hlim)

/-- Sampford's explicit lower comparison holds for the concrete Gaussian Mills ratio. -/
theorem gaussianSampfordLowerComparison_lt_millsRatio :
    ∀ t, gaussianSampfordLowerComparison t < gaussianMillsRatio t :=
  gaussianSampfordLowerComparison_lt_millsRatio_of_gap_tendsto_atTop_zero
    gaussianSampfordGap_tendsto_atTop_zero

/-- The concrete Gaussian Mills ratio is positive. -/
theorem gaussianMillsRatio_pos (t : ℝ) :
    0 < gaussianMillsRatio t :=
  (gaussianSampfordLowerComparison_pos t).trans
    (gaussianSampfordLowerComparison_lt_millsRatio t)

/-- The unnormalized Gaussian upper tail in the Mills ratio is positive. -/
theorem gaussianMillsTail_pos (t : ℝ) :
    0 < gaussianMillsTail t := by
  have hR : 0 < Real.exp (t ^ 2 / 2) * gaussianMillsTail t := by
    simpa [gaussianMillsRatio] using gaussianMillsRatio_pos t
  exact pos_of_mul_pos_left (by simpa [mul_comm] using hR) (Real.exp_pos _).le

/-- Scalar quadratic Mills inequality. -/
def gaussianMillsQuadraticBound (R : ℝ → ℝ) : Prop :=
  ∀ t, 0 < (R t) ^ 2 + t * R t - 1

/-- Sampford's lower bound implies the scalar Mills quadratic inequality. -/
theorem gaussianMillsQuadraticBound_of_sampford_lower
    {R : ℝ → ℝ}
    (hRpos : ∀ t, 0 < R t)
    (hlower : ∀ t, gaussianSampfordLowerComparison t < R t) :
    gaussianMillsQuadraticBound R := by
  intro t
  let L := gaussianSampfordLowerComparison t
  have hLpos : 0 < L := gaussianSampfordLowerComparison_pos t
  have hroot : L ^ 2 + t * L - 1 = 0 :=
    gaussianSampfordLowerComparison_quadratic_eq t
  have hsum_pos : 0 < R t + L + t := by
    have hR_gt_L : L < R t := hlower t
    have hL_formula : 2 * L + t = Real.sqrt (t ^ 2 + 4) := by
      dsimp [L, gaussianSampfordLowerComparison]
      ring
    have hsqrt_pos : 0 < Real.sqrt (t ^ 2 + 4) := by
      exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
    nlinarith
  have hdiff_pos : 0 < R t - L := sub_pos.mpr (hlower t)
  calc
    0 < (R t - L) * (R t + L + t) := mul_pos hdiff_pos hsum_pos
    _ = (R t) ^ 2 + t * R t - 1 := by
      calc
        (R t - L) * (R t + L + t)
            = (R t) ^ 2 + t * R t - (L ^ 2 + t * L) := by ring
        _ = (R t) ^ 2 + t * R t - 1 := by linarith

/-- Concrete scalar Mills quadratic inequality. -/
theorem gaussianMillsQuadraticBound_concrete :
    gaussianMillsQuadraticBound gaussianMillsRatio :=
  gaussianMillsQuadraticBound_of_sampford_lower
    gaussianMillsRatio_pos gaussianSampfordLowerComparison_lt_millsRatio

/--
Determinant/log-convex Mills bound.  For the concrete `R`, the determinant
expression is `R R'' - (R')^2`; expanding the Riccati formulas gives exactly
`R^2 + tR - 1`.
-/
def gaussianMillsDeterminantBound (R : ℝ → ℝ) : Prop :=
  ∀ t, 0 < R t * (((t ^ 2 + 1) * R t) - t) - (t * R t - 1) ^ 2

/-- The determinant/log-convex form is algebraically equivalent to the quadratic form. -/
theorem gaussianMillsQuadraticBound_of_determinant
    (hdet : gaussianMillsDeterminantBound gaussianMillsRatio) :
    gaussianMillsQuadraticBound gaussianMillsRatio := by
  intro t
  have h := hdet t
  convert h using 1
  ring

/--
Sampford derivative bound: the derivative of the reciprocal Mills ratio is
strictly below `1`.
-/
def gaussianSampfordMillsBound (R : ℝ → ℝ) : Prop :=
  ∀ t, ∃ d, HasDerivAt (fun u => (R u)⁻¹) d t ∧ d < 1

/--
A positive differentiable Mills ratio satisfying the quadratic Mills inequality
has Sampford's derivative bound.
-/
theorem gaussianSampfordMillsBound_of_derivative_quadratic
    {R : ℝ → ℝ}
    (hRpos : ∀ t, 0 < R t)
    (hRderiv : ∀ t, HasDerivAt R (t * R t - 1) t)
    (hquad : gaussianMillsQuadraticBound R) :
    gaussianSampfordMillsBound R := by
  intro t
  refine ⟨- (t * R t - 1) / (R t) ^ 2, ?_, ?_⟩
  · exact (hRderiv t).inv (hRpos t).ne'
  · have hden : 0 < (R t) ^ 2 := sq_pos_of_ne_zero (hRpos t).ne'
    have h := hquad t
    rw [div_lt_one hden]
    linarith

/-- Concrete Sampford Mills-ratio derivative bound. -/
theorem gaussianSampfordMillsBound_concrete :
    gaussianSampfordMillsBound gaussianMillsRatio :=
  gaussianSampfordMillsBound_of_derivative_quadratic
    gaussianMillsRatio_pos gaussianMillsRatio_hasDerivAt
    gaussianMillsQuadraticBound_concrete

/-- The reciprocal Mills ratio, equal to the standard-normal hazard rate. -/
def gaussianMillsHazard (t : ℝ) : ℝ :=
  (gaussianMillsRatio t)⁻¹

/-- The reciprocal Mills ratio is positive. -/
theorem gaussianMillsHazard_pos (t : ℝ) :
    0 < gaussianMillsHazard t := by
  unfold gaussianMillsHazard
  exact inv_pos.mpr (gaussianMillsRatio_pos t)

/-- Derivative of the reciprocal Mills ratio. -/
theorem gaussianMillsHazard_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianMillsHazard
      (-(t * gaussianMillsRatio t - 1) / (gaussianMillsRatio t) ^ 2) t := by
  unfold gaussianMillsHazard
  exact (gaussianMillsRatio_hasDerivAt t).inv (gaussianMillsRatio_pos t).ne'

/-- The derivative of the reciprocal Mills ratio is strictly below `1`. -/
theorem gaussianMillsHazard_deriv_lt_one (t : ℝ) :
    ∃ d, HasDerivAt gaussianMillsHazard d t ∧ d < 1 := by
  simpa [gaussianMillsHazard] using gaussianSampfordMillsBound_concrete t

/--
Algebraic consequence of Sampford's comparison function:
for positive arguments, `(t^2+1)L(t)` is strictly larger than `t`.
-/
theorem gaussianSampfordLowerComparison_sq_add_one_mul_gt_arg
    {t : ℝ} (ht : 0 < t) :
    t < (t ^ 2 + 1) * gaussianSampfordLowerComparison t := by
  let s := Real.sqrt (t ^ 2 + 4)
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hleft_nonneg : 0 ≤ t ^ 3 + 3 * t := by positivity
  have hright_nonneg : 0 ≤ (t ^ 2 + 1) * s := by
    exact mul_nonneg (by nlinarith [sq_nonneg t]) hspos.le
  have hs_sq : s ^ 2 = t ^ 2 + 4 := by
    dsimp [s]
    exact Real.sq_sqrt (by nlinarith [sq_nonneg t])
  have hs_sq_gt :
      (t ^ 3 + 3 * t) ^ 2 < ((t ^ 2 + 1) * s) ^ 2 := by
    nlinarith [hs_sq]
  have hcore : t ^ 3 + 3 * t < (t ^ 2 + 1) * s :=
    (sq_lt_sq₀ hleft_nonneg hright_nonneg).1 hs_sq_gt
  dsimp [s] at hcore
  unfold gaussianSampfordLowerComparison
  nlinarith

/--
For positive arguments, Sampford's lower bound implies
`t < (t^2+1)R(t)` for the Gaussian Mills ratio.
-/
theorem gaussianMillsRatio_sq_add_one_mul_gt_arg
    {t : ℝ} (ht : 0 < t) :
    t < (t ^ 2 + 1) * gaussianMillsRatio t := by
  have hL := gaussianSampfordLowerComparison_sq_add_one_mul_gt_arg ht
  have hcoef : 0 < t ^ 2 + 1 := by nlinarith [sq_nonneg t]
  have hlower := gaussianSampfordLowerComparison_lt_millsRatio t
  have hmul :
      (t ^ 2 + 1) * gaussianSampfordLowerComparison t <
        (t ^ 2 + 1) * gaussianMillsRatio t :=
    mul_lt_mul_of_pos_left hlower hcoef
  exact hL.trans hmul

/-- Derivative of `t ↦ gaussianMillsHazard t / t` away from zero. -/
theorem gaussianMillsHazard_div_id_hasDerivAt
    {t : ℝ} (ht_ne : t ≠ 0) :
    HasDerivAt (fun u : ℝ => gaussianMillsHazard u / u)
      (((-(t * gaussianMillsRatio t - 1) / (gaussianMillsRatio t) ^ 2) * t -
          gaussianMillsHazard t) / t ^ 2) t := by
  have hH := gaussianMillsHazard_hasDerivAt t
  convert hH.div (hasDerivAt_id t) ht_ne using 1
  simp [id]

/-- On positive arguments, `t ↦ gaussianMillsHazard t / t` has negative derivative. -/
theorem gaussianMillsHazard_div_id_deriv_neg
    {t : ℝ} (ht : 0 < t) :
    ((-(t * gaussianMillsRatio t - 1) / (gaussianMillsRatio t) ^ 2) * t -
        gaussianMillsHazard t) / t ^ 2 < 0 := by
  let R := gaussianMillsRatio t
  have hRpos : 0 < R := by
    dsimp [R]
    exact gaussianMillsRatio_pos t
  have htR : t < (t ^ 2 + 1) * R := by
    simpa [R] using gaussianMillsRatio_sq_add_one_mul_gt_arg ht
  have hnum : t - t ^ 2 * R - R < 0 := by
    nlinarith
  have hden : 0 < R ^ 2 * t ^ 2 := by
    exact mul_pos (sq_pos_of_ne_zero hRpos.ne') (sq_pos_of_ne_zero ht.ne')
  unfold gaussianMillsHazard
  dsimp [R] at hRpos htR hnum hden ⊢
  field_simp [hRpos.ne', ht.ne']
  nlinarith

/--
The reciprocal Mills ratio divided by its argument is strictly antitone on
positive arguments.
-/
theorem gaussianMillsHazard_div_id_strictAntiOn_Ioi :
    StrictAntiOn (fun t : ℝ => gaussianMillsHazard t / t) (Set.Ioi 0) := by
  have hcont :
      ContinuousOn (fun t : ℝ => gaussianMillsHazard t / t) (Set.Ioi 0) := by
    intro t ht
    have htpos : 0 < t := by simpa using ht
    exact (gaussianMillsHazard_div_id_hasDerivAt htpos.ne').continuousAt.continuousWithinAt
  refine strictAntiOn_of_hasDerivWithinAt_neg
    (D := Set.Ioi (0 : ℝ))
    (f := fun t : ℝ => gaussianMillsHazard t / t)
    (f' := fun t : ℝ =>
      ((-(t * gaussianMillsRatio t - 1) / (gaussianMillsRatio t) ^ 2) * t -
        gaussianMillsHazard t) / t ^ 2)
    (convex_Ioi (0 : ℝ)) hcont ?_ ?_
  · intro t ht
    have htpos : 0 < t := by simpa using ht
    exact (gaussianMillsHazard_div_id_hasDerivAt htpos.ne').hasDerivWithinAt
  · intro t ht
    have htpos : 0 < t := by simpa using ht
    exact gaussianMillsHazard_div_id_deriv_neg htpos

/-- Strict scaled-hazard monotonicity for the Gaussian Mills hazard. -/
theorem gaussianMillsHazard_scaled_strictMono
    {a x y : ℝ} (ha : 0 < a) (hx : 0 < x) (hxy : x < y) :
    x * gaussianMillsHazard (a / x) <
      y * gaussianMillsHazard (a / y) := by
  have hy : 0 < y := hx.trans hxy
  let u := a / y
  let v := a / x
  have hu : u ∈ Set.Ioi (0 : ℝ) := by
    dsimp [u]
    exact div_pos ha hy
  have hv : v ∈ Set.Ioi (0 : ℝ) := by
    dsimp [v]
    exact div_pos ha hx
  have huv : u < v := by
    dsimp [u, v]
    exact div_lt_div_of_pos_left ha hx hxy
  have hratio :
      gaussianMillsHazard v / v < gaussianMillsHazard u / u :=
    gaussianMillsHazard_div_id_strictAntiOn_Ioi hu hv huv
  have hx_eq : x = a / v := by
    dsimp [v]
    field_simp [hx.ne']
  have hy_eq : y = a / u := by
    dsimp [u]
    field_simp [hy.ne']
  have hscaled :
      a * (gaussianMillsHazard v / v) <
        a * (gaussianMillsHazard u / u) :=
    mul_lt_mul_of_pos_left hratio ha
  calc
    x * gaussianMillsHazard (a / x)
        = a * (gaussianMillsHazard v / v) := by
          rw [hx_eq]
          dsimp [v]
          field_simp [ha.ne', hx.ne']
    _ < a * (gaussianMillsHazard u / u) := hscaled
    _ = y * gaussianMillsHazard (a / y) := by
          rw [hy_eq]
          dsimp [u]
          field_simp [ha.ne', hy.ne']

/-- Non-strict scaled-hazard monotonicity for the Gaussian Mills hazard. -/
theorem gaussianMillsHazard_scaled_mono
    {a x y : ℝ} (ha : 0 < a) (hx : 0 < x) (hxy : x ≤ y) :
    x * gaussianMillsHazard (a / x) ≤
      y * gaussianMillsHazard (a / y) := by
  rcases lt_or_eq_of_le hxy with hlt | rfl
  · exact le_of_lt (gaussianMillsHazard_scaled_strictMono ha hx hlt)
  · rfl

/--
Upper-bound gap for the classical Mills inequality `R(t) < 1/t` on positive
arguments, written before multiplication by `exp(t^2/2)`.
-/
def gaussianMillsUpperGap (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2) / 2) / t - gaussianMillsTail t

/-- Derivative of the Mills upper-bound gap away from zero. -/
theorem gaussianMillsUpperGap_hasDerivAt {t : ℝ} (ht_ne : t ≠ 0) :
    HasDerivAt gaussianMillsUpperGap
      (-(Real.exp (-(t ^ 2) / 2) / t ^ 2)) t := by
  let E : ℝ → ℝ := fun u => Real.exp (-(u ^ 2) / 2)
  have hE : HasDerivAt E (-(t * E t)) t := by
    have hinner : HasDerivAt (fun u : ℝ => -(u ^ 2) / 2) (-t) t := by
      convert (((hasDerivAt_id t).pow 2).neg.div_const (2 : ℝ)) using 1
      ring_nf
      simp [id]
    convert hinner.exp using 1
    all_goals
      dsimp [E]
      ring
  have hdiv := hE.div (hasDerivAt_id t) ht_ne
  have htail := gaussianMillsTail_hasDerivAt t
  have hsub := hdiv.sub htail
  unfold gaussianMillsUpperGap gaussianMillsTail
  dsimp [E] at hsub ⊢
  convert hsub using 1
  field_simp [ht_ne]
  ring

/-- The Mills upper-bound gap has strictly negative derivative on positive arguments. -/
theorem gaussianMillsUpperGap_deriv_neg {t : ℝ} (ht : 0 < t) :
    -(Real.exp (-(t ^ 2) / 2) / t ^ 2) < 0 := by
  have hden : 0 < t ^ 2 := sq_pos_of_ne_zero ht.ne'
  exact neg_neg_of_pos (div_pos (Real.exp_pos _) hden)

/-- The first term in the Mills upper-bound gap tends to zero at `+∞`. -/
theorem gaussianMillsUpperGap_firstTerm_tendsto_atTop_zero :
    Tendsto (fun t : ℝ => Real.exp (-(t ^ 2) / 2) / t) atTop (nhds 0) := by
  have hmul :=
    gaussianExpFactor_tendsto_atTop_zero.mul tendsto_inv_atTop_zero
  simpa [div_eq_mul_inv] using hmul

/-- The Mills upper-bound gap tends to zero at `+∞`. -/
theorem gaussianMillsUpperGap_tendsto_atTop_zero :
    Tendsto gaussianMillsUpperGap atTop (nhds 0) := by
  simpa [gaussianMillsUpperGap] using
    gaussianMillsUpperGap_firstTerm_tendsto_atTop_zero.sub
      gaussianMillsTail_tendsto_atTop_zero

/-- The Mills upper-bound gap is positive on positive arguments. -/
theorem gaussianMillsUpperGap_pos_of_pos {t : ℝ} (ht : 0 < t) :
    0 < gaussianMillsUpperGap t := by
  have hanti : StrictAntiOn gaussianMillsUpperGap (Set.Ioi 0) := by
    have hcont : ContinuousOn gaussianMillsUpperGap (Set.Ioi 0) := by
      intro x hx
      have hxpos : 0 < x := by simpa using hx
      exact (gaussianMillsUpperGap_hasDerivAt hxpos.ne').continuousAt.continuousWithinAt
    refine strictAntiOn_of_hasDerivWithinAt_neg
      (D := Set.Ioi (0 : ℝ)) (f := gaussianMillsUpperGap)
      (f' := fun x : ℝ => -(Real.exp (-(x ^ 2) / 2) / x ^ 2))
      (convex_Ioi (0 : ℝ)) hcont ?_ ?_
    · intro x hx
      have hxpos : 0 < x := by simpa using hx
      exact (gaussianMillsUpperGap_hasDerivAt hxpos.ne').hasDerivWithinAt
    · intro x hx
      have hxpos : 0 < x := by simpa using hx
      exact gaussianMillsUpperGap_deriv_neg hxpos
  have ht1 : t + 1 ∈ Set.Ioi (0 : ℝ) := by
    dsimp
    exact add_pos ht zero_lt_one
  have hnext_nonneg : 0 ≤ gaussianMillsUpperGap (t + 1) := by
    refine le_of_tendsto_of_tendsto
      gaussianMillsUpperGap_tendsto_atTop_zero tendsto_const_nhds ?_
    filter_upwards [eventually_ge_atTop (t + 1)] with y hy
    have hypos : y ∈ Set.Ioi (0 : ℝ) := by
      have : 0 < y := lt_of_lt_of_le (by linarith : 0 < t + 1) hy
      exact this
    by_cases hy_eq : y = t + 1
    · simp [hy_eq]
    · have hlt : t + 1 < y := lt_of_le_of_ne hy (Ne.symm hy_eq)
      exact le_of_lt (hanti ht1 hypos hlt)
  have hstrict : gaussianMillsUpperGap (t + 1) < gaussianMillsUpperGap t := by
    exact hanti (show t ∈ Set.Ioi (0 : ℝ) from ht) ht1 (by linarith)
  linarith

/-- Classical upper Mills-ratio bound: `R(t) < 1/t` for `t > 0`. -/
theorem gaussianMillsRatio_lt_inv_of_pos {t : ℝ} (ht : 0 < t) :
    gaussianMillsRatio t < 1 / t := by
  have hgap := gaussianMillsUpperGap_pos_of_pos ht
  have htail_lt :
      gaussianMillsTail t < Real.exp (-(t ^ 2) / 2) / t := by
    simpa [gaussianMillsUpperGap, sub_pos] using hgap
  have hmul := mul_lt_mul_of_pos_left htail_lt (Real.exp_pos (t ^ 2 / 2))
  unfold gaussianMillsRatio
  calc
    Real.exp (t ^ 2 / 2) * gaussianMillsTail t
        < Real.exp (t ^ 2 / 2) * (Real.exp (-(t ^ 2) / 2) / t) := hmul
    _ = 1 / t := by
          calc
            Real.exp (t ^ 2 / 2) * (Real.exp (-(t ^ 2) / 2) / t)
                = (Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2) / 2)) / t := by
                  ring
            _ = 1 / t := by
              rw [← Real.exp_add]
              have hsum : t ^ 2 / 2 + -(t ^ 2) / 2 = 0 := by ring
              rw [hsum, Real.exp_zero]

/-- The reciprocal Mills ratio has positive derivative everywhere. -/
theorem gaussianMillsHazard_deriv_pos (t : ℝ) :
    0 < -(t * gaussianMillsRatio t - 1) / (gaussianMillsRatio t) ^ 2 := by
  let R := gaussianMillsRatio t
  have hRpos : 0 < R := by
    dsimp [R]
    exact gaussianMillsRatio_pos t
  have htR_lt_one : t * R < 1 := by
    by_cases ht : 0 < t
    · have hRlt : R < 1 / t := by
        simpa [R] using gaussianMillsRatio_lt_inv_of_pos ht
      have hmul := mul_lt_mul_of_pos_left hRlt ht
      field_simp [ht.ne'] at hmul
      simpa [R] using hmul
    · have ht_nonpos : t ≤ 0 := le_of_not_gt ht
      have hmul_nonpos : t * R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht_nonpos hRpos.le
      linarith
  have hden : 0 < R ^ 2 := sq_pos_of_ne_zero hRpos.ne'
  dsimp [R] at hRpos htR_lt_one hden ⊢
  exact div_pos (by linarith) hden

/-- The reciprocal Mills ratio is strictly increasing. -/
theorem gaussianMillsHazard_strictMono :
    StrictMono gaussianMillsHazard :=
  strictMono_of_hasDerivAt_pos
    gaussianMillsHazard_hasDerivAt
    (fun t => gaussianMillsHazard_deriv_pos t)

/-- The reciprocal Mills ratio is monotone. -/
theorem gaussianMillsHazard_mono :
    Monotone gaussianMillsHazard :=
  gaussianMillsHazard_strictMono.monotone

/-- On positive arguments, the reciprocal Mills ratio dominates the identity. -/
theorem gaussianMillsHazard_gt_arg_of_pos {t : ℝ} (ht : 0 < t) :
    t < gaussianMillsHazard t := by
  have hRlt : gaussianMillsRatio t < 1 / t :=
    gaussianMillsRatio_lt_inv_of_pos ht
  unfold gaussianMillsHazard
  exact (lt_inv_comm₀ ht (gaussianMillsRatio_pos t)).mpr
    (by simpa [one_div] using hRlt)

end

end Probability
end AppliedModelingLib
