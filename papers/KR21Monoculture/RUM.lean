import KR21Monoculture.Theorem1
import AppliedModelingLib.Foundations.Math.MonotoneContinuity
import AppliedModelingLib.Foundations.Optimization.Endpoint
import AppliedModelingLib.Foundations.Probability.BivariateGaussian
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import AppliedModelingLib.Foundations.Probability.RandomUtility
import AppliedModelingLib.Foundations.Probability.RandomUtilityDensity
import AppliedModelingLib.SocialChoice.Ranking.Probability
import AppliedModelingLib.SocialChoice.Ranking.Score
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open AppliedModelingLib MeasureTheory
open scoped ENNReal NNReal

namespace KR21Monoculture

/-!
# Random-Utility Noise Inequalities

This file starts the random-utility-model side of the monoculture paper with the
finite real inequalities used by Appendix C.
-/

/--
Paper Definition 4, strict form.

For `a > b` and `c > d`, assigning the larger realized value to the larger true
value is strictly more likely than the crossed assignment.
-/
def StrictlyWellOrderedNoise (f : ℝ → ℝ) : Prop := AppliedModelingLib.Probability.StrictlyWellOrderedNoise f

/--
Weak version of Definition 4.  This is useful for Laplacian kernels, where the
strict paper inequality can be an equality when the two ordered intervals are
separated on the real line.
-/
def WeaklyWellOrderedNoise (f : ℝ → ℝ) : Prop := AppliedModelingLib.Probability.WeaklyWellOrderedNoise f

/-- The strict paper condition immediately gives the weak comparison. -/
theorem StrictlyWellOrderedNoise.weak {f : ℝ → ℝ}
    (hf : StrictlyWellOrderedNoise f) :
    WeaklyWellOrderedNoise f :=  AppliedModelingLib.Probability.StrictlyWellOrderedNoise.weak hf

/-- Positive density normalization preserves strict well-ordering. -/
theorem StrictlyWellOrderedNoise.const_mul_pos {f : ℝ → ℝ} {c : ℝ}
    (hf : StrictlyWellOrderedNoise f) (hc : 0 < c) :
    StrictlyWellOrderedNoise (fun z => c * f z) :=
  AppliedModelingLib.Probability.StrictlyWellOrderedNoise.const_mul_pos hf hc

/-- Nonnegative density normalization preserves weak well-ordering. -/
theorem WeaklyWellOrderedNoise.const_mul_nonneg {f : ℝ → ℝ} {c : ℝ}
    (hf : WeaklyWellOrderedNoise f) (hc : 0 ≤ c) :
    WeaklyWellOrderedNoise (fun z => c * f z) :=
  AppliedModelingLib.Probability.WeaklyWellOrderedNoise.const_mul_nonneg hf hc

/-- Gaussian density kernel, omitting the positive normalizing constant. -/
noncomputable def gaussianNoiseKernel (κ : ℝ) (x : ℝ) : ℝ := AppliedModelingLib.Probability.gaussianNoiseKernel κ x

/-- Laplacian density kernel, omitting the positive normalizing constant. -/
noncomputable def laplacianNoiseKernel (lam : ℝ) (x : ℝ) : ℝ := AppliedModelingLib.Probability.laplacianNoiseKernel lam x

theorem gaussianNoiseKernel_pos (κ x : ℝ) :
    0 < gaussianNoiseKernel κ x :=  AppliedModelingLib.Probability.gaussianNoiseKernel_pos κ x

theorem gaussianNoiseKernel_nonneg (κ x : ℝ) :
    0 ≤ gaussianNoiseKernel κ x := le_of_lt (gaussianNoiseKernel_pos κ x)

theorem laplacianNoiseKernel_pos (lam x : ℝ) :
    0 < laplacianNoiseKernel lam x :=  AppliedModelingLib.Probability.laplacianNoiseKernel_pos lam x

theorem laplacianNoiseKernel_nonneg (lam x : ℝ) :
    0 ≤ laplacianNoiseKernel lam x := le_of_lt (laplacianNoiseKernel_pos lam x)

/--
The algebraic core of the Gaussian well-ordering proof:
swapping the larger realized value to the larger true value improves the
negative squared-error exponent by `2κ(a-b)(c-d)`.
-/
theorem gaussian_exponent_cross_lt_ordered
    {κ a b c d : ℝ} (hκ : 0 < κ) (hab : b < a) (hcd : d < c) :
    -κ * (a - d) ^ 2 + -κ * (b - c) ^ 2 <
      -κ * (a - c) ^ 2 + -κ * (b - d) ^ 2 :=  AppliedModelingLib.Probability.gaussian_exponent_cross_lt_ordered hκ hab hcd

/-- Gaussian kernels satisfy the paper's strict well-ordering condition. -/
theorem gaussianNoiseKernel_strictlyWellOrdered
    {κ : ℝ} (hκ : 0 < κ) :
    StrictlyWellOrderedNoise (gaussianNoiseKernel κ) := by
  simpa [StrictlyWellOrderedNoise, gaussianNoiseKernel] using
    AppliedModelingLib.Probability.gaussianNoiseKernel_strictlyWellOrdered hκ

/-- Four-point rearrangement inequality for absolute distance on the line. -/
theorem abs_ordered_cross_le_ordered
    {a b c d : ℝ} (hab : b ≤ a) (hcd : d ≤ c) :
    |a - c| + |b - d| ≤ |a - d| + |b - c| :=  AppliedModelingLib.Probability.abs_ordered_cross_le_ordered hab hcd

/--
Strict four-point rearrangement for absolute distance when the two ordered
intervals overlap (`b < c` and `d < a`).
-/
theorem abs_ordered_cross_lt_ordered_of_overlap
    {a b c d : ℝ} (hab : b < a) (hcd : d < c) (hbc : b < c) (hda : d < a) :
    |a - c| + |b - d| < |a - d| + |b - c| :=
   AppliedModelingLib.Probability.abs_ordered_cross_lt_ordered_of_overlap
    hab hcd hbc hda

/-- Laplacian kernels satisfy the weak well-ordering inequality. -/
theorem laplacianNoiseKernel_weaklyWellOrdered
    {lam : ℝ} (hlam : 0 ≤ lam) :
    WeaklyWellOrderedNoise (laplacianNoiseKernel lam) := by
  simpa [WeaklyWellOrderedNoise, laplacianNoiseKernel] using
    AppliedModelingLib.Probability.laplacianNoiseKernel_weaklyWellOrdered hlam

/--
The paper's strict Definition 4 is not satisfied by the Laplacian kernel as
stated: for separated ordered pairs, both assignments have the same total
absolute deviation.
-/
theorem laplacianNoiseKernel_not_strictlyWellOrdered (lam : ℝ) :
    ¬ StrictlyWellOrderedNoise (laplacianNoiseKernel lam) := by
  simpa [StrictlyWellOrderedNoise, laplacianNoiseKernel] using
    AppliedModelingLib.Probability.laplacianNoiseKernel_not_strictlyWellOrdered lam

/--
Laplacian kernels satisfy the strict paper inequality on the overlap region.
With `b < a` and `d < c`, the extra hypotheses `b < c` and `d < a` say exactly
that the open intervals `(b,a)` and `(d,c)` overlap.  This is the pointwise
strict case left after the separated-interval equality case is removed.
-/
theorem laplacianNoiseKernel_strictlyWellOrdered_of_overlap
    {lam a b c d : ℝ} (hlam : 0 < lam)
    (hab : b < a) (hcd : d < c) (hbc : b < c) (hda : d < a) :
    laplacianNoiseKernel lam (a - c) * laplacianNoiseKernel lam (b - d) >
      laplacianNoiseKernel lam (a - d) * laplacianNoiseKernel lam (b - c) := by
  simpa [laplacianNoiseKernel] using
    AppliedModelingLib.Probability.laplacianNoiseKernel_strictlyWellOrdered_of_overlap
      hlam hab hcd hbc hda

/-! ## Appendix C, Theorem 7 scalar Laplacian derivative inequalities -/

/--
Appendix C, Theorem 7 scalar exponential bound used in the middle truncation
case of the Laplacian calculation.
-/
theorem paper_theorem7_exp_neg_gt_one_sub_two_mul {z : ℝ} (hz : 0 < z) :
    1 - 2 * z < Real.exp (-z) := by
  have hlinear : 1 - 2 * z < 1 - z := by linarith
  have hexp : 1 - z < Real.exp (-z) := by
    simpa [sub_eq_add_neg, add_comm] using
      (Real.add_one_lt_exp (show -z ≠ 0 by linarith))
  exact hlinear.trans hexp

/--
Appendix C, Theorem 7, case `x_j < a <= x_i`: after differentiating the
closed-form conditional probability, the sign condition reduces to
`exp (-z) > 1 - 2z` with `z = λ(a - x_j)`.
-/
theorem paper_theorem7_laplacian_case2_derivative_core
    {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) :
    (2 * Real.exp (lam * u) - 1) * lam <
      (1 / 2 + lam * u) * (2 * lam * Real.exp (lam * u)) := by
  let z : ℝ := lam * u
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos hlam hu
  have hneg : 1 - 2 * z < Real.exp (-z) :=
    paper_theorem7_exp_neg_gt_one_sub_two_mul hz
  have hcore : 1 - Real.exp (-z) < 2 * z := by
    linarith
  have hmul :
      Real.exp z * (1 - Real.exp (-z)) <
        Real.exp z * (2 * z) :=
    mul_lt_mul_of_pos_left hcore (Real.exp_pos z)
  have hexp : Real.exp z * Real.exp (-z) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hmain : Real.exp z - 1 < 2 * z * Real.exp z := by
    nlinarith
  have hdiv :
      2 * Real.exp z - 1 < (1 / 2 + z) * (2 * Real.exp z) := by
    nlinarith
  have hscaled :=
    mul_lt_mul_of_pos_right hdiv hlam
  dsimp [z] at hscaled
  nlinarith

/--
The tail ratio subtracted from `1` in Appendix C, Theorem 7, case
`x_j < a <= x_i`.
-/
noncomputable def theorem7LaplacianCase2TailRatio
    (lam xj a : ℝ) : ℝ :=
  (1 / 2 + lam * (a - xj)) /
    (2 * Real.exp (lam * (a - xj)) - 1)

/--
Derivative of the Appendix C, Theorem 7 middle-case tail ratio.
-/
theorem theorem7LaplacianCase2TailRatio_hasDerivAt
    {lam xj a : ℝ}
    (hden : 2 * Real.exp (lam * (a - xj)) - 1 ≠ 0) :
    HasDerivAt
      (fun a => theorem7LaplacianCase2TailRatio lam xj a)
      (((lam) * (2 * Real.exp (lam * (a - xj)) - 1) -
          (1 / 2 + lam * (a - xj)) *
            (2 * (Real.exp (lam * (a - xj)) * lam))) /
        (2 * Real.exp (lam * (a - xj)) - 1) ^ 2)
      a := by
  have hlin : HasDerivAt (fun a => lam * (a - xj)) lam a := by
    simpa using ((hasDerivAt_id a).sub_const xj).const_mul lam
  have hnum :
      HasDerivAt (fun a => 1 / 2 + lam * (a - xj)) lam a := by
    convert (hasDerivAt_const a (1 / 2)).add hlin using 1
    ring
  have hexp :
      HasDerivAt
        (fun a => Real.exp (lam * (a - xj)))
        (Real.exp (lam * (a - xj)) * lam) a :=
    by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_exp (lam * (a - xj))).comp a hlin
  have hden' :
      HasDerivAt
        (fun a => 2 * Real.exp (lam * (a - xj)) - 1)
        (2 * (Real.exp (lam * (a - xj)) * lam)) a := by
    simpa using (hexp.const_mul 2).sub_const 1
  unfold theorem7LaplacianCase2TailRatio
  simpa using hnum.div hden' hden

/--
Appendix C, Theorem 7, case `x_j < a <= x_i`: the derivative of the
closed-form conditional probability is strictly positive in the interior.
-/
theorem theorem7LaplacianCase2ConditionalProb_hasDerivAt_pos
    {lam xj a : ℝ} (hlam : 0 < lam) (hu : 0 < a - xj) :
    ∃ d,
      HasDerivAt
        (fun a => 1 - theorem7LaplacianCase2TailRatio lam xj a) d a ∧
        0 < d := by
  have hden_pos : 0 < 2 * Real.exp (lam * (a - xj)) - 1 := by
    have hz : 0 < lam * (a - xj) := mul_pos hlam hu
    have hexp : 1 < Real.exp (lam * (a - xj)) :=
      Real.one_lt_exp_iff.mpr hz
    nlinarith
  have htail :=
    theorem7LaplacianCase2TailRatio_hasDerivAt
      (lam := lam) (xj := xj) (a := a) hden_pos.ne'
  let dTail :=
    ((lam) * (2 * Real.exp (lam * (a - xj)) - 1) -
        (1 / 2 + lam * (a - xj)) *
          (2 * (Real.exp (lam * (a - xj)) * lam))) /
      (2 * Real.exp (lam * (a - xj)) - 1) ^ 2
  refine ⟨-dTail, ?_, ?_⟩
  · simpa [dTail] using (hasDerivAt_const a (1 : ℝ)).sub htail
  · have hnum_neg :
        lam * (2 * Real.exp (lam * (a - xj)) - 1) -
            (1 / 2 + lam * (a - xj)) *
              (2 * (Real.exp (lam * (a - xj)) * lam)) < 0 := by
      have hcore :=
        paper_theorem7_laplacian_case2_derivative_core
          (lam := lam) (u := a - xj) hlam hu
      nlinarith
    have hden_sq_pos :
        0 < (2 * Real.exp (lam * (a - xj)) - 1) ^ 2 :=
      sq_pos_of_ne_zero hden_pos.ne'
    have htail_neg : dTail < 0 := by
      dsimp [dTail]
      exact div_neg_of_neg_of_pos hnum_neg hden_sq_pos
    linarith

/--
Appendix C, Theorem 7 final scalar bound in the right truncation case:
`3(e^z - 1) > 2z` for `z > 0`.
-/
theorem paper_theorem7_three_mul_exp_sub_one_gt_two_mul
    {z : ℝ} (hz : 0 < z) :
    2 * z < 3 * (Real.exp z - 1) := by
  have hexp : 1 + z < Real.exp z := by
    simpa [add_comm] using Real.add_one_lt_exp (show z ≠ 0 by linarith)
  have hgap : z < Real.exp z - 1 := by
    linarith
  nlinarith

/-- Auxiliary scalar expression used in Appendix C, Theorem 7, case 3. -/
noncomputable def theorem7LaplacianCase3EndpointAux (z : ℝ) : ℝ := z + 2 * Real.exp (-z) + z * Real.exp (-z)

/-- Derivative of the Theorem 7 case-3 endpoint auxiliary expression. -/
theorem theorem7LaplacianCase3EndpointAux_hasDerivAt (z : ℝ) :
    HasDerivAt theorem7LaplacianCase3EndpointAux
      (1 - (1 + z) * Real.exp (-z)) z := by
  have hnegexp :
      HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-z)) z := by
    have hneg : HasDerivAt (fun z : ℝ => -z) (-1 : ℝ) z := by
      simpa using (hasDerivAt_id z).neg
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-z)).comp z hneg
  have hmain :
      HasDerivAt
        (fun z : ℝ => z + 2 * Real.exp (-z) + z * Real.exp (-z))
        (1 + 2 * (-Real.exp (-z)) +
          (1 * Real.exp (-z) + z * (-Real.exp (-z)))) z :=
    ((hasDerivAt_id z).add (hnegexp.const_mul 2)).add
      ((hasDerivAt_id z).mul hnegexp)
  unfold theorem7LaplacianCase3EndpointAux
  convert hmain using 1
  ring

/--
Appendix C, Theorem 7 scalar endpoint bound used in case 3:
`z + 2e^{-z} + z e^{-z} > 2` for `z > 0`.
-/
theorem paper_theorem7_case3_endpoint_aux_gt_two
    {z : ℝ} (hz : 0 < z) :
    2 < theorem7LaplacianCase3EndpointAux z := by
  have hcont :
      ContinuousOn theorem7LaplacianCase3EndpointAux (Set.Ici (0 : ℝ)) := by
    intro x hx
    exact (theorem7LaplacianCase3EndpointAux_hasDerivAt x).continuousAt.continuousWithinAt
  have hstrict :
      StrictMonoOn theorem7LaplacianCase3EndpointAux (Set.Ici (0 : ℝ)) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos
      (D := Set.Ici (0 : ℝ))
      (f := theorem7LaplacianCase3EndpointAux)
      (f' := fun x => 1 - (1 + x) * Real.exp (-x))
      (convex_Ici (0 : ℝ)) hcont ?_ ?_
    · intro x hx
      exact (theorem7LaplacianCase3EndpointAux_hasDerivAt x).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      have hexp : 1 + x < Real.exp x := by
        simpa [add_comm] using Real.add_one_lt_exp (show x ≠ 0 by linarith)
      have hmul :
          (1 + x) * Real.exp (-x) < Real.exp x * Real.exp (-x) :=
        mul_lt_mul_of_pos_right hexp (Real.exp_pos (-x))
      have hright : Real.exp x * Real.exp (-x) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
      linarith
  have hlt := hstrict (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ))
    (le_of_lt hz) hz
  simpa [theorem7LaplacianCase3EndpointAux] using hlt

/--
Appendix C, Theorem 7, case 3 polynomial derivative numerator after the
substitution `r = exp(-λ(a-x_i))` and `s = exp(-λ(x_i-x_j))`.  The proof follows
the paper's endpoint bounds and convex interpolation in the remaining `r`
coordinate.
-/
theorem paper_theorem7_laplacian_case3_derivative_poly_core
    {z r : ℝ} (hz : 0 < z) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r ^ 2 * (1 - Real.exp (-z)) +
        r * (2 * Real.exp (-z) * z + 4 * Real.exp (-z) - 4) +
        (4 - 2 * Real.exp (-z) * z - 4 * Real.exp (-z) - 2 * z) < 0 := by
  let s : ℝ := Real.exp (-z)
  let B : ℝ :=
    r ^ 2 * (1 - s) + r * (2 * s * z + 4 * s - 4) +
      (4 - 2 * s * z - 4 * s - 2 * z)
  let B0 : ℝ := 4 - 2 * s * z - 4 * s - 2 * z
  let B1 : ℝ := 1 - s - 2 * z
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.exp_pos _
  have hs_lt_one : s < 1 := by
    dsimp [s]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hB0 : B0 < 0 := by
    have haux := paper_theorem7_case3_endpoint_aux_gt_two hz
    dsimp [theorem7LaplacianCase3EndpointAux] at haux
    dsimp [B0, s]
    nlinarith
  have hB1 : B1 < 0 := by
    have haux := paper_theorem7_exp_neg_gt_one_sub_two_mul hz
    dsimp [B1, s]
    nlinarith
  have hinterp :
      B ≤ (1 - r) * B0 + r * B1 := by
    have hdiff :
        ((1 - r) * B0 + r * B1) - B = (1 - s) * r * (1 - r) := by
      dsimp [B, B0, B1]
      ring
    have hnonneg : 0 ≤ (1 - s) * r * (1 - r) :=
      mul_nonneg (mul_nonneg (by linarith) hr0) (by linarith)
    linarith
  have hcombo : (1 - r) * B0 + r * B1 < 0 := by
    by_cases hr_zero : r = 0
    · subst r
      simpa using hB0
    · by_cases hr_one : r = 1
      · subst r
        simpa using hB1
      · have hr_pos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr_zero)
        have h1r_pos : 0 < 1 - r := sub_pos.mpr (lt_of_le_of_ne hr1 hr_one)
        have hleft : (1 - r) * B0 < 0 := mul_neg_of_pos_of_neg h1r_pos hB0
        have hright : r * B1 < 0 := mul_neg_of_pos_of_neg hr_pos hB1
        linarith
  dsimp [B, s] at hinterp
  exact lt_of_le_of_lt hinterp hcombo

/-- Numerator of the Appendix C, Theorem 7 case-3 closed-form probability. -/
noncomputable def theorem7LaplacianCase3Numerator (z r : ℝ) : ℝ := 8 - (4 + 2 * z) * Real.exp (-z) - 4 * r + Real.exp (-z) * r ^ 2

/-- Denominator of the Appendix C, Theorem 7 case-3 closed-form probability. -/
noncomputable def theorem7LaplacianCase3Denominator (z r : ℝ) : ℝ := 4 - 2 * r - 2 * r * Real.exp (-z) + Real.exp (-z) * r ^ 2

/--
Appendix C, Theorem 7, case 3 closed-form conditional probability after the
substitution `z = λ(x_i-x_j)` and `r = exp(-λ(a-x_i))`.
-/
noncomputable def theorem7LaplacianCase3Ratio (z r : ℝ) : ℝ :=
  theorem7LaplacianCase3Numerator z r /
    theorem7LaplacianCase3Denominator z r

/-- Case-3 denominator positivity on the paper's domain `z > 0`, `0 ≤ r ≤ 1`. -/
theorem theorem7LaplacianCase3Denominator_pos
    {z r : ℝ} (hz : 0 < z) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 < theorem7LaplacianCase3Denominator z r := by
  let s : ℝ := Real.exp (-z)
  have hs_le_one : s ≤ 1 := by
    dsimp [s]
    exact le_of_lt (Real.exp_lt_one_iff.mpr (by linarith))
  have h2r : 0 ≤ 2 - r := by linarith
  have hdiff :
      theorem7LaplacianCase3Denominator z r - (2 - r) ^ 2 =
        (1 - s) * r * (2 - r) := by
    dsimp [theorem7LaplacianCase3Denominator, s]
    ring
  have hnonneg : 0 ≤ (1 - s) * r * (2 - r) :=
    mul_nonneg (mul_nonneg (by linarith) hr0) h2r
  have hbase : 0 < (2 - r) ^ 2 := by
    have hpos : 0 < 2 - r := by linarith
    exact sq_pos_of_pos hpos
  nlinarith

/-- Derivative of the Appendix C, Theorem 7 case-3 ratio with respect to `r`. -/
theorem theorem7LaplacianCase3Ratio_hasDerivAt
    {z r : ℝ} (hden : theorem7LaplacianCase3Denominator z r ≠ 0) :
    HasDerivAt
      (fun r => theorem7LaplacianCase3Ratio z r)
      (((-4 + 2 * Real.exp (-z) * r) *
            theorem7LaplacianCase3Denominator z r -
          theorem7LaplacianCase3Numerator z r *
            (-2 - 2 * Real.exp (-z) + 2 * Real.exp (-z) * r)) /
        theorem7LaplacianCase3Denominator z r ^ 2)
      r := by
  have hnum :
      HasDerivAt
        (fun r => theorem7LaplacianCase3Numerator z r)
        (-4 + 2 * Real.exp (-z) * r) r := by
    have hsq :
        HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
      simpa [pow_two, two_mul] using (hasDerivAt_id r).mul (hasDerivAt_id r)
    unfold theorem7LaplacianCase3Numerator
    convert
      ((((hasDerivAt_const r (8 : ℝ)).sub
          ((hasDerivAt_const r ((4 + 2 * z) * Real.exp (-z))))).sub
          ((hasDerivAt_id r).const_mul 4)).add
          (hsq.const_mul (Real.exp (-z)))) using 1
    · ring
  have hden' :
      HasDerivAt
        (fun r => theorem7LaplacianCase3Denominator z r)
        (-2 - 2 * Real.exp (-z) + 2 * Real.exp (-z) * r) r := by
    have hsq :
        HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
      simpa [pow_two, two_mul] using (hasDerivAt_id r).mul (hasDerivAt_id r)
    unfold theorem7LaplacianCase3Denominator
    convert
      ((((hasDerivAt_const r (4 : ℝ)).sub
          ((hasDerivAt_id r).const_mul 2)).sub
          ((hasDerivAt_id r).const_mul (2 * Real.exp (-z)))).add
          (hsq.const_mul (Real.exp (-z)))) using 1
    · ext y
      simp
      ring
    · ring
  unfold theorem7LaplacianCase3Ratio
  simpa using hnum.div hden' hden

/--
Appendix C, Theorem 7, case 3: the closed-form ratio is strictly decreasing in
`r` on the paper's domain.
-/
theorem theorem7LaplacianCase3Ratio_hasDerivAt_neg
    {z r : ℝ} (hz : 0 < z) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ d,
      HasDerivAt (fun r => theorem7LaplacianCase3Ratio z r) d r ∧
        d < 0 := by
  have hden_pos := theorem7LaplacianCase3Denominator_pos hz hr0 hr1
  let d :=
    (((-4 + 2 * Real.exp (-z) * r) *
          theorem7LaplacianCase3Denominator z r -
        theorem7LaplacianCase3Numerator z r *
          (-2 - 2 * Real.exp (-z) + 2 * Real.exp (-z) * r)) /
      theorem7LaplacianCase3Denominator z r ^ 2)
  refine ⟨d, theorem7LaplacianCase3Ratio_hasDerivAt hden_pos.ne', ?_⟩
  have hpoly :=
    paper_theorem7_laplacian_case3_derivative_poly_core hz hr0 hr1
  have hnum_eq :
      (-4 + 2 * Real.exp (-z) * r) *
          theorem7LaplacianCase3Denominator z r -
        theorem7LaplacianCase3Numerator z r *
          (-2 - 2 * Real.exp (-z) + 2 * Real.exp (-z) * r) =
        2 * Real.exp (-z) *
          (r ^ 2 * (1 - Real.exp (-z)) +
            r * (2 * Real.exp (-z) * z + 4 * Real.exp (-z) - 4) +
            (4 - 2 * Real.exp (-z) * z - 4 * Real.exp (-z) - 2 * z)) := by
    dsimp [theorem7LaplacianCase3Numerator,
      theorem7LaplacianCase3Denominator]
    ring
  have hnum_neg :
      (-4 + 2 * Real.exp (-z) * r) *
          theorem7LaplacianCase3Denominator z r -
        theorem7LaplacianCase3Numerator z r *
          (-2 - 2 * Real.exp (-z) + 2 * Real.exp (-z) * r) < 0 := by
    rw [hnum_eq]
    exact mul_neg_of_pos_of_neg
      (mul_pos zero_lt_two (Real.exp_pos _)) hpoly
  have hden_sq_pos :
      0 < theorem7LaplacianCase3Denominator z r ^ 2 :=
    sq_pos_of_ne_zero hden_pos.ne'
  dsimp [d]
  exact div_neg_of_neg_of_pos hnum_neg hden_sq_pos

/-- The Appendix C case-3 ratio is continuous on its scalar domain. -/
theorem theorem7LaplacianCase3Ratio_continuousAt
    {z r : ℝ} (hz : 0 < z) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ContinuousAt (fun r => theorem7LaplacianCase3Ratio z r) r := by
  obtain ⟨d, hd, _⟩ :=
    theorem7LaplacianCase3Ratio_hasDerivAt_neg
      (z := z) (r := r) hz hr0 hr1
  exact hd.continuousAt

/--
Appendix C, Theorem 7, case 3 endpoint comparison: every positive right-tail
parameter `r` gives a strictly smaller conditional ratio than the `r = 0`
unconditional endpoint.
-/
theorem theorem7LaplacianCase3Ratio_lt_endpoint_zero
    {z r : ℝ} (hz : 0 < z) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    theorem7LaplacianCase3Ratio z r <
      theorem7LaplacianCase3Ratio z 0 := by
  have hden_r_pos :
      0 < theorem7LaplacianCase3Denominator z r :=
    theorem7LaplacianCase3Denominator_pos hz (le_of_lt hr0) hr1
  have hden_0_pos :
      0 < theorem7LaplacianCase3Denominator z 0 :=
    theorem7LaplacianCase3Denominator_pos hz le_rfl zero_le_one
  unfold theorem7LaplacianCase3Ratio
  rw [div_lt_div_iff₀ hden_r_pos hden_0_pos]
  let s : ℝ := Real.exp (-z)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.exp_pos _
  have haux := paper_theorem7_case3_endpoint_aux_gt_two hz
  have hA : 0 < z - 2 + (2 + z) * s := by
    dsimp [theorem7LaplacianCase3EndpointAux, s] at haux
    linarith
  have hB : 0 < 2 - (2 + z) * s := by
    have hhalf : 1 + z / 2 < Real.exp z := by
      have hzhalf : z / 2 ≠ 0 := by
        positivity
      have hsmall : 1 + z / 2 < Real.exp (z / 2) := by
        simpa [add_comm] using Real.add_one_lt_exp hzhalf
      have hlt : z / 2 < z := by linarith
      exact hsmall.trans (Real.exp_lt_exp.mpr hlt)
    have hscaled : 2 + z < 2 * Real.exp z := by
      nlinarith
    have hmul := mul_lt_mul_of_pos_right hscaled hs_pos
    have hexp : Real.exp z * s = 1 := by
      dsimp [s]
      rw [← Real.exp_add]
      ring_nf
      simp
    nlinarith
  have hbracket : 0 < 2 * (z - 2 + (2 + z) * s) +
      r * (2 - (2 + z) * s) := by
    nlinarith [hA, hB, hr0]
  have hdiff :
      theorem7LaplacianCase3Numerator z 0 *
          theorem7LaplacianCase3Denominator z r -
        theorem7LaplacianCase3Numerator z r *
          theorem7LaplacianCase3Denominator z 0 =
        2 * s * r *
          (2 * (z - 2 + (2 + z) * s) +
            r * (2 - (2 + z) * s)) := by
    dsimp [theorem7LaplacianCase3Numerator,
      theorem7LaplacianCase3Denominator, s]
    ring
  have hdiff_pos :
      0 <
        theorem7LaplacianCase3Numerator z 0 *
            theorem7LaplacianCase3Denominator z r -
          theorem7LaplacianCase3Numerator z r *
            theorem7LaplacianCase3Denominator z 0 := by
    rw [hdiff]
    positivity
  nlinarith

/-- Closed form for the `r = 0` endpoint of the Appendix C case-3 ratio. -/
theorem theorem7LaplacianCase3Endpoint_eq_closedForm (z : ℝ) :
    (1 / 2 : ℝ) * theorem7LaplacianCase3Ratio z 0 =
      1 - (1 / 2 + z / 4) * Real.exp (-z) := by
  unfold theorem7LaplacianCase3Ratio
    theorem7LaplacianCase3Numerator theorem7LaplacianCase3Denominator
  ring

/-- The unconditional case-3 endpoint is strictly above one half when `z > 0`. -/
theorem theorem7LaplacianCase3Endpoint_gt_half
    {z : ℝ} (hz : 0 < z) :
    (1 / 2 : ℝ) <
      (1 / 2 : ℝ) * theorem7LaplacianCase3Ratio z 0 := by
  rw [theorem7LaplacianCase3Endpoint_eq_closedForm z]
  let s : ℝ := Real.exp (-z)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.exp_pos _
  have hbase : 1 + z / 2 < Real.exp z := by
    have hzhalf : z / 2 ≠ 0 := by positivity
    have hsmall : 1 + z / 2 < Real.exp (z / 2) := by
      simpa [add_comm] using Real.add_one_lt_exp hzhalf
    have hlt : z / 2 < z := by linarith
    exact hsmall.trans (Real.exp_lt_exp.mpr hlt)
  have hmul := mul_lt_mul_of_pos_right hbase hs_pos
  have hexp : Real.exp z * s = 1 := by
    dsimp [s]
    rw [← Real.exp_add]
    ring_nf
    simp
  nlinarith

/-- The unconditional case-3 endpoint is strictly below one when `z > 0`. -/
theorem theorem7LaplacianCase3Endpoint_lt_one
    {z : ℝ} (hz : 0 < z) :
    (1 / 2 : ℝ) * theorem7LaplacianCase3Ratio z 0 < 1 := by
  rw [theorem7LaplacianCase3Endpoint_eq_closedForm z]
  have hcoef : 0 < (1 / 2 : ℝ) + z / 4 := by positivity
  have hexp : 0 < Real.exp (-z) := Real.exp_pos _
  nlinarith [mul_pos hcoef hexp]

/--
Derivative of the complement term in the closed-form unconditional case-3
endpoint.
-/
theorem theorem7LaplacianCase3EndpointComplement_hasDerivAt (z : ℝ) :
    HasDerivAt
      (fun z : ℝ => ((1 / 2 : ℝ) + z / 4) * Real.exp (-z))
      (-(1 + z) / 4 * Real.exp (-z)) z := by
  have hlin :
      HasDerivAt (fun z : ℝ => (1 / 2 : ℝ) + z / 4)
        (1 / 4 : ℝ) z := by
    convert (hasDerivAt_const z (1 / 2 : ℝ)).add
      ((hasDerivAt_id z).div_const 4) using 1
    ring
  have hneg : HasDerivAt (fun z : ℝ => -z) (-1 : ℝ) z := by
    simpa using (hasDerivAt_id z).neg
  have hexp :
      HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-z)) z := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-z)).comp z hneg
  convert hlin.mul hexp using 1
  ring

/--
The unconditional Laplacian pairwise winner endpoint is strictly increasing in
the positive score gap.
-/
theorem theorem7LaplacianCase3Endpoint_strictMono_pos
    {z1 z2 : ℝ} (hz1 : 0 < z1) (hzlt : z1 < z2) :
    (1 / 2 : ℝ) * theorem7LaplacianCase3Ratio z1 0 <
      (1 / 2 : ℝ) * theorem7LaplacianCase3Ratio z2 0 := by
  let G : ℝ → ℝ := fun z => ((1 / 2 : ℝ) + z / 4) * Real.exp (-z)
  have hclosed :
      ∀ z, (1 / 2 : ℝ) * theorem7LaplacianCase3Ratio z 0 = 1 - G z := by
    intro z
    dsimp [G]
    rw [theorem7LaplacianCase3Endpoint_eq_closedForm z]
  have hderG :
      ∀ x, HasDerivAt G (-(1 + x) / 4 * Real.exp (-x)) x := by
    intro x
    simpa [G] using
      theorem7LaplacianCase3EndpointComplement_hasDerivAt x
  have hcont : ContinuousOn G (Set.Ici (0 : ℝ)) := by
    intro x _hx
    exact (hderG x).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn G (Set.Ici (0 : ℝ)) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg
      (D := Set.Ici (0 : ℝ)) (f := G)
      (f' := fun x => -(1 + x) / 4 * Real.exp (-x))
      (convex_Ici (0 : ℝ)) hcont ?_ ?_
    · intro x _hx
      exact (hderG x).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      have hpos : 0 < (1 + x) / 4 := by positivity
      have hexp : 0 < Real.exp (-x) := Real.exp_pos _
      nlinarith [mul_pos hpos hexp]
  have h1mem : z1 ∈ Set.Ici (0 : ℝ) := le_of_lt hz1
  have h2mem : z2 ∈ Set.Ici (0 : ℝ) := le_of_lt (lt_trans hz1 hzlt)
  have hg : G z2 < G z1 := hanti h1mem h2mem hzlt
  rw [hclosed z1, hclosed z2]
  linarith

/--
At the middle/right split point, the Appendix C case-2 conditional probability
is strictly below the unconditional case-3 endpoint.
-/
theorem theorem7LaplacianCase2Endpoint_lt_case3_endpoint
    {z : ℝ} (hz : 0 < z) :
    1 - (1 / 2 + z) / (2 * Real.exp z - 1) <
      (1 / 2 : ℝ) * theorem7LaplacianCase3Ratio z 0 := by
  rw [theorem7LaplacianCase3Endpoint_eq_closedForm z]
  have hden_pos : 0 < 2 * Real.exp z - 1 := by
    have hexp_gt : 1 < Real.exp z := Real.one_lt_exp_iff.mpr hz
    nlinarith
  let s : ℝ := Real.exp (-z)
  have haux := paper_theorem7_case3_endpoint_aux_gt_two hz
  have hcore : 0 < 2 * z - 2 + (2 + z) * s := by
    have hA : 0 < z - 2 + (2 + z) * s := by
      dsimp [theorem7LaplacianCase3EndpointAux, s] at haux
      linarith
    nlinarith
  have htail :
      (1 / 2 + z / 4) * s <
        (1 / 2 + z) / (2 * Real.exp z - 1) := by
    rw [lt_div_iff₀ hden_pos]
    have hexp : Real.exp z * s = 1 := by
      dsimp [s]
      rw [← Real.exp_add]
      ring_nf
      simp
    nlinarith
  nlinarith

/--
Appendix C, Theorem 7, middle region: the closed-form conditional probability
is monotone in the cutoff once the cutoff is above `x_j`.
-/
theorem theorem7LaplacianCase2ConditionalProb_mono
    {lam xj a b : ℝ} (hlam : 0 < lam) (ha : xj < a) (hab : a ≤ b) :
    1 - theorem7LaplacianCase2TailRatio lam xj a ≤
      1 - theorem7LaplacianCase2TailRatio lam xj b := by
  let G : ℝ → ℝ := fun u => 1 - theorem7LaplacianCase2TailRatio lam xj u
  have hcont : ContinuousOn G (Set.Icc a b) := by
    intro u hu
    have hu_pos : 0 < u - xj := sub_pos.mpr (ha.trans_le hu.1)
    obtain ⟨d, hd, _⟩ :=
      theorem7LaplacianCase2ConditionalProb_hasDerivAt_pos
        (lam := lam) (xj := xj) (a := u) hlam hu_pos
    have hc : ContinuousAt G u := by
      simpa [G] using hd.continuousAt
    exact hc.continuousWithinAt
  have hderiv :
      ∀ u ∈ Set.Ioo a b, HasDerivAt G (deriv G u) u := by
    intro u hu
    have hu_pos : 0 < u - xj := sub_pos.mpr (ha.trans hu.1)
    obtain ⟨d, hd, _⟩ :=
      theorem7LaplacianCase2ConditionalProb_hasDerivAt_pos
        (lam := lam) (xj := xj) (a := u) hlam hu_pos
    have hdG : HasDerivAt G d u := by simpa [G] using hd
    simpa [hdG.deriv] using hdG
  have hnonneg :
      ∀ u ∈ Set.Ioo a b, 0 ≤ deriv G u := by
    intro u hu
    have hu_pos : 0 < u - xj := sub_pos.mpr (ha.trans hu.1)
    obtain ⟨d, hd, hdpos⟩ :=
      theorem7LaplacianCase2ConditionalProb_hasDerivAt_pos
        (lam := lam) (xj := xj) (a := u) hlam hu_pos
    have hdG : HasDerivAt G d u := by simpa [G] using hd
    rw [hdG.deriv]
    exact le_of_lt hdpos
  exact AppliedModelingLib.Optimization.endpoint_path_le_of_hasDerivAt_nonneg_on_Icc
    (f := G) (f' := deriv G) hab hcont hderiv hnonneg

/--
Appendix C, Theorem 7, case 3 closed-form conditional probability in the
original `a` coordinate.
-/
noncomputable def theorem7LaplacianCase3ConditionalProb
    (lam xi xj a : ℝ) : ℝ :=
  theorem7LaplacianCase3Ratio
    (lam * (xi - xj))
    (Real.exp (-lam * (a - xi)))

/--
Appendix C, Theorem 7, case `a > x_i`: the derivative of the closed-form
conditional probability is strictly positive.
-/
theorem theorem7LaplacianCase3ConditionalProb_hasDerivAt_pos
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi < a) :
    ∃ d,
      HasDerivAt
        (fun a => theorem7LaplacianCase3ConditionalProb lam xi xj a) d a ∧
        0 < d := by
  let z : ℝ := lam * (xi - xj)
  let r : ℝ := Real.exp (-lam * (a - xi))
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos hlam (sub_pos.mpr hx)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact le_of_lt (Real.exp_pos _)
  have hr1 : r ≤ 1 := by
    dsimp [r]
    have hneg : -lam * (a - xi) < 0 := by
      have hpos : 0 < lam * (a - xi) := mul_pos hlam (sub_pos.mpr ha)
      linarith
    exact le_of_lt (Real.exp_lt_one_iff.mpr hneg)
  obtain ⟨dRatio, hratio, hdRatio⟩ :=
    theorem7LaplacianCase3Ratio_hasDerivAt_neg
      (z := z) (r := r) hz hr0 hr1
  have hinner :
      HasDerivAt
        (fun a : ℝ => Real.exp (-lam * (a - xi)))
        (Real.exp (-lam * (a - xi)) * (-lam)) a := by
    have hlin : HasDerivAt (fun a : ℝ => -lam * (a - xi)) (-lam) a := by
      simpa using ((hasDerivAt_id a).sub_const xi).const_mul (-lam)
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-lam * (a - xi))).comp a hlin
  refine ⟨dRatio * (Real.exp (-lam * (a - xi)) * (-lam)), ?_, ?_⟩
  · dsimp [theorem7LaplacianCase3ConditionalProb, z, r] at hratio ⊢
    exact hratio.comp a hinner
  · have hinner_neg : Real.exp (-lam * (a - xi)) * (-lam) < 0 :=
      mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith)
    exact mul_pos_of_neg_of_neg hdRatio hinner_neg

/-- Appendix C, Theorem 7, case `a ≤ x_j`: the closed form is constant. -/
theorem theorem7LaplacianCase1ConditionalProb_hasDerivAt_nonneg (a : ℝ) :
    HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 a ∧ 0 ≤ (0 : ℝ) := ⟨hasDerivAt_const a (1 / 2 : ℝ), le_rfl⟩

/--
Appendix C, Theorem 7 for the paper's three Laplacian closed-form cases.

Lean states the result at the closed-form layer obtained after the integrations
in the paper: case 1 is constant, case 2 is
`1 - (1/2 + λ(a-x_j))/(2 exp(λ(a-x_j))-1)`, and case 3 is the right-tail
ratio after the substitutions `z = λ(x_i-x_j)` and
`r = exp(-λ(a-x_i))`.
-/
theorem paper_theorem7_laplacian_closedForm_derivative_cases
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (a ≤ xj →
      HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 a ∧ 0 ≤ (0 : ℝ)) ∧
    (xj < a → a ≤ xi →
      ∃ d,
        HasDerivAt
          (fun a => 1 - theorem7LaplacianCase2TailRatio lam xj a) d a ∧
          0 < d) ∧
    (xi < a →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianCase3ConditionalProb lam xi xj a) d a ∧
          0 < d) ∧
    (∃ a d,
      xj < a ∧ a < xi ∧
        HasDerivAt
          (fun a => 1 - theorem7LaplacianCase2TailRatio lam xj a) d a ∧
        0 < d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ha
    exact theorem7LaplacianCase1ConditionalProb_hasDerivAt_nonneg a
  · intro hleft _hright
    exact theorem7LaplacianCase2ConditionalProb_hasDerivAt_pos
      (lam := lam) (xj := xj) (a := a) hlam (sub_pos.mpr hleft)
  · intro hright
    exact theorem7LaplacianCase3ConditionalProb_hasDerivAt_pos
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx hright
  · let amid : ℝ := (xj + xi) / 2
    have hleft : xj < amid := by
      dsimp [amid]
      linarith
    have hright : amid < xi := by
      dsimp [amid]
      linarith
    obtain ⟨d, hd, hdpos⟩ :=
      theorem7LaplacianCase2ConditionalProb_hasDerivAt_pos
        (lam := lam) (xj := xj) (a := amid) hlam (sub_pos.mpr hleft)
    exact ⟨amid, d, hleft, hright, hd, hdpos⟩

/-
The next lemmas are the elementary integration identities used to connect the
paper's Laplace pdf/cdf integrals to the closed forms above.
-/

/-- Appendix C, Theorem 7: improper integral of an affine exponential. -/
theorem paper_theorem7_integral_exp_affine_Iic
    {k β c : ℝ} (hk : 0 < k) :
    ∫ x : ℝ in Set.Iic c, Real.exp (β + k * x) =
      Real.exp (β + k * c) / k := by
  calc
    ∫ x : ℝ in Set.Iic c, Real.exp (β + k * x) =
        ∫ x : ℝ in Set.Iic c, Real.exp β * Real.exp (k * x) := by
      refine setIntegral_congr_fun measurableSet_Iic fun x _hx => ?_
      rw [Real.exp_add]
    _ = Real.exp β * ∫ x : ℝ in Set.Iic c, Real.exp (k * x) := by
      rw [integral_const_mul]
    _ = Real.exp β * (Real.exp (k * c) / k) := by
      rw [integral_exp_mul_Iic hk]
    _ = Real.exp (β + k * c) / k := by
      rw [Real.exp_add]
      ring

/-- Appendix C, Theorem 7: finite-interval integral of an affine exponential. -/
theorem paper_theorem7_intervalIntegral_exp_affine
    {k β l u : ℝ} (hk : k ≠ 0) :
    ∫ x in l..u, Real.exp (β + k * x) =
      (Real.exp (β + k * u) - Real.exp (β + k * l)) / k := by
  calc
    ∫ x in l..u, Real.exp (β + k * x) =
        ∫ x in l..u, Real.exp β * Real.exp (k * x) := by
      refine intervalIntegral.integral_congr fun x _hx => ?_
      rw [Real.exp_add]
    _ = Real.exp β * ∫ x in l..u, Real.exp (k * x) := by
      rw [intervalIntegral.integral_const_mul]
    _ = Real.exp β * (k⁻¹ * ∫ y in k * l..k * u, Real.exp y) := by
      rw [intervalIntegral.integral_comp_mul_left (f := Real.exp) (a := l) (b := u)
        (c := k) hk]
      rfl
    _ = Real.exp β * (k⁻¹ * (Real.exp (k * u) - Real.exp (k * l))) := by
      rw [integral_exp]
    _ = (Real.exp (β + k * u) - Real.exp (β + k * l)) / k := by
      rw [Real.exp_add, Real.exp_add]
      field_simp [hk]

/-- The Laplace pdf used in Appendix C, Theorem 7. -/
noncomputable def theorem7LaplacePDF (lam μ x : ℝ) : ℝ := lam / 2 * Real.exp (-lam * |x - μ|)

/-- The paper's closed-form Laplace CDF. -/
noncomputable def theorem7LaplaceCDFClosedForm (lam μ a : ℝ) : ℝ :=
  if a < μ then
    (1 / 2) * Real.exp (-lam * (μ - a))
  else
    1 - (1 / 2) * Real.exp (-lam * (a - μ))

/-- Appendix C, Theorem 7: the Laplace pdf below its mean. -/
theorem theorem7LaplacePDF_of_le_mean
    {lam μ x : ℝ} (hx : x ≤ μ) :
    theorem7LaplacePDF lam μ x =
      lam / 2 * Real.exp (-lam * (μ - x)) := by
  have habs : |x - μ| = μ - x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hx)]
    ring
  simp [theorem7LaplacePDF, habs]

/-- Appendix C, Theorem 7: the Laplace pdf above its mean. -/
theorem theorem7LaplacePDF_of_mean_le
    {lam μ x : ℝ} (hx : μ ≤ x) :
    theorem7LaplacePDF lam μ x =
      lam / 2 * Real.exp (-lam * (x - μ)) := by
  have habs : |x - μ| = x - μ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx)]
  simp [theorem7LaplacePDF, habs]

/-- Appendix C, Theorem 7: continuity of the paper Laplace density. -/
theorem theorem7LaplacePDF_continuous (lam μ : ℝ) :
    Continuous fun x : ℝ => theorem7LaplacePDF lam μ x := by
  unfold theorem7LaplacePDF
  exact continuous_const.mul
    (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_id.sub continuous_const).abs)))

/--
Appendix C, Theorem 7: the paper Laplace density is integrable on left
half-lines that end at or below the mean.
-/
theorem theorem7LaplacePDF_integrableOn_Iic_of_le_mean
    {lam μ a : ℝ} (hlam : 0 < lam) (ha : a ≤ μ) :
    IntegrableOn (fun x : ℝ => theorem7LaplacePDF lam μ x) (Set.Iic a) := by
  have hexp :
      IntegrableOn
        (fun x : ℝ => Real.exp ((-lam * μ) + lam * x))
        (Set.Iic a) := by
    have hbase := integrableOn_exp_mul_Iic (a := lam) hlam a
    have hmul := hbase.const_mul (Real.exp (-lam * μ))
    refine IntegrableOn.congr_fun hmul ?_ measurableSet_Iic
    intro x _hx
    change Real.exp (-lam * μ) * Real.exp (lam * x) =
      Real.exp (-lam * μ + lam * x)
    rw [← Real.exp_add]
  have hscaled := hexp.const_mul (lam / 2)
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Iic
  intro x hx
  have hxμ : x ≤ μ := le_trans hx ha
  change lam / 2 * Real.exp (-lam * μ + lam * x) =
    theorem7LaplacePDF lam μ x
  rw [theorem7LaplacePDF_of_le_mean hxμ]
  have harg : -lam * (μ - x) = (-lam * μ) + lam * x := by ring
  rw [harg]

/--
Appendix C, Theorem 7: the paper Laplace density is integrable on every left
half-line.
-/
theorem theorem7LaplacePDF_integrableOn_Iic
    {lam μ a : ℝ} (hlam : 0 < lam) :
    IntegrableOn (fun x : ℝ => theorem7LaplacePDF lam μ x) (Set.Iic a) := by
  by_cases ha : a ≤ μ
  · exact theorem7LaplacePDF_integrableOn_Iic_of_le_mean
      (lam := lam) (μ := μ) (a := a) hlam ha
  · have hμa : μ ≤ a := le_of_not_ge ha
    have hleft :
        IntegrableOn
          (fun x : ℝ => theorem7LaplacePDF lam μ x)
          (Set.Iic μ) :=
      theorem7LaplacePDF_integrableOn_Iic_of_le_mean
        (lam := lam) (μ := μ) (a := μ) hlam le_rfl
    have hright :
        IntegrableOn
          (fun x : ℝ => theorem7LaplacePDF lam μ x)
          (Set.Ioc μ a) := by
      have hcompact :
          IntegrableOn
            (fun x : ℝ => theorem7LaplacePDF lam μ x)
            (Set.Icc μ a) :=
        (theorem7LaplacePDF_continuous lam μ).integrableOn_Icc
      exact hcompact.mono_set Set.Ioc_subset_Icc_self
    have hunion : Set.Iic a = Set.Iic μ ∪ Set.Ioc μ a := by
      exact (Set.Iic_union_Ioc_eq_Iic hμa).symm
    rw [hunion]
    exact hleft.union hright

/--
Appendix C, Theorem 7: the low-tail Laplace CDF integral, matching the paper's
`x < μ` CDF branch.
-/
theorem theorem7LaplaceCDFIntegral_of_lt_mean
    {lam μ a : ℝ} (hlam : 0 < lam) (ha : a < μ) :
    ∫ x : ℝ in Set.Iic a, theorem7LaplacePDF lam μ x =
      (1 / 2) * Real.exp (-lam * (μ - a)) := by
  calc
    ∫ x : ℝ in Set.Iic a, theorem7LaplacePDF lam μ x =
        ∫ x : ℝ in Set.Iic a,
          lam / 2 * Real.exp ((-lam * μ) + lam * x) := by
      refine setIntegral_congr_fun measurableSet_Iic fun x hx => ?_
      have hxμ : x ≤ μ := le_trans hx (le_of_lt ha)
      rw [theorem7LaplacePDF_of_le_mean hxμ]
      have harg : -lam * (μ - x) = (-lam * μ) + lam * x := by ring
      rw [harg]
    _ = lam / 2 *
        ∫ x : ℝ in Set.Iic a, Real.exp ((-lam * μ) + lam * x) := by
      rw [integral_const_mul]
    _ = lam / 2 * (Real.exp ((-lam * μ) + lam * a) / lam) := by
      rw [paper_theorem7_integral_exp_affine_Iic
        (k := lam) (β := -lam * μ) (c := a) hlam]
    _ = (1 / 2) * Real.exp (-lam * (μ - a)) := by
      have harg : (-lam * μ) + lam * a = -lam * (μ - a) := by ring
      rw [harg]
      field_simp [hlam.ne']

/--
Appendix C, Theorem 7: the low-tail Laplace CDF integral, including the
endpoint at the mean.
-/
theorem theorem7LaplaceCDFIntegral_of_le_mean
    {lam μ a : ℝ} (hlam : 0 < lam) (ha : a ≤ μ) :
    ∫ x : ℝ in Set.Iic a, theorem7LaplacePDF lam μ x =
      (1 / 2) * Real.exp (-lam * (μ - a)) := by
  calc
    ∫ x : ℝ in Set.Iic a, theorem7LaplacePDF lam μ x =
        ∫ x : ℝ in Set.Iic a,
          lam / 2 * Real.exp ((-lam * μ) + lam * x) := by
      refine setIntegral_congr_fun measurableSet_Iic fun x hx => ?_
      have hxμ : x ≤ μ := le_trans hx ha
      rw [theorem7LaplacePDF_of_le_mean hxμ]
      have harg : -lam * (μ - x) = (-lam * μ) + lam * x := by ring
      rw [harg]
    _ = lam / 2 *
        ∫ x : ℝ in Set.Iic a, Real.exp ((-lam * μ) + lam * x) := by
      rw [integral_const_mul]
    _ = lam / 2 * (Real.exp ((-lam * μ) + lam * a) / lam) := by
      rw [paper_theorem7_integral_exp_affine_Iic
        (k := lam) (β := -lam * μ) (c := a) hlam]
    _ = (1 / 2) * Real.exp (-lam * (μ - a)) := by
      have harg : (-lam * μ) + lam * a = -lam * (μ - a) := by ring
      rw [harg]
      field_simp [hlam.ne']

/--
Appendix C, Theorem 7: the high-tail Laplace CDF integral, matching the paper's
`x ≥ μ` CDF branch.
-/
theorem theorem7LaplaceCDFIntegral_of_mean_le
    {lam μ a : ℝ} (hlam : 0 < lam) (ha : μ ≤ a) :
    ∫ x : ℝ in Set.Iic a, theorem7LaplacePDF lam μ x =
      1 - (1 / 2) * Real.exp (-lam * (a - μ)) := by
  let f : ℝ → ℝ := fun x => theorem7LaplacePDF lam μ x
  have hleft_int : IntegrableOn f (Set.Iic μ) := by
    simpa [f] using
      theorem7LaplacePDF_integrableOn_Iic
        (lam := lam) (μ := μ) (a := μ) hlam
  have hright_int : IntegrableOn f (Set.Iic a) := by
    simpa [f] using
      theorem7LaplacePDF_integrableOn_Iic
        (lam := lam) (μ := μ) (a := a) hlam
  have hsub :
      (∫ x : ℝ in Set.Iic a, f x) -
          ∫ x : ℝ in Set.Iic μ, f x =
        ∫ x : ℝ in μ..a, f x := by
    simpa using
      (intervalIntegral.integral_Iic_sub_Iic
        (f := f) (a := μ) (b := a) hleft_int hright_int)
  have hleft :
      ∫ x : ℝ in Set.Iic μ, f x = (1 / 2 : ℝ) := by
    dsimp [f]
    simpa using
      theorem7LaplaceCDFIntegral_of_le_mean
        (lam := lam) (μ := μ) (a := μ) hlam le_rfl
  have hinterval :
      ∫ x : ℝ in μ..a, f x =
        (1 / 2 : ℝ) * (1 - Real.exp (-lam * (a - μ))) := by
    dsimp [f]
    calc
      ∫ x : ℝ in μ..a, theorem7LaplacePDF lam μ x =
          ∫ x : ℝ in μ..a,
            lam / 2 * Real.exp ((lam * μ) + (-lam) * x) := by
        refine intervalIntegral.integral_congr fun x hxint => ?_
        have hxIcc : x ∈ Set.Icc μ a := by
          simpa [Set.uIcc_of_le ha] using hxint
        have hμx : μ ≤ x := hxIcc.1
        rw [theorem7LaplacePDF_of_mean_le hμx]
        have harg : -lam * (x - μ) = (lam * μ) + (-lam) * x := by ring
        rw [harg]
      _ = lam / 2 *
          ∫ x : ℝ in μ..a,
            Real.exp ((lam * μ) + (-lam) * x) := by
        rw [intervalIntegral.integral_const_mul]
      _ = lam / 2 *
          ((Real.exp ((lam * μ) + (-lam) * a) -
              Real.exp ((lam * μ) + (-lam) * μ)) / (-lam)) := by
        rw [paper_theorem7_intervalIntegral_exp_affine
          (k := -lam) (β := lam * μ) (l := μ) (u := a)
          (neg_ne_zero.mpr hlam.ne')]
      _ = (1 / 2 : ℝ) * (1 - Real.exp (-lam * (a - μ))) := by
        have harg_a : (lam * μ) + (-lam) * a = -lam * (a - μ) := by ring
        have harg_μ : (lam * μ) + (-lam) * μ = 0 := by ring
        rw [harg_a, harg_μ, Real.exp_zero]
        field_simp [hlam.ne']
        ring
  have htotal :
      ∫ x : ℝ in Set.Iic a, f x =
        (1 / 2 : ℝ) + (1 / 2) *
          (1 - Real.exp (-lam * (a - μ))) := by
    linarith
  dsimp [f] at htotal
  rw [htotal]
  ring

/-- Appendix C, Theorem 7: closed-form CDF on and below the mean. -/
theorem theorem7LaplaceCDFClosedForm_of_le_mean
    {lam μ a : ℝ} (ha : a ≤ μ) :
    theorem7LaplaceCDFClosedForm lam μ a =
      (1 / 2) * Real.exp (-lam * (μ - a)) := by
  by_cases hlt : a < μ
  · simp [theorem7LaplaceCDFClosedForm, hlt]
  · have hEq : a = μ := le_antisymm ha (le_of_not_gt hlt)
    subst a
    simp [theorem7LaplaceCDFClosedForm]
    ring

/-- Appendix C, Theorem 7: closed-form CDF on and above the mean. -/
theorem theorem7LaplaceCDFClosedForm_of_mean_le
    {lam μ a : ℝ} (ha : μ ≤ a) :
    theorem7LaplaceCDFClosedForm lam μ a =
      1 - (1 / 2) * Real.exp (-lam * (a - μ)) := by
  have hnot : ¬ a < μ := not_lt.mpr ha
  simp [theorem7LaplaceCDFClosedForm, hnot]

/--
Appendix C, Theorem 7: the paper's closed-form Laplace CDF is the left
integral of the paper Laplace density.
-/
theorem theorem7LaplaceCDFIntegral_eq_closedForm
    {lam μ a : ℝ} (hlam : 0 < lam) :
    ∫ x : ℝ in Set.Iic a, theorem7LaplacePDF lam μ x =
      theorem7LaplaceCDFClosedForm lam μ a := by
  by_cases ha : a ≤ μ
  · rw [theorem7LaplaceCDFIntegral_of_le_mean hlam ha,
      theorem7LaplaceCDFClosedForm_of_le_mean (lam := lam) (μ := μ) ha]
  · have hμa : μ ≤ a := le_of_not_ge ha
    rw [theorem7LaplaceCDFIntegral_of_mean_le hlam hμa,
      theorem7LaplaceCDFClosedForm_of_mean_le (lam := lam) (μ := μ) hμa]

/-- Appendix C, Theorem 7: nonnegativity of the paper Laplace density. -/
theorem theorem7LaplacePDF_nonneg
    {lam μ x : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ theorem7LaplacePDF lam μ x := by
  unfold theorem7LaplacePDF
  positivity

/-- Appendix C, Theorem 7: positivity of the paper Laplace density. -/
theorem theorem7LaplacePDF_pos
    {lam μ x : ℝ} (hlam : 0 < lam) :
    0 < theorem7LaplacePDF lam μ x := by
  unfold theorem7LaplacePDF
  positivity

/-- Appendix C, Theorem 7: measurability of the paper Laplace density. -/
theorem theorem7LaplacePDF_measurable (lam μ : ℝ) :
    Measurable (theorem7LaplacePDF lam μ) :=
  (theorem7LaplacePDF_continuous lam μ).measurable

/--
Appendix C, Theorem 7: the zero-mean paper Laplace PDF is a positive constant
multiple of the Laplacian kernel used in Lemma 1.
-/
theorem theorem7LaplacePDF_zero_eq_const_mul_laplacianNoiseKernel
    (lam x : ℝ) :
    theorem7LaplacePDF lam 0 x =
      (lam / 2) * laplacianNoiseKernel lam x := by
  unfold theorem7LaplacePDF laplacianNoiseKernel
    AppliedModelingLib.Probability.laplacianNoiseKernel
  ring_nf

/--
Appendix C, Lemma 1 for the normalized zero-mean Laplace density: multiplying
the weakly well-ordered Laplacian kernel by the nonnegative normalizing
constant preserves weak well-ordering.
-/
theorem theorem7LaplacePDF_zero_weaklyWellOrdered
    {lam : ℝ} (hlam : 0 ≤ lam) :
    WeaklyWellOrderedNoise (theorem7LaplacePDF lam 0) := by
  have hkernel : WeaklyWellOrderedNoise (laplacianNoiseKernel lam) :=
    laplacianNoiseKernel_weaklyWellOrdered hlam
  have hconst : 0 ≤ lam / 2 := by positivity
  rw [show theorem7LaplacePDF lam 0 =
      fun x => (lam / 2) * laplacianNoiseKernel lam x by
        funext x
        exact theorem7LaplacePDF_zero_eq_const_mul_laplacianNoiseKernel lam x]
  exact hkernel.const_mul_nonneg hconst

/-- Appendix C, Theorem 7: nonnegativity of the paper Laplace CDF. -/
theorem theorem7LaplaceCDFClosedForm_nonneg
    {lam μ a : ℝ} (hlam : 0 < lam) :
    0 ≤ theorem7LaplaceCDFClosedForm lam μ a := by
  rw [← theorem7LaplaceCDFIntegral_eq_closedForm (lam := lam) (μ := μ) (a := a) hlam]
  exact integral_nonneg fun x =>
    theorem7LaplacePDF_nonneg (lam := lam) (μ := μ) (x := x) (le_of_lt hlam)

/-- Appendix C, Theorem 7: the paper Laplace CDF is strictly positive. -/
theorem theorem7LaplaceCDFClosedForm_pos
    {lam μ a : ℝ} (hlam : 0 < lam) :
    0 < theorem7LaplaceCDFClosedForm lam μ a := by
  by_cases ha : a ≤ μ
  · rw [theorem7LaplaceCDFClosedForm_of_le_mean
      (lam := lam) (μ := μ) (a := a) ha]
    positivity
  · have hμa : μ ≤ a := le_of_not_ge ha
    rw [theorem7LaplaceCDFClosedForm_of_mean_le
      (lam := lam) (μ := μ) (a := a) hμa]
    have hexp_le_one : Real.exp (-lam * (a - μ)) ≤ 1 := by
      rw [← Real.exp_zero]
      refine Real.exp_le_exp.mpr ?_
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (le_of_lt hlam)) (sub_nonneg.mpr hμa)
    have htail_le : (1 / 2 : ℝ) * Real.exp (-lam * (a - μ)) ≤ 1 / 2 := by
      nlinarith
    linarith

/-- Appendix C, Theorem 7: the paper Laplace CDF is at most one. -/
theorem theorem7LaplaceCDFClosedForm_le_one
    {lam μ a : ℝ} (hlam : 0 < lam) :
    theorem7LaplaceCDFClosedForm lam μ a ≤ 1 := by
  by_cases ha : a ≤ μ
  · rw [theorem7LaplaceCDFClosedForm_of_le_mean (lam := lam) (μ := μ) ha]
    have hexp_le_one : Real.exp (-lam * (μ - a)) ≤ 1 := by
      rw [← Real.exp_zero]
      refine Real.exp_le_exp.mpr ?_
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (le_of_lt hlam)) (sub_nonneg.mpr ha)
    linarith
  · have hμa : μ ≤ a := le_of_not_ge ha
    rw [theorem7LaplaceCDFClosedForm_of_mean_le (lam := lam) (μ := μ) hμa]
    have hsub_nonneg :
        0 ≤ (1 / 2 : ℝ) * Real.exp (-lam * (a - μ)) := by
      positivity
    linarith

/-- Appendix C, Theorem 7: the paper Laplace CDF tends to one at `+∞`. -/
theorem theorem7LaplaceCDFClosedForm_tendsto_atTop_one
    {lam μ : ℝ} (hlam : 0 < lam) :
    Filter.Tendsto (fun a : ℝ => theorem7LaplaceCDFClosedForm lam μ a)
      Filter.atTop (nhds 1) := by
  have hneg : -lam < 0 := by linarith
  have harg :
      Filter.Tendsto (fun a : ℝ => -lam * (a - μ))
        Filter.atTop Filter.atBot := by
    have hlin :
        Filter.Tendsto (fun a : ℝ => (-lam) * a + lam * μ)
          Filter.atTop Filter.atBot :=
      (Filter.Tendsto.const_mul_atTop_of_neg hneg Filter.tendsto_id).atBot_add
        tendsto_const_nhds
    convert hlin using 1
    ext a
    ring
  have htail :
      Filter.Tendsto
        (fun a : ℝ => (1 / 2 : ℝ) * Real.exp (-lam * (a - μ)))
        Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul
        (Real.tendsto_exp_atBot.comp harg)
  have hlim :
      Filter.Tendsto
        (fun a : ℝ => (1 : ℝ) -
          (1 / 2 : ℝ) * Real.exp (-lam * (a - μ)))
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub htail
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop μ] with a ha
  rw [theorem7LaplaceCDFClosedForm_of_mean_le
    (lam := lam) (μ := μ) (a := a) ha]

/-- Appendix C, Theorem 7: the paper Laplace CDF tends to zero at `-∞`. -/
theorem theorem7LaplaceCDFClosedForm_tendsto_atBot_zero
    {lam μ : ℝ} (hlam : 0 < lam) :
    Filter.Tendsto (fun a : ℝ => theorem7LaplaceCDFClosedForm lam μ a)
      Filter.atBot (nhds 0) := by
  have harg :
      Filter.Tendsto (fun a : ℝ => lam * (a - μ))
        Filter.atBot Filter.atBot := by
    have hlin :
        Filter.Tendsto (fun a : ℝ => lam * a + (-(lam * μ)))
          Filter.atBot Filter.atBot :=
      ((Filter.tendsto_const_mul_atBot_of_pos hlam).2 Filter.tendsto_id).atBot_add
        tendsto_const_nhds
    convert hlin using 1
    ext a
    ring
  have htail :
      Filter.Tendsto
        (fun a : ℝ => (1 / 2 : ℝ) * Real.exp (lam * (a - μ)))
        Filter.atBot (nhds 0) := by
    simpa using
      (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul
        (Real.tendsto_exp_atBot.comp harg)
  refine htail.congr' ?_
  filter_upwards [Filter.eventually_le_atBot μ] with a ha
  rw [theorem7LaplaceCDFClosedForm_of_le_mean
    (lam := lam) (μ := μ) (a := a) ha]
  ring_nf

/--
Appendix C, Theorem 7, case 1: numerator integral in the paper's equation
(C.3), on the region `a ≤ x_j < x_i`.
-/
theorem paper_theorem7_laplacian_case1_numerator_integral
    {lam xi xj a : ℝ} (hlam : 0 < lam) (ha : a ≤ xj) (hx : xj < xi) :
    ∫ x : ℝ in Set.Iic a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
      Real.exp (-lam * (xi + xj - 2 * a)) / 8 := by
  have hk : 0 < 2 * lam := by positivity
  calc
    ∫ x : ℝ in Set.Iic a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
        ∫ x : ℝ in Set.Iic a,
          lam / 4 *
            Real.exp ((-lam * (xi + xj)) + (2 * lam) * x) := by
      refine setIntegral_congr_fun measurableSet_Iic fun x hxIic => ?_
      have hxj : x ≤ xj := le_trans hxIic ha
      have hxi : x ≤ xi := le_trans hxj (le_of_lt hx)
      rw [theorem7LaplacePDF_of_le_mean hxi,
        theorem7LaplaceCDFClosedForm_of_le_mean (lam := lam) (μ := xj) hxj]
      calc
        lam / 2 * Real.exp (-lam * (xi - x)) *
            (1 / 2 * Real.exp (-lam * (xj - x))) =
            lam / 4 *
              (Real.exp (-lam * (xi - x)) *
                Real.exp (-lam * (xj - x))) := by ring
        _ = lam / 4 *
            Real.exp ((-lam * (xi + xj)) + (2 * lam) * x) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
    _ = lam / 4 *
        ∫ x : ℝ in Set.Iic a,
          Real.exp ((-lam * (xi + xj)) + (2 * lam) * x) := by
      rw [integral_const_mul]
    _ = lam / 4 *
        (Real.exp ((-lam * (xi + xj)) + (2 * lam) * a) / (2 * lam)) := by
      rw [paper_theorem7_integral_exp_affine_Iic
        (k := 2 * lam) (β := -lam * (xi + xj)) (c := a) hk]
    _ = Real.exp (-lam * (xi + xj - 2 * a)) / 8 := by
      have harg :
          (-lam * (xi + xj)) + (2 * lam) * a =
            -lam * (xi + xj - 2 * a) := by ring
      rw [harg]
      field_simp [hlam.ne']
      ring

/--
Appendix C, Theorem 7, case 1: denominator in the paper's equation (C.3), on
the region `a ≤ x_j < x_i`.
-/
theorem paper_theorem7_laplacian_case1_denominator_closedForm
    {lam xi xj a : ℝ} (ha : a ≤ xj) (hx : xj < xi) :
    theorem7LaplaceCDFClosedForm lam xi a *
        theorem7LaplaceCDFClosedForm lam xj a =
      (1 / 4) * Real.exp (-lam * (xi + xj - 2 * a)) := by
  have haxi : a ≤ xi := le_trans ha (le_of_lt hx)
  rw [theorem7LaplaceCDFClosedForm_of_le_mean (lam := lam) (μ := xi) haxi,
    theorem7LaplaceCDFClosedForm_of_le_mean (lam := lam) (μ := xj) ha]
  calc
    (1 / 2) * Real.exp (-lam * (xi - a)) *
        ((1 / 2) * Real.exp (-lam * (xj - a))) =
        (1 / 4) *
          (Real.exp (-lam * (xi - a)) *
            Real.exp (-lam * (xj - a))) := by ring
    _ = (1 / 4) * Real.exp (-lam * (xi + xj - 2 * a)) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf

/--
Appendix C, Theorem 7, case 1: the integral expression in (C.3) reduces to the
constant `1/2`.
-/
theorem paper_theorem7_laplacian_case1_integral_ratio
    {lam xi xj a : ℝ} (hlam : 0 < lam) (ha : a ≤ xj) (hx : xj < xi) :
    (∫ x : ℝ in Set.Iic a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) /
        (theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a) =
      (1 / 2 : ℝ) := by
  rw [paper_theorem7_laplacian_case1_numerator_integral hlam ha hx,
    paper_theorem7_laplacian_case1_denominator_closedForm (lam := lam) ha hx]
  have hne : Real.exp (-lam * (xi + xj - 2 * a)) ≠ 0 := Real.exp_ne_zero _
  field_simp [hne]
  norm_num

/--
Appendix C, Theorem 7, case 2: the paper's second integral over
`x_j ≤ x ≤ a ≤ x_i`.
-/
theorem paper_theorem7_laplacian_case2_second_integral
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hleft : xj ≤ a) (hright : a ≤ xi) :
    ∫ x in xj..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
      (1 / 2) *
          (Real.exp (-lam * (xi - a)) - Real.exp (-lam * (xi - xj))) -
        (lam / 4) * (a - xj) * Real.exp (-lam * (xi - xj)) := by
  calc
    ∫ x in xj..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
        ∫ x in xj..a,
          lam / 2 * Real.exp ((-lam * xi) + lam * x) -
            (lam / 4) * Real.exp (-lam * (xi - xj)) := by
      refine intervalIntegral.integral_congr fun x hxint => ?_
      have hxIcc : x ∈ Set.Icc xj a := by
        simpa [Set.uIcc_of_le hleft] using hxint
      have hxj : xj ≤ x := hxIcc.1
      have hxi : x ≤ xi := le_trans hxIcc.2 hright
      rw [theorem7LaplacePDF_of_le_mean hxi,
        theorem7LaplaceCDFClosedForm_of_mean_le (lam := lam) (μ := xj) hxj]
      calc
        lam / 2 * Real.exp (-lam * (xi - x)) *
            (1 - 1 / 2 * Real.exp (-lam * (x - xj))) =
            lam / 2 * Real.exp (-lam * (xi - x)) -
              lam / 4 *
                (Real.exp (-lam * (xi - x)) *
                  Real.exp (-lam * (x - xj))) := by ring
        _ = lam / 2 * Real.exp ((-lam * xi) + lam * x) -
            (lam / 4) * Real.exp (-lam * (xi - xj)) := by
          rw [← Real.exp_add]
          have hfirst : -lam * (xi - x) = (-lam * xi) + lam * x := by ring
          have hsecond :
              ((-lam * xi) + lam * x) + -lam * (x - xj) =
                -lam * (xi - xj) := by ring
          rw [hfirst, hsecond]
    _ = (∫ x in xj..a,
          lam / 2 * Real.exp ((-lam * xi) + lam * x)) -
        ∫ x in xj..a,
          (lam / 4) * Real.exp (-lam * (xi - xj)) := by
      have hInt1 :
          IntervalIntegrable
            (fun x : ℝ => lam / 2 * Real.exp ((-lam * xi) + lam * x))
            volume xj a := by
        apply ContinuousOn.intervalIntegrable
        fun_prop
      have hInt2 :
          IntervalIntegrable
            (fun _x : ℝ => (lam / 4) * Real.exp (-lam * (xi - xj)))
            volume xj a :=
        intervalIntegrable_const
      rw [intervalIntegral.integral_sub hInt1 hInt2]
    _ = (lam / 2 *
          ∫ x in xj..a, Real.exp ((-lam * xi) + lam * x)) -
        (a - xj) * ((lam / 4) * Real.exp (-lam * (xi - xj))) := by
      have hA :
          (∫ x in xj..a,
            lam / 2 * Real.exp ((-lam * xi) + lam * x)) =
            lam / 2 *
              ∫ x in xj..a, Real.exp ((-lam * xi) + lam * x) := by
        rw [intervalIntegral.integral_const_mul]
      have hB :
          (∫ x in xj..a,
            (lam / 4) * Real.exp (-lam * (xi - xj))) =
            (a - xj) * ((lam / 4) * Real.exp (-lam * (xi - xj))) := by
        rw [intervalIntegral.integral_const]
        ring
      rw [hA, hB]
    _ = (lam / 2 *
          ((Real.exp ((-lam * xi) + lam * a) -
              Real.exp ((-lam * xi) + lam * xj)) / lam)) -
        (a - xj) * ((lam / 4) * Real.exp (-lam * (xi - xj))) := by
      have hEval :=
        paper_theorem7_intervalIntegral_exp_affine
          (k := lam) (β := -lam * xi) (l := xj) (u := a) hlam.ne'
      exact congrArg
        (fun T =>
          lam / 2 * T -
            (a - xj) * ((lam / 4) * Real.exp (-lam * (xi - xj))))
        hEval
    _ = (1 / 2) *
          (Real.exp (-lam * (xi - a)) - Real.exp (-lam * (xi - xj))) -
        (lam / 4) * (a - xj) * Real.exp (-lam * (xi - xj)) := by
      have ha_arg : (-lam * xi) + lam * a = -lam * (xi - a) := by ring
      have hxj_arg : (-lam * xi) + lam * xj = -lam * (xi - xj) := by ring
      rw [ha_arg, hxj_arg]
      field_simp [hlam.ne']

/--
Appendix C, Theorem 7, case 2: the two paper numerator integrals combine to
the displayed closed form.
-/
theorem paper_theorem7_laplacian_case2_numerator_integral
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hleft : xj ≤ a) (hright : a ≤ xi)
    (hx : xj < xi) :
    (∫ x : ℝ in Set.Iic xj,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) +
      ∫ x in xj..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
      (1 / 2) * Real.exp (-lam * (xi - a)) -
      (3 / 8 + (lam / 4) * (a - xj)) *
          Real.exp (-lam * (xi - xj)) := by
  rw [paper_theorem7_laplacian_case1_numerator_integral
      (lam := lam) (xi := xi) (xj := xj) (a := xj) hlam le_rfl hx,
    paper_theorem7_laplacian_case2_second_integral hlam hleft hright]
  ring_nf

/--
Appendix C, Theorem 7, case 2: denominator in (C.3), on
`x_j ≤ a ≤ x_i`.
-/
theorem paper_theorem7_laplacian_case2_denominator_closedForm
    {lam xi xj a : ℝ} (hleft : xj ≤ a) (hright : a ≤ xi) :
    theorem7LaplaceCDFClosedForm lam xi a *
        theorem7LaplaceCDFClosedForm lam xj a =
      (1 / 2) * Real.exp (-lam * (xi - a)) -
        (1 / 4) * Real.exp (-lam * (xi - xj)) := by
  rw [theorem7LaplaceCDFClosedForm_of_le_mean (lam := lam) (μ := xi) hright,
    theorem7LaplaceCDFClosedForm_of_mean_le (lam := lam) (μ := xj) hleft]
  calc
    (1 / 2) * Real.exp (-lam * (xi - a)) *
        (1 - 1 / 2 * Real.exp (-lam * (a - xj))) =
        (1 / 2) * Real.exp (-lam * (xi - a)) -
          (1 / 4) *
            (Real.exp (-lam * (xi - a)) *
              Real.exp (-lam * (a - xj))) := by ring
    _ = (1 / 2) * Real.exp (-lam * (xi - a)) -
        (1 / 4) * Real.exp (-lam * (xi - xj)) := by
      rw [← Real.exp_add]
      have harg :
          -lam * (xi - a) + -lam * (a - xj) =
            -lam * (xi - xj) := by ring
      rw [harg]

/-- Algebraic simplification behind Appendix C, Theorem 7, case 2. -/
theorem paper_theorem7_laplacian_case2_ratio_algebra
    {R u : ℝ} (hden : 2 * R - 1 ≠ 0) :
    ((1 / 2) * R - (3 / 8 + u / 4)) /
        ((1 / 2) * R - 1 / 4) =
      1 - (1 / 2 + u) / (2 * R - 1) := by
  let D : ℝ := 2 * R - 1
  have hD : D ≠ 0 := by
    dsimp [D]
    exact hden
  have hnum :
      (1 / 2) * R - (3 / 8 + u / 4) =
        (D - (1 / 2 + u)) / 4 := by
    dsimp [D]
    ring
  have hden' :
      (1 / 2) * R - 1 / 4 = D / 4 := by
    dsimp [D]
    ring
  rw [hnum, hden']
  dsimp [D]
  field_simp [hden]

/--
Appendix C, Theorem 7, case 2: the split-integral expression equals the paper's
middle closed form.
-/
theorem paper_theorem7_laplacian_case2_integral_ratio
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hleft : xj < a) (hright : a ≤ xi)
    (hx : xj < xi) :
    ((∫ x : ℝ in Set.Iic xj,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) +
      ∫ x in xj..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) /
        (theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a) =
      1 - theorem7LaplacianCase2TailRatio lam xj a := by
  rw [paper_theorem7_laplacian_case2_numerator_integral
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam (le_of_lt hleft) hright hx,
    paper_theorem7_laplacian_case2_denominator_closedForm
      (lam := lam) (xi := xi) (xj := xj) (a := a) (le_of_lt hleft) hright]
  have hsplit :
      Real.exp (-lam * (xi - a)) =
        Real.exp (-lam * (xi - xj)) * Real.exp (lam * (a - xj)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  unfold theorem7LaplacianCase2TailRatio
  let E : ℝ := Real.exp (-lam * (xi - xj))
  let R : ℝ := Real.exp (lam * (a - xj))
  let u : ℝ := lam * (a - xj)
  have hE : E ≠ 0 := by
    dsimp [E]
    exact Real.exp_ne_zero _
  have hden : 2 * R - 1 ≠ 0 := by
    have hpos : 0 < lam * (a - xj) := mul_pos hlam (sub_pos.mpr hleft)
    have hgt : 1 < R := by
      dsimp [R]
      exact Real.one_lt_exp_iff.mpr hpos
    nlinarith
  change (((1 / 2) * (E * R) -
        (3 / 8 + (lam / 4) * (a - xj)) * E) /
        ((1 / 2) * (E * R) - (1 / 4) * E) =
      1 - (1 / 2 + u) / (2 * R - 1))
  have hu : (lam / 4) * (a - xj) = u / 4 := by
    dsimp [u]
    ring
  rw [hu]
  have hsmall : (1 / 2) * R - 1 / 4 ≠ 0 := by
    intro h
    apply hden
    nlinarith
  have hcancel :
      (((1 / 2) * (E * R) - (3 / 8 + u / 4) * E) /
          ((1 / 2) * (E * R) - (1 / 4) * E)) =
        ((1 / 2) * R - (3 / 8 + u / 4)) /
          ((1 / 2) * R - 1 / 4) := by
    field_simp [hE, hsmall]
  exact hcancel.trans (paper_theorem7_laplacian_case2_ratio_algebra hden)

/--
Appendix C, Theorem 7, case 3: the paper's third numerator integral over
`x_i ≤ x ≤ a`.
-/
theorem paper_theorem7_laplacian_case3_third_integral
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi ≤ a) :
    ∫ x in xi..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
      (1 / 2) * (1 - Real.exp (-lam * (a - xi))) -
        (1 / 8) *
          (Real.exp (-lam * (xi - xj)) -
            Real.exp (-lam * (2 * a - xi - xj))) := by
  calc
    ∫ x in xi..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
        ∫ x in xi..a,
          lam / 2 * Real.exp ((lam * xi) + (-lam) * x) -
            lam / 4 * Real.exp ((lam * (xi + xj)) + (-2 * lam) * x) := by
      refine intervalIntegral.integral_congr fun x hxint => ?_
      have hxIcc : x ∈ Set.Icc xi a := by
        simpa [Set.uIcc_of_le ha] using hxint
      have hxi : xi ≤ x := hxIcc.1
      have hxj : xj ≤ x := (le_of_lt hx).trans hxi
      rw [theorem7LaplacePDF_of_mean_le hxi,
        theorem7LaplaceCDFClosedForm_of_mean_le (lam := lam) (μ := xj) hxj]
      calc
        lam / 2 * Real.exp (-lam * (x - xi)) *
            (1 - 1 / 2 * Real.exp (-lam * (x - xj))) =
            lam / 2 * Real.exp (-lam * (x - xi)) -
              lam / 4 *
                (Real.exp (-lam * (x - xi)) *
                  Real.exp (-lam * (x - xj))) := by ring
        _ = lam / 2 * Real.exp ((lam * xi) + (-lam) * x) -
            lam / 4 * Real.exp ((lam * (xi + xj)) + (-2 * lam) * x) := by
          rw [← Real.exp_add]
          have hfirst : -lam * (x - xi) = (lam * xi) + (-lam) * x := by ring
          have hsecond :
              (lam * xi + -lam * x) + -lam * (x - xj) =
                (lam * (xi + xj)) + (-2 * lam) * x := by ring
          rw [hfirst, hsecond]
    _ = (∫ x in xi..a,
          lam / 2 * Real.exp ((lam * xi) + (-lam) * x)) -
        ∫ x in xi..a,
          lam / 4 * Real.exp ((lam * (xi + xj)) + (-2 * lam) * x) := by
      have hInt1 :
          IntervalIntegrable
            (fun x : ℝ => lam / 2 * Real.exp ((lam * xi) + (-lam) * x))
            volume xi a := by
        apply ContinuousOn.intervalIntegrable
        fun_prop
      have hInt2 :
          IntervalIntegrable
            (fun x : ℝ => lam / 4 * Real.exp ((lam * (xi + xj)) + (-2 * lam) * x))
            volume xi a := by
        apply ContinuousOn.intervalIntegrable
        fun_prop
      rw [intervalIntegral.integral_sub hInt1 hInt2]
    _ = (lam / 2 *
          ∫ x in xi..a, Real.exp ((lam * xi) + (-lam) * x)) -
        (lam / 4 *
          ∫ x in xi..a, Real.exp ((lam * (xi + xj)) + (-2 * lam) * x)) := by
      have hA :
          (∫ x in xi..a,
            lam / 2 * Real.exp ((lam * xi) + (-lam) * x)) =
            lam / 2 *
              ∫ x in xi..a, Real.exp ((lam * xi) + (-lam) * x) := by
        rw [intervalIntegral.integral_const_mul]
      have hB :
          (∫ x in xi..a,
            lam / 4 * Real.exp ((lam * (xi + xj)) + (-2 * lam) * x)) =
            lam / 4 *
              ∫ x in xi..a, Real.exp ((lam * (xi + xj)) + (-2 * lam) * x) := by
        rw [intervalIntegral.integral_const_mul]
      rw [hA, hB]
    _ = (lam / 2 *
          ((Real.exp ((lam * xi) + (-lam) * a) -
              Real.exp ((lam * xi) + (-lam) * xi)) / (-lam))) -
        (lam / 4 *
          ((Real.exp ((lam * (xi + xj)) + (-2 * lam) * a) -
              Real.exp ((lam * (xi + xj)) + (-2 * lam) * xi)) / (-2 * lam))) := by
      have hEval1 :=
        paper_theorem7_intervalIntegral_exp_affine
          (k := -lam) (β := lam * xi) (l := xi) (u := a) (by linarith : -lam ≠ 0)
      have hEval2 :=
        paper_theorem7_intervalIntegral_exp_affine
          (k := -2 * lam) (β := lam * (xi + xj)) (l := xi) (u := a)
          (by nlinarith [hlam] : -2 * lam ≠ 0)
      rw [hEval1, hEval2]
    _ = (1 / 2) * (1 - Real.exp (-lam * (a - xi))) -
        (1 / 8) *
          (Real.exp (-lam * (xi - xj)) -
            Real.exp (-lam * (2 * a - xi - xj))) := by
      have h1a : (lam * xi) + (-lam) * a = -lam * (a - xi) := by ring
      have h1xi : (lam * xi) + (-lam) * xi = 0 := by ring
      have h2a :
          (lam * (xi + xj)) + (-2 * lam) * a =
            -lam * (2 * a - xi - xj) := by ring
      have h2xi :
          (lam * (xi + xj)) + (-2 * lam) * xi =
            -lam * (xi - xj) := by ring
      rw [h1a, h1xi, h2a, h2xi, Real.exp_zero]
      field_simp [hlam.ne']
      ring

/--
Appendix C, Theorem 7, case 3: the three numerator integrals in (C.3)
combine to the scaled numerator used in the paper's right-tail closed form.
-/
theorem paper_theorem7_laplacian_case3_numerator_integral
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi ≤ a) :
    ((∫ x : ℝ in Set.Iic xj,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) +
      ∫ x in xj..xi,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) +
      ∫ x in xi..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
      (1 / 8) *
        theorem7LaplacianCase3Numerator
          (lam * (xi - xj)) (Real.exp (-lam * (a - xi))) := by
  rw [paper_theorem7_laplacian_case2_numerator_integral
      (lam := lam) (xi := xi) (xj := xj) (a := xi)
      hlam (le_of_lt hx) le_rfl hx,
    paper_theorem7_laplacian_case3_third_integral
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx ha]
  have hzero : -lam * (xi - xi) = 0 := by ring
  have hquad :
      Real.exp (-lam * (2 * a - xi - xj)) =
        Real.exp (-lam * (xi - xj)) *
          Real.exp (-lam * (a - xi)) ^ 2 := by
    have harg :
        -lam * (2 * a - xi - xj) =
          -lam * (xi - xj) + (-lam * (a - xi) + -lam * (a - xi)) := by
      ring
    rw [harg, Real.exp_add, Real.exp_add]
    ring
  have hzarg : -(lam * (xi - xj)) = -lam * (xi - xj) := by ring
  rw [hzero, Real.exp_zero, hquad]
  dsimp [theorem7LaplacianCase3Numerator]
  rw [hzarg]
  ring

/--
Appendix C, Theorem 7, case 3: denominator in (C.3), on the region
`x_j < x_i ≤ a`.
-/
theorem paper_theorem7_laplacian_case3_denominator_closedForm
    {lam xi xj a : ℝ} (hx : xj < xi) (ha : xi ≤ a) :
    theorem7LaplaceCDFClosedForm lam xi a *
        theorem7LaplaceCDFClosedForm lam xj a =
      (1 / 4) *
        theorem7LaplacianCase3Denominator
          (lam * (xi - xj)) (Real.exp (-lam * (a - xi))) := by
  have hxj_le_a : xj ≤ a := (le_of_lt hx).trans ha
  rw [theorem7LaplaceCDFClosedForm_of_mean_le (lam := lam) (μ := xi) ha,
    theorem7LaplaceCDFClosedForm_of_mean_le (lam := lam) (μ := xj) hxj_le_a]
  have hsplit :
      Real.exp (-lam * (a - xj)) =
        Real.exp (-lam * (a - xi)) *
          Real.exp (-lam * (xi - xj)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hzarg : -(lam * (xi - xj)) = -lam * (xi - xj) := by ring
  rw [hsplit]
  dsimp [theorem7LaplacianCase3Denominator]
  rw [hzarg]
  ring

/--
Appendix C, Theorem 7, case 3: the split-integral expression in (C.3) equals
one half of the paper's cleared right-tail ratio.  The harmless factor `1/2`
does not affect the derivative sign proved above.
-/
theorem paper_theorem7_laplacian_case3_integral_ratio
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi < a) :
    (((∫ x : ℝ in Set.Iic xj,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) +
      ∫ x in xj..xi,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) +
      ∫ x in xi..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) /
        (theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a) =
      (1 / 2) *
        theorem7LaplacianCase3ConditionalProb lam xi xj a := by
  rw [paper_theorem7_laplacian_case3_numerator_integral
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx (le_of_lt ha),
    paper_theorem7_laplacian_case3_denominator_closedForm
      (lam := lam) (xi := xi) (xj := xj) (a := a) hx (le_of_lt ha)]
  let z : ℝ := lam * (xi - xj)
  let r : ℝ := Real.exp (-lam * (a - xi))
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos hlam (sub_pos.mpr hx)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact le_of_lt (Real.exp_pos _)
  have hr1 : r ≤ 1 := by
    dsimp [r]
    have hneg : -lam * (a - xi) < 0 := by
      have hpos : 0 < lam * (a - xi) := mul_pos hlam (sub_pos.mpr ha)
      linarith
    exact le_of_lt (Real.exp_lt_one_iff.mpr hneg)
  have hden_pos := theorem7LaplacianCase3Denominator_pos hz hr0 hr1
  dsimp [theorem7LaplacianCase3ConditionalProb,
    theorem7LaplacianCase3Ratio, z, r]
  field_simp [hden_pos.ne']
  ring

/-- The integrand in Appendix C, Theorem 7 equation (C.3). -/
noncomputable def theorem7LaplacianPairIntegrand
    (lam xi xj x : ℝ) : ℝ := theorem7LaplacePDF lam xi x * theorem7LaplaceCDFClosedForm lam xj x

/-- Appendix C, Theorem 7 case-1 split-integral ratio. -/
noncomputable def theorem7LaplacianCase1IntegralRatio
    (lam xi xj a : ℝ) : ℝ :=
  (∫ x : ℝ in Set.Iic a,
      theorem7LaplacianPairIntegrand lam xi xj x) /
    (theorem7LaplaceCDFClosedForm lam xi a *
      theorem7LaplaceCDFClosedForm lam xj a)

/-- Appendix C, Theorem 7 case-2 split-integral ratio. -/
noncomputable def theorem7LaplacianCase2IntegralRatio
    (lam xi xj a : ℝ) : ℝ :=
  ((∫ x : ℝ in Set.Iic xj,
      theorem7LaplacianPairIntegrand lam xi xj x) +
    ∫ x in xj..a,
      theorem7LaplacianPairIntegrand lam xi xj x) /
    (theorem7LaplaceCDFClosedForm lam xi a *
      theorem7LaplaceCDFClosedForm lam xj a)

/-- Appendix C, Theorem 7 case-3 split-integral ratio. -/
noncomputable def theorem7LaplacianCase3IntegralRatio
    (lam xi xj a : ℝ) : ℝ :=
  (((∫ x : ℝ in Set.Iic xj,
      theorem7LaplacianPairIntegrand lam xi xj x) +
    ∫ x in xj..xi,
      theorem7LaplacianPairIntegrand lam xi xj x) +
    ∫ x in xi..a,
      theorem7LaplacianPairIntegrand lam xi xj x) /
    (theorem7LaplaceCDFClosedForm lam xi a *
      theorem7LaplaceCDFClosedForm lam xj a)

/--
Appendix C, Theorem 7 case 1: the split-integral ratio is locally constant on
the open region `a < x_j`.
-/
theorem theorem7LaplacianCase1IntegralRatio_hasDerivAt_nonneg
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : a < xj) :
    HasDerivAt
        (fun a => theorem7LaplacianCase1IntegralRatio lam xi xj a) 0 a ∧
      0 ≤ (0 : ℝ) := by
  have hconst : HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 a :=
    hasDerivAt_const a (1 / 2 : ℝ)
  have hEq :
      (fun b => theorem7LaplacianCase1IntegralRatio lam xi xj b) =ᶠ[nhds a]
        (fun _ : ℝ => (1 / 2 : ℝ)) := by
    have hnear : ∀ᶠ b in nhds a, b ∈ Set.Iio xj :=
      isOpen_Iio.mem_nhds (show a ∈ Set.Iio xj by exact ha)
    exact hnear.mono fun b hb => by
      unfold theorem7LaplacianCase1IntegralRatio
      unfold theorem7LaplacianPairIntegrand
      exact paper_theorem7_laplacian_case1_integral_ratio
        (lam := lam) (xi := xi) (xj := xj) (a := b) hlam (le_of_lt hb) hx
  exact ⟨hconst.congr_of_eventuallyEq hEq, le_rfl⟩

/--
Appendix C, Theorem 7 case 2: the split-integral ratio has the positive
derivative proved for the paper's middle closed form throughout
`x_j < a < x_i`.
-/
theorem theorem7LaplacianCase2IntegralRatio_hasDerivAt_pos
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi)
    (hleft : xj < a) (hright : a < xi) :
    ∃ d,
      HasDerivAt
        (fun a => theorem7LaplacianCase2IntegralRatio lam xi xj a) d a ∧
        0 < d := by
  obtain ⟨d, hclosed, hdpos⟩ :=
    theorem7LaplacianCase2ConditionalProb_hasDerivAt_pos
      (lam := lam) (xj := xj) (a := a) hlam (sub_pos.mpr hleft)
  have hEq :
      (fun b => theorem7LaplacianCase2IntegralRatio lam xi xj b) =ᶠ[nhds a]
        (fun b => 1 - theorem7LaplacianCase2TailRatio lam xj b) := by
    have hnear : ∀ᶠ b in nhds a, b ∈ Set.Ioo xj xi :=
      isOpen_Ioo.mem_nhds
        (show a ∈ Set.Ioo xj xi by exact ⟨hleft, hright⟩)
    exact hnear.mono fun b hb => by
      unfold theorem7LaplacianCase2IntegralRatio
      unfold theorem7LaplacianPairIntegrand
      exact paper_theorem7_laplacian_case2_integral_ratio
        (lam := lam) (xi := xi) (xj := xj) (a := b)
        hlam hb.1 (le_of_lt hb.2) hx
  exact ⟨d, hclosed.congr_of_eventuallyEq hEq, hdpos⟩

/--
Appendix C, Theorem 7 case 3: the split-integral ratio has positive derivative
throughout `x_i < a`.  The integral ratio is one half of the cleared closed
form, so its derivative is one half of the closed-form derivative.
-/
theorem theorem7LaplacianCase3IntegralRatio_hasDerivAt_pos
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi < a) :
    ∃ d,
      HasDerivAt
        (fun a => theorem7LaplacianCase3IntegralRatio lam xi xj a) d a ∧
        0 < d := by
  obtain ⟨dClosed, hclosed, hdClosedPos⟩ :=
    theorem7LaplacianCase3ConditionalProb_hasDerivAt_pos
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx ha
  have hscaled :
      HasDerivAt
        (fun a => (1 / 2 : ℝ) *
          theorem7LaplacianCase3ConditionalProb lam xi xj a)
        ((1 / 2 : ℝ) * dClosed) a :=
    hclosed.const_mul (1 / 2 : ℝ)
  have hEq :
      (fun b => theorem7LaplacianCase3IntegralRatio lam xi xj b) =ᶠ[nhds a]
        (fun b => (1 / 2 : ℝ) *
          theorem7LaplacianCase3ConditionalProb lam xi xj b) := by
    have hnear : ∀ᶠ b in nhds a, b ∈ Set.Ioi xi :=
      isOpen_Ioi.mem_nhds (show a ∈ Set.Ioi xi by exact ha)
    exact hnear.mono fun b hb => by
      unfold theorem7LaplacianCase3IntegralRatio
      unfold theorem7LaplacianPairIntegrand
      exact paper_theorem7_laplacian_case3_integral_ratio
        (lam := lam) (xi := xi) (xj := xj) (a := b) hlam hx hb
  refine ⟨(1 / 2 : ℝ) * dClosed, ?_, ?_⟩
  · exact hscaled.congr_of_eventuallyEq hEq
  · nlinarith

/--
Appendix C, Theorem 7 at the split-integral layer.  This combines the paper's
three Laplace-integral regions with the derivative signs of the corresponding
closed forms, stated on the interiors of the three regions.
-/
theorem paper_theorem7_laplacian_integralRatio_derivative_cases
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (a < xj →
      HasDerivAt
          (fun a => theorem7LaplacianCase1IntegralRatio lam xi xj a) 0 a ∧
        0 ≤ (0 : ℝ)) ∧
    (xj < a → a < xi →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianCase2IntegralRatio lam xi xj a) d a ∧
          0 < d) ∧
    (xi < a →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianCase3IntegralRatio lam xi xj a) d a ∧
          0 < d) ∧
    (∃ a d,
      xj < a ∧ a < xi ∧
        HasDerivAt
          (fun a => theorem7LaplacianCase2IntegralRatio lam xi xj a) d a ∧
        0 < d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hleft
    exact theorem7LaplacianCase1IntegralRatio_hasDerivAt_nonneg
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx hleft
  · intro hleft hright
    exact theorem7LaplacianCase2IntegralRatio_hasDerivAt_pos
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx hleft hright
  · intro hright
    exact theorem7LaplacianCase3IntegralRatio_hasDerivAt_pos
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx hright
  · let amid : ℝ := (xj + xi) / 2
    have hleft : xj < amid := by
      dsimp [amid]
      linarith
    have hright : amid < xi := by
      dsimp [amid]
      linarith
    obtain ⟨d, hd, hdpos⟩ :=
      theorem7LaplacianCase2IntegralRatio_hasDerivAt_pos
        (lam := lam) (xi := xi) (xj := xj) (a := amid)
        hlam hx hleft hright
    exact ⟨amid, d, hleft, hright, hd, hdpos⟩

/--
Appendix C, Theorem 7: canonical one-dimensional Laplace measure for the
paper's density.
-/
noncomputable def theorem7LaplaceMeasure (lam μ : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun x => ENNReal.ofReal (theorem7LaplacePDF lam μ x))

/--
Appendix C, Theorem 7: the canonical Laplace measure assigns a left
half-line the paper's closed-form CDF value.
-/
theorem theorem7LaplaceMeasure_Iic_eq_CDF
    {lam μ a : ℝ} (hlam : 0 < lam) :
    theorem7LaplaceMeasure lam μ (Set.Iic a) =
      ENNReal.ofReal (theorem7LaplaceCDFClosedForm lam μ a) := by
  have h_int :
      Integrable (fun x : ℝ => theorem7LaplacePDF lam μ x)
        (volume.restrict (Set.Iic a)) := by
    simpa [IntegrableOn] using
      theorem7LaplacePDF_integrableOn_Iic
        (lam := lam) (μ := μ) (a := a) hlam
  have h_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Iic a)]
        (fun x : ℝ => theorem7LaplacePDF lam μ x) :=
    ae_of_all _ fun x =>
      theorem7LaplacePDF_nonneg (lam := lam) (μ := μ) (x := x)
        (le_of_lt hlam)
  unfold theorem7LaplaceMeasure
  rw [withDensity_apply _ measurableSet_Iic]
  rw [← ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
  rw [theorem7LaplaceCDFIntegral_eq_closedForm
    (lam := lam) (μ := μ) (a := a) hlam]

/-- Appendix C, Theorem 7: the canonical Laplace measure has total mass one. -/
theorem theorem7LaplaceMeasure_univ
    {lam μ : ℝ} (hlam : 0 < lam) :
    theorem7LaplaceMeasure lam μ Set.univ = 1 := by
  have hmono : Monotone fun a : ℝ => (Set.Iic a : Set ℝ) := by
    intro a b hab
    exact Set.Iic_subset_Iic.mpr hab
  have hcont :=
    MeasureTheory.tendsto_measure_iUnion_atTop
      (μ := theorem7LaplaceMeasure lam μ) hmono
  have hsets : (⋃ a : ℝ, Set.Iic a) = (Set.univ : Set ℝ) := by
    simpa using
      (Set.iUnion_Iic : (⋃ a : ℝ, Set.Iic a) = (Set.univ : Set ℝ))
  have hmeasure :
      Filter.Tendsto
        (fun a : ℝ => theorem7LaplaceMeasure lam μ (Set.Iic a))
        Filter.atTop (nhds (theorem7LaplaceMeasure lam μ Set.univ)) := by
    simpa [Function.comp_def, hsets] using hcont
  have hcdf :
      Filter.Tendsto
        (fun a : ℝ => theorem7LaplaceMeasure lam μ (Set.Iic a))
        Filter.atTop (nhds (1 : ℝ≥0∞)) := by
    have hreal :=
      ENNReal.tendsto_ofReal
        (theorem7LaplaceCDFClosedForm_tendsto_atTop_one
          (lam := lam) (μ := μ) hlam)
    simpa [theorem7LaplaceMeasure_Iic_eq_CDF
      (lam := lam) (μ := μ) (hlam := hlam), ENNReal.ofReal_one] using hreal
  exact tendsto_nhds_unique hmeasure hcdf

/--
Appendix C, Theorem 7: the paper Laplace density integrates to one as an
`ENNReal` density.
-/
theorem theorem7LaplacePDF_lintegral_eq_one
    {lam μ : ℝ} (hlam : 0 < lam) :
    ∫⁻ x : ℝ, ENNReal.ofReal (theorem7LaplacePDF lam μ x)
      ∂(volume : Measure ℝ) = 1 := by
  have hmass := theorem7LaplaceMeasure_univ (lam := lam) (μ := μ) hlam
  simpa [theorem7LaplaceMeasure] using hmass

/--
Appendix C, Theorem 7: the canonical Laplace measure has no atom at the cutoff,
so strict and weak left half-lines have the same mass.
-/
theorem theorem7LaplaceMeasure_Iio_eq_Iic (lam μ a : ℝ) :
    theorem7LaplaceMeasure lam μ (Set.Iio a) =
      theorem7LaplaceMeasure lam μ (Set.Iic a) := by
  haveI : NoAtoms (theorem7LaplaceMeasure lam μ) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  exact measure_congr
    (Iio_ae_eq_Iic (μ := theorem7LaplaceMeasure lam μ) (a := a))

/-- Lower-tail probability for the paper Laplace measure in CDF form. -/
theorem theorem7LaplaceMeasure_Iio_measureProb_eq_CDF
    {lam μ a : ℝ} (hlam : 0 < lam) :
    measureProb (theorem7LaplaceMeasure lam μ) (fun z => z < a) =
      theorem7LaplaceCDFClosedForm lam μ a := by
  unfold measureProb
  change (theorem7LaplaceMeasure lam μ (Set.Iio a)).toReal =
    theorem7LaplaceCDFClosedForm lam μ a
  rw [theorem7LaplaceMeasure_Iio_eq_Iic,
    theorem7LaplaceMeasure_Iic_eq_CDF (lam := lam) (μ := μ) (a := a) hlam,
    ENNReal.toReal_ofReal
      (theorem7LaplaceCDFClosedForm_nonneg
        (lam := lam) (μ := μ) (a := a) hlam)]

/-- Lower-tail probability below the mean in the explicit Laplace rate form. -/
theorem theorem7LaplaceMeasure_Iio_measureProb_eq_leftTail
    {lam μ a : ℝ} (hlam : 0 < lam) (ha : a ≤ μ) :
    measureProb (theorem7LaplaceMeasure lam μ) (fun z => z < a) =
      (1 / 2 : ℝ) * Real.exp (lam * (a - μ)) := by
  rw [theorem7LaplaceMeasure_Iio_measureProb_eq_CDF
      (lam := lam) (μ := μ) (a := a) hlam,
    theorem7LaplaceCDFClosedForm_of_le_mean
      (lam := lam) (μ := μ) (a := a) ha]
  ring_nf

/-- Upper-tail probability for the paper Laplace measure in CDF form. -/
theorem theorem7LaplaceMeasure_Ioi_measureProb_eq_one_sub_CDF
    {lam μ a : ℝ} (hlam : 0 < lam) :
    measureProb (theorem7LaplaceMeasure lam μ) (fun z => a < z) =
      1 - theorem7LaplaceCDFClosedForm lam μ a := by
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam μ) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := μ) hlam⟩
  unfold measureProb
  change (theorem7LaplaceMeasure lam μ (Set.Ioi a)).toReal =
    1 - theorem7LaplaceCDFClosedForm lam μ a
  have hcompl :=
    probReal_compl_eq_one_sub
      (μ := theorem7LaplaceMeasure lam μ) (s := Set.Iic a)
      measurableSet_Iic
  rw [show (Set.Iic a)ᶜ = Set.Ioi a by exact Set.compl_Iic] at hcompl
  have hIic :
      (theorem7LaplaceMeasure lam μ).real (Set.Iic a) =
        theorem7LaplaceCDFClosedForm lam μ a := by
    rw [Measure.real_def]
    rw [theorem7LaplaceMeasure_Iic_eq_CDF
        (lam := lam) (μ := μ) (a := a) hlam,
      ENNReal.toReal_ofReal
        (theorem7LaplaceCDFClosedForm_nonneg
          (lam := lam) (μ := μ) (a := a) hlam)]
  change (theorem7LaplaceMeasure lam μ).real (Set.Ioi a) =
    1 - theorem7LaplaceCDFClosedForm lam μ a
  rw [hcompl, hIic]

/-- Upper-tail probability above the mean in the explicit Laplace rate form. -/
theorem theorem7LaplaceMeasure_Ioi_measureProb_eq_rightTail
    {lam μ a : ℝ} (hlam : 0 < lam) (ha : μ ≤ a) :
    measureProb (theorem7LaplaceMeasure lam μ) (fun z => a < z) =
      (1 / 2 : ℝ) * Real.exp (-(lam * (a - μ))) := by
  rw [theorem7LaplaceMeasure_Ioi_measureProb_eq_one_sub_CDF
      (lam := lam) (μ := μ) (a := a) hlam,
    theorem7LaplaceCDFClosedForm_of_mean_le
      (lam := lam) (μ := μ) (a := a) ha]
  ring_nf

/--
If `lam θ → ∞` and the cutoff is strictly below the location, the lower
Laplace tail vanishes.
-/
theorem theorem7LaplaceMeasure_Iio_tendsto_atTop_zero
    {lam : ℝ → ℝ} {μ a : ℝ}
    (hlam : Filter.Tendsto lam Filter.atTop Filter.atTop) (ha : a < μ) :
    Filter.Tendsto
      (fun θ : ℝ =>
        measureProb (theorem7LaplaceMeasure (lam θ) μ) (fun z => z < a))
      Filter.atTop (nhds 0) := by
  have hgap : a - μ < 0 := by linarith
  have harg :
      Filter.Tendsto (fun θ : ℝ => lam θ * (a - μ))
        Filter.atTop Filter.atBot :=
    hlam.atTop_mul_const_of_neg hgap
  have htail :
      Filter.Tendsto
        (fun θ : ℝ => (1 / 2 : ℝ) * Real.exp (lam θ * (a - μ)))
        Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul
        (Real.tendsto_exp_atBot.comp harg)
  refine htail.congr' ?_
  filter_upwards [hlam.eventually (Filter.eventually_gt_atTop (0 : ℝ))]
    with θ hθ
  exact (theorem7LaplaceMeasure_Iio_measureProb_eq_leftTail
    (lam := lam θ) (μ := μ) (a := a) hθ (le_of_lt ha)).symm

/--
If `lam θ → ∞` and the cutoff is strictly above the location, the upper
Laplace tail vanishes.
-/
theorem theorem7LaplaceMeasure_Ioi_tendsto_atTop_zero
    {lam : ℝ → ℝ} {μ a : ℝ}
    (hlam : Filter.Tendsto lam Filter.atTop Filter.atTop) (ha : μ < a) :
    Filter.Tendsto
      (fun θ : ℝ =>
        measureProb (theorem7LaplaceMeasure (lam θ) μ) (fun z => a < z))
      Filter.atTop (nhds 0) := by
  have hgap : 0 < a - μ := by linarith
  have harg_pos :
      Filter.Tendsto (fun θ : ℝ => lam θ * (a - μ))
        Filter.atTop Filter.atTop :=
    hlam.atTop_mul_const hgap
  have harg :
      Filter.Tendsto (fun θ : ℝ => -(lam θ * (a - μ)))
        Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp harg_pos
  have htail :
      Filter.Tendsto
        (fun θ : ℝ => (1 / 2 : ℝ) * Real.exp (-(lam θ * (a - μ))))
        Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul
        (Real.tendsto_exp_atBot.comp harg)
  refine htail.congr' ?_
  filter_upwards [hlam.eventually (Filter.eventually_gt_atTop (0 : ℝ))]
    with θ hθ
  exact (theorem7LaplaceMeasure_Ioi_measureProb_eq_rightTail
    (lam := lam θ) (μ := μ) (a := a) hθ (le_of_lt ha)).symm

/-- Appendix C, Theorem 7: measurability of the paper Laplace CDF. -/
theorem theorem7LaplaceCDFClosedForm_measurable (lam μ : ℝ) :
    Measurable fun a : ℝ => theorem7LaplaceCDFClosedForm lam μ a := by
  unfold theorem7LaplaceCDFClosedForm
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) ?_ ?_
  · exact
      (continuous_const.mul
        (Real.continuous_exp.comp
          (continuous_const.mul (continuous_const.sub continuous_id)))).measurable
  · exact
      (continuous_const.sub
        (continuous_const.mul
          (Real.continuous_exp.comp
            (continuous_const.mul (continuous_id.sub continuous_const))))).measurable

/--
Appendix C, Theorem 7: integrability of the density/CDF product in equation
(C.3) over a left half-line.
-/
theorem theorem7LaplacianPairIntegrand_integrableOn_Iic
    {lam xi xj a : ℝ} (hlam : 0 < lam) :
    IntegrableOn
      (fun x : ℝ => theorem7LaplacianPairIntegrand lam xi xj x)
      (Set.Iic a) := by
  have hpdf :
      IntegrableOn (fun x : ℝ => theorem7LaplacePDF lam xi x) (Set.Iic a) :=
    theorem7LaplacePDF_integrableOn_Iic
      (lam := lam) (μ := xi) (a := a) hlam
  have hcdf_meas :
      AEStronglyMeasurable
        (fun x : ℝ => theorem7LaplaceCDFClosedForm lam xj x)
        (volume.restrict (Set.Iic a)) :=
    (theorem7LaplaceCDFClosedForm_measurable lam xj).aestronglyMeasurable
  have hcdf_bound :
      ∀ᵐ x ∂volume.restrict (Set.Iic a),
        ‖theorem7LaplaceCDFClosedForm lam xj x‖ ≤ (1 : ℝ) := by
    refine ae_restrict_of_forall_mem measurableSet_Iic ?_
    intro x _hx
    rw [Real.norm_of_nonneg
      (theorem7LaplaceCDFClosedForm_nonneg
        (lam := lam) (μ := xj) (a := x) hlam)]
    exact theorem7LaplaceCDFClosedForm_le_one
      (lam := lam) (μ := xj) (a := x) hlam
  simpa [theorem7LaplacianPairIntegrand] using
    hpdf.mul_bdd hcdf_meas hcdf_bound

/--
Appendix C, Theorem 7: canonical product probability space for two independent
Laplace scores with common scale parameter `lam` and means `x_i`, `x_j`.
-/
noncomputable def theorem7LaplacianPairMeasure
    (lam xi xj : ℝ) : Measure (ℝ × ℝ) :=
  (theorem7LaplaceMeasure lam xi).prod (theorem7LaplaceMeasure lam xj)

/--
Appendix C, Theorem 7: numerator event for the canonical product bridge,
written with weak inequalities.  For continuous Laplace densities this agrees
in measure with the strict paper event `X_i > X_j, X_i < a, X_j < a`.
-/
def theorem7LaplacianPairNumeratorEvent (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ a ∧ p.2 ≤ p.1}

/-- Appendix C, Theorem 7: conditioning event for the product bridge. -/
def theorem7LaplacianPairDenominatorEvent (a : ℝ) : Set (ℝ × ℝ) :=
  Set.Iic a ×ˢ Set.Iic a

/-- Appendix C, Theorem 7: unconditional pairwise winner event. -/
def theorem7LaplacianPairWinnerEvent : Set (ℝ × ℝ) := {p | p.2 ≤ p.1}

/--
Appendix C, Theorem 7: conditioning event where the first coordinate is
strictly below the cutoff and the second is weakly below it.
-/
def theorem7LaplacianPairLeftStrictDenominatorEvent (a : ℝ) : Set (ℝ × ℝ) :=
  Set.Iio a ×ˢ Set.Iic a

/--
Appendix C, Theorem 7: numerator event in the strict paper syntax,
`X_i < a`, `X_j < X_i`.
-/
def theorem7LaplacianPairStrictNumeratorEvent (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 < a ∧ p.2 < p.1}

/--
Appendix C, Theorem 7: strict conditioning event in the paper syntax,
`X_i < a`, `X_j < a`.
-/
def theorem7LaplacianPairStrictDenominatorEvent (a : ℝ) : Set (ℝ × ℝ) :=
  Set.Iio a ×ˢ Set.Iio a

/-- Appendix C, Theorem 7: measurability of the product-bridge numerator. -/
theorem theorem7LaplacianPairNumeratorEvent_measurable (a : ℝ) :
    MeasurableSet (theorem7LaplacianPairNumeratorEvent a) := by
  unfold theorem7LaplacianPairNumeratorEvent
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_snd measurable_fst)

/-- Appendix C, Theorem 7: measurability of the unconditional pairwise winner event. -/
theorem theorem7LaplacianPairWinnerEvent_measurable :
    MeasurableSet theorem7LaplacianPairWinnerEvent := by
  unfold theorem7LaplacianPairWinnerEvent
  exact measurableSet_le measurable_snd measurable_fst

/--
Appendix C, Theorem 7: measurability of the strict paper-syntax numerator.
-/
theorem theorem7LaplacianPairStrictNumeratorEvent_measurable (a : ℝ) :
    MeasurableSet (theorem7LaplacianPairStrictNumeratorEvent a) := by
  unfold theorem7LaplacianPairStrictNumeratorEvent
  exact (measurableSet_lt measurable_fst measurable_const).inter
    (measurableSet_lt measurable_snd measurable_fst)

/--
Appendix C, Theorem 7: Tonelli/product-measure form of the numerator event.
-/
theorem theorem7LaplacianPairNumerator_measure_eq_lintegral
    (lam xi xj a : ℝ) :
    theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairNumeratorEvent a) =
      ∫⁻ x in Set.Iic a,
        theorem7LaplaceMeasure lam xj (Set.Iic x)
        ∂theorem7LaplaceMeasure lam xi := by
  let μi := theorem7LaplaceMeasure lam xi
  let μj := theorem7LaplaceMeasure lam xj
  haveI : SFinite μi := by
    dsimp [μi, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μj := by
    dsimp [μj, theorem7LaplaceMeasure]
    infer_instance
  have hmeas := theorem7LaplacianPairNumeratorEvent_measurable a
  unfold theorem7LaplacianPairMeasure
  change μi.prod μj (theorem7LaplacianPairNumeratorEvent a) =
    ∫⁻ x in Set.Iic a, μj (Set.Iic x) ∂μi
  rw [Measure.prod_apply hmeas]
  rw [← lintegral_indicator measurableSet_Iic]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ≤ a
  · have hsection :
        Prod.mk x ⁻¹' theorem7LaplacianPairNumeratorEvent a = Set.Iic x := by
        ext y
        simp [theorem7LaplacianPairNumeratorEvent, hx]
    simp [hsection, hx]
  · have hsection :
        Prod.mk x ⁻¹' theorem7LaplacianPairNumeratorEvent a =
          (∅ : Set ℝ) := by
        ext y
        simp [theorem7LaplacianPairNumeratorEvent, hx]
    have hxnot : x ∉ Set.Iic a := by
      simpa using hx
    simp [hsection, hxnot]

/--
Appendix C, Theorem 7: Fubini/density bridge from the product numerator event
to the paper's one-dimensional Laplace density/CDF integral.
-/
theorem theorem7LaplacianPairNumerator_measure_eq_integral
    {lam xi xj a : ℝ} (hlam : 0 < lam) :
    theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairNumeratorEvent a) =
      ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          theorem7LaplacianPairIntegrand lam xi xj x) := by
  let μi := theorem7LaplaceMeasure lam xi
  let μj := theorem7LaplaceMeasure lam xj
  have h_int :=
    theorem7LaplacianPairIntegrand_integrableOn_Iic
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam
  have h_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Iic a)]
        (fun x : ℝ => theorem7LaplacianPairIntegrand lam xi xj x) := by
    refine ae_of_all _ fun x => ?_
    unfold theorem7LaplacianPairIntegrand
    exact mul_nonneg
      (theorem7LaplacePDF_nonneg
        (lam := lam) (μ := xi) (x := x) (le_of_lt hlam))
      (theorem7LaplaceCDFClosedForm_nonneg
        (lam := lam) (μ := xj) (a := x) hlam)
  calc
    theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairNumeratorEvent a)
        = ∫⁻ x in Set.Iic a, μj (Set.Iic x) ∂μi := by
          simpa [μi, μj] using
            theorem7LaplacianPairNumerator_measure_eq_lintegral lam xi xj a
    _ = ∫⁻ x in Set.Iic a,
          ENNReal.ofReal (theorem7LaplaceCDFClosedForm lam xj x) ∂μi := by
          refine setLIntegral_congr_fun measurableSet_Iic ?_
          intro x _hx
          exact theorem7LaplaceMeasure_Iic_eq_CDF
            (lam := lam) (μ := xj) (a := x) hlam
    _ = ∫⁻ x in Set.Iic a,
          ENNReal.ofReal (theorem7LaplacePDF lam xi x) *
            ENNReal.ofReal (theorem7LaplaceCDFClosedForm lam xj x) := by
          dsimp [μi]
          unfold theorem7LaplaceMeasure
          exact setLIntegral_withDensity_eq_setLIntegral_mul volume
            ((theorem7LaplacePDF_continuous lam xi).measurable.ennreal_ofReal)
            ((theorem7LaplaceCDFClosedForm_measurable lam xj).ennreal_ofReal)
            measurableSet_Iic
    _ = ∫⁻ x in Set.Iic a,
          ENNReal.ofReal (theorem7LaplacianPairIntegrand lam xi xj x) := by
          refine setLIntegral_congr_fun measurableSet_Iic ?_
          intro x _hx
          unfold theorem7LaplacianPairIntegrand
          change
            ENNReal.ofReal (theorem7LaplacePDF lam xi x) *
                ENNReal.ofReal (theorem7LaplaceCDFClosedForm lam xj x) =
              ENNReal.ofReal
                (theorem7LaplacePDF lam xi x *
                  theorem7LaplaceCDFClosedForm lam xj x)
          rw [ENNReal.ofReal_mul
            (theorem7LaplacePDF_nonneg
              (lam := lam) (μ := xi) (x := x) (le_of_lt hlam))]
    _ = ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          theorem7LaplacianPairIntegrand lam xi xj x) := by
          simpa using
            (ofReal_integral_eq_lintegral_ofReal
              (μ := volume.restrict (Set.Iic a)) h_int h_nonneg).symm

/--
Appendix C, Theorem 7: Tonelli/product-measure form of the strict
paper-syntax numerator event.
-/
theorem theorem7LaplacianPairStrictNumerator_measure_eq_lintegral
    (lam xi xj a : ℝ) :
    theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairStrictNumeratorEvent a) =
      ∫⁻ x in Set.Iio a,
        theorem7LaplaceMeasure lam xj (Set.Iio x)
        ∂theorem7LaplaceMeasure lam xi := by
  let μi := theorem7LaplaceMeasure lam xi
  let μj := theorem7LaplaceMeasure lam xj
  haveI : SFinite μi := by
    dsimp [μi, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μj := by
    dsimp [μj, theorem7LaplaceMeasure]
    infer_instance
  have hmeas := theorem7LaplacianPairStrictNumeratorEvent_measurable a
  unfold theorem7LaplacianPairMeasure
  change μi.prod μj (theorem7LaplacianPairStrictNumeratorEvent a) =
    ∫⁻ x in Set.Iio a, μj (Set.Iio x) ∂μi
  rw [Measure.prod_apply hmeas]
  rw [← lintegral_indicator measurableSet_Iio]
  refine lintegral_congr fun x => ?_
  by_cases hx : x < a
  · have hsection :
        Prod.mk x ⁻¹' theorem7LaplacianPairStrictNumeratorEvent a = Set.Iio x := by
        ext y
        simp [theorem7LaplacianPairStrictNumeratorEvent, hx]
    simp [hsection, hx]
  · have hsection :
        Prod.mk x ⁻¹' theorem7LaplacianPairStrictNumeratorEvent a =
          (∅ : Set ℝ) := by
        ext y
        simp [theorem7LaplacianPairStrictNumeratorEvent, hx]
    have hxnot : x ∉ Set.Iio a := by
      simpa using hx
    simp [hsection, hxnot]

/--
Appendix C, Theorem 7: strict paper-syntax numerator has the same mass as the
weak bridge numerator, hence the same Laplace density/CDF integral.
-/
theorem theorem7LaplacianPairStrictNumerator_measure_eq_integral
    {lam xi xj a : ℝ} (hlam : 0 < lam) :
    theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairStrictNumeratorEvent a) =
      ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          theorem7LaplacianPairIntegrand lam xi xj x) := by
  let μi := theorem7LaplaceMeasure lam xi
  let μj := theorem7LaplaceMeasure lam xj
  haveI : NoAtoms μi := by
    dsimp [μi, theorem7LaplaceMeasure]
    infer_instance
  calc
    theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairStrictNumeratorEvent a)
        = ∫⁻ x in Set.Iio a, μj (Set.Iio x) ∂μi := by
          simpa [μi, μj] using
            theorem7LaplacianPairStrictNumerator_measure_eq_lintegral lam xi xj a
    _ = ∫⁻ x in Set.Iio a, μj (Set.Iic x) ∂μi := by
          refine setLIntegral_congr_fun measurableSet_Iio ?_
          intro x _hx
          exact theorem7LaplaceMeasure_Iio_eq_Iic lam xj x
    _ = ∫⁻ x in Set.Iic a, μj (Set.Iic x) ∂μi :=
          setLIntegral_congr
            (μ := μi) (f := fun x : ℝ => μj (Set.Iic x))
            (Iio_ae_eq_Iic (μ := μi) (a := a))
    _ = theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairNumeratorEvent a) := by
          simpa [μi, μj] using
            (theorem7LaplacianPairNumerator_measure_eq_lintegral lam xi xj a).symm
    _ = ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          theorem7LaplacianPairIntegrand lam xi xj x) :=
          theorem7LaplacianPairNumerator_measure_eq_integral
            (lam := lam) (xi := xi) (xj := xj) (a := a) hlam

/--
Appendix C, Theorem 7: product-measure mass of the conditioning event.
-/
theorem theorem7LaplacianPairDenominator_measure_eq
    {lam xi xj a : ℝ} (hlam : 0 < lam) :
    theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairDenominatorEvent a) =
      ENNReal.ofReal
        (theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a) := by
  haveI : SFinite (theorem7LaplaceMeasure lam xi) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  haveI : SFinite (theorem7LaplaceMeasure lam xj) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  unfold theorem7LaplacianPairMeasure theorem7LaplacianPairDenominatorEvent
  rw [Measure.prod_prod]
  rw [theorem7LaplaceMeasure_Iic_eq_CDF (lam := lam) (μ := xi) (a := a) hlam,
    theorem7LaplaceMeasure_Iic_eq_CDF (lam := lam) (μ := xj) (a := a) hlam]
  rw [← ENNReal.ofReal_mul
    (theorem7LaplaceCDFClosedForm_nonneg
      (lam := lam) (μ := xi) (a := a) hlam)]

/--
Appendix C, Theorem 7: product-measure mass of the strict paper-syntax
conditioning event.
-/
theorem theorem7LaplacianPairStrictDenominator_measure_eq
    {lam xi xj a : ℝ} (hlam : 0 < lam) :
    theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairStrictDenominatorEvent a) =
      ENNReal.ofReal
        (theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a) := by
  haveI : SFinite (theorem7LaplaceMeasure lam xi) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  haveI : SFinite (theorem7LaplaceMeasure lam xj) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  unfold theorem7LaplacianPairMeasure theorem7LaplacianPairStrictDenominatorEvent
  rw [Measure.prod_prod]
  rw [theorem7LaplaceMeasure_Iio_eq_Iic lam xi a,
    theorem7LaplaceMeasure_Iio_eq_Iic lam xj a]
  rw [theorem7LaplaceMeasure_Iic_eq_CDF (lam := lam) (μ := xi) (a := a) hlam,
    theorem7LaplaceMeasure_Iic_eq_CDF (lam := lam) (μ := xj) (a := a) hlam]
  rw [← ENNReal.ofReal_mul
    (theorem7LaplaceCDFClosedForm_nonneg
      (lam := lam) (μ := xi) (a := a) hlam)]

/--
Appendix C, Theorem 7: making only the first coordinate cutoff strict does not
change the Laplace product mass.
-/
theorem theorem7LaplacianPairLeftStrictDenominator_measure_eq_denominator
    (lam xi xj a : ℝ) :
    theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairLeftStrictDenominatorEvent a) =
      theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairDenominatorEvent a) := by
  haveI : SFinite (theorem7LaplaceMeasure lam xi) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  haveI : SFinite (theorem7LaplaceMeasure lam xj) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  unfold theorem7LaplacianPairMeasure
    theorem7LaplacianPairLeftStrictDenominatorEvent
    theorem7LaplacianPairDenominatorEvent
  rw [Measure.prod_prod, Measure.prod_prod]
  rw [theorem7LaplaceMeasure_Iio_eq_Iic lam xi a]

/--
Appendix C, Theorem 7: making both cutoff inequalities strict does not change
the Laplace product mass.
-/
theorem theorem7LaplacianPairStrictDenominator_measure_eq_denominator
    (lam xi xj a : ℝ) :
    theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairStrictDenominatorEvent a) =
      theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairDenominatorEvent a) := by
  haveI : SFinite (theorem7LaplaceMeasure lam xi) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  haveI : SFinite (theorem7LaplaceMeasure lam xj) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  unfold theorem7LaplacianPairMeasure
    theorem7LaplacianPairStrictDenominatorEvent
    theorem7LaplacianPairDenominatorEvent
  rw [Measure.prod_prod, Measure.prod_prod]
  rw [theorem7LaplaceMeasure_Iio_eq_Iic lam xi a,
    theorem7LaplaceMeasure_Iio_eq_Iic lam xj a]

/--
Appendix C, Theorem 7: canonical product-probability conditional ratio
corresponding to the source expression
`Pr[X_i > X_j | X_i < a, X_j < a]`, stated with weak inequalities on null
boundaries.
-/
noncomputable def theorem7LaplacianProductConditionalRatioAt
    (lam xi xj a : ℝ) : ℝ :=
  (theorem7LaplacianPairMeasure lam xi xj
      (theorem7LaplacianPairNumeratorEvent a)).toReal /
    (theorem7LaplacianPairMeasure lam xi xj
      (theorem7LaplacianPairDenominatorEvent a)).toReal

/--
Appendix C, Theorem 7: canonical product-probability conditional ratio in the
paper's strict event syntax.
-/
noncomputable def theorem7LaplacianProductStrictConditionalRatioAt
    (lam xi xj a : ℝ) : ℝ :=
  (theorem7LaplacianPairMeasure lam xi xj
      (theorem7LaplacianPairStrictNumeratorEvent a)).toReal /
    (theorem7LaplacianPairMeasure lam xi xj
      (theorem7LaplacianPairStrictDenominatorEvent a)).toReal

/-- Appendix C, Theorem 7: the paper's density/CDF integral ratio. -/
noncomputable def theorem7LaplacianPDFCDFRatioAt
    (lam xi xj a : ℝ) : ℝ :=
  (∫ x : ℝ in Set.Iic a,
      theorem7LaplacianPairIntegrand lam xi xj x) /
    (theorem7LaplaceCDFClosedForm lam xi a *
      theorem7LaplaceCDFClosedForm lam xj a)

/--
Appendix C, Theorem 7: the canonical product-probability ratio equals the
paper's Laplace density/CDF ratio.
-/
theorem theorem7LaplacianProductConditionalRatioAt_eq_pdf_cdf
    {lam xi xj a : ℝ} (hlam : 0 < lam) :
    theorem7LaplacianProductConditionalRatioAt lam xi xj a =
      theorem7LaplacianPDFCDFRatioAt lam xi xj a := by
  have hI_nonneg :
      0 ≤
        (∫ x : ℝ in Set.Iic a,
          theorem7LaplacianPairIntegrand lam xi xj x) := by
    refine integral_nonneg fun x => ?_
    unfold theorem7LaplacianPairIntegrand
    exact mul_nonneg
      (theorem7LaplacePDF_nonneg
        (lam := lam) (μ := xi) (x := x) (le_of_lt hlam))
      (theorem7LaplaceCDFClosedForm_nonneg
        (lam := lam) (μ := xj) (a := x) hlam)
  have hden_nonneg :
      0 ≤ theorem7LaplaceCDFClosedForm lam xi a *
        theorem7LaplaceCDFClosedForm lam xj a :=
    mul_nonneg
      (theorem7LaplaceCDFClosedForm_nonneg
        (lam := lam) (μ := xi) (a := a) hlam)
      (theorem7LaplaceCDFClosedForm_nonneg
        (lam := lam) (μ := xj) (a := a) hlam)
  unfold theorem7LaplacianProductConditionalRatioAt
    theorem7LaplacianPDFCDFRatioAt
  rw [theorem7LaplacianPairNumerator_measure_eq_integral (hlam := hlam),
    theorem7LaplacianPairDenominator_measure_eq (hlam := hlam)]
  rw [ENNReal.toReal_ofReal hI_nonneg, ENNReal.toReal_ofReal hden_nonneg]

/--
Appendix C, Theorem 7: the strict paper-syntax product-probability ratio equals
the paper's Laplace density/CDF ratio.
-/
theorem theorem7LaplacianProductStrictConditionalRatioAt_eq_pdf_cdf
    {lam xi xj a : ℝ} (hlam : 0 < lam) :
    theorem7LaplacianProductStrictConditionalRatioAt lam xi xj a =
      theorem7LaplacianPDFCDFRatioAt lam xi xj a := by
  have hI_nonneg :
      0 ≤
        (∫ x : ℝ in Set.Iic a,
          theorem7LaplacianPairIntegrand lam xi xj x) := by
    refine integral_nonneg fun x => ?_
    unfold theorem7LaplacianPairIntegrand
    exact mul_nonneg
      (theorem7LaplacePDF_nonneg
        (lam := lam) (μ := xi) (x := x) (le_of_lt hlam))
      (theorem7LaplaceCDFClosedForm_nonneg
        (lam := lam) (μ := xj) (a := x) hlam)
  have hden_nonneg :
      0 ≤ theorem7LaplaceCDFClosedForm lam xi a *
        theorem7LaplaceCDFClosedForm lam xj a :=
    mul_nonneg
      (theorem7LaplaceCDFClosedForm_nonneg
        (lam := lam) (μ := xi) (a := a) hlam)
      (theorem7LaplaceCDFClosedForm_nonneg
        (lam := lam) (μ := xj) (a := a) hlam)
  unfold theorem7LaplacianProductStrictConditionalRatioAt
    theorem7LaplacianPDFCDFRatioAt
  rw [theorem7LaplacianPairStrictNumerator_measure_eq_integral (hlam := hlam),
    theorem7LaplacianPairStrictDenominator_measure_eq (hlam := hlam)]
  rw [ENNReal.toReal_ofReal hI_nonneg, ENNReal.toReal_ofReal hden_nonneg]

/-!
The preceding product-measure bridge gives the literal conditional probability
ratio.  The next lemmas connect that ratio to the three split integrals used in
the paper's Appendix C derivative proof.
-/

/-- Appendix C, Theorem 7: the density/CDF ratio is the case-1 ratio by definition. -/
theorem theorem7LaplacianPDFCDFRatioAt_eq_case1
    (lam xi xj a : ℝ) :
    theorem7LaplacianPDFCDFRatioAt lam xi xj a =
      theorem7LaplacianCase1IntegralRatio lam xi xj a := by
  rfl

/--
Appendix C, Theorem 7: on and above the first split point, the full
left-half-line density/CDF integral is the sum of the case-2 pieces.
-/
theorem theorem7LaplacianPDFCDFRatioAt_eq_case2
    {lam xi xj a : ℝ} (hlam : 0 < lam) (ha : xj ≤ a) :
    theorem7LaplacianPDFCDFRatioAt lam xi xj a =
      theorem7LaplacianCase2IntegralRatio lam xi xj a := by
  let f : ℝ → ℝ := theorem7LaplacianPairIntegrand lam xi xj
  have hxj_int :
      IntegrableOn f (Set.Iic xj) := by
    simpa [f] using
      theorem7LaplacianPairIntegrand_integrableOn_Iic
        (lam := lam) (xi := xi) (xj := xj) (a := xj) hlam
  have ha_int :
      IntegrableOn f (Set.Iic a) := by
    simpa [f] using
      theorem7LaplacianPairIntegrand_integrableOn_Iic
        (lam := lam) (xi := xi) (xj := xj) (a := a) hlam
  have hsub :
      (∫ x : ℝ in Set.Iic a, f x) -
          ∫ x : ℝ in Set.Iic xj, f x =
        ∫ x : ℝ in xj..a, f x := by
    simpa using
      (intervalIntegral.integral_Iic_sub_Iic
        (f := f) (a := xj) (b := a) hxj_int ha_int)
  have hsplit :
      (∫ x : ℝ in Set.Iic a, f x) =
          (∫ x : ℝ in Set.Iic xj, f x) + (∫ x : ℝ in xj..a, f x) := by
    calc
      (∫ x : ℝ in Set.Iic a, f x)
          = ((∫ x : ℝ in Set.Iic a, f x) -
              ∫ x : ℝ in Set.Iic xj, f x) +
              ∫ x : ℝ in Set.Iic xj, f x := by ring
      _ = (∫ x : ℝ in xj..a, f x) +
              ∫ x : ℝ in Set.Iic xj, f x := by rw [hsub]
      _ = (∫ x : ℝ in Set.Iic xj, f x) +
              (∫ x : ℝ in xj..a, f x) := by ring
  unfold theorem7LaplacianPDFCDFRatioAt theorem7LaplacianCase2IntegralRatio
  dsimp [f] at hsplit ⊢
  rw [hsplit]

/--
Appendix C, Theorem 7: on and above the second split point, the full
left-half-line density/CDF integral is the sum of the case-3 pieces.
-/
theorem theorem7LaplacianPDFCDFRatioAt_eq_case3
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj ≤ xi) (ha : xi ≤ a) :
    theorem7LaplacianPDFCDFRatioAt lam xi xj a =
      theorem7LaplacianCase3IntegralRatio lam xi xj a := by
  let f : ℝ → ℝ := theorem7LaplacianPairIntegrand lam xi xj
  have hxj_int :
      IntegrableOn f (Set.Iic xj) := by
    simpa [f] using
      theorem7LaplacianPairIntegrand_integrableOn_Iic
        (lam := lam) (xi := xi) (xj := xj) (a := xj) hlam
  have hxi_int :
      IntegrableOn f (Set.Iic xi) := by
    simpa [f] using
      theorem7LaplacianPairIntegrand_integrableOn_Iic
        (lam := lam) (xi := xi) (xj := xj) (a := xi) hlam
  have ha_int :
      IntegrableOn f (Set.Iic a) := by
    simpa [f] using
      theorem7LaplacianPairIntegrand_integrableOn_Iic
        (lam := lam) (xi := xi) (xj := xj) (a := a) hlam
  have hsub_xj_xi :
      (∫ x : ℝ in Set.Iic xi, f x) -
          ∫ x : ℝ in Set.Iic xj, f x =
        ∫ x : ℝ in xj..xi, f x := by
    simpa using
      (intervalIntegral.integral_Iic_sub_Iic
        (f := f) (a := xj) (b := xi) hxj_int hxi_int)
  have hsub_xi_a :
      (∫ x : ℝ in Set.Iic a, f x) -
          ∫ x : ℝ in Set.Iic xi, f x =
        ∫ x : ℝ in xi..a, f x := by
    simpa using
      (intervalIntegral.integral_Iic_sub_Iic
        (f := f) (a := xi) (b := a) hxi_int ha_int)
  have hsplit_xj_xi :
      (∫ x : ℝ in Set.Iic xi, f x) =
          (∫ x : ℝ in Set.Iic xj, f x) + (∫ x : ℝ in xj..xi, f x) := by
    calc
      (∫ x : ℝ in Set.Iic xi, f x)
          = ((∫ x : ℝ in Set.Iic xi, f x) -
              ∫ x : ℝ in Set.Iic xj, f x) +
              ∫ x : ℝ in Set.Iic xj, f x := by ring
      _ = (∫ x : ℝ in xj..xi, f x) +
              ∫ x : ℝ in Set.Iic xj, f x := by rw [hsub_xj_xi]
      _ = (∫ x : ℝ in Set.Iic xj, f x) +
              (∫ x : ℝ in xj..xi, f x) := by ring
  have hsplit :
      (∫ x : ℝ in Set.Iic a, f x) =
          ((∫ x : ℝ in Set.Iic xj, f x) + (∫ x : ℝ in xj..xi, f x)) +
            (∫ x : ℝ in xi..a, f x) := by
    calc
      (∫ x : ℝ in Set.Iic a, f x)
          = ((∫ x : ℝ in Set.Iic a, f x) -
              ∫ x : ℝ in Set.Iic xi, f x) +
              ∫ x : ℝ in Set.Iic xi, f x := by ring
      _ = (∫ x : ℝ in xi..a, f x) +
              ∫ x : ℝ in Set.Iic xi, f x := by rw [hsub_xi_a]
      _ = ((∫ x : ℝ in Set.Iic xj, f x) +
              (∫ x : ℝ in xj..xi, f x)) +
              (∫ x : ℝ in xi..a, f x) := by
            rw [hsplit_xj_xi]
            ring
  unfold theorem7LaplacianPDFCDFRatioAt theorem7LaplacianCase3IntegralRatio
  dsimp [f] at hsplit ⊢
  rw [hsplit]

/--
Appendix C, Theorem 7: derivative cases for the literal density/CDF ratio
appearing in the product probability bridge.
-/
theorem theorem7LaplacianPDFCDFRatioAt_derivative_cases
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (a < xj →
      HasDerivAt
          (fun a => theorem7LaplacianPDFCDFRatioAt lam xi xj a) 0 a ∧
        0 ≤ (0 : ℝ)) ∧
    (xj < a → a < xi →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianPDFCDFRatioAt lam xi xj a) d a ∧
          0 < d) ∧
    (xi < a →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianPDFCDFRatioAt lam xi xj a) d a ∧
          0 < d) ∧
    (∃ a d,
      xj < a ∧ a < xi ∧
        HasDerivAt
          (fun a => theorem7LaplacianPDFCDFRatioAt lam xi xj a) d a ∧
        0 < d) := by
  obtain ⟨hcase1, hcase2, hcase3, hwitness⟩ :=
    paper_theorem7_laplacian_integralRatio_derivative_cases
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hleft
    obtain ⟨hd, hdnonneg⟩ := hcase1 hleft
    refine ⟨?_, hdnonneg⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => by
        exact (theorem7LaplacianPDFCDFRatioAt_eq_case1 lam xi xj u).symm)
  · intro hleft hright
    obtain ⟨d, hd, hdpos⟩ := hcase2 hleft hright
    refine ⟨d, ?_, hdpos⟩
    have hnear : ∀ᶠ u in nhds a, u ∈ Set.Ioi xj :=
      isOpen_Ioi.mem_nhds (show a ∈ Set.Ioi xj by exact hleft)
    exact hd.congr_of_eventuallyEq
      (hnear.mono fun u hu => by
        exact theorem7LaplacianPDFCDFRatioAt_eq_case2
          (lam := lam) (xi := xi) (xj := xj) (a := u)
          hlam (le_of_lt hu))
  · intro hright
    obtain ⟨d, hd, hdpos⟩ := hcase3 hright
    refine ⟨d, ?_, hdpos⟩
    have hnear : ∀ᶠ u in nhds a, u ∈ Set.Ioi xi :=
      isOpen_Ioi.mem_nhds (show a ∈ Set.Ioi xi by exact hright)
    exact hd.congr_of_eventuallyEq
      (hnear.mono fun u hu => by
        exact theorem7LaplacianPDFCDFRatioAt_eq_case3
          (lam := lam) (xi := xi) (xj := xj) (a := u)
          hlam (le_of_lt hx) (le_of_lt hu))
  · obtain ⟨amid, d, hleft, hright, hd, hdpos⟩ := hwitness
    refine ⟨amid, d, hleft, hright, ?_, hdpos⟩
    have hnear : ∀ᶠ u in nhds amid, u ∈ Set.Ioi xj :=
      isOpen_Ioi.mem_nhds (show amid ∈ Set.Ioi xj by exact hleft)
    exact hd.congr_of_eventuallyEq
      (hnear.mono fun u hu => by
        exact theorem7LaplacianPDFCDFRatioAt_eq_case2
          (lam := lam) (xi := xi) (xj := xj) (a := u)
          hlam (le_of_lt hu))

/--
Appendix C, Theorem 7: derivative cases for the canonical product-probability
conditional ratio with weak boundary syntax.
-/
theorem theorem7LaplacianProductConditionalRatioAt_derivative_cases
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (a < xj →
      HasDerivAt
          (fun a => theorem7LaplacianProductConditionalRatioAt lam xi xj a) 0 a ∧
        0 ≤ (0 : ℝ)) ∧
    (xj < a → a < xi →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianProductConditionalRatioAt lam xi xj a) d a ∧
          0 < d) ∧
    (xi < a →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianProductConditionalRatioAt lam xi xj a) d a ∧
          0 < d) ∧
    (∃ a d,
      xj < a ∧ a < xi ∧
        HasDerivAt
          (fun a => theorem7LaplacianProductConditionalRatioAt lam xi xj a) d a ∧
        0 < d) := by
  obtain ⟨hcase1, hcase2, hcase3, hwitness⟩ :=
    theorem7LaplacianPDFCDFRatioAt_derivative_cases
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hleft
    obtain ⟨hd, hdnonneg⟩ := hcase1 hleft
    refine ⟨?_, hdnonneg⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        theorem7LaplacianProductConditionalRatioAt_eq_pdf_cdf
          (lam := lam) (xi := xi) (xj := xj) (a := u) hlam)
  · intro hleft hright
    obtain ⟨d, hd, hdpos⟩ := hcase2 hleft hright
    refine ⟨d, ?_, hdpos⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        theorem7LaplacianProductConditionalRatioAt_eq_pdf_cdf
          (lam := lam) (xi := xi) (xj := xj) (a := u) hlam)
  · intro hright
    obtain ⟨d, hd, hdpos⟩ := hcase3 hright
    refine ⟨d, ?_, hdpos⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        theorem7LaplacianProductConditionalRatioAt_eq_pdf_cdf
          (lam := lam) (xi := xi) (xj := xj) (a := u) hlam)
  · obtain ⟨amid, d, hleft, hright, hd, hdpos⟩ := hwitness
    refine ⟨amid, d, hleft, hright, ?_, hdpos⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        theorem7LaplacianProductConditionalRatioAt_eq_pdf_cdf
          (lam := lam) (xi := xi) (xj := xj) (a := u) hlam)

/--
Appendix C, Theorem 7: derivative cases for the product-probability
conditional ratio in the paper's strict event syntax.
-/
theorem theorem7LaplacianProductStrictConditionalRatioAt_derivative_cases
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (a < xj →
      HasDerivAt
          (fun a => theorem7LaplacianProductStrictConditionalRatioAt lam xi xj a) 0 a ∧
        0 ≤ (0 : ℝ)) ∧
    (xj < a → a < xi →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianProductStrictConditionalRatioAt lam xi xj a) d a ∧
          0 < d) ∧
    (xi < a →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianProductStrictConditionalRatioAt lam xi xj a) d a ∧
          0 < d) ∧
    (∃ a d,
      xj < a ∧ a < xi ∧
        HasDerivAt
          (fun a => theorem7LaplacianProductStrictConditionalRatioAt lam xi xj a) d a ∧
        0 < d) := by
  obtain ⟨hcase1, hcase2, hcase3, hwitness⟩ :=
    theorem7LaplacianPDFCDFRatioAt_derivative_cases
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hleft
    obtain ⟨hd, hdnonneg⟩ := hcase1 hleft
    refine ⟨?_, hdnonneg⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        theorem7LaplacianProductStrictConditionalRatioAt_eq_pdf_cdf
          (lam := lam) (xi := xi) (xj := xj) (a := u) hlam)
  · intro hleft hright
    obtain ⟨d, hd, hdpos⟩ := hcase2 hleft hright
    refine ⟨d, ?_, hdpos⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        theorem7LaplacianProductStrictConditionalRatioAt_eq_pdf_cdf
          (lam := lam) (xi := xi) (xj := xj) (a := u) hlam)
  · intro hright
    obtain ⟨d, hd, hdpos⟩ := hcase3 hright
    refine ⟨d, ?_, hdpos⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        theorem7LaplacianProductStrictConditionalRatioAt_eq_pdf_cdf
          (lam := lam) (xi := xi) (xj := xj) (a := u) hlam)
  · obtain ⟨amid, d, hleft, hright, hd, hdpos⟩ := hwitness
    refine ⟨amid, d, hleft, hright, ?_, hdpos⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        theorem7LaplacianProductStrictConditionalRatioAt_eq_pdf_cdf
          (lam := lam) (xi := xi) (xj := xj) (a := u) hlam)

/--
Appendix C, Theorem 7: monotone-limit consequence for the Laplacian cutoff
ratio.  Because the Laplacian ratio is flat in the far-left region, the useful
condition is not global strict monotonicity but monotonicity plus a strict
increase somewhere to the right of the cutoff.
-/
theorem theorem7LaplacianProductStrictConditionalRatioAt_lt_of_monotone_tendsto_atTop
    {lam xi xj L a : ℝ}
    (hmono : Monotone fun u =>
      theorem7LaplacianProductStrictConditionalRatioAt lam xi xj u)
    (hstrict :
      ∃ b : ℝ, a < b ∧
        theorem7LaplacianProductStrictConditionalRatioAt lam xi xj a <
          theorem7LaplacianProductStrictConditionalRatioAt lam xi xj b)
    (hlim :
      Filter.Tendsto
        (fun u => theorem7LaplacianProductStrictConditionalRatioAt lam xi xj u)
        Filter.atTop (nhds L)) :
    theorem7LaplacianProductStrictConditionalRatioAt lam xi xj a < L :=
  monotone_lt_tendsto_atTop_limit_of_exists_strict_right
    (f := fun u => theorem7LaplacianProductStrictConditionalRatioAt lam xi xj u)
    hmono hlim hstrict

/--
Appendix C, Theorem 7: the weak-boundary Laplacian conditional pairwise ratio
tends to the unconditional pairwise win probability as the cutoff tends to
`+∞`.
-/
theorem theorem7LaplacianProductConditionalRatioAt_tendsto_atTop_winner
    {lam xi xj : ℝ} (hlam : 0 < lam) :
    Filter.Tendsto
      (fun a => theorem7LaplacianProductConditionalRatioAt lam xi xj a)
      Filter.atTop
      (nhds ((theorem7LaplacianPairMeasure lam xi xj
        theorem7LaplacianPairWinnerEvent).toReal)) := by
  let μpair := theorem7LaplacianPairMeasure lam xi xj
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam xi) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := xi) hlam⟩
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam xj) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := xj) hlam⟩
  haveI : IsProbabilityMeasure μpair := by
    dsimp [μpair, theorem7LaplacianPairMeasure]
    infer_instance
  have hnum_mono : Monotone fun a : ℝ =>
      theorem7LaplacianPairNumeratorEvent a := by
    intro a b hab p hp
    exact ⟨hp.1.trans hab, hp.2⟩
  have hnum_iUnion :
      (⋃ a : ℝ, theorem7LaplacianPairNumeratorEvent a) =
        theorem7LaplacianPairWinnerEvent := by
    ext p
    constructor
    · intro hp
      rcases Set.mem_iUnion.mp hp with ⟨a, ha⟩
      exact ha.2
    · intro hp
      exact Set.mem_iUnion.mpr
        ⟨p.1, by
          exact ⟨le_rfl, hp⟩⟩
  have hnum_enn :
      Filter.Tendsto
        (fun a : ℝ => μpair (theorem7LaplacianPairNumeratorEvent a))
        Filter.atTop
        (nhds (μpair theorem7LaplacianPairWinnerEvent)) := by
    have hcont :=
      MeasureTheory.tendsto_measure_iUnion_atTop
        (μ := μpair) hnum_mono
    simpa [Function.comp_def, hnum_iUnion] using hcont
  have hnum :
      Filter.Tendsto
        (fun a : ℝ =>
          (theorem7LaplacianPairMeasure lam xi xj
            (theorem7LaplacianPairNumeratorEvent a)).toReal)
        Filter.atTop
        (nhds ((theorem7LaplacianPairMeasure lam xi xj
          theorem7LaplacianPairWinnerEvent).toReal)) := by
    simpa [μpair] using
      (ENNReal.tendsto_toReal
        (measure_ne_top μpair theorem7LaplacianPairWinnerEvent)).comp hnum_enn
  have hden_real :
      Filter.Tendsto
        (fun a : ℝ =>
          theorem7LaplaceCDFClosedForm lam xi a *
            theorem7LaplaceCDFClosedForm lam xj a)
        Filter.atTop (nhds (1 : ℝ)) := by
    have hi :=
      theorem7LaplaceCDFClosedForm_tendsto_atTop_one
        (lam := lam) (μ := xi) hlam
    have hj :=
      theorem7LaplaceCDFClosedForm_tendsto_atTop_one
        (lam := lam) (μ := xj) hlam
    simpa [show (1 : ℝ) * 1 = 1 by norm_num] using hi.mul hj
  have hden :
      Filter.Tendsto
        (fun a : ℝ =>
          (theorem7LaplacianPairMeasure lam xi xj
            (theorem7LaplacianPairDenominatorEvent a)).toReal)
        Filter.atTop (nhds (1 : ℝ)) := by
    refine hden_real.congr' ?_
    filter_upwards with a
    rw [theorem7LaplacianPairDenominator_measure_eq
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam]
    exact (ENNReal.toReal_ofReal
      (mul_nonneg
        (theorem7LaplaceCDFClosedForm_nonneg
          (lam := lam) (μ := xi) (a := a) hlam)
        (theorem7LaplaceCDFClosedForm_nonneg
          (lam := lam) (μ := xj) (a := a) hlam))).symm
  have hratio := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  simpa [theorem7LaplacianProductConditionalRatioAt] using hratio

/--
Appendix C, Theorem 7: the weak-boundary Laplacian conditional pairwise ratio
tends to the right-tail case-3 endpoint.  This gives the unconditional pairwise
winner probability without repeating the product-measure integral calculation.
-/
theorem theorem7LaplacianProductConditionalRatioAt_tendsto_atTop_case3_endpoint
    {lam xi xj : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    Filter.Tendsto
      (fun a => theorem7LaplacianProductConditionalRatioAt lam xi xj a)
      Filter.atTop
      (nhds ((1 / 2 : ℝ) *
        theorem7LaplacianCase3Ratio (lam * (xi - xj)) 0)) := by
  let z : ℝ := lam * (xi - xj)
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos hlam (sub_pos.mpr hx)
  have harg :
      Filter.Tendsto (fun a : ℝ => -lam * (a - xi))
        Filter.atTop Filter.atBot := by
    have hneg : -lam < 0 := by linarith
    have hlin :
        Filter.Tendsto (fun a : ℝ => (-lam) * a + lam * xi)
          Filter.atTop Filter.atBot :=
      (Filter.Tendsto.const_mul_atTop_of_neg hneg Filter.tendsto_id).atBot_add
        tendsto_const_nhds
    convert hlin using 1
    ext a
    ring
  have hr :
      Filter.Tendsto (fun a : ℝ => Real.exp (-lam * (a - xi)))
        Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hcont :
      ContinuousAt
        (fun r : ℝ => theorem7LaplacianCase3Ratio z r) 0 :=
    theorem7LaplacianCase3Ratio_continuousAt
      (z := z) (r := 0) hz le_rfl zero_le_one
  have hratio :
      Filter.Tendsto
        (fun a : ℝ =>
          theorem7LaplacianCase3Ratio z
            (Real.exp (-lam * (a - xi))))
        Filter.atTop
        (nhds (theorem7LaplacianCase3Ratio z 0)) :=
    hcont.tendsto.comp hr
  have hclosed :
      Filter.Tendsto
        (fun a : ℝ =>
          (1 / 2 : ℝ) *
            theorem7LaplacianCase3ConditionalProb lam xi xj a)
        Filter.atTop
        (nhds ((1 / 2 : ℝ) *
          theorem7LaplacianCase3Ratio z 0)) := by
    simpa [theorem7LaplacianCase3ConditionalProb, z] using
      (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hratio
  refine hclosed.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop xi] with a ha
  rw [theorem7LaplacianProductConditionalRatioAt_eq_pdf_cdf
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam,
    theorem7LaplacianPDFCDFRatioAt_eq_case3
      (lam := lam) (xi := xi) (xj := xj) (a := a)
      hlam (le_of_lt hx) (le_of_lt ha)]
  exact (paper_theorem7_laplacian_case3_integral_ratio
    (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx ha
    ).symm

/--
Appendix C, Theorem 7: closed-form endpoint for the unconditional Laplacian
pairwise winner probability.
-/
theorem theorem7LaplacianPairWinner_toReal_eq_case3_endpoint
    {lam xi xj : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (theorem7LaplacianPairMeasure lam xi xj
      theorem7LaplacianPairWinnerEvent).toReal =
        (1 / 2 : ℝ) *
          theorem7LaplacianCase3Ratio (lam * (xi - xj)) 0 := by
  have hlim_winner :=
    theorem7LaplacianProductConditionalRatioAt_tendsto_atTop_winner
      (lam := lam) (xi := xi) (xj := xj) hlam
  have hlim_endpoint :=
    theorem7LaplacianProductConditionalRatioAt_tendsto_atTop_case3_endpoint
      (lam := lam) (xi := xi) (xj := xj) hlam hx
  exact (tendsto_nhds_unique hlim_endpoint hlim_winner).symm

/-- The higher-mean Laplace score wins a pairwise comparison with probability above one half. -/
theorem theorem7LaplacianPairWinner_toReal_gt_half
    {lam xi xj : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (1 / 2 : ℝ) <
      (theorem7LaplacianPairMeasure lam xi xj
        theorem7LaplacianPairWinnerEvent).toReal := by
  rw [theorem7LaplacianPairWinner_toReal_eq_case3_endpoint
    (lam := lam) (xi := xi) (xj := xj) hlam hx]
  exact theorem7LaplacianCase3Endpoint_gt_half
    (mul_pos hlam (sub_pos.mpr hx))

/-- The pairwise Laplace winner event has probability strictly below one. -/
theorem theorem7LaplacianPairWinner_toReal_lt_one
    {lam xi xj : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (theorem7LaplacianPairMeasure lam xi xj
      theorem7LaplacianPairWinnerEvent).toReal < 1 := by
  rw [theorem7LaplacianPairWinner_toReal_eq_case3_endpoint
    (lam := lam) (xi := xi) (xj := xj) hlam hx]
  exact theorem7LaplacianCase3Endpoint_lt_one
    (mul_pos hlam (sub_pos.mpr hx))

/--
For a fixed lower score mean, the Laplace pairwise winner probability is
strictly increasing in the higher score mean.
-/
theorem theorem7LaplacianPairWinner_toReal_lt_of_lt
    {lam xi1 xi2 xj : ℝ}
    (hlam : 0 < lam) (hx1 : xj < xi1) (hxi : xi1 < xi2) :
    (theorem7LaplacianPairMeasure lam xi1 xj
      theorem7LaplacianPairWinnerEvent).toReal <
      (theorem7LaplacianPairMeasure lam xi2 xj
        theorem7LaplacianPairWinnerEvent).toReal := by
  have hx2 : xj < xi2 := hx1.trans hxi
  have hz1 : 0 < lam * (xi1 - xj) :=
    mul_pos hlam (sub_pos.mpr hx1)
  have hgap : lam * (xi1 - xj) < lam * (xi2 - xj) := by
    exact mul_lt_mul_of_pos_left (by linarith) hlam
  rw [theorem7LaplacianPairWinner_toReal_eq_case3_endpoint
      (lam := lam) (xi := xi1) (xj := xj) hlam hx1,
    theorem7LaplacianPairWinner_toReal_eq_case3_endpoint
      (lam := lam) (xi := xi2) (xj := xj) hlam hx2]
  exact theorem7LaplacianCase3Endpoint_strictMono_pos hz1 hgap

/--
Appendix C, Theorem 7: finite right-tail cutoffs are strictly below the
unconditional Laplacian pairwise winner probability.
-/
theorem theorem7LaplacianProductConditionalRatioAt_lt_winner_of_xi_lt
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi < a) :
    theorem7LaplacianProductConditionalRatioAt lam xi xj a <
      (theorem7LaplacianPairMeasure lam xi xj
        theorem7LaplacianPairWinnerEvent).toReal := by
  let z : ℝ := lam * (xi - xj)
  let r : ℝ := Real.exp (-lam * (a - xi))
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos hlam (sub_pos.mpr hx)
  have hr0 : 0 < r := by
    dsimp [r]
    exact Real.exp_pos _
  have hr1 : r ≤ 1 := by
    dsimp [r]
    have hneg : -lam * (a - xi) < 0 := by
      have hpos : 0 < lam * (a - xi) :=
        mul_pos hlam (sub_pos.mpr ha)
      linarith
    exact le_of_lt (Real.exp_lt_one_iff.mpr hneg)
  have hcase :
      theorem7LaplacianCase3Ratio z r <
        theorem7LaplacianCase3Ratio z 0 :=
    theorem7LaplacianCase3Ratio_lt_endpoint_zero hz hr0 hr1
  have hscaled :
      (1 / 2 : ℝ) * theorem7LaplacianCase3Ratio z r <
        (1 / 2 : ℝ) * theorem7LaplacianCase3Ratio z 0 :=
    mul_lt_mul_of_pos_left hcase (by norm_num)
  have hratio :
      theorem7LaplacianProductConditionalRatioAt lam xi xj a =
        (1 / 2 : ℝ) *
          theorem7LaplacianCase3ConditionalProb lam xi xj a := by
    rw [theorem7LaplacianProductConditionalRatioAt_eq_pdf_cdf
        (lam := lam) (xi := xi) (xj := xj) (a := a) hlam,
      theorem7LaplacianPDFCDFRatioAt_eq_case3
        (lam := lam) (xi := xi) (xj := xj) (a := a)
        hlam (le_of_lt hx) (le_of_lt ha)]
    exact paper_theorem7_laplacian_case3_integral_ratio
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx ha
  rw [hratio,
    theorem7LaplacianPairWinner_toReal_eq_case3_endpoint
      (lam := lam) (xi := xi) (xj := xj) hlam hx]
  simpa [theorem7LaplacianCase3ConditionalProb, z, r] using hscaled

/--
Appendix C, Theorem 7: middle-region cutoffs are strictly below the
unconditional Laplacian pairwise winner probability.
-/
theorem theorem7LaplacianProductConditionalRatioAt_lt_winner_of_xj_lt_of_le_xi
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi)
    (hleft : xj < a) (hright : a ≤ xi) :
    theorem7LaplacianProductConditionalRatioAt lam xi xj a <
      (theorem7LaplacianPairMeasure lam xi xj
        theorem7LaplacianPairWinnerEvent).toReal := by
  let G : ℝ → ℝ := fun u =>
    1 - theorem7LaplacianCase2TailRatio lam xj u
  let z : ℝ := lam * (xi - xj)
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos hlam (sub_pos.mpr hx)
  have hratio :
      theorem7LaplacianProductConditionalRatioAt lam xi xj a = G a := by
    rw [theorem7LaplacianProductConditionalRatioAt_eq_pdf_cdf
        (lam := lam) (xi := xi) (xj := xj) (a := a) hlam,
      theorem7LaplacianPDFCDFRatioAt_eq_case2
        (lam := lam) (xi := xi) (xj := xj) (a := a)
        hlam (le_of_lt hleft)]
    dsimp [G]
    exact paper_theorem7_laplacian_case2_integral_ratio
      (lam := lam) (xi := xi) (xj := xj) (a := a)
      hlam hleft hright hx
  have hmono : G a ≤ G xi := by
    dsimp [G]
    exact theorem7LaplacianCase2ConditionalProb_mono
      (lam := lam) (xj := xj) (a := a) (b := xi)
      hlam hleft hright
  have hxi_lt :
      G xi <
        (theorem7LaplacianPairMeasure lam xi xj
          theorem7LaplacianPairWinnerEvent).toReal := by
    rw [theorem7LaplacianPairWinner_toReal_eq_case3_endpoint
      (lam := lam) (xi := xi) (xj := xj) hlam hx]
    have hscalar := theorem7LaplacianCase2Endpoint_lt_case3_endpoint
      (z := z) hz
    simpa [G, theorem7LaplacianCase2TailRatio, z] using hscalar
  exact hratio ▸ lt_of_le_of_lt hmono hxi_lt

/--
Appendix C, Theorem 7: left-region cutoffs are strictly below the unconditional
Laplacian pairwise winner probability.
-/
theorem theorem7LaplacianProductConditionalRatioAt_lt_winner_of_le_xj
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : a ≤ xj) :
    theorem7LaplacianProductConditionalRatioAt lam xi xj a <
      (theorem7LaplacianPairMeasure lam xi xj
        theorem7LaplacianPairWinnerEvent).toReal := by
  let z : ℝ := lam * (xi - xj)
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos hlam (sub_pos.mpr hx)
  have hratio :
      theorem7LaplacianProductConditionalRatioAt lam xi xj a = (1 / 2 : ℝ) := by
    rw [theorem7LaplacianProductConditionalRatioAt_eq_pdf_cdf
        (lam := lam) (xi := xi) (xj := xj) (a := a) hlam,
      theorem7LaplacianPDFCDFRatioAt_eq_case1]
    unfold theorem7LaplacianCase1IntegralRatio
      theorem7LaplacianPairIntegrand
    exact paper_theorem7_laplacian_case1_integral_ratio
      (lam := lam) (xi := xi) (xj := xj) (a := a)
      hlam ha hx
  rw [hratio,
    theorem7LaplacianPairWinner_toReal_eq_case3_endpoint
      (lam := lam) (xi := xi) (xj := xj) hlam hx]
  exact theorem7LaplacianCase3Endpoint_gt_half hz

/--
Appendix C, Theorem 7: every finite weak-boundary Laplacian cutoff conditional
ratio is strictly below the unconditional pairwise winner probability.
-/
theorem theorem7LaplacianProductConditionalRatioAt_lt_winner
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    theorem7LaplacianProductConditionalRatioAt lam xi xj a <
      (theorem7LaplacianPairMeasure lam xi xj
        theorem7LaplacianPairWinnerEvent).toReal := by
  by_cases ha_left : a ≤ xj
  · exact theorem7LaplacianProductConditionalRatioAt_lt_winner_of_le_xj
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx ha_left
  · have hleft : xj < a := lt_of_not_ge ha_left
    by_cases ha_mid : a ≤ xi
    · exact theorem7LaplacianProductConditionalRatioAt_lt_winner_of_xj_lt_of_le_xi
        (lam := lam) (xi := xi) (xj := xj) (a := a)
        hlam hx hleft ha_mid
    · have hright : xi < a := lt_of_not_ge ha_mid
      exact theorem7LaplacianProductConditionalRatioAt_lt_winner_of_xi_lt
        (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx hright

/--
Appendix C, Theorem 7: product-form finite-cutoff inequality for the Laplacian
pair numerator.
-/
theorem theorem7LaplacianPairNumerator_toReal_lt_winner_mul_denominator
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (theorem7LaplacianPairMeasure lam xi xj
        (theorem7LaplacianPairNumeratorEvent a)).toReal <
      (theorem7LaplacianPairMeasure lam xi xj
        theorem7LaplacianPairWinnerEvent).toReal *
        (theorem7LaplacianPairMeasure lam xi xj
          (theorem7LaplacianPairDenominatorEvent a)).toReal := by
  have hratio :=
    theorem7LaplacianProductConditionalRatioAt_lt_winner
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx
  have hden_pos :
      0 <
        (theorem7LaplacianPairMeasure lam xi xj
          (theorem7LaplacianPairDenominatorEvent a)).toReal := by
    have hcdf_pos :
        0 < theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a :=
      mul_pos
        (theorem7LaplaceCDFClosedForm_pos
          (lam := lam) (μ := xi) (a := a) hlam)
        (theorem7LaplaceCDFClosedForm_pos
          (lam := lam) (μ := xj) (a := a) hlam)
    rw [theorem7LaplacianPairDenominator_measure_eq
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam,
      ENNReal.toReal_ofReal (le_of_lt hcdf_pos)]
    exact hcdf_pos
  unfold theorem7LaplacianProductConditionalRatioAt at hratio
  exact (div_lt_iff₀ hden_pos).mp hratio

/-! ## Appendix C, Theorem 8 scalar Gaussian/Mills-ratio inequalities -/

/--
Appendix C, Theorem 8, equation (C.10) to the finite-difference bound.

The paper defines `g(t) = (1 + erf(t)) / exp(-t^2)` and, after reducing the
Gaussian derivative sign to (C.9), uses the mean value theorem to show it
suffices to prove `(d/dt) (1 / g(t)) > -sqrt(pi)` everywhere.  This lemma is
that mean-value step for any positive-spacing interval.
-/
theorem paper_theorem8_mills_mvt_step
    {g : ℝ → ℝ} {t δ : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn (fun u => (g u)⁻¹) (Set.Icc t (t + δ)))
    (hderiv :
      ∀ u ∈ Set.Ioo t (t + δ),
        ∃ d,
          HasDerivAt (fun u => (g u)⁻¹) d u ∧
            -Real.sqrt Real.pi < d) :
    (g t)⁻¹ - (g (t + δ))⁻¹ < δ * Real.sqrt Real.pi := by
  let f : ℝ → ℝ := fun u => (g u)⁻¹
  let f' : ℝ → ℝ :=
    fun u =>
      if hu : u ∈ Set.Ioo t (t + δ) then
        Classical.choose (hderiv u hu)
      else
        0
  have htd : t < t + δ := by linarith
  have hderiv' : ∀ u ∈ Set.Ioo t (t + δ), HasDerivAt f (f' u) u := by
    intro u hu
    dsimp [f']
    rw [dif_pos hu]
    exact (Classical.choose_spec (hderiv u hu)).1
  obtain ⟨c, hc, hmean⟩ :=
    exists_hasDerivAt_eq_slope
      (f := f) (f' := f') htd hcont hderiv'
  have hcderiv : -Real.sqrt Real.pi < f' c := by
    dsimp [f']
    rw [dif_pos hc]
    exact (Classical.choose_spec (hderiv c hc)).2
  have hslope :
      -Real.sqrt Real.pi <
        (f (t + δ) - f t) / ((t + δ) - t) := by
    simpa [hmean] using hcderiv
  have hdelta : (t + δ) - t = δ := by ring
  dsimp [f] at hslope ⊢
  rw [hdelta] at hslope
  have hmul : -Real.sqrt Real.pi * δ <
      (g (t + δ))⁻¹ - (g t)⁻¹ := by
    have hmul' := mul_lt_mul_of_pos_right hslope hδ
    rw [div_mul_cancel₀ _ hδ.ne'] at hmul'
    exact hmul'
  nlinarith

/--
Appendix C, Theorem 8, equation (C.9): the Mills-ratio finite-difference bound
implies positivity of the bracketed expression used for the Gaussian derivative
sign.
-/
theorem paper_theorem8_c9_positive_of_mills_mvt
    {g : ℝ → ℝ} {t δ : ℝ} (hδ : 0 < δ) (hgpos : 0 < g t)
    (hcont : ContinuousOn (fun u => (g u)⁻¹) (Set.Icc t (t + δ)))
    (hderiv :
      ∀ u ∈ Set.Ioo t (t + δ),
        ∃ d,
          HasDerivAt (fun u => (g u)⁻¹) d u ∧
            -Real.sqrt Real.pi < d) :
    0 < g t * (δ * Real.sqrt Real.pi + (g (t + δ))⁻¹) - 1 := by
  have hdiff :=
    paper_theorem8_mills_mvt_step
      (g := g) (t := t) (δ := δ) hδ hcont hderiv
  have hmain :
      (g t)⁻¹ < δ * Real.sqrt Real.pi + (g (t + δ))⁻¹ := by
    linarith
  have hmul :=
    mul_lt_mul_of_pos_left hmain hgpos
  have hcancel : g t * (g t)⁻¹ = 1 := by
    rw [mul_inv_cancel₀ hgpos.ne']
  nlinarith

/--
Appendix C, Theorem 8 positivity template.

This formalizes the paper's criterion used after (C.6): if a real function has
limit `0` at `-∞` and is strictly increasing, then it is positive everywhere.
-/
theorem paper_theorem8_positive_of_strictMono_tendsto_atBot_zero
    {F : ℝ → ℝ} (hmono : StrictMono F)
    (hlim : Filter.Tendsto F Filter.atBot (nhds 0)) (t : ℝ) :
    0 < F t := by
  let y : ℝ := t - 1
  have hyt : y < t := by
    dsimp [y]
    linarith
  have hy_nonneg : 0 ≤ F y := by
    by_contra hnot
    have hyneg : F y < 0 := lt_of_not_ge hnot
    have hlt : ∀ᶠ z in Filter.atBot, F z < F y :=
      (Filter.eventually_lt_atBot y).mono fun z hz => hmono hz
    have hgt : ∀ᶠ z in Filter.atBot, F y < F z :=
      hlim (isOpen_Ioi.mem_nhds (show (0 : ℝ) ∈ Set.Ioi (F y) by exact hyneg))
    obtain ⟨z, hzlt, hzgt⟩ := (hlt.and hgt).exists
    linarith
  have hy_lt : F y < F t := hmono hyt
  linarith

/--
Appendix C, Theorem 8 positivity template in the derivative form used in the
paper: differentiability with everywhere-positive derivative gives strict
monotonicity, and the `-∞` limit then gives positivity.
-/
theorem paper_theorem8_positive_of_deriv_pos_tendsto_atBot_zero
    {F F' : ℝ → ℝ}
    (hderiv : ∀ t, HasDerivAt F (F' t) t)
    (hpos : ∀ t, 0 < F' t)
    (hlim : Filter.Tendsto F Filter.atBot (nhds 0)) :
    ∀ t, 0 < F t := by
  intro t
  exact paper_theorem8_positive_of_strictMono_tendsto_atBot_zero
    (strictMono_of_hasDerivAt_pos hderiv hpos) hlim t

/--
The bracket in Appendix C, Theorem 8 equation (C.9), after writing
`g(t) = (1 + erf(t)) / exp(-t^2)`.
-/
noncomputable def theorem8GaussianC9Bracket (g : ℝ → ℝ) (δ t : ℝ) : ℝ := g t * (δ * Real.sqrt Real.pi + (g (t + δ))⁻¹) - 1

/--
Appendix C, Theorem 8 paper definition
`g(t) = (1 + erf(t)) / exp(-t^2)`.
-/
noncomputable def theorem8GaussianG (erf : ℝ → ℝ) (t : ℝ) : ℝ := (1 + erf t) / Real.exp (-(t ^ 2))

/--
Appendix C, Theorem 8: the standard error function normalization used in the
Gaussian calculation, written directly as the paper's interval integral.
-/
noncomputable def theorem8Erf (t : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) *
    ∫ x : ℝ in (0 : ℝ)..t, Real.exp (-(x ^ 2))

/--
Appendix C, Theorem 8: derivative of the paper's concrete `erf` definition.

This discharges the standard `erf` derivative assumption for wrappers that use
`theorem8Erf`.
-/
theorem theorem8Erf_hasDerivAt (t : ℝ) :
    HasDerivAt theorem8Erf
      ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t := by
  unfold theorem8Erf
  have hcont : Continuous fun x : ℝ => Real.exp (-(x ^ 2)) :=
    Real.continuous_exp.comp ((continuous_id.pow 2).neg)
  simpa [mul_assoc] using
    (hcont.integral_hasStrictDerivAt (0 : ℝ) t).hasDerivAt.const_mul
      (2 / Real.sqrt Real.pi)

/-- Appendix C, Theorem 8: continuity of the concrete `erf` integral. -/
theorem theorem8Erf_continuous : Continuous theorem8Erf := continuous_iff_continuousAt.mpr fun t => (theorem8Erf_hasDerivAt t).continuousAt

/-- Appendix C, Theorem 8: the left half-Gaussian integral used by `erf(-∞)=-1`. -/
theorem theorem8Gaussian_integral_Iic_zero :
    (∫ x : ℝ in Set.Iic (0 : ℝ), Real.exp (-(x ^ 2))) =
      Real.sqrt Real.pi / 2 := by
  have hsymm :
      (∫ x : ℝ in Set.Iic (0 : ℝ), Real.exp (-(x ^ 2))) =
        ∫ x : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2)) := by
    have hcomp :=
      integral_comp_neg_Iic (c := (0 : ℝ))
        (f := fun x : ℝ => Real.exp (-(x ^ 2)))
    simpa [neg_sq] using hcomp
  rw [hsymm]
  simpa [one_mul, div_one] using (integral_gaussian_Ioi (1 : ℝ))

/--
Appendix C, Theorem 8: the concrete interval-integral definition of `erf`
rewrites the left Gaussian tail as
`∫_{-∞}^t exp(-x^2) dx = sqrt(pi)/2 * (1 + erf(t))`.
-/
theorem theorem8Gaussian_integral_Iic_eq_erf (t : ℝ) :
    (∫ x : ℝ in Set.Iic t, Real.exp (-(x ^ 2))) =
      Real.sqrt Real.pi / 2 * (1 + theorem8Erf t) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2))
  have hfi0 : IntegrableOn f (Set.Iic (0 : ℝ)) := by
    simpa [f, one_mul] using
      (integrable_exp_neg_mul_sq (show 0 < (1 : ℝ) by norm_num)).integrableOn
  have hfit : IntegrableOn f (Set.Iic t) := by
    simpa [f, one_mul] using
      (integrable_exp_neg_mul_sq (show 0 < (1 : ℝ) by norm_num)).integrableOn
  have hsub :
      (∫ x : ℝ in Set.Iic t, f x) -
          ∫ x : ℝ in Set.Iic (0 : ℝ), f x =
        ∫ x : ℝ in (0 : ℝ)..t, f x := by
    simpa using
      (intervalIntegral.integral_Iic_sub_Iic
        (f := f) (a := (0 : ℝ)) (b := t) hfi0 hfit)
  have hI :
      (∫ x : ℝ in Set.Iic t, f x) =
        Real.sqrt Real.pi / 2 + ∫ x : ℝ in (0 : ℝ)..t, f x := by
    rw [show (∫ x : ℝ in Set.Iic (0 : ℝ), f x) =
        Real.sqrt Real.pi / 2 by
      simpa [f] using theorem8Gaussian_integral_Iic_zero] at hsub
    linarith
  rw [hI]
  unfold theorem8Erf
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
    Real.sqrt_ne_zero'.mpr Real.pi_pos
  field_simp [f, hsqrt_ne]
  ring

/--
Appendix C, Theorem 8: translation of a left-half-line integral.  This is the
change of variables `u = x - μ` used when the Gaussian density with mean `μ`
is rewritten in centered coordinates.
-/
theorem theorem8_integral_Iic_sub_eq_integral_Iic
    (f : ℝ → ℝ) (a μ : ℝ) :
    (∫ x : ℝ in Set.Iic a, f (x - μ)) =
      ∫ x : ℝ in Set.Iic (a - μ), f x := by
  have A : MeasurableEmbedding (fun x : ℝ => x + μ) :=
    (Homeomorph.addRight μ).isClosedEmbedding.measurableEmbedding
  calc
    (∫ y : ℝ in Set.Iic a, f (y - μ)) =
        ∫ y : ℝ in Set.Iic a, f (y - μ) ∂Measure.map (fun x : ℝ => x + μ) volume := by
          rw [map_add_right_eq_self]
    _ = ∫ x : ℝ in (fun x : ℝ => x + μ) ⁻¹' Set.Iic a, f ((x + μ) - μ) :=
          A.setIntegral_map (g := fun y : ℝ => f (y - μ)) (s := Set.Iic a)
    _ = ∫ x : ℝ in Set.Iic (a - μ), f x := by
          have hpre :
              (fun x : ℝ => x + μ) ⁻¹' Set.Iic a = Set.Iic (a - μ) := by
            ext x
            constructor <;> intro hx
            · change x + μ ≤ a at hx
              change x ≤ a - μ
              linarith
            · change x + μ ≤ a
              change x ≤ a - μ at hx
              linarith
          simp [hpre]

/--
Appendix C, Theorem 8: `1 + erf(t)` tends to `0` as `t -> -∞` for the
paper's concrete interval-integral `erf`.
-/
theorem theorem8Erf_tendsto_one_add_atBot_zero :
    Filter.Tendsto (fun t => 1 + theorem8Erf t) Filter.atBot (nhds 0) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2))
  have hfi : IntegrableOn f (Set.Iic (0 : ℝ)) := by
    simpa [f, one_mul] using
      (integrable_exp_neg_mul_sq (show 0 < (1 : ℝ) by norm_num)).integrableOn
  have ht_left :
      Filter.Tendsto (fun t => ∫ x : ℝ in t..(0 : ℝ), f x)
        Filter.atBot
        (nhds (∫ x : ℝ in Set.Iic (0 : ℝ), f x)) :=
    intervalIntegral_tendsto_integral_Iic
      (f := f) (b := (0 : ℝ)) hfi Filter.tendsto_id
  have ht_interval :
      Filter.Tendsto (fun t => ∫ x : ℝ in (0 : ℝ)..t, f x)
        Filter.atBot
        (nhds (-(∫ x : ℝ in Set.Iic (0 : ℝ), f x))) := by
    refine ht_left.neg.congr' ?_
    filter_upwards with t
    rw [intervalIntegral.integral_symm]
    abel
  have hscaled :
      Filter.Tendsto
        (fun t => (2 / Real.sqrt Real.pi) *
          ∫ x : ℝ in (0 : ℝ)..t, f x)
        Filter.atBot (nhds (-1)) := by
    have hconst :
        (2 / Real.sqrt Real.pi) *
            (-(∫ x : ℝ in Set.Iic (0 : ℝ), f x)) = -1 := by
      rw [show (∫ x : ℝ in Set.Iic (0 : ℝ), f x) =
          Real.sqrt Real.pi / 2 by
        simpa [f] using theorem8Gaussian_integral_Iic_zero]
      have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
        Real.sqrt_ne_zero'.mpr Real.pi_pos
      field_simp [hsqrt_ne]
    simpa [hconst] using ht_interval.const_mul (2 / Real.sqrt Real.pi)
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atBot (nhds 1) :=
    tendsto_const_nhds
  simpa [theorem8Erf, f] using hone.add hscaled

/--
Appendix C, Theorem 8: `1 + erf(t)` tends to `2` as `t -> +∞` for the
paper's concrete interval-integral `erf`.
-/
theorem theorem8Erf_tendsto_one_add_atTop_two :
    Filter.Tendsto (fun t => 1 + theorem8Erf t) Filter.atTop (nhds 2) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2))
  have hfi : IntegrableOn f (Set.Ioi (0 : ℝ)) := by
    simpa [f, one_mul] using
      (integrable_exp_neg_mul_sq (show 0 < (1 : ℝ) by norm_num)).integrableOn
  have ht_interval :
      Filter.Tendsto (fun t => ∫ x : ℝ in (0 : ℝ)..t, f x)
        Filter.atTop
        (nhds (∫ x : ℝ in Set.Ioi (0 : ℝ), f x)) :=
    intervalIntegral_tendsto_integral_Ioi
      (f := f) (a := (0 : ℝ)) hfi Filter.tendsto_id
  have hscaled :
      Filter.Tendsto
        (fun t => (2 / Real.sqrt Real.pi) *
          ∫ x : ℝ in (0 : ℝ)..t, f x)
        Filter.atTop (nhds 1) := by
    have hconst :
        (2 / Real.sqrt Real.pi) *
            (∫ x : ℝ in Set.Ioi (0 : ℝ), f x) = 1 := by
      rw [show (∫ x : ℝ in Set.Ioi (0 : ℝ), f x) =
          Real.sqrt Real.pi / 2 by
        simpa [f, one_mul, div_one] using (integral_gaussian_Ioi (1 : ℝ))]
      have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
        Real.sqrt_ne_zero'.mpr Real.pi_pos
      field_simp [hsqrt_ne]
    simpa [hconst] using ht_interval.const_mul (2 / Real.sqrt Real.pi)
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  simpa [theorem8Erf, f, show (1 : ℝ) + 1 = 2 by norm_num] using
    hone.add hscaled

/-- Appendix C, Theorem 8: positivity of `1 + erf(t)` for the concrete `erf`. -/
theorem theorem8Erf_one_add_pos (t : ℝ) :
    0 < 1 + theorem8Erf t := by
  have hderiv :
      ∀ t,
        HasDerivAt (fun u => 1 + theorem8Erf u)
          ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t := by
    intro t
    simpa using (theorem8Erf_hasDerivAt t).const_add (1 : ℝ)
  have hpos :
      ∀ t, 0 < (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) := by
    intro t
    positivity
  exact paper_theorem8_positive_of_deriv_pos_tendsto_atBot_zero
    hderiv hpos theorem8Erf_tendsto_one_add_atBot_zero t

/-- Appendix C, Theorem 8: the concrete interval-integral `erf` is strictly increasing. -/
theorem theorem8Erf_strictMono : StrictMono theorem8Erf := by
  refine strictMono_of_hasDerivAt_pos theorem8Erf_hasDerivAt ?_
  intro t
  positivity

/--
Appendix C, Theorem 8: on the left half-line used by `J(t)`, the shifted
concrete `erf` factor is bounded.  This is the bounded-factor input needed to
show integrability of the paper's `J` integrand.
-/
theorem theorem8Erf_boundedOn_left_shift (δ : ℝ) :
    ∀ x ∈ Set.Iic (0 : ℝ),
      ‖theorem8Erf (x + δ)‖ ≤ max 1 ‖theorem8Erf δ‖ := by
  intro x hx
  have hC1 : (1 : ℝ) ≤ max 1 ‖theorem8Erf δ‖ := le_max_left _ _
  have hCδ : ‖theorem8Erf δ‖ ≤ max 1 ‖theorem8Erf δ‖ := le_max_right _ _
  have hlower : -1 < theorem8Erf (x + δ) := by
    have h := theorem8Erf_one_add_pos (x + δ)
    linarith
  have hx0 : x ≤ 0 := by
    simpa using hx
  have hupper : theorem8Erf (x + δ) ≤ theorem8Erf δ :=
    theorem8Erf_strictMono.monotone (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact abs_le.mpr
    ⟨(neg_le_neg hC1).trans (le_of_lt hlower),
      hupper.trans ((le_abs_self _).trans hCδ)⟩

/--
Appendix C, Theorem 8 rational term appearing in equation (C.6), before
subtracting `(1 + erf(t))` and the integral term.
-/
noncomputable def theorem8GaussianC6RationalTerm (erf : ℝ → ℝ)
    (δ t : ℝ) : ℝ :=
  ((1 + erf t) * (1 + erf (t + δ)) ^ 2 * Real.exp (-(t ^ 2))) /
    ((1 + erf t) * Real.exp (-((t + δ) ^ 2)) +
      (1 + erf (t + δ)) * Real.exp (-(t ^ 2)))

/--
Appendix C, Theorem 8, equation (C.7): the rational term is nonnegative when
the two Gaussian CDF factors are nonnegative.
-/
theorem theorem8GaussianC6RationalTerm_nonneg
    {erf : ℝ → ℝ} {δ t : ℝ}
    (ht : 0 ≤ 1 + erf t) (htδ : 0 ≤ 1 + erf (t + δ)) :
    0 ≤ theorem8GaussianC6RationalTerm erf δ t := by
  unfold theorem8GaussianC6RationalTerm
  have hnum :
      0 ≤ (1 + erf t) * (1 + erf (t + δ)) ^ 2 * Real.exp (-(t ^ 2)) := by
    positivity
  have hden :
      0 ≤ (1 + erf t) * Real.exp (-((t + δ) ^ 2)) +
          (1 + erf (t + δ)) * Real.exp (-(t ^ 2)) := by
    positivity
  exact div_nonneg hnum hden

/--
Appendix C, Theorem 8, equation (C.7): the paper's upper bound on the rational
term by `(1 + erf(t)) * (1 + erf(t+δ))`.
-/
theorem theorem8GaussianC6RationalTerm_le_product
    {erf : ℝ → ℝ} {δ t : ℝ}
    (ht : 0 < 1 + erf t) (htδ : 0 < 1 + erf (t + δ)) :
    theorem8GaussianC6RationalTerm erf δ t ≤
      (1 + erf t) * (1 + erf (t + δ)) := by
  unfold theorem8GaussianC6RationalTerm
  set A : ℝ := 1 + erf t
  set B : ℝ := 1 + erf (t + δ)
  set Et : ℝ := Real.exp (-(t ^ 2))
  set Ed : ℝ := Real.exp (-((t + δ) ^ 2))
  have hA : 0 < A := by simpa [A] using ht
  have hB : 0 < B := by simpa [B] using htδ
  have hEt : 0 < Et := by simpa [Et] using Real.exp_pos (-(t ^ 2))
  have hEd : 0 < Ed := by simpa [Ed] using Real.exp_pos (-((t + δ) ^ 2))
  have hden : 0 < A * Ed + B * Et :=
    add_pos (mul_pos hA hEd) (mul_pos hB hEt)
  rw [div_le_iff₀ hden]
  have hextra : 0 ≤ A * A * B * Ed := by positivity
  calc
    A * B ^ 2 * Et ≤ A * B ^ 2 * Et + A * A * B * Ed := by linarith
    _ = A * B * (A * Ed + B * Et) := by ring

/-- Appendix C, Theorem 8: shifting the concrete `erf` left-tail limit. -/
theorem theorem8Erf_tendsto_one_add_atBot_zero_shift (δ : ℝ) :
    Filter.Tendsto (fun t => 1 + theorem8Erf (t + δ))
      Filter.atBot (nhds 0) := by
  have hshift :
      Filter.Tendsto (fun t : ℝ => t + δ) Filter.atBot Filter.atBot := by
    rw [Filter.tendsto_atBot_atBot]
    intro b
    exact ⟨b - δ, fun a ha => by linarith⟩
  exact theorem8Erf_tendsto_one_add_atBot_zero.comp hshift

/--
Appendix C, Theorem 8, equation (C.7): for the concrete `erf`, the rational
term in C.6 tends to zero as `t -> -∞`.
-/
theorem theorem8GaussianC6RationalTerm_tendsto_atBot_zero_concrete
    (δ : ℝ) :
    Filter.Tendsto
      (fun t => theorem8GaussianC6RationalTerm theorem8Erf δ t)
      Filter.atBot (nhds 0) := by
  have hprod :
      Filter.Tendsto
        (fun t => (1 + theorem8Erf t) * (1 + theorem8Erf (t + δ)))
        Filter.atBot (nhds 0) := by
    simpa using
      theorem8Erf_tendsto_one_add_atBot_zero.mul
        (theorem8Erf_tendsto_one_add_atBot_zero_shift δ)
  refine squeeze_zero ?_ ?_ hprod
  · intro t
    exact theorem8GaussianC6RationalTerm_nonneg
      (le_of_lt (theorem8Erf_one_add_pos t))
      (le_of_lt (theorem8Erf_one_add_pos (t + δ)))
  · intro t
    exact theorem8GaussianC6RationalTerm_le_product
      (theorem8Erf_one_add_pos t)
      (theorem8Erf_one_add_pos (t + δ))

/--
Appendix C, Theorem 8: the paper's improper integral
`J(t) = ∫_{-∞}^t exp(-x^2) erf(x + δ) dx`, represented as a left half-line
set integral.
-/
noncomputable def theorem8GaussianJ (erf : ℝ → ℝ) (δ t : ℝ) : ℝ := ∫ x : ℝ in Set.Iic t, Real.exp (-(x ^ 2)) * erf (x + δ)

/--
Generic left-tail lemma used for Appendix C, Theorem 8: if a real integrand is
integrable on `(-∞, 0]`, then its left half-line integral tends to zero as the
right endpoint tends to `-∞`.
-/
theorem integral_Iic_tendsto_atBot_zero_of_integrableOn_Iic_zero
    {f : ℝ → ℝ} (hfi : IntegrableOn f (Set.Iic (0 : ℝ))) :
    Filter.Tendsto (fun t => ∫ x : ℝ in Set.Iic t, f x)
      Filter.atBot (nhds 0) := by
  have ht_interval :
      Filter.Tendsto (fun t => ∫ x : ℝ in t..(0 : ℝ), f x)
        Filter.atBot
        (nhds (∫ x : ℝ in Set.Iic (0 : ℝ), f x)) :=
    intervalIntegral_tendsto_integral_Iic
      (f := f) (b := (0 : ℝ)) hfi Filter.tendsto_id
  have htail_expr :
      Filter.Tendsto
        (fun t => (∫ x : ℝ in Set.Iic (0 : ℝ), f x) -
          ∫ x : ℝ in t..(0 : ℝ), f x)
        Filter.atBot (nhds 0) := by
    have hconst :
        Filter.Tendsto
          (fun _ : ℝ => ∫ x : ℝ in Set.Iic (0 : ℝ), f x)
          Filter.atBot
          (nhds (∫ x : ℝ in Set.Iic (0 : ℝ), f x)) :=
      tendsto_const_nhds
    simpa using hconst.sub ht_interval
  refine htail_expr.congr' ?_
  filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with t ht
  have hfi_t : IntegrableOn f (Set.Iic t) :=
    hfi.mono_set (Set.Iic_subset_Iic.mpr ht)
  have hsub :=
    intervalIntegral.integral_Iic_sub_Iic
      (f := f) (a := t) (b := (0 : ℝ)) hfi_t hfi
  linarith

/--
Appendix C, Theorem 8: the paper's `J(t)` tends to zero at `-∞` once its
integrand is known to be integrable on the left half-line.
-/
theorem theorem8GaussianJ_tendsto_atBot_zero_of_integrableOn
    {erf : ℝ → ℝ} {δ : ℝ}
    (hJ_integrable :
      IntegrableOn
        (fun x : ℝ => Real.exp (-(x ^ 2)) * erf (x + δ))
        (Set.Iic (0 : ℝ))) :
    Filter.Tendsto (theorem8GaussianJ erf δ) Filter.atBot (nhds 0) := by
  simpa [theorem8GaussianJ] using
    integral_Iic_tendsto_atBot_zero_of_integrableOn_Iic_zero
      (f := fun x : ℝ => Real.exp (-(x ^ 2)) * erf (x + δ))
      hJ_integrable

/--
Appendix C, Theorem 8: integrability of the concrete `J` integrand on the
left half-line.  The Gaussian factor is integrable, and the shifted concrete
`erf` factor is bounded there by `theorem8Erf_boundedOn_left_shift`.
-/
theorem theorem8GaussianJ_integrableOn_concrete (δ : ℝ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ))
      (Set.Iic (0 : ℝ)) := by
  have hgauss :
      IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2))) (Set.Iic (0 : ℝ)) := by
    simpa [one_mul] using
      (integrable_exp_neg_mul_sq (show 0 < (1 : ℝ) by norm_num)).integrableOn
  exact hgauss.mul_bdd
    ((theorem8Erf_continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Iic
      (theorem8Erf_boundedOn_left_shift δ))

/--
Appendix C, Theorem 8: integrability of the concrete `J` integrand on any
left half-line.  This extends the left-tail integrability proof by adding only
a compact interval when the endpoint is positive.
-/
theorem theorem8GaussianJ_integrableOn_Iic_concrete (δ a : ℝ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ))
      (Set.Iic a) := by
  by_cases ha : a ≤ 0
  · exact (theorem8GaussianJ_integrableOn_concrete δ).mono_set
      (Set.Iic_subset_Iic.mpr ha)
  · have h0a : 0 ≤ a := le_of_not_ge ha
    have hcont :
        Continuous
          (fun x : ℝ => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ)) :=
      (Real.continuous_exp.comp ((continuous_id.pow 2).neg)).mul
        (theorem8Erf_continuous.comp (continuous_id.add continuous_const))
    have hcompact :
        IntegrableOn
          (fun x : ℝ => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ))
          (Set.Icc (0 : ℝ) a) :=
      hcont.continuousOn.integrableOn_compact isCompact_Icc
    rw [← Set.Iic_union_Icc_eq_Iic h0a]
    exact (theorem8GaussianJ_integrableOn_concrete δ).union hcompact

/--
Appendix C, Theorem 8: rewriting the concrete `J(t)` left-half-line integral
as a constant left tail plus an ordinary interval integral.
-/
theorem theorem8GaussianJ_eq_Iic_zero_add_interval (δ t : ℝ) :
    theorem8GaussianJ theorem8Erf δ t =
      (∫ x : ℝ in Set.Iic (0 : ℝ),
        Real.exp (-(x ^ 2)) * theorem8Erf (x + δ)) +
        ∫ x : ℝ in (0 : ℝ)..t,
          Real.exp (-(x ^ 2)) * theorem8Erf (x + δ) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ)
  have hfi0 : IntegrableOn f (Set.Iic (0 : ℝ)) := by
    simpa [f] using theorem8GaussianJ_integrableOn_concrete δ
  have hfit : IntegrableOn f (Set.Iic t) := by
    simpa [f] using theorem8GaussianJ_integrableOn_Iic_concrete δ t
  have hsub :
      (∫ x : ℝ in Set.Iic t, f x) -
          ∫ x : ℝ in Set.Iic (0 : ℝ), f x =
        ∫ x : ℝ in (0 : ℝ)..t, f x := by
    simpa using
      (intervalIntegral.integral_Iic_sub_Iic
        (f := f) (a := (0 : ℝ)) (b := t) hfi0 hfit)
  unfold theorem8GaussianJ
  dsimp [f] at hsub ⊢
  linarith

/--
Appendix C, Theorem 8: derivative of the concrete `J(t)` integral.
-/
theorem theorem8GaussianJ_hasDerivAt_concrete (δ t : ℝ) :
    HasDerivAt (theorem8GaussianJ theorem8Erf δ)
      (Real.exp (-(t ^ 2)) * theorem8Erf (t + δ)) t := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ)
  have hcont : Continuous f :=
    (Real.continuous_exp.comp ((continuous_id.pow 2).neg)).mul
      (theorem8Erf_continuous.comp (continuous_id.add continuous_const))
  have hderiv :
      HasDerivAt
        (fun u : ℝ =>
          (∫ x : ℝ in Set.Iic (0 : ℝ), f x) +
            ∫ x : ℝ in (0 : ℝ)..u, f x)
        (f t) t :=
    (hcont.integral_hasStrictDerivAt (0 : ℝ) t).hasDerivAt.const_add
      (∫ x : ℝ in Set.Iic (0 : ℝ), f x)
  refine hderiv.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun u => by
    simp [f, theorem8GaussianJ_eq_Iic_zero_add_interval]

/--
Appendix C, Theorem 8 left-hand side of equation (C.6).  The argument `J`
stands for the paper's integral
`J(t) = ∫_{-∞}^t exp(-x^2) erf(x + δ) dx`.
-/
noncomputable def theorem8GaussianC6LHS (erf J : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  theorem8GaussianC6RationalTerm erf δ t -
    (1 + erf t) - (2 / Real.sqrt Real.pi) * J t

/--
Appendix C, Theorem 8 positive prefactor factored out of the derivative in
equation (C.8) to obtain the C.9 bracket.

The paper's displayed prefactor has a typographical mismatch with the C.9
bracket.  The positive factor below is the algebraically correct factor whose
product with `theorem8GaussianC9Bracket` equals the C.8 derivative.
-/
noncomputable def theorem8GaussianC8PositiveFactor (erf : ℝ → ℝ)
    (δ t : ℝ) : ℝ :=
  (2 * (1 + erf t) * (1 + erf (t + δ)) ^ 2 * Real.exp ((t + δ) ^ 2)) /
    (Real.sqrt Real.pi *
      (((erf t + 1) * Real.exp (t ^ 2) +
        (erf (t + δ) + 1) * Real.exp ((t + δ) ^ 2)) ^ 2))

/-- Appendix C, Theorem 8: positivity of the paper's `g(t)`. -/
theorem theorem8GaussianG_pos
    {erf : ℝ → ℝ} {t : ℝ} (hone : 0 < 1 + erf t) :
    0 < theorem8GaussianG erf t := by
  unfold theorem8GaussianG
  positivity

/-- Appendix C, Theorem 8: continuity of the paper's `g(t)`. -/
theorem theorem8GaussianG_continuous
    {erf : ℝ → ℝ} (herf : Continuous erf) :
    Continuous (theorem8GaussianG erf) := by
  unfold theorem8GaussianG
  have hnum : Continuous fun t : ℝ => 1 + erf t :=
    continuous_const.add herf
  have hden : Continuous fun t : ℝ => Real.exp (-(t ^ 2)) :=
    Real.continuous_exp.comp ((continuous_id.pow 2).neg)
  exact hnum.div hden (fun t => (Real.exp_pos (-(t ^ 2))).ne')

/--
Appendix C, Theorem 8: continuity of `1 / g` on any interval, derived from
continuity of `erf` and positivity of `1 + erf`.
-/
theorem theorem8GaussianG_inv_continuousOn
    {erf : ℝ → ℝ} (herf : Continuous erf)
    (hone : ∀ t, 0 < 1 + erf t) (s : Set ℝ) :
    ContinuousOn (fun u => (theorem8GaussianG erf u)⁻¹) s :=
   (theorem8GaussianG_continuous herf).continuousOn.inv₀
    (fun u _hu => (theorem8GaussianG_pos (hone u)).ne')

/-- Appendix C, Theorem 8: the usual derivative formula for `erf` implies continuity. -/
theorem theorem8Erf_continuous_of_hasDerivAt
    {erf : ℝ → ℝ}
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t) :
    Continuous erf := continuous_iff_continuousAt.mpr fun t => (herf_deriv t).continuousAt

/--
Appendix C, Theorem 8: positivity of `1 + erf(t)` from the standard derivative
formula and the left-tail limit `1 + erf(t) -> 0` as `t -> -∞`.
-/
theorem theorem8_one_add_erf_pos_of_deriv_tendsto_atBot
    {erf : ℝ → ℝ}
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (hlim : Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0)) :
    ∀ t, 0 < 1 + erf t := by
  have hderiv :
      ∀ t,
        HasDerivAt (fun u => 1 + erf u)
          ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t := by
    intro t
    simpa using (herf_deriv t).const_add (1 : ℝ)
  have hpos :
      ∀ t, 0 < (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) := by
    intro t
    positivity
  exact paper_theorem8_positive_of_deriv_pos_tendsto_atBot_zero
    hderiv hpos hlim

/--
Appendix C, Theorem 8, limit of the C.6 expression from the three component
limits used in the paper after equation (C.7).
-/
theorem theorem8GaussianC6LHS_tendsto_atBot_zero
    {erf J : ℝ → ℝ} {δ : ℝ}
    (hratio :
      Filter.Tendsto (fun t => theorem8GaussianC6RationalTerm erf δ t)
        Filter.atBot (nhds 0))
    (herf_tail : Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0))
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0)) :
    Filter.Tendsto (fun t => theorem8GaussianC6LHS erf J δ t)
      Filter.atBot (nhds 0) := by
  have hJ_scaled :
      Filter.Tendsto (fun t => (2 / Real.sqrt Real.pi) * J t)
        Filter.atBot (nhds 0) := by
    simpa using hJ_tail.const_mul (2 / Real.sqrt Real.pi)
  simpa [theorem8GaussianC6LHS, sub_eq_add_neg] using
    (hratio.sub herf_tail).sub hJ_scaled

/--
Appendix C, Theorem 8: the prefactor removed from equation (C.8) is positive
whenever the two Gaussian CDF terms `1 + erf(t)` and `1 + erf(t + δ)` are
positive.
-/
theorem theorem8GaussianC8PositiveFactor_pos
    {erf : ℝ → ℝ} {δ t : ℝ}
    (ht : 0 < 1 + erf t) (htδ : 0 < 1 + erf (t + δ)) :
    0 < theorem8GaussianC8PositiveFactor erf δ t := by
  unfold theorem8GaussianC8PositiveFactor
  have ht' : 0 < erf t + 1 := by linarith
  have htδ' : 0 < erf (t + δ) + 1 := by linarith
  have hsum :
      0 <
        (erf t + 1) * Real.exp (t ^ 2) +
          (erf (t + δ) + 1) * Real.exp ((t + δ) ^ 2) :=
    add_pos (mul_pos ht' (Real.exp_pos _)) (mul_pos htδ' (Real.exp_pos _))
  refine div_pos ?_ ?_
  · positivity
  · exact mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (sq_pos_of_ne_zero hsum.ne')

/--
Appendix C, Theorem 8, C.8 algebraic factorization after abbreviating
`a=1+erf(t)`, `b=1+erf(t+δ)`, `p=exp(-t^2)`, and
`q=exp(-(t+δ)^2)`.  This is the pure real-field identity that turns the
explicit derivative of the C.6 rational term into the corrected positive
factor times the C.9 bracket.
-/
theorem theorem8GaussianC8_algebra
    (a b p q s δ t : ℝ) (hs : s ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hb : b ≠ 0) (hden : a * q + b * p ≠ 0) :
    ((((2 / s * p * b ^ 2 * p + a * (2 * b * (2 / s * q)) * p +
        a * b ^ 2 * (-(2 * t * p))) * (a * q + b * p) -
      (a * b ^ 2 * p) *
        ((2 / s * p) * q + a * (-(2 * (t + δ) * q)) +
          (2 / s * q) * p + b * (-(2 * t * p)))) /
      (a * q + b * p) ^ 2) - (2 / s) * p * b) =
      ((2 * a * b ^ 2 * q⁻¹) /
        (s * ((a * p⁻¹ + b * q⁻¹) ^ 2))) *
        (a / p * (δ * s + (b / q)⁻¹) - 1) := by
  have hden_sq : (a * q + b * p) ^ 2 ≠ 0 := pow_ne_zero 2 hden
  field_simp [hs, hp, hq, hb, hden, hden_sq]
  apply (mul_right_inj' hden_sq).mp
  field_simp [hden_sq]
  ring

/--
Appendix C, Theorem 8: Mills ratio as used in the paper,
`R(t) = exp(t^2 / 2) * ∫_t^∞ exp(-x^2 / 2) dx`.
-/
noncomputable def theorem8MillsRatio (t : ℝ) : ℝ :=
  Real.exp (t ^ 2 / 2) *
    ∫ x : ℝ in Set.Ioi t, Real.exp (-(x ^ 2) / 2)

/-- The Gaussian tail integral inside the Mills ratio. -/
noncomputable def theorem8MillsTail (t : ℝ) : ℝ := ∫ x : ℝ in Set.Ioi t, Real.exp (-(x ^ 2) / 2)

/-- Appendix C, Theorem 8: derivative of the Gaussian tail in Mills ratio. -/
theorem theorem8MillsTail_hasDerivAt (t : ℝ) :
    HasDerivAt theorem8MillsTail (-(Real.exp (-(t ^ 2) / 2))) t := by
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
      (∫ x : ℝ in Set.Iic u, f x) =
        (∫ x : ℝ in Set.Iic (0 : ℝ), f x) + ∫ x : ℝ in (0 : ℝ)..u, f x := by
    have hfi0 : IntegrableOn f (Set.Iic (0 : ℝ)) := hfint.integrableOn
    have hfiu : IntegrableOn f (Set.Iic u) := hfint.integrableOn
    have hsub := intervalIntegral.integral_Iic_sub_Iic
      (f := f) (a := (0 : ℝ)) (b := u) hfi0 hfiu
    linarith
  have hIic_deriv : HasDerivAt
      (fun u : ℝ => ∫ x : ℝ in Set.Iic u, f x) (f t) t := by
    have hderiv : HasDerivAt
        (fun u : ℝ =>
          (∫ x : ℝ in Set.Iic (0 : ℝ), f x) + ∫ x : ℝ in (0 : ℝ)..u, f x)
        (f t) t :=
      (hcont.integral_hasStrictDerivAt (0 : ℝ) t).hasDerivAt.const_add
        (∫ x : ℝ in Set.Iic (0 : ℝ), f x)
    refine hderiv.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun u => hIic_eq u
  have htail_eq : (fun u : ℝ => theorem8MillsTail u) =ᶠ[nhds t]
      (fun u : ℝ => (∫ x : ℝ, f x) - ∫ x : ℝ in Set.Iic u, f x) :=
    Filter.Eventually.of_forall fun u => by
      have hsum := intervalIntegral.integral_Iic_add_Ioi
        (f := f) (b := u) (μ := volume) hfint.integrableOn hfint.integrableOn
      dsimp [theorem8MillsTail]
      dsimp [f] at hsum ⊢
      linarith
  exact hIic_deriv.const_sub (∫ x : ℝ, f x) |>.congr_of_eventuallyEq htail_eq

/--
Appendix C, Theorem 8: the Gaussian tail integral in the Mills ratio tends to
zero at `+∞`.
-/
theorem theorem8MillsTail_tendsto_atTop_zero :
    Filter.Tendsto theorem8MillsTail Filter.atTop (nhds 0) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2)
  have hfint : Integrable f := by
    have hbase := integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by norm_num)
    convert hbase using 1
    ext x
    dsimp [f]
    ring_nf
  have hanti : Antitone (fun t : ℝ => Set.Ioi t) := by
    intro a b hab x hx
    exact hab.trans_lt hx
  have hInter : (⋂ t : ℝ, Set.Ioi t) = ∅ := by
    ext x
    constructor
    · intro hx
      have hxlt : x < x := by
        simpa using (Set.mem_iInter.mp hx x)
      exact (lt_irrefl x hxlt).elim
    · intro hx
      simp at hx
  have htail :=
    tendsto_setIntegral_of_antitone
      (μ := volume) (s := fun t : ℝ => Set.Ioi t) (f := f)
      (fun _ => measurableSet_Ioi) hanti ⟨(0 : ℝ), hfint.integrableOn⟩
  simpa [theorem8MillsTail, f, hInter] using htail

/-- Appendix C, Theorem 8: derivative of the concrete Mills ratio. -/
theorem theorem8MillsRatio_hasDerivAt (t : ℝ) :
    HasDerivAt theorem8MillsRatio (t * theorem8MillsRatio t - 1) t := by
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (u ^ 2 / 2))
      (t * Real.exp (t ^ 2 / 2)) t := by
    have hinner : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
      simpa using ((hasDerivAt_id t).pow 2).div_const (2 : ℝ)
    convert hinner.exp using 1
    ring
  have htail := theorem8MillsTail_hasDerivAt t
  have hprod := hexp.mul htail
  unfold theorem8MillsRatio at hprod ⊢
  convert hprod using 1
  rw [mul_neg, sub_eq_add_neg]
  congr 1
  · rw [← mul_assoc]
    rfl
  · congr 1
    rw [← Real.exp_add]
    rw [show t ^ 2 / 2 + -(t ^ 2) / 2 = 0 by ring]
    rw [Real.exp_zero]

/--
Appendix C, Theorem 8: derivative of the Mills-ratio derivative expression.
Equivalently, for `R(t)=theorem8MillsRatio t`, this is the second-derivative
identity `R''(t) = (t^2+1)R(t)-t`.
-/
theorem theorem8MillsRatio_derivExpr_hasDerivAt (t : ℝ) :
    HasDerivAt
      (fun u => u * theorem8MillsRatio u - 1)
      (((t ^ 2 + 1) * theorem8MillsRatio t) - t) t := by
  have hmul :=
    (hasDerivAt_id t).mul (theorem8MillsRatio_hasDerivAt t)
  have hsub := hmul.sub_const (1 : ℝ)
  convert hsub using 1
  simp [id]
  ring

/--
Appendix C, Theorem 8: change of variables in the Gaussian tail appearing in
the Mills-ratio comparison with `g`.
-/
theorem theorem8MillsRatio_tail_changeOfVariables (t : ℝ) :
    (∫ x : ℝ in Set.Ioi (-(Real.sqrt 2 * t)),
        Real.exp (-(x ^ 2) / 2)) =
      Real.sqrt 2 * ∫ x : ℝ in Set.Iic t, Real.exp (-(x ^ 2)) := by
  let h : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2)
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2))
  have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := hsqrt2_pos.ne'
  have hscale_raw :=
    integral_comp_mul_left_Ioi (g := h) (a := -t) hsqrt2_pos
  have hscale :
      Real.sqrt 2 *
          (∫ x : ℝ in Set.Ioi (-t), h (Real.sqrt 2 * x)) =
        ∫ x : ℝ in Set.Ioi (-(Real.sqrt 2 * t)), h x := by
    rw [hscale_raw]
    simp only [smul_eq_mul]
    rw [show Real.sqrt 2 * -t = -(Real.sqrt 2 * t) by ring]
    field_simp [hsqrt2_ne]
  have hcomp :
      (∫ x : ℝ in Set.Ioi (-t), h (Real.sqrt 2 * x)) =
        ∫ x : ℝ in Set.Ioi (-t), f x := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _hx
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    simp [h, f, mul_pow, hsqrt_sq]
    ring_nf
  have hsymm :
      (∫ x : ℝ in Set.Ioi (-t), f x) =
        ∫ x : ℝ in Set.Iic t, f x := by
    calc
      (∫ x : ℝ in Set.Ioi (-t), f x)
          = ∫ x : ℝ in Set.Ioi (-t), f (-x) := by
              refine setIntegral_congr_fun measurableSet_Ioi ?_
              intro x _hx
              simp [f]
      _ = ∫ x : ℝ in Set.Iic t, f x := by
              simpa using (integral_comp_neg_Ioi (c := -t) (f := f))
  rw [← hscale, hcomp, hsymm]

/--
Appendix C, Theorem 8: the paper's value relation between Mills ratio and
`g(t) = (1 + erf(t)) / exp(-t^2)`.
-/
theorem theorem8MillsRatio_value_relation (t : ℝ) :
    theorem8MillsRatio (-(Real.sqrt 2 * t)) =
      Real.sqrt (Real.pi / 2) * theorem8GaussianG theorem8Erf t := by
  have htail := theorem8MillsRatio_tail_changeOfVariables t
  have hI := theorem8Gaussian_integral_Iic_eq_erf t
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hexp :
      Real.exp (((-(Real.sqrt 2 * t)) ^ 2) / 2) =
        Real.exp (t ^ 2) := by
    congr 1
    rw [neg_sq, mul_pow, hsqrt2_sq]
    ring
  have hconst :
      Real.sqrt 2 * (Real.sqrt Real.pi / 2) =
        Real.sqrt (Real.pi / 2) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).1
    have hpi : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
      Real.sq_sqrt Real.pi_pos.le
    have hpi2 : (Real.sqrt (Real.pi / 2)) ^ 2 = Real.pi / 2 :=
      Real.sq_sqrt (show 0 ≤ Real.pi / 2 by positivity)
    nlinarith
  unfold theorem8MillsRatio theorem8GaussianG
  rw [htail, hI, hexp]
  rw [← mul_assoc (Real.sqrt 2) (Real.sqrt Real.pi / 2)
    (1 + theorem8Erf t), hconst]
  rw [Real.exp_neg, div_inv_eq_mul]
  ring

/-- Appendix C, Theorem 8: positivity of the concrete Mills ratio. -/
theorem theorem8MillsRatio_pos (y : ℝ) :
    0 < theorem8MillsRatio y := by
  let t : ℝ := -y / Real.sqrt 2
  have hrel := theorem8MillsRatio_value_relation t
  have hsqrt2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hy : -(Real.sqrt 2 * t) = y := by
    dsimp [t]
    field_simp [hsqrt2]
  rw [hy] at hrel
  rw [hrel]
  exact mul_pos (by positivity) (theorem8GaussianG_pos (theorem8Erf_one_add_pos t))

/--
The external Mills-ratio inequality used in Appendix C, Theorem 8.

The paper cites Sampford [21, Eq. (3)] for the statement that
`d/dt (1 / R(t)) < 1`.  Lean records exactly that cited analytic input as a
named hypothesis, so the local proof can follow the paper from Mills ratio to
equation (C.10).
-/
def theorem8SampfordMillsBound (R : ℝ → ℝ) : Prop := ∀ t, ∃ d, HasDerivAt (fun u => (R u)⁻¹) d t ∧ d < 1

/--
Appendix C, Theorem 8: the scalar inequality equivalent to Sampford's
derivative bound once the Mills-ratio derivative is known.
-/
def theorem8MillsQuadraticBound (R : ℝ → ℝ) : Prop := ∀ t, 0 < (R t) ^ 2 + t * R t - 1

/--
Appendix C, Theorem 8: Sampford's lower comparison function for the Mills
ratio.  The inequality `theorem8SampfordLowerComparison t < R t` is
algebraically equivalent to the scalar quadratic bound
`0 < R(t)^2 + t R(t) - 1`, using positivity of `R`.
-/
noncomputable def theorem8SampfordLowerComparison (t : ℝ) : ℝ := (Real.sqrt (t ^ 2 + 4) - t) / 2

/-- Appendix C, Theorem 8: Sampford's comparison function is positive. -/
theorem theorem8SampfordLowerComparison_pos (t : ℝ) :
    0 < theorem8SampfordLowerComparison t := by
  unfold theorem8SampfordLowerComparison
  have hsqrt_gt_abs : |t| < Real.sqrt (t ^ 2 + 4) := by
    rw [Real.lt_sqrt (abs_nonneg t)]
    nlinarith [sq_abs t]
  have ht_lt : t < Real.sqrt (t ^ 2 + 4) :=
    (le_abs_self t).trans_lt hsqrt_gt_abs
  linarith

/--
Appendix C, Theorem 8: for nonnegative arguments, Sampford's lower comparison
is bounded by `1`.  This is the bound used to prove the comparison gap vanishes
at `+∞`.
-/
theorem theorem8SampfordLowerComparison_le_one_of_nonneg {t : ℝ}
    (ht : 0 ≤ t) :
    theorem8SampfordLowerComparison t ≤ 1 := by
  unfold theorem8SampfordLowerComparison
  have hsqrt_le : Real.sqrt (t ^ 2 + 4) ≤ t + 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  linarith

/--
Appendix C, Theorem 8: the Sampford comparison function is the positive root
of `x^2 + t*x - 1 = 0`.
-/
theorem theorem8SampfordLowerComparison_quadratic_eq (t : ℝ) :
    (theorem8SampfordLowerComparison t) ^ 2 +
        t * theorem8SampfordLowerComparison t - 1 = 0 := by
  unfold theorem8SampfordLowerComparison
  have hsqrt_sq : (Real.sqrt (t ^ 2 + 4)) ^ 2 = t ^ 2 + 4 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg t])
  nlinarith

/--
Appendix C, Theorem 8: derivative of Sampford's lower comparison function.
-/
theorem theorem8SampfordLowerComparison_hasDerivAt (t : ℝ) :
    HasDerivAt theorem8SampfordLowerComparison
      ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2) t := by
  have hinner : HasDerivAt (fun u : ℝ => u ^ 2 + 4) (2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).add_const (4 : ℝ) using 1
    simp [id]
  have hpos : t ^ 2 + 4 ≠ 0 := by
    positivity
  have hsqrt := hinner.sqrt hpos
  have hsub := hsqrt.sub (hasDerivAt_id t)
  have hdiv := hsub.div_const (2 : ℝ)
  unfold theorem8SampfordLowerComparison
  convert hdiv using 1
  have hsqrt_ne : Real.sqrt (t ^ 2 + 4) ≠ 0 :=
    (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])).ne'
  field_simp [hsqrt_ne]

/--
Appendix C, Theorem 8: a small algebraic fact behind Sampford's comparison
proof.  The comparison function is larger than the reciprocal of the square
root appearing in its derivative.
-/
theorem theorem8SampfordLowerComparison_inv_sqrt_lt (t : ℝ) :
    (Real.sqrt (t ^ 2 + 4))⁻¹ < theorem8SampfordLowerComparison t := by
  let L := theorem8SampfordLowerComparison t
  let s := Real.sqrt (t ^ 2 + 4)
  have hLpos : 0 < L := theorem8SampfordLowerComparison_pos t
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hroot : L ^ 2 + t * L - 1 = 0 :=
    theorem8SampfordLowerComparison_quadratic_eq t
  have hs_eq : s = 2 * L + t := by
    dsimp [L, s, theorem8SampfordLowerComparison]
    ring
  have hLs : L * s = 1 + L ^ 2 := by
    rw [hs_eq]
    nlinarith
  have hone : 1 < L * s := by
    rw [hLs]
    nlinarith [sq_pos_of_ne_zero hLpos.ne']
  exact (inv_lt_iff_one_lt_mul₀ hspos).2 hone

/--
Appendix C, Theorem 8: the derivative correction term in Sampford's
comparison proof is positive.
-/
theorem theorem8SampfordLowerComparison_sq_add_deriv_pos (t : ℝ) :
    0 <
      (theorem8SampfordLowerComparison t) ^ 2 +
        ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2) := by
  let L := theorem8SampfordLowerComparison t
  let s := Real.sqrt (t ^ 2 + 4)
  have hLpos : 0 < L := theorem8SampfordLowerComparison_pos t
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hderiv_eq : ((t / s - 1) / 2) = -L / s := by
    dsimp [L, s, theorem8SampfordLowerComparison]
    field_simp [hspos.ne']
    ring
  have hinv_lt : s⁻¹ < L := theorem8SampfordLowerComparison_inv_sqrt_lt t
  have hgap : 0 < L - s⁻¹ := sub_pos.mpr hinv_lt
  calc
    0 < L * (L - s⁻¹) := mul_pos hLpos hgap
    _ = L ^ 2 + ((t / s - 1) / 2) := by
      rw [hderiv_eq]
      field_simp [hspos.ne']
      ring

/--
Appendix C, Theorem 8: gap used to prove Sampford's lower bound.  Multiplying
`theorem8SampfordGap t > 0` by `exp(t^2/2)` gives
`theorem8SampfordLowerComparison t < theorem8MillsRatio t`.
-/
noncomputable def theorem8SampfordGap (t : ℝ) : ℝ :=
  theorem8MillsTail t -
    theorem8SampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)

/-- Appendix C, Theorem 8: derivative of the Sampford lower-bound gap. -/
theorem theorem8SampfordGap_hasDerivAt (t : ℝ) :
    HasDerivAt theorem8SampfordGap
      (-(Real.exp (-(t ^ 2) / 2) *
          ((theorem8SampfordLowerComparison t) ^ 2 +
            ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2)))) t := by
  let L := theorem8SampfordLowerComparison
  let E : ℝ → ℝ := fun u => Real.exp (-(u ^ 2) / 2)
  have htail := theorem8MillsTail_hasDerivAt t
  have hL : HasDerivAt L
      ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2) t := by
    simpa [L] using theorem8SampfordLowerComparison_hasDerivAt t
  have hE : HasDerivAt E (-(t * E t)) t := by
    have hinner : HasDerivAt (fun u : ℝ => -(u ^ 2) / 2) (-t) t := by
      convert (((hasDerivAt_id t).pow 2).neg.div_const (2 : ℝ)) using 1
      ring_nf
      simp [id]
    convert hinner.exp using 1
    dsimp [E]
    ring
  have hprod := hL.mul hE
  have hsub := htail.sub hprod
  unfold theorem8SampfordGap theorem8MillsTail
  dsimp [L, E] at hsub ⊢
  convert hsub using 1
  have hroot :
      -((theorem8SampfordLowerComparison t) ^ 2) =
        t * theorem8SampfordLowerComparison t - 1 := by
    have h := theorem8SampfordLowerComparison_quadratic_eq t
    nlinarith
  have hroot_mul :
      Real.exp (t ^ 2 * (-1 / 2)) *
          (-((theorem8SampfordLowerComparison t) ^ 2)) =
        Real.exp (t ^ 2 * (-1 / 2)) *
          (t * theorem8SampfordLowerComparison t - 1) := by
    rw [hroot]
  ring_nf
  ring_nf at hroot_mul
  nlinarith

/--
Appendix C, Theorem 8: the Sampford gap has strictly negative derivative.
-/
theorem theorem8SampfordGap_deriv_neg (t : ℝ) :
    let d :=
      -(Real.exp (-(t ^ 2) / 2) *
          ((theorem8SampfordLowerComparison t) ^ 2 +
            ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2)))
    d < 0 := by
  dsimp
  have hpos :=
    theorem8SampfordLowerComparison_sq_add_deriv_pos t
  exact neg_neg_of_pos (mul_pos (Real.exp_pos _) hpos)

/-- Appendix C, Theorem 8: the Gaussian exponential factor decays at `+∞`. -/
theorem theorem8GaussianExpFactor_tendsto_atTop_zero :
    Filter.Tendsto (fun t : ℝ => Real.exp (-(t ^ 2) / 2))
      Filter.atTop (nhds 0) := by
  have harg :
      Filter.Tendsto (fun t : ℝ => (-(1 / 2 : ℝ)) * t ^ 2)
        Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_const_mul_pow_atTop (n := 2) (by norm_num) (by norm_num)
  refine (Real.tendsto_exp_atBot.comp harg).congr' ?_
  filter_upwards with t
  have hpow : (-(t ^ 2) / 2 : ℝ) = (-(1 / 2 : ℝ)) * t ^ 2 := by
    ring
  simpa [Function.comp_apply, hpow]

/--
Appendix C, Theorem 8: Sampford's gap tends to zero at `+∞`.
-/
theorem theorem8SampfordGap_tendsto_atTop_zero :
    Filter.Tendsto theorem8SampfordGap Filter.atTop (nhds 0) := by
  have hprod :
      Filter.Tendsto
        (fun t : ℝ =>
          theorem8SampfordLowerComparison t * Real.exp (-(t ^ 2) / 2))
        Filter.atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ theorem8GaussianExpFactor_tendsto_atTop_zero
    · exact Filter.Eventually.of_forall fun t =>
        mul_nonneg (le_of_lt (theorem8SampfordLowerComparison_pos t))
          (le_of_lt (Real.exp_pos _))
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact mul_le_of_le_one_left (le_of_lt (Real.exp_pos _))
        (theorem8SampfordLowerComparison_le_one_of_nonneg ht)
  simpa [theorem8SampfordGap] using
    theorem8MillsTail_tendsto_atTop_zero.sub hprod

/--
Appendix C, Theorem 8: if the Sampford gap tends to zero at `+∞`, then it is
positive everywhere because its derivative is strictly negative.
-/
theorem theorem8SampfordGap_pos_of_tendsto_atTop_zero
    (hlim : Filter.Tendsto theorem8SampfordGap Filter.atTop (nhds 0)) :
    ∀ t, 0 < theorem8SampfordGap t := by
  have hanti : StrictAnti theorem8SampfordGap := by
    refine strictAnti_of_hasDerivAt_neg
      (f' := fun x =>
        -(Real.exp (-(x ^ 2) / 2) *
          ((theorem8SampfordLowerComparison x) ^ 2 +
            ((x / Real.sqrt (x ^ 2 + 4) - 1) / 2)))) ?_ ?_
    · exact theorem8SampfordGap_hasDerivAt
    · intro x
      exact theorem8SampfordGap_deriv_neg x
  intro t
  have hnext_nonneg : 0 ≤ theorem8SampfordGap (t + 1) := by
    refine le_of_tendsto_of_tendsto hlim tendsto_const_nhds ?_
    filter_upwards [Filter.eventually_ge_atTop (t + 1)] with y hy
    by_cases hy_eq : y = t + 1
    · simp [hy_eq]
    · have hlt : t + 1 < y := lt_of_le_of_ne hy (Ne.symm hy_eq)
      exact le_of_lt (hanti hlt)
  have hstrict : theorem8SampfordGap (t + 1) < theorem8SampfordGap t :=
    hanti (by linarith)
  linarith

/--
Appendix C, Theorem 8: positivity of the Sampford gap is exactly the explicit
lower bound on the concrete Mills ratio.
-/
theorem theorem8SampfordLowerComparison_lt_millsRatio_of_gap_pos
    (hgap : ∀ t, 0 < theorem8SampfordGap t) :
    ∀ t, theorem8SampfordLowerComparison t < theorem8MillsRatio t := by
  intro t
  have hgap_t := hgap t
  have htail_lt :
      theorem8SampfordLowerComparison t * Real.exp (-(t ^ 2) / 2) <
        theorem8MillsTail t := by
    simpa [theorem8SampfordGap, sub_pos] using hgap_t
  have hmul := mul_lt_mul_of_pos_left htail_lt (Real.exp_pos (t ^ 2 / 2))
  unfold theorem8MillsRatio
  calc
    theorem8SampfordLowerComparison t
        = Real.exp (t ^ 2 / 2) *
            (theorem8SampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)) := by
          have hexp :
              Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2) / 2) = 1 := by
            rw [← Real.exp_add]
            have : t ^ 2 / 2 + -(t ^ 2) / 2 = 0 := by ring
            rw [this, Real.exp_zero]
          calc
            theorem8SampfordLowerComparison t =
                theorem8SampfordLowerComparison t *
                  (Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2) / 2)) := by
              rw [hexp]
              ring
            _ = Real.exp (t ^ 2 / 2) *
                (theorem8SampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)) := by
              ring
    _ < Real.exp (t ^ 2 / 2) * theorem8MillsTail t := hmul

/--
Appendix C, Theorem 8: once the explicit gap limit is known, Sampford's lower
comparison bound follows for the concrete Mills ratio.
-/
theorem theorem8SampfordLowerComparison_lt_millsRatio_of_gap_tendsto_atTop_zero
    (hlim : Filter.Tendsto theorem8SampfordGap Filter.atTop (nhds 0)) :
    ∀ t, theorem8SampfordLowerComparison t < theorem8MillsRatio t :=
  theorem8SampfordLowerComparison_lt_millsRatio_of_gap_pos
    (theorem8SampfordGap_pos_of_tendsto_atTop_zero hlim)

/--
Appendix C, Theorem 8: Sampford's explicit lower comparison holds for the
concrete Gaussian Mills ratio.
-/
theorem theorem8SampfordLowerComparison_lt_millsRatio :
    ∀ t, theorem8SampfordLowerComparison t < theorem8MillsRatio t :=
  theorem8SampfordLowerComparison_lt_millsRatio_of_gap_tendsto_atTop_zero
    theorem8SampfordGap_tendsto_atTop_zero

/--
Appendix C, Theorem 8: Sampford's lower bound implies the scalar Mills
quadratic inequality used by the paper.
-/
theorem theorem8MillsQuadraticBound_of_sampford_lower
    {R : ℝ → ℝ}
    (hRpos : ∀ t, 0 < R t)
    (hlower : ∀ t, theorem8SampfordLowerComparison t < R t) :
    theorem8MillsQuadraticBound R := by
  intro t
  let L := theorem8SampfordLowerComparison t
  have hLpos : 0 < L := theorem8SampfordLowerComparison_pos t
  have hroot : L ^ 2 + t * L - 1 = 0 := theorem8SampfordLowerComparison_quadratic_eq t
  have hsum_pos : 0 < R t + L + t := by
    have hR_gt_L : L < R t := hlower t
    have hL_formula : 2 * L + t = Real.sqrt (t ^ 2 + 4) := by
      dsimp [L, theorem8SampfordLowerComparison]
      ring
    have hsqrt_pos : 0 < Real.sqrt (t ^ 2 + 4) :=
      Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
    nlinarith
  have hdiff_pos : 0 < R t - L := sub_pos.mpr (hlower t)
  calc
    0 < (R t - L) * (R t + L + t) := mul_pos hdiff_pos hsum_pos
    _ = (R t) ^ 2 + t * R t - 1 := by
      calc
        (R t - L) * (R t + L + t)
            = (R t) ^ 2 + t * R t - (L ^ 2 + t * L) := by ring
        _ = (R t) ^ 2 + t * R t - 1 := by linarith

/--
Appendix C, Theorem 8: for the concrete Mills ratio, it suffices to prove
Sampford's explicit lower comparison bound.
-/
theorem theorem8MillsQuadraticBound_of_sampford_lower_concrete
    (hlower : ∀ t, theorem8SampfordLowerComparison t < theorem8MillsRatio t) :
    theorem8MillsQuadraticBound theorem8MillsRatio :=
  theorem8MillsQuadraticBound_of_sampford_lower
    theorem8MillsRatio_pos hlower

/--
Appendix C, Theorem 8: concrete scalar Mills quadratic inequality.
-/
theorem theorem8MillsQuadraticBound_concrete :
    theorem8MillsQuadraticBound theorem8MillsRatio :=
  theorem8MillsQuadraticBound_of_sampford_lower_concrete
    theorem8SampfordLowerComparison_lt_millsRatio

/--
Appendix C, Theorem 8: the log-convexity/determinant form of the remaining
Mills-ratio inequality.  For the concrete `R`, the determinant expression is
`R R'' - (R')^2`; expanding the Riccati formulas gives exactly
`R^2 + tR - 1`.
-/
def theorem8MillsDeterminantBound (R : ℝ → ℝ) : Prop := ∀ t, 0 < R t * (((t ^ 2 + 1) * R t) - t) - (t * R t - 1) ^ 2

/--
Appendix C, Theorem 8: the determinant/log-convex Mills bound is algebraically
equivalent to the quadratic Sampford bound once the concrete Riccati derivative
formulas are known.
-/
theorem theorem8MillsQuadraticBound_of_determinant
    (hdet : theorem8MillsDeterminantBound theorem8MillsRatio) :
    theorem8MillsQuadraticBound theorem8MillsRatio := by
  intro t
  have h := hdet t
  convert h using 1
  ring

/--
Appendix C, Theorem 8: a positive differentiable Mills ratio satisfying the
quadratic Mills inequality has Sampford's derivative bound.
-/
theorem theorem8SampfordMillsBound_of_derivative_quadratic
    {R : ℝ → ℝ}
    (hRpos : ∀ t, 0 < R t)
    (hRderiv : ∀ t, HasDerivAt R (t * R t - 1) t)
    (hquad : theorem8MillsQuadraticBound R) :
    theorem8SampfordMillsBound R := by
  intro t
  refine ⟨- (t * R t - 1) / (R t) ^ 2, ?_, ?_⟩
  · exact (hRderiv t).inv (hRpos t).ne'
  · have hden : 0 < (R t) ^ 2 := sq_pos_of_ne_zero (hRpos t).ne'
    have h := hquad t
    rw [div_lt_one hden]
    linarith

/--
Appendix C, Theorem 8: for the concrete Mills ratio, it remains only to prove
the scalar quadratic Mills inequality.
-/
theorem theorem8SampfordMillsBound_of_quadratic
    (hquad : theorem8MillsQuadraticBound theorem8MillsRatio) :
    theorem8SampfordMillsBound theorem8MillsRatio :=
  theorem8SampfordMillsBound_of_derivative_quadratic
    theorem8MillsRatio_pos theorem8MillsRatio_hasDerivAt hquad

/--
Appendix C, Theorem 8: concrete Sampford Mills-ratio derivative bound.
-/
theorem theorem8SampfordMillsBound_concrete :
    theorem8SampfordMillsBound theorem8MillsRatio := theorem8SampfordMillsBound_of_quadratic theorem8MillsQuadraticBound_concrete

/--
Appendix C, Theorem 8: after reducing Sampford to the quadratic form, it also
suffices to prove the concrete Mills log-convexity determinant.
-/
theorem theorem8SampfordMillsBound_of_determinant
    (hdet : theorem8MillsDeterminantBound theorem8MillsRatio) :
    theorem8SampfordMillsBound theorem8MillsRatio :=
  theorem8SampfordMillsBound_of_quadratic
    (theorem8MillsQuadraticBound_of_determinant hdet)

/--
Appendix C, Theorem 8 relation between the Mills ratio `R` and the paper's
`g`.  The constants are left explicit so the statement is usable before
committing to a particular definition of `erf` in Lean:
`1 / g(t) = c * 1 / R(-q t)`.
-/
def theorem8MillsToGRelation (R g : ℝ → ℝ) (c q : ℝ) : Prop := ∀ t, (g t)⁻¹ = c * (R (-(q * t)))⁻¹

/--
Appendix C, Theorem 8: the paper states the Mills-to-`g` relation as a value
identity `R(-q t) = c * g(t)`.  This lemma converts that source-facing identity
to the inverse relation used in the C.10 derivative calculation.
-/
theorem theorem8MillsToGRelation_of_value_relation
    {R g : ℝ → ℝ} {c q : ℝ} (hc : c ≠ 0)
    (hrel : ∀ t, R (-(q * t)) = c * g t) :
    theorem8MillsToGRelation R g c q := by
  intro t
  rw [hrel t]
  by_cases hg : g t = 0
  · simp [hg]
  · field_simp [hc, hg]

/-- Appendix C, Theorem 8: the constants in the Mills-ratio change of variables. -/
theorem paper_theorem8_mills_constants_mul :
    Real.sqrt (Real.pi / 2) * Real.sqrt 2 = Real.sqrt Real.pi := by
  have hpi2 : 0 ≤ Real.pi / 2 := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).1
  calc
    (Real.sqrt (Real.pi / 2) * Real.sqrt 2) ^ 2
        = (Real.pi / 2) * 2 := by
          rw [mul_pow, Real.sq_sqrt hpi2, Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]
    _ = Real.pi := by ring
    _ = (Real.sqrt Real.pi) ^ 2 := by
          rw [Real.sq_sqrt Real.pi_pos.le]

/--
Appendix C, Theorem 8, Sampford's Mills-ratio inequality implies equation
(C.10) for the paper's function `g`.
-/
theorem paper_theorem8_c10_of_sampford_mills
    {R g : ℝ → ℝ} {c q : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hcq : c * q = Real.sqrt Real.pi)
    (hrel : theorem8MillsToGRelation R g c q)
    (hsamp : theorem8SampfordMillsBound R) :
    ∀ t, ∃ d,
      HasDerivAt (fun u => (g u)⁻¹) d t ∧ -Real.sqrt Real.pi < d := by
  intro t
  obtain ⟨dR, hdR, hdRlt⟩ := hsamp (-(q * t))
  have hlin : HasDerivAt (fun u : ℝ => -(q * u)) (-q) t := by
    have hmul : HasDerivAt (fun u : ℝ => q * u) q t := by
      simpa using (hasDerivAt_id t).const_mul q
    simpa using hmul.neg
  have hcomp : HasDerivAt (fun u : ℝ => (R (-(q * u)))⁻¹) (dR * (-q)) t := by
    simpa using hdR.comp t hlin
  have hscaled :
      HasDerivAt (fun u : ℝ => c * (R (-(q * u)))⁻¹)
        (c * (dR * (-q))) t :=
    hcomp.const_mul c
  have hderiv :
      HasDerivAt (fun u : ℝ => (g u)⁻¹) (c * (dR * (-q))) t := by
    have hfun : (fun u : ℝ => (g u)⁻¹) =
        fun u : ℝ => c * (R (-(q * u)))⁻¹ := by
      funext u
      exact hrel u
    simpa [hfun] using hscaled
  have hcoef : 0 < c * q := mul_pos hc hq
  have hlt : c * q * dR < c * q := by
    simpa [mul_assoc] using mul_lt_mul_of_pos_left hdRlt hcoef
  refine ⟨c * (dR * (-q)), hderiv, ?_⟩
  nlinarith

/--
Appendix C, Theorem 8, equation (C.9) from Sampford via the mean-value step.
-/
theorem paper_theorem8_c9_positive_of_sampford_mills
    {R g : ℝ → ℝ} {c q t δ : ℝ} (hδ : 0 < δ) (hgpos : 0 < g t)
    (hc : 0 < c) (hq : 0 < q) (hcq : c * q = Real.sqrt Real.pi)
    (hrel : theorem8MillsToGRelation R g c q)
    (hsamp : theorem8SampfordMillsBound R)
    (hcont : ContinuousOn (fun u => (g u)⁻¹) (Set.Icc t (t + δ))) :
    0 < theorem8GaussianC9Bracket g δ t := by
  have hderiv_global :=
    paper_theorem8_c10_of_sampford_mills
      (R := R) (g := g) (c := c) (q := q) hc hq hcq hrel hsamp
  simpa [theorem8GaussianC9Bracket] using
    (paper_theorem8_c9_positive_of_mills_mvt
      (g := g) (t := t) (δ := δ) hδ hgpos hcont
      (fun u _hu => hderiv_global u))

/--
Appendix C, Theorem 8 derivative-factorization step: once differentiating
the C.6 left-hand side factors into a positive prefactor times the C.9
bracket, positivity of C.9 gives a positive derivative.
-/
theorem paper_theorem8_derivative_pos_of_c9_factorization
    {F' factor g : ℝ → ℝ} {δ : ℝ}
    (hfactor :
      ∀ t, F' t = factor t * theorem8GaussianC9Bracket g δ t)
    (hfactor_pos : ∀ t, 0 < factor t)
    (hc9 : ∀ t, 0 < theorem8GaussianC9Bracket g δ t) :
    ∀ t, 0 < F' t := by
  intro t
  rw [hfactor t]
  exact mul_pos (hfactor_pos t) (hc9 t)

/--
Appendix C, Theorem 8, C.6 positivity from the paper's three analytic inputs:
limit `0` at `-∞`, positive derivative after the C.9 factorization, and
Sampford's Mills-ratio bound for equation (C.10).
-/
theorem paper_theorem8_c6_positive_of_sampford_mills
    {R g F F' factor : ℝ → ℝ} {c q δ : ℝ} (hδ : 0 < δ)
    (hc : 0 < c) (hq : 0 < q) (hcq : c * q = Real.sqrt Real.pi)
    (hrel : theorem8MillsToGRelation R g c q)
    (hsamp : theorem8SampfordMillsBound R)
    (hgpos : ∀ t, 0 < g t)
    (hcont : ∀ t, ContinuousOn (fun u => (g u)⁻¹) (Set.Icc t (t + δ)))
    (hFderiv : ∀ t, HasDerivAt F (F' t) t)
    (hFlim : Filter.Tendsto F Filter.atBot (nhds 0))
    (hfactor :
      ∀ t, F' t = factor t * theorem8GaussianC9Bracket g δ t)
    (hfactor_pos : ∀ t, 0 < factor t) :
    ∀ t, 0 < F t := by
  have hc9 : ∀ t, 0 < theorem8GaussianC9Bracket g δ t := by
    intro t
    exact paper_theorem8_c9_positive_of_sampford_mills
      (R := R) (g := g) (c := c) (q := q) (t := t) (δ := δ)
      hδ (hgpos t) hc hq hcq hrel hsamp (hcont t)
  exact paper_theorem8_positive_of_deriv_pos_tendsto_atBot_zero
    hFderiv
    (paper_theorem8_derivative_pos_of_c9_factorization
      (F' := F') (factor := factor) (g := g) (δ := δ)
      hfactor hfactor_pos hc9)
    hFlim

/--
Appendix C, Theorem 8 with the paper's concrete Mills-ratio constants
`R(-sqrt(2)t) = sqrt(pi/2) g(t)` (equivalently stated for inverses).
-/
theorem paper_theorem8_c6_positive_of_sampford_mills_concrete
    {R g F F' factor : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hrel :
      theorem8MillsToGRelation R g (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : theorem8SampfordMillsBound R)
    (hgpos : ∀ t, 0 < g t)
    (hcont : ∀ t, ContinuousOn (fun u => (g u)⁻¹) (Set.Icc t (t + δ)))
    (hFderiv : ∀ t, HasDerivAt F (F' t) t)
    (hFlim : Filter.Tendsto F Filter.atBot (nhds 0))
    (hfactor :
      ∀ t, F' t = factor t * theorem8GaussianC9Bracket g δ t)
    (hfactor_pos : ∀ t, 0 < factor t) :
    ∀ t, 0 < F t :=
  paper_theorem8_c6_positive_of_sampford_mills
    (R := R) (g := g) (F := F) (F' := F') (factor := factor)
    (c := Real.sqrt (Real.pi / 2)) (q := Real.sqrt 2) (δ := δ)
    hδ (by positivity) (by positivity) paper_theorem8_mills_constants_mul
    hrel hsamp hgpos hcont hFderiv hFlim hfactor hfactor_pos

/--
Appendix C, Theorem 8 for the explicit C.6 formula.

The remaining assumptions are exactly the analytic bridges not yet expanded
locally: Sampford's cited Mills-ratio derivative bound, the Mills-to-`g`
identity for the chosen `erf`, continuity of `1/g` on the MVT intervals, the
`-∞` limit of the C.6 expression, and the derivative calculation/factorization
from (C.8) to (C.9).
-/
theorem paper_theorem8_c6_formula_positive_of_sampford_mills
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hone : ∀ t, 0 < 1 + erf t)
    (hrel :
      theorem8MillsToGRelation R (theorem8GaussianG erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : theorem8SampfordMillsBound R)
    (hcont :
      ∀ t,
        ContinuousOn
          (fun u => (theorem8GaussianG erf u)⁻¹) (Set.Icc t (t + δ)))
    (hlim :
      Filter.Tendsto (fun t => theorem8GaussianC6LHS erf J δ t)
        Filter.atBot (nhds 0))
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS erf J δ u)
          (theorem8GaussianC8PositiveFactor erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS erf J δ t :=
  paper_theorem8_c6_positive_of_sampford_mills_concrete
    (R := R) (g := theorem8GaussianG erf)
    (F := fun t => theorem8GaussianC6LHS erf J δ t)
    (F' := fun t =>
      theorem8GaussianC8PositiveFactor erf δ t *
        theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t)
    (factor := fun t => theorem8GaussianC8PositiveFactor erf δ t)
    (δ := δ) hδ hrel hsamp
    (fun t => theorem8GaussianG_pos (hone t))
    hcont hderiv_factor hlim
    (by intro t; rfl)
    (fun t => theorem8GaussianC8PositiveFactor_pos
      (hone t) (by simpa [add_comm] using hone (t + δ)))

/--
Appendix C, Theorem 8 for the explicit C.6 formula, with the continuity of
`1/g` discharged from continuity of `erf`.
-/
theorem paper_theorem8_c6_formula_positive_of_sampford_mills_of_continuous_erf
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf : Continuous erf) (hone : ∀ t, 0 < 1 + erf t)
    (hrel :
      theorem8MillsToGRelation R (theorem8GaussianG erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : theorem8SampfordMillsBound R)
    (hlim :
      Filter.Tendsto (fun t => theorem8GaussianC6LHS erf J δ t)
        Filter.atBot (nhds 0))
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS erf J δ u)
          (theorem8GaussianC8PositiveFactor erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ hone hrel hsamp
    (fun t => theorem8GaussianG_inv_continuousOn herf hone (Set.Icc t (t + δ)))
    hlim hderiv_factor

/--
Appendix C, Theorem 8 for the explicit C.6 formula, with continuity of `erf`
derived from the standard derivative formula for `erf`.
-/
theorem paper_theorem8_c6_formula_positive_of_sampford_mills_of_erf_deriv
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (hone : ∀ t, 0 < 1 + erf t)
    (hrel :
      theorem8MillsToGRelation R (theorem8GaussianG erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : theorem8SampfordMillsBound R)
    (hlim :
      Filter.Tendsto (fun t => theorem8GaussianC6LHS erf J δ t)
        Filter.atBot (nhds 0))
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS erf J δ u)
          (theorem8GaussianC8PositiveFactor erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills_of_continuous_erf
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ (theorem8Erf_continuous_of_hasDerivAt herf_deriv)
    hone hrel hsamp hlim hderiv_factor

/--
Appendix C, Theorem 8 for the explicit C.6 formula, deriving both continuity
of `erf` and positivity of `1 + erf` from standard `erf` analytic inputs.
-/
theorem paper_theorem8_c6_formula_positive_of_sampford_mills_of_erf_deriv_and_tail
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (herf_tail :
      Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0))
    (hrel :
      theorem8MillsToGRelation R (theorem8GaussianG erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : theorem8SampfordMillsBound R)
    (hlim :
      Filter.Tendsto (fun t => theorem8GaussianC6LHS erf J δ t)
        Filter.atBot (nhds 0))
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS erf J δ u)
          (theorem8GaussianC8PositiveFactor erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills_of_erf_deriv
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ herf_deriv
    (theorem8_one_add_erf_pos_of_deriv_tendsto_atBot herf_deriv herf_tail)
    hrel hsamp hlim hderiv_factor

/--
Appendix C, Theorem 8 for the explicit C.6 formula, with the C.6 limit
assembled from the paper's component limits.
-/
theorem paper_theorem8_c6_formula_positive_of_sampford_mills_of_component_limits
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (herf_tail :
      Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0))
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hratio :
      Filter.Tendsto (fun t => theorem8GaussianC6RationalTerm erf δ t)
        Filter.atBot (nhds 0))
    (hrel :
      theorem8MillsToGRelation R (theorem8GaussianG erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS erf J δ u)
          (theorem8GaussianC8PositiveFactor erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills_of_erf_deriv_and_tail
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ herf_deriv herf_tail hrel hsamp
    (theorem8GaussianC6LHS_tendsto_atBot_zero hratio herf_tail hJ_tail)
    hderiv_factor

/--
Appendix C, Theorem 8 with the Mills relation stated in the source-facing value
form `R(-sqrt(2)t) = sqrt(pi/2) g(t)`.
-/
theorem paper_theorem8_c6_formula_positive_of_component_limits_value_relation
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (herf_tail :
      Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0))
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hratio :
      Filter.Tendsto (fun t => theorem8GaussianC6RationalTerm erf δ t)
        Filter.atBot (nhds 0))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * theorem8GaussianG erf t)
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS erf J δ u)
          (theorem8GaussianC8PositiveFactor erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills_of_component_limits
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ herf_deriv herf_tail hJ_tail hratio
    (theorem8MillsToGRelation_of_value_relation
      (by positivity : Real.sqrt (Real.pi / 2) ≠ 0)
      hrel_value)
    hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the paper's concrete interval-integral
definition of `erf`.  The derivative of `erf` is now proved locally; the
remaining assumptions are the paper's left-tail/component-limit bridges, the
Mills-ratio value identity, Sampford's cited bound, and the C.6 derivative
factorization.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_erf
    {R J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_tail :
      Filter.Tendsto (fun t => 1 + theorem8Erf t) Filter.atBot (nhds 0))
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hratio :
      Filter.Tendsto
        (fun t => theorem8GaussianC6RationalTerm theorem8Erf δ t)
        Filter.atBot (nhds 0))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * theorem8GaussianG theorem8Erf t)
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS theorem8Erf J δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS theorem8Erf J δ t :=
  paper_theorem8_c6_formula_positive_of_component_limits_value_relation
    (R := R) (erf := theorem8Erf) (J := J) (δ := δ)
    hδ theorem8Erf_hasDerivAt herf_tail hJ_tail hratio
    hrel_value hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the concrete `erf`, with the `erf`
derivative and left-tail limit both proved locally.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_erf_of_component_limits
    {R J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hratio :
      Filter.Tendsto
        (fun t => theorem8GaussianC6RationalTerm theorem8Erf δ t)
        Filter.atBot (nhds 0))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * theorem8GaussianG theorem8Erf t)
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS theorem8Erf J δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS theorem8Erf J δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf
    (R := R) (J := J) (δ := δ)
    hδ theorem8Erf_tendsto_one_add_atBot_zero hJ_tail hratio
    hrel_value hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the concrete `erf`, with the `erf`
derivative, `erf` left-tail limit, and C.7 rational-term limit all proved
locally.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_erf_of_integral_tail
    {R J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * theorem8GaussianG theorem8Erf t)
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS theorem8Erf J δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS theorem8Erf J δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf_of_component_limits
    (R := R) (J := J) (δ := δ)
    hδ hJ_tail
    (theorem8GaussianC6RationalTerm_tendsto_atBot_zero_concrete δ)
    hrel_value hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the concrete `erf` and the paper's
concrete `J(t)=∫_{-∞}^t exp(-x^2)erf(x+δ)dx`.  The `J` tail limit is
derived from the integrability of its left-half-line integrand.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_erf_and_J_of_integrable
    {R : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hJ_integrable :
      IntegrableOn
        (fun x : ℝ => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ))
        (Set.Iic (0 : ℝ)))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * theorem8GaussianG theorem8Erf t)
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u =>
            theorem8GaussianC6LHS theorem8Erf
              (theorem8GaussianJ theorem8Erf δ) δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t) :
    ∀ t,
      0 <
        theorem8GaussianC6LHS theorem8Erf
          (theorem8GaussianJ theorem8Erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf_of_integral_tail
    (R := R) (J := theorem8GaussianJ theorem8Erf δ) (δ := δ)
    hδ
    (theorem8GaussianJ_tendsto_atBot_zero_of_integrableOn
      (erf := theorem8Erf) (δ := δ) hJ_integrable)
    hrel_value hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the concrete `erf` and the paper's
concrete `J`.  The derivative of `erf`, its left-tail limit, the C.7 rational
limit, and the `J` left-tail limit are all proved locally.  The remaining
assumptions are the paper's Mills-ratio value identity, Sampford's cited
Mills-ratio derivative bound, and the C.6 derivative factorization.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_erf_and_J
    {R : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * theorem8GaussianG theorem8Erf t)
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u =>
            theorem8GaussianC6LHS theorem8Erf
              (theorem8GaussianJ theorem8Erf δ) δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t) :
    ∀ t,
      0 <
        theorem8GaussianC6LHS theorem8Erf
          (theorem8GaussianJ theorem8Erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf_and_J_of_integrable
    (R := R) (δ := δ) hδ
    (theorem8GaussianJ_integrableOn_concrete δ)
    hrel_value hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the paper's concrete Mills ratio,
concrete `erf`, and concrete `J`.  The Mills-to-`g` value identity is proved by
change of variables in `theorem8MillsRatio_value_relation`; the remaining
assumptions are Sampford's cited Mills-ratio derivative bound for the concrete
Mills ratio and the C.6 derivative factorization.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J
    {δ : ℝ} (hδ : 0 < δ)
    (hsamp : theorem8SampfordMillsBound theorem8MillsRatio)
    (hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u =>
            theorem8GaussianC6LHS theorem8Erf
              (theorem8GaussianJ theorem8Erf δ) δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t) :
    ∀ t,
      0 <
        theorem8GaussianC6LHS theorem8Erf
          (theorem8GaussianJ theorem8Erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf_and_J
    (R := theorem8MillsRatio) (δ := δ)
    hδ theorem8MillsRatio_value_relation hsamp hderiv_factor

/--
Appendix C, Theorem 8: explicit derivative of the C.6 rational term for the
concrete interval-integral `erf`.
-/
noncomputable def theorem8GaussianC6RationalTermDerivative (δ t : ℝ) : ℝ :=
  let c : ℝ := 2 / Real.sqrt Real.pi
  let A : ℝ := 1 + theorem8Erf t
  let B : ℝ := 1 + theorem8Erf (t + δ)
  let E : ℝ := Real.exp (-(t ^ 2))
  let D : ℝ := Real.exp (-((t + δ) ^ 2))
  ((((c * E) * B ^ 2 * E + A * (2 * B * (c * D)) * E +
      A * B ^ 2 * (-(2 * t * E))) * (A * D + B * E) -
    (A * B ^ 2 * E) *
      ((c * E) * D + A * (-(2 * (t + δ) * D)) +
        (c * D) * E + B * (-(2 * t * E)))) /
    (A * D + B * E) ^ 2)

/--
Appendix C, Theorem 8: differentiating the concrete C.6 rational term gives
the explicit quotient-rule derivative used in equation (C.8).
-/
theorem theorem8GaussianC6RationalTerm_hasDerivAt_concrete_explicit
    (δ t : ℝ) :
    HasDerivAt
      (fun u => theorem8GaussianC6RationalTerm theorem8Erf δ u)
      (theorem8GaussianC6RationalTermDerivative δ t) t := by
  let c : ℝ := 2 / Real.sqrt Real.pi
  let A : ℝ → ℝ := fun u => 1 + theorem8Erf u
  let B : ℝ → ℝ := fun u => 1 + theorem8Erf (u + δ)
  let E : ℝ → ℝ := fun u => Real.exp (-(u ^ 2))
  let D : ℝ → ℝ := fun u => Real.exp (-((u + δ) ^ 2))
  have hA : HasDerivAt A (c * E t) t := by
    dsimp [A, c, E]
    simpa using (theorem8Erf_hasDerivAt t).const_add (1 : ℝ)
  have hshift : HasDerivAt (fun u : ℝ => u + δ) 1 t := by
    simpa [add_comm] using (hasDerivAt_id t).const_add δ
  have hB : HasDerivAt B (c * D t) t := by
    dsimp [B, c, D]
    simpa using
      ((theorem8Erf_hasDerivAt (t + δ)).comp t hshift).const_add (1 : ℝ)
  have hE : HasDerivAt E (-(2 * t * E t)) t := by
    have hinner : HasDerivAt (fun u : ℝ => -(u ^ 2)) (-(2 * t)) t := by
      simpa using ((hasDerivAt_id t).pow 2).neg
    dsimp [E]
    convert hinner.exp using 1
    ring
  have hD : HasDerivAt D (-(2 * (t + δ) * D t)) t := by
    have hsq : HasDerivAt (fun u : ℝ => (u + δ) ^ 2) (2 * (t + δ)) t := by
      simpa [one_mul] using hshift.pow 2
    have hinner :
        HasDerivAt (fun u : ℝ => -((u + δ) ^ 2)) (-(2 * (t + δ))) t := by
      simpa using hsq.neg
    dsimp [D]
    convert hinner.exp using 1
    ring
  have hBsq :
      HasDerivAt (fun u => B u ^ 2) (2 * B t * (c * D t)) t := by
    convert hB.pow 2 using 1
    ring
  have hAB :
      HasDerivAt (fun u => A u * B u ^ 2)
        ((c * E t) * B t ^ 2 + A t * (2 * B t * (c * D t))) t := by
    convert hA.mul hBsq using 1
  have hnum :
      HasDerivAt (fun u => A u * B u ^ 2 * E u)
        ((c * E t) * B t ^ 2 * E t +
          A t * (2 * B t * (c * D t)) * E t +
          A t * B t ^ 2 * (-(2 * t * E t))) t := by
    convert hAB.mul hE using 1
    ring
  have hAD :
      HasDerivAt (fun u => A u * D u)
        ((c * E t) * D t + A t * (-(2 * (t + δ) * D t))) t := by
    convert hA.mul hD using 1
  have hBE :
      HasDerivAt (fun u => B u * E u)
        ((c * D t) * E t + B t * (-(2 * t * E t))) t := by
    convert hB.mul hE using 1
  have hden_deriv :
      HasDerivAt (fun u => A u * D u + B u * E u)
        ((c * E t) * D t + A t * (-(2 * (t + δ) * D t)) +
          ((c * D t) * E t + B t * (-(2 * t * E t)))) t :=
    hAD.add hBE
  have hden_ne : A t * D t + B t * E t ≠ 0 := by
    have hpos : 0 < A t * D t + B t * E t := by
      dsimp [A, B, D, E]
      exact add_pos
        (mul_pos (theorem8Erf_one_add_pos t) (Real.exp_pos _))
        (mul_pos (theorem8Erf_one_add_pos (t + δ)) (Real.exp_pos _))
    exact hpos.ne'
  have hquot := hnum.div hden_deriv hden_ne
  unfold theorem8GaussianC6RationalTerm theorem8GaussianC6RationalTermDerivative
  simpa [A, B, E, D, c, add_assoc] using hquot

/--
Appendix C, Theorem 8, equation (C.8): the derivative of the C.6 left-hand
side before the paper's algebraic factorization into the C.8 prefactor and
C.9 bracket.
-/
noncomputable def theorem8GaussianC8Derivative (δ t : ℝ) : ℝ :=
  deriv (fun u => theorem8GaussianC6RationalTerm theorem8Erf δ u) t -
    (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) -
    (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) *
      theorem8Erf (t + δ)

/--
Appendix C, Theorem 8: calculus part of equation (C.8) for the concrete `erf`
and concrete `J`.  The remaining paper step after this lemma is purely the
algebraic factorization of `theorem8GaussianC8Derivative` into the C.8 positive
prefactor times the C.9 bracket.
-/
theorem theorem8GaussianC6LHS_hasDerivAt_concrete_C8
    (δ t : ℝ) :
    HasDerivAt
      (fun u =>
        theorem8GaussianC6LHS theorem8Erf
          (theorem8GaussianJ theorem8Erf δ) δ u)
      (theorem8GaussianC8Derivative δ t) t := by
  let c : ℝ := 2 / Real.sqrt Real.pi
  let A : ℝ → ℝ := fun u => 1 + theorem8Erf u
  let B : ℝ → ℝ := fun u => 1 + theorem8Erf (u + δ)
  let E : ℝ → ℝ := fun u => Real.exp (-(u ^ 2))
  let D : ℝ → ℝ := fun u => Real.exp (-((u + δ) ^ 2))
  have hA_diff : DifferentiableAt ℝ A t := by
    dsimp [A]
    exact ((theorem8Erf_hasDerivAt t).const_add (1 : ℝ)).differentiableAt
  have hshift : HasDerivAt (fun u : ℝ => u + δ) 1 t := by
    simpa [add_comm] using (hasDerivAt_id t).const_add δ
  have hB_diff : DifferentiableAt ℝ B t := by
    dsimp [B]
    exact (((theorem8Erf_hasDerivAt (t + δ)).comp t hshift).const_add
      (1 : ℝ)).differentiableAt
  have hE_diff : DifferentiableAt ℝ E t := by
    dsimp [E]
    fun_prop
  have hD_diff : DifferentiableAt ℝ D t := by
    dsimp [D]
    fun_prop
  have hnum_diff :
      DifferentiableAt ℝ (fun u => A u * B u ^ 2 * E u) t :=
    (hA_diff.mul (hB_diff.pow 2)).mul hE_diff
  have hden_diff :
      DifferentiableAt ℝ (fun u => A u * D u + B u * E u) t :=
    (hA_diff.mul hD_diff).add (hB_diff.mul hE_diff)
  have hden_ne : A t * D t + B t * E t ≠ 0 := by
    have hpos : 0 < A t * D t + B t * E t := by
      dsimp [A, B, D, E]
      exact add_pos
        (mul_pos (theorem8Erf_one_add_pos t) (Real.exp_pos _))
        (mul_pos (theorem8Erf_one_add_pos (t + δ)) (Real.exp_pos _))
    exact hpos.ne'
  have hrat_diff :
      DifferentiableAt ℝ
        (fun u => theorem8GaussianC6RationalTerm theorem8Erf δ u) t := by
    unfold theorem8GaussianC6RationalTerm
    simpa [A, B, E, D] using hnum_diff.div hden_diff hden_ne
  have hrat_deriv :
      HasDerivAt
        (fun u => theorem8GaussianC6RationalTerm theorem8Erf δ u)
        (deriv (fun u => theorem8GaussianC6RationalTerm theorem8Erf δ u) t) t :=
    hrat_diff.hasDerivAt
  have hA_deriv :
      HasDerivAt (fun u => 1 + theorem8Erf u)
        (c * Real.exp (-(t ^ 2))) t := by
    dsimp [c]
    simpa using (theorem8Erf_hasDerivAt t).const_add (1 : ℝ)
  have hJ_deriv := theorem8GaussianJ_hasDerivAt_concrete δ t
  have hmain :=
    (hrat_deriv.sub hA_deriv).sub (hJ_deriv.const_mul c)
  refine hmain.congr_deriv ?_
  unfold theorem8GaussianC8Derivative c
  ring

/--
Appendix C, Theorem 8: equation (C.8) factors as a positive prefactor times
the C.9 bracket for the concrete interval-integral `erf`.
-/
theorem theorem8GaussianC8Derivative_factorization
    (δ t : ℝ) :
    theorem8GaussianC8Derivative δ t =
      theorem8GaussianC8PositiveFactor theorem8Erf δ t *
        theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t := by
  have hrat :=
    (theorem8GaussianC6RationalTerm_hasDerivAt_concrete_explicit δ t).deriv
  let a : ℝ := 1 + theorem8Erf t
  let b : ℝ := 1 + theorem8Erf (t + δ)
  let p : ℝ := Real.exp (-(t ^ 2))
  let q : ℝ := Real.exp (-((t + δ) ^ 2))
  let s : ℝ := Real.sqrt Real.pi
  have hs : s ≠ 0 := by
    dsimp [s]
    exact (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hp : p ≠ 0 := by
    dsimp [p]
    exact (Real.exp_pos _).ne'
  have hq : q ≠ 0 := by
    dsimp [q]
    exact (Real.exp_pos _).ne'
  have hb : b ≠ 0 := by
    dsimp [b]
    exact (theorem8Erf_one_add_pos (t + δ)).ne'
  have hden : a * q + b * p ≠ 0 := by
    have hpos : 0 < a * q + b * p := by
      dsimp [a, b, p, q]
      exact add_pos
        (mul_pos (theorem8Erf_one_add_pos t) (Real.exp_pos _))
        (mul_pos (theorem8Erf_one_add_pos (t + δ)) (Real.exp_pos _))
    exact hpos.ne'
  have halg := theorem8GaussianC8_algebra a b p q s δ t hs hp hq hb hden
  have hc8_compact :
      theorem8GaussianC8Derivative δ t =
        theorem8GaussianC6RationalTermDerivative δ t -
          (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) *
            (1 + theorem8Erf (t + δ)) := by
    unfold theorem8GaussianC8Derivative
    rw [hrat]
    ring
  rw [hc8_compact]
  unfold theorem8GaussianC6RationalTermDerivative
  unfold theorem8GaussianC8PositiveFactor theorem8GaussianC9Bracket theorem8GaussianG
  simpa [a, b, p, q, s, Real.exp_neg, add_comm, add_left_comm, add_assoc]
    using halg

/--
Appendix C, Theorem 8 specialized to the paper's concrete Mills ratio,
concrete `erf`, and concrete `J`, with the C.6 derivative factorization
discharged by `theorem8GaussianC8Derivative_factorization`.

The only remaining scalar analytic input is Sampford's cited Mills-ratio
derivative bound.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J_of_sampford
    {δ : ℝ} (hδ : 0 < δ)
    (hsamp : theorem8SampfordMillsBound theorem8MillsRatio) :
    ∀ t,
      0 <
        theorem8GaussianC6LHS theorem8Erf
          (theorem8GaussianJ theorem8Erf δ) δ t := by
  have hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u =>
            theorem8GaussianC6LHS theorem8Erf
              (theorem8GaussianJ theorem8Erf δ) δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t := by
    intro t
    exact (theorem8GaussianC6LHS_hasDerivAt_concrete_C8 δ t).congr_deriv
      (theorem8GaussianC8Derivative_factorization δ t)
  exact paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J
    (δ := δ) hδ hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the paper's concrete Mills ratio,
concrete `erf`, and concrete `J`, after formalizing Sampford's Mills-ratio
input for the concrete Gaussian Mills ratio.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J_unconditional
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ t,
      0 <
        theorem8GaussianC6LHS theorem8Erf
          (theorem8GaussianJ theorem8Erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J_of_sampford
    hδ theorem8SampfordMillsBound_concrete

/--
Appendix C, Theorem 8: the conditional pairwise probability expression after
the paper's Gaussian density/CDF calculation and the substitution
`t = a - x_i`, `δ = x_i - x_j`.

This is the formula immediately before differentiating to obtain (C.5)--(C.6):
`((1+erf(t)) + (2/sqrt(pi)) J(t)) /
 ((1+erf(t)) (1+erf(t+δ)))`.
-/
noncomputable def theorem8GaussianConditionalIntegralRatio
    (erf J : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  ((1 + erf t) + (2 / Real.sqrt Real.pi) * J t) /
    ((1 + erf t) * (1 + erf (t + δ)))

/--
Appendix C, Theorem 8: algebra connecting the quotient-rule derivative of the
Gaussian conditional integral ratio to the C.6 left-hand side.
-/
theorem theorem8GaussianConditionalIntegralRatio_deriv_eq_c6_algebra
    {A B p q J c : ℝ} (hden : A * q + B * p ≠ 0) :
    ((c * p * B) * (A * B) - (A + c * J) * (c * p * B + A * (c * q))) /
        (A * B) ^ 2 =
      c * (A * q + B * p) *
        (A * B ^ 2 * p / (A * q + B * p) - A - c * J) /
          (A * B) ^ 2 := by
  have hnum :
      (c * p * B) * (A * B) - (A + c * J) * (c * p * B + A * (c * q)) =
        c * (A * q + B * p) *
          (A * B ^ 2 * p / (A * q + B * p) - A - c * J) := by
    let S : ℝ := A * q + B * p
    let T : ℝ := A * B ^ 2 * p
    have hcancel : S * (T / S) = T :=
      mul_div_cancel₀ T (by simpa [S] using hden)
    calc
      (c * p * B) * (A * B) - (A + c * J) * (c * p * B + A * (c * q))
          = c * (T - S * A - S * (c * J)) := by
            dsimp [S, T]
            ring
      _ = c * (S * (T / S) - S * A - S * (c * J)) := by
            rw [hcancel]
      _ = c * S * (T / S - A - c * J) := by
            ring
      _ = c * (A * q + B * p) *
            (A * B ^ 2 * p / (A * q + B * p) - A - c * J) := by
            dsimp [S, T]
  rw [hnum]

/--
Appendix C, Theorem 8: at the Gaussian integral-ratio layer, the derivative of
the conditional pairwise probability expression is strictly positive.  The
sign is exactly the already formalized C.6 scalar positivity theorem.
-/
theorem theorem8GaussianConditionalIntegralRatio_hasDerivAt_pos
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∃ d,
      HasDerivAt
        (fun u =>
          theorem8GaussianConditionalIntegralRatio theorem8Erf
            (theorem8GaussianJ theorem8Erf δ) δ u) d t ∧
        0 < d := by
  let c : ℝ := 2 / Real.sqrt Real.pi
  let A : ℝ := 1 + theorem8Erf t
  let B : ℝ := 1 + theorem8Erf (t + δ)
  let p : ℝ := Real.exp (-(t ^ 2))
  let q : ℝ := Real.exp (-((t + δ) ^ 2))
  let Jv : ℝ := theorem8GaussianJ theorem8Erf δ t
  let F : ℝ := theorem8GaussianC6LHS theorem8Erf (theorem8GaussianJ theorem8Erf δ) δ t
  let d : ℝ := c * (A * q + B * p) * F / (A * B) ^ 2
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hA_pos : 0 < A := by
    dsimp [A]
    exact theorem8Erf_one_add_pos t
  have hB_pos : 0 < B := by
    dsimp [B]
    exact theorem8Erf_one_add_pos (t + δ)
  have hp_pos : 0 < p := by
    dsimp [p]
    exact Real.exp_pos _
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Real.exp_pos _
  have hden_prod_ne : A * B ≠ 0 :=
    (mul_pos hA_pos hB_pos).ne'
  have hden_c6_pos : 0 < A * q + B * p :=
    add_pos (mul_pos hA_pos hq_pos) (mul_pos hB_pos hp_pos)
  have hF_pos : 0 < F := by
    dsimp [F]
    exact paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J_unconditional hδ t
  have hA_deriv :
      HasDerivAt (fun u => 1 + theorem8Erf u) (c * p) t := by
    dsimp [c, p]
    simpa using (theorem8Erf_hasDerivAt t).const_add (1 : ℝ)
  have hshift : HasDerivAt (fun u : ℝ => u + δ) 1 t := by
    simpa using (hasDerivAt_id t).add_const δ
  have hB_deriv :
      HasDerivAt (fun u => 1 + theorem8Erf (u + δ)) (c * q) t := by
    dsimp [c, q]
    simpa [one_mul] using
      ((theorem8Erf_hasDerivAt (t + δ)).comp t hshift).const_add (1 : ℝ)
  have hJ_deriv :
      HasDerivAt
        (fun u => theorem8GaussianJ theorem8Erf δ u)
        (p * theorem8Erf (t + δ)) t := by
    dsimp [p]
    exact theorem8GaussianJ_hasDerivAt_concrete δ t
  have hnum_deriv :
      HasDerivAt
        (fun u =>
          (1 + theorem8Erf u) +
            c * theorem8GaussianJ theorem8Erf δ u)
        (c * p * B) t := by
    have hraw := hA_deriv.add (hJ_deriv.const_mul c)
    convert hraw using 1
    dsimp [B]
    ring
  have hden_deriv :
      HasDerivAt
        (fun u => (1 + theorem8Erf u) * (1 + theorem8Erf (u + δ)))
        (c * p * B + A * (c * q)) t := by
    have hraw := hA_deriv.mul hB_deriv
    simpa [A, B] using hraw
  have hratio :
      HasDerivAt
        (fun u =>
          theorem8GaussianConditionalIntegralRatio theorem8Erf
            (theorem8GaussianJ theorem8Erf δ) δ u)
        (((c * p * B) * (A * B) -
            (A + c * Jv) * (c * p * B + A * (c * q))) /
          (A * B) ^ 2) t := by
    have hdiv := hnum_deriv.div hden_deriv hden_prod_ne
    simpa [theorem8GaussianConditionalIntegralRatio, A, B, Jv] using hdiv
  have hderiv_eq :
      ((c * p * B) * (A * B) -
            (A + c * Jv) * (c * p * B + A * (c * q))) /
          (A * B) ^ 2 = d := by
    dsimp [d, F, theorem8GaussianC6LHS, theorem8GaussianC6RationalTerm]
    exact theorem8GaussianConditionalIntegralRatio_deriv_eq_c6_algebra
      (A := A) (B := B) (p := p) (q := q) (J := Jv) (c := c)
      hden_c6_pos.ne'
  refine ⟨d, ?_, ?_⟩
  · exact hratio.congr_deriv hderiv_eq
  · dsimp [d]
    positivity

/--
Appendix C, Theorem 8: the Gaussian conditional integral ratio in the paper's
original cutoff coordinate `a`, with `t = a - x_i` and `δ = x_i - x_j`.
-/
noncomputable def theorem8GaussianConditionalIntegralRatioAt
    (xi xj a : ℝ) : ℝ :=
  theorem8GaussianConditionalIntegralRatio theorem8Erf
    (theorem8GaussianJ theorem8Erf (xi - xj)) (xi - xj) (a - xi)

/--
Appendix C, Theorem 8 at the Gaussian integral-ratio layer, in the original
`a, x_i, x_j` coordinates: if `x_i > x_j`, the displayed conditional integral
ratio has strictly positive derivative in the cutoff `a`.
-/
theorem theorem8GaussianConditionalIntegralRatioAt_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => theorem8GaussianConditionalIntegralRatioAt xi xj u) d a ∧
        0 < d := by
  have hδ : 0 < xi - xj := sub_pos.mpr hx
  obtain ⟨d, hd, hdpos⟩ :=
    theorem8GaussianConditionalIntegralRatio_hasDerivAt_pos
      (δ := xi - xj) hδ (a - xi)
  have hshift : HasDerivAt (fun u : ℝ => u - xi) 1 a := by
    simpa using (hasDerivAt_id a).sub_const xi
  refine ⟨d, ?_, hdpos⟩
  unfold theorem8GaussianConditionalIntegralRatioAt
  simpa [one_mul] using hd.comp a hshift

/--
Appendix C, Theorem 8: the Gaussian density used after the paper normalizes to
`σ = 1 / sqrt 2`, so that the variance is `1/2`.
-/
noncomputable def theorem8GaussianPDF (μ x : ℝ) : ℝ := Real.exp (-((x - μ) ^ 2)) / Real.sqrt Real.pi

/--
Appendix C, Theorem 8: the paper Gaussian density agrees with Mathlib's
`gaussianPDFReal` at variance `1/2`.
-/
theorem theorem8GaussianPDF_eq_gaussianPDFReal_half (μ x : ℝ) :
    theorem8GaussianPDF μ x =
      ProbabilityTheory.gaussianPDFReal μ (1 / 2 : ℝ≥0) x := by
  unfold theorem8GaussianPDF ProbabilityTheory.gaussianPDFReal
  norm_num
  field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos]

/-- The paper's zero-mean normalized Gaussian density is a positive multiple of
the unnormalized Gaussian kernel used in Lemma 1. -/
theorem theorem8GaussianPDF_zero_eq_const_mul_gaussianNoiseKernel (x : ℝ) :
    theorem8GaussianPDF 0 x =
      (1 / Real.sqrt Real.pi) * gaussianNoiseKernel 1 x := by
  unfold theorem8GaussianPDF gaussianNoiseKernel AppliedModelingLib.Probability.gaussianNoiseKernel
  ring_nf

/-- The normalized zero-mean Gaussian density used in Theorem 8 is strictly
well-ordered. -/
theorem theorem8GaussianPDF_zero_strictlyWellOrdered :
    StrictlyWellOrderedNoise (theorem8GaussianPDF 0) := by
  have hbase : StrictlyWellOrderedNoise (gaussianNoiseKernel 1) :=
    gaussianNoiseKernel_strictlyWellOrdered (by norm_num)
  have hc : 0 < (1 / Real.sqrt Real.pi) :=
    one_div_pos.mpr (Real.sqrt_pos.mpr Real.pi_pos)
  have hscaled :=
    StrictlyWellOrderedNoise.const_mul_pos hbase hc
  have hfun :
      theorem8GaussianPDF 0 =
        fun z : ℝ => (1 / Real.sqrt Real.pi) * gaussianNoiseKernel 1 z := by
    funext z
    rw [theorem8GaussianPDF_zero_eq_const_mul_gaussianNoiseKernel z]
  simpa [hfun] using hscaled

/--
Appendix C, Theorem 8: the corresponding Gaussian CDF in the paper's
normalization.
-/
noncomputable def theorem8GaussianCDF (μ a : ℝ) : ℝ := (1 + theorem8Erf (a - μ)) / 2

/--
Appendix C, Theorem 8: the paper's CDF formula is the left integral of the
paper Gaussian density.
-/
theorem theorem8GaussianPDF_integral_Iic_eq_CDF (μ a : ℝ) :
    (∫ x : ℝ in Set.Iic a, theorem8GaussianPDF μ x) =
      theorem8GaussianCDF μ a := by
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
    Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hshift :=
    theorem8_integral_Iic_sub_eq_integral_Iic
      (f := fun u : ℝ => Real.exp (-(u ^ 2)))
      (a := a) (μ := μ)
  unfold theorem8GaussianPDF theorem8GaussianCDF
  calc
    (∫ x : ℝ in Set.Iic a, Real.exp (-((x - μ) ^ 2)) / Real.sqrt Real.pi)
        = (1 / Real.sqrt Real.pi) *
            ∫ x : ℝ in Set.Iic a, Real.exp (-((x - μ) ^ 2)) := by
          rw [← integral_const_mul]
          congr 1
          ext x
          field_simp [hsqrt_ne]
    _ = (1 / Real.sqrt Real.pi) *
            ∫ u : ℝ in Set.Iic (a - μ), Real.exp (-(u ^ 2)) := by
          rw [hshift]
    _ = (1 / Real.sqrt Real.pi) *
          (Real.sqrt Real.pi / 2 * (1 + theorem8Erf (a - μ))) := by
          rw [theorem8Gaussian_integral_Iic_eq_erf]
    _ = (1 + theorem8Erf (a - μ)) / 2 := by
          field_simp [hsqrt_ne]

/--
Appendix C, Theorem 8: the Mathlib Gaussian measure at variance `1/2` assigns
the left half-line the paper's CDF value.
-/
theorem theorem8GaussianReal_Iic_eq_CDF (μ a : ℝ) :
    ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0) (Set.Iic a) =
      ENNReal.ofReal (theorem8GaussianCDF μ a) := by
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral μ hv (Set.Iic a)]
  congr 1
  rw [← theorem8GaussianPDF_integral_Iic_eq_CDF μ a]
  refine setIntegral_congr_fun measurableSet_Iic ?_
  intro x _hx
  exact (theorem8GaussianPDF_eq_gaussianPDFReal_half μ x).symm

/-- Appendix C, Theorem 8: nonnegativity of the paper Gaussian CDF. -/
theorem theorem8GaussianCDF_nonneg (μ a : ℝ) :
    0 ≤ theorem8GaussianCDF μ a := by
  unfold theorem8GaussianCDF
  exact div_nonneg (le_of_lt (theorem8Erf_one_add_pos (a - μ))) (by norm_num)

/-- Appendix C, Theorem 8: the paper Gaussian CDF is strictly positive. -/
theorem theorem8GaussianCDF_pos (μ a : ℝ) :
    0 < theorem8GaussianCDF μ a := by
  have hvar : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  have htail :
      0 <
        ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0)
          (Set.Ioc (a - 1) a) :=
    AppliedModelingLib.Probability.gaussianReal_Ioc_pos μ hvar (by linarith)
  have hmono :
      ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0)
          (Set.Ioc (a - 1) a) ≤
        ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0) (Set.Iic a) :=
    measure_mono (by intro x hx; exact hx.2)
  have hpos :
      0 <
        ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0) (Set.Iic a) :=
    lt_of_lt_of_le htail hmono
  rw [theorem8GaussianReal_Iic_eq_CDF μ a] at hpos
  exact ENNReal.ofReal_pos.mp hpos

/-- Appendix C, Theorem 8: the paper Gaussian CDF is at most one. -/
theorem theorem8GaussianCDF_le_one (μ a : ℝ) :
    theorem8GaussianCDF μ a ≤ 1 := by
  have hle :
      ENNReal.ofReal (theorem8GaussianCDF μ a) ≤ (1 : ℝ≥0∞) := by
    rw [← theorem8GaussianReal_Iic_eq_CDF μ a]
    simpa using
      measure_mono
        (μ := ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0))
        (Set.subset_univ (Set.Iic a))
  exact ENNReal.ofReal_le_one.mp hle

/--
Appendix C, Theorem 8: the paper Gaussian CDF tends to one at the right tail.
-/
theorem theorem8GaussianCDF_tendsto_atTop_one (μ : ℝ) :
    Filter.Tendsto (fun a => theorem8GaussianCDF μ a)
      Filter.atTop (nhds 1) := by
  have hshift :
      Filter.Tendsto (fun a : ℝ => a - μ) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.Ici_mem_atTop (b + μ)] with a ha
    have ha' : b + μ ≤ a := by simpa using ha
    linarith
  have herf :
      Filter.Tendsto (fun a => 1 + theorem8Erf (a - μ))
        Filter.atTop (nhds 2) :=
    theorem8Erf_tendsto_one_add_atTop_two.comp hshift
  have hdiv := herf.div_const (2 : ℝ)
  simpa [theorem8GaussianCDF, show (2 : ℝ) / 2 = 1 by norm_num] using hdiv

/--
Appendix C, Theorem 8: the paper Gaussian CDF tends to zero at the left tail.
-/
theorem theorem8GaussianCDF_tendsto_atBot_zero (μ : ℝ) :
    Filter.Tendsto (fun a => theorem8GaussianCDF μ a)
      Filter.atBot (nhds 0) := by
  have hshift :
      Filter.Tendsto (fun a : ℝ => a - μ) Filter.atBot Filter.atBot := by
    refine Filter.tendsto_atBot.2 ?_
    intro b
    filter_upwards [Filter.Iic_mem_atBot (b + μ)] with a ha
    have ha' : a ≤ b + μ := by simpa using ha
    linarith
  have herf :
      Filter.Tendsto (fun a => 1 + theorem8Erf (a - μ))
        Filter.atBot (nhds 0) :=
    theorem8Erf_tendsto_one_add_atBot_zero.comp hshift
  have hdiv := herf.div_const (2 : ℝ)
  simpa [theorem8GaussianCDF] using hdiv

/-- Appendix C, Theorem 8: nonnegativity of the paper Gaussian density. -/
theorem theorem8GaussianPDF_nonneg (μ x : ℝ) :
    0 ≤ theorem8GaussianPDF μ x := by
  unfold theorem8GaussianPDF
  positivity

/-- Appendix C, Theorem 8: positivity of the paper Gaussian density. -/
theorem theorem8GaussianPDF_pos (μ x : ℝ) :
    0 < theorem8GaussianPDF μ x := by
  unfold theorem8GaussianPDF
  positivity

/-- Appendix C, Theorem 8: measurability of the paper Gaussian density. -/
theorem theorem8GaussianPDF_measurable (μ : ℝ) :
    Measurable (theorem8GaussianPDF μ) := by
  have h := ProbabilityTheory.measurable_gaussianPDFReal μ (1 / 2 : ℝ≥0)
  convert h using 1
  ext x
  exact theorem8GaussianPDF_eq_gaussianPDFReal_half μ x

/-- Appendix C, Theorem 8: the paper Gaussian density has total mass one. -/
theorem theorem8GaussianPDF_lintegral_eq_one (μ : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal (theorem8GaussianPDF μ x) = 1 := by
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  calc
    ∫⁻ x : ℝ, ENNReal.ofReal (theorem8GaussianPDF μ x)
        = ∫⁻ x : ℝ,
            ENNReal.ofReal
              (ProbabilityTheory.gaussianPDFReal μ (1 / 2 : ℝ≥0) x) := by
          refine lintegral_congr_ae ?_
          exact Filter.Eventually.of_forall fun x => by
            exact congrArg ENNReal.ofReal
              (theorem8GaussianPDF_eq_gaussianPDFReal_half μ x)
    _ = 1 := ProbabilityTheory.lintegral_gaussianPDFReal_eq_one μ hv

/-- A zero-mean Gaussian noise draw around value `μ` is the Gaussian density
with mean `μ` in the score coordinate. -/
theorem theorem8GaussianPDF_zero_sub_eq (μ x : ℝ) :
    theorem8GaussianPDF 0 (x - μ) = theorem8GaussianPDF μ x := by
  unfold theorem8GaussianPDF
  ring_nf

/-- Shifted zero-mean paper Gaussian density has total mass one. -/
theorem theorem8GaussianPDF_zero_sub_lintegral_eq_one (μ : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal (theorem8GaussianPDF 0 (x - μ)) = 1 := by
  calc
    ∫⁻ x : ℝ, ENNReal.ofReal (theorem8GaussianPDF 0 (x - μ))
        = ∫⁻ x : ℝ, ENNReal.ofReal (theorem8GaussianPDF μ x) := by
          refine lintegral_congr_ae ?_
          exact Filter.Eventually.of_forall fun x => by
            exact congrArg ENNReal.ofReal
              (theorem8GaussianPDF_zero_sub_eq μ x)
    _ = 1 := theorem8GaussianPDF_lintegral_eq_one μ

/--
Appendix C, Theorem 8: integrability of the product of the paper Gaussian
density and CDF over a left half-line.
-/
theorem theorem8GaussianPDF_mul_CDF_integrableOn (xi xj a : ℝ) :
    IntegrableOn
      (fun x : ℝ => theorem8GaussianPDF xi x * theorem8GaussianCDF xj x)
      (Set.Iic a) := by
  have hpdf : Integrable (theorem8GaussianPDF xi) := by
    have h := ProbabilityTheory.integrable_gaussianPDFReal xi (1 / 2 : ℝ≥0)
    convert h using 1
    ext x
    exact theorem8GaussianPDF_eq_gaussianPDFReal_half xi x
  have hcdf_meas :
      AEStronglyMeasurable (fun x : ℝ => theorem8GaussianCDF xj x)
        (volume.restrict (Set.Iic a)) := by
    have hcont : Continuous fun x : ℝ => theorem8GaussianCDF xj x := by
      unfold theorem8GaussianCDF
      exact ((theorem8Erf_continuous.comp
        (continuous_id.sub continuous_const)).const_add 1).div_const 2
    exact hcont.aestronglyMeasurable
  have hcdf_bound :
      ∀ᵐ x ∂volume.restrict (Set.Iic a),
        ‖theorem8GaussianCDF xj x‖ ≤ (1 : ℝ) := by
    refine ae_restrict_of_forall_mem measurableSet_Iic ?_
    intro x _hx
    rw [Real.norm_of_nonneg (theorem8GaussianCDF_nonneg xj x)]
    exact theorem8GaussianCDF_le_one xj x
  exact hpdf.integrableOn.mul_bdd hcdf_meas hcdf_bound

/--
Appendix C, Theorem 8: full-space integrability of the Gaussian density/CDF
integrand.
-/
theorem theorem8GaussianPDF_mul_CDF_integrable (xi xj : ℝ) :
    Integrable
      (fun x : ℝ => theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
  have hpdf : Integrable (theorem8GaussianPDF xi) := by
    have h := ProbabilityTheory.integrable_gaussianPDFReal xi (1 / 2 : ℝ≥0)
    convert h using 1
    ext x
    exact theorem8GaussianPDF_eq_gaussianPDFReal_half xi x
  have hcdf_meas :
      AEStronglyMeasurable (fun x : ℝ => theorem8GaussianCDF xj x) volume := by
    have hcont : Continuous fun x : ℝ => theorem8GaussianCDF xj x := by
      unfold theorem8GaussianCDF
      exact ((theorem8Erf_continuous.comp
        (continuous_id.sub continuous_const)).const_add 1).div_const 2
    exact hcont.aestronglyMeasurable
  have hcdf_bound :
      ∀ᵐ x ∂volume, ‖theorem8GaussianCDF xj x‖ ≤ (1 : ℝ) := by
    exact ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (theorem8GaussianCDF_nonneg xj x)]
      exact theorem8GaussianCDF_le_one xj x
  exact hpdf.mul_bdd hcdf_meas hcdf_bound

/--
Appendix C, Theorem 8: the density/CDF numerator over `(-∞, a]` converges to
the unconditional density/CDF numerator as `a -> +∞`.
-/
theorem theorem8GaussianPDF_mul_CDF_integral_Iic_tendsto_atTop
    (xi xj : ℝ) :
    Filter.Tendsto
      (fun a : ℝ =>
        ∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x)
      Filter.atTop
      (nhds (∫ x : ℝ,
        theorem8GaussianPDF xi x * theorem8GaussianCDF xj x)) := by
  let f : ℝ → ℝ := fun x => theorem8GaussianPDF xi x * theorem8GaussianCDF xj x
  have hmono : Monotone (fun a : ℝ => Set.Iic a) := by
    intro a b hab x hx
    exact le_trans hx hab
  have hUnion : (⋃ a : ℝ, Set.Iic a) = (Set.univ : Set ℝ) := by
    ext x
    simp
  have hfi : IntegrableOn f (⋃ a : ℝ, Set.Iic a) := by
    rw [hUnion]
    exact (theorem8GaussianPDF_mul_CDF_integrable xi xj).integrableOn
  have h :=
    tendsto_setIntegral_of_monotone
      (μ := volume) (f := f) (s := fun a : ℝ => Set.Iic a)
      (fun _ => measurableSet_Iic) hmono hfi
  simpa [f, hUnion] using h

/--
Appendix C, Theorem 8: the paper Gaussian density as an `ENNReal` density is
Mathlib's `gaussianPDF` at variance `1/2`.
-/
theorem theorem8GaussianPDF_ofReal_eq_gaussianPDF_half (μ x : ℝ) :
    ENNReal.ofReal (theorem8GaussianPDF μ x) =
      ProbabilityTheory.gaussianPDF μ (1 / 2 : ℝ≥0) x := by
  simp [ProbabilityTheory.gaussianPDF,
    theorem8GaussianPDF_eq_gaussianPDFReal_half]

/--
Appendix C, Theorem 8: after substituting `u = x - x_i`, the numerator
integral in the paper's Gaussian density/CDF formula splits into the `erf`
tail and the paper's `J` integral.
-/
theorem theorem8Gaussian_integral_shift_split (xi xj a : ℝ) :
    (∫ x : ℝ in Set.Iic a,
        Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) =
      Real.sqrt Real.pi / 2 * (1 + theorem8Erf (a - xi)) +
        theorem8GaussianJ theorem8Erf (xi - xj) (a - xi) := by
  let t : ℝ := a - xi
  let δ : ℝ := xi - xj
  have hshift :
      (∫ x : ℝ in Set.Iic a,
          Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) =
        ∫ u : ℝ in Set.Iic t,
          Real.exp (-(u ^ 2)) * (1 + theorem8Erf (u + δ)) := by
    have h :=
      theorem8_integral_Iic_sub_eq_integral_Iic
        (f := fun u : ℝ =>
          Real.exp (-(u ^ 2)) * (1 + theorem8Erf (u + δ)))
        (a := a) (μ := xi)
    dsimp [t, δ] at h ⊢
    convert h using 2
    · ext x
      ring_nf
  have hgauss :
      IntegrableOn (fun u : ℝ => Real.exp (-(u ^ 2))) (Set.Iic t) := by
    simpa [one_mul] using
      (integrable_exp_neg_mul_sq (show 0 < (1 : ℝ) by norm_num)).integrableOn
  have hJ :
      IntegrableOn
        (fun u : ℝ => Real.exp (-(u ^ 2)) * theorem8Erf (u + δ))
        (Set.Iic t) := by
    simpa [δ, t] using theorem8GaussianJ_integrableOn_Iic_concrete δ t
  have hsplit :
      (∫ u : ℝ in Set.Iic t,
          Real.exp (-(u ^ 2)) * (1 + theorem8Erf (u + δ))) =
        (∫ u : ℝ in Set.Iic t, Real.exp (-(u ^ 2))) +
          ∫ u : ℝ in Set.Iic t,
            Real.exp (-(u ^ 2)) * theorem8Erf (u + δ) := by
    simpa [mul_add, mul_one] using integral_add hgauss hJ
  calc
    (∫ x : ℝ in Set.Iic a,
        Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj)))
        = ∫ u : ℝ in Set.Iic t,
          Real.exp (-(u ^ 2)) * (1 + theorem8Erf (u + δ)) := hshift
    _ = (∫ u : ℝ in Set.Iic t, Real.exp (-(u ^ 2))) +
          ∫ u : ℝ in Set.Iic t,
            Real.exp (-(u ^ 2)) * theorem8Erf (u + δ) := hsplit
    _ = Real.sqrt Real.pi / 2 * (1 + theorem8Erf t) +
          theorem8GaussianJ theorem8Erf δ t := by
          rw [theorem8Gaussian_integral_Iic_eq_erf]
          rfl
    _ = Real.sqrt Real.pi / 2 * (1 + theorem8Erf (a - xi)) +
          theorem8GaussianJ theorem8Erf (xi - xj) (a - xi) := by
          rfl

/--
Appendix C, Theorem 8: the paper's density/CDF expression
`∫ f_i(x) F_j(x) dx / (F_i(a)F_j(a))` for the Gaussian conditional pairwise
probability.
-/
noncomputable def theorem8GaussianPDFCDFRatioAt
    (xi xj a : ℝ) : ℝ :=
  (∫ x : ℝ in Set.Iic a,
      theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) /
    (theorem8GaussianCDF xi a * theorem8GaussianCDF xj a)

/--
Appendix C, Theorem 8: the same density/CDF ratio after clearing the common
Gaussian CDF constants, exactly as displayed in the paper before the
`t = a - x_i`, `δ = x_i - x_j` substitution.
-/
noncomputable def theorem8GaussianDensityCDFIntegralRatioAt
    (xi xj a : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) *
    (∫ x : ℝ in Set.Iic a,
      Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) /
    ((1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj)))

/--
Appendix C, Theorem 8: clearing the Gaussian density/CDF constants in the
paper's conditional probability integral formula.
-/
theorem theorem8GaussianPDFCDFRatioAt_eq_densityCDF (xi xj a : ℝ) :
    theorem8GaussianPDFCDFRatioAt xi xj a =
      theorem8GaussianDensityCDFIntegralRatioAt xi xj a := by
  let Iraw : ℝ :=
    ∫ x : ℝ in Set.Iic a,
      Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
    Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hA_ne : 1 + theorem8Erf (a - xi) ≠ 0 :=
    (theorem8Erf_one_add_pos (a - xi)).ne'
  have hB_ne : 1 + theorem8Erf (a - xj) ≠ 0 :=
    (theorem8Erf_one_add_pos (a - xj)).ne'
  have hnum :
      (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) =
        (1 / (2 * Real.sqrt Real.pi)) * Iraw := by
    dsimp [Iraw]
    rw [← integral_const_mul]
    congr 1
    ext x
    unfold theorem8GaussianPDF theorem8GaussianCDF
    field_simp [hsqrt_ne]
  unfold theorem8GaussianPDFCDFRatioAt
    theorem8GaussianDensityCDFIntegralRatioAt
  rw [hnum]
  unfold theorem8GaussianCDF
  dsimp [Iraw]
  field_simp [hsqrt_ne, hA_ne, hB_ne]

/--
Appendix C, Theorem 8: the cleared density/CDF expression is exactly the
`erf/J` conditional integral ratio used in the C.5--C.6 derivative proof.
-/
theorem theorem8GaussianDensityCDFIntegralRatioAt_eq_conditional
    (xi xj a : ℝ) :
    theorem8GaussianDensityCDFIntegralRatioAt xi xj a =
      theorem8GaussianConditionalIntegralRatioAt xi xj a := by
  have hint := theorem8Gaussian_integral_shift_split xi xj a
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
    Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hA_ne : 1 + theorem8Erf (a - xi) ≠ 0 :=
    (theorem8Erf_one_add_pos (a - xi)).ne'
  have hB_ne : 1 + theorem8Erf (a - xj) ≠ 0 :=
    (theorem8Erf_one_add_pos (a - xj)).ne'
  unfold theorem8GaussianDensityCDFIntegralRatioAt
    theorem8GaussianConditionalIntegralRatioAt
    theorem8GaussianConditionalIntegralRatio
  rw [hint]
  have harg : a - xi + (xi - xj) = a - xj := by ring
  rw [harg]
  field_simp [hsqrt_ne, hA_ne, hB_ne]

/--
Appendix C, Theorem 8: the paper's Gaussian density/CDF integral expression
has strictly positive derivative in the cutoff `a`.
-/
theorem theorem8GaussianPDFCDFRatioAt_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => theorem8GaussianPDFCDFRatioAt xi xj u) d a ∧
        0 < d := by
  obtain ⟨d, hd, hdpos⟩ :=
    theorem8GaussianConditionalIntegralRatioAt_hasDerivAt_pos
      (xi := xi) (xj := xj) (a := a) hx
  refine ⟨d, ?_, hdpos⟩
  have hdensity :
      HasDerivAt
        (fun u => theorem8GaussianDensityCDFIntegralRatioAt xi xj u)
        d a :=
    hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        theorem8GaussianDensityCDFIntegralRatioAt_eq_conditional xi xj u)
  exact hdensity.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u =>
      theorem8GaussianPDFCDFRatioAt_eq_densityCDF xi xj u)

/--
Appendix C, Theorem 8: canonical product probability space for two independent
Gaussian scores with means `x_i`, `x_j` and variance `1/2`.
-/
noncomputable def theorem8GaussianPairMeasure (xi xj : ℝ) : Measure (ℝ × ℝ) :=
  (ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)).prod
    (ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0))

/--
Appendix C, Theorem 8: numerator event for the canonical product bridge,
written with weak inequalities.  For continuous Gaussians this agrees in
measure with the strict paper event `X_i > X_j, X_i < a, X_j < a`.
-/
def theorem8GaussianPairNumeratorEvent (a : ℝ) : Set (ℝ × ℝ) := {p | p.1 ≤ a ∧ p.2 ≤ p.1}

/-- Appendix C, Theorem 8: conditioning event for the product bridge. -/
def theorem8GaussianPairDenominatorEvent (a : ℝ) : Set (ℝ × ℝ) := Set.Iic a ×ˢ Set.Iic a

/-- Appendix C, Theorem 8: unconditional pairwise winner event. -/
def theorem8GaussianPairWinnerEvent : Set (ℝ × ℝ) := {p | p.2 ≤ p.1}

/--
Appendix C, Theorem 8: conditioning event where the first coordinate is
strictly below the cutoff and the second is weakly below it.
-/
def theorem8GaussianPairLeftStrictDenominatorEvent (a : ℝ) : Set (ℝ × ℝ) :=
  Set.Iio a ×ˢ Set.Iic a

/--
Appendix C, Theorem 8: numerator event in the strict paper syntax,
`X_i < a`, `X_j < X_i`.
-/
def theorem8GaussianPairStrictNumeratorEvent (a : ℝ) : Set (ℝ × ℝ) := {p | p.1 < a ∧ p.2 < p.1}

/--
Appendix C, Theorem 8: strict conditioning event in the paper syntax,
`X_i < a`, `X_j < a`.
-/
def theorem8GaussianPairStrictDenominatorEvent (a : ℝ) : Set (ℝ × ℝ) := Set.Iio a ×ˢ Set.Iio a

/-- Appendix C, Theorem 8: measurability of the product-bridge numerator. -/
theorem theorem8GaussianPairNumeratorEvent_measurable (a : ℝ) :
    MeasurableSet (theorem8GaussianPairNumeratorEvent a) := by
  unfold theorem8GaussianPairNumeratorEvent
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_snd measurable_fst)

/-- Appendix C, Theorem 8: measurability of the unconditional pairwise winner event. -/
theorem theorem8GaussianPairWinnerEvent_measurable :
    MeasurableSet theorem8GaussianPairWinnerEvent := by
  unfold theorem8GaussianPairWinnerEvent
  exact measurableSet_le measurable_snd measurable_fst

/--
Appendix C, Theorem 8: measurability of the strict paper-syntax numerator.
-/
theorem theorem8GaussianPairStrictNumeratorEvent_measurable (a : ℝ) :
    MeasurableSet (theorem8GaussianPairStrictNumeratorEvent a) := by
  unfold theorem8GaussianPairStrictNumeratorEvent
  exact (measurableSet_lt measurable_fst measurable_const).inter
    (measurableSet_lt measurable_snd measurable_fst)

/--
Appendix C, Theorem 8: a Gaussian has no mass at the cutoff, so strict and
weak one-sided lower intervals have the same mass.
-/
theorem theorem8GaussianReal_Iio_eq_Iic (μ a : ℝ) :
    ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0) (Set.Iio a) =
      ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0) (Set.Iic a) := by
  have hvar : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  haveI : NoAtoms (ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0)) :=
    ProbabilityTheory.noAtoms_gaussianReal hvar
  exact measure_congr
    (Iio_ae_eq_Iic
      (μ := ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0)) (a := a))

/--
Appendix C, Theorem 8: Tonelli/product-measure form of the numerator event.
-/
theorem theorem8GaussianPairNumerator_measure_eq_lintegral (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairNumeratorEvent a) =
      ∫⁻ x in Set.Iic a,
        ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0) (Set.Iic x)
        ∂ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0) := by
  let μi := ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)
  let μj := ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0)
  have hmeas := theorem8GaussianPairNumeratorEvent_measurable a
  unfold theorem8GaussianPairMeasure
  change μi.prod μj (theorem8GaussianPairNumeratorEvent a) =
    ∫⁻ x in Set.Iic a, μj (Set.Iic x) ∂μi
  rw [Measure.prod_apply hmeas]
  rw [← lintegral_indicator measurableSet_Iic]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ≤ a
  · have hsection :
        Prod.mk x ⁻¹' theorem8GaussianPairNumeratorEvent a = Set.Iic x := by
        ext y
        simp [theorem8GaussianPairNumeratorEvent, hx]
    simp [hsection, hx]
  · have hsection :
        Prod.mk x ⁻¹' theorem8GaussianPairNumeratorEvent a =
          (∅ : Set ℝ) := by
        ext y
        simp [theorem8GaussianPairNumeratorEvent, hx]
    have hxnot : x ∉ Set.Iic a := by
      simpa using hx
    simp [hsection, hxnot]

/--
Appendix C, Theorem 8: Fubini/density bridge from the product numerator event
to the paper's one-dimensional Gaussian density/CDF integral.
-/
theorem theorem8GaussianPairNumerator_measure_eq_integral (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairNumeratorEvent a) =
      ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
  let μi := ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)
  let μj := ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0)
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  have h_int := theorem8GaussianPDF_mul_CDF_integrableOn xi xj a
  have h_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Iic a)]
        (fun x : ℝ => theorem8GaussianPDF xi x *
          theorem8GaussianCDF xj x) :=
    ae_of_all _ fun x =>
      mul_nonneg (theorem8GaussianPDF_nonneg xi x)
        (theorem8GaussianCDF_nonneg xj x)
  calc
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairNumeratorEvent a)
        = ∫⁻ x in Set.Iic a, μj (Set.Iic x) ∂μi := by
          simpa [μi, μj] using
            theorem8GaussianPairNumerator_measure_eq_lintegral xi xj a
    _ = ∫⁻ x in Set.Iic a, ENNReal.ofReal (theorem8GaussianCDF xj x) ∂μi := by
          refine setLIntegral_congr_fun measurableSet_Iic ?_
          intro x _hx
          exact theorem8GaussianReal_Iic_eq_CDF xj x
    _ = ∫⁻ x in Set.Iic a,
          ProbabilityTheory.gaussianPDF xi (1 / 2 : ℝ≥0) x *
            ENNReal.ofReal (theorem8GaussianCDF xj x) := by
          dsimp [μi]
          rw [ProbabilityTheory.gaussianReal_of_var_ne_zero xi hv]
          exact setLIntegral_withDensity_eq_setLIntegral_mul volume
            (ProbabilityTheory.measurable_gaussianPDF xi (1 / 2 : ℝ≥0))
            ((by
              have hcont : Continuous fun x : ℝ => theorem8GaussianCDF xj x := by
                unfold theorem8GaussianCDF
                exact ((theorem8Erf_continuous.comp
                  (continuous_id.sub continuous_const)).const_add 1).div_const 2
              exact hcont.measurable.ennreal_ofReal) : Measurable fun x : ℝ =>
                ENNReal.ofReal (theorem8GaussianCDF xj x))
            measurableSet_Iic
    _ = ∫⁻ x in Set.Iic a,
          ENNReal.ofReal
            (theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
          refine setLIntegral_congr_fun measurableSet_Iic ?_
          intro x _hx
          change ProbabilityTheory.gaussianPDF xi (1 / 2 : ℝ≥0) x *
              ENNReal.ofReal (theorem8GaussianCDF xj x) =
            ENNReal.ofReal
              (theorem8GaussianPDF xi x * theorem8GaussianCDF xj x)
          rw [← theorem8GaussianPDF_ofReal_eq_gaussianPDF_half]
          rw [ENNReal.ofReal_mul (theorem8GaussianPDF_nonneg xi x)]
    _ = ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
          simpa using
            (ofReal_integral_eq_lintegral_ofReal
              (μ := volume.restrict (Set.Iic a)) h_int h_nonneg).symm

/--
Appendix C, Theorem 8: Tonelli/product-measure form of the unconditional
pairwise winner event.
-/
theorem theorem8GaussianPairWinner_measure_eq_lintegral (xi xj : ℝ) :
    theorem8GaussianPairMeasure xi xj theorem8GaussianPairWinnerEvent =
      ∫⁻ x,
        ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0) (Set.Iic x)
        ∂ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0) := by
  let μi := ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)
  let μj := ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0)
  unfold theorem8GaussianPairMeasure
  change μi.prod μj theorem8GaussianPairWinnerEvent =
    ∫⁻ x, μj (Set.Iic x) ∂μi
  rw [Measure.prod_apply theorem8GaussianPairWinnerEvent_measurable]
  refine lintegral_congr fun x => ?_
  have hsection :
      Prod.mk x ⁻¹' theorem8GaussianPairWinnerEvent = Set.Iic x := by
    ext y
    simp [theorem8GaussianPairWinnerEvent]
  simp [hsection]

/--
Appendix C, Theorem 8: the unconditional pairwise winner probability is the
paper's full Gaussian density/CDF integral.
-/
theorem theorem8GaussianPairWinner_measure_eq_integral (xi xj : ℝ) :
    theorem8GaussianPairMeasure xi xj theorem8GaussianPairWinnerEvent =
      ENNReal.ofReal
        (∫ x : ℝ, theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
  let μi := ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)
  let μj := ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0)
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  have h_int := theorem8GaussianPDF_mul_CDF_integrable xi xj
  have h_nonneg :
      0 ≤ᵐ[volume]
        (fun x : ℝ => theorem8GaussianPDF xi x *
          theorem8GaussianCDF xj x) :=
    ae_of_all _ fun x =>
      mul_nonneg (theorem8GaussianPDF_nonneg xi x)
        (theorem8GaussianCDF_nonneg xj x)
  calc
    theorem8GaussianPairMeasure xi xj theorem8GaussianPairWinnerEvent
        = ∫⁻ x, μj (Set.Iic x) ∂μi := by
          simpa [μi, μj] using
            theorem8GaussianPairWinner_measure_eq_lintegral xi xj
    _ = ∫⁻ x, ENNReal.ofReal (theorem8GaussianCDF xj x) ∂μi := by
          refine lintegral_congr fun x => ?_
          exact theorem8GaussianReal_Iic_eq_CDF xj x
    _ = ∫⁻ x,
          ProbabilityTheory.gaussianPDF xi (1 / 2 : ℝ≥0) x *
            ENNReal.ofReal (theorem8GaussianCDF xj x) := by
          dsimp [μi]
          rw [ProbabilityTheory.gaussianReal_of_var_ne_zero xi hv]
          exact lintegral_withDensity_eq_lintegral_mul
            volume
            (ProbabilityTheory.measurable_gaussianPDF xi (1 / 2 : ℝ≥0))
            ((by
              have hcont : Continuous fun x : ℝ => theorem8GaussianCDF xj x := by
                unfold theorem8GaussianCDF
                exact ((theorem8Erf_continuous.comp
                  (continuous_id.sub continuous_const)).const_add 1).div_const 2
              exact hcont.measurable.ennreal_ofReal) : Measurable fun x : ℝ =>
                ENNReal.ofReal (theorem8GaussianCDF xj x))
    _ = ∫⁻ x,
          ENNReal.ofReal
            (theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
          refine lintegral_congr fun x => ?_
          change ProbabilityTheory.gaussianPDF xi (1 / 2 : ℝ≥0) x *
              ENNReal.ofReal (theorem8GaussianCDF xj x) =
            ENNReal.ofReal
              (theorem8GaussianPDF xi x * theorem8GaussianCDF xj x)
          rw [← theorem8GaussianPDF_ofReal_eq_gaussianPDF_half]
          rw [ENNReal.ofReal_mul (theorem8GaussianPDF_nonneg xi x)]
    _ = ENNReal.ofReal
        (∫ x : ℝ, theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
          simpa using
            (ofReal_integral_eq_lintegral_ofReal h_int h_nonneg).symm

/--
Appendix C, Theorem 8: Tonelli/product-measure form of the strict
paper-syntax numerator event.
-/
theorem theorem8GaussianPairStrictNumerator_measure_eq_lintegral (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairStrictNumeratorEvent a) =
      ∫⁻ x in Set.Iio a,
        ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0) (Set.Iio x)
        ∂ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0) := by
  let μi := ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)
  let μj := ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0)
  have hmeas := theorem8GaussianPairStrictNumeratorEvent_measurable a
  unfold theorem8GaussianPairMeasure
  change μi.prod μj (theorem8GaussianPairStrictNumeratorEvent a) =
    ∫⁻ x in Set.Iio a, μj (Set.Iio x) ∂μi
  rw [Measure.prod_apply hmeas]
  rw [← lintegral_indicator measurableSet_Iio]
  refine lintegral_congr fun x => ?_
  by_cases hx : x < a
  · have hsection :
        Prod.mk x ⁻¹' theorem8GaussianPairStrictNumeratorEvent a = Set.Iio x := by
        ext y
        simp [theorem8GaussianPairStrictNumeratorEvent, hx]
    simp [hsection, hx]
  · have hsection :
        Prod.mk x ⁻¹' theorem8GaussianPairStrictNumeratorEvent a =
          (∅ : Set ℝ) := by
        ext y
        simp [theorem8GaussianPairStrictNumeratorEvent, hx]
    have hxnot : x ∉ Set.Iio a := by
      simpa using hx
    simp [hsection, hxnot]

/--
Appendix C, Theorem 8: strict paper-syntax numerator has the same mass as the
weak bridge numerator, hence the same Gaussian density/CDF integral.
-/
theorem theorem8GaussianPairStrictNumerator_measure_eq_integral (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairStrictNumeratorEvent a) =
      ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
  let μi := ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)
  let μj := ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0)
  have hvar : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  haveI : NoAtoms μi := ProbabilityTheory.noAtoms_gaussianReal hvar
  calc
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairStrictNumeratorEvent a)
        = ∫⁻ x in Set.Iio a, μj (Set.Iio x) ∂μi := by
          simpa [μi, μj] using
            theorem8GaussianPairStrictNumerator_measure_eq_lintegral xi xj a
    _ = ∫⁻ x in Set.Iio a, μj (Set.Iic x) ∂μi := by
          refine setLIntegral_congr_fun measurableSet_Iio ?_
          intro x _hx
          exact theorem8GaussianReal_Iio_eq_Iic xj x
    _ = ∫⁻ x in Set.Iic a, μj (Set.Iic x) ∂μi :=
          setLIntegral_congr
            (μ := μi) (f := fun x : ℝ => μj (Set.Iic x))
            (Iio_ae_eq_Iic (μ := μi) (a := a))
    _ = theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairNumeratorEvent a) := by
          simpa [μi, μj] using
            (theorem8GaussianPairNumerator_measure_eq_lintegral xi xj a).symm
    _ = ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) :=
          theorem8GaussianPairNumerator_measure_eq_integral xi xj a

/--
Appendix C, Theorem 8: product-measure mass of the conditioning event.
-/
theorem theorem8GaussianPairDenominator_measure_eq (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairDenominatorEvent a) =
      ENNReal.ofReal
        (theorem8GaussianCDF xi a * theorem8GaussianCDF xj a) := by
  unfold theorem8GaussianPairMeasure theorem8GaussianPairDenominatorEvent
  rw [Measure.prod_prod]
  rw [theorem8GaussianReal_Iic_eq_CDF xi a,
    theorem8GaussianReal_Iic_eq_CDF xj a]
  rw [← ENNReal.ofReal_mul (theorem8GaussianCDF_nonneg xi a)]

/--
Appendix C, Theorem 8: product-measure mass of the strict paper-syntax
conditioning event.
-/
theorem theorem8GaussianPairStrictDenominator_measure_eq (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairStrictDenominatorEvent a) =
      ENNReal.ofReal
        (theorem8GaussianCDF xi a * theorem8GaussianCDF xj a) := by
  unfold theorem8GaussianPairMeasure theorem8GaussianPairStrictDenominatorEvent
  rw [Measure.prod_prod]
  rw [theorem8GaussianReal_Iio_eq_Iic xi a,
    theorem8GaussianReal_Iio_eq_Iic xj a]
  rw [theorem8GaussianReal_Iic_eq_CDF xi a,
    theorem8GaussianReal_Iic_eq_CDF xj a]
  rw [← ENNReal.ofReal_mul (theorem8GaussianCDF_nonneg xi a)]

/--
Appendix C, Theorem 8: making only the first coordinate cutoff strict does not
change the Gaussian product mass.
-/
theorem theorem8GaussianPairLeftStrictDenominator_measure_eq_denominator
    (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairLeftStrictDenominatorEvent a) =
      theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairDenominatorEvent a) := by
  unfold theorem8GaussianPairMeasure theorem8GaussianPairLeftStrictDenominatorEvent
    theorem8GaussianPairDenominatorEvent
  rw [Measure.prod_prod, Measure.prod_prod]
  rw [theorem8GaussianReal_Iio_eq_Iic xi a]

/--
Appendix C, Theorem 8: making both coordinate cutoffs strict does not change
the Gaussian product conditioning mass.
-/
theorem theorem8GaussianPairStrictDenominator_measure_eq_denominator
    (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairStrictDenominatorEvent a) =
      theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairDenominatorEvent a) := by
  rw [theorem8GaussianPairStrictDenominator_measure_eq,
    theorem8GaussianPairDenominator_measure_eq]

/--
Appendix C, Theorem 8: canonical product-probability conditional ratio
corresponding to the source expression
`Pr[X_i > X_j | X_i < a, X_j < a]`, stated with weak inequalities on null
boundaries.
-/
noncomputable def theorem8GaussianProductConditionalRatioAt
    (xi xj a : ℝ) : ℝ :=
  (theorem8GaussianPairMeasure xi xj
      (theorem8GaussianPairNumeratorEvent a)).toReal /
    (theorem8GaussianPairMeasure xi xj
      (theorem8GaussianPairDenominatorEvent a)).toReal

/--
Appendix C, Theorem 8: canonical product-probability conditional ratio in the
paper's strict event syntax.
-/
noncomputable def theorem8GaussianProductStrictConditionalRatioAt
    (xi xj a : ℝ) : ℝ :=
  (theorem8GaussianPairMeasure xi xj
      (theorem8GaussianPairStrictNumeratorEvent a)).toReal /
    (theorem8GaussianPairMeasure xi xj
      (theorem8GaussianPairStrictDenominatorEvent a)).toReal

/--
Appendix C, Theorem 8: the canonical product-probability ratio equals the
paper's Gaussian density/CDF ratio.
-/
theorem theorem8GaussianProductConditionalRatioAt_eq_pdf_cdf
    (xi xj a : ℝ) :
    theorem8GaussianProductConditionalRatioAt xi xj a =
      theorem8GaussianPDFCDFRatioAt xi xj a := by
  have hI_nonneg :
      0 ≤
        (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
    refine integral_nonneg fun x => ?_
    exact mul_nonneg (theorem8GaussianPDF_nonneg xi x)
      (theorem8GaussianCDF_nonneg xj x)
  have hden_nonneg :
      0 ≤ theorem8GaussianCDF xi a * theorem8GaussianCDF xj a :=
    mul_nonneg (theorem8GaussianCDF_nonneg xi a)
      (theorem8GaussianCDF_nonneg xj a)
  unfold theorem8GaussianProductConditionalRatioAt
    theorem8GaussianPDFCDFRatioAt
  rw [theorem8GaussianPairNumerator_measure_eq_integral,
    theorem8GaussianPairDenominator_measure_eq]
  rw [ENNReal.toReal_ofReal hI_nonneg, ENNReal.toReal_ofReal hden_nonneg]

/--
Appendix C, Theorem 8: the strict paper-syntax product-probability ratio equals
the paper's Gaussian density/CDF ratio.
-/
theorem theorem8GaussianProductStrictConditionalRatioAt_eq_pdf_cdf
    (xi xj a : ℝ) :
    theorem8GaussianProductStrictConditionalRatioAt xi xj a =
      theorem8GaussianPDFCDFRatioAt xi xj a := by
  have hI_nonneg :
      0 ≤
        (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
    refine integral_nonneg fun x => ?_
    exact mul_nonneg (theorem8GaussianPDF_nonneg xi x)
      (theorem8GaussianCDF_nonneg xj x)
  have hden_nonneg :
      0 ≤ theorem8GaussianCDF xi a * theorem8GaussianCDF xj a :=
    mul_nonneg (theorem8GaussianCDF_nonneg xi a)
      (theorem8GaussianCDF_nonneg xj a)
  unfold theorem8GaussianProductStrictConditionalRatioAt
    theorem8GaussianPDFCDFRatioAt
  rw [theorem8GaussianPairStrictNumerator_measure_eq_integral,
    theorem8GaussianPairStrictDenominator_measure_eq]
  rw [ENNReal.toReal_ofReal hI_nonneg, ENNReal.toReal_ofReal hden_nonneg]

/--
Appendix C, Theorem 8: the canonical product-probability conditional ratio has
strictly positive derivative in the cutoff `a`.
-/
theorem theorem8GaussianProductConditionalRatioAt_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => theorem8GaussianProductConditionalRatioAt xi xj u)
        d a ∧
        0 < d := by
  obtain ⟨d, hd, hdpos⟩ :=
    theorem8GaussianPDFCDFRatioAt_hasDerivAt_pos
      (xi := xi) (xj := xj) (a := a) hx
  refine ⟨d, ?_, hdpos⟩
  exact hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u =>
      theorem8GaussianProductConditionalRatioAt_eq_pdf_cdf xi xj u)

/--
Appendix C, Theorem 8: the strict paper-syntax product-probability conditional
ratio has strictly positive derivative in the cutoff `a`.
-/
theorem theorem8GaussianProductStrictConditionalRatioAt_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => theorem8GaussianProductStrictConditionalRatioAt xi xj u)
        d a ∧
        0 < d := by
  obtain ⟨d, hd, hdpos⟩ :=
    theorem8GaussianPDFCDFRatioAt_hasDerivAt_pos
      (xi := xi) (xj := xj) (a := a) hx
  refine ⟨d, ?_, hdpos⟩
  exact hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u =>
      theorem8GaussianProductStrictConditionalRatioAt_eq_pdf_cdf xi xj u)

/--
Appendix C, Theorem 8: the Gaussian density/CDF conditional ratio tends to
the unconditional pairwise numerator as the cutoff tends to `+∞`.
-/
theorem theorem8GaussianPDFCDFRatioAt_tendsto_atTop_unconditionalIntegral
    (xi xj : ℝ) :
    Filter.Tendsto (fun a => theorem8GaussianPDFCDFRatioAt xi xj a)
      Filter.atTop
      (nhds (∫ x : ℝ,
        theorem8GaussianPDF xi x * theorem8GaussianCDF xj x)) := by
  have hnum :=
    theorem8GaussianPDF_mul_CDF_integral_Iic_tendsto_atTop xi xj
  have hden :
      Filter.Tendsto
        (fun a => theorem8GaussianCDF xi a * theorem8GaussianCDF xj a)
        Filter.atTop (nhds 1) := by
    have hi := theorem8GaussianCDF_tendsto_atTop_one xi
    have hj := theorem8GaussianCDF_tendsto_atTop_one xj
    simpa [show (1 : ℝ) * 1 = 1 by norm_num] using hi.mul hj
  have hratio := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  simpa [theorem8GaussianPDFCDFRatioAt] using hratio

/--
Appendix C, Theorem 8: the strict product-measure conditional ratio has the
same right-tail limit, because strict and weak cutoff events differ only on
Gaussian null boundaries.
-/
theorem theorem8GaussianProductStrictConditionalRatioAt_tendsto_atTop_unconditionalIntegral
    (xi xj : ℝ) :
    Filter.Tendsto
      (fun a => theorem8GaussianProductStrictConditionalRatioAt xi xj a)
      Filter.atTop
      (nhds (∫ x : ℝ,
        theorem8GaussianPDF xi x * theorem8GaussianCDF xj x)) :=
  (theorem8GaussianPDFCDFRatioAt_tendsto_atTop_unconditionalIntegral xi xj).congr'
    (Filter.Eventually.of_forall fun a =>
      (theorem8GaussianProductStrictConditionalRatioAt_eq_pdf_cdf xi xj a).symm)

/--
Appendix C, Theorem 8: every finite Gaussian cutoff conditional ratio is
strictly below the unconditional pairwise numerator.
-/
theorem theorem8GaussianProductStrictConditionalRatioAt_lt_unconditionalIntegral
    {xi xj a : ℝ} (hx : xj < xi) :
    theorem8GaussianProductStrictConditionalRatioAt xi xj a <
      ∫ x : ℝ, theorem8GaussianPDF xi x * theorem8GaussianCDF xj x := by
  let F : ℝ → ℝ := fun u => theorem8GaussianProductStrictConditionalRatioAt xi xj u
  let F' : ℝ → ℝ := fun u =>
    Classical.choose
      (theorem8GaussianProductStrictConditionalRatioAt_hasDerivAt_pos
        (xi := xi) (xj := xj) (a := u) hx)
  have hderiv : ∀ u, HasDerivAt F (F' u) u := by
    intro u
    dsimp [F']
    exact
      (Classical.choose_spec
        (theorem8GaussianProductStrictConditionalRatioAt_hasDerivAt_pos
          (xi := xi) (xj := xj) (a := u) hx)).1
  have hpos : ∀ u, 0 < F' u := by
    intro u
    dsimp [F']
    exact
      (Classical.choose_spec
        (theorem8GaussianProductStrictConditionalRatioAt_hasDerivAt_pos
          (xi := xi) (xj := xj) (a := u) hx)).2
  have hmono : StrictMono F := strictMono_of_hasDerivAt_pos hderiv hpos
  have hlim :=
    theorem8GaussianProductStrictConditionalRatioAt_tendsto_atTop_unconditionalIntegral
      xi xj
  exact strictMono_lt_tendsto_atTop_limit
    (f := F)
    (L := ∫ x : ℝ, theorem8GaussianPDF xi x * theorem8GaussianCDF xj x)
    hmono hlim a

/--
Appendix C, Theorem 8: the weak-boundary product-probability conditional ratio
has the same strict finite-cutoff bound as the paper's strict syntax, because
Gaussian boundary events have zero mass.
-/
theorem theorem8GaussianProductConditionalRatioAt_lt_unconditionalIntegral
    {xi xj a : ℝ} (hx : xj < xi) :
    theorem8GaussianProductConditionalRatioAt xi xj a <
      ∫ x : ℝ, theorem8GaussianPDF xi x * theorem8GaussianCDF xj x := by
  have h :=
    theorem8GaussianProductStrictConditionalRatioAt_lt_unconditionalIntegral
      (xi := xi) (xj := xj) (a := a) hx
  rwa [theorem8GaussianProductStrictConditionalRatioAt_eq_pdf_cdf,
    ← theorem8GaussianProductConditionalRatioAt_eq_pdf_cdf] at h

/--
Appendix C, Theorem 8: product-form inequality obtained by multiplying the
finite-cutoff conditional-ratio comparison by the positive conditioning mass.
-/
theorem theorem8GaussianPairNumerator_toReal_lt_winner_mul_denominator
    {xi xj a : ℝ} (hx : xj < xi) :
    (theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairNumeratorEvent a)).toReal <
      (theorem8GaussianPairMeasure xi xj
        theorem8GaussianPairWinnerEvent).toReal *
        (theorem8GaussianPairMeasure xi xj
          (theorem8GaussianPairDenominatorEvent a)).toReal := by
  have hratio :=
    theorem8GaussianProductConditionalRatioAt_lt_unconditionalIntegral
      (xi := xi) (xj := xj) (a := a) hx
  have hden_pos :
      0 <
        (theorem8GaussianPairMeasure xi xj
          (theorem8GaussianPairDenominatorEvent a)).toReal := by
    have hcdf_pos :
        0 < theorem8GaussianCDF xi a * theorem8GaussianCDF xj a :=
      mul_pos (theorem8GaussianCDF_pos xi a) (theorem8GaussianCDF_pos xj a)
    rw [theorem8GaussianPairDenominator_measure_eq,
      ENNReal.toReal_ofReal (le_of_lt hcdf_pos)]
    exact hcdf_pos
  have hwinner_nonneg :
      0 ≤ ∫ x : ℝ, theorem8GaussianPDF xi x * theorem8GaussianCDF xj x := by
    refine integral_nonneg fun x => ?_
    exact mul_nonneg (theorem8GaussianPDF_nonneg xi x)
      (theorem8GaussianCDF_nonneg xj x)
  have hwinner_eq :
      (theorem8GaussianPairMeasure xi xj
        theorem8GaussianPairWinnerEvent).toReal =
        ∫ x : ℝ, theorem8GaussianPDF xi x * theorem8GaussianCDF xj x := by
    rw [theorem8GaussianPairWinner_measure_eq_integral,
      ENNReal.toReal_ofReal hwinner_nonneg]
  rw [← hwinner_eq] at hratio
  unfold theorem8GaussianProductConditionalRatioAt at hratio
  exact (div_lt_iff₀ hden_pos).mp hratio

/-! ### Gaussian three-score source bridge for Definition 2 -/

/--
Source space for the Gaussian Definition-2 bridge, grouped as
`(score₁, (score₂, score₃))` so conditioning on `score₁` exposes the existing
two-score Gaussian product theorem.
-/
abbrev Theorem8GaussianDefinition2ScoreSpace := ℝ × (ℝ × ℝ)

/-- Independent Gaussian source law for the Definition-2 bridge. -/
noncomputable def theorem8GaussianDefinition2ScoreMeasure
    (x1 x2 x3 : ℝ) : Measure Theorem8GaussianDefinition2ScoreSpace :=
  (ProbabilityTheory.gaussianReal x1 (1 / 2 : ℝ≥0)).prod
    (theorem8GaussianPairMeasure x2 x3)

instance theorem8GaussianDefinition2ScoreMeasure_isProbabilityMeasure
    (x1 x2 x3 : ℝ) :
    IsProbabilityMeasure (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3) := by
  dsimp [theorem8GaussianDefinition2ScoreMeasure, theorem8GaussianPairMeasure]
  infer_instance

/-- First Gaussian score coordinate. -/
def theorem8GaussianDefinition2Score1
    (ω : Theorem8GaussianDefinition2ScoreSpace) : ℝ := ω.1

/-- Second Gaussian score coordinate. -/
def theorem8GaussianDefinition2Score2
    (ω : Theorem8GaussianDefinition2ScoreSpace) : ℝ := ω.2.1

/-- Third Gaussian score coordinate. -/
def theorem8GaussianDefinition2Score3
    (ω : Theorem8GaussianDefinition2ScoreSpace) : ℝ := ω.2.2

theorem theorem8GaussianDefinition2Score1_measurable :
    Measurable theorem8GaussianDefinition2Score1 := measurable_fst

theorem theorem8GaussianDefinition2Score2_measurable :
    Measurable theorem8GaussianDefinition2Score2 := measurable_snd.fst

theorem theorem8GaussianDefinition2Score3_measurable :
    Measurable theorem8GaussianDefinition2Score3 := measurable_snd.snd

/-- Swap the first two coordinates in the Definition-2 Gaussian source space. -/
def theorem8GaussianDefinition2Swap12 :
    Theorem8GaussianDefinition2ScoreSpace ≃ᵐ
      Theorem8GaussianDefinition2ScoreSpace :=
  (MeasurableEquiv.prodAssoc.symm).trans
    (((MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
      (MeasurableEquiv.refl ℝ))).trans MeasurableEquiv.prodAssoc)

@[simp] theorem theorem8GaussianDefinition2Swap12_score1
    (ω : Theorem8GaussianDefinition2ScoreSpace) :
    theorem8GaussianDefinition2Score1
        (theorem8GaussianDefinition2Swap12 ω) =
      theorem8GaussianDefinition2Score2 ω := rfl

@[simp] theorem theorem8GaussianDefinition2Swap12_score2
    (ω : Theorem8GaussianDefinition2ScoreSpace) :
    theorem8GaussianDefinition2Score2
        (theorem8GaussianDefinition2Swap12 ω) =
      theorem8GaussianDefinition2Score1 ω := rfl

@[simp] theorem theorem8GaussianDefinition2Swap12_score3
    (ω : Theorem8GaussianDefinition2ScoreSpace) :
    theorem8GaussianDefinition2Score3
        (theorem8GaussianDefinition2Swap12 ω) =
      theorem8GaussianDefinition2Score3 ω := rfl

/--
The top/middle coordinate swap sends the independent Gaussian score law with
means `(x₁,x₂,x₃)` to the law with means `(x₂,x₁,x₃)`.
-/
theorem theorem8GaussianDefinition2Swap12_measurePreserving
    (x1 x2 x3 : ℝ) :
    MeasurePreserving theorem8GaussianDefinition2Swap12
      (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
      (theorem8GaussianDefinition2ScoreMeasure x2 x1 x3) := by
  let μ1 := ProbabilityTheory.gaussianReal x1 (1 / 2 : ℝ≥0)
  let μ2 := ProbabilityTheory.gaussianReal x2 (1 / 2 : ℝ≥0)
  let μ3 := ProbabilityTheory.gaussianReal x3 (1 / 2 : ℝ≥0)
  have hassoc_symm : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        Theorem8GaussianDefinition2ScoreSpace ≃ᵐ (ℝ × ℝ) × ℝ)
      (μ1.prod (μ2.prod μ3)) ((μ1.prod μ2).prod μ3) :=
    MeasurePreserving.symm
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ
        Theorem8GaussianDefinition2ScoreSpace)
      (MeasureTheory.measurePreserving_prodAssoc μ1 μ2 μ3)
  have hpair : MeasurePreserving Prod.swap (μ1.prod μ2) (μ2.prod μ1) :=
    Measure.measurePreserving_swap
  have hmiddle : MeasurePreserving (Prod.map Prod.swap id)
      ((μ1.prod μ2).prod μ3) ((μ2.prod μ1).prod μ3) := by
    simpa using hpair.prod (MeasurePreserving.id μ3)
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ
        Theorem8GaussianDefinition2ScoreSpace)
      ((μ2.prod μ1).prod μ3) (μ2.prod (μ1.prod μ3)) :=
    MeasureTheory.measurePreserving_prodAssoc μ2 μ1 μ3
  have hcomp := hassoc.comp (hmiddle.comp hassoc_symm)
  simpa [theorem8GaussianDefinition2Swap12,
    theorem8GaussianDefinition2ScoreMeasure, theorem8GaussianPairMeasure,
    μ1, μ2, μ3] using hcomp

/-- Cycle coordinates `(score₁,score₂,score₃)` to `(score₃,score₁,score₂)`. -/
def theorem8GaussianDefinition2Cycle312 :
    Theorem8GaussianDefinition2ScoreSpace ≃ᵐ
      Theorem8GaussianDefinition2ScoreSpace :=
  MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm

@[simp] theorem theorem8GaussianDefinition2Cycle312_score1
    (ω : Theorem8GaussianDefinition2ScoreSpace) :
    theorem8GaussianDefinition2Score1
        (theorem8GaussianDefinition2Cycle312 ω) =
      theorem8GaussianDefinition2Score3 ω := rfl

@[simp] theorem theorem8GaussianDefinition2Cycle312_score2
    (ω : Theorem8GaussianDefinition2ScoreSpace) :
    theorem8GaussianDefinition2Score2
        (theorem8GaussianDefinition2Cycle312 ω) =
      theorem8GaussianDefinition2Score1 ω := rfl

@[simp] theorem theorem8GaussianDefinition2Cycle312_score3
    (ω : Theorem8GaussianDefinition2ScoreSpace) :
    theorem8GaussianDefinition2Score3
        (theorem8GaussianDefinition2Cycle312 ω) =
      theorem8GaussianDefinition2Score2 ω := rfl

/--
The coordinate cycle sends the independent Gaussian score law with means
`(x₁,x₂,x₃)` to the law with means `(x₃,x₁,x₂)`.
-/
theorem theorem8GaussianDefinition2Cycle312_measurePreserving
    (x1 x2 x3 : ℝ) :
    MeasurePreserving theorem8GaussianDefinition2Cycle312
      (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
      (theorem8GaussianDefinition2ScoreMeasure x3 x1 x2) := by
  let μ1 := ProbabilityTheory.gaussianReal x1 (1 / 2 : ℝ≥0)
  let μ2 := ProbabilityTheory.gaussianReal x2 (1 / 2 : ℝ≥0)
  let μ3 := ProbabilityTheory.gaussianReal x3 (1 / 2 : ℝ≥0)
  have hassoc_symm : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        Theorem8GaussianDefinition2ScoreSpace ≃ᵐ (ℝ × ℝ) × ℝ)
      (μ1.prod (μ2.prod μ3)) ((μ1.prod μ2).prod μ3) :=
    MeasurePreserving.symm
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ
        Theorem8GaussianDefinition2ScoreSpace)
      (MeasureTheory.measurePreserving_prodAssoc μ1 μ2 μ3)
  have hcomm : MeasurePreserving Prod.swap
      ((μ1.prod μ2).prod μ3) (μ3.prod (μ1.prod μ2)) :=
    Measure.measurePreserving_swap
  have hcomp := hcomm.comp hassoc_symm
  simpa [theorem8GaussianDefinition2Cycle312,
    theorem8GaussianDefinition2ScoreMeasure, theorem8GaussianPairMeasure,
    μ1, μ2, μ3] using hcomp

/--
Gaussian Definition-2 source inequality for the shared first-choice event
`score₁`: conditioning both lower-valued alternatives below a finite `score₁`
strictly lowers the chance that `score₂` beats `score₃`.
-/
theorem theorem8GaussianDefinition2_event0_score_inter_lt_mul
    {x1 x2 x3 : ℝ} (hx23 : x3 < x2) :
    measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score2 ω ∧
            theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω) <
      measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score2 ω) *
        measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
                theorem8GaussianDefinition2Score1 ω ∧
              theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score1 ω) := by
  let μ1 := ProbabilityTheory.gaussianReal x1 (1 / 2 : ℝ≥0)
  let μ23 := theorem8GaussianPairMeasure x2 x3
  let ν := theorem8GaussianDefinition2ScoreMeasure x1 x2 x3
  haveI : IsProbabilityMeasure μ1 := by
    dsimp [μ1]
    infer_instance
  haveI : IsProbabilityMeasure μ23 := by
    dsimp [μ23, theorem8GaussianPairMeasure]
    infer_instance
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, theorem8GaussianDefinition2ScoreMeasure, μ1, μ23,
      theorem8GaussianPairMeasure]
    infer_instance
  let A : Set Theorem8GaussianDefinition2ScoreSpace :=
    {ω |
      theorem8GaussianDefinition2Score3 ω ≤
          theorem8GaussianDefinition2Score2 ω ∧
        theorem8GaussianDefinition2Score2 ω ≤
          theorem8GaussianDefinition2Score1 ω}
  let B : Set Theorem8GaussianDefinition2ScoreSpace :=
    {ω |
      theorem8GaussianDefinition2Score2 ω ≤
          theorem8GaussianDefinition2Score1 ω ∧
        theorem8GaussianDefinition2Score3 ω ≤
          theorem8GaussianDefinition2Score1 ω}
  let C : Set Theorem8GaussianDefinition2ScoreSpace :=
    {ω |
      theorem8GaussianDefinition2Score3 ω ≤
        theorem8GaussianDefinition2Score2 ω}
  have hA_meas : MeasurableSet A := by
    dsimp [A, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3]
    exact (measurableSet_le measurable_snd.snd measurable_snd.fst).inter
      (measurableSet_le measurable_snd.fst measurable_fst)
  have hB_meas : MeasurableSet B := by
    dsimp [B, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3]
    exact (measurableSet_le measurable_snd.fst measurable_fst).inter
      (measurableSet_le measurable_snd.snd measurable_fst)
  have hC_meas : MeasurableSet C := by
    dsimp [C, theorem8GaussianDefinition2Score2,
      theorem8GaussianDefinition2Score3]
    exact measurableSet_le measurable_snd.snd measurable_snd.fst
  have hν_eq : ν = μ1.prod μ23 := by
    rfl
  let N : ℝ → ℝ := fun a =>
    (μ23 (theorem8GaussianPairNumeratorEvent a)).toReal
  let D : ℝ → ℝ := fun a =>
    (μ23 (theorem8GaussianPairDenominatorEvent a)).toReal
  let P : ℝ := (μ23 theorem8GaussianPairWinnerEvent).toReal
  have hA_section :
      ∀ a,
        μ23 (Prod.mk a ⁻¹' A) =
          μ23 (theorem8GaussianPairNumeratorEvent a) := by
    intro a
    apply congrArg μ23
    ext p
    simp [A, theorem8GaussianPairNumeratorEvent,
      theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2,
      theorem8GaussianDefinition2Score3, and_comm]
  have hB_section :
      ∀ a,
        μ23 (Prod.mk a ⁻¹' B) =
          μ23 (theorem8GaussianPairDenominatorEvent a) := by
    intro a
    apply congrArg μ23
    ext p
    simp [B, theorem8GaussianPairDenominatorEvent,
      theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2,
      theorem8GaussianDefinition2Score3, Prod.le_def]
  have hN_int : Integrable N μ1 := by
    have hraw :
        Integrable (fun a => (μ23 (Prod.mk a ⁻¹' A)).toReal) μ1 := by
      refine integrable_toReal_of_lintegral_ne_top
        (measurable_measure_prodMk_left hA_meas).aemeasurable ?_
      rw [← Measure.prod_apply (μ := μ1) (ν := μ23) hA_meas]
      exact measure_ne_top (μ1.prod μ23) A
    convert hraw using 1
    ext a
    exact congrArg ENNReal.toReal (hA_section a).symm
  have hD_int : Integrable D μ1 := by
    have hraw :
        Integrable (fun a => (μ23 (Prod.mk a ⁻¹' B)).toReal) μ1 := by
      refine integrable_toReal_of_lintegral_ne_top
        (measurable_measure_prodMk_left hB_meas).aemeasurable ?_
      rw [← Measure.prod_apply (μ := μ1) (ν := μ23) hB_meas]
      exact measure_ne_top (μ1.prod μ23) B
    convert hraw using 1
  have hA_prob :
      measureProb ν (fun ω => ω ∈ A) = ∫ a, N a ∂μ1 := by
    unfold measureProb
    change (ν A).toReal = ∫ a, N a ∂μ1
    rw [hν_eq, Measure.prod_apply hA_meas]
    rw [← integral_toReal
      (measurable_measure_prodMk_left hA_meas).aemeasurable
      (ae_of_all μ1 fun a =>
        lt_top_iff_ne_top.2 (measure_ne_top μ23 (Prod.mk a ⁻¹' A)))]
    exact integral_congr_ae
      (ae_of_all μ1 fun a =>
        congrArg ENNReal.toReal (hA_section a))
  have hB_prob :
      measureProb ν (fun ω => ω ∈ B) = ∫ a, D a ∂μ1 := by
    unfold measureProb
    change (ν B).toReal = ∫ a, D a ∂μ1
    rw [hν_eq, Measure.prod_apply hB_meas]
    rw [← integral_toReal
      (measurable_measure_prodMk_left hB_meas).aemeasurable
      (ae_of_all μ1 fun a =>
        lt_top_iff_ne_top.2 (measure_ne_top μ23 (Prod.mk a ⁻¹' B)))]
    exact integral_congr_ae
      (ae_of_all μ1 fun a =>
        congrArg ENNReal.toReal (hB_section a))
  have hC_set :
      C = Set.univ ×ˢ theorem8GaussianPairWinnerEvent := by
    ext ω
    simp [C, theorem8GaussianPairWinnerEvent,
      theorem8GaussianDefinition2Score2,
      theorem8GaussianDefinition2Score3]
  have hC_prob :
      measureProb ν (fun ω => ω ∈ C) = P := by
    unfold measureProb
    change (ν C).toReal = P
    rw [hν_eq, hC_set, Measure.prod_prod]
    simp [P]
  have hfiber : ∀ a, N a < P * D a := by
    intro a
    dsimp [N, D, P, μ23]
    exact theorem8GaussianPairNumerator_toReal_lt_winner_mul_denominator
      (xi := x2) (xj := x3) (a := a) hx23
  have hmain :
      measureProb ν (fun ω => ω ∈ A) <
        measureProb ν (fun ω => ω ∈ C) *
          measureProb ν (fun ω => ω ∈ B) :=
    measureProb_lt_mul_of_integral_fiber_lt
      μ1 ν (fun ω => ω ∈ A) (fun ω => ω ∈ B) (fun ω => ω ∈ C)
      hN_int hD_int hA_prob hB_prob hC_prob hfiber
  simpa [A, B, C, ν, theorem8GaussianDefinition2ScoreMeasure] using hmain

/--
Gaussian Definition-2 source boundary hygiene: for the event0 source law,
making the middle score strictly below the top score does not change the first
choice event probability.
-/
theorem theorem8GaussianDefinition2_event0_first_weak_eq_leftStrict
    (x1 x2 x3 : ℝ) :
    measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω) =
      measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score2 ω <
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω) := by
  let μ1 := ProbabilityTheory.gaussianReal x1 (1 / 2 : ℝ≥0)
  let μ23 := theorem8GaussianPairMeasure x2 x3
  let ν := theorem8GaussianDefinition2ScoreMeasure x1 x2 x3
  haveI : SFinite μ23 := by
    dsimp [μ23, theorem8GaussianPairMeasure]
    infer_instance
  have hν_eq : ν = μ1.prod μ23 := by rfl
  let W : Set Theorem8GaussianDefinition2ScoreSpace :=
    {ω |
      theorem8GaussianDefinition2Score2 ω ≤
          theorem8GaussianDefinition2Score1 ω ∧
        theorem8GaussianDefinition2Score3 ω ≤
          theorem8GaussianDefinition2Score1 ω}
  let L : Set Theorem8GaussianDefinition2ScoreSpace :=
    {ω |
      theorem8GaussianDefinition2Score2 ω <
          theorem8GaussianDefinition2Score1 ω ∧
        theorem8GaussianDefinition2Score3 ω ≤
          theorem8GaussianDefinition2Score1 ω}
  have hW_meas : MeasurableSet W := by
    dsimp [W, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3]
    exact (measurableSet_le measurable_snd.fst measurable_fst).inter
      (measurableSet_le measurable_snd.snd measurable_fst)
  have hL_meas : MeasurableSet L := by
    dsimp [L, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3]
    exact (measurableSet_lt measurable_snd.fst measurable_fst).inter
      (measurableSet_le measurable_snd.snd measurable_fst)
  have hW_section :
      ∀ a,
        μ23 (Prod.mk a ⁻¹' W) =
          μ23 (theorem8GaussianPairDenominatorEvent a) := by
    intro a
    apply congrArg μ23
    ext p
    simp [W, theorem8GaussianPairDenominatorEvent,
      theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2,
      theorem8GaussianDefinition2Score3, Prod.le_def]
  have hL_section :
      ∀ a,
        μ23 (Prod.mk a ⁻¹' L) =
          μ23 (theorem8GaussianPairLeftStrictDenominatorEvent a) := by
    intro a
    apply congrArg μ23
    ext p
    simp [L, theorem8GaussianPairLeftStrictDenominatorEvent,
      theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2,
      theorem8GaussianDefinition2Score3]
  unfold measureProb
  change (ν W).toReal = (ν L).toReal
  apply congrArg ENNReal.toReal
  rw [hν_eq, Measure.prod_apply hW_meas, Measure.prod_apply hL_meas]
  refine lintegral_congr fun a => ?_
  rw [hW_section a, hL_section a,
    theorem8GaussianPairLeftStrictDenominator_measure_eq_denominator]

/--
Gaussian Definition-2 source boundary hygiene: for the event0 source law,
making both lower scores strictly below the top score does not change the
first-choice event probability.
-/
theorem theorem8GaussianDefinition2_event0_first_weak_eq_strict
    (x1 x2 x3 : ℝ) :
    measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω) =
      measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score2 ω <
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score3 ω <
              theorem8GaussianDefinition2Score1 ω) := by
  let μ1 := ProbabilityTheory.gaussianReal x1 (1 / 2 : ℝ≥0)
  let μ23 := theorem8GaussianPairMeasure x2 x3
  let ν := theorem8GaussianDefinition2ScoreMeasure x1 x2 x3
  haveI : SFinite μ23 := by
    dsimp [μ23, theorem8GaussianPairMeasure]
    infer_instance
  have hν_eq : ν = μ1.prod μ23 := by rfl
  let W : Set Theorem8GaussianDefinition2ScoreSpace :=
    {ω |
      theorem8GaussianDefinition2Score2 ω ≤
          theorem8GaussianDefinition2Score1 ω ∧
        theorem8GaussianDefinition2Score3 ω ≤
          theorem8GaussianDefinition2Score1 ω}
  let S : Set Theorem8GaussianDefinition2ScoreSpace :=
    {ω |
      theorem8GaussianDefinition2Score2 ω <
          theorem8GaussianDefinition2Score1 ω ∧
        theorem8GaussianDefinition2Score3 ω <
          theorem8GaussianDefinition2Score1 ω}
  have hW_meas : MeasurableSet W := by
    dsimp [W, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3]
    exact (measurableSet_le measurable_snd.fst measurable_fst).inter
      (measurableSet_le measurable_snd.snd measurable_fst)
  have hS_meas : MeasurableSet S := by
    dsimp [S, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3]
    exact (measurableSet_lt measurable_snd.fst measurable_fst).inter
      (measurableSet_lt measurable_snd.snd measurable_fst)
  have hW_section :
      ∀ a,
        μ23 (Prod.mk a ⁻¹' W) =
          μ23 (theorem8GaussianPairDenominatorEvent a) := by
    intro a
    apply congrArg μ23
    ext p
    simp [W, theorem8GaussianPairDenominatorEvent,
      theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2,
      theorem8GaussianDefinition2Score3, Prod.le_def]
  have hS_section :
      ∀ a,
        μ23 (Prod.mk a ⁻¹' S) =
          μ23 (theorem8GaussianPairStrictDenominatorEvent a) := by
    intro a
    apply congrArg μ23
    ext p
    simp [S, theorem8GaussianPairStrictDenominatorEvent,
      theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2,
      theorem8GaussianDefinition2Score3]
  unfold measureProb
  change (ν W).toReal = (ν S).toReal
  apply congrArg ENNReal.toReal
  rw [hν_eq, Measure.prod_apply hW_meas, Measure.prod_apply hS_meas]
  refine lintegral_congr fun a => ?_
  rw [hW_section a, hS_section a,
    theorem8GaussianPairStrictDenominator_measure_eq_denominator]

/--
Gaussian Definition-2 source inequality for the shared first-choice event
`score₂`, in weak-boundary form. Boundary equalities are handled separately
when this is connected to the deterministic tie-breaking ranking rule.
-/
theorem theorem8GaussianDefinition2_event1_weak_score_inter_lt_mul
    {x1 x2 x3 : ℝ} (hx13 : x3 < x1) :
    measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score1 ω ≤
              theorem8GaussianDefinition2Score2 ω) <
      measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
        measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω ≤
                theorem8GaussianDefinition2Score2 ω ∧
              theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score2 ω) := by
  let ν123 := theorem8GaussianDefinition2ScoreMeasure x1 x2 x3
  let ν213 := theorem8GaussianDefinition2ScoreMeasure x2 x1 x3
  let e := theorem8GaussianDefinition2Swap12
  have he : MeasurePreserving e ν123 ν213 := by
    simpa [e, ν123, ν213] using
      theorem8GaussianDefinition2Swap12_measurePreserving x1 x2 x3
  let A : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score3 ω ≤
        theorem8GaussianDefinition2Score2 ω ∧
      theorem8GaussianDefinition2Score2 ω ≤
        theorem8GaussianDefinition2Score1 ω
  let B : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score2 ω ≤
        theorem8GaussianDefinition2Score1 ω ∧
      theorem8GaussianDefinition2Score3 ω ≤
        theorem8GaussianDefinition2Score1 ω
  let C : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score3 ω ≤
      theorem8GaussianDefinition2Score2 ω
  have hbase :
      measureProb ν213 A < measureProb ν213 C * measureProb ν213 B := by
    simpa [ν213, A, B, C] using
      theorem8GaussianDefinition2_event0_score_inter_lt_mul
        (x1 := x2) (x2 := x1) (x3 := x3) hx13
  have hA :
      measureProb ν123 (fun ω => A (e ω)) = measureProb ν213 A :=
    measureProb_preimage_equiv_of_measurePreserving e he A
  have hB :
      measureProb ν123 (fun ω => B (e ω)) = measureProb ν213 B :=
    measureProb_preimage_equiv_of_measurePreserving e he B
  have hC :
      measureProb ν123 (fun ω => C (e ω)) = measureProb ν213 C :=
    measureProb_preimage_equiv_of_measurePreserving e he C
  rw [← hA, ← hB, ← hC] at hbase
  simpa [ν123, e, A, B, C, theorem8GaussianDefinition2ScoreMeasure] using hbase

/-- Boundary hygiene for the event1 first-choice source event. -/
theorem theorem8GaussianDefinition2_event1_first_weak_eq_leftStrict
    (x1 x2 x3 : ℝ) :
    measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score1 ω ≤
              theorem8GaussianDefinition2Score2 ω ∧
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score2 ω) =
      measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score2 ω ∧
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score2 ω) := by
  let ν123 := theorem8GaussianDefinition2ScoreMeasure x1 x2 x3
  let ν213 := theorem8GaussianDefinition2ScoreMeasure x2 x1 x3
  let e := theorem8GaussianDefinition2Swap12
  have he : MeasurePreserving e ν123 ν213 := by
    simpa [e, ν123, ν213] using
      theorem8GaussianDefinition2Swap12_measurePreserving x1 x2 x3
  let W : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score2 ω ≤
        theorem8GaussianDefinition2Score1 ω ∧
      theorem8GaussianDefinition2Score3 ω ≤
        theorem8GaussianDefinition2Score1 ω
  let L : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score2 ω <
        theorem8GaussianDefinition2Score1 ω ∧
      theorem8GaussianDefinition2Score3 ω ≤
        theorem8GaussianDefinition2Score1 ω
  have hbase :
      measureProb ν213 W = measureProb ν213 L := by
    simpa [ν213, W, L] using
      theorem8GaussianDefinition2_event0_first_weak_eq_leftStrict x2 x1 x3
  have hW :
      measureProb ν123 (fun ω => W (e ω)) = measureProb ν213 W :=
    measureProb_preimage_equiv_of_measurePreserving e he W
  have hL :
      measureProb ν123 (fun ω => L (e ω)) = measureProb ν213 L :=
    measureProb_preimage_equiv_of_measurePreserving e he L
  rw [← hW, ← hL] at hbase
  simpa [ν123, e, W, L, theorem8GaussianDefinition2ScoreMeasure] using hbase

/--
Gaussian Definition-2 source inequality for the shared first-choice event
`score₂`, in the strict form used by the deterministic tie-breaking ranking
rule.
-/
theorem theorem8GaussianDefinition2_event1_score_inter_lt_mul
    {x1 x2 x3 : ℝ} (hx13 : x3 < x1) :
    measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score2 ω) <
      measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
        measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω <
                theorem8GaussianDefinition2Score2 ω ∧
              theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score2 ω) := by
  let ν := theorem8GaussianDefinition2ScoreMeasure x1 x2 x3
  haveI : IsFiniteMeasure ν := by
    dsimp [ν, theorem8GaussianDefinition2ScoreMeasure, theorem8GaussianPairMeasure]
    infer_instance
  have hweak :=
    theorem8GaussianDefinition2_event1_weak_score_inter_lt_mul
      (x1 := x1) (x2 := x2) (x3 := x3) hx13
  have hboundary :=
    theorem8GaussianDefinition2_event1_first_weak_eq_leftStrict x1 x2 x3
  have hle :
      measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score1 ω ∧
              theorem8GaussianDefinition2Score1 ω <
                theorem8GaussianDefinition2Score2 ω) ≤
        measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score1 ω ∧
              theorem8GaussianDefinition2Score1 ω ≤
                theorem8GaussianDefinition2Score2 ω) := by
    refine measureProb_le_of_measure_le ν _ _ (measure_mono ?_)
    intro ω hω
    exact ⟨hω.1, le_of_lt hω.2⟩
  calc
    measureProb ν
        (fun ω =>
          theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score2 ω)
        ≤ measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score1 ω ∧
              theorem8GaussianDefinition2Score1 ω ≤
                theorem8GaussianDefinition2Score2 ω) := hle
    _ < measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
        measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω ≤
                theorem8GaussianDefinition2Score2 ω ∧
              theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score2 ω) := by
          simpa [ν] using hweak
    _ = measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
        measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω <
                theorem8GaussianDefinition2Score2 ω ∧
              theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score2 ω) := by
          rw [hboundary]

/--
Gaussian Definition-2 source inequality for the shared first-choice event
`score₃`, in weak-boundary form. Boundary equalities are handled separately
when this is connected to the deterministic tie-breaking ranking rule.
-/
theorem theorem8GaussianDefinition2_event2_weak_score_inter_lt_mul
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) :
    measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score1 ω ≤
              theorem8GaussianDefinition2Score3 ω) <
      measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
        measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω ≤
                theorem8GaussianDefinition2Score3 ω ∧
              theorem8GaussianDefinition2Score2 ω ≤
                theorem8GaussianDefinition2Score3 ω) := by
  let ν123 := theorem8GaussianDefinition2ScoreMeasure x1 x2 x3
  let ν312 := theorem8GaussianDefinition2ScoreMeasure x3 x1 x2
  let e := theorem8GaussianDefinition2Cycle312
  have he : MeasurePreserving e ν123 ν312 := by
    simpa [e, ν123, ν312] using
      theorem8GaussianDefinition2Cycle312_measurePreserving x1 x2 x3
  let A : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score3 ω ≤
        theorem8GaussianDefinition2Score2 ω ∧
      theorem8GaussianDefinition2Score2 ω ≤
        theorem8GaussianDefinition2Score1 ω
  let B : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score2 ω ≤
        theorem8GaussianDefinition2Score1 ω ∧
      theorem8GaussianDefinition2Score3 ω ≤
        theorem8GaussianDefinition2Score1 ω
  let C : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score3 ω ≤
      theorem8GaussianDefinition2Score2 ω
  have hbase :
      measureProb ν312 A < measureProb ν312 C * measureProb ν312 B := by
    simpa [ν312, A, B, C] using
      theorem8GaussianDefinition2_event0_score_inter_lt_mul
        (x1 := x3) (x2 := x1) (x3 := x2) hx12
  have hA :
      measureProb ν123 (fun ω => A (e ω)) = measureProb ν312 A :=
    measureProb_preimage_equiv_of_measurePreserving e he A
  have hB :
      measureProb ν123 (fun ω => B (e ω)) = measureProb ν312 B :=
    measureProb_preimage_equiv_of_measurePreserving e he B
  have hC :
      measureProb ν123 (fun ω => C (e ω)) = measureProb ν312 C :=
    measureProb_preimage_equiv_of_measurePreserving e he C
  rw [← hA, ← hB, ← hC] at hbase
  simpa [ν123, e, A, B, C, theorem8GaussianDefinition2ScoreMeasure] using hbase

/-- Boundary hygiene for the event2 first-choice source event. -/
theorem theorem8GaussianDefinition2_event2_first_weak_eq_strict
    (x1 x2 x3 : ℝ) :
    measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score1 ω ≤
              theorem8GaussianDefinition2Score3 ω ∧
            theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score3 ω) =
      measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score3 ω ∧
            theorem8GaussianDefinition2Score2 ω <
              theorem8GaussianDefinition2Score3 ω) := by
  let ν123 := theorem8GaussianDefinition2ScoreMeasure x1 x2 x3
  let ν312 := theorem8GaussianDefinition2ScoreMeasure x3 x1 x2
  let e := theorem8GaussianDefinition2Cycle312
  have he : MeasurePreserving e ν123 ν312 := by
    simpa [e, ν123, ν312] using
      theorem8GaussianDefinition2Cycle312_measurePreserving x1 x2 x3
  let W : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score2 ω ≤
        theorem8GaussianDefinition2Score1 ω ∧
      theorem8GaussianDefinition2Score3 ω ≤
        theorem8GaussianDefinition2Score1 ω
  let S : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score2 ω <
        theorem8GaussianDefinition2Score1 ω ∧
      theorem8GaussianDefinition2Score3 ω <
        theorem8GaussianDefinition2Score1 ω
  have hbase :
      measureProb ν312 W = measureProb ν312 S := by
    simpa [ν312, W, S] using
      theorem8GaussianDefinition2_event0_first_weak_eq_strict x3 x1 x2
  have hW :
      measureProb ν123 (fun ω => W (e ω)) = measureProb ν312 W :=
    measureProb_preimage_equiv_of_measurePreserving e he W
  have hS :
      measureProb ν123 (fun ω => S (e ω)) = measureProb ν312 S :=
    measureProb_preimage_equiv_of_measurePreserving e he S
  rw [← hW, ← hS] at hbase
  simpa [ν123, e, W, S, theorem8GaussianDefinition2ScoreMeasure] using hbase

/--
Gaussian Definition-2 source inequality for the shared first-choice event
`score₃`, in the strict form used by the deterministic tie-breaking ranking
rule.
-/
theorem theorem8GaussianDefinition2_event2_score_inter_lt_mul
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) :
    measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score3 ω) <
      measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
        measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω <
                theorem8GaussianDefinition2Score3 ω ∧
              theorem8GaussianDefinition2Score2 ω <
                theorem8GaussianDefinition2Score3 ω) := by
  let ν := theorem8GaussianDefinition2ScoreMeasure x1 x2 x3
  haveI : IsFiniteMeasure ν := by
    dsimp [ν, theorem8GaussianDefinition2ScoreMeasure, theorem8GaussianPairMeasure]
    infer_instance
  have hweak :=
    theorem8GaussianDefinition2_event2_weak_score_inter_lt_mul
      (x1 := x1) (x2 := x2) (x3 := x3) hx12
  have hboundary :=
    theorem8GaussianDefinition2_event2_first_weak_eq_strict x1 x2 x3
  have hle :
      measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
                theorem8GaussianDefinition2Score1 ω ∧
              theorem8GaussianDefinition2Score1 ω <
                theorem8GaussianDefinition2Score3 ω) ≤
        measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
                theorem8GaussianDefinition2Score1 ω ∧
              theorem8GaussianDefinition2Score1 ω ≤
                theorem8GaussianDefinition2Score3 ω) := by
    refine measureProb_le_of_measure_le ν _ _ (measure_mono ?_)
    intro ω hω
    exact ⟨hω.1, le_of_lt hω.2⟩
  calc
    measureProb ν
        (fun ω =>
          theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score3 ω)
        ≤ measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
                theorem8GaussianDefinition2Score1 ω ∧
              theorem8GaussianDefinition2Score1 ω ≤
                theorem8GaussianDefinition2Score3 ω) := hle
    _ < measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
        measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω ≤
                theorem8GaussianDefinition2Score3 ω ∧
              theorem8GaussianDefinition2Score2 ω ≤
                theorem8GaussianDefinition2Score3 ω) := by
          simpa [ν] using hweak
    _ = measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
        measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω <
                theorem8GaussianDefinition2Score3 ω ∧
              theorem8GaussianDefinition2Score2 ω <
                theorem8GaussianDefinition2Score3 ω) := by
          rw [hboundary]

/--
Source space for the Laplace Definition-2 bridge, grouped as
`(score₁, (score₂, score₃))` so conditioning on `score₁` exposes the existing
two-score Laplace product theorem.
-/
abbrev Theorem7LaplacianDefinition2ScoreSpace :=
  Theorem8GaussianDefinition2ScoreSpace

/-- Independent Laplace source law for the Definition-2 bridge. -/
noncomputable def theorem7LaplacianDefinition2ScoreMeasure
    (lam x1 x2 x3 : ℝ) :
    Measure Theorem7LaplacianDefinition2ScoreSpace :=
  (theorem7LaplaceMeasure lam x1).prod
    (theorem7LaplacianPairMeasure lam x2 x3)

/-- First Laplace score coordinate. -/
def theorem7LaplacianDefinition2Score1
    (ω : Theorem7LaplacianDefinition2ScoreSpace) : ℝ := ω.1

/-- Second Laplace score coordinate. -/
def theorem7LaplacianDefinition2Score2
    (ω : Theorem7LaplacianDefinition2ScoreSpace) : ℝ := ω.2.1

/-- Third Laplace score coordinate. -/
def theorem7LaplacianDefinition2Score3
    (ω : Theorem7LaplacianDefinition2ScoreSpace) : ℝ := ω.2.2

theorem theorem7LaplacianDefinition2Score1_measurable :
    Measurable theorem7LaplacianDefinition2Score1 := measurable_fst

theorem theorem7LaplacianDefinition2Score2_measurable :
    Measurable theorem7LaplacianDefinition2Score2 := measurable_snd.fst

theorem theorem7LaplacianDefinition2Score3_measurable :
    Measurable theorem7LaplacianDefinition2Score3 := measurable_snd.snd

/-- The independent Laplace Definition-2 source law is a probability law when `0 < lam`. -/
theorem theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) :
    IsProbabilityMeasure
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3) := by
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam x1) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x1) hlam⟩
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam x2) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x2) hlam⟩
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam x3) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x3) hlam⟩
  dsimp [theorem7LaplacianDefinition2ScoreMeasure,
    theorem7LaplacianPairMeasure]
  infer_instance

/-- The first coordinate marginal of the Laplace Definition-2 source law. -/
theorem theorem7LaplacianDefinition2ScoreMeasure_score1_Iio_measureProb_eq
    {lam x1 x2 x3 m : ℝ} (hlam : 0 < lam) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω => theorem7LaplacianDefinition2Score1 ω < m) =
      measureProb (theorem7LaplaceMeasure lam x1) (fun z => z < m) := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ2 := theorem7LaplaceMeasure lam x2
  let μ3 := theorem7LaplaceMeasure lam x3
  haveI : SFinite μ1 := by
    dsimp [μ1, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ2 := by
    dsimp [μ2, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ3 := by
    dsimp [μ3, theorem7LaplaceMeasure]
    infer_instance
  haveI : IsProbabilityMeasure (μ2.prod μ3) := by
    haveI : IsProbabilityMeasure μ2 :=
      ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x2) hlam⟩
    haveI : IsProbabilityMeasure μ3 :=
      ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x3) hlam⟩
    infer_instance
  unfold measureProb
  change ((μ1.prod (μ2.prod μ3))
      {ω : Theorem7LaplacianDefinition2ScoreSpace | ω.1 < m}).toReal =
    (μ1 {z : ℝ | z < m}).toReal
  have hset :
      {ω : Theorem7LaplacianDefinition2ScoreSpace | ω.1 < m} =
        Set.Iio m ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
    ext ω
    simp [Set.mem_Iio]
  rw [hset, Measure.prod_prod]
  simpa [Set.Iio, μ1, μ2, μ3]

/-- The second coordinate lower-tail marginal of the Laplace Definition-2 source law. -/
theorem theorem7LaplacianDefinition2ScoreMeasure_score2_Iio_measureProb_eq
    {lam x1 x2 x3 m : ℝ} (hlam : 0 < lam) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω => theorem7LaplacianDefinition2Score2 ω < m) =
      measureProb (theorem7LaplaceMeasure lam x2) (fun z => z < m) := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ2 := theorem7LaplaceMeasure lam x2
  let μ3 := theorem7LaplaceMeasure lam x3
  haveI : SFinite μ1 := by
    dsimp [μ1, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ2 := by
    dsimp [μ2, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ3 := by
    dsimp [μ3, theorem7LaplaceMeasure]
    infer_instance
  haveI : IsProbabilityMeasure μ1 :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x1) hlam⟩
  haveI : IsProbabilityMeasure μ3 :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x3) hlam⟩
  unfold measureProb
  change ((μ1.prod (μ2.prod μ3))
      {ω : Theorem7LaplacianDefinition2ScoreSpace | ω.2.1 < m}).toReal =
    (μ2 {z : ℝ | z < m}).toReal
  have hset :
      {ω : Theorem7LaplacianDefinition2ScoreSpace | ω.2.1 < m} =
        (Set.univ : Set ℝ) ×ˢ (Set.Iio m ×ˢ (Set.univ : Set ℝ)) := by
    ext ω
    simp [Set.mem_Iio]
  rw [hset, Measure.prod_prod, Measure.prod_prod]
  simpa [Set.Iio, μ1, μ2, μ3]

/-- The second coordinate upper-tail marginal of the Laplace Definition-2 source law. -/
theorem theorem7LaplacianDefinition2ScoreMeasure_score2_Ioi_measureProb_eq
    {lam x1 x2 x3 m : ℝ} (hlam : 0 < lam) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω => m < theorem7LaplacianDefinition2Score2 ω) =
      measureProb (theorem7LaplaceMeasure lam x2) (fun z => m < z) := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ2 := theorem7LaplaceMeasure lam x2
  let μ3 := theorem7LaplaceMeasure lam x3
  haveI : SFinite μ1 := by
    dsimp [μ1, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ2 := by
    dsimp [μ2, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ3 := by
    dsimp [μ3, theorem7LaplaceMeasure]
    infer_instance
  haveI : IsProbabilityMeasure μ1 :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x1) hlam⟩
  haveI : IsProbabilityMeasure μ3 :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x3) hlam⟩
  unfold measureProb
  change ((μ1.prod (μ2.prod μ3))
      {ω : Theorem7LaplacianDefinition2ScoreSpace | m < ω.2.1}).toReal =
    (μ2 {z : ℝ | m < z}).toReal
  have hset :
      {ω : Theorem7LaplacianDefinition2ScoreSpace | m < ω.2.1} =
        (Set.univ : Set ℝ) ×ˢ (Set.Ioi m ×ˢ (Set.univ : Set ℝ)) := by
    ext ω
    simp [Set.mem_Ioi]
  rw [hset, Measure.prod_prod, Measure.prod_prod]
  simpa [Set.Ioi, μ1, μ2, μ3]

/-- The third coordinate upper-tail marginal of the Laplace Definition-2 source law. -/
theorem theorem7LaplacianDefinition2ScoreMeasure_score3_Ioi_measureProb_eq
    {lam x1 x2 x3 m : ℝ} (hlam : 0 < lam) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω => m < theorem7LaplacianDefinition2Score3 ω) =
      measureProb (theorem7LaplaceMeasure lam x3) (fun z => m < z) := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ2 := theorem7LaplaceMeasure lam x2
  let μ3 := theorem7LaplaceMeasure lam x3
  haveI : SFinite μ1 := by
    dsimp [μ1, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ2 := by
    dsimp [μ2, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ3 := by
    dsimp [μ3, theorem7LaplaceMeasure]
    infer_instance
  haveI : IsProbabilityMeasure μ1 :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x1) hlam⟩
  haveI : IsProbabilityMeasure μ2 :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x2) hlam⟩
  unfold measureProb
  change ((μ1.prod (μ2.prod μ3))
      {ω : Theorem7LaplacianDefinition2ScoreSpace | m < ω.2.2}).toReal =
    (μ3 {z : ℝ | m < z}).toReal
  have hset :
      {ω : Theorem7LaplacianDefinition2ScoreSpace | m < ω.2.2} =
        (Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ Set.Ioi m) := by
    ext ω
    simp [Set.mem_Ioi]
  rw [hset, Measure.prod_prod, Measure.prod_prod]
  simpa [Set.Ioi, μ1, μ2, μ3]

/--
When the first true score exceeds the second and `lam θ → ∞`, the Laplace
probability that the first realized score falls below the second vanishes.
-/
theorem theorem7LaplacianDefinition2ScoreMeasure_score12_inversion_tendsto_atTop_zero
    {lam : ℝ → ℝ} (hlam : Filter.Tendsto lam Filter.atTop Filter.atTop)
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) :
    Filter.Tendsto
      (fun θ : ℝ =>
        measureProb (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score1 ω <
              theorem7LaplacianDefinition2Score2 ω))
      Filter.atTop (nhds 0) := by
  let m : ℝ := (x1 + x2) / 2
  have hm_lt_x1 : m < x1 := by
    dsimp [m]
    linarith
  have hx2_lt_m : x2 < m := by
    dsimp [m]
    linarith
  have hpos_ev : ∀ᶠ θ : ℝ in Filter.atTop, 0 < lam θ :=
    hlam.eventually (Filter.eventually_gt_atTop (0 : ℝ))
  have htail1 :
      Filter.Tendsto
        (fun θ : ℝ =>
          measureProb
            (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
            (fun ω => theorem7LaplacianDefinition2Score1 ω < m))
        Filter.atTop (nhds 0) := by
    have hbase :=
      theorem7LaplaceMeasure_Iio_tendsto_atTop_zero
        (lam := lam) (μ := x1) (a := m) hlam hm_lt_x1
    refine hbase.congr' ?_
    filter_upwards [hpos_ev] with θ hθ
    exact (theorem7LaplacianDefinition2ScoreMeasure_score1_Iio_measureProb_eq
      (lam := lam θ) (x1 := x1) (x2 := x2) (x3 := x3) (m := m) hθ).symm
  have htail2 :
      Filter.Tendsto
        (fun θ : ℝ =>
          measureProb
            (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
            (fun ω => m < theorem7LaplacianDefinition2Score2 ω))
        Filter.atTop (nhds 0) := by
    have hbase :=
      theorem7LaplaceMeasure_Ioi_tendsto_atTop_zero
        (lam := lam) (μ := x2) (a := m) hlam hx2_lt_m
    refine hbase.congr' ?_
    filter_upwards [hpos_ev] with θ hθ
    exact (theorem7LaplacianDefinition2ScoreMeasure_score2_Ioi_measureProb_eq
      (lam := lam θ) (x1 := x1) (x2 := x2) (x3 := x3) (m := m) hθ).symm
  have hupper :
      Filter.Tendsto
        (fun θ : ℝ =>
          measureProb
            (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
            (fun ω => theorem7LaplacianDefinition2Score1 ω < m) +
          measureProb
            (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
            (fun ω => m < theorem7LaplacianDefinition2Score2 ω))
        Filter.atTop (nhds 0) := by
    simpa using htail1.add htail2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 0) from
      tendsto_const_nhds)
    hupper ?_ ?_
  · exact Filter.Eventually.of_forall fun θ => by
      unfold measureProb
      exact ENNReal.toReal_nonneg
  · filter_upwards [hpos_ev] with θ hθ
    haveI : IsProbabilityMeasure
        (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3) :=
      theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure
        (lam := lam θ) (x1 := x1) (x2 := x2) (x3 := x3) hθ
    exact
      measureProb_lt_le_midpoint_tails
        (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
        theorem7LaplacianDefinition2Score1
        theorem7LaplacianDefinition2Score2 m

/--
When the second true score exceeds the third and `lam θ → ∞`, the Laplace
probability that the second realized score falls below the third vanishes.
-/
theorem theorem7LaplacianDefinition2ScoreMeasure_score23_inversion_tendsto_atTop_zero
    {lam : ℝ → ℝ} (hlam : Filter.Tendsto lam Filter.atTop Filter.atTop)
    {x1 x2 x3 : ℝ} (hx23 : x3 < x2) :
    Filter.Tendsto
      (fun θ : ℝ =>
        measureProb (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω <
              theorem7LaplacianDefinition2Score3 ω))
      Filter.atTop (nhds 0) := by
  let m : ℝ := (x2 + x3) / 2
  have hm_lt_x2 : m < x2 := by
    dsimp [m]
    linarith
  have hx3_lt_m : x3 < m := by
    dsimp [m]
    linarith
  have hpos_ev : ∀ᶠ θ : ℝ in Filter.atTop, 0 < lam θ :=
    hlam.eventually (Filter.eventually_gt_atTop (0 : ℝ))
  have htail1 :
      Filter.Tendsto
        (fun θ : ℝ =>
          measureProb
            (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
            (fun ω => theorem7LaplacianDefinition2Score2 ω < m))
        Filter.atTop (nhds 0) := by
    have hbase :=
      theorem7LaplaceMeasure_Iio_tendsto_atTop_zero
        (lam := lam) (μ := x2) (a := m) hlam hm_lt_x2
    refine hbase.congr' ?_
    filter_upwards [hpos_ev] with θ hθ
    exact (theorem7LaplacianDefinition2ScoreMeasure_score2_Iio_measureProb_eq
      (lam := lam θ) (x1 := x1) (x2 := x2) (x3 := x3) (m := m) hθ).symm
  have htail2 :
      Filter.Tendsto
        (fun θ : ℝ =>
          measureProb
            (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
            (fun ω => m < theorem7LaplacianDefinition2Score3 ω))
        Filter.atTop (nhds 0) := by
    have hbase :=
      theorem7LaplaceMeasure_Ioi_tendsto_atTop_zero
        (lam := lam) (μ := x3) (a := m) hlam hx3_lt_m
    refine hbase.congr' ?_
    filter_upwards [hpos_ev] with θ hθ
    exact (theorem7LaplacianDefinition2ScoreMeasure_score3_Ioi_measureProb_eq
      (lam := lam θ) (x1 := x1) (x2 := x2) (x3 := x3) (m := m) hθ).symm
  have hupper :
      Filter.Tendsto
        (fun θ : ℝ =>
          measureProb
            (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
            (fun ω => theorem7LaplacianDefinition2Score2 ω < m) +
          measureProb
            (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
            (fun ω => m < theorem7LaplacianDefinition2Score3 ω))
        Filter.atTop (nhds 0) := by
    simpa using htail1.add htail2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 0) from
      tendsto_const_nhds)
    hupper ?_ ?_
  · exact Filter.Eventually.of_forall fun θ => by
      unfold measureProb
      exact ENNReal.toReal_nonneg
  · filter_upwards [hpos_ev] with θ hθ
    haveI : IsProbabilityMeasure
        (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3) :=
      theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure
        (lam := lam θ) (x1 := x1) (x2 := x2) (x3 := x3) hθ
    exact
      measureProb_lt_le_midpoint_tails
        (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
        theorem7LaplacianDefinition2Score2
        theorem7LaplacianDefinition2Score3 m

/-- The sum of the two adjacent Laplace inversion probabilities vanishes. -/
theorem theorem7LaplacianDefinition2ScoreMeasure_adjacent_inversions_tendsto_atTop_zero
    {lam : ℝ → ℝ} (hlam : Filter.Tendsto lam Filter.atTop Filter.atTop)
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Filter.Tendsto
      (fun θ : ℝ =>
        measureProb (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score1 ω <
              theorem7LaplacianDefinition2Score2 ω) +
        measureProb (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω <
              theorem7LaplacianDefinition2Score3 ω))
      Filter.atTop (nhds 0) := by
  simpa using
    (theorem7LaplacianDefinition2ScoreMeasure_score12_inversion_tendsto_atTop_zero
      (lam := lam) hlam (x1 := x1) (x2 := x2) (x3 := x3) hx12).add
    (theorem7LaplacianDefinition2ScoreMeasure_score23_inversion_tendsto_atTop_zero
      (lam := lam) hlam (x1 := x1) (x2 := x2) (x3 := x3) hx23)

/-- Swap the first two coordinates in the Definition-2 Laplace source space. -/
abbrev theorem7LaplacianDefinition2Swap12 :
    Theorem7LaplacianDefinition2ScoreSpace ≃ᵐ
      Theorem7LaplacianDefinition2ScoreSpace :=
  theorem8GaussianDefinition2Swap12

/-- Cycle coordinates `(score₁,score₂,score₃)` to `(score₃,score₁,score₂)`. -/
abbrev theorem7LaplacianDefinition2Cycle312 :
    Theorem7LaplacianDefinition2ScoreSpace ≃ᵐ
      Theorem7LaplacianDefinition2ScoreSpace :=
  theorem8GaussianDefinition2Cycle312

/--
The top/middle coordinate swap sends the independent Laplace score law with
locations `(x₁,x₂,x₃)` to the law with locations `(x₂,x₁,x₃)`.
-/
theorem theorem7LaplacianDefinition2Swap12_measurePreserving
    (lam x1 x2 x3 : ℝ) :
    MeasurePreserving theorem7LaplacianDefinition2Swap12
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
      (theorem7LaplacianDefinition2ScoreMeasure lam x2 x1 x3) := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ2 := theorem7LaplaceMeasure lam x2
  let μ3 := theorem7LaplaceMeasure lam x3
  haveI : SFinite μ1 := by
    dsimp [μ1, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ2 := by
    dsimp [μ2, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ3 := by
    dsimp [μ3, theorem7LaplaceMeasure]
    infer_instance
  have hassoc_symm : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        Theorem7LaplacianDefinition2ScoreSpace ≃ᵐ (ℝ × ℝ) × ℝ)
      (μ1.prod (μ2.prod μ3)) ((μ1.prod μ2).prod μ3) :=
    MeasurePreserving.symm
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ
        Theorem7LaplacianDefinition2ScoreSpace)
      (MeasureTheory.measurePreserving_prodAssoc μ1 μ2 μ3)
  have hpair : MeasurePreserving Prod.swap (μ1.prod μ2) (μ2.prod μ1) :=
    Measure.measurePreserving_swap
  have hmiddle : MeasurePreserving (Prod.map Prod.swap id)
      ((μ1.prod μ2).prod μ3) ((μ2.prod μ1).prod μ3) := by
    simpa using hpair.prod (MeasurePreserving.id μ3)
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ
        Theorem7LaplacianDefinition2ScoreSpace)
      ((μ2.prod μ1).prod μ3) (μ2.prod (μ1.prod μ3)) :=
    MeasureTheory.measurePreserving_prodAssoc μ2 μ1 μ3
  have hcomp := hassoc.comp (hmiddle.comp hassoc_symm)
  simpa [theorem7LaplacianDefinition2Swap12,
    theorem7LaplacianDefinition2ScoreMeasure, theorem7LaplacianPairMeasure,
    μ1, μ2, μ3] using hcomp

/--
The coordinate cycle sends the independent Laplace score law with locations
`(x₁,x₂,x₃)` to the law with locations `(x₃,x₁,x₂)`.
-/
theorem theorem7LaplacianDefinition2Cycle312_measurePreserving
    (lam x1 x2 x3 : ℝ) :
    MeasurePreserving theorem7LaplacianDefinition2Cycle312
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
      (theorem7LaplacianDefinition2ScoreMeasure lam x3 x1 x2) := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ2 := theorem7LaplaceMeasure lam x2
  let μ3 := theorem7LaplaceMeasure lam x3
  haveI : SFinite μ1 := by
    dsimp [μ1, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ2 := by
    dsimp [μ2, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ3 := by
    dsimp [μ3, theorem7LaplaceMeasure]
    infer_instance
  have hassoc_symm : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        Theorem7LaplacianDefinition2ScoreSpace ≃ᵐ (ℝ × ℝ) × ℝ)
      (μ1.prod (μ2.prod μ3)) ((μ1.prod μ2).prod μ3) :=
    MeasurePreserving.symm
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ
        Theorem7LaplacianDefinition2ScoreSpace)
      (MeasureTheory.measurePreserving_prodAssoc μ1 μ2 μ3)
  have hcomm : MeasurePreserving Prod.swap
      ((μ1.prod μ2).prod μ3) (μ3.prod (μ1.prod μ2)) :=
    Measure.measurePreserving_swap
  have hcomp := hcomm.comp hassoc_symm
  simpa [theorem7LaplacianDefinition2Cycle312,
    theorem7LaplacianDefinition2ScoreMeasure, theorem7LaplacianPairMeasure,
    μ1, μ2, μ3] using hcomp

/--
Laplace Definition-2 source inequality for the shared first-choice event
`score₁`.
-/
theorem theorem7LaplacianDefinition2_event0_score_inter_lt_mul
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) (hx23 : x3 < x2) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score2 ω ∧
            theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score1 ω) <
      measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score2 ω) *
        measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω ≤
                theorem7LaplacianDefinition2Score1 ω ∧
              theorem7LaplacianDefinition2Score3 ω ≤
                theorem7LaplacianDefinition2Score1 ω) := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ23 := theorem7LaplacianPairMeasure lam x2 x3
  let ν := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  haveI : IsProbabilityMeasure μ1 :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x1) hlam⟩
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam x2) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x2) hlam⟩
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam x3) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x3) hlam⟩
  haveI : IsProbabilityMeasure μ23 := by
    dsimp [μ23, theorem7LaplacianPairMeasure]
    infer_instance
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, theorem7LaplacianDefinition2ScoreMeasure, μ1, μ23,
      theorem7LaplacianPairMeasure]
    infer_instance
  let A : Set Theorem7LaplacianDefinition2ScoreSpace :=
    {ω |
      theorem7LaplacianDefinition2Score3 ω ≤
          theorem7LaplacianDefinition2Score2 ω ∧
        theorem7LaplacianDefinition2Score2 ω ≤
          theorem7LaplacianDefinition2Score1 ω}
  let B : Set Theorem7LaplacianDefinition2ScoreSpace :=
    {ω |
      theorem7LaplacianDefinition2Score2 ω ≤
          theorem7LaplacianDefinition2Score1 ω ∧
        theorem7LaplacianDefinition2Score3 ω ≤
          theorem7LaplacianDefinition2Score1 ω}
  let C : Set Theorem7LaplacianDefinition2ScoreSpace :=
    {ω |
      theorem7LaplacianDefinition2Score3 ω ≤
        theorem7LaplacianDefinition2Score2 ω}
  have hA_meas : MeasurableSet A := by
    dsimp [A, theorem7LaplacianDefinition2Score1,
      theorem7LaplacianDefinition2Score2, theorem7LaplacianDefinition2Score3]
    exact (measurableSet_le measurable_snd.snd measurable_snd.fst).inter
      (measurableSet_le measurable_snd.fst measurable_fst)
  have hB_meas : MeasurableSet B := by
    dsimp [B, theorem7LaplacianDefinition2Score1,
      theorem7LaplacianDefinition2Score2, theorem7LaplacianDefinition2Score3]
    exact (measurableSet_le measurable_snd.fst measurable_fst).inter
      (measurableSet_le measurable_snd.snd measurable_fst)
  have hC_meas : MeasurableSet C := by
    dsimp [C, theorem7LaplacianDefinition2Score2,
      theorem7LaplacianDefinition2Score3]
    exact measurableSet_le measurable_snd.snd measurable_snd.fst
  have hν_eq : ν = μ1.prod μ23 := by rfl
  let N : ℝ → ℝ := fun a =>
    (μ23 (theorem7LaplacianPairNumeratorEvent a)).toReal
  let D : ℝ → ℝ := fun a =>
    (μ23 (theorem7LaplacianPairDenominatorEvent a)).toReal
  let P : ℝ := (μ23 theorem7LaplacianPairWinnerEvent).toReal
  have hA_section :
      ∀ a,
        μ23 (Prod.mk a ⁻¹' A) =
          μ23 (theorem7LaplacianPairNumeratorEvent a) := by
    intro a
    apply congrArg μ23
    ext p
    simp [A, theorem7LaplacianPairNumeratorEvent,
      theorem7LaplacianDefinition2Score1,
      theorem7LaplacianDefinition2Score2,
      theorem7LaplacianDefinition2Score3, and_comm]
  have hB_section :
      ∀ a,
        μ23 (Prod.mk a ⁻¹' B) =
          μ23 (theorem7LaplacianPairDenominatorEvent a) := by
    intro a
    apply congrArg μ23
    ext p
    simp [B, theorem7LaplacianPairDenominatorEvent,
      theorem7LaplacianDefinition2Score1,
      theorem7LaplacianDefinition2Score2,
      theorem7LaplacianDefinition2Score3, Prod.le_def]
  have hN_int : Integrable N μ1 := by
    have hraw :
        Integrable (fun a => (μ23 (Prod.mk a ⁻¹' A)).toReal) μ1 := by
      refine integrable_toReal_of_lintegral_ne_top
        (measurable_measure_prodMk_left hA_meas).aemeasurable ?_
      rw [← Measure.prod_apply (μ := μ1) (ν := μ23) hA_meas]
      exact measure_ne_top (μ1.prod μ23) A
    convert hraw using 1
    ext a
    exact congrArg ENNReal.toReal (hA_section a).symm
  have hD_int : Integrable D μ1 := by
    have hraw :
        Integrable (fun a => (μ23 (Prod.mk a ⁻¹' B)).toReal) μ1 := by
      refine integrable_toReal_of_lintegral_ne_top
        (measurable_measure_prodMk_left hB_meas).aemeasurable ?_
      rw [← Measure.prod_apply (μ := μ1) (ν := μ23) hB_meas]
      exact measure_ne_top (μ1.prod μ23) B
    convert hraw using 1
  have hA_prob :
      measureProb ν (fun ω => ω ∈ A) = ∫ a, N a ∂μ1 := by
    unfold measureProb
    change (ν A).toReal = ∫ a, N a ∂μ1
    rw [hν_eq, Measure.prod_apply hA_meas]
    rw [← integral_toReal
      (measurable_measure_prodMk_left hA_meas).aemeasurable
      (ae_of_all μ1 fun a =>
        lt_top_iff_ne_top.2 (measure_ne_top μ23 (Prod.mk a ⁻¹' A)))]
    exact integral_congr_ae
      (ae_of_all μ1 fun a =>
        congrArg ENNReal.toReal (hA_section a))
  have hB_prob :
      measureProb ν (fun ω => ω ∈ B) = ∫ a, D a ∂μ1 := by
    unfold measureProb
    change (ν B).toReal = ∫ a, D a ∂μ1
    rw [hν_eq, Measure.prod_apply hB_meas]
    rw [← integral_toReal
      (measurable_measure_prodMk_left hB_meas).aemeasurable
      (ae_of_all μ1 fun a =>
        lt_top_iff_ne_top.2 (measure_ne_top μ23 (Prod.mk a ⁻¹' B)))]
    exact integral_congr_ae
      (ae_of_all μ1 fun a =>
        congrArg ENNReal.toReal (hB_section a))
  have hC_set :
      C = Set.univ ×ˢ theorem7LaplacianPairWinnerEvent := by
    ext ω
    simp [C, theorem7LaplacianPairWinnerEvent,
      theorem7LaplacianDefinition2Score2,
      theorem7LaplacianDefinition2Score3]
  have hC_prob :
      measureProb ν (fun ω => ω ∈ C) = P := by
    unfold measureProb
    change (ν C).toReal = P
    rw [hν_eq, hC_set, Measure.prod_prod]
    simp [P]
  have hfiber : ∀ a, N a < P * D a := by
    intro a
    dsimp [N, D, P, μ23]
    exact theorem7LaplacianPairNumerator_toReal_lt_winner_mul_denominator
      (lam := lam) (xi := x2) (xj := x3) (a := a) hlam hx23
  have hmain :
      measureProb ν (fun ω => ω ∈ A) <
        measureProb ν (fun ω => ω ∈ C) *
          measureProb ν (fun ω => ω ∈ B) :=
    measureProb_lt_mul_of_integral_fiber_lt
      μ1 ν (fun ω => ω ∈ A) (fun ω => ω ∈ B) (fun ω => ω ∈ C)
      hN_int hD_int hA_prob hB_prob hC_prob hfiber
  simpa [A, B, C, ν, theorem7LaplacianDefinition2ScoreMeasure] using hmain

/--
Laplace Definition-2 source boundary hygiene: making the middle score strictly
below the top score does not change the first-choice event probability.
-/
theorem theorem7LaplacianDefinition2_event0_first_weak_eq_leftStrict
    (lam x1 x2 x3 : ℝ) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score1 ω ∧
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score1 ω) =
      measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score2 ω <
              theorem7LaplacianDefinition2Score1 ω ∧
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score1 ω) := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ23 := theorem7LaplacianPairMeasure lam x2 x3
  let ν := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  haveI : SFinite (theorem7LaplaceMeasure lam x2) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  haveI : SFinite (theorem7LaplaceMeasure lam x3) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  haveI : SFinite μ23 := by
    dsimp [μ23, theorem7LaplacianPairMeasure]
    infer_instance
  have hν_eq : ν = μ1.prod μ23 := by rfl
  let W : Set Theorem7LaplacianDefinition2ScoreSpace :=
    {ω |
      theorem7LaplacianDefinition2Score2 ω ≤
          theorem7LaplacianDefinition2Score1 ω ∧
        theorem7LaplacianDefinition2Score3 ω ≤
          theorem7LaplacianDefinition2Score1 ω}
  let L : Set Theorem7LaplacianDefinition2ScoreSpace :=
    {ω |
      theorem7LaplacianDefinition2Score2 ω <
          theorem7LaplacianDefinition2Score1 ω ∧
        theorem7LaplacianDefinition2Score3 ω ≤
          theorem7LaplacianDefinition2Score1 ω}
  have hW_meas : MeasurableSet W := by
    dsimp [W, theorem7LaplacianDefinition2Score1,
      theorem7LaplacianDefinition2Score2, theorem7LaplacianDefinition2Score3]
    exact (measurableSet_le measurable_snd.fst measurable_fst).inter
      (measurableSet_le measurable_snd.snd measurable_fst)
  have hL_meas : MeasurableSet L := by
    dsimp [L, theorem7LaplacianDefinition2Score1,
      theorem7LaplacianDefinition2Score2, theorem7LaplacianDefinition2Score3]
    exact (measurableSet_lt measurable_snd.fst measurable_fst).inter
      (measurableSet_le measurable_snd.snd measurable_fst)
  have hW_section :
      ∀ a,
        μ23 (Prod.mk a ⁻¹' W) =
          μ23 (theorem7LaplacianPairDenominatorEvent a) := by
    intro a
    apply congrArg μ23
    ext p
    simp [W, theorem7LaplacianPairDenominatorEvent,
      theorem7LaplacianDefinition2Score1,
      theorem7LaplacianDefinition2Score2,
      theorem7LaplacianDefinition2Score3, Prod.le_def]
  have hL_section :
      ∀ a,
        μ23 (Prod.mk a ⁻¹' L) =
          μ23 (theorem7LaplacianPairLeftStrictDenominatorEvent a) := by
    intro a
    apply congrArg μ23
    ext p
    simp [L, theorem7LaplacianPairLeftStrictDenominatorEvent,
      theorem7LaplacianDefinition2Score1,
      theorem7LaplacianDefinition2Score2,
      theorem7LaplacianDefinition2Score3]
  unfold measureProb
  change (ν W).toReal = (ν L).toReal
  apply congrArg ENNReal.toReal
  rw [hν_eq, Measure.prod_apply hW_meas, Measure.prod_apply hL_meas]
  refine lintegral_congr fun a => ?_
  rw [hW_section a, hL_section a,
    theorem7LaplacianPairLeftStrictDenominator_measure_eq_denominator]

/--
Laplace Definition-2 source boundary hygiene: making both lower scores
strictly below the top score does not change the first-choice event
probability.
-/
theorem theorem7LaplacianDefinition2_event0_first_weak_eq_strict
    (lam x1 x2 x3 : ℝ) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score1 ω ∧
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score1 ω) =
      measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score2 ω <
              theorem7LaplacianDefinition2Score1 ω ∧
            theorem7LaplacianDefinition2Score3 ω <
              theorem7LaplacianDefinition2Score1 ω) := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ23 := theorem7LaplacianPairMeasure lam x2 x3
  let ν := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  haveI : SFinite (theorem7LaplaceMeasure lam x2) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  haveI : SFinite (theorem7LaplaceMeasure lam x3) := by
    unfold theorem7LaplaceMeasure
    infer_instance
  haveI : SFinite μ23 := by
    dsimp [μ23, theorem7LaplacianPairMeasure]
    infer_instance
  have hν_eq : ν = μ1.prod μ23 := by rfl
  let W : Set Theorem7LaplacianDefinition2ScoreSpace :=
    {ω |
      theorem7LaplacianDefinition2Score2 ω ≤
          theorem7LaplacianDefinition2Score1 ω ∧
        theorem7LaplacianDefinition2Score3 ω ≤
          theorem7LaplacianDefinition2Score1 ω}
  let S : Set Theorem7LaplacianDefinition2ScoreSpace :=
    {ω |
      theorem7LaplacianDefinition2Score2 ω <
          theorem7LaplacianDefinition2Score1 ω ∧
        theorem7LaplacianDefinition2Score3 ω <
          theorem7LaplacianDefinition2Score1 ω}
  have hW_meas : MeasurableSet W := by
    dsimp [W, theorem7LaplacianDefinition2Score1,
      theorem7LaplacianDefinition2Score2, theorem7LaplacianDefinition2Score3]
    exact (measurableSet_le measurable_snd.fst measurable_fst).inter
      (measurableSet_le measurable_snd.snd measurable_fst)
  have hS_meas : MeasurableSet S := by
    dsimp [S, theorem7LaplacianDefinition2Score1,
      theorem7LaplacianDefinition2Score2, theorem7LaplacianDefinition2Score3]
    exact (measurableSet_lt measurable_snd.fst measurable_fst).inter
      (measurableSet_lt measurable_snd.snd measurable_fst)
  have hW_section :
      ∀ a,
        μ23 (Prod.mk a ⁻¹' W) =
          μ23 (theorem7LaplacianPairDenominatorEvent a) := by
    intro a
    apply congrArg μ23
    ext p
    simp [W, theorem7LaplacianPairDenominatorEvent,
      theorem7LaplacianDefinition2Score1,
      theorem7LaplacianDefinition2Score2,
      theorem7LaplacianDefinition2Score3, Prod.le_def]
  have hS_section :
      ∀ a,
        μ23 (Prod.mk a ⁻¹' S) =
          μ23 (theorem7LaplacianPairStrictDenominatorEvent a) := by
    intro a
    apply congrArg μ23
    ext p
    simp [S, theorem7LaplacianPairStrictDenominatorEvent,
      theorem7LaplacianDefinition2Score1,
      theorem7LaplacianDefinition2Score2,
      theorem7LaplacianDefinition2Score3]
  unfold measureProb
  change (ν W).toReal = (ν S).toReal
  apply congrArg ENNReal.toReal
  rw [hν_eq, Measure.prod_apply hW_meas, Measure.prod_apply hS_meas]
  refine lintegral_congr fun a => ?_
  rw [hW_section a, hS_section a,
    theorem7LaplacianPairStrictDenominator_measure_eq_denominator]

/--
Laplace Definition-2 source inequality for the shared first-choice event
`score₂`, in weak-boundary form.
-/
theorem theorem7LaplacianDefinition2_event1_weak_score_inter_lt_mul
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) (hx13 : x3 < x1) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score1 ω ∧
            theorem7LaplacianDefinition2Score1 ω ≤
              theorem7LaplacianDefinition2Score2 ω) <
      measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score1 ω) *
        measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score1 ω ≤
                theorem7LaplacianDefinition2Score2 ω ∧
              theorem7LaplacianDefinition2Score3 ω ≤
                theorem7LaplacianDefinition2Score2 ω) := by
  let ν123 := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  let ν213 := theorem7LaplacianDefinition2ScoreMeasure lam x2 x1 x3
  let e := theorem7LaplacianDefinition2Swap12
  have he : MeasurePreserving e ν123 ν213 := by
    simpa [e, ν123, ν213] using
      theorem7LaplacianDefinition2Swap12_measurePreserving lam x1 x2 x3
  let A : Theorem7LaplacianDefinition2ScoreSpace → Prop := fun ω =>
    theorem7LaplacianDefinition2Score3 ω ≤
        theorem7LaplacianDefinition2Score2 ω ∧
      theorem7LaplacianDefinition2Score2 ω ≤
        theorem7LaplacianDefinition2Score1 ω
  let B : Theorem7LaplacianDefinition2ScoreSpace → Prop := fun ω =>
    theorem7LaplacianDefinition2Score2 ω ≤
        theorem7LaplacianDefinition2Score1 ω ∧
      theorem7LaplacianDefinition2Score3 ω ≤
        theorem7LaplacianDefinition2Score1 ω
  let C : Theorem7LaplacianDefinition2ScoreSpace → Prop := fun ω =>
    theorem7LaplacianDefinition2Score3 ω ≤
      theorem7LaplacianDefinition2Score2 ω
  have hbase :
      measureProb ν213 A < measureProb ν213 C * measureProb ν213 B := by
    simpa [ν213, A, B, C] using
      theorem7LaplacianDefinition2_event0_score_inter_lt_mul
        (lam := lam) (x1 := x2) (x2 := x1) (x3 := x3) hlam hx13
  have hA :
      measureProb ν123 (fun ω => A (e ω)) = measureProb ν213 A :=
    measureProb_preimage_equiv_of_measurePreserving e he A
  have hB :
      measureProb ν123 (fun ω => B (e ω)) = measureProb ν213 B :=
    measureProb_preimage_equiv_of_measurePreserving e he B
  have hC :
      measureProb ν123 (fun ω => C (e ω)) = measureProb ν213 C :=
    measureProb_preimage_equiv_of_measurePreserving e he C
  rw [← hA, ← hB, ← hC] at hbase
  simpa [ν123, e, A, B, C, theorem7LaplacianDefinition2ScoreMeasure] using hbase

/-- Boundary hygiene for the Laplace event1 first-choice source event. -/
theorem theorem7LaplacianDefinition2_event1_first_weak_eq_leftStrict
    (lam x1 x2 x3 : ℝ) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score1 ω ≤
              theorem7LaplacianDefinition2Score2 ω ∧
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score2 ω) =
      measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score1 ω <
              theorem7LaplacianDefinition2Score2 ω ∧
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score2 ω) := by
  let ν123 := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  let ν213 := theorem7LaplacianDefinition2ScoreMeasure lam x2 x1 x3
  let e := theorem7LaplacianDefinition2Swap12
  have he : MeasurePreserving e ν123 ν213 := by
    simpa [e, ν123, ν213] using
      theorem7LaplacianDefinition2Swap12_measurePreserving lam x1 x2 x3
  let W : Theorem7LaplacianDefinition2ScoreSpace → Prop := fun ω =>
    theorem7LaplacianDefinition2Score2 ω ≤
        theorem7LaplacianDefinition2Score1 ω ∧
      theorem7LaplacianDefinition2Score3 ω ≤
        theorem7LaplacianDefinition2Score1 ω
  let L : Theorem7LaplacianDefinition2ScoreSpace → Prop := fun ω =>
    theorem7LaplacianDefinition2Score2 ω <
        theorem7LaplacianDefinition2Score1 ω ∧
      theorem7LaplacianDefinition2Score3 ω ≤
        theorem7LaplacianDefinition2Score1 ω
  have hbase :
      measureProb ν213 W = measureProb ν213 L := by
    simpa [ν213, W, L] using
      theorem7LaplacianDefinition2_event0_first_weak_eq_leftStrict lam x2 x1 x3
  have hW :
      measureProb ν123 (fun ω => W (e ω)) = measureProb ν213 W :=
    measureProb_preimage_equiv_of_measurePreserving e he W
  have hL :
      measureProb ν123 (fun ω => L (e ω)) = measureProb ν213 L :=
    measureProb_preimage_equiv_of_measurePreserving e he L
  rw [← hW, ← hL] at hbase
  simpa [ν123, e, W, L, theorem7LaplacianDefinition2ScoreMeasure] using hbase

/--
Laplace Definition-2 source inequality for the shared first-choice event
`score₂`, in the strict form used by deterministic tie-breaking.
-/
theorem theorem7LaplacianDefinition2_event1_score_inter_lt_mul
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) (hx13 : x3 < x1) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score1 ω ∧
            theorem7LaplacianDefinition2Score1 ω <
              theorem7LaplacianDefinition2Score2 ω) <
      measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score1 ω) *
        measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score1 ω <
                theorem7LaplacianDefinition2Score2 ω ∧
              theorem7LaplacianDefinition2Score3 ω ≤
                theorem7LaplacianDefinition2Score2 ω) := by
  let ν := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam x1) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x1) hlam⟩
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam x2) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x2) hlam⟩
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam x3) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x3) hlam⟩
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, theorem7LaplacianDefinition2ScoreMeasure,
      theorem7LaplacianPairMeasure]
    infer_instance
  haveI : IsFiniteMeasure ν := by
    infer_instance
  have hweak :=
    theorem7LaplacianDefinition2_event1_weak_score_inter_lt_mul
      (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam hx13
  have hboundary :=
    theorem7LaplacianDefinition2_event1_first_weak_eq_leftStrict lam x1 x2 x3
  have hle :
      measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
                theorem7LaplacianDefinition2Score1 ω ∧
              theorem7LaplacianDefinition2Score1 ω <
                theorem7LaplacianDefinition2Score2 ω) ≤
        measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
                theorem7LaplacianDefinition2Score1 ω ∧
              theorem7LaplacianDefinition2Score1 ω ≤
                theorem7LaplacianDefinition2Score2 ω) := by
    refine measureProb_le_of_measure_le ν _ _ (measure_mono ?_)
    intro ω hω
    exact ⟨hω.1, le_of_lt hω.2⟩
  calc
    measureProb ν
        (fun ω =>
          theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score1 ω ∧
            theorem7LaplacianDefinition2Score1 ω <
              theorem7LaplacianDefinition2Score2 ω)
        ≤ measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
                theorem7LaplacianDefinition2Score1 ω ∧
              theorem7LaplacianDefinition2Score1 ω ≤
                theorem7LaplacianDefinition2Score2 ω) := hle
    _ < measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score1 ω) *
        measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score1 ω ≤
                theorem7LaplacianDefinition2Score2 ω ∧
              theorem7LaplacianDefinition2Score3 ω ≤
                theorem7LaplacianDefinition2Score2 ω) := by
          simpa [ν] using hweak
    _ = measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score1 ω) *
        measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score1 ω <
                theorem7LaplacianDefinition2Score2 ω ∧
              theorem7LaplacianDefinition2Score3 ω ≤
                theorem7LaplacianDefinition2Score2 ω) := by
          rw [hboundary]

/--
Laplace Definition-2 source inequality for the shared first-choice event
`score₃`, in weak-boundary form.
-/
theorem theorem7LaplacianDefinition2_event2_weak_score_inter_lt_mul
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) (hx12 : x2 < x1) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score1 ω ∧
            theorem7LaplacianDefinition2Score1 ω ≤
              theorem7LaplacianDefinition2Score3 ω) <
      measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score1 ω) *
        measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score1 ω ≤
                theorem7LaplacianDefinition2Score3 ω ∧
              theorem7LaplacianDefinition2Score2 ω ≤
                theorem7LaplacianDefinition2Score3 ω) := by
  let ν123 := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  let ν312 := theorem7LaplacianDefinition2ScoreMeasure lam x3 x1 x2
  let e := theorem7LaplacianDefinition2Cycle312
  have he : MeasurePreserving e ν123 ν312 := by
    simpa [e, ν123, ν312] using
      theorem7LaplacianDefinition2Cycle312_measurePreserving lam x1 x2 x3
  let A : Theorem7LaplacianDefinition2ScoreSpace → Prop := fun ω =>
    theorem7LaplacianDefinition2Score3 ω ≤
        theorem7LaplacianDefinition2Score2 ω ∧
      theorem7LaplacianDefinition2Score2 ω ≤
        theorem7LaplacianDefinition2Score1 ω
  let B : Theorem7LaplacianDefinition2ScoreSpace → Prop := fun ω =>
    theorem7LaplacianDefinition2Score2 ω ≤
        theorem7LaplacianDefinition2Score1 ω ∧
      theorem7LaplacianDefinition2Score3 ω ≤
        theorem7LaplacianDefinition2Score1 ω
  let C : Theorem7LaplacianDefinition2ScoreSpace → Prop := fun ω =>
    theorem7LaplacianDefinition2Score3 ω ≤
      theorem7LaplacianDefinition2Score2 ω
  have hbase :
      measureProb ν312 A < measureProb ν312 C * measureProb ν312 B := by
    simpa [ν312, A, B, C] using
      theorem7LaplacianDefinition2_event0_score_inter_lt_mul
        (lam := lam) (x1 := x3) (x2 := x1) (x3 := x2) hlam hx12
  have hA :
      measureProb ν123 (fun ω => A (e ω)) = measureProb ν312 A :=
    measureProb_preimage_equiv_of_measurePreserving e he A
  have hB :
      measureProb ν123 (fun ω => B (e ω)) = measureProb ν312 B :=
    measureProb_preimage_equiv_of_measurePreserving e he B
  have hC :
      measureProb ν123 (fun ω => C (e ω)) = measureProb ν312 C :=
    measureProb_preimage_equiv_of_measurePreserving e he C
  rw [← hA, ← hB, ← hC] at hbase
  simpa [ν123, e, A, B, C, theorem7LaplacianDefinition2ScoreMeasure] using hbase

/-- Boundary hygiene for the Laplace event2 first-choice source event. -/
theorem theorem7LaplacianDefinition2_event2_first_weak_eq_strict
    (lam x1 x2 x3 : ℝ) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score1 ω ≤
              theorem7LaplacianDefinition2Score3 ω ∧
            theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score3 ω) =
      measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score1 ω <
              theorem7LaplacianDefinition2Score3 ω ∧
            theorem7LaplacianDefinition2Score2 ω <
              theorem7LaplacianDefinition2Score3 ω) := by
  let ν123 := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  let ν312 := theorem7LaplacianDefinition2ScoreMeasure lam x3 x1 x2
  let e := theorem7LaplacianDefinition2Cycle312
  have he : MeasurePreserving e ν123 ν312 := by
    simpa [e, ν123, ν312] using
      theorem7LaplacianDefinition2Cycle312_measurePreserving lam x1 x2 x3
  let W : Theorem7LaplacianDefinition2ScoreSpace → Prop := fun ω =>
    theorem7LaplacianDefinition2Score2 ω ≤
        theorem7LaplacianDefinition2Score1 ω ∧
      theorem7LaplacianDefinition2Score3 ω ≤
        theorem7LaplacianDefinition2Score1 ω
  let S : Theorem7LaplacianDefinition2ScoreSpace → Prop := fun ω =>
    theorem7LaplacianDefinition2Score2 ω <
        theorem7LaplacianDefinition2Score1 ω ∧
      theorem7LaplacianDefinition2Score3 ω <
        theorem7LaplacianDefinition2Score1 ω
  have hbase :
      measureProb ν312 W = measureProb ν312 S := by
    simpa [ν312, W, S] using
      theorem7LaplacianDefinition2_event0_first_weak_eq_strict lam x3 x1 x2
  have hW :
      measureProb ν123 (fun ω => W (e ω)) = measureProb ν312 W :=
    measureProb_preimage_equiv_of_measurePreserving e he W
  have hS :
      measureProb ν123 (fun ω => S (e ω)) = measureProb ν312 S :=
    measureProb_preimage_equiv_of_measurePreserving e he S
  rw [← hW, ← hS] at hbase
  simpa [ν123, e, W, S, theorem7LaplacianDefinition2ScoreMeasure] using hbase

/--
Laplace Definition-2 source inequality for the shared first-choice event
`score₃`, in the strict form used by deterministic tie-breaking.
-/
theorem theorem7LaplacianDefinition2_event2_score_inter_lt_mul
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) (hx12 : x2 < x1) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score1 ω ∧
            theorem7LaplacianDefinition2Score1 ω <
              theorem7LaplacianDefinition2Score3 ω) <
      measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score1 ω) *
        measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score1 ω <
                theorem7LaplacianDefinition2Score3 ω ∧
              theorem7LaplacianDefinition2Score2 ω <
                theorem7LaplacianDefinition2Score3 ω) := by
  let ν := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam x1) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x1) hlam⟩
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam x2) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x2) hlam⟩
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam x3) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x3) hlam⟩
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, theorem7LaplacianDefinition2ScoreMeasure,
      theorem7LaplacianPairMeasure]
    infer_instance
  haveI : IsFiniteMeasure ν := by
    infer_instance
  have hweak :=
    theorem7LaplacianDefinition2_event2_weak_score_inter_lt_mul
      (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam hx12
  have hboundary :=
    theorem7LaplacianDefinition2_event2_first_weak_eq_strict lam x1 x2 x3
  have hle :
      measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω ≤
                theorem7LaplacianDefinition2Score1 ω ∧
              theorem7LaplacianDefinition2Score1 ω <
                theorem7LaplacianDefinition2Score3 ω) ≤
        measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω ≤
                theorem7LaplacianDefinition2Score1 ω ∧
              theorem7LaplacianDefinition2Score1 ω ≤
                theorem7LaplacianDefinition2Score3 ω) := by
    refine measureProb_le_of_measure_le ν _ _ (measure_mono ?_)
    intro ω hω
    exact ⟨hω.1, le_of_lt hω.2⟩
  calc
    measureProb ν
        (fun ω =>
          theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score1 ω ∧
            theorem7LaplacianDefinition2Score1 ω <
              theorem7LaplacianDefinition2Score3 ω)
        ≤ measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω ≤
                theorem7LaplacianDefinition2Score1 ω ∧
              theorem7LaplacianDefinition2Score1 ω ≤
                theorem7LaplacianDefinition2Score3 ω) := hle
    _ < measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score1 ω) *
        measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score1 ω ≤
                theorem7LaplacianDefinition2Score3 ω ∧
              theorem7LaplacianDefinition2Score2 ω ≤
                theorem7LaplacianDefinition2Score3 ω) := by
          simpa [ν] using hweak
    _ = measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score1 ω) *
        measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score1 ω <
                theorem7LaplacianDefinition2Score3 ω ∧
              theorem7LaplacianDefinition2Score2 ω <
                theorem7LaplacianDefinition2Score3 ω) := by
          rw [hboundary]

/--
Appendix C, Theorem 8: encode an arbitrary Gaussian standard deviation as the
variance parameter used by Mathlib's `gaussianReal`.
-/
def theorem8GaussianVarianceFromStd (σ : ℝ) : ℝ≥0 := AppliedModelingLib.Probability.gaussianVarianceFromStd σ

theorem theorem8GaussianVarianceFromStd_mul_left (t σ : ℝ) :
    NNReal.mk (t ^ 2) (sq_nonneg t) * theorem8GaussianVarianceFromStd σ =
      theorem8GaussianVarianceFromStd (t * σ) := by
  ext
  simp [theorem8GaussianVarianceFromStd,
    AppliedModelingLib.Probability.gaussianVarianceFromStd]
  ring

theorem theorem8GaussianVarianceFromStd_ne_zero {σ : ℝ} (hσ : σ ≠ 0) :
    theorem8GaussianVarianceFromStd σ ≠ 0 := by
  intro hzero
  have hcoe : ((theorem8GaussianVarianceFromStd σ : ℝ≥0) : ℝ) = 0 := by
    rw [hzero]
    rfl
  have hsq : σ ^ 2 = 0 := by
    simpa [theorem8GaussianVarianceFromStd,
      AppliedModelingLib.Probability.gaussianVarianceFromStd] using hcoe
  exact hσ (sq_eq_zero_iff.mp hsq)

/--
Appendix C, Theorem 8: the positive scale that sends standard deviation `σ` to
the paper's canonical standard deviation `1 / sqrt 2`.
-/
noncomputable def theorem8GaussianCanonicalScale (σ : ℝ) : ℝ := AppliedModelingLib.Probability.canonicalHalfVarianceScale σ

/-- Appendix C, Theorem 8: the canonical Gaussian scale is positive. -/
theorem theorem8GaussianCanonicalScale_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < theorem8GaussianCanonicalScale σ :=  AppliedModelingLib.Probability.canonicalHalfVarianceScale_pos hσ

/-- Appendix C, Theorem 8: the canonical Gaussian scale is nonzero. -/
theorem theorem8GaussianCanonicalScale_ne_zero {σ : ℝ} (hσ : 0 < σ) :
    theorem8GaussianCanonicalScale σ ≠ 0 := ne_of_gt (theorem8GaussianCanonicalScale_pos hσ)

/--
Appendix C, Theorem 8: as the accuracy parameter `θ` tends to infinity, the
canonical scale for standard deviation `1 / θ` tends to infinity.
-/
theorem theorem8GaussianCanonicalScale_one_div_tendsto_atTop :
    Filter.Tendsto (fun θ : ℝ => theorem8GaussianCanonicalScale (1 / θ))
      Filter.atTop Filter.atTop := by
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt_pos
  have hlinear :
      Filter.Tendsto (fun θ : ℝ => (1 / Real.sqrt 2) * θ)
        Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos
      (one_div_pos.mpr hsqrt_pos)).2 Filter.tendsto_id
  refine hlinear.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with θ hθ
  unfold theorem8GaussianCanonicalScale
  simp [AppliedModelingLib.Probability.canonicalHalfVarianceScale,
    one_div]
  ring

/--
Appendix C, Theorem 8: multiplying a variance-`σ^2` Gaussian by the canonical
scale gives variance `1/2`.
-/
theorem theorem8GaussianCanonicalScale_sq_mul_variance
    {σ : ℝ} (hσ : 0 < σ) :
    NNReal.mk ((theorem8GaussianCanonicalScale σ) ^ 2)
        (sq_nonneg (theorem8GaussianCanonicalScale σ)) *
      theorem8GaussianVarianceFromStd σ =
        (1 / 2 : ℝ≥0) := by
  simpa [theorem8GaussianCanonicalScale, theorem8GaussianVarianceFromStd] using
    AppliedModelingLib.Probability.canonicalHalfVarianceScale_sq_mul_gaussianVarianceFromStd hσ

/--
Appendix C, Theorem 8: Mathlib's one-dimensional Gaussian scaling theorem,
specialized to the paper's `σ` to `1 / sqrt 2` normalization.
-/
theorem theorem8GaussianReal_map_canonicalScale
    {σ μ : ℝ} (hσ : 0 < σ) :
    (ProbabilityTheory.gaussianReal μ
        (theorem8GaussianVarianceFromStd σ)).map
        (fun x => theorem8GaussianCanonicalScale σ * x) =
      ProbabilityTheory.gaussianReal
        (theorem8GaussianCanonicalScale σ * μ) (1 / 2 : ℝ≥0) := by
  simpa [theorem8GaussianCanonicalScale, theorem8GaussianVarianceFromStd] using
    AppliedModelingLib.Probability.gaussianReal_map_canonicalHalfVarianceScale
      (σ := σ) (μ := μ) hσ

/--
For Gaussian standard deviation `1 / θ`, the lower-tail event probability is
the canonical variance-`1/2` CDF at the scaled threshold gap.
-/
theorem theorem8GaussianRealStd_Iio_measureProb_eq_CDF
    {θ x m : ℝ} (hθ : 0 < θ) :
    measureProb
        (ProbabilityTheory.gaussianReal x
          (theorem8GaussianVarianceFromStd (1 / θ)))
        (fun z => z < m) =
      theorem8GaussianCDF 0
        (theorem8GaussianCanonicalScale (1 / θ) * (m - x)) := by
  let σ := 1 / θ
  let c := theorem8GaussianCanonicalScale σ
  let μstd := ProbabilityTheory.gaussianReal x
    (theorem8GaussianVarianceFromStd σ)
  let μcan := ProbabilityTheory.gaussianReal (c * x) (1 / 2 : ℝ≥0)
  have hσ : 0 < σ := by
    dsimp [σ]
    exact one_div_pos.mpr hθ
  have hc : 0 < c := theorem8GaussianCanonicalScale_pos hσ
  have hmap : μstd.map (fun z : ℝ => c * z) = μcan := by
    simpa [μstd, μcan, c, σ] using
      theorem8GaussianReal_map_canonicalScale (σ := σ) (μ := x) hσ
  have hpre : (fun z : ℝ => c * z) ⁻¹' Set.Iio (c * m) = Set.Iio m := by
    ext z
    simpa [Set.mem_Iio] using
      (mul_lt_mul_iff_right₀ hc : c * z < c * m ↔ z < m)
  have hmass : μstd (Set.Iio m) = μcan (Set.Iio (c * m)) := by
    have hmeas : Measurable (fun z : ℝ => c * z) := by fun_prop
    have h := congrArg (fun μ : Measure ℝ => μ (Set.Iio (c * m))) hmap
    change (Measure.map (fun z : ℝ => c * z) μstd) (Set.Iio (c * m)) =
      μcan (Set.Iio (c * m)) at h
    rw [Measure.map_apply hmeas measurableSet_Iio, hpre] at h
    exact h
  unfold measureProb
  change (μstd (Set.Iio m)).toReal =
    theorem8GaussianCDF 0 (c * (m - x))
  rw [hmass, theorem8GaussianReal_Iio_eq_Iic (μ := c * x) (a := c * m),
    theorem8GaussianReal_Iic_eq_CDF (μ := c * x) (a := c * m),
    ENNReal.toReal_ofReal (theorem8GaussianCDF_nonneg (c * x) (c * m))]
  dsimp [c, σ]
  unfold theorem8GaussianCDF
  ring_nf

/--
For Gaussian standard deviation `1 / θ`, the upper-tail event probability is
one minus the canonical variance-`1/2` CDF at the scaled threshold gap.
-/
theorem theorem8GaussianRealStd_Ioi_measureProb_eq_one_sub_CDF
    {θ x m : ℝ} (hθ : 0 < θ) :
    measureProb
        (ProbabilityTheory.gaussianReal x
          (theorem8GaussianVarianceFromStd (1 / θ)))
        (fun z => m < z) =
      1 -
        theorem8GaussianCDF 0
          (theorem8GaussianCanonicalScale (1 / θ) * (m - x)) := by
  let σ := 1 / θ
  let c := theorem8GaussianCanonicalScale σ
  let μstd := ProbabilityTheory.gaussianReal x
    (theorem8GaussianVarianceFromStd σ)
  let μcan := ProbabilityTheory.gaussianReal (c * x) (1 / 2 : ℝ≥0)
  have hσ : 0 < σ := by
    dsimp [σ]
    exact one_div_pos.mpr hθ
  haveI : IsProbabilityMeasure μstd := by
    dsimp [μstd]
    infer_instance
  have hc : 0 < c := theorem8GaussianCanonicalScale_pos hσ
  have hmap : μstd.map (fun z : ℝ => c * z) = μcan := by
    simpa [μstd, μcan, c, σ] using
      theorem8GaussianReal_map_canonicalScale (σ := σ) (μ := x) hσ
  have hpre : (fun z : ℝ => c * z) ⁻¹' Set.Iic (c * m) = Set.Iic m := by
    ext z
    simpa [Set.mem_Iic] using
      (mul_le_mul_iff_right₀ hc : c * z ≤ c * m ↔ z ≤ m)
  have hmass : μstd (Set.Iic m) = μcan (Set.Iic (c * m)) := by
    have hmeas : Measurable (fun z : ℝ => c * z) := by fun_prop
    have h := congrArg (fun μ : Measure ℝ => μ (Set.Iic (c * m))) hmap
    change (Measure.map (fun z : ℝ => c * z) μstd) (Set.Iic (c * m)) =
      μcan (Set.Iic (c * m)) at h
    rw [Measure.map_apply hmeas measurableSet_Iic, hpre] at h
    exact h
  have htail :
      measureProb μstd (fun z => m < z) =
        1 - (μstd (Set.Iic m)).toReal := by
    unfold measureProb
    change (μstd (Set.Ioi m)).toReal =
      1 - (μstd (Set.Iic m)).toReal
    have hcompl :=
      probReal_compl_eq_one_sub (μ := μstd) (s := Set.Iic m)
        measurableSet_Iic
    simpa [Measure.real, Set.compl_Iic] using hcompl
  rw [htail, hmass, theorem8GaussianReal_Iic_eq_CDF (μ := c * x) (a := c * m),
    ENNReal.toReal_ofReal (theorem8GaussianCDF_nonneg (c * x) (c * m))]
  dsimp [c, σ]
  unfold theorem8GaussianCDF
  ring_nf

/--
If the cutoff is strictly below the Gaussian mean, the lower tail under
standard deviation `1 / θ` vanishes as `θ → ∞`.
-/
theorem theorem8GaussianRealStd_Iio_tendsto_atTop_zero
    {x m : ℝ} (hmx : m < x) :
    Filter.Tendsto
      (fun θ : ℝ =>
        measureProb
          (ProbabilityTheory.gaussianReal x
            (theorem8GaussianVarianceFromStd (1 / θ)))
          (fun z => z < m))
      Filter.atTop (nhds 0) := by
  have hgap : m - x < 0 := by linarith
  have harg :
      Filter.Tendsto
        (fun θ : ℝ =>
          theorem8GaussianCanonicalScale (1 / θ) * (m - x))
        Filter.atTop Filter.atBot :=
    theorem8GaussianCanonicalScale_one_div_tendsto_atTop
      |>.atTop_mul_const_of_neg hgap
  have hcdf :
      Filter.Tendsto
        (fun θ : ℝ =>
          theorem8GaussianCDF 0
            (theorem8GaussianCanonicalScale (1 / θ) * (m - x)))
        Filter.atTop (nhds 0) :=
    (theorem8GaussianCDF_tendsto_atBot_zero 0).comp harg
  refine hcdf.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with θ hθ
  exact (theorem8GaussianRealStd_Iio_measureProb_eq_CDF
    (θ := θ) (x := x) (m := m) hθ
    ).symm

/--
If the cutoff is strictly above the Gaussian mean, the upper tail under
standard deviation `1 / θ` vanishes as `θ → ∞`.
-/
theorem theorem8GaussianRealStd_Ioi_tendsto_atTop_zero
    {x m : ℝ} (hxm : x < m) :
    Filter.Tendsto
      (fun θ : ℝ =>
        measureProb
          (ProbabilityTheory.gaussianReal x
            (theorem8GaussianVarianceFromStd (1 / θ)))
          (fun z => m < z))
      Filter.atTop (nhds 0) := by
  have hgap : 0 < m - x := by linarith
  have harg :
      Filter.Tendsto
        (fun θ : ℝ =>
          theorem8GaussianCanonicalScale (1 / θ) * (m - x))
        Filter.atTop Filter.atTop :=
    theorem8GaussianCanonicalScale_one_div_tendsto_atTop
      |>.atTop_mul_const hgap
  have hcdf :
      Filter.Tendsto
        (fun θ : ℝ =>
          theorem8GaussianCDF 0
            (theorem8GaussianCanonicalScale (1 / θ) * (m - x)))
        Filter.atTop (nhds 1) :=
    (theorem8GaussianCDF_tendsto_atTop_one 0).comp harg
  have htail :
      Filter.Tendsto
        (fun θ : ℝ =>
          1 -
            theorem8GaussianCDF 0
              (theorem8GaussianCanonicalScale (1 / θ) * (m - x)))
        Filter.atTop (nhds 0) := by
    have hone :
        Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
          Filter.atTop (nhds (1 : ℝ)) :=
      tendsto_const_nhds
    simpa using hone.sub hcdf
  refine htail.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with θ hθ
  exact (theorem8GaussianRealStd_Ioi_measureProb_eq_one_sub_CDF
    (θ := θ) (x := x) (m := m) hθ
    ).symm

/--
Appendix C, Theorem 8: product measure for independent Gaussians with arbitrary
positive standard deviation `σ`.
-/
noncomputable def theorem8GaussianPairMeasureStd
    (σ xi xj : ℝ) : Measure (ℝ × ℝ) := AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd σ xi xj

/--
Appendix C, Theorem 8: scale both coordinates of the Gaussian product space.
-/
noncomputable def theorem8GaussianPairCanonicalScaleMap
    (σ : ℝ) : ℝ × ℝ → ℝ × ℝ := AppliedModelingLib.Probability.pairCanonicalHalfVarianceScaleMap σ

theorem theorem8GaussianPairCanonicalScaleMap_measurable
    (σ : ℝ) :
    Measurable (theorem8GaussianPairCanonicalScaleMap σ) := by
  unfold theorem8GaussianPairCanonicalScaleMap
    AppliedModelingLib.Probability.pairCanonicalHalfVarianceScaleMap
  fun_prop

/--
Appendix C, Theorem 8: the arbitrary-`σ` product measure maps to the canonical
variance-`1/2` product measure.
-/
theorem theorem8GaussianPairMeasureStd_map_canonicalScale
    {σ xi xj : ℝ} (hσ : 0 < σ) :
    (theorem8GaussianPairMeasureStd σ xi xj).map
        (theorem8GaussianPairCanonicalScaleMap σ) =
      theorem8GaussianPairMeasure
        (theorem8GaussianCanonicalScale σ * xi)
        (theorem8GaussianCanonicalScale σ * xj) := by
  simpa [theorem8GaussianPairMeasureStd, theorem8GaussianPairCanonicalScaleMap,
    theorem8GaussianPairMeasure, theorem8GaussianCanonicalScale,
    theorem8GaussianVarianceFromStd,
    AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd,
    AppliedModelingLib.Probability.pairCanonicalHalfVarianceScaleMap,
    AppliedModelingLib.Probability.independentGaussianPairMeasureHalf] using
      AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd_map_canonicalHalfVarianceScale
        (σ := σ) (xi := xi) (xj := xj) hσ

/-- Independent three-score Gaussian source law with arbitrary standard deviation. -/
noncomputable def theorem8GaussianDefinition2ScoreMeasureStd
    (σ x1 x2 x3 : ℝ) : Measure Theorem8GaussianDefinition2ScoreSpace :=
  (ProbabilityTheory.gaussianReal x1 (theorem8GaussianVarianceFromStd σ)).prod
    (theorem8GaussianPairMeasureStd σ x2 x3)

instance theorem8GaussianDefinition2ScoreMeasureStd_isProbabilityMeasure
    (σ x1 x2 x3 : ℝ) :
    IsProbabilityMeasure
      (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3) := by
  dsimp [theorem8GaussianDefinition2ScoreMeasureStd,
    theorem8GaussianPairMeasureStd,
    AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd,
    theorem8GaussianVarianceFromStd,
    AppliedModelingLib.Probability.gaussianVarianceFromStd]
  infer_instance

/-- The first coordinate marginal of the arbitrary-variance Gaussian source law. -/
theorem theorem8GaussianDefinition2ScoreMeasureStd_score1_Iio_measureProb_eq
    (σ x1 x2 x3 m : ℝ) :
    measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (fun ω => theorem8GaussianDefinition2Score1 ω < m) =
      measureProb
        (ProbabilityTheory.gaussianReal x1
          (theorem8GaussianVarianceFromStd σ))
        (fun z => z < m) := by
  let μ1 := ProbabilityTheory.gaussianReal x1
    (theorem8GaussianVarianceFromStd σ)
  let μ2 := ProbabilityTheory.gaussianReal x2
    (theorem8GaussianVarianceFromStd σ)
  let μ3 := ProbabilityTheory.gaussianReal x3
    (theorem8GaussianVarianceFromStd σ)
  haveI : IsProbabilityMeasure (μ2.prod μ3) := by infer_instance
  unfold measureProb
  change ((μ1.prod (μ2.prod μ3))
      {ω : Theorem8GaussianDefinition2ScoreSpace | ω.1 < m}).toReal =
    (μ1 {z : ℝ | z < m}).toReal
  have hset :
      {ω : Theorem8GaussianDefinition2ScoreSpace | ω.1 < m} =
        Set.Iio m ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
    ext ω
    simp [Set.mem_Iio]
  rw [hset, Measure.prod_prod]
  simpa [Set.Iio, μ1, μ2, μ3]

/-- The second coordinate lower-tail marginal of the arbitrary-variance Gaussian source law. -/
theorem theorem8GaussianDefinition2ScoreMeasureStd_score2_Iio_measureProb_eq
    (σ x1 x2 x3 m : ℝ) :
    measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (fun ω => theorem8GaussianDefinition2Score2 ω < m) =
      measureProb
        (ProbabilityTheory.gaussianReal x2
          (theorem8GaussianVarianceFromStd σ))
        (fun z => z < m) := by
  let μ1 := ProbabilityTheory.gaussianReal x1
    (theorem8GaussianVarianceFromStd σ)
  let μ2 := ProbabilityTheory.gaussianReal x2
    (theorem8GaussianVarianceFromStd σ)
  let μ3 := ProbabilityTheory.gaussianReal x3
    (theorem8GaussianVarianceFromStd σ)
  haveI : IsProbabilityMeasure μ1 := by infer_instance
  haveI : IsProbabilityMeasure μ3 := by infer_instance
  unfold measureProb
  change ((μ1.prod (μ2.prod μ3))
      {ω : Theorem8GaussianDefinition2ScoreSpace | ω.2.1 < m}).toReal =
    (μ2 {z : ℝ | z < m}).toReal
  have hset :
      {ω : Theorem8GaussianDefinition2ScoreSpace | ω.2.1 < m} =
        (Set.univ : Set ℝ) ×ˢ (Set.Iio m ×ˢ (Set.univ : Set ℝ)) := by
    ext ω
    simp [Set.mem_Iio]
  rw [hset, Measure.prod_prod, Measure.prod_prod]
  simpa [Set.Iio, μ1, μ2, μ3]

/-- The second coordinate upper-tail marginal of the arbitrary-variance Gaussian source law. -/
theorem theorem8GaussianDefinition2ScoreMeasureStd_score2_Ioi_measureProb_eq
    (σ x1 x2 x3 m : ℝ) :
    measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (fun ω => m < theorem8GaussianDefinition2Score2 ω) =
      measureProb
        (ProbabilityTheory.gaussianReal x2
          (theorem8GaussianVarianceFromStd σ))
        (fun z => m < z) := by
  let μ1 := ProbabilityTheory.gaussianReal x1
    (theorem8GaussianVarianceFromStd σ)
  let μ2 := ProbabilityTheory.gaussianReal x2
    (theorem8GaussianVarianceFromStd σ)
  let μ3 := ProbabilityTheory.gaussianReal x3
    (theorem8GaussianVarianceFromStd σ)
  haveI : IsProbabilityMeasure μ1 := by infer_instance
  haveI : IsProbabilityMeasure μ3 := by infer_instance
  unfold measureProb
  change ((μ1.prod (μ2.prod μ3))
      {ω : Theorem8GaussianDefinition2ScoreSpace | m < ω.2.1}).toReal =
    (μ2 {z : ℝ | m < z}).toReal
  have hset :
      {ω : Theorem8GaussianDefinition2ScoreSpace | m < ω.2.1} =
        (Set.univ : Set ℝ) ×ˢ (Set.Ioi m ×ˢ (Set.univ : Set ℝ)) := by
    ext ω
    simp [Set.mem_Ioi]
  rw [hset, Measure.prod_prod, Measure.prod_prod]
  simpa [Set.Ioi, μ1, μ2, μ3]

/-- The third coordinate upper-tail marginal of the arbitrary-variance Gaussian source law. -/
theorem theorem8GaussianDefinition2ScoreMeasureStd_score3_Ioi_measureProb_eq
    (σ x1 x2 x3 m : ℝ) :
    measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (fun ω => m < theorem8GaussianDefinition2Score3 ω) =
      measureProb
        (ProbabilityTheory.gaussianReal x3
          (theorem8GaussianVarianceFromStd σ))
        (fun z => m < z) := by
  let μ1 := ProbabilityTheory.gaussianReal x1
    (theorem8GaussianVarianceFromStd σ)
  let μ2 := ProbabilityTheory.gaussianReal x2
    (theorem8GaussianVarianceFromStd σ)
  let μ3 := ProbabilityTheory.gaussianReal x3
    (theorem8GaussianVarianceFromStd σ)
  haveI : IsProbabilityMeasure μ1 := by infer_instance
  haveI : IsProbabilityMeasure μ2 := by infer_instance
  unfold measureProb
  change ((μ1.prod (μ2.prod μ3))
      {ω : Theorem8GaussianDefinition2ScoreSpace | m < ω.2.2}).toReal =
    (μ3 {z : ℝ | m < z}).toReal
  have hset :
      {ω : Theorem8GaussianDefinition2ScoreSpace | m < ω.2.2} =
        (Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ Set.Ioi m) := by
    ext ω
    simp [Set.mem_Ioi]
  rw [hset, Measure.prod_prod, Measure.prod_prod]
  simpa [Set.Ioi, μ1, μ2, μ3]

/--
When the first true score exceeds the second, the Gaussian probability that the
first realized score falls below the second vanishes as `θ → ∞`.
-/
theorem theorem8GaussianDefinition2ScoreMeasureStd_score12_inversion_tendsto_atTop_zero
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) :
    Filter.Tendsto
      (fun θ : ℝ =>
        measureProb
          (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score2 ω))
      Filter.atTop (nhds 0) := by
  let m : ℝ := (x1 + x2) / 2
  have hm_lt_x1 : m < x1 := by
    dsimp [m]
    linarith
  have hx2_lt_m : x2 < m := by
    dsimp [m]
    linarith
  have htail1 :
      Filter.Tendsto
        (fun θ : ℝ =>
          measureProb
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (fun ω => theorem8GaussianDefinition2Score1 ω < m))
        Filter.atTop (nhds 0) := by
    have hbase :=
      theorem8GaussianRealStd_Iio_tendsto_atTop_zero
        (x := x1) (m := m) hm_lt_x1
    refine hbase.congr' ?_
    filter_upwards with θ
    exact (theorem8GaussianDefinition2ScoreMeasureStd_score1_Iio_measureProb_eq
      (σ := 1 / θ) (x1 := x1) (x2 := x2) (x3 := x3) (m := m)).symm
  have htail2 :
      Filter.Tendsto
        (fun θ : ℝ =>
          measureProb
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (fun ω => m < theorem8GaussianDefinition2Score2 ω))
        Filter.atTop (nhds 0) := by
    have hbase :=
      theorem8GaussianRealStd_Ioi_tendsto_atTop_zero
        (x := x2) (m := m) hx2_lt_m
    refine hbase.congr' ?_
    filter_upwards with θ
    exact (theorem8GaussianDefinition2ScoreMeasureStd_score2_Ioi_measureProb_eq
      (σ := 1 / θ) (x1 := x1) (x2 := x2) (x3 := x3) (m := m)).symm
  have hupper :
      Filter.Tendsto
        (fun θ : ℝ =>
          measureProb
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (fun ω => theorem8GaussianDefinition2Score1 ω < m) +
          measureProb
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (fun ω => m < theorem8GaussianDefinition2Score2 ω))
        Filter.atTop (nhds 0) := by
    simpa using htail1.add htail2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 0) from
      tendsto_const_nhds)
    hupper ?_ ?_
  · exact Filter.Eventually.of_forall fun θ => by
      unfold measureProb
      exact ENNReal.toReal_nonneg
  · exact Filter.Eventually.of_forall fun θ =>
      measureProb_lt_le_midpoint_tails
        (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
        theorem8GaussianDefinition2Score1
        theorem8GaussianDefinition2Score2 m

/--
When the second true score exceeds the third, the Gaussian probability that the
second realized score falls below the third vanishes as `θ → ∞`.
-/
theorem theorem8GaussianDefinition2ScoreMeasureStd_score23_inversion_tendsto_atTop_zero
    {x1 x2 x3 : ℝ} (hx23 : x3 < x2) :
    Filter.Tendsto
      (fun θ : ℝ =>
        measureProb
          (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω <
              theorem8GaussianDefinition2Score3 ω))
      Filter.atTop (nhds 0) := by
  let m : ℝ := (x2 + x3) / 2
  have hm_lt_x2 : m < x2 := by
    dsimp [m]
    linarith
  have hx3_lt_m : x3 < m := by
    dsimp [m]
    linarith
  have htail1 :
      Filter.Tendsto
        (fun θ : ℝ =>
          measureProb
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (fun ω => theorem8GaussianDefinition2Score2 ω < m))
        Filter.atTop (nhds 0) := by
    have hbase :=
      theorem8GaussianRealStd_Iio_tendsto_atTop_zero
        (x := x2) (m := m) hm_lt_x2
    refine hbase.congr' ?_
    filter_upwards with θ
    exact (theorem8GaussianDefinition2ScoreMeasureStd_score2_Iio_measureProb_eq
      (σ := 1 / θ) (x1 := x1) (x2 := x2) (x3 := x3) (m := m)).symm
  have htail2 :
      Filter.Tendsto
        (fun θ : ℝ =>
          measureProb
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (fun ω => m < theorem8GaussianDefinition2Score3 ω))
        Filter.atTop (nhds 0) := by
    have hbase :=
      theorem8GaussianRealStd_Ioi_tendsto_atTop_zero
        (x := x3) (m := m) hx3_lt_m
    refine hbase.congr' ?_
    filter_upwards with θ
    exact (theorem8GaussianDefinition2ScoreMeasureStd_score3_Ioi_measureProb_eq
      (σ := 1 / θ) (x1 := x1) (x2 := x2) (x3 := x3) (m := m)).symm
  have hupper :
      Filter.Tendsto
        (fun θ : ℝ =>
          measureProb
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (fun ω => theorem8GaussianDefinition2Score2 ω < m) +
          measureProb
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (fun ω => m < theorem8GaussianDefinition2Score3 ω))
        Filter.atTop (nhds 0) := by
    simpa using htail1.add htail2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 0) from
      tendsto_const_nhds)
    hupper ?_ ?_
  · exact Filter.Eventually.of_forall fun θ => by
      unfold measureProb
      exact ENNReal.toReal_nonneg
  · exact Filter.Eventually.of_forall fun θ =>
      measureProb_lt_le_midpoint_tails
        (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
        theorem8GaussianDefinition2Score2
        theorem8GaussianDefinition2Score3 m

/-- The sum of the two adjacent Gaussian inversion probabilities vanishes. -/
theorem theorem8GaussianDefinition2ScoreMeasureStd_adjacent_inversions_tendsto_atTop_zero
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Filter.Tendsto
      (fun θ : ℝ =>
        measureProb
          (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score2 ω) +
        measureProb
          (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω <
              theorem8GaussianDefinition2Score3 ω))
      Filter.atTop (nhds 0) := by
  simpa using
    (theorem8GaussianDefinition2ScoreMeasureStd_score12_inversion_tendsto_atTop_zero
      (x1 := x1) (x2 := x2) (x3 := x3) hx12).add
    (theorem8GaussianDefinition2ScoreMeasureStd_score23_inversion_tendsto_atTop_zero
      (x1 := x1) (x2 := x2) (x3 := x3) hx23)

/-- Coordinatewise canonical scaling for the three-score Gaussian source space. -/
noncomputable def theorem8GaussianDefinition2CanonicalScaleMap
    (σ : ℝ) : Theorem8GaussianDefinition2ScoreSpace →
      Theorem8GaussianDefinition2ScoreSpace :=
  Prod.map (fun z => theorem8GaussianCanonicalScale σ * z)
    (theorem8GaussianPairCanonicalScaleMap σ)

theorem theorem8GaussianDefinition2CanonicalScaleMap_measurable
    (σ : ℝ) :
    Measurable (theorem8GaussianDefinition2CanonicalScaleMap σ) := by
  unfold theorem8GaussianDefinition2CanonicalScaleMap
    theorem8GaussianPairCanonicalScaleMap
    AppliedModelingLib.Probability.pairCanonicalHalfVarianceScaleMap
  fun_prop

@[simp] theorem theorem8GaussianDefinition2CanonicalScaleMap_score1
    (σ : ℝ) (ω : Theorem8GaussianDefinition2ScoreSpace) :
    theorem8GaussianDefinition2Score1
        (theorem8GaussianDefinition2CanonicalScaleMap σ ω) =
      theorem8GaussianCanonicalScale σ *
        theorem8GaussianDefinition2Score1 ω := rfl

@[simp] theorem theorem8GaussianDefinition2CanonicalScaleMap_score2
    (σ : ℝ) (ω : Theorem8GaussianDefinition2ScoreSpace) :
    theorem8GaussianDefinition2Score2
        (theorem8GaussianDefinition2CanonicalScaleMap σ ω) =
      theorem8GaussianCanonicalScale σ *
        theorem8GaussianDefinition2Score2 ω := rfl

@[simp] theorem theorem8GaussianDefinition2CanonicalScaleMap_score3
    (σ : ℝ) (ω : Theorem8GaussianDefinition2ScoreSpace) :
    theorem8GaussianDefinition2Score3
        (theorem8GaussianDefinition2CanonicalScaleMap σ ω) =
      theorem8GaussianCanonicalScale σ *
        theorem8GaussianDefinition2Score3 ω := rfl

/--
The arbitrary-`σ` three-score Gaussian law maps to the canonical variance-`1/2`
three-score Gaussian law under coordinatewise canonical scaling.
-/
theorem theorem8GaussianDefinition2ScoreMeasureStd_map_canonicalScale
    {σ x1 x2 x3 : ℝ} (hσ : 0 < σ) :
    (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3).map
        (theorem8GaussianDefinition2CanonicalScaleMap σ) =
      theorem8GaussianDefinition2ScoreMeasure
        (theorem8GaussianCanonicalScale σ * x1)
        (theorem8GaussianCanonicalScale σ * x2)
        (theorem8GaussianCanonicalScale σ * x3) := by
  let μ1 := ProbabilityTheory.gaussianReal x1 (theorem8GaussianVarianceFromStd σ)
  let μ23 := theorem8GaussianPairMeasureStd σ x2 x3
  haveI : SFinite μ23 := by
    dsimp [μ23, theorem8GaussianPairMeasureStd,
      AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd,
      theorem8GaussianVarianceFromStd,
      AppliedModelingLib.Probability.gaussianVarianceFromStd]
    infer_instance
  unfold theorem8GaussianDefinition2ScoreMeasureStd
    theorem8GaussianDefinition2CanonicalScaleMap theorem8GaussianDefinition2ScoreMeasure
  change (μ1.prod μ23).map
      (Prod.map (fun z => theorem8GaussianCanonicalScale σ * z)
        (theorem8GaussianPairCanonicalScaleMap σ)) =
    (ProbabilityTheory.gaussianReal
        (theorem8GaussianCanonicalScale σ * x1) (1 / 2 : ℝ≥0)).prod
      (theorem8GaussianPairMeasure
        (theorem8GaussianCanonicalScale σ * x2)
        (theorem8GaussianCanonicalScale σ * x3))
  rw [← Measure.map_prod_map μ1 μ23 (by fun_prop)
    (theorem8GaussianPairCanonicalScaleMap_measurable σ)]
  rw [theorem8GaussianReal_map_canonicalScale (σ := σ) (μ := x1) hσ,
    theorem8GaussianPairMeasureStd_map_canonicalScale
      (σ := σ) (xi := x2) (xj := x3) hσ]

/-- Measure-preserving form of the arbitrary-`σ` three-score Gaussian scaling. -/
theorem theorem8GaussianDefinition2CanonicalScaleMap_measurePreserving
    {σ x1 x2 x3 : ℝ} (hσ : 0 < σ) :
    MeasurePreserving (theorem8GaussianDefinition2CanonicalScaleMap σ)
      (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
      (theorem8GaussianDefinition2ScoreMeasure
        (theorem8GaussianCanonicalScale σ * x1)
        (theorem8GaussianCanonicalScale σ * x2)
        (theorem8GaussianCanonicalScale σ * x3)) where
  measurable := theorem8GaussianDefinition2CanonicalScaleMap_measurable σ
  map_eq :=
    theorem8GaussianDefinition2ScoreMeasureStd_map_canonicalScale
      (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) hσ

/--
Appendix C, Theorem 8: under positive scaling, the strict numerator event with
cutoff `scale * a` pulls back to the strict numerator event with cutoff `a`.
-/
theorem theorem8GaussianPairCanonicalScaleMap_preimage_strict_numerator
    {σ a : ℝ} (hσ : 0 < σ) :
    (theorem8GaussianPairCanonicalScaleMap σ) ⁻¹'
        theorem8GaussianPairStrictNumeratorEvent
          (theorem8GaussianCanonicalScale σ * a) =
        theorem8GaussianPairStrictNumeratorEvent a := by
  simpa [theorem8GaussianPairCanonicalScaleMap,
    theorem8GaussianPairStrictNumeratorEvent, theorem8GaussianCanonicalScale,
    AppliedModelingLib.Probability.pairCanonicalHalfVarianceScaleMap,
    AppliedModelingLib.Probability.pairStrictWinnerBelowEvent] using
      AppliedModelingLib.Probability.pairCanonicalHalfVarianceScaleMap_preimage_strictWinnerBelow
        (σ := σ) (a := a) hσ

/--
Appendix C, Theorem 8: under positive scaling, the strict conditioning event
with cutoff `scale * a` pulls back to the strict conditioning event with cutoff
`a`.
-/
theorem theorem8GaussianPairCanonicalScaleMap_preimage_strict_denominator
    {σ a : ℝ} (hσ : 0 < σ) :
    (theorem8GaussianPairCanonicalScaleMap σ) ⁻¹'
        theorem8GaussianPairStrictDenominatorEvent
          (theorem8GaussianCanonicalScale σ * a) =
        theorem8GaussianPairStrictDenominatorEvent a := by
  simpa [theorem8GaussianPairCanonicalScaleMap,
    theorem8GaussianPairStrictDenominatorEvent, theorem8GaussianCanonicalScale,
    AppliedModelingLib.Probability.pairCanonicalHalfVarianceScaleMap,
    AppliedModelingLib.Probability.pairStrictBothBelowEvent] using
      AppliedModelingLib.Probability.pairCanonicalHalfVarianceScaleMap_preimage_strictBothBelow
        (σ := σ) (a := a) hσ

/--
Appendix C, Theorem 8: arbitrary-`σ` strict numerator mass equals the
corresponding canonical strict numerator mass after scaling.
-/
theorem theorem8GaussianPairMeasureStd_strict_numerator_eq_scaled
    {σ xi xj a : ℝ} (hσ : 0 < σ) :
    theorem8GaussianPairMeasureStd σ xi xj
        (theorem8GaussianPairStrictNumeratorEvent a) =
      theorem8GaussianPairMeasure
        (theorem8GaussianCanonicalScale σ * xi)
        (theorem8GaussianCanonicalScale σ * xj)
        (theorem8GaussianPairStrictNumeratorEvent
          (theorem8GaussianCanonicalScale σ * a)) := by
  simpa [theorem8GaussianPairMeasureStd,
    theorem8GaussianPairStrictNumeratorEvent, theorem8GaussianPairMeasure,
    theorem8GaussianCanonicalScale, theorem8GaussianVarianceFromStd,
    AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd,
    AppliedModelingLib.Probability.independentGaussianPairMeasureHalf,
    AppliedModelingLib.Probability.pairStrictWinnerBelowEvent] using
      AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd_strictWinnerBelow_eq_scaled
        (σ := σ) (xi := xi) (xj := xj) (a := a) hσ

/--
Appendix C, Theorem 8: arbitrary-`σ` strict denominator mass equals the
corresponding canonical strict denominator mass after scaling.
-/
theorem theorem8GaussianPairMeasureStd_strict_denominator_eq_scaled
    {σ xi xj a : ℝ} (hσ : 0 < σ) :
    theorem8GaussianPairMeasureStd σ xi xj
        (theorem8GaussianPairStrictDenominatorEvent a) =
      theorem8GaussianPairMeasure
        (theorem8GaussianCanonicalScale σ * xi)
        (theorem8GaussianCanonicalScale σ * xj)
        (theorem8GaussianPairStrictDenominatorEvent
          (theorem8GaussianCanonicalScale σ * a)) := by
  simpa [theorem8GaussianPairMeasureStd,
    theorem8GaussianPairStrictDenominatorEvent, theorem8GaussianPairMeasure,
    theorem8GaussianCanonicalScale, theorem8GaussianVarianceFromStd,
    AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd,
    AppliedModelingLib.Probability.independentGaussianPairMeasureHalf,
    AppliedModelingLib.Probability.pairStrictBothBelowEvent] using
      AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd_strictBothBelow_eq_scaled
        (σ := σ) (xi := xi) (xj := xj) (a := a) hσ

/--
Appendix C, Theorem 8: strict conditional probability ratio for independent
Gaussian scores with arbitrary positive standard deviation `σ`.
-/
noncomputable def theorem8GaussianProductStrictConditionalRatioAtStd
    (σ xi xj a : ℝ) : ℝ :=
  (theorem8GaussianPairMeasureStd σ xi xj
      (theorem8GaussianPairStrictNumeratorEvent a)).toReal /
    (theorem8GaussianPairMeasureStd σ xi xj
      (theorem8GaussianPairStrictDenominatorEvent a)).toReal

/--
Appendix C, Theorem 8: the arbitrary-`σ` strict conditional probability ratio
is the canonical variance-`1/2` ratio after scaling values and cutoff.
-/
theorem theorem8GaussianProductStrictConditionalRatioAtStd_eq_scaled
    {σ xi xj a : ℝ} (hσ : 0 < σ) :
    theorem8GaussianProductStrictConditionalRatioAtStd σ xi xj a =
      theorem8GaussianProductStrictConditionalRatioAt
        (theorem8GaussianCanonicalScale σ * xi)
        (theorem8GaussianCanonicalScale σ * xj)
        (theorem8GaussianCanonicalScale σ * a) := by
  simpa [theorem8GaussianProductStrictConditionalRatioAtStd,
    theorem8GaussianProductStrictConditionalRatioAt,
    theorem8GaussianPairMeasureStd, theorem8GaussianPairMeasure,
    theorem8GaussianPairStrictNumeratorEvent,
    theorem8GaussianPairStrictDenominatorEvent,
    theorem8GaussianCanonicalScale, theorem8GaussianVarianceFromStd,
    AppliedModelingLib.Probability.independentGaussianStrictConditionalWinnerRatioWithStd,
    AppliedModelingLib.Probability.independentGaussianStrictConditionalWinnerRatioHalf,
    AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd,
    AppliedModelingLib.Probability.independentGaussianPairMeasureHalf,
    AppliedModelingLib.Probability.pairStrictWinnerBelowEvent,
    AppliedModelingLib.Probability.pairStrictBothBelowEvent] using
      AppliedModelingLib.Probability.independentGaussianStrictConditionalWinnerRatioWithStd_eq_scaled
        (σ := σ) (xi := xi) (xj := xj) (a := a) hσ

/--
Appendix C, Theorem 8: the paper's arbitrary-`σ` strict conditional probability
ratio has strictly positive derivative in the cutoff `a`.  This formalizes the
source proof's WLOG reduction to `σ = 1 / sqrt 2` by an explicit positive
scaling of scores, values, and cutoff.
-/
theorem theorem8GaussianProductStrictConditionalRatioAtStd_hasDerivAt_pos
    {σ xi xj a : ℝ} (hσ : 0 < σ) (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => theorem8GaussianProductStrictConditionalRatioAtStd σ xi xj u)
        d a ∧
        0 < d := by
  let c := theorem8GaussianCanonicalScale σ
  have hc : 0 < c := theorem8GaussianCanonicalScale_pos hσ
  have hxc : c * xj < c * xi :=
    mul_lt_mul_of_pos_left hx hc
  obtain ⟨d, hd, hdpos⟩ :=
    theorem8GaussianProductStrictConditionalRatioAt_hasDerivAt_pos
      (xi := c * xi) (xj := c * xj) (a := c * a) hxc
  have hlin : HasDerivAt (fun u : ℝ => c * u) c a := by
    simpa using (hasDerivAt_id a).const_mul c
  refine ⟨d * c, ?_, mul_pos hdpos hc⟩
  have hcomp :
      HasDerivAt
        (fun u : ℝ =>
          theorem8GaussianProductStrictConditionalRatioAt
            (c * xi) (c * xj) (c * u))
        (d * c) a :=
    hd.comp a hlin
  exact hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u => by
      simpa [c] using
        theorem8GaussianProductStrictConditionalRatioAtStd_eq_scaled
          (σ := σ) (xi := xi) (xj := xj) (a := u) hσ)

/--
Appendix C, Theorem 8: if the arbitrary-`σ` strict conditional probability
ratio has finite atTop limit `L`, then every finite cutoff ratio is strictly
below `L`.  The strict monotonicity comes from the already formalized positive
derivative theorem.
-/
theorem theorem8GaussianProductStrictConditionalRatioAtStd_lt_of_tendsto_atTop
    {σ xi xj L a : ℝ} (hσ : 0 < σ) (hx : xj < xi)
    (hlim :
      Filter.Tendsto
        (fun u => theorem8GaussianProductStrictConditionalRatioAtStd σ xi xj u)
        Filter.atTop (nhds L)) :
    theorem8GaussianProductStrictConditionalRatioAtStd σ xi xj a < L := by
  let F : ℝ → ℝ := fun u =>
    theorem8GaussianProductStrictConditionalRatioAtStd σ xi xj u
  let F' : ℝ → ℝ := fun u =>
    Classical.choose
      (theorem8GaussianProductStrictConditionalRatioAtStd_hasDerivAt_pos
        (σ := σ) (xi := xi) (xj := xj) (a := u) hσ hx)
  have hderiv : ∀ u, HasDerivAt F (F' u) u := by
    intro u
    dsimp [F']
    exact
      (Classical.choose_spec
        (theorem8GaussianProductStrictConditionalRatioAtStd_hasDerivAt_pos
          (σ := σ) (xi := xi) (xj := xj) (a := u) hσ hx)).1
  have hpos : ∀ u, 0 < F' u := by
    intro u
    dsimp [F']
    exact
      (Classical.choose_spec
        (theorem8GaussianProductStrictConditionalRatioAtStd_hasDerivAt_pos
          (σ := σ) (xi := xi) (xj := xj) (a := u) hσ hx)).2
  have hmono : StrictMono F := strictMono_of_hasDerivAt_pos hderiv hpos
  exact strictMono_lt_tendsto_atTop_limit (f := F) (L := L) hmono hlim a

/-! ## Contraction geometry for RUM realizations -/

/--
The paper's contraction map on one coordinate:
`r' = x + t * (r - x)`, where `x` is the candidate's true value and
`0 ≤ t ≤ 1` corresponds to `θH / θA`.
-/
noncomputable def rumContractScore (t x r : ℝ) : ℝ := AppliedModelingLib.Probability.rumContractScore t x r

theorem rumContractScore_eq_affine (t x r : ℝ) :
    rumContractScore t x r = (1 - t) * x + t * r :=  AppliedModelingLib.Probability.rumContractScore_eq_affine t x r

/-- Contraction commutes with positive or negative scalar multiplication of the
score and its center. -/
theorem rumContractScore_mul_left (c t x r : ℝ) :
    rumContractScore t (c * x) (c * r) = c * rumContractScore t x r := by
  rw [rumContractScore_eq_affine, rumContractScore_eq_affine]
  ring

theorem theorem8GaussianReal_map_rumContractScore
    (t σ x : ℝ) :
    (ProbabilityTheory.gaussianReal x
        (theorem8GaussianVarianceFromStd σ)).map
        (fun r => rumContractScore t x r) =
      ProbabilityTheory.gaussianReal x
        (theorem8GaussianVarianceFromStd (t * σ)) := by
  have hfun :
      (fun r : ℝ => rumContractScore t x r) =
        (fun r : ℝ => t * r + (1 - t) * x) := by
    funext r
    rw [rumContractScore_eq_affine]
    ring
  rw [hfun]
  change
    Measure.map ((fun y : ℝ => y + (1 - t) * x) ∘
        (fun r : ℝ => t * r))
      (ProbabilityTheory.gaussianReal x (theorem8GaussianVarianceFromStd σ)) =
    ProbabilityTheory.gaussianReal x
      (theorem8GaussianVarianceFromStd (t * σ))
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [ProbabilityTheory.gaussianReal_map_const_mul]
  rw [ProbabilityTheory.gaussianReal_map_add_const]
  congr 2
  · ring
  · exact theorem8GaussianVarianceFromStd_mul_left t σ

theorem theorem8GaussianContractScore_measurable
    (t x : ℝ) :
    Measurable (fun r : ℝ => rumContractScore t x r) := by
  unfold rumContractScore
  exact measurable_const.add
    (measurable_const.mul (measurable_id.sub measurable_const))

/--
Laplace CDF transport under the paper's score contraction map.

If a Laplace noise coordinate has rate `lam` around mean `x`, then contracting
realizations toward `x` by a positive factor `t` gives rate `lam / t`.
-/
theorem theorem7LaplaceCDFClosedForm_contract
    {lam t x a : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    theorem7LaplaceCDFClosedForm lam x (x + (a - x) / t) =
      theorem7LaplaceCDFClosedForm (lam / t) x a := by
  have hrate : 0 < lam / t := div_pos hlam ht
  by_cases ha : a ≤ x
  · have harg_le : x + (a - x) / t ≤ x := by
      have hdiv : (a - x) / t ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ha) (le_of_lt ht)
      linarith
    rw [theorem7LaplaceCDFClosedForm_of_le_mean
        (lam := lam) (μ := x) (a := x + (a - x) / t) harg_le,
      theorem7LaplaceCDFClosedForm_of_le_mean
        (lam := lam / t) (μ := x) (a := a) ha]
    congr 2
    field_simp [ht.ne']
    ring_nf
  · have hxa : x ≤ a := le_of_not_ge ha
    have harg_ge : x ≤ x + (a - x) / t := by
      have hdiv : 0 ≤ (a - x) / t :=
        div_nonneg (sub_nonneg.mpr hxa) (le_of_lt ht)
      linarith
    rw [theorem7LaplaceCDFClosedForm_of_mean_le
        (lam := lam) (μ := x) (a := x + (a - x) / t) harg_ge,
      theorem7LaplaceCDFClosedForm_of_mean_le
        (lam := lam / t) (μ := x) (a := a) hxa]
    congr 2
    field_simp [ht.ne']
    ring_nf

theorem rumContractScore_preimage_Iic
    {t x a : ℝ} (ht : 0 < t) :
    (fun r : ℝ => rumContractScore t x r) ⁻¹' Set.Iic a =
      Set.Iic (x + (a - x) / t) := by
  ext r
  rw [Set.mem_preimage, Set.mem_Iic, Set.mem_Iic, rumContractScore_eq_affine]
  constructor
  · intro h
    have hmul : t * r ≤ a - (1 - t) * x := by
      nlinarith
    have hr : r ≤ (a - (1 - t) * x) / t :=
      (le_div_iff₀' ht).2 hmul
    have htarget : (a - (1 - t) * x) / t = x + (a - x) / t := by
      field_simp [ht.ne']
      ring
    simpa [htarget] using hr
  · intro h
    have htarget : x + (a - x) / t = (a - (1 - t) * x) / t := by
      field_simp [ht.ne']
      ring
    have hr : r ≤ (a - (1 - t) * x) / t := by
      simpa [htarget] using h
    have hmul : t * r ≤ a - (1 - t) * x :=
      (le_div_iff₀' ht).1 hr
    nlinarith

theorem theorem7LaplaceMeasure_map_rumContractScore
    {lam t x : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (theorem7LaplaceMeasure lam x).map
        (fun r => rumContractScore t x r) =
      theorem7LaplaceMeasure (lam / t) x := by
  have hrate : 0 < lam / t := div_pos hlam ht
  have hmeas : Measurable (fun r : ℝ => rumContractScore t x r) :=
    theorem8GaussianContractScore_measurable t x
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam x) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x) hlam⟩
  haveI : IsProbabilityMeasure
      ((theorem7LaplaceMeasure lam x).map
        (fun r => rumContractScore t x r)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure (lam / t) x) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam / t) (μ := x) hrate⟩
  apply Measure.eq_of_cdf
  ext a
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  rw [Measure.real_def, Measure.real_def]
  rw [Measure.map_apply hmeas measurableSet_Iic]
  rw [rumContractScore_preimage_Iic (t := t) (x := x) (a := a) ht]
  rw [theorem7LaplaceMeasure_Iic_eq_CDF (lam := lam) (μ := x)
      (a := x + (a - x) / t) hlam,
    theorem7LaplaceMeasure_Iic_eq_CDF (lam := lam / t) (μ := x)
      (a := a) hrate]
  rw [ENNReal.toReal_ofReal
      (theorem7LaplaceCDFClosedForm_nonneg (lam := lam) (μ := x)
        (a := x + (a - x) / t) hlam),
    ENNReal.toReal_ofReal
      (theorem7LaplaceCDFClosedForm_nonneg (lam := lam / t) (μ := x)
        (a := a) hrate)]
  exact theorem7LaplaceCDFClosedForm_contract
    (lam := lam) (t := t) (x := x) (a := a) hlam ht

noncomputable def theorem8GaussianDefinition2ContractMap
    (t x1 x2 x3 : ℝ) :
    Theorem8GaussianDefinition2ScoreSpace →
      Theorem8GaussianDefinition2ScoreSpace :=
  Prod.map (fun r1 => rumContractScore t x1 r1)
    (Prod.map (fun r2 => rumContractScore t x2 r2)
      (fun r3 => rumContractScore t x3 r3))

theorem theorem8GaussianDefinition2ContractMap_measurable
    (t x1 x2 x3 : ℝ) :
    Measurable (theorem8GaussianDefinition2ContractMap t x1 x2 x3) := by
  unfold theorem8GaussianDefinition2ContractMap
  exact
    (theorem8GaussianContractScore_measurable t x1).prodMap
      ((theorem8GaussianContractScore_measurable t x2).prodMap
        (theorem8GaussianContractScore_measurable t x3))

@[simp] theorem theorem8GaussianDefinition2ContractMap_score1
    (t x1 x2 x3 : ℝ) (ω : Theorem8GaussianDefinition2ScoreSpace) :
    theorem8GaussianDefinition2Score1
        (theorem8GaussianDefinition2ContractMap t x1 x2 x3 ω) =
      rumContractScore t x1 (theorem8GaussianDefinition2Score1 ω) := rfl

@[simp] theorem theorem8GaussianDefinition2ContractMap_score2
    (t x1 x2 x3 : ℝ) (ω : Theorem8GaussianDefinition2ScoreSpace) :
    theorem8GaussianDefinition2Score2
        (theorem8GaussianDefinition2ContractMap t x1 x2 x3 ω) =
      rumContractScore t x2 (theorem8GaussianDefinition2Score2 ω) := rfl

@[simp] theorem theorem8GaussianDefinition2ContractMap_score3
    (t x1 x2 x3 : ℝ) (ω : Theorem8GaussianDefinition2ScoreSpace) :
    theorem8GaussianDefinition2Score3
        (theorem8GaussianDefinition2ContractMap t x1 x2 x3 ω) =
      rumContractScore t x3 (theorem8GaussianDefinition2Score3 ω) := rfl

theorem theorem8GaussianPairMeasureStd_map_contract
    (t σ x2 x3 : ℝ) :
    (theorem8GaussianPairMeasureStd σ x2 x3).map
        (Prod.map (fun r2 => rumContractScore t x2 r2)
          (fun r3 => rumContractScore t x3 r3)) =
      theorem8GaussianPairMeasureStd (t * σ) x2 x3 := by
  let μ2 := ProbabilityTheory.gaussianReal x2 (theorem8GaussianVarianceFromStd σ)
  let μ3 := ProbabilityTheory.gaussianReal x3 (theorem8GaussianVarianceFromStd σ)
  haveI : SFinite μ2 := by
    dsimp [μ2]
    infer_instance
  haveI : SFinite μ3 := by
    dsimp [μ3]
    infer_instance
  unfold theorem8GaussianPairMeasureStd
    AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd
  change (μ2.prod μ3).map
        (Prod.map (fun r2 => rumContractScore t x2 r2)
          (fun r3 => rumContractScore t x3 r3)) =
      (ProbabilityTheory.gaussianReal x2
          (theorem8GaussianVarianceFromStd (t * σ))).prod
        (ProbabilityTheory.gaussianReal x3
          (theorem8GaussianVarianceFromStd (t * σ)))
  rw [← Measure.map_prod_map μ2 μ3
    (theorem8GaussianContractScore_measurable t x2)
    (theorem8GaussianContractScore_measurable t x3)]
  rw [theorem8GaussianReal_map_rumContractScore,
    theorem8GaussianReal_map_rumContractScore]

theorem theorem8GaussianDefinition2ScoreMeasureStd_map_contract
    (t σ x1 x2 x3 : ℝ) :
    (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3).map
        (theorem8GaussianDefinition2ContractMap t x1 x2 x3) =
      theorem8GaussianDefinition2ScoreMeasureStd (t * σ) x1 x2 x3 := by
  let μ1 := ProbabilityTheory.gaussianReal x1 (theorem8GaussianVarianceFromStd σ)
  let μ23 := theorem8GaussianPairMeasureStd σ x2 x3
  haveI : SFinite μ1 := by
    dsimp [μ1]
    infer_instance
  haveI : SFinite μ23 := by
    dsimp [μ23, theorem8GaussianPairMeasureStd,
      AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd]
    infer_instance
  unfold theorem8GaussianDefinition2ScoreMeasureStd
    theorem8GaussianDefinition2ContractMap
  change (μ1.prod μ23).map
        (Prod.map (fun r1 => rumContractScore t x1 r1)
          (Prod.map (fun r2 => rumContractScore t x2 r2)
            (fun r3 => rumContractScore t x3 r3))) =
      (ProbabilityTheory.gaussianReal x1
          (theorem8GaussianVarianceFromStd (t * σ))).prod
        (theorem8GaussianPairMeasureStd (t * σ) x2 x3)
  rw [← Measure.map_prod_map μ1 μ23
    (theorem8GaussianContractScore_measurable t x1)
    ((theorem8GaussianContractScore_measurable t x2).prodMap
      (theorem8GaussianContractScore_measurable t x3))]
  rw [theorem8GaussianReal_map_rumContractScore,
    theorem8GaussianPairMeasureStd_map_contract]

theorem theorem8GaussianDefinition2ContractMap_measurePreserving
    (t σ x1 x2 x3 : ℝ) :
    MeasurePreserving (theorem8GaussianDefinition2ContractMap t x1 x2 x3)
      (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
      (theorem8GaussianDefinition2ScoreMeasureStd (t * σ) x1 x2 x3) where
  measurable := theorem8GaussianDefinition2ContractMap_measurable t x1 x2 x3
  map_eq :=
    theorem8GaussianDefinition2ScoreMeasureStd_map_contract
      t σ x1 x2 x3

/-- Laplace analogue of the Definition-2 coordinate contraction map. -/
noncomputable abbrev theorem7LaplacianDefinition2ContractMap
    (t x1 x2 x3 : ℝ) :
    Theorem7LaplacianDefinition2ScoreSpace →
      Theorem7LaplacianDefinition2ScoreSpace :=
  theorem8GaussianDefinition2ContractMap t x1 x2 x3

theorem theorem7LaplacianDefinition2ContractMap_measurable
    (t x1 x2 x3 : ℝ) :
    Measurable (theorem7LaplacianDefinition2ContractMap t x1 x2 x3) :=
  theorem8GaussianDefinition2ContractMap_measurable t x1 x2 x3

@[simp] theorem theorem7LaplacianDefinition2ContractMap_score1
    (t x1 x2 x3 : ℝ) (ω : Theorem7LaplacianDefinition2ScoreSpace) :
    theorem7LaplacianDefinition2Score1
        (theorem7LaplacianDefinition2ContractMap t x1 x2 x3 ω) =
      rumContractScore t x1 (theorem7LaplacianDefinition2Score1 ω) := rfl

@[simp] theorem theorem7LaplacianDefinition2ContractMap_score2
    (t x1 x2 x3 : ℝ) (ω : Theorem7LaplacianDefinition2ScoreSpace) :
    theorem7LaplacianDefinition2Score2
        (theorem7LaplacianDefinition2ContractMap t x1 x2 x3 ω) =
      rumContractScore t x2 (theorem7LaplacianDefinition2Score2 ω) := rfl

@[simp] theorem theorem7LaplacianDefinition2ContractMap_score3
    (t x1 x2 x3 : ℝ) (ω : Theorem7LaplacianDefinition2ScoreSpace) :
    theorem7LaplacianDefinition2Score3
        (theorem7LaplacianDefinition2ContractMap t x1 x2 x3 ω) =
      rumContractScore t x3 (theorem7LaplacianDefinition2Score3 ω) := rfl

theorem theorem7LaplacianPairMeasure_map_contract
    {lam t x2 x3 : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (theorem7LaplacianPairMeasure lam x2 x3).map
        (Prod.map (fun r2 => rumContractScore t x2 r2)
          (fun r3 => rumContractScore t x3 r3)) =
      theorem7LaplacianPairMeasure (lam / t) x2 x3 := by
  let μ2 := theorem7LaplaceMeasure lam x2
  let μ3 := theorem7LaplaceMeasure lam x3
  haveI : SFinite μ2 := by
    dsimp [μ2, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ3 := by
    dsimp [μ3, theorem7LaplaceMeasure]
    infer_instance
  unfold theorem7LaplacianPairMeasure
  change (μ2.prod μ3).map
        (Prod.map (fun r2 => rumContractScore t x2 r2)
          (fun r3 => rumContractScore t x3 r3)) =
      (theorem7LaplaceMeasure (lam / t) x2).prod
        (theorem7LaplaceMeasure (lam / t) x3)
  rw [← Measure.map_prod_map μ2 μ3
    (theorem8GaussianContractScore_measurable t x2)
    (theorem8GaussianContractScore_measurable t x3)]
  rw [theorem7LaplaceMeasure_map_rumContractScore
      (lam := lam) (t := t) (x := x2) hlam ht,
    theorem7LaplaceMeasure_map_rumContractScore
      (lam := lam) (t := t) (x := x3) hlam ht]

theorem theorem7LaplacianDefinition2ScoreMeasure_map_contract
    {lam t x1 x2 x3 : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3).map
        (theorem7LaplacianDefinition2ContractMap t x1 x2 x3) =
      theorem7LaplacianDefinition2ScoreMeasure (lam / t) x1 x2 x3 := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ23 := theorem7LaplacianPairMeasure lam x2 x3
  haveI : SFinite μ1 := by
    dsimp [μ1, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ23 := by
    dsimp [μ23, theorem7LaplacianPairMeasure, theorem7LaplaceMeasure]
    infer_instance
  unfold theorem7LaplacianDefinition2ScoreMeasure
    theorem7LaplacianDefinition2ContractMap
    theorem8GaussianDefinition2ContractMap
  change (μ1.prod μ23).map
        (Prod.map (fun r1 => rumContractScore t x1 r1)
          (Prod.map (fun r2 => rumContractScore t x2 r2)
            (fun r3 => rumContractScore t x3 r3))) =
      (theorem7LaplaceMeasure (lam / t) x1).prod
        (theorem7LaplacianPairMeasure (lam / t) x2 x3)
  rw [← Measure.map_prod_map μ1 μ23
    (theorem8GaussianContractScore_measurable t x1)
    ((theorem8GaussianContractScore_measurable t x2).prodMap
      (theorem8GaussianContractScore_measurable t x3))]
  rw [theorem7LaplaceMeasure_map_rumContractScore
      (lam := lam) (t := t) (x := x1) hlam ht,
    theorem7LaplacianPairMeasure_map_contract
      (lam := lam) (t := t) (x2 := x2) (x3 := x3) hlam ht]

theorem theorem7LaplacianDefinition2ContractMap_measurePreserving
    {lam t x1 x2 x3 : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    MeasurePreserving (theorem7LaplacianDefinition2ContractMap t x1 x2 x3)
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
      (theorem7LaplacianDefinition2ScoreMeasure (lam / t) x1 x2 x3) where
  measurable := theorem7LaplacianDefinition2ContractMap_measurable t x1 x2 x3
  map_eq :=
    theorem7LaplacianDefinition2ScoreMeasure_map_contract
      (lam := lam) (t := t) (x1 := x1) (x2 := x2) (x3 := x3) hlam ht

theorem rumContractScore_sub
    (t xi xj ri rj : ℝ) :
    rumContractScore t xi ri - rumContractScore t xj rj =
      (1 - t) * (xi - xj) + t * (ri - rj) :=  AppliedModelingLib.Probability.rumContractScore_sub t xi xj ri rj

/-- Candidate `x₁` is weakly first among three realized scores. -/
def rum3TopFirstByScores (s1 s2 s3 : ℝ) : Prop := AppliedModelingLib.SocialChoice.Ranking.rum3TopFirstByScores s1 s2 s3

/-- Candidate `x₂` strictly beats `x₁` and weakly beats `x₃`. -/
def rum3MiddleBeatsTopByScores (s1 s2 s3 : ℝ) : Prop := AppliedModelingLib.SocialChoice.Ranking.rum3MiddleBeatsTopByScores s1 s2 s3

/-- Candidate `x₃` is weakly first among three realized scores. -/
def rum3BottomFirstByScores (s1 s2 s3 : ℝ) : Prop := AppliedModelingLib.SocialChoice.Ranking.rum3BottomFirstByScores s1 s2 s3

/--
Contraction cannot reverse an already-correct weak order between two candidates.
-/
theorem rumContractScore_preserves_weak_order
    {t xi xj ri rj : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : xj ≤ xi) (hr : rj ≤ ri) :
    rumContractScore t xj rj ≤ rumContractScore t xi ri :=
   AppliedModelingLib.Probability.rumContractScore_preserves_weak_order
    ht0 ht1 hx hr

/--
Strict version of the contraction order lemma.  If both true values and realized
scores put candidate `i` above candidate `j`, then contraction keeps `i` strictly
above `j`.
-/
theorem rumContractScore_preserves_strict_order
    {t xi xj ri rj : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : xj < xi) (hr : rj < ri) :
    rumContractScore t xj rj < rumContractScore t xi ri :=
   AppliedModelingLib.Probability.rumContractScore_preserves_strict_order
    ht0 ht1 hx hr

/--
If a raw-score winner is beaten after a genuine contraction, the contracted
winner has weakly higher true value.
-/
theorem rumContractScore_value_le_of_raw_le_and_contract_ge
    {t xi xj ri rj : ℝ}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hr : ri ≤ rj)
    (hc : rumContractScore t xj rj ≤ rumContractScore t xi ri) :
    xj ≤ xi :=
  AppliedModelingLib.Probability.rumContractScore_value_le_of_raw_le_and_contract_ge
    ht0 htlt1 hr hc

/--
Argmax form for finite RUM monotonicity.  If `rawBest` maximizes realized
scores and `contractBest` maximizes contracted scores, the contracted best
candidate has weakly higher true value.
-/
theorem rumContractScore_value_le_of_raw_max_and_contract_max
    {ι : Type*} {t : ℝ} {value raw : ι → ℝ}
    {rawBest contractBest : ι}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hrawMax : ∀ i : ι, raw i ≤ raw rawBest)
    (hcontractMax : ∀ i : ι,
      rumContractScore t (value i) (raw i) ≤
        rumContractScore t (value contractBest) (raw contractBest)) :
    value rawBest ≤ value contractBest :=
  AppliedModelingLib.Probability.rumContractScore_value_le_of_raw_max_and_contract_max
    ht0 htlt1 hrawMax hcontractMax

/--
Feasible-set form of the argmax contraction lemma, used for arbitrary
remaining-candidate sets.
-/
theorem rumContractScore_value_le_of_raw_max_on_and_contract_max_on
    {ι : Type*} {t : ℝ} {value raw : ι → ℝ} {feasible : ι → Prop}
    {rawBest contractBest : ι}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hrawMem : feasible rawBest) (hcontractMem : feasible contractBest)
    (hrawMax : ∀ i : ι, feasible i → raw i ≤ raw rawBest)
    (hcontractMax : ∀ i : ι, feasible i →
      rumContractScore t (value i) (raw i) ≤
        rumContractScore t (value contractBest) (raw contractBest)) :
    value rawBest ≤ value contractBest :=
  AppliedModelingLib.Probability.rumContractScore_value_le_of_raw_max_on_and_contract_max_on
    ht0 htlt1 hrawMem hcontractMem hrawMax hcontractMax

/--
Three-candidate top-first preservation: if `x₁` is first before contraction,
it is still first after contraction.
-/
theorem rum3_contract_top_first_of_original_top_first
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 ≤ x1) (hx13 : x3 ≤ x1)
    (hr12 : r2 ≤ r1) (hr13 : r3 ≤ r1) :
    rumContractScore t x2 r2 ≤ rumContractScore t x1 r1 ∧
      rumContractScore t x3 r3 ≤ rumContractScore t x1 r1 :=
  AppliedModelingLib.Probability.rum3_contract_top_first_of_original_top_first
    ht0 ht1 hx12 hx13 hr12 hr13

/--
Three-candidate bottom-first reflection: if the lowest-value candidate `x₃` is
first after contraction, then it was already first before contraction.
-/
theorem rum3_contract_bottom_first_imp_original_bottom_first
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx31 : x3 < x1) (hx32 : x3 < x2)
    (hc31 : rumContractScore t x1 r1 ≤ rumContractScore t x3 r3)
    (hc32 : rumContractScore t x2 r2 ≤ rumContractScore t x3 r3) :
    r1 ≤ r3 ∧ r2 ≤ r3 :=
   AppliedModelingLib.Probability.rum3_contract_bottom_first_imp_original_bottom_first
    ht0 ht1 hx31 hx32 hc31 hc32

/--
Strict bottom-first reflection for a genuine contraction (`t < 1`).

If the lowest-value candidate `x₃` is weakly first after contraction, then its
raw realized score was strictly above both higher-valued candidates.  This is
the continuous-paper way to avoid a pointwise no-tie assumption in the concrete
score-ranking bridge.
-/
theorem rum3_contract_bottom_first_imp_original_bottom_first_strict_of_t_lt_one
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hx31 : x3 < x1) (hx32 : x3 < x2)
    (hc31 : rumContractScore t x1 r1 ≤ rumContractScore t x3 r3)
    (hc32 : rumContractScore t x2 r2 ≤ rumContractScore t x3 r3) :
    r1 < r3 ∧ r2 < r3 :=
   AppliedModelingLib.Probability.rum3_contract_bottom_first_imp_original_bottom_first_strict_of_t_lt_one
    ht0 htlt1 hx31 hx32 hc31 hc32

/-! ## Concrete three-score rankings -/

/-- The concrete ranking `[x₁, x₂, x₃]`. -/
def rum3Ranking012 : Ranking 1 := AppliedModelingLib.SocialChoice.Ranking.rum3Ranking012

/-- The concrete ranking `[x₁, x₃, x₂]`. -/
def rum3Ranking021 : Ranking 1 := AppliedModelingLib.SocialChoice.Ranking.rum3Ranking021

/-- The concrete ranking `[x₂, x₁, x₃]`. -/
def rum3Ranking102 : Ranking 1 := AppliedModelingLib.SocialChoice.Ranking.rum3Ranking102

/-- The concrete ranking `[x₂, x₃, x₁]`. -/
def rum3Ranking120 : Ranking 1 := AppliedModelingLib.SocialChoice.Ranking.rum3Ranking120

/-- The concrete ranking `[x₃, x₁, x₂]`. -/
def rum3Ranking201 : Ranking 1 := AppliedModelingLib.SocialChoice.Ranking.rum3Ranking201

/-- The concrete ranking `[x₃, x₂, x₁]`. -/
def rum3Ranking210 : Ranking 1 := AppliedModelingLib.SocialChoice.Ranking.rum3Ranking210

@[simp] theorem rum3Ranking012_apply_zero :
    rum3Ranking012 (0 : Candidate 1) = (0 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking012_apply_zero

@[simp] theorem rum3Ranking012_apply_one :
    rum3Ranking012 (1 : Candidate 1) = (1 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking012_apply_one

@[simp] theorem rum3Ranking012_apply_two :
    rum3Ranking012 (2 : Candidate 1) = (2 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking012_apply_two

@[simp] theorem rum3Ranking021_apply_zero :
    rum3Ranking021 (0 : Candidate 1) = (0 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking021_apply_zero

@[simp] theorem rum3Ranking021_apply_one :
    rum3Ranking021 (1 : Candidate 1) = (2 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking021_apply_one

@[simp] theorem rum3Ranking021_apply_two :
    rum3Ranking021 (2 : Candidate 1) = (1 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking021_apply_two

@[simp] theorem rum3Ranking102_apply_zero :
    rum3Ranking102 (0 : Candidate 1) = (1 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking102_apply_zero

@[simp] theorem rum3Ranking102_apply_one :
    rum3Ranking102 (1 : Candidate 1) = (0 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking102_apply_one

@[simp] theorem rum3Ranking102_apply_two :
    rum3Ranking102 (2 : Candidate 1) = (2 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking102_apply_two

@[simp] theorem rum3Ranking120_apply_zero :
    rum3Ranking120 (0 : Candidate 1) = (1 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking120_apply_zero

@[simp] theorem rum3Ranking120_apply_one :
    rum3Ranking120 (1 : Candidate 1) = (2 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking120_apply_one

@[simp] theorem rum3Ranking120_apply_two :
    rum3Ranking120 (2 : Candidate 1) = (0 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking120_apply_two

@[simp] theorem rum3Ranking201_apply_zero :
    rum3Ranking201 (0 : Candidate 1) = (2 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking201_apply_zero

@[simp] theorem rum3Ranking201_apply_one :
    rum3Ranking201 (1 : Candidate 1) = (0 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking201_apply_one

@[simp] theorem rum3Ranking201_apply_two :
    rum3Ranking201 (2 : Candidate 1) = (1 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking201_apply_two

@[simp] theorem rum3Ranking210_apply_zero :
    rum3Ranking210 (0 : Candidate 1) = (2 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking210_apply_zero

@[simp] theorem rum3Ranking210_apply_one :
    rum3Ranking210 (1 : Candidate 1) = (1 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking210_apply_one

@[simp] theorem rum3Ranking210_apply_two :
    rum3Ranking210 (2 : Candidate 1) = (0 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3Ranking210_apply_two

/--
Ranking induced by three realized scores, ordered descending by score and
breaking ties in favor of the lower-indexed candidate.  The paper's continuous
RUM has zero tie probability for ordinary densities, but this deterministic
tie convention makes the score-to-ranking map total.
-/
noncomputable def rum3RankByScores (s1 s2 s3 : ℝ) : Ranking 1 := AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores s1 s2 s3

/-- Realized scores have no pairwise ties. -/
def rum3NoTiesByScores (s1 s2 s3 : ℝ) : Prop := AppliedModelingLib.SocialChoice.Ranking.rum3NoTiesByScores s1 s2 s3

/-- Ranking map induced by three score-coordinate functions. -/
noncomputable def rum3RankByScoreFns {Ω : Type*}
    (r1 r2 r3 : Ω → ℝ) : Ω → Ranking 1 := fun ω => rum3RankByScores (r1 ω) (r2 ω) (r3 ω)

theorem rum3RankByScores_eq012_of_adjacent_order
    {s1 s2 s3 : ℝ} (h21 : s2 ≤ s1) (h32 : s3 ≤ s2) :
    rum3RankByScores s1 s2 s3 = rum3Ranking012 :=
  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_eq012_of_adjacent_order
    h21 h32

theorem rum3RankByScores_eq102_of_order
    {s1 s2 s3 : ℝ} (h12 : s1 < s2) (h31 : s3 ≤ s1) :
    rum3RankByScores s1 s2 s3 = rum3Ranking102 :=
  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_eq102_of_order h12 h31

theorem rum3RankByScores_pos_mul
    {c s1 s2 s3 : ℝ} (hc : 0 < c) :
    rum3RankByScores (c * s1) (c * s2) (c * s3) =
      rum3RankByScores s1 s2 s3 :=
  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_pos_mul hc

theorem rum3RankByScores_ne012_imp_adjacent_inversion
    {s1 s2 s3 : ℝ}
    (h : rum3RankByScores s1 s2 s3 ≠ rum3Ranking012) :
    s1 < s2 ∨ s2 < s3 :=
  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_ne012_imp_adjacent_inversion h

theorem rum3RankByScoreFns_ne012_imp_adjacent_inversion
    {Ω : Type*} {r1 r2 r3 : Ω → ℝ} {ω : Ω}
    (h : rum3RankByScoreFns r1 r2 r3 ω ≠ rum3Ranking012) :
    r1 ω < r2 ω ∨ r2 ω < r3 ω :=
  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScoreFns_ne012_imp_adjacent_inversion h

/-- Positive rescaling of all three scores does not change the induced ranking. -/
theorem rum3RankByScores_mul_pos {c : ℝ} (hc : 0 < c) (s1 s2 s3 : ℝ) :
    rum3RankByScores (c * s1) (c * s2) (c * s3) =
      rum3RankByScores s1 s2 s3 := by
  unfold rum3RankByScores AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores
  simp [mul_le_mul_iff_right₀ hc, mul_lt_mul_iff_right₀ hc]

/-- Positive rescaling of all score-coordinate functions does not change rankings. -/
theorem rum3RankByScoreFns_mul_pos {Ω : Type*} {c : ℝ} (hc : 0 < c)
    (r1 r2 r3 : Ω → ℝ) :
    rum3RankByScoreFns (fun ω => c * r1 ω) (fun ω => c * r2 ω)
        (fun ω => c * r3 ω) =
      rum3RankByScoreFns r1 r2 r3 := by
  funext ω
  exact rum3RankByScores_mul_pos hc (r1 ω) (r2 ω) (r3 ω)

/-- Ranking map induced by contracted score-coordinate functions. -/
noncomputable def rum3ContractRankByScoreFns {Ω : Type*}
    (t x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) : Ω → Ranking 1 :=
  fun ω => rum3RankByScores
    (rumContractScore t x1 (r1 ω))
    (rumContractScore t x2 (r2 ω))
    (rumContractScore t x3 (r3 ω))

theorem rumContractScore_measurable
    {Ω : Type*} [MeasurableSpace Ω] {r : Ω → ℝ}
    (hr : Measurable r) (t x : ℝ) :
    Measurable (fun ω => rumContractScore t x (r ω)) := by
  unfold rumContractScore
  exact measurable_const.add (measurable_const.mul (hr.sub measurable_const))

theorem rum3RankByScoreFns_measurable
    {Ω : Type*} [MeasurableSpace Ω] {r1 r2 r3 : Ω → ℝ}
    (hr1 : Measurable r1) (hr2 : Measurable r2) (hr3 : Measurable r3) :
    Measurable (rum3RankByScoreFns r1 r2 r3) := by
  unfold rum3RankByScoreFns rum3RankByScores
    AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores
  refine Measurable.ite
    ((measurableSet_le hr2 hr1).inter (measurableSet_le hr3 hr1)) ?_ ?_
  · exact Measurable.ite (measurableSet_le hr3 hr2) measurable_const measurable_const
  · refine Measurable.ite
      ((measurableSet_lt hr1 hr2).inter (measurableSet_le hr3 hr2)) ?_ ?_
    · exact Measurable.ite (measurableSet_le hr3 hr1) measurable_const measurable_const
    · exact Measurable.ite (measurableSet_le hr2 hr1) measurable_const measurable_const

theorem rum3ContractRankByScoreFns_measurable
    {Ω : Type*} [MeasurableSpace Ω] {r1 r2 r3 : Ω → ℝ}
    (hr1 : Measurable r1) (hr2 : Measurable r2) (hr3 : Measurable r3)
    (t x1 x2 x3 : ℝ) :
    Measurable (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3) :=
  rum3RankByScoreFns_measurable
    (rumContractScore_measurable hr1 t x1)
    (rumContractScore_measurable hr2 t x2)
    (rumContractScore_measurable hr3 t x3)

theorem rumContractScore_pair_le_eventually_at_one
    {xi xj ri rj : ℝ} (hne : ri ≠ rj) :
    ∀ᶠ t : ℝ in nhds (1 : ℝ),
      (rumContractScore t xj rj ≤ rumContractScore t xi ri) ↔ rj ≤ ri := by
  let d : ℝ → ℝ := fun t =>
    rumContractScore t xi ri - rumContractScore t xj rj
  have hd_cont : ContinuousAt d 1 := by
    dsimp [d, rumContractScore, AppliedModelingLib.Probability.rumContractScore]
    fun_prop
  have hd_one : d 1 = ri - rj := by
    dsimp [d]
    rw [rumContractScore_eq_affine, rumContractScore_eq_affine]
    ring
  by_cases hle : rj ≤ ri
  · have hlt : rj < ri := lt_of_le_of_ne hle hne.symm
    have hpos : 0 < d 1 := by
      rw [hd_one]
      exact sub_pos.mpr hlt
    exact
      (hd_cont.eventually (Ioi_mem_nhds hpos)).mono fun t ht => by
        have hscore :
            rumContractScore t xj rj < rumContractScore t xi ri := by
          dsimp [d] at ht
          linarith
        simp [hle, le_of_lt hscore]
  · have hlt : ri < rj := lt_of_not_ge hle
    have hneg : d 1 < 0 := by
      rw [hd_one]
      exact sub_neg.mpr hlt
    exact
      (hd_cont.eventually (Iio_mem_nhds hneg)).mono fun t ht => by
        have hscore :
            rumContractScore t xi ri < rumContractScore t xj rj := by
          dsimp [d] at ht
          linarith
        have hnot :
            ¬ rumContractScore t xj rj ≤ rumContractScore t xi ri :=
          not_le_of_gt hscore
        simp [hle, hnot]

theorem rumContractScore_pair_lt_eventually_at_one
    {xi xj ri rj : ℝ} (hne : ri ≠ rj) :
    ∀ᶠ t : ℝ in nhds (1 : ℝ),
      (rumContractScore t xi ri < rumContractScore t xj rj) ↔ ri < rj := by
  have hev :=
    rumContractScore_pair_le_eventually_at_one
      (xi := xi) (xj := xj) (ri := ri) (rj := rj) hne
  exact hev.mono fun t ht => by
    rw [← not_le, ← not_le]
    exact not_congr ht

theorem rum3ContractRankByScoreFns_eventually_eq_rankByScoreFns_at_one
    {Ω : Type*} {x1 x2 x3 : ℝ} {r1 r2 r3 : Ω → ℝ} {ω : Ω}
    (h12 : r1 ω ≠ r2 ω) (h13 : r1 ω ≠ r3 ω)
    (h23 : r2 ω ≠ r3 ω) :
    ∀ᶠ t : ℝ in nhds (1 : ℝ),
      rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω =
        rum3RankByScoreFns r1 r2 r3 ω := by
  have h21 :=
    rumContractScore_pair_le_eventually_at_one
      (xi := x1) (xj := x2) (ri := r1 ω) (rj := r2 ω) h12
  have h31 :=
    rumContractScore_pair_le_eventually_at_one
      (xi := x1) (xj := x3) (ri := r1 ω) (rj := r3 ω) h13
  have h12lt :=
    rumContractScore_pair_lt_eventually_at_one
      (xi := x1) (xj := x2) (ri := r1 ω) (rj := r2 ω) h12
  have h32 :=
    rumContractScore_pair_le_eventually_at_one
      (xi := x2) (xj := x3) (ri := r2 ω) (rj := r3 ω) h23
  filter_upwards [h21, h31, h12lt, h32] with t ht21 ht31 ht12lt ht32
  unfold rum3ContractRankByScoreFns rum3RankByScoreFns rum3RankByScores
    AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores
  simp [ht21, ht31, ht12lt, ht32]

@[simp] theorem firstChoice_rum3RankByScores (s1 s2 s3 : ℝ) :
    firstChoice (rum3RankByScores s1 s2 s3) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then (0 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then (1 : Candidate 1)
      else (2 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.firstChoice_rum3RankByScores s1 s2 s3

@[simp] theorem secondChoice_rum3RankByScores (s1 s2 s3 : ℝ) :
    secondChoice (rum3RankByScores s1 s2 s3) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then
        if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then
        if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1)
      else
        if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.secondChoice_rum3RankByScores s1 s2 s3

@[simp] theorem rum3RankByScores_apply_zero (s1 s2 s3 : ℝ) :
    rum3RankByScores s1 s2 s3 (0 : Candidate 1) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then (0 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then (1 : Candidate 1)
      else (2 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_apply_zero s1 s2 s3

@[simp] theorem rum3RankByScores_apply_one (s1 s2 s3 : ℝ) :
    rum3RankByScores s1 s2 s3 (1 : Candidate 1) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then
        if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then
        if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1)
      else
        if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_apply_one s1 s2 s3

@[simp] theorem bestRemainingAfter_rum3RankByScores_remove0
    (s1 s2 s3 : ℝ) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
      if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1) :=
   AppliedModelingLib.SocialChoice.Ranking.bestRemainingAfter_rum3RankByScores_remove0
    s1 s2 s3

@[simp] theorem bestRemainingAfter_rum3RankByScores_remove1
    (s1 s2 s3 : ℝ) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (1 : Candidate 1) =
      if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1) :=
   AppliedModelingLib.SocialChoice.Ranking.bestRemainingAfter_rum3RankByScores_remove1
    s1 s2 s3

@[simp] theorem bestRemainingAfter_rum3RankByScores_remove2
    (s1 s2 s3 : ℝ) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (2 : Candidate 1) =
      if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1) :=
   AppliedModelingLib.SocialChoice.Ranking.bestRemainingAfter_rum3RankByScores_remove2
    s1 s2 s3

theorem rum3RankByScores_firstChoice_of_top_scores
    {s1 s2 s3 : ℝ}
    (h : rum3TopFirstByScores s1 s2 s3) :
    firstChoice (rum3RankByScores s1 s2 s3) = (0 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_firstChoice_of_top_scores h

theorem rum3RankByScores_top_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (0 : Candidate 1)) :
    rum3TopFirstByScores s1 s2 s3 :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_top_scores_of_firstChoice h

theorem rum3RankByScores_bottom_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1)) :
    rum3BottomFirstByScores s1 s2 s3 :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_bottom_scores_of_firstChoice h

theorem rum3RankByScores_firstChoice_of_bottom_scores_of_noTies
    {s1 s2 s3 : ℝ}
    (hnt : rum3NoTiesByScores s1 s2 s3)
    (h : rum3BottomFirstByScores s1 s2 s3) :
    firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1) :=
   AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_firstChoice_of_bottom_scores_of_noTies
    hnt h

theorem rum3RankByScores_firstChoice_of_strict_bottom_scores
    {s1 s2 s3 : ℝ}
    (h13 : s1 < s3) (h23 : s2 < s3) :
    firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1) :=
   AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_firstChoice_of_strict_bottom_scores
    h13 h23

theorem rum3RankByScores_strict_bottom_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1)) :
    s1 < s3 ∧ s2 < s3 :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_strict_bottom_scores_of_firstChoice h

theorem rum3RankByScores_middle_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (1 : Candidate 1)) :
    rum3MiddleBeatsTopByScores s1 s2 s3 :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_middle_scores_of_firstChoice h

theorem rum3RankByScores_remove0_eq1_imp_score23
    {s1 s2 s3 : ℝ}
    (h :
      bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
        (1 : Candidate 1)) :
    s3 ≤ s2 :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_remove0_eq1_imp_score23 h

theorem rum3RankByScores_remove1_ne0_imp_score13
    {s1 s2 s3 : ℝ}
    (h :
      ¬ bestRemainingAfter (rum3RankByScores s1 s2 s3) (1 : Candidate 1) =
        (0 : Candidate 1)) :
    s1 < s3 :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_remove1_ne0_imp_score13 h

theorem rum3RankByScores_remove1_eq0_of_score31
    {s1 s2 s3 : ℝ} (h31 : s3 ≤ s1) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (1 : Candidate 1) =
      (0 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_remove1_eq0_of_score31 h31

theorem rum3RankByScores_remove0_ne1_of_score23_lt
    {s1 s2 s3 : ℝ} (h23 : s2 < s3) :
    ¬ bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
      (1 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_remove0_ne1_of_score23_lt h23

theorem rum3RankByScores_remove0_eq2_imp_score23_lt
    {s1 s2 s3 : ℝ}
    (h :
      bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
        (2 : Candidate 1)) :
    s2 < s3 :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_remove0_eq2_imp_score23_lt h

theorem rum3RankByScores_remove0_eq1_of_score32
    {s1 s2 s3 : ℝ} (h32 : s3 ≤ s2) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
      (1 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_remove0_eq1_of_score32 h32

theorem rum3RankByScores_remove2_eq1_imp_score12_lt
    {s1 s2 s3 : ℝ}
    (h :
      bestRemainingAfter (rum3RankByScores s1 s2 s3) (2 : Candidate 1) =
        (1 : Candidate 1)) :
    s1 < s2 :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_remove2_eq1_imp_score12_lt h

theorem rum3RankByScores_remove2_eq0_of_score21
    {s1 s2 s3 : ℝ} (h21 : s2 ≤ s1) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (2 : Candidate 1) =
      (0 : Candidate 1) :=  AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores_remove2_eq0_of_score21 h21

/--
For a concrete three-score RUM realization, after removing `x₁`, the best
remaining candidate is `x₂` exactly when `x₂`'s realized score weakly beats
`x₃`'s realized score.
-/
theorem rum3RankByScoreFns_remove0_eq1_iff
    {Ω : Type*} {r1 r2 r3 : Ω → ℝ} (ω : Ω) :
    bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω) (0 : Candidate 1) =
        (1 : Candidate 1) ↔
      r3 ω ≤ r2 ω := by
  by_cases h32 : r3 ω ≤ r2 ω
  · simp [rum3RankByScoreFns, h32]
  · simp [rum3RankByScoreFns, h32]

/--
For a concrete three-score RUM realization, after removing `x₂`, the best
remaining candidate is `x₁` exactly when `x₁`'s realized score weakly beats
`x₃`'s realized score.
-/
theorem rum3RankByScoreFns_remove1_eq0_iff
    {Ω : Type*} {r1 r2 r3 : Ω → ℝ} (ω : Ω) :
    bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω) (1 : Candidate 1) =
        (0 : Candidate 1) ↔
      r3 ω ≤ r1 ω := by
  by_cases h31 : r3 ω ≤ r1 ω
  · simp [rum3RankByScoreFns, h31]
  · simp [rum3RankByScoreFns, h31]

/--
For a concrete three-score RUM realization, after removing `x₃`, the best
remaining candidate is `x₁` exactly when `x₁`'s realized score weakly beats
`x₂`'s realized score.
-/
theorem rum3RankByScoreFns_remove2_eq0_iff
    {Ω : Type*} {r1 r2 r3 : Ω → ℝ} (ω : Ω) :
    bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω) (2 : Candidate 1) =
        (0 : Candidate 1) ↔
      r2 ω ≤ r1 ω := by
  by_cases h21 : r2 ω ≤ r1 ω
  · simp [rum3RankByScoreFns, h21]
  · simp [rum3RankByScoreFns, h21]

/--
Candidate `x₁` is first in the concrete three-score ranking exactly when its
realized score weakly beats both other realized scores.
-/
theorem rum3RankByScoreFns_first0_iff
    {Ω : Type*} {r1 r2 r3 : Ω → ℝ} (ω : Ω) :
    (0 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω) ↔
      r2 ω ≤ r1 ω ∧ r3 ω ≤ r1 ω := by
  by_cases h0 : r2 ω ≤ r1 ω ∧ r3 ω ≤ r1 ω
  · simp [rum3RankByScoreFns, h0]
  · by_cases h1 : r1 ω < r2 ω ∧ r3 ω ≤ r2 ω
    · simp [rum3RankByScoreFns, h0, h1]
    · simp [rum3RankByScoreFns, h0, h1]

/--
Candidate `x₂` is first in the concrete three-score ranking exactly when its
realized score strictly beats `x₁`'s and weakly beats `x₃`'s.
-/
theorem rum3RankByScoreFns_first1_iff
    {Ω : Type*} {r1 r2 r3 : Ω → ℝ} (ω : Ω) :
    (1 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω) ↔
      r1 ω < r2 ω ∧ r3 ω ≤ r2 ω := by
  by_cases h0 : r2 ω ≤ r1 ω ∧ r3 ω ≤ r1 ω
  · have hnot : ¬ (r1 ω < r2 ω ∧ r3 ω ≤ r2 ω) := by
      intro h
      exact not_lt_of_ge h0.1 h.1
    simp [rum3RankByScoreFns, h0, hnot]
  · by_cases h1 : r1 ω < r2 ω ∧ r3 ω ≤ r2 ω
    · simp [rum3RankByScoreFns, h0, h1]
    · simp [rum3RankByScoreFns, h0, h1]

/--
Candidate `x₃` is first in the concrete three-score ranking exactly when its
realized score strictly beats both higher-valued candidates' realized scores.
-/
theorem rum3RankByScoreFns_first2_iff
    {Ω : Type*} {r1 r2 r3 : Ω → ℝ} (ω : Ω) :
    (2 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω) ↔
      r1 ω < r3 ω ∧ r2 ω < r3 ω := by
  constructor
  · intro h
    exact rum3RankByScores_strict_bottom_scores_of_firstChoice
      (s1 := r1 ω) (s2 := r2 ω) (s3 := r3 ω)
      (by simpa [rum3RankByScoreFns] using h.symm)
  · intro h
    exact
      (rum3RankByScores_firstChoice_of_strict_bottom_scores
        (s1 := r1 ω) (s2 := r2 ω) (s3 := r3 ω) h.1 h.2).symm

/--
Definition-2 source event for shared first choice `x₁`: after translating the
ranking predicates, it is exactly the primitive score event
`r₃ ≤ r₂ ≤ r₁`.
-/
theorem rum3RankByScoreFns_def2_event0_iff
    {Ω : Type*} {r1 r2 r3 : Ω → ℝ} (ω : Ω) :
    (bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω) (0 : Candidate 1) =
          (1 : Candidate 1) ∧
        (0 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω)) ↔
      r3 ω ≤ r2 ω ∧ r2 ω ≤ r1 ω := by
  rw [rum3RankByScoreFns_remove0_eq1_iff,
    rum3RankByScoreFns_first0_iff]
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro h
    exact ⟨h.1, h.2, le_trans h.1 h.2⟩

/--
Definition-2 source event for shared first choice `x₂`: after translating the
ranking predicates, it is exactly the primitive score event
`r₃ ≤ r₁ < r₂`.
-/
theorem rum3RankByScoreFns_def2_event1_iff
    {Ω : Type*} {r1 r2 r3 : Ω → ℝ} (ω : Ω) :
    (bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω) (1 : Candidate 1) =
          (0 : Candidate 1) ∧
        (1 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω)) ↔
      r3 ω ≤ r1 ω ∧ r1 ω < r2 ω := by
  rw [rum3RankByScoreFns_remove1_eq0_iff,
    rum3RankByScoreFns_first1_iff]
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro h
    exact ⟨h.1, h.2, le_trans h.1 (le_of_lt h.2)⟩

/--
Definition-2 source event for shared first choice `x₃`: after translating the
ranking predicates, it is exactly the primitive score event
`r₂ ≤ r₁ < r₃`.
-/
theorem rum3RankByScoreFns_def2_event2_iff
    {Ω : Type*} {r1 r2 r3 : Ω → ℝ} (ω : Ω) :
    (bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω) (2 : Candidate 1) =
          (0 : Candidate 1) ∧
        (2 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω)) ↔
      r2 ω ≤ r1 ω ∧ r1 ω < r3 ω := by
  rw [rum3RankByScoreFns_remove2_eq0_iff,
    rum3RankByScoreFns_first2_iff]
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro h
    exact ⟨h.1, h.2, lt_of_le_of_lt h.1 h.2⟩

/--
The deterministic `swapi` geometry used in Appendix C / Lemma 3 for `i = 2`.

If the original realization is bottom-first (`r₁,r₂ ≤ r₃`) and contraction
makes the middle candidate strictly beat the top candidate while weakly beating
the bottom candidate, then after swapping the top and middle realization
coordinates, the original realization is still bottom-first and the contracted
realization is top-first.
-/
theorem rum3_swap_middle_transition_geometry
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hr13 : r1 ≤ r3) (hr23 : r2 ≤ r3)
    (hc12 : rumContractScore t x1 r1 < rumContractScore t x2 r2)
    (hc32 : rumContractScore t x3 r3 ≤ rumContractScore t x2 r2) :
    r2 ≤ r3 ∧ r1 ≤ r3 ∧
      rumContractScore t x2 r1 ≤ rumContractScore t x1 r2 ∧
      rumContractScore t x3 r3 ≤ rumContractScore t x1 r2 :=
   AppliedModelingLib.Probability.rum3_swap_middle_transition_geometry
    ht0 ht1 hx12 hr13 hr23 hc12 hc32

/--
If the middle candidate beats the top candidate after contraction, then its
original realization score is strictly higher than the top candidate's score.
-/
theorem rum3_swap_middle_base_score_lt
    {t x1 x2 r1 r2 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hc12 :
      rumContractScore t x1 r1 <
        rumContractScore t x2 r2) :
    r1 < r2 :=
   AppliedModelingLib.Probability.rum3_swap_middle_base_score_lt
    ht0 ht1 hx12 hc12

theorem weaklyWellOrderedNoise_swap_middle_density_le
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 r1 r2 : ℝ} (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) ≤ f (r2 - x1) * f (r1 - x2) :=
   AppliedModelingLib.Probability.weaklyWellOrderedNoise_swap_middle_density_le
    hf hx12 hr12

theorem strictlyWellOrderedNoise_swap_middle_density_lt
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 r1 r2 : ℝ} (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) < f (r2 - x1) * f (r1 - x2) :=
   AppliedModelingLib.Probability.strictlyWellOrderedNoise_swap_middle_density_lt
    hf hx12 hr12

/--
Pointwise three-coordinate density comparison for swapping the top and middle
coordinates in a wrong `x₁`/`x₂` pairwise realization.
-/
theorem weaklyWellOrderedNoise_swap12_density3_le
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 ≤ f (r3 - x3))
    (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) ≤
      f (r2 - x1) * f (r1 - x2) * f (r3 - x3) :=
   AppliedModelingLib.Probability.weaklyWellOrderedNoise_swap12_density3_le
    hf hctx hx12 hr12

/--
Strict three-coordinate density comparison for swapping the top and middle
coordinates in a wrong `x₁`/`x₂` pairwise realization.
-/
theorem strictlyWellOrderedNoise_swap12_density3_lt
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 < f (r3 - x3))
    (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) <
      f (r2 - x1) * f (r1 - x2) * f (r3 - x3) :=
   AppliedModelingLib.Probability.strictlyWellOrderedNoise_swap12_density3_lt
    hf hctx hx12 hr12

/--
Pointwise three-coordinate density comparison for swapping the middle and
bottom coordinates in a wrong `x₂`/`x₃` pairwise realization.
-/
theorem weaklyWellOrderedNoise_swap23_density3_le
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 ≤ f (r1 - x1))
    (hx23 : x3 < x2) (hr23 : r2 < r3) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) ≤
      f (r1 - x1) * f (r3 - x2) * f (r2 - x3) :=
   AppliedModelingLib.Probability.weaklyWellOrderedNoise_swap23_density3_le
    hf hctx hx23 hr23

/--
Strict three-coordinate density comparison for swapping the middle and bottom
coordinates in a wrong `x₂`/`x₃` pairwise realization.
-/
theorem strictlyWellOrderedNoise_swap23_density3_lt
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 < f (r1 - x1))
    (hx23 : x3 < x2) (hr23 : r2 < r3) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) <
      f (r1 - x1) * f (r3 - x2) * f (r2 - x3) :=
   AppliedModelingLib.Probability.strictlyWellOrderedNoise_swap23_density3_lt
    hf hctx hx23 hr23

/--
Three-coordinate RUM score density as an `ℝ≥0∞` density for `withDensity`.

This is the continuous analogue of the finite density-product formula used by
the sample-space endpoints.
-/
noncomputable def rum3ScoreDensityENN {Ω : Type*} (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) : Ω → ENNReal := AppliedModelingLib.Probability.rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3

/-- Measurability of the three-coordinate score density. -/
theorem rum3ScoreDensityENN_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    {f : ℝ → ℝ} (hf : Measurable f)
    (x1 x2 x3 : ℝ) {r1 r2 r3 : Ω → ℝ}
    (hr1 : Measurable r1) (hr2 : Measurable r2) (hr3 : Measurable r3) :
    Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) :=
   AppliedModelingLib.Probability.rum3ScoreDensityENN_measurable
    hf x1 x2 x3 hr1 hr2 hr3

/-- Positive noise density makes the three-coordinate score density nonzero. -/
theorem rum3ScoreDensityENN_ne_zero_of_noise_pos
    {Ω : Type*} {f : ℝ → ℝ}
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hpos : ∀ z : ℝ, 0 < f z) (ω : Ω) :
    rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3 ω ≠ 0 :=
   AppliedModelingLib.Probability.rum3ScoreDensityENN_ne_zero_of_noise_pos
    x1 x2 x3 r1 r2 r3 hpos ω

/--
Positive base mass of a region remains positive under a strictly positive
three-coordinate score density.
-/
theorem rum3ScoreDensity_withDensity_measure_ne_zero_of_base_measure_ne_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) {f : ℝ → ℝ}
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hpos : ∀ z : ℝ, 0 < f z)
    {s : Set Ω} (hs : MeasurableSet s) (hbase : base s ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) s ≠ 0 :=
  AppliedModelingLib.Probability.rum3ScoreDensity_withDensity_measure_ne_zero_of_base_measure_ne_zero
    base x1 x2 x3 r1 r2 r3 hD hpos hs hbase

/-- Normalization criterion for the three-coordinate score density. -/
theorem rum3ScoreDensity_isProbabilityMeasure_of_lintegral_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hD :
      ∫⁻ ω, (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂base = 1) :
    IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)) :=
  AppliedModelingLib.Probability.rum3ScoreDensity_isProbabilityMeasure_of_lintegral_eq_one
    base f x1 x2 x3 r1 r2 r3 hD

/--
Any source-region density integral is finite once the full score density is
normalized.
-/
theorem rum3ScoreDensity_setLIntegral_ne_top_of_lintegral_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hD :
      ∫⁻ ω, (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂base = 1)
    (s : Set Ω) :
    (∫⁻ ω in s, (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂base) ≠ ∞ :=
  AppliedModelingLib.Probability.rum3ScoreDensity_setLIntegral_ne_top_of_lintegral_eq_one
    base f x1 x2 x3 r1 r2 r3 hD s

/--
Concrete three-coordinate score space for continuous three-candidate RUMs.

The nesting `((r₁, r₂), r₃)` is chosen to line up with mathlib's binary product
measure lemmas.
-/
abbrev RUM3ScoreSpace := (ℝ × ℝ) × ℝ

/-- First realized score coordinate. -/
def rum3Score1 (ω : RUM3ScoreSpace) : ℝ := ω.1.1

/-- Second realized score coordinate. -/
def rum3Score2 (ω : RUM3ScoreSpace) : ℝ := ω.1.2

/-- Third realized score coordinate. -/
def rum3Score3 (ω : RUM3ScoreSpace) : ℝ := ω.2

/-- Open rectangular box in the concrete three-score space. -/
def rum3ScoreOpenBox
    (a1 b1 a2 b2 a3 b3 : ℝ) : Set RUM3ScoreSpace := ((Set.Ioo a1 b1).prod (Set.Ioo a2 b2)).prod (Set.Ioo a3 b3)

theorem rum3ScoreOpenBox_isOpen
    (a1 b1 a2 b2 a3 b3 : ℝ) :
    IsOpen (rum3ScoreOpenBox a1 b1 a2 b2 a3 b3) := (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo

theorem rum3ScoreOpenBox_nonempty
    {a1 b1 a2 b2 a3 b3 : ℝ}
    (h1 : a1 < b1) (h2 : a2 < b2) (h3 : a3 < b3) :
    (rum3ScoreOpenBox a1 b1 a2 b2 a3 b3).Nonempty := by
  refine ⟨(((a1 + b1) / 2, (a2 + b2) / 2), (a3 + b3) / 2), ?_⟩
  change
    (((a1 + b1) / 2, (a2 + b2) / 2) ∈
        (Set.Ioo a1 b1).prod (Set.Ioo a2 b2)) ∧
      (a3 + b3) / 2 ∈ Set.Ioo a3 b3
  constructor
  · constructor
    · constructor <;> linarith
    · constructor <;> linarith
  · constructor <;> linarith

theorem rum3ScoreOpenBox_volume_ne_zero
    {a1 b1 a2 b2 a3 b3 : ℝ}
    (h1 : a1 < b1) (h2 : a2 < b2) (h3 : a3 < b3) :
    (volume : Measure RUM3ScoreSpace)
      (rum3ScoreOpenBox a1 b1 a2 b2 a3 b3) ≠ 0 :=
  (rum3ScoreOpenBox_isOpen a1 b1 a2 b2 a3 b3).measure_ne_zero
    (volume : Measure RUM3ScoreSpace)
    (rum3ScoreOpenBox_nonempty h1 h2 h3)

theorem rum3Score_volume_ne_zero_of_openBox_subset
    {s : Set RUM3ScoreSpace} {a1 b1 a2 b2 a3 b3 : ℝ}
    (hsubset : rum3ScoreOpenBox a1 b1 a2 b2 a3 b3 ⊆ s)
    (h1 : a1 < b1) (h2 : a2 < b2) (h3 : a3 < b3) :
    (volume : Measure RUM3ScoreSpace) s ≠ 0 := by
  have hbox_ne :
      (volume : Measure RUM3ScoreSpace)
        (rum3ScoreOpenBox a1 b1 a2 b2 a3 b3) ≠ 0 :=
    rum3ScoreOpenBox_volume_ne_zero h1 h2 h3
  exact ne_of_gt
    (lt_of_lt_of_le hbox_ne.bot_lt (measure_mono hsubset))

/-- The first concrete score coordinate is measurable. -/
theorem rum3Score1_measurable : Measurable rum3Score1 := measurable_fst.fst

/-- The second concrete score coordinate is measurable. -/
theorem rum3Score2_measurable : Measurable rum3Score2 := measurable_fst.snd

/-- The third concrete score coordinate is measurable. -/
theorem rum3Score3_measurable : Measurable rum3Score3 := measurable_snd

/-- Measurability of the concrete three-score density. -/
theorem rum3ScoreDensityENN_measurable_scoreSpace
    {f : ℝ → ℝ} (hf : Measurable f) (x1 x2 x3 : ℝ) :
    Measurable
      (rum3ScoreDensityENN f x1 x2 x3 rum3Score1 rum3Score2 rum3Score3) :=
  rum3ScoreDensityENN_measurable hf x1 x2 x3
    rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable

/-- The normalized Gaussian RUM score density factors as the product of the
three corresponding one-dimensional Gaussian densities. -/
theorem rum3ScoreDensityENN_gaussian_zero_eq_prod
    (x1 x2 x3 : ℝ) (ω : RUM3ScoreSpace) :
    rum3ScoreDensityENN (theorem8GaussianPDF 0) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3 ω =
      ENNReal.ofReal (theorem8GaussianPDF x1 (rum3Score1 ω)) *
        ENNReal.ofReal (theorem8GaussianPDF x2 (rum3Score2 ω)) *
          ENNReal.ofReal (theorem8GaussianPDF x3 (rum3Score3 ω)) := by
  unfold rum3ScoreDensityENN AppliedModelingLib.Probability.rum3ScoreDensityENN
  rw [theorem8GaussianPDF_zero_sub_eq x1 (rum3Score1 ω),
    theorem8GaussianPDF_zero_sub_eq x2 (rum3Score2 ω),
    theorem8GaussianPDF_zero_sub_eq x3 (rum3Score3 ω)]
  rw [ENNReal.ofReal_mul
    (mul_nonneg (theorem8GaussianPDF_nonneg x1 (rum3Score1 ω))
      (theorem8GaussianPDF_nonneg x2 (rum3Score2 ω)))]
  rw [ENNReal.ofReal_mul
    (theorem8GaussianPDF_nonneg x1 (rum3Score1 ω))]

/-- The concrete three-score Gaussian RUM density is normalized on `ℝ³`. -/
theorem rum3ScoreDensityENN_gaussian_zero_lintegral_eq_one
    (x1 x2 x3 : ℝ) :
    ∫⁻ ω : RUM3ScoreSpace,
        (rum3ScoreDensityENN (theorem8GaussianPDF 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3) ω
          ∂(volume : Measure RUM3ScoreSpace) = 1 := by
  let f1 : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (theorem8GaussianPDF x1 z)
  let f2 : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (theorem8GaussianPDF x2 z)
  let f3 : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (theorem8GaussianPDF x3 z)
  have hf1 : AEMeasurable f1 (volume : Measure ℝ) := by
    exact ((theorem8GaussianPDF_measurable x1).ennreal_ofReal).aemeasurable
  have hf2 : AEMeasurable f2 (volume : Measure ℝ) := by
    exact ((theorem8GaussianPDF_measurable x2).ennreal_ofReal).aemeasurable
  have hf3 : AEMeasurable f3 (volume : Measure ℝ) := by
    exact ((theorem8GaussianPDF_measurable x3).ennreal_ofReal).aemeasurable
  have hf12 :
      AEMeasurable
        (fun z : ℝ × ℝ => f1 z.1 * f2 z.2)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    fun_prop
  have h12 :
      (∫⁻ z : ℝ × ℝ, f1 z.1 * f2 z.2
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) = 1 := by
    rw [lintegral_prod_mul hf1 hf2]
    simp [f1, f2, theorem8GaussianPDF_lintegral_eq_one]
  calc
    ∫⁻ ω : RUM3ScoreSpace,
        (rum3ScoreDensityENN (theorem8GaussianPDF 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3) ω
          ∂(volume : Measure RUM3ScoreSpace)
        =
      ∫⁻ z : (ℝ × ℝ) × ℝ,
        (f1 z.1.1 * f2 z.1.2) * f3 z.2
          ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
            (volume : Measure ℝ)) := by
          simp [RUM3ScoreSpace, Measure.volume_eq_prod, f1, f2, f3,
            rum3Score1, rum3Score2, rum3Score3,
            rum3ScoreDensityENN_gaussian_zero_eq_prod]
    _ =
      (∫⁻ z : ℝ × ℝ, f1 z.1 * f2 z.2
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) *
        ∫⁻ z : ℝ, f3 z ∂(volume : Measure ℝ) := by
          rw [lintegral_prod_mul hf12 hf3]
    _ = 1 := by
      simp [h12, f3, theorem8GaussianPDF_lintegral_eq_one]

/--
The concrete three-score Gaussian RUM law is the binary-product law of the
three one-dimensional Gaussian score laws at variance `1/2`.
-/
theorem rum3ScoreMeasure_gaussian_zero_eq_prod
    (x1 x2 x3 : ℝ) :
    (volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem8GaussianPDF 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3)
      =
      ((ProbabilityTheory.gaussianReal x1 (1 / 2 : ℝ≥0)).prod
        (ProbabilityTheory.gaussianReal x2 (1 / 2 : ℝ≥0))).prod
          (ProbabilityTheory.gaussianReal x3 (1 / 2 : ℝ≥0)) := by
  let f1 : ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (theorem8GaussianPDF x1 z)
  let f2 : ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (theorem8GaussianPDF x2 z)
  let f3 : ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (theorem8GaussianPDF x3 z)
  have hf1 : Measurable f1 :=
    (theorem8GaussianPDF_measurable x1).ennreal_ofReal
  have hf2 : Measurable f2 :=
    (theorem8GaussianPDF_measurable x2).ennreal_ofReal
  have hf3 : Measurable f3 :=
    (theorem8GaussianPDF_measurable x3).ennreal_ofReal
  have hf12 : Measurable (fun z : ℝ × ℝ => f1 z.1 * f2 z.2) := by
    fun_prop
  have hvar : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  have hdens :
      rum3ScoreDensityENN (theorem8GaussianPDF 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3 =
        (fun z : RUM3ScoreSpace => (f1 z.1.1 * f2 z.1.2) * f3 z.2) := by
    funext z
    simp [f1, f2, f3, rum3Score1, rum3Score2, rum3Score3,
      rum3ScoreDensityENN_gaussian_zero_eq_prod]
  have hgauss1 :
      ProbabilityTheory.gaussianPDF x1 (1 / 2 : ℝ≥0) = f1 := by
    funext z
    simp [f1, theorem8GaussianPDF_ofReal_eq_gaussianPDF_half]
  have hgauss2 :
      ProbabilityTheory.gaussianPDF x2 (1 / 2 : ℝ≥0) = f2 := by
    funext z
    simp [f2, theorem8GaussianPDF_ofReal_eq_gaussianPDF_half]
  have hgauss3 :
      ProbabilityTheory.gaussianPDF x3 (1 / 2 : ℝ≥0) = f3 := by
    funext z
    simp [f3, theorem8GaussianPDF_ofReal_eq_gaussianPDF_half]
  calc
    (volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem8GaussianPDF 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3)
        =
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
            (volume : Measure ℝ)).withDensity
        (fun z : (ℝ × ℝ) × ℝ => (f1 z.1.1 * f2 z.1.2) * f3 z.2) := by
          rw [hdens]
          simp [RUM3ScoreSpace, Measure.volume_eq_prod]
    _ = ((ProbabilityTheory.gaussianReal x1 (1 / 2 : ℝ≥0)).prod
        (ProbabilityTheory.gaussianReal x2 (1 / 2 : ℝ≥0))).prod
          (ProbabilityTheory.gaussianReal x3 (1 / 2 : ℝ≥0)) := by
          rw [ProbabilityTheory.gaussianReal_of_var_ne_zero x1 hvar,
            ProbabilityTheory.gaussianReal_of_var_ne_zero x2 hvar,
            ProbabilityTheory.gaussianReal_of_var_ne_zero x3 hvar]
          rw [hgauss1, hgauss2, hgauss3]
          change (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
              (volume : Measure ℝ)).withDensity
              (fun z : (ℝ × ℝ) × ℝ => (f1 z.1.1 * f2 z.1.2) * f3 z.2) =
            (((volume : Measure ℝ).withDensity f1).prod
              ((volume : Measure ℝ).withDensity f2)).prod
                ((volume : Measure ℝ).withDensity f3)
          rw [prod_withDensity hf1 hf2]
          rw [prod_withDensity hf12 hf3]

/--
The concrete `((score₁, score₂), score₃)` Gaussian score law is the
prod-association pullback of the Definition-2 grouped score law
`(score₁, (score₂, score₃))`.
-/
theorem rum3ScoreMeasure_gaussian_zero_prodAssoc_measurePreserving
    (x1 x2 x3 : ℝ) :
    MeasurePreserving
      (MeasurableEquiv.prodAssoc : RUM3ScoreSpace ≃ᵐ
        Theorem8GaussianDefinition2ScoreSpace)
      ((volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem8GaussianPDF 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3))
      (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3) := by
  let μ1 := ProbabilityTheory.gaussianReal x1 (1 / 2 : ℝ≥0)
  let μ2 := ProbabilityTheory.gaussianReal x2 (1 / 2 : ℝ≥0)
  let μ3 := ProbabilityTheory.gaussianReal x3 (1 / 2 : ℝ≥0)
  haveI : SFinite μ1 := by
    dsimp [μ1]
    infer_instance
  haveI : SFinite μ2 := by
    dsimp [μ2]
    infer_instance
  haveI : SFinite μ3 := by
    dsimp [μ3]
    infer_instance
  have hprod : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ))
      ((μ1.prod μ2).prod μ3) (μ1.prod (μ2.prod μ3)) :=
    MeasureTheory.measurePreserving_prodAssoc μ1 μ2 μ3
  simpa [RUM3ScoreSpace, Theorem8GaussianDefinition2ScoreSpace,
    theorem8GaussianDefinition2ScoreMeasure, theorem8GaussianPairMeasure,
    rum3ScoreMeasure_gaussian_zero_eq_prod x1 x2 x3,
    μ1, μ2, μ3] using hprod

/-- A zero-mean Laplace noise draw around value `μ` is the Laplace density
with mean `μ` in the score coordinate. -/
theorem theorem7LaplacePDF_zero_sub_eq (lam μ x : ℝ) :
    theorem7LaplacePDF lam 0 (x - μ) = theorem7LaplacePDF lam μ x := by
  simp [theorem7LaplacePDF]

/-- The normalized Laplacian RUM score density factors as the product of the
three corresponding one-dimensional Laplace densities. -/
theorem rum3ScoreDensityENN_laplace_zero_eq_prod
    {lam : ℝ} (hlam : 0 ≤ lam) (x1 x2 x3 : ℝ) (ω : RUM3ScoreSpace) :
    rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3 ω =
      ENNReal.ofReal (theorem7LaplacePDF lam x1 (rum3Score1 ω)) *
        ENNReal.ofReal (theorem7LaplacePDF lam x2 (rum3Score2 ω)) *
          ENNReal.ofReal (theorem7LaplacePDF lam x3 (rum3Score3 ω)) := by
  unfold rum3ScoreDensityENN AppliedModelingLib.Probability.rum3ScoreDensityENN
  rw [theorem7LaplacePDF_zero_sub_eq lam x1 (rum3Score1 ω),
    theorem7LaplacePDF_zero_sub_eq lam x2 (rum3Score2 ω),
    theorem7LaplacePDF_zero_sub_eq lam x3 (rum3Score3 ω)]
  rw [ENNReal.ofReal_mul
    (mul_nonneg
      (theorem7LaplacePDF_nonneg (lam := lam) (μ := x1)
        (x := rum3Score1 ω) hlam)
      (theorem7LaplacePDF_nonneg (lam := lam) (μ := x2)
        (x := rum3Score2 ω) hlam))]
  rw [ENNReal.ofReal_mul
    (theorem7LaplacePDF_nonneg (lam := lam) (μ := x1)
      (x := rum3Score1 ω) hlam)]

/-- The concrete three-score Laplace RUM density is normalized on `ℝ³`. -/
theorem rum3ScoreDensityENN_laplace_zero_lintegral_eq_one
    {lam : ℝ} (hlam : 0 < lam) (x1 x2 x3 : ℝ) :
    ∫⁻ ω : RUM3ScoreSpace,
        (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3) ω
          ∂(volume : Measure RUM3ScoreSpace) = 1 := by
  let f1 : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (theorem7LaplacePDF lam x1 z)
  let f2 : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (theorem7LaplacePDF lam x2 z)
  let f3 : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (theorem7LaplacePDF lam x3 z)
  have hf1 : AEMeasurable f1 (volume : Measure ℝ) := by
    exact ((theorem7LaplacePDF_measurable lam x1).ennreal_ofReal).aemeasurable
  have hf2 : AEMeasurable f2 (volume : Measure ℝ) := by
    exact ((theorem7LaplacePDF_measurable lam x2).ennreal_ofReal).aemeasurable
  have hf3 : AEMeasurable f3 (volume : Measure ℝ) := by
    exact ((theorem7LaplacePDF_measurable lam x3).ennreal_ofReal).aemeasurable
  have hf12 :
      AEMeasurable
        (fun z : ℝ × ℝ => f1 z.1 * f2 z.2)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    fun_prop
  have h12 :
      (∫⁻ z : ℝ × ℝ, f1 z.1 * f2 z.2
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) = 1 := by
    rw [lintegral_prod_mul hf1 hf2]
    simp [f1, f2, theorem7LaplacePDF_lintegral_eq_one, hlam]
  calc
    ∫⁻ ω : RUM3ScoreSpace,
        (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3) ω
          ∂(volume : Measure RUM3ScoreSpace)
        =
      ∫⁻ z : (ℝ × ℝ) × ℝ,
        (f1 z.1.1 * f2 z.1.2) * f3 z.2
          ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
            (volume : Measure ℝ)) := by
          simp [RUM3ScoreSpace, Measure.volume_eq_prod, f1, f2, f3,
            rum3Score1, rum3Score2, rum3Score3,
            rum3ScoreDensityENN_laplace_zero_eq_prod (le_of_lt hlam)]
    _ =
      (∫⁻ z : ℝ × ℝ, f1 z.1 * f2 z.2
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) *
        ∫⁻ z : ℝ, f3 z ∂(volume : Measure ℝ) := by
          rw [lintegral_prod_mul hf12 hf3]
    _ = 1 := by
      simp [h12, f3, theorem7LaplacePDF_lintegral_eq_one, hlam]

/--
The concrete three-score Laplace RUM law is the binary-product law of the
three one-dimensional Laplace score laws.
-/
theorem rum3ScoreMeasure_laplace_zero_eq_prod
    {lam : ℝ} (hlam : 0 < lam) (x1 x2 x3 : ℝ) :
    (volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3)
      =
      ((theorem7LaplaceMeasure lam x1).prod
        (theorem7LaplaceMeasure lam x2)).prod
          (theorem7LaplaceMeasure lam x3) := by
  let f1 : ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (theorem7LaplacePDF lam x1 z)
  let f2 : ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (theorem7LaplacePDF lam x2 z)
  let f3 : ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (theorem7LaplacePDF lam x3 z)
  have hf1 : Measurable f1 :=
    (theorem7LaplacePDF_measurable lam x1).ennreal_ofReal
  have hf2 : Measurable f2 :=
    (theorem7LaplacePDF_measurable lam x2).ennreal_ofReal
  have hf3 : Measurable f3 :=
    (theorem7LaplacePDF_measurable lam x3).ennreal_ofReal
  have hf12 : Measurable (fun z : ℝ × ℝ => f1 z.1 * f2 z.2) := by
    fun_prop
  have hdens :
      rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3 =
        (fun z : RUM3ScoreSpace => (f1 z.1.1 * f2 z.1.2) * f3 z.2) := by
    funext z
    simp [f1, f2, f3, rum3Score1, rum3Score2, rum3Score3,
      rum3ScoreDensityENN_laplace_zero_eq_prod (le_of_lt hlam)]
  calc
    (volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3)
        =
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
            (volume : Measure ℝ)).withDensity
        (fun z : (ℝ × ℝ) × ℝ => (f1 z.1.1 * f2 z.1.2) * f3 z.2) := by
          rw [hdens]
          simp [RUM3ScoreSpace, Measure.volume_eq_prod]
    _ = ((theorem7LaplaceMeasure lam x1).prod
        (theorem7LaplaceMeasure lam x2)).prod
          (theorem7LaplaceMeasure lam x3) := by
          rw [theorem7LaplaceMeasure, theorem7LaplaceMeasure,
            theorem7LaplaceMeasure]
          rw [prod_withDensity hf1 hf2]
          rw [prod_withDensity hf12 hf3]

/--
The concrete `((score₁, score₂), score₃)` Laplace score law is the
prod-association pullback of the Definition-2 grouped score law
`(score₁, (score₂, score₃))`.
-/
theorem rum3ScoreMeasure_laplace_zero_prodAssoc_measurePreserving
    {lam : ℝ} (hlam : 0 < lam) (x1 x2 x3 : ℝ) :
    MeasurePreserving
      (MeasurableEquiv.prodAssoc : RUM3ScoreSpace ≃ᵐ
        Theorem7LaplacianDefinition2ScoreSpace)
      ((volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3))
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3) := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ2 := theorem7LaplaceMeasure lam x2
  let μ3 := theorem7LaplaceMeasure lam x3
  haveI : SFinite μ1 := by
    dsimp [μ1, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ2 := by
    dsimp [μ2, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ3 := by
    dsimp [μ3, theorem7LaplaceMeasure]
    infer_instance
  have hprod : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ))
      ((μ1.prod μ2).prod μ3) (μ1.prod (μ2.prod μ3)) :=
    MeasureTheory.measurePreserving_prodAssoc μ1 μ2 μ3
  simpa [RUM3ScoreSpace, Theorem7LaplacianDefinition2ScoreSpace,
    theorem7LaplacianDefinition2ScoreMeasure, theorem7LaplacianPairMeasure,
    rum3ScoreMeasure_laplace_zero_eq_prod (lam := lam) hlam x1 x2 x3,
    μ1, μ2, μ3] using hprod

/--
In the grouped Definition-2 Laplace score law, the `score₂` beats `score₃`
event is exactly the two-score Laplace winner event for means `(x₂,x₃)`.
-/
theorem theorem7LaplacianDefinition2_pairWinner23_measureProb_eq
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) :
    measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
      (fun ω =>
        theorem7LaplacianDefinition2Score3 ω ≤
          theorem7LaplacianDefinition2Score2 ω)
    =
      (theorem7LaplacianPairMeasure lam x2 x3
        theorem7LaplacianPairWinnerEvent).toReal := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ23 := theorem7LaplacianPairMeasure lam x2 x3
  let ν := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  haveI : IsProbabilityMeasure μ1 :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := x1) hlam⟩
  haveI : SFinite μ23 := by
    dsimp [μ23, theorem7LaplacianPairMeasure, theorem7LaplaceMeasure]
    infer_instance
  have hν_eq : ν = μ1.prod μ23 := by rfl
  let C : Set Theorem7LaplacianDefinition2ScoreSpace :=
    {ω |
      theorem7LaplacianDefinition2Score3 ω ≤
        theorem7LaplacianDefinition2Score2 ω}
  have hC_set : C = Set.univ ×ˢ theorem7LaplacianPairWinnerEvent := by
    ext ω
    simp [C, theorem7LaplacianPairWinnerEvent,
      theorem7LaplacianDefinition2Score2,
      theorem7LaplacianDefinition2Score3]
  unfold measureProb
  change (ν C).toReal = (μ23 theorem7LaplacianPairWinnerEvent).toReal
  rw [hν_eq, hC_set, Measure.prod_prod]
  simp [μ1]

/--
In the concrete `ℝ³` Laplace score law, the `score₂` beats `score₃` marginal
is the corresponding two-score Laplace winner probability.
-/
theorem rum3ScoreMeasure_laplace_zero_pairWinner23_measureProb_eq
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) :
    measureProb
      ((volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3))
      (fun ω => rum3Score3 ω ≤ rum3Score2 ω)
    =
      (theorem7LaplacianPairMeasure lam x2 x3
        theorem7LaplacianPairWinnerEvent).toReal := by
  let μ :=
    (volume : Measure RUM3ScoreSpace).withDensity
      (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3)
  let ν := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  let e : RUM3ScoreSpace ≃ᵐ Theorem7LaplacianDefinition2ScoreSpace :=
    MeasurableEquiv.prodAssoc
  have he : MeasurePreserving e μ ν := by
    simpa [e, μ, ν] using
      rum3ScoreMeasure_laplace_zero_prodAssoc_measurePreserving
        (lam := lam) hlam x1 x2 x3
  have hpre :
      measureProb μ
          (fun ω =>
            theorem7LaplacianDefinition2Score3 (e ω) ≤
              theorem7LaplacianDefinition2Score2 (e ω)) =
        measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score2 ω) :=
    measureProb_preimage_equiv_of_measurePreserving e he
      (fun ω =>
        theorem7LaplacianDefinition2Score3 ω ≤
          theorem7LaplacianDefinition2Score2 ω)
  calc
    measureProb μ (fun ω => rum3Score3 ω ≤ rum3Score2 ω)
        =
      measureProb μ
          (fun ω =>
            theorem7LaplacianDefinition2Score3 (e ω) ≤
              theorem7LaplacianDefinition2Score2 (e ω)) := by
          rfl
    _ =
      measureProb ν
        (fun ω =>
          theorem7LaplacianDefinition2Score3 ω ≤
            theorem7LaplacianDefinition2Score2 ω) := hpre
    _ =
      (theorem7LaplacianPairMeasure lam x2 x3
        theorem7LaplacianPairWinnerEvent).toReal :=
          theorem7LaplacianDefinition2_pairWinner23_measureProb_eq
            (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam

/-- Concrete top/middle coordinate swap on three-score space. -/
def rum3ScoreSwap12 : RUM3ScoreSpace ≃ᵐ RUM3ScoreSpace := MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl ℝ)

/-- Concrete middle/bottom coordinate swap on three-score space. -/
def rum3ScoreSwap23 : RUM3ScoreSpace ≃ᵐ RUM3ScoreSpace :=
  ((MeasurableEquiv.prodAssoc : RUM3ScoreSpace ≃ᵐ ℝ × (ℝ × ℝ))).trans
    (((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm).trans
      (MeasurableEquiv.prodAssoc.symm))

@[simp] theorem rum3ScoreSwap12_score1 (ω : RUM3ScoreSpace) :
    rum3Score1 (rum3ScoreSwap12 ω) = rum3Score2 ω := rfl

@[simp] theorem rum3ScoreSwap12_score2 (ω : RUM3ScoreSpace) :
    rum3Score2 (rum3ScoreSwap12 ω) = rum3Score1 ω := rfl

@[simp] theorem rum3ScoreSwap12_score3 (ω : RUM3ScoreSpace) :
    rum3Score3 (rum3ScoreSwap12 ω) = rum3Score3 ω := rfl

@[simp] theorem rum3ScoreSwap23_score1 (ω : RUM3ScoreSpace) :
    rum3Score1 (rum3ScoreSwap23 ω) = rum3Score1 ω := rfl

@[simp] theorem rum3ScoreSwap23_score2 (ω : RUM3ScoreSpace) :
    rum3Score2 (rum3ScoreSwap23 ω) = rum3Score3 ω := rfl

@[simp] theorem rum3ScoreSwap23_score3 (ω : RUM3ScoreSpace) :
    rum3Score3 (rum3ScoreSwap23 ω) = rum3Score2 ω := rfl

/-- The concrete top/middle score swap preserves three-dimensional Lebesgue volume. -/
theorem rum3ScoreSwap12_measurePreserving_volume :
    MeasurePreserving rum3ScoreSwap12 (volume : Measure RUM3ScoreSpace) volume := by
  have hpair : MeasurePreserving Prod.swap ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    simpa using
      (Measure.measurePreserving_swap
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
  have hprod : MeasurePreserving (Prod.map Prod.swap id)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) := by
    simpa using hpair.prod (MeasurePreserving.id (volume : Measure ℝ))
  simpa [rum3ScoreSwap12, RUM3ScoreSpace, Measure.volume_eq_prod] using hprod

/--
The concrete top/middle score swap sends the Laplace score law with locations
`(x₁,x₂,x₃)` to the score law with locations `(x₂,x₁,x₃)`.
-/
theorem rum3ScoreMeasure_laplace_zero_swap12_measurePreserving
    {lam : ℝ} (hlam : 0 < lam) (x1 x2 x3 : ℝ) :
    MeasurePreserving rum3ScoreSwap12
      ((volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3))
      ((volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x2 x1 x3
          rum3Score1 rum3Score2 rum3Score3)) := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ2 := theorem7LaplaceMeasure lam x2
  let μ3 := theorem7LaplaceMeasure lam x3
  haveI : SFinite μ1 := by
    dsimp [μ1, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ2 := by
    dsimp [μ2, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ3 := by
    dsimp [μ3, theorem7LaplaceMeasure]
    infer_instance
  have hpair : MeasurePreserving Prod.swap (μ1.prod μ2) (μ2.prod μ1) :=
    Measure.measurePreserving_swap
  have hprod : MeasurePreserving (Prod.map Prod.swap id)
      ((μ1.prod μ2).prod μ3) ((μ2.prod μ1).prod μ3) := by
    simpa using hpair.prod (MeasurePreserving.id μ3)
  simpa [rum3ScoreSwap12, RUM3ScoreSpace,
    rum3ScoreMeasure_laplace_zero_eq_prod (lam := lam) hlam x1 x2 x3,
    rum3ScoreMeasure_laplace_zero_eq_prod (lam := lam) hlam x2 x1 x3,
    μ1, μ2, μ3] using hprod

/-- The concrete middle/bottom score swap preserves three-dimensional Lebesgue volume. -/
theorem rum3ScoreSwap23_measurePreserving_volume :
    MeasurePreserving rum3ScoreSwap23 (volume : Measure RUM3ScoreSpace) volume := by
  have hpair : MeasurePreserving Prod.swap ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    simpa using
      (Measure.measurePreserving_swap
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
  have hinner : MeasurePreserving (Prod.map id Prod.swap)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
    simpa using (MeasurePreserving.id (volume : Measure ℝ)).prod hpair
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : RUM3ScoreSpace ≃ᵐ ℝ × (ℝ × ℝ))
      (volume : Measure RUM3ScoreSpace) (volume : Measure (ℝ × (ℝ × ℝ))) := by
    simpa [RUM3ScoreSpace] using
      (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ))
  have hassoc_symm : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : ℝ × (ℝ × ℝ) ≃ᵐ RUM3ScoreSpace)
      (volume : Measure (ℝ × (ℝ × ℝ))) (volume : Measure RUM3ScoreSpace) :=
    MeasurePreserving.symm
      (MeasurableEquiv.prodAssoc : RUM3ScoreSpace ≃ᵐ ℝ × (ℝ × ℝ)) hassoc
  have htail : MeasurePreserving
      (((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm).trans
        (MeasurableEquiv.prodAssoc.symm) : ℝ × (ℝ × ℝ) ≃ᵐ RUM3ScoreSpace)
      (volume : Measure (ℝ × (ℝ × ℝ))) (volume : Measure RUM3ScoreSpace) :=
    hassoc_symm.comp hinner
  exact htail.comp hassoc

/--
In the concrete `ℝ³` Laplace score law, the `score₁` beats `score₂` marginal
is the corresponding two-score Laplace winner probability.
-/
theorem rum3ScoreMeasure_laplace_zero_pairWinner12_measureProb_eq
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) :
    measureProb
      ((volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3))
      (fun ω => rum3Score2 ω ≤ rum3Score1 ω)
    =
      (theorem7LaplacianPairMeasure lam x1 x2
        theorem7LaplacianPairWinnerEvent).toReal := by
  let μ3 := theorem7LaplaceMeasure lam x3
  let μ12 := theorem7LaplacianPairMeasure lam x1 x2
  let μ :=
    (volume : Measure RUM3ScoreSpace).withDensity
      (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3)
  haveI : SFinite μ3 := by
    dsimp [μ3, theorem7LaplaceMeasure]
    infer_instance
  have hμ3_univ : μ3 Set.univ = 1 :=
    theorem7LaplaceMeasure_univ (lam := lam) (μ := x3) hlam
  let C : Set RUM3ScoreSpace := {ω | rum3Score2 ω ≤ rum3Score1 ω}
  have hC_set : C = theorem7LaplacianPairWinnerEvent ×ˢ Set.univ := by
    ext ω
    simp [C, theorem7LaplacianPairWinnerEvent, rum3Score1, rum3Score2]
  have hμ_eq :
      μ =
        ((theorem7LaplacianPairMeasure lam x1 x2).prod μ3) := by
    dsimp [μ, μ3, theorem7LaplacianPairMeasure]
    rw [rum3ScoreMeasure_laplace_zero_eq_prod (lam := lam) hlam x1 x2 x3]
  unfold measureProb
  change (μ C).toReal = (μ12 theorem7LaplacianPairWinnerEvent).toReal
  rw [hμ_eq]
  change (((theorem7LaplacianPairMeasure lam x1 x2).prod μ3) C).toReal =
    (μ12 theorem7LaplacianPairWinnerEvent).toReal
  rw [hC_set, Measure.prod_prod]
  simp [μ12, μ3, hμ3_univ]

/--
In the concrete `ℝ³` Laplace score law, the `score₁` beats `score₃` marginal
is the corresponding two-score Laplace winner probability.
-/
theorem rum3ScoreMeasure_laplace_zero_pairWinner13_measureProb_eq
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) :
    measureProb
      ((volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3))
      (fun ω => rum3Score3 ω ≤ rum3Score1 ω)
    =
      (theorem7LaplacianPairMeasure lam x1 x3
        theorem7LaplacianPairWinnerEvent).toReal := by
  let μ :=
    (volume : Measure RUM3ScoreSpace).withDensity
      (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3)
  let ν :=
    (volume : Measure RUM3ScoreSpace).withDensity
      (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x2 x1 x3
        rum3Score1 rum3Score2 rum3Score3)
  let e := rum3ScoreSwap12
  have he : MeasurePreserving e μ ν := by
    simpa [e, μ, ν] using
      rum3ScoreMeasure_laplace_zero_swap12_measurePreserving
        (lam := lam) hlam x1 x2 x3
  have hpre :
      measureProb μ (fun ω => rum3Score3 (e ω) ≤ rum3Score2 (e ω)) =
        measureProb ν (fun ω => rum3Score3 ω ≤ rum3Score2 ω) :=
    measureProb_preimage_equiv_of_measurePreserving e he
      (fun ω => rum3Score3 ω ≤ rum3Score2 ω)
  calc
    measureProb μ (fun ω => rum3Score3 ω ≤ rum3Score1 ω)
        = measureProb μ
            (fun ω => rum3Score3 (e ω) ≤ rum3Score2 (e ω)) := by
          rfl
    _ = measureProb ν (fun ω => rum3Score3 ω ≤ rum3Score2 ω) := hpre
    _ =
      (theorem7LaplacianPairMeasure lam x1 x3
        theorem7LaplacianPairWinnerEvent).toReal :=
          rum3ScoreMeasure_laplace_zero_pairWinner23_measureProb_eq
            (lam := lam) (x1 := x2) (x2 := x1) (x3 := x3) hlam

/-- The residual `λ₁ ∧ ¬λ₂` source event has positive Lebesgue volume. -/
theorem rum3Score_lambda13gap_source_volume_ne_zero :
    (volume : Measure RUM3ScoreSpace)
      {ω | bestRemainingAfter
              (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω)
              (0 : Candidate 1) = (1 : Candidate 1) ∧
            ¬ bestRemainingAfter
              (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω)
              (1 : Candidate 1) = (0 : Candidate 1)} ≠ 0 := by
  refine rum3Score_volume_ne_zero_of_openBox_subset
    (a1 := 0) (b1 := 1) (a2 := 4) (b2 := 5) (a3 := 2) (b3 := 3)
    ?_ (by norm_num) (by norm_num) (by norm_num)
  intro ω hω
  rcases hω with ⟨⟨h1, h2⟩, h3⟩
  rcases h1 with ⟨h1lo, h1hi⟩
  rcases h2 with ⟨h2lo, h2hi⟩
  rcases h3 with ⟨h3lo, h3hi⟩
  have h32 : rum3Score3 ω ≤ rum3Score2 ω := by
    dsimp [rum3Score2, rum3Score3] at h2lo h2hi h3lo h3hi ⊢
    linarith
  have h31not : ¬ rum3Score3 ω ≤ rum3Score1 ω := by
    dsimp [rum3Score1, rum3Score3] at h1lo h1hi h3lo h3hi ⊢
    linarith
  constructor
  · simpa [rum3RankByScoreFns, h32]
  · simpa [rum3RankByScoreFns, h31not]

/-- The `x₂`/`x₃` wrong-choice source event has positive Lebesgue volume. -/
theorem rum3Score_lambda23wrong_source_volume_ne_zero :
    (volume : Measure RUM3ScoreSpace)
      {ω | bestRemainingAfter
              (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω)
              (0 : Candidate 1) = (2 : Candidate 1)} ≠ 0 := by
  refine rum3Score_volume_ne_zero_of_openBox_subset
    (a1 := 0) (b1 := 1) (a2 := 0) (b2 := 1) (a3 := 2) (b3 := 3)
    ?_ (by norm_num) (by norm_num) (by norm_num)
  intro ω hω
  rcases hω with ⟨⟨_h1, h2⟩, h3⟩
  rcases h2 with ⟨h2lo, h2hi⟩
  rcases h3 with ⟨h3lo, h3hi⟩
  have h32not : ¬ rum3Score3 ω ≤ rum3Score2 ω := by
    dsimp [rum3Score2, rum3Score3] at h2lo h2hi h3lo h3hi ⊢
    linarith
  simpa [rum3RankByScoreFns] using lt_of_not_ge h32not

/-- The `x₁`/`x₂` wrong-choice source event has positive Lebesgue volume. -/
theorem rum3Score_lambda12wrong_source_volume_ne_zero :
    (volume : Measure RUM3ScoreSpace)
      {ω | bestRemainingAfter
              (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω)
              (2 : Candidate 1) = (1 : Candidate 1)} ≠ 0 := by
  refine rum3Score_volume_ne_zero_of_openBox_subset
    (a1 := 0) (b1 := 1) (a2 := 2) (b2 := 3) (a3 := 0) (b3 := 1)
    ?_ (by norm_num) (by norm_num) (by norm_num)
  intro ω hω
  rcases hω with ⟨⟨h1, h2⟩, _h3⟩
  rcases h1 with ⟨h1lo, h1hi⟩
  rcases h2 with ⟨h2lo, h2hi⟩
  have h21not : ¬ rum3Score2 ω ≤ rum3Score1 ω := by
    dsimp [rum3Score1, rum3Score2] at h1lo h1hi h2lo h2hi ⊢
    linarith
  simpa [rum3RankByScoreFns] using lt_of_not_ge h21not

/-- The exact swapped-top-two source region `[1,0,2]` has positive Lebesgue volume. -/
theorem rum3Score_ranking102_source_volume_ne_zero :
    (volume : Measure RUM3ScoreSpace)
      {ω |
        rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω =
          rum3Ranking102} ≠ 0 := by
  refine rum3Score_volume_ne_zero_of_openBox_subset
    (a1 := 2) (b1 := 3) (a2 := 4) (b2 := 5) (a3 := 0) (b3 := 1)
    ?_ (by norm_num) (by norm_num) (by norm_num)
  intro ω hω
  rcases hω with ⟨⟨h1, h2⟩, h3⟩
  rcases h1 with ⟨h1lo, h1hi⟩
  rcases h2 with ⟨h2lo, _h2hi⟩
  rcases h3 with ⟨_h3lo, h3hi⟩
  have h12 : rum3Score1 ω < rum3Score2 ω := by
    dsimp [rum3Score1, rum3Score2] at h1hi h2lo ⊢
    linarith
  have h31 : rum3Score3 ω ≤ rum3Score1 ω := by
    dsimp [rum3Score1, rum3Score3] at h1lo h3hi ⊢
    linarith
  simpa [rum3RankByScoreFns] using
    rum3RankByScores_eq102_of_order
      (s1 := rum3Score1 ω) (s2 := rum3Score2 ω)
      (s3 := rum3Score3 ω) h12 h31

theorem rum3Score_ranking102_measurableSet :
    MeasurableSet
      {ω : RUM3ScoreSpace |
        rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω =
          rum3Ranking102} := by
  exact measurableSet_eq_fun
    (rum3RankByScoreFns_measurable
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable)
    measurable_const

theorem rum3Score_gaussian_zero_ranking102_measureProb_pos
    (x1 x2 x3 : ℝ) :
    0 <
      measureProb
        ((volume : Measure RUM3ScoreSpace).withDensity
          (rum3ScoreDensityENN (theorem8GaussianPDF 0) x1 x2 x3
            rum3Score1 rum3Score2 rum3Score3))
        (fun ω =>
          rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω =
            rum3Ranking102) := by
  let μ :=
    (volume : Measure RUM3ScoreSpace).withDensity
      (rum3ScoreDensityENN (theorem8GaussianPDF 0) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3)
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact
      rum3ScoreDensity_isProbabilityMeasure_of_lintegral_eq_one
        (volume : Measure RUM3ScoreSpace) (theorem8GaussianPDF 0)
        x1 x2 x3 rum3Score1 rum3Score2 rum3Score3
        (rum3ScoreDensityENN_gaussian_zero_lintegral_eq_one x1 x2 x3)
  have hne : μ {ω |
        rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω =
          rum3Ranking102} ≠ 0 := by
    dsimp [μ]
    exact
      rum3ScoreDensity_withDensity_measure_ne_zero_of_base_measure_ne_zero
        (volume : Measure RUM3ScoreSpace) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3
        (rum3ScoreDensityENN_measurable_scoreSpace
          (theorem8GaussianPDF_measurable 0) x1 x2 x3)
        (fun z => theorem8GaussianPDF_pos 0 z)
        rum3Score_ranking102_measurableSet
        rum3Score_ranking102_source_volume_ne_zero
  exact measureProb_pos_of_measure_ne_zero μ
    (fun ω =>
      rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω =
        rum3Ranking102) hne

theorem rum3Score_laplace_zero_ranking102_measureProb_pos
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) :
    0 <
      measureProb
        ((volume : Measure RUM3ScoreSpace).withDensity
          (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
            rum3Score1 rum3Score2 rum3Score3))
        (fun ω =>
          rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω =
            rum3Ranking102) := by
  let μ :=
    (volume : Measure RUM3ScoreSpace).withDensity
      (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3)
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact
      rum3ScoreDensity_isProbabilityMeasure_of_lintegral_eq_one
        (volume : Measure RUM3ScoreSpace) (theorem7LaplacePDF lam 0)
        x1 x2 x3 rum3Score1 rum3Score2 rum3Score3
        (rum3ScoreDensityENN_laplace_zero_lintegral_eq_one
          (lam := lam) hlam x1 x2 x3)
  have hne : μ {ω |
        rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω =
          rum3Ranking102} ≠ 0 := by
    dsimp [μ]
    exact
      rum3ScoreDensity_withDensity_measure_ne_zero_of_base_measure_ne_zero
        (volume : Measure RUM3ScoreSpace) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3
        (rum3ScoreDensityENN_measurable_scoreSpace
          (theorem7LaplacePDF_measurable lam 0) x1 x2 x3)
        (fun z => theorem7LaplacePDF_pos (lam := lam) (μ := 0) (x := z) hlam)
        rum3Score_ranking102_measurableSet
        rum3Score_ranking102_source_volume_ne_zero
  exact measureProb_pos_of_measure_ne_zero μ
    (fun ω =>
      rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω =
        rum3Ranking102) hne

theorem theorem8GaussianDefinition2_ranking102_measureProb_pos
    (x1 x2 x3 : ℝ) :
    0 <
      measureProb (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (fun ω =>
          rum3RankByScoreFns
            theorem8GaussianDefinition2Score1
            theorem8GaussianDefinition2Score2
            theorem8GaussianDefinition2Score3 ω =
          rum3Ranking102) := by
  let μ :=
    (volume : Measure RUM3ScoreSpace).withDensity
      (rum3ScoreDensityENN (theorem8GaussianPDF 0) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3)
  let ν := theorem8GaussianDefinition2ScoreMeasure x1 x2 x3
  let e : RUM3ScoreSpace ≃ᵐ Theorem8GaussianDefinition2ScoreSpace :=
    MeasurableEquiv.prodAssoc
  have he : MeasurePreserving e μ ν := by
    simpa [e, μ, ν] using
      rum3ScoreMeasure_gaussian_zero_prodAssoc_measurePreserving x1 x2 x3
  have hpre :
      measureProb μ
          (fun ω =>
            rum3RankByScoreFns
              theorem8GaussianDefinition2Score1
              theorem8GaussianDefinition2Score2
              theorem8GaussianDefinition2Score3 (e ω) =
            rum3Ranking102) =
        measureProb ν
          (fun ω =>
            rum3RankByScoreFns
              theorem8GaussianDefinition2Score1
              theorem8GaussianDefinition2Score2
              theorem8GaussianDefinition2Score3 ω =
            rum3Ranking102) :=
    measureProb_preimage_equiv_of_measurePreserving e he
      (fun ω =>
        rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3 ω =
        rum3Ranking102)
  have hconcrete := rum3Score_gaussian_zero_ranking102_measureProb_pos x1 x2 x3
  rw [← hpre]
  simpa [e, rum3RankByScoreFns, theorem8GaussianDefinition2Score1,
    theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3,
    rum3Score1, rum3Score2, rum3Score3] using hconcrete

theorem theorem7LaplacianDefinition2_ranking102_measureProb_pos
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) :
    0 <
      measureProb (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
        (fun ω =>
          rum3RankByScoreFns
            theorem7LaplacianDefinition2Score1
            theorem7LaplacianDefinition2Score2
            theorem7LaplacianDefinition2Score3 ω =
          rum3Ranking102) := by
  let μ :=
    (volume : Measure RUM3ScoreSpace).withDensity
      (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3)
  let ν := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  let e : RUM3ScoreSpace ≃ᵐ Theorem7LaplacianDefinition2ScoreSpace :=
    MeasurableEquiv.prodAssoc
  have he : MeasurePreserving e μ ν := by
    simpa [e, μ, ν] using
      rum3ScoreMeasure_laplace_zero_prodAssoc_measurePreserving
        (lam := lam) hlam x1 x2 x3
  have hpre :
      measureProb μ
          (fun ω =>
            rum3RankByScoreFns
              theorem7LaplacianDefinition2Score1
              theorem7LaplacianDefinition2Score2
              theorem7LaplacianDefinition2Score3 (e ω) =
            rum3Ranking102) =
        measureProb ν
          (fun ω =>
            rum3RankByScoreFns
              theorem7LaplacianDefinition2Score1
              theorem7LaplacianDefinition2Score2
              theorem7LaplacianDefinition2Score3 ω =
            rum3Ranking102) :=
    measureProb_preimage_equiv_of_measurePreserving e he
      (fun ω =>
        rum3RankByScoreFns
          theorem7LaplacianDefinition2Score1
          theorem7LaplacianDefinition2Score2
          theorem7LaplacianDefinition2Score3 ω =
        rum3Ranking102)
  have hconcrete :=
    rum3Score_laplace_zero_ranking102_measureProb_pos
      (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam
  rw [← hpre]
  simpa [e, rum3RankByScoreFns, theorem7LaplacianDefinition2Score1,
    theorem7LaplacianDefinition2Score2, theorem7LaplacianDefinition2Score3,
    rum3Score1, rum3Score2, rum3Score3] using hconcrete

theorem theorem8GaussianDefinition2Std_ranking102_measureProb_pos
    {σ x1 x2 x3 : ℝ} (hσ : 0 < σ) :
    0 <
      measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (fun ω =>
          rum3RankByScoreFns
            theorem8GaussianDefinition2Score1
            theorem8GaussianDefinition2Score2
            theorem8GaussianDefinition2Score3 ω =
          rum3Ranking102) := by
  let c := theorem8GaussianCanonicalScale σ
  let νstd := theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3
  let νcan := theorem8GaussianDefinition2ScoreMeasure
    (c * x1) (c * x2) (c * x3)
  let e := theorem8GaussianDefinition2CanonicalScaleMap σ
  let p : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    rum3RankByScoreFns
      theorem8GaussianDefinition2Score1
      theorem8GaussianDefinition2Score2
      theorem8GaussianDefinition2Score3 ω =
    rum3Ranking102
  have hc : 0 < c := theorem8GaussianCanonicalScale_pos hσ
  have hp : MeasurableSet {ω | p ω} := by
    dsimp [p]
    exact measurableSet_eq_fun
      (rum3RankByScoreFns_measurable
        theorem8GaussianDefinition2Score1_measurable
        theorem8GaussianDefinition2Score2_measurable
        theorem8GaussianDefinition2Score3_measurable)
      measurable_const
  have he : MeasurePreserving e νstd νcan := by
    simpa [e, νstd, νcan, c] using
      theorem8GaussianDefinition2CanonicalScaleMap_measurePreserving
        (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) hσ
  have hpre : measureProb νstd (fun ω => p (e ω)) = measureProb νcan p :=
    measureProb_preimage_of_measurePreserving e he p hp
  have hcan :
      0 < measureProb νcan p := by
    simpa [νcan, c, p] using
      theorem8GaussianDefinition2_ranking102_measureProb_pos
        (c * x1) (c * x2) (c * x3)
  rw [← hpre] at hcan
  unfold measureProb at hcan ⊢
  dsimp [p, e, theorem8GaussianDefinition2CanonicalScaleMap,
    theorem8GaussianDefinition2Score1, theorem8GaussianDefinition2Score2,
    theorem8GaussianDefinition2Score3] at hcan
  change 0 <
    (νstd {ω |
      rum3RankByScores (c * theorem8GaussianDefinition2Score1 ω)
        (c * theorem8GaussianDefinition2Score2 ω)
        (c * theorem8GaussianDefinition2Score3 ω) =
      rum3Ranking102}).toReal at hcan
  have hset :
      {ω |
        rum3RankByScores (c * theorem8GaussianDefinition2Score1 ω)
          (c * theorem8GaussianDefinition2Score2 ω)
          (c * theorem8GaussianDefinition2Score3 ω) =
        rum3Ranking102} =
      {ω |
        rum3RankByScores (theorem8GaussianDefinition2Score1 ω)
          (theorem8GaussianDefinition2Score2 ω)
          (theorem8GaussianDefinition2Score3 ω) =
        rum3Ranking102} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [rum3RankByScores_pos_mul (c := c) hc]
  rw [hset] at hcan
  simpa [νstd, rum3RankByScoreFns] using hcan

/--
For a genuine contraction toward strictly ordered values, there is a positive
volume region where candidate `x₁` is corrected into first place.
-/
theorem rum3Score_correctedTop_volume_ne_zero_of_t_lt_one
    {x1 x2 x3 t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    (volume : Measure RUM3ScoreSpace)
      ({ω | (0 : Candidate 1) =
            firstChoice
              (rum3ContractRankByScoreFns
                t x1 x2 x3 rum3Score1 rum3Score2 rum3Score3 ω)} ∩
        {ω | (0 : Candidate 1) =
            firstChoice
              (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω)}ᶜ) ≠
        0 := by
  let gap : ℝ := (1 - t) * (x1 - x2)
  have hgap : 0 < gap := by
    have h1t : 0 < 1 - t := by linarith
    have hx : 0 < x1 - x2 := sub_pos.mpr hx12
    exact mul_pos h1t hx
  refine rum3Score_volume_ne_zero_of_openBox_subset
    (s :=
      ({ω | (0 : Candidate 1) =
            firstChoice
              (rum3ContractRankByScoreFns
                t x1 x2 x3 rum3Score1 rum3Score2 rum3Score3 ω)} ∩
        {ω | (0 : Candidate 1) =
            firstChoice
              (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω)}ᶜ))
    (a1 := 0) (b1 := gap / 8)
    (a2 := gap / 4) (b2 := 3 * gap / 8)
    (a3 := -1) (b3 := -(1 / 2 : ℝ))
    ?_ (by nlinarith) (by nlinarith) (by norm_num)
  intro ω hω
  rcases hω with ⟨⟨h1, h2⟩, h3⟩
  rcases h1 with ⟨h1lo, h1hi⟩
  rcases h2 with ⟨h2lo, h2hi⟩
  rcases h3 with ⟨h3lo, h3hi⟩
  have hr12 : rum3Score1 ω < rum3Score2 ω := by
    dsimp [rum3Score1, rum3Score2] at h1lo h1hi h2lo h2hi ⊢
    nlinarith
  have hr32 : rum3Score3 ω < rum3Score2 ω := by
    dsimp [rum3Score2, rum3Score3] at h2lo h2hi h3lo h3hi ⊢
    nlinarith [hgap]
  have hr31 : rum3Score3 ω < rum3Score1 ω := by
    dsimp [rum3Score1, rum3Score3] at h1lo h1hi h3lo h3hi ⊢
    nlinarith
  have hrawFirst :
      firstChoice
          (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω) =
        (1 : Candidate 1) := by
    rw [rum3RankByScoreFns, firstChoice_rum3RankByScores]
    have h0 : ¬
        (rum3Score2 ω ≤ rum3Score1 ω ∧ rum3Score3 ω ≤ rum3Score1 ω) := by
      intro h
      exact not_le_of_gt hr12 h.1
    have h1first :
        rum3Score1 ω < rum3Score2 ω ∧ rum3Score3 ω ≤ rum3Score2 ω :=
      ⟨hr12, le_of_lt hr32⟩
    simp [h0, h1first]
  have hrawNotTop :
      ¬ (0 : Candidate 1) =
        firstChoice
          (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω) := by
    rw [hrawFirst]
    decide
  have hcontract21 :
      rumContractScore t x2 (rum3Score2 ω) <
        rumContractScore t x1 (rum3Score1 ω) := by
    have hr_nonneg : 0 ≤ rum3Score2 ω - rum3Score1 ω := by
      linarith
    have hmul_le :
        t * (rum3Score2 ω - rum3Score1 ω) ≤
          1 * (rum3Score2 ω - rum3Score1 ω) :=
      mul_le_mul_of_nonneg_right ht1 hr_nonneg
    have hr_gap : rum3Score2 ω - rum3Score1 ω < gap := by
      dsimp [rum3Score1, rum3Score2] at h1lo h1hi h2lo h2hi ⊢
      nlinarith [hgap]
    have hdiff :
        0 <
          rumContractScore t x1 (rum3Score1 ω) -
            rumContractScore t x2 (rum3Score2 ω) := by
      rw [rumContractScore_sub]
      nlinarith
    linarith
  have hcontract31 :
      rumContractScore t x3 (rum3Score3 ω) <
        rumContractScore t x1 (rum3Score1 ω) :=
    rumContractScore_preserves_strict_order ht0 ht1 (lt_trans hx23 hx12) hr31
  have hbetterFirst :
      firstChoice
          (rum3ContractRankByScoreFns
            t x1 x2 x3 rum3Score1 rum3Score2 rum3Score3 ω) =
        (0 : Candidate 1) := by
    have htop : rum3TopFirstByScores
        (rumContractScore t x1 (rum3Score1 ω))
        (rumContractScore t x2 (rum3Score2 ω))
        (rumContractScore t x3 (rum3Score3 ω)) :=
      ⟨le_of_lt hcontract21, le_of_lt hcontract31⟩
    simpa [rum3ContractRankByScoreFns] using
      rum3RankByScores_firstChoice_of_top_scores htop
  exact ⟨hbetterFirst.symm, hrawNotTop⟩

/--
Continuous with-density mass comparison for a top/middle coordinate swap.

This is the measure-theoretic version of
`rum3_swap12_mass_le_of_density_formula`: if a measurable equivalence preserves
the base score measure, maps source event `p` into target event `q`, and swaps
the first two score coordinates, then weak well-ordering plus the source score
inequality gives the corresponding mass comparison under the product density.
-/
theorem rum3_withDensity_swap12_measure_le_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} ≤
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} :=
   AppliedModelingLib.Probability.rum3_withDensity_swap12_measure_le_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap p q hp hq hmp hmap hf
    hswap1 hswap2 hswap3 hctx hx12 hscore

/--
Continuous with-density mass comparison for a middle/bottom coordinate swap.
-/
theorem rum3_withDensity_swap23_measure_le_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} ≤
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} :=
   AppliedModelingLib.Probability.rum3_withDensity_swap23_measure_le_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap p q hp hq hmp hmap hf
    hswap1 hswap2 hswap3 hctx hx23 hscore

/--
Continuous with-density transition comparison for Appendix C / Lemma 3.

The source event is the `x₃ -> x₂` transition: the worse ranking puts `x₃`
first and the contracted/better ranking puts `x₂` first.  The target event is
the `x₃ -> x₁` transition.  The `swapi` map swaps the first two score
coordinates, the deterministic contraction geometry maps the source event into
the target event, and weak well-ordering gives density monotonicity.
-/
theorem rum3_deltaTransition_withDensity_measure_le_of_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (better worse : Ω → Ranking 1)
    (hp : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω)})
    (hq : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω)})
    (hmp : MeasurePreserving swap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω))) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω)} ≤
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω)} := by
  refine rum3_withDensity_swap12_measure_le_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω))
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω))
    hp hq hmp ?_ hf hswap1 hswap2 hswap3 hctx hx12 ?_
  · intro ω htransition
    rcases hworseBottom_scores_of_first ω htransition.1 with ⟨hr13, hr23⟩
    rcases hbetterMiddle_scores_of_first ω htransition.2 with ⟨hc12, hc32⟩
    rcases rum3_swap_middle_transition_geometry
        ht0 ht1 hx12 hr13 hr23 hc12 hc32 with
      ⟨hr23_swap, hr13_swap, hc21_swap, hc31_swap⟩
    constructor
    · apply hworseBottom_of_scores
      unfold rum3BottomFirstByScores
      constructor
      · rw [hswap1, hswap3]
        exact hr23_swap
      · rw [hswap2, hswap3]
        exact hr13_swap
    · apply hbetterTop_of_scores
      unfold rum3TopFirstByScores
      constructor
      · rw [hswap2, hswap1]
        exact hc21_swap
      · rw [hswap3, hswap1]
        exact hc31_swap
  · intro ω htransition
    exact rum3_swap_middle_base_score_lt ht0 ht1 hx12
      ((hbetterMiddle_scores_of_first ω htransition.2).1)

/--
Real-valued probability version of
`rum3_deltaTransition_withDensity_measure_le_of_score_facts`.
-/
theorem rum3_deltaTransition_measureProb_le_of_withDensity_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (better worse : Ω → Ranking 1)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hp : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω)})
    (hq : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω)})
    (hmp : MeasurePreserving swap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω))) :
    measureProb
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
      measureProb
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω)) :=
  measureProb_le_of_measure_le
    (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω))
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω))
    (rum3_deltaTransition_withDensity_measure_le_of_score_facts
      base f x1 x2 x3 t r1 r2 r3 swap better worse
      hp hq hmp hf hswap1 hswap2 hswap3 hctx ht0 ht1 hx12
      hbetterTop_of_scores hworseBottom_scores_of_first
      hworseBottom_of_scores hbetterMiddle_scores_of_first)

/--
Strict continuous with-density mass comparison for a top/middle coordinate swap.

The positive-base-measure source assumption is the continuous replacement for a
finite strict witness atom.
-/
theorem rum3_withDensity_swap12_measure_lt_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω)
    (hfi :
      (∫⁻ ω in {ω | p ω},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos : base {ω | p ω} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} :=
   AppliedModelingLib.Probability.rum3_withDensity_swap12_measure_lt_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap p q hp hq hmp hD hmap hf hpos
    hswap1 hswap2 hswap3 hx12 hscore hfi hsource_pos

/--
Strict continuous with-density mass comparison for a middle/bottom coordinate
swap.
-/
theorem rum3_withDensity_swap23_measure_lt_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω)
    (hfi :
      (∫⁻ ω in {ω | p ω},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos : base {ω | p ω} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} :=
   AppliedModelingLib.Probability.rum3_withDensity_swap23_measure_lt_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap p q hp hq hmp hD hmap hf hpos
    hswap1 hswap2 hswap3 hx23 hscore hfi hsource_pos

/--
Mass comparison for a finite sample law whose atoms are represented by the
three-coordinate density product, under a top/middle coordinate swap.
-/
theorem rum3_swap12_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    ∀ ω, p ω → (ν ω).toReal ≤ (ν (swap ω)).toReal :=
   AppliedModelingLib.Probability.rum3_swap12_mass_le_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap p hf hdens
    hswap1 hswap2 hswap3 hctx hx12 hscore

/--
Strict mass comparison for a finite sample law represented by the
three-coordinate density product, under a top/middle coordinate swap.
-/
theorem rum3_swap12_mass_lt_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 < f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    ∀ ω, p ω → (ν ω).toReal < (ν (swap ω)).toReal :=
   AppliedModelingLib.Probability.rum3_swap12_mass_lt_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap p hf hdens
    hswap1 hswap2 hswap3 hctx hx12 hscore

/--
Finite mass comparison for the asymmetric `λ₁ < λ₂` gap event.

The source event is the part of `λ₁` not already counted by `λ₂`: after
removing `x₁`, `x₂` beats `x₃`, but after removing `x₂`, `x₁` does not beat
`x₃`.  Score interfaces turn this into `r₁ < r₂`, which feeds the top/middle
density swap formula.
-/
theorem rum3_lambda13gap_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hnot_target_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        r1 ω < r3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal := by
  refine rum3_swap12_mass_le_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap
    (fun ω =>
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
        ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    hf hdens hswap1 hswap2 hswap3 hctx hx12 ?_
  intro ω hp
  exact lt_of_lt_of_le (hnot_target_scores ω hp.2) (hsource_scores ω hp.1)

/-- Strict finite mass comparison for the asymmetric `λ₁ < λ₂` gap event. -/
theorem rum3_lambda13gap_mass_lt_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        0 < f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hnot_target_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        r1 ω < r3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        (ν ω).toReal < (ν (swap ω)).toReal := by
  refine rum3_swap12_mass_lt_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap
    (fun ω =>
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
        ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    hf hdens hswap1 hswap2 hswap3 hctx hx12 ?_
  intro ω hp
  exact lt_of_lt_of_le (hnot_target_scores ω hp.2) (hsource_scores ω hp.1)

/--
Finite mass comparison for the delta-side `swapi` map in Lemma 3.

The transition event says the worse ranking puts `x₃` first and the contracted
better ranking puts `x₂` first.  The better-first score interface gives the
contracted inequality `c₁ < c₂`; contraction geometry turns it into the raw
score inequality `r₁ < r₂`, which feeds the top/middle density swap formula.
-/
theorem rum3_deltaSwap_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (better worse : Ω → Ranking 1)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω))) :
    ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal := by
  refine rum3_swap12_mass_le_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω))
    hf hdens hswap1 hswap2 hswap3 hctx hx12 ?_
  intro ω hp
  exact rum3_swap_middle_base_score_lt ht0 ht1 hx12
    ((hbetterMiddle_scores_of_first ω hp.2).1)

/--
Mass comparison for a finite sample law whose atoms are represented by the
three-coordinate density product, under a middle/bottom coordinate swap.
-/
theorem rum3_swap23_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    ∀ ω, p ω → (ν ω).toReal ≤ (ν (swap ω)).toReal :=
   AppliedModelingLib.Probability.rum3_swap23_mass_le_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap p hf hdens
    hswap1 hswap2 hswap3 hctx hx23 hscore

/--
Strict mass comparison for a finite sample law represented by the
three-coordinate density product, under a middle/bottom coordinate swap.
-/
theorem rum3_swap23_mass_lt_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 < f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    ∀ ω, p ω → (ν ω).toReal < (ν (swap ω)).toReal :=
   AppliedModelingLib.Probability.rum3_swap23_mass_lt_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap p hf hdens
    hswap1 hswap2 hswap3 hctx hx23 hscore

/-! ## Three-candidate RUM payoff algebra -/

/-- In the three-candidate RUM proof, utility after candidate `x₁` is unavailable. -/
noncomputable def rum3_uMinus1 (ell1 x2 x3 : ℝ) : ℝ := ell1 * x2 + (1 - ell1) * x3

/-- In the three-candidate RUM proof, utility after candidate `x₂` is unavailable. -/
noncomputable def rum3_uMinus2 (ell2 x1 x3 : ℝ) : ℝ := ell2 * x1 + (1 - ell2) * x3

/-- In the three-candidate RUM proof, utility after candidate `x₃` is unavailable. -/
noncomputable def rum3_uMinus3 (ell3 x1 x2 : ℝ) : ℝ := ell3 * x1 + (1 - ell3) * x2

/-- Paper Theorem 6's `λ₁`: after `x₁` is unavailable, human chooses `x₂`. -/
noncomputable def rum3Lambda1 (μ : PMF (Ranking 1)) : ℝ :=
  pmfProb μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))

/-- Paper Theorem 6's `λ₂`: after `x₂` is unavailable, human chooses `x₁`. -/
noncomputable def rum3Lambda2 (μ : PMF (Ranking 1)) : ℝ :=
  pmfProb μ (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))

/-- Paper Theorem 6's `λ₃`: after `x₃` is unavailable, human chooses `x₁`. -/
noncomputable def rum3Lambda3 (μ : PMF (Ranking 1)) : ℝ :=
  pmfProb μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))

/--
The ranking PMF induced by pushing a continuous realization measure through a
ranking map.
-/
noncomputable def rumRankingPMFOfMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank) : PMF (Ranking 1) :=
  AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure μ rank hrank

/--
Event probabilities for the induced ranking PMF are source-measure preimage
masses.
-/
theorem rumRankingPMFOfMeasure_eventProb
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (p : Ranking 1 → Prop) [DecidablePred p] :
    pmfProb (rumRankingPMFOfMeasure μ rank hrank) p =
      measureProb μ (fun ω => p (rank ω)) :=
   AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eventProb
    μ rank hrank p

/--
Under an almost-sure no-tie source law, atom probabilities of the finite ranking
law induced by the paper contraction are continuous at the raw-score endpoint
`t = 1`.
-/
theorem rumRankingPMFOfMeasure_contractRankByScoreFns_atom_continuousAt_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hr1 : Measurable r1) (hr2 : Measurable r2) (hr3 : Measurable r3)
    (hnoTies :
      ∀ᵐ ω ∂μ, r1 ω ≠ r2 ω ∧ r1 ω ≠ r3 ω ∧ r2 ω ≠ r3 ω)
    (π : Ranking 1) :
    ContinuousAt
      (fun t : ℝ =>
        ((rumRankingPMFOfMeasure μ
          (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3)
          (rum3ContractRankByScoreFns_measurable hr1 hr2 hr3 t x1 x2 x3))
          π).toReal)
      1 := by
  classical
  haveI : IsFiniteMeasure μ := by infer_instance
  let rawRank : Ω → Ranking 1 := rum3RankByScoreFns r1 r2 r3
  let contractRank : ℝ → Ω → Ranking 1 := fun t =>
    rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3
  have hraw_meas : Measurable rawRank :=
    rum3RankByScoreFns_measurable hr1 hr2 hr3
  have hcontract_meas :
      ∀ t : ℝ, Measurable (contractRank t) := by
    intro t
    exact rum3ContractRankByScoreFns_measurable hr1 hr2 hr3 t x1 x2 x3
  have hmeas_contract :
      ∀ t : ℝ, MeasurableSet {ω : Ω | contractRank t ω = π} := by
    intro t
    exact measurableSet_eq_fun (hcontract_meas t) measurable_const
  have hmeas_raw : MeasurableSet {ω : Ω | rawRank ω = π} :=
    measurableSet_eq_fun hraw_meas measurable_const
  have hlim :
      Filter.Tendsto
        (fun t : ℝ => μ {ω : Ω | contractRank t ω = π})
        (nhds (1 : ℝ))
        (nhds (μ {ω : Ω | contractRank 1 ω = π})) := by
    refine
      MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
        (L := nhds (1 : ℝ)) (μ := μ)
        (A := {ω : Ω | contractRank 1 ω = π})
        (hmeas_contract 1) hmeas_contract ?_
    refine hnoTies.mono ?_
    intro ω hω
    rcases hω with ⟨h12, h13, h23⟩
    exact
      (rum3ContractRankByScoreFns_eventually_eq_rankByScoreFns_at_one
        (x1 := x1) (x2 := x2) (x3 := x3)
        (r1 := r1) (r2 := r2) (r3 := r3) (ω := ω)
        h12 h13 h23).mono fun t ht => by
          have h1 : contractRank 1 ω = rawRank ω := by
            unfold contractRank rawRank rum3ContractRankByScoreFns
              rum3RankByScoreFns
            simp [rumContractScore_eq_affine]
          simp [rawRank, contractRank, ht, h1]
  have hreal :
      Filter.Tendsto
        (fun t : ℝ => (μ {ω : Ω | contractRank t ω = π}).toReal)
        (nhds (1 : ℝ))
        (nhds ((μ {ω : Ω | contractRank 1 ω = π}).toReal)) :=
    (ENNReal.tendsto_toReal
      (measure_ne_top μ {ω : Ω | contractRank 1 ω = π})).comp
      hlim
  have hatom :
      (fun t : ℝ =>
        ((rumRankingPMFOfMeasure μ (contractRank t) (hcontract_meas t)) π).toReal)
        =
      fun t : ℝ => (μ {ω : Ω | contractRank t ω = π}).toReal := by
    funext t
    rw [← pmfProb_singleton
      (rumRankingPMFOfMeasure μ (contractRank t) (hcontract_meas t)) π]
    rw [rumRankingPMFOfMeasure_eventProb μ (contractRank t) (hcontract_meas t)
      (fun ρ : Ranking 1 => ρ = π)]
    rfl
  change
    ContinuousAt
      (fun t : ℝ =>
        ((rumRankingPMFOfMeasure μ (contractRank t) (hcontract_meas t)) π).toReal)
      1
  have hatom_one :
      ((rumRankingPMFOfMeasure μ (contractRank 1) (hcontract_meas 1)) π).toReal =
        (μ {ω : Ω | contractRank 1 ω = π}).toReal := by
    simpa using congrFun hatom 1
  rw [ContinuousAt]
  rw [hatom]
  rw [hatom_one]
  exact hreal

theorem prod_prod_real_score12_tie_measure_zero
    (μ1 μ2 μ3 : Measure ℝ) [SFinite μ1] [SFinite μ2] [SFinite μ3]
    [NoAtoms μ2] :
    (μ1.prod (μ2.prod μ3))
      {ω : ℝ × (ℝ × ℝ) | ω.1 = ω.2.1} = 0 := by
  let S : Set (ℝ × (ℝ × ℝ)) := {ω | ω.1 = ω.2.1}
  have hS_meas : MeasurableSet S :=
    (isClosed_eq continuous_fst (continuous_snd.fst)).measurableSet
  have hsection :
      ∀ x : ℝ, (μ2.prod μ3) (Prod.mk x ⁻¹' S) = 0 := by
    intro x
    have hset :
        Prod.mk x ⁻¹' S = ({x} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p
      simp [S, eq_comm]
    rw [hset, Measure.prod_prod]
    simp
  calc
    (μ1.prod (μ2.prod μ3)) S
        = ∫⁻ x, (μ2.prod μ3) (Prod.mk x ⁻¹' S) ∂μ1 := by
          rw [Measure.prod_apply hS_meas]
    _ = ∫⁻ _x, 0 ∂μ1 := by
          exact lintegral_congr hsection
    _ = 0 := by simp

theorem prod_prod_real_score13_tie_measure_zero
    (μ1 μ2 μ3 : Measure ℝ) [SFinite μ1] [SFinite μ2] [SFinite μ3]
    [NoAtoms μ3] :
    (μ1.prod (μ2.prod μ3))
      {ω : ℝ × (ℝ × ℝ) | ω.1 = ω.2.2} = 0 := by
  let S : Set (ℝ × (ℝ × ℝ)) := {ω | ω.1 = ω.2.2}
  have hS_meas : MeasurableSet S :=
    (isClosed_eq continuous_fst (continuous_snd.snd)).measurableSet
  have hsection :
      ∀ x : ℝ, (μ2.prod μ3) (Prod.mk x ⁻¹' S) = 0 := by
    intro x
    have hset :
        Prod.mk x ⁻¹' S = (Set.univ : Set ℝ) ×ˢ ({x} : Set ℝ) := by
      ext p
      simp [S, eq_comm]
    rw [hset, Measure.prod_prod]
    simp
  calc
    (μ1.prod (μ2.prod μ3)) S
        = ∫⁻ x, (μ2.prod μ3) (Prod.mk x ⁻¹' S) ∂μ1 := by
          rw [Measure.prod_apply hS_meas]
    _ = ∫⁻ _x, 0 ∂μ1 := by
          exact lintegral_congr hsection
    _ = 0 := by simp

theorem prod_prod_real_score23_tie_measure_zero
    (μ1 μ2 μ3 : Measure ℝ) [SFinite μ1] [SFinite μ2] [SFinite μ3]
    [NoAtoms μ3] :
    (μ1.prod (μ2.prod μ3))
      {ω : ℝ × (ℝ × ℝ) | ω.2.1 = ω.2.2} = 0 := by
  let S : Set (ℝ × (ℝ × ℝ)) := {ω | ω.2.1 = ω.2.2}
  let T : Set (ℝ × ℝ) := {p | p.1 = p.2}
  have hS_meas : MeasurableSet S :=
    (isClosed_eq (continuous_snd.fst) (continuous_snd.snd)).measurableSet
  have hT_meas : MeasurableSet T :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  have hT_zero : (μ2.prod μ3) T = 0 := by
    have hsection : ∀ x : ℝ, μ3 (Prod.mk x ⁻¹' T) = 0 := by
      intro x
      have hset : Prod.mk x ⁻¹' T = ({x} : Set ℝ) := by
        ext y
        simp [T]
      rw [hset]
      simp
    calc
      (μ2.prod μ3) T
          = ∫⁻ x, μ3 (Prod.mk x ⁻¹' T) ∂μ2 := by
            rw [Measure.prod_apply hT_meas]
      _ = ∫⁻ _x, 0 ∂μ2 := by
            exact lintegral_congr hsection
      _ = 0 := by simp
  have hS_set : S = (Set.univ : Set ℝ) ×ˢ T := by
    ext ω
    simp [S, T]
  change (μ1.prod (μ2.prod μ3)) S = 0
  rw [hS_set, Measure.prod_prod]
  simp [hT_zero]

theorem prod_prod_real_no_score_ties_ae
    (μ1 μ2 μ3 : Measure ℝ) [SFinite μ1] [SFinite μ2] [SFinite μ3]
    [NoAtoms μ2] [NoAtoms μ3] :
    ∀ᵐ ω ∂ μ1.prod (μ2.prod μ3),
      ω.1 ≠ ω.2.1 ∧ ω.1 ≠ ω.2.2 ∧ ω.2.1 ≠ ω.2.2 := by
  have h12 :
      (μ1.prod (μ2.prod μ3))
        {ω : ℝ × (ℝ × ℝ) | ω.1 = ω.2.1} = 0 :=
    prod_prod_real_score12_tie_measure_zero μ1 μ2 μ3
  have h13 :
      (μ1.prod (μ2.prod μ3))
        {ω : ℝ × (ℝ × ℝ) | ω.1 = ω.2.2} = 0 :=
    prod_prod_real_score13_tie_measure_zero μ1 μ2 μ3
  have h23 :
      (μ1.prod (μ2.prod μ3))
        {ω : ℝ × (ℝ × ℝ) | ω.2.1 = ω.2.2} = 0 :=
    prod_prod_real_score23_tie_measure_zero μ1 μ2 μ3
  have h12ae :
      ∀ᵐ ω ∂ μ1.prod (μ2.prod μ3), ω.1 ≠ ω.2.1 :=
    (measure_eq_zero_iff_ae_notMem.1 h12).mono fun _ h => h
  have h13ae :
      ∀ᵐ ω ∂ μ1.prod (μ2.prod μ3), ω.1 ≠ ω.2.2 :=
    (measure_eq_zero_iff_ae_notMem.1 h13).mono fun _ h => h
  have h23ae :
      ∀ᵐ ω ∂ μ1.prod (μ2.prod μ3), ω.2.1 ≠ ω.2.2 :=
    (measure_eq_zero_iff_ae_notMem.1 h23).mono fun _ h => h
  filter_upwards [h12ae, h13ae, h23ae] with ω h12ω h13ω h23ω
  exact ⟨h12ω, h13ω, h23ω⟩

theorem theorem8GaussianDefinition2ScoreMeasureStd_no_score_ties_ae
    {σ x1 x2 x3 : ℝ} (hσ : σ ≠ 0) :
    ∀ᵐ ω ∂ theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3,
      theorem8GaussianDefinition2Score1 ω ≠
          theorem8GaussianDefinition2Score2 ω ∧
        theorem8GaussianDefinition2Score1 ω ≠
          theorem8GaussianDefinition2Score3 ω ∧
        theorem8GaussianDefinition2Score2 ω ≠
          theorem8GaussianDefinition2Score3 ω := by
  let μ1 := ProbabilityTheory.gaussianReal x1 (theorem8GaussianVarianceFromStd σ)
  let μ2 := ProbabilityTheory.gaussianReal x2 (theorem8GaussianVarianceFromStd σ)
  let μ3 := ProbabilityTheory.gaussianReal x3 (theorem8GaussianVarianceFromStd σ)
  haveI : NoAtoms μ2 :=
    ProbabilityTheory.noAtoms_gaussianReal
      (theorem8GaussianVarianceFromStd_ne_zero hσ)
  haveI : NoAtoms μ3 :=
    ProbabilityTheory.noAtoms_gaussianReal
      (theorem8GaussianVarianceFromStd_ne_zero hσ)
  have hties := prod_prod_real_no_score_ties_ae μ1 μ2 μ3
  simpa [theorem8GaussianDefinition2ScoreMeasureStd,
    theorem8GaussianPairMeasureStd,
    AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd,
    theorem8GaussianDefinition2Score1,
    theorem8GaussianDefinition2Score2,
    theorem8GaussianDefinition2Score3,
    μ1, μ2, μ3] using hties

theorem theorem7LaplaceMeasure_noAtoms (lam μ : ℝ) :
    NoAtoms (theorem7LaplaceMeasure lam μ) := by
  unfold theorem7LaplaceMeasure
  infer_instance

theorem theorem7LaplacianDefinition2ScoreMeasure_no_score_ties_ae
    {lam x1 x2 x3 : ℝ} :
    ∀ᵐ ω ∂ theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3,
      theorem7LaplacianDefinition2Score1 ω ≠
          theorem7LaplacianDefinition2Score2 ω ∧
        theorem7LaplacianDefinition2Score1 ω ≠
          theorem7LaplacianDefinition2Score3 ω ∧
        theorem7LaplacianDefinition2Score2 ω ≠
          theorem7LaplacianDefinition2Score3 ω := by
  let μ1 := theorem7LaplaceMeasure lam x1
  let μ2 := theorem7LaplaceMeasure lam x2
  let μ3 := theorem7LaplaceMeasure lam x3
  haveI : SFinite μ1 := by
    dsimp [μ1, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ2 := by
    dsimp [μ2, theorem7LaplaceMeasure]
    infer_instance
  haveI : SFinite μ3 := by
    dsimp [μ3, theorem7LaplaceMeasure]
    infer_instance
  haveI : NoAtoms μ2 := theorem7LaplaceMeasure_noAtoms lam x2
  haveI : NoAtoms μ3 := theorem7LaplaceMeasure_noAtoms lam x3
  have hties := prod_prod_real_no_score_ties_ae μ1 μ2 μ3
  simpa [theorem7LaplacianDefinition2ScoreMeasure,
    theorem7LaplacianPairMeasure,
    theorem7LaplacianDefinition2Score1,
    theorem7LaplacianDefinition2Score2,
    theorem7LaplacianDefinition2Score3,
    μ1, μ2, μ3] using hties

theorem rumRankingPMFOfMeasure_rankByScoreFns_ranking102_toReal_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r1 r2 r3 : Ω → ℝ)
    (hrank : Measurable (rum3RankByScoreFns r1 r2 r3))
    (hpos :
      0 <
        measureProb μ
          (fun ω => rum3RankByScoreFns r1 r2 r3 ω = rum3Ranking102)) :
    0 <
      ((rumRankingPMFOfMeasure μ (rum3RankByScoreFns r1 r2 r3) hrank)
        rum3Ranking102).toReal := by
  rw [← pmfProb_singleton
    (rumRankingPMFOfMeasure μ (rum3RankByScoreFns r1 r2 r3) hrank)
    rum3Ranking102]
  rw [rumRankingPMFOfMeasure_eventProb μ
    (rum3RankByScoreFns r1 r2 r3) hrank
    (fun π => π = rum3Ranking102)]
  exact hpos

theorem theorem8GaussianDefinition2RankingPMFStd_ranking102_toReal_pos
    {σ x1 x2 x3 : ℝ} (hσ : 0 < σ) :
    0 <
      ((rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable))
        rum3Ranking102).toReal :=
  rumRankingPMFOfMeasure_rankByScoreFns_ranking102_toReal_pos
    (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
    theorem8GaussianDefinition2Score1
    theorem8GaussianDefinition2Score2
    theorem8GaussianDefinition2Score3
    (rum3RankByScoreFns_measurable
      theorem8GaussianDefinition2Score1_measurable
      theorem8GaussianDefinition2Score2_measurable
      theorem8GaussianDefinition2Score3_measurable)
    (theorem8GaussianDefinition2Std_ranking102_measureProb_pos
      (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) hσ)

/--
If the source law assigns less than `δ` mass to realizations whose induced
ranking differs from `[0,1,2]`, then the induced finite ranking law is
atomwise `δ`-close to the pure `[0,1,2]` ranking law.
-/
theorem rumRankingPMFOfMeasure_atomwise_close_to_pure012_of_wrong_prob_lt
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    {δ : ℝ} (hδ : 0 < δ)
    (hwrong :
      measureProb μ (fun ω => rank ω ≠ rum3Ranking012) < δ) :
    ∀ π : Ranking 1,
      |((rumRankingPMFOfMeasure μ rank hrank) π).toReal -
          (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) π).toReal)| < δ := by
  classical
  have hwrong_pmf :
      pmfProb (rumRankingPMFOfMeasure μ rank hrank)
          (fun π => π ≠ rum3Ranking012) < δ := by
    rw [rumRankingPMFOfMeasure_eventProb μ rank hrank
      (fun π => π ≠ rum3Ranking012)]
    simpa [Ne] using hwrong
  exact
    atomwise_close_to_pure_of_wrong_prob_lt
      (rumRankingPMFOfMeasure μ rank hrank) rum3Ranking012 hδ hwrong_pmf

/--
Pairwise adjacent inversion bound for score-induced rankings.

For three scores ordered by true value as `x₁ > x₂ > x₃`, any ranking different
from `[0,1,2]` must invert either the adjacent pair `(1,2)` or `(2,3)`.
Thus small pairwise inversion probabilities imply atomwise concentration of
the induced finite ranking law at `[0,1,2]`.
-/
theorem rumRankingPMFOfMeasure_rankByScoreFns_atomwise_close_to_pure012_of_pair_inversions_lt
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r1 r2 r3 : Ω → ℝ)
    (hrank : Measurable (rum3RankByScoreFns r1 r2 r3))
    {δ : ℝ} (hδ : 0 < δ)
    (hpair :
      measureProb μ (fun ω => r1 ω < r2 ω) +
          measureProb μ (fun ω => r2 ω < r3 ω) < δ) :
    ∀ π : Ranking 1,
      |((rumRankingPMFOfMeasure μ (rum3RankByScoreFns r1 r2 r3) hrank) π).toReal -
          (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) π).toReal)| < δ := by
  classical
  have hwrong_le :
      measureProb μ
          (fun ω => rum3RankByScoreFns r1 r2 r3 ω ≠ rum3Ranking012) ≤
        measureProb μ (fun ω => r1 ω < r2 ω) +
          measureProb μ (fun ω => r2 ω < r3 ω) := by
    calc
      measureProb μ
          (fun ω => rum3RankByScoreFns r1 r2 r3 ω ≠ rum3Ranking012)
          ≤
        measureProb μ (fun ω => r1 ω < r2 ω ∨ r2 ω < r3 ω) := by
          refine measureProb_mono μ
            (fun ω => rum3RankByScoreFns r1 r2 r3 ω ≠ rum3Ranking012)
            (fun ω => r1 ω < r2 ω ∨ r2 ω < r3 ω) ?_
          intro ω hω
          exact rum3RankByScoreFns_ne012_imp_adjacent_inversion hω
      _ ≤
        measureProb μ (fun ω => r1 ω < r2 ω) +
          measureProb μ (fun ω => r2 ω < r3 ω) :=
          measureProb_or_le μ (fun ω => r1 ω < r2 ω) (fun ω => r2 ω < r3 ω)
  exact
    rumRankingPMFOfMeasure_atomwise_close_to_pure012_of_wrong_prob_lt
      μ (rum3RankByScoreFns r1 r2 r3) hrank hδ
      (lt_of_le_of_lt hwrong_le hpair)

/--
Gaussian source-model concentration: with standard deviation `1 / θ`, the
induced ranking law converges atomwise to the true ranking `[0,1,2]`.
-/
theorem theorem8GaussianDefinition2RankingPMFStd_atomwise_concentration
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    ∀ lower δ, 0 < δ →
      ∃ hi, lower < hi ∧
        ∀ π : Ranking 1,
          |((rumRankingPMFOfMeasure
              (theorem8GaussianDefinition2ScoreMeasureStd (1 / hi) x1 x2 x3)
              (rum3RankByScoreFns
                theorem8GaussianDefinition2Score1
                theorem8GaussianDefinition2Score2
                theorem8GaussianDefinition2Score3)
              (rum3RankByScoreFns_measurable
                theorem8GaussianDefinition2Score1_measurable
                theorem8GaussianDefinition2Score2_measurable
                theorem8GaussianDefinition2Score3_measurable)) π).toReal -
            (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) π).toReal)| < δ := by
  intro lower δ hδ
  have hsum :=
    theorem8GaussianDefinition2ScoreMeasureStd_adjacent_inversions_tendsto_atTop_zero
      (x1 := x1) (x2 := x2) (x3 := x3) hx12 hx23
  have hsmall :
      ∀ᶠ θ : ℝ in Filter.atTop,
        measureProb
          (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score2 ω) +
        measureProb
          (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω <
              theorem8GaussianDefinition2Score3 ω) < δ :=
    hsum.eventually (Iio_mem_nhds hδ)
  rcases Filter.eventually_atTop.1
      (hsmall.and (Filter.eventually_gt_atTop lower)) with
    ⟨hi, hhi⟩
  refine ⟨hi, (hhi hi le_rfl).2, ?_⟩
  have hpair := (hhi hi le_rfl).1
  let μ := theorem8GaussianDefinition2ScoreMeasureStd (1 / hi) x1 x2 x3
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  exact
    rumRankingPMFOfMeasure_rankByScoreFns_atomwise_close_to_pure012_of_pair_inversions_lt
      μ theorem8GaussianDefinition2Score1 theorem8GaussianDefinition2Score2
      theorem8GaussianDefinition2Score3
      (rum3RankByScoreFns_measurable
        theorem8GaussianDefinition2Score1_measurable
        theorem8GaussianDefinition2Score2_measurable
        theorem8GaussianDefinition2Score3_measurable)
      hδ hpair

/-- Continuous-measure form of `λ₁` for an induced ranking PMF. -/
theorem rum3Lambda1_rumRankingPMFOfMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank) :
    rum3Lambda1 (rumRankingPMFOfMeasure μ rank hrank) =
      measureProb μ
        (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)) := by
  unfold rum3Lambda1
  exact rumRankingPMFOfMeasure_eventProb μ rank hrank
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))

/-- Continuous-measure form of `λ₂` for an induced ranking PMF. -/
theorem rum3Lambda2_rumRankingPMFOfMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank) :
    rum3Lambda2 (rumRankingPMFOfMeasure μ rank hrank) =
      measureProb μ
        (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
          (0 : Candidate 1)) := by
  unfold rum3Lambda2
  exact rumRankingPMFOfMeasure_eventProb μ rank hrank
    (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))

/-- Continuous-measure form of `λ₃` for an induced ranking PMF. -/
theorem rum3Lambda3_rumRankingPMFOfMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank) :
    rum3Lambda3 (rumRankingPMFOfMeasure μ rank hrank) =
      measureProb μ
        (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)) := by
  unfold rum3Lambda3
  exact rumRankingPMFOfMeasure_eventProb μ rank hrank
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))

/-- Continuous-measure form of first-choice probability. -/
theorem firstChoiceProb_rumRankingPMFOfMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (c : Candidate 1) :
    firstChoiceProb (rumRankingPMFOfMeasure μ rank hrank) c =
      measureProb μ (fun ω => c = firstChoice (rank ω)) := by
  unfold firstChoiceProb
  exact rumRankingPMFOfMeasure_eventProb μ rank hrank
    (fun π => c = firstChoice π)

/--
Gaussian contraction transport for the induced three-candidate ranking law.

Ranking the contracted scores under the original standard deviation `σ` has the
same finite ranking law as ranking raw scores under standard deviation `t * σ`.
-/
theorem theorem8GaussianDefinition2RankingPMFStd_contract_eq
    (t σ x1 x2 x3 : ℝ) :
    rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3ContractRankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable
          t x1 x2 x3) =
      rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd (t * σ) x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable) := by
  refine
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eq_of_measurePreserving
      (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
      (theorem8GaussianDefinition2ScoreMeasureStd (t * σ) x1 x2 x3)
      (theorem8GaussianDefinition2ContractMap t x1 x2 x3)
      (theorem8GaussianDefinition2ContractMap_measurePreserving
        t σ x1 x2 x3)
      (rum3ContractRankByScoreFns
        t x1 x2 x3
        theorem8GaussianDefinition2Score1
        theorem8GaussianDefinition2Score2
        theorem8GaussianDefinition2Score3)
      (rum3ContractRankByScoreFns_measurable
        theorem8GaussianDefinition2Score1_measurable
        theorem8GaussianDefinition2Score2_measurable
        theorem8GaussianDefinition2Score3_measurable
        t x1 x2 x3)
      (rum3RankByScoreFns
        theorem8GaussianDefinition2Score1
        theorem8GaussianDefinition2Score2
        theorem8GaussianDefinition2Score3)
      (rum3RankByScoreFns_measurable
        theorem8GaussianDefinition2Score1_measurable
        theorem8GaussianDefinition2Score2_measurable
        theorem8GaussianDefinition2Score3_measurable)
      ?_
  intro ω
  rfl

/--
Canonical scaling transport for the raw arbitrary-standard-deviation Gaussian
ranking law.  Scaling all realized scores and all means by the same positive
constant preserves the induced ranking.
-/
theorem theorem8GaussianDefinition2RankingPMFStd_canonical_eq
    {σ x1 x2 x3 : ℝ} (hσ : 0 < σ) :
    rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable) =
      rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasure
          (theorem8GaussianCanonicalScale σ * x1)
          (theorem8GaussianCanonicalScale σ * x2)
          (theorem8GaussianCanonicalScale σ * x3))
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable) := by
  let c := theorem8GaussianCanonicalScale σ
  have hc : 0 < c := theorem8GaussianCanonicalScale_pos hσ
  refine
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eq_of_measurePreserving
      (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
      (theorem8GaussianDefinition2ScoreMeasure
        (c * x1) (c * x2) (c * x3))
      (theorem8GaussianDefinition2CanonicalScaleMap σ)
      (by
        simpa [c] using
          (theorem8GaussianDefinition2CanonicalScaleMap_measurePreserving
            (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) hσ))
      (rum3RankByScoreFns
        theorem8GaussianDefinition2Score1
        theorem8GaussianDefinition2Score2
        theorem8GaussianDefinition2Score3)
      (rum3RankByScoreFns_measurable
        theorem8GaussianDefinition2Score1_measurable
        theorem8GaussianDefinition2Score2_measurable
        theorem8GaussianDefinition2Score3_measurable)
      (rum3RankByScoreFns
        theorem8GaussianDefinition2Score1
        theorem8GaussianDefinition2Score2
        theorem8GaussianDefinition2Score3)
      (rum3RankByScoreFns_measurable
        theorem8GaussianDefinition2Score1_measurable
        theorem8GaussianDefinition2Score2_measurable
        theorem8GaussianDefinition2Score3_measurable)
      ?_
  intro ω
  symm
  simpa [rum3RankByScoreFns, theorem8GaussianDefinition2CanonicalScaleMap, c]
    using
      rum3RankByScores_mul_pos hc
        (theorem8GaussianDefinition2Score1 ω)
        (theorem8GaussianDefinition2Score2 ω)
        (theorem8GaussianDefinition2Score3 ω)

/--
Canonical scaling transport for the contracted arbitrary-standard-deviation
Gaussian ranking law.
-/
theorem theorem8GaussianDefinition2ContractRankingPMFStd_canonical_eq
    {σ x1 x2 x3 : ℝ} (hσ : 0 < σ) (t : ℝ) :
    rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3ContractRankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable
          t x1 x2 x3) =
      rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasure
          (theorem8GaussianCanonicalScale σ * x1)
          (theorem8GaussianCanonicalScale σ * x2)
          (theorem8GaussianCanonicalScale σ * x3))
        (rum3ContractRankByScoreFns
          t
          (theorem8GaussianCanonicalScale σ * x1)
          (theorem8GaussianCanonicalScale σ * x2)
          (theorem8GaussianCanonicalScale σ * x3)
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3ContractRankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable
          t
          (theorem8GaussianCanonicalScale σ * x1)
          (theorem8GaussianCanonicalScale σ * x2)
          (theorem8GaussianCanonicalScale σ * x3)) := by
  let c := theorem8GaussianCanonicalScale σ
  have hc : 0 < c := theorem8GaussianCanonicalScale_pos hσ
  refine
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eq_of_measurePreserving
      (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
      (theorem8GaussianDefinition2ScoreMeasure
        (c * x1) (c * x2) (c * x3))
      (theorem8GaussianDefinition2CanonicalScaleMap σ)
      (by
        simpa [c] using
          (theorem8GaussianDefinition2CanonicalScaleMap_measurePreserving
            (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) hσ))
      (rum3ContractRankByScoreFns
        t x1 x2 x3
        theorem8GaussianDefinition2Score1
        theorem8GaussianDefinition2Score2
        theorem8GaussianDefinition2Score3)
      (rum3ContractRankByScoreFns_measurable
        theorem8GaussianDefinition2Score1_measurable
        theorem8GaussianDefinition2Score2_measurable
        theorem8GaussianDefinition2Score3_measurable
        t x1 x2 x3)
      (rum3ContractRankByScoreFns
        t (c * x1) (c * x2) (c * x3)
        theorem8GaussianDefinition2Score1
        theorem8GaussianDefinition2Score2
        theorem8GaussianDefinition2Score3)
      (rum3ContractRankByScoreFns_measurable
        theorem8GaussianDefinition2Score1_measurable
        theorem8GaussianDefinition2Score2_measurable
        theorem8GaussianDefinition2Score3_measurable
        t (c * x1) (c * x2) (c * x3))
      ?_
  intro ω
  symm
  change
    rum3RankByScores
        (rumContractScore t (c * x1)
          (c * theorem8GaussianDefinition2Score1 ω))
        (rumContractScore t (c * x2)
          (c * theorem8GaussianDefinition2Score2 ω))
        (rumContractScore t (c * x3)
          (c * theorem8GaussianDefinition2Score3 ω)) =
      rum3RankByScores
        (rumContractScore t x1 (theorem8GaussianDefinition2Score1 ω))
        (rumContractScore t x2 (theorem8GaussianDefinition2Score2 ω))
        (rumContractScore t x3 (theorem8GaussianDefinition2Score3 ω))
  rw [rumContractScore_mul_left, rumContractScore_mul_left,
    rumContractScore_mul_left]
  exact rum3RankByScores_mul_pos hc
    (rumContractScore t x1 (theorem8GaussianDefinition2Score1 ω))
    (rumContractScore t x2 (theorem8GaussianDefinition2Score2 ω))
    (rumContractScore t x3 (theorem8GaussianDefinition2Score3 ω))

theorem rum3Lambda1_wrong_eq_one_sub (μ : PMF (Ranking 1)) :
    pmfProb μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
      1 - rum3Lambda1 μ := by
  classical
  unfold rum3Lambda1
  rw [← pmfProb_compl μ
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))]
  unfold pmfProb
  refine pmfExp_congr μ ?_
  intro π
  by_cases h1 : bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1)
  · simp [h1]
  · have hne0 :
        bestRemainingAfter π (0 : Candidate 1) ≠ (0 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (0 : Candidate 1)
    have h2 : bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (0 : Candidate 1)).val = 2
      have hval0 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact hne0 (Fin.ext hv)
      have hval1 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 1 := by
        intro hv
        exact h1 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (0 : Candidate 1)).isLt
      omega
    simp [h2]

theorem rum3Lambda3_wrong_eq_one_sub (μ : PMF (Ranking 1)) :
    pmfProb μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
      1 - rum3Lambda3 μ := by
  classical
  unfold rum3Lambda3
  rw [← pmfProb_compl μ
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))]
  unfold pmfProb
  refine pmfExp_congr μ ?_
  intro π
  by_cases h0 : bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1)
  · simp [h0]
  · have hne2 :
        bestRemainingAfter π (2 : Candidate 1) ≠ (2 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (2 : Candidate 1)
    have h1 : bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (2 : Candidate 1)).val = 1
      have hval0 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact h0 (Fin.ext hv)
      have hval2 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 2 := by
        intro hv
        exact hne2 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (2 : Candidate 1)).isLt
      omega
    simp [h1]

theorem rum3Lambda1_half_of_wrong_lt_correct
    {μ : PMF (Ranking 1)}
    (hwrong :
      pmfProb μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μ) :
    (1 : ℝ) / 2 < rum3Lambda1 μ := by
  rw [rum3Lambda1_wrong_eq_one_sub μ] at hwrong
  linarith

theorem rum3Lambda3_half_of_wrong_lt_correct
    {μ : PMF (Ranking 1)}
    (hwrong :
      pmfProb μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μ) :
    (1 : ℝ) / 2 < rum3Lambda3 μ := by
  rw [rum3Lambda3_wrong_eq_one_sub μ] at hwrong
  linarith

/--
Named finite certificate for Appendix C / Theorem 6.

The fields are the exact non-analytic facts used after the paper invokes
monotonicity, Lemma 2, Lemma 3, and the pairwise human-ranking probabilities.
-/
structure RUM3Theorem6Certificate
    (μBetter μWorse : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    (x1 x2 x3 : ℝ) : Prop where
  value_first : value (0 : Candidate 1) = x1
  value_second : value (1 : Candidate 1) = x2
  value_third : value (2 : Candidate 1) = x3
  value12 : x2 < x1
  value23 : x3 < x2
  /-- Paper: `1/2 < λ₁`. -/
  lambda1_half : (1 : ℝ) / 2 < rum3Lambda1 μWorse
  /-- Paper: `λ₁ < 1`. -/
  lambda1_lt_one : rum3Lambda1 μWorse < 1
  /-- Paper: `λ₂ > λ₁`. -/
  lambda12 : rum3Lambda1 μWorse < rum3Lambda2 μWorse
  /-- Paper: `1/2 < λ₃`. -/
  lambda3_half : (1 : ℝ) / 2 < rum3Lambda3 μWorse
  /-- Paper monotonicity: `Δp₁ > 0`. -/
  delta_top_pos :
    0 <
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1)
  /-- Paper Lemma 3 for `i = 2`: `Δp₂ ≤ Δp₁`. -/
  delta_middle_le_top :
    firstChoiceProb μBetter (1 : Candidate 1) -
        firstChoiceProb μWorse (1 : Candidate 1) ≤
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1)
  /-- Paper Lemma 2: `Δp₃ ≤ 0`. -/
  delta_bottom_nonpos :
    firstChoiceProb μBetter (2 : Candidate 1) -
        firstChoiceProb μWorse (2 : Candidate 1) ≤ 0

/-- The lambda side of the paper's Theorem 6 proof. -/
structure RUM3LambdaCertificate (μWorse : PMF (Ranking 1)) : Prop where
  lambda1_half : (1 : ℝ) / 2 < rum3Lambda1 μWorse
  lambda1_lt_one : rum3Lambda1 μWorse < 1
  lambda12 : rum3Lambda1 μWorse < rum3Lambda2 μWorse
  lambda3_half : (1 : ℝ) / 2 < rum3Lambda3 μWorse

/-- The first-choice-delta side of the paper's Theorem 6 proof. -/
structure RUM3DeltaCertificate
    (μBetter μWorse : PMF (Ranking 1)) : Prop where
  delta_top_pos :
    0 <
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1)
  delta_middle_le_top :
    firstChoiceProb μBetter (1 : Candidate 1) -
        firstChoiceProb μWorse (1 : Candidate 1) ≤
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1)
  delta_bottom_nonpos :
    firstChoiceProb μBetter (2 : Candidate 1) -
        firstChoiceProb μWorse (2 : Candidate 1) ≤ 0

/--
Named finite certificate for Appendix C / Definition 2 in the three-candidate
RUM proof.

The fields are exactly the source-proof conditional-gain obligations after
conditioning on the shared first choice `τ₁ = x_k`.
-/
structure RUM3Definition2Certificate
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) : Prop where
  first0_gain :
    0 < firstChoiceProb μ (0 : Candidate 1) →
      0 < pmfConditionalExp μ
        (fun τ => (0 : Candidate 1) = firstChoice τ)
        (fun τ =>
          pmfExp μ (fun π =>
            value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))
  first1_gain :
    0 < firstChoiceProb μ (1 : Candidate 1) →
      0 < pmfConditionalExp μ
        (fun τ => (1 : Candidate 1) = firstChoice τ)
        (fun τ =>
          pmfExp μ (fun π =>
            value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))
  first2_gain :
    0 < firstChoiceProb μ (2 : Candidate 1) →
      0 < pmfConditionalExp μ
        (fun τ => (2 : Candidate 1) = firstChoice τ)
        (fun τ =>
          pmfExp μ (fun π =>
            value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))

theorem rum3_prefersIndependentReranking_of_definition2Certificate
    {μ : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (cert : RUM3Definition2Certificate μ value) :
    Model.PrefersIndependentReranking μ value := by
  refine prefersIndependentReranking_of_firstChoiceProb_conditional_gain_pos
    (μ := μ) (value := value) ?_
  intro c hc
  fin_cases c
  · exact cert.first0_gain hc
  · exact cert.first1_gain hc
  · exact cert.first2_gain hc

/--
Pairwise-probability form of Appendix C / Definition 2 for three candidates.

For each possible first choice, the unconditional probability that the better
remaining candidate beats the worse remaining candidate is larger than the
conditional probability that the shared ranking puts that better remaining
candidate second.
-/
structure RUM3Definition2PairwiseGapCertificate
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) : Prop where
  value01 : value (1 : Candidate 1) < value (0 : Candidate 1)
  value12 : value (2 : Candidate 1) < value (1 : Candidate 1)
  first0_second1_lt_lambda1 :
    pmfConditionalProb μ
        (fun τ => (0 : Candidate 1) = firstChoice τ)
        (fun τ => secondChoice τ = (1 : Candidate 1)) <
      rum3Lambda1 μ
  first1_second0_lt_lambda2 :
    pmfConditionalProb μ
        (fun τ => (1 : Candidate 1) = firstChoice τ)
        (fun τ => secondChoice τ = (0 : Candidate 1)) <
      rum3Lambda2 μ
  first2_second0_lt_lambda3 :
    pmfConditionalProb μ
        (fun τ => (2 : Candidate 1) = firstChoice τ)
        (fun τ => secondChoice τ = (0 : Candidate 1)) <
      rum3Lambda3 μ

/--
Paper-facing negative-correlation form of Appendix C / Definition 2 for three
candidates.

For each possible shared first choice, conditioning on that candidate being top
strictly lowers the probability that the better of the two remaining candidates
beats the worse one.
-/
structure RUM3Definition2NegativeCorrelationCertificate
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) : Prop where
  value01 : value (1 : Candidate 1) < value (0 : Candidate 1)
  value12 : value (2 : Candidate 1) < value (1 : Candidate 1)
  first0_best1_cond_lt_uncond :
    pmfConditionalProb μ
        (fun τ => (0 : Candidate 1) = firstChoice τ)
        (fun τ => bestRemainingAfter τ (0 : Candidate 1) = (1 : Candidate 1)) <
      pmfProb μ
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
  first1_best0_cond_lt_uncond :
    pmfConditionalProb μ
        (fun τ => (1 : Candidate 1) = firstChoice τ)
        (fun τ => bestRemainingAfter τ (1 : Candidate 1) = (0 : Candidate 1)) <
      pmfProb μ
        (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))
  first2_best0_cond_lt_uncond :
    pmfConditionalProb μ
        (fun τ => (2 : Candidate 1) = firstChoice τ)
        (fun τ => bestRemainingAfter τ (2 : Candidate 1) = (0 : Candidate 1)) <
      pmfProb μ
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))

theorem rum3Definition2NegativeCorrelationCertificate_of_inter_lt_mul
    {μ : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hfirst0 : 0 < pmfProb μ (fun τ => (0 : Candidate 1) = firstChoice τ))
    (hfirst1 : 0 < pmfProb μ (fun τ => (1 : Candidate 1) = firstChoice τ))
    (hfirst2 : 0 < pmfProb μ (fun τ => (2 : Candidate 1) = firstChoice τ))
    (h0 :
      pmfProb μ
          (fun τ =>
            bestRemainingAfter τ (0 : Candidate 1) = (1 : Candidate 1) ∧
              (0 : Candidate 1) = firstChoice τ) <
        pmfProb μ
          (fun τ => bestRemainingAfter τ (0 : Candidate 1) = (1 : Candidate 1)) *
          pmfProb μ (fun τ => (0 : Candidate 1) = firstChoice τ))
    (h1 :
      pmfProb μ
          (fun τ =>
            bestRemainingAfter τ (1 : Candidate 1) = (0 : Candidate 1) ∧
              (1 : Candidate 1) = firstChoice τ) <
        pmfProb μ
          (fun τ => bestRemainingAfter τ (1 : Candidate 1) = (0 : Candidate 1)) *
          pmfProb μ (fun τ => (1 : Candidate 1) = firstChoice τ))
    (h2 :
      pmfProb μ
          (fun τ =>
            bestRemainingAfter τ (2 : Candidate 1) = (0 : Candidate 1) ∧
              (2 : Candidate 1) = firstChoice τ) <
        pmfProb μ
          (fun τ => bestRemainingAfter τ (2 : Candidate 1) = (0 : Candidate 1)) *
          pmfProb μ (fun τ => (2 : Candidate 1) = firstChoice τ)) :
    RUM3Definition2NegativeCorrelationCertificate μ value where
  value01 := hvalue01
  value12 := hvalue12
  first0_best1_cond_lt_uncond :=
    pmfConditionalProb_lt_of_inter_lt_mul μ
      (fun τ => bestRemainingAfter τ (0 : Candidate 1) = (1 : Candidate 1))
      (fun τ => (0 : Candidate 1) = firstChoice τ) hfirst0 h0
  first1_best0_cond_lt_uncond :=
    pmfConditionalProb_lt_of_inter_lt_mul μ
      (fun τ => bestRemainingAfter τ (1 : Candidate 1) = (0 : Candidate 1))
      (fun τ => (1 : Candidate 1) = firstChoice τ) hfirst1 h1
  first2_best0_cond_lt_uncond :=
    pmfConditionalProb_lt_of_inter_lt_mul μ
      (fun τ => bestRemainingAfter τ (2 : Candidate 1) = (0 : Candidate 1))
      (fun τ => (2 : Candidate 1) = firstChoice τ) hfirst2 h2

theorem rum3Definition2NegativeCorrelationCertificate_of_measure_inter_lt_mul
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    {value : Candidate 1 → ℝ}
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hfirst0 :
      0 < measureProb ν
        (fun ω => (0 : Candidate 1) = firstChoice (rank ω)))
    (hfirst1 :
      0 < measureProb ν
        (fun ω => (1 : Candidate 1) = firstChoice (rank ω)))
    (hfirst2 :
      0 < measureProb ν
        (fun ω => (2 : Candidate 1) = firstChoice (rank ω)))
    (h0 :
      measureProb ν
          (fun ω =>
            bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
              (0 : Candidate 1) = firstChoice (rank ω)) <
        measureProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)) *
          measureProb ν
            (fun ω => (0 : Candidate 1) = firstChoice (rank ω)))
    (h1 :
      measureProb ν
          (fun ω =>
            bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) ∧
              (1 : Candidate 1) = firstChoice (rank ω)) <
        measureProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)) *
          measureProb ν
            (fun ω => (1 : Candidate 1) = firstChoice (rank ω)))
    (h2 :
      measureProb ν
          (fun ω =>
            bestRemainingAfter (rank ω) (2 : Candidate 1) = (0 : Candidate 1) ∧
              (2 : Candidate 1) = firstChoice (rank ω)) <
        measureProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)) *
          measureProb ν
            (fun ω => (2 : Candidate 1) = firstChoice (rank ω))) :
    RUM3Definition2NegativeCorrelationCertificate
      (rumRankingPMFOfMeasure ν rank hrank) value := by
  refine rum3Definition2NegativeCorrelationCertificate_of_inter_lt_mul
    hvalue01 hvalue12 ?hfirst0 ?hfirst1 ?hfirst2 ?h0 ?h1 ?h2
  · rw [rumRankingPMFOfMeasure_eventProb]
    exact hfirst0
  · rw [rumRankingPMFOfMeasure_eventProb]
    exact hfirst1
  · rw [rumRankingPMFOfMeasure_eventProb]
    exact hfirst2
  · rw [rumRankingPMFOfMeasure_eventProb]
    rw [rumRankingPMFOfMeasure_eventProb]
    rw [rumRankingPMFOfMeasure_eventProb]
    exact h0
  · rw [rumRankingPMFOfMeasure_eventProb]
    rw [rumRankingPMFOfMeasure_eventProb]
    rw [rumRankingPMFOfMeasure_eventProb]
    exact h1
  · rw [rumRankingPMFOfMeasure_eventProb]
    rw [rumRankingPMFOfMeasure_eventProb]
    rw [rumRankingPMFOfMeasure_eventProb]
    exact h2

/--
Concrete score-order constructor for the three-candidate Definition-2
negative-correlation certificate.

This exposes the remaining source-model obligations as primitive inequalities
between the three realized score coordinates, instead of hiding them behind
ranking-event predicates.
-/
theorem rum3Definition2NegativeCorrelationCertificate_of_score_inter_lt_mul
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {r1 r2 r3 : Ω → ℝ}
    (hr1 : Measurable r1) (hr2 : Measurable r2) (hr3 : Measurable r3)
    {value : Candidate 1 → ℝ}
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hfirst0 :
      0 < measureProb ν
        (fun ω => r2 ω ≤ r1 ω ∧ r3 ω ≤ r1 ω))
    (hfirst1 :
      0 < measureProb ν
        (fun ω => r1 ω < r2 ω ∧ r3 ω ≤ r2 ω))
    (hfirst2 :
      0 < measureProb ν
        (fun ω => r1 ω < r3 ω ∧ r2 ω < r3 ω))
    (h0 :
      measureProb ν
          (fun ω => r3 ω ≤ r2 ω ∧ r2 ω ≤ r1 ω) <
        measureProb ν (fun ω => r3 ω ≤ r2 ω) *
          measureProb ν
            (fun ω => r2 ω ≤ r1 ω ∧ r3 ω ≤ r1 ω))
    (h1 :
      measureProb ν
          (fun ω => r3 ω ≤ r1 ω ∧ r1 ω < r2 ω) <
        measureProb ν (fun ω => r3 ω ≤ r1 ω) *
          measureProb ν
            (fun ω => r1 ω < r2 ω ∧ r3 ω ≤ r2 ω))
    (h2 :
      measureProb ν
          (fun ω => r2 ω ≤ r1 ω ∧ r1 ω < r3 ω) <
        measureProb ν (fun ω => r2 ω ≤ r1 ω) *
          measureProb ν
            (fun ω => r1 ω < r3 ω ∧ r2 ω < r3 ω)) :
    RUM3Definition2NegativeCorrelationCertificate
      (rumRankingPMFOfMeasure ν (rum3RankByScoreFns r1 r2 r3)
        (rum3RankByScoreFns_measurable hr1 hr2 hr3)) value := by
  let rank : Ω → Ranking 1 := rum3RankByScoreFns r1 r2 r3
  have hrank : Measurable rank := rum3RankByScoreFns_measurable hr1 hr2 hr3
  have hfirst0_eq :
      measureProb ν (fun ω => (0 : Candidate 1) = firstChoice (rank ω)) =
        measureProb ν
          (fun ω => r2 ω ≤ r1 ω ∧ r3 ω ≤ r1 ω) := by
    unfold measureProb
    exact congrArg (fun s : Set Ω => (ν s).toReal)
      (Set.ext fun ω =>
        rum3RankByScoreFns_first0_iff (r1 := r1) (r2 := r2) (r3 := r3) ω)
  have hfirst1_eq :
      measureProb ν (fun ω => (1 : Candidate 1) = firstChoice (rank ω)) =
        measureProb ν
          (fun ω => r1 ω < r2 ω ∧ r3 ω ≤ r2 ω) := by
    unfold measureProb
    exact congrArg (fun s : Set Ω => (ν s).toReal)
      (Set.ext fun ω =>
        rum3RankByScoreFns_first1_iff (r1 := r1) (r2 := r2) (r3 := r3) ω)
  have hfirst2_eq :
      measureProb ν (fun ω => (2 : Candidate 1) = firstChoice (rank ω)) =
        measureProb ν
          (fun ω => r1 ω < r3 ω ∧ r2 ω < r3 ω) := by
    unfold measureProb
    exact congrArg (fun s : Set Ω => (ν s).toReal)
      (Set.ext fun ω =>
        rum3RankByScoreFns_first2_iff (r1 := r1) (r2 := r2) (r3 := r3) ω)
  have hbest0_eq :
      measureProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)) =
        measureProb ν (fun ω => r3 ω ≤ r2 ω) := by
    unfold measureProb
    exact congrArg (fun s : Set Ω => (ν s).toReal)
      (Set.ext fun ω =>
        rum3RankByScoreFns_remove0_eq1_iff (r1 := r1) (r2 := r2) (r3 := r3) ω)
  have hbest1_eq :
      measureProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)) =
        measureProb ν (fun ω => r3 ω ≤ r1 ω) := by
    unfold measureProb
    exact congrArg (fun s : Set Ω => (ν s).toReal)
      (Set.ext fun ω =>
        rum3RankByScoreFns_remove1_eq0_iff (r1 := r1) (r2 := r2) (r3 := r3) ω)
  have hbest2_eq :
      measureProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)) =
        measureProb ν (fun ω => r2 ω ≤ r1 ω) := by
    unfold measureProb
    exact congrArg (fun s : Set Ω => (ν s).toReal)
      (Set.ext fun ω =>
        rum3RankByScoreFns_remove2_eq0_iff (r1 := r1) (r2 := r2) (r3 := r3) ω)
  have hinter0_eq :
      measureProb ν
          (fun ω =>
            bestRemainingAfter (rank ω) (0 : Candidate 1) =
                (1 : Candidate 1) ∧
              (0 : Candidate 1) = firstChoice (rank ω)) =
        measureProb ν
          (fun ω => r3 ω ≤ r2 ω ∧ r2 ω ≤ r1 ω) := by
    unfold measureProb
    exact congrArg (fun s : Set Ω => (ν s).toReal)
      (Set.ext fun ω =>
        rum3RankByScoreFns_def2_event0_iff (r1 := r1) (r2 := r2) (r3 := r3) ω)
  have hinter1_eq :
      measureProb ν
          (fun ω =>
            bestRemainingAfter (rank ω) (1 : Candidate 1) =
                (0 : Candidate 1) ∧
              (1 : Candidate 1) = firstChoice (rank ω)) =
        measureProb ν
          (fun ω => r3 ω ≤ r1 ω ∧ r1 ω < r2 ω) := by
    unfold measureProb
    exact congrArg (fun s : Set Ω => (ν s).toReal)
      (Set.ext fun ω =>
        rum3RankByScoreFns_def2_event1_iff (r1 := r1) (r2 := r2) (r3 := r3) ω)
  have hinter2_eq :
      measureProb ν
          (fun ω =>
            bestRemainingAfter (rank ω) (2 : Candidate 1) =
                (0 : Candidate 1) ∧
              (2 : Candidate 1) = firstChoice (rank ω)) =
        measureProb ν
          (fun ω => r2 ω ≤ r1 ω ∧ r1 ω < r3 ω) := by
    unfold measureProb
    exact congrArg (fun s : Set Ω => (ν s).toReal)
      (Set.ext fun ω =>
        rum3RankByScoreFns_def2_event2_iff (r1 := r1) (r2 := r2) (r3 := r3) ω)
  refine rum3Definition2NegativeCorrelationCertificate_of_measure_inter_lt_mul
    (ν := ν) (rank := rank) (hrank := hrank)
    hvalue01 hvalue12 ?_ ?_ ?_ ?_ ?_ ?_
  · rwa [hfirst0_eq]
  · rwa [hfirst1_eq]
  · rwa [hfirst2_eq]
  · rwa [hinter0_eq, hbest0_eq, hfirst0_eq]
  · rwa [hinter1_eq, hbest1_eq, hfirst1_eq]
  · rwa [hinter2_eq, hbest2_eq, hfirst2_eq]

/--
Appendix C / Theorem 8, Definition 2 endpoint for three Gaussian scores.

For independent Gaussian score signals with common variance `1 / 2` and ordered
means `x₁ > x₂ > x₃`, the induced three-candidate ranking law satisfies the
negative-correlation certificate used by Definition 2.
-/
theorem theorem8GaussianDefinition2_negativeCorrelationCertificate
    {x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    RUM3Definition2NegativeCorrelationCertificate
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) value := by
  let ν := theorem8GaussianDefinition2ScoreMeasure x1 x2 x3
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, theorem8GaussianDefinition2ScoreMeasure, theorem8GaussianPairMeasure]
    infer_instance
  have h0 :
      measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score2 ω ∧
              theorem8GaussianDefinition2Score2 ω ≤
                theorem8GaussianDefinition2Score1 ω) <
        measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score2 ω) *
          measureProb ν
            (fun ω =>
              theorem8GaussianDefinition2Score2 ω ≤
                  theorem8GaussianDefinition2Score1 ω ∧
                theorem8GaussianDefinition2Score3 ω ≤
                  theorem8GaussianDefinition2Score1 ω) := by
    simpa [ν] using
      theorem8GaussianDefinition2_event0_score_inter_lt_mul
        (x1 := x1) (x2 := x2) (x3 := x3) hx23
  have h1 :
      measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score1 ω ∧
              theorem8GaussianDefinition2Score1 ω <
                theorem8GaussianDefinition2Score2 ω) <
        measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
          measureProb ν
            (fun ω =>
              theorem8GaussianDefinition2Score1 ω <
                  theorem8GaussianDefinition2Score2 ω ∧
                theorem8GaussianDefinition2Score3 ω ≤
                  theorem8GaussianDefinition2Score2 ω) := by
    simpa [ν] using
      theorem8GaussianDefinition2_event1_score_inter_lt_mul
        (x1 := x1) (x2 := x2) (x3 := x3) (lt_trans hx23 hx12)
  have h2 :
      measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
                theorem8GaussianDefinition2Score1 ω ∧
              theorem8GaussianDefinition2Score1 ω <
                theorem8GaussianDefinition2Score3 ω) <
        measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
          measureProb ν
            (fun ω =>
              theorem8GaussianDefinition2Score1 ω <
                  theorem8GaussianDefinition2Score3 ω ∧
                theorem8GaussianDefinition2Score2 ω <
                  theorem8GaussianDefinition2Score3 ω) := by
    simpa [ν] using
      theorem8GaussianDefinition2_event2_score_inter_lt_mul
        (x1 := x1) (x2 := x2) (x3 := x3) hx12
  have right_factor_pos :
      ∀ {L C B : ℝ}, 0 ≤ L → 0 ≤ C → L < C * B → 0 < B := by
    intro L C B hL hC hlt
    by_contra hnot
    have hB : B ≤ 0 := le_of_not_gt hnot
    have hCB : C * B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC hB
    exact (not_lt_of_ge (le_trans hCB hL)) hlt
  have hfirst0 :
      0 < measureProb ν
        (fun ω =>
          theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω) := by
    refine right_factor_pos ?_ ?_ h0
    · unfold measureProb
      exact ENNReal.toReal_nonneg
    · unfold measureProb
      exact ENNReal.toReal_nonneg
  have hfirst1 :
      0 < measureProb ν
        (fun ω =>
          theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score2 ω ∧
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score2 ω) := by
    refine right_factor_pos ?_ ?_ h1
    · unfold measureProb
      exact ENNReal.toReal_nonneg
    · unfold measureProb
      exact ENNReal.toReal_nonneg
  have hfirst2 :
      0 < measureProb ν
        (fun ω =>
          theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score3 ω ∧
            theorem8GaussianDefinition2Score2 ω <
              theorem8GaussianDefinition2Score3 ω) := by
    refine right_factor_pos ?_ ?_ h2
    · unfold measureProb
      exact ENNReal.toReal_nonneg
    · unfold measureProb
      exact ENNReal.toReal_nonneg
  exact
    rum3Definition2NegativeCorrelationCertificate_of_score_inter_lt_mul
      (ν := ν)
      theorem8GaussianDefinition2Score1_measurable
      theorem8GaussianDefinition2Score2_measurable
      theorem8GaussianDefinition2Score3_measurable
      hvalue01 hvalue12 hfirst0 hfirst1 hfirst2 h0 h1 h2

/--
Independent three-score Laplace ranking law used in the Definition-2 endpoint.
The positivity proof is explicit because the Laplace density normalizes only
for positive rate.
-/
noncomputable def theorem7LaplacianDefinition2RankingPMF
    (lam x1 x2 x3 : ℝ) (hlam : 0 < lam) : PMF (Ranking 1) :=
  letI : IsProbabilityMeasure
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3) :=
    theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure
      (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam
  rumRankingPMFOfMeasure
    (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
    (rum3RankByScoreFns
      theorem7LaplacianDefinition2Score1
      theorem7LaplacianDefinition2Score2
      theorem7LaplacianDefinition2Score3)
    (rum3RankByScoreFns_measurable
      theorem7LaplacianDefinition2Score1_measurable
      theorem7LaplacianDefinition2Score2_measurable
      theorem7LaplacianDefinition2Score3_measurable)

theorem theorem7LaplacianDefinition2RankingPMF_ranking102_toReal_pos
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) :
    0 <
      ((theorem7LaplacianDefinition2RankingPMF lam x1 x2 x3 hlam)
        rum3Ranking102).toReal := by
  letI : IsProbabilityMeasure
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3) :=
    theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure
      (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam
  simpa [theorem7LaplacianDefinition2RankingPMF] using
    (rumRankingPMFOfMeasure_rankByScoreFns_ranking102_toReal_pos
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
      theorem7LaplacianDefinition2Score1
      theorem7LaplacianDefinition2Score2
      theorem7LaplacianDefinition2Score3
      (rum3RankByScoreFns_measurable
        theorem7LaplacianDefinition2Score1_measurable
        theorem7LaplacianDefinition2Score2_measurable
        theorem7LaplacianDefinition2Score3_measurable)
      (theorem7LaplacianDefinition2_ranking102_measureProb_pos
        (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam))

/--
Changing the displayed Laplace rate by equality does not change the induced
ranking PMF; the positivity proof is proof-irrelevant.
-/
theorem theorem7LaplacianDefinition2RankingPMF_congr_rate
    {lam lam' x1 x2 x3 : ℝ}
    (h : lam = lam') (hlam : 0 < lam) (hlam' : 0 < lam') :
    theorem7LaplacianDefinition2RankingPMF lam x1 x2 x3 hlam =
      theorem7LaplacianDefinition2RankingPMF lam' x1 x2 x3 hlam' := by
  cases h
  rfl

/--
Laplace source-model concentration: if the rate parameter tends to infinity,
the induced ranking law converges atomwise to the true ranking `[0,1,2]`.
-/
theorem theorem7LaplacianDefinition2RankingPMF_atomwise_concentration
    {lam : ℝ → ℝ} (hlam : Filter.Tendsto lam Filter.atTop Filter.atTop)
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    ∀ lower δ, 0 < δ →
      ∃ hi, lower < hi ∧
        ∃ hpos : 0 < lam hi,
          ∀ π : Ranking 1,
            |((theorem7LaplacianDefinition2RankingPMF
                (lam hi) x1 x2 x3 hpos) π).toReal -
              (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) π).toReal)| < δ := by
  intro lower δ hδ
  have hsum :=
    theorem7LaplacianDefinition2ScoreMeasure_adjacent_inversions_tendsto_atTop_zero
      (lam := lam) hlam (x1 := x1) (x2 := x2) (x3 := x3) hx12 hx23
  have hsmall :
      ∀ᶠ θ : ℝ in Filter.atTop,
        measureProb (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score1 ω <
              theorem7LaplacianDefinition2Score2 ω) +
        measureProb (theorem7LaplacianDefinition2ScoreMeasure (lam θ) x1 x2 x3)
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω <
              theorem7LaplacianDefinition2Score3 ω) < δ :=
    hsum.eventually (Iio_mem_nhds hδ)
  have hpos_ev : ∀ᶠ θ : ℝ in Filter.atTop, 0 < lam θ :=
    hlam.eventually (Filter.eventually_gt_atTop (0 : ℝ))
  rcases Filter.eventually_atTop.1
      (hsmall.and ((Filter.eventually_gt_atTop lower).and hpos_ev)) with
    ⟨hi, hhi⟩
  refine ⟨hi, (hhi hi le_rfl).2.1, ?_⟩
  have hpair := (hhi hi le_rfl).1
  have hpos := (hhi hi le_rfl).2.2
  let μ := theorem7LaplacianDefinition2ScoreMeasure (lam hi) x1 x2 x3
  haveI : IsProbabilityMeasure μ :=
    theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure
      (lam := lam hi) (x1 := x1) (x2 := x2) (x3 := x3) hpos
  refine ⟨hpos, ?_⟩
  simpa [μ, theorem7LaplacianDefinition2RankingPMF] using
    rumRankingPMFOfMeasure_rankByScoreFns_atomwise_close_to_pure012_of_pair_inversions_lt
      μ theorem7LaplacianDefinition2Score1 theorem7LaplacianDefinition2Score2
      theorem7LaplacianDefinition2Score3
      (rum3RankByScoreFns_measurable
        theorem7LaplacianDefinition2Score1_measurable
        theorem7LaplacianDefinition2Score2_measurable
        theorem7LaplacianDefinition2Score3_measurable)
      hδ hpair

/--
Contracted three-score Laplace ranking law.  This is the same source law as
`theorem7LaplacianDefinition2RankingPMF`, but the realized scores are
contracted toward their candidate values before ranking.
-/
noncomputable def theorem7LaplacianDefinition2ContractRankingPMF
    (lam t x1 x2 x3 : ℝ) (hlam : 0 < lam) : PMF (Ranking 1) :=
  letI : IsProbabilityMeasure
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3) :=
    theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure
      (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam
  rumRankingPMFOfMeasure
    (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
    (rum3ContractRankByScoreFns
      t x1 x2 x3
      theorem7LaplacianDefinition2Score1
      theorem7LaplacianDefinition2Score2
      theorem7LaplacianDefinition2Score3)
    (rum3ContractRankByScoreFns_measurable
      theorem7LaplacianDefinition2Score1_measurable
      theorem7LaplacianDefinition2Score2_measurable
      theorem7LaplacianDefinition2Score3_measurable
      t x1 x2 x3)

/--
Laplace contraction transport for the induced three-candidate ranking law.

Ranking the contracted scores under Laplace rate `lam` has the same finite
ranking law as ranking raw scores under Laplace rate `lam / t`.
-/
theorem theorem7LaplacianDefinition2RankingPMF_contract_eq
    {lam t x1 x2 x3 : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    theorem7LaplacianDefinition2ContractRankingPMF lam t x1 x2 x3 hlam =
      theorem7LaplacianDefinition2RankingPMF (lam / t) x1 x2 x3
        (div_pos hlam ht) := by
  have hrate : 0 < lam / t := div_pos hlam ht
  haveI : IsProbabilityMeasure
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3) :=
    theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure
      (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam
  haveI : IsProbabilityMeasure
      (theorem7LaplacianDefinition2ScoreMeasure (lam / t) x1 x2 x3) :=
    theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure
      (lam := lam / t) (x1 := x1) (x2 := x2) (x3 := x3) hrate
  dsimp [theorem7LaplacianDefinition2ContractRankingPMF,
    theorem7LaplacianDefinition2RankingPMF]
  refine
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eq_of_measurePreserving
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
      (theorem7LaplacianDefinition2ScoreMeasure (lam / t) x1 x2 x3)
      (theorem7LaplacianDefinition2ContractMap t x1 x2 x3)
      (theorem7LaplacianDefinition2ContractMap_measurePreserving
        (lam := lam) (t := t) (x1 := x1) (x2 := x2) (x3 := x3)
        hlam ht)
      (rum3ContractRankByScoreFns
        t x1 x2 x3
        theorem7LaplacianDefinition2Score1
        theorem7LaplacianDefinition2Score2
        theorem7LaplacianDefinition2Score3)
      (rum3ContractRankByScoreFns_measurable
        theorem7LaplacianDefinition2Score1_measurable
        theorem7LaplacianDefinition2Score2_measurable
        theorem7LaplacianDefinition2Score3_measurable
        t x1 x2 x3)
      (rum3RankByScoreFns
        theorem7LaplacianDefinition2Score1
        theorem7LaplacianDefinition2Score2
        theorem7LaplacianDefinition2Score3)
      (rum3RankByScoreFns_measurable
        theorem7LaplacianDefinition2Score1_measurable
        theorem7LaplacianDefinition2Score2_measurable
        theorem7LaplacianDefinition2Score3_measurable)
      ?_
  intro ω
  rfl

theorem theorem8GaussianDefinition2RankingPMFStd_contract_atom_continuousAt_one
    {σ x1 x2 x3 : ℝ} (hσ : σ ≠ 0) (π : Ranking 1) :
    ContinuousAt
      (fun t : ℝ =>
        ((rumRankingPMFOfMeasure
          (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
          (rum3ContractRankByScoreFns
            t x1 x2 x3
            theorem8GaussianDefinition2Score1
            theorem8GaussianDefinition2Score2
            theorem8GaussianDefinition2Score3)
          (rum3ContractRankByScoreFns_measurable
            theorem8GaussianDefinition2Score1_measurable
            theorem8GaussianDefinition2Score2_measurable
            theorem8GaussianDefinition2Score3_measurable
            t x1 x2 x3))
          π).toReal)
      1 :=
  rumRankingPMFOfMeasure_contractRankByScoreFns_atom_continuousAt_one
    (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
    x1 x2 x3
    theorem8GaussianDefinition2Score1
    theorem8GaussianDefinition2Score2
    theorem8GaussianDefinition2Score3
    theorem8GaussianDefinition2Score1_measurable
    theorem8GaussianDefinition2Score2_measurable
    theorem8GaussianDefinition2Score3_measurable
    (theorem8GaussianDefinition2ScoreMeasureStd_no_score_ties_ae hσ) π

theorem theorem8GaussianDefinition2RankingPMFStd_atom_epsilonContinuousAt
    {θ x1 x2 x3 : ℝ} (hθ : 0 < θ) (π : Ranking 1) :
    AppliedModelingLib.EpsilonContinuousAt
      (fun θ' : ℝ =>
        ((rumRankingPMFOfMeasure
          (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ') x1 x2 x3)
          (rum3RankByScoreFns
            theorem8GaussianDefinition2Score1
            theorem8GaussianDefinition2Score2
            theorem8GaussianDefinition2Score3)
          (rum3RankByScoreFns_measurable
            theorem8GaussianDefinition2Score1_measurable
            theorem8GaussianDefinition2Score2_measurable
            theorem8GaussianDefinition2Score3_measurable))
          π).toReal)
      θ := by
  let σ0 : ℝ := 1 / θ
  let G : ℝ → ℝ := fun t : ℝ =>
    ((rumRankingPMFOfMeasure
      (theorem8GaussianDefinition2ScoreMeasureStd σ0 x1 x2 x3)
      (rum3ContractRankByScoreFns
        t x1 x2 x3
        theorem8GaussianDefinition2Score1
        theorem8GaussianDefinition2Score2
        theorem8GaussianDefinition2Score3)
      (rum3ContractRankByScoreFns_measurable
        theorem8GaussianDefinition2Score1_measurable
        theorem8GaussianDefinition2Score2_measurable
        theorem8GaussianDefinition2Score3_measurable
        t x1 x2 x3))
      π).toReal
  have hσ0 : σ0 ≠ 0 := by
    dsimp [σ0]
    exact one_div_ne_zero hθ.ne'
  have hG : ContinuousAt G 1 := by
    simpa [G] using
      theorem8GaussianDefinition2RankingPMFStd_contract_atom_continuousAt_one
        (σ := σ0) (x1 := x1) (x2 := x2) (x3 := x3) hσ0 π
  have hmap : ContinuousAt (fun θ' : ℝ => θ / θ') θ := by
    simpa [div_eq_mul_inv] using
      (continuousAt_const.mul (continuousAt_id.inv₀ hθ.ne'))
  have hG_at : ContinuousAt G (θ / θ) := by
    simpa [div_self hθ.ne'] using hG
  have hcomp : ContinuousAt (fun θ' : ℝ => G (θ / θ')) θ :=
    hG_at.comp hmap
  have heq :
      (fun θ' : ℝ => G (θ / θ')) =
        (fun θ' : ℝ =>
          ((rumRankingPMFOfMeasure
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ') x1 x2 x3)
            (rum3RankByScoreFns
              theorem8GaussianDefinition2Score1
              theorem8GaussianDefinition2Score2
              theorem8GaussianDefinition2Score3)
            (rum3RankByScoreFns_measurable
              theorem8GaussianDefinition2Score1_measurable
              theorem8GaussianDefinition2Score2_measurable
              theorem8GaussianDefinition2Score3_measurable))
            π).toReal) := by
    funext θ'
    dsimp [G, σ0]
    rw [theorem8GaussianDefinition2RankingPMFStd_contract_eq]
    have hstd : (θ / θ') * (1 / θ) = 1 / θ' := by
      by_cases hθ' : θ' = 0
      · simp [hθ']
      · field_simp [hθ.ne', hθ']
    rw [hstd]
  exact AppliedModelingLib.epsilonContinuousAt_of_continuousAt (by simpa [heq] using hcomp)

theorem theorem7LaplacianDefinition2ContractRankingPMF_atom_continuousAt_one
    {lam x1 x2 x3 : ℝ} (hlam : 0 < lam) (π : Ranking 1) :
    ContinuousAt
      (fun t : ℝ =>
        ((theorem7LaplacianDefinition2ContractRankingPMF
          lam t x1 x2 x3 hlam) π).toReal)
      1 := by
  haveI : IsProbabilityMeasure
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3) :=
    theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure
      (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam
  unfold theorem7LaplacianDefinition2ContractRankingPMF
  exact
    rumRankingPMFOfMeasure_contractRankByScoreFns_atom_continuousAt_one
      (theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3)
      x1 x2 x3
      theorem7LaplacianDefinition2Score1
      theorem7LaplacianDefinition2Score2
      theorem7LaplacianDefinition2Score3
      theorem7LaplacianDefinition2Score1_measurable
      theorem7LaplacianDefinition2Score2_measurable
      theorem7LaplacianDefinition2Score3_measurable
      theorem7LaplacianDefinition2ScoreMeasure_no_score_ties_ae π

theorem theorem7LaplacianDefinition2RankingPMF_canonical_atom_epsilonContinuousAt
    {θ x1 x2 x3 : ℝ} (hθ : 0 < θ) (π : Ranking 1) :
    AppliedModelingLib.EpsilonContinuousAt
      (fun θ' : ℝ =>
        if hθ' : 0 < θ' then
          ((theorem7LaplacianDefinition2RankingPMF θ' x1 x2 x3 hθ') π).toReal
        else
          ((theorem7LaplacianDefinition2RankingPMF θ x1 x2 x3 hθ) π).toReal)
      θ := by
  let G : ℝ → ℝ := fun t : ℝ =>
    ((theorem7LaplacianDefinition2ContractRankingPMF θ t x1 x2 x3 hθ)
      π).toReal
  have hG : ContinuousAt G 1 := by
    simpa [G] using
      theorem7LaplacianDefinition2ContractRankingPMF_atom_continuousAt_one
        (lam := θ) (x1 := x1) (x2 := x2) (x3 := x3) hθ π
  have hmap : ContinuousAt (fun θ' : ℝ => θ / θ') θ := by
    simpa [div_eq_mul_inv] using
      (continuousAt_const.mul (continuousAt_id.inv₀ hθ.ne'))
  have hG_at : ContinuousAt G (θ / θ) := by
    simpa [div_self hθ.ne'] using hG
  have hsource :
      AppliedModelingLib.EpsilonContinuousAt (fun θ' : ℝ => G (θ / θ')) θ :=
    AppliedModelingLib.epsilonContinuousAt_of_continuousAt (hG_at.comp hmap)
  refine AppliedModelingLib.epsilonContinuousAt_congr_eventually hsource ?_ ?_
  · filter_upwards [Ioi_mem_nhds hθ] with θ' hθ'_mem
    have hθ' : 0 < θ' := hθ'_mem
    dsimp [G]
    rw [theorem7LaplacianDefinition2RankingPMF_contract_eq
      (hlam := hθ) (ht := div_pos hθ hθ')]
    have hrate : θ / (θ / θ') = θ' := by
      field_simp [hθ.ne', hθ'.ne']
    have hpmf :
        theorem7LaplacianDefinition2RankingPMF
            (θ / (θ / θ')) x1 x2 x3 (div_pos hθ (div_pos hθ hθ')) =
          theorem7LaplacianDefinition2RankingPMF θ' x1 x2 x3 hθ' :=
      theorem7LaplacianDefinition2RankingPMF_congr_rate
        hrate (div_pos hθ (div_pos hθ hθ')) hθ'
    rw [hpmf]
    simp [hθ']
  · dsimp [G]
    have hdiv : θ / θ = (1 : ℝ) := div_self hθ.ne'
    rw [hdiv]
    rw [theorem7LaplacianDefinition2RankingPMF_contract_eq
      (hlam := hθ) (ht := zero_lt_one)]
    have hpmf :
        theorem7LaplacianDefinition2RankingPMF
            (θ / 1) x1 x2 x3 (div_pos hθ zero_lt_one) =
          theorem7LaplacianDefinition2RankingPMF θ x1 x2 x3 hθ :=
      theorem7LaplacianDefinition2RankingPMF_congr_rate
        (by ring) (div_pos hθ zero_lt_one) hθ
    rw [hpmf]
    simp [hθ]

/--
Appendix C / Theorem 7, Definition 2 endpoint for three Laplace scores.

For independent Laplace score signals with common positive rate `lam` and
ordered locations `x₁ > x₂ > x₃`, the induced three-candidate ranking law
satisfies the negative-correlation certificate used by Definition 2.
-/
theorem theorem7LaplacianDefinition2_negativeCorrelationCertificate
    {lam x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    RUM3Definition2NegativeCorrelationCertificate
      (theorem7LaplacianDefinition2RankingPMF lam x1 x2 x3 hlam) value := by
  let ν := theorem7LaplacianDefinition2ScoreMeasure lam x1 x2 x3
  haveI : IsProbabilityMeasure ν :=
    theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure
      (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam
  have h0 :
      measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
                theorem7LaplacianDefinition2Score2 ω ∧
              theorem7LaplacianDefinition2Score2 ω ≤
                theorem7LaplacianDefinition2Score1 ω) <
        measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score2 ω) *
          measureProb ν
            (fun ω =>
              theorem7LaplacianDefinition2Score2 ω ≤
                  theorem7LaplacianDefinition2Score1 ω ∧
                theorem7LaplacianDefinition2Score3 ω ≤
                  theorem7LaplacianDefinition2Score1 ω) := by
    simpa [ν] using
      theorem7LaplacianDefinition2_event0_score_inter_lt_mul
        (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam hx23
  have h1 :
      measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
                theorem7LaplacianDefinition2Score1 ω ∧
              theorem7LaplacianDefinition2Score1 ω <
                theorem7LaplacianDefinition2Score2 ω) <
        measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score1 ω) *
          measureProb ν
            (fun ω =>
              theorem7LaplacianDefinition2Score1 ω <
                  theorem7LaplacianDefinition2Score2 ω ∧
                theorem7LaplacianDefinition2Score3 ω ≤
                  theorem7LaplacianDefinition2Score2 ω) := by
    simpa [ν] using
      theorem7LaplacianDefinition2_event1_score_inter_lt_mul
        (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3)
        hlam (lt_trans hx23 hx12)
  have h2 :
      measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω ≤
                theorem7LaplacianDefinition2Score1 ω ∧
              theorem7LaplacianDefinition2Score1 ω <
                theorem7LaplacianDefinition2Score3 ω) <
        measureProb ν
          (fun ω =>
            theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score1 ω) *
          measureProb ν
            (fun ω =>
              theorem7LaplacianDefinition2Score1 ω <
                  theorem7LaplacianDefinition2Score3 ω ∧
                theorem7LaplacianDefinition2Score2 ω <
                  theorem7LaplacianDefinition2Score3 ω) := by
    simpa [ν] using
      theorem7LaplacianDefinition2_event2_score_inter_lt_mul
        (lam := lam) (x1 := x1) (x2 := x2) (x3 := x3) hlam hx12
  have right_factor_pos :
      ∀ {L C B : ℝ}, 0 ≤ L → 0 ≤ C → L < C * B → 0 < B := by
    intro L C B hL hC hlt
    by_contra hnot
    have hB : B ≤ 0 := le_of_not_gt hnot
    have hCB : C * B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC hB
    exact (not_lt_of_ge (le_trans hCB hL)) hlt
  have hfirst0 :
      0 < measureProb ν
        (fun ω =>
          theorem7LaplacianDefinition2Score2 ω ≤
              theorem7LaplacianDefinition2Score1 ω ∧
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score1 ω) := by
    refine right_factor_pos ?_ ?_ h0
    · unfold measureProb
      exact ENNReal.toReal_nonneg
    · unfold measureProb
      exact ENNReal.toReal_nonneg
  have hfirst1 :
      0 < measureProb ν
        (fun ω =>
          theorem7LaplacianDefinition2Score1 ω <
              theorem7LaplacianDefinition2Score2 ω ∧
            theorem7LaplacianDefinition2Score3 ω ≤
              theorem7LaplacianDefinition2Score2 ω) := by
    refine right_factor_pos ?_ ?_ h1
    · unfold measureProb
      exact ENNReal.toReal_nonneg
    · unfold measureProb
      exact ENNReal.toReal_nonneg
  have hfirst2 :
      0 < measureProb ν
        (fun ω =>
          theorem7LaplacianDefinition2Score1 ω <
              theorem7LaplacianDefinition2Score3 ω ∧
            theorem7LaplacianDefinition2Score2 ω <
              theorem7LaplacianDefinition2Score3 ω) := by
    refine right_factor_pos ?_ ?_ h2
    · unfold measureProb
      exact ENNReal.toReal_nonneg
    · unfold measureProb
      exact ENNReal.toReal_nonneg
  simpa [theorem7LaplacianDefinition2RankingPMF, ν] using
    rum3Definition2NegativeCorrelationCertificate_of_score_inter_lt_mul
      (ν := ν)
      theorem7LaplacianDefinition2Score1_measurable
      theorem7LaplacianDefinition2Score2_measurable
      theorem7LaplacianDefinition2Score3_measurable
      hvalue01 hvalue12 hfirst0 hfirst1 hfirst2 h0 h1 h2

/-- Arbitrary-variance Gaussian source inequality for shared first choice `score₁`. -/
theorem theorem8GaussianDefinition2Std_event0_score_inter_lt_mul
    {σ x1 x2 x3 : ℝ} (hσ : 0 < σ) (hx23 : x3 < x2) :
    measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score2 ω ∧
            theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω) <
      measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score2 ω) *
        measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
                theorem8GaussianDefinition2Score1 ω ∧
              theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score1 ω) := by
  let c := theorem8GaussianCanonicalScale σ
  let νstd := theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3
  let νcan := theorem8GaussianDefinition2ScoreMeasure
    (c * x1) (c * x2) (c * x3)
  let e := theorem8GaussianDefinition2CanonicalScaleMap σ
  have hc : 0 < c := theorem8GaussianCanonicalScale_pos hσ
  have he : MeasurePreserving e νstd νcan := by
    simpa [e, νstd, νcan, c] using
      theorem8GaussianDefinition2CanonicalScaleMap_measurePreserving
        (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) hσ
  let A : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score3 ω ≤
        theorem8GaussianDefinition2Score2 ω ∧
      theorem8GaussianDefinition2Score2 ω ≤
        theorem8GaussianDefinition2Score1 ω
  let B : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score2 ω ≤
        theorem8GaussianDefinition2Score1 ω ∧
      theorem8GaussianDefinition2Score3 ω ≤
        theorem8GaussianDefinition2Score1 ω
  let C : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score3 ω ≤
      theorem8GaussianDefinition2Score2 ω
  have hA_meas : MeasurableSet {ω | A ω} := by
    dsimp [A, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3]
    exact (measurableSet_le measurable_snd.snd measurable_snd.fst).inter
      (measurableSet_le measurable_snd.fst measurable_fst)
  have hB_meas : MeasurableSet {ω | B ω} := by
    dsimp [B, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3]
    exact (measurableSet_le measurable_snd.fst measurable_fst).inter
      (measurableSet_le measurable_snd.snd measurable_fst)
  have hC_meas : MeasurableSet {ω | C ω} := by
    dsimp [C, theorem8GaussianDefinition2Score2,
      theorem8GaussianDefinition2Score3]
    exact measurableSet_le measurable_snd.snd measurable_snd.fst
  have hbase :
      measureProb νcan A < measureProb νcan C * measureProb νcan B := by
    have hx23' : c * x3 < c * x2 := (mul_lt_mul_iff_right₀ hc).2 hx23
    simpa [νcan, c, A, B, C] using
      theorem8GaussianDefinition2_event0_score_inter_lt_mul
        (x1 := c * x1) (x2 := c * x2) (x3 := c * x3) hx23'
  have hA :
      measureProb νstd (fun ω => A (e ω)) = measureProb νcan A :=
    measureProb_preimage_of_measurePreserving e he A hA_meas
  have hB :
      measureProb νstd (fun ω => B (e ω)) = measureProb νcan B :=
    measureProb_preimage_of_measurePreserving e he B hB_meas
  have hC :
      measureProb νstd (fun ω => C (e ω)) = measureProb νcan C :=
    measureProb_preimage_of_measurePreserving e he C hC_meas
  rw [← hA, ← hB, ← hC] at hbase
  simpa [νstd, e, A, B, C, c, mul_le_mul_iff_right₀ hc] using hbase

/-- Arbitrary-variance Gaussian source inequality for shared first choice `score₂`. -/
theorem theorem8GaussianDefinition2Std_event1_score_inter_lt_mul
    {σ x1 x2 x3 : ℝ} (hσ : 0 < σ) (hx13 : x3 < x1) :
    measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score2 ω) <
      measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
        measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω <
                theorem8GaussianDefinition2Score2 ω ∧
              theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score2 ω) := by
  let c := theorem8GaussianCanonicalScale σ
  let νstd := theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3
  let νcan := theorem8GaussianDefinition2ScoreMeasure
    (c * x1) (c * x2) (c * x3)
  let e := theorem8GaussianDefinition2CanonicalScaleMap σ
  have hc : 0 < c := theorem8GaussianCanonicalScale_pos hσ
  have he : MeasurePreserving e νstd νcan := by
    simpa [e, νstd, νcan, c] using
      theorem8GaussianDefinition2CanonicalScaleMap_measurePreserving
        (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) hσ
  let A : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score3 ω ≤
        theorem8GaussianDefinition2Score1 ω ∧
      theorem8GaussianDefinition2Score1 ω <
        theorem8GaussianDefinition2Score2 ω
  let B : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score1 ω <
        theorem8GaussianDefinition2Score2 ω ∧
      theorem8GaussianDefinition2Score3 ω ≤
        theorem8GaussianDefinition2Score2 ω
  let C : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score3 ω ≤
      theorem8GaussianDefinition2Score1 ω
  have hA_meas : MeasurableSet {ω | A ω} := by
    dsimp [A, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3]
    exact (measurableSet_le measurable_snd.snd measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd.fst)
  have hB_meas : MeasurableSet {ω | B ω} := by
    dsimp [B, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3]
    exact (measurableSet_lt measurable_fst measurable_snd.fst).inter
      (measurableSet_le measurable_snd.snd measurable_snd.fst)
  have hC_meas : MeasurableSet {ω | C ω} := by
    dsimp [C, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score3]
    exact measurableSet_le measurable_snd.snd measurable_fst
  have hbase :
      measureProb νcan A < measureProb νcan C * measureProb νcan B := by
    have hx13' : c * x3 < c * x1 := (mul_lt_mul_iff_right₀ hc).2 hx13
    simpa [νcan, c, A, B, C] using
      theorem8GaussianDefinition2_event1_score_inter_lt_mul
        (x1 := c * x1) (x2 := c * x2) (x3 := c * x3) hx13'
  have hA :
      measureProb νstd (fun ω => A (e ω)) = measureProb νcan A :=
    measureProb_preimage_of_measurePreserving e he A hA_meas
  have hB :
      measureProb νstd (fun ω => B (e ω)) = measureProb νcan B :=
    measureProb_preimage_of_measurePreserving e he B hB_meas
  have hC :
      measureProb νstd (fun ω => C (e ω)) = measureProb νcan C :=
    measureProb_preimage_of_measurePreserving e he C hC_meas
  rw [← hA, ← hB, ← hC] at hbase
  simpa [νstd, e, A, B, C, c, mul_le_mul_iff_right₀ hc,
    mul_lt_mul_iff_right₀ hc] using hbase

/-- Arbitrary-variance Gaussian source inequality for shared first choice `score₃`. -/
theorem theorem8GaussianDefinition2Std_event2_score_inter_lt_mul
    {σ x1 x2 x3 : ℝ} (hσ : 0 < σ) (hx12 : x2 < x1) :
    measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (fun ω =>
          theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score3 ω) <
      measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
        measureProb (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
          (fun ω =>
            theorem8GaussianDefinition2Score1 ω <
                theorem8GaussianDefinition2Score3 ω ∧
              theorem8GaussianDefinition2Score2 ω <
                theorem8GaussianDefinition2Score3 ω) := by
  let c := theorem8GaussianCanonicalScale σ
  let νstd := theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3
  let νcan := theorem8GaussianDefinition2ScoreMeasure
    (c * x1) (c * x2) (c * x3)
  let e := theorem8GaussianDefinition2CanonicalScaleMap σ
  have hc : 0 < c := theorem8GaussianCanonicalScale_pos hσ
  have he : MeasurePreserving e νstd νcan := by
    simpa [e, νstd, νcan, c] using
      theorem8GaussianDefinition2CanonicalScaleMap_measurePreserving
        (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) hσ
  let A : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score2 ω ≤
        theorem8GaussianDefinition2Score1 ω ∧
      theorem8GaussianDefinition2Score1 ω <
        theorem8GaussianDefinition2Score3 ω
  let B : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score1 ω <
        theorem8GaussianDefinition2Score3 ω ∧
      theorem8GaussianDefinition2Score2 ω <
        theorem8GaussianDefinition2Score3 ω
  let C : Theorem8GaussianDefinition2ScoreSpace → Prop := fun ω =>
    theorem8GaussianDefinition2Score2 ω ≤
      theorem8GaussianDefinition2Score1 ω
  have hA_meas : MeasurableSet {ω | A ω} := by
    dsimp [A, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3]
    exact (measurableSet_le measurable_snd.fst measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd.snd)
  have hB_meas : MeasurableSet {ω | B ω} := by
    dsimp [B, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2, theorem8GaussianDefinition2Score3]
    exact (measurableSet_lt measurable_fst measurable_snd.snd).inter
      (measurableSet_lt measurable_snd.fst measurable_snd.snd)
  have hC_meas : MeasurableSet {ω | C ω} := by
    dsimp [C, theorem8GaussianDefinition2Score1,
      theorem8GaussianDefinition2Score2]
    exact measurableSet_le measurable_snd.fst measurable_fst
  have hbase :
      measureProb νcan A < measureProb νcan C * measureProb νcan B := by
    have hx12' : c * x2 < c * x1 := (mul_lt_mul_iff_right₀ hc).2 hx12
    simpa [νcan, c, A, B, C] using
      theorem8GaussianDefinition2_event2_score_inter_lt_mul
        (x1 := c * x1) (x2 := c * x2) (x3 := c * x3) hx12'
  have hA :
      measureProb νstd (fun ω => A (e ω)) = measureProb νcan A :=
    measureProb_preimage_of_measurePreserving e he A hA_meas
  have hB :
      measureProb νstd (fun ω => B (e ω)) = measureProb νcan B :=
    measureProb_preimage_of_measurePreserving e he B hB_meas
  have hC :
      measureProb νstd (fun ω => C (e ω)) = measureProb νcan C :=
    measureProb_preimage_of_measurePreserving e he C hC_meas
  rw [← hA, ← hB, ← hC] at hbase
  simpa [νstd, e, A, B, C, c, mul_le_mul_iff_right₀ hc,
    mul_lt_mul_iff_right₀ hc] using hbase

/--
Appendix C / Theorem 8, Definition 2 endpoint for three Gaussian scores with
arbitrary positive standard deviation.
-/
theorem theorem8GaussianDefinition2Std_negativeCorrelationCertificate
    {σ x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hσ : 0 < σ)
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    RUM3Definition2NegativeCorrelationCertificate
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) value := by
  let ν := theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, theorem8GaussianDefinition2ScoreMeasureStd,
      theorem8GaussianPairMeasureStd,
      AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd,
      theorem8GaussianVarianceFromStd,
      AppliedModelingLib.Probability.gaussianVarianceFromStd]
    infer_instance
  have h0 :
      measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score2 ω ∧
              theorem8GaussianDefinition2Score2 ω ≤
                theorem8GaussianDefinition2Score1 ω) <
        measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score2 ω) *
          measureProb ν
            (fun ω =>
              theorem8GaussianDefinition2Score2 ω ≤
                  theorem8GaussianDefinition2Score1 ω ∧
                theorem8GaussianDefinition2Score3 ω ≤
                  theorem8GaussianDefinition2Score1 ω) := by
    simpa [ν] using
      theorem8GaussianDefinition2Std_event0_score_inter_lt_mul
        (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) hσ hx23
  have h1 :
      measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
                theorem8GaussianDefinition2Score1 ω ∧
              theorem8GaussianDefinition2Score1 ω <
                theorem8GaussianDefinition2Score2 ω) <
        measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
          measureProb ν
            (fun ω =>
              theorem8GaussianDefinition2Score1 ω <
                  theorem8GaussianDefinition2Score2 ω ∧
                theorem8GaussianDefinition2Score3 ω ≤
                  theorem8GaussianDefinition2Score2 ω) := by
    simpa [ν] using
      theorem8GaussianDefinition2Std_event1_score_inter_lt_mul
        (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) hσ
        (lt_trans hx23 hx12)
  have h2 :
      measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
                theorem8GaussianDefinition2Score1 ω ∧
              theorem8GaussianDefinition2Score1 ω <
                theorem8GaussianDefinition2Score3 ω) <
        measureProb ν
          (fun ω =>
            theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω) *
          measureProb ν
            (fun ω =>
              theorem8GaussianDefinition2Score1 ω <
                  theorem8GaussianDefinition2Score3 ω ∧
                theorem8GaussianDefinition2Score2 ω <
                  theorem8GaussianDefinition2Score3 ω) := by
    simpa [ν] using
      theorem8GaussianDefinition2Std_event2_score_inter_lt_mul
        (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) hσ hx12
  have right_factor_pos :
      ∀ {L C B : ℝ}, 0 ≤ L → 0 ≤ C → L < C * B → 0 < B := by
    intro L C B hL hC hlt
    by_contra hnot
    have hB : B ≤ 0 := le_of_not_gt hnot
    have hCB : C * B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC hB
    exact (not_lt_of_ge (le_trans hCB hL)) hlt
  have hfirst0 :
      0 < measureProb ν
        (fun ω =>
          theorem8GaussianDefinition2Score2 ω ≤
              theorem8GaussianDefinition2Score1 ω ∧
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score1 ω) := by
    refine right_factor_pos ?_ ?_ h0
    · unfold measureProb
      exact ENNReal.toReal_nonneg
    · unfold measureProb
      exact ENNReal.toReal_nonneg
  have hfirst1 :
      0 < measureProb ν
        (fun ω =>
          theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score2 ω ∧
            theorem8GaussianDefinition2Score3 ω ≤
              theorem8GaussianDefinition2Score2 ω) := by
    refine right_factor_pos ?_ ?_ h1
    · unfold measureProb
      exact ENNReal.toReal_nonneg
    · unfold measureProb
      exact ENNReal.toReal_nonneg
  have hfirst2 :
      0 < measureProb ν
        (fun ω =>
          theorem8GaussianDefinition2Score1 ω <
              theorem8GaussianDefinition2Score3 ω ∧
            theorem8GaussianDefinition2Score2 ω <
              theorem8GaussianDefinition2Score3 ω) := by
    refine right_factor_pos ?_ ?_ h2
    · unfold measureProb
      exact ENNReal.toReal_nonneg
    · unfold measureProb
      exact ENNReal.toReal_nonneg
  exact
    rum3Definition2NegativeCorrelationCertificate_of_score_inter_lt_mul
      (ν := ν)
      theorem8GaussianDefinition2Score1_measurable
      theorem8GaussianDefinition2Score2_measurable
      theorem8GaussianDefinition2Score3_measurable
      hvalue01 hvalue12 hfirst0 hfirst1 hfirst2 h0 h1 h2

theorem rum3Theorem6Certificate_of_lambda_delta
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda : RUM3LambdaCertificate μWorse)
    (delta : RUM3DeltaCertificate μBetter μWorse) :
    RUM3Theorem6Certificate μBetter μWorse value x1 x2 x3 where
  value_first := hvalue1
  value_second := hvalue2
  value_third := hvalue3
  value12 := hx12
  value23 := hx23
  lambda1_half := lambda.lambda1_half
  lambda1_lt_one := lambda.lambda1_lt_one
  lambda12 := lambda.lambda12
  lambda3_half := lambda.lambda3_half
  delta_top_pos := delta.delta_top_pos
  delta_middle_le_top := delta.delta_middle_le_top
  delta_bottom_nonpos := delta.delta_bottom_nonpos

theorem rum3DeltaCertificate_of_paper_lemmas
    {μBetter μWorse : PMF (Ranking 1)}
    (monotonicity_top :
      firstChoiceProb μWorse (0 : Candidate 1) <
        firstChoiceProb μBetter (0 : Candidate 1))
    (lemma3_middle :
      firstChoiceProb μBetter (1 : Candidate 1) -
          firstChoiceProb μWorse (1 : Candidate 1) ≤
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (lemma2_bottom :
      firstChoiceProb μBetter (2 : Candidate 1) ≤
        firstChoiceProb μWorse (2 : Candidate 1)) :
    RUM3DeltaCertificate μBetter μWorse where
  delta_top_pos := by linarith
  delta_middle_le_top := lemma3_middle
  delta_bottom_nonpos := by linarith

/--
The first-mover part of Definition 1 for the three-candidate RUM delta
certificate.

This is purely finite PMF algebra: once the more accurate law gains first-choice
probability on the highest-valued candidate and does not gain probability on the
lowest-valued candidate, expected first-mover utility strictly increases.
-/
theorem rum3_expectedFirstMoverUtility_strict_of_deltaCertificate
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (delta : RUM3DeltaCertificate μBetter μWorse) :
    expectedFirstMoverUtility μWorse value <
      expectedFirstMoverUtility μBetter value :=
  AppliedModelingLib.SocialChoice.Ranking.expectedFirstMoverUtility_lt_of_fin3_top_gain_bottom_nongain
      μBetter μWorse value hvalue1 hvalue2 hvalue3 hx12 hx23
      delta.delta_top_pos delta.delta_bottom_nonpos

/--
Definition 1 finite-removal monotonicity for a three-candidate family, once the
RUM delta certificate and the three singleton-removal inequalities have been
proved from the source model.

This wrapper is intentionally explicit: the first-mover strict inequality is
derived from the delta certificate, while the three best-after-removal
inequalities remain visible source-model obligations.
-/
theorem rum3_theorem1RemovalMonotonicityAt_of_delta_and_bestRemaining
    {F : AccuracyFamily 1} {θA θH : ℝ}
    {μBetter μWorse : PMF (Ranking 1)} {x1 x2 x3 : ℝ}
    (hdistA : F.dist θA = μBetter)
    (hdistH : F.dist θH = μWorse)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (delta : RUM3DeltaCertificate μBetter μWorse)
    (hremove0 :
      AccuracyFamily.expectedBestAfterRemoval μWorse F.value (0 : Candidate 1) ≤
        AccuracyFamily.expectedBestAfterRemoval μBetter F.value (0 : Candidate 1))
    (hremove1 :
      AccuracyFamily.expectedBestAfterRemoval μWorse F.value (1 : Candidate 1) ≤
        AccuracyFamily.expectedBestAfterRemoval μBetter F.value (1 : Candidate 1))
    (hremove2 :
      AccuracyFamily.expectedBestAfterRemoval μWorse F.value (2 : Candidate 1) ≤
        AccuracyFamily.expectedBestAfterRemoval μBetter F.value (2 : Candidate 1)) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F θA θH where
  firstMover_strict := by
    rw [hdistH, hdistA]
    exact rum3_expectedFirstMoverUtility_strict_of_deltaCertificate
      hvalue1 hvalue2 hvalue3 hx12 hx23 delta
  bestRemaining_weak := by
    intro c
    fin_cases c
    · simpa [hdistH, hdistA] using hremove0
    · simpa [hdistH, hdistA] using hremove1
    · simpa [hdistH, hdistA] using hremove2

/--
Abstract finite-coupling form of Appendix C / Lemma 2 for the bottom candidate.

The continuous paper proof constructs such a coupling by contraction.  This
lemma isolates the order-theoretic probability step: if every coupled realization
where the better/more accurate ranking puts `x₃` first also has the worse/human
ranking put `x₃` first, then the better bottom-first probability is no larger.
-/
theorem rum3_lemma2_bottom_of_coupling
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter :
      firstChoiceProb μBetter (2 : Candidate 1) =
        pmfProb ν (fun ω => (2 : Candidate 1) = firstChoice (better ω)))
    (hworse :
      firstChoiceProb μWorse (2 : Candidate 1) =
        pmfProb ν (fun ω => (2 : Candidate 1) = firstChoice (worse ω)))
    (himp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω)) :
    firstChoiceProb μBetter (2 : Candidate 1) ≤
      firstChoiceProb μWorse (2 : Candidate 1) := by
  rw [hbetter, hworse]
  exact pmfProb_le_of_imp ν
    (fun ω => (2 : Candidate 1) = firstChoice (better ω))
    (fun ω => (2 : Candidate 1) = firstChoice (worse ω))
    himp

theorem rum3_middle_delta_indicator_le_bottom_middle
    (b w : Candidate 1)
    (hnoTopOut : (0 : Candidate 1) = w → (0 : Candidate 1) = b) :
    (if (1 : Candidate 1) = b then (1 : ℝ) else 0) -
        (if (1 : Candidate 1) = w then (1 : ℝ) else 0) ≤
      (if (2 : Candidate 1) = w ∧ (1 : Candidate 1) = b then (1 : ℝ) else 0) -
        (if False then (1 : ℝ) else 0) := by
  fin_cases b <;> fin_cases w <;> simp at *

theorem rum3_bottom_top_indicator_le_top_delta
    (b w : Candidate 1)
    (hnoTopOut : (0 : Candidate 1) = w → (0 : Candidate 1) = b) :
    (if (2 : Candidate 1) = w ∧ (0 : Candidate 1) = b then (1 : ℝ) else 0) -
        (if False then (1 : ℝ) else 0) ≤
      (if (0 : Candidate 1) = b then (1 : ℝ) else 0) -
        (if (0 : Candidate 1) = w then (1 : ℝ) else 0) := by
  fin_cases b <;> fin_cases w <;> simp at *

/--
Abstract finite transition-mass form of Appendix C / Lemma 3 for the middle
candidate in the three-candidate case.

The continuous paper proof shows that the human-realization mass moving from
`x₃` to `x₂` under contraction is at most the mass moving from `x₃` to `x₁`,
using the `swapi` bijection and well-ordered noise.  This lemma isolates the
finite probability algebra around that step: if top-first realizations cannot
leave the top under contraction, and `x₃ → x₂` mass is no larger than
`x₃ → x₁` mass, then the paper's Lemma 3 delta inequality for `i = 2` follows.
-/
theorem rum3_lemma3_middle_of_transition_mass
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hbottomMiddle_le_bottomTop :
      pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω))) :
    firstChoiceProb μBetter (1 : Candidate 1) -
        firstChoiceProb μWorse (1 : Candidate 1) ≤
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1) := by
  rw [hbetter (1 : Candidate 1), hworse (1 : Candidate 1),
    hbetter (0 : Candidate 1), hworse (0 : Candidate 1)]
  have hmid :
      pmfProb ν (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
          pmfProb ν (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
        pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) -
          pmfProb ν (fun _ => False) := by
    refine pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le ν
      (fun ω => (1 : Candidate 1) = firstChoice (better ω))
      (fun ω => (1 : Candidate 1) = firstChoice (worse ω))
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω))
      (fun _ => False) ?_
    intro ω
    exact rum3_middle_delta_indicator_le_bottom_middle
      (firstChoice (better ω)) (firstChoice (worse ω)) (hnoTopOut ω)
  have htop :
      pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω)) -
          pmfProb ν (fun _ => False) ≤
        pmfProb ν (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
          pmfProb ν (fun ω => (0 : Candidate 1) = firstChoice (worse ω)) := by
    refine pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le ν
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω))
      (fun _ => False)
      (fun ω => (0 : Candidate 1) = firstChoice (better ω))
      (fun ω => (0 : Candidate 1) = firstChoice (worse ω)) ?_
    intro ω
    exact rum3_bottom_top_indicator_le_top_delta
      (firstChoice (better ω)) (firstChoice (worse ω)) (hnoTopOut ω)
  simp only [pmfProb_false, sub_zero] at hmid htop
  linarith

/--
Finite `swapi` change-of-variables skeleton for Appendix C / Lemma 3.

An equivalence `swap` sends each `x₃ → x₂` transition realization into an
`x₃ → x₁` transition realization, and the target atom has at least as much
mass.  Therefore the `x₃ → x₂` transition probability is no larger.
-/
theorem rum3_bottomMiddle_transition_le_bottomTop_of_swap_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (ν : PMF Ω) (swap : Ω ≃ Ω)
    (better worse : Ω → Ranking 1)
    (hmap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (swap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (swap ω)))
    (hmass : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    pmfProb ν (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω)) ≤
      pmfProb ν (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω)) :=
  pmfProb_le_of_equiv_event_mass_le ν swap
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω))
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω))
    hmap hmass

/--
Finite coupling form of the top-candidate monotonicity step used in Appendix C /
Theorem 6.

If every coupled realization that is top-first for the worse/human ranking is
also top-first for the better/algorithmic ranking, and some positive-mass
realization is corrected into top-first, then the top-first probability is
strictly larger for the better ranking.
-/
theorem rum3_monotonicity_top_of_coupling
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmass : 0 < (ν ω₀).toReal) :
    firstChoiceProb μWorse (0 : Candidate 1) <
      firstChoiceProb μBetter (0 : Candidate 1) := by
  rw [hworse (0 : Candidate 1), hbetter (0 : Candidate 1)]
  exact pmfProb_lt_of_imp_of_mass ν
    (fun ω => (0 : Candidate 1) = firstChoice (worse ω))
    (fun ω => (0 : Candidate 1) = firstChoice (better ω))
    hnoTopOut ω₀ hbetterTop hworseNotTop hmass

/--
Finite contraction/coupling certificate for the delta side of Appendix C /
Theorem 6.

This packages the finite monotonicity step, Lemma 2 bottom inequality, and
Lemma 3 middle-vs-top inequality into the `RUM3DeltaCertificate` consumed by
the final payoff algebra.  The continuous RUM proof still needs to construct the
coupling and prove the listed event/transition facts from contraction and
well-ordered noise.
-/
theorem rum3DeltaCertificate_of_finite_contraction_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmass : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbottomMiddle_le_bottomTop :
      pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω))) :
    RUM3DeltaCertificate μBetter μWorse :=
  rum3DeltaCertificate_of_paper_lemmas
    (rum3_monotonicity_top_of_coupling
      μBetter μWorse ν better worse hbetter hworse hnoTopOut
      hbetterTop hworseNotTop hmass)
    (rum3_lemma3_middle_of_transition_mass
      μBetter μWorse ν better worse hbetter hworse hnoTopOut
      hbottomMiddle_le_bottomTop)
    (rum3_lemma2_bottom_of_coupling
      μBetter μWorse ν better worse
      (hbetter (2 : Candidate 1)) (hworse (2 : Candidate 1)) hbottomImp)

/--
Delta certificate where the Lemma 3 transition-mass inequality is supplied by a
finite `swapi` equivalence with pointwise mass dominance.
-/
theorem rum3DeltaCertificate_of_finite_contraction_swap_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hmap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (swap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (swap ω)))
    (hmassSwap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    RUM3DeltaCertificate μBetter μWorse :=
  rum3DeltaCertificate_of_finite_contraction_facts
    μBetter μWorse ν better worse hbetter hworse hnoTopOut
    hbetterTop hworseNotTop hmassTop hbottomImp
    (rum3_bottomMiddle_transition_le_bottomTop_of_swap_equiv
      ν swap better worse hmap hmassSwap)

/--
Delta certificate from finite score-level contraction and `swapi` facts.

This bridge derives the ranking-level event implications used by Lemmas 2 and 3
from deterministic score geometry.  The remaining measure-theoretic work is only
the marginal identification and the mass comparison for the finite/discretized
`swapi` map.
-/
theorem rum3DeltaCertificate_of_finite_score_contraction_swap_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (t x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ Ω)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hmassSwap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    RUM3DeltaCertificate μBetter μWorse := by
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  have hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω) := by
    intro ω hwTop
    rcases hworseTop_scores_of_first ω hwTop with ⟨hr21, hr31⟩
    exact hbetterTop_of_scores ω
      (rum3_contract_top_first_of_original_top_first
        ht0 ht1 (le_of_lt hx12) (le_of_lt hx13) hr21 hr31)
  have hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω) := by
    intro ω hbBetter
    rcases hbetterBottom_scores_of_first ω hbBetter with ⟨hc13, hc23⟩
    exact hworseBottom_of_scores ω
      (rum3_contract_bottom_first_imp_original_bottom_first
        ht0 ht1 hx13 hx23 hc13 hc23)
  have hmap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (swap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (swap ω)) := by
    intro ω htransition
    rcases hworseBottom_scores_of_first ω htransition.1 with ⟨hr13, hr23⟩
    rcases hbetterMiddle_scores_of_first ω htransition.2 with ⟨hc12, hc32⟩
    rcases rum3_swap_middle_transition_geometry
        ht0 ht1 hx12 hr13 hr23 hc12 hc32 with
      ⟨hr23_swap, hr13_swap, hc21_swap, hc31_swap⟩
    constructor
    · apply hworseBottom_of_scores
      unfold rum3BottomFirstByScores
      constructor
      · rw [hswap1, hswap3]
        exact hr23_swap
      · rw [hswap2, hswap3]
        exact hr13_swap
    · apply hbetterTop_of_scores
      unfold rum3TopFirstByScores
      constructor
      · rw [hswap2, hswap1]
        exact hc21_swap
      · rw [hswap3, hswap1]
        exact hc31_swap
  exact rum3DeltaCertificate_of_finite_contraction_swap_facts
    μBetter μWorse ν better worse swap hbetter hworse hnoTopOut
    hbetterTop hworseNotTop hmassTop hbottomImp hmap hmassSwap

theorem rum3LambdaCertificate_of_pairwise_facts
    {μWorse : PMF (Ranking 1)}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_correct : (1 : ℝ) / 2 < rum3Lambda1 μWorse)
    (h23_not_sure : rum3Lambda1 μWorse < 1)
    (h12_correct : (1 : ℝ) / 2 < rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse where
  lambda1_half := h23_correct
  lambda1_lt_one := h23_not_sure
  lambda12 := h13_gt_23
  lambda3_half := h12_correct

theorem rum3Lambda1_le_one (μ : PMF (Ranking 1)) :
    rum3Lambda1 μ ≤ 1 :=
   pmfProb_le_one μ
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))

theorem rum3Lambda2_le_one (μ : PMF (Ranking 1)) :
    rum3Lambda2 μ ≤ 1 :=
   pmfProb_le_one μ
    (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))

theorem rum3Lambda3_le_one (μ : PMF (Ranking 1)) :
    rum3Lambda3 μ ≤ 1 :=
   pmfProb_le_one μ
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))

theorem rum3Lambda1_lt_one_of_mass_choose_third_after_first_removed
    (μ : PMF (Ranking 1)) (π₀ : Ranking 1)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μ π₀).toReal) :
    rum3Lambda1 μ < 1 := by
  unfold rum3Lambda1
  refine pmfProb_lt_one_of_mass_not μ
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    π₀ ?hnot hmass
  intro h
  have : (2 : Candidate 1) = (1 : Candidate 1) := by
    rw [← hchoose, h]
  have hval : (2 : ℕ) = 1 := by
    simpa using congrArg Fin.val this
  norm_num at hval

theorem rum3_bestRemainingAfter_swap02_remove0 :
    bestRemainingAfter
        (Equiv.swap (0 : Candidate 1) (2 : Candidate 1))
        (0 : Candidate 1) = (2 : Candidate 1) := by
  simp [bestRemainingAfter, firstChoice]

theorem rum3Lambda1_lt_one_of_full_support
    (μ : PMF (Ranking 1))
    (hfull : ∀ π : Ranking 1, 0 < (μ π).toReal) :
    rum3Lambda1 μ < 1 :=
  rum3Lambda1_lt_one_of_mass_choose_third_after_first_removed
    μ (Equiv.swap (0 : Candidate 1) (2 : Candidate 1))
    rum3_bestRemainingAfter_swap02_remove0
    (hfull (Equiv.swap (0 : Candidate 1) (2 : Candidate 1)))

theorem rum3_fullSupport_of_sample_preimages
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1)
    (hpreimage : ∀ π : Ranking 1,
      (μ π).toReal = pmfProb ν (fun ω => rank ω = π))
    (hsupport : ∀ π : Ranking 1,
      ∃ ω : Ω, rank ω = π ∧ 0 < (ν ω).toReal) :
    ∀ π : Ranking 1, 0 < (μ π).toReal := by
  intro π
  rcases hsupport π with ⟨ω, hω_rank, hω_mass⟩
  exact pmf_apply_toReal_pos_of_pmfProb_preimage
    μ ν rank hpreimage hω_rank hω_mass

theorem rum3LambdaCertificate_of_pairwise_facts_and_support
    {μWorse : PMF (Ranking 1)} {π₀ : Ranking 1}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_correct : (1 : ℝ) / 2 < rum3Lambda1 μWorse)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μWorse π₀).toReal)
    (h12_correct : (1 : ℝ) / 2 < rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_facts
    h13_gt_23 h23_correct
    (rum3Lambda1_lt_one_of_mass_choose_third_after_first_removed
      μWorse π₀ hchoose hmass)
    h12_correct

theorem rum3LambdaCertificate_of_pairwise_wrong_facts_and_support
    {μWorse : PMF (Ranking 1)} {π₀ : Ranking 1}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_wrong_lt_correct :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μWorse)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μWorse π₀).toReal)
    (h12_wrong_lt_correct :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_facts_and_support
    h13_gt_23
    (rum3Lambda1_half_of_wrong_lt_correct h23_wrong_lt_correct)
    hchoose hmass
    (rum3Lambda3_half_of_wrong_lt_correct h12_wrong_lt_correct)

theorem rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    {μWorse : PMF (Ranking 1)}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_wrong_lt_correct :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μWorse)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (h12_wrong_lt_correct :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_facts
    h13_gt_23
    (rum3Lambda1_half_of_wrong_lt_correct h23_wrong_lt_correct)
    (rum3Lambda1_lt_one_of_full_support μWorse hfull)
    (rum3Lambda3_half_of_wrong_lt_correct h12_wrong_lt_correct)

/-- Continuous-measure version of the `x₂` versus `x₃` wrong-choice comparison. -/
theorem rum3Lambda1_wrong_lt_correct_of_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hmeasure :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)}) :
    pmfProb (rumRankingPMFOfMeasure μ rank hrank)
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
      rum3Lambda1 (rumRankingPMFOfMeasure μ rank hrank) := by
  rw [rumRankingPMFOfMeasure_eventProb, rum3Lambda1_rumRankingPMFOfMeasure]
  exact measureProb_lt_of_measure_lt μ
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
      (2 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
      (1 : Candidate 1))
    hmeasure

/-- Continuous-measure version of the `x₁` versus `x₂` wrong-choice comparison. -/
theorem rum3Lambda3_wrong_lt_correct_of_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hmeasure :
      μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)}) :
    pmfProb (rumRankingPMFOfMeasure μ rank hrank)
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
      rum3Lambda3 (rumRankingPMFOfMeasure μ rank hrank) := by
  rw [rumRankingPMFOfMeasure_eventProb, rum3Lambda3_rumRankingPMFOfMeasure]
  exact measureProb_lt_of_measure_lt μ
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
      (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
      (0 : Candidate 1))
    hmeasure

/-- Continuous-measure version of the `λ₁ < λ₂` comparison. -/
theorem rum3Lambda1_lt_lambda2_of_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hmeasure :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
          (0 : Candidate 1)}) :
    rum3Lambda1 (rumRankingPMFOfMeasure μ rank hrank) <
      rum3Lambda2 (rumRankingPMFOfMeasure μ rank hrank) := by
  rw [rum3Lambda1_rumRankingPMFOfMeasure, rum3Lambda2_rumRankingPMFOfMeasure]
  exact measureProb_lt_of_measure_lt μ
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
      (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
      (0 : Candidate 1))
    hmeasure

/--
Continuous-measure version of the residual `λ₁ ∧ ¬λ₂` cancellation argument.
-/
theorem rum3Lambda1_lt_lambda2_of_cross_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hcross :
      μ ({ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)}ᶜ) <
        μ ({ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)}ᶜ)) :
    rum3Lambda1 (rumRankingPMFOfMeasure μ rank hrank) <
      rum3Lambda2 (rumRankingPMFOfMeasure μ rank hrank) := by
  rw [rum3Lambda1_rumRankingPMFOfMeasure, rum3Lambda2_rumRankingPMFOfMeasure]
  have hp : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (1 : Candidate 1)} :=
    by
      simpa only [Set.preimage_setOf_eq] using
        hrank (show MeasurableSet
          {π : Ranking 1 | bestRemainingAfter π (0 : Candidate 1) =
            (1 : Candidate 1)} from MeasurableSet.of_discrete)
  have hq : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
        (0 : Candidate 1)} :=
    by
      simpa only [Set.preimage_setOf_eq] using
        hrank (show MeasurableSet
          {π : Ranking 1 | bestRemainingAfter π (1 : Candidate 1) =
            (0 : Candidate 1)} from MeasurableSet.of_discrete)
  exact measureProb_lt_of_cross_event_measure_lt μ
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
      (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
      (0 : Candidate 1))
    hp hq hcross

/--
Lambda certificate from continuous realization-measure comparisons plus full
support of the induced human ranking law.
-/
theorem rum3LambdaCertificate_of_measure_facts_and_full_support
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hfull : ∀ π : Ranking 1,
      0 < (rumRankingPMFOfMeasure μ rank hrank π).toReal)
    (h13_gt_23 :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
          (0 : Candidate 1)})
    (h23_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)})
    (h12_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)}) :
    RUM3LambdaCertificate (rumRankingPMFOfMeasure μ rank hrank) :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    (rum3Lambda1_lt_lambda2_of_measure μ rank hrank h13_gt_23)
    (rum3Lambda1_wrong_lt_correct_of_measure
      μ rank hrank h23_wrong_lt_correct)
    hfull
    (rum3Lambda3_wrong_lt_correct_of_measure
      μ rank hrank h12_wrong_lt_correct)

/--
Lambda certificate from continuous realization-measure comparisons, using the
paper's residual `λ₁ ∧ ¬λ₂` comparison for `λ₁ < λ₂`.
-/
theorem rum3LambdaCertificate_of_cross_measure_facts_and_full_support
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hfull : ∀ π : Ranking 1,
      0 < (rumRankingPMFOfMeasure μ rank hrank π).toReal)
    (h13_cross :
      μ ({ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)}ᶜ) <
        μ ({ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)}ᶜ))
    (h23_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)})
    (h12_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)}) :
    RUM3LambdaCertificate (rumRankingPMFOfMeasure μ rank hrank) :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    (rum3Lambda1_lt_lambda2_of_cross_measure μ rank hrank h13_cross)
    (rum3Lambda1_wrong_lt_correct_of_measure
      μ rank hrank h23_wrong_lt_correct)
    hfull
    (rum3Lambda3_wrong_lt_correct_of_measure
      μ rank hrank h12_wrong_lt_correct)

/-- Positive wrong-choice probability makes `λ₁` strictly below one. -/
theorem rum3Lambda1_lt_one_of_wrong_prob_pos
    {μ : PMF (Ranking 1)}
    (hwrong :
      0 <
        pmfProb μ
          (fun π => bestRemainingAfter π (0 : Candidate 1) =
            (2 : Candidate 1))) :
    rum3Lambda1 μ < 1 := by
  rw [rum3Lambda1_wrong_eq_one_sub μ] at hwrong
  linarith

/--
Lambda certificate from continuous realization-measure comparisons, replacing
full ranking support by the exact positive wrong-event mass needed for
`λ₁ < 1`.
-/
theorem rum3LambdaCertificate_of_cross_measure_facts_and_wrong_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hwrong23_pos :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1)} ≠ 0)
    (h13_cross :
      μ ({ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)}ᶜ) <
        μ ({ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)}ᶜ))
    (h23_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)})
    (h12_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)}) :
    RUM3LambdaCertificate (rumRankingPMFOfMeasure μ rank hrank) := by
  have hwrong_prob :
      0 <
        pmfProb (rumRankingPMFOfMeasure μ rank hrank)
          (fun π => bestRemainingAfter π (0 : Candidate 1) =
            (2 : Candidate 1)) := by
    rw [rumRankingPMFOfMeasure_eventProb]
    exact measureProb_pos_of_measure_ne_zero μ
      (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1))
      hwrong23_pos
  exact
    rum3LambdaCertificate_of_pairwise_facts
      (rum3Lambda1_lt_lambda2_of_cross_measure μ rank hrank h13_cross)
      (rum3Lambda1_half_of_wrong_lt_correct
        (rum3Lambda1_wrong_lt_correct_of_measure
          μ rank hrank h23_wrong_lt_correct))
      (rum3Lambda1_lt_one_of_wrong_prob_pos hwrong_prob)
      (rum3Lambda3_half_of_wrong_lt_correct
        (rum3Lambda3_wrong_lt_correct_of_measure
          μ rank hrank h12_wrong_lt_correct))

/--
Delta certificate from continuous first-choice measure inequalities.

This is the continuous analogue of `rum3DeltaCertificate_of_paper_lemmas` after
pushing the realization measure forward to the better and worse ranking laws.
-/
theorem rum3DeltaCertificate_of_measure_probability_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    (monotonicity_top :
      μ {ω | (0 : Candidate 1) = firstChoice (worse ω)} <
        μ {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (lemma3_middle :
      measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
        measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (worse ω)))
    (lemma2_bottom :
      μ {ω | (2 : Candidate 1) = firstChoice (better ω)} ≤
        μ {ω | (2 : Candidate 1) = firstChoice (worse ω)}) :
    RUM3DeltaCertificate
      (rumRankingPMFOfMeasure μ better hbetter)
      (rumRankingPMFOfMeasure μ worse hworse) := by
  refine rum3DeltaCertificate_of_paper_lemmas ?_ ?_ ?_
  · rw [firstChoiceProb_rumRankingPMFOfMeasure,
      firstChoiceProb_rumRankingPMFOfMeasure]
    exact measureProb_lt_of_measure_lt μ
      (fun ω => (0 : Candidate 1) = firstChoice (worse ω))
      (fun ω => (0 : Candidate 1) = firstChoice (better ω))
      monotonicity_top
  · rw [firstChoiceProb_rumRankingPMFOfMeasure,
      firstChoiceProb_rumRankingPMFOfMeasure,
      firstChoiceProb_rumRankingPMFOfMeasure,
      firstChoiceProb_rumRankingPMFOfMeasure]
    exact lemma3_middle
  · rw [firstChoiceProb_rumRankingPMFOfMeasure,
      firstChoiceProb_rumRankingPMFOfMeasure]
    exact measureProb_le_of_measure_le μ
      (fun ω => (2 : Candidate 1) = firstChoice (better ω))
      (fun ω => (2 : Candidate 1) = firstChoice (worse ω))
      lemma2_bottom

/-- Continuous coupling form of the top-candidate monotonicity step. -/
theorem rum3_monotonicity_top_of_measure_coupling
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (worse ω)})
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hcorrected_pos :
      μ ({ω | (0 : Candidate 1) = firstChoice (better ω)} ∩
          {ω | (0 : Candidate 1) = firstChoice (worse ω)}ᶜ) ≠ 0) :
    μ {ω | (0 : Candidate 1) = firstChoice (worse ω)} <
      μ {ω | (0 : Candidate 1) = firstChoice (better ω)} :=
  measure_lt_of_imp_of_diff_ne_zero μ
    (fun ω => (0 : Candidate 1) = firstChoice (worse ω))
    (fun ω => (0 : Candidate 1) = firstChoice (better ω))
    hworseTopMeas hbetterTopMeas hnoTopOut hcorrected_pos

/-- Continuous coupling form of Appendix C / Lemma 2 for the bottom candidate. -/
theorem rum3_lemma2_bottom_of_measure_coupling
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (better worse : Ω → Ranking 1)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω)) :
    μ {ω | (2 : Candidate 1) = firstChoice (better ω)} ≤
      μ {ω | (2 : Candidate 1) = firstChoice (worse ω)} :=
  measure_le_of_imp μ
    (fun ω => (2 : Candidate 1) = firstChoice (better ω))
    (fun ω => (2 : Candidate 1) = firstChoice (worse ω))
    hbottomImp

/--
Continuous transition-mass form of Appendix C / Lemma 3 for the middle
candidate.

This is the continuous counterpart of
`rum3_lemma3_middle_of_transition_mass`.  The proof pushes the continuous
coupling through the finite first-choice-pair summary and reuses the finite
indicator algebra on that finite image.
-/
theorem rum3_lemma3_middle_of_measure_transition_mass
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hbottomMiddle_le_bottomTop :
      measureProb μ (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        measureProb μ (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω))) :
    measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
        measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
      measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
        measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (worse ω)) := by
  classical
  let firstPair : Ω → Candidate 1 × Candidate 1 := fun ω =>
    (firstChoice (better ω), firstChoice (worse ω))
  have hpair : Measurable firstPair := by
    have hb : Measurable (fun ω => firstChoice (better ω)) :=
      (measurable_of_finite firstChoice).comp hbetter
    have hw : Measurable (fun ω => firstChoice (worse ω)) :=
      (measurable_of_finite firstChoice).comp hworse
    exact Measurable.prod hb hw
  have hmid :
      measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
        measureProb μ (fun ω =>
            (2 : Candidate 1) = firstChoice (worse ω) ∧
              (1 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun _ => False) := by
    simpa [firstPair, and_comm, and_left_comm, and_assoc] using
      (measureProb_sub_le_measureProb_sub_of_forall_indicator_sub_le
        (μ := μ) (f := firstPair) hpair
        (p := fun bw : Candidate 1 × Candidate 1 => (1 : Candidate 1) = bw.1)
        (q := fun bw : Candidate 1 × Candidate 1 => (1 : Candidate 1) = bw.2)
        (r := fun bw : Candidate 1 × Candidate 1 =>
          (2 : Candidate 1) = bw.2 ∧ (1 : Candidate 1) = bw.1)
        (s := fun _ : Candidate 1 × Candidate 1 => False)
        MeasurableSet.of_discrete MeasurableSet.of_discrete
        MeasurableSet.of_discrete MeasurableSet.of_discrete
        (by
          intro ω
          exact rum3_middle_delta_indicator_le_bottom_middle
            (firstChoice (better ω)) (firstChoice (worse ω)) (hnoTopOut ω)))
  have htop :
      measureProb μ (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun _ => False) ≤
        measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (worse ω)) := by
    simpa [firstPair, and_comm, and_left_comm, and_assoc] using
      (measureProb_sub_le_measureProb_sub_of_forall_indicator_sub_le
        (μ := μ) (f := firstPair) hpair
        (p := fun bw : Candidate 1 × Candidate 1 =>
          (2 : Candidate 1) = bw.2 ∧ (0 : Candidate 1) = bw.1)
        (q := fun _ : Candidate 1 × Candidate 1 => False)
        (r := fun bw : Candidate 1 × Candidate 1 => (0 : Candidate 1) = bw.1)
        (s := fun bw : Candidate 1 × Candidate 1 => (0 : Candidate 1) = bw.2)
        MeasurableSet.of_discrete MeasurableSet.of_discrete
        MeasurableSet.of_discrete MeasurableSet.of_discrete
        (by
          intro ω
          exact rum3_bottom_top_indicator_le_top_delta
            (firstChoice (better ω)) (firstChoice (worse ω)) (hnoTopOut ω)))
  simp only [measureProb_false, sub_zero] at hmid htop
  linarith

/--
Continuous with-density delta certificate from score-level contraction and
`swapi` facts.

This closes the delta side for a normalized score law
`base.withDensity (rum3ScoreDensityENN ...)`: top monotonicity and bottom
monotonicity come from contraction, while Lemma 3's transition-mass comparison
comes from the continuous `swapi` change of variables.
-/
theorem rum3DeltaCertificate_of_withDensity_score_contraction_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (better worse : Ω → Ranking 1)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hbetter : Measurable better) (hworse : Measurable worse)
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (worse ω)})
    (hp : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω)})
    (hq : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω)})
    (hmp : MeasurePreserving swap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hcorrected_pos :
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | (0 : Candidate 1) = firstChoice (better ω)} ∩
          {ω | (0 : Candidate 1) = firstChoice (worse ω)}ᶜ) ≠ 0)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω))) :
    RUM3DeltaCertificate
      (rumRankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        better hbetter)
      (rumRankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        worse hworse) := by
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  have hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω) := by
    intro ω hwTop
    rcases hworseTop_scores_of_first ω hwTop with ⟨hr21, hr31⟩
    exact hbetterTop_of_scores ω
      (rum3_contract_top_first_of_original_top_first
        ht0 ht1 (le_of_lt hx12) (le_of_lt hx13) hr21 hr31)
  have hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω) := by
    intro ω hbBetter
    rcases hbetterBottom_scores_of_first ω hbBetter with ⟨hc13, hc23⟩
    exact hworseBottom_of_scores ω
      (rum3_contract_bottom_first_imp_original_bottom_first
        ht0 ht1 hx13 hx23 hc13 hc23)
  let μD : Measure Ω :=
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
  change RUM3DeltaCertificate
      (rumRankingPMFOfMeasure μD better hbetter)
      (rumRankingPMFOfMeasure μD worse hworse)
  refine rum3DeltaCertificate_of_measure_probability_facts
    μD better worse hbetter hworse ?_ ?_ ?_
  · exact rum3_monotonicity_top_of_measure_coupling
      μD better worse hbetterTopMeas hworseTopMeas hnoTopOut
      hcorrected_pos
  · exact rum3_lemma3_middle_of_measure_transition_mass
      μD better worse hbetter hworse hnoTopOut
      (rum3_deltaTransition_measureProb_le_of_withDensity_score_facts
        base f x1 x2 x3 t r1 r2 r3 swap better worse
        hp hq hmp hf hswap1 hswap2 hswap3 hctx ht0 ht1 hx12
        hbetterTop_of_scores hworseBottom_scores_of_first
        hworseBottom_of_scores hbetterMiddle_scores_of_first)
  · exact rum3_lemma2_bottom_of_measure_coupling
      μD better worse hbottomImp

/--
Concrete score-ranking version of the continuous delta certificate.

The better ranking is induced by contracted scores, while the worse ranking is
induced by raw scores.  The only remaining model-specific inputs are
measurability of the concrete ranking/event maps, positive corrected-top mass,
the measure-preserving top/middle score swap, and the no-tie invariant needed
to turn weak bottom-score dominance into a pointwise bottom-first ranking fact.
-/
theorem rum3DeltaCertificate_of_withDensity_rankByScores_contraction_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hbetter : Measurable (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3))
    (hworse : Measurable (rum3RankByScoreFns r1 r2 r3))
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) =
        firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω)})
    (hp : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω) ∧
        (1 : Candidate 1) =
          firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)})
    (hq : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω) ∧
        (0 : Candidate 1) =
          firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)})
    (hmp : MeasurePreserving swap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hcorrected_pos :
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | (0 : Candidate 1) =
            firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)} ∩
          {ω | (0 : Candidate 1) =
            firstChoice (rum3RankByScoreFns r1 r2 r3 ω)}ᶜ) ≠ 0)
    (hworseNoTies : ∀ ω, rum3NoTiesByScores (r1 ω) (r2 ω) (r3 ω)) :
    RUM3DeltaCertificate
      (rumRankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3) hbetter)
      (rumRankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (rum3RankByScoreFns r1 r2 r3) hworse) := by
  refine rum3DeltaCertificate_of_withDensity_score_contraction_facts
    base f x1 x2 x3 t r1 r2 r3 swap
    (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3)
    (rum3RankByScoreFns r1 r2 r3)
    hbetter hworse hbetterTopMeas hworseTopMeas hp hq hmp hf
    hswap1 hswap2 hswap3 ?_ ht0 ht1 hx12 hx23
    hcorrected_pos ?_ ?_ ?_ ?_ ?_ ?_
  · intro ω _
    exact le_of_lt (hpos (r3 ω - x3))
  · intro ω htop
    simpa [rum3ContractRankByScoreFns] using
      (rum3RankByScores_firstChoice_of_top_scores htop).symm
  · intro ω hfirst
    exact rum3RankByScores_top_scores_of_firstChoice
      (by simpa [rum3RankByScoreFns] using hfirst.symm)
  · intro ω hfirst
    exact rum3RankByScores_bottom_scores_of_firstChoice
      (by simpa [rum3ContractRankByScoreFns] using hfirst.symm)
  · intro ω hfirst
    exact rum3RankByScores_bottom_scores_of_firstChoice
      (by simpa [rum3RankByScoreFns] using hfirst.symm)
  · intro ω hbottom
    simpa [rum3RankByScoreFns] using
      (rum3RankByScores_firstChoice_of_bottom_scores_of_noTies
        (hworseNoTies ω) hbottom).symm
  · intro ω hfirst
    exact rum3RankByScores_middle_scores_of_firstChoice
      (by simpa [rum3ContractRankByScoreFns] using hfirst.symm)

/--
Concrete score-ranking version of the continuous delta certificate for a genuine
accuracy contraction (`t < 1`).

This removes the pointwise no-tie assumption from
`rum3DeltaCertificate_of_withDensity_rankByScores_contraction_facts`: whenever
the contracted ranking puts the lowest-valued candidate first, strict
contraction forces that candidate's raw score to be strictly first, so the
deterministic tie-breaking convention is irrelevant.
-/
theorem rum3DeltaCertificate_of_withDensity_rankByScores_contraction_facts_of_t_lt_one
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hbetter : Measurable (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3))
    (hworse : Measurable (rum3RankByScoreFns r1 r2 r3))
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) =
        firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω)})
    (hp : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω) ∧
        (1 : Candidate 1) =
          firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)})
    (hq : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω) ∧
        (0 : Candidate 1) =
          firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)})
    (hmp : MeasurePreserving swap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hcorrected_pos :
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | (0 : Candidate 1) =
            firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)} ∩
          {ω | (0 : Candidate 1) =
            firstChoice (rum3RankByScoreFns r1 r2 r3 ω)}ᶜ) ≠ 0) :
    RUM3DeltaCertificate
      (rumRankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3) hbetter)
      (rumRankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (rum3RankByScoreFns r1 r2 r3) hworse) := by
  let better : Ω → Ranking 1 :=
    rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3
  let worse : Ω → Ranking 1 := rum3RankByScoreFns r1 r2 r3
  let μD : Measure Ω :=
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  have hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω) := by
    intro ω hwTop
    have htopRaw :
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω) :=
      rum3RankByScores_top_scores_of_firstChoice
        (by simpa [worse, rum3RankByScoreFns] using hwTop.symm)
    exact (rum3RankByScores_firstChoice_of_top_scores
      (rum3_contract_top_first_of_original_top_first
        ht0 ht1 (le_of_lt hx12) (le_of_lt hx13)
        htopRaw.1 htopRaw.2)).symm
  have hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω) := by
    intro ω hbBetter
    have hbottomContract :
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) :=
      rum3RankByScores_bottom_scores_of_firstChoice
        (by simpa [better, rum3ContractRankByScoreFns] using hbBetter.symm)
    rcases rum3_contract_bottom_first_imp_original_bottom_first_strict_of_t_lt_one
        ht0 htlt1 hx13 hx23 hbottomContract.1 hbottomContract.2 with
      ⟨hr13, hr23⟩
    exact (rum3RankByScores_firstChoice_of_strict_bottom_scores hr13 hr23).symm
  change RUM3DeltaCertificate
      (rumRankingPMFOfMeasure μD better hbetter)
      (rumRankingPMFOfMeasure μD worse hworse)
  refine rum3DeltaCertificate_of_measure_probability_facts
    μD better worse hbetter hworse ?_ ?_ ?_
  · exact rum3_monotonicity_top_of_measure_coupling
      μD better worse hbetterTopMeas hworseTopMeas hnoTopOut
      hcorrected_pos
  · refine rum3_lemma3_middle_of_measure_transition_mass
      μD better worse hbetter hworse hnoTopOut ?_
    refine measureProb_le_of_measure_le μD
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω))
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω)) ?_
    change
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
          {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)} ≤
        base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
          {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω)}
    refine rum3_withDensity_swap12_measure_le_of_density_formula
      base f x1 x2 x3 r1 r2 r3 swap
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω))
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω))
      (by simpa [better, worse] using hp)
      (by simpa [better, worse] using hq)
      hmp ?_ hf hswap1 hswap2 hswap3
      (fun ω _ => le_of_lt (hpos (r3 ω - x3))) hx12 ?_
    · intro ω htransition
      have hrawBottomStrict :
          r1 ω < r3 ω ∧ r2 ω < r3 ω :=
        rum3RankByScores_strict_bottom_scores_of_firstChoice
          (by simpa [worse, rum3RankByScoreFns] using htransition.1.symm)
      have hrawBottomWeak :
          rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) :=
        ⟨le_of_lt hrawBottomStrict.1, le_of_lt hrawBottomStrict.2⟩
      have hbetterMiddle :
          rum3MiddleBeatsTopByScores
            (rumContractScore t x1 (r1 ω))
            (rumContractScore t x2 (r2 ω))
            (rumContractScore t x3 (r3 ω)) :=
        rum3RankByScores_middle_scores_of_firstChoice
          (by simpa [better, rum3ContractRankByScoreFns] using htransition.2.symm)
      rcases rum3_swap_middle_transition_geometry
          ht0 ht1 hx12 hrawBottomWeak.1 hrawBottomWeak.2
          hbetterMiddle.1 hbetterMiddle.2 with
        ⟨_, _, hc21_swap, hc31_swap⟩
      constructor
      · have h13swap : r1 (swap ω) < r3 (swap ω) := by
          rw [hswap1, hswap3]
          exact hrawBottomStrict.2
        have h23swap : r2 (swap ω) < r3 (swap ω) := by
          rw [hswap2, hswap3]
          exact hrawBottomStrict.1
        exact (rum3RankByScores_firstChoice_of_strict_bottom_scores
          h13swap h23swap).symm
      · exact (rum3RankByScores_firstChoice_of_top_scores (by
          unfold rum3TopFirstByScores
          constructor
          · rw [hswap2, hswap1]
            exact hc21_swap
          · rw [hswap3, hswap1]
            exact hc31_swap)).symm
    · intro ω htransition
      have hbetterMiddle :
          rum3MiddleBeatsTopByScores
            (rumContractScore t x1 (r1 ω))
            (rumContractScore t x2 (r2 ω))
            (rumContractScore t x3 (r3 ω)) :=
        rum3RankByScores_middle_scores_of_firstChoice
          (by simpa [better, rum3ContractRankByScoreFns] using htransition.2.symm)
      exact rum3_swap_middle_base_score_lt ht0 ht1 hx12 hbetterMiddle.1
  · exact rum3_lemma2_bottom_of_measure_coupling μD better worse hbottomImp

/--
Finite paired-density skeleton for the `x₂` versus `x₃` lambda comparison.

If a finite equivalence sends each realization choosing `x₃` after `x₁` is
removed to one choosing `x₂`, never decreases mass on that wrong-choice event,
and strictly increases mass for one such realization, then the wrong-choice
probability is strictly smaller than `λ₁`.
-/
theorem rum3Lambda1_wrong_lt_correct_of_equiv
    (μ : PMF (Ranking 1)) (swap : Ranking 1 ≃ Ranking 1)
    (hmap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μ π).toReal ≤ (μ (swap π)).toReal)
    {π₀ : Ranking 1}
    (hwrong : bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict : (μ π₀).toReal < (μ (swap π₀)).toReal) :
    pmfProb μ
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
      rum3Lambda1 μ := by
  unfold rum3Lambda1
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    μ swap
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1))
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    hmap hmass hwrong hstrict

/--
Finite paired-density skeleton for the `x₁` versus `x₂` lambda comparison.

If a finite equivalence sends each realization choosing `x₂` after `x₃` is
removed to one choosing `x₁`, never decreases mass on that wrong-choice event,
and strictly increases mass for one such realization, then the wrong-choice
probability is strictly smaller than `λ₃`.
-/
theorem rum3Lambda3_wrong_lt_correct_of_equiv
    (μ : PMF (Ranking 1)) (swap : Ranking 1 ≃ Ranking 1)
    (hmap : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μ π).toReal ≤ (μ (swap π)).toReal)
    {π₀ : Ranking 1}
    (hwrong : bestRemainingAfter π₀ (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (μ π₀).toReal < (μ (swap π₀)).toReal) :
    pmfProb μ
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
      rum3Lambda3 μ := by
  unfold rum3Lambda3
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    μ swap
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1))
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hwrong hstrict

/--
Finite paired-density skeleton for the `λ₁ < λ₂` gap in Theorem 6.

If a finite equivalence sends each realization where `x₂` beats `x₃` after
`x₁` is removed to one where `x₁` beats `x₃` after `x₂` is removed, never
decreases mass on the source event, and strictly increases mass for one such
realization, then `λ₁ < λ₂`.
-/
theorem rum3Lambda1_lt_lambda2_of_equiv
    (μ : PMF (Ranking 1)) (swap : Ranking 1 ≃ Ranking 1)
    (hmap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap π) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μ π).toReal ≤ (μ (swap π)).toReal)
    {π₀ : Ranking 1}
    (hsource : bestRemainingAfter π₀ (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (μ π₀).toReal < (μ (swap π₀)).toReal) :
    rum3Lambda1 μ < rum3Lambda2 μ := by
  unfold rum3Lambda1 rum3Lambda2
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    μ swap
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hsource hstrict

/--
Sample-space version of the `x₂` versus `x₃` lambda comparison.

The strict change-of-variables argument runs on a finite realization space `Ω`;
the two marginal-identification equalities connect it back to the ranking law.
-/
theorem rum3Lambda1_wrong_lt_correct_of_sample_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hwrongμ :
      pmfProb μ
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hcorrectμ :
      rum3Lambda1 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hmap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal)
    {ω₀ : Ω}
    (hwrong : bestRemainingAfter (rank ω₀) (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict : (ν ω₀).toReal < (ν (swap ω₀)).toReal) :
    pmfProb μ
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
      rum3Lambda1 μ := by
  rw [hwrongμ, hcorrectμ]
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    ν swap
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    hmap hmass hwrong hstrict

/--
Sample-space version of the `x₁` versus `x₂` lambda comparison.
-/
theorem rum3Lambda3_wrong_lt_correct_of_sample_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hwrongμ :
      pmfProb μ
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)))
    (hcorrectμ :
      rum3Lambda3 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hmap : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal)
    {ω₀ : Ω}
    (hwrong : bestRemainingAfter (rank ω₀) (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (ν ω₀).toReal < (ν (swap ω₀)).toReal) :
    pmfProb μ
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
      rum3Lambda3 μ := by
  rw [hwrongμ, hcorrectμ]
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    ν swap
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hwrong hstrict

/--
Sample-space version of the `λ₁ < λ₂` gap comparison.
-/
theorem rum3Lambda1_lt_lambda2_of_sample_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hlambda1μ :
      rum3Lambda1 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hmap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal)
    {ω₀ : Ω}
    (hsource : bestRemainingAfter (rank ω₀) (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (ν ω₀).toReal < (ν (swap ω₀)).toReal) :
    rum3Lambda1 μ < rum3Lambda2 μ := by
  rw [hlambda1μ, hlambda2μ]
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    ν swap
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hsource hstrict

/--
Sample-space `λ₁ < λ₂` comparison using only the asymmetric gap event.

This is the right finite analogue for the paper's two-candidate comparison: the
common event where both `λ₁` and `λ₂` hold cancels, and the swap only needs to
map the residual `λ₁ ∧ ¬λ₂` event into `λ₂ ∧ ¬λ₁`.
-/
theorem rum3Lambda1_lt_lambda2_of_cross_sample_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hlambda1μ :
      rum3Lambda1 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hmap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank (swap ω)) (0 : Candidate 1) =
            (1 : Candidate 1))
    (hmass : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal)
    {ω₀ : Ω}
    (hsource :
      bestRemainingAfter (rank ω₀) (0 : Candidate 1) = (1 : Candidate 1) ∧
        ¬ bestRemainingAfter (rank ω₀) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hstrict : (ν ω₀).toReal < (ν (swap ω₀)).toReal) :
    rum3Lambda1 μ < rum3Lambda2 μ := by
  rw [hlambda1μ, hlambda2μ]
  exact pmfProb_lt_of_cross_event_equiv_mass_le_of_exists_strict
    ν swap
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hsource hstrict

/--
Score-level event map for the `x₂` versus `x₃` lambda swap.

If choosing `x₃` after removing `x₁` implies the `x₃` score strictly beats the
`x₂` score, and a weak `x₂` score lead implies choosing `x₂`, then swapping the
two scores maps the wrong event into the correct event.
-/
theorem rum3Lambda1_wrong_to_correct_map_of_score_swap23
    {Ω : Type*} (rank : Ω → Ranking 1) (s2 s3 : Ω → ℝ) (swap : Ω → Ω)
    (hwrong_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        s2 ω < s3 ω)
    (hcorrect_of_scores : ∀ ω,
      s3 ω ≤ s2 ω →
        bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hswap2 : ∀ ω, s2 (swap ω) = s3 ω)
    (hswap3 : ∀ ω, s3 (swap ω) = s2 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (0 : Candidate 1) =
          (1 : Candidate 1) := by
  intro ω hwrong
  apply hcorrect_of_scores
  rw [hswap2, hswap3]
  exact le_of_lt (hwrong_scores ω hwrong)

/--
Score-level event map for the `x₁` versus `x₂` lambda swap.
-/
theorem rum3Lambda3_wrong_to_correct_map_of_score_swap12
    {Ω : Type*} (rank : Ω → Ranking 1) (s1 s2 : Ω → ℝ) (swap : Ω → Ω)
    (hwrong_scores : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        s1 ω < s2 ω)
    (hcorrect_of_scores : ∀ ω,
      s2 ω ≤ s1 ω →
        bestRemainingAfter (rank ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hswap1 : ∀ ω, s1 (swap ω) = s2 ω)
    (hswap2 : ∀ ω, s2 (swap ω) = s1 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (2 : Candidate 1) =
          (0 : Candidate 1) := by
  intro ω hwrong
  apply hcorrect_of_scores
  rw [hswap1, hswap2]
  exact le_of_lt (hwrong_scores ω hwrong)

/--
Score-level event map for the `λ₁ < λ₂` comparison.

If choosing `x₂` after removing `x₁` implies that the `x₂` score weakly beats
the `x₃` score, and a weak `x₁` score lead over `x₃` implies choosing `x₁`
after removing `x₂`, then swapping the `x₁` and `x₂` scores maps the source
event for `λ₁` into the target event for `λ₂`.
-/
theorem rum3Lambda1_to_lambda2_map_of_score_swap12
    {Ω : Type*} (rank : Ω → Ranking 1)
    (s1 s2 s3 : Ω → ℝ) (swap : Ω → Ω)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        s3 ω ≤ s2 ω)
    (htarget_of_scores : ∀ ω,
      s3 ω ≤ s1 ω →
        bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hswap1 : ∀ ω, s1 (swap ω) = s2 ω)
    (hswap3 : ∀ ω, s3 (swap ω) = s3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (1 : Candidate 1) =
          (0 : Candidate 1) := by
  intro ω hsource
  apply htarget_of_scores
  rw [hswap1, hswap3]
  exact hsource_scores ω hsource

/--
Score-level cross-event map for the `λ₁ < λ₂` comparison.

The source is the asymmetric gap `λ₁ ∧ ¬λ₂`.  After swapping the `x₁` and `x₂`
score coordinates, the source score inequalities imply the target asymmetric
event `λ₂ ∧ ¬λ₁`.
-/
theorem rum3Lambda1_to_lambda2_cross_map_of_score_swap12
    {Ω : Type*} (rank : Ω → Ranking 1)
    (s1 s2 s3 : Ω → ℝ) (swap : Ω → Ω)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        s3 ω ≤ s2 ω)
    (hnot_target_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        s1 ω < s3 ω)
    (htarget_of_scores : ∀ ω,
      s3 ω ≤ s1 ω →
        bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hnot_source_of_scores : ∀ ω,
      s2 ω < s3 ω →
        ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hswap1 : ∀ ω, s1 (swap ω) = s2 ω)
    (hswap2 : ∀ ω, s2 (swap ω) = s1 ω)
    (hswap3 : ∀ ω, s3 (swap ω) = s3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank (swap ω)) (0 : Candidate 1) =
            (1 : Candidate 1) := by
  intro ω hsource
  constructor
  · apply htarget_of_scores
    rw [hswap1, hswap3]
    exact hsource_scores ω hsource.1
  · apply hnot_source_of_scores
    rw [hswap2, hswap3]
    exact hnot_target_scores ω hsource.2

/--
Continuous density-derived residual comparison for `λ₁ < λ₂`.

This is the measure-level version of the paper's residual change of variables:
the `x₁`/`x₂` coordinate swap strictly increases the with-density mass of
`λ₁ ∧ ¬λ₂` into `λ₂ ∧ ¬λ₁`.
-/
theorem rum3_lambda13cross_withDensity_measure_lt_of_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (hp : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)})
    (hq : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hx12 : x2 < x1)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hnot_target_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        r1 ω < r3 ω)
    (htarget_of_scores : ∀ ω,
      r3 ω ≤ r1 ω →
        bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hnot_source_of_scores : ∀ ω,
      r2 ω < r3 ω →
        ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hfi :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
                (1 : Candidate 1) ∧
              ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) =
                (0 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos :
      base
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
                (1 : Candidate 1) ∧
              ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) =
                (0 : Candidate 1)} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)}ᶜ) <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)}ᶜ) := by
  simpa [Set.setOf_and, Set.compl_setOf] using
    (rum3_withDensity_swap12_measure_lt_of_density_formula
      base f x1 x2 x3 r1 r2 r3 swap
      (fun ω =>
        bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
      (fun ω =>
        bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
      hp hq hmp hD
      (rum3Lambda1_to_lambda2_cross_map_of_score_swap12
        rank r1 r2 r3 swap hsource_scores hnot_target_scores
        htarget_of_scores hnot_source_of_scores hswap1 hswap2 hswap3)
      hf hpos hswap1 hswap2 hswap3 hx12
      (fun ω hω =>
        lt_of_lt_of_le (hnot_target_scores ω hω.2)
          (hsource_scores ω hω.1))
      hfi hsource_pos)

/-- Continuous density-derived wrong-vs-correct comparison for `λ₁`. -/
theorem rum3_lambda23wrong_withDensity_measure_lt_of_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (hp : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1)})
    (hq : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (1 : Candidate 1)})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hx23 : x3 < x2)
    (hwrong_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        r2 ω < r3 ω)
    (hcorrect_of_scores : ∀ ω,
      r3 ω ≤ r2 ω →
        bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hfi :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos :
      base {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1)} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)} :=
  rum3_withDensity_swap23_measure_lt_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
      (2 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
      (1 : Candidate 1))
    hp hq hmp hD
    (rum3Lambda1_wrong_to_correct_map_of_score_swap23
      rank r2 r3 swap hwrong_scores hcorrect_of_scores hswap2 hswap3)
    hf hpos hswap1 hswap2 hswap3 hx23 hwrong_scores hfi hsource_pos

/-- Continuous density-derived wrong-vs-correct comparison for `λ₃`. -/
theorem rum3_lambda12wrong_withDensity_measure_lt_of_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (hp : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
        (1 : Candidate 1)})
    (hq : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
        (0 : Candidate 1)})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hx12 : x2 < x1)
    (hwrong_scores : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        r1 ω < r2 ω)
    (hcorrect_of_scores : ∀ ω,
      r2 ω ≤ r1 ω →
        bestRemainingAfter (rank ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hfi :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos :
      base {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
        (1 : Candidate 1)} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)} :=
  rum3_withDensity_swap12_measure_lt_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
      (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
      (0 : Candidate 1))
    hp hq hmp hD
    (rum3Lambda3_wrong_to_correct_map_of_score_swap12
      rank r1 r2 swap hwrong_scores hcorrect_of_scores hswap1 hswap2)
    hf hpos hswap1 hswap2 hswap3 hx12 hwrong_scores hfi hsource_pos

/--
Lambda certificate from finite paired-density swap facts.

This packages the two strict pairwise comparisons in the form produced by a
finite change-of-variables argument, while keeping the separate support witness
needed for `λ₁ < 1`.
-/
theorem rum3LambdaCertificate_of_pairwise_swap_facts_and_support
    {μWorse : PMF (Ranking 1)}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (swap23 : Ranking 1 ≃ Ranking 1)
    (hmap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap23 π)).toReal)
    {π23 : Ranking 1}
    (hwrong23 : bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (μWorse π23).toReal < (μWorse (swap23 π23)).toReal)
    {πsupport : Ranking 1}
    (hchooseSupport :
      bestRemainingAfter πsupport (0 : Candidate 1) = (2 : Candidate 1))
    (hmassSupport : 0 < (μWorse πsupport).toReal)
    (swap12 : Ranking 1 ≃ Ranking 1)
    (hmap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap12 π)).toReal)
    {π12 : Ranking 1}
    (hwrong12 : bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (μWorse π12).toReal < (μWorse (swap12 π12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_support
    h13_gt_23
    (rum3Lambda1_wrong_lt_correct_of_equiv
      μWorse swap23 hmap23 hmass23 hwrong23 hstrict23)
    hchooseSupport hmassSupport
    (rum3Lambda3_wrong_lt_correct_of_equiv
      μWorse swap12 hmap12 hmass12 hwrong12 hstrict12)

/--
Lambda certificate from finite paired-density swap facts, including the
`λ₁ < λ₂` comparison as a swap certificate rather than a raw scalar premise.
-/
theorem rum3LambdaCertificate_of_all_pairwise_swap_facts_and_support
    {μWorse : PMF (Ranking 1)}
    (swap13gap : Ranking 1 ≃ Ranking 1)
    (hmap13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap13gap π) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap13gap π)).toReal)
    {π13gap : Ranking 1}
    (hsource13gap :
      bestRemainingAfter π13gap (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict13gap :
      (μWorse π13gap).toReal < (μWorse (swap13gap π13gap)).toReal)
    (swap23 : Ranking 1 ≃ Ranking 1)
    (hmap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap23 π)).toReal)
    {π23 : Ranking 1}
    (hwrong23 : bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (μWorse π23).toReal < (μWorse (swap23 π23)).toReal)
    {πsupport : Ranking 1}
    (hchooseSupport :
      bestRemainingAfter πsupport (0 : Candidate 1) = (2 : Candidate 1))
    (hmassSupport : 0 < (μWorse πsupport).toReal)
    (swap12 : Ranking 1 ≃ Ranking 1)
    (hmap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap12 π)).toReal)
    {π12 : Ranking 1}
    (hwrong12 : bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (μWorse π12).toReal < (μWorse (swap12 π12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_swap_facts_and_support
    (rum3Lambda1_lt_lambda2_of_equiv
      μWorse swap13gap hmap13gap hmass13gap hsource13gap hstrict13gap)
    swap23 hmap23 hmass23 hwrong23 hstrict23
    hchooseSupport hmassSupport swap12 hmap12 hmass12 hwrong12 hstrict12

/--
Lambda certificate from finite paired-density swap facts plus full support of
the finite human ranking law.
-/
theorem rum3LambdaCertificate_of_all_pairwise_swap_facts_and_full_support
    {μWorse : PMF (Ranking 1)}
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (swap13gap : Ranking 1 ≃ Ranking 1)
    (hmap13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap13gap π) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap13gap π)).toReal)
    {π13gap : Ranking 1}
    (hsource13gap :
      bestRemainingAfter π13gap (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict13gap :
      (μWorse π13gap).toReal < (μWorse (swap13gap π13gap)).toReal)
    (swap23 : Ranking 1 ≃ Ranking 1)
    (hmap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap23 π)).toReal)
    {π23 : Ranking 1}
    (hwrong23 : bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (μWorse π23).toReal < (μWorse (swap23 π23)).toReal)
    (swap12 : Ranking 1 ≃ Ranking 1)
    (hmap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap12 π)).toReal)
    {π12 : Ranking 1}
    (hwrong12 : bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (μWorse π12).toReal < (μWorse (swap12 π12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    (rum3Lambda1_lt_lambda2_of_equiv
      μWorse swap13gap hmap13gap hmass13gap hsource13gap hstrict13gap)
    (rum3Lambda1_wrong_lt_correct_of_equiv
      μWorse swap23 hmap23 hmass23 hwrong23 hstrict23)
    hfull
    (rum3Lambda3_wrong_lt_correct_of_equiv
      μWorse swap12 hmap12 hmass12 hwrong12 hstrict12)

/--
Lambda certificate from finite sample-space swap facts plus full support of the
human ranking law.

This is the finite/discrete analogue closest to the continuous RUM density
argument: the swaps act on realizations, and marginal equalities identify the
realization events with the ranking-law lambda events.
-/
theorem rum3LambdaCertificate_of_sample_swap_facts_and_full_support
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μWorse : PMF (Ranking 1)}
    (ν : PMF Ω) (rank : Ω → Ranking 1)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (hlambda1μ :
      rum3Lambda1 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong23μ :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hlambda3μ :
      rum3Lambda3 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong12μ :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)))
    (swap13gap : Ω ≃ Ω)
    (hmap13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap13gap ω)) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hmass13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap13gap ω)).toReal)
    {ω13gap : Ω}
    (hsource13gap :
      bestRemainingAfter (rank ω13gap) (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict13gap :
      (ν ω13gap).toReal < (ν (swap13gap ω13gap)).toReal)
    (swap23 : Ω ≃ Ω)
    (hmap23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap23 ω)) (0 : Candidate 1) =
          (1 : Candidate 1))
    (hmass23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap23 ω)).toReal)
    {ω23 : Ω}
    (hwrong23 :
      bestRemainingAfter (rank ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (ν ω23).toReal < (ν (swap23 ω23)).toReal)
    (swap12 : Ω ≃ Ω)
    (hmap12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap12 ω)) (2 : Candidate 1) =
          (0 : Candidate 1))
    (hmass12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap12 ω)).toReal)
    {ω12 : Ω}
    (hwrong12 :
      bestRemainingAfter (rank ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (ν ω12).toReal < (ν (swap12 ω12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    (rum3Lambda1_lt_lambda2_of_sample_equiv
      μWorse ν rank swap13gap hlambda1μ hlambda2μ
      hmap13gap hmass13gap hsource13gap hstrict13gap)
    (rum3Lambda1_wrong_lt_correct_of_sample_equiv
      μWorse ν rank swap23 hwrong23μ hlambda1μ
      hmap23 hmass23 hwrong23 hstrict23)
    hfull
    (rum3Lambda3_wrong_lt_correct_of_sample_equiv
      μWorse ν rank swap12 hwrong12μ hlambda3μ
      hmap12 hmass12 hwrong12 hstrict12)

/--
Lambda certificate from finite sample-space swap facts where the `λ₁ < λ₂`
comparison is proved only on the asymmetric residual event `λ₁ ∧ ¬λ₂`.

This is the sample-space form closest to the paper's cancellation argument:
the common part of the two lambda events cancels, and only the residual gap
requires a mass-improving change of variables.
-/
theorem rum3LambdaCertificate_of_sample_cross_gap_and_wrong_swap_facts_and_full_support
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μWorse : PMF (Ranking 1)}
    (ν : PMF Ω) (rank : Ω → Ranking 1)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (hlambda1μ :
      rum3Lambda1 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong23μ :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hlambda3μ :
      rum3Lambda3 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong12μ :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)))
    (swap13gap : Ω ≃ Ω)
    (hmap13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (rank (swap13gap ω)) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank (swap13gap ω)) (0 : Candidate 1) =
            (1 : Candidate 1))
    (hmass13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap13gap ω)).toReal)
    {ω13gap : Ω}
    (hsource13gap :
      bestRemainingAfter (rank ω13gap) (0 : Candidate 1) = (1 : Candidate 1) ∧
        ¬ bestRemainingAfter (rank ω13gap) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hstrict13gap :
      (ν ω13gap).toReal < (ν (swap13gap ω13gap)).toReal)
    (swap23 : Ω ≃ Ω)
    (hmap23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap23 ω)) (0 : Candidate 1) =
          (1 : Candidate 1))
    (hmass23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap23 ω)).toReal)
    {ω23 : Ω}
    (hwrong23 :
      bestRemainingAfter (rank ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (ν ω23).toReal < (ν (swap23 ω23)).toReal)
    (swap12 : Ω ≃ Ω)
    (hmap12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap12 ω)) (2 : Candidate 1) =
          (0 : Candidate 1))
    (hmass12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap12 ω)).toReal)
    {ω12 : Ω}
    (hwrong12 :
      bestRemainingAfter (rank ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (ν ω12).toReal < (ν (swap12 ω12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    (rum3Lambda1_lt_lambda2_of_cross_sample_equiv
      μWorse ν rank swap13gap hlambda1μ hlambda2μ
      hmap13gap hmass13gap hsource13gap hstrict13gap)
    (rum3Lambda1_wrong_lt_correct_of_sample_equiv
      μWorse ν rank swap23 hwrong23μ hlambda1μ
      hmap23 hmass23 hwrong23 hstrict23)
    hfull
    (rum3Lambda3_wrong_lt_correct_of_sample_equiv
      μWorse ν rank swap12 hwrong12μ hlambda3μ
      hmap12 hmass12 hwrong12 hstrict12)

theorem expectedBestAfterRemoval_rum3_remove0
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) :
    AccuracyFamily.expectedBestAfterRemoval μ value (0 : Candidate 1) =
      rum3Lambda1 μ * value (1 : Candidate 1) +
        (1 - rum3Lambda1 μ) * value (2 : Candidate 1) := by
  classical
  unfold AccuracyFamily.expectedBestAfterRemoval rum3Lambda1
  refine pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    (fun π => value (bestRemainingAfter π (0 : Candidate 1)))
    (value (1 : Candidate 1)) (value (2 : Candidate 1)) ?_
  intro π
  by_cases h : bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1)
  · simp [h]
  · have hne0 : bestRemainingAfter π (0 : Candidate 1) ≠ (0 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (0 : Candidate 1)
    have h2 : bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (0 : Candidate 1)).val = 2
      have hval0 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact hne0 (Fin.ext hv)
      have hval1 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 1 := by
        intro hv
        exact h (Fin.ext hv)
      have hlt := (bestRemainingAfter π (0 : Candidate 1)).isLt
      omega
    simp [h2]

theorem expectedBestAfterRemoval_rum3_remove1
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) :
    AccuracyFamily.expectedBestAfterRemoval μ value (1 : Candidate 1) =
      rum3Lambda2 μ * value (0 : Candidate 1) +
        (1 - rum3Lambda2 μ) * value (2 : Candidate 1) := by
  classical
  unfold AccuracyFamily.expectedBestAfterRemoval rum3Lambda2
  refine pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    μ (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))
    (fun π => value (bestRemainingAfter π (1 : Candidate 1)))
    (value (0 : Candidate 1)) (value (2 : Candidate 1)) ?_
  intro π
  by_cases h : bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1)
  · simp [h]
  · have hne1 : bestRemainingAfter π (1 : Candidate 1) ≠ (1 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (1 : Candidate 1)
    have h2 : bestRemainingAfter π (1 : Candidate 1) = (2 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (1 : Candidate 1)).val = 2
      have hval0 : (bestRemainingAfter π (1 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact h (Fin.ext hv)
      have hval1 : (bestRemainingAfter π (1 : Candidate 1)).val ≠ 1 := by
        intro hv
        exact hne1 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (1 : Candidate 1)).isLt
      omega
    simp [h2]

theorem expectedBestAfterRemoval_rum3_remove2
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) :
    AccuracyFamily.expectedBestAfterRemoval μ value (2 : Candidate 1) =
      rum3Lambda3 μ * value (0 : Candidate 1) +
        (1 - rum3Lambda3 μ) * value (1 : Candidate 1) := by
  classical
  unfold AccuracyFamily.expectedBestAfterRemoval rum3Lambda3
  refine pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))
    (fun π => value (bestRemainingAfter π (2 : Candidate 1)))
    (value (0 : Candidate 1)) (value (1 : Candidate 1)) ?_
  intro π
  by_cases h : bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1)
  · simp [h]
  · have hne2 : bestRemainingAfter π (2 : Candidate 1) ≠ (2 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (2 : Candidate 1)
    have h1 : bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (2 : Candidate 1)).val = 1
      have hval0 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact h (Fin.ext hv)
      have hval2 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 2 := by
        intro hv
        exact hne2 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (2 : Candidate 1)).isLt
      omega
    simp [h1]

theorem rum3_definition2_first0_gain_of_pairwise_gap
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    (hvalue : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hgap :
      pmfConditionalProb μ
          (fun τ => (0 : Candidate 1) = firstChoice τ)
          (fun τ => secondChoice τ = (1 : Candidate 1)) <
        rum3Lambda1 μ)
    (hfirst : 0 < firstChoiceProb μ (0 : Candidate 1)) :
    0 < pmfConditionalExp μ
      (fun τ => (0 : Candidate 1) = firstChoice τ)
      (fun τ =>
        pmfExp μ (fun π =>
          value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ))) := by
  classical
  let B : ℝ := AccuracyFamily.expectedBestAfterRemoval μ value (0 : Candidate 1)
  have hfirst' :
      0 < pmfProb μ (fun τ => (0 : Candidate 1) = firstChoice τ) := by
    simpa [firstChoiceProb] using hfirst
  rw [pmfConditionalExp_eq_conditionalProb_mul_add_one_sub_mul_of_forall_eq_if
    (μ := μ)
    (p := fun τ => (0 : Candidate 1) = firstChoice τ)
    (q := fun τ => secondChoice τ = (1 : Candidate 1))
    (f := fun τ =>
      pmfExp μ (fun π =>
        value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))
    (x := B - value (1 : Candidate 1))
    (y := B - value (2 : Candidate 1)) hfirst' ?_]
  · have hB :
        B =
          rum3Lambda1 μ * value (1 : Candidate 1) +
            (1 - rum3Lambda1 μ) * value (2 : Candidate 1) := by
      simpa [B] using expectedBestAfterRemoval_rum3_remove0 μ value
    let c : ℝ :=
      pmfConditionalProb μ
        (fun τ => (0 : Candidate 1) = firstChoice τ)
        (fun τ => secondChoice τ = (1 : Candidate 1))
    have hcalc :
        c * (B - value (1 : Candidate 1)) +
            (1 - c) * (B - value (2 : Candidate 1)) =
          (rum3Lambda1 μ - c) *
            (value (1 : Candidate 1) - value (2 : Candidate 1)) := by
      dsimp [c]
      rw [hB]
      ring
    rw [hcalc]
    exact mul_pos (sub_pos.mpr hgap) (sub_pos.mpr hvalue)
  · intro τ hτ
    have hbest :
        pmfExp μ (fun π =>
            value (bestRemainingAfter π (firstChoice τ))) = B := by
      unfold B AccuracyFamily.expectedBestAfterRemoval
      refine pmfExp_congr μ ?_
      intro π
      rw [← hτ]
    have hbest_apply :
        pmfExp μ (fun π =>
            value (bestRemainingAfter π (τ 0))) = B := by
      simpa [firstChoice] using hbest
    have hgain :
        pmfExp μ (fun π =>
            value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)) =
          B - value (secondChoice τ) := by
      rw [pmfExp_sub]
      simpa [firstChoice, hbest_apply]
    by_cases hq : secondChoice τ = (1 : Candidate 1)
    · have hq' : τ 1 = (1 : Candidate 1) := by
        simpa [secondChoice] using hq
      simpa [secondChoice, hq'] using hgain
    · have hfirstτ : firstChoice τ = (0 : Candidate 1) := hτ.symm
      have hsecond_ne0 : secondChoice τ ≠ (0 : Candidate 1) := by
        intro hsecond0
        exact (firstChoice_ne_secondChoice τ) (by rw [hfirstτ, hsecond0])
      have hsecond2 : secondChoice τ = (2 : Candidate 1) := by
        apply Fin.ext
        change (secondChoice τ).val = 2
        have hval0 : (secondChoice τ).val ≠ 0 := by
          intro hv
          exact hsecond_ne0 (Fin.ext hv)
        have hval1 : (secondChoice τ).val ≠ 1 := by
          intro hv
          exact hq (Fin.ext hv)
        have hlt := (secondChoice τ).isLt
        omega
      have hq' : τ 1 ≠ (1 : Candidate 1) := by
        simpa [secondChoice] using hq
      have hsecond2' : τ 1 = (2 : Candidate 1) := by
        simpa [secondChoice] using hsecond2
      simpa [secondChoice, hq', hsecond2'] using hgain

theorem rum3_definition2_first1_gain_of_pairwise_gap
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    (hvalue : value (2 : Candidate 1) < value (0 : Candidate 1))
    (hgap :
      pmfConditionalProb μ
          (fun τ => (1 : Candidate 1) = firstChoice τ)
          (fun τ => secondChoice τ = (0 : Candidate 1)) <
        rum3Lambda2 μ)
    (hfirst : 0 < firstChoiceProb μ (1 : Candidate 1)) :
    0 < pmfConditionalExp μ
      (fun τ => (1 : Candidate 1) = firstChoice τ)
      (fun τ =>
        pmfExp μ (fun π =>
          value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ))) := by
  classical
  let B : ℝ := AccuracyFamily.expectedBestAfterRemoval μ value (1 : Candidate 1)
  have hfirst' :
      0 < pmfProb μ (fun τ => (1 : Candidate 1) = firstChoice τ) := by
    simpa [firstChoiceProb] using hfirst
  rw [pmfConditionalExp_eq_conditionalProb_mul_add_one_sub_mul_of_forall_eq_if
    (μ := μ)
    (p := fun τ => (1 : Candidate 1) = firstChoice τ)
    (q := fun τ => secondChoice τ = (0 : Candidate 1))
    (f := fun τ =>
      pmfExp μ (fun π =>
        value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))
    (x := B - value (0 : Candidate 1))
    (y := B - value (2 : Candidate 1)) hfirst' ?_]
  · have hB :
        B =
          rum3Lambda2 μ * value (0 : Candidate 1) +
            (1 - rum3Lambda2 μ) * value (2 : Candidate 1) := by
      simpa [B] using expectedBestAfterRemoval_rum3_remove1 μ value
    let c : ℝ :=
      pmfConditionalProb μ
        (fun τ => (1 : Candidate 1) = firstChoice τ)
        (fun τ => secondChoice τ = (0 : Candidate 1))
    have hcalc :
        c * (B - value (0 : Candidate 1)) +
            (1 - c) * (B - value (2 : Candidate 1)) =
          (rum3Lambda2 μ - c) *
            (value (0 : Candidate 1) - value (2 : Candidate 1)) := by
      dsimp [c]
      rw [hB]
      ring
    rw [hcalc]
    exact mul_pos (sub_pos.mpr hgap) (sub_pos.mpr hvalue)
  · intro τ hτ
    have hbest :
        pmfExp μ (fun π =>
            value (bestRemainingAfter π (firstChoice τ))) = B := by
      unfold B AccuracyFamily.expectedBestAfterRemoval
      refine pmfExp_congr μ ?_
      intro π
      rw [← hτ]
    have hbest_apply :
        pmfExp μ (fun π =>
            value (bestRemainingAfter π (τ 0))) = B := by
      simpa [firstChoice] using hbest
    have hgain :
        pmfExp μ (fun π =>
            value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)) =
          B - value (secondChoice τ) := by
      rw [pmfExp_sub]
      simpa [firstChoice, hbest_apply]
    by_cases hq : secondChoice τ = (0 : Candidate 1)
    · have hq' : τ 1 = (0 : Candidate 1) := by
        simpa [secondChoice] using hq
      simpa [secondChoice, hq'] using hgain
    · have hfirstτ : firstChoice τ = (1 : Candidate 1) := hτ.symm
      have hsecond_ne1 : secondChoice τ ≠ (1 : Candidate 1) := by
        intro hsecond1
        exact (firstChoice_ne_secondChoice τ) (by rw [hfirstτ, hsecond1])
      have hsecond2 : secondChoice τ = (2 : Candidate 1) := by
        apply Fin.ext
        change (secondChoice τ).val = 2
        have hval0 : (secondChoice τ).val ≠ 0 := by
          intro hv
          exact hq (Fin.ext hv)
        have hval1 : (secondChoice τ).val ≠ 1 := by
          intro hv
          exact hsecond_ne1 (Fin.ext hv)
        have hlt := (secondChoice τ).isLt
        omega
      have hq' : τ 1 ≠ (0 : Candidate 1) := by
        simpa [secondChoice] using hq
      have hsecond2' : τ 1 = (2 : Candidate 1) := by
        simpa [secondChoice] using hsecond2
      simpa [secondChoice, hq', hsecond2'] using hgain

theorem rum3_definition2_first2_gain_of_pairwise_gap
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    (hvalue : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hgap :
      pmfConditionalProb μ
          (fun τ => (2 : Candidate 1) = firstChoice τ)
          (fun τ => secondChoice τ = (0 : Candidate 1)) <
        rum3Lambda3 μ)
    (hfirst : 0 < firstChoiceProb μ (2 : Candidate 1)) :
    0 < pmfConditionalExp μ
      (fun τ => (2 : Candidate 1) = firstChoice τ)
      (fun τ =>
        pmfExp μ (fun π =>
          value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ))) := by
  classical
  let B : ℝ := AccuracyFamily.expectedBestAfterRemoval μ value (2 : Candidate 1)
  have hfirst' :
      0 < pmfProb μ (fun τ => (2 : Candidate 1) = firstChoice τ) := by
    simpa [firstChoiceProb] using hfirst
  rw [pmfConditionalExp_eq_conditionalProb_mul_add_one_sub_mul_of_forall_eq_if
    (μ := μ)
    (p := fun τ => (2 : Candidate 1) = firstChoice τ)
    (q := fun τ => secondChoice τ = (0 : Candidate 1))
    (f := fun τ =>
      pmfExp μ (fun π =>
        value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))
    (x := B - value (0 : Candidate 1))
    (y := B - value (1 : Candidate 1)) hfirst' ?_]
  · have hB :
        B =
          rum3Lambda3 μ * value (0 : Candidate 1) +
            (1 - rum3Lambda3 μ) * value (1 : Candidate 1) := by
      simpa [B] using expectedBestAfterRemoval_rum3_remove2 μ value
    let c : ℝ :=
      pmfConditionalProb μ
        (fun τ => (2 : Candidate 1) = firstChoice τ)
        (fun τ => secondChoice τ = (0 : Candidate 1))
    have hcalc :
        c * (B - value (0 : Candidate 1)) +
            (1 - c) * (B - value (1 : Candidate 1)) =
          (rum3Lambda3 μ - c) *
            (value (0 : Candidate 1) - value (1 : Candidate 1)) := by
      dsimp [c]
      rw [hB]
      ring
    rw [hcalc]
    exact mul_pos (sub_pos.mpr hgap) (sub_pos.mpr hvalue)
  · intro τ hτ
    have hbest :
        pmfExp μ (fun π =>
            value (bestRemainingAfter π (firstChoice τ))) = B := by
      unfold B AccuracyFamily.expectedBestAfterRemoval
      refine pmfExp_congr μ ?_
      intro π
      rw [← hτ]
    have hbest_apply :
        pmfExp μ (fun π =>
            value (bestRemainingAfter π (τ 0))) = B := by
      simpa [firstChoice] using hbest
    have hgain :
        pmfExp μ (fun π =>
            value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)) =
          B - value (secondChoice τ) := by
      rw [pmfExp_sub]
      simpa [firstChoice, hbest_apply]
    by_cases hq : secondChoice τ = (0 : Candidate 1)
    · have hq' : τ 1 = (0 : Candidate 1) := by
        simpa [secondChoice] using hq
      simpa [secondChoice, hq'] using hgain
    · have hfirstτ : firstChoice τ = (2 : Candidate 1) := hτ.symm
      have hsecond_ne2 : secondChoice τ ≠ (2 : Candidate 1) := by
        intro hsecond2
        exact (firstChoice_ne_secondChoice τ) (by rw [hfirstτ, hsecond2])
      have hsecond1 : secondChoice τ = (1 : Candidate 1) := by
        apply Fin.ext
        change (secondChoice τ).val = 1
        have hval0 : (secondChoice τ).val ≠ 0 := by
          intro hv
          exact hq (Fin.ext hv)
        have hval2 : (secondChoice τ).val ≠ 2 := by
          intro hv
          exact hsecond_ne2 (Fin.ext hv)
        have hlt := (secondChoice τ).isLt
        omega
      have hq' : τ 1 ≠ (0 : Candidate 1) := by
        simpa [secondChoice] using hq
      have hsecond1' : τ 1 = (1 : Candidate 1) := by
        simpa [secondChoice] using hsecond1
      simpa [secondChoice, hq', hsecond1'] using hgain

theorem rum3Definition2PairwiseGapCertificate_of_negativeCorrelationCertificate
    {μ : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (cert : RUM3Definition2NegativeCorrelationCertificate μ value) :
    RUM3Definition2PairwiseGapCertificate μ value where
  value01 := cert.value01
  value12 := cert.value12
  first0_second1_lt_lambda1 := by
    calc
      pmfConditionalProb μ
          (fun τ => (0 : Candidate 1) = firstChoice τ)
          (fun τ => secondChoice τ = (1 : Candidate 1)) =
        pmfConditionalProb μ
          (fun τ => (0 : Candidate 1) = firstChoice τ)
          (fun τ => bestRemainingAfter τ (0 : Candidate 1) = (1 : Candidate 1)) := by
          refine pmfConditionalProb_congr_of_condition μ
            (fun τ => (0 : Candidate 1) = firstChoice τ)
            (fun τ => secondChoice τ = (1 : Candidate 1))
            (fun τ => bestRemainingAfter τ (0 : Candidate 1) = (1 : Candidate 1)) ?_
          intro τ hτ
          have hbest : bestRemainingAfter τ (0 : Candidate 1) = secondChoice τ := by
            rw [hτ, bestRemainingAfter_of_eq]
          constructor
          · intro hsecond
            change secondChoice τ = (1 : Candidate 1) at hsecond
            rw [hbest, hsecond]
          · intro hbest1
            change bestRemainingAfter τ (0 : Candidate 1) = (1 : Candidate 1) at hbest1
            rwa [hbest] at hbest1
      _ < pmfProb μ
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1)) :=
        cert.first0_best1_cond_lt_uncond
      _ = rum3Lambda1 μ := rfl
  first1_second0_lt_lambda2 := by
    calc
      pmfConditionalProb μ
          (fun τ => (1 : Candidate 1) = firstChoice τ)
          (fun τ => secondChoice τ = (0 : Candidate 1)) =
        pmfConditionalProb μ
          (fun τ => (1 : Candidate 1) = firstChoice τ)
          (fun τ => bestRemainingAfter τ (1 : Candidate 1) = (0 : Candidate 1)) := by
          refine pmfConditionalProb_congr_of_condition μ
            (fun τ => (1 : Candidate 1) = firstChoice τ)
            (fun τ => secondChoice τ = (0 : Candidate 1))
            (fun τ => bestRemainingAfter τ (1 : Candidate 1) = (0 : Candidate 1)) ?_
          intro τ hτ
          have hbest : bestRemainingAfter τ (1 : Candidate 1) = secondChoice τ := by
            rw [hτ, bestRemainingAfter_of_eq]
          constructor
          · intro hsecond
            change secondChoice τ = (0 : Candidate 1) at hsecond
            rw [hbest, hsecond]
          · intro hbest0
            change bestRemainingAfter τ (1 : Candidate 1) = (0 : Candidate 1) at hbest0
            rwa [hbest] at hbest0
      _ < pmfProb μ
          (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1)) :=
        cert.first1_best0_cond_lt_uncond
      _ = rum3Lambda2 μ := rfl
  first2_second0_lt_lambda3 := by
    calc
      pmfConditionalProb μ
          (fun τ => (2 : Candidate 1) = firstChoice τ)
          (fun τ => secondChoice τ = (0 : Candidate 1)) =
        pmfConditionalProb μ
          (fun τ => (2 : Candidate 1) = firstChoice τ)
          (fun τ => bestRemainingAfter τ (2 : Candidate 1) = (0 : Candidate 1)) := by
          refine pmfConditionalProb_congr_of_condition μ
            (fun τ => (2 : Candidate 1) = firstChoice τ)
            (fun τ => secondChoice τ = (0 : Candidate 1))
            (fun τ => bestRemainingAfter τ (2 : Candidate 1) = (0 : Candidate 1)) ?_
          intro τ hτ
          have hbest : bestRemainingAfter τ (2 : Candidate 1) = secondChoice τ := by
            rw [hτ, bestRemainingAfter_of_eq]
          constructor
          · intro hsecond
            change secondChoice τ = (0 : Candidate 1) at hsecond
            rw [hbest, hsecond]
          · intro hbest0
            change bestRemainingAfter τ (2 : Candidate 1) = (0 : Candidate 1) at hbest0
            rwa [hbest] at hbest0
      _ < pmfProb μ
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1)) :=
        cert.first2_best0_cond_lt_uncond
      _ = rum3Lambda3 μ := rfl

theorem rum3Definition2Certificate_of_pairwiseGapCertificate
    {μ : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (cert : RUM3Definition2PairwiseGapCertificate μ value) :
    RUM3Definition2Certificate μ value where
  first0_gain := by
    intro hfirst
    exact rum3_definition2_first0_gain_of_pairwise_gap
      μ value cert.value12 cert.first0_second1_lt_lambda1 hfirst
  first1_gain := by
    intro hfirst
    exact rum3_definition2_first1_gain_of_pairwise_gap
      μ value (lt_trans cert.value12 cert.value01)
      cert.first1_second0_lt_lambda2 hfirst
  first2_gain := by
    intro hfirst
    exact rum3_definition2_first2_gain_of_pairwise_gap
      μ value cert.value01 cert.first2_second0_lt_lambda3 hfirst

theorem rum3_prefersIndependentReranking_of_pairwiseGapCertificate
    {μ : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (cert : RUM3Definition2PairwiseGapCertificate μ value) :
    Model.PrefersIndependentReranking μ value :=
  rum3_prefersIndependentReranking_of_definition2Certificate
    (rum3Definition2Certificate_of_pairwiseGapCertificate cert)

theorem rum3_prefersIndependentReranking_of_negativeCorrelationCertificate
    {μ : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (cert : RUM3Definition2NegativeCorrelationCertificate μ value) :
    Model.PrefersIndependentReranking μ value :=
  rum3_prefersIndependentReranking_of_pairwiseGapCertificate
    (rum3Definition2PairwiseGapCertificate_of_negativeCorrelationCertificate cert)

/-- Removal of `x₁`: increasing the probability of choosing `x₂` weakly
increases best-after-removal value when `x₂` is at least as valuable as `x₃`. -/
theorem expectedBestAfterRemoval_rum3_remove0_le_of_lambda1_le
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (hvalue : value (2 : Candidate 1) ≤ value (1 : Candidate 1))
    (hlambda : rum3Lambda1 μWorse ≤ rum3Lambda1 μBetter) :
    AccuracyFamily.expectedBestAfterRemoval μWorse value (0 : Candidate 1) ≤
      AccuracyFamily.expectedBestAfterRemoval μBetter value (0 : Candidate 1) := by
  rw [expectedBestAfterRemoval_rum3_remove0]
  rw [expectedBestAfterRemoval_rum3_remove0]
  nlinarith

/-- Removal of `x₂`: increasing the probability of choosing `x₁` weakly
increases best-after-removal value when `x₁` is at least as valuable as `x₃`. -/
theorem expectedBestAfterRemoval_rum3_remove1_le_of_lambda2_le
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (hvalue : value (2 : Candidate 1) ≤ value (0 : Candidate 1))
    (hlambda : rum3Lambda2 μWorse ≤ rum3Lambda2 μBetter) :
    AccuracyFamily.expectedBestAfterRemoval μWorse value (1 : Candidate 1) ≤
      AccuracyFamily.expectedBestAfterRemoval μBetter value (1 : Candidate 1) := by
  rw [expectedBestAfterRemoval_rum3_remove1]
  rw [expectedBestAfterRemoval_rum3_remove1]
  nlinarith

/-- Removal of `x₃`: increasing the probability of choosing `x₁` weakly
increases best-after-removal value when `x₁` is at least as valuable as `x₂`. -/
theorem expectedBestAfterRemoval_rum3_remove2_le_of_lambda3_le
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (hvalue : value (1 : Candidate 1) ≤ value (0 : Candidate 1))
    (hlambda : rum3Lambda3 μWorse ≤ rum3Lambda3 μBetter) :
    AccuracyFamily.expectedBestAfterRemoval μWorse value (2 : Candidate 1) ≤
      AccuracyFamily.expectedBestAfterRemoval μBetter value (2 : Candidate 1) := by
  rw [expectedBestAfterRemoval_rum3_remove2]
  rw [expectedBestAfterRemoval_rum3_remove2]
  nlinarith

theorem rum3Lambda1_le_of_remove0_coupling
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μBetter μWorse : PMF (Ranking 1)} (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter :
      rum3Lambda1 μBetter =
        pmfProb ν
          (fun ω => bestRemainingAfter (better ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hworse :
      rum3Lambda1 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (himp : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (better ω) (0 : Candidate 1) = (1 : Candidate 1)) :
    rum3Lambda1 μWorse ≤ rum3Lambda1 μBetter := by
  rw [hworse, hbetter]
  exact pmfProb_le_of_imp ν
    (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
      (1 : Candidate 1))
    (fun ω => bestRemainingAfter (better ω) (0 : Candidate 1) =
      (1 : Candidate 1))
    himp

theorem rum3Lambda2_le_of_remove1_coupling
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μBetter μWorse : PMF (Ranking 1)} (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter :
      rum3Lambda2 μBetter =
        pmfProb ν
          (fun ω => bestRemainingAfter (better ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hworse :
      rum3Lambda2 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (himp : ∀ ω,
      bestRemainingAfter (worse ω) (1 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (better ω) (1 : Candidate 1) = (0 : Candidate 1)) :
    rum3Lambda2 μWorse ≤ rum3Lambda2 μBetter := by
  rw [hworse, hbetter]
  exact pmfProb_le_of_imp ν
    (fun ω => bestRemainingAfter (worse ω) (1 : Candidate 1) =
      (0 : Candidate 1))
    (fun ω => bestRemainingAfter (better ω) (1 : Candidate 1) =
      (0 : Candidate 1))
    himp

theorem rum3Lambda3_le_of_remove2_coupling
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μBetter μWorse : PMF (Ranking 1)} (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter :
      rum3Lambda3 μBetter =
        pmfProb ν
          (fun ω => bestRemainingAfter (better ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hworse :
      rum3Lambda3 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (himp : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (better ω) (2 : Candidate 1) = (0 : Candidate 1)) :
    rum3Lambda3 μWorse ≤ rum3Lambda3 μBetter := by
  rw [hworse, hbetter]
  exact pmfProb_le_of_imp ν
    (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
      (0 : Candidate 1))
    (fun ω => bestRemainingAfter (better ω) (2 : Candidate 1) =
      (0 : Candidate 1))
    himp

theorem rum3Lambda1_le_of_remove0_measure_coupling
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    (himp : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (better ω) (0 : Candidate 1) = (1 : Candidate 1)) :
    rum3Lambda1 (rumRankingPMFOfMeasure μ worse hworse) ≤
      rum3Lambda1 (rumRankingPMFOfMeasure μ better hbetter) := by
  rw [rum3Lambda1_rumRankingPMFOfMeasure,
    rum3Lambda1_rumRankingPMFOfMeasure]
  exact measureProb_mono μ
    (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
      (1 : Candidate 1))
    (fun ω => bestRemainingAfter (better ω) (0 : Candidate 1) =
      (1 : Candidate 1))
    himp

theorem rum3Lambda2_le_of_remove1_measure_coupling
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    (himp : ∀ ω,
      bestRemainingAfter (worse ω) (1 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (better ω) (1 : Candidate 1) = (0 : Candidate 1)) :
    rum3Lambda2 (rumRankingPMFOfMeasure μ worse hworse) ≤
      rum3Lambda2 (rumRankingPMFOfMeasure μ better hbetter) := by
  rw [rum3Lambda2_rumRankingPMFOfMeasure,
    rum3Lambda2_rumRankingPMFOfMeasure]
  exact measureProb_mono μ
    (fun ω => bestRemainingAfter (worse ω) (1 : Candidate 1) =
      (0 : Candidate 1))
    (fun ω => bestRemainingAfter (better ω) (1 : Candidate 1) =
      (0 : Candidate 1))
    himp

theorem rum3Lambda3_le_of_remove2_measure_coupling
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    (himp : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (better ω) (2 : Candidate 1) = (0 : Candidate 1)) :
    rum3Lambda3 (rumRankingPMFOfMeasure μ worse hworse) ≤
      rum3Lambda3 (rumRankingPMFOfMeasure μ better hbetter) := by
  rw [rum3Lambda3_rumRankingPMFOfMeasure,
    rum3Lambda3_rumRankingPMFOfMeasure]
  exact measureProb_mono μ
    (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
      (0 : Candidate 1))
    (fun ω => bestRemainingAfter (better ω) (2 : Candidate 1) =
      (0 : Candidate 1))
    himp

theorem rum3_remove0_high_preserved_of_contract
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx23 : x3 < x2)
    (h :
      bestRemainingAfter (rum3RankByScores r1 r2 r3) (0 : Candidate 1) =
        (1 : Candidate 1)) :
    bestRemainingAfter
        (rum3RankByScores
          (rumContractScore t x1 r1)
          (rumContractScore t x2 r2)
          (rumContractScore t x3 r3))
        (0 : Candidate 1) = (1 : Candidate 1) := by
  have hr32 : r3 ≤ r2 := rum3RankByScores_remove0_eq1_imp_score23 h
  exact rum3RankByScores_remove0_eq1_of_score32
    (rumContractScore_preserves_weak_order ht0 ht1 (le_of_lt hx23) hr32)

theorem rum3_remove1_high_preserved_of_contract
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx13 : x3 < x1)
    (h :
      bestRemainingAfter (rum3RankByScores r1 r2 r3) (1 : Candidate 1) =
        (0 : Candidate 1)) :
    bestRemainingAfter
        (rum3RankByScores
          (rumContractScore t x1 r1)
          (rumContractScore t x2 r2)
          (rumContractScore t x3 r3))
        (1 : Candidate 1) = (0 : Candidate 1) := by
  have hr31 : r3 ≤ r1 := by
    by_contra hnot
    have hnot' : ¬ r3 ≤ r1 := hnot
    simp [hnot'] at h
  exact rum3RankByScores_remove1_eq0_of_score31
    (rumContractScore_preserves_weak_order ht0 ht1 (le_of_lt hx13) hr31)

theorem rum3_remove2_high_preserved_of_contract
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx12 : x2 < x1)
    (h :
      bestRemainingAfter (rum3RankByScores r1 r2 r3) (2 : Candidate 1) =
        (0 : Candidate 1)) :
    bestRemainingAfter
        (rum3RankByScores
          (rumContractScore t x1 r1)
          (rumContractScore t x2 r2)
          (rumContractScore t x3 r3))
        (2 : Candidate 1) = (0 : Candidate 1) := by
  have hr21 : r2 ≤ r1 := by
    by_contra hnot
    have hnot' : ¬ r2 ≤ r1 := hnot
    simp [hnot'] at h
  exact rum3RankByScores_remove2_eq0_of_score21
    (rumContractScore_preserves_weak_order ht0 ht1 (le_of_lt hx12) hr21)

/--
Definition 1 finite-removal monotonicity from a delta certificate plus explicit
couplings for the three singleton-removal subproblems.
-/
theorem rum3_theorem1RemovalMonotonicityAt_of_delta_and_removal_couplings
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {F : AccuracyFamily 1} {θA θH : ℝ}
    {μBetter μWorse : PMF (Ranking 1)} {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1)
    (hdistA : F.dist θA = μBetter)
    (hdistH : F.dist θH = μWorse)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (delta : RUM3DeltaCertificate μBetter μWorse)
    (hbetter0 :
      rum3Lambda1 μBetter =
        pmfProb ν
          (fun ω => bestRemainingAfter (better ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hworse0 :
      rum3Lambda1 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (himp0 : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (better ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hbetter1 :
      rum3Lambda2 μBetter =
        pmfProb ν
          (fun ω => bestRemainingAfter (better ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hworse1 :
      rum3Lambda2 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (himp1 : ∀ ω,
      bestRemainingAfter (worse ω) (1 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (better ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hbetter2 :
      rum3Lambda3 μBetter =
        pmfProb ν
          (fun ω => bestRemainingAfter (better ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hworse2 :
      rum3Lambda3 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (himp2 : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (better ω) (2 : Candidate 1) = (0 : Candidate 1)) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F θA θH := by
  have hv23 : F.value (2 : Candidate 1) ≤ F.value (1 : Candidate 1) := by
    rw [hvalue2, hvalue3]
    exact le_of_lt hx23
  have hv13 : F.value (2 : Candidate 1) ≤ F.value (0 : Candidate 1) := by
    rw [hvalue1, hvalue3]
    exact le_of_lt (lt_trans hx23 hx12)
  have hv12 : F.value (1 : Candidate 1) ≤ F.value (0 : Candidate 1) := by
    rw [hvalue1, hvalue2]
    exact le_of_lt hx12
  exact rum3_theorem1RemovalMonotonicityAt_of_delta_and_bestRemaining
    hdistA hdistH hvalue1 hvalue2 hvalue3 hx12 hx23 delta
    (expectedBestAfterRemoval_rum3_remove0_le_of_lambda1_le
      hv23
      (rum3Lambda1_le_of_remove0_coupling
        ν better worse hbetter0 hworse0 himp0))
    (expectedBestAfterRemoval_rum3_remove1_le_of_lambda2_le
      hv13
      (rum3Lambda2_le_of_remove1_coupling
        ν better worse hbetter1 hworse1 himp1))
    (expectedBestAfterRemoval_rum3_remove2_le_of_lambda3_le
      hv12
      (rum3Lambda3_le_of_remove2_coupling
        ν better worse hbetter2 hworse2 himp2))

/--
Definition 1 finite-removal monotonicity from score contraction, after the
source model supplies the delta certificate and the three removal-event
pushforward identities.
-/
theorem rum3_theorem1RemovalMonotonicityAt_of_delta_and_score_contraction
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {F : AccuracyFamily 1} {θA θH : ℝ}
    {μBetter μWorse : PMF (Ranking 1)} {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1)
    (t : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hdistA : F.dist θA = μBetter)
    (hdistH : F.dist θH = μWorse)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (delta : RUM3DeltaCertificate μBetter μWorse)
    (hbetterRank : ∀ ω,
      better ω =
        rum3RankByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseRank : ∀ ω,
      worse ω = rum3RankByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetter0 :
      rum3Lambda1 μBetter =
        pmfProb ν
          (fun ω => bestRemainingAfter (better ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hworse0 :
      rum3Lambda1 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hbetter1 :
      rum3Lambda2 μBetter =
        pmfProb ν
          (fun ω => bestRemainingAfter (better ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hworse1 :
      rum3Lambda2 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hbetter2 :
      rum3Lambda3 μBetter =
        pmfProb ν
          (fun ω => bestRemainingAfter (better ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hworse2 :
      rum3Lambda3 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (0 : Candidate 1))) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F θA θH := by
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  refine rum3_theorem1RemovalMonotonicityAt_of_delta_and_removal_couplings
    ν better worse hdistA hdistH hvalue1 hvalue2 hvalue3 hx12 hx23
    delta hbetter0 hworse0 ?himp0 hbetter1 hworse1 ?himp1
    hbetter2 hworse2 ?himp2
  · intro ω h
    rw [hworseRank ω] at h
    rw [hbetterRank ω]
    exact rum3_remove0_high_preserved_of_contract ht0 ht1 hx23 h
  · intro ω h
    rw [hworseRank ω] at h
    rw [hbetterRank ω]
    exact rum3_remove1_high_preserved_of_contract ht0 ht1 hx13 h
  · intro ω h
    rw [hworseRank ω] at h
    rw [hbetterRank ω]
    exact rum3_remove2_high_preserved_of_contract ht0 ht1 hx12 h

/--
Continuous-measure version of the three-candidate RUM finite-removal
monotonicity wrapper.

The source measure is pushed forward through the contracted and original score
rankings.  The only probabilistic input left explicit is the first-choice delta
certificate; the singleton-removal weak inequalities are derived from the
score-contraction geometry and the induced-ranking PMF identities.
-/
theorem rum3_theorem1RemovalMonotonicityAt_of_measure_delta_and_score_contraction
    {Ω : Type*} [MeasurableSpace Ω]
    {F : AccuracyFamily 1} {θA θH : ℝ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    {x1 x2 x3 : ℝ}
    (t : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hdistA :
      F.dist θA = rumRankingPMFOfMeasure μ better hbetter)
    (hdistH :
      F.dist θH = rumRankingPMFOfMeasure μ worse hworse)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (delta :
      RUM3DeltaCertificate
        (rumRankingPMFOfMeasure μ better hbetter)
        (rumRankingPMFOfMeasure μ worse hworse))
    (hbetterRank : ∀ ω,
      better ω =
        rum3RankByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseRank : ∀ ω,
      worse ω = rum3RankByScores (r1 ω) (r2 ω) (r3 ω)) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F θA θH := by
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  have hv23 : F.value (2 : Candidate 1) ≤ F.value (1 : Candidate 1) := by
    rw [hvalue2, hvalue3]
    exact le_of_lt hx23
  have hv13 : F.value (2 : Candidate 1) ≤ F.value (0 : Candidate 1) := by
    rw [hvalue1, hvalue3]
    exact le_of_lt hx13
  have hv12 : F.value (1 : Candidate 1) ≤ F.value (0 : Candidate 1) := by
    rw [hvalue1, hvalue2]
    exact le_of_lt hx12
  refine rum3_theorem1RemovalMonotonicityAt_of_delta_and_bestRemaining
    hdistA hdistH hvalue1 hvalue2 hvalue3 hx12 hx23 delta ?hremove0
    ?hremove1 ?hremove2
  · refine expectedBestAfterRemoval_rum3_remove0_le_of_lambda1_le hv23 ?_
    refine rum3Lambda1_le_of_remove0_measure_coupling μ better worse hbetter hworse ?_
    intro ω h
    rw [hworseRank ω] at h
    rw [hbetterRank ω]
    exact rum3_remove0_high_preserved_of_contract ht0 ht1 hx23 h
  · refine expectedBestAfterRemoval_rum3_remove1_le_of_lambda2_le hv13 ?_
    refine rum3Lambda2_le_of_remove1_measure_coupling μ better worse hbetter hworse ?_
    intro ω h
    rw [hworseRank ω] at h
    rw [hbetterRank ω]
    exact rum3_remove1_high_preserved_of_contract ht0 ht1 hx13 h
  · refine expectedBestAfterRemoval_rum3_remove2_le_of_lambda3_le hv12 ?_
    refine rum3Lambda3_le_of_remove2_measure_coupling μ better worse hbetter hworse ?_
    intro ω h
    rw [hworseRank ω] at h
    rw [hbetterRank ω]
    exact rum3_remove2_high_preserved_of_contract ht0 ht1 hx12 h

theorem rum3_uMinus1_lt_uMinus2
    {x1 x2 x3 ell1 ell2 : ℝ}
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hell1_pos : 0 < ell1) (hell12 : ell1 < ell2) :
    rum3_uMinus1 ell1 x2 x3 < rum3_uMinus2 ell2 x1 x3 := by
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  have hx23_pos : 0 < x2 - x3 := sub_pos.mpr hx23
  have hx13_pos : 0 < x1 - x3 := sub_pos.mpr hx13
  have hx_gap : x2 - x3 < x1 - x3 := by linarith
  have hleft : ell1 * (x2 - x3) < ell1 * (x1 - x3) :=
    mul_lt_mul_of_pos_left hx_gap hell1_pos
  have hright : ell1 * (x1 - x3) < ell2 * (x1 - x3) :=
    mul_lt_mul_of_pos_right hell12 hx13_pos
  have hmain : ell1 * (x2 - x3) < ell2 * (x1 - x3) :=
    lt_trans hleft hright
  unfold rum3_uMinus1 rum3_uMinus2
  nlinarith

theorem rum3_uMinus1_lt_x2
    {x2 x3 ell1 : ℝ} (hx23 : x3 < x2) (hell1_lt_one : ell1 < 1) :
    rum3_uMinus1 ell1 x2 x3 < x2 := by
  have hcoef : 0 < 1 - ell1 := by linarith
  have hgap : x3 - x2 < 0 := by linarith
  have hprod : (1 - ell1) * (x3 - x2) < 0 :=
    mul_neg_of_pos_of_neg hcoef hgap
  unfold rum3_uMinus1
  nlinarith

theorem rum3_x2_lt_uMinus3
    {x1 x2 ell3 : ℝ} (hx12 : x2 < x1) (hell3_pos : 0 < ell3) :
    x2 < rum3_uMinus3 ell3 x1 x2 := by
  have hgap : 0 < x1 - x2 := sub_pos.mpr hx12
  have hprod : 0 < ell3 * (x1 - x2) := mul_pos hell3_pos hgap
  unfold rum3_uMinus3
  nlinarith

theorem rum3_uMinus2_le_x1
    {x1 x3 ell2 : ℝ} (hx31 : x3 ≤ x1) (hell2_le_one : ell2 ≤ 1) :
    rum3_uMinus2 ell2 x1 x3 ≤ x1 := by
  have hcoef : 0 ≤ 1 - ell2 := by linarith
  have hgap : x3 - x1 ≤ 0 := by linarith
  have hprod : (1 - ell2) * (x3 - x1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoef hgap
  unfold rum3_uMinus2
  nlinarith

theorem x1_add_x2_lt_two_mul_rum3_uMinus3
    {x1 x2 ell3 : ℝ} (hx12 : x2 < x1) (hell3_half : (1 : ℝ) / 2 < ell3) :
    x1 + x2 < 2 * rum3_uMinus3 ell3 x1 x2 := by
  have hcoef : 0 < 2 * ell3 - 1 := by linarith
  have hgap : 0 < x1 - x2 := sub_pos.mpr hx12
  have hprod : 0 < (2 * ell3 - 1) * (x1 - x2) := mul_pos hcoef hgap
  unfold rum3_uMinus3
  nlinarith

/--
The scalar algebra at the end of paper Theorem 6.

Here `dᵢ = Pr[τ₁ = xᵢ] - Pr[π₁ = xᵢ]`, and `uᵢ` is the human expected utility
when candidate `xᵢ` is unavailable.  The hypotheses are the paper's
`Δp₁ > 0`, `Δp₁ ≥ Δp₂`, `Δp₃ ≤ 0`, total-mass identity, and the three utility
comparisons derived in the proof.
-/
theorem rum3_delta_weighted_sum_neg
    {u1 u2 u3 d1 d2 d3 : ℝ}
    (hu12 : u1 < u2) (hu13 : u1 < u3) (hu_sum : u1 + u2 < 2 * u3)
    (hd1_pos : 0 < d1) (hd12 : d2 ≤ d1) (hd3_nonpos : d3 ≤ 0)
    (hd_sum : d1 + d2 + d3 = 0) :
    d1 * u1 + d2 * u2 + d3 * u3 < 0 := by
  by_cases hd2_nonpos : d2 ≤ 0
  · have hsome_neg : d2 < 0 ∨ d3 < 0 := by
      by_contra hnot
      have hd2_nonneg : 0 ≤ d2 := le_of_not_gt (fun h => hnot (Or.inl h))
      have hd3_nonneg : 0 ≤ d3 := le_of_not_gt (fun h => hnot (Or.inr h))
      nlinarith
    cases hsome_neg with
    | inl hd2_neg =>
        have h2 : d2 * u2 < d2 * u1 :=
          mul_lt_mul_of_neg_left hu12 hd2_neg
        have h3 : d3 * u3 ≤ d3 * u1 :=
          mul_le_mul_of_nonpos_left (le_of_lt hu13) hd3_nonpos
        calc
          d1 * u1 + d2 * u2 + d3 * u3
              < d1 * u1 + d2 * u1 + d3 * u1 := by linarith
          _ = (d1 + d2 + d3) * u1 := by ring
          _ = 0 := by rw [hd_sum]; ring
    | inr hd3_neg =>
        have h2 : d2 * u2 ≤ d2 * u1 :=
          mul_le_mul_of_nonpos_left (le_of_lt hu12) hd2_nonpos
        have h3 : d3 * u3 < d3 * u1 :=
          mul_lt_mul_of_neg_left hu13 hd3_neg
        calc
          d1 * u1 + d2 * u2 + d3 * u3
              < d1 * u1 + d2 * u1 + d3 * u1 := by linarith
          _ = (d1 + d2 + d3) * u1 := by ring
          _ = 0 := by rw [hd_sum]; ring
  · have hd2_pos : 0 < d2 := lt_of_not_ge hd2_nonpos
    have hdiff_nonpos : u1 - u3 ≤ 0 := by linarith
    have hfirst :
        d1 * (u1 - u3) ≤ d2 * (u1 - u3) :=
      mul_le_mul_of_nonpos_right hd12 hdiff_nonpos
    have htail : d2 * (u1 + u2 - 2 * u3) < 0 := by
      have hsum_neg : u1 + u2 - 2 * u3 < 0 := by linarith
      exact mul_neg_of_pos_of_neg hd2_pos hsum_neg
    have hbound :
        d1 * u1 + d2 * u2 + d3 * u3 ≤
          d2 * (u1 + u2 - 2 * u3) := by
      have hd3_eq : d3 = -d1 - d2 := by linarith
      calc
        d1 * u1 + d2 * u2 + d3 * u3
            = d1 * (u1 - u3) + d2 * (u2 - u3) := by
                rw [hd3_eq]
                ring
        _ ≤ d2 * (u1 - u3) + d2 * (u2 - u3) := by linarith
        _ = d2 * (u1 + u2 - 2 * u3) := by ring
    exact lt_of_le_of_lt hbound htail

/--
Paper Theorem 6 payoff algebra after substituting the three `u_-i` formulas.

The remaining RUM-specific tasks are to derive the lambda and delta hypotheses
from the continuous random-utility model.  This theorem closes the final
finite-dimensional inequality once those hypotheses are available.
-/
theorem rum3_theorem6_payoff_algebra
    {x1 x2 x3 ell1 ell2 ell3 d1 d2 d3 : ℝ}
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hell1_half : (1 : ℝ) / 2 < ell1) (hell1_lt_one : ell1 < 1)
    (hell12 : ell1 < ell2) (hell2_le_one : ell2 ≤ 1)
    (hell3_half : (1 : ℝ) / 2 < ell3)
    (hd1_pos : 0 < d1) (hd12 : d2 ≤ d1) (hd3_nonpos : d3 ≤ 0)
    (hd_sum : d1 + d2 + d3 = 0) :
    d1 * rum3_uMinus1 ell1 x2 x3 +
        d2 * rum3_uMinus2 ell2 x1 x3 +
        d3 * rum3_uMinus3 ell3 x1 x2 < 0 := by
  have hell1_pos : 0 < ell1 := by nlinarith
  have hell3_pos : 0 < ell3 := by nlinarith
  have hx13_le : x3 ≤ x1 := le_of_lt (lt_trans hx23 hx12)
  have hu12 :
      rum3_uMinus1 ell1 x2 x3 < rum3_uMinus2 ell2 x1 x3 :=
    rum3_uMinus1_lt_uMinus2 hx12 hx23 hell1_pos hell12
  have hu1_x2 : rum3_uMinus1 ell1 x2 x3 < x2 :=
    rum3_uMinus1_lt_x2 hx23 hell1_lt_one
  have hx2_u3 : x2 < rum3_uMinus3 ell3 x1 x2 :=
    rum3_x2_lt_uMinus3 hx12 hell3_pos
  have hu13 :
      rum3_uMinus1 ell1 x2 x3 < rum3_uMinus3 ell3 x1 x2 :=
    lt_trans hu1_x2 hx2_u3
  have hu2_x1 : rum3_uMinus2 ell2 x1 x3 ≤ x1 :=
    rum3_uMinus2_le_x1 hx13_le hell2_le_one
  have hxsum_u3 : x1 + x2 < 2 * rum3_uMinus3 ell3 x1 x2 :=
    x1_add_x2_lt_two_mul_rum3_uMinus3 hx12 hell3_half
  have hu_sum :
      rum3_uMinus1 ell1 x2 x3 + rum3_uMinus2 ell2 x1 x3 <
        2 * rum3_uMinus3 ell3 x1 x2 := by
    nlinarith
  exact rum3_delta_weighted_sum_neg
    hu12 hu13 hu_sum hd1_pos hd12 hd3_nonpos hd_sum

/--
Three-candidate RUM weaker-competition bridge in model notation.

This turns the scalar Theorem 6 algebra into the utility predicate from
Definition 3.  The first-choice delta hypotheses are stated directly in terms of
the better and worse first-mover ranking laws; their total-mass identity is
derived from `sum_firstChoiceProb_eq_one`.
-/
theorem rum3_prefersWeakerCompetition_of_payoff_algebra
    (μBetter μWorse : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    {x1 x2 x3 ell1 ell2 ell3 : ℝ}
    (hbest1 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (0 : Candidate 1) =
        rum3_uMinus1 ell1 x2 x3)
    (hbest2 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (1 : Candidate 1) =
        rum3_uMinus2 ell2 x1 x3)
    (hbest3 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (2 : Candidate 1) =
        rum3_uMinus3 ell3 x1 x2)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hell1_half : (1 : ℝ) / 2 < ell1) (hell1_lt_one : ell1 < 1)
    (hell12 : ell1 < ell2) (hell2_le_one : ell2 ≤ 1)
    (hell3_half : (1 : ℝ) / 2 < ell3)
    (hd1_pos :
      0 <
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd12 :
      firstChoiceProb μBetter (1 : Candidate 1) -
          firstChoiceProb μWorse (1 : Candidate 1) ≤
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd3_nonpos :
      firstChoiceProb μBetter (2 : Candidate 1) -
          firstChoiceProb μWorse (2 : Candidate 1) ≤ 0) :
    Model.PrefersWeakerCompetition μBetter μWorse value := by
  classical
  let d1 : ℝ :=
    firstChoiceProb μBetter (0 : Candidate 1) -
      firstChoiceProb μWorse (0 : Candidate 1)
  let d2 : ℝ :=
    firstChoiceProb μBetter (1 : Candidate 1) -
      firstChoiceProb μWorse (1 : Candidate 1)
  let d3 : ℝ :=
    firstChoiceProb μBetter (2 : Candidate 1) -
      firstChoiceProb μWorse (2 : Candidate 1)
  have hbetter_sum :
      firstChoiceProb μBetter (0 : Candidate 1) +
          firstChoiceProb μBetter (1 : Candidate 1) +
          firstChoiceProb μBetter (2 : Candidate 1) = 1 := by
    have hsum := sum_firstChoiceProb_eq_one (μ := μBetter) (n := 1)
    change (∑ c : Fin 3, firstChoiceProb μBetter c) = 1 at hsum
    rw [Fin.sum_univ_three] at hsum
    exact hsum
  have hworse_sum :
      firstChoiceProb μWorse (0 : Candidate 1) +
          firstChoiceProb μWorse (1 : Candidate 1) +
          firstChoiceProb μWorse (2 : Candidate 1) = 1 := by
    have hsum := sum_firstChoiceProb_eq_one (μ := μWorse) (n := 1)
    change (∑ c : Fin 3, firstChoiceProb μWorse c) = 1 at hsum
    rw [Fin.sum_univ_three] at hsum
    exact hsum
  have hd_sum : d1 + d2 + d3 = 0 := by
    dsimp [d1, d2, d3]
    nlinarith
  have hneg :
      d1 * rum3_uMinus1 ell1 x2 x3 +
          d2 * rum3_uMinus2 ell2 x1 x3 +
          d3 * rum3_uMinus3 ell3 x1 x2 < 0 :=
    rum3_theorem6_payoff_algebra
      hx12 hx23 hell1_half hell1_lt_one hell12 hell2_le_one hell3_half
      (by simpa [d1] using hd1_pos)
      (by simpa [d1, d2] using hd12)
      (by simpa [d3] using hd3_nonpos)
      hd_sum
  have hdiff :
      expectedSecondMoverIndependent μWorse μBetter value -
          expectedSecondMoverIndependent μWorse μWorse value =
        d1 * rum3_uMinus1 ell1 x2 x3 +
          d2 * rum3_uMinus2 ell2 x1 x3 +
          d3 * rum3_uMinus3 ell3 x1 x2 := by
    rw [AccuracyFamily.expectedSecondMoverIndependent_sub_eq_sum_firstChoiceProb_sub_mul_bestAfterRemoval]
    change
      (∑ c : Fin 3,
        (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
          AccuracyFamily.expectedBestAfterRemoval μWorse value c) =
        d1 * rum3_uMinus1 ell1 x2 x3 +
          d2 * rum3_uMinus2 ell2 x1 x3 +
          d3 * rum3_uMinus3 ell3 x1 x2
    rw [Fin.sum_univ_three]
    simp [d1, d2, d3, hbest1, hbest2, hbest3]
  unfold Model.PrefersWeakerCompetition
    AppliedModelingLib.SocialChoice.Ranking.PrefersWeakerCompetition
  have hsub : expectedSecondMoverIndependent μWorse μBetter value -
      expectedSecondMoverIndependent μWorse μWorse value < 0 := by
    rw [hdiff]
    exact hneg
  linarith

/--
Three-candidate RUM weaker-competition bridge with the `u_-i` formulas derived
from the human ranking law itself.

The remaining assumptions are exactly the upstream RUM probability facts from
the paper: value ordering, `λ₁ > 1/2`, `λ₁ < 1`, `λ₂ > λ₁`, `λ₃ > 1/2`, and
the first-choice delta inequalities.
-/
theorem rum3_prefersWeakerCompetition
    (μBetter μWorse : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hlam1_half : (1 : ℝ) / 2 < rum3Lambda1 μWorse)
    (hlam1_lt_one : rum3Lambda1 μWorse < 1)
    (hlam12 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (hlam3_half : (1 : ℝ) / 2 < rum3Lambda3 μWorse)
    (hd1_pos :
      0 <
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd12 :
      firstChoiceProb μBetter (1 : Candidate 1) -
          firstChoiceProb μWorse (1 : Candidate 1) ≤
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd3_nonpos :
      firstChoiceProb μBetter (2 : Candidate 1) -
          firstChoiceProb μWorse (2 : Candidate 1) ≤ 0) :
    Model.PrefersWeakerCompetition μBetter μWorse value := by
  have hbest1 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (0 : Candidate 1) =
        rum3_uMinus1 (rum3Lambda1 μWorse) x2 x3 := by
    rw [expectedBestAfterRemoval_rum3_remove0]
    simp [rum3_uMinus1, hvalue2, hvalue3]
  have hbest2 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (1 : Candidate 1) =
        rum3_uMinus2 (rum3Lambda2 μWorse) x1 x3 := by
    rw [expectedBestAfterRemoval_rum3_remove1]
    simp [rum3_uMinus2, hvalue1, hvalue3]
  have hbest3 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (2 : Candidate 1) =
        rum3_uMinus3 (rum3Lambda3 μWorse) x1 x2 := by
    rw [expectedBestAfterRemoval_rum3_remove2]
    simp [rum3_uMinus3, hvalue1, hvalue2]
  exact rum3_prefersWeakerCompetition_of_payoff_algebra
    μBetter μWorse value
    hbest1 hbest2 hbest3
    hx12 hx23 hlam1_half hlam1_lt_one hlam12
    (pmfProb_le_one μWorse
      (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1)))
    hlam3_half hd1_pos hd12 hd3_nonpos

/-- Appendix C / Theorem 6 from its named finite certificate. -/
theorem rum3_prefersWeakerCompetition_of_certificate
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (cert : RUM3Theorem6Certificate μBetter μWorse value x1 x2 x3) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  rum3_prefersWeakerCompetition
    μBetter μWorse value
    cert.value_first cert.value_second cert.value_third
    cert.value12 cert.value23
    cert.lambda1_half cert.lambda1_lt_one cert.lambda12 cert.lambda3_half
    cert.delta_top_pos cert.delta_middle_le_top cert.delta_bottom_nonpos

end KR21Monoculture
