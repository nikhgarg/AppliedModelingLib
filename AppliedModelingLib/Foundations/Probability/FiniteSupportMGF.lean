import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Tactic

open scoped BigOperators Topology
open Filter

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-!
# Finite-Support Moment Generating Functions

Reusable log-MGF and Legendre-transform scaffolding for finite rating-scale
and finite signal laws.  This is the algebraic surface used by large-deviation
arguments in rating-system papers; the deep analytic large-deviation theorem is
kept in `LargeDeviations.lean` as a certificate boundary.

## Main declarations

- `finiteMGF`
- `finiteLogMGF`
- `finiteLegendreValue`
- `finiteRateFunction`
- `finiteRateFunctionTop`
- `withTopRealScale`
- `finiteChernoffRate`
- `FiniteScoreGapLDPModel`
- `FiniteRatingLDPModel`
- `FiniteRatingLDPModel.rateFunctionTop`
- `FiniteRatingLDPModel.pairwiseRateObjectiveTop`
- `FiniteRatingLDPModel.pairwiseThresholdRateTop`
- `bernoulliKL`
-/

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
A differentiable convex real function with derivative zero at `z0` has a
global minimum at `z0`.
-/
theorem global_min_of_convex_hasDerivAt_zero
    {f : ℝ → ℝ} {z0 : ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hf : HasDerivAt f 0 z0) :
    ∀ z : ℝ, f z0 ≤ f z := by
  intro z
  rcases lt_trichotomy z z0 with hlt | heq | hgt
  · have hslope : slope f z z0 ≤ 0 := by
      simpa [hf.deriv] using
        (hconv.slope_le_deriv (Set.mem_univ z) (Set.mem_univ z0) hlt
          hf.differentiableAt)
    exact (slope_nonpos_iff_of_le (f := f) hlt.le).mp hslope
  · subst z
    exact le_rfl
  · have hslope : 0 ≤ slope f z0 z := by
      simpa [hf.deriv] using
        (hconv.deriv_le_slope (Set.mem_univ z0) (Set.mem_univ z) hgt
          hf.differentiableAt)
    exact (slope_nonneg_iff_of_le (f := f) hgt.le).mp hslope

/--
Supporting-line inequality for a differentiable convex real function.

If `f` is convex and has derivative `a` at `z0`, then the tangent line at
`z0` lies below `f` everywhere.
-/
theorem convex_tangent_le_of_hasDerivAt
    {f : ℝ → ℝ} {a z0 : ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hf : HasDerivAt f a z0) :
    ∀ z : ℝ, f z0 + a * (z - z0) ≤ f z := by
  intro z
  rcases lt_trichotomy z z0 with hlt | heq | hgt
  · have hslope : slope f z z0 ≤ a :=
      hconv.slope_le_of_hasDerivAt
        (Set.mem_univ z) (Set.mem_univ z0) hlt hf
    have hden_pos : 0 < z0 - z := sub_pos.mpr hlt
    have hslope' : (f z0 - f z) / (z0 - z) ≤ a := by
      simpa [slope_def_field] using hslope
    have hmul : f z0 - f z ≤ a * (z0 - z) :=
      (div_le_iff₀ hden_pos).mp hslope'
    linarith
  · subst z
    simp
  · have hslope : a ≤ slope f z0 z :=
      hconv.le_slope_of_hasDerivAt
        (Set.mem_univ z0) (Set.mem_univ z) hgt hf
    have hden_pos : 0 < z - z0 := sub_pos.mpr hgt
    have hslope' : a ≤ (f z - f z0) / (z - z0) := by
      simpa [slope_def_field] using hslope
    have hmul : a * (z - z0) ≤ f z - f z0 :=
      (le_div_iff₀ hden_pos).mp hslope'
    linarith

/-- Derivatives of a differentiable convex real function are monotone. -/
theorem convex_hasDerivAt_mono_of_le
    {f : ℝ → ℝ} {x y dx dy : ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hxy : x ≤ y)
    (hx : HasDerivAt f dx x)
    (hy : HasDerivAt f dy y) :
    dx ≤ dy := by
  rcases lt_or_eq_of_le hxy with hlt | rfl
  · have htx := convex_tangent_le_of_hasDerivAt hconv hx y
    have hty := convex_tangent_le_of_hasDerivAt hconv hy x
    have hpos : 0 < y - x := sub_pos.mpr hlt
    nlinarith
  · exact le_of_eq (hx.unique hy)

theorem exists_pmf_toReal_pos (μ : PMF α) :
    ∃ a : α, 0 < (μ a).toReal := by
  by_contra h
  have hzero : ∀ a : α, (μ a).toReal = 0 := by
    intro a
    have hnot : ¬ 0 < (μ a).toReal := by
      intro ha
      exact h ⟨a, ha⟩
    exact le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
  have hsum := pmfToRealSum μ
  have hsum_zero : ∑ a : α, (μ a).toReal = 0 := by
    simp [hzero]
  linarith

/-- Finite moment-generating function for a real score under a finite PMF. -/
def finiteMGF (μ : PMF α) (score : α → ℝ) (z : ℝ) : ℝ :=
  ∑ a : α, (μ a).toReal * Real.exp (z * score a)

/-- The finite moment-generating function is continuous in its dual parameter. -/
theorem finiteMGF_continuous (μ : PMF α) (score : α → ℝ) :
    Continuous (fun z : ℝ => finiteMGF μ score z) := by
  unfold finiteMGF
  exact continuous_finset_sum Finset.univ (fun a _ =>
    continuous_const.mul
      (Real.continuous_exp.comp
        (continuous_id.mul continuous_const)))

theorem finiteMGF_pos (μ : PMF α) (score : α → ℝ) (z : ℝ) :
    0 < finiteMGF μ score z := by
  rcases exists_pmf_toReal_pos μ with ⟨a, ha⟩
  dsimp [finiteMGF]
  exact Finset.sum_pos' (by
    intro b _
    exact mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) (by
    exact ⟨a, Finset.mem_univ a, mul_pos ha (Real.exp_pos _)⟩)

theorem finiteMGF_nonneg (μ : PMF α) (score : α → ℝ) (z : ℝ) :
    0 ≤ finiteMGF μ score z :=
  (finiteMGF_pos μ score z).le

/-- A single atom's MGF contribution lower-bounds the full finite MGF. -/
theorem finiteMGF_ge_atom
    (μ : PMF α) (score : α → ℝ) (z : ℝ) (a : α) :
    (μ a).toReal * Real.exp (z * score a) ≤ finiteMGF μ score z := by
  unfold finiteMGF
  exact
    Finset.single_le_sum
      (f := fun b : α => (μ b).toReal * Real.exp (z * score b))
      (fun b _hb =>
        mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
      (Finset.mem_univ a)

theorem finiteMGF_zero (μ : PMF α) (score : α → ℝ) :
    finiteMGF μ score 0 = 1 := by
  dsimp [finiteMGF]
  simpa using pmfToRealSum μ

/--
Finite-MGF tangent lower bound at zero: `exp x >= 1 + x`, averaged under the
finite PMF.
-/
theorem one_add_mul_pmfExp_le_finiteMGF
    (μ : PMF α) (score : α → ℝ) (z : ℝ) :
    1 + z * pmfExp μ score ≤ finiteMGF μ score z := by
  unfold finiteMGF pmfExp
  have hsum_eq :
      (∑ a : α, (μ a).toReal * (1 + z * score a)) =
        1 + z * (∑ a : α, (μ a).toReal * score a) := by
    calc
      ∑ a : α, (μ a).toReal * (1 + z * score a)
          =
          ∑ a : α,
            ((μ a).toReal + z * ((μ a).toReal * score a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            ring
      _ =
          (∑ a : α, (μ a).toReal) +
            ∑ a : α, z * ((μ a).toReal * score a) := by
            rw [Finset.sum_add_distrib]
      _ =
          (∑ a : α, (μ a).toReal) +
            z * (∑ a : α, (μ a).toReal * score a) := by
            rw [Finset.mul_sum]
      _ =
          1 + z * (∑ a : α, (μ a).toReal * score a) := by
            rw [pmfToRealSum μ]
  calc
    1 + z * (∑ a : α, (μ a).toReal * score a)
        =
        ∑ a : α, (μ a).toReal * (1 + z * score a) := by
          exact hsum_eq.symm
    _ ≤ ∑ a : α, (μ a).toReal * Real.exp (z * score a) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact mul_le_mul_of_nonneg_left
            (by simpa [add_comm] using Real.add_one_le_exp (z * score a))
            ENNReal.toReal_nonneg

theorem finiteMGF_hasDerivAt_zero (μ : PMF α) (score : α → ℝ) :
    HasDerivAt (fun z : ℝ => finiteMGF μ score z) (pmfExp μ score) 0 := by
  classical
  unfold finiteMGF pmfExp
  have hterm : ∀ a : α,
      HasDerivAt (fun z : ℝ => (μ a).toReal * Real.exp (z * score a))
        ((μ a).toReal * score a) 0 := by
    intro a
    have hlin : HasDerivAt (fun z : ℝ => z * score a) (score a) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (score a)
    have hexp :
        HasDerivAt (fun z : ℝ => Real.exp (z * score a)) (score a) 0 := by
      simpa using hlin.exp
    simpa [mul_assoc, mul_comm, mul_left_comm] using hexp.const_mul ((μ a).toReal)
  simpa using HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => hterm a)

/-- Derivative of the finite MGF at an arbitrary dual parameter. -/
theorem finiteMGF_hasDerivAt (μ : PMF α) (score : α → ℝ) (z0 : ℝ) :
    HasDerivAt (fun z : ℝ => finiteMGF μ score z)
      (∑ a : α, (μ a).toReal * (score a * Real.exp (z0 * score a))) z0 := by
  classical
  unfold finiteMGF
  have hterm : ∀ a : α,
      HasDerivAt (fun z : ℝ => (μ a).toReal * Real.exp (z * score a))
        ((μ a).toReal * (score a * Real.exp (z0 * score a))) z0 := by
    intro a
    have hlin : HasDerivAt (fun z : ℝ => z * score a) (score a) z0 := by
      simpa using (hasDerivAt_id z0).mul_const (score a)
    have hexp :
        HasDerivAt (fun z : ℝ => Real.exp (z * score a))
          (score a * Real.exp (z0 * score a)) z0 := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hlin.exp
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      hexp.const_mul ((μ a).toReal)
  simpa using HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => hterm a)

theorem exists_left_lt_of_hasDerivAt_pos
    {f : ℝ → ℝ} {fderiv : ℝ}
    (hf : HasDerivAt f fderiv 0) (hpos : 0 < fderiv) :
    ∃ z : ℝ, z < 0 ∧ f z < f 0 := by
  have hslope : Tendsto (slope f 0) (𝓝[<] (0 : ℝ)) (𝓝 fderiv) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hf).1
  have hevent : ∀ᶠ z in 𝓝[<] (0 : ℝ), 0 < slope f 0 z :=
    hslope.eventually_const_lt hpos
  have hleft : ∀ᶠ z in 𝓝[<] (0 : ℝ), z < 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz
  rcases (hevent.and hleft).exists with ⟨z, hsl, hz⟩
  exact ⟨z, hz, (slope_pos_iff_gt (f := f) (x₀ := 0) hz).mp hsl⟩

theorem exists_neg_finiteMGF_lt_one_of_pmfExp_pos
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 < pmfExp μ score) :
    ∃ z : ℝ, z < 0 ∧ finiteMGF μ score z < 1 := by
  rcases exists_left_lt_of_hasDerivAt_pos
      (finiteMGF_hasDerivAt_zero μ score) hmean with
    ⟨z, hz, hlt⟩
  exact ⟨z, hz, by simpa [finiteMGF_zero] using hlt⟩

/-- Finite log moment-generating function. -/
def finiteLogMGF (μ : PMF α) (score : α → ℝ) (z : ℝ) : ℝ :=
  Real.log (finiteMGF μ score z)

/-- The finite log-MGF is continuous in its dual parameter. -/
theorem finiteLogMGF_continuous (μ : PMF α) (score : α → ℝ) :
    Continuous (fun z : ℝ => finiteLogMGF μ score z) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact
    (finiteMGF_continuous μ score).continuousAt.log
      (finiteMGF_pos μ score z).ne'

/-- Derivative of the finite log-MGF at an arbitrary dual parameter. -/
theorem finiteLogMGF_hasDerivAt (μ : PMF α) (score : α → ℝ) (z0 : ℝ) :
    HasDerivAt (fun z : ℝ => finiteLogMGF μ score z)
      ((∑ a : α,
          (μ a).toReal * (score a * Real.exp (z0 * score a))) /
        finiteMGF μ score z0) z0 := by
  unfold finiteLogMGF
  exact
    (finiteMGF_hasDerivAt μ score z0).log
      (finiteMGF_pos μ score z0).ne'

/-- Derivative of the finite log-MGF at zero is the ordinary expectation. -/
theorem finiteLogMGF_hasDerivAt_zero (μ : PMF α) (score : α → ℝ) :
    HasDerivAt (fun z : ℝ => finiteLogMGF μ score z)
      (pmfExp μ score) 0 := by
  have h := finiteLogMGF_hasDerivAt μ score 0
  simpa [finiteMGF_zero, pmfExp, mul_assoc, mul_comm, mul_left_comm] using h

/--
First-order finite log-MGF certificate: if the exponentially tilted weighted
score sum vanishes at `z0`, then the finite log-MGF derivative there is zero.
-/
theorem finiteLogMGF_hasDerivAt_zero_of_weighted_exp_score_sum_eq_zero
    (μ : PMF α) (score : α → ℝ) {z0 : ℝ}
    (hstationary :
      (∑ a : α,
        (μ a).toReal * (score a * Real.exp (z0 * score a))) = 0) :
    HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) 0 z0 := by
  simpa [hstationary] using finiteLogMGF_hasDerivAt μ score z0

/--
Conversely, a zero derivative of the finite log-MGF gives the expanded
stationary weighted-exponential score equation.
-/
theorem finiteLogMGF_weighted_exp_score_sum_eq_zero_of_hasDerivAt_zero
    (μ : PMF α) (score : α → ℝ) {z0 : ℝ}
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) 0 z0) :
    (∑ a : α,
      (μ a).toReal * (score a * Real.exp (z0 * score a))) = 0 := by
  have hformula := finiteLogMGF_hasDerivAt μ score z0
  have hquot_zero :
      (∑ a : α, (μ a).toReal * (score a * Real.exp (z0 * score a))) /
          finiteMGF μ score z0 = 0 :=
    hformula.unique hderiv
  have hmgf_ne : finiteMGF μ score z0 ≠ 0 :=
    (finiteMGF_pos μ score z0).ne'
  have hmul :=
    congrArg (fun x : ℝ => x * finiteMGF μ score z0) hquot_zero
  field_simp [hmgf_ne] at hmul
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

/--
Finite stationary tilt exists on the nonpositive dual half-line whenever the
score has nonnegative mean and has positive mass on both a strictly positive
and a strictly negative score.

The proof uses an elementary domination argument: on `z <= 0`, all
positive-score contributions are bounded by their value at zero, while one
negative atom can be made to dominate them by moving far enough left.
-/
theorem exists_nonpos_weighted_exp_score_sum_eq_zero_of_pmfExp_nonneg_pos_neg_atoms
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (_hmassPos : 0 < (μ aPos).toReal)
    (_hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0) :
    ∃ z : ℝ, z ≤ 0 ∧
      (∑ a : α,
        (μ a).toReal * (score a * Real.exp (z * score a))) = 0 := by
  classical
  let g : ℝ → ℝ :=
    fun z =>
      ∑ a : α, (μ a).toReal * (score a * Real.exp (z * score a))
  have hg_cont : Continuous g := by
    dsimp [g]
    exact continuous_finset_sum Finset.univ (fun a _ =>
      continuous_const.mul
        (continuous_const.mul
          (Real.continuous_exp.comp (continuous_id.mul continuous_const))))
  have hg_zero_nonneg : 0 ≤ g 0 := by
    dsimp [g]
    simpa [pmfExp, mul_assoc, mul_comm, mul_left_comm] using hmean
  by_cases hg_zero : g 0 = 0
  · exact ⟨0, le_rfl, hg_zero⟩
  have hg_zero_pos : 0 < g 0 := lt_of_le_of_ne hg_zero_nonneg (Ne.symm hg_zero)
  let posBound : ℝ :=
    ((Finset.univ : Finset α).erase aNeg).sum (fun a =>
      max 0 ((μ a).toReal * score a)
    )
  have hposBound_nonneg : 0 ≤ posBound := by
    dsimp [posBound]
    exact Finset.sum_nonneg (fun a _ => le_max_left _ _)
  let negScale : ℝ := (μ aNeg).toReal * (-(score aNeg))
  have hnegScale_pos : 0 < negScale := by
    dsimp [negScale]
    exact mul_pos hmassNeg (neg_pos.mpr hscoreNeg)
  let ratio : ℝ := posBound / negScale + 1
  have hratio_pos : 0 < ratio := by
    dsimp [ratio]
    have hdiv_nonneg : 0 ≤ posBound / negScale :=
      div_nonneg hposBound_nonneg hnegScale_pos.le
    linarith
  have hratio_ge_one : 1 ≤ ratio := by
    dsimp [ratio]
    have hdiv_nonneg : 0 ≤ posBound / negScale :=
      div_nonneg hposBound_nonneg hnegScale_pos.le
    linarith
  let zNeg : ℝ := Real.log ratio / score aNeg
  have hzNeg_nonpos : zNeg ≤ 0 := by
    dsimp [zNeg]
    exact div_nonpos_of_nonneg_of_nonpos
      (Real.log_nonneg hratio_ge_one) hscoreNeg.le
  have hzNeg_mul_score :
      zNeg * score aNeg = Real.log ratio := by
    dsimp [zNeg]
    exact div_mul_cancel₀ (Real.log ratio) (ne_of_lt hscoreNeg)
  have hexp_zNeg :
      Real.exp (zNeg * score aNeg) = ratio := by
    rw [hzNeg_mul_score]
    exact Real.exp_log hratio_pos
  have hneg_term_lt :
      (μ aNeg).toReal *
          (score aNeg * Real.exp (zNeg * score aNeg)) <
        -posBound := by
    have hneg_term_eq :
        (μ aNeg).toReal *
            (score aNeg * Real.exp (zNeg * score aNeg)) =
          -negScale * ratio := by
      dsimp [negScale]
      rw [hexp_zNeg]
      ring
    rw [hneg_term_eq]
    have hscale_ne : negScale ≠ 0 := ne_of_gt hnegScale_pos
    have hcalc : negScale * ratio = posBound + negScale := by
      dsimp [ratio]
      field_simp [hscale_ne]
    have hgt : posBound < negScale * ratio := by
      rw [hcalc]
      linarith
    linarith
  have hterm_le_bound :
      ∀ a ∈ (Finset.univ : Finset α).erase aNeg,
        (μ a).toReal * (score a * Real.exp (zNeg * score a)) ≤
          max 0 ((μ a).toReal * score a) := by
    intro a _ha
    by_cases hscore_nonneg : 0 ≤ score a
    · have hzscore_nonpos : zNeg * score a ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hzNeg_nonpos hscore_nonneg
      have hexp_le_one : Real.exp (zNeg * score a) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr hzscore_nonpos
      have hcoef_nonneg : 0 ≤ (μ a).toReal * score a :=
        mul_nonneg ENNReal.toReal_nonneg hscore_nonneg
      have hle :
          ((μ a).toReal * score a) *
              Real.exp (zNeg * score a) ≤
            (μ a).toReal * score a := by
        calc
          ((μ a).toReal * score a) *
              Real.exp (zNeg * score a)
              ≤ ((μ a).toReal * score a) * 1 :=
                mul_le_mul_of_nonneg_left hexp_le_one hcoef_nonneg
          _ = (μ a).toReal * score a := by ring
      have hmax_eq :
          max 0 ((μ a).toReal * score a) =
            (μ a).toReal * score a :=
        max_eq_right hcoef_nonneg
      simpa [mul_assoc, hmax_eq] using hle
    · have hscore_neg : score a < 0 := lt_of_not_ge hscore_nonneg
      have hterm_nonpos :
          (μ a).toReal * (score a * Real.exp (zNeg * score a)) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hscore_neg.le
            (Real.exp_pos _).le)
      exact hterm_nonpos.trans (le_max_left _ _)
  have hsum_erase_le :
      ((Finset.univ : Finset α).erase aNeg).sum
          (fun a =>
            (μ a).toReal * (score a * Real.exp (zNeg * score a))) ≤
        posBound := by
    dsimp [posBound]
    exact Finset.sum_le_sum hterm_le_bound
  have hg_zNeg_neg : g zNeg < 0 := by
    have hmem : aNeg ∈ (Finset.univ : Finset α) := Finset.mem_univ aNeg
    have hsum_eq :
        g zNeg =
          (μ aNeg).toReal *
              (score aNeg * Real.exp (zNeg * score aNeg)) +
            ((Finset.univ : Finset α).erase aNeg).sum
              (fun a =>
                (μ a).toReal * (score a * Real.exp (zNeg * score a))) := by
      dsimp [g]
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (i := aNeg) hmem]
      rw [Finset.sdiff_singleton_eq_erase]
    rw [hsum_eq]
    linarith
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (g zNeg) (g 0) :=
    ⟨le_of_lt hg_zNeg_neg, le_of_lt hg_zero_pos⟩
  rcases intermediate_value_Icc hzNeg_nonpos hg_cont.continuousOn hzero_mem with
    ⟨z, hz_mem, hz_zero⟩
  exact ⟨z, hz_mem.2, by simpa [g] using hz_zero⟩

/--
Finite Hölder bound for the MGF.  This is the multiplicative log-convexity
estimate used to prove convexity of `finiteLogMGF`.
-/
theorem finiteMGF_logConvex (μ : PMF α) (score : α → ℝ)
    {x y a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    finiteMGF μ score (a * x + b * y) ≤
      (finiteMGF μ score x) ^ a * (finiteMGF μ score y) ^ b := by
  classical
  let f : α → ℝ := fun c => ((μ c).toReal) ^ a * Real.exp (a * x * score c)
  let g : α → ℝ := fun c => ((μ c).toReal) ^ b * Real.exp (b * y * score c)
  have hpq : (1 / a).HolderConjugate (1 / b) :=
    Real.holderConjugate_one_div ha hb hab
  have hf_nonneg : ∀ c ∈ Finset.univ, 0 ≤ f c := by
    intro c _
    exact mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg a) (Real.exp_pos _).le
  have hg_nonneg : ∀ c ∈ Finset.univ, 0 ≤ g c := by
    intro c _
    exact mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg b) (Real.exp_pos _).le
  have hholder :=
    Real.inner_le_Lp_mul_Lq_of_nonneg
      (s := Finset.univ) (f := f) (g := g) hpq hf_nonneg hg_nonneg
  have hfg : ∀ c : α,
      f c * g c =
        (μ c).toReal * Real.exp ((a * x + b * y) * score c) := by
    intro c
    have hpow :
        ((μ c).toReal) ^ a * ((μ c).toReal) ^ b = (μ c).toReal := by
      rw [← Real.rpow_add' ENNReal.toReal_nonneg]
      · rw [hab, Real.rpow_one]
      · rw [hab]
        norm_num
    have hexp :
        Real.exp (a * x * score c) * Real.exp (b * y * score c) =
          Real.exp ((a * x + b * y) * score c) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp [f, g]
    calc
      (((μ c).toReal) ^ a * Real.exp (a * x * score c)) *
          (((μ c).toReal) ^ b * Real.exp (b * y * score c))
          = (((μ c).toReal) ^ a * ((μ c).toReal) ^ b) *
              (Real.exp (a * x * score c) * Real.exp (b * y * score c)) := by
            ring
      _ = (μ c).toReal * Real.exp ((a * x + b * y) * score c) := by
            rw [hpow, hexp]
  have hf_pow : ∀ c : α,
      f c ^ (1 / a) = (μ c).toReal * Real.exp (x * score c) := by
    intro c
    have hfa_nonneg : 0 ≤ ((μ c).toReal) ^ a :=
      Real.rpow_nonneg ENNReal.toReal_nonneg a
    dsimp [f]
    rw [Real.mul_rpow hfa_nonneg (Real.exp_pos _).le]
    rw [← Real.rpow_mul ENNReal.toReal_nonneg]
    rw [show a * (1 / a) = 1 by field_simp [ha.ne']]
    rw [Real.rpow_one]
    rw [← Real.exp_mul]
    congr 1
    field_simp [ha.ne']
  have hg_pow : ∀ c : α,
      g c ^ (1 / b) = (μ c).toReal * Real.exp (y * score c) := by
    intro c
    have hgb_nonneg : 0 ≤ ((μ c).toReal) ^ b :=
      Real.rpow_nonneg ENNReal.toReal_nonneg b
    dsimp [g]
    rw [Real.mul_rpow hgb_nonneg (Real.exp_pos _).le]
    rw [← Real.rpow_mul ENNReal.toReal_nonneg]
    rw [show b * (1 / b) = 1 by field_simp [hb.ne']]
    rw [Real.rpow_one]
    rw [← Real.exp_mul]
    congr 1
    field_simp [hb.ne']
  have hsumf :
      (∑ c ∈ Finset.univ, f c ^ (1 / a)) = finiteMGF μ score x := by
    unfold finiteMGF
    refine Finset.sum_congr rfl ?_
    intro c _
    simpa [one_div] using hf_pow c
  have hsumg :
      (∑ c ∈ Finset.univ, g c ^ (1 / b)) = finiteMGF μ score y := by
    unfold finiteMGF
    refine Finset.sum_congr rfl ?_
    intro c _
    simpa [one_div] using hg_pow c
  calc
    finiteMGF μ score (a * x + b * y)
        = ∑ c ∈ Finset.univ, f c * g c := by
          unfold finiteMGF
          simp [hfg]
    _ ≤
        (∑ c ∈ Finset.univ, f c ^ (1 / a)) ^ (1 / (1 / a)) *
          (∑ c ∈ Finset.univ, g c ^ (1 / b)) ^ (1 / (1 / b)) := hholder
    _ = (finiteMGF μ score x) ^ a * (finiteMGF μ score y) ^ b := by
      rw [hsumf, hsumg]
      congr 1 <;> field_simp [ha.ne', hb.ne']

/-- The finite log-MGF is convex in its real dual parameter. -/
theorem finiteLogMGF_convex (μ : PMF α) (score : α → ℝ) :
    ConvexOn ℝ Set.univ (fun z : ℝ => finiteLogMGF μ score z) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  rcases eq_or_lt_of_le ha with ha_zero | ha_pos
  · subst a
    have hb_one : b = 1 := by linarith
    subst b
    simp
  rcases eq_or_lt_of_le hb with hb_zero | hb_pos
  · subst b
    have ha_one : a = 1 := by linarith
    subst a
    simp
  have hmgf :=
    finiteMGF_logConvex μ score (x := x) (y := y)
      (a := a) (b := b) ha_pos hb_pos hab
  have hlog := Real.log_le_log (finiteMGF_pos μ score (a * x + b * y)) hmgf
  have hxpos : 0 < finiteMGF μ score x := finiteMGF_pos μ score x
  have hypos : 0 < finiteMGF μ score y := finiteMGF_pos μ score y
  calc
    finiteLogMGF μ score (a • x + b • y)
        = Real.log (finiteMGF μ score (a * x + b * y)) := by
          simp [finiteLogMGF, smul_eq_mul]
    _ ≤ Real.log ((finiteMGF μ score x) ^ a * (finiteMGF μ score y) ^ b) := hlog
    _ = a • finiteLogMGF μ score x + b • finiteLogMGF μ score y := by
      rw [Real.log_mul]
      · rw [Real.log_rpow hxpos, Real.log_rpow hypos]
        simp [finiteLogMGF, smul_eq_mul]
      · exact (Real.rpow_pos_of_pos hxpos a).ne'
      · exact (Real.rpow_pos_of_pos hypos b).ne'

/--
For a finite log-MGF, a derivative at a nonpositive dual parameter is bounded
above by the ordinary mean.
-/
theorem finiteLogMGF_hasDerivAt_le_mean_of_nonpos
    (μ : PMF α) (score : α → ℝ) {a z0 : ℝ}
    (hz0 : z0 ≤ 0)
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) a z0) :
    a ≤ pmfExp μ score :=
  convex_hasDerivAt_mono_of_le
    (finiteLogMGF_convex μ score) hz0 hderiv
    (finiteLogMGF_hasDerivAt_zero μ score)

/--
For a finite log-MGF, the ordinary mean is bounded above by any derivative at
a nonnegative dual parameter.
-/
theorem finiteLogMGF_mean_le_hasDerivAt_of_nonneg
    (μ : PMF α) (score : α → ℝ) {a z0 : ℝ}
    (hz0 : 0 ≤ z0)
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) a z0) :
    pmfExp μ score ≤ a :=
  convex_hasDerivAt_mono_of_le
    (finiteLogMGF_convex μ score) hz0
    (finiteLogMGF_hasDerivAt_zero μ score) hderiv

/--
If a finite score law has positive probability on one strictly positive score
and one strictly negative score, its log-MGF range is bounded below.

The proof is elementary: for `z >= 0`, the positive atom contributes at least
its mass; for `z <= 0`, the negative atom contributes at least its mass.
-/
theorem finiteLogMGF_bddBelow_of_pos_neg_atoms
    (μ : PMF α) (score : α → ℝ)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0) :
    BddBelow (Set.range fun z : ℝ => finiteLogMGF μ score z) := by
  let m : ℝ := min (μ aPos).toReal (μ aNeg).toReal
  have hm_pos : 0 < m := lt_min hmassPos hmassNeg
  refine ⟨Real.log m, ?_⟩
  intro y hy
  rcases hy with ⟨z, rfl⟩
  unfold finiteLogMGF
  refine Real.log_le_log hm_pos ?_
  by_cases hz : 0 ≤ z
  · have hexp :
        1 ≤ Real.exp (z * score aPos) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonneg hz (le_of_lt hscorePos))
    have hterm :
        (μ aPos).toReal ≤
          (μ aPos).toReal * Real.exp (z * score aPos) := by
      calc
        (μ aPos).toReal = (μ aPos).toReal * 1 := by ring
        _ ≤ (μ aPos).toReal * Real.exp (z * score aPos) :=
          mul_le_mul_of_nonneg_left hexp hmassPos.le
    exact
      (min_le_left (μ aPos).toReal (μ aNeg).toReal).trans
        (hterm.trans (finiteMGF_ge_atom μ score z aPos))
  · have hz_nonpos : z ≤ 0 := le_of_not_ge hz
    have hexp :
        1 ≤ Real.exp (z * score aNeg) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonneg_of_nonpos_of_nonpos hz_nonpos (le_of_lt hscoreNeg))
    have hterm :
        (μ aNeg).toReal ≤
          (μ aNeg).toReal * Real.exp (z * score aNeg) := by
      calc
        (μ aNeg).toReal = (μ aNeg).toReal * 1 := by ring
        _ ≤ (μ aNeg).toReal * Real.exp (z * score aNeg) :=
          mul_le_mul_of_nonneg_left hexp hmassNeg.le
    exact
      (min_le_right (μ aPos).toReal (μ aNeg).toReal).trans
        (hterm.trans (finiteMGF_ge_atom μ score z aNeg))

/--
The zero-score event gives a fixed lower bound on every finite MGF value.
This is useful for one-sided boundary cases where the left-tail event is
realized exactly by zero-score samples.
-/
theorem finiteMGF_ge_pmfProb_score_eq_zero
    (μ : PMF α) (score : α → ℝ) (z : ℝ) :
    AppliedModelingLib.pmfProb μ (fun a => score a = 0) ≤ finiteMGF μ score z := by
  classical
  unfold AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp finiteMGF
  refine Finset.sum_le_sum ?_
  intro a _
  by_cases hzero : score a = 0
  · simp [hzero]
  · simp [hzero, mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le]

/--
At the lower endpoint of a nonnegative finite score law, the finite MGF
converges to the mass of the zero-score event as the dual parameter tends to
minus infinity.  Zero-mass labels are intentionally ignored.
-/
theorem finiteMGF_tendsto_pmfProb_score_eq_zero_atBot_of_support_nonneg
    (μ : PMF α) (score : α → ℝ)
    (hsupport : ∀ a, 0 < (μ a).toReal → 0 ≤ score a) :
    Filter.Tendsto (fun z : ℝ => finiteMGF μ score z)
      Filter.atBot
      (nhds (AppliedModelingLib.pmfProb μ (fun a => score a = 0))) := by
  classical
  have hsum :
      Filter.Tendsto
        (fun z : ℝ =>
          ∑ a : α, (μ a).toReal * Real.exp (z * score a))
        Filter.atBot
        (nhds (∑ a : α,
          (μ a).toReal * (if score a = 0 then (1 : ℝ) else 0))) := by
    refine tendsto_finset_sum (Finset.univ : Finset α) ?_
    intro a _ha
    by_cases hmass_zero : (μ a).toReal = 0
    · have hterm_zero :
          (fun z : ℝ => (μ a).toReal * Real.exp (z * score a)) =
            fun _ : ℝ => (μ a).toReal * (if score a = 0 then (1 : ℝ) else 0) := by
          funext z
          simp [hmass_zero]
      rw [hterm_zero]
      exact tendsto_const_nhds
    · have hmass_pos : 0 < (μ a).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hmass_zero)
      by_cases hscore_zero : score a = 0
      · have hterm_const :
          (fun z : ℝ => (μ a).toReal * Real.exp (z * score a)) =
            fun _ : ℝ => (μ a).toReal * (if score a = 0 then (1 : ℝ) else 0) := by
          funext z
          simp [hscore_zero]
        rw [hterm_const]
        exact tendsto_const_nhds
      · have hscore_pos : 0 < score a :=
          lt_of_le_of_ne (hsupport a hmass_pos) (Ne.symm hscore_zero)
        have harg :
            Filter.Tendsto (fun z : ℝ => z * score a)
              Filter.atBot Filter.atBot :=
          Filter.tendsto_id.atBot_mul_const hscore_pos
        have hexp :
            Filter.Tendsto (fun z : ℝ => Real.exp (z * score a))
              Filter.atBot (nhds 0) :=
          Real.tendsto_exp_atBot.comp harg
        have hterm := hexp.const_mul ((μ a).toReal)
        have htarget :
            (μ a).toReal * (if score a = 0 then (1 : ℝ) else 0) = 0 := by
          simp [hscore_zero]
        simpa [htarget] using hterm
  simpa [finiteMGF, AppliedModelingLib.pmfProb, AppliedModelingLib.pmfExp] using hsum

/--
If a finite law is concentrated on one score, its MGF is the exponential MGF
of that constant.  The premise is support-based so zero-mass labels need not
share the score.
-/
theorem finiteMGF_eq_exp_of_support_score_eq_const
    (μ : PMF α) (score : α → ℝ) (c z : ℝ)
    (hconst : ∀ a, 0 < (μ a).toReal → score a = c) :
    finiteMGF μ score z = Real.exp (z * c) := by
  classical
  unfold finiteMGF
  calc
    ∑ a : α, (μ a).toReal * Real.exp (z * score a)
        = ∑ a : α, (μ a).toReal * Real.exp (z * c) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          by_cases hmass : 0 < (μ a).toReal
          · rw [hconst a hmass]
          · have hzero : (μ a).toReal = 0 :=
              le_antisymm (le_of_not_gt hmass) ENNReal.toReal_nonneg
            simp [hzero]
    _ = (∑ a : α, (μ a).toReal) * Real.exp (z * c) := by
          rw [Finset.sum_mul]
    _ = Real.exp (z * c) := by rw [pmfToRealSum μ, one_mul]

/-- A finite log-MGF is linear when its score is constant on positive support. -/
theorem finiteLogMGF_eq_mul_of_support_score_eq_const
    (μ : PMF α) (score : α → ℝ) (c z : ℝ)
    (hconst : ∀ a, 0 < (μ a).toReal → score a = c) :
    finiteLogMGF μ score z = z * c := by
  rw [finiteLogMGF,
    finiteMGF_eq_exp_of_support_score_eq_const μ score c z hconst,
    Real.log_exp]

/--
If the zero-score event has positive probability, the finite log-MGF range is
bounded below.  The lower bound is `log Pr(score = 0)`.
-/
theorem finiteLogMGF_bddBelow_of_zero_score_prob_pos
    (μ : PMF α) (score : α → ℝ)
    (hzero :
      0 < AppliedModelingLib.pmfProb μ (fun a => score a = 0)) :
    BddBelow (Set.range fun z : ℝ => finiteLogMGF μ score z) := by
  refine ⟨Real.log (AppliedModelingLib.pmfProb μ (fun a => score a = 0)), ?_⟩
  intro y hy
  rcases hy with ⟨z, rfl⟩
  unfold finiteLogMGF
  exact Real.log_le_log hzero
    (finiteMGF_ge_pmfProb_score_eq_zero μ score z)

theorem finiteLogMGF_zero (μ : PMF α) (score : α → ℝ) :
    finiteLogMGF μ score 0 = 0 := by
  rw [finiteLogMGF, finiteMGF_zero, Real.log_one]

/--
If `z * E[X] >= 0`, then the finite log-MGF at `z` is nonnegative.
-/
theorem finiteLogMGF_nonneg_of_mul_pmfExp_nonneg
    (μ : PMF α) (score : α → ℝ) {z : ℝ}
    (hmul : 0 ≤ z * pmfExp μ score) :
    0 ≤ finiteLogMGF μ score z := by
  unfold finiteLogMGF
  apply Real.log_nonneg
  have hone :
      1 ≤ 1 + z * pmfExp μ score := by
    linarith
  exact hone.trans (one_add_mul_pmfExp_le_finiteMGF μ score z)

/--
For a finite score with nonnegative mean, every nonnegative dual has
nonnegative log-MGF.
-/
theorem finiteLogMGF_nonneg_of_nonneg_dual_of_pmfExp_nonneg
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ finiteLogMGF μ score z :=
  finiteLogMGF_nonneg_of_mul_pmfExp_nonneg μ score
    (mul_nonneg hz hmean)

/--
Positive finite-support mean gives a nonpositive Chernoff dual whose
negative log-MGF value is strictly positive.
-/
theorem exists_nonpos_dual_neg_finiteLogMGF_pos_of_pmfExp_pos
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 < pmfExp μ score) :
    ∃ z : ℝ, z ≤ 0 ∧ 0 < -finiteLogMGF μ score z := by
  rcases exists_neg_finiteMGF_lt_one_of_pmfExp_pos μ score hmean with
    ⟨z, hz, hlt⟩
  have hlog_lt_zero :
      finiteLogMGF μ score z < 0 := by
    unfold finiteLogMGF
    simpa using
      (Real.log_lt_log (finiteMGF_pos μ score z) hlt)
  exact ⟨z, le_of_lt hz, by linarith⟩

theorem exp_finiteLogMGF (μ : PMF α) (score : α → ℝ) (z : ℝ) :
    Real.exp (finiteLogMGF μ score z) = finiteMGF μ score z := by
  rw [finiteLogMGF]
  exact Real.exp_log (finiteMGF_pos μ score z)

theorem finiteMGF_const_score (μ : PMF α) (c z : ℝ) :
    finiteMGF μ (fun _ => c) z = Real.exp (z * c) := by
  dsimp [finiteMGF]
  rw [← Finset.sum_mul]
  rw [pmfToRealSum]
  ring

theorem finiteLogMGF_const_score (μ : PMF α) (c z : ℝ) :
    finiteLogMGF μ (fun _ => c) z = z * c := by
  rw [finiteLogMGF, finiteMGF_const_score, Real.log_exp]

/-- Shifting a score down by a constant factors the finite MGF. -/
theorem finiteMGF_sub_const (μ : PMF α) (score : α → ℝ) (a z : ℝ) :
    finiteMGF μ (fun x => score x - a) z =
      Real.exp (-(z * a)) * finiteMGF μ score z := by
  unfold finiteMGF
  calc
    ∑ x : α, (μ x).toReal * Real.exp (z * (score x - a))
        =
        ∑ x : α,
          Real.exp (-(z * a)) *
            ((μ x).toReal * Real.exp (z * score x)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [show z * (score x - a) = -(z * a) + z * score x by ring]
          rw [Real.exp_add]
          ring
    _ =
        Real.exp (-(z * a)) *
          ∑ x : α, (μ x).toReal * Real.exp (z * score x) := by
          rw [Finset.mul_sum]

/-- Shifting a score down by a constant subtracts the corresponding linear term. -/
theorem finiteLogMGF_sub_const (μ : PMF α) (score : α → ℝ) (a z : ℝ) :
    finiteLogMGF μ (fun x => score x - a) z =
      finiteLogMGF μ score z - z * a := by
  rw [finiteLogMGF, finiteMGF_sub_const]
  rw [Real.log_mul (Real.exp_pos (-(z * a))).ne'
    (finiteMGF_pos μ score z).ne']
  rw [Real.log_exp, finiteLogMGF]
  ring

/-- Shifting a score up from a constant evaluates the original MGF at `-z`. -/
theorem finiteMGF_const_sub (μ : PMF α) (score : α → ℝ) (a z : ℝ) :
    finiteMGF μ (fun x => a - score x) z =
      Real.exp (z * a) * finiteMGF μ score (-z) := by
  unfold finiteMGF
  calc
    ∑ x : α, (μ x).toReal * Real.exp (z * (a - score x))
        =
        ∑ x : α,
          Real.exp (z * a) *
            ((μ x).toReal * Real.exp ((-z) * score x)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [show z * (a - score x) = z * a + (-z) * score x by ring]
          rw [Real.exp_add]
          ring
    _ =
        Real.exp (z * a) *
          ∑ x : α, (μ x).toReal * Real.exp ((-z) * score x) := by
          rw [Finset.mul_sum]

/-- Shifting a score up from a constant adds a linear term and flips the dual. -/
theorem finiteLogMGF_const_sub (μ : PMF α) (score : α → ℝ) (a z : ℝ) :
    finiteLogMGF μ (fun x => a - score x) z =
      z * a + finiteLogMGF μ score (-z) := by
  rw [finiteLogMGF, finiteMGF_const_sub]
  rw [Real.log_mul (Real.exp_pos (z * a)).ne'
    (finiteMGF_pos μ score (-z)).ne']
  rw [Real.log_exp, finiteLogMGF]

/--
If the original finite log-MGF has derivative `a`, then the log-MGF of
`score - a` has derivative zero at the same dual parameter.
-/
theorem finiteLogMGF_sub_const_hasDerivAt_zero
    (μ : PMF α) (score : α → ℝ) {a z0 : ℝ}
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) a z0) :
    HasDerivAt
      (fun z : ℝ => finiteLogMGF μ (fun x => score x - a) z) 0 z0 := by
  have hfun :
      (fun z : ℝ => finiteLogMGF μ (fun x => score x - a) z) =
        fun z : ℝ => finiteLogMGF μ score z - z * a := by
    funext z
    exact finiteLogMGF_sub_const μ score a z
  rw [hfun]
  have hlinear : HasDerivAt (fun z : ℝ => z * a) a z0 := by
    simpa using (hasDerivAt_id z0).mul_const a
  simpa using hderiv.sub hlinear

/--
If the original finite log-MGF has derivative `a` at `-z0`, then the log-MGF
of `a - score` has derivative zero at `z0`.
-/
theorem finiteLogMGF_const_sub_hasDerivAt_zero
    (μ : PMF α) (score : α → ℝ) {a z0 : ℝ}
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) a (-z0)) :
    HasDerivAt
      (fun z : ℝ => finiteLogMGF μ (fun x => a - score x) z) 0 z0 := by
  have hfun :
      (fun z : ℝ => finiteLogMGF μ (fun x => a - score x) z) =
        fun z : ℝ => z * a + finiteLogMGF μ score (-z) := by
    funext z
    exact finiteLogMGF_const_sub μ score a z
  rw [hfun]
  have hlinear : HasDerivAt (fun z : ℝ => z * a) a z0 := by
    simpa using (hasDerivAt_id z0).mul_const a
  have hneg : HasDerivAt (fun z : ℝ => -z) (-1) z0 := by
    simpa using (hasDerivAt_id z0).neg
  have hcomp :
      HasDerivAt (fun z : ℝ => finiteLogMGF μ score (-z)) (-a) z0 := by
    simpa using hderiv.comp z0 hneg
  simpa using hlinear.add hcomp

/-- Legendre-transform objective at a fixed dual parameter `z`. -/
def finiteLegendreValue (μ : PMF α) (score : α → ℝ)
    (a z : ℝ) : ℝ :=
  z * a - finiteLogMGF μ score z

/--
Finite-support Cramer-style rate function written as the supremum of the
Legendre objective.
-/
def finiteRateFunction (μ : PMF α) (score : α → ℝ)
    (a : ℝ) : ℝ :=
  sSup (Set.range fun z : ℝ => finiteLegendreValue μ score a z)

/--
Extended finite-support Legendre rate. Unlike `finiteRateFunction`, this
records an unbounded Legendre supremum as `⊤`, which is the mathematically
correct value for thresholds outside the finite score hull.
-/
def finiteRateFunctionTop (μ : PMF α) (score : α → ℝ)
    (a : ℝ) : WithTop ℝ :=
  sSup (Set.range fun z : ℝ =>
    (finiteLegendreValue μ score a z : WithTop ℝ))

/--
For a nonpositive dual parameter, a global lower score bound upper-bounds the
finite MGF. This is the elementary estimate behind the fact that the legacy
real-valued Legendre wrapper is not sound outside the score hull.
-/
theorem finiteMGF_le_exp_mul_of_nonpos_of_score_lower_bound
    (μ : PMF α) (score : α → ℝ) (b z : ℝ)
    (hz : z ≤ 0) (hlower : ∀ x : α, b ≤ score x) :
    finiteMGF μ score z ≤ Real.exp (z * b) := by
  unfold finiteMGF
  calc
    (Finset.univ.sum fun x : α =>
        (μ x).toReal * Real.exp (z * score x)) ≤
      Finset.univ.sum fun x : α =>
        (μ x).toReal * Real.exp (z * b) := by
          refine Finset.sum_le_sum fun x _ => ?_
          apply mul_le_mul_of_nonneg_left
          · apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonpos_left (hlower x) hz
          · exact ENNReal.toReal_nonneg
    _ = (Finset.univ.sum fun x : α => (μ x).toReal) *
          Real.exp (z * b) := by
          rw [Finset.sum_mul]
    _ = Real.exp (z * b) := by rw [pmfToRealSum μ, one_mul]

/-- A lower score bound controls the finite log-MGF along negative duals. -/
theorem finiteLogMGF_le_mul_of_nonpos_of_score_lower_bound
    (μ : PMF α) (score : α → ℝ) (b z : ℝ)
    (hz : z ≤ 0) (hlower : ∀ x : α, b ≤ score x) :
    finiteLogMGF μ score z ≤ z * b := by
  unfold finiteLogMGF
  have hmgf := finiteMGF_le_exp_mul_of_nonpos_of_score_lower_bound
    μ score b z hz hlower
  have hlog := Real.log_le_log (finiteMGF_pos μ score z) hmgf
  simpa using hlog

/--
Below a global score lower bound, the real Legendre-value range is unbounded
above. This is a warning about `finiteRateFunction`'s `Real.sSup` codomain,
not a large-deviation statement: the mathematically correct extended value is
`⊤`.
-/
theorem finiteLegendreValue_not_bddAbove_of_lt_score_lower_bound
    (μ : PMF α) (score : α → ℝ) (a b : ℝ)
    (ha : a < b) (hlower : ∀ x : α, b ≤ score x) :
    ¬ BddAbove (Set.range fun z : ℝ => finiteLegendreValue μ score a z) := by
  rw [not_bddAbove_iff]
  intro bound
  let z : ℝ := -(abs bound + 1) / (b - a)
  have hba : 0 < b - a := sub_pos.mpr ha
  have hz : z ≤ 0 := by
    dsimp [z]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by positivity)) hba.le
  have hlog := finiteLogMGF_le_mul_of_nonpos_of_score_lower_bound
    μ score b z hz hlower
  have hgrowth : z * a - z * b = abs bound + 1 := by
    dsimp [z]
    field_simp [ne_of_gt hba]
    ring
  refine ⟨finiteLegendreValue μ score a z, ⟨z, rfl⟩, ?_⟩
  unfold finiteLegendreValue
  calc
    bound < abs bound + 1 := by linarith [le_abs_self bound]
    _ = z * a - z * b := hgrowth.symm
    _ ≤ z * a - finiteLogMGF μ score z := by linarith

/--
`finiteRateFunction` has a legacy `Real` codomain. Since `Real.sSup` is zero
on an unbounded-above set, its value below a global score lower bound is zero,
whereas `finiteRateFunctionTop` correctly returns `⊤` there.
-/
theorem finiteRateFunction_eq_zero_of_lt_score_lower_bound
    (μ : PMF α) (score : α → ℝ) (a b : ℝ)
    (ha : a < b) (hlower : ∀ x : α, b ≤ score x) :
    finiteRateFunction μ score a = 0 := by
  unfold finiteRateFunction
  exact Real.sSup_of_not_bddAbove
    (finiteLegendreValue_not_bddAbove_of_lt_score_lower_bound
      μ score a b ha hlower)

/--
Finite-support Chernoff exponent for the left-tail event of a score with
positive mean, written as `- inf_z log E exp(z X)`. The actual tail theorem is
supplied by a caller-provided LDP/Chernoff certificate; this definition fixes
the reusable finite-support formula.
-/
def finiteChernoffRate (μ : PMF α) (score : α → ℝ) : ℝ :=
  -sInf (Set.range fun z : ℝ => finiteLogMGF μ score z)

/--
The zero-score probability upper-bounds the finite Chernoff exponent.  This is
the order form of `finiteLogMGF_bddBelow_of_zero_score_prob_pos`: every
log-MGF value is at least `log Pr(score = 0)`, so `-inf logMGF` is at most the
zero-gap exponent.
-/
theorem finiteChernoffRate_le_neg_log_pmfProb_score_eq_zero
    (μ : PMF α) (score : α → ℝ)
    (hzero :
      0 < AppliedModelingLib.pmfProb μ (fun a => score a = 0)) :
    finiteChernoffRate μ score ≤
      -Real.log (AppliedModelingLib.pmfProb μ (fun a => score a = 0)) := by
  unfold finiteChernoffRate
  apply neg_le_neg
  refine le_csInf ?_ ?_
  · exact ⟨finiteLogMGF μ score 0, ⟨0, rfl⟩⟩
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    unfold finiteLogMGF
    exact Real.log_le_log hzero
      (finiteMGF_ge_pmfProb_score_eq_zero μ score z)

/--
At the lower endpoint of a nonnegative finite score law with positive
zero-score mass, the Chernoff exponent is the negative logarithm of that
mass.  The infimum need not be attained at a finite dual parameter.
-/
theorem finiteChernoffRate_eq_neg_log_pmfProb_score_eq_zero_of_support_nonneg
    (μ : PMF α) (score : α → ℝ)
    (hsupport : ∀ a, 0 < (μ a).toReal → 0 ≤ score a)
    {pZero : ℝ}
    (hpZero : AppliedModelingLib.pmfProb μ (fun a => score a = 0) = pZero)
    (hpZero_pos : 0 < pZero) :
    finiteChernoffRate μ score = -Real.log pZero := by
  have hmgf :
      Filter.Tendsto (fun z : ℝ => finiteMGF μ score z)
        Filter.atBot
        (nhds pZero) := by
    simpa [hpZero] using
      finiteMGF_tendsto_pmfProb_score_eq_zero_atBot_of_support_nonneg
        μ score hsupport
  have hlog :
      Filter.Tendsto (fun z : ℝ => finiteLogMGF μ score z)
        Filter.atBot
        (nhds (Real.log pZero)) := by
    simpa [finiteLogMGF] using
      (Real.continuousAt_log (ne_of_gt hpZero_pos)).tendsto.comp hmgf
  have hInf :
      sInf (Set.range fun z : ℝ => finiteLogMGF μ score z) =
        Real.log pZero := by
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt (Set.range_nonempty _)
    · intro y hy
      rcases hy with ⟨z, rfl⟩
      rw [← hpZero]
      unfold finiteLogMGF
      exact Real.log_le_log (by simpa [hpZero] using hpZero_pos)
        (finiteMGF_ge_pmfProb_score_eq_zero μ score z)
    · intro w hw
      rcases (hlog.eventually_lt_const hw).exists with ⟨z, hz⟩
      exact ⟨finiteLogMGF μ score z, ⟨z, rfl⟩, hz⟩
  simp [finiteChernoffRate, hInf]

/--
If a proposed value is a global minimum of the finite log-MGF and is attained,
then it is the `sInf` of the log-MGF range.
-/
theorem finiteLogMGF_sInf_eq_of_global_min
    (μ : PMF α) (score : α → ℝ) {minVal z0 : ℝ}
    (hmin : ∀ z : ℝ, minVal ≤ finiteLogMGF μ score z)
    (hwitness : finiteLogMGF μ score z0 = minVal) :
    sInf (Set.range fun z : ℝ => finiteLogMGF μ score z) = minVal := by
  let S : Set ℝ := Set.range fun z : ℝ => finiteLogMGF μ score z
  have hnonempty : S.Nonempty :=
    ⟨finiteLogMGF μ score z0, ⟨z0, rfl⟩⟩
  have hbdd : BddBelow S := by
    refine ⟨minVal, ?_⟩
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact hmin z
  have hle : sInf S ≤ minVal := by
    rw [← hwitness]
    exact csInf_le hbdd ⟨z0, rfl⟩
  have hge : minVal ≤ sInf S := by
    refine le_csInf hnonempty ?_
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact hmin z
  exact le_antisymm hle hge

/--
Finite Chernoff-rate identity from an attained global log-MGF minimum.
-/
theorem finiteChernoffRate_eq_neg_of_logMGF_global_min
    (μ : PMF α) (score : α → ℝ) {minVal z0 : ℝ}
    (hmin : ∀ z : ℝ, minVal ≤ finiteLogMGF μ score z)
    (hwitness : finiteLogMGF μ score z0 = minVal) :
    finiteChernoffRate μ score = -minVal := by
  rw [finiteChernoffRate,
    finiteLogMGF_sInf_eq_of_global_min μ score hmin hwitness]

/--
Finite Chernoff-rate identity in the geometric-base form used by explicit
periodic/type lower-bound certificates.
-/
theorem finiteChernoffRate_eq_neg_log_base_of_logMGF_global_min
    (μ : PMF α) (score : α → ℝ) {base z0 : ℝ}
    (hmin : ∀ z : ℝ, Real.log base ≤ finiteLogMGF μ score z)
    (hwitness : finiteLogMGF μ score z0 = Real.log base) :
    finiteChernoffRate μ score = -Real.log base :=
  finiteChernoffRate_eq_neg_of_logMGF_global_min
    μ score hmin hwitness

/--
Finite log-MGF minimizer certificate from convexity and a zero derivative at
the proposed minimizer.
-/
theorem finiteLogMGF_global_min_of_convex_hasDerivAt_zero
    (μ : PMF α) (score : α → ℝ) {z0 : ℝ}
    (hconv : ConvexOn ℝ Set.univ (fun z : ℝ => finiteLogMGF μ score z))
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) 0 z0) :
    ∀ z : ℝ, finiteLogMGF μ score z0 ≤ finiteLogMGF μ score z :=
  global_min_of_convex_hasDerivAt_zero hconv hderiv

/--
Finite Chernoff-rate identity from the source proof's usual first-order
certificate for the minimizing log-MGF dual parameter.
-/
theorem finiteChernoffRate_eq_neg_log_base_of_convex_hasDerivAt_zero
    (μ : PMF α) (score : α → ℝ) {base z0 : ℝ}
    (hconv : ConvexOn ℝ Set.univ (fun z : ℝ => finiteLogMGF μ score z))
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) 0 z0)
    (hwitness : finiteLogMGF μ score z0 = Real.log base) :
    finiteChernoffRate μ score = -Real.log base := by
  have hmin_at_z0 :
      ∀ z : ℝ, finiteLogMGF μ score z0 ≤ finiteLogMGF μ score z :=
    finiteLogMGF_global_min_of_convex_hasDerivAt_zero μ score hconv hderiv
  have hmin : ∀ z : ℝ, Real.log base ≤ finiteLogMGF μ score z := by
    intro z
    simpa [hwitness] using hmin_at_z0 z
  exact finiteChernoffRate_eq_neg_log_base_of_logMGF_global_min
    μ score hmin hwitness

/--
Finite Chernoff-rate identity from convexity plus the explicit stationary
equation for the finite log-MGF.
-/
theorem finiteChernoffRate_eq_neg_log_base_of_convex_stationary
    (μ : PMF α) (score : α → ℝ) {base z0 : ℝ}
    (hconv : ConvexOn ℝ Set.univ (fun z : ℝ => finiteLogMGF μ score z))
    (hstationary :
      (∑ a : α,
        (μ a).toReal * (score a * Real.exp (z0 * score a))) = 0)
    (hwitness : finiteLogMGF μ score z0 = Real.log base) :
    finiteChernoffRate μ score = -Real.log base :=
  finiteChernoffRate_eq_neg_log_base_of_convex_hasDerivAt_zero
    μ score hconv
    (finiteLogMGF_hasDerivAt_zero_of_weighted_exp_score_sum_eq_zero
      μ score hstationary)
    hwitness

/--
If one log-MGF is pointwise no larger than another, its Chernoff exponent
`-inf logMGF` is weakly larger.  The bounded-below hypothesis is exactly the
condition needed to use the real `sInf` API on the smaller log-MGF.
-/
theorem neg_sInf_range_mono_of_pointwise_le
    {f g : ℝ → ℝ}
    (hf_bdd : BddBelow (Set.range f))
    (hfg : ∀ z : ℝ, f z ≤ g z) :
    -sInf (Set.range g) ≤ -sInf (Set.range f) := by
  have hinf_le : sInf (Set.range f) ≤ sInf (Set.range g) := by
    refine le_csInf ⟨g 0, ⟨0, rfl⟩⟩ ?_
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact (csInf_le hf_bdd ⟨z, rfl⟩).trans (hfg z)
  exact neg_le_neg hinf_le

/--
Chernoff-rate monotonicity under pointwise log-MGF domination.
-/
theorem finiteChernoffRate_mono_of_logMGF_le
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (staticLaw : PMF α) (randomizedLaw : PMF β)
    (staticScore : α → ℝ) (randomizedScore : β → ℝ)
    (hstatic_bdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF staticLaw staticScore z))
    (hlog :
      ∀ z : ℝ,
        finiteLogMGF staticLaw staticScore z ≤
          finiteLogMGF randomizedLaw randomizedScore z) :
    finiteChernoffRate randomizedLaw randomizedScore ≤
      finiteChernoffRate staticLaw staticScore := by
  simpa [finiteChernoffRate] using
    neg_sInf_range_mono_of_pointwise_le hstatic_bdd hlog

theorem finiteRateFunction_ge_eval
    (μ : PMF α) (score : α → ℝ) (a z : ℝ)
    (hbdd : BddAbove (Set.range fun t : ℝ =>
      finiteLegendreValue μ score a t)) :
    finiteLegendreValue μ score a z ≤ finiteRateFunction μ score a := by
  exact le_csSup hbdd ⟨z, rfl⟩

/-- Every finite Legendre value is below the extended Legendre supremum. -/
theorem finiteRateFunctionTop_ge_eval
    (μ : PMF α) (score : α → ℝ) (a z : ℝ) :
    (finiteLegendreValue μ score a z : WithTop ℝ) ≤
      finiteRateFunctionTop μ score a := by
  exact
    le_csSup
      (show BddAbove
        (Set.range fun t : ℝ =>
          (finiteLegendreValue μ score a t : WithTop ℝ)) from
      ⟨⊤, by intro y _hy; exact le_top⟩)
      ⟨z, rfl⟩

/--
An unbounded finite Legendre-value range has infinite extended rate.
-/
theorem finiteRateFunctionTop_eq_top_of_not_bddAbove
    (μ : PMF α) (score : α → ℝ) (a : ℝ)
    (hnotbdd : ¬ BddAbove (Set.range fun z : ℝ =>
      finiteLegendreValue μ score a z)) :
    finiteRateFunctionTop μ score a = ⊤ := by
  classical
  unfold finiteRateFunctionTop
  have htop_notmem :
      (⊤ : WithTop ℝ) ∉ Set.range (fun z : ℝ =>
        (finiteLegendreValue μ score a z : WithTop ℝ)) := by
    rintro ⟨z, hz⟩
    exact WithTop.coe_ne_top hz
  have hpreimage :
      ((fun y : ℝ => (y : WithTop ℝ)) ⁻¹'
        Set.range (fun z : ℝ =>
          (finiteLegendreValue μ score a z : WithTop ℝ))) =
        Set.range fun z : ℝ => finiteLegendreValue μ score a z := by
    ext y
    simp
  change
    (if (⊤ : WithTop ℝ) ∈ Set.range (fun z : ℝ =>
      (finiteLegendreValue μ score a z : WithTop ℝ)) then ⊤
      else if BddAbove
        ((fun y : ℝ => (y : WithTop ℝ)) ⁻¹'
          Set.range (fun z : ℝ =>
            (finiteLegendreValue μ score a z : WithTop ℝ))) then
        (↑(sSup ((fun y : ℝ => (y : WithTop ℝ)) ⁻¹'
          Set.range (fun z : ℝ =>
            (finiteLegendreValue μ score a z : WithTop ℝ))) : ℝ) : WithTop ℝ)
      else ⊤) = ⊤
  simp [htop_notmem, hpreimage, hnotbdd]

/--
At a point strictly below every positive-mass score, the extended finite
Legendre rate is infinite.  Zero-mass labels are ignored.
-/
theorem finiteRateFunctionTop_eq_top_of_support_pos
    (μ : PMF α) (score : α → ℝ)
    (hsupport : ∀ a, 0 < (μ a).toReal → 0 < score a) :
    finiteRateFunctionTop μ score 0 = ⊤ := by
  have hsupport_nonneg :
      ∀ a, 0 < (μ a).toReal → 0 ≤ score a := by
    intro a hmass
    exact (hsupport a hmass).le
  have hzero : AppliedModelingLib.pmfProb μ (fun a => score a = 0) = 0 := by
    refine AppliedModelingLib.pmfProb_eq_zero_of_no_mass μ
      (fun a => score a = 0) ?_
    intro a hscore
    by_cases hmass : 0 < (μ a).toReal
    · have hpos := hsupport a hmass
      exfalso
      exact (lt_irrefl (0 : ℝ)) (by simpa [hscore] using hpos)
    · exact le_antisymm (le_of_not_gt hmass) ENNReal.toReal_nonneg
  have hmgf :
      Filter.Tendsto (fun z : ℝ => finiteMGF μ score z)
        Filter.atBot (nhds 0) := by
    simpa [hzero] using
      finiteMGF_tendsto_pmfProb_score_eq_zero_atBot_of_support_nonneg
        μ score hsupport_nonneg
  have hnotbdd_log : ¬ BddBelow (Set.range fun z : ℝ =>
      finiteLogMGF μ score z) := by
    rw [not_bddBelow_iff]
    intro bound
    rcases (hmgf.eventually_lt_const (Real.exp_pos bound)).exists with
      ⟨z, hz⟩
    refine ⟨finiteLogMGF μ score z, ⟨z, rfl⟩, ?_⟩
    unfold finiteLogMGF
    calc
      Real.log (finiteMGF μ score z) < Real.log (Real.exp bound) :=
        Real.log_lt_log (finiteMGF_pos μ score z) hz
      _ = bound := Real.log_exp bound
  have hnotbdd_leg : ¬ BddAbove (Set.range fun z : ℝ =>
      finiteLegendreValue μ score 0 z) := by
    rw [not_bddAbove_iff]
    intro bound
    rcases (not_bddBelow_iff.mp hnotbdd_log (-bound)) with
      ⟨_, ⟨z, rfl⟩, hz⟩
    refine ⟨finiteLegendreValue μ score 0 z, ⟨z, rfl⟩, ?_⟩
    simp only [finiteLegendreValue]
    linarith
  exact finiteRateFunctionTop_eq_top_of_not_bddAbove μ score 0 hnotbdd_leg

/-- The extended finite Legendre rate is always nonnegative. -/
theorem finiteRateFunctionTop_nonneg
    (μ : PMF α) (score : α → ℝ) (a : ℝ) :
    (0 : WithTop ℝ) ≤ finiteRateFunctionTop μ score a := by
  have hzero := finiteRateFunctionTop_ge_eval μ score a 0
  simpa [finiteLegendreValue, finiteLogMGF_zero] using hzero

/--
The extended finite rate of a law concentrated at one score is zero at that
score.  This handles the degenerate endpoint case without pretending a finite
Legendre dual is stationary.
-/
theorem finiteRateFunctionTop_eq_zero_of_support_score_eq_const
    (μ : PMF α) (score : α → ℝ) (c : ℝ)
    (hconst : ∀ a, 0 < (μ a).toReal → score a = c) :
    finiteRateFunctionTop μ score c = 0 := by
  apply le_antisymm
  · unfold finiteRateFunctionTop
    refine csSup_le (Set.range_nonempty _) ?_
    intro y hy
    rcases hy with ⟨z, rfl⟩
    simp only [finiteLegendreValue]
    rw [finiteLogMGF_eq_mul_of_support_score_eq_const μ score c z hconst]
    norm_num
  · exact finiteRateFunctionTop_nonneg μ score c

/--
Away from its sole positive-support score, a concentrated finite law has
infinite extended Legendre rate.  The proof witnesses arbitrarily large
finite dual values directly.
-/
theorem finiteRateFunctionTop_eq_top_of_support_score_eq_const_of_ne
    (μ : PMF α) (score : α → ℝ) (c x : ℝ)
    (hconst : ∀ a, 0 < (μ a).toReal → score a = c)
    (hxc : x ≠ c) :
    finiteRateFunctionTop μ score x = ⊤ := by
  classical
  unfold finiteRateFunctionTop
  let f : ℝ → ℝ := fun z => finiteLegendreValue μ score x z
  have hsub_ne : x - c ≠ 0 := sub_ne_zero.mpr hxc
  have hnotbdd : ¬ BddAbove (Set.range f) := by
    rw [not_bddAbove_iff]
    intro b
    let z : ℝ := (b + 1) / (x - c)
    refine ⟨f z, ⟨z, rfl⟩, ?_⟩
    have hval : f z = b + 1 := by
      dsimp [f, z]
      simp only [finiteLegendreValue]
      rw [finiteLogMGF_eq_mul_of_support_score_eq_const μ score c
        ((b + 1) / (x - c)) hconst]
      field_simp [hsub_ne]
    rw [hval]
    linarith
  have htop_notmem :
      (⊤ : WithTop ℝ) ∉ Set.range (fun z : ℝ => (f z : WithTop ℝ)) := by
    rintro ⟨z, hz⟩
    exact WithTop.coe_ne_top hz
  have hpreimage :
      ((fun y : ℝ => (y : WithTop ℝ)) ⁻¹'
        Set.range (fun z : ℝ => (f z : WithTop ℝ))) = Set.range f := by
    ext y
    simp
  change
    (if (⊤ : WithTop ℝ) ∈ Set.range (fun z : ℝ => (f z : WithTop ℝ)) then ⊤
      else if BddAbove
        ((fun y : ℝ => (y : WithTop ℝ)) ⁻¹'
          Set.range (fun z : ℝ => (f z : WithTop ℝ))) then
        (↑(sSup ((fun y : ℝ => (y : WithTop ℝ)) ⁻¹'
          Set.range (fun z : ℝ => (f z : WithTop ℝ))) : ℝ) : WithTop ℝ)
      else ⊤) = ⊤
  simp [htop_notmem, hpreimage, hnotbdd]

/--
At the finite lower endpoint of a nonnegative score law, the extended
Legendre rate is the negative logarithm of the zero-score mass.  Unlike the
interior derivative theorem, this result does not require a finite minimizing
dual parameter.
-/
theorem finiteRateFunctionTop_eq_neg_log_pmfProb_score_eq_zero_of_support_nonneg
    (μ : PMF α) (score : α → ℝ)
    (hsupport : ∀ a, 0 < (μ a).toReal → 0 ≤ score a)
    {pZero : ℝ}
    (hpZero : AppliedModelingLib.pmfProb μ (fun a => score a = 0) = pZero)
    (hpZero_pos : 0 < pZero) :
    finiteRateFunctionTop μ score 0 = (-Real.log pZero : WithTop ℝ) := by
  have hmgf :
      Filter.Tendsto (fun z : ℝ => finiteMGF μ score z)
        Filter.atBot
        (nhds pZero) := by
    simpa [hpZero] using
      finiteMGF_tendsto_pmfProb_score_eq_zero_atBot_of_support_nonneg
        μ score hsupport
  have hlog :
      Filter.Tendsto (fun z : ℝ => finiteLogMGF μ score z)
        Filter.atBot
        (nhds (Real.log pZero)) := by
    simpa [finiteLogMGF] using
      (Real.continuousAt_log (ne_of_gt hpZero_pos)).tendsto.comp hmgf
  have hneg :
      Filter.Tendsto (fun z : ℝ => -finiteLogMGF μ score z)
        Filter.atBot
        (nhds (-Real.log pZero)) := by
    simpa using hlog.neg
  have hub :
      BddAbove (Set.range fun z : ℝ => finiteLegendreValue μ score 0 z) := by
    refine ⟨-Real.log pZero, ?_⟩
    intro y hy
    rcases hy with ⟨z, rfl⟩
    have hbound :
        Real.log pZero ≤ finiteLogMGF μ score z := by
      rw [← hpZero]
      unfold finiteLogMGF
      exact Real.log_le_log (by simpa [hpZero] using hpZero_pos)
        (finiteMGF_ge_pmfProb_score_eq_zero μ score z)
    simp only [finiteLegendreValue]
    linarith
  have hrate : finiteRateFunction μ score 0 = -Real.log pZero := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt (Set.range_nonempty _)
    · intro y hy
      rcases hy with ⟨z, rfl⟩
      have hbound :
          Real.log pZero ≤ finiteLogMGF μ score z := by
        rw [← hpZero]
        unfold finiteLogMGF
        exact Real.log_le_log (by simpa [hpZero] using hpZero_pos)
          (finiteMGF_ge_pmfProb_score_eq_zero μ score z)
      simp only [finiteLegendreValue]
      linarith
    · intro w hw
      rcases (hneg.eventually_const_lt hw).exists with ⟨z, hz⟩
      refine ⟨finiteLegendreValue μ score 0 z, ⟨z, rfl⟩, ?_⟩
      simpa [finiteLegendreValue] using hz
  unfold finiteRateFunctionTop
  have hrate_top :
      (finiteRateFunction μ score 0 : WithTop ℝ) =
        (-Real.log pZero : WithTop ℝ) := by
    simpa using congrArg (fun x : ℝ => (x : WithTop ℝ)) hrate
  rw [← hrate_top]
  unfold finiteRateFunction
  change
    sSup (Set.range fun z : ℝ =>
      (finiteLegendreValue μ score 0 z : WithTop ℝ)) =
      ((sSup (Set.range fun z : ℝ => finiteLegendreValue μ score 0 z) : ℝ) : WithTop ℝ)
  rw [show
    Set.range (fun z : ℝ => (finiteLegendreValue μ score 0 z : WithTop ℝ)) =
      (fun x : ℝ => (x : WithTop ℝ)) ''
        Set.range (fun z : ℝ => finiteLegendreValue μ score 0 z) by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨finiteLegendreValue μ score 0 z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, rfl⟩]
  exact (WithTop.coe_sSup' hub).symm

/--
Shifting a score by its displayed threshold leaves the extended Legendre rate
at that threshold unchanged.  This transfers lower-endpoint results from zero
to an arbitrary finite score.
-/
theorem finiteRateFunctionTop_score_eq_shift_at_score
    (μ : PMF α) (score : α → ℝ) (c : ℝ) :
    finiteRateFunctionTop μ score c =
      finiteRateFunctionTop μ (fun a => score a - c) 0 := by
  have hleg : ∀ z : ℝ,
      finiteLegendreValue μ score c z =
        finiteLegendreValue μ (fun a => score a - c) 0 z := by
    intro z
    simp only [finiteLegendreValue]
    rw [finiteLogMGF_sub_const]
    ring
  unfold finiteRateFunctionTop
  congr 1
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, by
      simpa using congrArg (fun q : ℝ => (q : WithTop ℝ)) (hleg z).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, by
      simpa using congrArg (fun q : ℝ => (q : WithTop ℝ)) (hleg z)⟩

/--
Endpoint-rate identity at an arbitrary lower support score.  It is the
score-shifted form of the zero-score endpoint theorem and requires no finite
stationary dual.
-/
theorem finiteRateFunctionTop_eq_neg_log_pmfProb_score_eq_of_support_lower_bound
    (μ : PMF α) (score : α → ℝ) (c : ℝ)
    (hsupport : ∀ a, 0 < (μ a).toReal → c ≤ score a)
    {pMin : ℝ}
    (hpMin : AppliedModelingLib.pmfProb μ (fun a => score a = c) = pMin)
    (hpMin_pos : 0 < pMin) :
    finiteRateFunctionTop μ score c = (-Real.log pMin : WithTop ℝ) := by
  rw [finiteRateFunctionTop_score_eq_shift_at_score]
  apply finiteRateFunctionTop_eq_neg_log_pmfProb_score_eq_zero_of_support_nonneg
  · intro a hmass
    exact sub_nonneg.mpr (hsupport a hmass)
  · simpa [sub_eq_zero] using hpMin
  · exact hpMin_pos

/-- The finite Legendre rate function is nonnegative whenever the supremum is finite. -/
theorem finiteRateFunction_nonneg
    (μ : PMF α) (score : α → ℝ) (a : ℝ)
    (hbdd : BddAbove (Set.range fun z : ℝ =>
      finiteLegendreValue μ score a z)) :
    0 ≤ finiteRateFunction μ score a := by
  have hzero := finiteRateFunction_ge_eval μ score a 0 hbdd
  simpa [finiteLegendreValue, finiteLogMGF_zero] using hzero

/--
The legacy real Legendre wrapper is nonnegative both when its supremum is
bounded and when its default value is used for an unbounded range.
-/
theorem finiteRateFunction_nonneg_or_default
    (μ : PMF α) (score : α → ℝ) (a : ℝ) :
    0 ≤ finiteRateFunction μ score a := by
  by_cases hbdd : BddAbove (Set.range fun z : ℝ =>
      finiteLegendreValue μ score a z)
  · exact finiteRateFunction_nonneg μ score a hbdd
  · rw [finiteRateFunction, Real.sSup_of_not_bddAbove hbdd]

/--
If the finite log-MGF derivative at `z0` is `a`, then the Legendre values at
`a` are bounded above by their value at `z0`.
-/
theorem finiteLegendreValue_bddAbove_of_logMGF_hasDerivAt
    (μ : PMF α) (score : α → ℝ) (a z0 : ℝ)
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) a z0) :
    BddAbove (Set.range fun z : ℝ => finiteLegendreValue μ score a z) := by
  refine ⟨finiteLegendreValue μ score a z0, ?_⟩
  intro y hy
  rcases hy with ⟨z, rfl⟩
  have htangent :=
    convex_tangent_le_of_hasDerivAt
      (finiteLogMGF_convex μ score) hderiv z
  unfold finiteLegendreValue
  linarith

/--
If the finite log-MGF has derivative `a` at `z0`, then the Legendre transform
at `a` is attained at `z0`.
-/
theorem finiteRateFunction_eq_eval_of_logMGF_hasDerivAt
    (μ : PMF α) (score : α → ℝ) (a z0 : ℝ)
    (hbdd : BddAbove (Set.range fun z : ℝ =>
      finiteLegendreValue μ score a z))
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) a z0) :
    finiteRateFunction μ score a =
      finiteLegendreValue μ score a z0 := by
  apply le_antisymm
  · refine csSup_le ⟨finiteLegendreValue μ score a z0, ⟨z0, rfl⟩⟩ ?_
    intro y hy
    rcases hy with ⟨z, rfl⟩
    have htangent :=
      convex_tangent_le_of_hasDerivAt
        (finiteLogMGF_convex μ score) hderiv z
    unfold finiteLegendreValue
    linarith
  · exact finiteRateFunction_ge_eval μ score a z0 hbdd

/--
If the finite log-MGF has derivative `a` at `z0`, then the Legendre transform
at `a` is attained at `z0`; the required boundedness follows from convexity.
-/
theorem finiteRateFunction_eq_eval_of_logMGF_hasDerivAt_no_bdd
    (μ : PMF α) (score : α → ℝ) (a z0 : ℝ)
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) a z0) :
    finiteRateFunction μ score a =
      finiteLegendreValue μ score a z0 :=
  finiteRateFunction_eq_eval_of_logMGF_hasDerivAt
    μ score a z0
    (finiteLegendreValue_bddAbove_of_logMGF_hasDerivAt
      μ score a z0 hderiv)
    hderiv

/--
If the finite log-MGF has derivative `a` at `z0`, then the extended Legendre
rate at `a` is finite and attained at `z0`.
-/
theorem finiteRateFunctionTop_eq_eval_of_logMGF_hasDerivAt
    (μ : PMF α) (score : α → ℝ) (a z0 : ℝ)
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) a z0) :
    finiteRateFunctionTop μ score a =
      (finiteLegendreValue μ score a z0 : WithTop ℝ) := by
  apply le_antisymm
  · refine
      csSup_le
        ⟨(finiteLegendreValue μ score a z0 : WithTop ℝ), ⟨z0, rfl⟩⟩ ?_
    intro y hy
    rcases hy with ⟨z, rfl⟩
    have htangent :=
      convex_tangent_le_of_hasDerivAt
        (finiteLogMGF_convex μ score) hderiv z
    rw [WithTop.coe_le_coe]
    unfold finiteLegendreValue
    linarith
  · exact finiteRateFunctionTop_ge_eval μ score a z0

/--
The Chernoff exponent of the shifted law `score - a` is the finite Legendre
rate at `a` when the original finite log-MGF derivative realizes that rate.
-/
theorem finiteChernoffRate_sub_const_eq_finiteRateFunction_of_logMGF_hasDerivAt
    (μ : PMF α) (score : α → ℝ) (a z0 : ℝ)
    (hbdd : BddAbove (Set.range fun z : ℝ =>
      finiteLegendreValue μ score a z))
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) a z0) :
    finiteChernoffRate μ (fun x => score x - a) =
      finiteRateFunction μ score a := by
  let shifted : α → ℝ := fun x => score x - a
  have hderiv_shift :
      HasDerivAt (fun z : ℝ => finiteLogMGF μ shifted z) 0 z0 := by
    simpa [shifted] using
      finiteLogMGF_sub_const_hasDerivAt_zero μ score hderiv
  have hmin_shift :
      ∀ z : ℝ, finiteLogMGF μ shifted z0 ≤ finiteLogMGF μ shifted z :=
    finiteLogMGF_global_min_of_convex_hasDerivAt_zero
      μ shifted (finiteLogMGF_convex μ shifted) hderiv_shift
  have hchern :
      finiteChernoffRate μ shifted = -finiteLogMGF μ shifted z0 :=
    finiteChernoffRate_eq_neg_of_logMGF_global_min
      μ shifted hmin_shift rfl
  have hrate :
      finiteRateFunction μ score a =
        finiteLegendreValue μ score a z0 :=
    finiteRateFunction_eq_eval_of_logMGF_hasDerivAt
      μ score a z0 hbdd hderiv
  calc
    finiteChernoffRate μ (fun x => score x - a)
        = -finiteLogMGF μ shifted z0 := by
          simpa [shifted] using hchern
    _ = z0 * a - finiteLogMGF μ score z0 := by
          dsimp [shifted]
          rw [finiteLogMGF_sub_const]
          ring
    _ = finiteRateFunction μ score a := by
          rw [hrate]
          simp [finiteLegendreValue]

/--
Version of
`finiteChernoffRate_sub_const_eq_finiteRateFunction_of_logMGF_hasDerivAt`
where Legendre boundedness is derived from the derivative witness.
-/
theorem finiteChernoffRate_sub_const_eq_finiteRateFunction_of_logMGF_hasDerivAt_no_bdd
    (μ : PMF α) (score : α → ℝ) (a z0 : ℝ)
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) a z0) :
    finiteChernoffRate μ (fun x => score x - a) =
      finiteRateFunction μ score a :=
  finiteChernoffRate_sub_const_eq_finiteRateFunction_of_logMGF_hasDerivAt
    μ score a z0
    (finiteLegendreValue_bddAbove_of_logMGF_hasDerivAt
      μ score a z0 hderiv)
    hderiv

/--
The Chernoff exponent of the shifted law `a - score` is the finite Legendre
rate at `a` when the original finite log-MGF derivative realizes that rate at
the flipped dual parameter.
-/
theorem finiteChernoffRate_const_sub_eq_finiteRateFunction_of_logMGF_hasDerivAt
    (μ : PMF α) (score : α → ℝ) (a z0 : ℝ)
    (hbdd : BddAbove (Set.range fun z : ℝ =>
      finiteLegendreValue μ score a z))
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) a (-z0)) :
    finiteChernoffRate μ (fun x => a - score x) =
      finiteRateFunction μ score a := by
  let shifted : α → ℝ := fun x => a - score x
  have hderiv_shift :
      HasDerivAt (fun z : ℝ => finiteLogMGF μ shifted z) 0 z0 := by
    simpa [shifted] using
      finiteLogMGF_const_sub_hasDerivAt_zero μ score hderiv
  have hmin_shift :
      ∀ z : ℝ, finiteLogMGF μ shifted z0 ≤ finiteLogMGF μ shifted z :=
    finiteLogMGF_global_min_of_convex_hasDerivAt_zero
      μ shifted (finiteLogMGF_convex μ shifted) hderiv_shift
  have hchern :
      finiteChernoffRate μ shifted = -finiteLogMGF μ shifted z0 :=
    finiteChernoffRate_eq_neg_of_logMGF_global_min
      μ shifted hmin_shift rfl
  have hrate :
      finiteRateFunction μ score a =
        finiteLegendreValue μ score a (-z0) :=
    finiteRateFunction_eq_eval_of_logMGF_hasDerivAt
      μ score a (-z0) hbdd hderiv
  calc
    finiteChernoffRate μ (fun x => a - score x)
        = -finiteLogMGF μ shifted z0 := by
          simpa [shifted] using hchern
    _ = (-z0) * a - finiteLogMGF μ score (-z0) := by
          dsimp [shifted]
          rw [finiteLogMGF_const_sub]
          ring
    _ = finiteRateFunction μ score a := by
          rw [hrate]
          simp [finiteLegendreValue]

/--
Version of
`finiteChernoffRate_const_sub_eq_finiteRateFunction_of_logMGF_hasDerivAt`
where Legendre boundedness is derived from the derivative witness.
-/
theorem finiteChernoffRate_const_sub_eq_finiteRateFunction_of_logMGF_hasDerivAt_no_bdd
    (μ : PMF α) (score : α → ℝ) (a z0 : ℝ)
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) a (-z0)) :
    finiteChernoffRate μ (fun x => a - score x) =
      finiteRateFunction μ score a :=
  finiteChernoffRate_const_sub_eq_finiteRateFunction_of_logMGF_hasDerivAt
    μ score a z0
    (finiteLegendreValue_bddAbove_of_logMGF_hasDerivAt
      μ score a (-z0) hderiv)
    hderiv

theorem neg_finiteLogMGF_le_finiteChernoffRate
    (μ : PMF α) (score : α → ℝ) (z : ℝ)
    (hbdd : BddBelow (Set.range fun t : ℝ => finiteLogMGF μ score t)) :
    -finiteLogMGF μ score z ≤ finiteChernoffRate μ score := by
  dsimp [finiteChernoffRate]
  exact neg_le_neg (csInf_le hbdd ⟨z, rfl⟩)

/-- MGF of a finite signal's score gap. -/
def finiteScoreGapMGF (μ : PMF α) (hiScore loScore : α → ℝ)
    (z : ℝ) : ℝ :=
  finiteMGF μ (fun a => hiScore a - loScore a) z

/-- Log-MGF of a finite signal's score gap. -/
def finiteScoreGapLogMGF (μ : PMF α) (hiScore loScore : α → ℝ)
    (z : ℝ) : ℝ :=
  finiteLogMGF μ (fun a => hiScore a - loScore a) z

/--
Score-gap form of `finiteLogMGF_bddBelow_of_pos_neg_atoms`.
-/
theorem finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
    (μ : PMF α) (hiScore loScore : α → ℝ)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0) :
    BddBelow (Set.range fun z : ℝ =>
      finiteLogMGF μ (fun a => hiScore a - loScore a) z) :=
  finiteLogMGF_bddBelow_of_pos_neg_atoms
    (μ := μ) (score := fun a => hiScore a - loScore a)
    hmassPos hgapPos hmassNeg hgapNeg

/-- Chernoff exponent for a finite score-gap law after choosing two scores. -/
def finiteScoreGapChernoffRate (μ : PMF α) (hiScore loScore : α → ℝ) :
    ℝ :=
  finiteChernoffRate μ (fun a => hiScore a - loScore a)

/--
Score-gap Chernoff-rate identity from an attained global finite log-MGF
minimum, stated in geometric-base form.
-/
theorem finiteScoreGapChernoffRate_eq_neg_log_base_of_logMGF_global_min
    (μ : PMF α) (hiScore loScore : α → ℝ) {base z0 : ℝ}
    (hmin :
      ∀ z : ℝ,
        Real.log base ≤
          finiteLogMGF μ (fun a => hiScore a - loScore a) z)
    (hwitness :
      finiteLogMGF μ (fun a => hiScore a - loScore a) z0 =
        Real.log base) :
    finiteScoreGapChernoffRate μ hiScore loScore = -Real.log base :=
  finiteChernoffRate_eq_neg_log_base_of_logMGF_global_min
    μ (fun a => hiScore a - loScore a) hmin hwitness

/--
Score-gap Chernoff-rate identity from convexity and a zero derivative at the
proposed minimizing dual parameter.
-/
theorem finiteScoreGapChernoffRate_eq_neg_log_base_of_convex_hasDerivAt_zero
    (μ : PMF α) (hiScore loScore : α → ℝ) {base z0 : ℝ}
    (hconv :
      ConvexOn ℝ Set.univ
        (fun z : ℝ =>
          finiteLogMGF μ (fun a => hiScore a - loScore a) z))
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          finiteLogMGF μ (fun a => hiScore a - loScore a) z)
        0 z0)
    (hwitness :
      finiteLogMGF μ (fun a => hiScore a - loScore a) z0 =
        Real.log base) :
    finiteScoreGapChernoffRate μ hiScore loScore = -Real.log base :=
  finiteChernoffRate_eq_neg_log_base_of_convex_hasDerivAt_zero
    μ (fun a => hiScore a - loScore a) hconv hderiv hwitness

/--
Score-gap Chernoff-rate identity from convexity plus the explicit stationary
equation for the score-gap finite log-MGF.
-/
theorem finiteScoreGapChernoffRate_eq_neg_log_base_of_convex_stationary
    (μ : PMF α) (hiScore loScore : α → ℝ) {base z0 : ℝ}
    (hconv :
      ConvexOn ℝ Set.univ
        (fun z : ℝ =>
          finiteLogMGF μ (fun a => hiScore a - loScore a) z))
    (hstationary :
      (∑ a : α,
        (μ a).toReal *
          ((hiScore a - loScore a) *
            Real.exp (z0 * (hiScore a - loScore a)))) = 0)
    (hwitness :
      finiteLogMGF μ (fun a => hiScore a - loScore a) z0 =
        Real.log base) :
    finiteScoreGapChernoffRate μ hiScore loScore = -Real.log base :=
  finiteChernoffRate_eq_neg_log_base_of_convex_stationary
    μ (fun a => hiScore a - loScore a) hconv hstationary hwitness

theorem finiteScoreGapMGF_pos (μ : PMF α) (hiScore loScore : α → ℝ)
    (z : ℝ) :
    0 < finiteScoreGapMGF μ hiScore loScore z :=
  finiteMGF_pos μ (fun a => hiScore a - loScore a) z

/--
MGF for a ternary score gap taking values `+1`, `0`, and `-1`, where `pUp`
is the probability of `+1` and `pDown` is the probability of `-1`.
This is the algebraic surface behind approval-voting pair rates.
-/
def ternaryGapMGF (pUp pDown z : ℝ) : ℝ :=
  pUp * Real.exp z + pDown * Real.exp (-z) + (1 - pUp - pDown)

/-- Log-MGF for the ternary gap law with values plus one, zero, and minus one. -/
def ternaryGapLogMGF (pUp pDown z : ℝ) : ℝ :=
  Real.log (ternaryGapMGF pUp pDown z)

/--
Identify the finite MGF of a score that only takes values `+1`, `0`, and
`-1` with the ternary approval-gap MGF, from the two nonzero event
probabilities.
-/
theorem finiteMGF_eq_ternaryGapMGF_of_score_eq_ternary
    (μ : PMF α) (score : α → ℝ) {pUp pDown : ℝ}
    (hscore : ∀ a, score a = 1 ∨ score a = 0 ∨ score a = -1)
    (hUp : pmfProb μ (fun a => score a = 1) = pUp)
    (hDown : pmfProb μ (fun a => score a = -1) = pDown)
    (z : ℝ) :
    finiteMGF μ score z = ternaryGapMGF pUp pDown z := by
  classical
  let up : α → Prop := fun a => score a = 1
  let down : α → Prop := fun a => score a = -1
  have hdisjoint : ∀ a, up a → down a → False := by
    intro a hup hdown
    have : (1 : ℝ) = -1 := hup.symm.trans hdown
    norm_num at this
  have hzero_prob :
      pmfProb μ (fun a => ¬up a ∧ ¬down a) = 1 - pUp - pDown := by
    have hsplit :=
      pmfProb_not_and_not_eq_one_sub_add_of_disjoint μ up down hdisjoint
    simpa [up, down, hUp, hDown] using hsplit
  have hpoint :
      ∀ a : α,
        Real.exp (z * score a) =
          (if up a then Real.exp z else 0) +
            (if down a then Real.exp (-z) else 0) +
            (if ¬up a ∧ ¬down a then 1 else 0) := by
    intro a
    by_cases hup : up a
    · have hnot_down : ¬down a := fun hdown => hdisjoint a hup hdown
      simp [up, down, hup, hnot_down]
    · by_cases hdown : down a
      · simp [up, down, hup, hdown]
      · have hzero : score a = 0 := by
          rcases hscore a with hone | hzero | hneg
          · exact False.elim (hup hone)
          · exact hzero
          · exact False.elim (hdown hneg)
        simp [up, down, hup, hdown, hzero]
  unfold finiteMGF ternaryGapMGF
  calc
    ∑ a : α, (μ a).toReal * Real.exp (z * score a)
        = ∑ a : α, (μ a).toReal *
            ((if up a then Real.exp z else 0) +
              (if down a then Real.exp (-z) else 0) +
              (if ¬up a ∧ ¬down a then 1 else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [hpoint a]
    _ =
        ∑ a : α,
          ((μ a).toReal * (if up a then Real.exp z else 0) +
            (μ a).toReal * (if down a then Real.exp (-z) else 0) +
            (μ a).toReal *
              (if ¬up a ∧ ¬down a then 1 else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ =
        (∑ a : α, (μ a).toReal * (if up a then Real.exp z else 0)) +
          (∑ a : α, (μ a).toReal * (if down a then Real.exp (-z) else 0)) +
          (∑ a : α, (μ a).toReal *
            (if ¬up a ∧ ¬down a then 1 else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ =
        Real.exp z * pmfProb μ up +
          Real.exp (-z) * pmfProb μ down +
          pmfProb μ (fun a => ¬up a ∧ ¬down a) := by
          have hup_sum :
              (∑ a : α, (μ a).toReal * (if up a then Real.exp z else 0)) =
                Real.exp z *
                  ∑ a : α, (μ a).toReal * (if up a then 1 else 0) := by
            calc
              ∑ a : α, (μ a).toReal * (if up a then Real.exp z else 0)
                  = ∑ a : α, Real.exp z *
                      ((μ a).toReal * (if up a then 1 else 0)) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    by_cases ha : up a
                    · simp [ha]
                      ring
                    · simp [ha]
              _ = Real.exp z *
                    ∑ a : α, (μ a).toReal * (if up a then 1 else 0) := by
                    rw [Finset.mul_sum]
          have hdown_sum :
              (∑ a : α, (μ a).toReal * (if down a then Real.exp (-z) else 0)) =
                Real.exp (-z) *
                  ∑ a : α, (μ a).toReal * (if down a then 1 else 0) := by
            calc
              ∑ a : α, (μ a).toReal * (if down a then Real.exp (-z) else 0)
                  = ∑ a : α, Real.exp (-z) *
                      ((μ a).toReal * (if down a then 1 else 0)) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    by_cases ha : down a
                    · simp [ha]
                      ring
                    · simp [ha]
              _ = Real.exp (-z) *
                    ∑ a : α, (μ a).toReal * (if down a then 1 else 0) := by
                    rw [Finset.mul_sum]
          unfold pmfProb pmfExp
          rw [hup_sum, hdown_sum]
    _ = pUp * Real.exp z + pDown * Real.exp (-z) + (1 - pUp - pDown) := by
          rw [hzero_prob]
          simp [up, down, hUp, hDown]
          ring

/--
Closed-form Chernoff exponent for a ternary approval gap, in the paper form
`-log(2 sqrt(pUp pDown) + 1 - pUp - pDown)`.
-/
def ternaryGapClosedChernoffRate (pUp pDown : ℝ) : ℝ :=
  -Real.log (2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown)

/--
The dual parameter that minimizes the ternary approval-gap MGF when
`0 < pDown <= pUp`.
-/
def ternaryGapChernoffDual (pUp pDown : ℝ) : ℝ :=
  Real.log (pDown / pUp) / 2

theorem ternaryGapChernoffDual_nonpos
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp) :
    ternaryGapChernoffDual pUp pDown ≤ 0 := by
  have hratio_nonneg : 0 ≤ pDown / pUp :=
    le_of_lt (div_pos hDown hUp)
  have hratio_le_one : pDown / pUp ≤ 1 :=
    div_le_one_of_le₀ hle (le_of_lt hUp)
  have hlog : Real.log (pDown / pUp) ≤ 0 :=
    Real.log_nonpos hratio_nonneg hratio_le_one
  dsimp [ternaryGapChernoffDual]
  linarith

theorem mul_sqrt_div_eq_sqrt_mul_of_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * Real.sqrt (y / x) = Real.sqrt (x * y) := by
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have hy_nonneg : 0 ≤ y := le_of_lt hy
  rw [Real.sqrt_div hy_nonneg x]
  rw [Real.sqrt_mul hx_nonneg y]
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  field_simp [hsx]
  rw [Real.sq_sqrt hx_nonneg]

theorem ternaryGap_exp_chernoffDual
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown) :
    Real.exp (ternaryGapChernoffDual pUp pDown) =
      Real.sqrt (pDown / pUp) := by
  dsimp [ternaryGapChernoffDual]
  rw [← Real.log_sqrt]
  · rw [Real.exp_log]
    exact Real.sqrt_pos.2 (div_pos hDown hUp)
  · exact le_of_lt (div_pos hDown hUp)

theorem ternaryGap_exp_neg_chernoffDual
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown) :
    Real.exp (-(ternaryGapChernoffDual pUp pDown)) =
      Real.sqrt (pUp / pDown) := by
  dsimp [ternaryGapChernoffDual]
  rw [show -(Real.log (pDown / pUp) / 2) =
      Real.log (pUp / pDown) / 2 by
    rw [Real.log_div hDown.ne' hUp.ne',
      Real.log_div hUp.ne' hDown.ne']
    ring]
  rw [← Real.log_sqrt]
  · rw [Real.exp_log]
    exact Real.sqrt_pos.2 (div_pos hUp hDown)
  · exact le_of_lt (div_pos hUp hDown)

theorem ternaryGapMGF_chernoffDual_eq_closed
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown) :
    ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown) =
      2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown := by
  unfold ternaryGapMGF
  rw [ternaryGap_exp_chernoffDual hUp hDown,
    ternaryGap_exp_neg_chernoffDual hUp hDown]
  have htermUp :
      pUp * Real.sqrt (pDown / pUp) = Real.sqrt (pUp * pDown) :=
    mul_sqrt_div_eq_sqrt_mul_of_pos hUp hDown
  have htermDown :
      pDown * Real.sqrt (pUp / pDown) = Real.sqrt (pUp * pDown) := by
    simpa [mul_comm] using
      (mul_sqrt_div_eq_sqrt_mul_of_pos hDown hUp)
  rw [htermUp, htermDown]
  ring

theorem ternaryGapMGF_chernoffDual_pos
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1) :
    0 < ternaryGapMGF pUp pDown
      (ternaryGapChernoffDual pUp pDown) := by
  dsimp [ternaryGapMGF]
  have htermUp :
      0 < pUp * Real.exp (ternaryGapChernoffDual pUp pDown) :=
    mul_pos hUp (Real.exp_pos _)
  have htermDown :
      0 ≤ pDown * Real.exp (-(ternaryGapChernoffDual pUp pDown)) :=
    mul_nonneg (le_of_lt hDown) (Real.exp_pos _).le
  have hrest : 0 ≤ 1 - pUp - pDown := by linarith
  linarith

theorem ternaryGap_closedExpr_pos
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1) :
    0 < 2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown := by
  rw [← ternaryGapMGF_chernoffDual_eq_closed hUp hDown]
  exact ternaryGapMGF_chernoffDual_pos hUp hDown hsum

theorem ternaryGapMGF_chernoffDual_eq_exp_neg_closedRate
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1) :
    ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown) =
      Real.exp (-(ternaryGapClosedChernoffRate pUp pDown)) := by
  rw [ternaryGapMGF_chernoffDual_eq_closed hUp hDown,
    ternaryGapClosedChernoffRate]
  have hpos := ternaryGap_closedExpr_pos hUp hDown hsum
  rw [show -(-Real.log
      (2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown)) =
      Real.log (2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown) by
    ring]
  exact (Real.exp_log hpos).symm

theorem two_mul_sqrt_mul_le_add_of_nonneg {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  have hsqrt_mul : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
    rw [Real.sqrt_mul hx y]
  have hsq : 0 ≤ (Real.sqrt x - Real.sqrt y) ^ 2 := sq_nonneg _
  rw [sub_sq, Real.sq_sqrt hx, Real.sq_sqrt hy] at hsq
  rw [hsqrt_mul]
  nlinarith

theorem ternaryGap_ge_closedExpr
    {pUp pDown z : ℝ} (hUp : 0 ≤ pUp) (hDown : 0 ≤ pDown) :
    2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown ≤
      ternaryGapMGF pUp pDown z := by
  unfold ternaryGapMGF
  have hx : 0 ≤ pUp * Real.exp z :=
    mul_nonneg hUp (Real.exp_pos _).le
  have hy : 0 ≤ pDown * Real.exp (-z) :=
    mul_nonneg hDown (Real.exp_pos _).le
  have hamgm :
      2 * Real.sqrt
          ((pUp * Real.exp z) * (pDown * Real.exp (-z))) ≤
        pUp * Real.exp z + pDown * Real.exp (-z) :=
    two_mul_sqrt_mul_le_add_of_nonneg hx hy
  have hprod :
      (pUp * Real.exp z) * (pDown * Real.exp (-z)) =
        pUp * pDown := by
    have hexp : Real.exp z * Real.exp (-z) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      rw [Real.exp_zero]
    calc
      (pUp * Real.exp z) * (pDown * Real.exp (-z))
          = pUp * pDown * (Real.exp z * Real.exp (-z)) := by ring
      _ = pUp * pDown := by rw [hexp, mul_one]
  rw [hprod] at hamgm
  linarith

theorem ternaryGapMGF_chernoffDual_le
    {pUp pDown z : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown) :
    ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown) ≤
      ternaryGapMGF pUp pDown z := by
  rw [ternaryGapMGF_chernoffDual_eq_closed hUp hDown]
  exact ternaryGap_ge_closedExpr (le_of_lt hUp) (le_of_lt hDown)

theorem ternaryGapLogMGF_chernoffDual_le
    {pUp pDown z : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1) :
    ternaryGapLogMGF pUp pDown (ternaryGapChernoffDual pUp pDown) ≤
      ternaryGapLogMGF pUp pDown z := by
  unfold ternaryGapLogMGF
  have hmin_pos :=
    ternaryGapMGF_chernoffDual_pos hUp hDown hsum
  exact Real.log_le_log hmin_pos
    (ternaryGapMGF_chernoffDual_le hUp hDown)

theorem ternaryGapLogMGF_sInf_eq_chernoffDual
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1) :
    sInf (Set.range fun z : ℝ => ternaryGapLogMGF pUp pDown z) =
      ternaryGapLogMGF pUp pDown
        (ternaryGapChernoffDual pUp pDown) := by
  let low := ternaryGapLogMGF pUp pDown
    (ternaryGapChernoffDual pUp pDown)
  have hbdd :
      BddBelow (Set.range fun z : ℝ => ternaryGapLogMGF pUp pDown z) := by
    refine ⟨low, ?_⟩
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact ternaryGapLogMGF_chernoffDual_le hUp hDown hsum
  have hle :
      sInf (Set.range fun z : ℝ => ternaryGapLogMGF pUp pDown z) ≤
        ternaryGapLogMGF pUp pDown
          (ternaryGapChernoffDual pUp pDown) :=
    csInf_le hbdd ⟨ternaryGapChernoffDual pUp pDown, rfl⟩
  have hge :
      ternaryGapLogMGF pUp pDown
          (ternaryGapChernoffDual pUp pDown) ≤
        sInf (Set.range fun z : ℝ => ternaryGapLogMGF pUp pDown z) := by
    refine le_csInf ⟨ternaryGapLogMGF pUp pDown
      (ternaryGapChernoffDual pUp pDown),
      ⟨ternaryGapChernoffDual pUp pDown, rfl⟩⟩ ?_
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact ternaryGapLogMGF_chernoffDual_le hUp hDown hsum
  exact le_antisymm hle hge

theorem ternaryGapLogMGF_chernoffDual_eq_neg_closedRate
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown) :
    ternaryGapLogMGF pUp pDown
        (ternaryGapChernoffDual pUp pDown) =
      -(ternaryGapClosedChernoffRate pUp pDown) := by
  rw [ternaryGapLogMGF, ternaryGapMGF_chernoffDual_eq_closed hUp hDown,
    ternaryGapClosedChernoffRate]
  ring

theorem ternaryGapClosedChernoffRate_eq_neg_sInf_logMGF
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1) :
    ternaryGapClosedChernoffRate pUp pDown =
      -sInf (Set.range fun z : ℝ => ternaryGapLogMGF pUp pDown z) := by
  rw [ternaryGapLogMGF_sInf_eq_chernoffDual hUp hDown hsum,
    ternaryGapLogMGF_chernoffDual_eq_neg_closedRate hUp hDown]
  ring

/-- Bernoulli KL divergence, written with real arithmetic. -/
def bernoulliKL (a b : ℝ) : ℝ :=
  a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))

/--
Two-population threshold rate used by binary-rating and rating-scale papers:
the two populations are sampled at rates `gHi`, `gLo`, have Bernoulli means
`tHi`, `tLo`, and are compared at threshold `a`.
-/
def twoBernoulliThresholdRate
    (gHi gLo tHi tLo a : ℝ) : ℝ :=
  gHi * bernoulliKL a tHi + gLo * bernoulliKL a tLo

/-- Nonnegative real scaling on `WithTop ℝ`, preserving `⊤`. -/
def withTopRealScale (c : ℝ) (x : WithTop ℝ) : WithTop ℝ :=
  WithTop.map (fun r : ℝ => c * r) x

theorem withTopRealScale_mono_of_nonneg {c : ℝ} (hc : 0 ≤ c) :
    Monotone (withTopRealScale c) := by
  intro x y hxy
  cases x <;> cases y <;> simp [withTopRealScale] at hxy ⊢
  exact_mod_cast (mul_le_mul_of_nonneg_left hxy hc)

/-- Nonnegative scaling preserves nonnegativity for extended real rates. -/
theorem withTopRealScale_nonneg_of_nonneg {c : ℝ} (hc : 0 ≤ c)
    {x : WithTop ℝ} (hx : (0 : WithTop ℝ) ≤ x) :
    (0 : WithTop ℝ) ≤ withTopRealScale c x := by
  cases x with
  | top =>
      simp [withTopRealScale]
  | coe r =>
      have hx_real : 0 ≤ r := by
        exact_mod_cast hx
      have hmul : (0 : WithTop ℝ) ≤ ((c * r : ℝ) : WithTop ℝ) := by
        exact_mod_cast (mul_nonneg hc hx_real)
      simpa [withTopRealScale] using hmul

/-- Nonnegative extended rates are monotone in the real scaling factor. -/
theorem withTopRealScale_le_of_le_of_nonneg {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) {x : WithTop ℝ}
    (hx : (0 : WithTop ℝ) ≤ x) :
    withTopRealScale c x ≤ withTopRealScale d x := by
  cases x with
  | top =>
      simp [withTopRealScale]
  | coe r =>
      have hr : 0 ≤ r := by
        exact_mod_cast hx
      have hmul : c * r ≤ d * r := mul_le_mul_of_nonneg_right hcd hr
      have hmul_top : ((c * r : ℝ) : WithTop ℝ) ≤ ((d * r : ℝ) : WithTop ℝ) := by
        exact_mod_cast hmul
      simpa [withTopRealScale] using hmul_top

/--
Finite signal model for pairwise score-gap LDP calculations, e.g. election
papers comparing the two candidates' per-voter score contributions under a
single finite law.
-/
structure FiniteScoreGapLDPModel (Signal : Type*) [Fintype Signal]
    [DecidableEq Signal] where
  law : PMF Signal
  hiScore : Signal → ℝ
  loScore : Signal → ℝ

namespace FiniteScoreGapLDPModel

variable {Signal : Type*} [Fintype Signal] [DecidableEq Signal]

def gapScore (M : FiniteScoreGapLDPModel Signal) (s : Signal) : ℝ :=
  M.hiScore s - M.loScore s

def mgf (M : FiniteScoreGapLDPModel Signal) (z : ℝ) : ℝ :=
  finiteMGF M.law M.gapScore z

def logMGF (M : FiniteScoreGapLDPModel Signal) (z : ℝ) : ℝ :=
  finiteLogMGF M.law M.gapScore z

def chernoffRate (M : FiniteScoreGapLDPModel Signal) : ℝ :=
  finiteChernoffRate M.law M.gapScore

theorem mgf_pos (M : FiniteScoreGapLDPModel Signal) (z : ℝ) :
    0 < M.mgf z :=
  finiteMGF_pos M.law M.gapScore z

theorem logMGF_zero (M : FiniteScoreGapLDPModel Signal) :
    M.logMGF 0 = 0 :=
  finiteLogMGF_zero M.law M.gapScore

end FiniteScoreGapLDPModel

/--
Finite rating-scale model for large-deviation calculations.  `typeLaw θ` is
the rating distribution for a seller/item of latent type `θ`, and `score`
assigns a real-valued score to each rating category.
-/
structure FiniteRatingLDPModel (θ Rating : Type*) [Fintype Rating]
    [DecidableEq Rating] where
  typeLaw : θ → PMF Rating
  score : Rating → ℝ

namespace FiniteRatingLDPModel

variable {θ Rating : Type*} [Fintype Rating] [DecidableEq Rating]

def mgf (M : FiniteRatingLDPModel θ Rating) (t : θ) (z : ℝ) : ℝ :=
  finiteMGF (M.typeLaw t) M.score z

def logMGF (M : FiniteRatingLDPModel θ Rating) (t : θ) (z : ℝ) : ℝ :=
  finiteLogMGF (M.typeLaw t) M.score z

def rateFunction (M : FiniteRatingLDPModel θ Rating)
    (t : θ) (a : ℝ) : ℝ :=
  finiteRateFunction (M.typeLaw t) M.score a

/--
Extended finite-rating rate function. Thresholds outside the finite score hull
have rate `⊤`, avoiding real-valued supremum boundary cases.
-/
def rateFunctionTop (M : FiniteRatingLDPModel θ Rating)
    (t : θ) (a : ℝ) : WithTop ℝ :=
  finiteRateFunctionTop (M.typeLaw t) M.score a

def pairwiseRateObjective (M : FiniteRatingLDPModel θ Rating)
    (sampleRate : θ → ℝ) (hi lo : θ) (a : ℝ) : ℝ :=
  sampleRate hi * M.rateFunction hi a +
    sampleRate lo * M.rateFunction lo a

/--
Pairwise threshold rate for comparing two finite-rating populations, before a
paper supplies the analytic large-deviation certificate.
-/
def pairwiseThresholdRate (M : FiniteRatingLDPModel θ Rating)
    (sampleRate : θ → ℝ) (hi lo : θ) : ℝ :=
  sInf (Set.range fun a : ℝ =>
    M.pairwiseRateObjective sampleRate hi lo a)

/--
Extended pairwise threshold objective. Out-of-support one-population thresholds
contribute `⊤` instead of forcing the Legendre supremum into a real number.
-/
def pairwiseRateObjectiveTop (M : FiniteRatingLDPModel θ Rating)
    (sampleRate : θ → ℝ) (hi lo : θ) (a : ℝ) : WithTop ℝ :=
  withTopRealScale (sampleRate hi) (M.rateFunctionTop hi a) +
    withTopRealScale (sampleRate lo) (M.rateFunctionTop lo a)

/-- Support-safe `WithTop` version of `pairwiseThresholdRate`. -/
noncomputable def pairwiseThresholdRateTop (M : FiniteRatingLDPModel θ Rating)
    (sampleRate : θ → ℝ) (hi lo : θ) : WithTop ℝ :=
  sInf (Set.range fun a : ℝ =>
    M.pairwiseRateObjectiveTop sampleRate hi lo a)

/-- Every rating has positive probability for every latent type. -/
def fullSupport (M : FiniteRatingLDPModel θ Rating) : Prop :=
  ∀ t r, 0 < (M.typeLaw t r).toReal

/-- Full support supplies positive mass at any requested rating atom. -/
theorem mass_pos_of_fullSupport (M : FiniteRatingLDPModel θ Rating)
    (hfull : M.fullSupport) (t : θ) (r : Rating) :
    0 < (M.typeLaw t r).toReal :=
  hfull t r

/--
A finite rating law places positive mass on both sides of a threshold score.
This is the reusable nondegeneracy condition used by finite empirical-type
Cramer lower bounds in rating-system papers.
-/
def straddlesThreshold (M : FiniteRatingLDPModel θ Rating)
    (t : θ) (a : ℝ) : Prop :=
  (∃ rBelow : Rating, 0 < (M.typeLaw t rBelow).toReal ∧ M.score rBelow < a) ∧
    (∃ rAbove : Rating, 0 < (M.typeLaw t rAbove).toReal ∧ a < M.score rAbove)

theorem mgf_pos (M : FiniteRatingLDPModel θ Rating)
    (t : θ) (z : ℝ) :
    0 < M.mgf t z :=
  finiteMGF_pos (M.typeLaw t) M.score z

theorem logMGF_zero (M : FiniteRatingLDPModel θ Rating)
    (t : θ) :
    M.logMGF t 0 = 0 :=
  finiteLogMGF_zero (M.typeLaw t) M.score

theorem exp_logMGF (M : FiniteRatingLDPModel θ Rating)
    (t : θ) (z : ℝ) :
    Real.exp (M.logMGF t z) = M.mgf t z :=
  exp_finiteLogMGF (M.typeLaw t) M.score z

/--
If the finite log-MGF has derivative `a` at `z0`, then the extended rate at
threshold `a` is finite and attained at `z0`.
-/
theorem rateFunctionTop_eq_eval_of_logMGF_hasDerivAt
    (M : FiniteRatingLDPModel θ Rating) (t : θ) (a z0 : ℝ)
    (hderiv : HasDerivAt (fun z : ℝ => M.logMGF t z) a z0) :
    M.rateFunctionTop t a =
      (finiteLegendreValue (M.typeLaw t) M.score a z0 : WithTop ℝ) := by
  simpa [rateFunctionTop, FiniteRatingLDPModel.logMGF] using
    finiteRateFunctionTop_eq_eval_of_logMGF_hasDerivAt
      (M.typeLaw t) M.score a z0 hderiv

/-- The extended pairwise source objective is nonnegative for nonnegative rates. -/
theorem pairwiseRateObjectiveTop_nonneg
    (M : FiniteRatingLDPModel θ Rating) (sampleRate : θ → ℝ)
    (hi lo : θ) (a : ℝ)
    (hgHi : 0 ≤ sampleRate hi) (hgLo : 0 ≤ sampleRate lo) :
    (0 : WithTop ℝ) ≤ M.pairwiseRateObjectiveTop sampleRate hi lo a := by
  have hhi :
      (0 : WithTop ℝ) ≤
        withTopRealScale (sampleRate hi) (M.rateFunctionTop hi a) :=
    withTopRealScale_nonneg_of_nonneg hgHi
      (finiteRateFunctionTop_nonneg (M.typeLaw hi) M.score a)
  have hlo :
      (0 : WithTop ℝ) ≤
        withTopRealScale (sampleRate lo) (M.rateFunctionTop lo a) :=
    withTopRealScale_nonneg_of_nonneg hgLo
      (finiteRateFunctionTop_nonneg (M.typeLaw lo) M.score a)
  simpa [pairwiseRateObjectiveTop] using add_nonneg hhi hlo

/--
The support-safe pairwise source objective is monotone in the two sample-rate
weights. This is useful when a paper replaces a continuum sample rate by an
interval lower bound.
-/
theorem pairwiseRateObjectiveTop_le_of_sampleRate_le
    (M : FiniteRatingLDPModel θ Rating) {sampleRate sampleRate' : θ → ℝ}
    (hi lo : θ) (a : ℝ)
    (hgHi : 0 ≤ sampleRate hi) (hgLo : 0 ≤ sampleRate lo)
    (hhi_le : sampleRate hi ≤ sampleRate' hi)
    (hlo_le : sampleRate lo ≤ sampleRate' lo) :
    M.pairwiseRateObjectiveTop sampleRate hi lo a ≤
      M.pairwiseRateObjectiveTop sampleRate' hi lo a := by
  have hhi :
      withTopRealScale (sampleRate hi) (M.rateFunctionTop hi a) ≤
        withTopRealScale (sampleRate' hi) (M.rateFunctionTop hi a) :=
    withTopRealScale_le_of_le_of_nonneg hgHi hhi_le
      (finiteRateFunctionTop_nonneg (M.typeLaw hi) M.score a)
  have hlo :
      withTopRealScale (sampleRate lo) (M.rateFunctionTop lo a) ≤
        withTopRealScale (sampleRate' lo) (M.rateFunctionTop lo a) :=
    withTopRealScale_le_of_le_of_nonneg hgLo hlo_le
      (finiteRateFunctionTop_nonneg (M.typeLaw lo) M.score a)
  simpa [pairwiseRateObjectiveTop] using add_le_add hhi hlo

/--
The support-safe pairwise threshold exponent is bounded above by the
support-safe objective at any displayed threshold.
-/
theorem pairwiseThresholdRateTop_le_pairwiseRateObjectiveTop
    (M : FiniteRatingLDPModel θ Rating) (sampleRate : θ → ℝ)
    (hi lo : θ) (a : ℝ)
    (hgHi : 0 ≤ sampleRate hi) (hgLo : 0 ≤ sampleRate lo) :
    M.pairwiseThresholdRateTop sampleRate hi lo ≤
      M.pairwiseRateObjectiveTop sampleRate hi lo a := by
  unfold pairwiseThresholdRateTop
  have hbdd :
      BddBelow
        (Set.range fun b : ℝ =>
          M.pairwiseRateObjectiveTop sampleRate hi lo b) := by
    refine ⟨(0 : WithTop ℝ), ?_⟩
    intro z hz
    rcases hz with ⟨b, rfl⟩
    exact M.pairwiseRateObjectiveTop_nonneg sampleRate hi lo b hgHi hgLo
  exact csInf_le hbdd ⟨a, rfl⟩

/--
Increasing both sample-rate weights can only increase the support-safe
pairwise threshold exponent.
-/
theorem pairwiseThresholdRateTop_le_of_sampleRate_le
    (M : FiniteRatingLDPModel θ Rating) {sampleRate sampleRate' : θ → ℝ}
    (hi lo : θ)
    (hgHi : 0 ≤ sampleRate hi) (hgLo : 0 ≤ sampleRate lo)
    (hhi_le : sampleRate hi ≤ sampleRate' hi)
    (hlo_le : sampleRate lo ≤ sampleRate' lo) :
    M.pairwiseThresholdRateTop sampleRate hi lo ≤
      M.pairwiseThresholdRateTop sampleRate' hi lo := by
  unfold pairwiseThresholdRateTop
  have hnonempty :
      (Set.range fun a : ℝ =>
        M.pairwiseRateObjectiveTop sampleRate' hi lo a).Nonempty :=
    ⟨M.pairwiseRateObjectiveTop sampleRate' hi lo 0, ⟨0, rfl⟩⟩
  refine le_csInf hnonempty ?_
  intro y hy
  rcases hy with ⟨a, rfl⟩
  have hbdd :
      BddBelow
        (Set.range fun b : ℝ =>
          M.pairwiseRateObjectiveTop sampleRate hi lo b) := by
    refine ⟨(0 : WithTop ℝ), ?_⟩
    intro z hz
    rcases hz with ⟨b, rfl⟩
    exact M.pairwiseRateObjectiveTop_nonneg sampleRate hi lo b hgHi hgLo
  exact
    (csInf_le hbdd ⟨a, rfl⟩).trans
      (M.pairwiseRateObjectiveTop_le_of_sampleRate_le hi lo a
        hgHi hgLo hhi_le hlo_le)

/--
If a displayed common threshold minimizes the pairwise source objective over
all thresholds, then evaluating at that threshold realizes the threshold rate.
-/
theorem pairwiseThresholdRate_eq_of_pairwiseRateObjective_minimizer
    (M : FiniteRatingLDPModel θ Rating) (sampleRate : θ → ℝ)
    (hi lo : θ) (a : ℝ)
    (hmin :
      ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate hi lo a ≤
          M.pairwiseRateObjective sampleRate hi lo b) :
    M.pairwiseRateObjective sampleRate hi lo a =
      M.pairwiseThresholdRate sampleRate hi lo := by
  unfold pairwiseThresholdRate
  have hnonempty :
      (Set.range fun b : ℝ => M.pairwiseRateObjective sampleRate hi lo b).Nonempty :=
    ⟨M.pairwiseRateObjective sampleRate hi lo a, ⟨a, rfl⟩⟩
  have hbdd :
      BddBelow
        (Set.range fun b : ℝ => M.pairwiseRateObjective sampleRate hi lo b) := by
    refine ⟨M.pairwiseRateObjective sampleRate hi lo a, ?_⟩
    intro y hy
    rcases hy with ⟨b, rfl⟩
    exact hmin b
  have hle_inf :
      M.pairwiseRateObjective sampleRate hi lo a ≤
        sInf (Set.range fun b : ℝ =>
          M.pairwiseRateObjective sampleRate hi lo b) := by
    refine le_csInf hnonempty ?_
    intro y hy
    rcases hy with ⟨b, rfl⟩
    exact hmin b
  have hinf_le :
      sInf (Set.range fun b : ℝ =>
          M.pairwiseRateObjective sampleRate hi lo b) ≤
        M.pairwiseRateObjective sampleRate hi lo a :=
    csInf_le hbdd ⟨a, rfl⟩
  exact le_antisymm hle_inf hinf_le

end FiniteRatingLDPModel

end

end Probability
end AppliedModelingLib
