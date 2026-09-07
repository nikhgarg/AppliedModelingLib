import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import AppliedModelingLib.Foundations.Optimization.Endpoint
import AppliedModelingLib.Foundations.Optimization.EntropyRegularized
import AppliedModelingLib.Foundations.Probability.ExponentialTilt
import AppliedModelingLib.Foundations.Probability.Weighted
import AppliedModelingLib.Learning.Online.Basic

/-!
# Finite Hedge updates

This module gives the reusable single-step and finite-list iteration behind
Hedge.  The source-paper interface will use its multiplicative discount
notation; the implementation is deliberately an exponential tilt so that the
same normalization and support facts are shared with the entropy-regularized
optimization core.

## Main declarations

- `hedgeStep`
- `hedgeStep_apply_toReal`
- `hedgeStep_fullSupport`
- `hedgeIterate`
-/

namespace AppliedModelingLib
namespace Learning
namespace Online

/-- One normalized Hedge update with positive multiplicative discount. -/
noncomputable def hedgeStep
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (current : PMF Action) (loss : Action → ℝ) (discount : ℝ) : PMF Action :=
  exponentialTilt current loss (Real.log discount)

/-- Hedge's normalized multiplicative update, written in real-mass form. -/
theorem hedgeStep_apply_toReal
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (current : PMF Action) (loss : Action → ℝ) (discount : ℝ)
    (hdiscount : 0 < discount) (action : Action) :
    (hedgeStep current loss discount action).toReal =
      (current action).toReal * discount ^ (loss action) /
        Probability.finiteMGF current loss (Real.log discount) := by
  unfold hedgeStep
  rw [exponentialTilt_apply_toReal, Real.rpow_def_of_pos hdiscount]

/-- A positive Hedge discount preserves full support of the current distribution. -/
theorem hedgeStep_fullSupport
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (current : PMF Action) (loss : Action → ℝ) (discount : ℝ)
    (hcurrent : PMFFullSupport current) :
    PMFFullSupport (hedgeStep current loss discount) := by
  unfold hedgeStep
  exact exponentialTilt_fullSupport current loss (Real.log discount) hcurrent

/--
Hedge's normalized update is the entropy-regularized optimizer with score
`loss` and inverse temperature `log discount`.  In the usual Hedge range
`0 < discount < 1`, that coefficient is negative, so maximizing this objective
penalizes rather than rewards loss.
-/
theorem exponentialTiltObjective_le_at_hedgeStep
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (current candidate : PMF Action) (loss : Action → ℝ) (discount : ℝ)
    (hcurrent : PMFFullSupport current) :
    exponentialTiltObjective current candidate loss (Real.log discount) ≤
      exponentialTiltObjective current (hedgeStep current loss discount) loss
        (Real.log discount) := by
  simpa [hedgeStep] using
    exponentialTiltObjective_le_at_exponentialTilt
      current candidate loss (Real.log discount) hcurrent

/-- Discount one leaves a Hedge iterate unchanged. -/
theorem hedgeStep_one
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (current : PMF Action) (loss : Action → ℝ) :
    hedgeStep current loss 1 = current := by
  unfold hedgeStep
  simpa using exponentialTilt_zero current loss

/--
The convex-chord inequality behind multiplicative-weight updates: on losses in
`[0, 1]`, every positive base lies below the linear interpolation of its values
at zero and one.  The statement deliberately allows bases above one, as arise
in adaptive boosting when a weak hypothesis has error above one half.
-/
theorem rpow_le_linear_interpolation
    (base exponent : ℝ) (hbase : 0 < base)
    (hexponent_nonneg : 0 ≤ exponent) (hexponent_one : exponent ≤ 1) :
    base ^ exponent ≤ 1 - (1 - base) * exponent := by
  have hchord := (convexOn_rpow_left hbase).2
    (show (0 : ℝ) ∈ Set.univ by simp)
    (show (1 : ℝ) ∈ Set.univ by simp)
    (show 0 ≤ 1 - exponent by linarith) hexponent_nonneg (by ring)
  calc
    base ^ exponent =
        base ^ ((1 - exponent) • (0 : ℝ) + exponent • (1 : ℝ)) := by
          simp [smul_eq_mul]
    _ ≤ (1 - exponent) • base ^ (0 : ℝ) + exponent • base ^ (1 : ℝ) := hchord
    _ = 1 - (1 - base) * exponent := by
          simp [smul_eq_mul]
          ring

/--
The chord inequality used in Freund--Schapire (1997), Eq. (3): on losses in
`[0, 1]`, a positive discount at most one lies below its linear interpolation
between the endpoint values.
-/
theorem hedge_discount_rpow_le_linear
    (discount loss : ℝ) (hdiscount : 0 < discount) (_hdiscount_one : discount ≤ 1)
    (hloss_nonneg : 0 ≤ loss) (hloss_one : loss ≤ 1) :
    discount ^ loss ≤ 1 - (1 - discount) * loss :=
  rpow_le_linear_interpolation discount loss hdiscount hloss_nonneg hloss_one

/--
The rational logarithmic upper bound used in the proof sketch of
Freund--Schapire (1997), Lemma 4.  It is recorded separately so source
learning-rate choices can reuse the exact estimate rather than a weaker
generic logarithm bound.
-/
theorem hedge_neg_log_le_quadratic
    {discount : ℝ} (hdiscount : 0 < discount) (hdiscount_one : discount ≤ 1) :
    -Real.log discount ≤ (1 - discount ^ 2) / (2 * discount) := by
  let f : ℝ → ℝ := fun x => ((1 : ℝ) / 2) * (1 / x) - ((1 : ℝ) / 2) * x + Real.log x
  have hderivAt : ∀ x : ℝ, 0 < x →
      HasDerivAt f (-((x - 1) ^ 2) / (2 * x ^ 2)) x := by
    intro x hx
    have hinv : HasDerivAt (fun z : ℝ => ((1 : ℝ) / 2) * (1 / z))
        (((1 : ℝ) / 2) * (-1 / x ^ 2)) x := by
      simpa [one_div, id] using
        ((hasDerivAt_id x).inv hx.ne').const_mul ((1 : ℝ) / 2)
    have hlinear : HasDerivAt (fun z : ℝ => ((1 : ℝ) / 2) * z)
        (((1 : ℝ) / 2) * 1) x := by
      simpa using (hasDerivAt_id x).const_mul ((1 : ℝ) / 2)
    have hlog : HasDerivAt Real.log (1 / x) x := by
      simpa [one_div] using Real.hasDerivAt_log hx.ne'
    convert (hinv.sub hlinear).add hlog using 1
    all_goals field_simp [hx.ne']; ring
  have hcontinuous : ContinuousOn f (Set.Icc discount 1) := by
    intro x hx
    exact (hderivAt x (lt_of_lt_of_le hdiscount hx.1)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo discount 1,
      HasDerivAt f (-((x - 1) ^ 2) / (2 * x ^ 2)) x := by
    intro x hx
    exact hderivAt x (lt_trans hdiscount hx.1)
  have hderiv_nonpos : ∀ x ∈ Set.Ioo discount 1,
      -((x - 1) ^ 2) / (2 * x ^ 2) ≤ 0 := by
    intro x hx
    have hxpos : 0 < x := lt_trans hdiscount hx.1
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg (x - 1)))
      (by positivity)
  have hendpoint := AppliedModelingLib.Optimization.endpoint_path_ge_of_hasDerivAt_nonpos_on_Icc
    (f := f) (f' := fun x => -((x - 1) ^ 2) / (2 * x ^ 2)) hdiscount_one
    hcontinuous hderiv hderiv_nonpos
  have hrewrite :
      ((1 : ℝ) / 2) * (1 / discount) - ((1 : ℝ) / 2) * discount + Real.log discount =
        (1 - discount ^ 2) / (2 * discount) + Real.log discount := by
    field_simp [hdiscount.ne']
  change f 1 ≤ f discount at hendpoint
  dsimp [f] at hendpoint
  norm_num at hendpoint
  rw [show
    ((1 : ℝ) / 2) * discount⁻¹ - ((1 : ℝ) / 2) * discount + Real.log discount =
      (1 - discount ^ 2) / (2 * discount) + Real.log discount by
        simpa [one_div] using hrewrite] at hendpoint
  linarith

/--
The source learning-rate choice `g(\bar L / \bar R)` from Freund--Schapire
(1997), Lemma 4, written in the algebraically equivalent form
`1 / (1 + sqrt (2 * \bar R / \bar L))`.
-/
noncomputable def hedgeDiscountFromBounds (lossBound regretBound : ℝ) : ℝ :=
  1 / (1 + Real.sqrt (2 * regretBound / lossBound))

/--
The continuous zero-loss-bound extension of the source learning-rate choice.
The displayed formula in Lemma 4 has an interior quotient; when `lossBound = 0`
we use its limiting discount `0` rather than Lean's totalized quotient.
-/
noncomputable def hedgeDiscountFromBoundsClosed (lossBound regretBound : ℝ) : ℝ := by
  classical
  exact if lossBound = 0 then 0 else hedgeDiscountFromBounds lossBound regretBound

/--
Freund--Schapire (1997), Lemma 4 in its finite real-valued interior regime.
The source writes `0 ≤ L ≤ \bar L` and `0 < R ≤ \bar R`; the explicit
`0 < lossBound` premise is needed to make its prescribed discount an interior
real number rather than a limiting boundary expression.
-/
theorem hedge_learning_rate_bound
    {loss lossBound regret regretBound : ℝ}
    (hloss_nonneg : 0 ≤ loss) (hloss_le : loss ≤ lossBound)
    (hregret_pos : 0 < regret) (hregret_le : regret ≤ regretBound)
    (hlossBound_pos : 0 < lossBound) :
    (-loss * Real.log (hedgeDiscountFromBounds lossBound regretBound) + regret) /
        (1 - hedgeDiscountFromBounds lossBound regretBound) ≤
      loss + Real.sqrt (2 * lossBound * regretBound) + regret := by
  let s : ℝ := Real.sqrt (2 * regretBound / lossBound)
  let discount : ℝ := 1 / (1 + s)
  change (-loss * Real.log discount + regret) / (1 - discount) ≤
    loss + Real.sqrt (2 * lossBound * regretBound) + regret
  have hregretBound_pos : 0 < regretBound := lt_of_lt_of_le hregret_pos hregret_le
  have hratio_pos : 0 < 2 * regretBound / lossBound := by positivity
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr hratio_pos
  have hs_sq : s ^ 2 = 2 * regretBound / lossBound := by
    dsimp [s]
    exact Real.sq_sqrt hratio_pos.le
  have hdenom_pos : 0 < 1 + s := by linarith
  have hdenom_ne : 1 + s ≠ 0 := hdenom_pos.ne'
  have hdiscount_pos : 0 < discount := by
    dsimp [discount]
    exact one_div_pos.mpr hdenom_pos
  have hdiscount_lt_one : discount < 1 := by
    dsimp [discount]
    exact (div_lt_one₀ hdenom_pos).mpr (by linarith)
  have hscale_sq : (lossBound * s) ^ 2 = 2 * lossBound * regretBound := by
    calc
      (lossBound * s) ^ 2 = lossBound ^ 2 * s ^ 2 := by ring
      _ = 2 * lossBound * regretBound := by
        rw [hs_sq]
        field_simp [hlossBound_pos.ne']
  have hroot_arg_nonneg : 0 ≤ 2 * lossBound * regretBound := by positivity
  have hroot_eq : Real.sqrt (2 * lossBound * regretBound) = lossBound * s := by
    have hroot_nonneg : 0 ≤ Real.sqrt (2 * lossBound * regretBound) := Real.sqrt_nonneg _
    have hscale_nonneg : 0 ≤ lossBound * s :=
      mul_nonneg hlossBound_pos.le hs_pos.le
    nlinarith [Real.sq_sqrt hroot_arg_nonneg, hscale_sq]
  have hscale_relation : lossBound * s ^ 2 = 2 * regretBound := by
    calc
      lossBound * s ^ 2 = lossBound * (2 * regretBound / lossBound) := by rw [hs_sq]
      _ = 2 * regretBound := by
        field_simp [hlossBound_pos.ne']
  have hregretBound_div : regretBound / s = lossBound * s / 2 := by
    apply (div_eq_iff hs_pos.ne').mpr
    nlinarith [hscale_relation]
  have hloss_ratio :
      ((1 - discount ^ 2) / (2 * discount)) / (1 - discount) = 1 + s / 2 := by
    dsimp [discount]
    field_simp [hs_pos.ne', hdenom_ne]; ring
  have hregret_ratio : regret / (1 - discount) = regret + regret / s := by
    dsimp [discount]
    field_simp [hs_pos.ne', hdenom_ne]; ring
  have hlog := hedge_neg_log_le_quadratic hdiscount_pos hdiscount_lt_one.le
  have hlog_scaled :
      -loss * Real.log discount ≤ loss * ((1 - discount ^ 2) / (2 * discount)) := by
    calc
      -loss * Real.log discount = loss * (-Real.log discount) := by ring
      _ ≤ loss * ((1 - discount ^ 2) / (2 * discount)) :=
        mul_le_mul_of_nonneg_left hlog hloss_nonneg
  have hdenominator_pos : 0 < 1 - discount := by linarith
  have hloss_scaled : loss * (s / 2) ≤ lossBound * (s / 2) :=
    mul_le_mul_of_nonneg_right hloss_le (by linarith)
  have hregret_scaled : regret / s ≤ regretBound / s :=
    div_le_div_of_nonneg_right hregret_le hs_pos.le
  calc
    (-loss * Real.log discount + regret) / (1 - discount) =
        (-loss * Real.log discount) / (1 - discount) + regret / (1 - discount) := by
          ring
    _ ≤ (loss * ((1 - discount ^ 2) / (2 * discount))) / (1 - discount) +
          regret / (1 - discount) :=
      add_le_add (div_le_div_of_nonneg_right hlog_scaled hdenominator_pos.le) le_rfl
    _ = loss * (1 + s / 2) + (regret + regret / s) := by
      calc
        (loss * ((1 - discount ^ 2) / (2 * discount))) / (1 - discount) +
            regret / (1 - discount) =
            loss * (((1 - discount ^ 2) / (2 * discount)) / (1 - discount)) +
              regret / (1 - discount) := by ring
        _ = loss * (1 + s / 2) + (regret + regret / s) := by
          rw [hloss_ratio, hregret_ratio]
    _ = loss + loss * (s / 2) + regret + regret / s := by ring
    _ ≤ loss + lossBound * (s / 2) + regret + regretBound / s := by linarith
    _ = loss + Real.sqrt (2 * lossBound * regretBound) + regret := by
      rw [hroot_eq, hregretBound_div]
      ring

/--
Closed-boundary extension of the Lemma-4 learning-rate inequality. In the
`lossBound = 0` branch, the source premises force `loss = 0`, and the
continuous-extension choice `discount = 0` gives the claimed bound exactly.
The positive-bound branch is the source's checked interior theorem.
-/
theorem hedge_learning_rate_bound_closed
    {loss lossBound regret regretBound : ℝ}
    (hloss_nonneg : 0 ≤ loss) (hloss_le : loss ≤ lossBound)
    (hregret_pos : 0 < regret) (hregret_le : regret ≤ regretBound) :
    (-loss * Real.log (hedgeDiscountFromBoundsClosed lossBound regretBound) + regret) /
        (1 - hedgeDiscountFromBoundsClosed lossBound regretBound) ≤
      loss + Real.sqrt (2 * lossBound * regretBound) + regret := by
  have hlossBound_nonneg : 0 ≤ lossBound := le_trans hloss_nonneg hloss_le
  by_cases hzero : lossBound = 0
  · have hloss_zero : loss = 0 := by linarith
    simp [hedgeDiscountFromBoundsClosed, hzero, hloss_zero]
  · have hlossBound_pos : 0 < lossBound := lt_of_le_of_ne hlossBound_nonneg (Ne.symm hzero)
    simpa [hedgeDiscountFromBoundsClosed, hzero] using
      hedge_learning_rate_bound hloss_nonneg hloss_le hregret_pos hregret_le hlossBound_pos

/--
One normalized Hedge step has the potential upper bound obtained by averaging
the source paper's Eq. (3).  It is the one-round form of the potential estimate
used in Lemma 1.
-/
theorem hedge_one_step_potential_upper
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (current : PMF Action) (loss : Action → ℝ) (discount : ℝ)
    (hdiscount : 0 < discount) (hdiscount_one : discount ≤ 1)
    (hloss_nonneg : ∀ action, 0 ≤ loss action)
    (hloss_one : ∀ action, loss action ≤ 1) :
    pmfExp current (fun action => discount ^ (loss action)) ≤
      1 - (1 - discount) * pmfExp current loss := by
  calc
    pmfExp current (fun action => discount ^ (loss action)) ≤
        pmfExp current (fun action => 1 - (1 - discount) * loss action) :=
      pmfExp_le_pmfExp_of_forall_le current _ _ fun action =>
        hedge_discount_rpow_le_linear discount (loss action) hdiscount hdiscount_one
          (hloss_nonneg action) (hloss_one action)
    _ = pmfExp current (fun _ => 1) -
          pmfExp current (fun action => (1 - discount) * loss action) := by
      rw [pmfExp_sub]
    _ = 1 - (1 - discount) * pmfExp current loss := by
      rw [pmfExp_const, pmfExp_const_mul]

/--
The same one-step potential calculation without the `discount ≤ 1` restriction.
Convexity of the real-power curve is sufficient for the chord inequality, so
this form also supports adaptive boosting rounds whose source update factor is
above one.
-/
theorem hedge_one_step_potential_upper_of_pos
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (current : PMF Action) (loss : Action → ℝ) (discount : ℝ)
    (hdiscount : 0 < discount)
    (hloss_nonneg : ∀ action, 0 ≤ loss action)
    (hloss_one : ∀ action, loss action ≤ 1) :
    pmfExp current (fun action => discount ^ (loss action)) ≤
      1 - (1 - discount) * pmfExp current loss := by
  calc
    pmfExp current (fun action => discount ^ (loss action)) ≤
        pmfExp current (fun action => 1 - (1 - discount) * loss action) :=
      pmfExp_le_pmfExp_of_forall_le current _ _ fun action =>
        rpow_le_linear_interpolation discount (loss action) hdiscount
          (hloss_nonneg action) (hloss_one action)
    _ = pmfExp current (fun _ => 1) -
          pmfExp current (fun action => (1 - discount) * loss action) := by
      rw [pmfExp_sub]
    _ = 1 - (1 - discount) * pmfExp current loss := by
      rw [pmfExp_const, pmfExp_const_mul]

/--
The logarithmic one-step potential estimate following Eq. (4) in
Freund--Schapire (1997).  The source's endpoint notation is made explicit as
the real-valued interior regime `0 < discount ≤ 1`.
-/
theorem hedge_one_step_log_potential_upper
    {Action : Type*} [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (current : PMF Action) (loss : Action → ℝ) (discount : ℝ)
    (hdiscount : 0 < discount) (hdiscount_one : discount ≤ 1)
    (hloss_nonneg : ∀ action, 0 ≤ loss action)
    (hloss_one : ∀ action, loss action ≤ 1) :
    Real.log (pmfExp current (fun action => discount ^ (loss action))) ≤
      -(1 - discount) * pmfExp current loss := by
  have hpotential := hedge_one_step_potential_upper current loss discount hdiscount
    hdiscount_one hloss_nonneg hloss_one
  have hpositive : 0 < pmfExp current (fun action => discount ^ (loss action)) :=
    pmfExp_pos_of_support_forall_pos current _ fun action _ =>
      Real.rpow_pos_of_pos hdiscount _
  exact (Real.log_le_sub_one_of_pos hpositive).trans (by linarith)

/--
The product of normalized Hedge partition factors along a finite loss path.
For the source algorithm, this is the total unnormalized weight relative to a
probability-normalized initial vector.
-/
noncomputable def hedgePotential
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (discount : ℝ) : PMF Action → List (Action → ℝ) → ℝ
  | _, [] => 1
  | current, loss :: remaining =>
      pmfExp current (fun action => discount ^ (loss action)) *
        hedgePotential discount (hedgeStep current loss discount) remaining

/-- The cumulative expected loss along the normalized Hedge trajectory. -/
noncomputable def hedgeCumulativeExpectedLoss
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (discount : ℝ) : PMF Action → List (Action → ℝ) → ℝ
  | _, [] => 0
  | current, loss :: remaining =>
      pmfExp current loss +
        hedgeCumulativeExpectedLoss discount (hedgeStep current loss discount) remaining

/-- Positive discounts make every finite Hedge potential strictly positive. -/
theorem hedgePotential_pos
    {Action : Type*} [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (current : PMF Action)
    (losses : List (Action → ℝ)) :
    0 < hedgePotential discount current losses := by
  induction losses generalizing current with
  | nil => simp [hedgePotential]
  | cons loss remaining ih =>
      simp only [hedgePotential]
      exact mul_pos
        (pmfExp_pos_of_support_forall_pos current _ fun action _ =>
          Real.rpow_pos_of_pos hdiscount _)
        (ih (hedgeStep current loss discount))

/--
Finite-list version of the normalized potential estimate underlying Lemma 1.
The direct source-weight formulation and its paper-facing specialization appear
below as `hedgeWeightState_log_total_upper` and
`hedgeWeightState_lemma1_finite`.
-/
theorem hedge_logPotential_upper
    {Action : Type*} [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_one : discount ≤ 1)
    (current : PMF Action) (losses : List (Action → ℝ))
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1) :
    Real.log (hedgePotential discount current losses) ≤
      -(1 - discount) * hedgeCumulativeExpectedLoss discount current losses := by
  induction losses generalizing current with
  | nil => simp [hedgePotential, hedgeCumulativeExpectedLoss]
  | cons loss remaining ih =>
      have hloss_head : ∀ action, 0 ≤ loss action ∧ loss action ≤ 1 :=
        hloss loss (by simp)
      have hloss_remaining :
          ∀ later ∈ remaining, ∀ action, 0 ≤ later action ∧ later action ≤ 1 := by
        intro later hmem action
        exact hloss later (by simp [hmem]) action
      have hstep := hedge_one_step_log_potential_upper current loss discount hdiscount
        hdiscount_one (fun action => (hloss_head action).1)
        (fun action => (hloss_head action).2)
      have hinduction := ih (hedgeStep current loss discount) hloss_remaining
      have hfactor_pos :
          0 < pmfExp current (fun action => discount ^ (loss action)) :=
        pmfExp_pos_of_support_forall_pos current _ fun action _ =>
          Real.rpow_pos_of_pos hdiscount _
      have hremaining_pos :
          0 < hedgePotential discount (hedgeStep current loss discount) remaining :=
        hedgePotential_pos discount hdiscount (hedgeStep current loss discount) remaining
      calc
        Real.log (hedgePotential discount current (loss :: remaining)) =
            Real.log (pmfExp current (fun action => discount ^ (loss action))) +
              Real.log (hedgePotential discount (hedgeStep current loss discount) remaining) := by
                rw [hedgePotential, Real.log_mul hfactor_pos.ne' hremaining_pos.ne']
        _ ≤ -(1 - discount) * pmfExp current loss +
              -(1 - discount) *
                hedgeCumulativeExpectedLoss discount (hedgeStep current loss discount) remaining :=
              add_le_add hstep hinduction
        _ = -(1 - discount) * hedgeCumulativeExpectedLoss discount current
              (loss :: remaining) := by
                rw [hedgeCumulativeExpectedLoss]
                ring

/--
An unnormalized finite Hedge weight vector with the nonnegativity and positive
total-mass invariants used by the source algorithm.
-/
structure HedgeWeightState (Action : Type*) [Fintype Action] where
  weight : Action → ℝ
  nonneg : ∀ action, 0 ≤ weight action
  total_pos : 0 < ∑ action, weight action

/-- Normalize an unnormalized Hedge weight state into the allocation in Fig. 1. -/
noncomputable def HedgeWeightState.policy
    {Action : Type*} [Fintype Action] (state : HedgeWeightState Action) : PMF Action :=
  finiteWeightedPMF state.weight state.nonneg state.total_pos

/-- The real mass of a Hedge allocation is its source weight divided by total mass. -/
theorem HedgeWeightState.policy_apply_toReal
    {Action : Type*} [Fintype Action] (state : HedgeWeightState Action) (action : Action) :
    (state.policy action).toReal = state.weight action / ∑ other, state.weight other := by
  exact finiteWeightedPMF_apply_toReal state.weight state.nonneg state.total_pos action

/-- Every normalized Hedge allocation mass is nonnegative. -/
theorem HedgeWeightState.policy_nonneg
    {Action : Type*} [Fintype Action] (state : HedgeWeightState Action) (action : Action) :
    0 ≤ (state.policy action).toReal :=
  ENNReal.toReal_nonneg

/-- The normalized Hedge allocation has total real mass one. -/
theorem HedgeWeightState.policy_toReal_sum
    {Action : Type*} [Fintype Action] (state : HedgeWeightState Action) :
    ∑ action, (state.policy action).toReal = 1 := by
  classical
  exact pmfToRealSum state.policy

/-- The expected value under the allocation obtained by normalizing source weights. -/
noncomputable def HedgeWeightState.expectation
    {Action : Type*} [Fintype Action]
    (state : HedgeWeightState Action) (quantity : Action → ℝ) : ℝ := by
  classical
  exact pmfExp state.policy quantity

/--
The weighted total after a source multiplicative update factors into its old
total mass and the normalized one-step potential.
-/
theorem hedgeWeightState_weighted_potential_eq
    {Action : Type*} [Fintype Action]
    (state : HedgeWeightState Action) (loss : Action → ℝ) (discount : ℝ) :
    (∑ action, state.weight action * discount ^ (loss action)) =
      (∑ action, state.weight action) *
        state.expectation (fun action => discount ^ (loss action)) := by
  classical
  unfold HedgeWeightState.expectation
  unfold HedgeWeightState.policy
  rw [finiteWeightedPMF_pmfExp_eq_sum_div]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro action _
  field_simp [state.total_pos.ne']

/-- Apply the source multiplicative weight update to an unnormalized state. -/
noncomputable def hedgeWeightStateStep
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (state : HedgeWeightState Action) (loss : Action → ℝ) (discount : ℝ)
    (hdiscount : 0 < discount) : HedgeWeightState Action := by
  classical
  refine
    { weight := fun action => state.weight action * discount ^ (loss action)
      nonneg := fun action =>
        mul_nonneg (state.nonneg action) (Real.rpow_pos_of_pos hdiscount _).le
      total_pos := ?_ }
  rw [hedgeWeightState_weighted_potential_eq]
  exact mul_pos state.total_pos
    (by
      unfold HedgeWeightState.expectation
      exact pmfExp_pos_of_support_forall_pos state.policy _ fun action _ =>
        Real.rpow_pos_of_pos hdiscount _)

/-- The exact total-mass recurrence for Figure 1's multiplicative update. -/
theorem hedgeWeightStateStep_total
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (state : HedgeWeightState Action) (loss : Action → ℝ) (discount : ℝ)
    (hdiscount : 0 < discount) :
    (∑ action, (hedgeWeightStateStep state loss discount hdiscount).weight action) =
      (∑ action, state.weight action) *
        state.expectation (fun action => discount ^ (loss action)) := by
  classical
  simpa [hedgeWeightStateStep] using
    hedgeWeightState_weighted_potential_eq state loss discount

/-- A strictly positive source weight remains strictly positive after one Hedge update. -/
theorem hedgeWeightStateStep_weight_pos
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (state : HedgeWeightState Action) (loss : Action → ℝ) (discount : ℝ)
    (hdiscount : 0 < discount) (action : Action) (hweight : 0 < state.weight action) :
    0 < (hedgeWeightStateStep state loss discount hdiscount).weight action := by
  simpa [hedgeWeightStateStep] using
    mul_pos hweight (Real.rpow_pos_of_pos hdiscount (loss action))

/--
Normalizing the source multiplicative update gives exactly the exponential-tilt
Hedge policy.  This identifies the Figure 1 weight recursion with the shared
normalized update used by the finite online-learning API.
-/
theorem hedgeWeightStateStep_policy_eq_hedgeStep
    {Action : Type*} [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (state : HedgeWeightState Action) (loss : Action → ℝ) (discount : ℝ)
    (hdiscount : 0 < discount) :
    (hedgeWeightStateStep state loss discount hdiscount).policy =
      hedgeStep state.policy loss discount := by
  have hpotential_pos :
      0 < state.expectation (fun action => discount ^ (loss action)) := by
    unfold HedgeWeightState.expectation
    exact pmfExp_pos_of_support_forall_pos state.policy _ fun action _ =>
      Real.rpow_pos_of_pos hdiscount _
  have hmgf :
      Probability.finiteMGF state.policy loss (Real.log discount) =
        state.expectation (fun action => discount ^ (loss action)) := by
    unfold Probability.finiteMGF HedgeWeightState.expectation pmfExp
    refine Finset.sum_congr rfl fun action _ => ?_
    change (state.policy action).toReal * Real.exp (Real.log discount * loss action) =
      (state.policy action).toReal * discount ^ (loss action)
    rw [Real.rpow_def_of_pos hdiscount]
  apply PMF.ext
  intro action
  apply (ENNReal.toReal_eq_toReal_iff'
    ((hedgeWeightStateStep state loss discount hdiscount).policy.apply_ne_top action)
    ((hedgeStep state.policy loss discount).apply_ne_top action)).mp
  rw [HedgeWeightState.policy_apply_toReal,
    hedgeStep_apply_toReal state.policy loss discount hdiscount action,
    hedgeWeightStateStep_total, hmgf, HedgeWeightState.policy_apply_toReal]
  simp only [hedgeWeightStateStep]
  field_simp [state.total_pos.ne', hpotential_pos.ne']

/-- Execute a finite sequence of source Hedge weight updates. -/
noncomputable def hedgeWeightStateRun
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) :
    HedgeWeightState Action → List (Action → ℝ) → HedgeWeightState Action
  | state, [] => state
  | state, loss :: remaining =>
      hedgeWeightStateRun discount hdiscount
        (hedgeWeightStateStep state loss discount hdiscount) remaining

/--
After a finite source Hedge run, each weight is its initial value times the
discount raised to that action's cumulative realized loss.
-/
theorem hedgeWeightStateRun_weight
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (state : HedgeWeightState Action)
    (losses : List (Action → ℝ)) (action : Action) :
    (hedgeWeightStateRun discount hdiscount state losses).weight action =
      state.weight action * discount ^ ((losses.map fun loss => loss action).sum) := by
  induction losses generalizing state with
  | nil => simp [hedgeWeightStateRun]
  | cons loss remaining ih =>
      rw [hedgeWeightStateRun, ih]
      simp only [hedgeWeightStateStep, List.map_cons, List.sum_cons]
      rw [mul_assoc]
      rw [← Real.rpow_add hdiscount]

/--
After any finite source Hedge run, normalizing its weights is exactly the
exponential tilt of the initial allocation by that action's cumulative loss.
-/
theorem hedgeWeightStateRun_policy_eq_exponentialTilt
    {Action : Type*} [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (state : HedgeWeightState Action)
    (losses : List (Action → ℝ)) :
    (hedgeWeightStateRun discount hdiscount state losses).policy =
      exponentialTilt state.policy
        (fun action => (losses.map fun loss => loss action).sum)
        (Real.log discount) := by
  let cumulativeLoss : Action → ℝ :=
    fun action => (losses.map fun loss => loss action).sum
  have hmgf :
      Probability.finiteMGF state.policy cumulativeLoss (Real.log discount) =
        state.expectation (fun action => discount ^ (cumulativeLoss action)) := by
    unfold Probability.finiteMGF HedgeWeightState.expectation pmfExp
    refine Finset.sum_congr rfl fun action _ => ?_
    change (state.policy action).toReal * Real.exp (Real.log discount * cumulativeLoss action) =
      (state.policy action).toReal * discount ^ (cumulativeLoss action)
    rw [Real.rpow_def_of_pos hdiscount]
  have htotal :
      (∑ action, (hedgeWeightStateRun discount hdiscount state losses).weight action) =
        (∑ action, state.weight action) *
          Probability.finiteMGF state.policy cumulativeLoss (Real.log discount) := by
    calc
      (∑ action, (hedgeWeightStateRun discount hdiscount state losses).weight action) =
          ∑ action, state.weight action * discount ^ (cumulativeLoss action) := by
            refine Finset.sum_congr rfl fun action _ => ?_
            rw [hedgeWeightStateRun_weight]
      _ = (∑ action, state.weight action) *
          state.expectation (fun action => discount ^ (cumulativeLoss action)) :=
        hedgeWeightState_weighted_potential_eq state cumulativeLoss discount
      _ = (∑ action, state.weight action) *
          Probability.finiteMGF state.policy cumulativeLoss (Real.log discount) := by
        rw [hmgf]
  apply PMF.ext
  intro action
  apply (ENNReal.toReal_eq_toReal_iff'
    ((hedgeWeightStateRun discount hdiscount state losses).policy.apply_ne_top action)
    ((exponentialTilt state.policy cumulativeLoss (Real.log discount)).apply_ne_top action)).mp
  rw [HedgeWeightState.policy_apply_toReal,
    exponentialTilt_apply_toReal, HedgeWeightState.policy_apply_toReal, htotal,
    hedgeWeightStateRun_weight, Real.rpow_def_of_pos hdiscount]
  field_simp [state.total_pos.ne',
    (Probability.finiteMGF_pos state.policy cumulativeLoss (Real.log discount)).ne']; ring

/-- Positive initial source weights remain positive throughout every finite Hedge run. -/
theorem hedgeWeightStateRun_weight_pos
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (state : HedgeWeightState Action)
    (losses : List (Action → ℝ)) (action : Action) (hweight : 0 < state.weight action) :
    0 < (hedgeWeightStateRun discount hdiscount state losses).weight action := by
  rw [hedgeWeightStateRun_weight]
  exact mul_pos hweight (Real.rpow_pos_of_pos hdiscount _)

/-- A zero initial source weight remains zero throughout every finite Hedge run. -/
theorem hedgeWeightStateRun_weight_eq_zero
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (state : HedgeWeightState Action)
    (losses : List (Action → ℝ)) (action : Action) (hweight : state.weight action = 0) :
    (hedgeWeightStateRun discount hdiscount state losses).weight action = 0 := by
  rw [hedgeWeightStateRun_weight, hweight, zero_mul]

/--
A selected set has zero total source weight exactly when it has zero total
weight after a finite positive-discount Hedge run.

This is the finite algebraic support fact behind the vacuous extended-real
reading of the source's subset bound when its initial selected mass is zero.
-/
theorem hedgeWeightStateRun_selected_weight_sum_eq_zero_iff
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (state : HedgeWeightState Action)
    (losses : List (Action → ℝ)) (selected : Finset Action) :
    (∑ action ∈ selected, state.weight action) = 0 ↔
      (∑ action ∈ selected,
        (hedgeWeightStateRun discount hdiscount state losses).weight action) = 0 := by
  constructor
  · intro hinitial
    rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun action haction =>
        (hedgeWeightStateRun discount hdiscount state losses).nonneg action)]
    intro action haction
    exact hedgeWeightStateRun_weight_eq_zero discount hdiscount state losses action
      ((Finset.sum_eq_zero_iff_of_nonneg (fun other hother => state.nonneg other)).mp hinitial
        action haction)
  · intro hfinal
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun action haction => state.nonneg action)]
    intro action haction
    have hrun_zero :
        (hedgeWeightStateRun discount hdiscount state losses).weight action = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun other hother =>
          (hedgeWeightStateRun discount hdiscount state losses).nonneg other)).mp hfinal
        action haction
    rw [hedgeWeightStateRun_weight] at hrun_zero
    exact (mul_eq_zero.mp hrun_zero).resolve_right
      (Real.rpow_pos_of_pos hdiscount _).ne'

/-- A final source weight is bounded above by the final total weight. -/
theorem hedgeWeightStateRun_weight_le_total
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (state : HedgeWeightState Action)
    (losses : List (Action → ℝ)) (action : Action) :
    (hedgeWeightStateRun discount hdiscount state losses).weight action ≤
      ∑ other, (hedgeWeightStateRun discount hdiscount state losses).weight other := by
  classical
  exact Finset.single_le_sum
    (fun other _ => (hedgeWeightStateRun discount hdiscount state losses).nonneg other)
    (Finset.mem_univ action)

/--
The final total source weight is at least the contribution of any initially
positive action, written in the logarithmic form used in the comparator proof.
-/
theorem hedgeWeightState_log_total_lower_of_positive_initial
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (state : HedgeWeightState Action)
    (losses : List (Action → ℝ)) (action : Action)
    (hweight : 0 < state.weight action) :
    Real.log (state.weight action) +
        (losses.map fun loss => loss action).sum * Real.log discount ≤
      Real.log
        (∑ other, (hedgeWeightStateRun discount hdiscount state losses).weight other) := by
  have hfinal_weight :
      0 < (hedgeWeightStateRun discount hdiscount state losses).weight action := by
    rw [hedgeWeightStateRun_weight]
    exact mul_pos hweight (Real.rpow_pos_of_pos hdiscount _)
  have hlog := Real.log_le_log hfinal_weight
    (hedgeWeightStateRun_weight_le_total discount hdiscount state losses action)
  rw [hedgeWeightStateRun_weight, Real.log_mul hweight.ne'
    (Real.rpow_pos_of_pos hdiscount _).ne', Real.log_rpow hdiscount] at hlog
  exact hlog

/--
The final total source weight is at least the aggregate contribution of a
nonempty finite comparator set.  This is the logarithmic lower-potential step
in Freund--Schapire (1997), Theorem 2, Eq. (8).  The source's zero-mass case is
expressed with extended-real logarithms; this reusable real-valued lemma keeps
the precisely necessary positive initial subset-mass assumption explicit.
-/
theorem hedgeWeightState_log_total_lower_of_subset_positive_initial
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1)
    (state : HedgeWeightState Action) (losses : List (Action → ℝ))
    (selected : Finset Action) (hselected : selected.Nonempty)
    (hweight : 0 < ∑ action ∈ selected, state.weight action) :
    Real.log (∑ action ∈ selected, state.weight action) +
        (selected.sup' hselected (fun action =>
          (losses.map fun loss => loss action).sum)) * Real.log discount ≤
      Real.log
        (∑ action, (hedgeWeightStateRun discount hdiscount state losses).weight action) := by
  classical
  let cumulativeLoss : Action → ℝ :=
    fun action => (losses.map fun loss => loss action).sum
  let maxSelectedLoss : ℝ := selected.sup' hselected cumulativeLoss
  have hterm : ∀ action ∈ selected,
      discount ^ maxSelectedLoss * state.weight action ≤
        (hedgeWeightStateRun discount hdiscount state losses).weight action := by
    intro action haction
    rw [hedgeWeightStateRun_weight]
    rw [mul_comm (discount ^ maxSelectedLoss)]
    apply mul_le_mul_of_nonneg_left
    · exact Real.rpow_le_rpow_of_exponent_ge hdiscount hdiscount_lt_one.le
        (show cumulativeLoss action ≤ maxSelectedLoss from
          Finset.le_sup' (s := selected) (f := cumulativeLoss) haction)
    · exact state.nonneg action
  have hselected_sum :
      discount ^ maxSelectedLoss * (∑ action ∈ selected, state.weight action) ≤
        ∑ action ∈ selected,
          (hedgeWeightStateRun discount hdiscount state losses).weight action := by
    calc
      discount ^ maxSelectedLoss * (∑ action ∈ selected, state.weight action) =
          ∑ action ∈ selected, discount ^ maxSelectedLoss * state.weight action := by
            rw [Finset.mul_sum]
      _ ≤ ∑ action ∈ selected,
          (hedgeWeightStateRun discount hdiscount state losses).weight action :=
        Finset.sum_le_sum fun action haction => hterm action haction
  have htotal_lower :
      discount ^ maxSelectedLoss * (∑ action ∈ selected, state.weight action) ≤
        ∑ action, (hedgeWeightStateRun discount hdiscount state losses).weight action :=
    hselected_sum.trans <|
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
        (fun action _ _ =>
          (hedgeWeightStateRun discount hdiscount state losses).nonneg action)
  have hproduct_pos :
      0 < discount ^ maxSelectedLoss * (∑ action ∈ selected, state.weight action) :=
    mul_pos (Real.rpow_pos_of_pos hdiscount _) hweight
  have hlog := Real.log_le_log hproduct_pos htotal_lower
  rw [Real.log_mul (Real.rpow_pos_of_pos hdiscount _).ne' hweight.ne',
    Real.log_rpow hdiscount] at hlog
  change Real.log (∑ action ∈ selected, state.weight action) +
      maxSelectedLoss * Real.log discount ≤ _
  linarith

/-- Cumulative allocation loss along a finite source Hedge trajectory. -/
noncomputable def hedgeWeightStateCumulativeLoss
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) :
    HedgeWeightState Action → List (Action → ℝ) → ℝ
  | _, [] => 0
  | state, loss :: remaining =>
      by
        classical
        exact state.expectation loss +
          hedgeWeightStateCumulativeLoss discount hdiscount
            (hedgeWeightStateStep state loss discount hdiscount) remaining

/--
The source Lemma 1 potential estimate for a finite trajectory, before fixing
the initial total mass to one.  The right side keeps the initial log mass
visible so the induction states exactly the multiplicative-weight invariant.
-/
theorem hedgeWeightState_log_total_upper
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_one : discount ≤ 1)
    (state : HedgeWeightState Action) (losses : List (Action → ℝ))
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1) :
    Real.log
        (∑ action, (hedgeWeightStateRun discount hdiscount state losses).weight action) ≤
      Real.log (∑ action, state.weight action) -
        (1 - discount) * hedgeWeightStateCumulativeLoss discount hdiscount state losses := by
  classical
  induction losses generalizing state with
  | nil => simp [hedgeWeightStateRun, hedgeWeightStateCumulativeLoss]
  | cons loss remaining ih =>
      have hloss_head : ∀ action, 0 ≤ loss action ∧ loss action ≤ 1 :=
        hloss loss (by simp)
      have hloss_remaining :
          ∀ later ∈ remaining, ∀ action, 0 ≤ later action ∧ later action ≤ 1 := by
        intro later hmem action
        exact hloss later (by simp [hmem]) action
      have hstep := hedge_one_step_log_potential_upper state.policy loss discount hdiscount
        hdiscount_one (fun action => (hloss_head action).1)
        (fun action => (hloss_head action).2)
      have hstep_source :
          Real.log (state.expectation (fun action => discount ^ (loss action))) ≤
            -(1 - discount) * state.expectation loss := by
        simpa only [HedgeWeightState.expectation] using hstep
      have hinduction := ih (hedgeWeightStateStep state loss discount hdiscount)
        hloss_remaining
      have hfactor_pos :
          0 < state.expectation (fun action => discount ^ (loss action)) := by
        unfold HedgeWeightState.expectation
        exact pmfExp_pos_of_support_forall_pos state.policy _ fun action _ =>
          Real.rpow_pos_of_pos hdiscount _
      calc
        Real.log
            (∑ action,
              (hedgeWeightStateRun discount hdiscount state (loss :: remaining)).weight action) =
            Real.log
              (∑ action,
                (hedgeWeightStateRun discount hdiscount
                  (hedgeWeightStateStep state loss discount hdiscount) remaining).weight action) :=
              rfl
        _ ≤ Real.log
              (∑ action, (hedgeWeightStateStep state loss discount hdiscount).weight action) -
            (1 - discount) *
              hedgeWeightStateCumulativeLoss discount hdiscount
                (hedgeWeightStateStep state loss discount hdiscount) remaining :=
              hinduction
        _ = (Real.log (∑ action, state.weight action) +
              Real.log (state.expectation (fun action => discount ^ (loss action)))) -
            (1 - discount) *
              hedgeWeightStateCumulativeLoss discount hdiscount
                (hedgeWeightStateStep state loss discount hdiscount) remaining := by
              rw [hedgeWeightStateStep_total state loss discount hdiscount,
                Real.log_mul state.total_pos.ne' hfactor_pos.ne']
        _ ≤ (Real.log (∑ action, state.weight action) -
              (1 - discount) * state.expectation loss) -
            (1 - discount) *
              hedgeWeightStateCumulativeLoss discount hdiscount
                (hedgeWeightStateStep state loss discount hdiscount) remaining := by
              linarith
        _ = Real.log (∑ action, state.weight action) -
            (1 - discount) * hedgeWeightStateCumulativeLoss discount hdiscount state
              (loss :: remaining) := by
              rw [hedgeWeightStateCumulativeLoss]
              ring

/--
Finite source specialization of Freund--Schapire (1997), Lemma 1: when the
initial Hedge weights sum to one, the log of the final unnormalized total
weight is bounded by the cumulative allocation loss.
-/
theorem hedgeWeightState_lemma1_finite
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_one : discount ≤ 1)
    (state : HedgeWeightState Action) (hinitial : (∑ action, state.weight action) = 1)
    (losses : List (Action → ℝ))
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1) :
    Real.log
        (∑ action, (hedgeWeightStateRun discount hdiscount state losses).weight action) ≤
      -(1 - discount) * hedgeWeightStateCumulativeLoss discount hdiscount state losses := by
  classical
  calc
    Real.log
        (∑ action, (hedgeWeightStateRun discount hdiscount state losses).weight action) ≤
        Real.log (∑ action, state.weight action) -
          (1 - discount) * hedgeWeightStateCumulativeLoss discount hdiscount state losses :=
      hedgeWeightState_log_total_upper discount hdiscount hdiscount_one state losses hloss
    _ = -(1 - discount) * hedgeWeightStateCumulativeLoss discount hdiscount state losses := by
      rw [hinitial, Real.log_one]
      ring

/--
Finite single-comparator specialization of Freund--Schapire (1997), Theorem 2.
The comparator's initial weight is assumed positive so its logarithmic prior
term is a finite real number.
-/
theorem hedgeWeightState_theorem2_single_finite
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1)
    (state : HedgeWeightState Action) (hinitial : (∑ action, state.weight action) = 1)
    (losses : List (Action → ℝ))
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1)
    (action : Action) (hweight : 0 < state.weight action) :
    hedgeWeightStateCumulativeLoss discount hdiscount state losses ≤
      (-Real.log (state.weight action) -
          (losses.map fun loss => loss action).sum * Real.log discount) /
        (1 - discount) := by
  have hupper := hedgeWeightState_lemma1_finite discount hdiscount hdiscount_lt_one.le
    state hinitial losses hloss
  have hlower := hedgeWeightState_log_total_lower_of_positive_initial discount hdiscount
    state losses action hweight
  have hcoefficient : 0 < 1 - discount := by linarith
  rw [le_div_iff₀ hcoefficient]
  linarith

/--
Finite real-valued subset-comparator specialization of Freund--Schapire
(1997), Theorem 2, Eq. (8).  The paper uses extended-real notation when the
initial subset mass is zero; the explicit positivity premise is the exact
finite-real boundary of this theorem.
-/
theorem hedgeWeightState_theorem2_subset_finite
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1)
    (state : HedgeWeightState Action) (hinitial : (∑ action, state.weight action) = 1)
    (losses : List (Action → ℝ))
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1)
    (selected : Finset Action) (hselected : selected.Nonempty)
    (hweight : 0 < ∑ action ∈ selected, state.weight action) :
    hedgeWeightStateCumulativeLoss discount hdiscount state losses ≤
      (-Real.log (∑ action ∈ selected, state.weight action) -
          (selected.sup' hselected (fun action =>
            (losses.map fun loss => loss action).sum)) * Real.log discount) /
        (1 - discount) := by
  classical
  have hupper := hedgeWeightState_lemma1_finite discount hdiscount hdiscount_lt_one.le
    state hinitial losses hloss
  have hlower := hedgeWeightState_log_total_lower_of_subset_positive_initial
    discount hdiscount hdiscount_lt_one state losses selected hselected hweight
  have hcoefficient : 0 < 1 - discount := by linarith
  rw [le_div_iff₀ hcoefficient]
  linarith

/--
The extended-real right-hand side of Freund--Schapire (1997), Theorem 2,
Eq. (8).  Within the theorem's nonnegative-weight model, a zero selected
initial mass has source penalty `-log 0 = +∞`; otherwise this is the printed
finite-real quotient.  The definition spells out that single infinite branch
instead of silently using Lean's totalized `Real.log 0`.
-/
noncomputable def hedgeWeightStateSubsetComparatorExtendedBound
    (discount initialSelectedMass maxSelectedLoss : ℝ) : EReal :=
  if initialSelectedMass = 0 then ⊤ else
    ((-Real.log initialSelectedMass - maxSelectedLoss * Real.log discount) /
      (1 - discount) : ℝ)

/--
Finite extended-real specialization of Freund--Schapire (1997), Theorem 2,
Eq. (8), including its zero-initial-subset-mass boundary.  The zero branch is
vacuous for the source reason `-log 0 = +∞`; positive mass reduces exactly to
the real-valued comparator theorem.
-/
theorem hedgeWeightState_theorem2_subset_extendedReal
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1)
    (state : HedgeWeightState Action) (hinitial : (∑ action, state.weight action) = 1)
    (losses : List (Action → ℝ))
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1)
    (selected : Finset Action) (hselected : selected.Nonempty) :
    (hedgeWeightStateCumulativeLoss discount hdiscount state losses : EReal) ≤
      hedgeWeightStateSubsetComparatorExtendedBound discount
        (∑ action ∈ selected, state.weight action)
        (selected.sup' hselected (fun action =>
          (losses.map fun loss => loss action).sum)) := by
  classical
  let initialSelectedMass : ℝ := ∑ action ∈ selected, state.weight action
  let maxSelectedLoss : ℝ := selected.sup' hselected
    (fun action => (losses.map fun loss => loss action).sum)
  by_cases hzero : initialSelectedMass = 0
  · rw [hedgeWeightStateSubsetComparatorExtendedBound, if_pos hzero]
    exact le_top
  · rw [hedgeWeightStateSubsetComparatorExtendedBound, if_neg hzero]
    apply EReal.coe_le_coe_iff.mpr
    have hmass_nonneg : 0 ≤ initialSelectedMass := by
      dsimp [initialSelectedMass]
      exact Finset.sum_nonneg fun action _ => state.nonneg action
    have hmass_pos : 0 < initialSelectedMass :=
      lt_of_le_of_ne hmass_nonneg (Ne.symm hzero)
    exact hedgeWeightState_theorem2_subset_finite discount hdiscount hdiscount_lt_one
      state hinitial losses hloss selected hselected (by simpa [initialSelectedMass] using hmass_pos)

/--
Finite equal-prior form of Freund--Schapire (1997), Theorem 2, Eq. (9).  The
minimum comparator loss is represented by the infimum over the finite action
set, while `huniform` makes the source initialization `w¹_i = 1 / N`
explicit.
-/
theorem hedgeWeightState_theorem2_uniform_best_finite
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1)
    (state : HedgeWeightState Action)
    (huniform : ∀ action, state.weight action = 1 / (Fintype.card Action : ℝ))
    (losses : List (Action → ℝ))
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1) :
    hedgeWeightStateCumulativeLoss discount hdiscount state losses ≤
      ((Finset.univ.inf' Finset.univ_nonempty
          (fun action => (losses.map fun loss => loss action).sum)) *
          Real.log (1 / discount) + Real.log (Fintype.card Action : ℝ)) /
        (1 - discount) := by
  classical
  have hcard_pos : 0 < (Fintype.card Action : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Action)
  have hinitial : (∑ action, state.weight action) = 1 := by
    calc
      (∑ action, state.weight action) =
          ∑ action, 1 / (Fintype.card Action : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro action _
            exact huniform action
      _ = (Fintype.card Action : ℝ) * (1 / (Fintype.card Action : ℝ)) := by
            simp [nsmul_eq_mul]
      _ = 1 := by field_simp [hcard_pos.ne']
  obtain ⟨best, _hbest_mem, hbest⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset Action))
      (H := Finset.univ_nonempty)
      (f := fun action => (losses.map fun loss => loss action).sum)
  have hbest_weight : 0 < state.weight best := by
    rw [huniform best]
    exact one_div_pos.mpr hcard_pos
  have hsingle := hedgeWeightState_theorem2_single_finite discount hdiscount hdiscount_lt_one
    state hinitial losses hloss best hbest_weight
  calc
    hedgeWeightStateCumulativeLoss discount hdiscount state losses ≤
        (-Real.log (state.weight best) -
            (losses.map fun loss => loss best).sum * Real.log discount) /
          (1 - discount) := hsingle
    _ = ((Finset.univ.inf' Finset.univ_nonempty
          (fun action => (losses.map fun loss => loss action).sum)) *
          Real.log (1 / discount) + Real.log (Fintype.card Action : ℝ)) /
        (1 - discount) := by
      rw [huniform best]
      simp only [one_div, Real.log_inv]
      rw [← hbest]
      ring

/--
The conventional square-root-loss corollary of the equal-prior Hedge bound.
For a nonempty loss path and at least two actions, the source Lemma-4
discount with `lossBound = path.length` and `regretBound = log |Action|`
turns Theorem 2's exact finite bound into an `O(sqrt(T log |Action|))`
comparison with the best fixed action.
-/
theorem hedgeWeightState_uniform_tuned_regret_bound
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (state : HedgeWeightState Action)
    (huniform : ∀ action, state.weight action = 1 / (Fintype.card Action : ℝ))
    (losses : List (Action → ℝ))
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1)
    (lossBound : ℝ)
    (hbest_le_bound :
      Finset.univ.inf' Finset.univ_nonempty
        (fun action => (losses.map fun loss => loss action).sum) ≤ lossBound)
    (hlossBound_pos : 0 < lossBound)
    (hcard : 1 < Fintype.card Action) :
    hedgeWeightStateCumulativeLoss
        (hedgeDiscountFromBounds lossBound (Real.log (Fintype.card Action : ℝ)))
        (by
          unfold hedgeDiscountFromBounds
          apply one_div_pos.mpr
          have hcard_real : 1 < (Fintype.card Action : ℝ) := by
            exact_mod_cast hcard
          have hlog_pos : 0 < Real.log (Fintype.card Action : ℝ) :=
            Real.log_pos hcard_real
          have hratio_pos : 0 < 2 * Real.log (Fintype.card Action : ℝ) / lossBound := by
            exact div_pos (mul_pos (by norm_num) hlog_pos) hlossBound_pos
          nlinarith [Real.sqrt_pos.mpr hratio_pos])
        state losses ≤
      (Finset.univ.inf' Finset.univ_nonempty
          (fun action => (losses.map fun loss => loss action).sum)) +
        Real.sqrt (2 * lossBound * Real.log (Fintype.card Action : ℝ)) +
          Real.log (Fintype.card Action : ℝ) := by
  classical
  have hcard_real : 1 < (Fintype.card Action : ℝ) := by
    exact_mod_cast hcard
  have hregret_pos : 0 < Real.log (Fintype.card Action : ℝ) :=
    Real.log_pos hcard_real
  have hratio_pos : 0 < 2 * Real.log (Fintype.card Action : ℝ) / lossBound := by
    exact div_pos (mul_pos (by norm_num) hregret_pos) hlossBound_pos
  have hdiscount_pos :
      0 < hedgeDiscountFromBounds lossBound (Real.log (Fintype.card Action : ℝ)) := by
    unfold hedgeDiscountFromBounds
    apply one_div_pos.mpr
    nlinarith [Real.sqrt_pos.mpr hratio_pos]
  have hdiscount_lt_one :
      hedgeDiscountFromBounds lossBound (Real.log (Fintype.card Action : ℝ)) < 1 := by
    unfold hedgeDiscountFromBounds
    apply (div_lt_one₀ (by nlinarith [Real.sqrt_pos.mpr hratio_pos])).mpr
    nlinarith [Real.sqrt_pos.mpr hratio_pos]
  obtain ⟨best, _hbest_mem, hbest⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset Action))
      (H := Finset.univ_nonempty)
      (f := fun action => (losses.map fun loss => loss action).sum)
  have hbest_nonneg : 0 ≤ (losses.map fun loss => loss best).sum := by
    apply List.sum_nonneg
    intro value hvalue
    obtain ⟨loss, hloss_mem, rfl⟩ := List.mem_map.mp hvalue
    exact (hloss loss hloss_mem best).1
  have hbest_le : (losses.map fun loss => loss best).sum ≤ lossBound := by
    rw [← hbest]
    exact hbest_le_bound
  have htheorem2 := hedgeWeightState_theorem2_uniform_best_finite
    (hedgeDiscountFromBounds lossBound (Real.log (Fintype.card Action : ℝ)))
    hdiscount_pos hdiscount_lt_one state huniform losses hloss
  have hrate := hedge_learning_rate_bound
    hbest_nonneg hbest_le hregret_pos le_rfl hlossBound_pos
  calc
    hedgeWeightStateCumulativeLoss
        (hedgeDiscountFromBounds lossBound (Real.log (Fintype.card Action : ℝ)))
        (by
          unfold hedgeDiscountFromBounds
          apply one_div_pos.mpr
          nlinarith [Real.sqrt_pos.mpr hratio_pos])
        state losses ≤
        ((Finset.univ.inf' Finset.univ_nonempty
            (fun action => (losses.map fun loss => loss action).sum)) *
            Real.log
              (1 / hedgeDiscountFromBounds lossBound
                (Real.log (Fintype.card Action : ℝ))) +
            Real.log (Fintype.card Action : ℝ)) /
          (1 - hedgeDiscountFromBounds lossBound
            (Real.log (Fintype.card Action : ℝ))) := by
          simpa using htheorem2
    _ =
        (-((losses.map fun loss => loss best).sum) *
            Real.log (hedgeDiscountFromBounds lossBound
              (Real.log (Fintype.card Action : ℝ))) +
          Real.log (Fintype.card Action : ℝ)) /
          (1 - hedgeDiscountFromBounds lossBound
            (Real.log (Fintype.card Action : ℝ))) := by
          rw [hbest, one_div, Real.log_inv]
          ring
    _ ≤ (losses.map fun loss => loss best).sum +
        Real.sqrt (2 * lossBound * Real.log (Fintype.card Action : ℝ)) +
          Real.log (Fintype.card Action : ℝ) := hrate
    _ =
        (Finset.univ.inf' Finset.univ_nonempty
          (fun action => (losses.map fun loss => loss action).sum)) +
          Real.sqrt (2 * lossBound * Real.log (Fintype.card Action : ℝ)) +
            Real.log (Fintype.card Action : ℝ) := by
          rw [hbest]

/--
The conventional square-root-loss corollary of the equal-prior Hedge bound.
For a nonempty loss path and at least two actions, the source Lemma-4
discount with `lossBound = path.length` and `regretBound = log |Action|`
turns Theorem 2's exact finite bound into an `O(sqrt(T log |Action|))`
comparison with the best fixed action.
-/
theorem hedgeWeightState_uniform_sqrt_regret_bound
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (state : HedgeWeightState Action)
    (huniform : ∀ action, state.weight action = 1 / (Fintype.card Action : ℝ))
    (losses : List (Action → ℝ)) (hlosses : losses ≠ [])
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1)
    (hcard : 1 < Fintype.card Action) :
    hedgeWeightStateCumulativeLoss
        (hedgeDiscountFromBounds (losses.length : ℝ) (Real.log (Fintype.card Action : ℝ)))
        (by
          unfold hedgeDiscountFromBounds
          apply one_div_pos.mpr
          have hlength_nat_pos : 0 < losses.length := List.length_pos_of_ne_nil hlosses
          have hlength_pos : 0 < (losses.length : ℝ) := by
            exact_mod_cast hlength_nat_pos
          have hcard_real : 1 < (Fintype.card Action : ℝ) := by
            exact_mod_cast hcard
          have hlog_pos : 0 < Real.log (Fintype.card Action : ℝ) :=
            Real.log_pos hcard_real
          have hratio_pos : 0 < 2 * Real.log (Fintype.card Action : ℝ) /
              (losses.length : ℝ) := by
            exact div_pos (mul_pos (by norm_num) hlog_pos) hlength_pos
          nlinarith [Real.sqrt_pos.mpr hratio_pos])
        state losses ≤
      (Finset.univ.inf' Finset.univ_nonempty
          (fun action => (losses.map fun loss => loss action).sum)) +
        Real.sqrt (2 * (losses.length : ℝ) * Real.log (Fintype.card Action : ℝ)) +
          Real.log (Fintype.card Action : ℝ) := by
  classical
  have hlength_nat_pos : 0 < losses.length := List.length_pos_of_ne_nil hlosses
  have hlength_pos : 0 < (losses.length : ℝ) := by
    exact_mod_cast hlength_nat_pos
  have hcard_real : 1 < (Fintype.card Action : ℝ) := by
    exact_mod_cast hcard
  have hregret_pos : 0 < Real.log (Fintype.card Action : ℝ) :=
    Real.log_pos hcard_real
  have hratio_pos : 0 < 2 * Real.log (Fintype.card Action : ℝ) /
      (losses.length : ℝ) := by
    exact div_pos (mul_pos (by norm_num) hregret_pos) hlength_pos
  have hdiscount_pos :
      0 < hedgeDiscountFromBounds (losses.length : ℝ)
        (Real.log (Fintype.card Action : ℝ)) := by
    unfold hedgeDiscountFromBounds
    apply one_div_pos.mpr
    nlinarith [Real.sqrt_pos.mpr hratio_pos]
  have hdiscount_lt_one :
      hedgeDiscountFromBounds (losses.length : ℝ)
        (Real.log (Fintype.card Action : ℝ)) < 1 := by
    unfold hedgeDiscountFromBounds
    apply (div_lt_one₀ (by nlinarith [Real.sqrt_pos.mpr hratio_pos])).mpr
    nlinarith [Real.sqrt_pos.mpr hratio_pos]
  have hloss_cumulative :
      ∀ path : List (Action → ℝ),
        (∀ loss ∈ path, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1) →
          ∀ action, 0 ≤ (path.map fun loss => loss action).sum ∧
            (path.map fun loss => loss action).sum ≤ (path.length : ℝ) := by
    intro path
    induction path with
    | nil =>
        intro _ action
        simp
    | cons loss remaining ih =>
        intro hpath action
        have hhead := hpath loss (by simp) action
        have htail := ih (by
          intro later hlater laterAction
          exact hpath later (by simp [hlater]) laterAction) action
        constructor
        · simpa using add_nonneg hhead.1 htail.1
        · have hsum_le := add_le_add hhead.2 htail.2
          simpa [Nat.cast_add, add_comm] using hsum_le
  obtain ⟨best, _hbest_mem, hbest⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset Action))
      (H := Finset.univ_nonempty)
      (f := fun action => (losses.map fun loss => loss action).sum)
  have hbest_bounds := hloss_cumulative losses hloss best
  have htheorem2 := hedgeWeightState_theorem2_uniform_best_finite
    (hedgeDiscountFromBounds (losses.length : ℝ) (Real.log (Fintype.card Action : ℝ)))
    hdiscount_pos hdiscount_lt_one state huniform losses hloss
  have hrate := hedge_learning_rate_bound
    hbest_bounds.1 hbest_bounds.2 hregret_pos le_rfl hlength_pos
  calc
    hedgeWeightStateCumulativeLoss
        (hedgeDiscountFromBounds (losses.length : ℝ) (Real.log (Fintype.card Action : ℝ)))
        (by
          unfold hedgeDiscountFromBounds
          apply one_div_pos.mpr
          nlinarith [Real.sqrt_pos.mpr hratio_pos])
        state losses ≤
        ((Finset.univ.inf' Finset.univ_nonempty
            (fun action => (losses.map fun loss => loss action).sum)) *
            Real.log
              (1 / hedgeDiscountFromBounds (losses.length : ℝ)
                (Real.log (Fintype.card Action : ℝ))) +
            Real.log (Fintype.card Action : ℝ)) /
          (1 - hedgeDiscountFromBounds (losses.length : ℝ)
            (Real.log (Fintype.card Action : ℝ))) := by
          simpa using htheorem2
    _ =
        (-((losses.map fun loss => loss best).sum) *
            Real.log (hedgeDiscountFromBounds (losses.length : ℝ)
              (Real.log (Fintype.card Action : ℝ))) +
          Real.log (Fintype.card Action : ℝ)) /
          (1 - hedgeDiscountFromBounds (losses.length : ℝ)
            (Real.log (Fintype.card Action : ℝ))) := by
          rw [hbest, one_div, Real.log_inv]
          ring
    _ ≤ (losses.map fun loss => loss best).sum +
        Real.sqrt (2 * (losses.length : ℝ) * Real.log (Fintype.card Action : ℝ)) +
          Real.log (Fintype.card Action : ℝ) := hrate
    _ =
        (Finset.univ.inf' Finset.univ_nonempty
          (fun action => (losses.map fun loss => loss action).sum)) +
          Real.sqrt (2 * (losses.length : ℝ) * Real.log (Fintype.card Action : ℝ)) +
            Real.log (Fintype.card Action : ℝ) := by
          rw [hbest]

/-- Apply Hedge sequentially to a finite list of full-information loss vectors. -/
noncomputable def hedgeIterate
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (discount : ℝ) : PMF Action → List (Action → ℝ) → PMF Action
  | current, [] => current
  | current, loss :: remaining =>
      hedgeIterate discount (hedgeStep current loss discount) remaining

/-- One-item Hedge iteration is exactly the single Hedge update. -/
@[simp] theorem hedgeIterate_singleton
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (current : PMF Action) (loss : Action → ℝ) (discount : ℝ) :
    hedgeIterate discount current [loss] = hedgeStep current loss discount := rfl

end Online
end Learning
end AppliedModelingLib
