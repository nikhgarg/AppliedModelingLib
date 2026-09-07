import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

namespace AppliedModelingLib

open scoped Topology
open Filter

/-!
# Continuous-time Markov chain support

This module provides small reusable facts for continuous-time Markov chains.
The first seam is the closed-form two-state switch probability used by dynamic
platform and surge-pricing models.

## Main declarations

- `twoStateCtmcSwitchProb`: closed-form probability of being in the opposite
  state after elapsed time `t` in a two-state CTMC with transition rates
  `lambdaIJ` and `lambdaJI`.
- `twoStateCtmcStayProb`: paired probability of remaining in the starting
  state, defined as one minus the switch probability.
- `twoStateCtmcTransitionProb`: the resulting two-state transition kernel on
  `Fin 2`.
- `twoStateCtmcSwitchProb_hasDerivAt`: derivative of the closed form.
- `twoStateCtmcSwitchProb_deriv_eq_forward`: the closed form satisfies the
  two-state Kolmogorov forward equation.
- `twoStateCtmcStayProb_deriv_eq_forward`: the paired stay probability
  satisfies the corresponding forward equation.
- `twoStateCtmcSwitchProbPerTime_deriv_neg`: the switch probability per unit
  time is strictly decreasing away from zero under positive rates.
- `twoStateCtmcSwitchProbPerTime_strictAntiOn_Ioi`: the switch probability
  per unit time is strictly antitone on positive elapsed times.
- `twoStateCtmcSwitchProbPerTime_tendsto_at_zero`: the switch probability per
  unit time converges to the outbound rate at zero.
- `twoStateCtmcSwitchProb_lt_rate_mul_time`: the switch probability lies
  strictly below its instantaneous-rate linearization for positive elapsed time.
- `twoStateCtmcSwitchProb_pos`, `twoStateCtmcSwitchProb_nonneg`,
  `twoStateCtmcSwitchProb_le_one`: basic probability-range checks under
  positive/nonnegative rates and elapsed time.
-/

/--
Closed-form probability that a two-state CTMC currently in state `i` is in the
opposite state `j` after elapsed time `t`.

The rates are `lambdaIJ` for transitions from `i` to `j` and `lambdaJI` for
transitions from `j` back to `i`.
-/
noncomputable def twoStateCtmcSwitchProb (lambdaIJ lambdaJI t : ℝ) : ℝ :=
  lambdaIJ / (lambdaIJ + lambdaJI) *
    (1 - Real.exp (-(lambdaIJ + lambdaJI) * t))

/-- Switch probability per unit elapsed time, `q(t)/t`. -/
noncomputable def twoStateCtmcSwitchProbPerTime
    (lambdaIJ lambdaJI t : ℝ) : ℝ :=
  twoStateCtmcSwitchProb lambdaIJ lambdaJI t / t

@[simp] theorem twoStateCtmcSwitchProb_zero
    (lambdaIJ lambdaJI : ℝ) :
    twoStateCtmcSwitchProb lambdaIJ lambdaJI 0 = 0 := by
  simp [twoStateCtmcSwitchProb]

/-- Closed-form probability of remaining in the starting state after elapsed time `t`. -/
noncomputable def twoStateCtmcStayProb (lambdaIJ lambdaJI t : ℝ) : ℝ :=
  1 - twoStateCtmcSwitchProb lambdaIJ lambdaJI t

@[simp] theorem twoStateCtmcStayProb_zero
    (lambdaIJ lambdaJI : ℝ) :
    twoStateCtmcStayProb lambdaIJ lambdaJI 0 = 1 := by
  simp [twoStateCtmcStayProb]

/-- The two outgoing probabilities from a starting state sum to one. -/
theorem twoStateCtmcStayProb_add_switchProb
    (lambdaIJ lambdaJI t : ℝ) :
    twoStateCtmcStayProb lambdaIJ lambdaJI t +
        twoStateCtmcSwitchProb lambdaIJ lambdaJI t = 1 := by
  unfold twoStateCtmcStayProb
  ring

/--
Two-state CTMC transition probabilities on states `0` and `1`, with transition
rate `lambda01` from state `0` to state `1` and `lambda10` from state `1` to
state `0`.
-/
noncomputable def twoStateCtmcTransitionProb
    (lambda01 lambda10 t : ℝ) (i j : Fin 2) : ℝ :=
  if i = j then
    if i = 0 then
      twoStateCtmcStayProb lambda01 lambda10 t
    else
      twoStateCtmcStayProb lambda10 lambda01 t
  else
    if i = 0 then
      twoStateCtmcSwitchProb lambda01 lambda10 t
    else
      twoStateCtmcSwitchProb lambda10 lambda01 t

@[simp] theorem twoStateCtmcTransitionProb_zero_zero
    (lambda01 lambda10 t : ℝ) :
    twoStateCtmcTransitionProb lambda01 lambda10 t 0 0 =
      twoStateCtmcStayProb lambda01 lambda10 t := by
  simp [twoStateCtmcTransitionProb]

@[simp] theorem twoStateCtmcTransitionProb_zero_one
    (lambda01 lambda10 t : ℝ) :
    twoStateCtmcTransitionProb lambda01 lambda10 t 0 1 =
      twoStateCtmcSwitchProb lambda01 lambda10 t := by
  simp [twoStateCtmcTransitionProb]

@[simp] theorem twoStateCtmcTransitionProb_one_zero
    (lambda01 lambda10 t : ℝ) :
    twoStateCtmcTransitionProb lambda01 lambda10 t 1 0 =
      twoStateCtmcSwitchProb lambda10 lambda01 t := by
  simp [twoStateCtmcTransitionProb]

@[simp] theorem twoStateCtmcTransitionProb_one_one
    (lambda01 lambda10 t : ℝ) :
    twoStateCtmcTransitionProb lambda01 lambda10 t 1 1 =
      twoStateCtmcStayProb lambda10 lambda01 t := by
  simp [twoStateCtmcTransitionProb]

/-- At elapsed time zero, the two-state transition kernel is the identity. -/
theorem twoStateCtmcTransitionProb_zero_time
    (lambda01 lambda10 : ℝ) (i j : Fin 2) :
    twoStateCtmcTransitionProb lambda01 lambda10 0 i j =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp

/-- Each row of the two-state transition kernel sums to one. -/
theorem twoStateCtmcTransitionProb_row_sum
    (lambda01 lambda10 t : ℝ) (i : Fin 2) :
    twoStateCtmcTransitionProb lambda01 lambda10 t i 0 +
        twoStateCtmcTransitionProb lambda01 lambda10 t i 1 = 1 := by
  fin_cases i
  · exact twoStateCtmcStayProb_add_switchProb lambda01 lambda10 t
  · simpa [add_comm] using
      twoStateCtmcStayProb_add_switchProb lambda10 lambda01 t

/-- Derivative of the two-state CTMC switch-probability closed form. -/
theorem twoStateCtmcSwitchProb_hasDerivAt
    (lambdaIJ lambdaJI t : ℝ) :
    HasDerivAt (fun s => twoStateCtmcSwitchProb lambdaIJ lambdaJI s)
      (lambdaIJ / (lambdaIJ + lambdaJI) *
        ((lambdaIJ + lambdaJI) *
          Real.exp (-(lambdaIJ + lambdaJI) * t))) t := by
  unfold twoStateCtmcSwitchProb
  have hlin :
      HasDerivAt (fun s : ℝ => -(lambdaIJ + lambdaJI) * s)
        (-(lambdaIJ + lambdaJI)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-(lambdaIJ + lambdaJI)))
  have hexp :
      HasDerivAt (fun s : ℝ => Real.exp (-(lambdaIJ + lambdaJI) * s))
        (Real.exp (-(lambdaIJ + lambdaJI) * t) *
          (-(lambdaIJ + lambdaJI))) t := by
    exact hlin.exp
  have hsub :
      HasDerivAt (fun s : ℝ => 1 - Real.exp (-(lambdaIJ + lambdaJI) * s))
        ((lambdaIJ + lambdaJI) *
          Real.exp (-(lambdaIJ + lambdaJI) * t)) t := by
    convert (hexp.const_sub 1) using 1
    ring
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    hsub.const_mul (lambdaIJ / (lambdaIJ + lambdaJI))

/--
The closed-form two-state switch probability satisfies the scalar forward
equation `q' = lambdaIJ - (lambdaIJ + lambdaJI) q`.
-/
theorem twoStateCtmcSwitchProb_deriv_eq_linear
    (lambdaIJ lambdaJI t : ℝ) (hsum : lambdaIJ + lambdaJI ≠ 0) :
    deriv (fun s => twoStateCtmcSwitchProb lambdaIJ lambdaJI s) t =
      lambdaIJ -
        (lambdaIJ + lambdaJI) * twoStateCtmcSwitchProb lambdaIJ lambdaJI t := by
  have hderiv := twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI t
  rw [hderiv.deriv]
  unfold twoStateCtmcSwitchProb
  field_simp [hsum]
  ring

/-- A differentiable solution of the two-state scalar forward equation with
zero initial switch probability is the closed-form two-state switch
probability.  This is the analytic uniqueness bridge used after a concrete
clock construction has established the forward ODE; it does not itself make a
stochastic-process claim. -/
theorem eq_twoStateCtmcSwitchProb_of_hasDerivAt_linear
    {lambdaIJ lambdaJI : ℝ} (hsum : lambdaIJ + lambdaJI ≠ 0)
    (f : ℝ → ℝ) (hzero : f 0 = 0)
    (hderiv : ∀ t, HasDerivAt f
      (lambdaIJ - (lambdaIJ + lambdaJI) * f t) t) :
    ∀ ⦃t⦄, 0 ≤ t → f t = twoStateCtmcSwitchProb lambdaIJ lambdaJI t := by
  let g : ℝ → ℝ := twoStateCtmcSwitchProb lambdaIJ lambdaJI
  have hgderiv : ∀ t, HasDerivAt g
      (lambdaIJ - (lambdaIJ + lambdaJI) * g t) t := by
    intro t
    change HasDerivAt (fun s => twoStateCtmcSwitchProb lambdaIJ lambdaJI s)
      (lambdaIJ - (lambdaIJ + lambdaJI) *
        twoStateCtmcSwitchProb lambdaIJ lambdaJI t) t
    convert twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI t using 1
    unfold twoStateCtmcSwitchProb
    field_simp [hsum]
    ring
  let d : ℝ → ℝ := fun t => f t - g t
  have hdderiv : ∀ t, HasDerivAt d
      (-(lambdaIJ + lambdaJI) * d t) t := by
    intro t
    change HasDerivAt (fun s => f s - g s)
      (-(lambdaIJ + lambdaJI) * (f t - g t)) t
    convert (hderiv t).sub (hgderiv t) using 1
    ring
  have hdcont : Continuous d := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hdderiv t).continuousAt
  have hdzero : d 0 = 0 := by
    simp [d, g, hzero]
  have hbound : ∀ x, ‖-(lambdaIJ + lambdaJI) * d x‖ ≤
      ‖lambdaIJ + lambdaJI‖ * ‖d x‖ := by
    intro x
    rw [norm_mul, norm_neg]
  intro t ht
  have hzeroOn := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := d) (f' := fun x => -(lambdaIJ + lambdaJI) * d x)
      (K := ‖lambdaIJ + lambdaJI‖) (a := (0 : ℝ)) (b := t)
      hdcont.continuousOn
      (fun x _hx => (hdderiv x).hasDerivWithinAt)
      hdzero
      (fun x _hx => hbound x)
  exact sub_eq_zero.mp (hzeroOn t ⟨ht, le_rfl⟩)

/-- A homogeneous scalar ODE with a zero initial value has the zero solution
on the nonnegative half-line when its derivative is available from the right
at the boundary.  This is the half-line Grönwall form needed for literal
clock paths, whose extension to negative calendar times need not be
two-sided differentiable at zero. -/
theorem eq_zero_of_continuousOn_Ici_of_hasDerivWithinAt_linear
    (c : ℝ) (f : ℝ → ℝ) (hzero : f 0 = 0)
    (hcontinuous : ContinuousOn f (Set.Ici 0))
    (hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt f (c * f t) (Set.Ici t) t) :
    ∀ ⦃t : ℝ⦄, 0 ≤ t → f t = 0 := by
  intro t ht
  have hzeroOn := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := f) (f' := fun x => c * f x) (K := ‖c‖)
    (a := (0 : ℝ)) (b := t)
    (hcontinuous.mono Set.Icc_subset_Ici_self)
    (fun x hx => hderiv x hx.1)
    hzero
    (fun x _ => by rw [norm_mul])
  exact hzeroOn t ⟨ht, le_rfl⟩

/--
The closed-form two-state switch probability satisfies the Kolmogorov forward
equation for being in the opposite state:
`q' = lambdaIJ * (1 - q) - lambdaJI * q`.
-/
theorem twoStateCtmcSwitchProb_deriv_eq_forward
    (lambdaIJ lambdaJI t : ℝ) (hsum : lambdaIJ + lambdaJI ≠ 0) :
    deriv (fun s => twoStateCtmcSwitchProb lambdaIJ lambdaJI s) t =
      lambdaIJ * (1 - twoStateCtmcSwitchProb lambdaIJ lambdaJI t) -
        lambdaJI * twoStateCtmcSwitchProb lambdaIJ lambdaJI t := by
  rw [twoStateCtmcSwitchProb_deriv_eq_linear lambdaIJ lambdaJI t hsum]
  ring

/-- Derivative of the switch probability per unit elapsed time. -/
theorem twoStateCtmcSwitchProbPerTime_hasDerivAt
    (lambdaIJ lambdaJI t : ℝ) (ht : t ≠ 0) :
    HasDerivAt
      (fun s => twoStateCtmcSwitchProbPerTime lambdaIJ lambdaJI s)
      ((lambdaIJ / (lambdaIJ + lambdaJI) *
          ((lambdaIJ + lambdaJI) *
            Real.exp (-(lambdaIJ + lambdaJI) * t)) * t -
          twoStateCtmcSwitchProb lambdaIJ lambdaJI t) / t ^ 2) t := by
  unfold twoStateCtmcSwitchProbPerTime
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
    (twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI t).div
      (hasDerivAt_id t) ht

/--
The switch probability per unit time has negative derivative under positive
outbound rate, positive total rate, and positive elapsed time.
-/
theorem twoStateCtmcSwitchProbPerTime_deriv_neg
    (lambdaIJ lambdaJI t : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (ht : 0 < t) :
    deriv (fun s => twoStateCtmcSwitchProbPerTime lambdaIJ lambdaJI s) t < 0 := by
  have hderiv :=
    (twoStateCtmcSwitchProbPerTime_hasDerivAt lambdaIJ lambdaJI t
      (ne_of_gt ht)).deriv
  rw [hderiv]
  unfold twoStateCtmcSwitchProb
  have hst : 0 < (lambdaIJ + lambdaJI) * t := mul_pos hsum ht
  have hexp_strict :
      (1 + (lambdaIJ + lambdaJI) * t) *
          Real.exp (-((lambdaIJ + lambdaJI) * t)) < 1 := by
    have hmain : 1 + (lambdaIJ + lambdaJI) * t <
        Real.exp ((lambdaIJ + lambdaJI) * t) := by
      simpa [add_comm] using Real.add_one_lt_exp (ne_of_gt hst)
    have hexp_pos : 0 < Real.exp (-((lambdaIJ + lambdaJI) * t)) :=
      Real.exp_pos _
    have hmul := mul_lt_mul_of_pos_right hmain hexp_pos
    simpa [Real.exp_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hbracket :
      (lambdaIJ + lambdaJI) * t *
          Real.exp (-(lambdaIJ + lambdaJI) * t) -
        (1 - Real.exp (-(lambdaIJ + lambdaJI) * t)) < 0 := by
    have hsame :
        (lambdaIJ + lambdaJI) * t *
            Real.exp (-(lambdaIJ + lambdaJI) * t) -
          (1 - Real.exp (-(lambdaIJ + lambdaJI) * t)) =
        (1 + (lambdaIJ + lambdaJI) * t) *
            Real.exp (-((lambdaIJ + lambdaJI) * t)) - 1 := by
      ring_nf
    rw [hsame]
    linarith
  have hfactor : 0 < lambdaIJ / (lambdaIJ + lambdaJI) :=
    div_pos hlambdaIJ hsum
  have ht_sq : 0 < t ^ 2 := sq_pos_of_ne_zero (ne_of_gt ht)
  have hnum :
      lambdaIJ / (lambdaIJ + lambdaJI) *
        ((lambdaIJ + lambdaJI) * t *
            Real.exp (-(lambdaIJ + lambdaJI) * t) -
          (1 - Real.exp (-(lambdaIJ + lambdaJI) * t))) < 0 := by
    exact mul_neg_of_pos_of_neg hfactor hbracket
  have hrewrite :
      lambdaIJ / (lambdaIJ + lambdaJI) *
            ((lambdaIJ + lambdaJI) *
              Real.exp (-(lambdaIJ + lambdaJI) * t)) *
            t -
          lambdaIJ / (lambdaIJ + lambdaJI) *
            (1 - Real.exp (-(lambdaIJ + lambdaJI) * t)) =
        lambdaIJ / (lambdaIJ + lambdaJI) *
          ((lambdaIJ + lambdaJI) * t *
              Real.exp (-(lambdaIJ + lambdaJI) * t) -
            (1 - Real.exp (-(lambdaIJ + lambdaJI) * t))) := by
    ring
  rw [hrewrite]
  exact div_neg_of_neg_of_pos hnum ht_sq

/--
The switch probability per unit time is strictly decreasing on positive
elapsed times.
-/
theorem twoStateCtmcSwitchProbPerTime_strictAntiOn_Ioi
    (lambdaIJ lambdaJI : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI) :
    StrictAntiOn
      (fun t => twoStateCtmcSwitchProbPerTime lambdaIJ lambdaJI t)
      (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro t ht
    exact
      (twoStateCtmcSwitchProbPerTime_hasDerivAt lambdaIJ lambdaJI t
        (ne_of_gt ht)).continuousAt.continuousWithinAt
  · intro t ht
    have ht_pos : 0 < t := by
      simpa using ht
    exact twoStateCtmcSwitchProbPerTime_deriv_neg
      lambdaIJ lambdaJI t hlambdaIJ hsum ht_pos

/--
The switch probability per unit time converges to the outbound rate as elapsed
time tends to zero.
-/
theorem twoStateCtmcSwitchProbPerTime_tendsto_at_zero
    (lambdaIJ lambdaJI : ℝ) (hsum : lambdaIJ + lambdaJI ≠ 0) :
    Tendsto (fun t => twoStateCtmcSwitchProbPerTime lambdaIJ lambdaJI t)
      (𝓝[≠] 0) (𝓝 lambdaIJ) := by
  have hderiv :
      HasDerivAt (fun t => twoStateCtmcSwitchProb lambdaIJ lambdaJI t)
        lambdaIJ 0 := by
    simpa [hsum] using twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI 0
  have hslope :=
    hderiv.tendsto_slope
  have heq :
      (fun t => slope (fun s => twoStateCtmcSwitchProb lambdaIJ lambdaJI s) 0 t)
        =ᶠ[𝓝[≠] 0]
      (fun t => twoStateCtmcSwitchProbPerTime lambdaIJ lambdaJI t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [slope, twoStateCtmcSwitchProbPerTime, div_eq_mul_inv, mul_comm]
  exact hslope.congr' heq

/--
The switch probability is strictly below the instantaneous-rate linearization
`lambdaIJ * t` for positive elapsed time.
-/
theorem twoStateCtmcSwitchProb_lt_rate_mul_time
    (lambdaIJ lambdaJI t : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (ht : 0 < t) :
    twoStateCtmcSwitchProb lambdaIJ lambdaJI t < lambdaIJ * t := by
  unfold twoStateCtmcSwitchProb
  have hst : 0 < (lambdaIJ + lambdaJI) * t := mul_pos hsum ht
  have hterm :
      1 - Real.exp (-(lambdaIJ + lambdaJI) * t) <
        (lambdaIJ + lambdaJI) * t := by
    have hbase :
        1 + (-((lambdaIJ + lambdaJI) * t)) <
          Real.exp (-((lambdaIJ + lambdaJI) * t)) := by
      simpa [add_comm] using
        Real.add_one_lt_exp (show -((lambdaIJ + lambdaJI) * t) ≠ 0 by
          nlinarith [hst])
    have hconverted :
        1 - Real.exp (-((lambdaIJ + lambdaJI) * t)) <
          (lambdaIJ + lambdaJI) * t := by
      linarith
    have hneg_arg :
        -((lambdaIJ + lambdaJI) * t) = -(lambdaIJ + lambdaJI) * t := by
      ring
    rw [← hneg_arg]
    exact hconverted
  have hfactor : 0 < lambdaIJ / (lambdaIJ + lambdaJI) :=
    div_pos hlambdaIJ hsum
  have hmul :
      lambdaIJ / (lambdaIJ + lambdaJI) *
          (1 - Real.exp (-(lambdaIJ + lambdaJI) * t)) <
        lambdaIJ / (lambdaIJ + lambdaJI) *
          ((lambdaIJ + lambdaJI) * t) :=
    mul_lt_mul_of_pos_left hterm hfactor
  have hprod :
      lambdaIJ / (lambdaIJ + lambdaJI) * ((lambdaIJ + lambdaJI) * t) =
        lambdaIJ * t := by
    field_simp [ne_of_gt hsum]
  exact lt_of_lt_of_eq hmul hprod

/--
Per-unit-time form of `twoStateCtmcSwitchProb_lt_rate_mul_time`:
`q(t)/t < lambdaIJ` for positive elapsed time.
-/
theorem twoStateCtmcSwitchProbPerTime_lt_rate
    (lambdaIJ lambdaJI t : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (ht : 0 < t) :
    twoStateCtmcSwitchProbPerTime lambdaIJ lambdaJI t < lambdaIJ := by
  unfold twoStateCtmcSwitchProbPerTime
  rw [div_lt_iff₀ ht]
  exact twoStateCtmcSwitchProb_lt_rate_mul_time
    lambdaIJ lambdaJI t hlambdaIJ hsum ht

/--
The paired stay probability satisfies the Kolmogorov forward equation:
`p' = -lambdaIJ * p + lambdaJI * q`.
-/
theorem twoStateCtmcStayProb_deriv_eq_forward
    (lambdaIJ lambdaJI t : ℝ) (hsum : lambdaIJ + lambdaJI ≠ 0) :
    deriv (fun s => twoStateCtmcStayProb lambdaIJ lambdaJI s) t =
      -lambdaIJ * twoStateCtmcStayProb lambdaIJ lambdaJI t +
        lambdaJI * twoStateCtmcSwitchProb lambdaIJ lambdaJI t := by
  unfold twoStateCtmcStayProb
  rw [deriv_const_sub, twoStateCtmcSwitchProb_deriv_eq_forward
    lambdaIJ lambdaJI t hsum]
  ring

/-- The two-state switch-probability closed form is positive at positive elapsed times. -/
theorem twoStateCtmcSwitchProb_pos
    (lambdaIJ lambdaJI t : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (ht : 0 < t) :
    0 < twoStateCtmcSwitchProb lambdaIJ lambdaJI t := by
  unfold twoStateCtmcSwitchProb
  have hfactor : 0 < lambdaIJ / (lambdaIJ + lambdaJI) :=
    div_pos hlambdaIJ hsum
  have harg : -(lambdaIJ + lambdaJI) * t < 0 := by
    nlinarith
  have hexp_lt_one : Real.exp (-(lambdaIJ + lambdaJI) * t) < 1 := by
    have := (Real.exp_lt_exp).2 harg
    simpa using this
  have hterm : 0 < 1 - Real.exp (-(lambdaIJ + lambdaJI) * t) := by
    linarith
  exact mul_pos hfactor hterm

/-- The two-state switch-probability closed form is nonnegative in the usual parameter range. -/
theorem twoStateCtmcSwitchProb_nonneg
    (lambdaIJ lambdaJI t : ℝ)
    (hlambdaIJ : 0 ≤ lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (ht : 0 ≤ t) :
    0 ≤ twoStateCtmcSwitchProb lambdaIJ lambdaJI t := by
  unfold twoStateCtmcSwitchProb
  apply mul_nonneg
  · exact div_nonneg hlambdaIJ (le_of_lt hsum)
  · have harg : -(lambdaIJ + lambdaJI) * t ≤ 0 := by nlinarith
    have hexp : Real.exp (-(lambdaIJ + lambdaJI) * t) ≤ 1 := by
      have := (Real.exp_le_exp).2 harg
      simpa using this
    linarith

/-- The two-state switch-probability closed form is at most one in the usual parameter range. -/
theorem twoStateCtmcSwitchProb_le_one
    (lambdaIJ lambdaJI t : ℝ)
    (hlambdaIJ : 0 ≤ lambdaIJ) (hlambdaJI : 0 ≤ lambdaJI)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (ht : 0 ≤ t) :
    twoStateCtmcSwitchProb lambdaIJ lambdaJI t ≤ 1 := by
  unfold twoStateCtmcSwitchProb
  have hfactor_le_one : lambdaIJ / (lambdaIJ + lambdaJI) ≤ 1 := by
    rw [div_le_one hsum]
    linarith
  have hterm_nonneg : 0 ≤ 1 - Real.exp (-(lambdaIJ + lambdaJI) * t) := by
    have harg : -(lambdaIJ + lambdaJI) * t ≤ 0 := by nlinarith
    have hexp : Real.exp (-(lambdaIJ + lambdaJI) * t) ≤ 1 := by
      have := (Real.exp_le_exp).2 harg
      simpa using this
    linarith
  have hterm_le_one : 1 - Real.exp (-(lambdaIJ + lambdaJI) * t) ≤ 1 := by
    have hnonneg := Real.exp_nonneg (-(lambdaIJ + lambdaJI) * t)
    linarith
  have hmul :
      lambdaIJ / (lambdaIJ + lambdaJI) *
          (1 - Real.exp (-(lambdaIJ + lambdaJI) * t)) ≤ 1 * 1 := by
    exact mul_le_mul hfactor_le_one hterm_le_one hterm_nonneg zero_le_one
  simpa using hmul

/-- The paired stay probability is nonnegative in the usual parameter range. -/
theorem twoStateCtmcStayProb_nonneg
    (lambdaIJ lambdaJI t : ℝ)
    (hlambdaIJ : 0 ≤ lambdaIJ) (hlambdaJI : 0 ≤ lambdaJI)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (ht : 0 ≤ t) :
    0 ≤ twoStateCtmcStayProb lambdaIJ lambdaJI t := by
  unfold twoStateCtmcStayProb
  have hswitch_le_one :=
    twoStateCtmcSwitchProb_le_one lambdaIJ lambdaJI t
      hlambdaIJ hlambdaJI hsum ht
  linarith

/-- The paired stay probability is at most one in the usual parameter range. -/
theorem twoStateCtmcStayProb_le_one
    (lambdaIJ lambdaJI t : ℝ)
    (hlambdaIJ : 0 ≤ lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (ht : 0 ≤ t) :
    twoStateCtmcStayProb lambdaIJ lambdaJI t ≤ 1 := by
  unfold twoStateCtmcStayProb
  have hswitch_nonneg :=
    twoStateCtmcSwitchProb_nonneg lambdaIJ lambdaJI t
      hlambdaIJ hsum ht
  linarith

end AppliedModelingLib
