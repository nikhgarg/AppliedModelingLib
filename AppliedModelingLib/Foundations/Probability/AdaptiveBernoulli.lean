import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Exponential controls for adaptive Bernoulli observations

This module supplies the martingale layer for a predictable sequence of
Bernoulli observations.  It is deliberately independent of any particular
MDP: the application supplies the conditional exponential bound for each
observation, while the theorem below accumulates those bounds into an
exponential supermartingale.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators MeasureTheory NNReal ENNReal

namespace AppliedModelingLib
namespace Probability

/-- Realized sum of the first `n` adaptive Bernoulli observations. -/
def adaptiveBernoulliCount
    {Omega : Type*} (observation : ℕ → Omega → ℝ) (n : ℕ) (omega : Omega) : ℝ :=
  ∑ index ∈ Finset.range n, observation index omega

/-- Predictable cumulative visit mass corresponding to `adaptiveBernoulliCount`. -/
def adaptiveBernoulliMass
    {Omega : Type*} (conditionalMean : ℕ → Omega → ℝ) (n : ℕ) (omega : Omega) : ℝ :=
  ∑ index ∈ Finset.range n, conditionalMean index omega

/--
Exponential control for a realized adaptive count relative to a predictable
cumulative mass.  A one-step conditional bound on its multiplicative factor
makes this process a supermartingale.
-/
noncomputable def adaptiveBernoulliExponentialControl
    {Omega : Type*} (rate compensator : ℝ)
    (observation conditionalMean : ℕ → Omega → ℝ) (n : ℕ) (omega : Omega) : ℝ :=
  Real.exp (-rate *
    (adaptiveBernoulliCount observation n omega -
      compensator * adaptiveBernoulliMass conditionalMean n omega))

/-- The one-step multiplier of `adaptiveBernoulliExponentialControl`. -/
noncomputable def adaptiveBernoulliExponentialFactor
    {Omega : Type*} (rate compensator : ℝ)
    (observation conditionalMean : ℕ → Omega → ℝ) (n : ℕ) (omega : Omega) : ℝ :=
  Real.exp (-rate * (observation n omega - compensator * conditionalMean n omega))

/-- A partial adaptive count is measurable with respect to the corresponding history. -/
theorem stronglyAdapted_adaptiveBernoulliCount
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (observation : ℕ → Omega → ℝ)
    (hadapted : StronglyAdapted filtration observation) :
    StronglyAdapted filtration (adaptiveBernoulliCount observation) := by
  intro n
  change StronglyMeasurable[filtration n]
    (fun omega => ∑ index ∈ Finset.range n, observation index omega)
  convert Finset.stronglyMeasurable_sum (Finset.range n) (fun index hindex =>
    (hadapted index).mono
      (filtration.mono (Nat.le_of_lt (Finset.mem_range.mp hindex)))) using 1
  funext omega
  simp only [Finset.sum_apply]

/-- A partial predictable mass is measurable with respect to the corresponding history. -/
theorem stronglyAdapted_adaptiveBernoulliMass
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (conditionalMean : ℕ → Omega → ℝ)
    (hadapted : StronglyAdapted filtration conditionalMean) :
    StronglyAdapted filtration (adaptiveBernoulliMass conditionalMean) := by
  intro n
  change StronglyMeasurable[filtration n]
    (fun omega => ∑ index ∈ Finset.range n, conditionalMean index omega)
  convert Finset.stronglyMeasurable_sum (Finset.range n) (fun index hindex =>
    (hadapted index).mono
      (filtration.mono (Nat.le_of_lt (Finset.mem_range.mp hindex)))) using 1
  funext omega
  simp only [Finset.sum_apply]

/-- The exponential control factors into its preceding value and one new observation. -/
theorem adaptiveBernoulliExponentialControl_succ
    {Omega : Type*} (rate compensator : ℝ)
    (observation conditionalMean : ℕ → Omega → ℝ) (n : ℕ) :
    adaptiveBernoulliExponentialControl rate compensator observation conditionalMean (n + 1) =
      fun omega =>
        adaptiveBernoulliExponentialControl rate compensator observation conditionalMean n omega *
          adaptiveBernoulliExponentialFactor rate compensator observation conditionalMean n omega := by
  funext omega
  unfold adaptiveBernoulliExponentialControl adaptiveBernoulliExponentialFactor
    adaptiveBernoulliCount adaptiveBernoulliMass
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  rw [show
    -rate * ((∑ index ∈ Finset.range n, observation index omega) + observation n omega -
      compensator * ((∑ index ∈ Finset.range n, conditionalMean index omega) +
        conditionalMean n omega)) =
      -rate * ((∑ index ∈ Finset.range n, observation index omega) -
        compensator * ∑ index ∈ Finset.range n, conditionalMean index omega) +
      -rate * (observation n omega - compensator * conditionalMean n omega) by ring]
  rw [Real.exp_add]

/-- The exponential control is adapted whenever observations and their conditional means are. -/
theorem stronglyAdapted_adaptiveBernoulliExponentialControl
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (rate compensator : ℝ) (observation conditionalMean : ℕ → Omega → ℝ)
    (hobs : StronglyAdapted filtration observation)
    (hmean : StronglyAdapted filtration conditionalMean) :
    StronglyAdapted filtration
      (adaptiveBernoulliExponentialControl rate compensator observation conditionalMean) := by
  intro n
  change StronglyMeasurable[filtration n]
    (fun omega => Real.exp (-rate *
      (adaptiveBernoulliCount observation n omega -
        compensator * adaptiveBernoulliMass conditionalMean n omega)))
  exact ((stronglyAdapted_adaptiveBernoulliCount filtration observation hobs n).sub
    ((stronglyAdapted_adaptiveBernoulliMass filtration conditionalMean hmean n).const_mul
      compensator)).const_mul (-rate) |>.measurable.exp.stronglyMeasurable

/-- The one-step exponential factor is adapted whenever its inputs are. -/
theorem stronglyAdapted_adaptiveBernoulliExponentialFactor
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (rate compensator : ℝ) (observation conditionalMean : ℕ → Omega → ℝ)
    (hobs : StronglyAdapted filtration observation)
    (hmean : StronglyAdapted filtration conditionalMean) :
    StronglyAdapted filtration
      (adaptiveBernoulliExponentialFactor rate compensator observation conditionalMean) := by
  intro n
  change StronglyMeasurable[filtration n]
    (fun omega => Real.exp (-rate *
      (observation n omega - compensator * conditionalMean n omega)))
  exact ((hobs n).sub ((hmean n).const_mul compensator)).const_mul (-rate) |>.measurable.exp
    |>.stronglyMeasurable

/-- A pointwise zero-one adapted observation is integrable under a finite measure. -/
theorem integrable_adaptiveBernoulli_zeroOne_observation
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation : ℕ → Omega → ℝ) (hobs : StronglyAdapted filtration observation)
    (hobs_zero_or_one : ∀ index omega,
      observation index omega = 0 ∨ observation index omega = 1)
    (n : ℕ) : Integrable (observation n) mu := by
  have hmeasurable : Measurable (observation n) :=
    (hobs n).measurable.le (filtration.le n)
  refine Integrable.of_bound hmeasurable.aestronglyMeasurable 1 ?_
  filter_upwards with omega
  rcases hobs_zero_or_one n omega with hzero | hone
  · simp [hzero]
  · simp [hone]

/--
A canonical pointwise `[0,1]` version of the conditional mean of a
zero-one process.  The clipping changes only a null set once the observation
is integrable, while making bounded exponential controls pointwise defined.
-/
noncomputable def adaptiveBernoulliClippedConditionalMean
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega)
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (observation : ℕ → Omega → ℝ) (n : ℕ) (omega : Omega) : ℝ :=
  max 0 (min 1 (mu[observation n | filtration n] omega))

/-- The clipped conditional mean is adapted to the same filtration. -/
theorem stronglyAdapted_adaptiveBernoulliClippedConditionalMean
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation : ℕ → Omega → ℝ) :
    StronglyAdapted filtration
      (adaptiveBernoulliClippedConditionalMean mu filtration observation) := by
  intro n
  unfold adaptiveBernoulliClippedConditionalMean
  have hconditional : StronglyMeasurable[filtration n]
      (mu[observation n | filtration n]) :=
    stronglyMeasurable_condExp
  have hzero : Measurable[filtration n] (fun _ : Omega => (0 : ℝ)) := measurable_const
  have hone : Measurable[filtration n] (fun _ : Omega => (1 : ℝ)) := measurable_const
  exact ((hzero.max (hone.min hconditional.measurable))).stronglyMeasurable

/-- The clipped conditional mean is pointwise a probability. -/
theorem adaptiveBernoulliClippedConditionalMean_unitInterval
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation : ℕ → Omega → ℝ) (n : ℕ) (omega : Omega) :
    0 ≤ adaptiveBernoulliClippedConditionalMean mu filtration observation n omega ∧
      adaptiveBernoulliClippedConditionalMean mu filtration observation n omega ≤ 1 := by
  unfold adaptiveBernoulliClippedConditionalMean
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/--
Clipping is almost surely inert for a zero-one observation: the clipped mean
is a bounded version of its conditional expectation.
-/
theorem condExp_ae_eq_adaptiveBernoulliClippedConditionalMean_of_zeroOne
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation : ℕ → Omega → ℝ) (hobs : StronglyAdapted filtration observation)
    (hobs_zero_or_one : ∀ index omega,
      observation index omega = 0 ∨ observation index omega = 1)
    (n : ℕ) :
    mu[observation n | filtration n] =ᵐ[mu]
      adaptiveBernoulliClippedConditionalMean mu filtration observation n := by
  have hobs_integrable : Integrable (observation n) mu :=
    integrable_adaptiveBernoulli_zeroOne_observation observation hobs hobs_zero_or_one n
  have hobs_nonneg : ∀ᵐ omega ∂mu, 0 ≤ observation n omega :=
    Filter.Eventually.of_forall fun omega => by
      rcases hobs_zero_or_one n omega with hzero | hone
      · simp [hzero]
      · simp [hone]
  have hobs_le_one : observation n ≤ᵐ[mu] fun _ => (1 : ℝ) :=
    Filter.Eventually.of_forall fun omega => by
      rcases hobs_zero_or_one n omega with hzero | hone
      · simp [hzero]
      · simp [hone]
  have hconditional_nonneg : ∀ᵐ omega ∂mu,
      0 ≤ mu[observation n | filtration n] omega :=
    condExp_nonneg hobs_nonneg
  have hconditional_le_one : mu[observation n | filtration n] ≤ᵐ[mu]
      fun _ => (1 : ℝ) := by
    have hle := condExp_mono (m := filtration n) hobs_integrable
      (integrable_const (c := (1 : ℝ))) hobs_le_one
    simpa only [condExp_const (filtration.le n) (1 : ℝ)] using hle
  filter_upwards [hconditional_nonneg, hconditional_le_one] with omega hnonneg hone
  unfold adaptiveBernoulliClippedConditionalMean
  rw [min_eq_right hone, max_eq_right hnonneg]

/--
For a zero-one observation and a pointwise unit-interval predictable mean,
the half-mass one-step exponential factor is integrable under every finite
measure.
-/
theorem integrable_adaptiveBernoulli_half_exponentialFactor_of_unitInterval
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation conditionalMean : ℕ → Omega → ℝ)
    (hobs : StronglyAdapted filtration observation)
    (hmean : StronglyAdapted filtration conditionalMean)
    (hobs_zero_or_one : ∀ index omega,
      observation index omega = 0 ∨ observation index omega = 1)
    (hmean_unitInterval : ∀ index omega,
      0 ≤ conditionalMean index omega ∧ conditionalMean index omega ≤ 1)
    (n : ℕ) :
    Integrable (adaptiveBernoulliExponentialFactor 1 ((1 : ℝ) / 2)
      observation conditionalMean n) mu := by
  have hfactor_adapted := stronglyAdapted_adaptiveBernoulliExponentialFactor filtration
    1 ((1 : ℝ) / 2) observation conditionalMean hobs hmean
  have hfactor_measurable : Measurable
      (adaptiveBernoulliExponentialFactor 1 ((1 : ℝ) / 2)
        observation conditionalMean n) :=
    (hfactor_adapted n).measurable.le (filtration.le n)
  refine Integrable.of_bound hfactor_measurable.aestronglyMeasurable (Real.exp ((1 : ℝ) / 2)) ?_
  filter_upwards with omega
  unfold adaptiveBernoulliExponentialFactor
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  rcases hobs_zero_or_one n omega with hzero | hone
  · rw [hzero]
    linarith [(hmean_unitInterval n omega).2]
  · rw [hone]
    linarith [(hmean_unitInterval n omega).2]

/--
The corresponding finite-time exponential count control is integrable.  The
bound uses only that each realized observation and predictable mean lies in
the unit interval.
-/
theorem integrable_adaptiveBernoulli_half_exponentialControl_of_unitInterval
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation conditionalMean : ℕ → Omega → ℝ)
    (hobs : StronglyAdapted filtration observation)
    (hmean : StronglyAdapted filtration conditionalMean)
    (hobs_zero_or_one : ∀ index omega,
      observation index omega = 0 ∨ observation index omega = 1)
    (hmean_unitInterval : ∀ index omega,
      0 ≤ conditionalMean index omega ∧ conditionalMean index omega ≤ 1)
    (n : ℕ) :
    Integrable (adaptiveBernoulliExponentialControl 1 ((1 : ℝ) / 2)
      observation conditionalMean n) mu := by
  have hcontrol_adapted := stronglyAdapted_adaptiveBernoulliExponentialControl filtration
    1 ((1 : ℝ) / 2) observation conditionalMean hobs hmean
  have hcontrol_measurable : Measurable
      (adaptiveBernoulliExponentialControl 1 ((1 : ℝ) / 2)
        observation conditionalMean n) :=
    (hcontrol_adapted n).measurable.le (filtration.le n)
  refine Integrable.of_bound hcontrol_measurable.aestronglyMeasurable
    (Real.exp ((n : ℝ) / 2)) ?_
  filter_upwards with omega
  unfold adaptiveBernoulliExponentialControl
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have hcount_nonneg : 0 ≤ adaptiveBernoulliCount observation n omega := by
    unfold adaptiveBernoulliCount
    apply Finset.sum_nonneg
    intro index _
    rcases hobs_zero_or_one index omega with hzero | hone
    · simp [hzero]
    · simp [hone]
  have hmass_le : adaptiveBernoulliMass conditionalMean n omega ≤ (n : ℝ) := by
    unfold adaptiveBernoulliMass
    calc
      ∑ index ∈ Finset.range n, conditionalMean index omega ≤
          ∑ _index ∈ Finset.range n, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro index _
            exact (hmean_unitInterval index omega).2
      _ = (n : ℝ) := by simp
  nlinarith

/--
The scalar conditional-MGF expression is at most one whenever the exponential
compensator dominates the Bernoulli log-MGF at the relevant mean.
-/
theorem adaptiveBernoulli_scalarFactor_le_one
    (rate compensator conditionalMean : ℝ)
    (hmean_nonneg : 0 ≤ conditionalMean)
    (hcompensator : rate * compensator + Real.exp (-rate) - 1 ≤ 0) :
    Real.exp (rate * compensator * conditionalMean) *
      (1 + (Real.exp (-rate) - 1) * conditionalMean) ≤ 1 := by
  calc
    Real.exp (rate * compensator * conditionalMean) *
        (1 + (Real.exp (-rate) - 1) * conditionalMean) ≤
        Real.exp (rate * compensator * conditionalMean) *
          Real.exp ((Real.exp (-rate) - 1) * conditionalMean) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [add_comm] using Real.add_one_le_exp
          ((Real.exp (-rate) - 1) * conditionalMean)
      · exact (Real.exp_pos _).le
    _ = Real.exp ((rate * compensator + Real.exp (-rate) - 1) * conditionalMean) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg hcompensator hmean_nonneg

/-- A valid half-mass compensator at rate `log 2`. -/
theorem adaptiveBernoulli_half_logTwo_scalarFactor_le_one
    (conditionalMean : ℝ) (hmean_nonneg : 0 ≤ conditionalMean) :
    Real.exp (Real.log 2 * ((1 : ℝ) / 2) * conditionalMean) *
      (1 + (Real.exp (-(Real.log 2)) - 1) * conditionalMean) ≤ 1 := by
  apply adaptiveBernoulli_scalarFactor_le_one
  · exact hmean_nonneg
  · have hexp : Real.exp (-(Real.log 2)) = (1 : ℝ) / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hexp]
    nlinarith [Real.log_two_lt_d9]

/--
The half-mass compensator at rate one controls every nonnegative Bernoulli
conditional mean.  Its exponent matches the standard `exp (-L)` adaptive
lower-tail form.
-/
theorem adaptiveBernoulli_half_scalarFactor_le_one
    (conditionalMean : ℝ) (hmean_nonneg : 0 ≤ conditionalMean) :
    Real.exp ((1 : ℝ) * ((1 : ℝ) / 2) * conditionalMean) *
      (1 + (Real.exp (-(1 : ℝ)) - 1) * conditionalMean) ≤ 1 := by
  apply adaptiveBernoulli_scalarFactor_le_one
  · exact hmean_nonneg
  · nlinarith [Real.exp_neg_one_lt_half]

/-- The negative exponential of a zero-one observation has an affine Bernoulli form. -/
theorem exp_neg_mul_eq_one_add_of_eq_zero_or_one
    (rate observation : ℝ) (hobs : observation = 0 ∨ observation = 1) :
    Real.exp (-rate * observation) =
      1 + (Real.exp (-rate) - 1) * observation := by
  rcases hobs with hzero | hone
  · simp [hzero]
  · rw [hone]
    ring

/-- The adaptive exponential factor has its conditional-Bernoulli product form. -/
theorem adaptiveBernoulliExponentialFactor_eq_of_zero_or_one
    {Omega : Type*} (rate compensator : ℝ)
    (observation conditionalMean : ℕ → Omega → ℝ) (n : ℕ) (omega : Omega)
    (hobs : observation n omega = 0 ∨ observation n omega = 1) :
    adaptiveBernoulliExponentialFactor rate compensator observation conditionalMean n omega =
      Real.exp (rate * compensator * conditionalMean n omega) *
        (1 + (Real.exp (-rate) - 1) * observation n omega) := by
  unfold adaptiveBernoulliExponentialFactor
  rw [show -rate * (observation n omega - compensator * conditionalMean n omega) =
    rate * compensator * conditionalMean n omega + -rate * observation n omega by ring,
    Real.exp_add, exp_neg_mul_eq_one_add_of_eq_zero_or_one rate (observation n omega) hobs]

/--
Conditional expectation of the adaptive exponential factor, expressed through
the conditional mean of a zero-one observation.
-/
theorem condExp_adaptiveBernoulliExponentialFactor_eq
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (rate compensator : ℝ) (observation conditionalMean : ℕ → Omega → ℝ) (n : ℕ)
    (hmean_measurable : StronglyMeasurable[filtration n] (conditionalMean n))
    (hobs_integrable : Integrable (observation n) mu)
    (hfactor_integrable : Integrable
      (adaptiveBernoulliExponentialFactor rate compensator observation conditionalMean n) mu)
    (hobs_zero_or_one : ∀ᵐ omega ∂mu,
      observation n omega = 0 ∨ observation n omega = 1)
    (hconditionalMean : mu[observation n | filtration n] =ᵐ[mu] conditionalMean n) :
    mu[adaptiveBernoulliExponentialFactor rate compensator observation conditionalMean n |
      filtration n] =ᵐ[mu]
      fun omega => Real.exp (rate * compensator * conditionalMean n omega) *
        (1 + (Real.exp (-rate) - 1) * conditionalMean n omega) := by
  let coefficient : ℝ := Real.exp (-rate) - 1
  let affineObservation : Omega → ℝ :=
    fun omega => 1 + coefficient * observation n omega
  let predictableScale : Omega → ℝ :=
    fun omega => Real.exp (rate * compensator * conditionalMean n omega)
  have haffine_integrable : Integrable affineObservation mu := by
    have haffine_eq : affineObservation =
        (fun _ : Omega => 1) + coefficient • observation n := by
      funext omega
      simp [affineObservation, coefficient, Pi.smul_apply, smul_eq_mul]
    rw [haffine_eq]
    exact (integrable_const _).add (hobs_integrable.const_mul coefficient)
  have hscale_measurable : StronglyMeasurable[filtration n] predictableScale := by
    change StronglyMeasurable[filtration n]
      (fun omega => Real.exp (rate * compensator * conditionalMean n omega))
    exact (hmean_measurable.const_mul (rate * compensator)).measurable.exp.stronglyMeasurable
  have hfactor_eq :
      adaptiveBernoulliExponentialFactor rate compensator observation conditionalMean n =ᵐ[mu]
        fun omega => predictableScale omega * affineObservation omega := by
    filter_upwards [hobs_zero_or_one] with omega homega
    exact adaptiveBernoulliExponentialFactor_eq_of_zero_or_one rate compensator observation
      conditionalMean n omega homega
  have hproduct_integrable : Integrable
      (fun omega => predictableScale omega * affineObservation omega) mu := by
    apply (integrable_congr hfactor_eq).mp
    exact hfactor_integrable
  have haffine_condExp : mu[affineObservation | filtration n] =ᵐ[mu]
      fun omega => 1 + coefficient * mu[observation n | filtration n] omega := by
    have haffine_eq : affineObservation =
        (fun _ : Omega => 1) + coefficient • observation n := by
      funext omega
      simp [affineObservation, Pi.smul_apply, smul_eq_mul]
    calc
      mu[affineObservation | filtration n] =
          mu[(fun _ : Omega => 1) + coefficient • observation n | filtration n] := by
        rw [haffine_eq]
      _ =ᵐ[mu] mu[(fun _ : Omega => 1) | filtration n] +
          mu[coefficient • observation n | filtration n] :=
        condExp_add (integrable_const _) (hobs_integrable.const_mul coefficient) _
      _ =ᵐ[mu] (fun _ : Omega => 1) + coefficient •
          mu[observation n | filtration n] := by
        rw [condExp_const (filtration.le n) 1]
        exact EventuallyEq.rfl.add (condExp_smul coefficient (observation n) (filtration n))
      _ =ᵐ[mu] fun omega => 1 + coefficient *
          mu[observation n | filtration n] omega := by
        rfl
  calc
    mu[adaptiveBernoulliExponentialFactor rate compensator observation conditionalMean n |
        filtration n] =ᵐ[mu]
        mu[fun omega => predictableScale omega * affineObservation omega |
          filtration n] :=
      condExp_congr_ae hfactor_eq
    _ =ᵐ[mu] fun omega => predictableScale omega * mu[affineObservation | filtration n] omega :=
      condExp_mul_of_stronglyMeasurable_left hscale_measurable hproduct_integrable
        haffine_integrable
    _ =ᵐ[mu] fun omega => predictableScale omega *
        (1 + coefficient * mu[observation n | filtration n] omega) := by
      filter_upwards [haffine_condExp] with omega homega
      rw [homega]
    _ =ᵐ[mu] fun omega => predictableScale omega *
        (1 + coefficient * conditionalMean n omega) := by
      filter_upwards [hconditionalMean] with omega homega
      rw [homega]
    _ =ᵐ[mu] fun omega => Real.exp (rate * compensator * conditionalMean n omega) *
        (1 + (Real.exp (-rate) - 1) * conditionalMean n omega) := by
      rfl

/--
A zero-one adapted observation with nonnegative predictable conditional mean
obeys the half-log-two exponential one-step bound.
-/
theorem adaptiveBernoulli_half_logTwo_factor_condExp_le_one
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation conditionalMean : ℕ → Omega → ℝ) (n : ℕ)
    (hmean_measurable : StronglyMeasurable[filtration n] (conditionalMean n))
    (hobs_integrable : Integrable (observation n) mu)
    (hfactor_integrable : Integrable
      (adaptiveBernoulliExponentialFactor (Real.log 2) ((1 : ℝ) / 2)
        observation conditionalMean n) mu)
    (hobs_zero_or_one : ∀ᵐ omega ∂mu,
      observation n omega = 0 ∨ observation n omega = 1)
    (hconditionalMean : mu[observation n | filtration n] =ᵐ[mu] conditionalMean n)
    (hmean_nonneg : ∀ᵐ omega ∂mu, 0 ≤ conditionalMean n omega) :
    mu[adaptiveBernoulliExponentialFactor (Real.log 2) ((1 : ℝ) / 2)
      observation conditionalMean n | filtration n] ≤ᵐ[mu] fun _ => 1 := by
  have hcondExp := condExp_adaptiveBernoulliExponentialFactor_eq
    (Real.log 2) ((1 : ℝ) / 2) observation conditionalMean n hmean_measurable
    hobs_integrable hfactor_integrable hobs_zero_or_one hconditionalMean
  filter_upwards [hcondExp, hmean_nonneg] with omega hfactor hmean
  rw [hfactor]
  exact adaptiveBernoulli_half_logTwo_scalarFactor_le_one _ hmean

/--
A zero-one adapted observation with nonnegative predictable conditional mean
obeys the rate-one half-mass exponential one-step bound.
-/
theorem adaptiveBernoulli_half_factor_condExp_le_one
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation conditionalMean : ℕ → Omega → ℝ) (n : ℕ)
    (hmean_measurable : StronglyMeasurable[filtration n] (conditionalMean n))
    (hobs_integrable : Integrable (observation n) mu)
    (hfactor_integrable : Integrable
      (adaptiveBernoulliExponentialFactor 1 ((1 : ℝ) / 2)
        observation conditionalMean n) mu)
    (hobs_zero_or_one : ∀ᵐ omega ∂mu,
      observation n omega = 0 ∨ observation n omega = 1)
    (hconditionalMean : mu[observation n | filtration n] =ᵐ[mu] conditionalMean n)
    (hmean_nonneg : ∀ᵐ omega ∂mu, 0 ≤ conditionalMean n omega) :
    mu[adaptiveBernoulliExponentialFactor 1 ((1 : ℝ) / 2)
      observation conditionalMean n | filtration n] ≤ᵐ[mu] fun _ => 1 := by
  have hcondExp := condExp_adaptiveBernoulliExponentialFactor_eq
    1 ((1 : ℝ) / 2) observation conditionalMean n hmean_measurable
    hobs_integrable hfactor_integrable hobs_zero_or_one hconditionalMean
  filter_upwards [hcondExp, hmean_nonneg] with omega hfactor hmean
  rw [hfactor]
  exact adaptiveBernoulli_half_scalarFactor_le_one _ hmean

/--
At a finite first-passage time, the stopped value dominates the threshold on
the event that an adapted process ever reaches that threshold.
-/
theorem smul_le_stoppedValue_hittingBtwn_of_adapted_integrable
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {process : ℕ → Omega → ℝ}
    (hadapted : StronglyAdapted filtration process)
    (hintegrable : ∀ index, Integrable (process index) mu)
    {threshold : ℝ≥0} (n : ℕ) :
    threshold • mu {omega |
      (threshold : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun index => process index omega} ≤
      ENNReal.ofReal (∫ omega in {omega |
        (threshold : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun index => process index omega},
        stoppedValue process
          (fun omega => (hittingBtwn process {value : ℝ | threshold ≤ value} 0 n omega : ℕ))
          omega ∂mu) := by
  have hstop : IsStoppingTime filtration
      (fun omega => (hittingBtwn process {value : ℝ | threshold ≤ value} 0 n omega : ℕ)) :=
    hadapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hstopped_integrable : Integrable
      (stoppedValue process
        (fun omega => (hittingBtwn process {value : ℝ | threshold ≤ value} 0 n omega : ℕ))) mu := by
    exact integrable_stoppedValue ℕ hstop hintegrable (N := n) (by
      intro omega
      have hle : hittingBtwn process {value : ℝ | threshold ≤ value} 0 n omega ≤ n :=
        hittingBtwn_le omega
      exact WithTop.coe_le_coe.mpr hle)
  have hdominates : ∀ omega,
      ((threshold : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun index => process index omega) →
      (threshold : ℝ) ≤ stoppedValue process
        (fun omega => (hittingBtwn process {value : ℝ | threshold ≤ value} 0 n omega : ℕ))
        omega := by
    intro omega homega
    simp_rw [Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff] at homega
    refine stoppedValue_hittingBtwn_mem ?_
    simp only [Set.mem_Icc, zero_le, true_and, Set.mem_setOf_eq]
    exact let ⟨index, hindex, hthreshold⟩ := homega
      ⟨index, hindex, hthreshold⟩
  have hset_integral := setIntegral_ge_of_const_le_real
    (measurableSet_le measurable_const
      (Finset.measurable_range_sup'' fun index _ =>
        (hadapted index).measurable.le (filtration.le index)))
    (measure_ne_top _ _) hdominates hstopped_integrable.integrableOn
  rw [ENNReal.le_ofReal_iff_toReal_le, ENNReal.toReal_smul]
  · exact hset_integral
  · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · exact le_trans (mul_nonneg threshold.coe_nonneg ENNReal.toReal_nonneg) hset_integral

/--
Finite-horizon Ville inequality for a nonnegative supermartingale.  The event
is a first passage above `threshold`; optional stopping bounds the stopped
value by the initial expectation.
-/
theorem supermartingale_maximal_ineq
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {process : ℕ → Omega → ℝ}
    (hsuper : Supermartingale process filtration mu)
    (hnonneg : ∀ index omega, 0 ≤ process index omega)
    {threshold : ℝ≥0} (n : ℕ) :
    threshold * mu {omega |
      (threshold : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun index => process index omega} ≤
      ENNReal.ofReal (∫ omega, process 0 omega ∂mu) := by
  let hittingTime : Omega → WithTop ℕ :=
    fun omega => (hittingBtwn process {value : ℝ | threshold ≤ value} 0 n omega : ℕ)
  let crossingEvent : Set Omega := {omega |
    (threshold : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun index => process index omega}
  have hstop : IsStoppingTime filtration hittingTime := by
    exact hsuper.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have htime_bound : ∀ omega, hittingTime omega ≤ n := by
    intro omega
    dsimp [hittingTime]
    exact WithTop.coe_le_coe.mpr (hittingBtwn_le omega)
  have hstopped_integrable : Integrable (stoppedValue process hittingTime) mu := by
    exact integrable_stoppedValue ℕ hstop hsuper.integrable (N := n) htime_bound
  have hstopped_nonneg : ∀ omega, 0 ≤ stoppedValue process hittingTime omega := by
    intro omega
    simp [hittingTime, stoppedValue, hnonneg]
  have hfirst_passage : threshold * mu crossingEvent ≤
      ENNReal.ofReal (∫ omega in crossingEvent, stoppedValue process hittingTime omega ∂mu) := by
    simpa [crossingEvent, hittingTime] using
      (smul_le_stoppedValue_hittingBtwn_of_adapted_integrable
        hsuper.stronglyAdapted hsuper.integrable (threshold := threshold) n)
  have hstopped_integral_le_initial :
      (∫ omega, stoppedValue process hittingTime omega ∂mu) ≤
        ∫ omega, process 0 omega ∂mu := by
    have hneg := hsuper.neg
    have hoptional := hneg.expected_stoppedValue_mono
      (isStoppingTime_const filtration 0) hstop
      (fun omega => bot_le) htime_bound
    simpa [hittingTime, stoppedValue, integral_neg] using neg_le_neg hoptional
  calc
    threshold * mu crossingEvent ≤
        ENNReal.ofReal (∫ omega in crossingEvent, stoppedValue process hittingTime omega ∂mu) :=
      hfirst_passage
    _ ≤ ENNReal.ofReal (∫ omega, stoppedValue process hittingTime omega ∂mu) :=
      ENNReal.ofReal_le_ofReal
        (setIntegral_le_integral hstopped_integrable (ae_of_all mu hstopped_nonneg))
    _ ≤ ENNReal.ofReal (∫ omega, process 0 omega ∂mu) :=
      ENNReal.ofReal_le_ofReal hstopped_integral_le_initial

/--
A finite-horizon adaptive Bernoulli lower-tail bound.  The event is allowed to
choose its first violating time after seeing the entire trajectory; the
supermartingale maximal inequality, rather than a union bound over times,
supplies the time-uniform control.
-/
theorem measure_adaptiveBernoulli_exists_lowerDeviation_le_exp_neg
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation conditionalMean : ℕ → Omega → ℝ) (logTerm : ℝ)
    (hsuper : Supermartingale
      (adaptiveBernoulliExponentialControl 1 ((1 : ℝ) / 2)
        observation conditionalMean) filtration mu)
    (n : ℕ) :
    mu {omega | ∃ index ≤ n,
      adaptiveBernoulliCount observation index omega <
        (1 / 2 : ℝ) * adaptiveBernoulliMass conditionalMean index omega - logTerm} ≤
      ENNReal.ofReal (Real.exp (-logTerm)) := by
  let control := adaptiveBernoulliExponentialControl 1 ((1 : ℝ) / 2)
    observation conditionalMean
  let threshold : ℝ≥0 := ⟨Real.exp logTerm, (Real.exp_pos logTerm).le⟩
  let crossingEvent : Set Omega := {omega |
    (threshold : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun index => control index omega}
  have hsuper_control : Supermartingale control filtration mu := by
    simpa [control] using hsuper
  have hcontrol_nonneg : ∀ index omega, 0 ≤ control index omega := by
    intro index omega
    exact (Real.exp_pos _).le
  have hcontrol_zero : control 0 = fun _ => 1 := by
    funext omega
    simp [control, adaptiveBernoulliExponentialControl,
      adaptiveBernoulliCount, adaptiveBernoulliMass]
  have hmax : (threshold : ℝ≥0∞) * mu crossingEvent ≤ 1 := by
    have h := supermartingale_maximal_ineq hsuper_control hcontrol_nonneg
      (threshold := threshold) n
    change (threshold : ℝ≥0∞) * mu crossingEvent ≤
      ENNReal.ofReal (∫ omega, control 0 omega ∂mu) at h
    rw [hcontrol_zero] at h
    simpa using h
  have hsubset : {omega | ∃ index ≤ n,
      adaptiveBernoulliCount observation index omega <
        (1 / 2 : ℝ) * adaptiveBernoulliMass conditionalMean index omega - logTerm} ⊆
      crossingEvent := by
    intro omega homega
    rcases homega with ⟨index, hindex, hdeviation⟩
    have hlog : logTerm <
        (1 / 2 : ℝ) * adaptiveBernoulliMass conditionalMean index omega -
          adaptiveBernoulliCount observation index omega := by
      linarith
    have hcontrol_gt : (threshold : ℝ) < control index omega := by
      change Real.exp logTerm <
        Real.exp (-1 *
          (adaptiveBernoulliCount observation index omega -
            (1 / 2 : ℝ) * adaptiveBernoulliMass conditionalMean index omega))
      rw [show -1 *
          (adaptiveBernoulliCount observation index omega -
            (1 / 2 : ℝ) * adaptiveBernoulliMass conditionalMean index omega) =
          (1 / 2 : ℝ) * adaptiveBernoulliMass conditionalMean index omega -
            adaptiveBernoulliCount observation index omega by ring]
      exact Real.exp_lt_exp.mpr hlog
    have hcontrol_le_max : control index omega ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun position => control position omega) := by
      exact (Finset.le_sup'_iff _).mpr ⟨index,
        Finset.mem_range.mpr (Nat.lt_succ_of_le hindex), le_rfl⟩
    exact hcontrol_gt.le.trans hcontrol_le_max
  have hthreshold_ne_zero : (threshold : ℝ≥0∞) ≠ 0 := by
    apply ENNReal.coe_ne_zero.mpr
    apply ne_of_gt
    change 0 < Real.exp logTerm
    exact Real.exp_pos logTerm
  have hthreshold_ne_top : (threshold : ℝ≥0∞) ≠ ∞ := by
    simp
  have hcross : mu crossingEvent ≤ 1 / (threshold : ℝ≥0∞) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hthreshold_ne_zero)
      (Or.inl hthreshold_ne_top)).mpr
    simpa [mul_comm] using hmax
  calc
    mu {omega | ∃ index ≤ n,
        adaptiveBernoulliCount observation index omega <
          (1 / 2 : ℝ) * adaptiveBernoulliMass conditionalMean index omega - logTerm} ≤
        mu crossingEvent := measure_mono hsubset
    _ ≤ 1 / (threshold : ℝ≥0∞) := hcross
    _ = ENNReal.ofReal (Real.exp (-logTerm)) := by
      dsimp only [threshold]
      rw [ENNReal.coe_nnreal_eq]
      change 1 / ENNReal.ofReal (Real.exp logTerm) =
        ENNReal.ofReal (Real.exp (-logTerm))
      rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos logTerm),
        ← Real.exp_neg]
      simp

/--
A finite union of adaptive Bernoulli lower-tail events.  Each coordinate has
the same time-uniform exponential tail, so this is the exact union-bound
layer used when several state, action, or stage coordinates share one
confidence budget.
-/
theorem measure_adaptiveBernoulli_exists_coordinate_lowerDeviation_le_card_mul_exp_neg
    {Coordinate Omega : Type*} [Fintype Coordinate]
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation conditionalMean : Coordinate → ℕ → Omega → ℝ) (logTerm : ℝ)
    (hsuper : ∀ coordinate, Supermartingale
      (adaptiveBernoulliExponentialControl 1 ((1 : ℝ) / 2)
        (observation coordinate) (conditionalMean coordinate)) filtration mu)
    (n : ℕ) :
    mu {omega | ∃ coordinate index, index ≤ n ∧
      adaptiveBernoulliCount (observation coordinate) index omega <
        (1 / 2 : ℝ) * adaptiveBernoulliMass (conditionalMean coordinate) index omega -
          logTerm} ≤
      (Fintype.card Coordinate : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-logTerm)) := by
  classical
  let badEvent : Coordinate → Set Omega := fun coordinate => {omega | ∃ index ≤ n,
    adaptiveBernoulliCount (observation coordinate) index omega <
      (1 / 2 : ℝ) * adaptiveBernoulliMass (conditionalMean coordinate) index omega - logTerm}
  have hbad : ∀ coordinate,
      mu (badEvent coordinate) ≤ ENNReal.ofReal (Real.exp (-logTerm)) := by
    intro coordinate
    exact measure_adaptiveBernoulli_exists_lowerDeviation_le_exp_neg
      (observation coordinate) (conditionalMean coordinate) logTerm (hsuper coordinate) n
  calc
    mu {omega | ∃ coordinate index, index ≤ n ∧
        adaptiveBernoulliCount (observation coordinate) index omega <
          (1 / 2 : ℝ) * adaptiveBernoulliMass (conditionalMean coordinate) index omega -
            logTerm} = mu (⋃ coordinate, badEvent coordinate) := by
      congr 1
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨coordinate, index, hindex, hdeviation⟩
        exact ⟨coordinate, index, hindex, hdeviation⟩
      · rintro ⟨coordinate, index, hindex, hdeviation⟩
        exact ⟨coordinate, index, hindex, hdeviation⟩
    _ ≤ ∑ coordinate, mu (badEvent coordinate) :=
      measure_iUnion_fintype_le mu badEvent
    _ ≤ ∑ _coordinate : Coordinate, ENNReal.ofReal (Real.exp (-logTerm)) := by
      exact Finset.sum_le_sum fun coordinate _ => hbad coordinate
    _ = (Fintype.card Coordinate : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-logTerm)) := by
      simp

/--
If every adapted one-step multiplier has conditional expectation at most one,
the corresponding exponential count control is a supermartingale.
-/
theorem supermartingale_adaptiveBernoulliExponentialControl
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (rate compensator : ℝ) (observation conditionalMean : ℕ → Omega → ℝ)
    (hobs : StronglyAdapted filtration observation)
    (hmean : StronglyAdapted filtration conditionalMean)
    (hcontrol_integrable : ∀ n,
      Integrable (adaptiveBernoulliExponentialControl rate compensator observation conditionalMean n) mu)
    (hfactor_integrable : ∀ n,
      Integrable (adaptiveBernoulliExponentialFactor rate compensator observation conditionalMean n) mu)
    (hfactor_condExp : ∀ n,
      mu[adaptiveBernoulliExponentialFactor rate compensator observation conditionalMean n |
        filtration n] ≤ᵐ[mu] fun _ => 1) :
    Supermartingale
      (adaptiveBernoulliExponentialControl rate compensator observation conditionalMean)
      filtration mu := by
  apply supermartingale_nat
    (stronglyAdapted_adaptiveBernoulliExponentialControl filtration rate compensator observation
      conditionalMean hobs hmean)
    hcontrol_integrable
  intro n
  have hstep := adaptiveBernoulliExponentialControl_succ rate compensator observation
    conditionalMean n
  have hproduct_integrable : Integrable
      (fun omega =>
        adaptiveBernoulliExponentialControl rate compensator observation conditionalMean n omega *
          adaptiveBernoulliExponentialFactor rate compensator observation conditionalMean n omega) mu := by
    apply (integrable_congr (Filter.Eventually.of_forall fun omega =>
      congrFun hstep omega)).mp
    exact hcontrol_integrable (n + 1)
  calc
    mu[adaptiveBernoulliExponentialControl rate compensator observation conditionalMean (n + 1) |
        filtration n] =ᵐ[mu]
        mu[fun omega =>
          adaptiveBernoulliExponentialControl rate compensator observation conditionalMean n omega *
            adaptiveBernoulliExponentialFactor rate compensator observation conditionalMean n omega |
          filtration n] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun omega => congrFun hstep omega)
    _ =ᵐ[mu] fun omega =>
        adaptiveBernoulliExponentialControl rate compensator observation conditionalMean n omega *
          mu[adaptiveBernoulliExponentialFactor rate compensator observation conditionalMean n |
            filtration n] omega :=
      condExp_mul_of_stronglyMeasurable_left
        (stronglyAdapted_adaptiveBernoulliExponentialControl filtration rate compensator observation
          conditionalMean hobs hmean n)
        hproduct_integrable (hfactor_integrable n)
    _ ≤ᵐ[mu]
        adaptiveBernoulliExponentialControl rate compensator observation conditionalMean n := by
      filter_upwards [hfactor_condExp n] with omega hfactor
      have hcontrol_nonneg : 0 ≤
          adaptiveBernoulliExponentialControl rate compensator observation conditionalMean n omega := by
        unfold adaptiveBernoulliExponentialControl
        exact (Real.exp_pos _).le
      simpa using mul_le_mul_of_nonneg_left hfactor hcontrol_nonneg

/--
The adaptive Bernoulli lower-tail bound obtained from the actual conditional
mean identity.  The assumptions state the measurability and integrability
needed to construct the exponential supermartingale; they do not package the
tail event or its probability bound.
-/
theorem measure_adaptiveBernoulli_exists_lowerDeviation_le_exp_neg_of_condExp
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation conditionalMean : ℕ → Omega → ℝ) (logTerm : ℝ)
    (hobs : StronglyAdapted filtration observation)
    (hmean : StronglyAdapted filtration conditionalMean)
    (hcontrol_integrable : ∀ index,
      Integrable (adaptiveBernoulliExponentialControl 1 ((1 : ℝ) / 2)
        observation conditionalMean index) mu)
    (hfactor_integrable : ∀ index,
      Integrable (adaptiveBernoulliExponentialFactor 1 ((1 : ℝ) / 2)
        observation conditionalMean index) mu)
    (hobs_integrable : ∀ index, Integrable (observation index) mu)
    (hobs_zero_or_one : ∀ index, ∀ᵐ omega ∂mu,
      observation index omega = 0 ∨ observation index omega = 1)
    (hconditionalMean : ∀ index,
      mu[observation index | filtration index] =ᵐ[mu] conditionalMean index)
    (hmean_nonneg : ∀ index, ∀ᵐ omega ∂mu, 0 ≤ conditionalMean index omega)
    (n : ℕ) :
    mu {omega | ∃ index ≤ n,
      adaptiveBernoulliCount observation index omega <
        (1 / 2 : ℝ) * adaptiveBernoulliMass conditionalMean index omega - logTerm} ≤
      ENNReal.ofReal (Real.exp (-logTerm)) := by
  apply measure_adaptiveBernoulli_exists_lowerDeviation_le_exp_neg
    (filtration := filtration) observation conditionalMean logTerm ?_ n
  apply supermartingale_adaptiveBernoulliExponentialControl
    1 ((1 : ℝ) / 2) observation conditionalMean hobs hmean
    hcontrol_integrable hfactor_integrable
  intro index
  exact adaptiveBernoulli_half_factor_condExp_le_one observation conditionalMean index
    (hmean index) (hobs_integrable index) (hfactor_integrable index)
    (hobs_zero_or_one index) (hconditionalMean index) (hmean_nonneg index)

/--
The adaptive Bernoulli bound with a canonical predictable mean constructed
from conditional expectation.  For a pointwise zero-one adapted observation,
all auxiliary adaptedness, integrability, range, and conditional-mean facts
are derived rather than supplied as a concentration certificate.
-/
theorem measure_adaptiveBernoulli_exists_lowerDeviation_le_exp_neg_of_adapted_zeroOne
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation : ℕ → Omega → ℝ) (logTerm : ℝ)
    (hobs : StronglyAdapted filtration observation)
    (hobs_zero_or_one : ∀ index omega,
      observation index omega = 0 ∨ observation index omega = 1)
    (n : ℕ) :
    mu {omega | ∃ index ≤ n,
      adaptiveBernoulliCount observation index omega <
        (1 / 2 : ℝ) * adaptiveBernoulliMass
          (adaptiveBernoulliClippedConditionalMean mu filtration observation) index omega -
          logTerm} ≤ ENNReal.ofReal (Real.exp (-logTerm)) := by
  let conditionalMean := adaptiveBernoulliClippedConditionalMean mu filtration observation
  have hmean : StronglyAdapted filtration conditionalMean :=
    stronglyAdapted_adaptiveBernoulliClippedConditionalMean observation
  apply measure_adaptiveBernoulli_exists_lowerDeviation_le_exp_neg_of_condExp
    observation conditionalMean logTerm hobs hmean ?_ ?_ ?_ ?_ ?_ ?_ n
  · intro index
    exact integrable_adaptiveBernoulli_half_exponentialControl_of_unitInterval
      observation conditionalMean hobs hmean hobs_zero_or_one
      (fun time omega => adaptiveBernoulliClippedConditionalMean_unitInterval observation time omega)
      index
  · intro index
    exact integrable_adaptiveBernoulli_half_exponentialFactor_of_unitInterval
      observation conditionalMean hobs hmean hobs_zero_or_one
      (fun time omega => adaptiveBernoulliClippedConditionalMean_unitInterval observation time omega)
      index
  · intro index
    exact integrable_adaptiveBernoulli_zeroOne_observation observation hobs hobs_zero_or_one index
  · intro index
    exact Filter.Eventually.of_forall fun omega => hobs_zero_or_one index omega
  · intro index
    exact condExp_ae_eq_adaptiveBernoulliClippedConditionalMean_of_zeroOne
      observation hobs hobs_zero_or_one index
  · intro index
    exact Filter.Eventually.of_forall fun omega =>
      (adaptiveBernoulliClippedConditionalMean_unitInterval observation index omega).1

/--
The finite-coordinate union bound for canonical conditional means of adapted
zero-one observations.  No coordinate is assigned a separate concentration
certificate: each predictable mean is built from its own conditional
expectation under the common history filtration.
-/
theorem measure_adaptiveBernoulli_exists_coordinate_lowerDeviation_le_card_mul_exp_neg_of_adapted_zeroOne
    {Coordinate Omega : Type*} [Fintype Coordinate]
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation : Coordinate → ℕ → Omega → ℝ) (logTerm : ℝ)
    (hobs : ∀ coordinate, StronglyAdapted filtration (observation coordinate))
    (hobs_zero_or_one : ∀ coordinate index omega,
      observation coordinate index omega = 0 ∨ observation coordinate index omega = 1)
    (n : ℕ) :
    mu {omega | ∃ coordinate index, index ≤ n ∧
      adaptiveBernoulliCount (observation coordinate) index omega <
        (1 / 2 : ℝ) * adaptiveBernoulliMass
          (adaptiveBernoulliClippedConditionalMean mu filtration (observation coordinate))
          index omega - logTerm} ≤
      (Fintype.card Coordinate : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-logTerm)) := by
  classical
  let badEvent : Coordinate → Set Omega := fun coordinate => {omega | ∃ index ≤ n,
    adaptiveBernoulliCount (observation coordinate) index omega <
      (1 / 2 : ℝ) * adaptiveBernoulliMass
        (adaptiveBernoulliClippedConditionalMean mu filtration (observation coordinate))
        index omega - logTerm}
  have hbad : ∀ coordinate,
      mu (badEvent coordinate) ≤ ENNReal.ofReal (Real.exp (-logTerm)) := by
    intro coordinate
    exact measure_adaptiveBernoulli_exists_lowerDeviation_le_exp_neg_of_adapted_zeroOne
      (observation coordinate) logTerm (hobs coordinate)
      (fun index omega => hobs_zero_or_one coordinate index omega) n
  calc
    mu {omega | ∃ coordinate index, index ≤ n ∧
        adaptiveBernoulliCount (observation coordinate) index omega <
          (1 / 2 : ℝ) * adaptiveBernoulliMass
            (adaptiveBernoulliClippedConditionalMean mu filtration (observation coordinate))
            index omega - logTerm} =
        mu (⋃ coordinate, badEvent coordinate) := by
      congr 1
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨coordinate, index, hindex, hdeviation⟩
        exact ⟨coordinate, index, hindex, hdeviation⟩
      · rintro ⟨coordinate, index, hindex, hdeviation⟩
        exact ⟨coordinate, index, hindex, hdeviation⟩
    _ ≤ ∑ coordinate, mu (badEvent coordinate) :=
      measure_iUnion_fintype_le mu badEvent
    _ ≤ ∑ _coordinate : Coordinate, ENNReal.ofReal (Real.exp (-logTerm)) := by
      exact Finset.sum_le_sum fun coordinate _ => hbad coordinate
    _ = (Fintype.card Coordinate : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-logTerm)) := by
      simp

/--
The finite-coordinate adaptive Bernoulli union bound derived directly from
each coordinate's conditional-mean identity.  This is the usable form when a
model supplies the individual adapted observations rather than preassembled
supermartingales.
-/
theorem measure_adaptiveBernoulli_exists_coordinate_lowerDeviation_le_card_mul_exp_neg_of_condExp
    {Coordinate Omega : Type*} [Fintype Coordinate]
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation conditionalMean : Coordinate → ℕ → Omega → ℝ) (logTerm : ℝ)
    (hobs : ∀ coordinate, StronglyAdapted filtration (observation coordinate))
    (hmean : ∀ coordinate, StronglyAdapted filtration (conditionalMean coordinate))
    (hcontrol_integrable : ∀ coordinate index,
      Integrable (adaptiveBernoulliExponentialControl 1 ((1 : ℝ) / 2)
        (observation coordinate) (conditionalMean coordinate) index) mu)
    (hfactor_integrable : ∀ coordinate index,
      Integrable (adaptiveBernoulliExponentialFactor 1 ((1 : ℝ) / 2)
        (observation coordinate) (conditionalMean coordinate) index) mu)
    (hobs_integrable : ∀ coordinate index, Integrable (observation coordinate index) mu)
    (hobs_zero_or_one : ∀ coordinate index, ∀ᵐ omega ∂mu,
      observation coordinate index omega = 0 ∨ observation coordinate index omega = 1)
    (hconditionalMean : ∀ coordinate index,
      mu[observation coordinate index | filtration index] =ᵐ[mu]
        conditionalMean coordinate index)
    (hmean_nonneg : ∀ coordinate index, ∀ᵐ omega ∂mu,
      0 ≤ conditionalMean coordinate index omega)
    (n : ℕ) :
    mu {omega | ∃ coordinate index, index ≤ n ∧
      adaptiveBernoulliCount (observation coordinate) index omega <
        (1 / 2 : ℝ) * adaptiveBernoulliMass (conditionalMean coordinate) index omega -
          logTerm} ≤
      (Fintype.card Coordinate : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-logTerm)) := by
  apply measure_adaptiveBernoulli_exists_coordinate_lowerDeviation_le_card_mul_exp_neg
    (filtration := filtration) observation conditionalMean logTerm ?_ n
  intro coordinate
  apply supermartingale_adaptiveBernoulliExponentialControl
    1 ((1 : ℝ) / 2) (observation coordinate) (conditionalMean coordinate)
    (hobs coordinate) (hmean coordinate)
    (hcontrol_integrable coordinate) (hfactor_integrable coordinate)
  intro index
  exact adaptiveBernoulli_half_factor_condExp_le_one
    (observation coordinate) (conditionalMean coordinate) index
    (hmean coordinate index) (hobs_integrable coordinate index)
    (hfactor_integrable coordinate index) (hobs_zero_or_one coordinate index)
    (hconditionalMean coordinate index) (hmean_nonneg coordinate index)

end Probability
end AppliedModelingLib
