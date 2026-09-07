import AppliedModelingLib.Foundations.Probability.AdaptiveBernoulli

/-!
# Predictable adaptive Bernoulli counts

This module uses the natural episodic timing for adaptive visit counts.  The
`n`th observation is revealed in the passage from history `n` to history
`n + 1`, while its predictable mean is measurable at history `n`.  Thus the
partial count through indices strictly below `n` is adapted at history `n`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators MeasureTheory NNReal ENNReal

namespace AppliedModelingLib
namespace Probability

/-- An observation at index `n` is revealed by the next history sigma-field. -/
abbrev NextStronglyAdapted
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (observation : ℕ → Omega → ℝ) : Prop :=
  ∀ n, StronglyMeasurable[filtration (n + 1)] (observation n)

/-- A general-valued observation is revealed by the next history sigma-field. -/
abbrev NextAdapted
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {B : Type*} [MeasurableSpace B]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (observation : ℕ → Omega → B) : Prop :=
  ∀ n, Measurable[filtration (n + 1)] (observation n)

/-- A partial count is adapted when each new observation is revealed one step later. -/
theorem stronglyAdapted_adaptiveBernoulliCount_of_next
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (observation : ℕ → Omega → ℝ)
    (hobs : NextStronglyAdapted filtration observation) :
    StronglyAdapted filtration (adaptiveBernoulliCount observation) := by
  intro n
  change StronglyMeasurable[filtration n]
    (fun omega => ∑ index ∈ Finset.range n, observation index omega)
  convert Finset.stronglyMeasurable_sum (Finset.range n) (fun index hindex =>
    (hobs index).mono
      (filtration.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hindex)))) using 1
  funext omega
  simp only [Finset.sum_apply]

/-- The exponential count control is adapted at the pre-next-episode history. -/
theorem stronglyAdapted_adaptiveBernoulliExponentialControl_of_next
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (rate compensator : ℝ) (observation conditionalMean : ℕ → Omega → ℝ)
    (hobs : NextStronglyAdapted filtration observation)
    (hmean : StronglyAdapted filtration conditionalMean) :
    StronglyAdapted filtration
      (adaptiveBernoulliExponentialControl rate compensator observation conditionalMean) := by
  intro n
  change StronglyMeasurable[filtration n]
    (fun omega => Real.exp (-rate *
      (adaptiveBernoulliCount observation n omega -
        compensator * adaptiveBernoulliMass conditionalMean n omega)))
  exact ((stronglyAdapted_adaptiveBernoulliCount_of_next filtration observation hobs n).sub
    ((stronglyAdapted_adaptiveBernoulliMass filtration conditionalMean hmean n).const_mul
      compensator)).const_mul (-rate) |>.measurable.exp.stronglyMeasurable

/-- A zero-one observation revealed at the next history is integrable. -/
theorem integrable_adaptiveBernoulli_zeroOne_observation_of_next
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation : ℕ → Omega → ℝ) (hobs : NextStronglyAdapted filtration observation)
    (hobs_zero_or_one : ∀ index omega,
      observation index omega = 0 ∨ observation index omega = 1)
    (n : ℕ) : Integrable (observation n) mu := by
  have hmeasurable : Measurable (observation n) :=
    (hobs n).measurable.le (filtration.le (n + 1))
  refine Integrable.of_bound hmeasurable.aestronglyMeasurable 1 ?_
  filter_upwards with omega
  rcases hobs_zero_or_one n omega with hzero | hone
  · simp [hzero]
  · simp [hone]

/-- The one-step half-mass factor is integrable under the natural episodic timing. -/
theorem integrable_adaptiveBernoulli_half_exponentialFactor_of_next
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation conditionalMean : ℕ → Omega → ℝ)
    (hobs : NextStronglyAdapted filtration observation)
    (hmean : StronglyAdapted filtration conditionalMean)
    (hobs_zero_or_one : ∀ index omega,
      observation index omega = 0 ∨ observation index omega = 1)
    (hmean_unitInterval : ∀ index omega,
      0 ≤ conditionalMean index omega ∧ conditionalMean index omega ≤ 1)
    (n : ℕ) :
    Integrable (adaptiveBernoulliExponentialFactor 1 ((1 : ℝ) / 2)
      observation conditionalMean n) mu := by
  have hobs_measurable : Measurable (observation n) :=
    (hobs n).measurable.le (filtration.le (n + 1))
  have hmean_measurable : Measurable (conditionalMean n) :=
    (hmean n).measurable.le (filtration.le n)
  have hfactor_measurable : Measurable
      (adaptiveBernoulliExponentialFactor 1 ((1 : ℝ) / 2)
        observation conditionalMean n) := by
    change Measurable (fun omega => Real.exp (-1 *
      (observation n omega - ((1 : ℝ) / 2) * conditionalMean n omega)))
    exact ((hobs_measurable.sub (hmean_measurable.const_mul ((1 : ℝ) / 2))).const_mul
      (-1)).exp
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

/-- The finite-time half-mass count control is integrable under natural timing. -/
theorem integrable_adaptiveBernoulli_half_exponentialControl_of_next
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation conditionalMean : ℕ → Omega → ℝ)
    (hobs : NextStronglyAdapted filtration observation)
    (hmean : StronglyAdapted filtration conditionalMean)
    (hobs_zero_or_one : ∀ index omega,
      observation index omega = 0 ∨ observation index omega = 1)
    (hmean_unitInterval : ∀ index omega,
      0 ≤ conditionalMean index omega ∧ conditionalMean index omega ≤ 1)
    (n : ℕ) :
    Integrable (adaptiveBernoulliExponentialControl 1 ((1 : ℝ) / 2)
      observation conditionalMean n) mu := by
  have hcontrol_adapted := stronglyAdapted_adaptiveBernoulliExponentialControl_of_next filtration
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

/-- The canonical clipped conditional mean agrees a.e. with the next-step conditional mean. -/
theorem condExp_ae_eq_adaptiveBernoulliClippedConditionalMean_of_next
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation : ℕ → Omega → ℝ) (hobs : NextStronglyAdapted filtration observation)
    (hobs_zero_or_one : ∀ index omega,
      observation index omega = 0 ∨ observation index omega = 1)
    (n : ℕ) :
    mu[observation n | filtration n] =ᵐ[mu]
      adaptiveBernoulliClippedConditionalMean mu filtration observation n := by
  have hobs_integrable : Integrable (observation n) mu :=
    integrable_adaptiveBernoulli_zeroOne_observation_of_next observation hobs hobs_zero_or_one n
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

/-- The exponential count control is a supermartingale under next-history observations. -/
theorem supermartingale_adaptiveBernoulliExponentialControl_of_next
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (rate compensator : ℝ) (observation conditionalMean : ℕ → Omega → ℝ)
    (hobs : NextStronglyAdapted filtration observation)
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
    (stronglyAdapted_adaptiveBernoulliExponentialControl_of_next filtration rate compensator observation
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
        (stronglyAdapted_adaptiveBernoulliExponentialControl_of_next filtration rate compensator
          observation conditionalMean hobs hmean n)
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
The adaptive lower-tail visit bound with the source timing: visit `n` is
revealed after conditioning on the history at `n`.
-/
theorem measure_adaptiveBernoulli_exists_lowerDeviation_le_exp_neg_of_nextAdapted_zeroOne
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation : ℕ → Omega → ℝ) (logTerm : ℝ)
    (hobs : NextStronglyAdapted filtration observation)
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
  apply measure_adaptiveBernoulli_exists_lowerDeviation_le_exp_neg
    (filtration := filtration) observation conditionalMean logTerm ?_ n
  apply supermartingale_adaptiveBernoulliExponentialControl_of_next
    1 ((1 : ℝ) / 2) observation conditionalMean hobs hmean
  · intro index
    exact integrable_adaptiveBernoulli_half_exponentialControl_of_next
      observation conditionalMean hobs hmean hobs_zero_or_one
      (fun time omega => adaptiveBernoulliClippedConditionalMean_unitInterval observation time omega)
      index
  · intro index
    exact integrable_adaptiveBernoulli_half_exponentialFactor_of_next
      observation conditionalMean hobs hmean hobs_zero_or_one
      (fun time omega => adaptiveBernoulliClippedConditionalMean_unitInterval observation time omega)
      index
  · intro index
    exact adaptiveBernoulli_half_factor_condExp_le_one observation conditionalMean index
      (hmean index)
      (integrable_adaptiveBernoulli_zeroOne_observation_of_next observation hobs hobs_zero_or_one index)
      (integrable_adaptiveBernoulli_half_exponentialFactor_of_next
        observation conditionalMean hobs hmean hobs_zero_or_one
        (fun time omega => adaptiveBernoulliClippedConditionalMean_unitInterval observation time omega)
        index)
      (Filter.Eventually.of_forall fun omega => hobs_zero_or_one index omega)
      (condExp_ae_eq_adaptiveBernoulliClippedConditionalMean_of_next
        observation hobs hobs_zero_or_one index)
      (Filter.Eventually.of_forall fun omega =>
        (adaptiveBernoulliClippedConditionalMean_unitInterval observation index omega).1)

/-- The source-timed finite-coordinate adaptive visitation union bound. -/
theorem measure_adaptiveBernoulli_exists_coordinate_lowerDeviation_le_card_mul_exp_neg_of_nextAdapted_zeroOne
    {Coordinate Omega : Type*} [Fintype Coordinate]
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    (observation : Coordinate → ℕ → Omega → ℝ) (logTerm : ℝ)
    (hobs : ∀ coordinate, NextStronglyAdapted filtration (observation coordinate))
    (hobs_zero_or_one : ∀ coordinate index omega,
      observation coordinate index omega = 0 ∨ observation coordinate index omega = 1)
    (n : ℕ) :
    mu {omega | ∃ coordinate index, index ≤ n ∧
      adaptiveBernoulliCount (observation coordinate) index omega <
        (1 / 2 : ℝ) * adaptiveBernoulliMass
          (adaptiveBernoulliClippedConditionalMean mu filtration (observation coordinate))
          index omega - logTerm} ≤
      (Fintype.card Coordinate : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-logTerm)) := by
  apply measure_adaptiveBernoulli_exists_coordinate_lowerDeviation_le_card_mul_exp_neg
    (filtration := filtration) observation
      (fun coordinate => adaptiveBernoulliClippedConditionalMean mu filtration (observation coordinate))
      logTerm ?_ n
  intro coordinate
  let conditionalMean := adaptiveBernoulliClippedConditionalMean mu filtration (observation coordinate)
  have hmean : StronglyAdapted filtration conditionalMean :=
    stronglyAdapted_adaptiveBernoulliClippedConditionalMean (observation coordinate)
  apply supermartingale_adaptiveBernoulliExponentialControl_of_next
    1 ((1 : ℝ) / 2) (observation coordinate) conditionalMean (hobs coordinate) hmean
  · intro index
    exact integrable_adaptiveBernoulli_half_exponentialControl_of_next
      (observation coordinate) conditionalMean (hobs coordinate) hmean
      (fun time omega => hobs_zero_or_one coordinate time omega)
      (fun time omega => adaptiveBernoulliClippedConditionalMean_unitInterval
        (observation coordinate) time omega) index
  · intro index
    exact integrable_adaptiveBernoulli_half_exponentialFactor_of_next
      (observation coordinate) conditionalMean (hobs coordinate) hmean
      (fun time omega => hobs_zero_or_one coordinate time omega)
      (fun time omega => adaptiveBernoulliClippedConditionalMean_unitInterval
        (observation coordinate) time omega) index
  · intro index
    exact adaptiveBernoulli_half_factor_condExp_le_one (observation coordinate) conditionalMean index
      (hmean index)
      (integrable_adaptiveBernoulli_zeroOne_observation_of_next
        (observation coordinate) (hobs coordinate)
        (fun time omega => hobs_zero_or_one coordinate time omega) index)
      (integrable_adaptiveBernoulli_half_exponentialFactor_of_next
        (observation coordinate) conditionalMean (hobs coordinate) hmean
        (fun time omega => hobs_zero_or_one coordinate time omega)
        (fun time omega => adaptiveBernoulliClippedConditionalMean_unitInterval
          (observation coordinate) time omega) index)
      (Filter.Eventually.of_forall fun omega => hobs_zero_or_one coordinate index omega)
      (condExp_ae_eq_adaptiveBernoulliClippedConditionalMean_of_next
        (observation coordinate) (hobs coordinate)
        (fun time omega => hobs_zero_or_one coordinate time omega) index)
      (Filter.Eventually.of_forall fun omega =>
        (adaptiveBernoulliClippedConditionalMean_unitInterval
          (observation coordinate) index omega).1)

end Probability
end AppliedModelingLib
