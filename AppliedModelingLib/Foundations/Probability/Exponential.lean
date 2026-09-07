import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

namespace AppliedModelingLib
namespace Probability
namespace Exponential

open scoped BigOperators ENNReal

/-!
# Exponential Distribution Model

Reusable wrappers around mathlib's exponential distribution on `ℝ`, plus the
standard harmonic closed form used by top-one exponential order-statistic
models.

## Main declarations

- `Model`: a positive-rate exponential distribution model.
- `Model.measure`: the mathlib exponential probability measure.
- `harmonicReal`: real harmonic numbers.
- `maxSurvivalOfRate`: analytic survival function for the maximum of `q`
  rate-`rate` exponential draws, expressed from the exponential CDF.
- `finiteSampleMax`: finite maximum of a nonempty iid sample.
- `Model.iidMaxSurvival_eq_maxSurvivalOfRate`: product-measure derivation of
  the analytic maximum-survival expression.
- `Model.iidProductMeasure_finiteSampleMax_tailIntegral_eq_expectedMaxValue`:
  the layer-cake tail-integral side for the finite iid maximum.
- `maxSurvivalOfRate_expansion`: binomial expansion of that survival function
  into finitely many exponential-tail terms.
- `integral_exp_neg_mul_Ioi`: the basic exponential-tail integral.
- `alternating_choose_succ_div_eq_harmonicReal`: the finite
  alternating-binomial identity for harmonic numbers.
- `maxSurvivalOfRate_integral_eq_expectedMaxValueOfRate`: the all-`q`
  analytic maximum-survival integral in harmonic closed form.
- `expectedMaxValueOfRate`: the standard closed-form expected maximum value
  `H_q / rate` for `q` i.i.d. rate-`rate` exponential draws.
-/

/-- On the nonnegative half-line, the real exponential density has its usual
elementary form.  This small normalization lemma is useful when converting a
first-event renewal equation to an interval convolution. -/
theorem exponentialPDFReal_eq_rate_mul_exp_of_nonneg
    (rate x : ℝ) (hx : 0 ≤ x) :
    ProbabilityTheory.exponentialPDFReal rate x =
      rate * Real.exp (-(rate * x)) := by
  simp [ProbabilityTheory.exponentialPDFReal, ProbabilityTheory.gammaPDFReal, hx]

/-- A first-event exponential-density integral with the natural residual-time
indicator is exactly its compact interval convolution when the horizon is
nonnegative.  No regularity of `g` is required for this support
normalization. -/
theorem integral_pdfReal_mul_indicator_eq_setIntegral_Icc_convolution
    (rate t : ℝ) (ht : 0 ≤ t) (g : ℝ → ℝ) :
    ∫ h, ProbabilityTheory.exponentialPDFReal rate h *
      (Set.Iic t).indicator (fun h => g (t - h)) h =
      ∫ h in Set.Icc 0 t, rate * Real.exp (-(rate * h)) * g (t - h) := by
  calc
    ∫ h, ProbabilityTheory.exponentialPDFReal rate h *
        (Set.Iic t).indicator (fun h => g (t - h)) h =
        ∫ h, (Set.Icc 0 t).indicator
          (fun h => rate * Real.exp (-(rate * h)) * g (t - h)) h := by
          apply MeasureTheory.integral_congr_ae
          apply Filter.Eventually.of_forall
          intro h
          change ProbabilityTheory.exponentialPDFReal rate h *
            (Set.Iic t).indicator (fun h => g (t - h)) h =
              (Set.Icc 0 t).indicator
                (fun h => rate * Real.exp (-(rate * h)) * g (t - h)) h
          by_cases hnonneg : 0 ≤ h
          · by_cases hle : h ≤ t
            · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hle),
                Set.indicator_of_mem (show h ∈ Set.Icc 0 t from ⟨hnonneg, hle⟩),
                exponentialPDFReal_eq_rate_mul_exp_of_nonneg rate h hnonneg]
            · rw [Set.indicator_of_notMem (Set.mem_Iic.not.mpr hle)]
              simp [Set.indicator_of_notMem
                (show h ∉ Set.Icc 0 t from fun hh => hle hh.2)]
          · rw [show ProbabilityTheory.exponentialPDFReal rate h = 0 by
              simp [ProbabilityTheory.exponentialPDFReal,
                ProbabilityTheory.gammaPDFReal, hnonneg]]
            simp [Set.indicator_of_notMem
              (show h ∉ Set.Icc 0 t from fun hh => hnonneg hh.1)]
    _ = ∫ h in Set.Icc 0 t, rate * Real.exp (-(rate * h)) * g (t - h) := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]

/-- Reversing time in a compact exponential convolution turns it into an
exponentially weighted primitive.  The equality is purely analytic and holds
for an arbitrary real integrand, including a merely measurable endpoint
probability. -/
theorem setIntegral_Icc_exponential_convolution_eq_weighted_primitive
    (rate t : ℝ) (ht : 0 ≤ t) (g : ℝ → ℝ) :
    ∫ h in Set.Icc 0 t, rate * Real.exp (-(rate * h)) * g (t - h) =
      (rate * Real.exp (-(rate * t))) *
        ∫ u in Set.Icc 0 t, Real.exp (rate * u) * g u := by
  let F : ℝ → ℝ := fun u => rate * Real.exp (-(rate * (t - u))) * g u
  have hreverse :
      ∫ h in (0 : ℝ)..t, rate * Real.exp (-(rate * h)) * g (t - h) =
        ∫ u in (0 : ℝ)..t, F u := by
    have hchange := intervalIntegral.integral_comp_sub_left (f := F)
      (a := (0 : ℝ)) (b := t) t
    simpa [F, sub_sub_cancel] using hchange
  calc
    ∫ h in Set.Icc 0 t, rate * Real.exp (-(rate * h)) * g (t - h) =
        ∫ h in Set.Ioc 0 t, rate * Real.exp (-(rate * h)) * g (t - h) :=
          MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ h in (0 : ℝ)..t, rate * Real.exp (-(rate * h)) * g (t - h) := by
          rw [intervalIntegral.integral_of_le ht]
    _ = ∫ u in (0 : ℝ)..t, F u := hreverse
    _ = ∫ u in (0 : ℝ)..t,
        (rate * Real.exp (-(rate * t))) * (Real.exp (rate * u) * g u) := by
          apply intervalIntegral.integral_congr_ae
          apply Filter.Eventually.of_forall
          intro u
          intro _
          dsimp [F]
          have hexp :
              Real.exp (-(rate * (t - u))) =
                Real.exp (-(rate * t)) * Real.exp (rate * u) := by
            rw [show -(rate * (t - u)) = -(rate * t) + rate * u by ring,
              Real.exp_add]
          rw [hexp]
          ring
    _ = (rate * Real.exp (-(rate * t))) *
        ∫ u in (0 : ℝ)..t, Real.exp (rate * u) * g u := by
          rw [intervalIntegral.integral_const_mul]
    _ = (rate * Real.exp (-(rate * t))) *
        ∫ u in Set.Icc 0 t, Real.exp (rate * u) * g u := by
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
            intervalIntegral.integral_of_le ht]

/-- A positive-rate exponential distribution model. -/
structure Model where
  rate : ℝ
  rate_pos : 0 < rate

namespace Model

/-- The mathlib exponential probability measure associated with a model. -/
noncomputable def measure (M : Model) : MeasureTheory.Measure ℝ :=
  ProbabilityTheory.expMeasure M.rate

theorem isProbabilityMeasure_measure (M : Model) :
    MeasureTheory.IsProbabilityMeasure M.measure :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure M.rate_pos

/-- CDF of the positive-rate exponential model. -/
theorem cdf_eq (M : Model) (x : ℝ) :
    ProbabilityTheory.cdf M.measure x =
      if 0 ≤ x then 1 - Real.exp (-(M.rate * x)) else 0 :=
  ProbabilityTheory.cdf_expMeasure_eq M.rate_pos x

theorem measure_Ioi_toReal (M : Model) {x : ℝ} (hx : 0 ≤ x) :
    (M.measure (Set.Ioi x)).toReal =
      Real.exp (-(M.rate * x)) := by
  haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
    M.isProbabilityMeasure_measure
  have hcompl : Set.Ioi x = (Set.Iic x)ᶜ := by
    ext y
    simp
  calc
    (M.measure (Set.Ioi x)).toReal =
        M.measure.real (Set.Ioi x) := rfl
    _ = 1 - ProbabilityTheory.cdf M.measure x := by
      rw [hcompl, MeasureTheory.measureReal_compl measurableSet_Iic,
        MeasureTheory.probReal_univ, ProbabilityTheory.cdf_eq_real]
    _ = Real.exp (-(M.rate * x)) := by
      rw [M.cdf_eq x, if_pos hx]
      ring

/--
Scaling a rate-`r` exponential time by `r` gives the unit-rate exponential
tail.  This is the service-work normalization used when an exponential
potential-service time is converted into unit-mean service requirement.
-/
theorem measure_rate_mul_Ioi_toReal
    (M : Model) {z : ℝ} (hz : 0 ≤ z) :
    (M.measure {x : ℝ | z < M.rate * x}).toReal = Real.exp (-z) := by
  have hset : {x : ℝ | z < M.rate * x} = Set.Ioi (z / M.rate) := by
    ext x
    have hiff : z / M.rate < x ↔ z < M.rate * x := by
      rw [div_lt_iff₀ M.rate_pos]
      rw [mul_comm]
    exact hiff.symm
  rw [hset, M.measure_Ioi_toReal (div_nonneg hz M.rate_pos.le)]
  have harg : -(M.rate * (z / M.rate)) = -z := by
    field_simp [M.rate_pos.ne']
  rw [harg]

/--
Memoryless tail ratio for a positive-rate exponential model, stated directly
in terms of the model's tail probabilities.
-/
theorem measure_Ioi_add_div_measure_Ioi_toReal
    (M : Model) {elapsed future : ℝ}
    (h_elapsed : 0 ≤ elapsed) (h_future : 0 ≤ future) :
    (M.measure (Set.Ioi (elapsed + future))).toReal /
        (M.measure (Set.Ioi elapsed)).toReal =
      (M.measure (Set.Ioi future)).toReal := by
  rw [M.measure_Ioi_toReal (add_nonneg h_elapsed h_future)]
  rw [M.measure_Ioi_toReal h_elapsed]
  rw [M.measure_Ioi_toReal h_future]
  rw [show -(M.rate * (elapsed + future)) =
      -(M.rate * elapsed) + -(M.rate * future) by ring]
  rw [Real.exp_add]
  field_simp [Real.exp_ne_zero]

/-- The elementary exponential overshoot calculation before conditioning: the
mass of surviving `elapsed` and then an additional `future` factorizes into
the two tail masses. A deterministic-clock renewal proof needs this identity
under a measurable random elapsed prefix. -/
theorem measure_residual_tail_toReal
    (M : Model) {elapsed future : ℝ}
    (helapsed : 0 ≤ elapsed) (hfuture : 0 ≤ future) :
    (M.measure {x : ℝ | elapsed < x ∧ future < x - elapsed}).toReal =
      (M.measure (Set.Ioi elapsed)).toReal *
        (M.measure (Set.Ioi future)).toReal := by
  have hset : {x : ℝ | elapsed < x ∧ future < x - elapsed} =
      Set.Ioi (elapsed + future) := by
    ext x
    constructor
    · intro hx
      change elapsed < x ∧ future < x - elapsed at hx
      change elapsed + future < x
      linarith [hx.2]
    · intro hx
      change elapsed + future < x at hx
      constructor
      · change elapsed < x
        linarith [hx]
      · change future < x - elapsed
        linarith [hx]
  rw [hset, M.measure_Ioi_toReal (add_nonneg helapsed hfuture),
    M.measure_Ioi_toReal helapsed, M.measure_Ioi_toReal hfuture]
  rw [show -(M.rate * (elapsed + future)) =
    -(M.rate * elapsed) + -(M.rate * future) by ring, Real.exp_add]

theorem measure_Iic_toReal (M : Model) {x : ℝ} (hx : 0 ≤ x) :
    (M.measure (Set.Iic x)).toReal =
      1 - Real.exp (-(M.rate * x)) := by
  haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
    M.isProbabilityMeasure_measure
  have hcdf :
      (M.measure (Set.Iic x)).toReal = ProbabilityTheory.cdf M.measure x := by
    rw [ProbabilityTheory.cdf_eq_real M.measure x]
    rfl
  rw [hcdf, M.cdf_eq x, if_pos hx]

theorem measure_Iic_zero (M : Model) :
    M.measure (Set.Iic (0 : ℝ)) = 0 := by
  haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
    M.isProbabilityMeasure_measure
  have hcdf : ProbabilityTheory.cdf M.measure 0 = 0 := by
    rw [M.cdf_eq]
    norm_num
  have hreal : M.measure.real (Set.Iic (0 : ℝ)) = 0 := by
    simpa [ProbabilityTheory.cdf_eq_real M.measure 0] using hcdf
  exact (MeasureTheory.measureReal_eq_zero_iff (μ := M.measure)
    (s := Set.Iic (0 : ℝ))).mp hreal

theorem measure_Iio_zero (M : Model) :
    M.measure (Set.Iio (0 : ℝ)) = 0 :=
  MeasureTheory.measure_mono_null
    (by intro x hx; exact le_of_lt (Set.mem_Iio.mp hx))
    M.measure_Iic_zero

/-- Integration against a positive-rate exponential law is integration
against its real-valued exponential density.  The statement is deliberately
for an arbitrary real integrand: it is the measure-conversion step used before
separate boundedness or continuity arguments for a particular renewal
equation. -/
theorem integral_expMeasure_eq_integral_pdfReal_mul
    (M : Model) (g : ℝ → ℝ) :
    ∫ x, g x ∂ProbabilityTheory.expMeasure M.rate =
      ∫ x, ProbabilityTheory.exponentialPDFReal M.rate x * g x := by
  change ∫ x, g x ∂(MeasureTheory.volume.withDensity
      (fun x => ENNReal.ofReal (ProbabilityTheory.exponentialPDFReal M.rate x))) = _
  calc
    _ = ∫ x, (ENNReal.ofReal (ProbabilityTheory.exponentialPDFReal M.rate x)).toReal • g x := by
      exact integral_withDensity_eq_integral_toReal_smul
        (f := fun x => ENNReal.ofReal (ProbabilityTheory.exponentialPDFReal M.rate x))
        (ENNReal.measurable_ofReal.comp
          (ProbabilityTheory.measurable_exponentialPDFReal M.rate))
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change (ENNReal.ofReal (ProbabilityTheory.exponentialPDFReal M.rate x)).toReal * g x = _
      rw [ENNReal.toReal_ofReal
        (ProbabilityTheory.exponentialPDFReal_nonneg M.rate_pos x)]

theorem ae_nonnegative (M : Model) :
    (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[M.measure] (fun x : ℝ => x) := by
  rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
  simpa [Set.compl_setOf] using M.measure_Iio_zero

/-- Real-valued PDF of the positive-rate exponential model. -/
noncomputable def pdfReal (M : Model) (x : ℝ) : ℝ :=
  ProbabilityTheory.exponentialPDFReal M.rate x

theorem pdfReal_nonneg (M : Model) (x : ℝ) :
    0 ≤ M.pdfReal x :=
  ProbabilityTheory.exponentialPDFReal_nonneg M.rate_pos x

theorem pdfReal_pos (M : Model) {x : ℝ} (hx : 0 < x) :
    0 < M.pdfReal x :=
  ProbabilityTheory.exponentialPDFReal_pos M.rate_pos hx

end Model

/-- Real harmonic numbers, indexed so `harmonicReal q = ∑_{j=1}^q 1 / j`. -/
noncomputable def harmonicReal (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range q, (1 : ℝ) / ((j + 1 : ℕ) : ℝ)

theorem harmonicReal_zero : harmonicReal 0 = 0 := by
  simp [harmonicReal]

theorem harmonicReal_succ (q : ℕ) :
    harmonicReal (q + 1) = harmonicReal q + (1 : ℝ) / ((q + 1 : ℕ) : ℝ) := by
  simp [harmonicReal, Finset.sum_range_succ]

theorem harmonicReal_eq_harmonic (q : ℕ) :
    harmonicReal q = (harmonic q : ℝ) := by
  simp [harmonicReal, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/--
Closed-form value for the expected maximum of `q` i.i.d. rate-`rate`
exponential draws.

This file records the standard closed form and its consequences. A future
order-statistic integration theorem can connect this value function directly to
`Model.measure`.
-/
noncomputable def expectedMaxValueOfRate (rate : ℝ) (q : ℕ) : ℝ :=
  (1 / rate) * harmonicReal q

theorem expectedMaxValueOfRate_forward_marginal
    (rate : ℝ) (q : ℕ) :
    expectedMaxValueOfRate rate (q + 1) -
        expectedMaxValueOfRate rate q =
      (1 / rate) * ((1 : ℝ) / ((q + 1 : ℕ) : ℝ)) := by
  rw [expectedMaxValueOfRate, expectedMaxValueOfRate, harmonicReal_succ]
  ring

theorem expectedMaxValueOfRate_backward_marginal
    (rate : ℝ) {q : ℕ} (hq : 0 < q) :
    expectedMaxValueOfRate rate q -
        expectedMaxValueOfRate rate (q - 1) =
      (1 / rate) * ((1 : ℝ) / (q : ℝ)) := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  nth_rewrite 1 [← hpred]
  rw [expectedMaxValueOfRate_forward_marginal]
  simp [hpred]

/--
The harmonic closed form differs from `(1/rate) * log q` by a convergent
Euler-Mascheroni constant term.
-/
theorem expectedMaxValueOfRate_sub_log_tendsto
    (rate : ℝ) :
    Filter.Tendsto
      (fun q : ℕ =>
        expectedMaxValueOfRate rate q -
          (1 / rate) * Real.log q)
      Filter.atTop
      (nhds ((1 / rate) * Real.eulerMascheroniConstant)) := by
  have h :=
    (Real.tendsto_harmonic_sub_log.const_mul (1 / rate))
  refine h.congr' ?_
  filter_upwards with q
  rw [expectedMaxValueOfRate, harmonicReal_eq_harmonic]
  ring

/-- Closed-form expected maximum value for a positive-rate model. -/
noncomputable def Model.expectedMaxValue (M : Model) (q : ℕ) : ℝ :=
  expectedMaxValueOfRate M.rate q

theorem Model.expectedMaxValue_forward_marginal
    (M : Model) (q : ℕ) :
    M.expectedMaxValue (q + 1) - M.expectedMaxValue q =
      (1 / M.rate) * ((1 : ℝ) / ((q + 1 : ℕ) : ℝ)) :=
  expectedMaxValueOfRate_forward_marginal M.rate q

theorem Model.expectedMaxValue_backward_marginal
    (M : Model) {q : ℕ} (hq : 0 < q) :
    M.expectedMaxValue q - M.expectedMaxValue (q - 1) =
      (1 / M.rate) * ((1 : ℝ) / (q : ℝ)) :=
  expectedMaxValueOfRate_backward_marginal M.rate hq

theorem Model.expectedMaxValue_sub_log_tendsto (M : Model) :
    Filter.Tendsto
      (fun q : ℕ =>
        M.expectedMaxValue q - (1 / M.rate) * Real.log q)
      Filter.atTop
      (nhds ((1 / M.rate) * Real.eulerMascheroniConstant)) :=
  expectedMaxValueOfRate_sub_log_tendsto M.rate

/-! ## Maximum survival algebra and the survival-integral base case -/

/--
Analytic survival function for the maximum of `q` independent exponential
draws, after substituting the exponential CDF on the nonnegative line:

`1 - (1 - exp (-rate*x))^q`.

The product-measure theorem connecting this expression to an actual iid maximum
is deliberately kept as a later order-statistic layer.
-/
noncomputable def maxSurvivalOfRate (rate : ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  1 - (1 - Real.exp (-(rate * x))) ^ q

/-- Finite maximum of a nonempty sample indexed by `Fin q`. -/
noncomputable def finiteSampleMax {q : ℕ} [NeZero q]
    (sample : Fin q → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin q)).sup' Finset.univ_nonempty sample

/-- Finite minimum of a nonempty sample indexed by `Fin q`. -/
noncomputable def finiteSampleMin {q : ℕ} [NeZero q]
    (sample : Fin q → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin q)).inf' Finset.univ_nonempty sample

theorem finiteSampleMax_le_iff {q : ℕ} [NeZero q]
    (sample : Fin q → ℝ) (x : ℝ) :
    finiteSampleMax sample ≤ x ↔ ∀ i, sample i ≤ x := by
  simp [finiteSampleMax, Finset.sup'_le_iff]

theorem finiteSampleMin_le_iff {q : ℕ} [NeZero q]
    (sample : Fin q → ℝ) (x : ℝ) :
    x ≤ finiteSampleMin sample ↔ ∀ i, x ≤ sample i := by
  simp [finiteSampleMin, Finset.le_inf'_iff]

theorem sample_le_finiteSampleMax {q : ℕ} [NeZero q]
    (sample : Fin q → ℝ) (i : Fin q) :
    sample i ≤ finiteSampleMax sample := by
  unfold finiteSampleMax
  exact Finset.le_sup' sample (Finset.mem_univ i)

theorem finiteSampleMin_le_sample {q : ℕ} [NeZero q]
    (sample : Fin q → ℝ) (i : Fin q) :
    finiteSampleMin sample ≤ sample i := by
  unfold finiteSampleMin
  exact Finset.inf'_le sample (Finset.mem_univ i)

theorem finiteSampleMin_nonnegative_of_forall {q : ℕ} [NeZero q]
    {sample : Fin q → ℝ} (h_nonneg : ∀ i, 0 ≤ sample i) :
    0 ≤ finiteSampleMin sample :=
  (finiteSampleMin_le_iff sample 0).2 h_nonneg

theorem finiteSampleMax_le_set_eq_pi_Iic {q : ℕ} [NeZero q] (x : ℝ) :
    {sample : Fin q → ℝ | finiteSampleMax sample ≤ x} =
      Set.pi Set.univ (fun _ : Fin q => Set.Iic x) := by
  ext sample
  constructor
  · intro h i _hi
    exact (finiteSampleMax_le_iff sample x).1 h i
  · intro h
    exact (finiteSampleMax_le_iff sample x).2 (fun i => h i trivial)

/-- The finite sample maximum is measurable as a function of the product sample. -/
theorem finiteSampleMax_measurable {q : ℕ} [NeZero q] :
    Measurable (finiteSampleMax (q := q)) := by
  classical
  unfold finiteSampleMax
  let hmeas :=
    Finset.measurable_sup' (s := (Finset.univ : Finset (Fin q)))
      Finset.univ_nonempty
      (fun i _ => measurable_pi_apply (X := fun _ : Fin q => ℝ) i)
  convert hmeas using 1
  ext sample
  rw [Finset.sup'_apply]

theorem finiteSampleMin_measurable {q : ℕ} [NeZero q] :
    Measurable (finiteSampleMin (q := q)) := by
  classical
  unfold finiteSampleMin
  let hmeas :=
    Finset.inf'_induction
      (s := (Finset.univ : Finset (Fin q)))
      Finset.univ_nonempty
      (fun i : Fin q => fun sample : Fin q → ℝ => sample i)
      (p := fun g : (Fin q → ℝ) → ℝ => Measurable g)
      (fun _f hf _g hg => hf.inf hg)
      (fun i _hi => measurable_pi_apply (X := fun _ : Fin q => ℝ) i)
  convert hmeas using 1
  ext sample
  rw [Finset.inf'_apply]

theorem finiteSampleMax_le_measurableSet {q : ℕ} [NeZero q] (x : ℝ) :
    MeasurableSet {sample : Fin q → ℝ | finiteSampleMax sample ≤ x} :=
  measurableSet_le finiteSampleMax_measurable measurable_const

theorem finiteSampleMin_gt_iff {q : ℕ} [NeZero q]
    (sample : Fin q → ℝ) (x : ℝ) :
    x < finiteSampleMin sample ↔ ∀ i, x < sample i := by
  simp [finiteSampleMin, Finset.lt_inf'_iff]

theorem finiteSampleMin_gt_set_eq_pi_Ioi {q : ℕ} [NeZero q] (x : ℝ) :
    {sample : Fin q → ℝ | x < finiteSampleMin sample} =
      Set.pi Set.univ (fun _ : Fin q => Set.Ioi x) := by
  ext sample
  constructor
  · intro h i _hi
    exact (finiteSampleMin_gt_iff sample x).1 h i
  · intro h
    exact (finiteSampleMin_gt_iff sample x).2 (fun i => h i trivial)

theorem finiteSampleMin_gt_measurableSet {q : ℕ} [NeZero q] (x : ℝ) :
    MeasurableSet {sample : Fin q → ℝ | x < finiteSampleMin sample} :=
  measurableSet_lt measurable_const finiteSampleMin_measurable

/-- I.i.d. product measure for `q` draws from an exponential model. -/
noncomputable def Model.iidProductMeasure
    (M : Model) (q : ℕ) : MeasureTheory.Measure (Fin q → ℝ) :=
  MeasureTheory.Measure.pi (fun _ : Fin q => M.measure)

theorem Model.isProbabilityMeasure_iidProductMeasure
    (M : Model) (q : ℕ) :
    MeasureTheory.IsProbabilityMeasure (M.iidProductMeasure q) := by
  haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
    M.isProbabilityMeasure_measure
  unfold Model.iidProductMeasure
  infer_instance

theorem Model.iidProductMeasure_finiteSampleMax_le
    (M : Model) {q : ℕ} [NeZero q] (x : ℝ) :
    (M.iidProductMeasure q) {sample : Fin q → ℝ | finiteSampleMax sample ≤ x} =
      (M.measure (Set.Iic x)) ^ q := by
  haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
    M.isProbabilityMeasure_measure
  rw [Model.iidProductMeasure, finiteSampleMax_le_set_eq_pi_Iic]
  rw [MeasureTheory.Measure.pi_pi]
  simp

theorem Model.iidProductMeasure_finiteSampleMax_le_toReal
    (M : Model) {q : ℕ} [NeZero q] (x : ℝ) :
    ((M.iidProductMeasure q)
        {sample : Fin q → ℝ | finiteSampleMax sample ≤ x}).toReal =
      (ProbabilityTheory.cdf M.measure x) ^ q := by
  haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
    M.isProbabilityMeasure_measure
  rw [Model.iidProductMeasure_finiteSampleMax_le, ENNReal.toReal_pow]
  have hcdf :
      (M.measure (Set.Iic x)).toReal = ProbabilityTheory.cdf M.measure x := by
    rw [ProbabilityTheory.cdf_eq_real M.measure x]
    rfl
  rw [hcdf]

/--
Product-measure derivation of the analytic maximum-survival expression on the
nonnegative line.
-/
theorem Model.iidMaxSurvival_eq_maxSurvivalOfRate
    (M : Model) {q : ℕ} [NeZero q] {x : ℝ} (hx : 0 ≤ x) :
    1 - ((M.iidProductMeasure q)
        {sample : Fin q → ℝ | finiteSampleMax sample ≤ x}).toReal =
      maxSurvivalOfRate M.rate q x := by
  rw [Model.iidProductMeasure_finiteSampleMax_le_toReal]
  rw [M.cdf_eq x, if_pos hx]
  rfl

theorem Model.iidProductMeasure_all_nonnegative_ae
    (M : Model) (q : ℕ) :
    (fun _ : Fin q → ℝ => fun _ : Fin q => (0 : ℝ)) ≤ᵐ[
        M.iidProductMeasure q] fun sample => sample := by
  haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
    M.isProbabilityMeasure_measure
  have hcoord :
      ∀ i : Fin q, (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[M.measure] (fun x : ℝ => x) :=
    fun _ => M.ae_nonnegative
  have hpi :
      (fun sample : Fin q → ℝ => fun _ : Fin q => (0 : ℝ)) ≤ᵐ[
        MeasureTheory.Measure.pi (fun _ : Fin q => M.measure)] fun sample => sample :=
    MeasureTheory.Measure.ae_le_pi (μ := fun _ : Fin q => M.measure) hcoord
  simpa [Model.iidProductMeasure] using hpi

/-- The finite iid maximum is a.e. nonnegative under the exponential product measure. -/
theorem Model.iidProductMeasure_finiteSampleMax_nonnegative_ae
    (M : Model) {q : ℕ} [NeZero q] :
    0 ≤ᵐ[M.iidProductMeasure q] (finiteSampleMax (q := q)) := by
  filter_upwards [M.iidProductMeasure_all_nonnegative_ae q] with sample hsample
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let i0 : Fin q := ⟨0, hqpos⟩
  rw [finiteSampleMax]
  exact (Finset.le_sup'_iff
    (s := (Finset.univ : Finset (Fin q)))
    (H := Finset.univ_nonempty) (f := sample) (a := (0 : ℝ))).2
    ⟨i0, by simp, hsample i0⟩

theorem Model.iidProductMeasure_finiteSampleMin_nonnegative_ae
    (M : Model) {q : ℕ} [NeZero q] :
    0 ≤ᵐ[M.iidProductMeasure q] (finiteSampleMin (q := q)) := by
  filter_upwards [M.iidProductMeasure_all_nonnegative_ae q] with sample hsample
  exact finiteSampleMin_nonnegative_of_forall (fun i => hsample i)

/--
Tail-probability form of the product-measure maximum survival expression.

This is the right-hand side used by the layer-cake formula for the expected
finite maximum.
-/
theorem Model.iidProductMeasure_finiteSampleMax_gt_real
    (M : Model) {q : ℕ} [NeZero q] {x : ℝ} (hx : 0 ≤ x) :
    (M.iidProductMeasure q).real
        {sample : Fin q → ℝ | x < finiteSampleMax sample} =
      maxSurvivalOfRate M.rate q x := by
  haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
    M.isProbabilityMeasure_measure
  haveI : MeasureTheory.IsProbabilityMeasure (M.iidProductMeasure q) :=
    M.isProbabilityMeasure_iidProductMeasure q
  have hcompl :
      {sample : Fin q → ℝ | x < finiteSampleMax sample} =
        {sample : Fin q → ℝ | finiteSampleMax sample ≤ x}ᶜ := by
    ext sample
    simp [not_le]
  rw [hcompl, MeasureTheory.measureReal_compl (finiteSampleMax_le_measurableSet x),
    MeasureTheory.probReal_univ]
  simpa [MeasureTheory.Measure.real] using
    M.iidMaxSurvival_eq_maxSurvivalOfRate (q := q) hx

theorem Model.iidProductMeasure_finiteSampleMin_gt_real
    (M : Model) {q : ℕ} [NeZero q] {x : ℝ} (hx : 0 ≤ x) :
    (M.iidProductMeasure q).real
        {sample : Fin q → ℝ | x < finiteSampleMin sample} =
      Real.exp (-(((q : ℝ) * M.rate) * x)) := by
  haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
    M.isProbabilityMeasure_measure
  have htail :
      (M.iidProductMeasure q)
          {sample : Fin q → ℝ | x < finiteSampleMin sample} =
        ∏ _i : Fin q, M.measure (Set.Ioi x) := by
    rw [Model.iidProductMeasure, finiteSampleMin_gt_set_eq_pi_Ioi,
      MeasureTheory.Measure.pi_pi]
  rw [MeasureTheory.Measure.real, htail, ENNReal.toReal_prod]
  calc
    ∏ _i : Fin q, (M.measure (Set.Ioi x)).toReal =
        ∏ _i : Fin q, Real.exp (-(M.rate * x)) := by
      simp [M.measure_Ioi_toReal hx]
    _ = (Real.exp (-(M.rate * x))) ^ q := by
      simp
    _ = Real.exp (-(((q : ℝ) * M.rate) * x)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/--
Binomial expansion of `maxSurvivalOfRate`.

The indexing follows mathlib's `sub_pow` orientation: the summation variable
`m = 0, ..., q-1` corresponds to exponential power `q - m`, so every term is an
integrable exponential tail when `q > 0`.
-/
theorem maxSurvivalOfRate_expansion
    (rate : ℝ) (q : ℕ) (x : ℝ) :
    maxSurvivalOfRate rate q x =
      - ∑ m ∈ Finset.range q,
          (-1 : ℝ) ^ (m + q) *
            (Real.exp (-(rate * x))) ^ (q - m) *
            (q.choose m : ℝ) := by
  unfold maxSurvivalOfRate
  have h :=
    sub_pow (1 : ℝ) (Real.exp (-(rate * x))) q
  rw [h, Finset.sum_range_succ]
  have hterm :
      (-1 : ℝ) ^ (q + q) * 1 ^ q *
          (Real.exp (-(rate * x))) ^ (q - q) *
          (q.choose q : ℝ) = 1 := by
    simp [Even.neg_one_pow (Even.add_self q)]
  rw [hterm]
  simp [mul_comm]

theorem maxSurvivalOfRate_one
    (rate x : ℝ) :
    maxSurvivalOfRate rate 1 x = Real.exp (-(rate * x)) := by
  simp [maxSurvivalOfRate]

theorem exp_neg_mul_pow_nat
    (rate x : ℝ) (n : ℕ) :
    (Real.exp (-(rate * x))) ^ n =
      Real.exp (-(((n : ℝ) * rate) * x)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

/--
Basic exponential-tail integral:

`∫_0^∞ exp (-rate * x) dx = 1 / rate`.

This is the analytic base case for deriving exponential expected-max formulas
from the distribution model rather than merely naming the harmonic closed form.
-/
theorem integral_exp_neg_mul_Ioi
    (rate : ℝ) (hrate : 0 < rate) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(rate * x)) = 1 / rate := by
  have h :=
    integral_exp_neg_mul_rpow (p := 1) (b := rate) (by norm_num) hrate
  norm_num [Real.rpow_one, Real.rpow_neg_one, Real.Gamma_nat_eq_factorial,
    div_eq_mul_inv, neg_mul, one_div] at h ⊢
  exact h

/--
Integrability of a positive natural power of an exponential survival term on
`(0,∞)`.
-/
theorem integrableOn_exp_neg_mul_pow_Ioi
    (rate : ℝ) (hrate : 0 < rate) {n : ℕ} (hn : 0 < n) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => (Real.exp (-(rate * x))) ^ n)
      (Set.Ioi (0 : ℝ)) := by
  have hnrate_pos : 0 < (n : ℝ) * rate :=
    mul_pos (by exact_mod_cast hn) hrate
  exact
    (exp_neg_integrableOn_Ioi (0 : ℝ) hnrate_pos).congr_fun
      (fun x _hx => by
        rw [show -((n : ℝ) * rate) * x =
            -(((n : ℝ) * rate) * x) by ring]
        exact (exp_neg_mul_pow_nat rate x n).symm)
      measurableSet_Ioi

/--
Integral of a positive natural power of an exponential survival term.

This is the termwise integral needed after expanding the maximum survival
function by the binomial theorem.
-/
theorem integral_exp_neg_mul_pow_Ioi
    (rate : ℝ) (hrate : 0 < rate) {n : ℕ} (hn : 0 < n) :
    ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-(rate * x))) ^ n =
      1 / ((n : ℝ) * rate) := by
  have hnrate_pos : 0 < (n : ℝ) * rate :=
    mul_pos (by exact_mod_cast hn) hrate
  calc
    ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-(rate * x))) ^ n
        = ∫ x in Set.Ioi (0 : ℝ),
            Real.exp (-(((n : ℝ) * rate) * x)) := by
          refine MeasureTheory.setIntegral_congr_fun
            measurableSet_Ioi ?_
          intro x _hx
          exact exp_neg_mul_pow_nat rate x n
    _ = 1 / ((n : ℝ) * rate) :=
          integral_exp_neg_mul_Ioi ((n : ℝ) * rate) hnrate_pos

/--
Integrability of the analytic maximum-survival expression on `(0,∞)`.
-/
theorem integrableOn_maxSurvivalOfRate_Ioi
    (rate : ℝ) (hrate : 0 < rate) (q : ℕ) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => maxSurvivalOfRate rate q x)
      (Set.Ioi (0 : ℝ)) := by
  have hsum : MeasureTheory.Integrable
      (fun x : ℝ =>
        ∑ m ∈ Finset.range q,
          (-1 : ℝ) ^ (m + q) *
            (Real.exp (-(rate * x))) ^ (q - m) *
            (q.choose m : ℝ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine MeasureTheory.integrable_finset_sum (Finset.range q) ?_
    intro m hm
    have hn : 0 < q - m :=
      Nat.sub_pos_of_lt (Finset.mem_range.mp hm)
    have hbase := integrableOn_exp_neg_mul_pow_Ioi rate hrate hn
    have hconst : MeasureTheory.Integrable
        (fun x : ℝ =>
          (((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
            (Real.exp (-(rate * x))) ^ (q - m)))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      hbase.const_mul _
    refine hconst.congr ?_
    filter_upwards with x
    ring
  refine hsum.neg.congr ?_
  filter_upwards with x
  rw [maxSurvivalOfRate_expansion]
  rfl

/--
Integral of the analytic maximum-survival expression, after the binomial
expansion and termwise exponential-tail integration.

The remaining combinatorial step toward `H_q / rate` is to identify this
finite alternating binomial sum with the harmonic number.
-/
theorem maxSurvivalOfRate_integral_eq_finite_sum
    (rate : ℝ) (hrate : 0 < rate) (q : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), maxSurvivalOfRate rate q x =
      - ∑ m ∈ Finset.range q,
          ((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
            (1 / (((q - m : ℕ) : ℝ) * rate)) := by
  have hcongr :
      ∫ x in Set.Ioi (0 : ℝ), maxSurvivalOfRate rate q x =
        ∫ x in Set.Ioi (0 : ℝ),
          - ∑ m ∈ Finset.range q,
            (-1 : ℝ) ^ (m + q) *
              (Real.exp (-(rate * x))) ^ (q - m) *
              (q.choose m : ℝ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _hx
    rw [maxSurvivalOfRate_expansion]
  rw [hcongr]
  rw [MeasureTheory.integral_neg]
  rw [MeasureTheory.integral_finset_sum]
  · congr 1
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hn : 0 < q - m :=
      Nat.sub_pos_of_lt (Finset.mem_range.mp hm)
    have hterm :
        ∫ x in Set.Ioi (0 : ℝ),
            (-1 : ℝ) ^ (m + q) *
              (Real.exp (-(rate * x))) ^ (q - m) *
              (q.choose m : ℝ) =
          ∫ x in Set.Ioi (0 : ℝ),
            (((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
              (Real.exp (-(rate * x))) ^ (q - m)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro x _hx
      ring
    rw [hterm]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_exp_neg_mul_pow_Ioi rate hrate hn]
  · intro m hm
    have hn : 0 < q - m :=
      Nat.sub_pos_of_lt (Finset.mem_range.mp hm)
    have hbase := integrableOn_exp_neg_mul_pow_Ioi rate hrate hn
    have hconst : MeasureTheory.Integrable
        (fun x : ℝ =>
          (((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
            (Real.exp (-(rate * x))) ^ (q - m)))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      hbase.const_mul _
    refine hconst.congr ?_
    filter_upwards with x
    ring

/--
Auxiliary alternating-binomial identity:

`∑_{j=0}^n (-1)^j * choose n j / (j+1) = 1/(n+1)`.
-/
theorem alternating_choose_div_succ_eq_inv_succ (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ j * (n.choose j : ℝ)) /
          (((j + 1 : ℕ) : ℝ))) =
      1 / (((n + 1 : ℕ) : ℝ)) := by
  have hchoose_sum :
      (∑ j ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ j * ((n + 1).choose (j + 1) : ℝ)) = 1 := by
    have halt :
        (∑ r ∈ Finset.range (n + 2),
            (-1 : ℝ) ^ r * ((n + 1).choose r : ℝ)) = 0 := by
      have h_int := Int.alternating_sum_range_choose_of_ne
        (n := n + 1) (by omega)
      exact_mod_cast h_int
    have hsplit :
        (∑ r ∈ Finset.range (n + 2),
            (-1 : ℝ) ^ r * ((n + 1).choose r : ℝ)) =
          (∑ j ∈ Finset.range (n + 1),
              (-1 : ℝ) ^ (j + 1) *
                ((n + 1).choose (j + 1) : ℝ)) + 1 := by
      rw [Finset.sum_range_succ'
        (fun r => (-1 : ℝ) ^ r * ((n + 1).choose r : ℝ)) (n + 1)]
      simp [add_comm]
    have hneg :
        (∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (j + 1) *
              ((n + 1).choose (j + 1) : ℝ)) = -1 := by
      linarith
    have hterm :
        (∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (j + 1) *
              ((n + 1).choose (j + 1) : ℝ)) =
          - (∑ j ∈ Finset.range (n + 1),
              (-1 : ℝ) ^ j *
                ((n + 1).choose (j + 1) : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [pow_succ]
      ring
    linarith
  have hscaled :
      (((n + 1 : ℕ) : ℝ) *
        (∑ j ∈ Finset.range (n + 1),
          ((-1 : ℝ) ^ j * (n.choose j : ℝ)) /
            (((j + 1 : ℕ) : ℝ)))) = 1 := by
    rw [Finset.mul_sum]
    calc
      ∑ x ∈ Finset.range (n + 1),
          ((n + 1 : ℕ) : ℝ) *
            (((-1 : ℝ) ^ x * (n.choose x : ℝ)) /
              (((x + 1 : ℕ) : ℝ)))
          = ∑ x ∈ Finset.range (n + 1),
              (-1 : ℝ) ^ x * ((n + 1).choose (x + 1) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            have hnat := Nat.add_one_mul_choose_eq n x
            have hcast :
                ((n + 1 : ℕ) : ℝ) * (n.choose x : ℝ) =
                  ((n + 1).choose (x + 1) : ℝ) *
                    (((x + 1 : ℕ) : ℝ)) := by
              exact_mod_cast hnat
            have hxne : (((x + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
            field_simp [hxne]
            nlinarith
      _ = 1 := hchoose_sum
  have hden : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hden]
  simpa [mul_comm] using hscaled

/--
Classical alternating-binomial harmonic identity:

`∑_{j=0}^{q-1} (-1)^j * choose q (j+1)/(j+1) = H_q`.
-/
theorem alternating_choose_succ_div_eq_harmonicReal (q : ℕ) :
    (∑ j ∈ Finset.range q,
        ((-1 : ℝ) ^ j * (q.choose (j + 1) : ℝ)) /
          (((j + 1 : ℕ) : ℝ))) = harmonicReal q := by
  induction q with
  | zero =>
      simp [harmonicReal]
  | succ n ih =>
      have hsplit :
          (∑ j ∈ Finset.range (n + 1),
              ((-1 : ℝ) ^ j * ((n + 1).choose (j + 1) : ℝ)) /
                (((j + 1 : ℕ) : ℝ))) =
            (∑ j ∈ Finset.range (n + 1),
              ((-1 : ℝ) ^ j * (n.choose j : ℝ)) /
                (((j + 1 : ℕ) : ℝ))) +
            (∑ j ∈ Finset.range (n + 1),
              ((-1 : ℝ) ^ j * (n.choose (j + 1) : ℝ)) /
                (((j + 1 : ℕ) : ℝ))) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        rw [Nat.choose_succ_succ]
        norm_num
        ring
      have htail :
          (∑ j ∈ Finset.range (n + 1),
              ((-1 : ℝ) ^ j * (n.choose (j + 1) : ℝ)) /
                (((j + 1 : ℕ) : ℝ))) =
            (∑ j ∈ Finset.range n,
              ((-1 : ℝ) ^ j * (n.choose (j + 1) : ℝ)) /
                (((j + 1 : ℕ) : ℝ))) := by
        rw [Finset.sum_range_succ]
        simp
      rw [hsplit, htail, ih, alternating_choose_div_succ_eq_inv_succ n,
        harmonicReal_succ]
      ring

/--
The finite alternating sum obtained by integrating the binomial expansion of
the maximum survival function equals the harmonic closed form `H_q/rate`.
-/
theorem maxSurvivalOfRate_finite_sum_eq_expectedMaxValueOfRate
    (rate : ℝ) (hrate : 0 < rate) (q : ℕ) :
    - ∑ m ∈ Finset.range q,
        ((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
          (1 / (((q - m : ℕ) : ℝ) * rate)) =
      expectedMaxValueOfRate rate q := by
  have hrate_ne : rate ≠ 0 := ne_of_gt hrate
  calc
    - ∑ m ∈ Finset.range q,
        ((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
          (1 / (((q - m : ℕ) : ℝ) * rate))
        = ∑ j ∈ Finset.range q,
            (((-1 : ℝ) ^ j * (q.choose (j + 1) : ℝ)) /
              (((j + 1 : ℕ) : ℝ))) * (1 / rate) := by
          rw [← Finset.sum_range_reflect
            (fun m => ((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
              (1 / (((q - m : ℕ) : ℝ) * rate))) q]
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hjlt : j < q := Finset.mem_range.mp hj
          have hsub : q - (q - 1 - j) = j + 1 := by omega
          have hchoose : q.choose (q - 1 - j) = q.choose (j + 1) := by
            have hle : j + 1 ≤ q := Nat.succ_le_of_lt hjlt
            convert Nat.choose_symm (n := q) (k := j + 1) hle using 2
            omega
          have hpow :
              (-1 : ℝ) ^ (q - 1 - j + q) = (-1 : ℝ) ^ (j + 1) := by
            have hparity :
                q - 1 - j + q = (j + 1) + 2 * (q - 1 - j) := by
              omega
            rw [hparity, pow_add, pow_mul]
            norm_num
          have hjne : (((j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
          rw [hsub, hchoose, hpow]
          field_simp [hrate_ne, hjne]
          ring
    _ = (∑ j ∈ Finset.range q,
          ((-1 : ℝ) ^ j * (q.choose (j + 1) : ℝ)) /
            (((j + 1 : ℕ) : ℝ))) * (1 / rate) := by
          rw [Finset.sum_mul]
    _ = harmonicReal q * (1 / rate) := by
          rw [alternating_choose_succ_div_eq_harmonicReal q]
    _ = expectedMaxValueOfRate rate q := by
          rw [expectedMaxValueOfRate]
          ring

/--
Integral of the analytic maximum-survival expression equals the harmonic
expected-maximum value.
-/
theorem maxSurvivalOfRate_integral_eq_expectedMaxValueOfRate
    (rate : ℝ) (hrate : 0 < rate) (q : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), maxSurvivalOfRate rate q x =
      expectedMaxValueOfRate rate q := by
  rw [maxSurvivalOfRate_integral_eq_finite_sum rate hrate q,
    maxSurvivalOfRate_finite_sum_eq_expectedMaxValueOfRate rate hrate q]

/--
Layer-cake tail-integral side for the finite iid maximum:
integrating the real tail probability of the sample maximum over `x > 0`
gives the harmonic expected-maximum closed form.

This theorem stops just before the separate Bochner-expectation step
`∫ sample, finiteSampleMax sample`, but its integrand is exactly the one used
by mathlib's layer-cake API.
-/
theorem Model.iidProductMeasure_finiteSampleMax_tailIntegral_eq_expectedMaxValue
    (M : Model) {q : ℕ} [NeZero q] :
    ∫ x in Set.Ioi (0 : ℝ),
        (M.iidProductMeasure q).real
          {sample : Fin q → ℝ | x < finiteSampleMax sample} =
      M.expectedMaxValue q := by
  calc
    ∫ x in Set.Ioi (0 : ℝ),
        (M.iidProductMeasure q).real
          {sample : Fin q → ℝ | x < finiteSampleMax sample}
        = ∫ x in Set.Ioi (0 : ℝ), maxSurvivalOfRate M.rate q x := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          exact M.iidProductMeasure_finiteSampleMax_gt_real
            (q := q) (le_of_lt hx)
    _ = M.expectedMaxValue q := by
          simpa [Model.expectedMaxValue] using
            maxSurvivalOfRate_integral_eq_expectedMaxValueOfRate
              M.rate M.rate_pos q

/--
Layer-cake tail-integral side for the finite iid minimum: integrating the
probability that every draw exceeds `x` gives the expected minimum closed form
`1 / (q * rate)`.
-/
theorem Model.iidProductMeasure_finiteSampleMin_tailIntegral_eq_expectedMinValue
    (M : Model) {q : ℕ} [NeZero q] :
    ∫ x in Set.Ioi (0 : ℝ),
        (M.iidProductMeasure q).real
          {sample : Fin q → ℝ | x < finiteSampleMin sample} =
      1 / ((q : ℝ) * M.rate) := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqrate_pos : 0 < (q : ℝ) * M.rate :=
    mul_pos (by exact_mod_cast hqpos) M.rate_pos
  calc
    ∫ x in Set.Ioi (0 : ℝ),
        (M.iidProductMeasure q).real
          {sample : Fin q → ℝ | x < finiteSampleMin sample}
        = ∫ x in Set.Ioi (0 : ℝ),
            Real.exp (-(((q : ℝ) * M.rate) * x)) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          exact M.iidProductMeasure_finiteSampleMin_gt_real
            (q := q) (le_of_lt hx)
    _ = 1 / ((q : ℝ) * M.rate) :=
          integral_exp_neg_mul_Ioi ((q : ℝ) * M.rate) hqrate_pos

/-- The finite iid maximum is integrable under the exponential product measure. -/
theorem Model.iidProductMeasure_finiteSampleMax_integrable
    (M : Model) {q : ℕ} [NeZero q] :
    MeasureTheory.Integrable
      (finiteSampleMax (q := q)) (M.iidProductMeasure q) := by
  let μ := M.iidProductMeasure q
  haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
    M.isProbabilityMeasure_measure
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    M.isProbabilityMeasure_iidProductMeasure q
  have h_nonneg :
      (fun _ : Fin q → ℝ => (0 : ℝ)) ≤ᵐ[μ] (finiteSampleMax (q := q)) := by
    simpa [μ] using
      M.iidProductMeasure_finiteSampleMax_nonnegative_ae (q := q)
  have h_layer :=
    MeasureTheory.lintegral_eq_lintegral_meas_lt (μ := μ)
      h_nonneg finiteSampleMax_measurable.aemeasurable
  have h_tail_int : MeasureTheory.Integrable
      (fun x : ℝ =>
        μ.real {sample : Fin q → ℝ | x < finiteSampleMax sample})
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hmax :=
      integrableOn_maxSurvivalOfRate_Ioi M.rate M.rate_pos q
    refine hmax.congr_fun ?_ measurableSet_Ioi
    intro x hx
    exact (M.iidProductMeasure_finiteSampleMax_gt_real
      (q := q) (le_of_lt hx)).symm
  let tailSet : ℝ → Set (Fin q → ℝ) :=
    fun x => {sample : Fin q → ℝ | x < finiteSampleMax sample}
  have h_tail_lintegral :
      (∫⁻ x, (μ (tailSet x))
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) < ∞ := by
    calc
      ∫⁻ x, (μ (tailSet x))
          ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        = ∫⁻ x, ENNReal.ofReal (μ.real (tailSet x))
            ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
            refine MeasureTheory.lintegral_congr_ae ?_
            filter_upwards with x
            rw [MeasureTheory.ofReal_measureReal]
      _ < ∞ := MeasureTheory.Integrable.lintegral_lt_top h_tail_int
  have h_lintegral :
      (∫⁻ sample, ENNReal.ofReal (finiteSampleMax sample) ∂μ) < ∞ := by
    simpa [μ, tailSet] using h_layer.trans_lt h_tail_lintegral
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    finiteSampleMax_measurable.aestronglyMeasurable h_nonneg).1 h_lintegral.ne

/--
Conditional layer-cake bridge from the product-measure tail integral to the
literal Bochner expectation of the finite maximum.

Kept as a reusable bridge for callers that already have an integrability proof;
`Model.iidProductMeasure_finiteSampleMax_integrable` discharges the hypothesis
for exponential product measures.
-/
theorem Model.iidProductMeasure_finiteSampleMax_integral_eq_expectedMaxValue_of_integrable
    (M : Model) {q : ℕ} [NeZero q]
    (h_int : MeasureTheory.Integrable
      (finiteSampleMax (q := q)) (M.iidProductMeasure q)) :
    ∫ sample, finiteSampleMax sample ∂M.iidProductMeasure q =
      M.expectedMaxValue q := by
  rw [h_int.integral_eq_integral_meas_lt
    M.iidProductMeasure_finiteSampleMax_nonnegative_ae]
  exact M.iidProductMeasure_finiteSampleMax_tailIntegral_eq_expectedMaxValue

/--
Literal Bochner expectation of the maximum of `q` iid rate-`M.rate`
exponential draws.
-/
theorem Model.iidProductMeasure_finiteSampleMax_integral_eq_expectedMaxValue
    (M : Model) {q : ℕ} [NeZero q] :
    ∫ sample, finiteSampleMax sample ∂M.iidProductMeasure q =
      M.expectedMaxValue q :=
  M.iidProductMeasure_finiteSampleMax_integral_eq_expectedMaxValue_of_integrable
    M.iidProductMeasure_finiteSampleMax_integrable

theorem finiteSampleMax_one_eq_eval_zero
    (sample : Fin 1 → ℝ) :
    finiteSampleMax sample = sample 0 := by
  unfold finiteSampleMax
  simp

theorem Model.integrable_id (M : Model) :
    MeasureTheory.Integrable (fun x : ℝ => x) M.measure := by
  have hmax_int :
      MeasureTheory.Integrable
        (finiteSampleMax (q := 1)) (M.iidProductMeasure 1) :=
    M.iidProductMeasure_finiteSampleMax_integrable (q := 1)
  have heval_int :
      MeasureTheory.Integrable
        (fun sample : Fin 1 → ℝ => sample 0) (M.iidProductMeasure 1) := by
    refine hmax_int.congr ?_
    exact Filter.Eventually.of_forall finiteSampleMax_one_eq_eval_zero
  let μ : Fin 1 → MeasureTheory.Measure ℝ := fun _ => M.measure
  have hprob :
      ∀ i : Fin 1,
        MeasureTheory.IsProbabilityMeasure (μ i) :=
    fun _ => M.isProbabilityMeasure_measure
  have hiff :=
    (@MeasureTheory.measurePreserving_eval
      (Fin 1) (fun _ : Fin 1 => ℝ) inferInstance
      (fun _ => inferInstance) μ hprob (0 : Fin 1)).integrable_comp
      (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable
  exact hiff.mp (by
    simpa [Model.iidProductMeasure, μ, Function.comp_def] using heval_int)

theorem Model.integral_id_eq_expectedMaxValue_one
    (M : Model) :
    ∫ x, x ∂M.measure = M.expectedMaxValue 1 := by
  have hmax :=
    M.iidProductMeasure_finiteSampleMax_integral_eq_expectedMaxValue (q := 1)
  have hmax_eval :
      ∫ sample,
          finiteSampleMax sample ∂M.iidProductMeasure 1 =
        ∫ sample : Fin 1 → ℝ,
          sample 0 ∂M.iidProductMeasure 1 := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall finiteSampleMax_one_eq_eval_zero
  let μ : Fin 1 → MeasureTheory.Measure ℝ := fun _ => M.measure
  have hprob :
      ∀ i : Fin 1,
        MeasureTheory.IsProbabilityMeasure (μ i) :=
    fun _ => M.isProbabilityMeasure_measure
  have heval :
      ∫ sample : Fin 1 → ℝ,
          sample 0 ∂M.iidProductMeasure 1 =
        ∫ x, x ∂M.measure := by
    simpa [Model.iidProductMeasure, μ] using
      (@MeasureTheory.integral_comp_eval
        (Fin 1) inferInstance (fun _ : Fin 1 => ℝ)
        (fun _ => inferInstance) μ ℝ inferInstance inferInstance hprob
        (0 : Fin 1) (fun x : ℝ => x)
        measurable_id.aestronglyMeasurable)
  calc
    ∫ x, x ∂M.measure =
        ∫ sample : Fin 1 → ℝ,
          sample 0 ∂M.iidProductMeasure 1 := heval.symm
    _ = ∫ sample,
          finiteSampleMax sample ∂M.iidProductMeasure 1 := hmax_eval.symm
    _ = M.expectedMaxValue 1 := hmax

theorem Model.iidProductMeasure_eval_integrable
    (M : Model) {q : ℕ} (i : Fin q) :
    MeasureTheory.Integrable
      (fun sample : Fin q → ℝ => sample i) (M.iidProductMeasure q) := by
  let μ : Fin q → MeasureTheory.Measure ℝ := fun _ => M.measure
  haveI : MeasureTheory.IsProbabilityMeasure M.measure :=
    M.isProbabilityMeasure_measure
  have hfinite : MeasureTheory.IsFiniteMeasure M.measure := inferInstance
  have hfin :
      ∀ j : Fin q,
        MeasureTheory.IsFiniteMeasure (μ j) :=
    fun _ => hfinite
  simpa [Model.iidProductMeasure, μ, Function.comp_def] using
    (@MeasureTheory.integrable_comp_eval
      (Fin q) inferInstance (fun _ : Fin q => ℝ)
      (fun _ => inferInstance) μ ℝ inferInstance hfin i
      (fun x : ℝ => x) M.integrable_id)

theorem Model.iidProductMeasure_finiteSampleMin_integrable
    (M : Model) {q : ℕ} [NeZero q] :
    MeasureTheory.Integrable
      (finiteSampleMin (q := q)) (M.iidProductMeasure q) := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let i0 : Fin q := ⟨0, hqpos⟩
  have hcoord_int :
      MeasureTheory.Integrable
        (fun sample : Fin q → ℝ => sample i0) (M.iidProductMeasure q) :=
    M.iidProductMeasure_eval_integrable i0
  refine MeasureTheory.Integrable.mono' hcoord_int
    finiteSampleMin_measurable.aestronglyMeasurable ?_
  filter_upwards [M.iidProductMeasure_all_nonnegative_ae q] with sample hsample
  have hmin_nonneg : 0 ≤ finiteSampleMin sample :=
    finiteSampleMin_nonnegative_of_forall (fun i => hsample i)
  have hcoord_nonneg : 0 ≤ sample i0 := hsample i0
  have hmin_le : finiteSampleMin sample ≤ sample i0 :=
    finiteSampleMin_le_sample sample i0
  simpa [Real.norm_eq_abs, abs_of_nonneg hmin_nonneg,
    abs_of_nonneg hcoord_nonneg] using hmin_le

/--
Conditional layer-cake bridge from the finite-minimum tail integral to the
literal Bochner expectation.
-/
theorem Model.iidProductMeasure_finiteSampleMin_integral_eq_expectedMinValue_of_integrable
    (M : Model) {q : ℕ} [NeZero q]
    (h_int : MeasureTheory.Integrable
      (finiteSampleMin (q := q)) (M.iidProductMeasure q)) :
    ∫ sample, finiteSampleMin sample ∂M.iidProductMeasure q =
      1 / ((q : ℝ) * M.rate) := by
  rw [h_int.integral_eq_integral_meas_lt
    M.iidProductMeasure_finiteSampleMin_nonnegative_ae]
  exact M.iidProductMeasure_finiteSampleMin_tailIntegral_eq_expectedMinValue

/-- Literal Bochner expectation of the minimum of `q` iid exponentials. -/
theorem Model.iidProductMeasure_finiteSampleMin_integral_eq_expectedMinValue
    (M : Model) {q : ℕ} [NeZero q] :
    ∫ sample, finiteSampleMin sample ∂M.iidProductMeasure q =
      1 / ((q : ℝ) * M.rate) :=
  M.iidProductMeasure_finiteSampleMin_integral_eq_expectedMinValue_of_integrable
    M.iidProductMeasure_finiteSampleMin_integrable

theorem Model.iidProductMeasure_eval_integral_eq_expectedMaxValue_one
    (M : Model) {q : ℕ} (i : Fin q) :
    ∫ sample,
        sample i ∂M.iidProductMeasure q =
      M.expectedMaxValue 1 := by
  let μ : Fin q → MeasureTheory.Measure ℝ := fun _ => M.measure
  have hprob :
      ∀ j : Fin q,
        MeasureTheory.IsProbabilityMeasure (μ j) :=
    fun _ => M.isProbabilityMeasure_measure
  calc
    ∫ sample,
        sample i ∂M.iidProductMeasure q =
        ∫ x, x ∂M.measure := by
      simpa [Model.iidProductMeasure, μ] using
        (@MeasureTheory.integral_comp_eval
          (Fin q) inferInstance (fun _ : Fin q => ℝ)
          (fun _ => inferInstance) μ ℝ inferInstance inferInstance hprob
          i (fun x : ℝ => x) measurable_id.aestronglyMeasurable)
    _ = M.expectedMaxValue 1 :=
      M.integral_id_eq_expectedMaxValue_one

theorem Model.iidProductMeasure_sum_integral_eq_card_mul_expectedMaxValue_one
    (M : Model) (q : ℕ) :
    ∫ sample,
        (∑ i : Fin q, sample i) ∂M.iidProductMeasure q =
      (q : ℝ) * M.expectedMaxValue 1 := by
  rw [MeasureTheory.integral_finset_sum]
  · simp [M.iidProductMeasure_eval_integral_eq_expectedMaxValue_one]
  · intro i _hi
    exact M.iidProductMeasure_eval_integrable i

theorem expectedMaxValueOfRate_one (rate : ℝ) :
    expectedMaxValueOfRate rate 1 = 1 / rate := by
  norm_num [expectedMaxValueOfRate, harmonicReal]

theorem Model.one_minus_cdf_eq_exp_neg_mul
    (M : Model) {x : ℝ} (hx : 0 ≤ x) :
    1 - ProbabilityTheory.cdf M.measure x =
      Real.exp (-(M.rate * x)) := by
  rw [M.cdf_eq x, if_pos hx]
  ring

/--
For one draw from the positive-rate exponential model, integrating the survival
function over the nonnegative line gives the same value as the harmonic
expected-maximum formula.

This is the `q = 1` measure-facing checkpoint for the top-one exponential
branch; the general `q` maximum still needs the product-measure/order-statistic
survival formula.
-/
theorem Model.singleDrawSurvivalIntegral_eq_expectedMaxValue
    (M : Model) :
    ∫ x in Set.Ioi (0 : ℝ), (1 - ProbabilityTheory.cdf M.measure x) =
      M.expectedMaxValue 1 := by
  have hsurv :
      ∫ x in Set.Ioi (0 : ℝ), (1 - ProbabilityTheory.cdf M.measure x) =
        ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(M.rate * x)) := by
    refine MeasureTheory.setIntegral_congr_fun
      measurableSet_Ioi ?_
    intro x hx
    exact M.one_minus_cdf_eq_exp_neg_mul (le_of_lt hx)
  rw [hsurv, integral_exp_neg_mul_Ioi M.rate M.rate_pos,
    Model.expectedMaxValue, expectedMaxValueOfRate_one]

end Exponential
end Probability
end AppliedModelingLib
