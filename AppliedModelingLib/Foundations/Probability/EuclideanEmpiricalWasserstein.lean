import AppliedModelingLib.Foundations.Probability.EmpiricalMeasure
import AppliedModelingLib.Foundations.Probability.FiniteIID
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import AppliedModelingLib.Foundations.Probability.EuclideanTruncation
import AppliedModelingLib.Foundations.Math.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Euclidean empirical Wasserstein events

This module supplies the measure-theoretic interface for concentration of the
empirical law of a finite iid sample in Wasserstein-1 distance.  It keeps the
transport primitive in `MeasureTransport` and records the Euclidean
exponential-moment hypothesis used by empirical-Wasserstein concentration
theorems.

The intended concentration result is the `p = 1` exponential-moment branch of
Fournier--Guillin, *On the rate of convergence in Wasserstein distance of the
empirical measure* (2015), Theorem 2:
<https://perso.lpsm.paris/~nfournier/a58.pdf>.

The outer-tail first-moment calculation directly uses Mathlib's
`integral_indicator` from
[`MeasureTheory/Integral/Bochner/Set.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Set.lean),
`integral_const_mul`, `integral_div`, `integral_mono_ae`, and
`ofReal_integral_eq_lintegral_ofReal` from
[`MeasureTheory/Integral/Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean),
and `Integrable.indicator` from
[`MeasureTheory/Integral/IntegrableOn.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/IntegrableOn.lean),
while the real-valued Markov-tail interfaces use `ENNReal.toReal_mono` and
`ENNReal.toReal_ofReal` from
[`Data/ENNReal/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/Real.lean)
and
[`Data/ENNReal/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/Basic.lean),
all at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. No source text is copied or
ported.
-/

namespace AppliedModelingLib
namespace Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/--
An exponential moment of the radial norm.  For a Euclidean law this is the
`E_{α,γ}` hypothesis in Fournier--Guillin's exponential-tail regime.
-/
def HasExponentialRadialMoment
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (law : ProbabilityMeasure E) (alpha gamma : ℝ) : Prop :=
  Integrable (fun x : E => Real.exp (gamma * Real.rpow ‖x‖ alpha))
    (law : Measure E)

/-- A quantitative exponential radial-moment hypothesis.  Unlike mere
integrability, its visible bound can be shared by a family of deployed laws
when one deterministic empirical-Wasserstein schedule is required. -/
def HasBoundedExponentialRadialMoment
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (law : ProbabilityMeasure E) (alpha gamma momentBound : ℝ) : Prop :=
  HasExponentialRadialMoment law alpha gamma ∧
    (∫ x : E, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂(law : Measure E)) ≤ momentBound

theorem HasBoundedExponentialRadialMoment.hasExponentialRadialMoment
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {law : ProbabilityMeasure E} {alpha gamma momentBound : ℝ}
    (hmoment : HasBoundedExponentialRadialMoment law alpha gamma momentBound) :
    HasExponentialRadialMoment law alpha gamma := hmoment.1

theorem HasBoundedExponentialRadialMoment.integral_le
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {law : ProbabilityMeasure E} {alpha gamma momentBound : ℝ}
    (hmoment : HasBoundedExponentialRadialMoment law alpha gamma momentBound) :
    (∫ x : E, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂(law : Measure E)) ≤ momentBound :=
  hmoment.2

/-- A single quantitative exponential-moment bound shared by an indexed
family of laws.  This is the form needed to choose one deterministic
confidence/sample schedule for adaptive sampling. -/
def HasUniformBoundedExponentialRadialMoment
    {Index E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (law : Index → ProbabilityMeasure E) (alpha gamma momentBound : ℝ) : Prop :=
  ∀ index, HasBoundedExponentialRadialMoment (law index) alpha gamma momentBound

theorem HasUniformBoundedExponentialRadialMoment.at
    {Index E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {law : Index → ProbabilityMeasure E} {alpha gamma momentBound : ℝ}
    (hmoment : HasUniformBoundedExponentialRadialMoment law alpha gamma momentBound)
    (index : Index) : HasBoundedExponentialRadialMoment (law index) alpha gamma momentBound :=
  hmoment index

/--
A continuous exponential-radial-moment functional is uniformly bounded on a
compact parameter set.  This is the bridge from pointwise integrability to a
single deterministic moment envelope when a sampling schedule must work for
every parameter in a compact deployed domain.

The compact-image bound is Mathlib's `IsCompact.bddAbove_image`, from
[`Mathlib/Topology/Order/Compact.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Order/Compact.lean),
Apache-2.0.  It is used as an upstream library result, not copied code.
-/
theorem exists_boundedExponentialRadialMoment_on_compact_of_continuous
    {Index E : Type*} [TopologicalSpace Index] [MeasurableSpace E] [NormedAddCommGroup E]
    (law : Index → ProbabilityMeasure E) (domain : Set Index) (alpha gamma : ℝ)
    (hcompact : IsCompact domain)
    (hmoment : ∀ index ∈ domain, HasExponentialRadialMoment (law index) alpha gamma)
    (hcontinuous : ContinuousOn (fun index =>
      ∫ datum : E, Real.exp (gamma * Real.rpow ‖datum‖ alpha) ∂(law index : Measure E)) domain) :
    ∃ momentBound : ℝ, ∀ index ∈ domain,
      HasBoundedExponentialRadialMoment (law index) alpha gamma momentBound := by
  obtain ⟨momentBound, hbound⟩ := hcompact.bddAbove_image hcontinuous
  refine ⟨momentBound, fun index hindex => ⟨hmoment index hindex, ?_⟩⟩
  exact hbound ⟨index, hindex, rfl⟩

/--
The elementary growth estimate that turns an exponential radial moment into a
first moment.  This is the analytic entrance condition needed to make the
independent transport coupling a finite W₁ witness.
-/
private theorem norm_le_one_add_inv_mul_exp_rpow
    {t alpha gamma : ℝ} (ht : 0 ≤ t) (halpha : 1 ≤ alpha) (hgamma : 0 < gamma) :
    t ≤ (1 + gamma⁻¹) * Real.exp (gamma * Real.rpow t alpha) := by
  have hpow_nonneg : 0 ≤ Real.rpow t alpha := Real.rpow_nonneg ht alpha
  have hbase : t ≤ 1 + Real.rpow t alpha := by
    by_cases htle : t ≤ 1
    · linarith
    · have hone_le : 1 ≤ t := le_of_lt (lt_of_not_ge htle)
      have hpower : t ≤ Real.rpow t alpha := Real.self_le_rpow_of_one_le hone_le halpha
      linarith
  have hexp_add_one : gamma * Real.rpow t alpha + 1 ≤
      Real.exp (gamma * Real.rpow t alpha) :=
    Real.add_one_le_exp _
  have hpower_bound : Real.rpow t alpha ≤
      gamma⁻¹ * Real.exp (gamma * Real.rpow t alpha) := by
    have hscaled : gamma * Real.rpow t alpha ≤
        Real.exp (gamma * Real.rpow t alpha) := by
      linarith
    calc
      Real.rpow t alpha = gamma⁻¹ * (gamma * Real.rpow t alpha) := by
        rw [← mul_assoc, inv_mul_cancel₀ hgamma.ne', one_mul]
      _ ≤ gamma⁻¹ * Real.exp (gamma * Real.rpow t alpha) :=
        mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hgamma.le)
  have hexp_one : 1 ≤ Real.exp (gamma * Real.rpow t alpha) := by
    exact Real.one_le_exp (mul_nonneg hgamma.le hpow_nonneg)
  calc
    t ≤ 1 + Real.rpow t alpha := hbase
    _ ≤ Real.exp (gamma * Real.rpow t alpha) +
        gamma⁻¹ * Real.exp (gamma * Real.rpow t alpha) :=
      add_le_add hexp_one hpower_bound
    _ = (1 + gamma⁻¹) * Real.exp (gamma * Real.rpow t alpha) := by ring

/--
The exponential radial-moment hypothesis of Fournier--Guillin supplies the
finite first moment required by W₁ transport constructions.
-/
theorem integrable_norm_of_exponentialRadialMoment
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (law : ProbabilityMeasure E) {alpha gamma : ℝ} (halpha : 1 ≤ alpha)
    (hgamma : 0 < gamma) (hmoment : HasExponentialRadialMoment law alpha gamma) :
    Integrable (fun x : E => ‖x‖) (law : Measure E) := by
  have hscaled : Integrable
      (fun x : E => (1 + gamma⁻¹) * Real.exp (gamma * Real.rpow ‖x‖ alpha))
      (law : Measure E) := by
    exact hmoment.const_mul (1 + gamma⁻¹)
  refine hscaled.mono' measurable_norm.aestronglyMeasurable ?_
  filter_upwards with x
  have hbound := norm_le_one_add_inv_mul_exp_rpow (t := ‖x‖)
    (norm_nonneg x) halpha hgamma
  have hscaled_nonneg : 0 ≤ (1 + gamma⁻¹) *
      Real.exp (gamma * Real.rpow ‖x‖ alpha) := by
    positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
    abs_of_nonneg hscaled_nonneg] using hbound

/--
The Markov truncation estimate used in the outer-shell part of an
empirical-Wasserstein proof.  It is deliberately stated before simplifying the
right hand side: the displayed integral is the exact exponential-moment
quantity available from the hypothesis.
-/
theorem measure_norm_ge_le_exponentialRadialMoment_div
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (law : ProbabilityMeasure E) {alpha gamma radius : ℝ}
    (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma) (hradius : 0 ≤ radius)
    (hmoment : HasExponentialRadialMoment law alpha gamma) :
    (law : Measure E) {x : E | radius ≤ ‖x‖} ≤
      ENNReal.ofReal (∫ x : E,
        Real.exp (gamma * Real.rpow ‖x‖ alpha) /
          Real.exp (gamma * Real.rpow radius alpha) ∂(law : Measure E)) := by
  let threshold : ℝ := Real.exp (gamma * Real.rpow radius alpha)
  have hthreshold_pos : 0 < threshold := Real.exp_pos _
  have hscaled : Integrable
      (fun x : E => Real.exp (gamma * Real.rpow ‖x‖ alpha) / threshold)
      (law : Measure E) := by
    exact hmoment.div_const threshold
  apply hscaled.measure_le_integral
  · filter_upwards with x
    exact div_nonneg (Real.exp_pos _).le hthreshold_pos.le
  · intro x hx
    rw [one_le_div hthreshold_pos]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hradius hx halpha) hgamma

/-- Real-valued non-strict radial Markov tail, used by source cube shells. -/
theorem measureReal_norm_ge_le_exponentialRadialMoment_div
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (law : ProbabilityMeasure E) {alpha gamma radius : ℝ}
    (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma) (hradius : 0 ≤ radius)
    (hmoment : HasExponentialRadialMoment law alpha gamma) :
    (law : Measure E).real {x : E | radius ≤ ‖x‖} ≤
      ∫ x : E, Real.exp (gamma * Real.rpow ‖x‖ alpha) /
        Real.exp (gamma * Real.rpow radius alpha) ∂(law : Measure E) := by
  have hmarkov := measure_norm_ge_le_exponentialRadialMoment_div law
    halpha hgamma hradius hmoment
  have hintegral_nonneg : 0 ≤ ∫ x : E,
      Real.exp (gamma * Real.rpow ‖x‖ alpha) /
        Real.exp (gamma * Real.rpow radius alpha) ∂(law : Measure E) := by
    apply integral_nonneg
    intro x
    exact div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  calc
    (law : Measure E).real {x : E | radius ≤ ‖x‖} =
        ((law : Measure E) {x : E | radius ≤ ‖x‖}).toReal := rfl
    _ ≤ (ENNReal.ofReal (∫ x : E,
        Real.exp (gamma * Real.rpow ‖x‖ alpha) /
          Real.exp (gamma * Real.rpow radius alpha) ∂(law : Measure E))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmarkov
    _ = _ := ENNReal.toReal_ofReal hintegral_nonneg

/--
The same radial Markov bound with its constant exponential denominator pulled
outside the integral.  This is reusable whenever an exponential radial moment
is converted into an explicit tail rate.

Library provenance: this directly uses Mathlib's `MeasureTheory.integral_div`
from
[`MeasureTheory/Integral/Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)
and `Real.exp_neg` from
[`Analysis/Complex/Exponential.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Complex/Exponential.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem measureReal_norm_ge_le_exponentialRadialMoment
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (law : ProbabilityMeasure E) {alpha gamma radius : ℝ}
    (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma) (hradius : 0 ≤ radius)
    (hmoment : HasExponentialRadialMoment law alpha gamma) :
    (law : Measure E).real {x : E | radius ≤ ‖x‖} ≤
      Real.exp (-(gamma * Real.rpow radius alpha)) *
        ∫ x : E, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂(law : Measure E) := by
  calc
    (law : Measure E).real {x : E | radius ≤ ‖x‖} ≤
        ∫ x : E, Real.exp (gamma * Real.rpow ‖x‖ alpha) /
          Real.exp (gamma * Real.rpow radius alpha) ∂(law : Measure E) :=
      measureReal_norm_ge_le_exponentialRadialMoment_div law halpha hgamma hradius hmoment
    _ = (∫ x : E, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂(law : Measure E)) /
        Real.exp (gamma * Real.rpow radius alpha) :=
      integral_div _ _
    _ = Real.exp (-(gamma * Real.rpow radius alpha)) *
        ∫ x : E, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂(law : Measure E) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      ring

/--
An exponential radial tail is bounded by a fifth-order polynomial tail.  The
fixed exponent is intentionally source-useful: it yields the `q = 5` dyadic
shell bound needed for the `p = 1`, `eta = 1` Fournier--Guillin allocation.

Library provenance: this reuses the local credited
`AppliedModelingLib.Math.exp_neg_le_factorial_div_pow` bridge and Mathlib's
`Real.self_le_rpow_of_one_le` from
[`Analysis/SpecialFunctions/Pow/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem exp_neg_mul_rpow_le_fifthOrderPolynomial
    {alpha gamma radius : ℝ} (halpha : 1 ≤ alpha) (hgamma : 0 < gamma)
    (hradius : 1 ≤ radius) :
    Real.exp (-(gamma * Real.rpow radius alpha)) ≤
      ((5 : ℕ).factorial : ℝ) * gamma⁻¹ ^ 5 / radius ^ 5 := by
  have hradius_pos : 0 < radius := lt_of_lt_of_le zero_lt_one hradius
  have hrpow_pos : 0 < Real.rpow radius alpha := Real.rpow_pos_of_pos hradius_pos _
  have harg_pos : 0 < gamma * Real.rpow radius alpha :=
    mul_pos hgamma hrpow_pos
  have hfactorial := AppliedModelingLib.Math.exp_neg_le_factorial_div_pow 5 harg_pos
  have hradius_le_rpow : radius ≤ Real.rpow radius alpha :=
    Real.self_le_rpow_of_one_le hradius halpha
  have hradius_pow_le : radius ^ 5 ≤ Real.rpow radius alpha ^ 5 :=
    pow_le_pow_left₀ hradius_pos.le hradius_le_rpow 5
  have hcoeff_nonneg : 0 ≤ ((5 : ℕ).factorial : ℝ) * gamma⁻¹ ^ 5 := by
    positivity
  calc
    Real.exp (-(gamma * Real.rpow radius alpha)) ≤
        ((5 : ℕ).factorial : ℝ) / (gamma * Real.rpow radius alpha) ^ 5 :=
      hfactorial
    _ = ((5 : ℕ).factorial : ℝ) * gamma⁻¹ ^ 5 /
        Real.rpow radius alpha ^ 5 := by
      field_simp [hgamma.ne', hrpow_pos.ne']
    _ ≤ ((5 : ℕ).factorial : ℝ) * gamma⁻¹ ^ 5 / radius ^ 5 := by
      exact div_le_div_of_nonneg_left hcoeff_nonneg (pow_pos hradius_pos _) hradius_pow_le

/--
The explicit fifth-order polynomial-tail constant induced by a radial
exponential moment.  It is independent of the ambient dimension and can be
reused for dyadic shell allocations or other radial truncations.
-/
noncomputable def fifthOrderExponentialRadialTailConstant
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (law : ProbabilityMeasure E) (alpha gamma : ℝ) : ℝ :=
  ((5 : ℕ).factorial : ℝ) * gamma⁻¹ ^ 5 *
    ∫ x : E, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂(law : Measure E)

/-- A bounded exponential moment gives a uniform bound on the fifth-order
tail constant used by the dyadic empirical-Wasserstein schedules. -/
theorem fifthOrderExponentialRadialTailConstant_le_of_boundedExponentialRadialMoment
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (law : ProbabilityMeasure E) {alpha gamma momentBound : ℝ}
    (hgamma : 0 ≤ gamma)
    (hmoment : HasBoundedExponentialRadialMoment law alpha gamma momentBound) :
    fifthOrderExponentialRadialTailConstant law alpha gamma ≤
      ((5 : ℕ).factorial : ℝ) * gamma⁻¹ ^ 5 * momentBound := by
  unfold fifthOrderExponentialRadialTailConstant
  apply mul_le_mul_of_nonneg_left hmoment.integral_le
  positivity

/-- A bounded radial exponential moment supplies a tail envelope that is
positive independently of whether the displayed moment bound has already been
normalized.  The `max momentBound 1` normalization is useful for schedules
that must be chosen before a particular law is fixed. -/
theorem fifthOrderExponentialRadialTailConstant_le_uniformBound_of_boundedExponentialRadialMoment
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (law : ProbabilityMeasure E) {alpha gamma momentBound : ℝ}
    (hgamma : 0 ≤ gamma)
    (hmoment : HasBoundedExponentialRadialMoment law alpha gamma momentBound) :
    fifthOrderExponentialRadialTailConstant law alpha gamma ≤
      ((5 : ℕ).factorial : ℝ) * gamma⁻¹ ^ 5 * max momentBound 1 := by
  refine (fifthOrderExponentialRadialTailConstant_le_of_boundedExponentialRadialMoment
    law hgamma hmoment).trans ?_
  gcongr
  exact le_max_left _ _

/-- The normalized fifth-order tail envelope is strictly positive whenever the
radial exponential rate is positive. -/
theorem fifthOrderExponentialRadialTailUniformBound_pos
    {gamma momentBound : ℝ} (hgamma : 0 < gamma) :
    0 < ((5 : ℕ).factorial : ℝ) * gamma⁻¹ ^ 5 * max momentBound 1 := by
  have hmax : 0 < max momentBound 1 :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  positivity

/-- Every class of laws with one bounded exponential radial moment has one
positive fifth-order tail envelope.  This packages the exact prerequisite used
by the dimension-aware empirical-Wasserstein count schedules. -/
theorem exists_positive_fifthOrderExponentialRadialTailEnvelope_of_boundedExponentialRadialMoment
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {alpha gamma momentBound : ℝ} (hgamma : 0 < gamma) :
    ∃ tailBound : ℝ, 0 < tailBound ∧
      ∀ law : ProbabilityMeasure E,
        HasBoundedExponentialRadialMoment law alpha gamma momentBound →
          fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound := by
  refine ⟨((5 : ℕ).factorial : ℝ) * gamma⁻¹ ^ 5 * max momentBound 1,
    fifthOrderExponentialRadialTailUniformBound_pos hgamma, ?_⟩
  intro law hmoment
  exact fifthOrderExponentialRadialTailConstant_le_uniformBound_of_boundedExponentialRadialMoment
    law hgamma.le hmoment

/--
The exponential-moment integral is at least one for nonnegative `gamma`.
This makes the fifth-order tail constant strictly positive whenever
`gamma > 0`.
-/
theorem one_le_exponentialRadialMomentIntegral
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (law : ProbabilityMeasure E) {alpha gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hmoment : HasExponentialRadialMoment law alpha gamma) :
    1 ≤ ∫ x : E, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂(law : Measure E) := by
  have hconst : Integrable (fun _ : E => (1 : ℝ)) (law : Measure E) :=
    integrable_const _
  have hpointwise : ∀ x : E, 1 ≤ Real.exp (gamma * Real.rpow ‖x‖ alpha) := by
    intro x
    apply Real.one_le_exp
    exact mul_nonneg hgamma (Real.rpow_nonneg (norm_nonneg x) alpha)
  calc
    1 = ∫ _ : E, (1 : ℝ) ∂(law : Measure E) := by
      simp [MeasureTheory.probReal_univ]
    _ ≤ ∫ x : E, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂(law : Measure E) :=
      integral_mono_ae hconst hmoment (ae_of_all _ hpointwise)

/-- A bounded nonnegative radial exponential moment has a moment bound at
least one.  This gives positivity of the common tail envelope used by uniform
empirical-Wasserstein schedules. -/
theorem one_le_momentBound_of_boundedExponentialRadialMoment
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (law : ProbabilityMeasure E) {alpha gamma momentBound : ℝ}
    (hgamma : 0 ≤ gamma)
    (hmoment : HasBoundedExponentialRadialMoment law alpha gamma momentBound) :
    1 ≤ momentBound :=
  (one_le_exponentialRadialMomentIntegral law hgamma hmoment.hasExponentialRadialMoment).trans
    hmoment.integral_le

/--
Strict positivity of the explicit fifth-order exponential-tail constant.
-/
theorem fifthOrderExponentialRadialTailConstant_pos
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (law : ProbabilityMeasure E) {alpha gamma : ℝ} (hgamma : 0 < gamma)
    (hmoment : HasExponentialRadialMoment law alpha gamma) :
    0 < fifthOrderExponentialRadialTailConstant law alpha gamma := by
  unfold fifthOrderExponentialRadialTailConstant
  have hintegral_pos : 0 < ∫ x : E,
      Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂(law : Measure E) := by
    exact lt_of_lt_of_le zero_lt_one
      (one_le_exponentialRadialMomentIntegral law hgamma.le hmoment)
  positivity

/--
Real-valued strict-tail form of the radial exponential-moment Markov bound.
The strict tail is used for the event that a finite iid sample changes under
radial collapse.
-/
theorem measureReal_norm_gt_le_exponentialRadialMoment_div
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (law : ProbabilityMeasure E) {alpha gamma radius : ℝ}
    (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma) (hradius : 0 ≤ radius)
    (hmoment : HasExponentialRadialMoment law alpha gamma) :
    (law : Measure E).real {x : E | radius < ‖x‖} ≤
      ∫ x : E, Real.exp (gamma * Real.rpow ‖x‖ alpha) /
        Real.exp (gamma * Real.rpow radius alpha) ∂(law : Measure E) := by
  have htail : (law : Measure E) {x : E | radius < ‖x‖} ≤
      (law : Measure E) {x : E | radius ≤ ‖x‖} := by
    apply measure_mono
    intro x hx
    exact (show radius < ‖x‖ from hx).le
  have hmarkov := measure_norm_ge_le_exponentialRadialMoment_div law
    halpha hgamma hradius hmoment
  have hintegral_nonneg : 0 ≤ ∫ x : E,
      Real.exp (gamma * Real.rpow ‖x‖ alpha) /
        Real.exp (gamma * Real.rpow radius alpha) ∂(law : Measure E) := by
    apply integral_nonneg
    intro x
    exact div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  calc
    (law : Measure E).real {x : E | radius < ‖x‖} =
        ((law : Measure E) {x : E | radius < ‖x‖}).toReal := rfl
    _ ≤ ((law : Measure E) {x : E | radius ≤ ‖x‖}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) htail
    _ ≤ (ENNReal.ofReal (∫ x : E,
        Real.exp (gamma * Real.rpow ‖x‖ alpha) /
          Real.exp (gamma * Real.rpow radius alpha) ∂(law : Measure E))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmarkov
    _ = _ := ENNReal.toReal_ofReal hintegral_nonneg

/--
Under the canonical finite iid law, the probability that radial collapse
changes at least one observation is at most the sample size times the
exponential-moment Markov tail.
-/
theorem measure_finiteIID_exists_norm_gt_le_exponentialRadialMoment_div
    (dimension : ℕ) (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (count : ℕ) {alpha gamma radius : ℝ}
    (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma) (hradius : 0 ≤ radius)
    (hmoment : HasExponentialRadialMoment law alpha gamma) :
    (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count).real
      {sample | ∃ index, radius < ‖sample index‖} ≤
      count * ∫ x : EuclideanSpace ℝ (Fin dimension),
        Real.exp (gamma * Real.rpow ‖x‖ alpha) /
          Real.exp (gamma * Real.rpow radius alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension))) := by
  calc
    (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count).real
        {sample | ∃ index, radius < ‖sample index‖} ≤
        count * (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
          {x | radius < ‖x‖} :=
      measure_finiteIID_exists_coordinate_mem_le
        (law : Measure (EuclideanSpace ℝ (Fin dimension))) count
        {x | radius < ‖x‖} (measurableSet_Ioi.preimage measurable_norm)
    _ ≤ count * ∫ x : EuclideanSpace ℝ (Fin dimension),
        Real.exp (gamma * Real.rpow ‖x‖ alpha) /
          Real.exp (gamma * Real.rpow radius alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension))) := by
      gcongr
      exact measureReal_norm_gt_le_exponentialRadialMoment_div law
        halpha hgamma hradius hmoment

/--
On a strict outer tail, the radial norm is dominated by the exponential-moment
density times an explicit exponentially small radius factor. This is the
pointwise analytic input to the truncation estimate.
-/
private theorem tail_norm_le_exponentialRadialMoment_density
    {t alpha gamma radius : ℝ} (ht : radius < t) (halpha : 1 ≤ alpha)
    (hgamma : 0 < gamma) (hradius : 0 ≤ radius) :
    t ≤ (1 + (gamma / 2)⁻¹) *
      Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
      Real.exp (gamma * Real.rpow t alpha) := by
  have hhalf_gamma : 0 < gamma / 2 := by positivity
  have ht_nonneg : 0 ≤ t := le_trans hradius ht.le
  have hbase := norm_le_one_add_inv_mul_exp_rpow ht_nonneg halpha hhalf_gamma
  calc
    t ≤ (1 + (gamma / 2)⁻¹) * Real.exp ((gamma / 2) * Real.rpow t alpha) := hbase
    _ ≤ (1 + (gamma / 2)⁻¹) *
        (Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
          Real.exp (gamma * Real.rpow t alpha)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hpow : Real.rpow radius alpha ≤ Real.rpow t alpha :=
        Real.rpow_le_rpow hradius ht.le (by linarith [halpha])
      nlinarith
    _ = (1 + (gamma / 2)⁻¹) *
        Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
        Real.exp (gamma * Real.rpow t alpha) := by ring

/--
The exact first moment of the strict outer Euclidean tail is exponentially
small under the `E_{alpha,gamma}` radial-moment hypothesis. The theorem retains
the moment integral explicitly rather than replacing it by an unrecorded
paper-specific constant.
-/
theorem setIntegral_norm_gt_le_exponentialRadialMoment
    (dimension : ℕ) (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    {alpha gamma radius : ℝ} (halpha : 1 ≤ alpha) (hgamma : 0 < gamma)
    (hradius : 0 ≤ radius) (hmoment : HasExponentialRadialMoment law alpha gamma) :
    ∫ x in {x | radius < ‖x‖}, ‖x‖ ∂
      (law : Measure (EuclideanSpace ℝ (Fin dimension))) ≤
      (1 + (gamma / 2)⁻¹) *
        Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
        ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension))) := by
  let tail : Set (EuclideanSpace ℝ (Fin dimension)) := {x | radius < ‖x‖}
  have htail : MeasurableSet tail := measurableSet_Ioi.preimage measurable_norm
  have hnorm : Integrable (fun x : EuclideanSpace ℝ (Fin dimension) => ‖x‖)
      (law : Measure _) :=
    integrable_norm_of_exponentialRadialMoment law halpha hgamma hmoment
  have hleft : Integrable (tail.indicator fun x : EuclideanSpace ℝ (Fin dimension) => ‖x‖)
      (law : Measure _) := hnorm.indicator htail
  have hright : Integrable (fun x : EuclideanSpace ℝ (Fin dimension) =>
      (1 + (gamma / 2)⁻¹) *
        Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
        Real.exp (gamma * Real.rpow ‖x‖ alpha)) (law : Measure _) := by
    exact hmoment.const_mul ((1 + (gamma / 2)⁻¹) *
      Real.exp (-(gamma / 2) * Real.rpow radius alpha))
  rw [← integral_indicator htail]
  rw [← integral_const_mul]
  exact integral_mono_ae hleft hright (Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ tail
    · rw [Set.indicator_of_mem hx]
      exact tail_norm_le_exponentialRadialMoment_density hx halpha hgamma hradius
    · rw [Set.indicator_of_notMem hx]
      positivity)

/--
Extended-integral form of `setIntegral_norm_gt_le_exponentialRadialMoment`,
matching the nonnegative first-moment quantity in the primal W₁ truncation
bound.
-/
theorem setLIntegral_norm_gt_le_exponentialRadialMoment
    (dimension : ℕ) (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    {alpha gamma radius : ℝ} (halpha : 1 ≤ alpha) (hgamma : 0 < gamma)
    (hradius : 0 ≤ radius) (hmoment : HasExponentialRadialMoment law alpha gamma) :
    ∫⁻ x in {x | radius < ‖x‖}, ENNReal.ofReal ‖x‖ ∂
      (law : Measure (EuclideanSpace ℝ (Fin dimension))) ≤
      ENNReal.ofReal ((1 + (gamma / 2)⁻¹) *
        Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
        ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension)))) := by
  have hnorm : Integrable (fun x : EuclideanSpace ℝ (Fin dimension) => ‖x‖)
      (law : Measure _) :=
    integrable_norm_of_exponentialRadialMoment law halpha hgamma hmoment
  rw [← ofReal_integral_eq_lintegral_ofReal hnorm.integrableOn
    (Filter.Eventually.of_forall fun x => norm_nonneg x)]
  exact ENNReal.ofReal_le_ofReal
    (setIntegral_norm_gt_le_exponentialRadialMoment dimension law
      halpha hgamma hradius hmoment)

/--
The radial-collapse W₁ error of a Euclidean law has the explicit
exponential-moment outer-tail bound.
-/
theorem wassersteinOne_euclideanRadialCollapse_le_exponentialRadialMoment
    (dimension : ℕ) (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    {alpha gamma radius : ℝ} (halpha : 1 ≤ alpha) (hgamma : 0 < gamma)
    (hradius : 0 ≤ radius) (hmoment : HasExponentialRadialMoment law alpha gamma) :
    ProbabilityCoupling.wassersteinOne law
      (law.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable) ≤
      ENNReal.ofReal ((1 + (gamma / 2)⁻¹) *
        Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
        ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension)))) := by
  calc
    ProbabilityCoupling.wassersteinOne law
        (law.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable) ≤
        ∫⁻ x in {x | radius < ‖x‖}, ENNReal.ofReal ‖x‖ ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension))) :=
      wassersteinOne_euclideanRadialCollapse_le_tailFirstMoment dimension radius law
    _ ≤ ENNReal.ofReal ((1 + (gamma / 2)⁻¹) *
        Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
        ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension)))) :=
      setLIntegral_norm_gt_le_exponentialRadialMoment dimension law
        halpha hgamma hradius hmoment

/-- The extended-real W₁ distance from a positive finite sample's empirical law to `law`. -/
noncomputable def empiricalWassersteinOne
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    (law : ProbabilityMeasure E) {count : ℕ}
    (hcount : 0 < count) (sample : Fin count → E) : ℝ≥0∞ :=
  ProbabilityCoupling.wassersteinOne
    (empiricalSampleProbabilityMeasureOfPos hcount sample) law

/--
An empirical law has a finite real W₁ witness against every population law
with an integrable norm.  The empirical side is automatic because the sample
has finite support; the witness is the independent coupling.
-/
theorem empiricalExpectedDistanceCosts_nonempty_of_integrable_norm
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    (law : ProbabilityMeasure E)
    (hlaw : Integrable (fun x : E => ‖x‖) (law : Measure E))
    {count : ℕ} (hcount : 0 < count) (sample : Fin count → E) :
    (ProbabilityCoupling.expectedDistanceCosts
      (empiricalSampleProbabilityMeasureOfPos hcount sample) law).Nonempty := by
  letI : Nonempty (Fin count) := Fin.pos_iff_nonempty.mp hcount
  change (ProbabilityCoupling.expectedDistanceCosts
    (empiricalSampleProbabilityMeasure sample) law).Nonempty
  exact ProbabilityCoupling.expectedDistanceCosts_nonempty_of_integrable_norm
    (empiricalSampleProbabilityMeasure sample) law
    (integrable_norm_empiricalSampleProbabilityMeasure sample) hlaw

/--
Under the exponential-moment regime of the Euclidean empirical-Wasserstein
theorem, every nonempty empirical law has a finite real W₁ witness against the
population law.
-/
theorem empiricalExpectedDistanceCosts_nonempty_of_exponentialRadialMoment
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    (law : ProbabilityMeasure E) {alpha gamma : ℝ} (halpha : 1 ≤ alpha)
    (hgamma : 0 < gamma) (hmoment : HasExponentialRadialMoment law alpha gamma)
    {count : ℕ} (hcount : 0 < count) (sample : Fin count → E) :
    (ProbabilityCoupling.expectedDistanceCosts
      (empiricalSampleProbabilityMeasureOfPos hcount sample) law).Nonempty :=
  empiricalExpectedDistanceCosts_nonempty_of_integrable_norm law
    (integrable_norm_of_exponentialRadialMoment law halpha hgamma hmoment) hcount sample

/-- The frequency of a measurable cell in a finite sample, as a real number. -/
noncomputable def finiteIIDCellFrequency
    {E : Type*} [MeasurableSpace E] (count : ℕ) (cell : Set E)
    (sample : Fin count → E) : ℝ :=
  (∑ index, cell.indicator (fun _ : E => (1 : ℝ)) (sample index)) / count

/-- A finite-sample frequency is measurable whenever its cell is measurable. -/
theorem measurable_finiteIIDCellFrequency
    {E : Type*} [MeasurableSpace E] (count : ℕ) (cell : Set E)
    (hcell : MeasurableSet cell) :
    Measurable (finiteIIDCellFrequency count cell) := by
  unfold finiteIIDCellFrequency
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro index _
  exact (Measurable.indicator measurable_const hcell).comp (measurable_pi_apply index)

/--
The frequency of a cell is exactly the cardinality of the selected-index
finset divided by the sample size.  This is the deterministic bridge from a
one-cell Hoeffding event to a random selected sample cardinality.

Library provenance: this uses Mathlib's `Finset.sum_boole` from
[`Algebra/BigOperators/Ring/Finset.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/BigOperators/Ring/Finset.lean),
at the pinned Apache-2.0 Mathlib commit. No source text is copied or ported.
-/
theorem finiteIIDCellFrequency_eq_empiricalSampleIndicesInSet_card_div
    {E : Type*} [MeasurableSpace E] (count : ℕ) (cell : Set E)
    (sample : Fin count → E) :
    finiteIIDCellFrequency count cell sample =
      ((empiricalSampleIndicesInSet sample cell).card : ℝ) / count := by
  classical
  unfold finiteIIDCellFrequency empiricalSampleIndicesInSet empiricalFintypeIndicesInSet
  change (∑ index : Fin count, if sample index ∈ cell then (1 : ℝ) else 0) / count =
    ((Finset.univ.filter fun index => sample index ∈ cell).card : ℝ) / count
  rw [Finset.sum_boole]

/--
The cell frequency is exactly the mass assigned by the nonempty empirical
probability law.  This is the measure-valued bridge from a finite partition to
the empirical W₁ problem.

Library provenance: it uses Mathlib's `PMF.toMeasure_map_apply` from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean>
at the pinned Apache-2.0 Mathlib commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
No source text is copied or ported; its axiom report has only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.
-/
theorem empiricalSampleProbabilityMeasureOfPos_real_cell_eq_finiteIIDCellFrequency
    {E : Type*} [MeasurableSpace E] {count : ℕ} (hcount : 0 < count)
    (sample : Fin count → E) (cell : Set E) (hcell : MeasurableSet cell) :
    (empiricalSampleProbabilityMeasureOfPos hcount sample : Measure E).real cell =
      finiteIIDCellFrequency count cell sample := by
  letI : Nonempty (Fin count) := Fin.pos_iff_nonempty.mp hcount
  rw [empiricalSampleProbabilityMeasureOfPos_eq_empiricalSampleProbabilityMeasure]
  change (empiricalSampleLaw sample).toMeasure.real cell = _
  unfold empiricalSampleLaw
  unfold Measure.real
  rw [PMF.toMeasure_map_apply sample (PMF.uniformOfFintype (Fin count)) cell
    (measurable_of_finite sample) hcell]
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · unfold finiteIIDCellFrequency
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro index _
    by_cases hsample : sample index ∈ cell
    · have hpre : index ∈ sample ⁻¹' cell := hsample
      rw [Set.indicator_of_mem hpre]
      rw [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv]
      norm_cast
      rw [Set.indicator_of_mem hsample]
      ring
    · have hpre : index ∉ sample ⁻¹' cell := hsample
      rw [Set.indicator_of_notMem hpre]
      simp [Set.indicator_of_notMem hsample]
  · intro index _
    by_cases hsample : index ∈ sample ⁻¹' cell
    · simp only [Set.indicator_of_mem hsample]
      rw [PMF.uniformOfFintype_apply, Fintype.card_fin]
      exact ENNReal.inv_ne_top.mpr (by exact_mod_cast Nat.ne_of_gt hcount)
    · simp [Set.indicator, hsample]

/--
The exact bridge from a frequency-scale relative cell event to the raw
indicator-count event.  It records the only use of division by the sample
size, under an explicit positive-count premise.
-/
theorem finiteIIDCellFrequency_relativeTail_eq_indicatorSumRelativeTail
    {E : Type*} [MeasurableSpace E] (law : ProbabilityMeasure E)
    (count : ℕ) (hcount : 0 < count) (cell : Set E) (z : ℝ) :
    {sample : Fin count → E |
      (law : Measure E).real cell * z ≤
        |finiteIIDCellFrequency count cell sample - (law : Measure E).real cell|} =
      finiteIIDIndicatorSumRelativeTail (law : Measure E) count cell z := by
  letI : Nonempty (Fin count) := Fin.pos_iff_nonempty.mp hcount
  have hcount_real_pos : 0 < (count : ℝ) := by exact_mod_cast hcount
  ext sample
  simp only [Set.mem_setOf_eq]
  unfold finiteIIDCellFrequency finiteIIDIndicatorSumRelativeTail
  have hsub :
      (∑ index, cell.indicator (fun _ : E => (1 : ℝ)) (sample index)) / (count : ℝ) -
        (law : Measure E).real cell =
      ((∑ index, cell.indicator (fun _ : E => (1 : ℝ)) (sample index)) -
        (count : ℝ) * (law : Measure E).real cell) / (count : ℝ) := by
    field_simp
  rw [hsub]
  rw [abs_div, abs_of_pos hcount_real_pos]
  constructor
  · intro h
    apply (le_div_iff₀ hcount_real_pos).mp at h
    have hscaled : (count : ℝ) * (law : Measure E).real cell * z ≤
        |(∑ index, cell.indicator (fun _ : E => (1 : ℝ)) (sample index)) -
          (count : ℝ) * (law : Measure E).real cell| := by
      convert h using 1 <;> ring
    simpa only [Set.mem_setOf_eq] using hscaled
  · intro h
    apply (le_div_iff₀ hcount_real_pos).mpr
    have hscaled : (count : ℝ) * (law : Measure E).real cell * z ≤
        |(∑ index, cell.indicator (fun _ : E => (1 : ℝ)) (sample index)) -
          (count : ℝ) * (law : Measure E).real cell| := by
      simpa only [Set.mem_setOf_eq] using h
    convert hscaled using 1 <;> ring

/--
The source-compatible relative small-deviation tail for an empirical frequency
of one measurable cell.  It is the frequency-scale view of the reusable
count-scale Bernoulli MGF estimate.
-/
theorem measure_finiteIIDCellFrequency_relativeTail_le_exp_quadratic
    {E : Type*} [MeasurableSpace E] (law : ProbabilityMeasure E)
    (count : ℕ) (hcount : 0 < count) (cell : Set E) (hcell : MeasurableSet cell)
    (z : ℝ) (hz_nonneg : 0 ≤ z) (hz_le_two : z ≤ 2) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      (law : Measure E).real cell * z ≤
        |finiteIIDCellFrequency count cell sample - (law : Measure E).real cell|} ≤
      2 * Real.exp (-((count : ℝ) * (law : Measure E).real cell * (z ^ 2 / 4))) := by
  rw [finiteIIDCellFrequency_relativeTail_eq_indicatorSumRelativeTail law count hcount cell z]
  exact measureReal_finiteIIDIndicatorSumRelativeTail_le_exp_quadratic
    (law : Measure E) count cell hcell z hz_nonneg hz_le_two

/--
The frequency-scale counterpart of the fixed-tilt bounded-middle relative
count bound.  It is kept alongside the `z ≤ 2` interface so shell arguments
can separate their small, middle, and logarithmic large regimes explicitly.
-/
theorem measure_finiteIIDCellFrequency_relativeTail_le_exp_quadratic_of_two_le_of_le_nine
    {E : Type*} [MeasurableSpace E] (law : ProbabilityMeasure E)
    (count : ℕ) (hcount : 0 < count) (cell : Set E) (hcell : MeasurableSet cell)
    (z : ℝ) (hz_two : 2 ≤ z) (hz_nine : z ≤ 9) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      (law : Measure E).real cell * z ≤
        |finiteIIDCellFrequency count cell sample - (law : Measure E).real cell|} ≤
      Real.exp (-((count : ℝ) * (law : Measure E).real cell * (z ^ 2 / 18))) := by
  rw [finiteIIDCellFrequency_relativeTail_eq_indicatorSumRelativeTail law count hcount cell z]
  exact measureReal_finiteIIDIndicatorSumRelativeTail_le_exp_quadratic_of_two_le_of_le_nine
    (law : Measure E) count cell hcell z hz_two hz_nine

/--
The matching large-relative-deviation empirical-frequency tail.  This exposes
the `N μ(cell)` sparse-cell branch without redoing the raw count argument.
-/
theorem measure_finiteIIDCellFrequency_relativeTail_le_count_mul
    {E : Type*} [MeasurableSpace E] (law : ProbabilityMeasure E)
    (count : ℕ) (hcount : 0 < count) (cell : Set E) (hcell : MeasurableSet cell)
    (z : ℝ) (hz_one_lt : 1 < z)
    (hcell_mass_pos : 0 < (law : Measure E).real cell) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      (law : Measure E).real cell * z ≤
        |finiteIIDCellFrequency count cell sample - (law : Measure E).real cell|} ≤
      count * (law : Measure E).real cell := by
  rw [finiteIIDCellFrequency_relativeTail_eq_indicatorSumRelativeTail law count hcount cell z]
  exact measureReal_finiteIIDIndicatorSumRelativeTail_le_count_mul
    (law : Measure E) count hcount cell hcell z hz_one_lt hcell_mass_pos

/--
The optimized large-relative-deviation empirical-frequency tail.  Together
with the sparse-cell branch this is the source's Lemma 12(a)--(b) input for a
noncompact dyadic shell schedule.
-/
theorem measure_finiteIIDCellFrequency_relativeTail_le_exp_bennett_of_one_lt
    {E : Type*} [MeasurableSpace E] (law : ProbabilityMeasure E)
    (count : ℕ) (hcount : 0 < count) (cell : Set E) (hcell : MeasurableSet cell)
    (z : ℝ) (hz_one_lt : 1 < z) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      (law : Measure E).real cell * z ≤
        |finiteIIDCellFrequency count cell sample - (law : Measure E).real cell|} ≤
      Real.exp (-((count : ℝ) * (law : Measure E).real cell *
        ((1 + z) * Real.log (1 + z) - z))) := by
  rw [finiteIIDCellFrequency_relativeTail_eq_indicatorSumRelativeTail law count hcount cell z]
  exact measureReal_finiteIIDIndicatorSumRelativeTail_le_exp_bennett_of_one_lt
    (law : Measure E) count cell hcell z hz_one_lt

/--
A single measurable cell has the canonical iid Hoeffding upper tail.

Library provenance: this is a local specialization of
`AppliedModelingLib.measure_sum_centered_bounded_ge_le_exp_of_iIndepFun`, which in turn
uses Mathlib's `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`
from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Moments/SubGaussian.lean>.
The pinned Mathlib commit is `5450b53e5ddc75d46418fabb605edbf36bd0beb6`, under
Apache-2.0; no Mathlib source text is copied or ported here.  The used local
wrapper and upstream declaration have only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms in their checked axiom reports.
-/
theorem measure_finiteIIDCellFrequency_upperTail_le_exp
    {E : Type*} [MeasurableSpace E] (law : ProbabilityMeasure E)
    (count : ℕ) (hcount : 0 < count) (cell : Set E) (hcell : MeasurableSet cell)
    (error : ℝ) (herror : 0 ≤ error) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      (law : Measure E).real cell + error ≤
        finiteIIDCellFrequency count cell sample} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw (law : Measure E) count) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  let observation : Fin count → (Fin count → E) → ℝ := fun index sample =>
    cell.indicator (fun _ : E => (1 : ℝ)) (sample index)
  have hindependent : iIndepFun observation (finiteIIDSampleLaw (law : Measure E) count) := by
    simpa only [observation, finiteIIDSampleCoordinate, Function.comp_apply] using
      (iIndepFun_finiteIIDSampleCoordinate (law : Measure E) count).comp
        (fun _ datum => cell.indicator (fun _ : E => (1 : ℝ)) datum)
        (fun _ => measurable_const.indicator hcell)
  have hmeasurable : ∀ index, Measurable (observation index) := by
    intro index
    exact (measurable_const.indicator hcell).comp (measurable_pi_apply _)
  have hbounded : ∀ index, ∀ᵐ sample ∂(finiteIIDSampleLaw (law : Measure E) count),
      observation index sample ∈ Set.Icc (0 : ℝ) 1 := by
    intro index
    filter_upwards [] with sample
    by_cases hsample : sample index ∈ cell <;> simp [observation, hsample]
  have hmean : ∀ index, ∫ sample, observation index sample ∂
      finiteIIDSampleLaw (law : Measure E) count = (law : Measure E).real cell := by
    intro index
    calc
      ∫ sample, observation index sample ∂finiteIIDSampleLaw (law : Measure E) count =
          ∫ x, cell.indicator (fun _ : E => (1 : ℝ)) x ∂
            Measure.map (fun sample => sample index) (finiteIIDSampleLaw (law : Measure E) count) := by
        symm
        apply integral_map
        · exact (measurable_pi_apply index).aemeasurable
        · exact (measurable_const.indicator hcell).aestronglyMeasurable
      _ = (law : Measure E).real cell := by
        change ∫ x, cell.indicator (fun _ : E => (1 : ℝ)) x ∂
          Measure.map (finiteIIDSampleCoordinate index)
            (finiteIIDSampleLaw (law : Measure E) count) = _
        rw [map_finiteIIDSampleCoordinate (law : Measure E) count index]
        exact integral_indicator_one hcell
  have hcount_real_pos : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hcentered : ∀ sample,
      (∑ index, (observation index sample - ∫ x, observation index x ∂
        finiteIIDSampleLaw (law : Measure E) count)) =
        (∑ index, observation index sample) - (count : ℝ) * (law : Measure E).real cell := by
    intro sample
    rw [Finset.sum_sub_distrib]
    simp_rw [hmean]
    simp
  have hevent : {sample |
      (law : Measure E).real cell + error ≤ finiteIIDCellFrequency count cell sample} =
      {sample | (count : ℝ) * error ≤ ∑ index,
        (observation index sample - ∫ x, observation index x ∂
          finiteIIDSampleLaw (law : Measure E) count)} := by
    ext sample
    change (law : Measure E).real cell + error ≤
      (∑ index, observation index sample) / (count : ℝ) ↔
      (count : ℝ) * error ≤ ∑ index,
        (observation index sample - ∫ x, observation index x ∂
          finiteIIDSampleLaw (law : Measure E) count)
    rw [hcentered sample]
    constructor
    · intro h
      have hmult := (le_div_iff₀ hcount_real_pos).mp h
      nlinarith
    · intro h
      apply (le_div_iff₀ hcount_real_pos).mpr
      nlinarith
  rw [hevent]
  have htail :=
    measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
      (finiteIIDSampleLaw (law : Measure E) count) hindependent (s := Finset.univ)
      (a := 0) (b := 1) (ε := (count : ℝ) * error)
      (fun index _ => (hmeasurable index).aemeasurable) (fun index _ => hbounded index)
      (mul_nonneg hcount_real_pos.le herror)
  calc
    _ ≤ Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * ((∑ _ : Fin count, ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
      simpa only [Fintype.card_fin] using htail
    _ = _ := by
      congr 1
      congr 1
      norm_num
      ring

/--
A single measurable cell has the matching canonical iid Hoeffding lower tail.
Together with `measure_finiteIIDCellFrequency_upperTail_le_exp`, this gives the
two-sided atomic estimate needed for finite partition transport bounds.  It
uses the same checked local Hoeffding wrapper and pinned Mathlib provenance as
the upper-tail theorem; no external code is copied or ported.
-/
theorem measure_finiteIIDCellFrequency_lowerTail_le_exp
    {E : Type*} [MeasurableSpace E] (law : ProbabilityMeasure E)
    (count : ℕ) (hcount : 0 < count) (cell : Set E) (hcell : MeasurableSet cell)
    (error : ℝ) (herror : 0 ≤ error) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      finiteIIDCellFrequency count cell sample ≤ (law : Measure E).real cell - error} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw (law : Measure E) count) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  let score : E → ℝ := fun datum => cell.indicator (fun _ : E => (1 : ℝ)) datum
  let observation : Fin count → (Fin count → E) → ℝ := fun index sample =>
    -score (sample index)
  have hscore_measurable : Measurable score := measurable_const.indicator hcell
  have hindependent : iIndepFun observation (finiteIIDSampleLaw (law : Measure E) count) := by
    simpa only [observation, finiteIIDSampleCoordinate, Function.comp_apply] using
      (iIndepFun_finiteIIDSampleCoordinate (law : Measure E) count).comp
        (fun _ datum => -score datum) (fun _ => hscore_measurable.neg)
  have hmeasurable : ∀ index, Measurable (observation index) := by
    intro index
    exact hscore_measurable.neg.comp (measurable_pi_apply _)
  have hbounded : ∀ index, ∀ᵐ sample ∂(finiteIIDSampleLaw (law : Measure E) count),
      observation index sample ∈ Set.Icc (-1 : ℝ) 0 := by
    intro index
    filter_upwards [] with sample
    by_cases hsample : sample index ∈ cell <;> simp [observation, score, hsample]
  have hmean : ∀ index, ∫ sample, observation index sample ∂
      finiteIIDSampleLaw (law : Measure E) count = -(law : Measure E).real cell := by
    intro index
    calc
      ∫ sample, observation index sample ∂finiteIIDSampleLaw (law : Measure E) count =
          ∫ x, -score x ∂ Measure.map (fun sample => sample index)
            (finiteIIDSampleLaw (law : Measure E) count) := by
        symm
        apply integral_map
        · exact (measurable_pi_apply index).aemeasurable
        · exact hscore_measurable.neg.aestronglyMeasurable
      _ = -(law : Measure E).real cell := by
        change ∫ x, -score x ∂ Measure.map (finiteIIDSampleCoordinate index)
          (finiteIIDSampleLaw (law : Measure E) count) = _
        rw [map_finiteIIDSampleCoordinate (law : Measure E) count index]
        rw [integral_neg]
        change -(∫ x, cell.indicator (fun _ : E => (1 : ℝ)) x ∂(law : Measure E)) = _
        congr 1
        exact integral_indicator_one hcell
  have hcount_real_pos : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hcentered : ∀ sample,
      (∑ index, (observation index sample - ∫ x, observation index x ∂
        finiteIIDSampleLaw (law : Measure E) count)) =
        (count : ℝ) * (law : Measure E).real cell -
          ∑ index, score (sample index) := by
    intro sample
    rw [Finset.sum_sub_distrib]
    simp_rw [hmean]
    simp only [observation, Finset.sum_neg_distrib]
    simp
    ring
  have hevent : {sample |
      finiteIIDCellFrequency count cell sample ≤ (law : Measure E).real cell - error} =
      {sample | (count : ℝ) * error ≤ ∑ index,
        (observation index sample - ∫ x, observation index x ∂
          finiteIIDSampleLaw (law : Measure E) count)} := by
    ext sample
    change (∑ index, score (sample index)) / (count : ℝ) ≤
      (law : Measure E).real cell - error ↔
      (count : ℝ) * error ≤ ∑ index,
        (observation index sample - ∫ x, observation index x ∂
          finiteIIDSampleLaw (law : Measure E) count)
    rw [hcentered sample]
    constructor
    · intro h
      have hmult := (div_le_iff₀ hcount_real_pos).mp h
      nlinarith
    · intro h
      apply (div_le_iff₀ hcount_real_pos).mpr
      nlinarith
  rw [hevent]
  have htail :=
    measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
      (finiteIIDSampleLaw (law : Measure E) count) hindependent (s := Finset.univ)
      (a := -1) (b := 0) (ε := (count : ℝ) * error)
      (fun index _ => (hmeasurable index).aemeasurable) (fun index _ => hbounded index)
      (mul_nonneg hcount_real_pos.le herror)
  calc
    _ ≤ Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * ((∑ _ : Fin count, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
      simpa only [Fintype.card_fin] using htail
    _ = _ := by
      congr 1
      congr 1
      norm_num
      ring

/--
The number of observations selected by a measurable cell is unlikely to fall
below one half of its population mass.  This is the finite-sample count bound
used before conditioning on a fixed membership pattern: the event is stated
in terms of the actual selected index set, so it can be partitioned exactly by
the `finiteIIDMembershipPattern` fibers.

It is an algebraic specialization of the preceding checked lower Hoeffding
tail, with deviation equal to half the cell mass; it introduces no additional
external Lean dependency or source material.
-/
theorem measure_finiteIIDSelectedIndexRatio_lowerTail_half_le_exp
    {E : Type*} [MeasurableSpace E] (law : ProbabilityMeasure E)
    (count : ℕ) (hcount : 0 < count) (cell : Set E) (hcell : MeasurableSet cell) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      ((empiricalSampleIndicesInSet sample cell).card : ℝ) / count ≤
        (law : Measure E).real cell / 2} ≤
      Real.exp (-((count : ℝ) * ((law : Measure E).real cell) ^ 2) / 2) := by
  have hcount_real_pos : 0 < (count : ℝ) := by
    exact_mod_cast hcount
  have hmass_nonneg : 0 ≤ (law : Measure E).real cell := measureReal_nonneg
  have hevent : {sample |
      ((empiricalSampleIndicesInSet sample cell).card : ℝ) / count ≤
        (law : Measure E).real cell / 2} =
      {sample | finiteIIDCellFrequency count cell sample ≤
        (law : Measure E).real cell - (law : Measure E).real cell / 2} := by
    ext sample
    simp only [Set.mem_setOf_eq]
    rw [finiteIIDCellFrequency_eq_empiricalSampleIndicesInSet_card_div]
    ring_nf
  rw [hevent]
  calc
    _ ≤ Real.exp (-((count : ℝ) * ((law : Measure E).real cell / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) :=
      measure_finiteIIDCellFrequency_lowerTail_le_exp law count hcount cell hcell
        ((law : Measure E).real cell / 2) (by linarith)
    _ = Real.exp (-((count : ℝ) * ((law : Measure E).real cell) ^ 2) / 2) := by
      congr 1
      field_simp [ne_of_gt hcount_real_pos]
      ring

/--
The same selected-index half-mass event has a multiplicative binomial tail.
Unlike the additive Hoeffding bound, its exponent is linear in the population
cell mass and can therefore support a countable dyadic-shell allocation.

This is the fixed-parameter `theta = 1` specialization of the source's
Fournier--Guillin Lemma 12(c) MGF step, proved through the reusable
arbitrary-measurable-space Chernoff theorem in `FiniteIID.lean`; no new
external Lean source is reused here.
-/
theorem measure_finiteIIDSelectedIndexRatio_lowerTail_half_le_exp_linear
    {E : Type*} [MeasurableSpace E] (law : ProbabilityMeasure E)
    (count : ℕ) (hcount : 0 < count) (cell : Set E) (hcell : MeasurableSet cell) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      ((empiricalSampleIndicesInSet sample cell).card : ℝ) / count ≤
        (law : Measure E).real cell / 2} ≤
      Real.exp (-((1 / 2 - Real.exp (-1)) * (count : ℝ) *
        (law : Measure E).real cell)) := by
  have hcount_real_pos : 0 < (count : ℝ) := by
    exact_mod_cast hcount
  have hevent : {sample : Fin count → E |
      ((empiricalSampleIndicesInSet sample cell).card : ℝ) / count ≤
        (law : Measure E).real cell / 2} =
      {sample : Fin count → E |
        ∑ index, cell.indicator (fun _ : E => (1 : ℝ)) (sample index) ≤
        (count : ℝ) * (law : Measure E).real cell / 2} := by
    ext sample
    simp only [Set.mem_setOf_eq]
    rw [← finiteIIDCellFrequency_eq_empiricalSampleIndicesInSet_card_div]
    unfold finiteIIDCellFrequency
    rw [div_le_iff₀ hcount_real_pos]
    ring
  rw [hevent]
  convert measureReal_finiteIIDIndicatorSum_le_exp_chernoff
    (law : Measure E) count cell hcell
      ((count : ℝ) * (law : Measure E).real cell / 2) 1 (by norm_num) using 1 <;> ring

/--
A finite family of measurable cells has a simultaneous upper-deviation bound.
This is the union-bound layer to be applied to the individual levels of a
dyadic partition; no partition or geometric hypothesis is hidden here.

Library provenance: the union step uses the local
`AppliedModelingLib.measureProb_biUnion_finset_le`, whose checked Mathlib basis is
`MeasureTheory.measureReal_biUnion_finset_le` in
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Real.lean>
at the same pinned Apache-2.0 Mathlib commit. No external source text is
copied or ported; the upstream declaration's axiom report has only
`propext`, `Classical.choice`, and `Quot.sound`.
-/
theorem measure_finiteIID_existsCellFrequency_upperTail_le_exp
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece]
    (law : ProbabilityMeasure E) (count : ℕ) (hcount : 0 < count)
    (cell : Piece → Set E) (hcell : ∀ piece, MeasurableSet (cell piece))
    (error : ℝ) (herror : 0 ≤ error) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      ∃ piece : Piece, (law : Measure E).real (cell piece) + error ≤
        finiteIIDCellFrequency count (cell piece) sample} ≤
      (Fintype.card Piece : ℝ) * Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  change measureProb (finiteIIDSampleLaw (law : Measure E) count) (fun sample =>
    ∃ piece : Piece, (law : Measure E).real (cell piece) + error ≤
      finiteIIDCellFrequency count (cell piece) sample) ≤ _
  calc
    _ ≤ ∑ piece ∈ Finset.univ,
        measureProb (finiteIIDSampleLaw (law : Measure E) count) (fun sample =>
          (law : Measure E).real (cell piece) + error ≤
            finiteIIDCellFrequency count (cell piece) sample) :=
      by
        simpa using (measureProb_biUnion_finset_le
          (finiteIIDSampleLaw (law : Measure E) count) Finset.univ (fun piece sample =>
          (law : Measure E).real (cell piece) + error ≤
            finiteIIDCellFrequency count (cell piece) sample))
    _ ≤ ∑ _piece ∈ Finset.univ,
        Real.exp (-((count : ℝ) * error) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
      gcongr with piece _
      exact measure_finiteIIDCellFrequency_upperTail_le_exp law count hcount (cell piece)
        (hcell piece) error herror
    _ = _ := by
      classical
      rw [Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul]

/-- A finite family of measurable cells has a simultaneous lower-deviation bound. -/
theorem measure_finiteIID_existsCellFrequency_lowerTail_le_exp
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece]
    (law : ProbabilityMeasure E) (count : ℕ) (hcount : 0 < count)
    (cell : Piece → Set E) (hcell : ∀ piece, MeasurableSet (cell piece))
    (error : ℝ) (herror : 0 ≤ error) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      ∃ piece : Piece, finiteIIDCellFrequency count (cell piece) sample ≤
        (law : Measure E).real (cell piece) - error} ≤
      (Fintype.card Piece : ℝ) * Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  change measureProb (finiteIIDSampleLaw (law : Measure E) count) (fun sample =>
    ∃ piece : Piece, finiteIIDCellFrequency count (cell piece) sample ≤
      (law : Measure E).real (cell piece) - error) ≤ _
  calc
    _ ≤ ∑ piece ∈ Finset.univ,
        measureProb (finiteIIDSampleLaw (law : Measure E) count) (fun sample =>
          finiteIIDCellFrequency count (cell piece) sample ≤
            (law : Measure E).real (cell piece) - error) :=
      by
        simpa using (measureProb_biUnion_finset_le
          (finiteIIDSampleLaw (law : Measure E) count) Finset.univ (fun piece sample =>
          finiteIIDCellFrequency count (cell piece) sample ≤
            (law : Measure E).real (cell piece) - error))
    _ ≤ ∑ _piece ∈ Finset.univ,
        Real.exp (-((count : ℝ) * error) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
      gcongr with piece _
      exact measure_finiteIIDCellFrequency_lowerTail_le_exp law count hcount (cell piece)
        (hcell piece) error herror
    _ = _ := by
      classical
      rw [Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul]

/--
The simultaneous two-sided empirical-mass deviation event for any finite
measurable family.  A dyadic transport argument will supply the geometric
family and sum this estimate across its scales.
-/
theorem measure_finiteIID_existsCellFrequency_absDeviation_le_exp
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece]
    (law : ProbabilityMeasure E) (count : ℕ) (hcount : 0 < count)
    (cell : Piece → Set E) (hcell : ∀ piece, MeasurableSet (cell piece))
    (error : ℝ) (herror : 0 ≤ error) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      ∃ piece : Piece,
        error ≤ |finiteIIDCellFrequency count (cell piece) sample -
          (law : Measure E).real (cell piece)|} ≤
      2 * (Fintype.card Piece : ℝ) * Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  let upper : Set (Fin count → E) := {sample |
    ∃ piece : Piece, (law : Measure E).real (cell piece) + error ≤
      finiteIIDCellFrequency count (cell piece) sample}
  let lower : Set (Fin count → E) := {sample |
    ∃ piece : Piece, finiteIIDCellFrequency count (cell piece) sample ≤
      (law : Measure E).real (cell piece) - error}
  have hevent : {sample |
      ∃ piece : Piece,
        error ≤ |finiteIIDCellFrequency count (cell piece) sample -
          (law : Measure E).real (cell piece)|} = upper ∪ lower := by
    ext sample
    simp only [upper, lower, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨piece, hpiece⟩
      rcases (le_abs.mp hpiece) with hlow | hupp
      · left
        refine ⟨piece, ?_⟩
        linarith
      · right
        refine ⟨piece, ?_⟩
        linarith
    · intro h
      rcases h with hupper | hlower
      · rcases hupper with ⟨piece, hpiece⟩
        refine ⟨piece, ?_⟩
        rw [abs_of_nonneg]
        · linarith
        · linarith
      · rcases hlower with ⟨piece, hpiece⟩
        refine ⟨piece, ?_⟩
        rw [abs_of_nonpos]
        · linarith
        · linarith
  rw [hevent]
  calc
    _ ≤ (finiteIIDSampleLaw (law : Measure E) count).real upper +
        (finiteIIDSampleLaw (law : Measure E) count).real lower :=
      measureReal_union_le upper lower
    _ ≤ (Fintype.card Piece : ℝ) * Real.exp (-((count : ℝ) * error) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) +
        (Fintype.card Piece : ℝ) * Real.exp (-((count : ℝ) * error) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
      gcongr
      · exact measure_finiteIID_existsCellFrequency_upperTail_le_exp
          law count hcount cell hcell error herror
      · exact measure_finiteIID_existsCellFrequency_lowerTail_le_exp
          law count hcount cell hcell error herror
    _ = _ := by ring

/--
The finite-iid event that the empirical W₁ distance is at least `radius`.
This is a set on the literal product sample space; measurability and its
concentration bound are separate proof obligations.
-/
noncomputable def finiteIIDEmpiricalWassersteinOneFailure
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    (law : ProbabilityMeasure E) (count : ℕ) (hcount : 0 < count) (radius : ℝ≥0∞) :
    Set (Fin count → E) :=
  {sample | radius ≤ empiricalWassersteinOne law hcount sample}

/-- The probability of an empirical-W₁ failure under the canonical finite iid product law. -/
noncomputable def finiteIIDEmpiricalWassersteinOneFailureProbability
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    (law : ProbabilityMeasure E) (count : ℕ) (hcount : 0 < count) (radius : ℝ≥0∞) : ℝ :=
  (finiteIIDSampleLaw (law : Measure E) count).real
    (finiteIIDEmpiricalWassersteinOneFailure law count hcount radius)

/-- Raising the W₁ threshold can only shrink the corresponding failure event. -/
theorem finiteIIDEmpiricalWassersteinOneFailure_antitone
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    (law : ProbabilityMeasure E) (count : ℕ) (hcount : 0 < count)
    {lower upper : ℝ≥0∞} (hthreshold : lower ≤ upper) :
    finiteIIDEmpiricalWassersteinOneFailure law count hcount upper ⊆
      finiteIIDEmpiricalWassersteinOneFailure law count hcount lower := by
  intro sample hsample
  exact le_trans hthreshold hsample

/-- Raising the W₁ threshold can only decrease its finite-iid failure probability. -/
theorem finiteIIDEmpiricalWassersteinOneFailureProbability_antitone
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    (law : ProbabilityMeasure E) (count : ℕ) (hcount : 0 < count)
    {lower upper : ℝ≥0∞} (hthreshold : lower ≤ upper) :
    finiteIIDEmpiricalWassersteinOneFailureProbability law count hcount upper ≤
      finiteIIDEmpiricalWassersteinOneFailureProbability law count hcount lower := by
  letI : ∀ _ : Fin count, IsProbabilityMeasure (law : Measure E) := fun _ => inferInstance
  letI : IsProbabilityMeasure (finiteIIDSampleLaw (law : Measure E) count) := by
    change IsProbabilityMeasure (Measure.pi fun _ : Fin count => (law : Measure E))
    infer_instance
  unfold finiteIIDEmpiricalWassersteinOneFailureProbability
  apply measureReal_mono
  · exact finiteIIDEmpiricalWassersteinOneFailure_antitone law count hcount hthreshold
  · exact measure_ne_top _ _

/-!
## Finite-partition total-variation concentration

The following paper-independent layer improves a union over individual cells
to a sharp finite-partition ℓ₁ tail.  If the cell discrepancies sum to zero,
their ℓ₁ norm is twice the positive-cell discrepancy.  The positive cells form
one of `2^card(Piece)` subsets; applying the already proved one-set Hoeffding
bound and union bounding over those subsets gives
`2^card(Piece) * exp (-count * error^2 / 2)`.

The fiber-sum identities directly reuse Mathlib's
`MeasureTheory.sum_measureReal_preimage_singleton` from
[`Mathlib/MeasureTheory/Measure/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Real.lean)
at pinned Apache-2.0 commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.  No source is copied or
modified.  The probability tail reuses the local checked
`measure_finiteIID_existsCellFrequency_upperTail_le_exp`, whose exact
Mathlib Hoeffding and finite-union provenance is recorded above.
-/

/-- A finite union of measurable locator fibers is measurable. -/
theorem measurableSet_preimage_finset_of_measurable_fibers
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece] [DecidableEq Piece]
    (locate : E → Piece) (hcell : ∀ piece, MeasurableSet {x | locate x = piece})
    (pieces : Finset Piece) : MeasurableSet (locate ⁻¹' (pieces : Set Piece)) := by
  rw [← Finset.set_biUnion_preimage_singleton locate pieces]
  exact MeasurableSet.biUnion pieces.countable_toSet fun piece _ ↦ hcell piece

/-- The masses of all fibers of a finite locator sum to one under a probability law. -/
theorem sum_measureReal_fibers_eq_one
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece]
    (law : ProbabilityMeasure E) (locate : E → Piece)
    (hcell : ∀ piece, MeasurableSet {x | locate x = piece}) :
    (∑ piece : Piece, (law : Measure E).real {x | locate x = piece}) = 1 := by
  classical
  calc
    (∑ piece : Piece, (law : Measure E).real {x | locate x = piece}) =
        (law : Measure E).real
          (locate ⁻¹' (↑(Finset.univ : Finset Piece) : Set Piece)) := by
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
        (sum_measureReal_preimage_singleton (μ := (law : Measure E))
          (f := locate) (Finset.univ : Finset Piece) (fun piece _ ↦ hcell piece))
    _ = 1 := by simp

theorem sum_finiteIIDCellFrequency_fibers_eq_one
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece]
    (count : ℕ) (hcount : 0 < count)
    (locate : E → Piece) (hcell : ∀ piece, MeasurableSet {x | locate x = piece})
    (sample : Fin count → E) :
    (∑ piece : Piece, finiteIIDCellFrequency count {x | locate x = piece} sample) = 1 := by
  classical
  calc
    (∑ piece : Piece, finiteIIDCellFrequency count {x | locate x = piece} sample) =
        ∑ piece : Piece,
          (empiricalSampleProbabilityMeasureOfPos hcount sample : Measure E).real
            {x | locate x = piece} := by
      apply Finset.sum_congr rfl
      intro piece _
      exact (empiricalSampleProbabilityMeasureOfPos_real_cell_eq_finiteIIDCellFrequency
        hcount sample {x | locate x = piece} (hcell piece)).symm
    _ = 1 := sum_measureReal_fibers_eq_one
      (empiricalSampleProbabilityMeasureOfPos hcount sample) locate hcell

theorem measureReal_preimage_finset_eq_sum_fibers
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece] [DecidableEq Piece]
    (law : ProbabilityMeasure E) (locate : E → Piece)
    (hcell : ∀ piece, MeasurableSet {x | locate x = piece})
    (pieces : Finset Piece) :
    (law : Measure E).real (locate ⁻¹' (pieces : Set Piece)) =
      ∑ piece ∈ pieces, (law : Measure E).real {x | locate x = piece} := by
  exact (sum_measureReal_preimage_singleton (μ := (law : Measure E))
    (f := locate) pieces (fun piece _ ↦ hcell piece)).symm

theorem finiteIIDCellFrequency_preimage_finset_eq_sum_fibers
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece] [DecidableEq Piece]
    (count : ℕ) (hcount : 0 < count) (sample : Fin count → E)
    (locate : E → Piece) (hcell : ∀ piece, MeasurableSet {x | locate x = piece})
    (pieces : Finset Piece) :
    finiteIIDCellFrequency count (locate ⁻¹' (pieces : Set Piece)) sample =
      ∑ piece ∈ pieces,
        finiteIIDCellFrequency count {x | locate x = piece} sample := by
  have hunion := measurableSet_preimage_finset_of_measurable_fibers locate hcell pieces
  calc
    finiteIIDCellFrequency count (locate ⁻¹' (pieces : Set Piece)) sample =
        (empiricalSampleProbabilityMeasureOfPos hcount sample : Measure E).real
          (locate ⁻¹' (pieces : Set Piece)) :=
      (empiricalSampleProbabilityMeasureOfPos_real_cell_eq_finiteIIDCellFrequency
        hcount sample _ hunion).symm
    _ = ∑ piece ∈ pieces,
        (empiricalSampleProbabilityMeasureOfPos hcount sample : Measure E).real
          {x | locate x = piece} :=
      measureReal_preimage_finset_eq_sum_fibers
        (empiricalSampleProbabilityMeasureOfPos hcount sample) locate hcell pieces
    _ = ∑ piece ∈ pieces,
        finiteIIDCellFrequency count {x | locate x = piece} sample := by
      apply Finset.sum_congr rfl
      intro piece _
      exact empiricalSampleProbabilityMeasureOfPos_real_cell_eq_finiteIIDCellFrequency
        hcount sample _ (hcell piece)

/--
For a finite real vector of total mass zero, its ℓ₁ norm is twice the sum
of its nonnegative coordinates.
-/
theorem sum_abs_eq_two_mul_sum_filter_nonneg_of_sum_eq_zero
    {Piece : Type*} [Fintype Piece] (delta : Piece → ℝ)
    (hsum : (∑ piece : Piece, delta piece) = 0) :
    (∑ piece : Piece, |delta piece|) =
      2 * ∑ piece ∈ Finset.univ.filter (fun piece ↦ 0 ≤ delta piece), delta piece := by
  classical
  have hpoint : ∀ piece : Piece,
      |delta piece| = 2 * (if 0 ≤ delta piece then delta piece else 0) - delta piece := by
    intro piece
    split_ifs with h
    · rw [abs_of_nonneg h]
      ring
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring
  calc
    (∑ piece : Piece, |delta piece|) =
        ∑ piece : Piece,
          (2 * (if 0 ≤ delta piece then delta piece else 0) - delta piece) := by
      exact Finset.sum_congr rfl fun piece _ ↦ hpoint piece
    _ = 2 * (∑ piece : Piece, if 0 ≤ delta piece then delta piece else 0) -
        ∑ piece : Piece, delta piece := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 2 * ∑ piece ∈ Finset.univ.filter (fun piece ↦ 0 ≤ delta piece),
        delta piece := by
      rw [hsum, sub_zero]
      congr 1
      simp only [Finset.sum_filter]

/--
If the cell-mass ℓ₁ discrepancy exceeds `error`, the union of the cells
with nonnegative discrepancy has an upper deviation of at least `error / 2`.
-/
theorem exists_preimage_upperDeviation_of_partitionL1Deviation
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece]
    (law : ProbabilityMeasure E) (count : ℕ) (hcount : 0 < count)
    (locate : E → Piece) (hcell : ∀ piece, MeasurableSet {x | locate x = piece})
    (sample : Fin count → E) (error : ℝ)
    (herror : error ≤ ∑ piece : Piece,
      |finiteIIDCellFrequency count {x | locate x = piece} sample -
        (law : Measure E).real {x | locate x = piece}|) :
    ∃ pieces : Finset Piece,
      (law : Measure E).real (locate ⁻¹' (pieces : Set Piece)) + error / 2 ≤
        finiteIIDCellFrequency count (locate ⁻¹' (pieces : Set Piece)) sample := by
  classical
  let delta : Piece → ℝ := fun piece ↦
    finiteIIDCellFrequency count {x | locate x = piece} sample -
      (law : Measure E).real {x | locate x = piece}
  let positive : Finset Piece := Finset.univ.filter (fun piece ↦ 0 ≤ delta piece)
  have hfrequency_sum :=
    sum_finiteIIDCellFrequency_fibers_eq_one count hcount locate hcell sample
  have hlaw_sum := sum_measureReal_fibers_eq_one law locate hcell
  have hdelta_sum : (∑ piece : Piece, delta piece) = 0 := by
    unfold delta
    rw [Finset.sum_sub_distrib, hfrequency_sum, hlaw_sum, sub_self]
  have habs := sum_abs_eq_two_mul_sum_filter_nonneg_of_sum_eq_zero delta hdelta_sum
  have hpositive : error / 2 ≤ ∑ piece ∈ positive, delta piece := by
    unfold positive
    change error ≤ ∑ piece : Piece, |delta piece| at herror
    linarith
  refine ⟨positive, ?_⟩
  have hfrequency := finiteIIDCellFrequency_preimage_finset_eq_sum_fibers
    count hcount sample locate hcell positive
  have hlaw := measureReal_preimage_finset_eq_sum_fibers law locate hcell positive
  have hdifference :
      finiteIIDCellFrequency count (locate ⁻¹' (positive : Set Piece)) sample -
          (law : Measure E).real (locate ⁻¹' (positive : Set Piece)) =
        ∑ piece ∈ positive, delta piece := by
    rw [hfrequency, hlaw]
    unfold delta
    rw [Finset.sum_sub_distrib]
  linarith

/--
Finite-partition ℓ₁ concentration in the exact algebraic form inherited
from the one-set Hoeffding bound.  There is one candidate event per subset of
the finite cell type.
-/
theorem measure_finiteIID_partitionL1Deviation_le_exp
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece]
    (law : ProbabilityMeasure E) (count : ℕ) (hcount : 0 < count)
    (locate : E → Piece) (hcell : ∀ piece, MeasurableSet {x | locate x = piece})
    (error : ℝ) (herror : 0 ≤ error) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      error ≤ ∑ piece : Piece,
        |finiteIIDCellFrequency count {x | locate x = piece} sample -
          (law : Measure E).real {x | locate x = piece}|} ≤
      (Fintype.card (Finset Piece) : ℝ) *
        Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  classical
  letI : IsProbabilityMeasure (finiteIIDSampleLaw (law : Measure E) count) := by
    unfold finiteIIDSampleLaw
    infer_instance
  calc
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
        error ≤ ∑ piece : Piece,
          |finiteIIDCellFrequency count {x | locate x = piece} sample -
            (law : Measure E).real {x | locate x = piece}|} ≤
        (finiteIIDSampleLaw (law : Measure E) count).real {sample |
          ∃ pieces : Finset Piece,
            (law : Measure E).real (locate ⁻¹' (pieces : Set Piece)) + error / 2 ≤
              finiteIIDCellFrequency count
                (locate ⁻¹' (pieces : Set Piece)) sample} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro sample hsample
      exact exists_preimage_upperDeviation_of_partitionL1Deviation
        law count hcount locate hcell sample error hsample
    _ ≤ (Fintype.card (Finset Piece) : ℝ) *
        Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
      exact measure_finiteIID_existsCellFrequency_upperTail_le_exp
        law count hcount (fun pieces : Finset Piece ↦ locate ⁻¹' (pieces : Set Piece))
        (fun pieces ↦ measurableSet_preimage_finset_of_measurable_fibers
          locate hcell pieces) (error / 2) (div_nonneg herror (by norm_num))

/--
Simplified finite-partition ℓ₁ tail:
`P[Σ |muHat(cell)-mu(cell)| ≥ error] ≤ 2^K exp(-n error²/2)`,
where `K` is the number of cells.  This is the scale-wise probability input
needed for the dimension-dependent dyadic Wasserstein argument.
-/
theorem measure_finiteIID_partitionL1Deviation_le_twoPow_mul_exp
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece]
    (law : ProbabilityMeasure E) (count : ℕ) (hcount : 0 < count)
    (locate : E → Piece) (hcell : ∀ piece, MeasurableSet {x | locate x = piece})
    (error : ℝ) (herror : 0 ≤ error) :
    (finiteIIDSampleLaw (law : Measure E) count).real {sample |
      error ≤ ∑ piece : Piece,
        |finiteIIDCellFrequency count {x | locate x = piece} sample -
          (law : Measure E).real {x | locate x = piece}|} ≤
      (2 ^ Fintype.card Piece : ℕ) * Real.exp (-((count : ℝ) * error ^ 2) / 2) := by
  have htail := measure_finiteIID_partitionL1Deviation_le_exp
    law count hcount locate hcell error herror
  convert htail using 1
  · simp
    have hcount_real_ne : (count : ℝ) ≠ 0 := by exact_mod_cast hcount.ne'
    field_simp
    ring

/-!
## Compact dyadic empirical Wasserstein concentration

These declarations connect the exact dyadic hierarchy to the finite-partition
ℓ₁ tail.  The final theorem accepts an arbitrary nonnegative threshold at each
level: the deterministic W₁ bound supplies the inclusion, and a finite union
bound supplies the displayed sum of levelwise probabilities.  Optimizing those
thresholds and then adding noncompact shells are deliberately separate proof
boundaries.
-/

/-- The center of the unique level-zero cube. -/
def dyadicCubeBasepoint (dimension : ℕ) : HalfOpenUnitCube dimension :=
  dyadicCubeAnchor dimension 0 (dyadicCubeRoot dimension)

theorem integrable_dist_dyadicCubeBasepoint
    (dimension : ℕ) (law : ProbabilityMeasure (HalfOpenUnitCube dimension)) :
    Integrable (fun x ↦ dist x (dyadicCubeBasepoint dimension)) (law : Measure _) := by
  apply Integrable.of_bound (measurable_id.dist measurable_const).aestronglyMeasurable
    (dyadicCubeRadius dimension 0)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
  unfold dyadicCubeBasepoint
  rw [← dyadicCubeLocate_zero dimension x]
  exact dist_dyadicCubeAnchor_le dimension 0 x

/-- Total empirical/population cell-mass discrepancy at one dyadic level. -/
def dyadicPartitionL1Deviation
    (dimension : ℕ) (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count level : ℕ) (sample : Fin count → HalfOpenUnitCube dimension) : ℝ :=
  ∑ index : dyadicCubeIndex dimension level,
    |finiteIIDCellFrequency count
        {x | dyadicCubeLocate dimension level x = index} sample -
      (law : Measure _).real {x | dyadicCubeLocate dimension level x = index}|

/-- The compact dyadic partition discrepancy is a measurable finite statistic. -/
theorem measurable_dyadicPartitionL1Deviation
    (dimension : ℕ) (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count level : ℕ) :
    Measurable (dyadicPartitionL1Deviation dimension law count level) := by
  unfold dyadicPartitionL1Deviation
  apply Finset.measurable_sum
  intro index _
  exact ((measurable_finiteIIDCellFrequency count
    {x | dyadicCubeLocate dimension level x = index}
    (measurableSet_dyadicCubeCell dimension level index)).sub measurable_const).abs

/-- The upper-tail event for a compact dyadic partition discrepancy is measurable. -/
theorem measurableSet_dyadicPartitionL1Deviation_le
    (dimension : ℕ) (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count level : ℕ) (error : ℝ) :
    MeasurableSet {sample |
      error ≤ dyadicPartitionL1Deviation dimension law count level sample} :=
  measurableSet_le measurable_const
    (measurable_dyadicPartitionL1Deviation dimension law count level)

/--
Samplewise compact-cube W₁ control by the terminal dyadic radius and the
weighted levelwise ℓ₁ cell discrepancies.
-/
theorem empiricalWassersteinOne_le_dyadicMultiscale
    (dimension : ℕ) (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count)
    (sample : Fin count → HalfOpenUnitCube dimension) (depth : ℕ) :
    empiricalWassersteinOne law hcount sample ≤ ENNReal.ofReal
      (2 * dyadicCubeRadius dimension depth +
        ∑ level ∈ Finset.range depth, dyadicCubeStepRadius dimension level *
          dyadicPartitionL1Deviation dimension law count (level + 1) sample) := by
  let empirical := empiricalSampleProbabilityMeasureOfPos hcount sample
  have hempirical : Integrable (fun x ↦ dist x (dyadicCubeBasepoint dimension))
      (empirical : Measure _) := integrable_dist_dyadicCubeBasepoint dimension empirical
  have hlaw := integrable_dist_dyadicCubeBasepoint dimension law
  have htransport := wassersteinOne_le_dyadicCube dimension empirical law
    (dyadicCubeBasepoint dimension) hempirical hlaw depth
  unfold empiricalWassersteinOne
  change ProbabilityCoupling.wassersteinOne empirical law ≤ _
  apply htransport.trans_eq
  congr 3
  funext level
  congr 1
  unfold dyadicPartitionL1Deviation
  apply Finset.sum_congr rfl
  intro index _
  rw [empiricalSampleProbabilityMeasureOfPos_real_cell_eq_finiteIIDCellFrequency
    hcount sample _ (measurableSet_dyadicCubeCell dimension (level + 1) index)]

/-- The sharp finite-partition tail specialized to the `2^(dimension*level)` dyadic cells. -/
theorem measure_dyadicPartitionL1Deviation_le_twoPow_mul_exp
    (dimension : ℕ) (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count) (level : ℕ)
    (error : ℝ) (herror : 0 ≤ error) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      error ≤ dyadicPartitionL1Deviation dimension law count level sample} ≤
      (2 ^ (2 ^ (dimension * level)) : ℕ) *
        Real.exp (-((count : ℝ) * error ^ 2) / 2) := by
  simpa only [dyadicPartitionL1Deviation, card_dyadicCubeIndex] using
    (measure_finiteIID_partitionL1Deviation_le_twoPow_mul_exp
      law count hcount (dyadicCubeLocate dimension level)
      (measurableSet_dyadicCubeCell dimension level) error herror)

/--
The dyadic partition discrepancy of a mapped sample, expressed on the
original sample space.  This lets a compact-cube tail be used without an
unproved measurability claim for the full Wasserstein event.

Library provenance: the pushforward mass equality uses Mathlib's
`Measure.map_apply` from
[`MeasureTheory/Measure/Map.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Map.lean),
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. No source text is copied or
ported.
-/
def mappedDyadicPartitionL1Deviation
    (dimension : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (f : EuclideanSpace ℝ (Fin dimension) → HalfOpenUnitCube dimension)
    (count level : ℕ) (sample : Fin count → EuclideanSpace ℝ (Fin dimension)) : ℝ :=
  ∑ index : dyadicCubeIndex dimension level,
    |finiteIIDCellFrequency count {x | dyadicCubeLocate dimension level (f x) = index} sample -
      (law : Measure _).real {x | dyadicCubeLocate dimension level (f x) = index}|

/--
The ordinary dyadic discrepancy of the pushforward law/sample equals its
original-space mapped form exactly.
-/
theorem dyadicPartitionL1Deviation_map_eq_mapped
    (dimension : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (f : EuclideanSpace ℝ (Fin dimension) → HalfOpenUnitCube dimension)
    (hf : Measurable f)
    (count level : ℕ) (sample : Fin count → EuclideanSpace ℝ (Fin dimension)) :
    dyadicPartitionL1Deviation dimension (law.map hf.aemeasurable) count level (f ∘ sample) =
      mappedDyadicPartitionL1Deviation dimension law f count level sample := by
  unfold dyadicPartitionL1Deviation mappedDyadicPartitionL1Deviation
  apply Finset.sum_congr rfl
  intro index _
  have hfreq : finiteIIDCellFrequency count
      {x | dyadicCubeLocate dimension level x = index} (f ∘ sample) =
      finiteIIDCellFrequency count
        {x | dyadicCubeLocate dimension level (f x) = index} sample := by
    rfl
  rw [hfreq]
  have hmass : ((law.map hf.aemeasurable :
      ProbabilityMeasure (HalfOpenUnitCube dimension)) :
      Measure (HalfOpenUnitCube dimension)).real
        {x | dyadicCubeLocate dimension level x = index} =
      (law : Measure _).real {x | dyadicCubeLocate dimension level (f x) = index} := by
    change (Measure.map f (law : Measure _)).real
        {x | dyadicCubeLocate dimension level x = index} = _
    unfold Measure.real
    rw [Measure.map_apply hf (measurableSet_dyadicCubeCell dimension level index)]
    rfl
  rw [hmass]

/--
The mapped dyadic discrepancy has the same finite-IID partition tail as the
compact pushforward sample. This theorem keeps the event on the original
sample space, where it can be combined with radial clipping events.
-/
theorem measure_finiteIID_mappedDyadicPartitionL1Deviation_le_twoPow_mul_exp
    (dimension : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (f : EuclideanSpace ℝ (Fin dimension) → HalfOpenUnitCube dimension)
    (hf : Measurable f)
    (count : ℕ) (hcount : 0 < count) (level : ℕ)
    (error : ℝ) (herror : 0 ≤ error) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      error ≤ dyadicPartitionL1Deviation dimension (law.map hf.aemeasurable) count level
        (f ∘ sample)} ≤
      (2 ^ (2 ^ (dimension * level)) : ℕ) *
        Real.exp (-((count : ℝ) * error ^ 2) / 2) := by
  let locate : EuclideanSpace ℝ (Fin dimension) → dyadicCubeIndex dimension level :=
    dyadicCubeLocate dimension level ∘ f
  have hcell : ∀ index, MeasurableSet {x | locate x = index} := by
    intro index
    exact (measurableSet_dyadicCubeCell dimension level index).preimage hf
  have htail := measure_finiteIID_partitionL1Deviation_le_twoPow_mul_exp
    law count hcount locate hcell error herror
  convert htail using 1
  · apply congrArg (fun S : Set (Fin count → EuclideanSpace ℝ (Fin dimension)) =>
      (finiteIIDSampleLaw (law : Measure _) count).real S)
    ext sample
    simp only [Set.mem_setOf_eq]
    rw [dyadicPartitionL1Deviation_map_eq_mapped
      dimension law f hf count level sample]
    rfl
  · rw [card_dyadicCubeIndex]

/-- Deterministic W₁ budget obtained by assigning one discrepancy threshold per level. -/
def dyadicMultiscaleThresholdBound
    (dimension depth : ℕ) (threshold : ℕ → ℝ) : ℝ :=
  2 * dyadicCubeRadius dimension depth +
    ∑ level ∈ Finset.range depth,
      dyadicCubeStepRadius dimension level * threshold (level + 1)

/--
Outside the union of the explicit levelwise discrepancy events, the compact
empirical W₁ cost is bounded by the chosen multiscale threshold budget.
-/
theorem empiricalWassersteinOne_le_dyadicMultiscaleThresholdBound_of_forall
    (dimension : ℕ) (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count)
    (sample : Fin count → HalfOpenUnitCube dimension) (depth : ℕ)
    (threshold : ℕ → ℝ)
    (hgood : ∀ level, level ∈ Finset.range depth →
      dyadicPartitionL1Deviation dimension law count (level + 1) sample ≤
        threshold (level + 1)) :
    empiricalWassersteinOne law hcount sample ≤
      ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth threshold) := by
  have hdeterministic := empiricalWassersteinOne_le_dyadicMultiscale
    dimension law count hcount sample depth
  have hrealBound :
      2 * dyadicCubeRadius dimension depth +
          ∑ level ∈ Finset.range depth,
            dyadicCubeStepRadius dimension level *
              dyadicPartitionL1Deviation dimension law count (level + 1) sample ≤
        dyadicMultiscaleThresholdBound dimension depth threshold := by
    unfold dyadicMultiscaleThresholdBound
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro level hlevel
    exact mul_le_mul_of_nonneg_left
      (hgood level hlevel) (dyadicCubeStepRadius_nonneg dimension level)
  exact hdeterministic.trans (ENNReal.ofReal_le_ofReal hrealBound)

/--
On a sample whose observations all lie in the radius-`R` ball, the Euclidean
empirical W₁ error is bounded by the scaled compact dyadic budget plus the
explicit exponential population-tail cost. This is a deterministic statement:
the two event families needed to ensure its hypotheses are kept separate.
-/
theorem empiricalWassersteinOne_le_radialCollapseCompact_add_exponentialTail
    (dimension : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (count : ℕ) (hcount : 0 < count)
    (sample : Fin count → EuclideanSpace ℝ (Fin dimension))
    {alpha gamma radius : ℝ} (halpha : 1 ≤ alpha) (hgamma : 0 < gamma)
    (hradius : 0 < radius) (hmoment : HasExponentialRadialMoment law alpha gamma)
    (depth : ℕ) (threshold : ℕ → ℝ)
    (hinside : ∀ index, ‖sample index‖ ≤ radius)
    (hgood : ∀ level, level ∈ Finset.range depth →
      dyadicPartitionL1Deviation dimension
        (law.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable)
        count (level + 1)
        (euclideanRadialCollapseScale dimension radius hradius ∘ sample) ≤
          threshold (level + 1)) :
    empiricalWassersteinOne law hcount sample ≤
      ((NNReal.mk (2 * radius) (by positivity) : NNReal) : ℝ≥0∞) *
        ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth threshold) +
      ENNReal.ofReal ((1 + (gamma / 2)⁻¹) *
        Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
        ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension)))) := by
  let empirical := empiricalSampleProbabilityMeasureOfPos hcount sample
  have hcollapse_sample : euclideanRadialCollapse dimension radius ∘ sample = sample := by
    funext index
    simp only [Function.comp_apply, euclideanRadialCollapse, if_pos (hinside index)]
  have hcollapse_empirical :
      empirical.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable =
        empirical := by
    rw [map_empiricalSampleProbabilityMeasureOfPos hcount sample
      (euclideanRadialCollapse dimension radius)
      (measurable_euclideanRadialCollapse dimension radius)]
    rw [hcollapse_sample]
  have hcompact := empiricalWassersteinOne_le_dyadicMultiscaleThresholdBound_of_forall
    dimension
    (law.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable)
    count hcount (euclideanRadialCollapseScale dimension radius hradius ∘ sample)
    depth threshold hgood
  have hscaled :
      ProbabilityCoupling.wassersteinOne
        (empirical.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable)
        (law.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable) ≤
        ((NNReal.mk (2 * radius) (by positivity) : NNReal) : ℝ≥0∞) *
          empiricalWassersteinOne
            (law.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable)
            hcount (euclideanRadialCollapseScale dimension radius hradius ∘ sample) := by
    change ProbabilityCoupling.wassersteinOne
        (empirical.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable)
        (law.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable) ≤
        ((NNReal.mk (2 * radius) (by positivity) : NNReal) : ℝ≥0∞) *
          ProbabilityCoupling.wassersteinOne
            (empiricalSampleProbabilityMeasureOfPos hcount
              (euclideanRadialCollapseScale dimension radius hradius ∘ sample))
            (law.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable)
    rw [← map_empiricalSampleProbabilityMeasureOfPos hcount sample
      (euclideanRadialCollapseScale dimension radius hradius)
      (measurable_euclideanRadialCollapseScale dimension radius hradius)]
    exact wassersteinOne_radialCollapse_le_scaleBack_compact dimension radius hradius empirical law
  have htail := wassersteinOne_euclideanRadialCollapse_le_exponentialRadialMoment
    dimension law halpha hgamma hradius.le hmoment
  have htailReverse : ProbabilityCoupling.wassersteinOne
      (law.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable) law ≤
      ENNReal.ofReal ((1 + (gamma / 2)⁻¹) *
        Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
        ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension)))) := by
    rw [← ProbabilityCoupling.wassersteinOne_comm]
    exact htail
  calc
    empiricalWassersteinOne law hcount sample =
        ProbabilityCoupling.wassersteinOne empirical law := rfl
    _ = ProbabilityCoupling.wassersteinOne
        (empirical.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable) law := by
      rw [hcollapse_empirical]
    _ ≤ ProbabilityCoupling.wassersteinOne
          (empirical.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable)
          (law.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable) +
        ProbabilityCoupling.wassersteinOne
          (law.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable) law :=
      ProbabilityCoupling.wassersteinOne_triangle
        (empirical.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable) law
        (law.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable)
    _ ≤ ((NNReal.mk (2 * radius) (by positivity) : NNReal) : ℝ≥0∞) *
          empiricalWassersteinOne
            (law.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable)
            hcount (euclideanRadialCollapseScale dimension radius hradius ∘ sample) +
        ENNReal.ofReal ((1 + (gamma / 2)⁻¹) *
          Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
          ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension)))) :=
      add_le_add hscaled htailReverse
    _ ≤ ((NNReal.mk (2 * radius) (by positivity) : NNReal) : ℝ≥0∞) *
          ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth threshold) +
        ENNReal.ofReal ((1 + (gamma / 2)⁻¹) *
          Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
          ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension)))) := by
      gcongr

/--
Finite-IID noncompact empirical-W₁ concentration with an explicit radial
collapse radius and arbitrary compact dyadic threshold schedule. The first
failure term is the event that some observation lies outside the ball; the
second is the finite sum of compact partition tails. This is a checked
global-truncation reduction, not a claim to reproduce Fournier--Guillin's
sharper annular-shell constants.
-/
def finiteIIDRadialCollapseCompactFailureBudget
    (dimension : ℕ) (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (count : ℕ) (alpha gamma radius : ℝ) (depth : ℕ) (threshold : ℕ → ℝ) : ℝ :=
  count * ∫ x : EuclideanSpace ℝ (Fin dimension),
    Real.exp (gamma * Real.rpow ‖x‖ alpha) /
      Real.exp (gamma * Real.rpow radius alpha) ∂
        (law : Measure (EuclideanSpace ℝ (Fin dimension))) +
    ∑ level ∈ Finset.range depth,
      (2 ^ (2 ^ (dimension * (level + 1))) : ℕ) *
        Real.exp (-((count : ℝ) * threshold (level + 1) ^ 2) / 2)

theorem measure_finiteIID_empiricalWassersteinOne_gt_radialCollapseCompactBound_le
    (dimension : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (count : ℕ) (hcount : 0 < count)
    {alpha gamma radius : ℝ} (halpha : 1 ≤ alpha) (hgamma : 0 < gamma)
    (hradius : 0 < radius) (hmoment : HasExponentialRadialMoment law alpha gamma)
    (depth : ℕ) (threshold : ℕ → ℝ) (hthreshold : ∀ level, 0 ≤ threshold level) :
    (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count).real
      {sample |
        ((NNReal.mk (2 * radius) (by positivity) : NNReal) : ℝ≥0∞) *
          ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth threshold) +
        ENNReal.ofReal ((1 + (gamma / 2)⁻¹) *
          Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
          ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension)))) <
          empiricalWassersteinOne law hcount sample} ≤
      count * ∫ x : EuclideanSpace ℝ (Fin dimension),
        Real.exp (gamma * Real.rpow ‖x‖ alpha) /
          Real.exp (gamma * Real.rpow radius alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension))) +
      ∑ level ∈ Finset.range depth,
        (2 ^ (2 ^ (dimension * (level + 1))) : ℕ) *
          Real.exp (-((count : ℝ) * threshold (level + 1) ^ 2) / 2) := by
  letI : IsProbabilityMeasure
      (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count) := by
    change IsProbabilityMeasure (Measure.pi fun _ : Fin count ↦
      (law : Measure (EuclideanSpace ℝ (Fin dimension))))
    infer_instance
  let compactBad : Set (Fin count → EuclideanSpace ℝ (Fin dimension)) := {sample |
    ∃ level ∈ Finset.range depth,
      threshold (level + 1) ≤ dyadicPartitionL1Deviation dimension
        (law.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable)
        count (level + 1) (euclideanRadialCollapseScale dimension radius hradius ∘ sample)}
  let sampleTail : Set (Fin count → EuclideanSpace ℝ (Fin dimension)) := {sample |
    ∃ index, radius < ‖sample index‖}
  have hfailure_subset : {sample |
      ((NNReal.mk (2 * radius) (by positivity) : NNReal) : ℝ≥0∞) *
        ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth threshold) +
      ENNReal.ofReal ((1 + (gamma / 2)⁻¹) *
        Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
        ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension)))) <
        empiricalWassersteinOne law hcount sample} ⊆ sampleTail ∪ compactBad := by
    intro sample hfailure
    by_contra hnot
    have hinside : ∀ index, ‖sample index‖ ≤ radius := by
      intro index
      by_contra hindex
      apply hnot
      left
      exact ⟨index, lt_of_not_ge hindex⟩
    have hgood : ∀ level, level ∈ Finset.range depth →
        dyadicPartitionL1Deviation dimension
          (law.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable)
          count (level + 1) (euclideanRadialCollapseScale dimension radius hradius ∘ sample) ≤
          threshold (level + 1) := by
      intro level hlevel
      by_contra hlevelBad
      apply hnot
      right
      exact ⟨level, hlevel, (lt_of_not_ge hlevelBad).le⟩
    have hdet := empiricalWassersteinOne_le_radialCollapseCompact_add_exponentialTail
      dimension law count hcount sample halpha hgamma hradius hmoment depth threshold hinside hgood
    exact (not_lt_of_ge hdet) hfailure
  have hsampleTail := measure_finiteIID_exists_norm_gt_le_exponentialRadialMoment_div
    dimension law count (by linarith [halpha]) hgamma.le hradius.le hmoment
  have hcompactBad :
      (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count).real
        compactBad ≤
      ∑ level ∈ Finset.range depth,
        (2 ^ (2 ^ (dimension * (level + 1))) : ℕ) *
          Real.exp (-((count : ℝ) * threshold (level + 1) ^ 2) / 2) := by
    calc
      (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count).real
          compactBad ≤
        ∑ level ∈ Finset.range depth,
          (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count).real
            {sample |
              threshold (level + 1) ≤ dyadicPartitionL1Deviation dimension
                (law.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable)
                count (level + 1)
                (euclideanRadialCollapseScale dimension radius hradius ∘ sample)} := by
          simpa [compactBad, measureProb] using (measureProb_biUnion_finset_le
            (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count)
            (Finset.range depth) (fun level sample =>
              threshold (level + 1) ≤ dyadicPartitionL1Deviation dimension
                (law.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable)
                count (level + 1)
                (euclideanRadialCollapseScale dimension radius hradius ∘ sample)))
      _ ≤ ∑ level ∈ Finset.range depth,
          (2 ^ (2 ^ (dimension * (level + 1))) : ℕ) *
            Real.exp (-((count : ℝ) * threshold (level + 1) ^ 2) / 2) := by
          gcongr with level hlevel
          exact measure_finiteIID_mappedDyadicPartitionL1Deviation_le_twoPow_mul_exp
            dimension law (euclideanRadialCollapseScale dimension radius hradius)
            (measurable_euclideanRadialCollapseScale dimension radius hradius)
            count hcount (level + 1) (threshold (level + 1))
            (hthreshold (level + 1))
  calc
    (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count).real
        {sample |
          ((NNReal.mk (2 * radius) (by positivity) : NNReal) : ℝ≥0∞) *
            ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth threshold) +
          ENNReal.ofReal ((1 + (gamma / 2)⁻¹) *
            Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
            ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
              (law : Measure (EuclideanSpace ℝ (Fin dimension)))) <
            empiricalWassersteinOne law hcount sample} ≤
        (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count).real
          (sampleTail ∪ compactBad) :=
      measureReal_mono hfailure_subset (measure_ne_top _ _)
    _ ≤ (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count).real
          sampleTail +
        (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count).real
          compactBad :=
      measureReal_union_le sampleTail compactBad
    _ ≤ count * ∫ x : EuclideanSpace ℝ (Fin dimension),
          Real.exp (gamma * Real.rpow ‖x‖ alpha) /
            Real.exp (gamma * Real.rpow radius alpha) ∂
              (law : Measure (EuclideanSpace ℝ (Fin dimension))) +
        ∑ level ∈ Finset.range depth,
          (2 ^ (2 ^ (dimension * (level + 1))) : ℕ) *
            Real.exp (-((count : ℝ) * threshold (level + 1) ^ 2) / 2) := by
      apply add_le_add
      · exact hsampleTail
      · exact hcompactBad

/--
Named-budget form of the global radial-collapse concentration theorem. This is
the interface a time-varying confidence schedule must place below its
per-round failure allocation.
-/
theorem measure_finiteIID_empiricalWassersteinOne_gt_radialCollapseCompactBound_le_failureBudget
    (dimension : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (count : ℕ) (hcount : 0 < count)
    {alpha gamma radius : ℝ} (halpha : 1 ≤ alpha) (hgamma : 0 < gamma)
    (hradius : 0 < radius) (hmoment : HasExponentialRadialMoment law alpha gamma)
    (depth : ℕ) (threshold : ℕ → ℝ) (hthreshold : ∀ level, 0 ≤ threshold level) :
    (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count).real
      {sample |
        ((NNReal.mk (2 * radius) (by positivity) : NNReal) : ℝ≥0∞) *
          ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth threshold) +
        ENNReal.ofReal ((1 + (gamma / 2)⁻¹) *
          Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
          ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension)))) <
          empiricalWassersteinOne law hcount sample} ≤
      finiteIIDRadialCollapseCompactFailureBudget dimension law count alpha gamma radius depth threshold := by
  simpa only [finiteIIDRadialCollapseCompactFailureBudget] using
    (measure_finiteIID_empiricalWassersteinOne_gt_radialCollapseCompactBound_le
      dimension law count hcount halpha hgamma hradius hmoment depth threshold hthreshold)

/--
Compact dyadic multiscale concentration with arbitrary nonnegative level
thresholds.  A W₁ violation forces a threshold violation at some retained
level; the conclusion sums the exact levelwise tails.  No asymptotic choice of
depth or thresholds is hidden in this theorem.
-/
theorem measure_empiricalWassersteinOne_gt_dyadicMultiscaleThresholdBound_le
    (dimension : ℕ) (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count) (depth : ℕ)
    (threshold : ℕ → ℝ) (hthreshold : ∀ level, 0 ≤ threshold level) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth threshold) <
        empiricalWassersteinOne law hcount sample} ≤
      ∑ level ∈ Finset.range depth,
        (2 ^ (2 ^ (dimension * (level + 1))) : ℕ) *
          Real.exp (-((count : ℝ) * threshold (level + 1) ^ 2) / 2) := by
  classical
  letI : IsProbabilityMeasure
      (finiteIIDSampleLaw (law : Measure (HalfOpenUnitCube dimension)) count) := by
    change IsProbabilityMeasure
      (Measure.pi fun _ : Fin count ↦ (law : Measure (HalfOpenUnitCube dimension)))
    infer_instance
  calc
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
        ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth threshold) <
          empiricalWassersteinOne law hcount sample} ≤
        (finiteIIDSampleLaw (law : Measure _) count).real {sample |
          ∃ level ∈ Finset.range depth,
            threshold (level + 1) ≤
              dyadicPartitionL1Deviation dimension law count (level + 1) sample} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro sample hsample
      by_contra hnoLevel
      have hnoLevel' : ∀ level, level ∈ Finset.range depth →
          ¬ threshold (level + 1) ≤
            dyadicPartitionL1Deviation dimension law count (level + 1) sample := by
        intro level hlevel hbad
        exact hnoLevel ⟨level, hlevel, hbad⟩
      have hdeterministic :=
        empiricalWassersteinOne_le_dyadicMultiscale
          dimension law count hcount sample depth
      have hrealBound :
          2 * dyadicCubeRadius dimension depth +
              ∑ level ∈ Finset.range depth,
                dyadicCubeStepRadius dimension level *
                  dyadicPartitionL1Deviation dimension law count (level + 1) sample ≤
            dyadicMultiscaleThresholdBound dimension depth threshold := by
        unfold dyadicMultiscaleThresholdBound
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro level hlevel
        exact mul_le_mul_of_nonneg_left
          (lt_of_not_ge (hnoLevel' level hlevel)).le
          (dyadicCubeStepRadius_nonneg dimension level)
      have hENNBound := hdeterministic.trans
        (ENNReal.ofReal_le_ofReal hrealBound)
      exact (not_lt_of_ge hENNBound) hsample
    _ ≤ ∑ level ∈ Finset.range depth,
        (finiteIIDSampleLaw (law : Measure _) count).real {sample |
          threshold (level + 1) ≤
            dyadicPartitionL1Deviation dimension law count (level + 1) sample} := by
      simpa using (measureProb_biUnion_finset_le
        (finiteIIDSampleLaw (law : Measure _) count) (Finset.range depth)
        (fun level sample ↦ threshold (level + 1) ≤
          dyadicPartitionL1Deviation dimension law count (level + 1) sample))
    _ ≤ ∑ level ∈ Finset.range depth,
        (2 ^ (2 ^ (dimension * (level + 1))) : ℕ) *
          Real.exp (-((count : ℝ) * threshold (level + 1) ^ 2) / 2) := by
      gcongr with level hlevel
      exact measure_dyadicPartitionL1Deviation_le_twoPow_mul_exp
        dimension law count hcount (level + 1) (threshold (level + 1))
          (hthreshold (level + 1))

/-!
## A concrete compact confidence schedule

The following schedule pays for the `2^(d * level)` cells at each dyadic
level and a finite-depth union bound.  It is deliberately finite and explicit:
the later dimension-regime theorem will choose the depth and simplify this
displayed budget.

Library provenance: `Real.exp_one_gt_two` is imported directly from Mathlib's
`Mathlib/Analysis/Complex/ExponentialBounds.lean` at pinned Apache-2.0 commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`:
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Complex/ExponentialBounds.lean>.
No source text is copied or ported; the declaration is a direct dependency.
-/

/--
The levelwise compact-cube discrepancy threshold with a confidence budget.
The square-root term is the natural `sqrt((number of cells + confidence) / n)`
scale for the sharp finite-partition ℓ₁ concentration bound.
-/
def dyadicConfidenceThreshold
    (dimension count level : ℕ) (confidence : ℝ) : ℝ :=
  Real.sqrt (4 * ((2 ^ (dimension * level) : ℕ) + confidence + level) / count)

private theorem two_pow_nat_le_exp_nat (n : ℕ) :
    ((2 ^ n : ℕ) : ℝ) ≤ Real.exp (n : ℝ) := by
  rw [Nat.cast_pow]
  calc
    (2 : ℝ) ^ n ≤ (Real.exp 1) ^ n :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_two) n
    _ = Real.exp ((n : ℝ) * 1) := by rw [Real.exp_nat_mul]
    _ = Real.exp (n : ℝ) := by ring_nf

theorem dyadicConfidenceThreshold_nonneg
    (dimension count level : ℕ) (confidence : ℝ) :
    0 ≤ dyadicConfidenceThreshold dimension count level confidence :=
  Real.sqrt_nonneg _

private theorem sqrt_add_le_add_sqrt {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (add_nonneg ha hb), add_sq]
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

private theorem sqrt_add_add_le {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  calc
    Real.sqrt (a + b + c) = Real.sqrt ((a + b) + c) := by ring
    _ ≤ Real.sqrt (a + b) + Real.sqrt c := sqrt_add_le_add_sqrt (add_nonneg ha hb) hc
    _ ≤ (Real.sqrt a + Real.sqrt b) + Real.sqrt c := by
      gcongr
      exact sqrt_add_le_add_sqrt ha hb
    _ = Real.sqrt a + Real.sqrt b + Real.sqrt c := by ring

/--
The confidence threshold separates into its dyadic-cell, confidence, and
level-allocation square-root contributions.  This finite inequality is the
numeric interface used to obtain the dimension-dependent compact rates.
-/
theorem dyadicConfidenceThreshold_le_threeTerm
    (dimension count level : ℕ) (hcount : 0 < count)
    (confidence : ℝ) (hconfidence : 0 ≤ confidence) :
    dyadicConfidenceThreshold dimension count level confidence ≤
      2 * (Real.sqrt ((2 ^ (dimension * level) : ℕ) : ℝ) +
        Real.sqrt confidence + Real.sqrt level) / Real.sqrt count := by
  unfold dyadicConfidenceThreshold
  have hsum : 0 ≤ ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence + level := by positivity
  have hroot : Real.sqrt (((2 ^ (dimension * level) : ℕ) : ℝ) + confidence + level) ≤
      Real.sqrt ((2 ^ (dimension * level) : ℕ) : ℝ) +
        Real.sqrt confidence + Real.sqrt level :=
    sqrt_add_add_le (by positivity) hconfidence (by positivity)
  have hcountRoot_pos : 0 < Real.sqrt (count : ℝ) := by positivity
  change √(4 * (((2 ^ (dimension * level) : ℕ) : ℝ) + confidence + level) /
      (count : ℝ)) ≤ _
  calc
    √(4 * (((2 ^ (dimension * level) : ℕ) : ℝ) + confidence + level) /
        (count : ℝ)) =
        2 * Real.sqrt (((2 ^ (dimension * level) : ℕ) : ℝ) + confidence + level) /
          Real.sqrt count := by
          rw [show 4 * (((2 ^ (dimension * level) : ℕ) : ℝ) + confidence + level) / (count : ℝ) =
                4 * ((((2 ^ (dimension * level) : ℕ) : ℝ) + confidence + level) / (count : ℝ)) by ring]
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_div hsum]
          norm_num
          ring
    _ ≤ 2 * (Real.sqrt ((2 ^ (dimension * level) : ℕ) : ℝ) +
        Real.sqrt confidence + Real.sqrt level) / Real.sqrt count := by
          apply div_le_div_of_nonneg_right ?_ hcountRoot_pos.le
          gcongr

/--
The full finite-depth compact budget after separating every level into the
dyadic-cell, confidence, and level-allocation square-root terms.  This makes
the purely numerical dimension-regime summations explicit and independent of
the empirical-measure event proof.
-/
theorem dyadicMultiscaleConfidenceBound_le_threeTerm
    (dimension count depth : ℕ) (hcount : 0 < count)
    (confidence : ℝ) (hconfidence : 0 ≤ confidence) :
    dyadicMultiscaleThresholdBound dimension depth
      (fun level ↦ dyadicConfidenceThreshold dimension count level confidence) ≤
      2 * dyadicCubeRadius dimension depth +
        ∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius dimension level *
            (2 * (Real.sqrt ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ) +
              Real.sqrt confidence + Real.sqrt (level + 1)) / Real.sqrt count) := by
  unfold dyadicMultiscaleThresholdBound
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro level hlevel
  apply mul_le_mul_of_nonneg_left
    (by simpa [Nat.cast_add] using
      (dyadicConfidenceThreshold_le_threeTerm dimension count (level + 1) hcount
        confidence hconfidence))
    (dyadicCubeStepRadius_nonneg dimension level)

private theorem count_mul_sq_dyadicConfidenceThreshold
    (dimension count level : ℕ) (hcount : 0 < count) (confidence : ℝ)
    (hconfidence : 0 ≤ confidence) :
    (count : ℝ) * (dyadicConfidenceThreshold dimension count level confidence) ^ 2 =
      4 * ((2 ^ (dimension * level) : ℕ) + confidence + level) := by
  unfold dyadicConfidenceThreshold
  have hinside : 0 ≤
      4 * ((2 ^ (dimension * level) : ℕ) + confidence + level) / count := by
    positivity
  rw [Real.sq_sqrt hinside]
  have hcount_ne : (count : ℝ) ≠ 0 := by exact_mod_cast hcount.ne'
  field_simp

private theorem dyadicConfidenceThreshold_numericalTail_le
    (dimension count level : ℕ) (hcount : 0 < count) (confidence : ℝ)
    (hconfidence : 0 ≤ confidence) :
    (2 ^ (2 ^ (dimension * level)) : ℕ) *
        Real.exp (-((count : ℝ) *
          dyadicConfidenceThreshold dimension count level confidence ^ 2) / 2) ≤
      Real.exp (-confidence - level) := by
  have hcountSq := count_mul_sq_dyadicConfidenceThreshold
    dimension count level hcount confidence hconfidence
  have hpow := two_pow_nat_le_exp_nat (2 ^ (dimension * level))
  have hnonneg : 0 ≤ ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence + level := by
    positivity
  rw [hcountSq]
  calc
    (2 ^ (2 ^ (dimension * level)) : ℕ) *
        Real.exp (-(4 * ((2 ^ (dimension * level) : ℕ) + confidence + level)) / 2) =
      ((2 ^ (2 ^ (dimension * level)) : ℕ) : ℝ) *
        Real.exp (-2 * ((2 ^ (dimension * level) : ℕ) + confidence + level)) := by
          congr 1
          ring_nf
    _ ≤ Real.exp ((2 ^ (dimension * level) : ℕ) : ℝ) *
        Real.exp (-2 * ((2 ^ (dimension * level) : ℕ) + confidence + level)) := by
          gcongr
    _ = Real.exp (-((2 ^ (dimension * level) : ℕ) : ℝ) - 2 * confidence - 2 * level) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
    _ ≤ Real.exp (-confidence - level) := by
          apply Real.exp_le_exp.mpr
          nlinarith

/--
At a fixed dyadic level, the explicit confidence threshold controls the
empirical/population partition discrepancy by `exp (-confidence - level)`.
-/
theorem dyadicConfidenceThreshold_tail_le
    (dimension : ℕ) (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count) (level : ℕ)
    (confidence : ℝ) (hconfidence : 0 ≤ confidence) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      dyadicConfidenceThreshold dimension count level confidence ≤
        dyadicPartitionL1Deviation dimension law count level sample} ≤
      Real.exp (-confidence - level) := by
  have htail := measure_dyadicPartitionL1Deviation_le_twoPow_mul_exp
    dimension law count hcount level
    (dyadicConfidenceThreshold dimension count level confidence)
    (dyadicConfidenceThreshold_nonneg dimension count level confidence)
  refine htail.trans ?_
  exact dyadicConfidenceThreshold_numericalTail_le
    dimension count level hcount confidence hconfidence

/--
Finite-depth compact dyadic Wasserstein concentration under the explicit
confidence threshold.  Its right-hand side is a finite union-bound budget;
subsequent dimension-regime results choose `depth` and simplify the threshold
sum without changing this source-independent interface.
-/
theorem measure_empiricalWassersteinOne_gt_dyadicConfidenceThresholdBound_le
    (dimension : ℕ) (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count) (depth : ℕ)
    (confidence : ℝ) (hconfidence : 0 ≤ confidence) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth
        (fun level ↦ dyadicConfidenceThreshold dimension count level confidence)) <
        empiricalWassersteinOne law hcount sample} ≤
      depth * Real.exp (-confidence) := by
  refine (measure_empiricalWassersteinOne_gt_dyadicMultiscaleThresholdBound_le
    dimension law count hcount depth
    (fun level ↦ dyadicConfidenceThreshold dimension count level confidence)
    (fun level ↦ dyadicConfidenceThreshold_nonneg dimension count level confidence)).trans ?_
  calc
    (∑ level ∈ Finset.range depth,
        (2 ^ (2 ^ (dimension * (level + 1))) : ℕ) *
          Real.exp (-((count : ℝ) *
            dyadicConfidenceThreshold dimension count (level + 1) confidence ^ 2) / 2)) ≤
        ∑ level ∈ Finset.range depth,
          Real.exp (-confidence - (level + 1)) := by
            gcongr with level hlevel
            simpa [Nat.cast_add] using
              (dyadicConfidenceThreshold_numericalTail_le dimension count
                (level + 1) hcount confidence hconfidence)
    _ ≤ ∑ _level ∈ Finset.range depth, Real.exp (-confidence) := by
            gcongr with level hlevel
            have hlevel_nonneg : (0 : ℝ) ≤ level := Nat.cast_nonneg _
            linarith
    _ = depth * Real.exp (-confidence) := by
            simp [nsmul_eq_mul]

/--
Choosing the confidence parameter as `log (depth / failure)` turns the
finite-depth compact bound into a prescribed failure budget.  The restriction
`failure ≤ 1` matches the high-probability use in time-varying empirical-W₁
arguments and guarantees the logarithm is nonnegative.
-/
theorem measure_empiricalWassersteinOne_gt_dyadicConfidenceThresholdBound_le_failure
    (dimension : ℕ) (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count) (depth : ℕ) (hdepth : 0 < depth)
    (failure : ℝ) (hfailure : 0 < failure) (hfailure_le_one : failure ≤ 1) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth
        (fun level ↦ dyadicConfidenceThreshold dimension count level
          (Real.log ((depth : ℝ) / failure)))) <
        empiricalWassersteinOne law hcount sample} ≤ failure := by
  have hratio : 0 < (depth : ℝ) / failure := by positivity
  have hconfidence : 0 ≤ Real.log ((depth : ℝ) / failure) := by
    apply Real.log_nonneg
    apply (one_le_div hfailure).mpr
    exact hfailure_le_one.trans (by exact_mod_cast Nat.succ_le_iff.mpr hdepth)
  refine (measure_empiricalWassersteinOne_gt_dyadicConfidenceThresholdBound_le
    dimension law count hcount depth (Real.log ((depth : ℝ) / failure))
    hconfidence).trans ?_
  rw [Real.exp_neg, Real.exp_log hratio]
  field_simp
  norm_num

/--
An alternative levelwise threshold that allocates a geometric failure budget
to the dyadic scales.  Its extra cell-count term removes the finite-depth
factor from the aggregate concentration tail while preserving the natural
square-root cell-count scale.
-/
def dyadicGeometricConfidenceThreshold
    (dimension count level : ℕ) (confidence : ℝ) : ℝ :=
  Real.sqrt (4 * (2 * (2 ^ (dimension * level) : ℕ) + confidence) / count)

theorem dyadicGeometricConfidenceThreshold_nonneg
    (dimension count level : ℕ) (confidence : ℝ) :
    0 ≤ dyadicGeometricConfidenceThreshold dimension count level confidence :=
  Real.sqrt_nonneg _

/--
The geometric confidence threshold separates into the cell-count and
confidence square-root contributions.  It is the numeric entry point for the
subcritical, critical, and supercritical dyadic sums.
-/
theorem dyadicGeometricConfidenceThreshold_le_twoTerm
    (dimension count level : ℕ) (hcount : 0 < count)
    (confidence : ℝ) (hconfidence : 0 ≤ confidence) :
    dyadicGeometricConfidenceThreshold dimension count level confidence ≤
      2 * (Real.sqrt (2 * ((2 ^ (dimension * level) : ℕ) : ℝ)) +
        Real.sqrt confidence) / Real.sqrt count := by
  unfold dyadicGeometricConfidenceThreshold
  have hsum : 0 ≤ 2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence := by positivity
  have hroot : Real.sqrt (2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence) ≤
      Real.sqrt (2 * ((2 ^ (dimension * level) : ℕ) : ℝ)) +
        Real.sqrt confidence :=
    sqrt_add_le_add_sqrt (by positivity) hconfidence
  have hcountRoot_pos : 0 < Real.sqrt (count : ℝ) := by positivity
  change √(4 * (2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence) /
      (count : ℝ)) ≤ _
  calc
    √(4 * (2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence) /
        (count : ℝ)) =
        2 * Real.sqrt (2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence) /
          Real.sqrt count := by
          rw [show 4 * (2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence) / (count : ℝ) =
                4 * ((2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence) / (count : ℝ)) by ring]
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_div hsum]
          norm_num
          ring
    _ ≤ 2 * (Real.sqrt (2 * ((2 ^ (dimension * level) : ℕ) : ℝ)) +
        Real.sqrt confidence) / Real.sqrt count := by
          apply div_le_div_of_nonneg_right ?_ hcountRoot_pos.le
          gcongr

/--
The same geometric dyadic threshold parameterized by a positive real
effective sample size.  Conditional shell concentration naturally supplies
`N * μ(B)` rather than an integer selected count; keeping that quantity real
allows the deterministic compact schedule to be shared without rounding it.
-/
def dyadicGeometricConfidenceThresholdReal
    (dimension level : ℕ) (effectiveCount confidence : ℝ) : ℝ :=
  Real.sqrt (4 * (2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence) /
    effectiveCount)

theorem dyadicGeometricConfidenceThresholdReal_nonneg
    (dimension level : ℕ) (effectiveCount confidence : ℝ) :
    0 ≤ dyadicGeometricConfidenceThresholdReal dimension level effectiveCount confidence :=
  Real.sqrt_nonneg _

/--
The real-effective-count threshold has the same cell and confidence
decomposition as the integer compact schedule.  It is a deterministic lemma;
the shell module separately proves the conditional probability bound that
licenses its use for an expected selected count.
-/
theorem dyadicGeometricConfidenceThresholdReal_le_twoTerm
    (dimension level : ℕ) {effectiveCount confidence : ℝ}
    (heffectiveCount : 0 < effectiveCount) (hconfidence : 0 ≤ confidence) :
    dyadicGeometricConfidenceThresholdReal dimension level effectiveCount confidence ≤
      2 * (Real.sqrt (2 * ((2 ^ (dimension * level) : ℕ) : ℝ)) +
        Real.sqrt confidence) / Real.sqrt effectiveCount := by
  unfold dyadicGeometricConfidenceThresholdReal
  have hsum : 0 ≤ 2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence := by positivity
  have hroot : Real.sqrt (2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence) ≤
      Real.sqrt (2 * ((2 ^ (dimension * level) : ℕ) : ℝ)) +
        Real.sqrt confidence :=
    sqrt_add_le_add_sqrt (by positivity) hconfidence
  have heffectiveCountRoot_pos : 0 < Real.sqrt effectiveCount :=
    Real.sqrt_pos.mpr heffectiveCount
  calc
    √(4 * (2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence) /
        effectiveCount) =
        2 * Real.sqrt (2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence) /
          Real.sqrt effectiveCount := by
          rw [show 4 * (2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence) /
                effectiveCount =
              4 * ((2 * ((2 ^ (dimension * level) : ℕ) : ℝ) + confidence) /
                effectiveCount) by ring]
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_div hsum]
          norm_num
          ring
    _ ≤ 2 * (Real.sqrt (2 * ((2 ^ (dimension * level) : ℕ) : ℝ)) +
        Real.sqrt confidence) / Real.sqrt effectiveCount := by
          apply div_le_div_of_nonneg_right ?_ heffectiveCountRoot_pos.le
          gcongr

/--
The deterministic multiscale compact budget for a positive real effective
sample size.  This is the common numerical interface between fixed-count
compact concentration and source-shell conditional concentration.
-/
theorem dyadicMultiscaleGeometricConfidenceBoundReal_le_twoTerm
    (dimension depth : ℕ) {effectiveCount confidence : ℝ}
    (heffectiveCount : 0 < effectiveCount) (hconfidence : 0 ≤ confidence) :
    dyadicMultiscaleThresholdBound dimension depth
      (fun level ↦ dyadicGeometricConfidenceThresholdReal
        dimension level effectiveCount confidence) ≤
      2 * dyadicCubeRadius dimension depth +
        ∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius dimension level *
            (2 * (Real.sqrt (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt effectiveCount) := by
  unfold dyadicMultiscaleThresholdBound
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro level hlevel
  apply mul_le_mul_of_nonneg_left
    (by simpa [Nat.cast_add] using
      (dyadicGeometricConfidenceThresholdReal_le_twoTerm dimension (level + 1)
        heffectiveCount hconfidence))
    (dyadicCubeStepRadius_nonneg dimension level)

/--
The deterministic finite-depth budget corresponding to the geometric
confidence schedule, with its two numerical components exposed explicitly.
-/
theorem dyadicMultiscaleGeometricConfidenceBound_le_twoTerm
    (dimension count depth : ℕ) (hcount : 0 < count)
    (confidence : ℝ) (hconfidence : 0 ≤ confidence) :
    dyadicMultiscaleThresholdBound dimension depth
      (fun level ↦ dyadicGeometricConfidenceThreshold dimension count level confidence) ≤
      2 * dyadicCubeRadius dimension depth +
        ∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius dimension level *
            (2 * (Real.sqrt (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt count) := by
  unfold dyadicMultiscaleThresholdBound
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro level hlevel
  apply mul_le_mul_of_nonneg_left
    (by simpa [Nat.cast_add] using
      (dyadicGeometricConfidenceThreshold_le_twoTerm dimension count (level + 1) hcount
        confidence hconfidence))
    (dyadicCubeStepRadius_nonneg dimension level)

private theorem count_mul_sq_dyadicGeometricConfidenceThreshold
    (dimension count level : ℕ) (hcount : 0 < count) (confidence : ℝ)
    (hconfidence : 0 ≤ confidence) :
    (count : ℝ) * (dyadicGeometricConfidenceThreshold dimension count level confidence) ^ 2 =
      4 * (2 * (2 ^ (dimension * level) : ℕ) + confidence) := by
  unfold dyadicGeometricConfidenceThreshold
  have hinside : 0 ≤ 4 * (2 * (2 ^ (dimension * level) : ℕ) + confidence) / count := by
    positivity
  rw [Real.sq_sqrt hinside]
  have hcount_ne : (count : ℝ) ≠ 0 := by exact_mod_cast hcount.ne'
  field_simp

private theorem nat_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.pow_succ]
      calc
        n + 1 + 1 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ n * 2 := by ring

private theorem level_succ_le_dyadicCellCount
    (dimension level : ℕ) (hdimension : 0 < dimension) :
    level + 1 ≤ 2 ^ (dimension * level) := by
  calc
    level + 1 ≤ 2 ^ level := nat_succ_le_two_pow level
    _ ≤ 2 ^ (dimension * level) := by
      apply Nat.pow_le_pow_right (by omega : 0 < 2)
      calc
        level ≤ dimension * level := Nat.le_mul_of_pos_left level hdimension
        _ = dimension * level := rfl

private theorem exp_neg_nat_le_half_pow_nat (n : ℕ) :
    Real.exp (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ n := by
  rw [Real.exp_neg]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
  rw [inv_pow]
  apply (inv_le_inv₀ (a := Real.exp (n : ℝ)) (b := (2 : ℝ) ^ n)
    (Real.exp_pos _) (by positivity)).mpr
  simpa [Nat.cast_pow] using two_pow_nat_le_exp_nat n

private theorem dyadicGeometricConfidenceThreshold_numericalTail_le
    (dimension count level : ℕ) (hdimension : 0 < dimension) (hcount : 0 < count)
    (confidence : ℝ) (hconfidence : 0 ≤ confidence) :
    (2 ^ (2 ^ (dimension * level)) : ℕ) *
        Real.exp (-((count : ℝ) *
          dyadicGeometricConfidenceThreshold dimension count level confidence ^ 2) / 2) ≤
      Real.exp (-confidence) * (1 / 2 : ℝ) ^ (level + 1) := by
  have hcountSq := count_mul_sq_dyadicGeometricConfidenceThreshold
    dimension count level hcount confidence hconfidence
  have hpow := two_pow_nat_le_exp_nat (2 ^ (dimension * level))
  have hKnonneg : 0 ≤ ((2 ^ (dimension * level) : ℕ) : ℝ) := by positivity
  rw [hcountSq]
  calc
    (2 ^ (2 ^ (dimension * level)) : ℕ) *
        Real.exp (-(4 * (2 * (2 ^ (dimension * level) : ℕ) + confidence)) / 2) =
      ((2 ^ (2 ^ (dimension * level)) : ℕ) : ℝ) *
        Real.exp (-4 * ((2 ^ (dimension * level) : ℕ) + confidence / 2)) := by
          congr 1
          ring_nf
    _ ≤ Real.exp ((2 ^ (dimension * level) : ℕ) : ℝ) *
        Real.exp (-4 * ((2 ^ (dimension * level) : ℕ) + confidence / 2)) := by
          gcongr
    _ = Real.exp (-3 * ((2 ^ (dimension * level) : ℕ) : ℝ) - 2 * confidence) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
    _ ≤ Real.exp (-confidence - ((2 ^ (dimension * level) : ℕ) : ℝ)) := by
          apply Real.exp_le_exp.mpr
          nlinarith
    _ = Real.exp (-confidence) *
        Real.exp (-((2 ^ (dimension * level) : ℕ) : ℝ)) := by
          rw [← Real.exp_add]
          ring_nf
    _ ≤ Real.exp (-confidence) * (1 / 2 : ℝ) ^ (2 ^ (dimension * level)) := by
          gcongr
          exact exp_neg_nat_le_half_pow_nat (2 ^ (dimension * level))
    _ ≤ Real.exp (-confidence) * (1 / 2 : ℝ) ^ (level + 1) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
          exact level_succ_le_dyadicCellCount dimension level hdimension

private theorem sum_range_half_pow_succ_le_one (depth : ℕ) :
    (∑ level ∈ Finset.range depth, (1 / 2 : ℝ) ^ (level + 1)) ≤ 1 := by
  have hformula : ∀ n : ℕ,
      (∑ level ∈ Finset.range n, (1 / 2 : ℝ) ^ (level + 1)) =
        1 - (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
  rw [hformula]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) depth]

private theorem two_pow_two_mul_eq_sq_two_pow (k : ℕ) :
    ((2 ^ (2 * k) : ℕ) : ℝ) = ((2 ^ k : ℕ) : ℝ) ^ 2 := by
  rw [show 2 * k = k * 2 by ring, pow_mul, Nat.cast_pow]

private theorem sqrt_two_mul_two_pow_two_mul (k : ℕ) :
    Real.sqrt (2 * ((2 ^ (2 * k) : ℕ) : ℝ)) =
      Real.sqrt 2 * ((2 ^ k : ℕ) : ℝ) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity), two_pow_two_mul_eq_sq_two_pow,
    mul_pow, Real.sq_sqrt (by norm_num)]

private theorem dyadicStepRadius_two_eq (level : ℕ) :
    dyadicCubeStepRadius 2 level = Real.sqrt 2 / ((2 ^ (level + 1) : ℕ) : ℝ) := by
  rfl

private theorem dyadicRadius_two_eq (depth : ℕ) :
    dyadicCubeRadius 2 depth = Real.sqrt 2 / ((2 ^ depth : ℕ) : ℝ) := by
  rfl

private theorem dyadicDimensionTwo_mainTerm_eq (level count : ℕ) (hcount : 0 < count) :
    dyadicCubeStepRadius 2 level *
      (2 * Real.sqrt (2 * ((2 ^ (2 * (level + 1)) : ℕ) : ℝ)) /
        Real.sqrt count) = 4 / Real.sqrt count := by
  rw [dyadicStepRadius_two_eq, sqrt_two_mul_two_pow_two_mul]
  have hpow : ((2 ^ (level + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring

private theorem dyadicDimensionTwo_confidenceTerm_eq (level count : ℕ) (hcount : 0 < count)
    (confidence : ℝ) :
    dyadicCubeStepRadius 2 level *
      (2 * Real.sqrt confidence / Real.sqrt count) =
      (2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt count) *
        (1 / 2 : ℝ) ^ (level + 1) := by
  rw [dyadicStepRadius_two_eq, one_div_pow]
  have hpow : ((2 ^ (level + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  rw [Nat.cast_pow]
  ring

/--
The critical `dimension = 2` deterministic compact budget.  The main
cell-count component contributes exactly one `4 / sqrt(count)` term per
retained scale, producing the source's logarithmic critical behavior after a
depth is chosen.
-/
theorem dyadicDimensionTwoGeometricConfidenceBound_le
    (count depth : ℕ) (hcount : 0 < count)
    (confidence : ℝ) (hconfidence : 0 ≤ confidence) :
    dyadicMultiscaleThresholdBound 2 depth
      (fun level ↦ dyadicGeometricConfidenceThreshold 2 count level confidence) ≤
      2 * Real.sqrt 2 / ((2 ^ depth : ℕ) : ℝ) +
        4 * depth / Real.sqrt count +
        2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt count := by
  refine (dyadicMultiscaleGeometricConfidenceBound_le_twoTerm
    2 count depth hcount confidence hconfidence).trans ?_
  rw [dyadicRadius_two_eq]
  have hsum :
      (∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius 2 level *
            (2 * (Real.sqrt (2 * ((2 ^ (2 * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt count)) ≤
        4 * depth / Real.sqrt count +
          2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt count := by
    calc
      (∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius 2 level *
            (2 * (Real.sqrt (2 * ((2 ^ (2 * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt count)) =
          ∑ level ∈ Finset.range depth,
            (4 / Real.sqrt count +
              (2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt count) *
                (1 / 2 : ℝ) ^ (level + 1)) := by
            apply Finset.sum_congr rfl
            intro level hlevel
            rw [show 2 *
                (Real.sqrt (2 * ((2 ^ (2 * (level + 1)) : ℕ) : ℝ)) +
                  Real.sqrt confidence) / Real.sqrt count =
                2 * Real.sqrt (2 * ((2 ^ (2 * (level + 1)) : ℕ) : ℝ)) /
                  Real.sqrt count +
                2 * Real.sqrt confidence / Real.sqrt count by ring]
            rw [mul_add, dyadicDimensionTwo_mainTerm_eq level count hcount,
              dyadicDimensionTwo_confidenceTerm_eq level count hcount confidence]
      _ = 4 * depth / Real.sqrt count +
          (2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt count) *
            ∑ level ∈ Finset.range depth, (1 / 2 : ℝ) ^ (level + 1) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            simp [nsmul_eq_mul]
            ring
      _ ≤ 4 * depth / Real.sqrt count +
          2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt count := by
            simpa using add_le_add_left
              (mul_le_mul_of_nonneg_left (sum_range_half_pow_succ_le_one depth) (by positivity))
              (4 * depth / Real.sqrt count)
  convert add_le_add_left hsum (2 * Real.sqrt 2 / ((2 ^ depth : ℕ) : ℝ)) using 1 <;> ring

private theorem sqrt_two_pow_eq_sqrt_two_pow (n : ℕ) :
    Real.sqrt ((2 ^ n : ℕ) : ℝ) = (Real.sqrt 2) ^ n := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  calc
    ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by norm_num [Nat.cast_pow]
    _ = ((Real.sqrt 2) ^ 2) ^ n := by rw [Real.sq_sqrt (by norm_num)]
    _ = (Real.sqrt 2) ^ (2 * n) := by rw [← pow_mul]
    _ = (Real.sqrt 2) ^ (n * 2) := by rw [Nat.mul_comm]
    _ = ((Real.sqrt 2) ^ n) ^ 2 := pow_mul _ n 2

private theorem dyadicStepRadius_one_eq (level : ℕ) :
    dyadicCubeStepRadius 1 level = 1 / ((2 ^ (level + 1) : ℕ) : ℝ) := by
  unfold dyadicCubeStepRadius
  norm_num

private theorem dyadicRadius_one_eq (depth : ℕ) :
    dyadicCubeRadius 1 depth = 1 / ((2 ^ depth : ℕ) : ℕ) := by
  unfold dyadicCubeRadius
  norm_num

private theorem dyadicDimensionOne_mainTerm_eq (level count : ℕ) (hcount : 0 < count) :
    dyadicCubeStepRadius 1 level *
      (2 * Real.sqrt (2 * ((2 ^ (1 * (level + 1)) : ℕ) : ℝ)) /
        Real.sqrt count) =
      2 / Real.sqrt count * (1 / Real.sqrt 2 : ℝ) ^ level := by
  rw [dyadicStepRadius_one_eq]
  rw [show 1 * (level + 1) = level + 1 by ring]
  have htwo : 2 * ((2 ^ (level + 1) : ℕ) : ℝ) =
      ((2 ^ (level + 1 + 1) : ℕ) : ℝ) := by
    calc
      2 * ((2 ^ (level + 1) : ℕ) : ℝ) =
          (2 : ℝ) * (2 : ℝ) ^ (level + 1) := by norm_num [Nat.cast_pow]
      _ = (2 : ℝ) ^ (level + 1 + 1) := by rw [pow_succ]; ring
      _ = ((2 ^ (level + 1 + 1) : ℕ) : ℝ) := by norm_num [Nat.cast_pow]
  rw [htwo]
  rw [sqrt_two_pow_eq_sqrt_two_pow]
  have hpow : ((2 ^ (level + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  rw [show (Real.sqrt 2) ^ (level + 1 + 1) = (Real.sqrt 2) ^ level * 2 by
    rw [show level + 1 + 1 = level + 2 by omega, pow_add, Real.sq_sqrt (by norm_num)]]
  have hsqrt2ne : Real.sqrt 2 ≠ 0 := by positivity
  have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [show (1 / Real.sqrt 2 : ℝ) ^ level =
      (Real.sqrt 2) ^ level / (2 : ℝ) ^ level by
    rw [one_div, hinv, div_pow]]
  field_simp
  rw [Nat.cast_pow, pow_succ]
  ring

private theorem sum_range_inv_sqrt_two_pow_le (depth : ℕ) :
    (∑ level ∈ Finset.range depth, (1 / Real.sqrt 2 : ℝ) ^ level) ≤
      1 / (1 - 1 / Real.sqrt 2) := by
  have hsqrt2_gt : 1 < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)
  have hr_lt_one : (1 / Real.sqrt 2 : ℝ) < 1 := by
    exact (div_lt_one₀ (by positivity)).mpr hsqrt2_gt
  have hden_pos : 0 < 1 - 1 / Real.sqrt 2 := by linarith
  apply (le_div_iff₀ hden_pos).mpr
  calc
    (∑ level ∈ Finset.range depth, (1 / Real.sqrt 2 : ℝ) ^ level) *
        (1 - 1 / Real.sqrt 2) =
        1 - (1 / Real.sqrt 2 : ℝ) ^ depth :=
          geom_sum_mul_of_le_one hr_lt_one.le depth
    _ ≤ 1 := by nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 2) depth]

private theorem dyadicDimensionOne_confidenceTerm_eq (level count : ℕ) (hcount : 0 < count)
    (confidence : ℝ) :
    dyadicCubeStepRadius 1 level *
      (2 * Real.sqrt confidence / Real.sqrt count) =
      (2 * Real.sqrt confidence / Real.sqrt count) *
        (1 / 2 : ℝ) ^ (level + 1) := by
  rw [dyadicStepRadius_one_eq, one_div_pow]
  have hpow : ((2 ^ (level + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  rw [Nat.cast_pow]
  ring

/--
The subcritical `dimension = 1` deterministic compact budget.  The principal
cell-count terms form a convergent geometric series, yielding the
`count^(-1/2)` rate before the terminal dyadic radius is balanced against it.
-/
theorem dyadicDimensionOneGeometricConfidenceBound_le
    (count depth : ℕ) (hcount : 0 < count)
    (confidence : ℝ) (hconfidence : 0 ≤ confidence) :
    dyadicMultiscaleThresholdBound 1 depth
      (fun level ↦ dyadicGeometricConfidenceThreshold 1 count level confidence) ≤
      2 / ((2 ^ depth : ℕ) : ℝ) +
        (2 / Real.sqrt count) * (1 / (1 - 1 / Real.sqrt 2)) +
        2 * Real.sqrt confidence / Real.sqrt count := by
  refine (dyadicMultiscaleGeometricConfidenceBound_le_twoTerm
    1 count depth hcount confidence hconfidence).trans ?_
  rw [dyadicRadius_one_eq]
  have hsum :
      (∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius 1 level *
            (2 * (Real.sqrt (2 * ((2 ^ (1 * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt count)) ≤
        (2 / Real.sqrt count) * (1 / (1 - 1 / Real.sqrt 2)) +
          2 * Real.sqrt confidence / Real.sqrt count := by
    calc
      (∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius 1 level *
            (2 * (Real.sqrt (2 * ((2 ^ (1 * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt count)) =
          ∑ level ∈ Finset.range depth,
            (2 / Real.sqrt count * (1 / Real.sqrt 2 : ℝ) ^ level +
              (2 * Real.sqrt confidence / Real.sqrt count) *
                (1 / 2 : ℝ) ^ (level + 1)) := by
            apply Finset.sum_congr rfl
            intro level hlevel
            rw [show 2 *
                (Real.sqrt (2 * ((2 ^ (1 * (level + 1)) : ℕ) : ℝ)) +
                  Real.sqrt confidence) / Real.sqrt count =
                2 * Real.sqrt (2 * ((2 ^ (1 * (level + 1)) : ℕ) : ℝ)) /
                  Real.sqrt count +
                2 * Real.sqrt confidence / Real.sqrt count by ring]
            rw [mul_add, dyadicDimensionOne_mainTerm_eq level count hcount,
              dyadicDimensionOne_confidenceTerm_eq level count hcount confidence]
      _ = (2 / Real.sqrt count) *
          ∑ level ∈ Finset.range depth, (1 / Real.sqrt 2 : ℝ) ^ level +
          (2 * Real.sqrt confidence / Real.sqrt count) *
            ∑ level ∈ Finset.range depth, (1 / 2 : ℝ) ^ (level + 1) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [Finset.mul_sum]
            · rw [Finset.mul_sum]
      _ ≤ (2 / Real.sqrt count) * (1 / (1 - 1 / Real.sqrt 2)) +
          2 * Real.sqrt confidence / Real.sqrt count := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left (sum_range_inv_sqrt_two_pow_le depth) (by positivity)
            · simpa using mul_le_mul_of_nonneg_left
                (sum_range_half_pow_succ_le_one depth) (by positivity)
  convert add_le_add_left hsum (2 / ((2 ^ depth : ℕ) : ℝ)) using 1 <;> ring

private theorem sqrt_pow_eq_pow_sqrt {base : ℝ} (hbase : 0 ≤ base) (exponent : ℕ) :
    Real.sqrt (base ^ exponent) = (Real.sqrt base) ^ exponent := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (pow_nonneg hbase _)]
  calc
    base ^ exponent = ((Real.sqrt base) ^ 2) ^ exponent := by
      rw [Real.sq_sqrt hbase]
    _ = (Real.sqrt base) ^ (2 * exponent) := by rw [← pow_mul]
    _ = (Real.sqrt base) ^ (exponent * 2) := by rw [Nat.mul_comm]
    _ = ((Real.sqrt base) ^ exponent) ^ 2 := pow_mul _ exponent 2

private theorem sqrt_two_mul_dyadicCellCount_eq
    (dimension level : ℕ) :
    Real.sqrt (2 * ((2 ^ (dimension * level) : ℕ) : ℝ)) =
      Real.sqrt 2 * (Real.sqrt ((2 ^ dimension : ℕ) : ℝ)) ^ level := by
  rw [show (2 ^ (dimension * level) : ℕ) = (2 ^ dimension) ^ level by
    rw [pow_mul]]
  rw [Nat.cast_pow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    sqrt_pow_eq_pow_sqrt (by positivity)]

private theorem dyadicSupercritical_mainTerm_eq (dimension level count : ℕ) (hcount : 0 < count) :
    dyadicCubeStepRadius dimension level *
      (2 * Real.sqrt (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ)) /
        Real.sqrt count) =
      (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
        (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (level + 1) := by
  unfold dyadicCubeStepRadius
  rw [sqrt_two_mul_dyadicCellCount_eq]
  rw [div_pow]
  have hpow : ((2 ^ (level + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  rw [Nat.cast_pow]
  ring

private theorem sum_range_pow_succ_le_geometric
    (ratio : ℝ) (hratio : 1 < ratio) (depth : ℕ) :
    (∑ level ∈ Finset.range depth, ratio ^ (level + 1)) ≤
      ratio ^ (depth + 1) / (ratio - 1) := by
  have hden : 0 < ratio - 1 := by linarith
  apply (le_div_iff₀ hden).mpr
  have hgeom := geom_sum_mul_of_one_le (le_of_lt hratio) depth
  have hsum : (∑ level ∈ Finset.range depth, ratio ^ (level + 1)) =
      ratio * ∑ level ∈ Finset.range depth, ratio ^ level := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro level hlevel
    rw [pow_succ]
    ring
  calc
    (∑ level ∈ Finset.range depth, ratio ^ (level + 1)) * (ratio - 1) =
        ratio * ((∑ level ∈ Finset.range depth, ratio ^ level) * (ratio - 1)) := by
          rw [hsum]
          ring
    _ = ratio * (ratio ^ depth - 1) := by rw [hgeom]
    _ ≤ ratio * ratio ^ depth := by nlinarith [le_of_lt hratio]
    _ = ratio ^ (depth + 1) := by rw [pow_succ]; ring

private theorem dyadicSupercritical_confidenceTerm_eq (dimension level count : ℕ) (hcount : 0 < count)
    (confidence : ℝ) :
    dyadicCubeStepRadius dimension level *
      (2 * Real.sqrt confidence / Real.sqrt count) =
      (2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt count) *
        (1 / 2 : ℝ) ^ (level + 1) := by
  unfold dyadicCubeStepRadius
  rw [one_div_pow]
  have hpow : ((2 ^ (level + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  rw [Nat.cast_pow]
  ring

private theorem dyadicSupercritical_ratio_gt_one (dimension : ℕ) (hdimension : 2 < dimension) :
    1 < Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 := by
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  simp only [one_mul]
  apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)).mpr
  have hpow : 2 ^ 2 < 2 ^ dimension :=
    Nat.pow_lt_pow_right (by norm_num) hdimension
  norm_num at hpow ⊢
  exact_mod_cast hpow

/--
For every `dimension > 2`, the supercritical compact dyadic budget is a
finite increasing geometric sum.  The displayed ratio is explicit so a later
depth-selection theorem can balance it against the terminal dyadic radius.
-/
theorem dyadicDimensionGreaterTwoGeometricConfidenceBound_le
    (dimension count depth : ℕ) (hdimension : 2 < dimension) (hcount : 0 < count)
    (confidence : ℝ) (hconfidence : 0 ≤ confidence) :
    dyadicMultiscaleThresholdBound dimension depth
      (fun level ↦ dyadicGeometricConfidenceThreshold dimension count level confidence) ≤
      2 * Real.sqrt dimension / ((2 ^ depth : ℕ) : ℝ) +
        (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
          (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (depth + 1) /
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) +
        2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt count := by
  have hratio := dyadicSupercritical_ratio_gt_one dimension hdimension
  refine (dyadicMultiscaleGeometricConfidenceBound_le_twoTerm
    dimension count depth hcount confidence hconfidence).trans ?_
  have hsum :
      (∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius dimension level *
            (2 * (Real.sqrt (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt count)) ≤
        (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
          (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (depth + 1) /
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) +
        2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt count := by
    calc
      (∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius dimension level *
            (2 * (Real.sqrt (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt count)) =
          ∑ level ∈ Finset.range depth,
            ((2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
                (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (level + 1) +
              (2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt count) *
                (1 / 2 : ℝ) ^ (level + 1)) := by
            apply Finset.sum_congr rfl
            intro level hlevel
            rw [show 2 *
                (Real.sqrt (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ)) +
                  Real.sqrt confidence) / Real.sqrt count =
                2 * Real.sqrt (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ)) /
                  Real.sqrt count +
                2 * Real.sqrt confidence / Real.sqrt count by ring]
            rw [mul_add, dyadicSupercritical_mainTerm_eq dimension level count hcount,
              dyadicSupercritical_confidenceTerm_eq dimension level count hcount confidence]
      _ = (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
          ∑ level ∈ Finset.range depth,
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (level + 1) +
          (2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt count) *
            ∑ level ∈ Finset.range depth, (1 / 2 : ℝ) ^ (level + 1) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [Finset.mul_sum]
            · rw [Finset.mul_sum]
      _ ≤ (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
          (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (depth + 1) /
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) +
          2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt count := by
            apply add_le_add
            · calc
                (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
                    ∑ level ∈ Finset.range depth,
                      (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (level + 1) ≤
                    (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
                      ((Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (depth + 1) /
                        (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1)) :=
                  mul_le_mul_of_nonneg_left
                    (sum_range_pow_succ_le_geometric
                      (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) hratio depth)
                    (by positivity)
                _ = (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
                    (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (depth + 1) /
                      (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) := by ring
            · simpa using mul_le_mul_of_nonneg_left
                (sum_range_half_pow_succ_le_one depth) (by positivity)
  unfold dyadicCubeRadius
  convert add_le_add_left hsum (2 * Real.sqrt dimension / ((2 ^ depth : ℕ) : ℝ)) using 1 <;> ring

/--
For every positive dimension, the geometric confidence schedule has compact
empirical-W₁ failure probability at most `exp (-confidence)`, independently
of the retained finite dyadic depth.
-/
theorem measure_empiricalWassersteinOne_gt_dyadicGeometricConfidenceThresholdBound_le
    (dimension : ℕ) (hdimension : 0 < dimension)
    (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count) (depth : ℕ)
    (confidence : ℝ) (hconfidence : 0 ≤ confidence) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth
        (fun level ↦ dyadicGeometricConfidenceThreshold dimension count level confidence)) <
        empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-confidence) := by
  refine (measure_empiricalWassersteinOne_gt_dyadicMultiscaleThresholdBound_le
    dimension law count hcount depth
    (fun level ↦ dyadicGeometricConfidenceThreshold dimension count level confidence)
    (fun level ↦ dyadicGeometricConfidenceThreshold_nonneg dimension count level confidence)).trans ?_
  calc
    (∑ level ∈ Finset.range depth,
        (2 ^ (2 ^ (dimension * (level + 1))) : ℕ) *
          Real.exp (-((count : ℝ) *
            dyadicGeometricConfidenceThreshold dimension count (level + 1) confidence ^ 2) / 2)) ≤
        ∑ level ∈ Finset.range depth,
          Real.exp (-confidence) * (1 / 2 : ℝ) ^ (level + 1 + 1) := by
            refine Finset.sum_le_sum ?_
            intro level hlevel
            simpa [Nat.cast_add] using
              (dyadicGeometricConfidenceThreshold_numericalTail_le dimension count
                (level + 1) hdimension hcount confidence hconfidence)
    _ = Real.exp (-confidence) * ∑ level ∈ Finset.range depth,
          (1 / 2 : ℝ) ^ (level + 1 + 1) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-confidence) := by
          have hshift : (∑ level ∈ Finset.range depth,
              (1 / 2 : ℝ) ^ (level + 1 + 1)) ≤
              ∑ level ∈ Finset.range depth, (1 / 2 : ℝ) ^ (level + 1) := by
            apply Finset.sum_le_sum
            intro level hlevel
            apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
            omega
          simpa using mul_le_mul_of_nonneg_left
            (hshift.trans (sum_range_half_pow_succ_le_one depth)) (Real.exp_pos _).le

/--
An explicit deterministic bound on the geometric dyadic budget immediately
turns the compact confidence schedule into a W₁ tail bound at that radius.
This is the source-facing Proposition 10 interface; the three dimension
regimes below provide its concrete numerical antecedents.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_of_dyadicGeometricConfidenceBudget_le
    (dimension : ℕ) (hdimension : 0 < dimension)
    (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count) (depth : ℕ)
    (confidence radius : ℝ) (hconfidence : 0 ≤ confidence)
    (hbudget : dyadicMultiscaleThresholdBound dimension depth
      (fun level ↦ dyadicGeometricConfidenceThreshold dimension count level confidence) ≤ radius) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-confidence) := by
  letI : IsProbabilityMeasure
      (finiteIIDSampleLaw (law : Measure (HalfOpenUnitCube dimension)) count) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  have hsubset : {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ⊆
      {sample |
        ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth
          (fun level ↦ dyadicGeometricConfidenceThreshold dimension count level confidence)) <
          empiricalWassersteinOne law hcount sample} := by
    intro sample hsample
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hbudget) hsample
  exact (measureReal_mono hsubset (measure_ne_top _ _)).trans
    (measure_empiricalWassersteinOne_gt_dyadicGeometricConfidenceThresholdBound_le
      dimension hdimension law count hcount depth confidence hconfidence)

/--
The compact `p = 1`, one-dimensional Proposition 10 consequence at any
finite depth satisfying its displayed dyadic bound.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_of_dyadicDimensionOneGeometricBudget
    (law : ProbabilityMeasure (HalfOpenUnitCube 1))
    (count : ℕ) (hcount : 0 < count) (depth : ℕ)
    (confidence radius : ℝ) (hconfidence : 0 ≤ confidence)
    (hbudget :
      2 / ((2 ^ depth : ℕ) : ℝ) +
        (2 / Real.sqrt count) * (1 / (1 - 1 / Real.sqrt 2)) +
        2 * Real.sqrt confidence / Real.sqrt count ≤ radius) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-confidence) := by
  apply measure_empiricalWassersteinOne_gt_le_exp_neg_of_dyadicGeometricConfidenceBudget_le
    1 (by norm_num) law count hcount depth confidence radius hconfidence
  exact (dyadicDimensionOneGeometricConfidenceBound_le count depth hcount confidence hconfidence).trans
    hbudget

/--
Normalizing the geometric-confidence term by `N x² / 64` makes its
contribution exactly `x / 4`.  This elementary identity is shared by the
one-dimensional compact square-rate schedule.
-/
theorem two_mul_sqrt_count_mul_sq_div_sixtyFour_div_sqrt_count
    (count : ℕ) (hcount : 0 < count) {radius : ℝ} (hradius : 0 ≤ radius) :
    2 * Real.sqrt ((count : ℝ) * radius ^ 2 / 64) / Real.sqrt count = radius / 4 := by
  have hcount_real : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hinsidenonneg : 0 ≤ (count : ℝ) * radius ^ 2 / 64 := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, mul_pow, Real.sq_sqrt hinsidenonneg, Real.sq_sqrt hcount_real.le]
  field_simp
  ring

/--
The compact one-dimensional Fournier--Guillin square-rate implication with
all finite-depth conditions displayed.  A depth that controls the terminal
radius and a sample count that controls the geometric main term yield failure
at most `exp (-N x² / 64)`.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_sixtyFour_of_dyadicDimensionOne
    (law : ProbabilityMeasure (HalfOpenUnitCube 1))
    (count : ℕ) (hcount : 0 < count) (depth : ℕ)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (hterminal : 2 / ((2 ^ depth : ℕ) : ℝ) ≤ radius / 4)
    (hmain : (2 / Real.sqrt count) * (1 / (1 - 1 / Real.sqrt 2)) ≤ radius / 4) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-((count : ℝ) * radius ^ 2 / 64)) := by
  apply measure_empiricalWassersteinOne_gt_le_exp_neg_of_dyadicDimensionOneGeometricBudget
    law count hcount depth ((count : ℝ) * radius ^ 2 / 64) radius (by positivity)
  have hconfidenceTerm := two_mul_sqrt_count_mul_sq_div_sixtyFour_div_sqrt_count
    count hcount hradius
  rw [hconfidenceTerm]
  linarith

/--
The compact critical two-dimensional Proposition 10 consequence at any
finite depth satisfying its displayed dyadic bound.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_of_dyadicDimensionTwoGeometricBudget
    (law : ProbabilityMeasure (HalfOpenUnitCube 2))
    (count : ℕ) (hcount : 0 < count) (depth : ℕ)
    (confidence radius : ℝ) (hconfidence : 0 ≤ confidence)
    (hbudget :
      2 * Real.sqrt 2 / ((2 ^ depth : ℕ) : ℝ) +
        4 * depth / Real.sqrt count +
        2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt count ≤ radius) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-confidence) := by
  apply measure_empiricalWassersteinOne_gt_le_exp_neg_of_dyadicGeometricConfidenceBudget_le
    2 (by norm_num) law count hcount depth confidence radius hconfidence
  exact (dyadicDimensionTwoGeometricConfidenceBound_le count depth hcount confidence hconfidence).trans
    hbudget

/--
At confidence `N x² / 128`, the critical two-dimensional confidence component
of the dyadic budget is exactly `x / 4`.
-/
theorem two_mul_sqrt_two_mul_sqrt_count_mul_sq_div_oneTwentyEight_div_sqrt_count
    (count : ℕ) (hcount : 0 < count) {radius : ℝ} (hradius : 0 ≤ radius) :
    2 * Real.sqrt 2 * Real.sqrt ((count : ℝ) * radius ^ 2 / 128) /
      Real.sqrt count = radius / 4 := by
  have hcount_real : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hinsidenonneg : 0 ≤ (count : ℝ) * radius ^ 2 / 128 := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt hinsidenonneg, Real.sq_sqrt hcount_real.le]
  field_simp
  ring

/--
The compact critical two-dimensional Fournier--Guillin implication with a
displayed finite depth.  The middle hypothesis is precisely the source's
logarithmic depth cost; once it is at most `x / 4`, the resulting tail is
`exp (-N x² / 128)`.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_oneTwentyEight_of_dyadicDimensionTwo
    (law : ProbabilityMeasure (HalfOpenUnitCube 2))
    (count : ℕ) (hcount : 0 < count) (depth : ℕ)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (hterminal : 2 * Real.sqrt 2 / ((2 ^ depth : ℕ) : ℝ) ≤ radius / 4)
    (hmain : 4 * depth / Real.sqrt count ≤ radius / 4) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-((count : ℝ) * radius ^ 2 / 128)) := by
  apply measure_empiricalWassersteinOne_gt_le_exp_neg_of_dyadicDimensionTwoGeometricBudget
    law count hcount depth ((count : ℝ) * radius ^ 2 / 128) radius (by positivity)
  have hconfidenceTerm :=
    two_mul_sqrt_two_mul_sqrt_count_mul_sq_div_oneTwentyEight_div_sqrt_count
      count hcount hradius
  rw [hconfidenceTerm]
  linarith

/--
The compact supercritical Proposition 10 consequence at any finite depth
satisfying its displayed increasing-geometric dyadic bound.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_of_dyadicDimensionGreaterTwoGeometricBudget
    (dimension : ℕ) (hdimension : 2 < dimension)
    (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count) (depth : ℕ)
    (confidence radius : ℝ) (hconfidence : 0 ≤ confidence)
    (hbudget :
      2 * Real.sqrt dimension / ((2 ^ depth : ℕ) : ℝ) +
        (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
          (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (depth + 1) /
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) +
        2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt count ≤ radius) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-confidence) := by
  apply measure_empiricalWassersteinOne_gt_le_exp_neg_of_dyadicGeometricConfidenceBudget_le
    dimension (by omega) law count hcount depth confidence radius hconfidence
  exact (dyadicDimensionGreaterTwoGeometricConfidenceBound_le
    dimension count depth hdimension hcount confidence hconfidence).trans hbudget

/--
For every positive dimension, confidence `N x² / (64 d)` makes the
dimension-scaled confidence component of the compact dyadic budget exactly
`x / 4`.
-/
theorem two_mul_sqrt_dimension_mul_sqrt_count_mul_sq_div_sixtyFour_mul_dimension_div_sqrt_count
    (dimension count : ℕ) (hdimension : 0 < dimension) (hcount : 0 < count)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    2 * Real.sqrt dimension *
      Real.sqrt ((count : ℝ) * radius ^ 2 / (64 * dimension)) /
        Real.sqrt count = radius / 4 := by
  have hcount_real : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hdimension_real : 0 < (dimension : ℝ) := by exact_mod_cast hdimension
  have hinsidenonneg : 0 ≤ (count : ℝ) * radius ^ 2 / (64 * dimension) := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hdimension_real.le,
    Real.sq_sqrt hinsidenonneg, Real.sq_sqrt hcount_real.le]
  field_simp
  ring

/--
The compact supercritical Fournier--Guillin implication with finite depth and
all three dyadic terms explicit.  The increasing geometric main term is the
only dimension-dependent condition left to a subsequent depth selection.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_sixtyFour_mul_dimension_of_dyadicDimensionGreaterTwo
    (dimension : ℕ) (hdimension : 2 < dimension)
    (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count) (depth : ℕ)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (hterminal : 2 * Real.sqrt dimension / ((2 ^ depth : ℕ) : ℝ) ≤ radius / 4)
    (hmain :
      (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
          (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (depth + 1) /
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) ≤ radius / 4) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-((count : ℝ) * radius ^ 2 / (64 * dimension))) := by
  apply measure_empiricalWassersteinOne_gt_le_exp_neg_of_dyadicDimensionGreaterTwoGeometricBudget
    dimension hdimension law count hcount depth
      ((count : ℝ) * radius ^ 2 / (64 * dimension)) radius (by positivity)
  have hconfidenceTerm :=
    two_mul_sqrt_dimension_mul_sqrt_count_mul_sq_div_sixtyFour_mul_dimension_div_sqrt_count
      dimension count (by omega) hcount hradius
  rw [hconfidenceTerm]
  linarith

private theorem dyadicDimensionTwo_mainTermReal_eq
    (level : ℕ) {effectiveCount : ℝ} (heffectiveCount : 0 < effectiveCount) :
    dyadicCubeStepRadius 2 level *
      (2 * Real.sqrt (2 * ((2 ^ (2 * (level + 1)) : ℕ) : ℝ)) /
        Real.sqrt effectiveCount) = 4 / Real.sqrt effectiveCount := by
  rw [dyadicStepRadius_two_eq, sqrt_two_mul_two_pow_two_mul]
  have hpow : ((2 ^ (level + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt effectiveCount ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr heffectiveCount)
  field_simp [hsqrt, hpow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

private theorem dyadicDimensionTwo_confidenceTermReal_eq
    (level : ℕ) {effectiveCount confidence : ℝ} (heffectiveCount : 0 < effectiveCount) :
    dyadicCubeStepRadius 2 level *
      (2 * Real.sqrt confidence / Real.sqrt effectiveCount) =
      (2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt effectiveCount) *
        (1 / 2 : ℝ) ^ (level + 1) := by
  rw [dyadicStepRadius_two_eq, one_div_pow]
  have hpow : ((2 ^ (level + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt effectiveCount ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr heffectiveCount)
  field_simp [hsqrt, hpow]
  rw [Nat.cast_pow]
  ring

/--
The critical compact dyadic budget at an arbitrary positive real effective
count.  This is the form used for conditional source-shell samples, whose
expected selected count need not be integral.
-/
theorem dyadicDimensionTwoGeometricConfidenceBoundReal_le
    (depth : ℕ) {effectiveCount confidence : ℝ}
    (heffectiveCount : 0 < effectiveCount) (hconfidence : 0 ≤ confidence) :
    dyadicMultiscaleThresholdBound 2 depth
      (fun level ↦ dyadicGeometricConfidenceThresholdReal
        2 level effectiveCount confidence) ≤
      2 * Real.sqrt 2 / ((2 ^ depth : ℕ) : ℝ) +
        4 * depth / Real.sqrt effectiveCount +
        2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt effectiveCount := by
  refine (dyadicMultiscaleGeometricConfidenceBoundReal_le_twoTerm
    2 depth heffectiveCount hconfidence).trans ?_
  rw [dyadicRadius_two_eq]
  have hsum :
      (∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius 2 level *
            (2 * (Real.sqrt (2 * ((2 ^ (2 * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt effectiveCount)) ≤
        4 * depth / Real.sqrt effectiveCount +
          2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt effectiveCount := by
    calc
      (∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius 2 level *
            (2 * (Real.sqrt (2 * ((2 ^ (2 * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt effectiveCount)) =
          ∑ level ∈ Finset.range depth,
            (4 / Real.sqrt effectiveCount +
              (2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt effectiveCount) *
                (1 / 2 : ℝ) ^ (level + 1)) := by
            apply Finset.sum_congr rfl
            intro level hlevel
            rw [show 2 *
                (Real.sqrt (2 * ((2 ^ (2 * (level + 1)) : ℕ) : ℝ)) +
                  Real.sqrt confidence) / Real.sqrt effectiveCount =
                2 * Real.sqrt (2 * ((2 ^ (2 * (level + 1)) : ℕ) : ℝ)) /
                  Real.sqrt effectiveCount +
                2 * Real.sqrt confidence / Real.sqrt effectiveCount by ring]
            rw [mul_add,
              dyadicDimensionTwo_mainTermReal_eq level heffectiveCount,
              dyadicDimensionTwo_confidenceTermReal_eq level heffectiveCount]
      _ = 4 * depth / Real.sqrt effectiveCount +
          (2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt effectiveCount) *
            ∑ level ∈ Finset.range depth, (1 / 2 : ℝ) ^ (level + 1) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            simp [nsmul_eq_mul]
            ring
      _ ≤ 4 * depth / Real.sqrt effectiveCount +
          2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt effectiveCount := by
            simpa using add_le_add_left
              (mul_le_mul_of_nonneg_left (sum_range_half_pow_succ_le_one depth) (by positivity))
              (4 * depth / Real.sqrt effectiveCount)
  convert add_le_add_left hsum (2 * Real.sqrt 2 / ((2 ^ depth : ℕ) : ℝ)) using 1 <;> ring

private theorem dyadicDimensionOne_mainTermReal_eq
    (level : ℕ) {effectiveCount : ℝ} (heffectiveCount : 0 < effectiveCount) :
    dyadicCubeStepRadius 1 level *
      (2 * Real.sqrt (2 * ((2 ^ (1 * (level + 1)) : ℕ) : ℝ)) /
        Real.sqrt effectiveCount) =
      2 / Real.sqrt effectiveCount * (1 / Real.sqrt 2 : ℝ) ^ level := by
  rw [dyadicStepRadius_one_eq]
  rw [show 1 * (level + 1) = level + 1 by ring]
  have htwo : 2 * ((2 ^ (level + 1) : ℕ) : ℝ) =
      ((2 ^ (level + 1 + 1) : ℕ) : ℝ) := by
    calc
      2 * ((2 ^ (level + 1) : ℕ) : ℝ) =
          (2 : ℝ) * (2 : ℝ) ^ (level + 1) := by norm_num [Nat.cast_pow]
      _ = (2 : ℝ) ^ (level + 1 + 1) := by rw [pow_succ]; ring
      _ = ((2 ^ (level + 1 + 1) : ℕ) : ℝ) := by norm_num [Nat.cast_pow]
  rw [htwo, sqrt_two_pow_eq_sqrt_two_pow]
  have hpow : ((2 ^ (level + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt effectiveCount ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr heffectiveCount)
  rw [show (Real.sqrt 2) ^ (level + 1 + 1) = (Real.sqrt 2) ^ level * 2 by
    rw [show level + 1 + 1 = level + 2 by omega, pow_add,
      Real.sq_sqrt (by norm_num)]]
  have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [show (1 / Real.sqrt 2 : ℝ) ^ level =
      (Real.sqrt 2) ^ level / (2 : ℝ) ^ level by
    rw [one_div, hinv, div_pow]]
  field_simp [hsqrt, hpow]
  rw [Nat.cast_pow, pow_succ]
  ring

private theorem dyadicDimensionOne_confidenceTermReal_eq
    (level : ℕ) {effectiveCount confidence : ℝ} (heffectiveCount : 0 < effectiveCount) :
    dyadicCubeStepRadius 1 level *
      (2 * Real.sqrt confidence / Real.sqrt effectiveCount) =
      (2 * Real.sqrt confidence / Real.sqrt effectiveCount) *
        (1 / 2 : ℝ) ^ (level + 1) := by
  rw [dyadicStepRadius_one_eq, one_div_pow]
  have hpow : ((2 ^ (level + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt effectiveCount ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr heffectiveCount)
  field_simp [hsqrt, hpow]
  rw [Nat.cast_pow]
  ring

/--
The subcritical compact dyadic budget at a positive real effective count.
Its main cell contribution remains summable independently of the retained
depth, exactly as in the fixed-count compact calculation.
-/
theorem dyadicDimensionOneGeometricConfidenceBoundReal_le
    (depth : ℕ) {effectiveCount confidence : ℝ}
    (heffectiveCount : 0 < effectiveCount) (hconfidence : 0 ≤ confidence) :
    dyadicMultiscaleThresholdBound 1 depth
      (fun level ↦ dyadicGeometricConfidenceThresholdReal
        1 level effectiveCount confidence) ≤
      2 / ((2 ^ depth : ℕ) : ℝ) +
        (2 / Real.sqrt effectiveCount) * (1 / (1 - 1 / Real.sqrt 2)) +
        2 * Real.sqrt confidence / Real.sqrt effectiveCount := by
  refine (dyadicMultiscaleGeometricConfidenceBoundReal_le_twoTerm
    1 depth heffectiveCount hconfidence).trans ?_
  rw [dyadicRadius_one_eq]
  have hsum :
      (∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius 1 level *
            (2 * (Real.sqrt (2 * ((2 ^ (1 * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt effectiveCount)) ≤
        (2 / Real.sqrt effectiveCount) * (1 / (1 - 1 / Real.sqrt 2)) +
          2 * Real.sqrt confidence / Real.sqrt effectiveCount := by
    calc
      (∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius 1 level *
            (2 * (Real.sqrt (2 * ((2 ^ (1 * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt effectiveCount)) =
          ∑ level ∈ Finset.range depth,
            (2 / Real.sqrt effectiveCount * (1 / Real.sqrt 2 : ℝ) ^ level +
              (2 * Real.sqrt confidence / Real.sqrt effectiveCount) *
                (1 / 2 : ℝ) ^ (level + 1)) := by
            apply Finset.sum_congr rfl
            intro level hlevel
            rw [show 2 *
                (Real.sqrt (2 * ((2 ^ (1 * (level + 1)) : ℕ) : ℝ)) +
                  Real.sqrt confidence) / Real.sqrt effectiveCount =
                2 * Real.sqrt (2 * ((2 ^ (1 * (level + 1)) : ℕ) : ℝ)) /
                  Real.sqrt effectiveCount +
                2 * Real.sqrt confidence / Real.sqrt effectiveCount by ring]
            rw [mul_add,
              dyadicDimensionOne_mainTermReal_eq level heffectiveCount,
              dyadicDimensionOne_confidenceTermReal_eq level heffectiveCount]
      _ = (2 / Real.sqrt effectiveCount) *
          ∑ level ∈ Finset.range depth, (1 / Real.sqrt 2 : ℝ) ^ level +
          (2 * Real.sqrt confidence / Real.sqrt effectiveCount) *
            ∑ level ∈ Finset.range depth, (1 / 2 : ℝ) ^ (level + 1) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [Finset.mul_sum]
            · rw [Finset.mul_sum]
      _ ≤ (2 / Real.sqrt effectiveCount) * (1 / (1 - 1 / Real.sqrt 2)) +
          2 * Real.sqrt confidence / Real.sqrt effectiveCount := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left
                (sum_range_inv_sqrt_two_pow_le depth) (by positivity)
            · simpa using mul_le_mul_of_nonneg_left
                (sum_range_half_pow_succ_le_one depth) (by positivity)
  convert add_le_add_left hsum (2 / ((2 ^ depth : ℕ) : ℝ)) using 1 <;> ring

private theorem dyadicSupercritical_mainTermReal_eq
    (dimension level : ℕ) {effectiveCount : ℝ} (heffectiveCount : 0 < effectiveCount) :
    dyadicCubeStepRadius dimension level *
      (2 * Real.sqrt (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ)) /
        Real.sqrt effectiveCount) =
      (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt effectiveCount) *
        (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (level + 1) := by
  unfold dyadicCubeStepRadius
  rw [sqrt_two_mul_dyadicCellCount_eq]
  rw [div_pow]
  have hpow : ((2 ^ (level + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt effectiveCount ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr heffectiveCount)
  field_simp [hsqrt, hpow]
  rw [Nat.cast_pow]
  ring

private theorem dyadicSupercritical_confidenceTermReal_eq
    (dimension level : ℕ) {effectiveCount confidence : ℝ}
    (heffectiveCount : 0 < effectiveCount) :
    dyadicCubeStepRadius dimension level *
      (2 * Real.sqrt confidence / Real.sqrt effectiveCount) =
      (2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt effectiveCount) *
        (1 / 2 : ℝ) ^ (level + 1) := by
  unfold dyadicCubeStepRadius
  rw [one_div_pow]
  have hpow : ((2 ^ (level + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt effectiveCount ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr heffectiveCount)
  field_simp [hsqrt, hpow]
  rw [Nat.cast_pow]
  ring

/--
The supercritical compact dyadic budget at a positive real effective count.
It retains the increasing finite-geometric term which, after a depth choice,
produces the general-dimensional `N^(-1/d)` compact scale.
-/
theorem dyadicDimensionGreaterTwoGeometricConfidenceBoundReal_le
    (dimension depth : ℕ) (hdimension : 2 < dimension)
    {effectiveCount confidence : ℝ}
    (heffectiveCount : 0 < effectiveCount) (hconfidence : 0 ≤ confidence) :
    dyadicMultiscaleThresholdBound dimension depth
      (fun level ↦ dyadicGeometricConfidenceThresholdReal
        dimension level effectiveCount confidence) ≤
      2 * Real.sqrt dimension / ((2 ^ depth : ℕ) : ℝ) +
        (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt effectiveCount) *
          (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (depth + 1) /
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) +
        2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt effectiveCount := by
  have hratio := dyadicSupercritical_ratio_gt_one dimension hdimension
  refine (dyadicMultiscaleGeometricConfidenceBoundReal_le_twoTerm
    dimension depth heffectiveCount hconfidence).trans ?_
  have hsum :
      (∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius dimension level *
            (2 * (Real.sqrt (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt effectiveCount)) ≤
        (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt effectiveCount) *
          (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (depth + 1) /
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) +
          2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt effectiveCount := by
    calc
      (∑ level ∈ Finset.range depth,
          dyadicCubeStepRadius dimension level *
            (2 * (Real.sqrt (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ)) +
              Real.sqrt confidence) / Real.sqrt effectiveCount)) =
          ∑ level ∈ Finset.range depth,
            ((2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt effectiveCount) *
                (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (level + 1) +
              (2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt effectiveCount) *
                (1 / 2 : ℝ) ^ (level + 1)) := by
            apply Finset.sum_congr rfl
            intro level hlevel
            rw [show 2 *
                (Real.sqrt (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ)) +
                  Real.sqrt confidence) / Real.sqrt effectiveCount =
                2 * Real.sqrt (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ)) /
                  Real.sqrt effectiveCount +
                2 * Real.sqrt confidence / Real.sqrt effectiveCount by ring]
            rw [mul_add,
              dyadicSupercritical_mainTermReal_eq dimension level heffectiveCount,
              dyadicSupercritical_confidenceTermReal_eq dimension level heffectiveCount]
      _ = (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt effectiveCount) *
          ∑ level ∈ Finset.range depth,
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (level + 1) +
          (2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt effectiveCount) *
            ∑ level ∈ Finset.range depth, (1 / 2 : ℝ) ^ (level + 1) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [Finset.mul_sum]
            · rw [Finset.mul_sum]
      _ ≤ (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt effectiveCount) *
          (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (depth + 1) /
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) +
          2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt effectiveCount := by
            apply add_le_add
            · calc
                (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt effectiveCount) *
                    ∑ level ∈ Finset.range depth,
                      (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (level + 1) ≤
                    (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt effectiveCount) *
                      ((Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (depth + 1) /
                        (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1)) :=
                  mul_le_mul_of_nonneg_left
                    (sum_range_pow_succ_le_geometric
                      (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) hratio depth)
                    (by positivity)
                _ = (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt effectiveCount) *
                    (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^ (depth + 1) /
                      (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) := by ring
            · simpa using mul_le_mul_of_nonneg_left
                (sum_range_half_pow_succ_le_one depth) (by positivity)
  unfold dyadicCubeRadius
  convert add_le_add_left hsum
    (2 * Real.sqrt dimension / ((2 ^ depth : ℕ) : ℝ)) using 1 <;> ring

/--
The source's compact dyadic terminal term has a single concrete logarithmic
cutoff in dimension one.  This packages the arithmetic choice independently
of the sample-count condition that controls the nonterminal dyadic sum.
-/
theorem dyadicDimensionOne_terminalDepth_le_quarter
    {radius : ℝ} (hradius : 0 < radius) :
    2 / ((2 ^ Nat.ceil (Real.logb 2 (8 / radius)) : ℕ) : ℝ) ≤ radius / 4 := by
  simpa using (Math.dyadic_terminalRadius_le_quarter
    (coefficient := (1 : ℝ)) (radius := radius) (by norm_num) hradius)

/--
At the explicit depth `ceil(log₂(8 / x))`, the compact one-dimensional
square-rate bound needs only its displayed effective-count condition.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_sixtyFour_of_dyadicDimensionOne_logDepth
    (law : ProbabilityMeasure (HalfOpenUnitCube 1))
    (count : ℕ) (hcount : 0 < count)
    {radius : ℝ} (hradius : 0 < radius)
    (hmain : (2 / Real.sqrt count) * (1 / (1 - 1 / Real.sqrt 2)) ≤ radius / 4) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-((count : ℝ) * radius ^ 2 / 64)) := by
  exact measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_sixtyFour_of_dyadicDimensionOne
    law count hcount (Nat.ceil (Real.logb 2 (8 / radius))) hradius.le
    (dyadicDimensionOne_terminalDepth_le_quarter hradius) hmain

/--
The source's compact dyadic terminal term has a concrete logarithmic cutoff
in the critical two-dimensional regime.
-/
theorem dyadicDimensionTwo_terminalDepth_le_quarter
    {radius : ℝ} (hradius : 0 < radius) :
    2 * Real.sqrt 2 /
        ((2 ^ Nat.ceil (Real.logb 2 (8 * Real.sqrt 2 / radius)) : ℕ) : ℝ) ≤
      radius / 4 := by
  simpa using (Math.dyadic_terminalRadius_le_quarter
    (coefficient := Real.sqrt 2) (radius := radius)
    (Real.sqrt_pos.2 (by norm_num)) hradius)

/--
At the explicit critical logarithmic depth, the compact two-dimensional
square-rate bound needs only the source's logarithmic effective-count term.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_oneTwentyEight_of_dyadicDimensionTwo_logDepth
    (law : ProbabilityMeasure (HalfOpenUnitCube 2))
    (count : ℕ) (hcount : 0 < count)
    {radius : ℝ} (hradius : 0 < radius)
    (hmain :
      4 * Nat.ceil (Real.logb 2 (8 * Real.sqrt 2 / radius)) /
        Real.sqrt count ≤ radius / 4) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-((count : ℝ) * radius ^ 2 / 128)) := by
  exact measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_oneTwentyEight_of_dyadicDimensionTwo
    law count hcount (Nat.ceil (Real.logb 2 (8 * Real.sqrt 2 / radius))) hradius.le
    (dyadicDimensionTwo_terminalDepth_le_quarter hradius) hmain

/--
For every supercritical dimension, `ceil(log₂(8 √d / x))` controls the
terminal compact dyadic radius.  The increasing multiscale term remains an
explicit, separately checkable effective-count condition.
-/
theorem dyadicDimensionGreaterTwo_terminalDepth_le_quarter
    (dimension : ℕ) (hdimension : 2 < dimension)
    {radius : ℝ} (hradius : 0 < radius) :
    2 * Real.sqrt dimension /
        ((2 ^ Nat.ceil (Real.logb 2 (8 * Real.sqrt dimension / radius)) : ℕ) : ℝ) ≤
      radius / 4 := by
  exact Math.dyadic_terminalRadius_le_quarter
    (coefficient := Real.sqrt dimension) (radius := radius)
    (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < dimension by omega))) hradius

/--
At the explicit supercritical logarithmic depth, the compact square-rate
bound has only its increasing-geometric effective-count condition remaining.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_sixtyFour_mul_dimension_of_dyadicDimensionGreaterTwo_logDepth
    (dimension : ℕ) (hdimension : 2 < dimension)
    (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count)
    {radius : ℝ} (hradius : 0 < radius)
    (hmain :
      (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
          (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^
              (Nat.ceil (Real.logb 2 (8 * Real.sqrt dimension / radius)) + 1) /
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) ≤ radius / 4) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-((count : ℝ) * radius ^ 2 / (64 * dimension))) := by
  exact measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_sixtyFour_mul_dimension_of_dyadicDimensionGreaterTwo
    dimension hdimension law count hcount
    (Nat.ceil (Real.logb 2 (8 * Real.sqrt dimension / radius))) hradius.le
    (dyadicDimensionGreaterTwo_terminalDepth_le_quarter dimension hdimension hradius) hmain

/--
The one-dimensional compact main term is at most `x / 4` under its explicit
inverse-square sample-size condition.
-/
theorem dyadicDimensionOne_mainTerm_le_quarter_of_effectiveCount
    (count : ℕ) (hcount : 0 < count)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (hcountBound :
      16 * (2 * (1 / (1 - 1 / Real.sqrt 2))) ^ 2 ≤
        (count : ℝ) * radius ^ 2) :
    (2 / Real.sqrt count) * (1 / (1 - 1 / Real.sqrt 2)) ≤ radius / 4 := by
  have hsqrtTwo_gt : 1 < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)
  have hden_pos : 0 < 1 - 1 / Real.sqrt 2 := by
    have hinv_lt_one : (1 / Real.sqrt 2 : ℝ) < 1 :=
      (div_lt_one₀ (by positivity)).mpr hsqrtTwo_gt
    linarith
  calc
    (2 / Real.sqrt count) * (1 / (1 - 1 / Real.sqrt 2)) =
        (2 * (1 / (1 - 1 / Real.sqrt 2))) / Real.sqrt count := by ring
    _ ≤ radius / 4 :=
      Math.div_sqrt_nat_le_quarter_of_sixteen_sq_le count hcount
        (by positivity) hradius hcountBound

/--
Combining the concrete dyadic depth with the explicit effective-count bound
gives a premise-free compact terminal/main schedule in dimension one.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_sixtyFour_of_dyadicDimensionOne_explicitEffectiveCount
    (law : ProbabilityMeasure (HalfOpenUnitCube 1))
    (count : ℕ) (hcount : 0 < count)
    {radius : ℝ} (hradius : 0 < radius)
    (hcountBound :
      16 * (2 * (1 / (1 - 1 / Real.sqrt 2))) ^ 2 ≤
        (count : ℝ) * radius ^ 2) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-((count : ℝ) * radius ^ 2 / 64)) := by
  exact measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_sixtyFour_of_dyadicDimensionOne_logDepth
    law count hcount hradius
    (dyadicDimensionOne_mainTerm_le_quarter_of_effectiveCount count hcount hradius.le hcountBound)

/--
The critical two-dimensional compact main term is at most `x / 4` under its
explicit logarithmic inverse-square effective-count condition.
-/
theorem dyadicDimensionTwo_mainTerm_le_quarter_of_effectiveCount
    (count : ℕ) (hcount : 0 < count)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (hcountBound :
      16 * (4 * Nat.ceil (Real.logb 2 (8 * Real.sqrt 2 / radius))) ^ 2 ≤
        (count : ℝ) * radius ^ 2) :
    4 * Nat.ceil (Real.logb 2 (8 * Real.sqrt 2 / radius)) /
      Real.sqrt count ≤ radius / 4 := by
  simpa using Math.div_sqrt_nat_le_quarter_of_sixteen_sq_le count hcount
    (coefficient := 4 * Nat.ceil (Real.logb 2 (8 * Real.sqrt 2 / radius)))
    (by positivity) hradius hcountBound

/--
The critical compact square-rate schedule with both its depth and its
logarithmic effective-count requirement explicit.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_oneTwentyEight_of_dyadicDimensionTwo_explicitEffectiveCount
    (law : ProbabilityMeasure (HalfOpenUnitCube 2))
    (count : ℕ) (hcount : 0 < count)
    {radius : ℝ} (hradius : 0 < radius)
    (hcountBound :
      16 * (4 * Nat.ceil (Real.logb 2 (8 * Real.sqrt 2 / radius))) ^ 2 ≤
        (count : ℝ) * radius ^ 2) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-((count : ℝ) * radius ^ 2 / 128)) := by
  exact measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_oneTwentyEight_of_dyadicDimensionTwo_logDepth
    law count hcount hradius
    (dyadicDimensionTwo_mainTerm_le_quarter_of_effectiveCount count hcount hradius.le hcountBound)

/--
The supercritical compact main term is at most `x / 4` under its displayed
dimension-dependent effective-count inequality.  The logarithmic depth is
the same terminal-radius choice used in the source multiscale argument.
-/
theorem dyadicDimensionGreaterTwo_mainTerm_le_quarter_of_effectiveCount
    (dimension count : ℕ) (hdimension : 2 < dimension) (hcount : 0 < count)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (hcountBound :
      16 *
          ((2 * Real.sqrt dimension * Real.sqrt 2) *
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^
                (Nat.ceil (Real.logb 2 (8 * Real.sqrt dimension / radius)) + 1) /
              (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1)) ^ 2 ≤
        (count : ℝ) * radius ^ 2) :
    (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
          (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^
              (Nat.ceil (Real.logb 2 (8 * Real.sqrt dimension / radius)) + 1) /
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) ≤ radius / 4 := by
  let ratio : ℝ := Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2
  let coefficient : ℝ :=
    (2 * Real.sqrt dimension * Real.sqrt 2) * ratio ^
        (Nat.ceil (Real.logb 2 (8 * Real.sqrt dimension / radius)) + 1) /
      (ratio - 1)
  have hratio : 1 < ratio := by
    dsimp [ratio]
    exact dyadicSupercritical_ratio_gt_one dimension hdimension
  have hcoefficient : 0 ≤ coefficient := by
    dsimp [coefficient]
    exact div_nonneg (by positivity) (by linarith)
  have hbase := Math.div_sqrt_nat_le_quarter_of_sixteen_sq_le count hcount
    (coefficient := coefficient) hcoefficient hradius (by
      simpa [coefficient, ratio] using hcountBound)
  calc
    (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt count) *
          (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^
              (Nat.ceil (Real.logb 2 (8 * Real.sqrt dimension / radius)) + 1) /
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) =
        coefficient / Real.sqrt count := by
          dsimp [coefficient, ratio]
          ring
    _ ≤ radius / 4 := hbase

/--
The supercritical compact square-rate schedule with explicit logarithmic
depth and effective-count condition.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_sixtyFour_mul_dimension_of_dyadicDimensionGreaterTwo_explicitEffectiveCount
    (dimension : ℕ) (hdimension : 2 < dimension)
    (law : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (count : ℕ) (hcount : 0 < count)
    {radius : ℝ} (hradius : 0 < radius)
    (hcountBound :
      16 *
          ((2 * Real.sqrt dimension * Real.sqrt 2) *
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^
                (Nat.ceil (Real.logb 2 (8 * Real.sqrt dimension / radius)) + 1) /
              (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1)) ^ 2 ≤
        (count : ℝ) * radius ^ 2) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-((count : ℝ) * radius ^ 2 / (64 * dimension))) := by
  exact measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_sixtyFour_mul_dimension_of_dyadicDimensionGreaterTwo_logDepth
    dimension hdimension law count hcount hradius
    (dyadicDimensionGreaterTwo_mainTerm_le_quarter_of_effectiveCount
      dimension count hdimension hcount hradius.le hcountBound)

/--
The first fully inverted supercritical compact rate.  In dimension four, the
dyadic ratio is exactly two, so the logarithmic depth can be eliminated with
an explicit polynomial count gate.  In particular, `N * r^4 ≥ 2097152`
controls the multiscale term and leaves the exponential confidence tail
`exp (-N r² / 256)`.

This is a concrete `p = 1`, `d > 2` compact component of the
Fournier--Guillin rate calculation.  It uses the reusable logarithmic-cutoff
upper bracket `Math.pow_natCeil_logb_lt_mul`, whose Mathlib provenance is
recorded in `ExponentialBounds.lean`; no external Lean proof is copied.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_twoHundredFiftySix_of_dyadicDimensionFour_polynomialEffectiveCount
    (law : ProbabilityMeasure (HalfOpenUnitCube 4))
    (count : ℕ) (hcount : 0 < count)
    {radius : ℝ} (hradius : 0 < radius) (hradius_le : radius ≤ 16)
    (hcountBound : (2097152 : ℝ) ≤ (count : ℝ) * radius ^ 4) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-((count : ℝ) * radius ^ 2 / 256)) := by
  suffices h :
      (finiteIIDSampleLaw (law : Measure _) count).real {sample |
        ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
        Real.exp (-((count : ℝ) * radius ^ 2 / (64 * (4 : ℝ)))) by
    norm_num at h ⊢
    exact h
  apply measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_sixtyFour_mul_dimension_of_dyadicDimensionGreaterTwo
    4 (by norm_num) law count hcount
    (Nat.ceil (Real.logb 2 (8 * Real.sqrt 4 / radius))) hradius.le
    (dyadicDimensionGreaterTwo_terminalDepth_le_quarter 4 (by norm_num) hradius)
  have hthreshold : 1 ≤ 16 / radius := by
    exact (le_div_iff₀ hradius).2 (by linarith)
  have hpow : (2 : ℝ) ^ Nat.ceil (Real.logb 2 (16 / radius)) < 32 / radius := by
    calc
      (2 : ℝ) ^ Nat.ceil (Real.logb 2 (16 / radius)) < 2 * (16 / radius) :=
        Math.pow_natCeil_logb_lt_mul (by norm_num) hthreshold
      _ = 32 / radius := by ring
  have hpow_succ : (2 : ℝ) ^ (Nat.ceil (Real.logb 2 (16 / radius)) + 1) <
      64 / radius := by
    calc
      (2 : ℝ) ^ (Nat.ceil (Real.logb 2 (16 / radius)) + 1) =
          (2 : ℝ) ^ Nat.ceil (Real.logb 2 (16 / radius)) * 2 := by
            rw [pow_succ]
      _ < (32 / radius) * 2 := mul_lt_mul_of_pos_right hpow (by norm_num)
      _ = 64 / radius := by ring
  have hradius_sq_pos : 0 < radius ^ 2 := sq_pos_of_pos hradius
  have hsqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hmainCount :
      16 * (256 * Real.sqrt 2 / radius) ^ 2 ≤ (count : ℝ) * radius ^ 2 := by
    apply le_of_mul_le_mul_right _ hradius_sq_pos
    calc
      (16 * (256 * Real.sqrt 2 / radius) ^ 2) * radius ^ 2 = (2097152 : ℝ) := by
        field_simp
        nlinarith [hsqrt_two_sq]
      _ ≤ (count : ℝ) * radius ^ 4 := hcountBound
      _ = ((count : ℝ) * radius ^ 2) * radius ^ 2 := by ring
  have hdiv : (256 * Real.sqrt 2 / radius) / Real.sqrt count ≤ radius / 4 :=
    Math.div_sqrt_nat_le_quarter_of_sixteen_sq_le count hcount (by positivity)
      hradius.le hmainCount
  norm_num
  calc
    (4 * Real.sqrt 2 / Real.sqrt count) *
          (2 : ℝ) ^ (Nat.ceil (Real.logb 2 (16 / radius)) + 1) ≤
        (4 * Real.sqrt 2 / Real.sqrt count) * (64 / radius) := by
      exact mul_le_mul_of_nonneg_left hpow_succ.le (by positivity)
    _ = (256 * Real.sqrt 2 / radius) / Real.sqrt count := by ring
    _ ≤ radius / 4 := hdiv

/--
Confidence-form corollary of the explicit compact four-dimensional rate.  The
polynomial gate controls the dyadic approximation, while the displayed
quadratic gate spends a requested confidence exponent.
-/
theorem measure_empiricalWassersteinOne_gt_le_exp_neg_confidence_of_dyadicDimensionFour_polynomialEffectiveCount
    (law : ProbabilityMeasure (HalfOpenUnitCube 4))
    (count : ℕ) (hcount : 0 < count)
    {radius confidence : ℝ} (hradius : 0 < radius) (hradius_le : radius ≤ 16)
    (hcountBound : (2097152 : ℝ) ≤ (count : ℝ) * radius ^ 4)
    (hconfidenceBound : 256 * confidence ≤ (count : ℝ) * radius ^ 2) :
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
      ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
      Real.exp (-confidence) := by
  calc
    (finiteIIDSampleLaw (law : Measure _) count).real {sample |
        ENNReal.ofReal radius < empiricalWassersteinOne law hcount sample} ≤
        Real.exp (-((count : ℝ) * radius ^ 2 / 256)) :=
      measure_empiricalWassersteinOne_gt_le_exp_neg_count_mul_sq_div_twoHundredFiftySix_of_dyadicDimensionFour_polynomialEffectiveCount
        law count hcount hradius hradius_le hcountBound
    _ ≤ Real.exp (-confidence) := by
      apply Real.exp_le_exp.mpr
      have hconfidence : confidence ≤ (count : ℝ) * radius ^ 2 / 256 :=
        (le_div_iff₀ (by norm_num : (0 : ℝ) < 256)).2 (by
          simpa [mul_comm] using hconfidenceBound)
      linarith

/--
The global radial-collapse concentration bound with the geometric compact
confidence allocation made explicit.  The compact contribution is at most
`exp (-confidence)` independently of the finite dyadic depth; the remaining
term is the literal probability bound for an observation escaping the common
radius.  This is a global-cutoff result, not the sharper annular-shell
Fournier--Guillin estimate.
-/
theorem measure_finiteIID_empiricalWassersteinOne_gt_radialCollapseGeometricConfidenceBound_le
    (dimension : ℕ) (hdimension : 0 < dimension)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (count : ℕ) (hcount : 0 < count)
    {alpha gamma radius : ℝ} (halpha : 1 ≤ alpha) (hgamma : 0 < gamma)
    (hradius : 0 < radius) (hmoment : HasExponentialRadialMoment law alpha gamma)
    (depth : ℕ) (confidence : ℝ) (hconfidence : 0 ≤ confidence) :
    (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count).real
      {sample |
        ((NNReal.mk (2 * radius) (by positivity) : NNReal) : ℝ≥0∞) *
          ENNReal.ofReal (dyadicMultiscaleThresholdBound dimension depth
            (fun level ↦ dyadicGeometricConfidenceThreshold dimension count level confidence)) +
        ENNReal.ofReal ((1 + (gamma / 2)⁻¹) *
          Real.exp (-(gamma / 2) * Real.rpow radius alpha) *
          ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension)))) <
          empiricalWassersteinOne law hcount sample} ≤
      count * ∫ x : EuclideanSpace ℝ (Fin dimension),
        Real.exp (gamma * Real.rpow ‖x‖ alpha) /
          Real.exp (gamma * Real.rpow radius alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension))) +
        Real.exp (-confidence) := by
  refine (measure_finiteIID_empiricalWassersteinOne_gt_radialCollapseCompactBound_le_failureBudget
    dimension law count hcount halpha hgamma hradius hmoment depth
    (fun level ↦ dyadicGeometricConfidenceThreshold dimension count level confidence)
    (fun level ↦ dyadicGeometricConfidenceThreshold_nonneg dimension count level confidence)).trans ?_
  unfold finiteIIDRadialCollapseCompactFailureBudget
  apply add_le_add_right
  calc
    (∑ level ∈ Finset.range depth,
        (2 ^ (2 ^ (dimension * (level + 1))) : ℕ) *
          Real.exp (-((count : ℝ) *
            dyadicGeometricConfidenceThreshold dimension count (level + 1) confidence ^ 2) / 2)) ≤
        ∑ level ∈ Finset.range depth,
          Real.exp (-confidence) * (1 / 2 : ℝ) ^ (level + 1 + 1) := by
            refine Finset.sum_le_sum ?_
            intro level hlevel
            simpa [Nat.cast_add] using
              (dyadicGeometricConfidenceThreshold_numericalTail_le dimension count
                (level + 1) hdimension hcount confidence hconfidence)
    _ = Real.exp (-confidence) * ∑ level ∈ Finset.range depth,
          (1 / 2 : ℝ) ^ (level + 1 + 1) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-confidence) := by
          have hshift : (∑ level ∈ Finset.range depth,
              (1 / 2 : ℝ) ^ (level + 1 + 1)) ≤
              ∑ level ∈ Finset.range depth, (1 / 2 : ℝ) ^ (level + 1) := by
            apply Finset.sum_le_sum
            intro level hlevel
            apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
            omega
          simpa using mul_le_mul_of_nonneg_left
            (hshift.trans (sum_range_half_pow_succ_le_one depth)) (Real.exp_pos _).le


end
end Probability
end AppliedModelingLib
