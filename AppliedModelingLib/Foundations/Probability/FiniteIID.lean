import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Measure.Real
import AppliedModelingLib.Foundations.Probability.MeasureInequalities

/-!
# Canonical finite iid samples

This module represents a finite iid sample directly by the finite product
measure of its marginal law. It supplies the canonical coordinate model used
when a probability argument needs independent training and ghost samples on a
single product space.
-/

namespace AppliedModelingLib
namespace Probability

open MeasureTheory ProbabilityTheory

/-- The product law of `count` independent observations with common marginal `law`. -/
noncomputable def finiteIIDSampleLaw
    {X : Type*} [MeasurableSpace X] (law : Measure X) (count : ℕ) :
    Measure (Fin count → X) :=
  Measure.pi fun _ => law

/-- The `index`-th coordinate of a finite iid sample. -/
def finiteIIDSampleCoordinate
    {X : Type*} {count : ℕ} (index : Fin count) :
    (Fin count → X) → X :=
  fun sample => sample index

/-- Each coordinate projection of the finite product sample is measurable. -/
theorem measurable_finiteIIDSampleCoordinate
    {X : Type*} [MeasurableSpace X] {count : ℕ} (index : Fin count) :
    Measurable (finiteIIDSampleCoordinate (X := X) index) :=
  measurable_pi_apply index

/-- The coordinate process under the finite product law is independent. -/
theorem iIndepFun_finiteIIDSampleCoordinate
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) :
    iIndepFun (fun index : Fin count =>
      finiteIIDSampleCoordinate (X := X) index) (finiteIIDSampleLaw law count) := by
  letI : ∀ _ : Fin count, IsProbabilityMeasure law := fun _ => inferInstance
  simpa only [finiteIIDSampleLaw, finiteIIDSampleCoordinate] using
    (iIndepFun_pi (X := fun _ : Fin count => (id : X → X))
      (μ := fun _ : Fin count => law)
      (fun _ => measurable_id.aemeasurable))

/-- Every finite-product coordinate has the declared marginal law. -/
theorem map_finiteIIDSampleCoordinate
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law] (count : ℕ)
    (index : Fin count) :
    Measure.map (finiteIIDSampleCoordinate (X := X) index) (finiteIIDSampleLaw law count) = law := by
  letI : ∀ _ : Fin count, IsProbabilityMeasure law := fun _ => inferInstance
  exact (measurePreserving_eval (fun _ : Fin count => law) index).map_eq

/--
The MGF of a measurable Bernoulli indicator is its elementary two-point
formula.  This provides the one-coordinate input for product Chernoff bounds
without restricting the underlying observation space to a finite type.

Library provenance: this directly uses Mathlib's `integral_indicator_one` from
[`MeasureTheory/Integral/Bochner/Set.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Set.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem mgf_indicator_one_eq
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (cell : Set X) (hcell : MeasurableSet cell) (t : ℝ) :
    ProbabilityTheory.mgf (cell.indicator (fun _ : X => (1 : ℝ))) law t =
      1 + (Real.exp t - 1) * law.real cell := by
  let indicator : X → ℝ := cell.indicator (fun _ : X => (1 : ℝ))
  have hintegrable : Integrable indicator law := by
    exact (integrable_const (1 : ℝ)).integrableOn.integrable_indicator hcell
  have hpoint : (fun x => Real.exp (t * indicator x)) =
      fun x => 1 + (Real.exp t - 1) * indicator x := by
    funext x
    by_cases hx : x ∈ cell
    · simp [indicator, hx]
    · simp [indicator, hx]
  unfold ProbabilityTheory.mgf
  rw [hpoint, integral_add (integrable_const _) (hintegrable.const_mul _)]
  rw [integral_const, integral_const_mul]
  have hintegral : ∫ x, indicator x ∂law = law.real cell := by
    dsimp [indicator]
    exact integral_indicator_one hcell
  rw [hintegral]
  simp

/--
The moment-generating function of a measurable score sum over a finite iid
sample is the corresponding power of its one-observation MGF.  This is the
product-MGF bridge needed for multiplicative binomial/Chernoff bounds.

Library provenance: this directly uses Mathlib's
`ProbabilityTheory.iIndepFun.mgf_sum₀` from
[`Probability/Moments/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Moments/Basic.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem mgf_finiteIIDScoreSum_eq_pow
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (score : X → ℝ) (hscore : Measurable score) (t : ℝ) :
    ProbabilityTheory.mgf (fun sample : Fin count → X => ∑ index, score (sample index))
      (finiteIIDSampleLaw law count) t =
      (ProbabilityTheory.mgf score law t) ^ count := by
  classical
  let sampleLaw := finiteIIDSampleLaw law count
  let observation : Fin count → (Fin count → X) → ℝ :=
    fun index sample => score (sample index)
  have hindependent : iIndepFun observation sampleLaw := by
    simpa only [observation, finiteIIDSampleCoordinate, Function.comp_apply] using
      (iIndepFun_finiteIIDSampleCoordinate law count).comp
        (fun _ datum => score datum) (fun _ => hscore)
  have hmeasurable : ∀ index, Measurable (observation index) := by
    intro index
    exact hscore.comp (measurable_pi_apply index)
  have hmgf : ∀ index, ProbabilityTheory.mgf (observation index) sampleLaw t =
      ProbabilityTheory.mgf score law t := by
    intro index
    unfold ProbabilityTheory.mgf
    calc
      ∫ sample, Real.exp (t * observation index sample) ∂sampleLaw =
          ∫ x, Real.exp (t * score x) ∂Measure.map (fun sample => sample index) sampleLaw := by
        symm
        apply integral_map
        · exact (measurable_pi_apply index).aemeasurable
        · exact (measurable_const.mul hscore).exp.aestronglyMeasurable
      _ = ∫ x, Real.exp (t * score x) ∂law := by
        change ∫ x, Real.exp (t * score x) ∂
          Measure.map (finiteIIDSampleCoordinate index) (finiteIIDSampleLaw law count) = _
        rw [map_finiteIIDSampleCoordinate law count index]
  calc
    ProbabilityTheory.mgf (fun sample : Fin count → X => ∑ index, score (sample index))
        (finiteIIDSampleLaw law count) t =
        ∏ index, ProbabilityTheory.mgf (observation index) sampleLaw t :=
      by
        convert hindependent.mgf_sum₀
          (fun index => (hmeasurable index).aemeasurable) Finset.univ (t := t) using 1
        change ProbabilityTheory.mgf
            (fun sample : Fin count → X => ∑ index, score (sample index))
            (finiteIIDSampleLaw law count) t =
          ProbabilityTheory.mgf (∑ index, fun sample : Fin count → X => score (sample index))
            (finiteIIDSampleLaw law count) t
        apply congrArg (fun f : (Fin count → X) → ℝ =>
          ProbabilityTheory.mgf f (finiteIIDSampleLaw law count) t)
        funext sample
        simp only [Finset.sum_apply]
    _ = ∏ _index : Fin count, ProbabilityTheory.mgf score law t := by
      apply Finset.prod_congr rfl
      intro index _
      exact hmgf index
    _ = (ProbabilityTheory.mgf score law t) ^ count := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/--
The MGF of the number of finite-iid observations in a measurable cell has the
usual Bernoulli-product formula.  This is stated for an arbitrary measurable
space, so it can be reused for geometric shell counts and other measurable
partitions.
-/
theorem mgf_finiteIIDIndicatorSum_eq_pow
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell) (t : ℝ) :
    ProbabilityTheory.mgf
        (fun sample : Fin count → X =>
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index))
        (finiteIIDSampleLaw law count) t =
      (1 + (Real.exp t - 1) * law.real cell) ^ count := by
  rw [mgf_finiteIIDScoreSum_eq_pow law count
    (cell.indicator (fun _ : X => (1 : ℝ)))
    (measurable_const.indicator hcell) t]
  exact congrArg (fun value : ℝ => value ^ count)
    (mgf_indicator_one_eq law cell hcell t)

/-- A negative exponential of a finite iid measurable-cell count is integrable. -/
theorem integrable_exp_neg_mul_finiteIIDIndicatorSum
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable
      (fun sample : Fin count → X =>
        Real.exp ((-t) *
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)))
      (finiteIIDSampleLaw law count) := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law count) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  have hsum_measurable : Measurable
      (fun sample : Fin count → X =>
        ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)) := by
    apply Finset.measurable_sum
    intro index _
    exact (measurable_const.indicator hcell).comp (measurable_pi_apply index)
  have hsum_nonneg : ∀ sample : Fin count → X,
      0 ≤ ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) := by
    intro sample
    apply Finset.sum_nonneg
    intro index _
    exact Set.indicator_apply_nonneg (fun _ => zero_le_one)
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((measurable_const.mul hsum_measurable).exp.aestronglyMeasurable) ?_
  filter_upwards [] with sample
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (hsum_nonneg sample))

/-- A positive exponential of a finite iid measurable-cell count is integrable. -/
theorem integrable_exp_mul_finiteIIDIndicatorSum
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable
      (fun sample : Fin count → X =>
        Real.exp (t *
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)))
      (finiteIIDSampleLaw law count) := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law count) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  have hsum_measurable : Measurable
      (fun sample : Fin count → X =>
        ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)) := by
    apply Finset.measurable_sum
    intro index _
    exact (measurable_const.indicator hcell).comp (measurable_pi_apply index)
  have hsum_le_count : ∀ sample : Fin count → X,
      ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) ≤ count := by
    intro sample
    calc
      ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) ≤
          ∑ _index : Fin count, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro index _
        by_cases hmem : sample index ∈ cell <;> simp [hmem]
      _ = count := by simp
  refine Integrable.mono' (integrable_const (Real.exp (t * (count : ℝ))))
    ((measurable_const.mul hsum_measurable).exp.aestronglyMeasurable) ?_
  filter_upwards [] with sample
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (hsum_le_count sample) ht

/--
Chernoff's upper-tail bound for an arbitrary measurable-cell count in a
finite iid sample.  This is the counterpart of the negative-MGF lower tail
needed for the shell-mass discrepancy term of Fournier--Guillin Section 6.

Library provenance: this directly uses Mathlib's
`ProbabilityTheory.measure_ge_le_exp_mul_mgf` from
[`Probability/Moments/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Moments/Basic.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem measureReal_finiteIIDIndicatorSum_ge_chernoff
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (threshold t : ℝ) (ht : 0 ≤ t) :
    (finiteIIDSampleLaw law count).real
        {sample | threshold ≤
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} ≤
      Real.exp (-t * threshold) *
        (1 + (Real.exp t - 1) * law.real cell) ^ count := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law count) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  calc
    (finiteIIDSampleLaw law count).real
        {sample | threshold ≤
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} ≤
        Real.exp (-t * threshold) *
          ProbabilityTheory.mgf
            (fun sample : Fin count → X =>
              ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index))
            (finiteIIDSampleLaw law count) t := by
      exact ProbabilityTheory.measure_ge_le_exp_mul_mgf threshold ht
        (integrable_exp_mul_finiteIIDIndicatorSum law count cell hcell t ht)
    _ = Real.exp (-t * threshold) *
        (1 + (Real.exp t - 1) * law.real cell) ^ count := by
      rw [mgf_finiteIIDIndicatorSum_eq_pow law count cell hcell]

/--
The positive Bernoulli product MGF has the elementary exponential upper bound
used to turn the preceding Chernoff statement into a shell-mass-linear rate.
-/
theorem finiteIID_indicatorMGF_le_exp_pos_mul
    (count : ℕ) (probability t : ℝ)
    (hprobability_nonneg : 0 ≤ probability) (ht : 0 ≤ t) :
    (1 + (Real.exp t - 1) * probability) ^ count ≤
      Real.exp ((count : ℝ) * probability * (Real.exp t - 1)) := by
  let increment := (Real.exp t - 1) * probability
  have hincrement_nonneg : 0 ≤ increment := by
    exact mul_nonneg (sub_nonneg.mpr (Real.one_le_exp ht)) hprobability_nonneg
  have hbase : 1 + increment ≤ Real.exp increment := by
    simpa [add_comm] using Real.add_one_le_exp increment
  calc
    (1 + (Real.exp t - 1) * probability) ^ count = (1 + increment) ^ count := by
      rfl
    _ ≤ (Real.exp increment) ^ count :=
      pow_le_pow_left₀ (by linarith) hbase count
    _ = Real.exp ((count : ℝ) * increment) := by rw [Real.exp_nat_mul]
    _ = Real.exp ((count : ℝ) * probability * (Real.exp t - 1)) := by
      congr 1
      dsimp [increment]
      ring

/--
The explicit positive-MGF Chernoff bound for an arbitrary measurable-cell
count.  Its exponent is proportional to the cell mass, which is the form
needed for a dyadic shell allocation.
-/
theorem measureReal_finiteIIDIndicatorSum_ge_exp_chernoff
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (threshold t : ℝ) (ht : 0 ≤ t) :
    (finiteIIDSampleLaw law count).real
        {sample | threshold ≤
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} ≤
      Real.exp (-t * threshold +
        (count : ℝ) * law.real cell * (Real.exp t - 1)) := by
  calc
    (finiteIIDSampleLaw law count).real
        {sample | threshold ≤
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} ≤
        Real.exp (-t * threshold) *
          (1 + (Real.exp t - 1) * law.real cell) ^ count :=
      measureReal_finiteIIDIndicatorSum_ge_chernoff law count cell hcell threshold t ht
    _ ≤ Real.exp (-t * threshold) *
        Real.exp ((count : ℝ) * law.real cell * (Real.exp t - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (finiteIID_indicatorMGF_le_exp_pos_mul count (law.real cell) t
          measureReal_nonneg ht)
        (Real.exp_pos _).le
    _ = Real.exp (-t * threshold +
        (count : ℝ) * law.real cell * (Real.exp t - 1)) := by
      rw [← Real.exp_add]

/--
The upper relative-count form of the measurable-cell Chernoff bound.  Keeping
the parameter `t` explicit makes the source's later shell-dependent rate
optimization a separate numerical step.
-/
theorem measureReal_finiteIIDIndicatorSum_upperRelative_le_exp_chernoff
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (relative t : ℝ) (ht : 0 ≤ t) :
    (finiteIIDSampleLaw law count).real
        {sample | (count : ℝ) * law.real cell * (1 + relative) ≤
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} ≤
      Real.exp (-((count : ℝ) * law.real cell *
        (t * (1 + relative) - (Real.exp t - 1)))) := by
  calc
    (finiteIIDSampleLaw law count).real
        {sample | (count : ℝ) * law.real cell * (1 + relative) ≤
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} ≤
        Real.exp (-t * ((count : ℝ) * law.real cell * (1 + relative)) +
          (count : ℝ) * law.real cell * (Real.exp t - 1)) :=
      measureReal_finiteIIDIndicatorSum_ge_exp_chernoff law count cell hcell
        ((count : ℝ) * law.real cell * (1 + relative)) t ht
    _ = Real.exp (-((count : ℝ) * law.real cell *
        (t * (1 + relative) - (Real.exp t - 1)))) := by
      congr 1
      ring

/--
The optimized upper binomial Chernoff rate for an arbitrary measurable cell.
This is the large-deviation branch of Fournier--Guillin Lemma 12(a); unlike
the quadratic specialization, it remains informative when the relative error
exceeds two.

Library provenance: this directly uses Mathlib's `Real.log_nonneg` and
`Real.exp_log` from
[`Analysis/SpecialFunctions/Log/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem measureReal_finiteIIDIndicatorSum_upperRelative_le_exp_bennett
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (z : ℝ) (hz_nonneg : 0 ≤ z) :
    (finiteIIDSampleLaw law count).real
        {sample | (count : ℝ) * law.real cell * (1 + z) ≤
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} ≤
      Real.exp (-((count : ℝ) * law.real cell *
        ((1 + z) * Real.log (1 + z) - z))) := by
  have hbase_pos : 0 < 1 + z := by linarith
  have htilt_nonneg : 0 ≤ Real.log (1 + z) :=
    Real.log_nonneg (by linarith)
  calc
    (finiteIIDSampleLaw law count).real
        {sample | (count : ℝ) * law.real cell * (1 + z) ≤
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} ≤
        Real.exp (-((count : ℝ) * law.real cell *
          (Real.log (1 + z) * (1 + z) -
            (Real.exp (Real.log (1 + z)) - 1)))) :=
      measureReal_finiteIIDIndicatorSum_upperRelative_le_exp_chernoff
        law count cell hcell z (Real.log (1 + z)) htilt_nonneg
    _ = Real.exp (-((count : ℝ) * law.real cell *
        ((1 + z) * Real.log (1 + z) - z))) := by
      rw [Real.exp_log hbase_pos]
      congr 1
      ring

/--
Chernoff's lower-tail bound for the count of arbitrary measurable events in a
finite iid sample.  The free nonnegative parameter supports the relative-tail
optimization used by Wasserstein shell concentration arguments.
-/
theorem measureReal_finiteIIDIndicatorSum_le_chernoff
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (threshold t : ℝ) (ht : 0 ≤ t) :
    (finiteIIDSampleLaw law count).real
        {sample | ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) ≤ threshold} ≤
      Real.exp (t * threshold) *
        (1 + (Real.exp (-t) - 1) * law.real cell) ^ count := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law count) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  calc
    (finiteIIDSampleLaw law count).real
        {sample | ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) ≤ threshold} ≤
        Real.exp (-(-t) * threshold) *
          ProbabilityTheory.mgf
            (fun sample : Fin count → X =>
              ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index))
            (finiteIIDSampleLaw law count) (-t) := by
      exact ProbabilityTheory.measure_le_le_exp_mul_mgf threshold (neg_nonpos.mpr ht)
        (integrable_exp_neg_mul_finiteIIDIndicatorSum law count cell hcell t ht)
    _ = Real.exp (t * threshold) *
        (1 + (Real.exp (-t) - 1) * law.real cell) ^ count := by
      rw [mgf_finiteIIDIndicatorSum_eq_pow law count cell hcell]
      simp only [neg_neg]

/--
The Bernoulli product factor at a negative exponential parameter has the
shell-mass-linear exponential bound used in binomial concentration.
-/
theorem finiteIID_indicatorMGF_le_exp_neg_mul
    (count : ℕ) (probability t : ℝ)
    (hprobability_nonneg : 0 ≤ probability)
    (hprobability_le_one : probability ≤ 1)
    (ht : 0 ≤ t) :
    (1 + (Real.exp (-t) - 1) * probability) ^ count ≤
      Real.exp (-((count : ℝ) * probability * (1 - Real.exp (-t)))) := by
  let deviation : ℝ := probability * (1 - Real.exp (-t))
  have hexp_le_one : Real.exp (-t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have hdeviation_nonneg : 0 ≤ deviation := by
    exact mul_nonneg hprobability_nonneg (sub_nonneg.mpr hexp_le_one)
  have hdeviation_le_one : deviation ≤ 1 := by
    calc
      deviation ≤ probability * 1 := by
        apply mul_le_mul_of_nonneg_left
          (sub_le_self 1 (Real.exp_pos _).le)
        exact hprobability_nonneg
      _ ≤ 1 := by nlinarith
  have hfactor : 1 + (Real.exp (-t) - 1) * probability = 1 - deviation := by
    dsimp [deviation]
    ring
  rw [hfactor]
  by_cases hcount : count = 0
  · simp [hcount]
  have hcount_ne : (count : ℝ) ≠ 0 := by
    exact_mod_cast hcount
  have hscaled_le_count : (count : ℝ) * deviation ≤ count := by
    calc
      (count : ℝ) * deviation ≤ (count : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left hdeviation_le_one (Nat.cast_nonneg _)
      _ = count := by norm_num
  have hdiv : ((count : ℝ) * deviation) / count = deviation := by
    field_simp
  have hpower := Real.one_sub_div_pow_le_exp_neg
    (n := count) (t := (count : ℝ) * deviation) hscaled_le_count
  rw [hdiv] at hpower
  simpa only [deviation, mul_assoc] using hpower

/-- The fixed `theta = 1` Bernoulli exponent used in the selected-count tail is positive. -/
theorem zero_lt_half_sub_exp_neg_one : 0 < (1 / 2 : ℝ) - Real.exp (-1) :=
  sub_pos.mpr Real.exp_neg_one_lt_half

/--
For a unit-bounded nonnegative exponent, `1 - exp(-x)` retains at least half
of `x`.  This is the elementary numerical bridge from the exact binomial MGF
to the quadratic small-deviation exponent used in the source shell schedule.
-/
theorem half_mul_le_one_sub_exp_neg
    (x : ℝ) (hx_nonneg : 0 ≤ x) (hx_le_one : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have hdenom_pos : 0 < 1 + x := by linarith
  have hdenom_le_two : 1 + x ≤ 2 := by linarith
  have hinv : (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) hdenom_pos).mpr
      (by simpa [add_comm] using Real.add_one_le_exp x)
  have hratio : x / (1 + x) = 1 - (1 + x)⁻¹ := by
    field_simp [hdenom_pos.ne']
    ring
  calc
    x / 2 ≤ x / (1 + x) :=
      div_le_div_of_nonneg_left hx_nonneg hdenom_pos hdenom_le_two
    _ = 1 - (1 + x)⁻¹ := hratio
    _ ≤ 1 - (Real.exp x)⁻¹ := by linarith
    _ = 1 - Real.exp (-x) := by rw [Real.exp_neg]

/--
The quadratic form of `half_mul_le_one_sub_exp_neg` used when a shell
threshold lies in `[0, 1]`.
-/
theorem sq_div_four_le_one_sub_exp_neg_sq_div_two
    (z : ℝ) (hz_nonneg : 0 ≤ z) (hz_le_one : z ≤ 1) :
    z ^ 2 / 4 ≤ 1 - Real.exp (-(z ^ 2 / 2)) := by
  have hz_sq_le_one : z ^ 2 ≤ 1 := by
    simpa only [pow_two, mul_one] using mul_self_le_mul_self hz_nonneg hz_le_one
  have hrate_nonneg : 0 ≤ z ^ 2 / 2 := by positivity
  have hrate_le_one : z ^ 2 / 2 ≤ 1 := by nlinarith
  have hbase := half_mul_le_one_sub_exp_neg (z ^ 2 / 2) hrate_nonneg hrate_le_one
  nlinarith

/--
For a relative count deviation in `[0, 2]`, the positive exponential tilt
`t = z / 2` retains a quadratic rate.  This is the numerical small-deviation
case of the source's shell-count estimate.

Library provenance: this directly uses Mathlib's
`Real.abs_exp_sub_one_sub_id_le` from
[`Analysis/Complex/Exponential.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Complex/Exponential.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem sq_div_four_le_upperRelativeRate_half
    (z : ℝ) (hz_nonneg : 0 ≤ z) (hz_le_two : z ≤ 2) :
    z ^ 2 / 4 ≤ (z / 2) * (1 + z) - (Real.exp (z / 2) - 1) := by
  have harg_nonneg : 0 ≤ z / 2 := by linarith
  have harg_le_one : z / 2 ≤ 1 := by linarith
  have hremainder : Real.exp (z / 2) - 1 - z / 2 ≤ (z / 2) ^ 2 := by
    exact le_trans (le_abs_self _) (Real.abs_exp_sub_one_sub_id_le
      (by rw [abs_of_nonneg harg_nonneg]; exact harg_le_one))
  nlinarith

/--
For a relative count deviation in `[0, 2]`, the negative exponential tilt
`t = z / 2` retains the matching quadratic rate.  Together with the preceding
lemma this supplies the two-sided small-deviation regime for an arbitrary
measurable cell.

Library provenance: this directly uses Mathlib's
`Real.abs_exp_sub_one_sub_id_le` from
[`Analysis/Complex/Exponential.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Complex/Exponential.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem sq_div_four_le_lowerRelativeRate_half
    (z : ℝ) (hz_nonneg : 0 ≤ z) (hz_le_two : z ≤ 2) :
    z ^ 2 / 4 ≤ (1 - Real.exp (-(z / 2))) - (z / 2) * (1 - z) := by
  have harg_nonpos : -(z / 2) ≤ 0 := by linarith
  have harg_abs_le_one : |-(z / 2)| ≤ 1 := by
    rw [abs_of_nonpos harg_nonpos]
    linarith
  have hremainders : Real.exp (-(z / 2)) - 1 - (-(z / 2)) ≤ (-(z / 2)) ^ 2 := by
    exact le_trans (le_abs_self _) (Real.abs_exp_sub_one_sub_id_le harg_abs_le_one)
  nlinarith

/--
The source's binomial MGF estimate (Fournier--Guillin Lemma 12(c)) for an
arbitrary measurable-cell count in a finite iid sample.
-/
theorem mgf_finiteIIDIndicatorSum_neg_le_exp_neg_mul
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (t : ℝ) (ht : 0 ≤ t) :
    ProbabilityTheory.mgf
        (fun sample : Fin count → X =>
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index))
        (finiteIIDSampleLaw law count) (-t) ≤
      Real.exp (-((count : ℝ) * law.real cell * (1 - Real.exp (-t)))) := by
  rw [mgf_finiteIIDIndicatorSum_eq_pow law count cell hcell]
  exact finiteIID_indicatorMGF_le_exp_neg_mul count (law.real cell) t
    measureReal_nonneg measureReal_le_one ht

/--
The arbitrary-cell finite-iid count lower tail in exponential form.  Its
negative term is linear in the cell mass, as required for a summable dyadic
shell allocation.
-/
theorem measureReal_finiteIIDIndicatorSum_le_exp_chernoff
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (threshold t : ℝ) (ht : 0 ≤ t) :
    (finiteIIDSampleLaw law count).real
        {sample | ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) ≤ threshold} ≤
      Real.exp (t * threshold -
        (count : ℝ) * law.real cell * (1 - Real.exp (-t))) := by
  calc
    (finiteIIDSampleLaw law count).real
        {sample | ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) ≤ threshold} ≤
        Real.exp (t * threshold) *
          (1 + (Real.exp (-t) - 1) * law.real cell) ^ count :=
      measureReal_finiteIIDIndicatorSum_le_chernoff law count cell hcell threshold t ht
    _ ≤ Real.exp (t * threshold) *
        Real.exp (-((count : ℝ) * law.real cell * (1 - Real.exp (-t)))) := by
      exact mul_le_mul_of_nonneg_left
        (finiteIID_indicatorMGF_le_exp_neg_mul count (law.real cell) t
          measureReal_nonneg measureReal_le_one ht)
        (Real.exp_pos _).le
    _ = Real.exp (t * threshold -
        (count : ℝ) * law.real cell * (1 - Real.exp (-t))) := by
      rw [← Real.exp_add]
      ring

/--
The lower relative-count form of the measurable-cell Chernoff bound.  It is
the matching ingredient for the two-sided shell-mass discrepancy term.
-/
theorem measureReal_finiteIIDIndicatorSum_lowerRelative_le_exp_chernoff
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (relative t : ℝ) (ht : 0 ≤ t) :
    (finiteIIDSampleLaw law count).real
        {sample | ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) ≤
          (count : ℝ) * law.real cell * (1 - relative)} ≤
      Real.exp (-((count : ℝ) * law.real cell *
        ((1 - Real.exp (-t)) - t * (1 - relative)))) := by
  calc
    (finiteIIDSampleLaw law count).real
        {sample | ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) ≤
          (count : ℝ) * law.real cell * (1 - relative)} ≤
        Real.exp (t * ((count : ℝ) * law.real cell * (1 - relative)) -
          (count : ℝ) * law.real cell * (1 - Real.exp (-t))) :=
      measureReal_finiteIIDIndicatorSum_le_exp_chernoff law count cell hcell
        ((count : ℝ) * law.real cell * (1 - relative)) t ht
    _ = Real.exp (-((count : ℝ) * law.real cell *
        ((1 - Real.exp (-t)) - t * (1 - relative)))) := by
      congr 1
      ring

/--
The quadratic small-deviation upper tail for the count of an arbitrary
measurable cell in a finite iid sample.  The `z ≤ 1` gate is deliberate: it is
the source's small-deviation branch, to be combined later with a separate
large-deviation allocation.
-/
theorem measureReal_finiteIIDIndicatorSum_upperRelative_half_le_exp_quadratic
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (z : ℝ) (hz_nonneg : 0 ≤ z) (hz_le_two : z ≤ 2) :
    (finiteIIDSampleLaw law count).real
        {sample | (count : ℝ) * law.real cell * (1 + z) ≤
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} ≤
      Real.exp (-((count : ℝ) * law.real cell * (z ^ 2 / 4))) := by
  have hrate := sq_div_four_le_upperRelativeRate_half z hz_nonneg hz_le_two
  have hscale_nonneg : 0 ≤ (count : ℝ) * law.real cell := by positivity
  calc
    (finiteIIDSampleLaw law count).real
        {sample | (count : ℝ) * law.real cell * (1 + z) ≤
          ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} ≤
        Real.exp (-((count : ℝ) * law.real cell *
          ((z / 2) * (1 + z) - (Real.exp (z / 2) - 1)))) :=
      measureReal_finiteIIDIndicatorSum_upperRelative_le_exp_chernoff
        law count cell hcell z (z / 2) (by linarith)
    _ ≤ Real.exp (-((count : ℝ) * law.real cell * (z ^ 2 / 4))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hrate hscale_nonneg]

/--
The quadratic small-deviation lower tail for the count of an arbitrary
measurable cell in a finite iid sample.  Together with the matching upper
tail, this is the reusable two-sided building block for shell-mass errors.
-/
theorem measureReal_finiteIIDIndicatorSum_lowerRelative_half_le_exp_quadratic
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (z : ℝ) (hz_nonneg : 0 ≤ z) (hz_le_two : z ≤ 2) :
    (finiteIIDSampleLaw law count).real
        {sample | ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) ≤
          (count : ℝ) * law.real cell * (1 - z)} ≤
      Real.exp (-((count : ℝ) * law.real cell * (z ^ 2 / 4))) := by
  have hrate := sq_div_four_le_lowerRelativeRate_half z hz_nonneg hz_le_two
  have hscale_nonneg : 0 ≤ (count : ℝ) * law.real cell := by positivity
  calc
    (finiteIIDSampleLaw law count).real
        {sample | ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) ≤
          (count : ℝ) * law.real cell * (1 - z)} ≤
        Real.exp (-((count : ℝ) * law.real cell *
          ((1 - Real.exp (-(z / 2))) - (z / 2) * (1 - z)))) :=
      measureReal_finiteIIDIndicatorSum_lowerRelative_le_exp_chernoff
        law count cell hcell z (z / 2) (by linarith)
    _ ≤ Real.exp (-((count : ℝ) * law.real cell * (z ^ 2 / 4))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hrate hscale_nonneg]

/--
The literal two-sided relative count failure event for one measurable cell.
It is expressed at the count scale so that its shell specialization does not
introduce a division by a possibly zero source mass.
-/
def finiteIIDIndicatorSumRelativeTail
    {X : Type*} [MeasurableSpace X] (law : Measure X) (count : ℕ) (cell : Set X)
    (z : ℝ) : Set (Fin count → X) :=
  {sample | (count : ℝ) * law.real cell * z ≤
    |(∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)) -
      (count : ℝ) * law.real cell|}

/--
For a relative deviation strictly larger than one, the lower-tail part of the
absolute count event is impossible.  Thus the literal two-sided event is
contained in its upper binomial event, allowing the optimized Bennett rate.
-/
theorem finiteIIDIndicatorSumRelativeTail_subset_upperRelative_of_one_lt
    {X : Type*} [MeasurableSpace X] (law : Measure X) (count : ℕ) (cell : Set X)
    (z : ℝ) (hz : 1 < z) :
    finiteIIDIndicatorSumRelativeTail law count cell z ⊆
      {sample | (count : ℝ) * law.real cell * (1 + z) ≤
        ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} := by
  intro sample htail
  let total : ℝ := ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)
  let mean : ℝ := (count : ℝ) * law.real cell
  have htotal_nonneg : 0 ≤ total := by
    apply Finset.sum_nonneg
    intro index _
    exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hmean_nonneg : 0 ≤ mean := by
    dsimp [mean]
    positivity
  change mean * z ≤ |total - mean| at htail
  by_cases hmean_zero : mean = 0
  · change mean * (1 + z) ≤ total
    simpa [hmean_zero] using htotal_nonneg
  by_cases hmean_le_total : mean ≤ total
  · change mean * (1 + z) ≤ total
    rw [abs_of_nonneg (sub_nonneg.mpr hmean_le_total)] at htail
    linarith
  · have htotal_le_mean : total ≤ mean := le_of_not_ge hmean_le_total
    rw [abs_of_nonpos (sub_nonpos.mpr htotal_le_mean)] at htail
    have hmean_pos : 0 < mean := lt_of_le_of_ne hmean_nonneg (Ne.symm hmean_zero)
    exfalso
    nlinarith

/--
The literal large relative count failure receives the optimized Bennett
upper-tail rate.  This preserves the source's large-deviation branch instead
of replacing it prematurely by the coarser occupancy estimate.
-/
theorem measureReal_finiteIIDIndicatorSumRelativeTail_le_exp_bennett_of_one_lt
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (z : ℝ) (hz : 1 < z) :
    (finiteIIDSampleLaw law count).real
        (finiteIIDIndicatorSumRelativeTail law count cell z) ≤
      Real.exp (-((count : ℝ) * law.real cell *
        ((1 + z) * Real.log (1 + z) - z))) := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law count) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  calc
    (finiteIIDSampleLaw law count).real
        (finiteIIDIndicatorSumRelativeTail law count cell z) ≤
        (finiteIIDSampleLaw law count).real
          {sample | (count : ℝ) * law.real cell * (1 + z) ≤
            ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} :=
      measureReal_mono
        (finiteIIDIndicatorSumRelativeTail_subset_upperRelative_of_one_lt law count cell z hz)
        (measure_ne_top _ _)
    _ ≤ _ := measureReal_finiteIIDIndicatorSum_upperRelative_le_exp_bennett
      law count cell hcell z (by linarith)

/--
At a bounded but genuinely large relative deviation, the fixed Chernoff tilt
`t = 1` supplies a concrete quadratic envelope.  This fills the finite band
between the source's `z ≤ 2` quadratic branch and its logarithmic Bennett
branch, without weakening either endpoint statement.

Library provenance: the numerical estimate directly uses Mathlib's
`Real.exp_one_lt_three` from
[`Analysis/Complex/ExponentialBounds.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Complex/ExponentialBounds.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem sq_div_eighteen_le_upperRelativeRate_one_of_two_le_of_le_nine
    (z : ℝ) (hz_two : 2 ≤ z) (hz_nine : z ≤ 9) :
    z ^ 2 / 18 ≤ (1 : ℝ) * (1 + z) - (Real.exp 1 - 1) := by
  have hz_nonneg : 0 ≤ z := (by norm_num : (0 : ℝ) ≤ 2).trans hz_two
  have hsq : z ^ 2 ≤ 9 * z := by
    simpa [pow_two, mul_comm] using mul_le_mul_of_nonneg_left hz_nine hz_nonneg
  have hhalf : z / 2 ≤ z + 2 - Real.exp 1 := by
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    nlinarith
  nlinarith

/--
For `2 ≤ z ≤ 9`, the literal two-sided relative count event is already an
upper-tail event and has a usable quadratic Chernoff bound.  It is intended as
the finite middle band in a shell concentration argument.
-/
theorem measureReal_finiteIIDIndicatorSumRelativeTail_le_exp_quadratic_of_two_le_of_le_nine
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (z : ℝ) (hz_two : 2 ≤ z) (hz_nine : z ≤ 9) :
    (finiteIIDSampleLaw law count).real
        (finiteIIDIndicatorSumRelativeTail law count cell z) ≤
      Real.exp (-((count : ℝ) * law.real cell * (z ^ 2 / 18))) := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law count) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  have hrate := sq_div_eighteen_le_upperRelativeRate_one_of_two_le_of_le_nine
    z hz_two hz_nine
  have hscale_nonneg : 0 ≤ (count : ℝ) * law.real cell := by positivity
  calc
    (finiteIIDSampleLaw law count).real
        (finiteIIDIndicatorSumRelativeTail law count cell z) ≤
        (finiteIIDSampleLaw law count).real
          {sample | (count : ℝ) * law.real cell * (1 + z) ≤
            ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)} :=
      measureReal_mono
        (finiteIIDIndicatorSumRelativeTail_subset_upperRelative_of_one_lt law count cell z
          (by linarith))
        (measure_ne_top _ _)
    _ ≤ Real.exp (-((count : ℝ) * law.real cell *
        ((1 : ℝ) * (1 + z) - (Real.exp 1 - 1)))) :=
      measureReal_finiteIIDIndicatorSum_upperRelative_le_exp_chernoff
        law count cell hcell z 1 (by norm_num)
    _ ≤ Real.exp (-((count : ℝ) * law.real cell * (z ^ 2 / 18))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hrate hscale_nonneg]

/--
Beyond the bounded transition band, Bennett's rate dominates one half of
`z log z`.  This is the numerical entrance used by the genuinely large
relative-deviation shell allocation.

Library provenance: besides the already credited `Real.exp_one_lt_three`,
this directly uses Mathlib's `Real.le_log_iff_exp_le` and `Real.log_le_log`
from
[`Analysis/SpecialFunctions/Log/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem half_mul_mul_log_le_bennettRate_of_nine_le
    (z : ℝ) (hz_nine : 9 ≤ z) :
    (1 / 2 : ℝ) * z * Real.log z ≤ (1 + z) * Real.log (1 + z) - z := by
  have hz_pos : 0 < z := by linarith
  have hlogz_nonneg : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hexp_two_lt_nine : Real.exp 2 < 9 := by
    calc
      Real.exp 2 = Real.exp (1 + 1) := by norm_num
      _ = Real.exp 1 * Real.exp 1 := Real.exp_add _ _
      _ < 3 * Real.exp 1 :=
        mul_lt_mul_of_pos_right Real.exp_one_lt_three (Real.exp_pos _)
      _ < 3 * 3 := mul_lt_mul_of_pos_left Real.exp_one_lt_three (by norm_num)
      _ = 9 := by norm_num
  have hlogz_ge_two : 2 ≤ Real.log z :=
    (Real.le_log_iff_exp_le hz_pos).mpr (hexp_two_lt_nine.le.trans hz_nine)
  have hlog_mono : Real.log z ≤ Real.log (1 + z) :=
    Real.log_le_log hz_pos (by linarith)
  have hlog_one_add_nonneg : 0 ≤ Real.log (1 + z) :=
    Real.log_nonneg (by linarith)
  have hmul_log : z * Real.log z ≤ (1 + z) * Real.log (1 + z) := by
    calc
      z * Real.log z ≤ z * Real.log (1 + z) :=
        mul_le_mul_of_nonneg_left hlog_mono hz_pos.le
      _ ≤ (1 + z) * Real.log (1 + z) :=
        mul_le_mul_of_nonneg_right (by linarith) hlog_one_add_nonneg
  have hhalf : (1 / 2 : ℝ) * z * Real.log z ≤ z * Real.log z - z := by
    have hscaled : z * 2 ≤ z * Real.log z :=
      mul_le_mul_of_nonneg_left hlogz_ge_two hz_pos.le
    nlinarith
  exact hhalf.trans (sub_le_sub_right hmul_log z)

/--
The two-sided quadratic small-deviation bound for a measurable-cell count in a
finite iid sample.  This keeps the count-scale formulation required by the
zero-mass shell branch, while providing the exact exponential form used for
the Fournier--Guillin `Z_N` allocation.
-/
theorem measureReal_finiteIIDIndicatorSumRelativeTail_le_exp_quadratic
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (cell : Set X) (hcell : MeasurableSet cell)
    (z : ℝ) (hz_nonneg : 0 ≤ z) (hz_le_two : z ≤ 2) :
    (finiteIIDSampleLaw law count).real
        (finiteIIDIndicatorSumRelativeTail law count cell z) ≤
      2 * Real.exp (-((count : ℝ) * law.real cell * (z ^ 2 / 4))) := by
  let upper : Set (Fin count → X) := {sample |
    (count : ℝ) * law.real cell * (1 + z) ≤
      ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)}
  let lower : Set (Fin count → X) := {sample |
    ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) ≤
      (count : ℝ) * law.real cell * (1 - z)}
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law count) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  have hupper : (finiteIIDSampleLaw law count).real upper ≤
      Real.exp (-((count : ℝ) * law.real cell * (z ^ 2 / 4))) := by
    dsimp [upper]
    exact measureReal_finiteIIDIndicatorSum_upperRelative_half_le_exp_quadratic
      law count cell hcell z hz_nonneg hz_le_two
  have hlower : (finiteIIDSampleLaw law count).real lower ≤
      Real.exp (-((count : ℝ) * law.real cell * (z ^ 2 / 4))) := by
    dsimp [lower]
    exact measureReal_finiteIIDIndicatorSum_lowerRelative_half_le_exp_quadratic
      law count cell hcell z hz_nonneg hz_le_two
  have hsubset : finiteIIDIndicatorSumRelativeTail law count cell z ⊆ upper ∪ lower := by
    intro sample htail
    dsimp only [finiteIIDIndicatorSumRelativeTail] at htail
    change (count : ℝ) * law.real cell * z ≤
      |(∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index)) -
        (count : ℝ) * law.real cell| at htail
    rcases le_abs.mp htail with hupperTail | hlowerTail
    · left
      dsimp [upper]
      linarith
    · right
      dsimp [lower]
      linarith
  calc
    (finiteIIDSampleLaw law count).real
        (finiteIIDIndicatorSumRelativeTail law count cell z) ≤
        (finiteIIDSampleLaw law count).real (upper ∪ lower) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ (finiteIIDSampleLaw law count).real upper +
        (finiteIIDSampleLaw law count).real lower := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-((count : ℝ) * law.real cell * (z ^ 2 / 4)) ) := by
      nlinarith

/-- Apply a common map coordinatewise to a finite sample. -/
def finiteIIDSampleMap {X Y : Type*} {count : ℕ} (f : X → Y) :
    (Fin count → X) → Fin count → Y :=
  fun sample index => f (sample index)

/--
A coordinatewise map of finite samples is measurable when its point map is.

Library provenance: this uses Mathlib's `measurable_pi_lambda` and
`measurable_pi_apply` from
[`MeasureTheory/MeasurableSpace/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean),
at the pinned Apache-2.0 Mathlib commit. No source text is copied or ported.
-/
theorem measurable_finiteIIDSampleMap
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {count : ℕ} (f : X → Y) (hf : Measurable f) :
    Measurable (finiteIIDSampleMap (count := count) f) := by
  exact measurable_pi_lambda _ (fun index => hf.comp (measurable_pi_apply index))

/--
Applying a measurable map coordinatewise to a finite iid sample gives the
finite iid product law of the pushed-forward marginal.

Library provenance: this directly uses Mathlib's `Measure.pi_map_pi` from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Constructions/Pi.lean>.
The pinned source is Apache-2.0; no external Lean source is copied or ported.
-/
theorem map_finiteIIDSampleMap
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure X) [IsProbabilityMeasure law] (count : ℕ)
    (f : X → Y) (hf : Measurable f) :
    Measure.map (finiteIIDSampleMap f) (finiteIIDSampleLaw law count) =
      finiteIIDSampleLaw (Measure.map f law) count := by
  letI : ∀ _ : Fin count, IsProbabilityMeasure (Measure.map f law) := fun _ =>
    Measure.isProbabilityMeasure_map hf.aemeasurable
  simpa only [finiteIIDSampleMap, finiteIIDSampleLaw] using
    (Measure.pi_map_pi (μ := fun _ : Fin count => law) (fun _ => hf.aemeasurable))

/--
An exact pushforward-law identity transfers the real probability of every
measurable event to its preimage.

Library provenance: this is a thin use of Mathlib's `Measure.map_apply` from
[`MeasureTheory/Measure/Map.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Map.lean),
at the pinned Apache-2.0 Mathlib commit. No source text is copied or ported.
-/
theorem measureReal_preimage_eq_of_map_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) (f : X → Y) (hf : Measurable f)
    (nu : Measure Y) (hmap : Measure.map f mu = nu)
    (event : Set Y) (hevent : MeasurableSet event) :
    mu.real (f ⁻¹' event) = nu.real event := by
  unfold Measure.real
  rw [← hmap, Measure.map_apply hf hevent]

/--
The canonical finite iid sample has a union-bound tail for any coordinate
event. This is the reusable sample-side truncation bound used by empirical
Wasserstein reductions.
-/
theorem measure_finiteIID_exists_coordinate_mem_le
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (bad : Set X) (hbad : MeasurableSet bad) :
    (finiteIIDSampleLaw law count).real {sample | ∃ index, sample index ∈ bad} ≤
      count * law.real bad := by
  calc
    (finiteIIDSampleLaw law count).real {sample | ∃ index, sample index ∈ bad} ≤
        ∑ index ∈ (Finset.univ : Finset (Fin count)),
          measureProb (finiteIIDSampleLaw law count) (fun sample => sample index ∈ bad) := by
      simpa [measureProb] using
        (measureProb_biUnion_finset_le (μ := finiteIIDSampleLaw law count)
          (s := Finset.univ) (p := fun index sample => sample index ∈ bad))
    _ = ∑ index : Fin count, law.real bad := by
      apply Finset.sum_congr rfl
      intro index _
      change (finiteIIDSampleLaw law count).real {sample | sample index ∈ bad} = law.real bad
      change (finiteIIDSampleLaw law count).real
        ((finiteIIDSampleCoordinate (X := X) index) ⁻¹' bad) = law.real bad
      unfold Measure.real
      rw [← Measure.map_apply (measurable_finiteIIDSampleCoordinate index) hbad,
        map_finiteIIDSampleCoordinate law count index]
    _ = count * law.real bad := by simp

/--
The large-relative-deviation branch for an arbitrary positive-mass measurable
cell.  If `z > 1`, a relative-count failure cannot occur on a sample with no
observation in the cell, so its probability is at most the elementary
probability that one of the `count` observations enters the cell.  This is the
`N p` branch used for sparse outer shells in Fournier--Guillin Lemma 12(b).
-/
theorem measureReal_finiteIIDIndicatorSumRelativeTail_le_count_mul
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (hcount : 0 < count) (cell : Set X) (hcell : MeasurableSet cell)
    (z : ℝ) (hz_one_lt : 1 < z) (hcell_mass_pos : 0 < law.real cell) :
    (finiteIIDSampleLaw law count).real
        (finiteIIDIndicatorSumRelativeTail law count cell z) ≤
      count * law.real cell := by
  classical
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law count) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  let occupied : Set (Fin count → X) := {sample | ∃ index, sample index ∈ cell}
  have hscale_pos : 0 < (count : ℝ) * law.real cell := by positivity
  have hscale_nonneg : 0 ≤ (count : ℝ) * law.real cell := hscale_pos.le
  have hstrict : (count : ℝ) * law.real cell <
      (count : ℝ) * law.real cell * z := by
    simpa using (mul_lt_mul_of_pos_left hz_one_lt hscale_pos)
  have hsubset : finiteIIDIndicatorSumRelativeTail law count cell z ⊆ occupied := by
    intro sample htail
    by_contra hnotoccupied
    have hnotmem : ∀ index, sample index ∉ cell := by
      intro index hmem
      apply hnotoccupied
      exact ⟨index, hmem⟩
    have hsum_zero : ∑ index, cell.indicator (fun _ : X => (1 : ℝ)) (sample index) = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      simp [hnotmem index]
    dsimp [finiteIIDIndicatorSumRelativeTail] at htail
    rw [hsum_zero, abs_of_nonpos (by linarith)] at htail
    ring_nf at htail
    exact (not_le_of_gt hstrict) htail
  calc
    (finiteIIDSampleLaw law count).real
        (finiteIIDIndicatorSumRelativeTail law count cell z) ≤
        (finiteIIDSampleLaw law count).real occupied :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ count * law.real cell := by
      dsimp [occupied]
      exact measure_finiteIID_exists_coordinate_mem_le law count cell hcell

/-- Any two coordinates of a finite iid sample have the same distribution. -/
theorem identDistrib_finiteIIDSampleCoordinate
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law] (count : ℕ)
    (first second : Fin count) :
    IdentDistrib (finiteIIDSampleCoordinate (X := X) first)
      (finiteIIDSampleCoordinate (X := X) second)
      (finiteIIDSampleLaw law count) (finiteIIDSampleLaw law count) := by
  letI : ∀ _ : Fin count, IsProbabilityMeasure law := fun _ => inferInstance
  refine ⟨(measurable_finiteIIDSampleCoordinate first).aemeasurable,
    (measurable_finiteIIDSampleCoordinate second).aemeasurable, ?_⟩
  rw [map_finiteIIDSampleCoordinate law count first,
    map_finiteIIDSampleCoordinate law count second]

/--
Every finite coordinate permutation preserves the canonical iid product law.
The measurable equivalence is written in Mathlib's reindexing direction: its
value at `permutation index` is the original value at `index`.
-/
theorem measurePreserving_finiteIIDSampleReindex
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (permutation : Fin count ≃ Fin count) :
    MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin count => X) permutation)
      (finiteIIDSampleLaw law count) (finiteIIDSampleLaw law count) := by
  letI : ∀ _ : Fin count, SigmaFinite law := fun _ => inferInstance
  simpa only [finiteIIDSampleLaw] using
    (measurePreserving_piCongrLeft (fun _ : Fin count => law) permutation)

/-- The first `count` coordinates of a `2 * count` iid sample. -/
def finiteIIDTrainSample
    {X : Type*} (count : ℕ) :
    (Fin (count + count) → X) → Fin count → X :=
  fun sample index => sample (Fin.castAdd count index)

/-- The last `count` coordinates of a `2 * count` iid sample. -/
def finiteIIDGhostSample
    {X : Type*} (count : ℕ) :
    (Fin (count + count) → X) → Fin count → X :=
  fun sample index => sample (Fin.natAdd count index)

/--
The measurable equivalence that splits a canonical `2 * count` sample into
its training and ghost halves.
-/
noncomputable def finiteIIDTrainGhostSplitEquiv
    {X : Type*} [MeasurableSpace X] (count : ℕ) :
    (Fin (count + count) → X) ≃ᵐ (Fin count → X) × (Fin count → X) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (count + count) => X) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin count ⊕ Fin count => X))

/-- The left component of the split equivalence is the training half. -/
theorem finiteIIDTrainGhostSplitEquiv_fst
    {X : Type*} [MeasurableSpace X] (count : ℕ) (sample : Fin (count + count) → X) :
    (finiteIIDTrainGhostSplitEquiv (X := X) count sample).1 =
      finiteIIDTrainSample count sample := by
  rfl

/-- The right component of the split equivalence is the ghost half. -/
theorem finiteIIDTrainGhostSplitEquiv_snd
    {X : Type*} [MeasurableSpace X] (count : ℕ) (sample : Fin (count + count) → X) :
    (finiteIIDTrainGhostSplitEquiv (X := X) count sample).2 =
      finiteIIDGhostSample count sample := by
  rfl

/--
Under the canonical iid law, the train/ghost split has the product of two
independent `count`-sample iid laws.
-/
theorem measurePreserving_finiteIIDTrainGhostSplit
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) :
    MeasurePreserving (finiteIIDTrainGhostSplitEquiv (X := X) count)
      (finiteIIDSampleLaw law (count + count))
      ((finiteIIDSampleLaw law count).prod (finiteIIDSampleLaw law count)) := by
  letI : ∀ _ : Fin (count + count), SigmaFinite law := fun _ => inferInstance
  letI : ∀ _ : Fin count ⊕ Fin count, SigmaFinite law := fun _ => inferInstance
  simpa only [finiteIIDTrainGhostSplitEquiv, finiteIIDSampleLaw] using
    (measurePreserving_sumPiEquivProdPi (fun _ : Fin count ⊕ Fin count => law)).comp
      ((measurePreserving_piCongrLeft (fun _ : Fin (count + count) => law)
        finSumFinEquiv).symm)

/-- A coordinate of the two halves of a finite iid sample. -/
def finiteIIDTrainGhostCoordinate
    {X : Type*} (count : ℕ) (side : Fin count ⊕ Fin count) :
    (Fin (count + count) → X) → X :=
  match side with
  | Sum.inl index => fun sample => finiteIIDTrainSample count sample index
  | Sum.inr index => fun sample => finiteIIDGhostSample count sample index

/-- Each coordinate in the training/ghost split is measurable. -/
theorem measurable_finiteIIDTrainGhostCoordinate
    {X : Type*} [MeasurableSpace X] (count : ℕ) (side : Fin count ⊕ Fin count) :
    Measurable (finiteIIDTrainGhostCoordinate (X := X) count side) := by
  rcases side with index | index
  · exact measurable_pi_apply _
  · exact measurable_pi_apply _

/--
The coordinates of the training and ghost halves form one independent family
under the `2 * count` product law.  This is the product-space iid premise for
two-sample symmetrization.
-/
theorem iIndepFun_finiteIIDTrainGhostCoordinates
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) :
    iIndepFun (finiteIIDTrainGhostCoordinate (X := X) count)
      (finiteIIDSampleLaw law (count + count)) := by
  have hcoordinates :
      (fun side : Fin count ⊕ Fin count =>
        finiteIIDSampleCoordinate (X := X) (finSumFinEquiv side)) =
        finiteIIDTrainGhostCoordinate (X := X) count := by
    funext side sample
    rcases side with index | index <;> rfl
  rw [← hcoordinates]
  exact (iIndepFun_finiteIIDSampleCoordinate law (count + count)).precomp
    finSumFinEquiv.injective

/-- Each training-half coordinate has the declared iid marginal law. -/
theorem map_finiteIIDTrainSampleCoordinate
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (index : Fin count) :
    Measure.map (fun sample => finiteIIDTrainSample (X := X) count sample index)
      (finiteIIDSampleLaw law (count + count)) = law := by
  simpa only [finiteIIDTrainSample] using
    (map_finiteIIDSampleCoordinate law (count + count) (Fin.castAdd count index))

/-- Each ghost-half coordinate has the declared iid marginal law. -/
theorem map_finiteIIDGhostSampleCoordinate
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (index : Fin count) :
    Measure.map (fun sample => finiteIIDGhostSample (X := X) count sample index)
      (finiteIIDSampleLaw law (count + count)) = law := by
  simpa only [finiteIIDGhostSample] using
    (map_finiteIIDSampleCoordinate law (count + count) (Fin.natAdd count index))

/-- Every coordinate in the training/ghost split has the declared marginal law. -/
theorem map_finiteIIDTrainGhostCoordinate
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (side : Fin count ⊕ Fin count) :
    Measure.map (finiteIIDTrainGhostCoordinate (X := X) count side)
      (finiteIIDSampleLaw law (count + count)) = law := by
  rcases side with index | index
  · exact map_finiteIIDTrainSampleCoordinate law count index
  · exact map_finiteIIDGhostSampleCoordinate law count index

/--
A uniform bound on all sections of a measurable event transfers unchanged to
the event under the product of two probability measures.  This is the
Fubini/Tonelli step used by finite-sample symmetrization arguments.
-/
theorem measure_prod_event_le_of_forall_section_le
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (event : Set (Ω × Ξ)) (hevent : MeasurableSet event) (bound : ENNReal)
    (hsection : ∀ outcome, ν {auxiliary | (outcome, auxiliary) ∈ event} ≤ bound) :
    μ.prod ν event ≤ bound := by
  rw [Measure.prod_apply hevent]
  calc
    ∫⁻ outcome, ν {auxiliary | (outcome, auxiliary) ∈ event} ∂μ ≤
        ∫⁻ _ : Ω, bound ∂μ :=
      lintegral_mono fun outcome => hsection outcome
    _ = bound := by simp [lintegral_const]

/--
The real-valued probability form of
`measure_prod_event_le_of_forall_section_le`.  It is convenient when a tail
bound is naturally stated using `Measure.real`.
-/
theorem measureReal_prod_event_le_of_forall_section_le
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (event : Set (Ω × Ξ)) (hevent : MeasurableSet event)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hsection : ∀ outcome, ν.real {auxiliary | (outcome, auxiliary) ∈ event} ≤ bound) :
    (μ.prod ν).real event ≤ bound := by
  have hsection' : ∀ outcome, ν {auxiliary | (outcome, auxiliary) ∈ event} ≤
      ENNReal.ofReal bound := by
    intro outcome
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hsection outcome)
  have hproduct := measure_prod_event_le_of_forall_section_le μ ν event hevent
    (ENNReal.ofReal bound) hsection'
  change (μ.prod ν event).toReal ≤ bound
  rw [← ENNReal.toReal_ofReal hbound]
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hproduct

/--
A measurable product event has probability at least a constant times the
probability of any set on which all of its right-hand sections have at least
that constant probability.  This is the lower-bound Fubini step used in
ghost-sample symmetrization.
-/
theorem mul_measure_le_measure_prod_event_of_forall_section_le
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (event : Set (Ω × Ξ)) (hevent : MeasurableSet event)
    (support : Set Ω) (hsupport : MeasurableSet support) (lowerBound : ENNReal)
    (hsection : ∀ outcome ∈ support,
      lowerBound ≤ ν {auxiliary | (outcome, auxiliary) ∈ event}) :
    lowerBound * μ support ≤ μ.prod ν event := by
  rw [Measure.prod_apply hevent]
  calc
    lowerBound * μ support = ∫⁻ _ in support, lowerBound ∂μ :=
      (setLIntegral_const support lowerBound).symm
    _ = ∫⁻ outcome, support.indicator (fun _ => lowerBound) outcome ∂μ := by
      rw [lintegral_indicator hsupport]
    _ ≤ ∫⁻ outcome, ν {auxiliary | (outcome, auxiliary) ∈ event} ∂μ := by
      apply lintegral_mono
      intro outcome
      by_cases houtcome : outcome ∈ support
      · simpa [Set.indicator, houtcome] using hsection outcome houtcome
      · simp [Set.indicator, houtcome]

/--
The real-valued probability form of
`mul_measure_le_measure_prod_event_of_forall_section_le`.

This is the Fubini lower-bound bridge used when a bad first sample guarantees
a fixed favorable probability for the independent ghost-sample section.
-/
theorem mul_measureReal_le_measureReal_prod_event_of_forall_section_le
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (event : Set (Ω × Ξ)) (hevent : MeasurableSet event)
    (support : Set Ω) (hsupport : MeasurableSet support) (lowerBound : ℝ)
    (hlowerBound : 0 ≤ lowerBound)
    (hsection : ∀ outcome ∈ support,
      lowerBound ≤ ν.real {auxiliary | (outcome, auxiliary) ∈ event}) :
    lowerBound * μ.real support ≤ (μ.prod ν).real event := by
  have hsection' : ∀ outcome ∈ support,
      ENNReal.ofReal lowerBound ≤ ν {auxiliary | (outcome, auxiliary) ∈ event} := by
    intro outcome houtcome
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hsection outcome houtcome)
  have hproduct := mul_measure_le_measure_prod_event_of_forall_section_le
    μ ν event hevent support hsupport (ENNReal.ofReal lowerBound) hsection'
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlowerBound] using
    (ENNReal.toReal_mono (measure_ne_top _ _) hproduct)

/-!
## Selected observations under a fixed membership pattern

The shell-resampling step for empirical measures conditions a finite iid
sample on a fixed pattern of membership in a measurable set.  The following
definitions and theorems make that conditional product structure available
without tying it to a particular empirical-Wasserstein argument.
-/

noncomputable section

/-- The event that exactly the coordinates in `inside` lie in `s`. -/
def finiteIIDMembershipPattern {X : Type*} [MeasurableSpace X]
    (count : ℕ) (inside : Finset (Fin count)) (s : Set X) :
    Set (Fin count → X) :=
  ⋂ index, finiteIIDSampleCoordinate index ⁻¹'
    (if index ∈ inside then s else sᶜ)

/--
Every finite-IID membership pattern of a measurable event is measurable.

Library provenance: this uses Mathlib's `MeasurableSet.iInter` from
[`MeasureTheory/MeasurableSpace/Defs.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean)
and `MeasurableSet.preimage` from
[`MeasureTheory/MeasurableSpace/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/MeasurableSpace/Basic.lean),
at the pinned Apache-2.0 Mathlib commit. No source text is copied or ported.
-/
theorem measurableSet_finiteIIDMembershipPattern
    {X : Type*} [MeasurableSpace X]
    (count : ℕ) (inside : Finset (Fin count)) (s : Set X) (hs : MeasurableSet s) :
    MeasurableSet (finiteIIDMembershipPattern count inside s) := by
  unfold finiteIIDMembershipPattern
  apply MeasurableSet.iInter
  intro index
  by_cases hinside : index ∈ inside
  · simpa [hinside] using hs.preimage (measurable_finiteIIDSampleCoordinate index)
  · simpa [hinside] using hs.compl.preimage (measurable_finiteIIDSampleCoordinate index)

/--
A finite iid membership pattern has positive mass exactly when every one of
its coordinate events has positive mass.  The result is deliberately stated
for a nonzero measure rather than as a conditional-probability identity: it
is the branch criterion needed before applying the fixed-pattern conditional
iid law.

Library provenance: this uses Mathlib's `Measure.pi_pi` from
[`MeasureTheory/Constructions/Pi.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Constructions/Pi.lean)
and `Finset.prod_ne_zero_iff` from
[`Algebra/BigOperators/GroupWithZero/Finset.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/BigOperators/GroupWithZero/Finset.lean),
at the pinned Apache-2.0 Mathlib commit. No source text is copied or ported.
-/
theorem finiteIIDMembershipPattern_measure_ne_zero_iff
    {X : Type*} [MeasurableSpace X]
    (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (inside : Finset (Fin count)) (s : Set X) :
    (finiteIIDSampleLaw law count)
      (finiteIIDMembershipPattern count inside s) ≠ 0 ↔
      ∀ index : Fin count, law (if index ∈ inside then s else sᶜ) ≠ 0 := by
  let coordinate : Fin count → (Fin count → X) → X :=
    finiteIIDSampleCoordinate
  let conditionSet : Fin count → Set X := fun index =>
    if index ∈ inside then s else sᶜ
  change (finiteIIDSampleLaw law count)
      (⋂ index, coordinate index ⁻¹' conditionSet index) ≠ 0 ↔ _
  rw [show (⋂ index, coordinate index ⁻¹' conditionSet index) =
      Set.univ.pi conditionSet by
        ext sample
        simp [coordinate, finiteIIDSampleCoordinate]]
  change (Measure.pi fun _ : Fin count => law) (Set.univ.pi conditionSet) ≠ 0 ↔ _
  rw [Measure.pi_pi]
  constructor
  · intro hproduct index
    simpa [conditionSet] using
      (Finset.prod_ne_zero_iff.mp hproduct index (Finset.mem_univ index))
  · intro hpositive
    apply Finset.prod_ne_zero_iff.mpr
    intro index _
    simpa [conditionSet] using hpositive index

/-- Distinct finite membership patterns are disjoint. -/
theorem pairwiseDisjoint_finiteIIDMembershipPattern
    {X : Type*} [MeasurableSpace X] (count : ℕ) (s : Set X) :
    Set.PairwiseDisjoint (Set.univ : Set (Finset (Fin count)))
      (fun inside => finiteIIDMembershipPattern count inside s) := by
  classical
  intro first _ second _ hne
  change Disjoint (finiteIIDMembershipPattern count first s)
    (finiteIIDMembershipPattern count second s)
  rw [Set.disjoint_left]
  intro sample hfirst hsecond
  have hdiff : ∃ index : Fin count,
      (index ∈ first ∧ index ∉ second) ∨ (index ∈ second ∧ index ∉ first) := by
    by_contra hno
    apply hne
    ext index
    constructor
    · intro hfirst_mem
      by_contra hsecond_mem
      apply hno
      exact ⟨index, Or.inl ⟨hfirst_mem, hsecond_mem⟩⟩
    · intro hsecond_mem
      by_contra hfirst_mem
      apply hno
      exact ⟨index, Or.inr ⟨hsecond_mem, hfirst_mem⟩⟩
  rcases hdiff with ⟨index, hfirst_second | hsecond_first⟩
  · have hfirst_index : sample index ∈ s := by
      unfold finiteIIDMembershipPattern at hfirst
      simpa [finiteIIDSampleCoordinate, hfirst_second.1] using
        (Set.mem_iInter.mp hfirst index)
    have hsecond_index : sample index ∉ s := by
      unfold finiteIIDMembershipPattern at hsecond
      simpa [finiteIIDSampleCoordinate, hfirst_second.2] using
        (Set.mem_iInter.mp hsecond index)
    exact hsecond_index hfirst_index
  · have hsecond_index : sample index ∈ s := by
      unfold finiteIIDMembershipPattern at hsecond
      simpa [finiteIIDSampleCoordinate, hsecond_first.1] using
        (Set.mem_iInter.mp hsecond index)
    have hfirst_index : sample index ∉ s := by
      unfold finiteIIDMembershipPattern at hfirst
      simpa [finiteIIDSampleCoordinate, hsecond_first.2] using
        (Set.mem_iInter.mp hfirst index)
    exact hfirst_index hsecond_index

/-- Every finite sample has one and only one in/out membership pattern. -/
theorem iUnion_finiteIIDMembershipPattern_eq_univ
    {X : Type*} [MeasurableSpace X] (count : ℕ) (s : Set X) :
    (⋃ inside : Finset (Fin count), finiteIIDMembershipPattern count inside s) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro sample
  let inside : Finset (Fin count) := Finset.univ.filter (fun index => sample index ∈ s)
  refine Set.mem_iUnion.2 ⟨inside, ?_⟩
  unfold finiteIIDMembershipPattern
  apply Set.mem_iInter.2
  intro index
  by_cases hsample : sample index ∈ s <;>
    simp [inside, finiteIIDSampleCoordinate, hsample]

/--
The probabilities of all finite in/out membership patterns add to one.

Library provenance: this uses Mathlib's `measureReal_biUnion_finset` from
[`MeasureTheory/Measure/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Real.lean),
at the pinned Apache-2.0 Mathlib commit. No source text is copied or ported.
-/
theorem sum_measureReal_finiteIIDMembershipPattern_eq_one
    {X : Type*} [MeasurableSpace X]
    (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (s : Set X) (hs : MeasurableSet s) :
    ∑ inside : Finset (Fin count),
      (finiteIIDSampleLaw law count).real
        (finiteIIDMembershipPattern count inside s) = 1 := by
  let sampleLaw := finiteIIDSampleLaw law count
  let pattern := fun inside : Finset (Fin count) =>
    finiteIIDMembershipPattern count inside s
  letI : IsProbabilityMeasure sampleLaw := by
    dsimp [sampleLaw, finiteIIDSampleLaw]
    infer_instance
  have hdisjoint : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Finset (Fin count)))) pattern := by
    simpa only [Finset.coe_univ] using
      (pairwiseDisjoint_finiteIIDMembershipPattern count s)
  have hmeasurable : ∀ inside ∈ (Finset.univ : Finset (Finset (Fin count))),
      MeasurableSet (pattern inside) := by
    intro inside _
    exact measurableSet_finiteIIDMembershipPattern count inside s hs
  have hcover : (⋃ inside ∈ (Finset.univ : Finset (Finset (Fin count))),
      pattern inside) = Set.univ := by
    simpa only [Finset.mem_univ, Set.iUnion_true] using
      (iUnion_finiteIIDMembershipPattern_eq_univ count s)
  calc
    ∑ inside : Finset (Fin count), sampleLaw.real (pattern inside) =
        sampleLaw.real (⋃ inside ∈ (Finset.univ : Finset (Finset (Fin count))),
          pattern inside) := by
      symm
      simpa only [Finset.mem_univ, Set.iUnion_true] using
        (measureReal_biUnion_finset (μ := sampleLaw) hdisjoint hmeasurable)
    _ = sampleLaw.real Set.univ := by rw [hcover]
    _ = 1 := by simp

/--
The exponential of a measurable-cell count is constant on each realized
membership-pattern fiber.  Consequently, the pattern-mass-weighted exponential
sum is exactly the product-law MGF of that count.  This is the averaging step
behind conditional binomial shell estimates.

Library provenance: this directly uses Mathlib's `integral_biUnion_finset` and
`setIntegral_const` from
[`MeasureTheory/Integral/Bochner/Set.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Set.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem sum_measureReal_finiteIIDMembershipPattern_mul_exp_card_eq_mgf
    {X : Type*} [MeasurableSpace X]
    (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (s : Set X) (hs : MeasurableSet s) (t : ℝ) (ht : 0 ≤ t) :
    ∑ inside : Finset (Fin count),
      (finiteIIDSampleLaw law count).real
        (finiteIIDMembershipPattern count inside s) *
        Real.exp (-t * (inside.card : ℝ)) =
      ProbabilityTheory.mgf
        (fun sample : Fin count → X =>
          ∑ index, s.indicator (fun _ : X => (1 : ℝ)) (sample index))
        (finiteIIDSampleLaw law count) (-t) := by
  classical
  let sampleLaw := finiteIIDSampleLaw law count
  let pattern := fun inside : Finset (Fin count) =>
    finiteIIDMembershipPattern count inside s
  let scoreSum : (Fin count → X) → ℝ := fun sample =>
    ∑ index, s.indicator (fun _ : X => (1 : ℝ)) (sample index)
  let exponential : (Fin count → X) → ℝ := fun sample => Real.exp (-t * scoreSum sample)
  letI : IsProbabilityMeasure sampleLaw := by
    dsimp [sampleLaw, finiteIIDSampleLaw]
    infer_instance
  have hdisjoint : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Finset (Fin count)))) pattern := by
    simpa only [Finset.coe_univ] using
      (pairwiseDisjoint_finiteIIDMembershipPattern count s)
  have hmeasurable : ∀ inside ∈ (Finset.univ : Finset (Finset (Fin count))),
      MeasurableSet (pattern inside) := by
    intro inside _
    exact measurableSet_finiteIIDMembershipPattern count inside s hs
  have hcover : (⋃ inside ∈ (Finset.univ : Finset (Finset (Fin count))),
      pattern inside) = Set.univ := by
    simpa only [Finset.mem_univ, Set.iUnion_true] using
      (iUnion_finiteIIDMembershipPattern_eq_univ count s)
  have hintegrable : Integrable exponential sampleLaw := by
    dsimp [exponential, scoreSum, sampleLaw]
    exact integrable_exp_neg_mul_finiteIIDIndicatorSum law count s hs t ht
  have hsum_on_pattern : ∀ (inside : Finset (Fin count)) (sample : Fin count → X),
      sample ∈ pattern inside → scoreSum sample = inside.card := by
    intro inside sample hsample
    unfold pattern finiteIIDMembershipPattern at hsample
    dsimp [scoreSum]
    calc
      ∑ index, s.indicator (fun _ : X => (1 : ℝ)) (sample index) =
          ∑ index, if index ∈ inside then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro index _
        have hindex := Set.mem_iInter.mp hsample index
        by_cases hinside : index ∈ inside
        · have hsample_mem : sample index ∈ s := by
            simpa [finiteIIDSampleCoordinate, hinside] using hindex
          simp [hsample_mem, hinside]
        · have hsample_not_mem : sample index ∉ s := by
            simpa [finiteIIDSampleCoordinate, hinside] using hindex
          simp [hsample_not_mem, hinside]
      _ = inside.card := by
        rw [Finset.sum_boole]
        simp
  have hsetIntegral : ∀ inside : Finset (Fin count),
      ∫ sample in pattern inside, exponential sample ∂sampleLaw =
        sampleLaw.real (pattern inside) * Real.exp (-t * (inside.card : ℝ)) := by
    intro inside
    calc
      ∫ sample in pattern inside, exponential sample ∂sampleLaw =
          ∫ _ in pattern inside, Real.exp (-t * (inside.card : ℝ)) ∂sampleLaw := by
        apply setIntegral_congr_fun (hmeasurable inside (Finset.mem_univ _))
        intro sample hsample
        dsimp [exponential]
        rw [hsum_on_pattern inside sample hsample]
      _ = sampleLaw.real (pattern inside) * Real.exp (-t * (inside.card : ℝ)) := by
        rw [setIntegral_const]
        simp only [smul_eq_mul]
  have hintegral_union : ∫ sample, exponential sample ∂sampleLaw =
      ∑ inside : Finset (Fin count), ∫ sample in pattern inside, exponential sample ∂sampleLaw := by
    calc
      ∫ sample, exponential sample ∂sampleLaw =
          ∫ sample in (⋃ inside ∈ (Finset.univ : Finset (Finset (Fin count))), pattern inside),
            exponential sample ∂sampleLaw := by rw [hcover, setIntegral_univ]
      _ = ∑ inside ∈ (Finset.univ : Finset (Finset (Fin count))),
          ∫ sample in pattern inside, exponential sample ∂sampleLaw :=
        integral_biUnion_finset (Finset.univ : Finset (Finset (Fin count))) hmeasurable
          hdisjoint (fun _ _ => hintegrable.integrableOn)
      _ = ∑ inside : Finset (Fin count),
          ∫ sample in pattern inside, exponential sample ∂sampleLaw := by
        simp
  calc
    ∑ inside : Finset (Fin count),
        (finiteIIDSampleLaw law count).real
          (finiteIIDMembershipPattern count inside s) *
          Real.exp (-t * (inside.card : ℝ)) =
        ∑ inside : Finset (Fin count),
          ∫ sample in pattern inside, exponential sample ∂sampleLaw := by
      apply Finset.sum_congr rfl
      intro inside _
      exact (hsetIntegral inside).symm
    _ = ∫ sample, exponential sample ∂sampleLaw := hintegral_union.symm
    _ = ProbabilityTheory.mgf
        (fun sample : Fin count → X =>
          ∑ index, s.indicator (fun _ : X => (1 : ℝ)) (sample index))
        (finiteIIDSampleLaw law count) (-t) := by
      rfl

/--
Aggregate membership-pattern conditional tails whose factor decays
exponentially in the selected cardinality.  The pattern-weighted factor is
computed by the measurable-cell-count MGF, so this argument pays neither a
union-bound factor nor a separate low-count event.
-/
theorem measureReal_iUnion_finiteIIDMembershipPattern_inter_le_mul_mgf
    {X : Type*} [MeasurableSpace X]
    (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (s : Set X) (hs : MeasurableSet s)
    (tail : Finset (Fin count) → Set (Fin count → X))
    (htail : ∀ inside, MeasurableSet (tail inside))
    (coefficient t : ℝ) (ht : 0 ≤ t)
    (hbound : ∀ inside,
      (finiteIIDSampleLaw law count).real
        (finiteIIDMembershipPattern count inside s ∩ tail inside) ≤
        coefficient * Real.exp (-t * (inside.card : ℝ)) *
          (finiteIIDSampleLaw law count).real
            (finiteIIDMembershipPattern count inside s)) :
    (finiteIIDSampleLaw law count).real
      (⋃ inside : Finset (Fin count),
        finiteIIDMembershipPattern count inside s ∩ tail inside) ≤
      coefficient * ProbabilityTheory.mgf
        (fun sample : Fin count → X =>
          ∑ index, s.indicator (fun _ : X => (1 : ℝ)) (sample index))
        (finiteIIDSampleLaw law count) (-t) := by
  classical
  let sampleLaw := finiteIIDSampleLaw law count
  let pattern := fun inside : Finset (Fin count) =>
    finiteIIDMembershipPattern count inside s
  let tailUnion : Set (Fin count → X) :=
    ⋃ inside : Finset (Fin count), pattern inside ∩ tail inside
  letI : IsProbabilityMeasure sampleLaw := by
    dsimp [sampleLaw, finiteIIDSampleLaw]
    infer_instance
  have hdisjoint : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Finset (Fin count))))
      (fun inside => pattern inside ∩ tail inside) := by
    intro first hfirst second hsecond hne
    exact ((pairwiseDisjoint_finiteIIDMembershipPattern count s)
      (Set.mem_univ first) (Set.mem_univ second) hne).mono
        Set.inter_subset_left Set.inter_subset_left
  have hmeasurable : ∀ inside ∈ (Finset.univ : Finset (Finset (Fin count))),
      MeasurableSet (pattern inside ∩ tail inside) := by
    intro inside _
    exact (measurableSet_finiteIIDMembershipPattern count inside s hs).inter (htail inside)
  have hunion : sampleLaw.real tailUnion =
      ∑ inside : Finset (Fin count), sampleLaw.real (pattern inside ∩ tail inside) := by
    unfold tailUnion
    simpa only [Finset.mem_univ, Set.iUnion_true] using
      (measureReal_biUnion_finset (μ := sampleLaw) hdisjoint hmeasurable)
  calc
    (finiteIIDSampleLaw law count).real
        (⋃ inside : Finset (Fin count),
          finiteIIDMembershipPattern count inside s ∩ tail inside) =
        ∑ inside : Finset (Fin count), sampleLaw.real (pattern inside ∩ tail inside) := by
      exact hunion
    _ ≤ ∑ inside : Finset (Fin count),
        coefficient * Real.exp (-t * (inside.card : ℝ)) * sampleLaw.real (pattern inside) := by
      apply Finset.sum_le_sum
      intro inside _
      exact hbound inside
    _ = coefficient * ∑ inside : Finset (Fin count),
        sampleLaw.real (pattern inside) * Real.exp (-t * (inside.card : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro inside _
      ring
    _ = coefficient * ProbabilityTheory.mgf
        (fun sample : Fin count → X =>
          ∑ index, s.indicator (fun _ : X => (1 : ℝ)) (sample index))
        (finiteIIDSampleLaw law count) (-t) := by
      rw [sum_measureReal_finiteIIDMembershipPattern_mul_exp_card_eq_mgf
        law count s hs t ht]

/--
Aggregate pattern-dependent tail events without paying for the number of
patterns. Every pattern failing `good` is charged to `low`; on good patterns,
a uniform conditional tail factor is averaged against the pattern masses,
whose total is one.

Library provenance: this uses Mathlib's `measureReal_biUnion_finset` from
[`MeasureTheory/Measure/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Real.lean)
and `Finset.sum_le_sum_of_subset_of_nonneg` from
[`Algebra/Order/BigOperators/Group/Finset.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean),
at the pinned Apache-2.0 Mathlib commit. No source text is copied or ported.
-/
theorem measureReal_iUnion_finiteIIDMembershipPattern_inter_le_add_of_uniform_tail
    {X : Type*} [MeasurableSpace X]
    (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (s : Set X) (hs : MeasurableSet s)
    (tail : Finset (Fin count) → Set (Fin count → X))
    (htail : ∀ inside, MeasurableSet (tail inside))
    (low : Set (Fin count → X)) (good : Finset (Fin count) → Prop)
    (hbad : ∀ inside, ¬ good inside →
      finiteIIDMembershipPattern count inside s ∩ tail inside ⊆ low)
    (q : ℝ) (hq : 0 ≤ q)
    (hgood : ∀ inside, good inside →
      (finiteIIDSampleLaw law count).real
        (finiteIIDMembershipPattern count inside s ∩ tail inside) ≤
        q * (finiteIIDSampleLaw law count).real
          (finiteIIDMembershipPattern count inside s)) :
    (finiteIIDSampleLaw law count).real
      (⋃ inside : Finset (Fin count),
        finiteIIDMembershipPattern count inside s ∩ tail inside) ≤
      (finiteIIDSampleLaw law count).real low + q := by
  classical
  let sampleLaw := finiteIIDSampleLaw law count
  let pattern := fun inside : Finset (Fin count) =>
    finiteIIDMembershipPattern count inside s
  let goodInside : Finset (Finset (Fin count)) := Finset.univ.filter good
  let goodTail : Set (Fin count → X) :=
    ⋃ inside ∈ goodInside, pattern inside ∩ tail inside
  letI : IsProbabilityMeasure sampleLaw := by
    dsimp [sampleLaw, finiteIIDSampleLaw]
    infer_instance
  have hsubset : (⋃ inside : Finset (Fin count), pattern inside ∩ tail inside) ⊆
      low ∪ goodTail := by
    intro sample hsample
    rcases Set.mem_iUnion.mp hsample with ⟨inside, hsample⟩
    by_cases hgood_inside : good inside
    · change sample ∈ low ∨ sample ∈ goodTail
      right
      unfold goodTail
      refine Set.mem_iUnion.2 ⟨inside, ?_⟩
      refine Set.mem_iUnion.2 ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hgood_inside⟩, ?_⟩
      exact hsample
    · change sample ∈ low ∨ sample ∈ goodTail
      left
      exact hbad inside hgood_inside hsample
  have hgood_disjoint : Set.PairwiseDisjoint (↑goodInside)
      (fun inside => pattern inside ∩ tail inside) := by
    intro first hfirst second hsecond hne
    exact ((pairwiseDisjoint_finiteIIDMembershipPattern count s)
      (Set.mem_univ first) (Set.mem_univ second) hne).mono
        Set.inter_subset_left Set.inter_subset_left
  have hgood_measurable : ∀ inside ∈ goodInside,
      MeasurableSet (pattern inside ∩ tail inside) := by
    intro inside _
    exact (measurableSet_finiteIIDMembershipPattern count inside s hs).inter (htail inside)
  have hgood_union : sampleLaw.real goodTail =
      ∑ inside ∈ goodInside, sampleLaw.real (pattern inside ∩ tail inside) := by
    unfold goodTail
    exact measureReal_biUnion_finset hgood_disjoint hgood_measurable
  have hpattern_sum : ∑ inside : Finset (Fin count),
      sampleLaw.real (pattern inside) = 1 := by
    dsimp [sampleLaw, pattern]
    exact sum_measureReal_finiteIIDMembershipPattern_eq_one law count s hs
  have hgood_weight_sum : ∑ inside ∈ goodInside,
      q * sampleLaw.real (pattern inside) ≤ q := by
    calc
      ∑ inside ∈ goodInside, q * sampleLaw.real (pattern inside) ≤
          ∑ inside : Finset (Fin count), q * sampleLaw.real (pattern inside) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro inside _ _
          exact mul_nonneg hq measureReal_nonneg
      _ = q * ∑ inside : Finset (Fin count), sampleLaw.real (pattern inside) := by
        rw [Finset.mul_sum]
      _ = q := by rw [hpattern_sum, mul_one]
  have hgood_tail : sampleLaw.real goodTail ≤ q := by
    rw [hgood_union]
    calc
      ∑ inside ∈ goodInside, sampleLaw.real (pattern inside ∩ tail inside) ≤
          ∑ inside ∈ goodInside, q * sampleLaw.real (pattern inside) := by
        apply Finset.sum_le_sum
        intro inside hinside
        exact hgood inside (Finset.mem_filter.mp hinside).2
      _ ≤ q := hgood_weight_sum
  change sampleLaw.real (⋃ inside : Finset (Fin count),
      pattern inside ∩ tail inside) ≤ sampleLaw.real low + q
  calc
    sampleLaw.real (⋃ inside : Finset (Fin count), pattern inside ∩ tail inside) ≤
        sampleLaw.real (low ∪ goodTail) := measureReal_mono hsubset
    _ ≤ sampleLaw.real low + sampleLaw.real goodTail :=
      measureReal_union_le low goodTail
    _ ≤ sampleLaw.real low + q := by
      simpa only [add_comm] using add_le_add_left hgood_tail (sampleLaw.real low)

/-- Restrict a finite sample to the coordinates selected by a finset. -/
def finiteIIDSampleOnFinset {X : Type*} {count : ℕ} (inside : Finset (Fin count)) :
    (Fin count → X) → ({index : Fin count // index ∈ inside} → X) :=
  fun sample index => sample index

/--
Enumerate the coordinates selected by a finset as `Fin inside.card`, using
Mathlib's canonical finite-type enumeration.  This is the version of a
selected sample that can be supplied to a fixed-length iid result.

Library provenance: `Fintype.equivFin` and `Fintype.card_coe` are from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Fintype/EquivFin.lean>,
and `finCongr` is from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Fin/SuccPred.lean>.
These pinned Mathlib sources are Apache-2.0; no upstream Lean source is
copied or ported.
-/
def finiteIIDSampleOnFinsetToFin {X : Type*} {count : ℕ} (inside : Finset (Fin count)) :
    (Fin count → X) → Fin inside.card → X :=
  fun sample index => finiteIIDSampleOnFinset inside sample
    (((finCongr (Fintype.card_coe inside).symm).trans
      (Fintype.equivFin {index : Fin count // index ∈ inside}).symm) index)

/-- The canonical finite enumeration of a selected sample is measurable. -/
theorem measurable_finiteIIDSampleOnFinsetToFin
    {X : Type*} [MeasurableSpace X] {count : ℕ} (inside : Finset (Fin count)) :
    Measurable (finiteIIDSampleOnFinsetToFin inside :
      (Fin count → X) → Fin inside.card → X) := by
  refine measurable_pi_lambda _ ?_
  intro index
  simpa [finiteIIDSampleOnFinsetToFin, finiteIIDSampleOnFinset] using
    (measurable_finiteIIDSampleCoordinate
      (((finCongr (Fintype.card_coe inside).symm).trans
        (Fintype.equivFin {index : Fin count // index ∈ inside}).symm) index).1)

/--
Given a fixed positive coordinatewise membership pattern, the selected
coordinates remain independent under the conditioned finite iid law.

Library provenance: this uses Mathlib's
`ProbabilityTheory.iIndepFun.cond` and `iIndepFun.precomp` from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Independence/Basic.lean>.
The pinned Mathlib commit is `5450b53e5ddc75d46418fabb605edbf36bd0beb6`,
under Apache-2.0; no upstream Lean source is copied or ported here.
-/
theorem iIndepFun_finiteIIDSampleOnFinset_conditioned
    {X : Type*} [MeasurableSpace X]
    (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (inside : Finset (Fin count)) (s : Set X)
    (hs : MeasurableSet s)
    (hpos : ∀ index : Fin count,
      law (if index ∈ inside then s else sᶜ) ≠ 0) :
    iIndepFun (fun index sample => finiteIIDSampleOnFinset inside sample index)
      ((finiteIIDSampleLaw law count)[|finiteIIDMembershipPattern count inside s]) := by
  let coordinate : Fin count → (Fin count → X) → X :=
    finiteIIDSampleCoordinate
  let conditionSet : Fin count → Set X := fun index =>
    if index ∈ inside then s else sᶜ
  have hconditionSet : ∀ index, MeasurableSet (conditionSet index) := by
    intro index
    by_cases hindex : index ∈ inside <;> simp [conditionSet, hindex, hs]
  have hpairs : iIndepFun (fun index sample =>
      (coordinate index sample, coordinate index sample))
      (finiteIIDSampleLaw law count) := by
    simpa only [coordinate, finiteIIDSampleCoordinate, Function.comp_apply] using
      (iIndepFun_finiteIIDSampleCoordinate law count).comp
        (fun _ value => (value, value))
        (fun _ => measurable_id.prodMk measurable_id)
  have hconditioned : iIndepFun coordinate
      ((finiteIIDSampleLaw law count)[|⋂ index, coordinate index ⁻¹' conditionSet index]) := by
    apply ProbabilityTheory.iIndepFun.cond
      (fun index => measurable_finiteIIDSampleCoordinate index)
      hpairs
    · intro index
      rw [← Measure.map_apply (measurable_finiteIIDSampleCoordinate index)
        (hconditionSet index), map_finiteIIDSampleCoordinate law count index]
      simpa [conditionSet] using hpos index
    · exact hconditionSet
  have hselected := ProbabilityTheory.iIndepFun.precomp
    (g := fun index : {index : Fin count // index ∈ inside} => index.1)
    Subtype.val_injective hconditioned
  simpa only [finiteIIDMembershipPattern, finiteIIDSampleOnFinset,
    coordinate, conditionSet, finiteIIDSampleCoordinate] using hselected

/--
Under a fixed positive membership pattern, every selected coordinate has the
source law conditioned on membership in `s`.

Library provenance: the finite conditional-event factorization is Mathlib's
`ProbabilityTheory.cond_iInter` from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Independence/Basic.lean>,
and the conditional-law evaluation is `ProbabilityTheory.cond_apply` from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ConditionalProbability.lean>.
Both modules are covered by Mathlib's Apache-2.0 license at the pinned commit;
no upstream source is copied or ported.
-/
theorem map_finiteIIDSampleOnFinsetCoordinate_conditioned
    {X : Type*} [MeasurableSpace X]
    (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (inside : Finset (Fin count)) (s : Set X)
    (hs : MeasurableSet s)
    (hpos : ∀ index : Fin count,
      law (if index ∈ inside then s else sᶜ) ≠ 0)
    (index : {index : Fin count // index ∈ inside}) :
    Measure.map (fun sample => finiteIIDSampleOnFinset inside sample index)
      ((finiteIIDSampleLaw law count)[|finiteIIDMembershipPattern count inside s]) =
      law[|s] := by
  let coordinate : Fin count → (Fin count → X) → X :=
    finiteIIDSampleCoordinate
  let conditionSet : Fin count → Set X := fun current =>
    if current ∈ inside then s else sᶜ
  have hconditionSet : ∀ current, MeasurableSet (conditionSet current) := by
    intro current
    by_cases hcurrent : current ∈ inside <;> simp [conditionSet, hcurrent, hs]
  have hpairs : iIndepFun (fun current sample =>
      (coordinate current sample, coordinate current sample))
      (finiteIIDSampleLaw law count) := by
    simpa only [coordinate, finiteIIDSampleCoordinate, Function.comp_apply] using
      (iIndepFun_finiteIIDSampleCoordinate law count).comp
        (fun _ value => (value, value))
        (fun _ => measurable_id.prodMk measurable_id)
  have hcoordinatePreimage_ne : ∀ current,
      (finiteIIDSampleLaw law count)
        (coordinate current ⁻¹' conditionSet current) ≠ 0 := by
    intro current
    rw [← Measure.map_apply (measurable_finiteIIDSampleCoordinate current)
      (hconditionSet current), map_finiteIIDSampleCoordinate law count current]
    simpa [coordinate, conditionSet] using hpos current
  apply Measure.ext
  intro t ht
  have hselected_measurable : Measurable
      (fun sample : Fin count → X => finiteIIDSampleOnFinset inside sample index) := by
    simpa [finiteIIDSampleOnFinset] using
      (measurable_finiteIIDSampleCoordinate index.1)
  rw [Measure.map_apply hselected_measurable ht]
  let f : Fin count → Set (Fin count → X) := fun current =>
      if current = index.1 then coordinate current ⁻¹' t else Set.univ
  have hf : ∀ current ∈ ({index.1} : Finset (Fin count)),
      MeasurableSet[MeasurableSpace.comap (coordinate current)
        (inferInstance : MeasurableSpace X)] (f current) := by
    intro current hcurrent
    have hcurrent_eq : current = index.1 := Finset.mem_singleton.mp hcurrent
    subst current
    apply MeasurableSpace.measurableSet_comap.mpr
    refine ⟨t, ht, ?_⟩
    simp [f]
  have hcond := ProbabilityTheory.cond_iInter
      (X := coordinate) (Y := coordinate) (t := conditionSet)
      (s := ({index.1} : Finset (Fin count)))
      (fun current => measurable_finiteIIDSampleCoordinate current)
      hpairs hf
      (fun current _ => hcoordinatePreimage_ne current)
      hconditionSet
  have hleft : (⋂ current ∈ ({index.1} : Finset (Fin count)), f current) =
      coordinate index.1 ⁻¹' t := by
    simp [f]
  rw [hleft] at hcond
  have hcoordinate_condition :
      (finiteIIDSampleLaw law count)[coordinate index.1 ⁻¹' t |
        coordinate index.1 ⁻¹' s] = law[t | s] := by
    rw [ProbabilityTheory.cond_apply
        (measurable_finiteIIDSampleCoordinate index.1 hs),
      ProbabilityTheory.cond_apply hs]
    have hmass : (finiteIIDSampleLaw law count) (coordinate index.1 ⁻¹' s) = law s := by
      rw [← Measure.map_apply (measurable_finiteIIDSampleCoordinate index.1) hs,
        map_finiteIIDSampleCoordinate law count index.1]
    have hinter : (finiteIIDSampleLaw law count)
        (coordinate index.1 ⁻¹' s ∩ coordinate index.1 ⁻¹' t) = law (s ∩ t) := by
      rw [show coordinate index.1 ⁻¹' s ∩ coordinate index.1 ⁻¹' t =
          coordinate index.1 ⁻¹' (s ∩ t) by ext sample; simp]
      rw [← Measure.map_apply (measurable_finiteIIDSampleCoordinate index.1) (hs.inter ht),
        map_finiteIIDSampleCoordinate law count index.1]
    rw [hmass, hinter]
  change (finiteIIDSampleLaw law count)[coordinate index.1 ⁻¹' t |
    ⋂ current, coordinate current ⁻¹' conditionSet current] =
      law[t | s]
  rw [hcond]
  simpa [f, conditionSet, index.property] using hcoordinate_condition

/--
The selected finite sample under a fixed positive membership pattern has the
finite product law of the source law conditioned on membership in `s`.

Library provenance: this assembles the two preceding conditional-IID facts
using Mathlib's `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map` from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Independence/Basic.lean>
and `ProbabilityTheory.cond_isProbabilityMeasure` from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ConditionalProbability.lean>.
The exact pinned Mathlib source is Apache-2.0; no external Lean source is
imported, copied, or ported.
-/
theorem map_finiteIIDSampleOnFinset_conditioned
    {X : Type*} [MeasurableSpace X]
    (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (inside : Finset (Fin count)) (s : Set X)
    (hs : MeasurableSet s)
    (hpos : ∀ index : Fin count,
      law (if index ∈ inside then s else sᶜ) ≠ 0) :
    Measure.map (finiteIIDSampleOnFinset inside)
      ((finiteIIDSampleLaw law count)[|finiteIIDMembershipPattern count inside s]) =
      Measure.pi (fun _ : {index : Fin count // index ∈ inside} => law[|s]) := by
  let coordinate : Fin count → (Fin count → X) → X :=
    finiteIIDSampleCoordinate
  let conditionSet : Fin count → Set X := fun index =>
    if index ∈ inside then s else sᶜ
  have hconditionSet : ∀ index, MeasurableSet (conditionSet index) := by
    intro index
    by_cases hindex : index ∈ inside <;> simp [conditionSet, hindex, hs]
  letI : IsFiniteMeasure (finiteIIDSampleLaw law count) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  have hpattern_ne : (finiteIIDSampleLaw law count)
      (finiteIIDMembershipPattern count inside s) ≠ 0 := by
    change (finiteIIDSampleLaw law count)
      (⋂ index, coordinate index ⁻¹' conditionSet index) ≠ 0
    rw [show (⋂ index, coordinate index ⁻¹' conditionSet index) =
      Set.univ.pi conditionSet by ext sample; simp [coordinate, finiteIIDSampleCoordinate]]
    change (Measure.pi fun _ : Fin count => law) (Set.univ.pi conditionSet) ≠ 0
    rw [Measure.pi_pi]
    apply Finset.prod_ne_zero_iff.mpr
    intro index _
    simpa [conditionSet] using hpos index
  letI : IsProbabilityMeasure
      ((finiteIIDSampleLaw law count)[|finiteIIDMembershipPattern count inside s]) :=
    ProbabilityTheory.cond_isProbabilityMeasure hpattern_ne
  have hindependent := iIndepFun_finiteIIDSampleOnFinset_conditioned
    law count inside s hs hpos
  have hmeasurable : ∀ index : {index : Fin count // index ∈ inside},
      Measurable (fun sample : Fin count → X => finiteIIDSampleOnFinset inside sample index) := by
    intro index
    simpa [finiteIIDSampleOnFinset] using
      (measurable_finiteIIDSampleCoordinate index.1)
  have hproduct := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun index => (hmeasurable index).aemeasurable)).mp hindependent
  calc
    Measure.map (finiteIIDSampleOnFinset inside)
        ((finiteIIDSampleLaw law count)[|finiteIIDMembershipPattern count inside s]) =
      Measure.pi (fun index => Measure.map
        (fun sample => finiteIIDSampleOnFinset inside sample index)
        ((finiteIIDSampleLaw law count)[|finiteIIDMembershipPattern count inside s])) := by
          simpa [finiteIIDSampleOnFinset] using hproduct
    _ = Measure.pi (fun _ : {index : Fin count // index ∈ inside} => law[|s]) := by
      congr 1
      funext index
      exact map_finiteIIDSampleOnFinsetCoordinate_conditioned law count inside s hs hpos index

/--
Conditioning an iid finite sample on a fixed positive membership pattern,
then enumerating its selected coordinates, gives an iid sample from the
conditional law and of exactly the selected cardinality.

Library provenance: `MeasurableEquiv.piCongrLeft` and
`Measure.pi_map_piCongrLeft` are from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Constructions/Pi.lean>.
The pinned Mathlib source is Apache-2.0; this proof only invokes its public
APIs and does not copy or port external Lean source.
-/
theorem map_finiteIIDSampleOnFinsetToFin_conditioned
    {X : Type*} [MeasurableSpace X]
    (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (inside : Finset (Fin count)) (s : Set X)
    (hs : MeasurableSet s)
    (hpos : ∀ index : Fin count,
      law (if index ∈ inside then s else sᶜ) ≠ 0) :
    Measure.map (finiteIIDSampleOnFinsetToFin inside)
      ((finiteIIDSampleLaw law count)[|finiteIIDMembershipPattern count inside s]) =
      finiteIIDSampleLaw (law[|s]) inside.card := by
  let subtype := {index : Fin count // index ∈ inside}
  let indexEquiv : Fin inside.card ≃ subtype :=
    (finCongr (Fintype.card_coe inside).symm).trans (Fintype.equivFin subtype).symm
  let reindex : (Fin inside.card → X) ≃ᵐ (subtype → X) :=
    MeasurableEquiv.piCongrLeft (fun _ : subtype => X) indexEquiv
  have hproduct := map_finiteIIDSampleOnFinset_conditioned law count inside s hs hpos
  have hselected : Measurable
      (finiteIIDSampleOnFinset inside : (Fin count → X) → subtype → X) := by
    exact measurable_pi_lambda _ (fun index => by
      simpa [finiteIIDSampleOnFinset] using (measurable_finiteIIDSampleCoordinate index.1))
  have hmap : Measure.map reindex (finiteIIDSampleLaw (law[|s]) inside.card) =
      Measure.pi (fun _ : subtype => law[|s]) := by
    simpa only [finiteIIDSampleLaw, reindex] using
      (Measure.pi_map_piCongrLeft indexEquiv (fun _ : subtype => law[|s]))
  calc
    Measure.map (finiteIIDSampleOnFinsetToFin inside)
        ((finiteIIDSampleLaw law count)[|finiteIIDMembershipPattern count inside s]) =
        Measure.map reindex.symm
          (Measure.map (finiteIIDSampleOnFinset inside)
            ((finiteIIDSampleLaw law count)[|finiteIIDMembershipPattern count inside s])) := by
          rw [Measure.map_map reindex.symm.measurable hselected]
          congr 1
    _ = Measure.map reindex.symm (Measure.pi (fun _ : subtype => law[|s])) := by
      rw [hproduct]
    _ = Measure.map reindex.symm
        (Measure.map reindex (finiteIIDSampleLaw (law[|s]) inside.card)) := by
          rw [hmap]
    _ = finiteIIDSampleLaw (law[|s]) inside.card := by
          rw [Measure.map_map reindex.symm.measurable reindex.measurable]
          simp

/--
After conditioning on a fixed membership pattern, a measurable coordinatewise
map of the enumerated selected sample is iid from the pushed-forward
conditional law. This is the reusable form needed to put a selected shell
sample into compact coordinates.

It composes the local selected-sample product theorem with the local iid-map
theorem. No new upstream Lean dependency or source material is introduced.
-/
theorem map_finiteIIDSampleMapOnFinsetToFin_conditioned
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (inside : Finset (Fin count)) (s : Set X)
    (hs : MeasurableSet s) (hs_nonzero : law s ≠ 0)
    (hpos : ∀ index : Fin count,
      law (if index ∈ inside then s else sᶜ) ≠ 0)
    (f : X → Y) (hf : Measurable f) :
    Measure.map (finiteIIDSampleMap f ∘ finiteIIDSampleOnFinsetToFin inside)
      ((finiteIIDSampleLaw law count)[|finiteIIDMembershipPattern count inside s]) =
      finiteIIDSampleLaw (Measure.map f (law[|s])) inside.card := by
  letI : IsProbabilityMeasure (law[|s]) :=
    ProbabilityTheory.cond_isProbabilityMeasure hs_nonzero
  have hselected : Measurable
      (finiteIIDSampleOnFinsetToFin inside : (Fin count → X) → Fin inside.card → X) := by
    refine measurable_pi_lambda _ ?_
    intro index
    simpa [finiteIIDSampleOnFinsetToFin, finiteIIDSampleOnFinset] using
      (measurable_finiteIIDSampleCoordinate
        (((finCongr (Fintype.card_coe inside).symm).trans
          (Fintype.equivFin {index : Fin count // index ∈ inside}).symm) index).1)
  have hmap : Measurable (finiteIIDSampleMap f :
      (Fin inside.card → X) → Fin inside.card → Y) := by
    exact measurable_pi_lambda _ (fun index => hf.comp (measurable_pi_apply index))
  calc
    Measure.map (finiteIIDSampleMap f ∘ finiteIIDSampleOnFinsetToFin inside)
        ((finiteIIDSampleLaw law count)[|finiteIIDMembershipPattern count inside s]) =
        Measure.map (finiteIIDSampleMap f)
          (Measure.map (finiteIIDSampleOnFinsetToFin inside)
            ((finiteIIDSampleLaw law count)[|finiteIIDMembershipPattern count inside s])) := by
          rw [Measure.map_map hmap hselected]
    _ = Measure.map (finiteIIDSampleMap f)
        (finiteIIDSampleLaw (law[|s]) inside.card) := by
          rw [map_finiteIIDSampleOnFinsetToFin_conditioned law count inside s hs hpos]
    _ = finiteIIDSampleLaw (Measure.map f (law[|s])) inside.card :=
      map_finiteIIDSampleMap (law[|s]) inside.card f hf

end

end Probability
end AppliedModelingLib
