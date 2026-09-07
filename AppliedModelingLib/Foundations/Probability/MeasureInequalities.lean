import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Data.Set.Disjoint
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Probability.CDF
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory
open ProbabilityTheory
open Filter
open scoped ENNReal NNReal MeasureTheory symmDiff

namespace AppliedModelingLib

/-!
# Measure Inequalities

Small reusable measure-theoretic probability lemmas for continuous
change-of-variables arguments.

## Main declarations

- `ae_of_forall_not_mem_null`
- `ae_eq_of_forall_not_mem_null`
- `ae_iff_of_forall_not_mem_null`
- `ae_eq_decide_of_ae_iff`
- `ae_eq_if_of_ae_iff`
- `ae_eq_setIndicator_of_ae_iff_mem`
- `measure_set_congr_of_symmDiff_null`
- `measure_symmDiff_union_left_eq_zero`
- `measure_symmDiff_diff_left_eq_zero`
- `measure_symmDiff_Ioo_union_Ioo_touching_eq_zero`
- `measure_symmDiff_Ioo_union_Ioi_touching_eq_zero`
- `ae_iff_le_lt_of_level_null`
- `ae_iff_lt_le_of_level_null`
- `measure_eq_zero_of_ae_property_failure_mass`
- `ae_le_contradicts_positive_gt_mass`
- `ae_lt_contradicts_positive_le_mass`
- `measureReal_iUnion_le_tsum`
-/

/-- Real-valued probability/mass of an event under a measure. -/
noncomputable def measureProb {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → Prop) : ℝ :=
  (μ {a | p a}).toReal

/--
Nonnegative random errors with summable expected mass are summable almost
surely. This is the Tonelli handoff used by stochastic approximation arguments
to control square-summable error terms pathwise.
-/
theorem ae_summable_of_summable_integral_of_nonneg
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {f : ℕ → Omega → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (f n) mu)
    (hintegrable : ∀ n, Integrable (f n) mu)
    (hnonneg : ∀ n, 0 ≤ᵐ[mu] f n)
    (hsum : Summable (fun n => ∫ omega, f n omega ∂mu)) :
    ∀ᵐ omega ∂mu, Summable (fun n => f n omega) := by
  have hsum_norm : Summable (fun n => ∫ omega, ‖f n omega‖ ∂mu) := by
    refine hsum.congr ?_
    intro n
    apply integral_congr_ae
    filter_upwards [hnonneg n] with omega homega
    exact (Real.norm_of_nonneg homega).symm
  have hlintegral :
      ∑' n, ∫⁻ omega, ‖f n omega‖ₑ ∂mu ≠ ∞ := by
    have hterm : ∀ n, ∫⁻ omega, ‖f n omega‖ₑ ∂mu =
        ‖∫ omega, ‖f n omega‖ ∂mu‖ₑ := by
      intro n
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hintegrable n).norm]
      simp only [ENNReal.coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs]
      rw [abs_of_nonneg (integral_nonneg (fun omega => abs_nonneg (f n omega)))]
    rw [funext hterm]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hsum_norm.abs
  have hpath_norm : ∀ᵐ omega ∂mu,
      Summable (fun n => (‖f n omega‖₊ : ℝ)) := by
    rw [← lintegral_tsum (fun n => (hmeas n).enorm)] at hlintegral
    refine (ae_lt_top' (AEMeasurable.ennreal_tsum
      (fun n => (hmeas n).enorm)) hlintegral).mono ?_
    intro omega homega
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact homega.ne
  filter_upwards [hpath_norm] with omega homega
  exact homega.of_norm

theorem measureProb_le_of_measure_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop)
    (h : μ {a | p a} ≤ μ {a | q a}) :
    measureProb μ p ≤ measureProb μ q := by
  exact ENNReal.toReal_mono (measure_ne_top μ {a | q a}) h

theorem measureProb_lt_of_measure_lt
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop)
    (h : μ {a | p a} < μ {a | q a}) :
    measureProb μ p < measureProb μ q := by
  exact (ENNReal.toReal_lt_toReal
    (measure_ne_top μ {a | p a}) (measure_ne_top μ {a | q a})).2 h

/-- Real-valued union bound for two events under a finite measure. -/
theorem measureProb_union_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop) :
    measureProb μ (fun a => p a ∨ q a) ≤
      measureProb μ p + measureProb μ q := by
  unfold measureProb
  have hsets : {a | p a ∨ q a} = {a | p a} ∪ {a | q a} := by
    ext a
    simp
  rw [hsets]
  calc
    (μ ({a | p a} ∪ {a | q a})).toReal ≤
        (μ {a | p a} + μ {a | q a}).toReal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr
          ⟨measure_ne_top μ {a | p a}, measure_ne_top μ {a | q a}⟩)
        (measure_union_le _ _)
    _ ≤ (μ {a | p a}).toReal + (μ {a | q a}).toReal :=
      ENNReal.toReal_add_le

/-- Real-valued finite union bound, written without measurability assumptions
because it follows from the outer-measure union inequality. -/
theorem measureProb_exists_mem_finset_le_sum
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (indices : Finset ι) (p : ι → α → Prop) :
    measureProb μ (fun a => ∃ i ∈ indices, p i a) ≤
      ∑ i ∈ indices, measureProb μ (p i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [measureProb]
  | @insert i indices hi ih =>
      have hevent : (fun a => ∃ j ∈ insert i indices, p j a) =
          fun a => p i a ∨ ∃ j ∈ indices, p j a := by
        funext a
        apply propext
        simp
      rw [hevent, Finset.sum_insert hi]
      exact (measureProb_union_le μ (p i)
        (fun a => ∃ j ∈ indices, p j a)).trans (add_le_add le_rfl ih)

theorem measureProb_pos_of_measure_ne_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p : α → Prop)
    (h : μ {a | p a} ≠ 0) :
    0 < measureProb μ p := by
  exact ENNReal.toReal_pos h (measure_ne_top μ {a | p a})

/-- Event probabilities are preserved by measure-preserving measurable equivalences. -/
theorem measureProb_preimage_equiv_of_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) {μ : Measure α} {ν : Measure β}
    (he : MeasurePreserving e μ ν) (p : β → Prop) :
    measureProb μ (fun a => p (e a)) = measureProb ν p := by
  unfold measureProb
  exact congrArg ENNReal.toReal (he.measure_preimage_equiv {b | p b})

/-- Event probabilities are preserved by measure-preserving maps. -/
theorem measureProb_preimage_of_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) {μ : Measure α} {ν : Measure β}
    (hf : MeasurePreserving f μ ν) (p : β → Prop)
    (hp : MeasurableSet {b | p b}) :
    measureProb μ (fun a => p (f a)) = measureProb ν p := by
  unfold measureProb
  rw [← hf.map_eq]
  rw [Measure.map_apply hf.measurable hp]
  rfl

/--
Pointwise strict inequalities integrate to strict inequalities under a
probability measure.

This is a small convenience wrapper around
`integral_pos_iff_support_of_nonneg_ae`; it is useful when a fiberwise strict
conditional-probability comparison must be averaged over the cutoff variable.
-/
theorem integral_lt_integral_of_forall_lt
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hlt : ∀ a, f a < g a) :
    ∫ a, f a ∂μ < ∫ a, g a ∂μ := by
  have hdiff_int : Integrable (fun a => g a - f a) μ := hg.sub hf
  have hdiff_nonneg : 0 ≤ᵐ[μ] fun a => g a - f a :=
    Eventually.of_forall fun a => sub_nonneg.mpr (le_of_lt (hlt a))
  have hsupport_pos :
      0 < μ (Function.support fun a => g a - f a) := by
    have hsupport :
        Function.support (fun a => g a - f a) = Set.univ := by
      ext a
      simp [Function.support, ne_of_gt (sub_pos.mpr (hlt a))]
    rw [hsupport]
    simp
  have hpos :
      0 < ∫ a, g a - f a ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hdiff_nonneg hdiff_int).2
      hsupport_pos
  have hsub :
      (∫ a, g a - f a ∂μ) =
        (∫ a, g a ∂μ) - ∫ a, f a ∂μ := by
    exact integral_sub hg hf
  linarith

/--
Pointwise weak inequalities integrate to strict inequalities when the strict
region has positive measure.
-/
theorem integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hle : ∀ a, f a ≤ g a)
    (hpos : 0 < μ {a | f a < g a}) :
    ∫ a, f a ∂μ < ∫ a, g a ∂μ := by
  have hdiff_int : Integrable (fun a => g a - f a) μ := hg.sub hf
  have hdiff_nonneg : 0 ≤ᵐ[μ] fun a => g a - f a :=
    Eventually.of_forall fun a => sub_nonneg.mpr (hle a)
  have hstrict_subset :
      {a | f a < g a} ⊆ Function.support (fun a => g a - f a) := by
    intro a ha
    change g a - f a ≠ 0
    exact ne_of_gt (sub_pos.mpr (show f a < g a from ha))
  have hsupport_pos :
      0 < μ (Function.support fun a => g a - f a) :=
    lt_of_lt_of_le hpos (measure_mono hstrict_subset)
  have hpos_int :
      0 < ∫ a, g a - f a ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hdiff_nonneg hdiff_int).2
      hsupport_pos
  have hsub :
      (∫ a, g a - f a ∂μ) =
        (∫ a, g a ∂μ) - ∫ a, f a ∂μ := by
    exact integral_sub hg hf
  linarith

/--
Upper-tail rearrangement for a shifted value objective.

If an admission rule `q` is pointwise between zero and one, then after
subtracting the cutoff `threshold` from every value, the strict upper-tail rule
weakly dominates `q` pointwise.  The dominance is strict whenever `q` is
fractional away from the cutoff on a positive-measure set.
-/
theorem shiftedIntegral_lt_upperTailStep_of_fractional
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {threshold : ℝ}
    {q : ℝ → ℝ}
    (hq_shift_int : Integrable (fun v : ℝ => (v - threshold) * q v) μ)
    (hstep_shift_int :
      Integrable
        (fun v : ℝ =>
          (v - threshold) * (if threshold < v then (1 : ℝ) else 0)) μ)
    (hq_bounds : ∀ v : ℝ, 0 ≤ q v ∧ q v ≤ 1)
    (hfractional :
      0 < μ {v : ℝ | v ≠ threshold ∧ 0 < q v ∧ q v < 1}) :
    (∫ v : ℝ, (v - threshold) * q v ∂μ) <
      ∫ v : ℝ,
        (v - threshold) * (if threshold < v then (1 : ℝ) else 0) ∂μ := by
  let f : ℝ → ℝ := fun v => (v - threshold) * q v
  let g : ℝ → ℝ :=
    fun v => (v - threshold) * (if threshold < v then (1 : ℝ) else 0)
  have hle : ∀ v : ℝ, f v ≤ g v := by
    intro v
    by_cases htv : threshold < v
    · have hnonneg : 0 ≤ v - threshold := by linarith
      calc
        f v = (v - threshold) * q v := rfl
        _ ≤ (v - threshold) * 1 :=
          mul_le_mul_of_nonneg_left (hq_bounds v).2 hnonneg
        _ = g v := by simp [g, htv]
    · have hv_le : v ≤ threshold := le_of_not_gt htv
      have hnonpos : v - threshold ≤ 0 := by linarith
      have hprod : (v - threshold) * q v ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hnonpos (hq_bounds v).1
      simpa [f, g, htv] using hprod
  have hstrict_subset :
      {v : ℝ | v ≠ threshold ∧ 0 < q v ∧ q v < 1} ⊆
        {v : ℝ | f v < g v} := by
    intro v hv
    rcases hv with ⟨hv_ne, hq_pos, hq_lt_one⟩
    by_cases htv : threshold < v
    · have hpos : 0 < v - threshold := by linarith
      calc
        f v = (v - threshold) * q v := rfl
        _ < (v - threshold) * 1 :=
          mul_lt_mul_of_pos_left hq_lt_one hpos
        _ = g v := by simp [g, htv]
    · have hv_lt : v < threshold := lt_of_le_of_ne (le_of_not_gt htv) hv_ne
      have hneg : v - threshold < 0 := by linarith
      have hprod : (v - threshold) * q v < 0 :=
        mul_neg_of_neg_of_pos hneg hq_pos
      simpa [f, g, htv] using hprod
  have hstrict_pos : 0 < μ {v : ℝ | f v < g v} :=
    lt_of_lt_of_le hfractional (measure_mono hstrict_subset)
  exact
    integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
      μ hq_shift_int hstep_shift_int hle hstrict_pos

/--
Upper-tail rearrangement for the original value objective.

Among `[0,1]` admission rules with the same total admitted mass as the strict
upper-tail rule at `threshold`, any rule that is fractional away from the
cutoff on a positive-measure set has strictly smaller value-weighted integral.
-/
theorem integral_value_mul_lt_upperTailStep_of_same_mass_fractional
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {threshold : ℝ}
    {q : ℝ → ℝ}
    (hq_int : Integrable q μ)
    (hstep_int :
      Integrable (fun v : ℝ => if threshold < v then (1 : ℝ) else 0) μ)
    (hq_value_int : Integrable (fun v : ℝ => v * q v) μ)
    (hstep_value_int :
      Integrable
        (fun v : ℝ => v * (if threshold < v then (1 : ℝ) else 0)) μ)
    (hq_bounds : ∀ v : ℝ, 0 ≤ q v ∧ q v ≤ 1)
    (hmass :
      (∫ v : ℝ, q v ∂μ) =
        ∫ v : ℝ, (if threshold < v then (1 : ℝ) else 0) ∂μ)
    (hfractional :
      0 < μ {v : ℝ | v ≠ threshold ∧ 0 < q v ∧ q v < 1}) :
    (∫ v : ℝ, v * q v ∂μ) <
      ∫ v : ℝ, v * (if threshold < v then (1 : ℝ) else 0) ∂μ := by
  have hq_shift_int :
      Integrable (fun v : ℝ => (v - threshold) * q v) μ := by
    refine (hq_value_int.sub (hq_int.const_mul threshold)).congr ?_
    filter_upwards with v
    change v * q v - threshold * q v = (v - threshold) * q v
    ring
  have hstep_shift_int :
      Integrable
        (fun v : ℝ =>
          (v - threshold) * (if threshold < v then (1 : ℝ) else 0)) μ := by
    refine (hstep_value_int.sub (hstep_int.const_mul threshold)).congr ?_
    filter_upwards with v
    change
      v * (if threshold < v then (1 : ℝ) else 0) -
          threshold * (if threshold < v then (1 : ℝ) else 0) =
        (v - threshold) * (if threshold < v then (1 : ℝ) else 0)
    ring
  have hshift_lt :
      (∫ v : ℝ, (v - threshold) * q v ∂μ) <
        ∫ v : ℝ,
          (v - threshold) * (if threshold < v then (1 : ℝ) else 0) ∂μ :=
    shiftedIntegral_lt_upperTailStep_of_fractional
      μ hq_shift_int hstep_shift_int hq_bounds hfractional
  have hq_shift_eq :
      (∫ v : ℝ, (v - threshold) * q v ∂μ) =
        (∫ v : ℝ, v * q v ∂μ) -
          threshold * ∫ v : ℝ, q v ∂μ := by
    calc
      (∫ v : ℝ, (v - threshold) * q v ∂μ) =
          ∫ v : ℝ, v * q v - threshold * q v ∂μ := by
            congr 1
            funext v
            ring
      _ = (∫ v : ℝ, v * q v ∂μ) -
            ∫ v : ℝ, threshold * q v ∂μ := by
            exact integral_sub hq_value_int (hq_int.const_mul threshold)
      _ = (∫ v : ℝ, v * q v ∂μ) -
            threshold * ∫ v : ℝ, q v ∂μ := by
            rw [integral_const_mul]
  have hstep_shift_eq :
      (∫ v : ℝ,
          (v - threshold) * (if threshold < v then (1 : ℝ) else 0) ∂μ) =
        (∫ v : ℝ, v * (if threshold < v then (1 : ℝ) else 0) ∂μ) -
          threshold *
            ∫ v : ℝ, (if threshold < v then (1 : ℝ) else 0) ∂μ := by
    calc
      (∫ v : ℝ,
          (v - threshold) * (if threshold < v then (1 : ℝ) else 0) ∂μ) =
          ∫ v : ℝ,
            v * (if threshold < v then (1 : ℝ) else 0) -
              threshold * (if threshold < v then (1 : ℝ) else 0) ∂μ := by
            congr 1
            funext v
            ring
      _ = (∫ v : ℝ, v * (if threshold < v then (1 : ℝ) else 0) ∂μ) -
            ∫ v : ℝ,
              threshold * (if threshold < v then (1 : ℝ) else 0) ∂μ := by
            exact integral_sub hstep_value_int
              (hstep_int.const_mul threshold)
      _ = (∫ v : ℝ, v * (if threshold < v then (1 : ℝ) else 0) ∂μ) -
            threshold *
              ∫ v : ℝ, (if threshold < v then (1 : ℝ) else 0) ∂μ := by
            rw [integral_const_mul]
  rw [hq_shift_eq, hstep_shift_eq] at hshift_lt
  rw [hmass] at hshift_lt
  linarith

/--
Integral upper bound from a two-piece pointwise bound.

If `f < lowBound` on a positive-measure measurable set `s` and
`f ≤ highBound` off `s`, then its integral is strictly below the corresponding
two-piece constant integral.
-/
theorem integral_lt_measureReal_mul_add_compl_of_lt_on_of_le_on_compl
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {s : Set α} (hs : MeasurableSet s) {f : α → ℝ}
    {lowBound highBound : ℝ}
    (hf : Integrable f μ)
    (hpos : 0 < μ s)
    (hlow : ∀ a, a ∈ s → f a < lowBound)
    (hhigh : ∀ a, a ∉ s → f a ≤ highBound) :
    ∫ a, f a ∂μ <
      lowBound * μ.real s + highBound * μ.real sᶜ := by
  classical
  let g : α → ℝ :=
    s.piecewise (fun _ : α => lowBound) (fun _ : α => highBound)
  have hg_s : IntegrableOn (fun _ : α => lowBound) s μ :=
    (integrable_const lowBound).integrableOn
  have hg_compl : IntegrableOn (fun _ : α => highBound) sᶜ μ :=
    (integrable_const highBound).integrableOn
  have hg : Integrable g μ := by
    dsimp [g]
    exact Integrable.piecewise hs hg_s hg_compl
  have hle : ∀ a, f a ≤ g a := by
    intro a
    by_cases ha : a ∈ s
    · have hlt := hlow a ha
      simpa [g, Set.piecewise, ha] using le_of_lt hlt
    · have hle' := hhigh a ha
      simpa [g, Set.piecewise, ha] using hle'
  have hstrict_subset : s ⊆ {a | f a < g a} := by
    intro a ha
    have hlt := hlow a ha
    simpa [g, Set.piecewise, ha] using hlt
  have hstrict_pos : 0 < μ {a | f a < g a} :=
    lt_of_lt_of_le hpos (measure_mono hstrict_subset)
  have hlt_int :
      ∫ a, f a ∂μ < ∫ a, g a ∂μ :=
    integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
      μ hf hg hle hstrict_pos
  have hg_integral :
      ∫ a, g a ∂μ =
        lowBound * μ.real s + highBound * μ.real sᶜ := by
    calc
      ∫ a, g a ∂μ =
          ∫ a in s, lowBound ∂μ + ∫ a in sᶜ, highBound ∂μ := by
            simpa [g] using
              (MeasureTheory.integral_piecewise
                (μ := μ) (s := s) hs hg_s hg_compl)
      _ = lowBound * μ.real s + highBound * μ.real sᶜ := by
            rw [MeasureTheory.setIntegral_const,
              MeasureTheory.setIntegral_const]
            simp [smul_eq_mul, mul_comm]
  exact hlt_int.trans_eq hg_integral

/--
Non-strict upper bound from a two-piece pointwise bound.

If `f ≤ lowBound` on a measurable set `s` and `f ≤ highBound` off `s`, then
the integral of `f` is bounded by the corresponding two-piece constant
integral.
-/
theorem integral_le_measureReal_mul_add_compl_of_le_on_of_le_on_compl
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {s : Set α} (hs : MeasurableSet s) {f : α → ℝ}
    {lowBound highBound : ℝ}
    (hf : Integrable f μ)
    (hlow : ∀ a, a ∈ s → f a ≤ lowBound)
    (hhigh : ∀ a, a ∉ s → f a ≤ highBound) :
    ∫ a, f a ∂μ ≤
      lowBound * μ.real s + highBound * μ.real sᶜ := by
  classical
  let g : α → ℝ :=
    s.piecewise (fun _ : α => lowBound) (fun _ : α => highBound)
  have hg_s : IntegrableOn (fun _ : α => lowBound) s μ :=
    (integrable_const lowBound).integrableOn
  have hg_compl : IntegrableOn (fun _ : α => highBound) sᶜ μ :=
    (integrable_const highBound).integrableOn
  have hg : Integrable g μ := by
    dsimp [g]
    exact Integrable.piecewise hs hg_s hg_compl
  have hle : ∀ a, f a ≤ g a := by
    intro a
    by_cases ha : a ∈ s
    · have hle' := hlow a ha
      simpa [g, Set.piecewise, ha] using hle'
    · have hle' := hhigh a ha
      simpa [g, Set.piecewise, ha] using hle'
  have hle_int : ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ :=
    MeasureTheory.integral_mono hf hg hle
  have hg_integral :
      ∫ a, g a ∂μ =
        lowBound * μ.real s + highBound * μ.real sᶜ := by
    calc
      ∫ a, g a ∂μ =
          ∫ a in s, lowBound ∂μ + ∫ a in sᶜ, highBound ∂μ := by
            simpa [g] using
              (MeasureTheory.integral_piecewise
                (μ := μ) (s := s) hs hg_s hg_compl)
      _ = lowBound * μ.real s + highBound * μ.real sᶜ := by
            rw [MeasureTheory.setIntegral_const,
              MeasureTheory.setIntegral_const]
            simp [smul_eq_mul, mul_comm]
  rw [hg_integral] at hle_int
  exact hle_int

/--
Almost-everywhere version of the two-piece constant integral bound.  This is
the natural form when a measurable stochastic construction is only specified
on the full-measure support of its sampling law.
-/
theorem integral_le_measureReal_mul_add_compl_of_ae_le_on_of_ae_le_on_compl
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {s : Set α} (hs : MeasurableSet s) {f : α → ℝ}
    {lowBound highBound : ℝ}
    (hf : Integrable f μ)
    (hle : ∀ᵐ a ∂μ,
      (a ∈ s → f a ≤ lowBound) ∧ (a ∉ s → f a ≤ highBound)) :
    ∫ a, f a ∂μ ≤
      lowBound * μ.real s + highBound * μ.real sᶜ := by
  classical
  let g : α → ℝ :=
    s.piecewise (fun _ : α => lowBound) (fun _ : α => highBound)
  have hg_s : IntegrableOn (fun _ : α => lowBound) s μ :=
    (integrable_const lowBound).integrableOn
  have hg_compl : IntegrableOn (fun _ : α => highBound) sᶜ μ :=
    (integrable_const highBound).integrableOn
  have hg : Integrable g μ := by
    dsimp [g]
    exact Integrable.piecewise hs hg_s hg_compl
  have hle' : ∀ᵐ a ∂μ, f a ≤ g a := by
    filter_upwards [hle] with a ha
    by_cases has : a ∈ s
    · simpa [g, Set.piecewise, has] using ha.1 has
    · simpa [g, Set.piecewise, has] using ha.2 has
  have hle_int : ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ :=
    MeasureTheory.integral_mono_ae hf hg hle'
  have hg_integral :
      ∫ a, g a ∂μ =
        lowBound * μ.real s + highBound * μ.real sᶜ := by
    calc
      ∫ a, g a ∂μ =
          ∫ a in s, lowBound ∂μ + ∫ a in sᶜ, highBound ∂μ := by
            simpa [g] using
              (MeasureTheory.integral_piecewise
                (μ := μ) (s := s) hs hg_s hg_compl)
      _ = lowBound * μ.real s + highBound * μ.real sᶜ := by
            rw [MeasureTheory.setIntegral_const,
              MeasureTheory.setIntegral_const]
            simp [smul_eq_mul, mul_comm]
  rw [hg_integral] at hle_int
  exact hle_int

/--
Integral lower bound from a two-piece pointwise bound.

If `lowBound < f` on a positive-measure measurable set `s` and `0 ≤ f` off
`s`, then the integral of `f` is strictly above the integral of the two-piece
constant lower bound.
-/
theorem measureReal_mul_lt_integral_of_lt_on_of_nonneg_on_compl
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {s : Set α} (hs : MeasurableSet s) {f : α → ℝ}
    {lowBound : ℝ}
    (hf : Integrable f μ)
    (hpos : 0 < μ s)
    (hlow : ∀ a, a ∈ s → lowBound < f a)
    (hnonneg : ∀ a, a ∉ s → 0 ≤ f a) :
    lowBound * μ.real s < ∫ a, f a ∂μ := by
  classical
  let g : α → ℝ :=
    s.piecewise (fun _ : α => lowBound) (fun _ : α => 0)
  have hg_s : IntegrableOn (fun _ : α => lowBound) s μ :=
    (integrable_const lowBound).integrableOn
  have hg_compl : IntegrableOn (fun _ : α => (0 : ℝ)) sᶜ μ :=
    (integrable_const (0 : ℝ)).integrableOn
  have hg : Integrable g μ := by
    dsimp [g]
    exact Integrable.piecewise hs hg_s hg_compl
  have hle : ∀ a, g a ≤ f a := by
    intro a
    by_cases ha : a ∈ s
    · have hlt := hlow a ha
      simpa [g, Set.piecewise, ha] using le_of_lt hlt
    · have hle' := hnonneg a ha
      simpa [g, Set.piecewise, ha] using hle'
  have hstrict_subset : s ⊆ {a | g a < f a} := by
    intro a ha
    have hlt := hlow a ha
    simpa [g, Set.piecewise, ha] using hlt
  have hstrict_pos : 0 < μ {a | g a < f a} :=
    lt_of_lt_of_le hpos (measure_mono hstrict_subset)
  have hlt_int :
      ∫ a, g a ∂μ < ∫ a, f a ∂μ :=
    integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
      μ hg hf hle hstrict_pos
  have hg_integral :
      ∫ a, g a ∂μ = lowBound * μ.real s := by
    calc
      ∫ a, g a ∂μ =
          ∫ a in s, lowBound ∂μ + ∫ a in sᶜ, (0 : ℝ) ∂μ := by
            simpa [g] using
              (MeasureTheory.integral_piecewise
                (μ := μ) (s := s) hs hg_s hg_compl)
      _ = lowBound * μ.real s := by
            rw [MeasureTheory.setIntegral_const,
              MeasureTheory.setIntegral_const]
            simp [smul_eq_mul, mul_comm]
  exact hg_integral.symm.trans_lt hlt_int

/--
Non-strict lower bound from a two-piece pointwise bound.

If `lowBound ≤ f` on a measurable set `s` and `0 ≤ f` off `s`, then the
integral of `f` is at least the corresponding two-piece constant lower bound.
-/
theorem measureReal_mul_le_integral_of_le_on_of_nonneg_on_compl
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {s : Set α} (hs : MeasurableSet s) {f : α → ℝ}
    {lowBound : ℝ}
    (hf : Integrable f μ)
    (hlow : ∀ a, a ∈ s → lowBound ≤ f a)
    (hnonneg : ∀ a, a ∉ s → 0 ≤ f a) :
    lowBound * μ.real s ≤ ∫ a, f a ∂μ := by
  classical
  let g : α → ℝ :=
    s.piecewise (fun _ : α => lowBound) (fun _ : α => 0)
  have hg_s : IntegrableOn (fun _ : α => lowBound) s μ :=
    (integrable_const lowBound).integrableOn
  have hg_compl : IntegrableOn (fun _ : α => (0 : ℝ)) sᶜ μ :=
    (integrable_const (0 : ℝ)).integrableOn
  have hg : Integrable g μ := by
    dsimp [g]
    exact Integrable.piecewise hs hg_s hg_compl
  have hle : ∀ a, g a ≤ f a := by
    intro a
    by_cases ha : a ∈ s
    · have hle' := hlow a ha
      simpa [g, Set.piecewise, ha] using hle'
    · have hle' := hnonneg a ha
      simpa [g, Set.piecewise, ha] using hle'
  have hle_int : ∫ a, g a ∂μ ≤ ∫ a, f a ∂μ :=
    MeasureTheory.integral_mono hg hf hle
  have hg_integral :
      ∫ a, g a ∂μ = lowBound * μ.real s := by
    calc
      ∫ a, g a ∂μ =
          ∫ a in s, lowBound ∂μ + ∫ a in sᶜ, (0 : ℝ) ∂μ := by
            simpa [g] using
              (MeasureTheory.integral_piecewise
                (μ := μ) (s := s) hs hg_s hg_compl)
      _ = lowBound * μ.real s := by
            rw [MeasureTheory.setIntegral_const,
              MeasureTheory.setIntegral_const]
            simp [smul_eq_mul, mul_comm]
  rw [hg_integral] at hle_int
  exact hle_int

/-- Fourth-moment Markov bound for the absolute-value upper tail of a real
random variable.  The statement is kept in real-valued probability form so
finite-union estimates can be summed without `ENNReal` coercion bookkeeping. -/
theorem fourth_mul_measureProb_abs_ge_le_integral_fourth
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {X : α → ℝ} (hX : Measurable X)
    (hfourth : Integrable (fun a => X a ^ 4) μ)
    {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    threshold ^ 4 * measureProb μ (fun a => threshold ≤ |X a|) ≤
      ∫ a, X a ^ 4 ∂μ := by
  rw [measureProb]
  apply measureReal_mul_le_integral_of_le_on_of_nonneg_on_compl μ
    (measurableSet_le measurable_const hX.abs) hfourth
  · intro a ha
    calc
      threshold ^ 4 ≤ |X a| ^ 4 :=
        pow_le_pow_left₀ hthreshold ha 4
      _ = X a ^ 4 := by
        calc
          |X a| ^ 4 = (|X a| ^ 2) ^ 2 := by ring
          _ = (X a ^ 2) ^ 2 := by rw [sq_abs]
          _ = X a ^ 4 := by ring
  · intro a _
    positivity

/--
Average a fiberwise strict probability comparison.

If the numerator event has source probability `∫ N`, the conditioning event has
source probability `∫ D`, the comparison event has probability `P`, and every
fiber satisfies `N a < P * D a`, then the averaged numerator is strictly below
the product of the comparison-event probability and the conditioning-event
probability.
-/
theorem measureProb_lt_mul_of_integral_fiber_lt
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (κ : Measure α) [IsProbabilityMeasure κ]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A B C : Ω → Prop)
    {N D : α → ℝ} {P : ℝ}
    (hN_int : Integrable N κ) (hD_int : Integrable D κ)
    (hA : measureProb ν A = ∫ a, N a ∂κ)
    (hB : measureProb ν B = ∫ a, D a ∂κ)
    (hC : measureProb ν C = P)
    (hlt : ∀ a, N a < P * D a) :
    measureProb ν A < measureProb ν C * measureProb ν B := by
  rw [hA, hB, hC]
  have hPD_int : Integrable (fun a => P * D a) κ := hD_int.const_mul P
  have hlt_int :
      (∫ a, N a ∂κ) < ∫ a, P * D a ∂κ :=
    integral_lt_integral_of_forall_lt κ hN_int hPD_int hlt
  rwa [integral_const_mul] at hlt_int

/-- Finite measure of a larger set transfers to every subset. -/
theorem measure_ne_top_of_subset_of_ne_top
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {s t : Set α}
    (hsub : s ⊆ t) (hfinite : μ t ≠ ∞) :
    μ s ≠ ∞ := by
  exact ne_top_of_le_ne_top hfinite (measure_mono hsub)

/-- Real-valued measure is positive when the underlying `ENNReal` mass is nonzero and finite. -/
theorem measureReal_pos_of_measure_ne_zero_ne_top
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α)
    (h_ne_zero : μ s ≠ 0)
    (h_ne_top : μ s ≠ ∞) :
    0 < μ.real s :=
  ENNReal.toReal_pos h_ne_zero h_ne_top

/-- Positive real-valued measure implies positive underlying `ENNReal` mass. -/
theorem measure_pos_of_measureReal_pos
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α)
    (h : 0 < μ.real s) :
    0 < μ s := by
  exact (ENNReal.toReal_pos_iff.mp h).1

/--
Positive measure is monotone under set inclusion.
-/
theorem measure_pos_of_subset
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {A B : Set α}
    (hAB : A ⊆ B) (hpos : 0 < μ A) : 0 < μ B :=
  lt_of_lt_of_le hpos (measure_mono hAB)

/--
An almost-everywhere property cannot fail on a positive-measure event.
-/
theorem measure_eq_zero_of_ae_property_failure_mass
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (P Q : α → Prop)
    (hAE : ∀ᵐ a ∂μ, P a)
    (hQ_bad : ∀ a, Q a → ¬ P a) :
    μ {a | Q a} = 0 := by
  exact measure_mono_null (fun a hQ => hQ_bad a hQ)
    (MeasureTheory.ae_iff.1 hAE)

/--
An almost-everywhere property cannot fail on a positive-measure event.
-/
theorem ae_property_contradicts_positive_failure_mass
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (P Q : α → Prop)
    (hAE : ∀ᵐ a ∂μ, P a)
    (hQ_bad : ∀ a, Q a → ¬ P a)
    (hpos : 0 < μ {a | Q a}) : False := by
  have hzero : μ {a | Q a} = 0 := by
    exact measure_eq_zero_of_ae_property_failure_mass μ P Q hAE hQ_bad
  exact (ne_of_gt hpos) hzero

/--
An a.e. implication of the form `selected a → reference a ≤ value a` rules out
positive mass of selected points with `value a < reference a`.
-/
theorem ae_imp_le_contradicts_positive_selected_lt_mass
    {α β : Type*} [MeasurableSpace α] [Preorder β]
    (μ : Measure α) (selected : α → Prop) (reference value : α → β)
    (hAE : ∀ᵐ a ∂μ, selected a → reference a ≤ value a)
    (hpos : 0 < μ {a | selected a ∧ value a < reference a}) : False :=
  ae_property_contradicts_positive_failure_mass μ
    (fun a => selected a → reference a ≤ value a)
    (fun a => selected a ∧ value a < reference a)
    hAE
    (fun _ hbad hAE_a => not_le_of_gt hbad.2 (hAE_a hbad.1))
    hpos

/--
Cancel a positive affine score transform inside an a.e. implication.

This is useful for equilibrium arguments where a payoff comparison is stated
as `(base + weight * x) / denom ≤ (base + weight * y) / denom`, with positive
`weight` and `denom`, but the economic conclusion is `x ≤ y`.
-/
theorem ae_imp_le_of_affine_div_le_affine_div
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (selected : α → Prop)
    (base weight denom x y : α → ℝ)
    (hweight : ∀ a, 0 < weight a)
    (hdenom : ∀ a, 0 < denom a)
    (hAE :
      ∀ᵐ a ∂μ, selected a →
        (base a + weight a * x a) / denom a ≤
          (base a + weight a * y a) / denom a) :
    ∀ᵐ a ∂μ, selected a → x a ≤ y a :=
  hAE.mono fun a hle hselected => by
    have hmul :=
      mul_le_mul_of_nonneg_right (hle hselected) (le_of_lt (hdenom a))
    have hsimpl :
        base a + weight a * x a ≤ base a + weight a * y a := by
      simpa [div_mul_cancel₀ _ (ne_of_gt (hdenom a))] using hmul
    have hmulxy : weight a * x a ≤ weight a * y a :=
      (add_le_add_iff_left (base a)).mp hsimpl
    exact le_of_mul_le_mul_left hmulxy (hweight a)

/--
If every point in an interval-like event is selected, then positive mass of
that event gives positive mass of selected points below the reference value.
-/
theorem positive_selected_lt_mass_of_positive_lower_lt_mass
    {α β : Type*} [MeasurableSpace α] [Preorder β]
    {μ : Measure α} {selected : α → Prop}
    {lower reference value : α → β}
    (hselected : ∀ a, lower a ≤ value a → selected a)
    (hpos : 0 < μ {a | lower a ≤ value a ∧ value a < reference a}) :
    0 < μ {a | selected a ∧ value a < reference a} :=
  measure_pos_of_subset
    (A := {a | lower a ≤ value a ∧ value a < reference a})
    (B := {a | selected a ∧ value a < reference a})
    (fun a ha => ⟨hselected a ha.1, ha.2⟩)
    hpos

/-- If `f ≤ g` a.e., then the strict reverse inequality has zero mass. -/
theorem measure_eq_zero_of_ae_le_of_gt
    {α β : Type*} [MeasurableSpace α] [Preorder β]
    {μ : Measure α} {f g : α → β}
    (hAE : ∀ᵐ a ∂μ, f a ≤ g a) :
    μ {a | g a < f a} = 0 :=
  measure_eq_zero_of_ae_property_failure_mass μ
    (fun a => f a ≤ g a) (fun a => g a < f a)
    hAE (fun _ hgt => not_le_of_gt hgt)

/--
An a.e. weak inequality cannot be strictly reversed on a positive-measure
event.
-/
theorem ae_le_contradicts_positive_gt_mass
    {α β : Type*} [MeasurableSpace α] [Preorder β]
    {μ : Measure α} {f g : α → β}
    (hAE : ∀ᵐ a ∂μ, f a ≤ g a)
    (hpos : 0 < μ {a | g a < f a}) : False := by
  exact (ne_of_gt hpos) (measure_eq_zero_of_ae_le_of_gt (μ := μ) hAE)

/-- If `f < g` a.e., then the weak reverse inequality has zero mass. -/
theorem measure_eq_zero_of_ae_lt_of_le
    {α β : Type*} [MeasurableSpace α] [Preorder β]
    {μ : Measure α} {f g : α → β}
    (hAE : ∀ᵐ a ∂μ, f a < g a) :
    μ {a | g a ≤ f a} = 0 :=
  measure_eq_zero_of_ae_property_failure_mass μ
    (fun a => f a < g a) (fun a => g a ≤ f a)
    hAE (fun _ hle hlt => not_le_of_gt hlt hle)

/--
An a.e. strict inequality cannot be weakly reversed on a positive-measure
event.
-/
theorem ae_lt_contradicts_positive_le_mass
    {α β : Type*} [MeasurableSpace α] [Preorder β]
    {μ : Measure α} {f g : α → β}
    (hAE : ∀ᵐ a ∂μ, f a < g a)
    (hpos : 0 < μ {a | g a ≤ f a}) : False := by
  exact (ne_of_gt hpos) (measure_eq_zero_of_ae_lt_of_le (μ := μ) hAE)

/--
If a property holds away from a null set, then it holds almost everywhere.
This is the basic boundary-null bridge for continuous cutoff arguments.
-/
theorem ae_of_forall_not_mem_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {P : α → Prop} {s : Set α}
    (hs : μ s = 0)
    (hP : ∀ a, a ∉ s → P a) :
    ∀ᵐ a ∂μ, P a := by
  refine MeasureTheory.ae_iff.2 ?_
  exact measure_mono_null
    (fun a hnotP => by
      by_contra hnotMem
      exact hnotP (hP a hnotMem))
    hs

/-- Two functions that agree outside a null set are equal almost everywhere. -/
theorem ae_eq_of_forall_not_mem_null
    {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → β} {s : Set α}
    (hs : μ s = 0)
    (hfg : ∀ a, a ∉ s → f a = g a) :
    f =ᵐ[μ] g :=
  ae_of_forall_not_mem_null (μ := μ) hs hfg

/-- Two predicates that agree outside a null set are equivalent almost everywhere. -/
theorem ae_iff_of_forall_not_mem_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {P Q : α → Prop} {s : Set α}
    (hs : μ s = 0)
    (hPQ : ∀ a, a ∉ s → (P a ↔ Q a)) :
    ∀ᵐ a ∂μ, (P a ↔ Q a) :=
  ae_of_forall_not_mem_null (μ := μ) hs hPQ

/-- A function is equal a.e. if its pointwise mismatch set is contained in a null set. -/
theorem ae_eq_of_subset_null
    {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → β} {s : Set α}
    (hsub : {a | f a ≠ g a} ⊆ s)
    (hs : μ s = 0) :
    f =ᵐ[μ] g := by
  exact MeasureTheory.ae_iff.2 (measure_mono_null hsub hs)

/-- Predicate equivalence a.e. from a null set containing all mismatches. -/
theorem ae_iff_of_subset_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {P Q : α → Prop} {s : Set α}
    (hsub : {a | ¬ (P a ↔ Q a)} ⊆ s)
    (hs : μ s = 0) :
    ∀ᵐ a ∂μ, (P a ↔ Q a) := by
  exact MeasureTheory.ae_iff.2 (measure_mono_null hsub hs)

/-- An a.e. predicate equivalence gives a.e. equality of Boolean indicators. -/
theorem ae_eq_decide_of_ae_iff
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ᵐ a ∂μ, (P a ↔ Q a)) :
    (fun a => decide (P a)) =ᵐ[μ] fun a => decide (Q a) := by
  filter_upwards [hPQ] with a hiff
  by_cases hP : P a
  · have hQ : Q a := hiff.1 hP
    simp [hP, hQ]
  · have hQ : ¬ Q a := fun hQa => hP (hiff.2 hQa)
    simp [hP, hQ]

/--
An a.e. predicate equivalence lets an `if` expression switch predicates when
the two branches are the same.
-/
theorem ae_eq_if_of_ae_iff
    {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (thenBranch elseBranch : α → β)
    (hPQ : ∀ᵐ a ∂μ, (P a ↔ Q a)) :
    (fun a => if P a then thenBranch a else elseBranch a) =ᵐ[μ]
      fun a => if Q a then thenBranch a else elseBranch a := by
  filter_upwards [hPQ] with a hiff
  by_cases hP : P a
  · have hQ : Q a := hiff.1 hP
    simp [hP, hQ]
  · have hQ : ¬ Q a := fun hQa => hP (hiff.2 hQa)
    simp [hP, hQ]

/-- Set indicators are equal a.e. when their membership predicates agree a.e. -/
theorem ae_eq_setIndicator_of_ae_iff_mem
    {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    [Zero β] {s t : Set α} (f : α → β)
    (hst : ∀ᵐ a ∂μ, (a ∈ s ↔ a ∈ t)) :
    s.indicator f =ᵐ[μ] t.indicator f := by
  filter_upwards [hst] with a hiff
  by_cases hs : a ∈ s
  · have ht : a ∈ t := hiff.1 hs
    simp [Set.indicator, hs, ht]
  · have ht : a ∉ t := fun ht => hs (hiff.2 ht)
    simp [Set.indicator, hs, ht]

/-- Set indicators are equal a.e. when their sets differ only inside a null set. -/
theorem ae_eq_setIndicator_of_forall_not_mem_null
    {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    [Zero β] {s t boundary : Set α} (f : α → β)
    (hboundary : μ boundary = 0)
    (hst : ∀ a, a ∉ boundary → (a ∈ s ↔ a ∈ t)) :
    s.indicator f =ᵐ[μ] t.indicator f :=
  ae_eq_setIndicator_of_ae_iff_mem (μ := μ) f
    (ae_iff_of_forall_not_mem_null (μ := μ) hboundary hst)

/-- Sets whose symmetric difference is null have equal measure. -/
theorem measure_set_congr_of_symmDiff_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hst : μ (s ∆ t) = 0) :
    μ s = μ t :=
  measure_congr (measure_symmDiff_eq_zero_iff.mp hst)

/--
Adding the same fixed context to both sets cannot create new symmetric
difference points.
-/
theorem symmDiff_union_left_subset
    {α : Type*} {κ s t : Set α} :
    ((κ ∪ s) ∆ (κ ∪ t)) ⊆ s ∆ t := by
  intro x hx
  rw [Set.symmDiff_def] at hx ⊢
  rcases hx with hx | hx
  · rcases hx with ⟨hx_left, hx_not_right⟩
    have hxs : x ∈ s := by
      rcases hx_left with hxκ | hxs
      · exact False.elim (hx_not_right (Or.inl hxκ))
      · exact hxs
    have hxt_not : x ∉ t := by
      intro hxt
      exact hx_not_right (Or.inr hxt)
    exact Or.inl ⟨hxs, hxt_not⟩
  · rcases hx with ⟨hx_right, hx_not_left⟩
    have hxt : x ∈ t := by
      rcases hx_right with hxκ | hxt
      · exact False.elim (hx_not_left (Or.inl hxκ))
      · exact hxt
    have hxs_not : x ∉ s := by
      intro hxs
      exact hx_not_left (Or.inr hxs)
    exact Or.inr ⟨hxt, hxs_not⟩

/-- Null symmetric difference is preserved after unioning with fixed context. -/
theorem measure_symmDiff_union_left_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {κ s t : Set α} (hst : μ (s ∆ t) = 0) :
    μ ((κ ∪ s) ∆ (κ ∪ t)) = 0 :=
  measure_mono_null symmDiff_union_left_subset hst

/-- A.e. set equality is preserved after unioning with fixed context. -/
theorem ae_eq_set_union_left
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {κ s t : Set α} (hst : s =ᵐ[μ] t) :
    ((κ ∪ s : Set α) =ᵐ[μ] (κ ∪ t : Set α)) := by
  rw [← measure_symmDiff_eq_zero_iff] at hst ⊢
  exact measure_symmDiff_union_left_eq_zero hst

/--
Intersecting a fixed left set with the complements of two sets cannot create
new symmetric difference points.
-/
theorem symmDiff_diff_left_subset
    {α : Type*} {A s t : Set α} :
    ((A \ s) ∆ (A \ t)) ⊆ s ∆ t := by
  intro x hx
  rw [Set.mem_symmDiff] at hx ⊢
  rcases hx with hx | hx
  · rcases hx with ⟨hxAs, hnotAt⟩
    have hxt : x ∈ t := by
      by_contra hxt
      exact hnotAt ⟨hxAs.1, hxt⟩
    exact Or.inr ⟨hxt, hxAs.2⟩
  · rcases hx with ⟨hxAt, hnotAs⟩
    have hxs : x ∈ s := by
      by_contra hxs
      exact hnotAs ⟨hxAt.1, hxs⟩
    exact Or.inl ⟨hxs, hxAt.2⟩

/-- Null symmetric difference is preserved by fixed-left set difference. -/
theorem measure_symmDiff_diff_left_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A s t : Set α} (hst : μ (s ∆ t) = 0) :
    μ ((A \ s) ∆ (A \ t)) = 0 :=
  measure_mono_null symmDiff_diff_left_subset hst

/-- A.e. set equality is preserved by fixed-left set difference. -/
theorem ae_eq_set_diff_left
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A s t : Set α} (hst : s =ᵐ[μ] t) :
    ((A \ s : Set α) =ᵐ[μ] (A \ t : Set α)) := by
  rw [← measure_symmDiff_eq_zero_iff] at hst ⊢
  exact measure_symmDiff_diff_left_eq_zero hst

/-- Measure of fixed-left set difference is invariant under null symmetric difference. -/
theorem measure_diff_left_congr_of_symmDiff_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A s t : Set α} (hst : μ (s ∆ t) = 0) :
    μ (A \ s) = μ (A \ t) :=
  measure_set_congr_of_symmDiff_null
    (measure_symmDiff_diff_left_eq_zero (A := A) hst)

/--
Two touching open intervals differ from the merged open interval only at the
touching endpoint.
-/
theorem symmDiff_Ioo_union_Ioo_touching_subset_singleton
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((Set.Ioo a b ∪ Set.Ioo b c) ∆ Set.Ioo a c) ⊆
      ({b} : Set ℝ) := by
  intro x hx
  rw [Set.symmDiff_def] at hx
  rcases hx with hx | hx
  · rcases hx with ⟨hx_union, hx_not⟩
    rcases hx_union with hx_left | hx_right
    · have hx_ac : x ∈ Set.Ioo a c :=
        ⟨hx_left.1, lt_of_lt_of_le hx_left.2 hbc⟩
      exact False.elim (hx_not hx_ac)
    · have hx_ac : x ∈ Set.Ioo a c :=
        ⟨lt_of_le_of_lt hab hx_right.1, hx_right.2⟩
      exact False.elim (hx_not hx_ac)
  · rcases hx with ⟨hx_ac, hx_not_union⟩
    by_cases hxb : x = b
    · simpa [hxb]
    · exfalso
      rcases lt_or_gt_of_ne hxb with hx_lt_b | hb_lt_x
      · exact hx_not_union (Or.inl ⟨hx_ac.1, hx_lt_b⟩)
      · exact hx_not_union (Or.inr ⟨hb_lt_x, hx_ac.2⟩)

/-- Under a nonatomic measure, touching open intervals are equal a.e. -/
theorem measure_symmDiff_Ioo_union_Ioo_touching_eq_zero
    (μ : Measure ℝ) [NoAtoms μ]
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    μ ((Set.Ioo a b ∪ Set.Ioo b c) ∆ Set.Ioo a c) = 0 :=
  measure_mono_null
    (symmDiff_Ioo_union_Ioo_touching_subset_singleton
      (a := a) (b := b) (c := c) hab hbc)
    (measure_singleton b)

/-- A.e. set equality form of `measure_symmDiff_Ioo_union_Ioo_touching_eq_zero`. -/
theorem ae_eq_Ioo_union_Ioo_touching
    (μ : Measure ℝ) [NoAtoms μ]
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((Set.Ioo a b ∪ Set.Ioo b c : Set ℝ) =ᵐ[μ] Set.Ioo a c) :=
  measure_symmDiff_eq_zero_iff.mp
    (measure_symmDiff_Ioo_union_Ioo_touching_eq_zero
      μ hab hbc)

/--
An open interval touching a right ray differs from the merged right ray only
at the touching endpoint.
-/
theorem symmDiff_Ioo_union_Ioi_touching_subset_singleton
    {a b : ℝ} (hab : a ≤ b) :
    ((Set.Ioo a b ∪ Set.Ioi b) ∆ Set.Ioi a) ⊆
      ({b} : Set ℝ) := by
  intro x hx
  rw [Set.symmDiff_def] at hx
  rcases hx with hx | hx
  · rcases hx with ⟨hx_union, hx_not⟩
    have hx_a : a < x := by
      rcases hx_union with hx_interval | hx_ray
      · exact hx_interval.1
      · exact lt_of_le_of_lt hab hx_ray
    exact False.elim (hx_not hx_a)
  · rcases hx with ⟨hx_ray, hx_not_union⟩
    by_cases hxb : x = b
    · simpa [hxb]
    · exfalso
      rcases lt_or_gt_of_ne hxb with hx_lt_b | hb_lt_x
      · exact hx_not_union (Or.inl ⟨hx_ray, hx_lt_b⟩)
      · exact hx_not_union (Or.inr hb_lt_x)

/-- Under a nonatomic measure, a touching open interval and right ray are equal a.e. -/
theorem measure_symmDiff_Ioo_union_Ioi_touching_eq_zero
    (μ : Measure ℝ) [NoAtoms μ]
    {a b : ℝ} (hab : a ≤ b) :
    μ ((Set.Ioo a b ∪ Set.Ioi b) ∆ Set.Ioi a) = 0 :=
  measure_mono_null
    (symmDiff_Ioo_union_Ioi_touching_subset_singleton
      (a := a) (b := b) hab)
    (measure_singleton b)

/-- A.e. set equality form of `measure_symmDiff_Ioo_union_Ioi_touching_eq_zero`. -/
theorem ae_eq_Ioo_union_Ioi_touching
    (μ : Measure ℝ) [NoAtoms μ]
    {a b : ℝ} (hab : a ≤ b) :
    ((Set.Ioo a b ∪ Set.Ioi b : Set ℝ) =ᵐ[μ] Set.Ioi a) :=
  measure_symmDiff_eq_zero_iff.mp
    (measure_symmDiff_Ioo_union_Ioi_touching_eq_zero μ hab)

/--
Weak and strict lower cutoff predicates are equivalent a.e. when the level set
has zero mass.
-/
theorem ae_iff_le_lt_of_level_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {score : α → ℝ} {cutoff : ℝ}
    (hlevel : μ {a | score a = cutoff} = 0) :
    ∀ᵐ a ∂μ, (cutoff ≤ score a ↔ cutoff < score a) := by
  refine ae_iff_of_forall_not_mem_null (μ := μ)
    (s := {a | score a = cutoff}) hlevel ?_
  intro a ha
  constructor
  · intro hle
    exact lt_of_le_of_ne hle (fun hEq => ha hEq.symm)
  · exact le_of_lt

/--
Strict and weak upper cutoff predicates are equivalent a.e. when the level set
has zero mass.
-/
theorem ae_iff_lt_le_of_level_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {score : α → ℝ} {cutoff : ℝ}
    (hlevel : μ {a | score a = cutoff} = 0) :
    ∀ᵐ a ∂μ, (score a < cutoff ↔ score a ≤ cutoff) := by
  refine ae_iff_of_forall_not_mem_null (μ := μ)
    (s := {a | score a = cutoff}) hlevel ?_
  intro a ha
  constructor
  · exact le_of_lt
  · intro hle
    exact lt_of_le_of_ne hle (fun hEq => ha hEq)

theorem measureReal_inter_ge_one_sub_add
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {P Q : Set α}
    (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    {epsP epsQ : ℝ}
    (hprobP : 1 - epsP ≤ μ.real P)
    (hprobQ : 1 - epsQ ≤ μ.real Q) :
    1 - epsP - epsQ ≤ μ.real (P ∩ Q) := by
  have hPcompl :
      μ.real Pᶜ ≤ epsP := by
    have hcompl :
        μ.real Pᶜ = 1 - μ.real P :=
      probReal_compl_eq_one_sub (μ := μ) hP
    linarith
  have hQcompl :
      μ.real Qᶜ ≤ epsQ := by
    have hcompl :
        μ.real Qᶜ = 1 - μ.real Q :=
      probReal_compl_eq_one_sub (μ := μ) hQ
    linarith
  have hbad :
      μ.real (Pᶜ ∪ Qᶜ) ≤ epsP + epsQ := by
    exact (measureReal_union_le (μ := μ) Pᶜ Qᶜ).trans
      (add_le_add hPcompl hQcompl)
  have hcompl_inter :
      μ.real (P ∩ Q)ᶜ = 1 - μ.real (P ∩ Q) :=
    probReal_compl_eq_one_sub (μ := μ) (hP.inter hQ)
  have hdeMorgan : (P ∩ Q)ᶜ = Pᶜ ∪ Qᶜ := by
    ext a
    by_cases hpa : a ∈ P <;> by_cases hqa : a ∈ Q <;> simp [hpa, hqa]
  have hbad_inter :
      μ.real (P ∩ Q)ᶜ ≤ epsP + epsQ := by
    rwa [hdeMorgan]
  linarith

/-- A measurable bad event of probability at most `p` leaves every set
containing its complement with probability at least `1 - p`. -/
theorem one_sub_le_measureReal_of_measureReal_bad_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {bad safe : Set α} {p : ℝ}
    (hbad_meas : MeasurableSet bad) (hbad : μ.real bad ≤ p)
    (hgood_subset : badᶜ ⊆ safe) :
    1 - p ≤ μ.real safe := by
  calc
    1 - p ≤ 1 - μ.real bad := sub_le_sub_left hbad 1
    _ = μ.real badᶜ := by
      rw [probReal_compl_eq_one_sub (μ := μ) hbad_meas]
    _ ≤ μ.real safe := measureReal_mono hgood_subset (measure_ne_top μ _)

theorem isProbabilityMeasure_withDensity_of_lintegral_eq_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (D : α → ENNReal)
    (hD : ∫⁻ a, D a ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity D) := by
  refine ⟨?_⟩
  rw [withDensity_apply D MeasurableSet.univ]
  simpa using hD

theorem setLIntegral_ne_top_of_lintegral_eq_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (D : α → ENNReal)
    (hD : ∫⁻ a, D a ∂μ = 1) (s : Set α) :
    (∫⁻ a in s, D a ∂μ) ≠ ∞ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [← hD]
  exact setLIntegral_le_lintegral s D

theorem withDensity_measure_ne_zero_of_pos_on
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (D : α → ENNReal)
    {s : Set α} (hD : Measurable D) (hs : MeasurableSet s)
    (hμ : μ s ≠ 0) (hpos : ∀ a, a ∈ s → D a ≠ 0) :
    μ.withDensity D s ≠ 0 := by
  have hsupport_inter : Function.support D ∩ s = s := by
    ext a
    constructor
    · intro ha
      exact ha.2
    · intro ha
      exact ⟨hpos a ha, ha⟩
  have hμpos : 0 < μ s := by
    rwa [pos_iff_ne_zero]
  have hlin : 0 < ∫⁻ a in s, D a ∂μ := by
    rw [setLIntegral_pos_iff hD, hsupport_inter]
    exact hμpos
  rw [withDensity_apply D hs]
  exact ne_of_gt hlin

/--
Positive density on a measurable set gives positive real mass under a finite
`withDensity` measure.
-/
theorem withDensity_measureReal_pos_of_pos_on
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (D : α → ENNReal)
    {s : Set α} (hD : Measurable D) (hs : MeasurableSet s)
    (hμ : μ s ≠ 0) (hfinite : μ.withDensity D s ≠ ∞)
    (hpos : ∀ a, a ∈ s → D a ≠ 0) :
    0 < (μ.withDensity D).real s :=
  measureReal_pos_of_measure_ne_zero_ne_top (μ.withDensity D) s
    (withDensity_measure_ne_zero_of_pos_on μ D hD hs hμ hpos)
    hfinite

/--
A finite product of nonempty open real intervals has nonzero Lebesgue volume.
-/
theorem realPiOpenBox_volume_ne_zero
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) :
    (volume : Measure (ι → ℝ))
      (Set.pi Set.univ (fun i => Set.Ioo (a i) (b i))) ≠ 0 := by
  rw [Real.volume_pi_Ioo]
  exact Finset.prod_ne_zero_iff.mpr (by
    intro i _hi
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hab i))))

/--
A coordinate-difference affine hyperplane in a finite real product has
Lebesgue measure zero.
-/
theorem realPi_eval_sub_eq_volume_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) (b : ℝ) :
    (volume : Measure (ι → ℝ)) {x | x i - x j = b} = 0 := by
  classical
  let L : (ι → ℝ) →ₗ[ℝ] ℝ := {
    toFun x := x i - x j
    map_add' x y := by
      simp [Pi.add_apply]
      ring
    map_smul' a x := by
      simp [Pi.smul_apply]
      ring }
  let p : ι → ℝ := fun k => if k = i then b else 0
  let S : AffineSubspace ℝ (ι → ℝ) := AffineSubspace.mk' p L.ker
  have hp_i : p i = b := by simp [p]
  have hp_j : p j = 0 := by simp [p, hij.symm]
  have hS_eq : (S : Set (ι → ℝ)) = {x | x i - x j = b} := by
    ext x
    constructor
    · intro hx
      have hker : x -ᵥ p ∈ L.ker := by
        simpa [S] using hx
      have hL : L (x -ᵥ p) = 0 := by
        simpa [LinearMap.mem_ker] using hker
      simp [L, hp_i, hp_j] at hL
      change x i - x j = b
      linarith
    · intro hx
      have hL : L (x -ᵥ p) = 0 := by
        simp [L, hp_i, hp_j]
        change x i - x j = b at hx
        change x i - b - x j = 0
        linarith
      simpa [S, LinearMap.mem_ker] using hL
  have hS_ne_top : S ≠ ⊤ := by
    intro htop
    let q : ι → ℝ := fun k => if k = i then b + 1 else 0
    have hqS : q ∈ S := by
      rw [htop]
      trivial
    have hq : q i - q j = b := by
      have hqSset : q ∈ (S : Set (ι → ℝ)) := hqS
      rw [hS_eq] at hqSset
      exact hqSset
    have hqi : q i = b + 1 := by simp [q]
    have hqj : q j = 0 := by simp [q, hij.symm]
    linarith
  simpa [hS_eq] using
    (MeasureTheory.Measure.addHaar_affineSubspace
      (volume : Measure (ι → ℝ)) S hS_ne_top)

/--
Coordinate-difference affine hyperplanes remain null after applying an
arbitrary density to finite-product Lebesgue measure.
-/
theorem withDensity_realPi_eval_sub_eq_measure_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : (ι → ℝ) → ENNReal)
    {i j : ι} (hij : i ≠ j) (b : ℝ) :
    ((volume : Measure (ι → ℝ)).withDensity D) {x | x i - x j = b} = 0 :=
  (MeasureTheory.withDensity_absolutelyContinuous
    (volume : Measure (ι → ℝ)) D)
    (realPi_eval_sub_eq_volume_zero hij b)

/--
Positive density on a finite real open box gives nonzero mass to any set
containing that box.

This is the reusable support certificate for finite-dimensional RUM source
arguments: prove a concrete open box lies inside the desired source event, and
that the density is positive on the box.
-/
theorem withDensity_realPiOpenBox_measure_ne_zero_of_subset
    {ι : Type*} [Fintype ι]
    (D : (ι → ℝ) → ENNReal) (hD : Measurable D)
    {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    {s : Set (ι → ℝ)}
    (hsubset :
      Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)) ⊆ s)
    (hpos :
      ∀ x, x ∈ Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)) →
        D x ≠ 0) :
    ((volume : Measure (ι → ℝ)).withDensity D) s ≠ 0 := by
  let box : Set (ι → ℝ) :=
    Set.pi Set.univ (fun i => Set.Ioo (a i) (b i))
  have hbox_meas : MeasurableSet box := by
    dsimp [box]
    exact MeasurableSet.univ_pi (fun i => measurableSet_Ioo)
  have hbox_base_ne : (volume : Measure (ι → ℝ)) box ≠ 0 := by
    simpa [box] using realPiOpenBox_volume_ne_zero (a := a) (b := b) hab
  have hbox_density_ne :
      ((volume : Measure (ι → ℝ)).withDensity D) box ≠ 0 := by
    exact withDensity_measure_ne_zero_of_pos_on
      (volume : Measure (ι → ℝ)) D hD hbox_meas hbox_base_ne
      (by
        intro x hx
        exact hpos x (by simpa [box] using hx))
  exact ne_of_gt
    (lt_of_lt_of_le hbox_density_ne.bot_lt
      (measure_mono (by
        intro x hx
        exact hsubset (by simpa [box] using hx))))

/--
Hoeffding upper-tail bound for a finite sum of independent bounded variables,
centered by their expectations.

This is a thin finite-sum wrapper around Mathlib's sub-Gaussian Hoeffding
inequality. It keeps EC paper proofs from repeatedly unpacking
`HasSubgaussianMGF` when they only need a concentration bound for a finite
family of bounded independent random variables.
-/
theorem measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {X : ι → α → ℝ}
    (h_indep : iIndepFun X μ)
    {s : Finset ι} {a b ε : ℝ}
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b)
    (hε : 0 ≤ ε) :
    μ.real
        {ω | ε ≤
          ∑ i ∈ s, (X i ω - ∫ x, X i x ∂μ)} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ((∑ _ ∈ s, ((‖b - a‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  let centered : ι → α → ℝ :=
    fun i ω => X i ω - ∫ x, X i x ∂μ
  have hcenter_indep : iIndepFun centered μ := by
    exact h_indep.comp
      (fun i x => x - ∫ y, X i y ∂μ)
      (fun _ => measurable_id.sub measurable_const)
  have hsub :
      ∀ i ∈ s,
        HasSubgaussianMGF
          (centered i)
          ((‖b - a‖₊ / 2) ^ 2) μ := by
    intro i hi
    exact hasSubgaussianMGF_of_mem_Icc (h_meas i hi) (h_bound i hi)
  simpa [centered] using
    (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := μ) hcenter_indep (s := s) hsub hε)

/--
Kernel-level Hoeffding lemma for bounded centered variables.  If almost every
conditional measure supplied by a Markov kernel sees `X` as a measurable,
bounded, mean-zero real variable, then `X` is sub-Gaussian with respect to the
kernel.  This is the reusable bridge needed before applying mathlib's
conditional/Azuma-Hoeffding theorem to adapted finite selected-voter
increments.
-/
theorem kernel_hasSubgaussianMGF_of_ae_mem_Icc_of_integral_eq_zero
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} {κ : Kernel α β} [IsMarkovKernel κ]
    {X : β → ℝ} {a b : ℝ}
    (h_integrable :
      ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) (κ ∘ₘ ν))
    (h_meas : ∀ᵐ x ∂ν, AEMeasurable X (κ x))
    (h_bound : ∀ᵐ x ∂ν, ∀ᵐ ω ∂κ x, X ω ∈ Set.Icc a b)
    (h_mean : ∀ᵐ x ∂ν, ∫ ω, X ω ∂κ x = 0) :
    Kernel.HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) κ ν where
  integrable_exp_mul := h_integrable
  mgf_le := by
    filter_upwards [h_meas, h_bound, h_mean] with x hx_meas hx_bound hx_mean t
    exact
      (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (μ := κ x) (X := X) hx_meas hx_bound hx_mean).mgf_le t

/--
Conditional Hoeffding bridge stated through mathlib's conditional-expectation
kernel.  This is the usable form for an adapted bounded increment: establish
measurability, conditional range, and conditional mean zero against the
history sigma-algebra, then obtain the conditional sub-Gaussian certificate
consumed by Azuma--Hoeffding.

The hypotheses deliberately expose the conditional kernel rather than hiding
measurability behind an opaque ``martingale difference'' assumption.  For an
i.i.d. online learner, these are the three facts supplied by predictability of
the current predictor and independence of the next sample.
-/
theorem hasCondSubgaussianMGF_of_condExpKernel_mem_Icc_of_integral_eq_zero
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {a b : ℝ}
    (hm : m ≤ mΩ)
    (h_integrable :
      ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (h_meas :
      ∀ᵐ x ∂(μ.trim hm),
        AEMeasurable X (ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m x))
    (h_bound :
      ∀ᵐ x ∂(μ.trim hm),
        ∀ᵐ ω ∂ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m x,
          X ω ∈ Set.Icc a b)
    (h_mean :
      ∀ᵐ x ∂(μ.trim hm),
        ∫ ω, X ω ∂ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m x = 0) :
    ProbabilityTheory.HasCondSubgaussianMGF (mΩ := mΩ) m hm X
      ((‖b - a‖₊ / 2) ^ 2) μ := by
  change
    ProbabilityTheory.Kernel.HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2)
      (ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m) (μ.trim hm)
  exact
    @kernel_hasSubgaussianMGF_of_ae_mem_Icc_of_integral_eq_zero
      Ω Ω m mΩ (μ.trim hm)
      (ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m)
      inferInstance X a b
      (by
        intro t
        simpa [ProbabilityTheory.condExpKernel_comp_trim (mΩ := mΩ) (μ := μ) hm]
          using h_integrable t)
      h_meas h_bound h_mean

/-- Azuma--Hoeffding for a finite prefix of an adapted process with explicit
conditional sub-Gaussian certificates.  This names the standard endpoint in
the shared library and keeps paper developments independent of a particular
martingale implementation. -/
theorem measure_sum_ge_le_of_conditional_subgaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {cY : ℕ → NNReal} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) μ)
    (n : ℕ)
    (h_subG :
      ∀ i < n - 1,
        ProbabilityTheory.HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
          (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by
  exact ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
    h_adapted h0 n h_subG hε

/--
If a real process converges almost surely, then almost surely each path has an
eventual finite lower bound.  This is the deterministic pathwise step used when
turning martingale convergence into eventual fluctuation control.
-/
theorem ae_eventually_ge_of_ae_exists_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {S : ℕ → α → ℝ}
    (hconv :
      ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n : ℕ => S n ω) atTop (nhds c)) :
    ∀ᵐ ω ∂μ, ∃ lower : ℝ, ∃ T : ℕ,
      ∀ n : ℕ, T ≤ n → lower ≤ S n ω := by
  filter_upwards [hconv] with ω hω
  rcases hω with ⟨c, hc⟩
  have h_event :
      ∀ᶠ n : ℕ in atTop, c - 1 < S n ω := by
    exact hc.eventually (Ioi_mem_nhds (by linarith : c - 1 < c))
  rcases Filter.eventually_atTop.mp h_event with ⟨T, hT⟩
  exact ⟨c - 1, T, fun n hn => le_of_lt (hT n hn)⟩

/--
If a real process converges almost surely, then almost surely each path has an
eventual finite upper bound.
-/
theorem ae_eventually_le_of_ae_exists_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {S : ℕ → α → ℝ}
    (hconv :
      ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n : ℕ => S n ω) atTop (nhds c)) :
    ∀ᵐ ω ∂μ, ∃ upper : ℝ, ∃ T : ℕ,
      ∀ n : ℕ, T ≤ n → S n ω ≤ upper := by
  filter_upwards [hconv] with ω hω
  rcases hω with ⟨c, hc⟩
  have h_event :
      ∀ᶠ n : ℕ in atTop, S n ω < c + 1 := by
    exact hc.eventually (Iio_mem_nhds (by linarith : c < c + 1))
  rcases Filter.eventually_atTop.mp h_event with ⟨T, hT⟩
  exact ⟨c + 1, T, fun n hn => le_of_lt (hT n hn)⟩

/--
L1-bounded submartingales have an almost-sure eventual lower bound on each
path.  This packages Mathlib's a.e. martingale convergence theorem in the
shape needed by finite-dot fluctuation arguments.
-/
theorem ae_eventually_ge_of_submartingale_L1_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {S : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    (hS : Submartingale S ℱ μ)
    (hL1 : ∀ n : ℕ, eLpNorm (S n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, ∃ lower : ℝ, ∃ T : ℕ,
      ∀ n : ℕ, T ≤ n → lower ≤ S n ω := by
  exact ae_eventually_ge_of_ae_exists_tendsto μ
    (Submartingale.exists_ae_tendsto_of_bdd hS hL1)

/--
L1-bounded submartingales have an almost-sure eventual upper bound on each
path.
-/
theorem ae_eventually_le_of_submartingale_L1_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {S : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    (hS : Submartingale S ℱ μ)
    (hL1 : ∀ n : ℕ, eLpNorm (S n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, ∃ upper : ℝ, ∃ T : ℕ,
      ∀ n : ℕ, T ≤ n → S n ω ≤ upper := by
  exact ae_eventually_le_of_ae_exists_tendsto μ
    (Submartingale.exists_ae_tendsto_of_bdd hS hL1)

/--
Martingale specialization of
`ae_eventually_ge_of_submartingale_L1_bdd`.
-/
theorem ae_eventually_ge_of_martingale_L1_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {S : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    (hS : Martingale S ℱ μ)
    (hL1 : ∀ n : ℕ, eLpNorm (S n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, ∃ lower : ℝ, ∃ T : ℕ,
      ∀ n : ℕ, T ≤ n → lower ≤ S n ω := by
  exact ae_eventually_ge_of_submartingale_L1_bdd
    (hS := hS.submartingale) hL1

/--
Martingale specialization of
`ae_eventually_le_of_submartingale_L1_bdd`.
-/
theorem ae_eventually_le_of_martingale_L1_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {S : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    (hS : Martingale S ℱ μ)
    (hL1 : ∀ n : ℕ, eLpNorm (S n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, ∃ upper : ℝ, ∃ T : ℕ,
      ∀ n : ℕ, T ≤ n → S n ω ≤ upper := by
  exact ae_eventually_le_of_submartingale_L1_bdd
    (hS := hS.submartingale) hL1

/--
Probability-space `L2`-bounded martingales have an almost-sure eventual upper
bound on each path.  This is the square-summable-moment handoff shape used
before invoking Mathlib's `L1` martingale convergence theorem.
-/
theorem ae_eventually_le_of_martingale_L2_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {S : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    (hS : Martingale S ℱ μ)
    (hL2 : ∀ n : ℕ, eLpNorm (S n) 2 μ ≤ R) :
    ∀ᵐ ω ∂μ, ∃ upper : ℝ, ∃ T : ℕ,
      ∀ n : ℕ, T ≤ n → S n ω ≤ upper := by
  exact ae_eventually_le_of_martingale_L1_bdd
    (hS := hS)
    (hL1 := fun n =>
      (eLpNorm_le_eLpNorm_of_exponent_le
        (μ := μ) (f := S n)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        ((hS.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable).trans
          (hL2 n))

/--
For real random variables, a concrete second-moment bound supplies the
corresponding `eLpNorm _ 2` bound.  This keeps martingale-convergence callers
from having to state their square-moment estimates directly in `ENNReal`
seminorm form.
-/
theorem eLpNorm_two_le_nnreal_of_integral_sq_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} {R : ℝ≥0}
    (hX : MemLp X 2 μ)
    (hsecond : (∫ ω, X ω ^ 2 ∂μ) ≤ (R : ℝ) ^ 2) :
    eLpNorm X 2 μ ≤ R := by
  rw [hX.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top]
  have hnorm_sq :
      (∫ ω, ‖X ω‖ ^ (2 : ℝ) ∂μ) = ∫ ω, X ω ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have hsecond_norm :
      (∫ ω, ‖X ω‖ ^ (2 : ℝ) ∂μ) ≤ (R : ℝ) ^ 2 := by
    simpa [hnorm_sq] using hsecond
  have hroot :
      (∫ ω, ‖X ω‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) ≤ (R : ℝ) := by
    have hsqrt :
        √(∫ ω, ‖X ω‖ ^ (2 : ℝ) ∂μ) ≤ √((R : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt hsecond_norm
    rw [show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) by norm_num,
      ← Real.sqrt_eq_rpow]
    exact hsqrt.trans_eq (Real.sqrt_sq R.2)
  simpa [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num] using
    (ENNReal.ofReal_le_ofReal hroot)

/-- The square of a real-valued `L²` martingale is a submartingale.  This is
the conditional-Jensen bridge used by maximal-inequality arguments. -/
theorem martingale_sq_submartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {S : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (hS : Martingale S ℱ μ)
    (hL2 : ∀ n : ℕ, MemLp (S n) 2 μ) :
    Submartingale (fun n ω => (S n ω) ^ 2) ℱ μ := by
  refine submartingale_nat ?_ ?_ ?_
  · intro n
    exact (hS.stronglyAdapted n).pow 2
  · intro n
    simpa using (hL2 n).integrable_sq
  · intro n
    have hJensen :=
      ((by norm_num : Even 2).convexOn_pow).map_condExp_le_univ
        (ℱ.le n) (continuous_pow 2).lowerSemicontinuous
        (hS.integrable (n + 1)) (by
          simpa [Function.comp_def] using (hL2 (n + 1)).integrable_sq)
    filter_upwards [hJensen, hS.condExp_ae_eq (Nat.le_succ n)] with ω hω hmartingale
    simpa [Function.comp_def, hmartingale] using hω

/-- Markov's second-moment estimate in a form convenient for real-valued
random variables. -/
theorem ennreal_mul_measure_sq_event_le_integral_sq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : Ω → ℝ}
    (hX_sq_int : Integrable (fun ω => (X ω) ^ 2) μ)
    (threshold : ℝ≥0) :
    threshold * μ {ω | (threshold : ℝ) ≤ (X ω) ^ 2} ≤
      ENNReal.ofReal (∫ ω, (X ω) ^ 2 ∂μ) := by
  have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ (X ω) ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hmarkov := MeasureTheory.mul_meas_ge_le_lintegral₀
    (hX_sq_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal) threshold
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hX_sq_int hnonneg] at hmarkov
  have hevent : {ω | (threshold : ℝ≥0∞) ≤ ENNReal.ofReal ((X ω) ^ 2)} =
      {ω | (threshold : ℝ) ≤ (X ω) ^ 2} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)
  rw [hevent] at hmarkov
  exact hmarkov

/-- Doob's maximal inequality for the squared values of a real `L²`
martingale, with the right-hand side enlarged to its terminal second moment. -/
theorem ennreal_mul_measure_range_sup_sq_le_integral_sq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {S : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (hS : Martingale S ℱ μ)
    (hL2 : ∀ n : ℕ, MemLp (S n) 2 μ)
    (threshold : ℝ≥0) (n : ℕ) :
    threshold * μ {ω | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => (S k ω) ^ 2)} ≤
      ENNReal.ofReal (∫ ω, (S n ω) ^ 2 ∂μ) := by
  let event : Set Ω := {ω | (threshold : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => (S k ω) ^ 2)}
  have hdoob := MeasureTheory.maximal_ineq
    (martingale_sq_submartingale hS hL2)
    (fun k ω => sq_nonneg (S k ω)) (ε := threshold) n
  change threshold * μ event ≤ ENNReal.ofReal (∫ ω, (S n ω) ^ 2 ∂μ)
  calc
    threshold * μ event ≤ ENNReal.ofReal (∫ ω in event, (S n ω) ^ 2 ∂μ) := by
      simpa [event] using hdoob
    _ ≤ ENNReal.ofReal (∫ ω, (S n ω) ^ 2 ∂μ) := by
      apply ENNReal.ofReal_le_ofReal
      exact setIntegral_le_integral (hL2 n).integrable_sq
        (Filter.Eventually.of_forall fun ω => sq_nonneg (S n ω))

/-- The fourth power of a real-valued `L⁴` martingale is a submartingale.
This is the fourth-moment analogue of `martingale_sq_submartingale` and is
useful for modulus estimates where a second-moment maximal bound is not
summable over time blocks. -/
theorem martingale_fourth_submartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {S : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (hS : Martingale S ℱ μ)
    (hL4 : ∀ n : ℕ, MemLp (S n) 4 μ) :
    Submartingale (fun n ω => (S n ω) ^ 4) ℱ μ := by
  have hEven : Even (4 : ℕ) := Nat.even_iff.mpr (by norm_num)
  have hintegrable_fourth : ∀ n : ℕ, Integrable (fun ω => (S n ω) ^ 4) μ := by
    intro n
    rw [← memLp_one_iff_integrable]
    convert (hL4 n).norm_rpow (by norm_num) ENNReal.ofNat_ne_top using 1
    ext ω
    norm_num [Real.norm_eq_abs]
    calc
      S n ω ^ 4 = (S n ω ^ 2) ^ 2 := by ring
      _ = (|S n ω| ^ 2) ^ 2 := by rw [sq_abs]
      _ = |S n ω| ^ 4 := by ring
  refine submartingale_nat ?_ ?_ ?_
  · intro n
    exact (hS.stronglyAdapted n).pow 4
  · intro n
    exact hintegrable_fourth n
  · intro n
    have hJensen :=
      hEven.convexOn_pow.map_condExp_le_univ
        (ℱ.le n) (continuous_pow 4).lowerSemicontinuous
        (hS.integrable (n + 1)) (by
          simpa [Function.comp_def] using hintegrable_fourth (n + 1))
    filter_upwards [hJensen, hS.condExp_ae_eq (Nat.le_succ n)] with ω hω hmartingale
    simpa [Function.comp_def, hmartingale] using hω

/-- Doob's maximal inequality at fourth-moment scale for a real `L⁴`
martingale.  Applying the ordinary nonnegative submartingale inequality to
the fourth power gives the form suited to a fourth-moment modulus estimate. -/
theorem ennreal_mul_measure_range_sup_fourth_le_integral_fourth
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {S : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (hS : Martingale S ℱ μ)
    (hL4 : ∀ n : ℕ, MemLp (S n) 4 μ)
    (threshold : ℝ≥0) (n : ℕ) :
    threshold * μ {ω | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => (S k ω) ^ 4)} ≤
      ENNReal.ofReal (∫ ω, (S n ω) ^ 4 ∂μ) := by
  have hEven : Even (4 : ℕ) := Nat.even_iff.mpr (by norm_num)
  have hintegrable_fourth : Integrable (fun ω => (S n ω) ^ 4) μ := by
    rw [← memLp_one_iff_integrable]
    convert (hL4 n).norm_rpow (by norm_num) ENNReal.ofNat_ne_top using 1
    ext ω
    norm_num [Real.norm_eq_abs]
    calc
      S n ω ^ 4 = (S n ω ^ 2) ^ 2 := by ring
      _ = (|S n ω| ^ 2) ^ 2 := by rw [sq_abs]
      _ = |S n ω| ^ 4 := by ring
  let event : Set Ω := {ω | (threshold : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => (S k ω) ^ 4)}
  have hdoob := MeasureTheory.maximal_ineq
    (martingale_fourth_submartingale hS hL4)
    (fun k ω => hEven.pow_nonneg (S k ω)) (ε := threshold) n
  change threshold * μ event ≤ ENNReal.ofReal (∫ ω, (S n ω) ^ 4 ∂μ)
  calc
    threshold * μ event ≤ ENNReal.ofReal (∫ ω in event, (S n ω) ^ 4 ∂μ) := by
      simpa [event] using hdoob
    _ ≤ ENNReal.ofReal (∫ ω, (S n ω) ^ 4 ∂μ) := by
      apply ENNReal.ofReal_le_ofReal
      exact setIntegral_le_integral hintegrable_fourth
        (Filter.Eventually.of_forall fun ω => hEven.pow_nonneg (S n ω))

/-- The conditional second moment of a centered indicator is its Bernoulli
variance whenever the conditional mean is `g`.  The integrability hypotheses
make this a reusable conditional-expectation algebra lemma, independent of
any particular stochastic-process construction. -/
theorem condExp_centered_indicator_sq_eq_conditional_variance
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {m : MeasurableSpace Ω} {f g : Ω → ℝ}
    (hf : Integrable f μ)
    (hcoefficient_f : Integrable ((fun ω => 1 - 2 * g ω) * f) μ)
    (hgsq : Integrable (g ^ 2) μ)
    (hm : m ≤ mΩ)
    (hgstrong : StronglyMeasurable[m] g)
    (hmean : μ[f | m] =ᵐ[μ] g)
    (hindicator : ∀ᵐ ω ∂μ, f ω ^ 2 = f ω) :
    μ[(fun ω => (f ω - g ω) ^ 2) | m] =ᵐ[μ]
      fun ω => g ω * (1 - g ω) := by
  let coefficient : Ω → ℝ := fun ω => 1 - 2 * g ω
  have hcoefficient_strong : StronglyMeasurable[m] coefficient := by
    dsimp [coefficient]
    exact stronglyMeasurable_const.sub (hgstrong.const_mul 2)
  have hcentered_sq : ∀ᵐ ω ∂μ,
      (f ω - g ω) ^ 2 = coefficient ω * f ω + g ω ^ 2 := by
    filter_upwards [hindicator] with ω hω
    dsimp [coefficient]
    nlinarith
  calc
    μ[(fun ω => (f ω - g ω) ^ 2) | m] =ᵐ[μ]
        μ[coefficient * f + fun ω => g ω ^ 2 | m] := by
          apply condExp_congr_ae
          simpa [coefficient, Pi.mul_apply] using hcentered_sq
    _ =ᵐ[μ] μ[coefficient * f | m] +
          μ[fun ω => g ω ^ 2 | m] :=
      condExp_add hcoefficient_f hgsq _
    _ =ᵐ[μ] coefficient * μ[f | m] + fun ω => g ω ^ 2 := by
      exact (condExp_mul_of_stronglyMeasurable_left hcoefficient_strong
        hcoefficient_f hf).add
          (by
            change μ[g ^ 2 | m] =ᵐ[μ] g ^ 2
            exact Filter.Eventually.of_forall fun ω =>
              congrFun (condExp_of_stronglyMeasurable (μ := μ) hm
                (hgstrong.pow 2) hgsq) ω)
    _ =ᵐ[μ] fun ω => g ω * (1 - g ω) := by
      filter_upwards [hmean] with ω hω
      change coefficient ω * μ[f | m] ω + g ω ^ 2 = g ω * (1 - g ω)
      rw [hω]
      dsimp [coefficient]
      ring

/--
Partial sums of a strongly adapted real process are strongly adapted to the
same filtration.
-/
theorem stronglyAdapted_partial_sum_of_stronglyAdapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (hY : StronglyAdapted ℱ Y) :
    StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω) := by
  intro n
  have hsum : StronglyMeasurable[ℱ n] (∑ i ∈ Finset.range n, Y i) :=
    Finset.stronglyMeasurable_sum (Finset.range n) fun i hi =>
      (hY i).mono (ℱ.mono (Nat.le_of_lt (Finset.mem_range.mp hi)))
  convert hsum using 1
  ext ω
  simp

/--
Centered partial sums are a martingale when their one-step increments have
zero conditional expectation.  The statement keeps the adaptedness and
integrability hypotheses on the partial-sum process, which is the shape most
often available after a concrete sampling construction has supplied the
one-step mean-zero fact.
-/
theorem martingale_partial_sum_of_condExp_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hintegrable :
      ∀ n : ℕ, Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ)
    (hcond_zero : ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0) :
    Martingale (fun n ω => ∑ i ∈ Finset.range n, Y i ω) ℱ μ := by
  let S : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n, Y i ω
  have hcond :
      ∀ n : ℕ, μ[S (n + 1) - S n | ℱ n] =ᵐ[μ] 0 := by
    intro n
    have hinc :
        (fun ω => S (n + 1) ω - S n ω) =ᵐ[μ] Y n := by
      exact Filter.Eventually.of_forall fun ω => by
        change
          (∑ i ∈ Finset.range (n + 1), Y i ω) -
              (∑ i ∈ Finset.range n, Y i ω) =
            Y n ω
        rw [Finset.sum_range_succ]
        ring
    exact (condExp_congr_ae hinc).trans (hcond_zero n)
  exact
    MeasureTheory.martingale_of_condExp_sub_eq_zero_nat
      (𝒢 := ℱ) (f := S) hadapted hintegrable hcond

/--
Partial-sum version of martingale convergence: adapted, integrable centered
increments with zero conditional expectation and an L1-bounded partial-sum
process are eventually bounded above almost surely.
-/
theorem ae_eventually_le_of_partial_sum_condExp_zero_L1_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    (hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hintegrable :
      ∀ n : ℕ, Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ)
    (hcond_zero : ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (hL1 :
      ∀ n : ℕ, eLpNorm (fun ω => ∑ i ∈ Finset.range n, Y i ω) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, ∃ upper : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
      (∑ i ∈ Finset.range n, Y i ω) ≤ upper := by
  exact ae_eventually_le_of_martingale_L1_bdd
    (hS := martingale_partial_sum_of_condExp_eq_zero
      (Y := Y) (ℱ := ℱ) hadapted hintegrable hcond_zero)
    hL1

/--
Partial-sum version of the `L2` martingale-convergence adapter: adapted,
integrable centered increments with zero conditional expectation and an
`L2`-bounded partial-sum process are eventually bounded above almost surely.
-/
theorem ae_eventually_le_of_partial_sum_condExp_zero_L2_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    (hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hintegrable :
      ∀ n : ℕ, Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ)
    (hcond_zero : ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (hL2 :
      ∀ n : ℕ, eLpNorm (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ ≤ R) :
    ∀ᵐ ω ∂μ, ∃ upper : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
      (∑ i ∈ Finset.range n, Y i ω) ≤ upper := by
  exact ae_eventually_le_of_martingale_L2_bdd
    (hS := martingale_partial_sum_of_condExp_eq_zero
      (Y := Y) (ℱ := ℱ) hadapted hintegrable hcond_zero)
    hL2

/--
Second-moment form of the partial-sum martingale-convergence adapter.  This is
the paper-facing square-summable-moment shape: once a caller proves a uniform
bound on the second moments of the centered partial sums, the `L2` seminorm
premise is discharged mechanically.
-/
theorem ae_eventually_le_of_partial_sum_condExp_zero_secondMoment_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    (hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hintegrable :
      ∀ n : ℕ, Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ)
    (hmemL2 :
      ∀ n : ℕ, MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ)
    (hcond_zero : ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (hsecond :
      ∀ n : ℕ,
        (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) ≤ (R : ℝ) ^ 2) :
    ∀ᵐ ω ∂μ, ∃ upper : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
      (∑ i ∈ Finset.range n, Y i ω) ≤ upper := by
  exact ae_eventually_le_of_partial_sum_condExp_zero_L2_bdd
    (Y := Y) (ℱ := ℱ) hadapted hintegrable hcond_zero
    (fun n =>
      eLpNorm_two_le_nnreal_of_integral_sq_le
        (hX := hmemL2 n) (hsecond := hsecond n))

/--
Orthogonality from conditional mean zero.  If `f` is measurable with respect
to a sub-sigma-algebra and `g` has zero conditional expectation there, then the
cross integral of `f * g` is zero.
-/
theorem integral_mul_eq_zero_of_stronglyMeasurable_condExp_eq_zero
    {Ω : Type*} {mΩ m : MeasurableSpace Ω} {μ : @Measure Ω mΩ}
    [IsFiniteMeasure μ]
    {f g : Ω → ℝ}
    (hm : m ≤ mΩ)
    (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (f * g) μ)
    (hg : Integrable g μ)
    (hcond_zero : μ[g | m] =ᵐ[μ] 0) :
    ∫ ω, f ω * g ω ∂μ = 0 := by
  have hpull :
      μ[f * g | m] =ᵐ[μ] f * μ[g | m] := by
    exact condExp_mul_of_stronglyMeasurable_left hf hfg hg
  have hce_zero : μ[f * g | m] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hcond_zero] with ω hpullω hzeroω
    simpa [Pi.mul_apply, hzeroω] using hpullω
  calc
    ∫ ω, f ω * g ω ∂μ = ∫ ω, (μ[f * g | m]) ω ∂μ := by
      exact (integral_condExp (μ := μ) (m := m) (m₀ := mΩ) hm
        (f := f * g)).symm
    _ = ∫ ω, (0 : ℝ) ∂μ := integral_congr_ae hce_zero
    _ = 0 := by simp

/--
Partial-sum orthogonality from one-step conditional mean zero.
-/
theorem partial_sum_cross_integral_eq_zero_of_condExp_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hcross_int :
      ∀ n : ℕ,
        Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) μ)
    (hY_integrable : ∀ n : ℕ, Integrable (Y n) μ)
    (hcond_zero : ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0) :
    ∀ n : ℕ,
      (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) = 0 := by
  intro n
  exact
    integral_mul_eq_zero_of_stronglyMeasurable_condExp_eq_zero
      (m := ℱ n)
      (hm := ℱ.le n)
      (hf := hadapted n)
      (hfg := hcross_int n)
      (hg := hY_integrable n)
      (hcond_zero := hcond_zero n)

/--
Nonpositive cross-moment corollary of partial-sum orthogonality.
-/
theorem partial_sum_cross_integral_nonpos_of_condExp_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hcross_int :
      ∀ n : ℕ,
        Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) μ)
    (hY_integrable : ∀ n : ℕ, Integrable (Y n) μ)
    (hcond_zero : ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0) :
    ∀ n : ℕ,
      (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) ≤ 0 := by
  intro n
  rw [partial_sum_cross_integral_eq_zero_of_condExp_eq_zero
    hadapted hcross_int hY_integrable hcond_zero n]

/-- Centering a square-integrable real variable cannot increase its second
moment on a probability space. -/
theorem integral_sq_sub_integral_le_integral_sq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) :
    (∫ ω, (X ω - ∫ z, X z ∂μ) ^ 2 ∂μ) ≤ ∫ ω, X ω ^ 2 ∂μ := by
  rw [← ProbabilityTheory.variance_eq_integral hX.aemeasurable]
  exact ProbabilityTheory.variance_le_expectation_sq hX.aestronglyMeasurable

/--
On a probability space, an almost-sure absolute bound gives a second-moment
bound.
-/
theorem integral_sq_le_sq_of_ae_abs_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ}
    (hX_sq_int : Integrable (fun ω => (X ω) ^ 2) μ)
    (hc : 0 ≤ c)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ c) :
    (∫ ω, (X ω) ^ 2 ∂μ) ≤ c ^ 2 := by
  have hle :
      (fun ω => (X ω) ^ 2) ≤ᵐ[μ] fun _ : Ω => c ^ 2 := by
    filter_upwards [hbound] with ω hω
    exact sq_le_sq.2 (by simpa [abs_of_nonneg hc] using hω)
  calc
    (∫ ω, (X ω) ^ 2 ∂μ) ≤ ∫ _ : Ω, c ^ 2 ∂μ := by
      exact integral_mono_ae hX_sq_int (integrable_const (c ^ 2)) hle
    _ = c ^ 2 := by simp

/--
Sequence form of `integral_sq_le_sq_of_ae_abs_le`.
-/
theorem integral_sq_le_sq_of_ae_abs_le_sequence
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    (hY_sq_int : ∀ n : ℕ, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hc : ∀ n : ℕ, 0 ≤ c n)
    (hbound : ∀ n : ℕ, ∀ᵐ ω ∂μ, |Y n ω| ≤ c n) :
    ∀ n : ℕ, (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ (c n) ^ 2 := by
  intro n
  exact integral_sq_le_sq_of_ae_abs_le
    (hX_sq_int := hY_sq_int n) (hc := hc n) (hbound := hbound n)

/--
On a finite measure space, an a.e. bounded real random variable has integrable
square.
-/
theorem integrable_sq_of_ae_abs_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} {c : ℝ}
    (hX : AEStronglyMeasurable X μ)
    (hc : 0 ≤ c)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ c) :
    Integrable (fun ω => (X ω) ^ 2) μ := by
  refine Integrable.of_bound (C := c ^ 2) ?_ ?_
  · exact hX.pow 2
  · filter_upwards [hbound] with ω hω
    have hsq : (X ω) ^ 2 ≤ c ^ 2 := by
      exact sq_le_sq.2 (by simpa [abs_of_nonneg hc] using hω)
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω))] using hsq

/--
Sequence form of `integrable_sq_of_ae_abs_le`.
-/
theorem integrable_sq_of_ae_abs_le_sequence
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    (hY : ∀ n : ℕ, AEStronglyMeasurable (Y n) μ)
    (hc : ∀ n : ℕ, 0 ≤ c n)
    (hbound : ∀ n : ℕ, ∀ᵐ ω ∂μ, |Y n ω| ≤ c n) :
    ∀ n : ℕ, Integrable (fun ω => (Y n ω) ^ 2) μ := by
  intro n
  exact integrable_sq_of_ae_abs_le
    (hX := hY n) (hc := hc n) (hbound := hbound n)

/--
A nonnegative summable real sequence has uniformly bounded finite partial sums,
with the bound packaged as a square of an `NNReal`.
-/
theorem exists_nnreal_sq_bound_of_summable_nonneg
    {b : ℕ → ℝ}
    (hsum : Summable b)
    (hnonneg : ∀ n : ℕ, 0 ≤ b n) :
    ∃ R : ℝ≥0, ∀ n : ℕ, (∑ i ∈ Finset.range n, b i) ≤ (R : ℝ) ^ 2 := by
  let S : ℝ := ∑' n : ℕ, b n
  let R : ℝ≥0 := ⟨max 1 S, by
    exact le_trans zero_le_one (le_max_left 1 S)⟩
  refine ⟨R, ?_⟩
  intro n
  have hpartial : (∑ i ∈ Finset.range n, b i) ≤ S := by
    exact hsum.sum_le_tsum (Finset.range n) (fun i _hi => hnonneg i)
  have hR_ge_one : (1 : ℝ) ≤ max 1 S := le_max_left 1 S
  have hR_ge_S : S ≤ max 1 S := le_max_right 1 S
  have hR_le_sq : max 1 S ≤ (max 1 S) ^ 2 := by
    nlinarith [hR_ge_one]
  have hS_le_sq : S ≤ (max 1 S) ^ 2 := le_trans hR_ge_S hR_le_sq
  exact le_trans hpartial (by simpa [R] using hS_le_sq)

/--
Finite partial-sum second-moment induction with explicit cross-term control.
If each increment has second moment at most `b n` and the current partial sum
has nonpositive cross moment with the next increment, then the second moment of
the partial sum is bounded by the accumulated `b` values.
-/
theorem partial_sum_secondMoment_le_sum_of_cross_nonpos
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {Y : ℕ → Ω → ℝ} {b : ℕ → ℝ}
    (hsum_sq_int :
      ∀ n : ℕ, Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2) μ)
    (hcross_int :
      ∀ n : ℕ,
        Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) μ)
    (hY_sq_int : ∀ n : ℕ, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hY_second :
      ∀ n : ℕ, (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ b n)
    (hcross_nonpos :
      ∀ n : ℕ,
        (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) ≤ 0) :
    ∀ n : ℕ,
      (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) ≤
        ∑ i ∈ Finset.range n, b i := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hsplit :
          (∫ ω, (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2 ∂μ) =
            (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) +
              2 * (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) +
                ∫ ω, (Y n ω) ^ 2 ∂μ := by
        have hpoint :
            (fun ω => (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2) =ᵐ[μ]
              fun ω =>
                (∑ i ∈ Finset.range n, Y i ω) ^ 2 +
                  2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω) +
                    (Y n ω) ^ 2 := by
          exact Filter.Eventually.of_forall fun ω => by
            change
              (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2 =
                (∑ i ∈ Finset.range n, Y i ω) ^ 2 +
                  2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω) +
                    (Y n ω) ^ 2
            rw [Finset.sum_range_succ]
            ring
        calc
          (∫ ω, (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2 ∂μ)
              = ∫ ω,
                  (∑ i ∈ Finset.range n, Y i ω) ^ 2 +
                    2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω) +
                      (Y n ω) ^ 2 ∂μ := integral_congr_ae hpoint
          _ = (∫ ω,
                  (∑ i ∈ Finset.range n, Y i ω) ^ 2 +
                    2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω) ∂μ) +
                ∫ ω, (Y n ω) ^ 2 ∂μ := by
              exact integral_add
                ((hsum_sq_int n).add ((hcross_int n).const_mul 2))
                (hY_sq_int n)
          _ = ((∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) +
                  ∫ ω, 2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω) ∂μ) +
                ∫ ω, (Y n ω) ^ 2 ∂μ := by
              rw [integral_add (hsum_sq_int n) ((hcross_int n).const_mul 2)]
          _ = (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) +
                2 * (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) +
                  ∫ ω, (Y n ω) ^ 2 ∂μ := by
              rw [integral_const_mul]
      calc
        (∫ ω, (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2 ∂μ)
            = (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) +
                2 * (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) +
                  ∫ ω, (Y n ω) ^ 2 ∂μ := hsplit
        _ ≤ (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) +
              ∫ ω, (Y n ω) ^ 2 ∂μ := by
            have hcross := hcross_nonpos n
            linarith
        _ ≤ (∑ i ∈ Finset.range n, b i) + b n := by
            exact add_le_add ih (hY_second n)
        _ = ∑ i ∈ Finset.range (n + 1), b i := by
            rw [Finset.sum_range_succ]

/-- Exact second-moment identity for a finite sum with pairwise successive
cross moments equal to zero.  This is the predictable-variance form of the
usual martingale orthogonality calculation. -/
theorem partial_sum_secondMoment_eq_sum_of_cross_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {Y : ℕ → Ω → ℝ} {v : ℕ → ℝ}
    (hsum_sq_int :
      ∀ n : ℕ, Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2) μ)
    (hcross_int :
      ∀ n : ℕ,
        Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) μ)
    (hY_sq_int : ∀ n : ℕ, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hY_second :
      ∀ n : ℕ, (∫ ω, (Y n ω) ^ 2 ∂μ) = v n)
    (hcross_zero :
      ∀ n : ℕ,
        (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) = 0) :
    ∀ n : ℕ,
      (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) =
        ∑ i ∈ Finset.range n, v i := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hsplit :
          (∫ ω, (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2 ∂μ) =
            (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) +
              2 * (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) +
                ∫ ω, (Y n ω) ^ 2 ∂μ := by
        have hpoint :
            (fun ω => (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2) =ᵐ[μ]
              fun ω =>
                (∑ i ∈ Finset.range n, Y i ω) ^ 2 +
                  2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω) +
                    (Y n ω) ^ 2 := by
          exact Filter.Eventually.of_forall fun ω => by
            change
              (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2 =
                (∑ i ∈ Finset.range n, Y i ω) ^ 2 +
                  2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω) +
                    (Y n ω) ^ 2
            rw [Finset.sum_range_succ]
            ring
        calc
          (∫ ω, (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2 ∂μ)
              = ∫ ω,
                  (∑ i ∈ Finset.range n, Y i ω) ^ 2 +
                    2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω) +
                      (Y n ω) ^ 2 ∂μ := integral_congr_ae hpoint
          _ = (∫ ω,
                  (∑ i ∈ Finset.range n, Y i ω) ^ 2 +
                    2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω) ∂μ) +
                ∫ ω, (Y n ω) ^ 2 ∂μ := by
              exact integral_add
                ((hsum_sq_int n).add ((hcross_int n).const_mul 2))
                (hY_sq_int n)
          _ = ((∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) +
                  ∫ ω, 2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω) ∂μ) +
                ∫ ω, (Y n ω) ^ 2 ∂μ := by
              rw [integral_add (hsum_sq_int n) ((hcross_int n).const_mul 2)]
          _ = (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) +
                2 * (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) +
                  ∫ ω, (Y n ω) ^ 2 ∂μ := by
              rw [integral_const_mul]
      calc
        (∫ ω, (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2 ∂μ)
            = (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) +
                2 * (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) +
                  ∫ ω, (Y n ω) ^ 2 ∂μ := hsplit
        _ = (∑ i ∈ Finset.range n, v i) + v n := by
            rw [ih, hcross_zero n, hY_second n]
            ring
        _ = ∑ i ∈ Finset.range (n + 1), v i := by
            rw [Finset.sum_range_succ]

/--
Uniform version of `partial_sum_secondMoment_le_sum_of_cross_nonpos`.
-/
theorem partial_sum_secondMoment_le_of_cross_nonpos
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {Y : ℕ → Ω → ℝ} {b : ℕ → ℝ} {R : ℝ≥0}
    (hsum_sq_int :
      ∀ n : ℕ, Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2) μ)
    (hcross_int :
      ∀ n : ℕ,
        Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) μ)
    (hY_sq_int : ∀ n : ℕ, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hY_second :
      ∀ n : ℕ, (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ b n)
    (hcross_nonpos :
      ∀ n : ℕ,
        (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) ≤ 0)
    (hbound : ∀ n : ℕ, (∑ i ∈ Finset.range n, b i) ≤ (R : ℝ) ^ 2) :
    ∀ n : ℕ,
      (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) ≤ (R : ℝ) ^ 2 := by
  intro n
  exact
    (partial_sum_secondMoment_le_sum_of_cross_nonpos
      (Y := Y) (b := b) hsum_sq_int hcross_int hY_sq_int hY_second
      hcross_nonpos n).trans (hbound n)

/--
Borel-Cantelli pathwise eventual-control wrapper for bad events.  If the
probabilities of bad events are summable, then almost surely there is a tail
after which no bad event occurs.
-/
theorem ae_eventually_notMem_of_tsum_measure_ne_top
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {bad : ℕ → Set α}
    (hsum : (∑' n, μ (bad n)) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n → ω ∉ bad n := by
  have hbc :
      ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, ω ∉ bad n :=
    MeasureTheory.ae_eventually_notMem (μ := μ) (s := bad) hsum
  filter_upwards [hbc] with ω hω
  rcases Filter.eventually_atTop.mp hω with ⟨T, hT⟩
  exact ⟨T, fun n hn => hT n hn⟩

/--
The real-valued countable union bound.  The ENNReal sum is required to be
finite before taking `toReal`; this is the form needed when a summable
per-round confidence allocation controls the probability that *any* round
fails.
-/
theorem measureReal_iUnion_le_tsum
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (bad : ℕ → Set α)
    (hsum : (∑' n, μ (bad n)) ≠ ∞) :
    μ.real (⋃ n, bad n) ≤ ∑' n, μ.real (bad n) := by
  change (μ (⋃ n, bad n)).toReal ≤ ∑' n, (μ (bad n)).toReal
  rw [← ENNReal.tsum_toReal_eq (fun n => measure_ne_top μ (bad n))]
  exact ENNReal.toReal_mono hsum (measure_iUnion_le bad)

/--
Predicate form of `ae_eventually_notMem_of_tsum_measure_ne_top`.
-/
theorem ae_eventually_not_of_tsum_measure_setOf_ne_top
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {bad : ℕ → α → Prop}
    (hsum : (∑' n, μ {ω | bad n ω}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n → ¬ bad n ω := by
  simpa using
    ae_eventually_notMem_of_tsum_measure_ne_top
      (μ := μ) (bad := fun n => {ω | bad n ω}) hsum

/--
Real-valued Borel-Cantelli corollary.  If the events where `lhs n` exceeds
`rhs n` have summable probabilities, then almost surely `lhs n <= rhs n`
eventually.
-/
theorem ae_eventually_le_of_tsum_measure_lt_ne_top
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {lhs rhs : ℕ → α → ℝ}
    (hsum : (∑' n, μ {ω | rhs n ω < lhs n ω}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n → lhs n ω ≤ rhs n ω := by
  have hbc :
      ∀ᵐ ω ∂μ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n → ¬ rhs n ω < lhs n ω :=
    ae_eventually_not_of_tsum_measure_setOf_ne_top
      (μ := μ) (bad := fun n ω => rhs n ω < lhs n ω) hsum
  filter_upwards [hbc] with ω hω
  rcases hω with ⟨T, hT⟩
  exact ⟨T, fun n hn => not_lt.mp (hT n hn)⟩

/--
Convert real-valued per-event bounds into the ENNReal summability hypothesis
used by Borel-Cantelli.
-/
theorem tsum_measure_ne_top_of_measureReal_le_of_tsum_ofReal_ne_top
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {bad : ℕ → Set α} {bound : ℕ → ℝ}
    (hbound_nonneg : ∀ n : ℕ, 0 ≤ bound n)
    (hle : ∀ n : ℕ, μ.real (bad n) ≤ bound n)
    (hsum_bound : (∑' n, ENNReal.ofReal (bound n)) ≠ ∞) :
    (∑' n, μ (bad n)) ≠ ∞ := by
  have hterm :
      ∀ n : ℕ, μ (bad n) ≤ ENNReal.ofReal (bound n) := by
    intro n
    exact
      (ENNReal.le_ofReal_iff_toReal_le
        (measure_ne_top μ (bad n)) (hbound_nonneg n)).2
        (by simpa [Measure.real] using hle n)
  have hsum_le :
      (∑' n, μ (bad n)) ≤ ∑' n, ENNReal.ofReal (bound n) :=
    ENNReal.tsum_le_tsum hterm
  exact
    (lt_top_iff_ne_top.mp
      (lt_of_le_of_lt hsum_le (lt_top_iff_ne_top.mpr hsum_bound)))

/--
Countable union bound with real-valued per-event budgets.  Unlike the
Borel--Cantelli wrappers above, this controls the probability that an event
fails at least once, rather than only the tail event of infinitely many
failures.
-/
theorem measureReal_iUnion_le_tsum_ofReal_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (bad : ℕ → Set α) (bound : ℕ → ℝ)
    (hbound_nonneg : ∀ n : ℕ, 0 ≤ bound n)
    (hle : ∀ n : ℕ, μ.real (bad n) ≤ bound n)
    (hsum_bound : (∑' n, ENNReal.ofReal (bound n)) ≠ ∞) :
    μ.real (⋃ n, bad n) ≤ (∑' n, ENNReal.ofReal (bound n)).toReal := by
  have hsum_measure : (∑' n, μ (bad n)) ≠ ∞ :=
    tsum_measure_ne_top_of_measureReal_le_of_tsum_ofReal_ne_top
      μ hbound_nonneg hle hsum_bound
  have hterm : ∀ n : ℕ, μ (bad n) ≤ ENNReal.ofReal (bound n) := by
    intro n
    exact
      (ENNReal.le_ofReal_iff_toReal_le
        (measure_ne_top μ (bad n)) (hbound_nonneg n)).2
        (by simpa [Measure.real] using hle n)
  calc
    μ.real (⋃ n, bad n) ≤ ∑' n, μ.real (bad n) :=
      measureReal_iUnion_le_tsum μ bad hsum_measure
    _ = (∑' n, μ (bad n)).toReal := by
      symm
      exact ENNReal.tsum_toReal_eq (fun n => measure_ne_top μ (bad n))
    _ ≤ (∑' n, ENNReal.ofReal (bound n)).toReal :=
      ENNReal.toReal_mono hsum_bound (ENNReal.tsum_le_tsum hterm)

/--
Lower-tail Hoeffding bound for independent `[0,1]` indicators with mean
`1/2`, in the form used by random half-sample arguments: the probability that
the observed count is at most one third of the set size is bounded by the
corresponding centered Hoeffding exponential.
-/
theorem measure_sum_half_mean_indicator_le_third_le_exp
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {X : ι → α → ℝ}
    (h_indep : iIndepFun X μ)
    {s : Finset ι}
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean_neg :
      ∀ i ∈ s, (∫ ω, (-X i ω) ∂μ) = -(1 / 2 : ℝ)) :
    μ.real
        {ω | (∑ i ∈ s, X i ω) ≤ (s.card : ℝ) / 3} ≤
      Real.exp
        (-((s.card : ℝ) / 6) ^ 2 /
          (2 * ((∑ _ ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  let Y : ι → α → ℝ := fun i ω => -X i ω
  have hY_indep : iIndepFun Y μ := by
    exact h_indep.comp (fun _ x => -x) (fun _ => measurable_id.neg)
  have hY_meas : ∀ i ∈ s, AEMeasurable (Y i) μ := by
    intro i hi
    exact (h_meas i hi).neg
  have hY_bound : ∀ i ∈ s, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-1 : ℝ) 0 := by
    intro i hi
    filter_upwards [h_bound i hi] with ω hω
    exact ⟨by linarith [hω.2], by linarith [hω.1]⟩
  have htail :=
    measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
      (μ := μ) (X := Y) hY_indep (s := s)
      (a := (-1 : ℝ)) (b := 0) (ε := (s.card : ℝ) / 6)
      hY_meas hY_bound (by positivity)
  refine le_trans ?_ htail
  refine measureReal_mono (μ := μ) ?_ (measure_ne_top μ _)
  intro ω hω
  have hsum_eq :
      (∑ i ∈ s, (Y i ω - ∫ x, Y i x ∂μ)) =
        (s.card : ℝ) / 2 - ∑ i ∈ s, X i ω := by
    calc
      (∑ i ∈ s, (Y i ω - ∫ x, Y i x ∂μ))
          = ∑ i ∈ s, (-X i ω + (1 / 2 : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hmean_neg i hi]
              simp [Y]
      _ = (s.card : ℝ) / 2 - ∑ i ∈ s, X i ω := by
              rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
              simp
              ring
  change (s.card : ℝ) / 3 ≥ ∑ i ∈ s, X i ω at hω
  change (s.card : ℝ) / 6 ≤
    ∑ i ∈ s, (Y i ω - ∫ x, Y i x ∂μ)
  rw [hsum_eq]
  nlinarith

/-- Fair-coin measure on `Bool`, with mass `1/2` on `true`. -/
noncomputable def fairBoolMeasure : Measure Bool :=
  ((PMF.bernoulli (1 / 2 : NNReal) (by norm_num)).toMeasure : Measure Bool)

/-- Product fair-coin measure on Boolean side assignments. -/
noncomputable def fairBoolProductMeasure (ι : Type*) : Measure (ι → Bool) :=
  Measure.infinitePi (fun _ : ι => fairBoolMeasure)

theorem fairBoolMeasure_isProbabilityMeasure : IsProbabilityMeasure fairBoolMeasure := by
  simpa [fairBoolMeasure] using
    (inferInstance : IsProbabilityMeasure (PMF.bernoulli (1 / 2 : NNReal) (by norm_num)).toMeasure)

theorem fairBoolProductMeasure_isProbabilityMeasure (ι : Type*) :
    IsProbabilityMeasure (fairBoolProductMeasure ι) := by
  let P : ι → Measure Bool := fun _ => fairBoolMeasure
  let hμ : ∀ i : ι, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using fairBoolMeasure_isProbabilityMeasure
  simpa [fairBoolProductMeasure, P] using
    @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (ι := ι) (X := fun _ : ι => Bool)
      (mX := fun _ => by infer_instance) (μ := P) hμ

theorem fairBoolProduct_indicator_iIndepFun
    {ι : Type*} (keep : Bool) :
    iIndepFun
      (fun i (side : ι → Bool) => if side i = keep then (1 : ℝ) else 0)
      (fairBoolProductMeasure ι) := by
  let P : ι → Measure Bool := fun _ => fairBoolMeasure
  let hμ : ∀ i : ι, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using fairBoolMeasure_isProbabilityMeasure
  have hcoord :
      iIndepFun (fun i (side : ι → Bool) => side i)
        (Measure.infinitePi P) := by
    exact
      @ProbabilityTheory.iIndepFun_infinitePi
        (ι := ι) (𝓧 := fun _ => Bool)
        (m𝓧 := fun _ => by infer_instance)
        (Ω := fun _ => Bool) (mΩ := fun _ => by infer_instance)
        (P := P) hμ (X := fun i : ι => (fun b : Bool => b))
        (mX := fun _ => measurable_id)
  simpa [fairBoolProductMeasure, P] using hcoord.comp
    (fun _ b => if b = keep then (1 : ℝ) else 0)
    (fun _ => measurable_of_finite _)

theorem fairBoolProduct_indicator_integral
    {ι : Type*} (i : ι) (keep : Bool) :
  (∫ side : ι → Bool,
        (if side i = keep then (1 : ℝ) else 0) ∂fairBoolProductMeasure ι) =
      1 / 2 := by
  let P : ι → Measure Bool := fun _ => fairBoolMeasure
  let hμ : ∀ i : ι, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using fairBoolMeasure_isProbabilityMeasure
  haveI : IsProbabilityMeasure (Measure.infinitePi P) :=
    @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (ι := ι) (X := fun _ : ι => Bool)
      (mX := fun _ => by infer_instance) (μ := P) hμ
  let f : Bool → ℝ := fun b => if b = keep then 1 else 0
  have hf :
      AEStronglyMeasurable f
        (Measure.map (fun side : ι → Bool => side i)
          (fairBoolProductMeasure ι)) :=
    (measurable_of_finite f).aestronglyMeasurable
  calc
    (∫ side : ι → Bool,
        (if side i = keep then (1 : ℝ) else 0) ∂fairBoolProductMeasure ι)
        = ∫ side : ι → Bool, f (side i) ∂fairBoolProductMeasure ι := by rfl
    _ = ∫ b : Bool, f b ∂Measure.map
          (fun side : ι → Bool => side i) (fairBoolProductMeasure ι) := by
        exact (integral_map
          (μ := fairBoolProductMeasure ι)
          (φ := fun side : ι → Bool => side i)
          (f := f) (measurable_pi_apply i).aemeasurable hf).symm
    _ = ∫ b : Bool, f b ∂Measure.map
          (fun side : ι → Bool => side i) (Measure.infinitePi P) := by
      simp [fairBoolProductMeasure, P]
    _ = ∫ b : Bool, f b ∂fairBoolMeasure := by
        rw [show
            (Measure.map (fun side : ι → Bool => side i) (Measure.infinitePi P))
              = fairBoolMeasure from by
              simpa [P] using
                (@MeasureTheory.Measure.infinitePi_map_eval
                  (ι := ι) (X := fun _ : ι => Bool)
                  (mX := fun _ => by infer_instance) (μ := P) hμ i)]
    _ = 1 / 2 := by
        cases keep <;>
          simp [f, fairBoolMeasure, PMF.integral_eq_sum, PMF.bernoulli]

theorem fairBoolProduct_indicator_lower_tail_le_exp
    {ι : Type*} (s : Finset ι) (keep : Bool) :
    (fairBoolProductMeasure ι).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
    Real.exp
        (-((s.card : ℝ) / 6) ^ 2 /
          (2 * ((∑ _ ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  let P : ι → Measure Bool := fun _ => fairBoolMeasure
  letI hμ : ∀ i : ι, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using fairBoolMeasure_isProbabilityMeasure
  letI : IsProbabilityMeasure (Measure.infinitePi P) :=
    @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (ι := ι) (X := fun _ : ι => Bool)
      (mX := fun _ => by infer_instance) (μ := P) hμ
  haveI : IsProbabilityMeasure (fairBoolProductMeasure ι) := by
    simpa [fairBoolProductMeasure, P] using
      @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
        (ι := ι) (X := fun _ : ι => Bool)
        (mX := fun _ => by infer_instance) (μ := P) hμ
  refine measure_sum_half_mean_indicator_le_third_le_exp
    (μ := fairBoolProductMeasure ι)
    (X := fun i side => if side i = keep then (1 : ℝ) else 0)
    (fairBoolProduct_indicator_iIndepFun keep)
    (s := s) ?_ ?_ ?_
  · intro i _hi
    exact ((measurable_of_finite
      (fun b : Bool => if b = keep then (1 : ℝ) else 0)).comp
        (measurable_pi_apply i)).aemeasurable
  · intro i _hi
    exact ae_of_all _ fun side => by
      by_cases h : side i = keep <;> simp [h]
  · intro i _hi
    rw [integral_neg]
    simp [fairBoolProduct_indicator_integral i keep]

theorem fairBoolProduct_indicator_lower_tail_le_exp_card
    {ι : Type*} (s : Finset ι) (keep : Bool) :
    (fairBoolProductMeasure ι).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
    Real.exp (-(s.card : ℝ) / 18) := by
  have hraw := fairBoolProduct_indicator_lower_tail_le_exp s keep
  have hsum :
      ((∑ _i ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ) =
        (s.card : ℝ) / 4 := by
    simp
    ring
  have hexp :
      -((s.card : ℝ) / 6) ^ 2 / (2 * ((s.card : ℝ) / 4)) =
        -(s.card : ℝ) / 18 := by
    by_cases hcard : s.card = 0
    · simp [hcard]
    · have hcard_ne : (s.card : ℝ) ≠ 0 := by
        exact_mod_cast hcard
      field_simp [hcard_ne]
      ring
  rw [hsum] at hraw
  simpa [hexp]
    using hraw

theorem fairBoolProduct_indicator_lower_tail_le_exp_card_relaxed
    {ι : Type*} (s : Finset ι) (keep : Bool) :
    (fairBoolProductMeasure ι).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
    Real.exp (-(s.card : ℝ) / 36) := by
  exact le_trans (fairBoolProduct_indicator_lower_tail_le_exp_card s keep)
    (Real.exp_le_exp.mpr (by
      have hnonneg : 0 ≤ (s.card : ℝ) := by exact_mod_cast Nat.zero_le s.card
      nlinarith))

@[simp] theorem measureProb_false
    {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    measureProb μ (fun _ => False) = 0 := by
  simp [measureProb]

theorem measure_le_of_imp
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p q : α → Prop)
    (h : ∀ a, p a → q a) :
    μ {a | p a} ≤ μ {a | q a} :=
  measure_mono (by intro a ha; exact h a ha)

/-- Direct monotonicity lemma for `measureProb` under predicate implication. -/
theorem measureProb_mono
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (himp : ∀ a, p a → q a) :
    measureProb μ p ≤ measureProb μ q :=
  measureProb_le_of_measure_le μ p q (measure_le_of_imp μ p q himp)

/--
For any real random variable under a probability measure, the probability of
falling below a threshold tends to zero when the threshold tends to `-∞`.
-/
theorem measureProb_le_threshold_tendsto_zero_of_threshold_tendsto_atBot
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (z : α → ℝ) (hz : Measurable z)
    (threshold : ℝ → ℝ)
    (hthreshold : Filter.Tendsto threshold Filter.atTop Filter.atBot) :
    Filter.Tendsto
      (fun θ : ℝ => measureProb μ (fun a => z a ≤ threshold θ))
      Filter.atTop (nhds 0) := by
  classical
  let ν : Measure ℝ := Measure.map z μ
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hz.aemeasurable
  have hcdf :
      Filter.Tendsto (fun x : ℝ => ProbabilityTheory.cdf ν x)
        Filter.atBot (nhds 0) :=
    ProbabilityTheory.tendsto_cdf_atBot ν
  have heq :
      (fun θ : ℝ => measureProb μ (fun a => z a ≤ threshold θ)) =
        fun θ : ℝ => ProbabilityTheory.cdf ν (threshold θ) := by
    funext θ
    rw [ProbabilityTheory.cdf_eq_real]
    change
      (μ {a | z a ≤ threshold θ}).toReal =
        ((Measure.map z μ) (Set.Iic (threshold θ))).toReal
    rw [Measure.map_apply hz measurableSet_Iic]
    rfl
  rw [heq]
  exact hcdf.comp hthreshold

/--
Special case of the lower-tail lemma for thresholds `-θ * gap` with
`gap > 0`.
-/
theorem measureProb_le_neg_mul_tendsto_atTop_zero
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (z : α → ℝ) (hz : Measurable z)
    {gap : ℝ} (hgap : 0 < gap) :
    Filter.Tendsto
      (fun θ : ℝ => measureProb μ (fun a => z a ≤ -θ * gap))
      Filter.atTop (nhds 0) := by
  have hthreshold :
      Filter.Tendsto (fun θ : ℝ => -θ * gap)
        Filter.atTop Filter.atBot := by
    simpa [neg_mul, mul_comm] using
      (Filter.tendsto_id.atTop_mul_const_of_neg (show -gap < 0 by linarith))
  exact measureProb_le_threshold_tendsto_zero_of_threshold_tendsto_atBot
    μ z hz (fun θ : ℝ => -θ * gap) hthreshold

/-- First-order union bound for two events, in real-valued `measureProb` form. -/
theorem measureProb_or_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop) :
    measureProb μ (fun a => p a ∨ q a) ≤
      measureProb μ p + measureProb μ q := by
  have hset :
      {a : α | p a ∨ q a} = {a : α | p a} ∪ {a : α | q a} := by
    ext a
    simp
  unfold measureProb
  rw [hset]
  calc
    (μ ({a : α | p a} ∪ {a : α | q a})).toReal
        ≤ (μ {a : α | p a} + μ {a : α | q a}).toReal := by
          exact ENNReal.toReal_mono
            (by
              exact ENNReal.add_ne_top.mpr
                ⟨measure_ne_top μ {a : α | p a},
                  measure_ne_top μ {a : α | q a}⟩)
            (measure_union_le {a : α | p a} {a : α | q a})
    _ = (μ {a : α | p a}).toReal + (μ {a : α | q a}).toReal := by
          rw [ENNReal.toReal_add
            (measure_ne_top μ {a : α | p a})
            (measure_ne_top μ {a : α | q a})]

/--
Midpoint union bound: if one real-valued score is below another, then relative
to any cutoff `m` either the first score is below `m` or the second score is
above `m`.
-/
theorem measureProb_lt_le_midpoint_tails
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (s1 s2 : α → ℝ) (m : ℝ) :
    measureProb μ (fun a => s1 a < s2 a) ≤
      measureProb μ (fun a => s1 a < m) +
        measureProb μ (fun a => m < s2 a) := by
  have hsubset :
      {a : α | s1 a < s2 a} ⊆
        {a : α | s1 a < m ∨ m < s2 a} := by
    intro a ha
    by_cases hleft : s1 a < m
    · exact Or.inl hleft
    · exact Or.inr (lt_of_le_of_lt (le_of_not_gt hleft) ha)
  calc
    measureProb μ (fun a => s1 a < s2 a)
        ≤ measureProb μ (fun a => s1 a < m ∨ m < s2 a) :=
          measureProb_le_of_measure_le μ
            (fun a => s1 a < s2 a)
            (fun a => s1 a < m ∨ m < s2 a)
            (measure_mono hsubset)
    _ ≤ measureProb μ (fun a => s1 a < m) +
          measureProb μ (fun a => m < s2 a) :=
          measureProb_or_le μ (fun a => s1 a < m) (fun a => m < s2 a)

theorem measure_lt_of_imp_of_diff_ne_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop)
    (hp : MeasurableSet {a | p a}) (hq : MeasurableSet {a | q a})
    (himp : ∀ a, p a → q a)
    (hpos : μ ({a | q a} ∩ {a | p a}ᶜ) ≠ 0) :
    μ {a | p a} < μ {a | q a} := by
  let P : Set α := {a | p a}
  let Q : Set α := {a | q a}
  have hdiff_meas : MeasurableSet (Q ∩ Pᶜ) := hq.inter hp.compl
  have hsplit : Q = P ∪ (Q ∩ Pᶜ) := by
    ext a
    constructor
    · intro hqa
      by_cases hpa : a ∈ P
      · exact Or.inl hpa
      · exact Or.inr ⟨hqa, hpa⟩
    · intro ha
      rcases ha with hpa | hdiff
      · exact himp a hpa
      · exact hdiff.1
  have hdisj : Disjoint P (Q ∩ Pᶜ) := by
    exact Set.disjoint_left.2 (by
      intro a hpa hdiff
      exact hdiff.2 hpa)
  have hdiff_pos : 0 < μ (Q ∩ Pᶜ) := by
    rwa [pos_iff_ne_zero]
  calc
    μ {a | p a} = μ P + 0 := by simp [P]
    _ < μ P + μ (Q ∩ Pᶜ) := by
      exact ENNReal.add_lt_add_left (measure_ne_top μ P) hdiff_pos
    _ = μ (P ∪ (Q ∩ Pᶜ)) := (measure_union hdisj hdiff_meas).symm
    _ = μ {a | q a} := by rw [← hsplit]

theorem measure_lt_of_cross_event_measure_lt
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop)
    (hp : MeasurableSet {a | p a}) (hq : MeasurableSet {a | q a})
    (hcross :
      μ ({a | p a} ∩ {a | q a}ᶜ) <
        μ ({a | q a} ∩ {a | p a}ᶜ)) :
    μ {a | p a} < μ {a | q a} := by
  let P : Set α := {a | p a}
  let Q : Set α := {a | q a}
  have hcommon : MeasurableSet (P ∩ Q) := hp.inter hq
  have hPnotQ : MeasurableSet (P ∩ Qᶜ) := hp.inter hq.compl
  have hQnotP : MeasurableSet (Q ∩ Pᶜ) := hq.inter hp.compl
  have hP_split : μ P = μ (P ∩ Q) + μ (P ∩ Qᶜ) := by
    have hunion : P = (P ∩ Q) ∪ (P ∩ Qᶜ) := by
      ext a
      by_cases hqa : a ∈ Q <;> simp [P, Q]
    conv_lhs => rw [hunion]
    exact measure_union (μ := μ) (s₁ := P ∩ Q) (s₂ := P ∩ Qᶜ)
      (Set.disjoint_left.2 (by
      intro a (ha : a ∈ P ∩ Q) (hb : a ∈ P ∩ Qᶜ)
      exact hb.2 ha.2)) hPnotQ
  have hQ_split : μ Q = μ (P ∩ Q) + μ (Q ∩ Pᶜ) := by
    have hunion : Q = (P ∩ Q) ∪ (Q ∩ Pᶜ) := by
      ext a
      by_cases hpa : a ∈ P <;> simp [P, Q, hpa, and_comm]
    conv_lhs => rw [hunion]
    exact measure_union (μ := μ) (s₁ := P ∩ Q) (s₂ := Q ∩ Pᶜ)
      (Set.disjoint_left.2 (by
      intro a (ha : a ∈ P ∩ Q) (hb : a ∈ Q ∩ Pᶜ)
      exact hb.2 ha.1)) hQnotP
  calc
    μ {a | p a} = μ (P ∩ Q) + μ (P ∩ Qᶜ) := hP_split
    _ < μ (P ∩ Q) + μ (Q ∩ Pᶜ) := by
      exact ENNReal.add_lt_add_left (measure_ne_top μ (P ∩ Q)) hcross
    _ = μ {a | q a} := hQ_split.symm

theorem measureProb_lt_of_cross_event_measure_lt
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop)
    (hp : MeasurableSet {a | p a}) (hq : MeasurableSet {a | q a})
    (hcross :
      μ ({a | p a} ∩ {a | q a}ᶜ) <
        μ ({a | q a} ∩ {a | p a}ᶜ)) :
    measureProb μ p < measureProb μ q :=
  measureProb_lt_of_measure_lt μ p q
    (measure_lt_of_cross_event_measure_lt μ p q hp hq hcross)

/-- Strict monotonicity for `measureProb` from a nonzero residual. -/
theorem measureProb_lt_of_imp_of_residual_ne_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hp : MeasurableSet {a | p a}) (hq : MeasurableSet {a | q a})
    (himp : ∀ a, p a → q a) (hres : μ ({a | q a} \ {a | p a}) ≠ 0) :
    measureProb μ p < measureProb μ q := by
  refine measureProb_lt_of_cross_event_measure_lt μ p q hp hq ?_
  have hleft : μ ({a | p a} ∩ {a | q a}ᶜ) = 0 := by
    apply measure_mono_null
      (s := ({a | p a} ∩ {a | q a}ᶜ : Set α))
      (t := (∅ : Set α))
    · intro a ha
      exact False.elim (ha.2 (himp a ha.1))
    · simp
  have hright : μ ({a | q a} ∩ {a | p a}ᶜ) ≠ 0 := by
    have hres' : ({a | q a} \ {a | p a}) = ({a | q a} ∩ {a | p a}ᶜ) := by
      ext a
      simp
    simpa [hres'] using hres
  rw [hleft]
  exact lt_of_le_of_ne (bot_le) hright.symm

/-- Real-valued mass of the lower-left rectangle `{(u,v) : u <= x, v <= y}`. -/
noncomputable def lowerLeftRectangleMass (μ : Measure (ℝ × ℝ)) (x y : ℝ) : ℝ :=
  μ.real {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 ≤ y}

/-- Real-valued mass of the first-coordinate lower half-space `{(u,v) : u <= x}`. -/
noncomputable def firstCoordinateLowerMass (μ : Measure (ℝ × ℝ)) (x : ℝ) : ℝ :=
  μ.real {p : ℝ × ℝ | p.1 ≤ x}

/-- Real-valued mass of the second-coordinate lower half-space `{(u,v) : v <= y}`. -/
noncomputable def secondCoordinateLowerMass (μ : Measure (ℝ × ℝ)) (y : ℝ) : ℝ :=
  μ.real {p : ℝ × ℝ | p.2 ≤ y}

/-- Real-valued mass of the vertical strip `{(u,v) : u <= x, y <= v}`. -/
noncomputable def verticalUpperStripMass (μ : Measure (ℝ × ℝ)) (x y : ℝ) : ℝ :=
  μ.real {p : ℝ × ℝ | p.1 ≤ x ∧ y ≤ p.2}

theorem measurableSet_lowerLeftRectangle (x y : ℝ) :
    MeasurableSet ({p : ℝ × ℝ | p.1 ≤ x ∧ p.2 ≤ y}) := by
  exact
    (isClosed_le continuous_fst continuous_const).measurableSet.inter
      (isClosed_le continuous_snd continuous_const).measurableSet

theorem measurableSet_firstCoordinateLower (x : ℝ) :
    MeasurableSet ({p : ℝ × ℝ | p.1 ≤ x}) :=
  (isClosed_le continuous_fst continuous_const).measurableSet

theorem measurableSet_secondCoordinateLower (y : ℝ) :
    MeasurableSet ({p : ℝ × ℝ | p.2 ≤ y}) :=
  (isClosed_le continuous_snd continuous_const).measurableSet

theorem measurableSet_verticalUpperStrip (x y : ℝ) :
    MeasurableSet ({p : ℝ × ℝ | p.1 ≤ x ∧ y ≤ p.2}) := by
  exact
    (isClosed_le continuous_fst continuous_const).measurableSet.inter
      (isClosed_le continuous_const continuous_snd).measurableSet

/-- A vertical upper strip has positive mass under a finite open-positive joint law. -/
theorem verticalUpperStripMass_pos_of_isOpenPosMeasure
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ] (x y : ℝ) :
    0 < verticalUpperStripMass μ x y := by
  let openStrip : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < x ∧ y < p.2}
  have hopen : IsOpen openStrip := by
    have hleft : IsOpen ({p : ℝ × ℝ | p.1 < x}) :=
      isOpen_lt continuous_fst continuous_const
    have hright : IsOpen ({p : ℝ × ℝ | y < p.2}) :=
      isOpen_lt continuous_const continuous_snd
    simpa [openStrip, Set.setOf_and] using hleft.inter hright
  have hnonempty : openStrip.Nonempty := by
    refine ⟨(x - 1, y + 1), ?_⟩
    simp [openStrip]
  have hsubset :
      openStrip ⊆ {p : ℝ × ℝ | p.1 ≤ x ∧ y ≤ p.2} := by
    intro p hp
    exact ⟨hp.1.le, hp.2.le⟩
  have hpos :
      0 < μ {p : ℝ × ℝ | p.1 ≤ x ∧ y ≤ p.2} :=
    lt_of_lt_of_le (hopen.measure_pos μ hnonempty) (measure_mono hsubset)
  exact ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top μ _)

/--
Moving a vertical-upper-strip cutoff left in the first coordinate and up in the
second coordinate strictly decreases its mass for any finite joint measure that
is positive on nonempty open sets.

This is the reusable measure-level fact behind displayed terms of the form
`P(X <= A(q), B(q) <= Y)`: if `A` is strictly decreasing and `B` is monotone
increasing, then the selected mass strictly falls.
-/
theorem verticalUpperStripMass_strictAnti_of_strictAnti_left_monotone_right
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {a b : ℝ → ℝ} (ha : StrictAnti a) (hb : Monotone b) :
    StrictAnti fun q : ℝ => verticalUpperStripMass μ (a q) (b q) := by
  intro q₁ q₂ hq
  have hmeasure_lt :
      μ {p : ℝ × ℝ | p.1 ≤ a q₂ ∧ b q₂ ≤ p.2} <
        μ {p : ℝ × ℝ | p.1 ≤ a q₁ ∧ b q₁ ≤ p.2} := by
    refine measure_lt_of_imp_of_diff_ne_zero μ
      (p := fun p : ℝ × ℝ => p.1 ≤ a q₂ ∧ b q₂ ≤ p.2)
      (q := fun p : ℝ × ℝ => p.1 ≤ a q₁ ∧ b q₁ ≤ p.2)
      (measurableSet_verticalUpperStrip (a q₂) (b q₂))
      (measurableSet_verticalUpperStrip (a q₁) (b q₁)) ?_ ?_
    · intro p hp
      exact ⟨hp.1.trans (ha hq).le, (hb hq.le).trans hp.2⟩
    · let U : Set (ℝ × ℝ) :=
        {p : ℝ × ℝ | a q₂ < p.1 ∧ p.1 < a q₁ ∧ b q₂ < p.2}
      have hU_open : IsOpen U := by
        have hopen_left : IsOpen {p : ℝ × ℝ | a q₂ < p.1} :=
          isOpen_lt (continuous_const : Continuous fun _ : ℝ × ℝ => a q₂)
            (continuous_fst : Continuous fun p : ℝ × ℝ => p.1)
        have hopen_mid : IsOpen {p : ℝ × ℝ | p.1 < a q₁} :=
          isOpen_lt (continuous_fst : Continuous fun p : ℝ × ℝ => p.1)
            (continuous_const : Continuous fun _ : ℝ × ℝ => a q₁)
        have hopen_right : IsOpen {p : ℝ × ℝ | b q₂ < p.2} :=
          isOpen_lt (continuous_const : Continuous fun _ : ℝ × ℝ => b q₂)
            (continuous_snd : Continuous fun p : ℝ × ℝ => p.2)
        simpa [U, Set.setOf_and, Set.inter_assoc] using
          (hopen_left.inter hopen_mid).inter hopen_right
      have hU_nonempty : U.Nonempty := by
        refine ⟨((a q₂ + a q₁) / 2, b q₂ + 1), ?_⟩
        have haq : a q₂ < a q₁ := ha hq
        dsimp [U]
        constructor
        · nlinarith
        · constructor
          · nlinarith
          · linarith
      have hU_ne_zero : μ U ≠ 0 :=
        hU_open.measure_ne_zero μ hU_nonempty
      intro hzero
      apply hU_ne_zero
      refine measure_mono_null ?_ hzero
      intro p hp
      rcases hp with ⟨hp_left, hp_between, hp_right⟩
      exact
        ⟨⟨hp_between.le, (hb hq.le).trans hp_right.le⟩,
          fun hnew => not_le_of_gt hp_left hnew.1⟩
  exact (ENNReal.toReal_lt_toReal
    (measure_ne_top μ {p : ℝ × ℝ | p.1 ≤ a q₂ ∧ b q₂ ≤ p.2})
    (measure_ne_top μ {p : ℝ × ℝ | p.1 ≤ a q₁ ∧ b q₁ ≤ p.2})).2
      hmeasure_lt

/--
If the upper threshold in a vertical strip tends to `+∞`, then the strip mass
tends to zero.
-/
theorem verticalUpperStripMass_tendsto_zero_of_right_tendsto_atTop
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] {a b : ℝ → ℝ}
    (hb : Filter.Tendsto b Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun q : ℝ => verticalUpperStripMass μ (a q) (b q))
      Filter.atTop (nhds 0) := by
  have hmeasure :
      Filter.Tendsto
        (fun q : ℝ => μ {p : ℝ × ℝ | p.1 ≤ a q ∧ b q ≤ p.2})
        Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    simpa using
      (MeasureTheory.tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
        (L := Filter.atTop) (μ := μ)
        (As := fun q : ℝ =>
          {p : ℝ × ℝ | p.1 ≤ a q ∧ b q ≤ p.2})
        (A := (∅ : Set (ℝ × ℝ)))
        (fun q => measurableSet_verticalUpperStrip (a q) (b q))
        (by
          intro p
          filter_upwards [hb.eventually (Filter.eventually_gt_atTop p.2)]
            with q hq
          constructor
          · intro hp
            exact False.elim ((not_le_of_gt hq) hp.2)
          · intro hp
            exact False.elim hp))
  change
    Filter.Tendsto
      (fun q : ℝ =>
        (μ {p : ℝ × ℝ | p.1 ≤ a q ∧ b q ≤ p.2}).toReal)
      Filter.atTop (nhds 0)
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeasure

/--
If the first-coordinate cutoff tends to `+∞` and the second-coordinate cutoff
tends to `-∞`, then the vertical strip mass tends to the whole mass.
-/
theorem verticalUpperStripMass_tendsto_atBot_univ_of_left_atTop_right_atBot
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] {a b : ℝ → ℝ}
    (ha : Filter.Tendsto a Filter.atBot Filter.atTop)
    (hb : Filter.Tendsto b Filter.atBot Filter.atBot) :
    Filter.Tendsto (fun q : ℝ => verticalUpperStripMass μ (a q) (b q))
      Filter.atBot (nhds (μ.real Set.univ)) := by
  have hmeasure :
      Filter.Tendsto
        (fun q : ℝ => μ {p : ℝ × ℝ | p.1 ≤ a q ∧ b q ≤ p.2})
        Filter.atBot (nhds (μ Set.univ)) := by
    simpa using
      (MeasureTheory.tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
        (L := Filter.atBot) (μ := μ)
        (As := fun q : ℝ =>
          {p : ℝ × ℝ | p.1 ≤ a q ∧ b q ≤ p.2})
        (A := (Set.univ : Set (ℝ × ℝ)))
        (fun q => measurableSet_verticalUpperStrip (a q) (b q))
        (by
          intro p
          filter_upwards
            [ha.eventually (Filter.eventually_gt_atTop p.1),
              hb.eventually (Filter.eventually_lt_atBot p.2)]
            with q hleft hright
          constructor
          · intro _hp
            trivial
          · intro _hp
            exact ⟨hleft.le, hright.le⟩))
  change
    Filter.Tendsto
      (fun q : ℝ =>
        (μ {p : ℝ × ℝ | p.1 ≤ a q ∧ b q ≤ p.2}).toReal)
      Filter.atBot (nhds (μ.real Set.univ))
  simpa [Measure.real] using
    (ENNReal.tendsto_toReal (measure_ne_top μ Set.univ)).comp hmeasure

/-- A lower-left rectangle has positive mass under a finite open-positive joint law. -/
theorem lowerLeftRectangleMass_pos_of_isOpenPosMeasure
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ] (x y : ℝ) :
    0 < lowerLeftRectangleMass μ x y := by
  let openRect : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < x ∧ p.2 < y}
  have hopen : IsOpen openRect := by
    have hleft : IsOpen ({p : ℝ × ℝ | p.1 < x}) :=
      isOpen_lt continuous_fst continuous_const
    have hright : IsOpen ({p : ℝ × ℝ | p.2 < y}) :=
      isOpen_lt continuous_snd continuous_const
    simpa [openRect, Set.setOf_and] using hleft.inter hright
  have hnonempty : openRect.Nonempty := by
    refine ⟨(x - 1, y - 1), ?_⟩
    simp [openRect]
  have hsubset :
      openRect ⊆ {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 ≤ y} := by
    intro p hp
    exact ⟨hp.1.le, hp.2.le⟩
  have hpos :
      0 < μ {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 ≤ y} :=
    lt_of_lt_of_le (hopen.measure_pos μ hnonempty) (measure_mono hsubset)
  exact ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top μ _)

/-- A second-coordinate lower half-space has positive mass under an open-positive finite joint law. -/
theorem secondCoordinateLowerMass_pos_of_isOpenPosMeasure
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ] (y : ℝ) :
    0 < secondCoordinateLowerMass μ y := by
  let openHalf : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 < y}
  have hopen : IsOpen openHalf := by
    simpa [openHalf] using isOpen_lt continuous_snd continuous_const
  have hnonempty : openHalf.Nonempty := by
    refine ⟨(0, y - 1), ?_⟩
    simp [openHalf]
  have hsubset : openHalf ⊆ {p : ℝ × ℝ | p.2 ≤ y} := by
    intro p hp
    exact (show p.2 < y from by simpa [openHalf] using hp).le
  have hpos : 0 < μ {p : ℝ × ℝ | p.2 ≤ y} :=
    lt_of_lt_of_le (hopen.measure_pos μ hnonempty) (measure_mono hsubset)
  exact ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top μ _)

/--
Moving the left threshold of a lower-left rectangle down strictly decreases
its mass for any finite joint measure that is positive on nonempty open sets.
-/
theorem lowerLeftRectangleMass_strictAnti_of_strictAnti_left_const_right
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {a : ℝ → ℝ} (y : ℝ) (ha : StrictAnti a) :
    StrictAnti fun q : ℝ => lowerLeftRectangleMass μ (a q) y := by
  intro q₁ q₂ hq
  have hmeasure_lt :
      μ {p : ℝ × ℝ | p.1 ≤ a q₂ ∧ p.2 ≤ y} <
        μ {p : ℝ × ℝ | p.1 ≤ a q₁ ∧ p.2 ≤ y} := by
    refine measure_lt_of_imp_of_diff_ne_zero μ
      (p := fun p : ℝ × ℝ => p.1 ≤ a q₂ ∧ p.2 ≤ y)
      (q := fun p : ℝ × ℝ => p.1 ≤ a q₁ ∧ p.2 ≤ y)
      (measurableSet_lowerLeftRectangle (a q₂) y)
      (measurableSet_lowerLeftRectangle (a q₁) y) ?_ ?_
    · intro p hp
      exact ⟨hp.1.trans (ha hq).le, hp.2⟩
    · let U : Set (ℝ × ℝ) :=
        {p : ℝ × ℝ | a q₂ < p.1 ∧ p.1 < a q₁ ∧ p.2 < y}
      have hU_open : IsOpen U := by
        have hopen_left : IsOpen {p : ℝ × ℝ | a q₂ < p.1} :=
          isOpen_lt (continuous_const : Continuous fun _ : ℝ × ℝ => a q₂)
            (continuous_fst : Continuous fun p : ℝ × ℝ => p.1)
        have hopen_mid : IsOpen {p : ℝ × ℝ | p.1 < a q₁} :=
          isOpen_lt (continuous_fst : Continuous fun p : ℝ × ℝ => p.1)
            (continuous_const : Continuous fun _ : ℝ × ℝ => a q₁)
        have hopen_right : IsOpen {p : ℝ × ℝ | p.2 < y} :=
          isOpen_lt (continuous_snd : Continuous fun p : ℝ × ℝ => p.2)
            (continuous_const : Continuous fun _ : ℝ × ℝ => y)
        simpa [U, Set.setOf_and, Set.inter_assoc] using
          (hopen_left.inter hopen_mid).inter hopen_right
      have hU_nonempty : U.Nonempty := by
        refine ⟨((a q₂ + a q₁) / 2, y - 1), ?_⟩
        have haq : a q₂ < a q₁ := ha hq
        dsimp [U]
        constructor
        · nlinarith
        · constructor
          · nlinarith
          · linarith
      have hU_ne_zero : μ U ≠ 0 :=
        hU_open.measure_ne_zero μ hU_nonempty
      intro hzero
      apply hU_ne_zero
      refine measure_mono_null ?_ hzero
      intro p hp
      rcases hp with ⟨hp_left, hp_between, hp_lower⟩
      exact
        ⟨⟨hp_between.le, hp_lower.le⟩,
          fun hnew => not_le_of_gt hp_left hnew.1⟩
  exact (ENNReal.toReal_lt_toReal
    (measure_ne_top μ {p : ℝ × ℝ | p.1 ≤ a q₂ ∧ p.2 ≤ y})
    (measure_ne_top μ {p : ℝ × ℝ | p.1 ≤ a q₁ ∧ p.2 ≤ y})).2
      hmeasure_lt

/--
If the left threshold of a lower-left rectangle tends to `-∞`, then the
rectangle mass tends to zero.
-/
theorem lowerLeftRectangleMass_tendsto_zero_of_left_tendsto_atBot
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] {a : ℝ → ℝ} (y : ℝ)
    (ha : Filter.Tendsto a Filter.atTop Filter.atBot) :
    Filter.Tendsto (fun q : ℝ => lowerLeftRectangleMass μ (a q) y)
      Filter.atTop (nhds 0) := by
  have hmeasure :
      Filter.Tendsto
        (fun q : ℝ => μ {p : ℝ × ℝ | p.1 ≤ a q ∧ p.2 ≤ y})
        Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    simpa using
      (MeasureTheory.tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
        (L := Filter.atTop) (μ := μ)
        (As := fun q : ℝ =>
          {p : ℝ × ℝ | p.1 ≤ a q ∧ p.2 ≤ y})
        (A := (∅ : Set (ℝ × ℝ)))
        (fun q => measurableSet_lowerLeftRectangle (a q) y)
        (by
          intro p
          filter_upwards [ha.eventually (Filter.eventually_lt_atBot p.1)]
            with q hq
          constructor
          · intro hp
            exact False.elim ((not_le_of_gt hq) hp.1)
          · intro hp
            exact False.elim hp))
  change
    Filter.Tendsto
      (fun q : ℝ =>
        (μ {p : ℝ × ℝ | p.1 ≤ a q ∧ p.2 ≤ y}).toReal)
      Filter.atTop (nhds 0)
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeasure

/--
If the left threshold of a lower-left rectangle tends to `+∞` while the right
threshold is fixed, then the rectangle mass tends to the second-coordinate
lower half-space mass.
-/
theorem lowerLeftRectangleMass_tendsto_secondCoordinateLower_of_left_tendsto_atTop
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] {a : ℝ → ℝ} (y : ℝ)
    (ha : Filter.Tendsto a Filter.atBot Filter.atTop) :
    Filter.Tendsto (fun q : ℝ => lowerLeftRectangleMass μ (a q) y)
      Filter.atBot (nhds (secondCoordinateLowerMass μ y)) := by
  have hmeasure :
      Filter.Tendsto
        (fun q : ℝ => μ {p : ℝ × ℝ | p.1 ≤ a q ∧ p.2 ≤ y})
        Filter.atBot (nhds (μ {p : ℝ × ℝ | p.2 ≤ y})) := by
    simpa using
      (MeasureTheory.tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
        (L := Filter.atBot) (μ := μ)
        (As := fun q : ℝ =>
          {p : ℝ × ℝ | p.1 ≤ a q ∧ p.2 ≤ y})
        (A := {p : ℝ × ℝ | p.2 ≤ y})
        (fun q => measurableSet_lowerLeftRectangle (a q) y)
        (by
          intro p
          filter_upwards [ha.eventually (Filter.eventually_gt_atTop p.1)]
            with q hq
          constructor
          · intro hp
            exact hp.2
          · intro hp
            exact ⟨hq.le, hp⟩))
  change
    Filter.Tendsto
      (fun q : ℝ =>
        (μ {p : ℝ × ℝ | p.1 ≤ a q ∧ p.2 ≤ y}).toReal)
      Filter.atBot (nhds ((μ {p : ℝ × ℝ | p.2 ≤ y}).toReal))
  exact
    (ENNReal.tendsto_toReal
      (measure_ne_top μ {p : ℝ × ℝ | p.2 ≤ y})).comp hmeasure

theorem measurableSet_horizontalBoundaryLeft (x y : ℝ) :
    MeasurableSet ({p : ℝ × ℝ | p.1 ≤ x ∧ p.2 = y}) := by
  exact
    (isClosed_le continuous_fst continuous_const).measurableSet.inter
      (isClosed_eq continuous_snd continuous_const).measurableSet

/--
A lower-left rectangle subtracts from the first-coordinate lower half-space to
give the vertical upper strip, up to a null horizontal boundary.

This is the reusable CDF bookkeeping behind identities of the form
`P(X <= x, y <= Y) = P(X <= x) - P(X <= x, Y <= y)` for continuous laws.
-/
theorem verticalUpperStripMass_eq_firstCoordinateLowerMass_sub_lowerLeftRectangleMass
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (x y : ℝ)
    (hboundary : μ.real {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 = y} = 0) :
    verticalUpperStripMass μ x y =
      firstCoordinateLowerMass μ x - lowerLeftRectangleMass μ x y := by
  let left : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ x}
  let lower : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 ≤ y}
  let strictUpper : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ x ∧ y < p.2}
  let upper : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ x ∧ y ≤ p.2}
  let boundary : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 = y}
  have hlower_subset : lower ⊆ left := by
    intro p hp
    exact hp.1
  have hdiff_eq : left \ lower = strictUpper := by
    ext p
    constructor
    · intro hp
      have hnot : ¬ p.2 ≤ y := by
        intro hle
        exact hp.2 ⟨hp.1, hle⟩
      exact ⟨hp.1, lt_of_not_ge hnot⟩
    · intro hp
      exact ⟨hp.1, by intro hlow; exact not_lt.mpr hlow.2 hp.2⟩
  have hupper_split : upper = strictUpper ∪ boundary := by
    ext p
    constructor
    · intro hp
      rcases lt_or_eq_of_le hp.2 with hlt | heq
      · exact Or.inl ⟨hp.1, hlt⟩
      · exact Or.inr ⟨hp.1, heq.symm⟩
    · intro hp
      rcases hp with hstrict | hbd
      · exact ⟨hstrict.1, hstrict.2.le⟩
      · exact ⟨hbd.1, hbd.2.ge⟩
  have hdisj : Disjoint strictUpper boundary := by
    refine Set.disjoint_left.2 ?_
    intro p hstrict hbd
    exact ne_of_gt hstrict.2 hbd.2
  have hboundary' : μ.real boundary = 0 := by
    simpa [boundary] using hboundary
  have hstrict_meas : MeasurableSet strictUpper := by
    have hleft : MeasurableSet ({p : ℝ × ℝ | p.1 ≤ x}) :=
      measurableSet_firstCoordinateLower x
    have hright : MeasurableSet ({p : ℝ × ℝ | y < p.2}) :=
      (isOpen_lt continuous_const continuous_snd).measurableSet
    simpa [strictUpper, Set.setOf_and] using hleft.inter hright
  have hboundary_meas : MeasurableSet boundary := by
    simpa [boundary] using measurableSet_horizontalBoundaryLeft x y
  have hupper_mass :
      μ.real upper = μ.real strictUpper := by
    rw [hupper_split, measureReal_union hdisj hboundary_meas, hboundary',
      add_zero]
  have hstrict_mass :
      μ.real strictUpper = μ.real left - μ.real lower := by
    rw [← hdiff_eq]
    exact measureReal_diff
      (μ := μ) (s₁ := left) (s₂ := lower) hlower_subset
      (by simpa [lower] using measurableSet_lowerLeftRectangle x y)
      (measure_ne_top μ left)
  calc
    verticalUpperStripMass μ x y = μ.real upper := rfl
    _ = μ.real strictUpper := hupper_mass
    _ = μ.real left - μ.real lower := hstrict_mass
    _ = firstCoordinateLowerMass μ x - lowerLeftRectangleMass μ x y := rfl

/--
Continuity of lower-left rectangle mass when the joint law puts zero mass on
every vertical or horizontal boundary.
-/
theorem lowerLeftRectangleMass_continuous_of_boundary_null
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hboundary :
      ∀ x y : ℝ,
        μ ({p : ℝ × ℝ | p.1 = x} ∪ {p : ℝ × ℝ | p.2 = y}) = 0) :
    Continuous fun q : ℝ × ℝ => lowerLeftRectangleMass μ q.1 q.2 := by
  refine continuous_iff_continuousAt.2 ?_
  intro q₀
  have hmeasure :
      Filter.Tendsto
        (fun q : ℝ × ℝ =>
          μ {p : ℝ × ℝ | p.1 ≤ q.1 ∧ p.2 ≤ q.2})
        (nhds q₀)
        (nhds (μ {p : ℝ × ℝ | p.1 ≤ q₀.1 ∧ p.2 ≤ q₀.2})) := by
    refine
      MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
        (L := nhds q₀) (μ := μ)
        (A := {p : ℝ × ℝ | p.1 ≤ q₀.1 ∧ p.2 ≤ q₀.2})
        (As := fun q : ℝ × ℝ =>
          {p : ℝ × ℝ | p.1 ≤ q.1 ∧ p.2 ≤ q.2})
        (measurableSet_lowerLeftRectangle q₀.1 q₀.2)
        (fun q => measurableSet_lowerLeftRectangle q.1 q.2) ?_
    have hboundary_ae :
        ∀ᵐ p ∂μ, p.1 ≠ q₀.1 ∧ p.2 ≠ q₀.2 := by
      refine (measure_eq_zero_iff_ae_notMem.1 (hboundary q₀.1 q₀.2)).mono ?_
      intro p hp
      constructor
      · intro h
        exact hp (Or.inl h)
      · intro h
        exact hp (Or.inr h)
    filter_upwards [hboundary_ae] with p hp
    have hfst_tend :
        Filter.Tendsto (fun q : ℝ × ℝ => q.1) (nhds q₀) (nhds q₀.1) :=
      continuous_fst.tendsto q₀
    have hsnd_tend :
        Filter.Tendsto (fun q : ℝ × ℝ => q.2) (nhds q₀) (nhds q₀.2) :=
      continuous_snd.tendsto q₀
    by_cases hfst_pos : p.1 < q₀.1
    · have hfst_event :
          ∀ᶠ q in nhds q₀, p.1 ≤ q.1 :=
        (hfst_tend.eventually (Ioi_mem_nhds hfst_pos)).mono
          (fun _ hlt => hlt.le)
      by_cases hsnd_pos : p.2 < q₀.2
      · have hsnd_event :
            ∀ᶠ q in nhds q₀, p.2 ≤ q.2 :=
          (hsnd_tend.eventually (Ioi_mem_nhds hsnd_pos)).mono
            (fun _ hlt => hlt.le)
        filter_upwards [hfst_event, hsnd_event] with q hqfst hqsnd
        simp [hqfst, hqsnd, hfst_pos.le, hsnd_pos.le]
      · have hsnd_neg : q₀.2 < p.2 :=
          lt_of_le_of_ne (le_of_not_gt hsnd_pos) hp.2.symm
        have hsnd_event :
            ∀ᶠ q in nhds q₀, ¬ p.2 ≤ q.2 :=
          (hsnd_tend.eventually (Iio_mem_nhds hsnd_neg)).mono
            (fun _ hlt => not_le_of_gt hlt)
        filter_upwards [hsnd_event] with q hqsnd
        simp [hqsnd, hsnd_neg.not_ge]
    · have hfst_neg : q₀.1 < p.1 :=
        lt_of_le_of_ne (le_of_not_gt hfst_pos) hp.1.symm
      have hfst_event :
          ∀ᶠ q in nhds q₀, ¬ p.1 ≤ q.1 :=
        (hfst_tend.eventually (Iio_mem_nhds hfst_neg)).mono
          (fun _ hlt => not_le_of_gt hlt)
      filter_upwards [hfst_event] with q hqfst
      simp [hqfst, hfst_neg.not_ge]
  change
    Filter.Tendsto
      (fun q : ℝ × ℝ =>
        (μ {p : ℝ × ℝ | p.1 ≤ q.1 ∧ p.2 ≤ q.2}).toReal)
      (nhds q₀)
      (nhds ((μ {p : ℝ × ℝ | p.1 ≤ q₀.1 ∧ p.2 ≤ q₀.2}).toReal))
  exact
    (ENNReal.tendsto_toReal
      (measure_ne_top μ {p : ℝ × ℝ | p.1 ≤ q₀.1 ∧ p.2 ≤ q₀.2})).comp
      hmeasure

/--
Continuity of lower-left rectangle mass from nonatomic first and second
marginals.
-/
theorem lowerLeftRectangleMass_continuous_of_noAtoms_marginals
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    [NoAtoms (μ.map Prod.fst)] [NoAtoms (μ.map Prod.snd)] :
    Continuous fun q : ℝ × ℝ => lowerLeftRectangleMass μ q.1 q.2 := by
  refine lowerLeftRectangleMass_continuous_of_boundary_null μ ?_
  intro x y
  have hleft : μ {p : ℝ × ℝ | p.1 = x} = 0 := by
    calc
      μ {p : ℝ × ℝ | p.1 = x}
          = μ (Prod.fst ⁻¹' ({x} : Set ℝ)) := by
              rfl
      _ = (μ.map Prod.fst) ({x} : Set ℝ) := by
              rw [Measure.map_apply measurable_fst (measurableSet_singleton x)]
      _ = 0 := by
              exact measure_singleton x
  have hright : μ {p : ℝ × ℝ | p.2 = y} = 0 := by
    calc
      μ {p : ℝ × ℝ | p.2 = y}
          = μ (Prod.snd ⁻¹' ({y} : Set ℝ)) := by
              rfl
      _ = (μ.map Prod.snd) ({y} : Set ℝ) := by
              rw [Measure.map_apply measurable_snd (measurableSet_singleton y)]
      _ = 0 := by
              exact measure_singleton y
  exact measure_union_null hleft hright

/-- Real-valued mass of the upper orthant `{(u,v) : x <= u, y <= v}`. -/
noncomputable def upperOrthantMass (μ : Measure (ℝ × ℝ)) (x y : ℝ) : ℝ :=
  μ.real {p : ℝ × ℝ | x ≤ p.1 ∧ y ≤ p.2}

theorem measurableSet_upperOrthant (x y : ℝ) :
    MeasurableSet ({p : ℝ × ℝ | x ≤ p.1 ∧ y ≤ p.2}) := by
  exact
    (isClosed_le continuous_const continuous_fst).measurableSet.inter
      (isClosed_le continuous_const continuous_snd).measurableSet

/--
Moving an upper-orthant threshold up in both coordinates strictly decreases
its mass for any finite joint measure that is positive on nonempty open sets.

This is the reusable measure-level fact behind strategic applicant pools:
if application and admission cutoffs both rise with the school cutoff, the
joint mass of students above both cutoffs falls strictly.
-/
theorem upperOrthantMass_strictAnti_of_strictMono_left_monotone_right
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {a b : ℝ → ℝ} (ha : StrictMono a) (hb : Monotone b) :
    StrictAnti fun q : ℝ => upperOrthantMass μ (a q) (b q) := by
  intro q₁ q₂ hq
  have hmeasure_lt :
      μ {p : ℝ × ℝ | a q₂ ≤ p.1 ∧ b q₂ ≤ p.2} <
        μ {p : ℝ × ℝ | a q₁ ≤ p.1 ∧ b q₁ ≤ p.2} := by
    refine measure_lt_of_imp_of_diff_ne_zero μ
      (p := fun p : ℝ × ℝ => a q₂ ≤ p.1 ∧ b q₂ ≤ p.2)
      (q := fun p : ℝ × ℝ => a q₁ ≤ p.1 ∧ b q₁ ≤ p.2)
      (measurableSet_upperOrthant (a q₂) (b q₂))
      (measurableSet_upperOrthant (a q₁) (b q₁)) ?_ ?_
    · intro p hp
      exact ⟨(ha hq).le.trans hp.1, (hb hq.le).trans hp.2⟩
    · let U : Set (ℝ × ℝ) :=
        {p : ℝ × ℝ | a q₁ < p.1 ∧ p.1 < a q₂ ∧ b q₂ < p.2}
      have hU_open : IsOpen U := by
        have hopen_left : IsOpen {p : ℝ × ℝ | a q₁ < p.1} :=
          isOpen_lt (continuous_const : Continuous fun _ : ℝ × ℝ => a q₁)
            (continuous_fst : Continuous fun p : ℝ × ℝ => p.1)
        have hopen_mid : IsOpen {p : ℝ × ℝ | p.1 < a q₂} :=
          isOpen_lt (continuous_fst : Continuous fun p : ℝ × ℝ => p.1)
            (continuous_const : Continuous fun _ : ℝ × ℝ => a q₂)
        have hopen_right : IsOpen {p : ℝ × ℝ | b q₂ < p.2} :=
          isOpen_lt (continuous_const : Continuous fun _ : ℝ × ℝ => b q₂)
            (continuous_snd : Continuous fun p : ℝ × ℝ => p.2)
        simpa [U, Set.setOf_and, Set.inter_assoc] using
          (hopen_left.inter hopen_mid).inter hopen_right
      have hU_nonempty : U.Nonempty := by
        refine ⟨((a q₁ + a q₂) / 2, b q₂ + 1), ?_⟩
        have haq : a q₁ < a q₂ := ha hq
        dsimp [U]
        constructor
        · nlinarith
        · constructor
          · nlinarith
          · linarith
      have hU_ne_zero : μ U ≠ 0 :=
        hU_open.measure_ne_zero μ hU_nonempty
      intro hzero
      apply hU_ne_zero
      refine measure_mono_null ?_ hzero
      intro p hp
      rcases hp with ⟨hp_left, hp_between, hp_right⟩
      exact
        ⟨⟨hp_left.le, (hb hq.le).trans hp_right.le⟩,
          fun hnew => not_le_of_gt hp_between hnew.1⟩
  exact (ENNReal.toReal_lt_toReal
    (measure_ne_top μ {p : ℝ × ℝ | a q₂ ≤ p.1 ∧ b q₂ ≤ p.2})
    (measure_ne_top μ {p : ℝ × ℝ | a q₁ ≤ p.1 ∧ b q₁ ≤ p.2})).2
      hmeasure_lt

/--
Along the diagonal path `(q - offset, q)`, upper-orthant mass tends to zero as
`q -> +∞`.
-/
theorem upperOrthantMass_diagonal_tendsto_atTop_zero
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (offset : ℝ) :
    Filter.Tendsto (fun q : ℝ => upperOrthantMass μ (q - offset) q)
      Filter.atTop (nhds 0) := by
  have hmeasure :
      Filter.Tendsto
        (fun q : ℝ =>
          μ {p : ℝ × ℝ | q - offset ≤ p.1 ∧ q ≤ p.2})
        Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    simpa using
      (MeasureTheory.tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
        (L := Filter.atTop) (μ := μ)
        (As := fun q : ℝ =>
          {p : ℝ × ℝ | q - offset ≤ p.1 ∧ q ≤ p.2})
        (A := (∅ : Set (ℝ × ℝ)))
        (fun q => measurableSet_upperOrthant (q - offset) q)
        (by
          intro p
          filter_upwards [Filter.eventually_gt_atTop p.2] with q hq
          constructor
          · intro hp
            exact False.elim ((not_le_of_gt hq) hp.2)
          · intro hp
            exact False.elim hp))
  change
    Filter.Tendsto
      (fun q : ℝ =>
        (μ {p : ℝ × ℝ | q - offset ≤ p.1 ∧ q ≤ p.2}).toReal)
      Filter.atTop (nhds 0)
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeasure

/--
Along the diagonal path `(q - offset, q)`, upper-orthant mass tends to the
whole mass as `q -> -∞`.
-/
theorem upperOrthantMass_diagonal_tendsto_atBot_univ
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (offset : ℝ) :
    Filter.Tendsto (fun q : ℝ => upperOrthantMass μ (q - offset) q)
      Filter.atBot (nhds (μ.real Set.univ)) := by
  have hmeasure :
      Filter.Tendsto
        (fun q : ℝ =>
          μ {p : ℝ × ℝ | q - offset ≤ p.1 ∧ q ≤ p.2})
        Filter.atBot (nhds (μ Set.univ)) := by
    simpa using
      (MeasureTheory.tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
        (L := Filter.atBot) (μ := μ)
        (As := fun q : ℝ =>
          {p : ℝ × ℝ | q - offset ≤ p.1 ∧ q ≤ p.2})
        (A := (Set.univ : Set (ℝ × ℝ)))
        (fun q => measurableSet_upperOrthant (q - offset) q)
        (by
          intro p
          filter_upwards [Filter.eventually_lt_atBot (min (p.1 + offset) p.2)] with q hq
          constructor
          · intro _hp
            trivial
          · intro _hp
            constructor
            · linarith [lt_of_lt_of_le hq (min_le_left (p.1 + offset) p.2)]
            · exact (lt_of_lt_of_le hq (min_le_right (p.1 + offset) p.2)).le))
  change
    Filter.Tendsto
      (fun q : ℝ =>
        (μ {p : ℝ × ℝ | q - offset ≤ p.1 ∧ q ≤ p.2}).toReal)
      Filter.atBot (nhds (μ.real Set.univ))
  simpa [Measure.real] using
    (ENNReal.tendsto_toReal (measure_ne_top μ Set.univ)).comp hmeasure

/--
Continuity of moving upper-orthant mass along `(q - offset, q)` when the joint
law puts zero mass on every corresponding vertical or horizontal boundary.
-/
theorem upperOrthantMass_diagonal_continuous_of_boundary_null
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (offset : ℝ)
    (hboundary :
      ∀ q : ℝ,
        μ ({p : ℝ × ℝ | p.1 = q - offset} ∪ {p : ℝ × ℝ | p.2 = q}) = 0) :
    Continuous fun q : ℝ => upperOrthantMass μ (q - offset) q := by
  refine continuous_iff_continuousAt.2 ?_
  intro q₀
  have hmeasure :
      Filter.Tendsto
        (fun q : ℝ =>
          μ {p : ℝ × ℝ | q - offset ≤ p.1 ∧ q ≤ p.2})
        (nhds q₀)
        (nhds (μ {p : ℝ × ℝ | q₀ - offset ≤ p.1 ∧ q₀ ≤ p.2})) := by
    refine
      MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
        (L := nhds q₀) (μ := μ)
        (A := {p : ℝ × ℝ | q₀ - offset ≤ p.1 ∧ q₀ ≤ p.2})
        (As := fun q : ℝ =>
          {p : ℝ × ℝ | q - offset ≤ p.1 ∧ q ≤ p.2})
        (measurableSet_upperOrthant (q₀ - offset) q₀)
        (fun q => measurableSet_upperOrthant (q - offset) q) ?_
    have hboundary_ae :
        ∀ᵐ p ∂μ, p.1 ≠ q₀ - offset ∧ p.2 ≠ q₀ := by
      refine (measure_eq_zero_iff_ae_notMem.1 (hboundary q₀)).mono ?_
      intro p hp
      constructor
      · intro h
        exact hp (Or.inl h)
      · intro h
        exact hp (Or.inr h)
    filter_upwards [hboundary_ae] with p hp
    have hsub_tend :
        Filter.Tendsto (fun q : ℝ => q - offset) (nhds q₀)
          (nhds (q₀ - offset)) :=
      (continuous_id.sub continuous_const).tendsto q₀
    by_cases hsub_pos : q₀ - offset < p.1
    · have hsub_event :
          ∀ᶠ q in nhds q₀, q - offset ≤ p.1 :=
        (hsub_tend.eventually (Iio_mem_nhds hsub_pos)).mono
          (fun _ hlt => hlt.le)
      by_cases hadmit_pos : q₀ < p.2
      · have hadmit_event :
            ∀ᶠ q in nhds q₀, q ≤ p.2 :=
          (tendsto_id.eventually (Iio_mem_nhds hadmit_pos)).mono
            (fun _ hlt => hlt.le)
        filter_upwards [hsub_event, hadmit_event] with q hqsub hqadmit
        simp [hqsub, hqadmit, hsub_pos.le, hadmit_pos.le]
      · have hadmit_neg : p.2 < q₀ :=
          lt_of_le_of_ne (le_of_not_gt hadmit_pos) hp.2
        have hadmit_event :
            ∀ᶠ q in nhds q₀, ¬ q ≤ p.2 :=
          (tendsto_id.eventually (Ioi_mem_nhds hadmit_neg)).mono
            (fun _ hgt => not_le_of_gt hgt)
        filter_upwards [hadmit_event] with q hqadmit
        simp [hqadmit, hadmit_neg.not_ge]
    · have hsub_neg : p.1 < q₀ - offset :=
        lt_of_le_of_ne (le_of_not_gt hsub_pos) hp.1
      have hsub_event :
          ∀ᶠ q in nhds q₀, ¬ q - offset ≤ p.1 :=
        (hsub_tend.eventually (Ioi_mem_nhds hsub_neg)).mono
          (fun _ hgt => not_le_of_gt hgt)
      filter_upwards [hsub_event] with q hqsub
      simp [hqsub, hsub_neg.not_ge]
  change
    Filter.Tendsto
      (fun q : ℝ =>
        (μ {p : ℝ × ℝ | q - offset ≤ p.1 ∧ q ≤ p.2}).toReal)
      (nhds q₀)
      (nhds ((μ {p : ℝ × ℝ | q₀ - offset ≤ p.1 ∧ q₀ ≤ p.2}).toReal))
  exact
    (ENNReal.tendsto_toReal
      (measure_ne_top μ {p : ℝ × ℝ | q₀ - offset ≤ p.1 ∧ q₀ ≤ p.2})).comp
      hmeasure

/--
Continuity of moving upper-orthant mass from nonatomic first and second
marginals.
-/
theorem upperOrthantMass_diagonal_continuous_of_noAtoms_marginals
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    [NoAtoms (μ.map Prod.fst)] [NoAtoms (μ.map Prod.snd)] (offset : ℝ) :
    Continuous fun q : ℝ => upperOrthantMass μ (q - offset) q := by
  refine upperOrthantMass_diagonal_continuous_of_boundary_null μ offset ?_
  intro q
  have hleft : μ {p : ℝ × ℝ | p.1 = q - offset} = 0 := by
    calc
      μ {p : ℝ × ℝ | p.1 = q - offset}
          = μ (Prod.fst ⁻¹' ({q - offset} : Set ℝ)) := by
              rfl
      _ = (μ.map Prod.fst) ({q - offset} : Set ℝ) := by
              rw [Measure.map_apply measurable_fst (measurableSet_singleton (q - offset))]
      _ = 0 := by
              exact measure_singleton (q - offset)
  have hright : μ {p : ℝ × ℝ | p.2 = q} = 0 := by
    calc
      μ {p : ℝ × ℝ | p.2 = q}
          = μ (Prod.snd ⁻¹' ({q} : Set ℝ)) := by
              rfl
      _ = (μ.map Prod.snd) ({q} : Set ℝ) := by
              rw [Measure.map_apply measurable_snd (measurableSet_singleton q)]
      _ = 0 := by
              exact measure_singleton q
  exact measure_union_null hleft hright

theorem volume_prod_vertical_line (x : ℝ) :
    (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.1 = x} = 0 := by
  have hset :
      ({p : ℝ × ℝ | p.1 = x} : Set (ℝ × ℝ)) =
        ({x} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext p
    simp
  rw [hset, Measure.volume_eq_prod ℝ ℝ,
    Measure.prod_prod ({x} : Set ℝ) (Set.univ : Set ℝ)]
  simp

theorem volume_prod_horizontal_line (y : ℝ) :
    (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.2 = y} = 0 := by
  have hset :
      ({p : ℝ × ℝ | p.2 = y} : Set (ℝ × ℝ)) =
        (Set.univ : Set ℝ) ×ˢ ({y} : Set ℝ) := by
    ext p
    simp
  rw [hset, Measure.volume_eq_prod ℝ ℝ,
    Measure.prod_prod (Set.univ : Set ℝ) ({y} : Set ℝ)]
  simp

theorem volume_withDensity_vertical_horizontal_boundary_null
    (D : ℝ × ℝ → ℝ≥0∞) (x y : ℝ) :
    ((volume : Measure (ℝ × ℝ)).withDensity D)
        ({p : ℝ × ℝ | p.1 = x} ∪ {p : ℝ × ℝ | p.2 = y}) = 0 := by
  have hac :
      ((volume : Measure (ℝ × ℝ)).withDensity D) ≪
        (volume : Measure (ℝ × ℝ)) :=
    withDensity_absolutelyContinuous (volume : Measure (ℝ × ℝ)) D
  have hleft :
      ((volume : Measure (ℝ × ℝ)).withDensity D)
          {p : ℝ × ℝ | p.1 = x} = 0 :=
    hac (volume_prod_vertical_line x)
  have hright :
      ((volume : Measure (ℝ × ℝ)).withDensity D)
          {p : ℝ × ℝ | p.2 = y} = 0 :=
    hac (volume_prod_horizontal_line y)
  exact measure_union_null hleft hright

theorem volume_withDensity_isOpenPosMeasure_of_ae_ne_zero
    (D : ℝ × ℝ → ℝ≥0∞)
    (hD : AEMeasurable D (volume : Measure (ℝ × ℝ)))
    (hD_ne_zero : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), D p ≠ 0) :
    Measure.IsOpenPosMeasure
      ((volume : Measure (ℝ × ℝ)).withDensity D) := by
  have h_ac :
      (volume : Measure (ℝ × ℝ)) ≪
        ((volume : Measure (ℝ × ℝ)).withDensity D) :=
    withDensity_absolutelyContinuous' hD hD_ne_zero
  exact h_ac.isOpenPosMeasure

theorem upperOrthantMass_diagonal_continuous_of_volume_withDensity
    (D : ℝ × ℝ → ℝ≥0∞)
    [IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).withDensity D)]
    (offset : ℝ) :
    Continuous fun q : ℝ =>
      upperOrthantMass ((volume : Measure (ℝ × ℝ)).withDensity D)
        (q - offset) q := by
  refine
    upperOrthantMass_diagonal_continuous_of_boundary_null
      ((volume : Measure (ℝ × ℝ)).withDensity D) offset ?_
  intro q
  exact volume_withDensity_vertical_horizontal_boundary_null D (q - offset) q

/--
If a probability measure is pushed forward to a countable measurable space and
then converted to a `PMF`, finite `pmfProb` agrees with the source-measure
preimage mass.
-/
theorem pmfProb_toPMF_map_eq_measureProb
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype β] [DecidableEq β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f)
    (p : β → Prop) [DecidablePred p]
    (hp : MeasurableSet {b | p b}) :
    pmfProb
        (@Measure.toPMF β _ _ _ (μ.map f)
          (Measure.isProbabilityMeasure_map hf.aemeasurable)) p =
      measureProb μ (fun a => p (f a)) := by
  classical
  haveI : IsProbabilityMeasure (μ.map f) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  unfold measureProb
  rw [pmfProb_eq_toOuterMeasure_toReal]
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply ((μ.map f).toPMF) hp]
  rw [Measure.toPMF_toMeasure]
  rw [Measure.map_apply hf hp]
  rfl

/--
Compare continuous probability deltas by reducing to the finite image of a
measurable summary map.

This is the measure-level analogue of
`pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le`: the pointwise
indicator comparison only needs to hold on the source space, not on every value
of the finite codomain.
-/
theorem measureProb_sub_le_measureProb_sub_of_forall_indicator_sub_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype β] [DecidableEq β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f)
    (p q r s : β → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r] [DecidablePred s]
    (hp : MeasurableSet {b | p b}) (hq : MeasurableSet {b | q b})
    (hr : MeasurableSet {b | r b}) (hs : MeasurableSet {b | s b})
    (h : ∀ a,
      (if p (f a) then (1 : ℝ) else 0) - (if q (f a) then (1 : ℝ) else 0) ≤
        (if r (f a) then (1 : ℝ) else 0) - (if s (f a) then (1 : ℝ) else 0)) :
    measureProb μ (fun a => p (f a)) - measureProb μ (fun a => q (f a)) ≤
      measureProb μ (fun a => r (f a)) - measureProb μ (fun a => s (f a)) := by
  classical
  let γ : Type _ := {b : β // b ∈ Set.range f}
  let g : α → γ := fun a => ⟨f a, ⟨a, rfl⟩⟩
  have hg : Measurable g := hf.subtype_mk
  have hpγ : MeasurableSet {b : γ | p b.1} :=
    hp.preimage measurable_subtype_coe
  have hqγ : MeasurableSet {b : γ | q b.1} :=
    hq.preimage measurable_subtype_coe
  have hrγ : MeasurableSet {b : γ | r b.1} :=
    hr.preimage measurable_subtype_coe
  have hsγ : MeasurableSet {b : γ | s b.1} :=
    hs.preimage measurable_subtype_coe
  let ν : PMF γ := @Measure.toPMF γ _ _ _ (μ.map g)
    (Measure.isProbabilityMeasure_map hg.aemeasurable)
  have hpmf :
      pmfProb ν (fun b : γ => p b.1) - pmfProb ν (fun b : γ => q b.1) ≤
        pmfProb ν (fun b : γ => r b.1) - pmfProb ν (fun b : γ => s b.1) := by
    refine pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le ν
      (fun b : γ => p b.1) (fun b : γ => q b.1)
      (fun b : γ => r b.1) (fun b : γ => s b.1) ?_
    intro b
    rcases b with ⟨b, hb⟩
    rcases hb with ⟨a, ha⟩
    subst b
    exact h a
  have hp_eq :
      pmfProb ν (fun b : γ => p b.1) = measureProb μ (fun a => p (f a)) := by
    simpa [ν, g] using pmfProb_toPMF_map_eq_measureProb μ g hg
      (fun b : γ => p b.1) hpγ
  have hq_eq :
      pmfProb ν (fun b : γ => q b.1) = measureProb μ (fun a => q (f a)) := by
    simpa [ν, g] using pmfProb_toPMF_map_eq_measureProb μ g hg
      (fun b : γ => q b.1) hqγ
  have hr_eq :
      pmfProb ν (fun b : γ => r b.1) = measureProb μ (fun a => r (f a)) := by
    simpa [ν, g] using pmfProb_toPMF_map_eq_measureProb μ g hg
      (fun b : γ => r b.1) hrγ
  have hs_eq :
      pmfProb ν (fun b : γ => s b.1) = measureProb μ (fun a => s (f a)) := by
    simpa [ν, g] using pmfProb_toPMF_map_eq_measureProb μ g hg
      (fun b : γ => s b.1) hsγ
  rw [hp_eq, hq_eq, hr_eq, hs_eq] at hpmf
  exact hpmf

/--
Change-of-variables mass comparison for a with-density measure.

If `e` preserves the base measure `μ`, maps source set `s` into target set `t`,
and the density at each source point is at most the density at its image, then
the `μ.withDensity D` mass of `s` is at most the mass of `t`.
-/
theorem withDensity_measure_le_of_measurableEquiv_image_subset_density_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (e : α ≃ᵐ α) (hmp : MeasurePreserving e μ μ)
    (D : α → ℝ≥0∞) {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hmap : ∀ a, a ∈ s → e a ∈ t)
    (hdens : ∀ a, a ∈ s → D a ≤ D (e a)) :
    μ.withDensity D s ≤ μ.withDensity D t := by
  rw [withDensity_apply D hs, withDensity_apply D ht]
  calc
    ∫⁻ a in s, D a ∂μ ≤ ∫⁻ a in s, D (e a) ∂μ := by
      exact setLIntegral_mono' hs hdens
    _ = ∫⁻ b in e '' s, D b ∂μ := by
      exact hmp.setLIntegral_comp_emb e.measurableEmbedding D s
    _ ≤ ∫⁻ b in t, D b ∂μ := by
      exact lintegral_mono_set (Set.image_subset_iff.mpr hmap)

/--
Strict change-of-variables mass comparison for a with-density measure.

This strengthens `withDensity_measure_le_of_measurableEquiv_image_subset_density_le`:
if the density inequality is strict on a positive-base-measure subset `u` of
`s`, and the source integral is finite, then the with-density mass comparison
is strict.
-/
theorem withDensity_measure_lt_of_measurableEquiv_image_subset_density_lt_on
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (e : α ≃ᵐ α) (hmp : MeasurePreserving e μ μ)
    (D : α → ℝ≥0∞) (hD : Measurable D)
    {s t u : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u)
    (hmap : ∀ a, a ∈ s → e a ∈ t)
    (hdens_le : ∀ a, a ∈ s → D a ≤ D (e a))
    (hfi : ∫⁻ a in s, D a ∂μ ≠ ∞)
    (hu_subset : u ⊆ s)
    (hu_pos : μ u ≠ 0)
    (hdens_lt : ∀ a, a ∈ u → D a < D (e a)) :
    μ.withDensity D s < μ.withDensity D t := by
  rw [withDensity_apply D hs, withDensity_apply D ht]
  have hstrict :
      ∫⁻ a in s, D a ∂μ < ∫⁻ a in s, D (e a) ∂μ := by
    refine lintegral_strict_mono_of_ae_le_of_ae_lt_on
      (μ := μ.restrict s) (s := u)
      ((hD.comp e.measurable).aemeasurable)
      hfi
      ((ae_restrict_iff' hs).2 (ae_of_all μ hdens_le))
      ?_ ?_
    · rw [Measure.restrict_apply hu]
      rwa [Set.inter_eq_left.mpr hu_subset]
    · exact ae_of_all _ (fun a ha => hdens_lt a ha)
  calc
    ∫⁻ a in s, D a ∂μ < ∫⁻ a in s, D (e a) ∂μ := hstrict
    _ = ∫⁻ b in e '' s, D b ∂μ := by
      exact hmp.setLIntegral_comp_emb e.measurableEmbedding D s
    _ ≤ ∫⁻ b in t, D b ∂μ := by
      exact lintegral_mono_set (Set.image_subset_iff.mpr hmap)


--  Bonferroni inequalities

/-- First-order union bound for finite families. -/
theorem measureProb_biUnion_finset_le
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (p : ι → α → Prop) :
    measureProb μ (fun a => ∃ i ∈ s, p i a) ≤
      ∑ i ∈ s, measureProb μ (fun a => p i a) := by
  let U : Set α := {a : α | ∃ i ∈ s, p i a}
  have hset : U = ⋃ i ∈ s, {a : α | p i a} := by
    ext a
    simp [U]
  change (μ U).toReal ≤ ∑ i ∈ s, measureProb μ (fun a => p i a)
  rw [hset]
  simpa [measureProb] using
    (measureReal_biUnion_finset_le (μ := μ) (s := s) (f := fun i => {a : α | p i a}))

/-- First-order complement lower bound for finite intersections. -/
theorem measureProb_inter_ge_one_sub_sum_compl
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (s : Finset ι) (p : ι → α → Prop)
    (hm : ∀ i ∈ s, MeasurableSet {a : α | p i a}) :
    1 - ∑ i ∈ s, measureProb μ (fun a => ¬ p i a) ≤
      measureProb μ (fun a => ∀ i ∈ s, p i a) := by
  classical
  let U : Set α := {a : α | ∀ i ∈ s, p i a}
  let C : Set α := ⋃ i ∈ s, {a : α | ¬ p i a}
  have hU : MeasurableSet U := by
    have hU' : U = ⋂ i ∈ s, {a : α | p i a} := by
      ext a
      simp [U]
    rw [hU']
    exact Finset.measurableSet_biInter (s := s)
      (f := fun i : ι => {a : α | p i a}) hm
  have hC : MeasurableSet C := by
    simpa [C] using Finset.measurableSet_biUnion (s := s)
      (f := fun i : ι => {a : α | ¬ p i a})
      (fun i hi => (hm i hi).compl)
  have hdeMorgan : Uᶜ = C := by
    ext a
    constructor
    · intro ha
      by_cases hC : a ∈ C
      · exact hC
      · exfalso
        apply ha
        simp [U]
        intro i hi
        by_contra hpi
        apply hC
        change a ∈ ⋃ i ∈ s, {a : α | ¬ p i a}
        exact Set.mem_iUnion.mpr
          ⟨i, Set.mem_iUnion.mpr ⟨hi, by simpa using hpi⟩⟩
    · intro hC
      change a ∈ ⋃ i ∈ s, {a : α | ¬ p i a} at hC
      rcases Set.mem_iUnion.mp hC with ⟨i, hCi⟩
      rcases Set.mem_iUnion.mp hCi with ⟨hi, hpi⟩
      intro hUA
      exact hpi (hUA i hi)
  have hcomp : μ.real C ≤ ∑ i ∈ s, measureProb μ (fun a => ¬ p i a) := by
    have hCset : C = ⋃ i ∈ s, {a : α | ¬ p i a} := by
      ext a
      simp [C]
    rw [hCset]
    simpa [measureProb, Measure.real] using
      (measureReal_biUnion_finset_le (μ := μ) (s := s)
        (f := fun i => {a : α | ¬ p i a}))
  have hprob : 1 - ∑ i ∈ s, measureProb μ (fun a => ¬ p i a) ≤ μ.real U := by
    have hCeq : μ.real C = 1 - μ.real U := by
      have hcompl := probReal_compl_eq_one_sub (μ := μ) hU
      simpa [hdeMorgan] using hcompl
    calc
      1 - ∑ i ∈ s, measureProb μ (fun a => ¬ p i a) ≤ 1 - μ.real C := by
        nlinarith [hcomp]
      _ = μ.real U := by linarith [hCeq]
  simpa [measureProb, U] using hprob

private theorem sum_filter_choose_eq
    {ι α : Type*} (s : Finset ι) (p : ι → α → Prop) (ω : α) (k : ℕ)
    [DecidablePred (fun i => p i ω)] :
    (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) =
      ((s.filter (fun i => p i ω)).card.choose k : ℝ) := by
  have hfilter :
      (s.powersetCard k).filter (fun t => ∀ i ∈ t, p i ω) =
        (s.filter (fun i => p i ω)).powersetCard k := by
    ext t
    constructor
    · intro ht
      rcases Finset.mem_filter.mp ht with ⟨ht, hpt⟩
      rcases Finset.mem_powersetCard.mp ht with ⟨hts, htk⟩
      exact Finset.mem_powersetCard.mpr
        ⟨fun i hi => Finset.mem_filter.mpr ⟨hts hi, hpt i hi⟩, htk⟩
    · intro ht
      rcases Finset.mem_powersetCard.mp ht with ⟨hts, htk⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_powersetCard.mpr
        ⟨fun i hi => (Finset.mem_filter.mp (hts hi)).1, htk⟩, ?_⟩
      intro i hi
      exact (Finset.mem_filter.mp (hts hi)).2
  calc
    (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
        = ∑ t ∈ (s.powersetCard k).filter (fun t => ∀ i ∈ t, p i ω), (1 : ℝ) := by
          simpa [Finset.sum_filter]
    _ = (((s.powersetCard k).filter (fun t => ∀ i ∈ t, p i ω)).card : ℝ) := by simp
    _ = (((s.filter (fun i => p i ω)).powersetCard k).card : ℝ) := by rw [hfilter]
    _ = ((s.filter (fun i => p i ω)).card.choose k : ℝ) := by
      simp [Finset.card_powersetCard]

private theorem sum_choose_zero_eq_one (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * ((0 : ℕ).choose k : ℝ)) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp [Finset.sum_range_succ, ih, Nat.choose_eq_zero_of_lt (Nat.succ_pos m)]

private theorem alternating_sum_choose_real_eq_odd
    {n m : ℕ} (hn : 0 < n) (hm : Odd m) :
    (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * (n.choose k : ℝ))
      = -((n - 1).choose m : ℝ) := by
  have hcast :
      (∑ k ∈ Finset.range (m + 1), ((-1 : ℤ)^k * (n.choose k : ℤ) : ℤ))
          = (-1 : ℤ)^m * (n - 1).choose m := by
    simpa [Nat.sub_add_cancel hn] using
      (Int.alternating_sum_range_choose_eq_choose (n := n - 1) (m := m))
  have hcast' :
      (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * (n.choose k : ℝ))
      = (∑ k ∈ Finset.range (m + 1), (((-1 : ℤ)^k * (n.choose k : ℤ) : ℤ) : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    norm_num [Int.cast_mul, Int.cast_pow]
  calc
    (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * (n.choose k : ℝ))
        = (∑ k ∈ Finset.range (m + 1),
            (((-1 : ℤ)^k * (n.choose k : ℤ) : ℤ) : ℝ)) := hcast'
    _ = ((-1 : ℝ)^m) * (n - 1).choose m := by
      exact_mod_cast hcast
    _ = -((n - 1).choose m : ℝ) := by simpa [hm.neg_one_pow]

private theorem alternating_sum_choose_real_eq_even
    {n m : ℕ} (hn : 0 < n) (hm : Even m) :
    (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * (n.choose k : ℝ))
      = ((n - 1).choose m : ℝ) := by
  have hcast :
      (∑ k ∈ Finset.range (m + 1), ((-1 : ℤ)^k * (n.choose k : ℤ) : ℤ))
          = (-1 : ℤ)^m * (n - 1).choose m := by
    simpa [Nat.sub_add_cancel hn] using
      (Int.alternating_sum_range_choose_eq_choose (n := n - 1) (m := m))
  have hcast' :
      (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * (n.choose k : ℝ))
      = (∑ k ∈ Finset.range (m + 1), (((-1 : ℤ)^k * (n.choose k : ℤ) : ℤ) : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    norm_num [Int.cast_mul, Int.cast_pow]
  calc
    (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * (n.choose k : ℝ))
        = (∑ k ∈ Finset.range (m + 1),
            (((-1 : ℤ)^k * (n.choose k : ℤ) : ℤ) : ℝ)) := hcast'
    _ = ((-1 : ℝ)^m) * (n - 1).choose m := by
      exact_mod_cast hcast
    _ = ((n - 1).choose m : ℝ) := by simpa [hm.neg_one_pow]

--  Bonferroni (finite odd-order truncation upper bound)
theorem measureProb_biUnion_finset_bonferroni_odd
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (s : Finset ι) (p : ι → α → Prop)
    (m : ℕ) (hm : ∀ i ∈ s, MeasurableSet {a : α | p i a}) (hodd : Odd m) :
    measureProb μ (fun a => ∃ i ∈ s, p i a) ≤
      1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
      ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
  classical
  let U : Set α := {a : α | ∃ i ∈ s, p i a}
  have hU : MeasurableSet U := by
    have hU' : U = ⋃ i ∈ s, {a : α | p i a} := by
      ext a
      simp [U]
    rw [hU']
    exact Finset.measurableSet_biUnion (s := s)
      (f := fun i : ι => {a : α | p i a}) hm
  let LHS : α → ℝ := U.indicator (fun _ : α => (1 : ℝ))
  let RHS : α → ℝ :=
    fun ω =>
      1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
        ∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
  have hpoint :
      ∀ ω, LHS ω ≤ RHS ω := by
    intro ω
    by_cases hUω : ω ∈ U
    · have hnzero : 0 < (s.filter (fun i => p i ω)).card := by
        rcases hUω with ⟨i, his, hp⟩
        exact Finset.card_pos.mpr ⟨i, by simp [his, hp]⟩
      have hsum :
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
            ) ) = -((s.filter (fun i => p i ω)).card - 1).choose m := by
        calc
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
              )
              = (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
                  ((s.filter (fun i => p i ω)).card.choose k : ℝ)) := by
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  rw [sum_filter_choose_eq (s := s) (p := p) (ω := ω) (k := k)]
          _ = -((s.filter (fun i => p i ω)).card - 1).choose m := by
                exact alternating_sum_choose_real_eq_odd
                  (hm := hodd) (n := (s.filter (fun i => p i ω)).card) hnzero
      have hchoose_nonneg : 0 ≤ (((s.filter (fun i => p i ω)).card - 1).choose m : ℝ) := by
        exact_mod_cast (Nat.zero_le (((s.filter (fun i => p i ω)).card - 1).choose m))
      have hrhs :
          RHS ω = 1 + (((s.filter (fun i => p i ω)).card - 1).choose m : ℝ) := by
        dsimp [RHS]
        nlinarith [hsum]
      have hLHS : LHS ω = (1 : ℝ) := by simp [LHS, hUω]
      rw [hLHS, hrhs]
      exact le_add_of_nonneg_right hchoose_nonneg
    · have hcard : (s.filter (fun i => p i ω)).card = 0 := by
        by_contra hcard
        rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hcard) with ⟨i, hi⟩
        exact hUω ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
      have hsum :
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
            ) ) = 1 := by
        calc
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
              )
              )
              = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
                  ((s.filter (fun i => p i ω)).card.choose k : ℝ) := by
                    refine Finset.sum_congr rfl ?_
                    intro k hk
                    rw [sum_filter_choose_eq (s := s) (p := p) (ω := ω) (k := k)]
              _ = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
                    ((0 : ℕ).choose k : ℝ) := by simp [hcard]
              _ = 1 := sum_choose_zero_eq_one m
      have hrhs : RHS ω = 0 := by
        dsimp [RHS]
        nlinarith [hsum]
      have hLHS : LHS ω = 0 := by simp [LHS, hUω]
      simpa [hLHS, hrhs]
  have hLInt : Integrable LHS μ := by
    refine (MeasureTheory.integrable_indicator_iff hU).2 ?_
    exact MeasureTheory.integrableOn_const (μ := μ) (s := U)
      (hs := measure_ne_top_of_subset (by simp) (measure_ne_top μ Set.univ))
  have hindicator_eq :
      ∀ (t : Finset ι), ∀ (ω : α),
        (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) =
          (⋂ i ∈ t, {a : α | p i a}).indicator (fun _ : α => (1 : ℝ)) ω := by
    intro t ω
    by_cases hforall : ∀ i ∈ t, p i ω
    · have hmem : ω ∈ ⋂ i ∈ t, {a : α | p i a} := by
        simpa [Set.mem_iInter] using hforall
      rw [if_pos hforall]
      simp [hmem]
    · have hnotmem : ω ∉ ⋂ i ∈ t, {a : α | p i a} := by
        intro hmem
        exact hforall (by simpa [Set.mem_iInter] using hmem)
      rw [if_neg hforall]
      simp [hnotmem]
  have hInnerInt :
      ∀ k, ∀ t ∈ s.powersetCard k,
      Integrable (fun ω => (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) μ := by
    intro k t ht
    let A : Set α := ⋂ i ∈ t, {a : α | p i a}
    have hA : MeasurableSet A := by
      refine t.measurableSet_biInter ?_
      intro i hi
      exact hm i ((Finset.mem_powersetCard.mp ht).1 hi)
    have hAint : Integrable (A.indicator (fun _ : α => (1 : ℝ))) μ := by
      refine (MeasureTheory.integrable_indicator_iff hA).2 ?_
      exact MeasureTheory.integrableOn_const (μ := μ) (s := A)
        (hs := measure_ne_top_of_subset (by simp) (measure_ne_top μ Set.univ))
    have hEq :
        (fun ω => (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
          = (fun ω => A.indicator (fun _ : α => (1 : ℝ)) ω) := by
      funext ω
      simpa [A] using hindicator_eq t ω
    exact hEq ▸ hAint
  have hInnerSumInt :
      ∀ k, Integrable (fun ω =>
        ∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) μ := by
    intro k
    refine MeasureTheory.integrable_finset_sum (s := s.powersetCard k) ?_
    intro t ht
    exact hInnerInt k t ht
  have hInnerMeasure :
      ∀ k,
      (∫ ω, (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ) =
        ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
    intro k
    calc
      (∫ ω, (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ)
          = ∑ t ∈ s.powersetCard k, ∫ ω, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) ∂μ := by
            refine MeasureTheory.integral_finset_sum (s := s.powersetCard k) ?_
            intro t ht
            exact hInnerInt k t ht
      _ = ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            let A : Set α := ⋂ i ∈ t, {a : α | p i a}
            have hA : MeasurableSet A := by
              refine t.measurableSet_biInter ?_
              intro i hi
              exact hm i ((Finset.mem_powersetCard.mp ht).1 hi)
            have hAeq : A = {a : α | ∀ i ∈ t, p i a} := by
              ext a
              simp [A, Set.mem_iInter]
            have hEq :
                (fun ω => (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
                  = (fun ω => A.indicator (fun _ : α => (1 : ℝ)) ω) := by
              funext ω
              simpa [A] using hindicator_eq t ω
            calc
              ∫ ω, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) ∂μ
                  = ∫ ω, A.indicator (fun _ : α => (1 : ℝ)) ω ∂μ := by
                    exact congrArg (fun g => ∫ ω, g ω ∂μ) hEq
              _ = ∫ ω in A, (1 : ℝ) ∂μ := by
                    rw [MeasureTheory.integral_indicator hA]
              _ = μ.real A := by
                    simpa using (MeasureTheory.setIntegral_one_eq_measureReal (μ := μ) (s := A))
              _ = measureProb μ (fun a => ∀ i ∈ t, p i a) := by
                    have hAeq' : μ.real A = μ.real {a : α | ∀ i ∈ t, p i a} := by
                      simpa [hAeq]
                    simpa [measureProb, Measure.real] using hAeq'
  have hOuterInt :
      Integrable (fun ω =>
        ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
          (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ) μ := by
    refine MeasureTheory.integrable_finset_sum (s := Finset.range (m + 1)) ?_
    intro k hk
    exact (hInnerSumInt k).const_mul ((-1 : ℝ)^k)
  have hRHSInt : Integrable RHS μ := by
    have hconstInt : Integrable (fun _ : α => (1 : ℝ)) μ := by
      simpa using (MeasureTheory.integrable_const (μ := μ) (c := (1 : ℝ)))
    exact (hconstInt.sub hOuterInt)
  have hOuterSum :
      (∫ ω, ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
        (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ)
          = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
    calc
      ∫ ω, ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
          (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ
          = ∑ k ∈ Finset.range (m + 1), ∫ ω, ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k,
                (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ := by
                exact MeasureTheory.integral_finset_sum (s := Finset.range (m + 1))
                  (f := fun k ω => ((-1 : ℝ)^k) *
                    (∑ t ∈ s.powersetCard k,
                      (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
                  ) (fun k hk => (hInnerSumInt k).const_mul ((-1 : ℝ)^k))
      _ = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
        ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          calc
            ∫ ω, ((-1 : ℝ)^k) *
                (∑ t ∈ s.powersetCard k,
                  (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ
                = ((-1 : ℝ)^k) * ∫ ω, (∑ t ∈ s.powersetCard k,
                    (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ := by
                      simpa using (MeasureTheory.integral_const_mul ((-1 : ℝ)^k)
                        (fun ω => ∑ t ∈ s.powersetCard k,
                          (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) )
              _ = ((-1 : ℝ)^k) * (∑ t ∈ s.powersetCard k,
                    measureProb μ (fun a => ∀ i ∈ t, p i a)) := by
                    rw [hInnerMeasure k]
  have hRHSIntEq :
      ∫ ω, RHS ω ∂μ =
        1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
          ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
    have hconstInt : Integrable (fun _ : α => (1 : ℝ)) μ := by
      simpa using (MeasureTheory.integrable_const (μ := μ) (c := (1 : ℝ)))
    calc
      (∫ ω, RHS ω ∂μ)
          = (∫ ω, (1 : ℝ) ∂μ) - ∫ ω, (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) ) ) ∂μ := by
                simpa [RHS] using (MeasureTheory.integral_sub hconstInt hOuterInt)
      _ = 1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
              rw [hOuterSum]
              simp [MeasureTheory.integral_const]
  have hLHSInt :
      (∫ ω, LHS ω ∂μ) = measureProb μ (fun a => ∃ i ∈ s, p i a) := by
    calc
      (∫ ω, LHS ω ∂μ) = ∫ ω, U.indicator (fun _ : α => (1 : ℝ)) ω ∂μ := by
        simp [LHS]
      _ = ∫ ω in U, (1 : ℝ) ∂μ := by
        simpa using (MeasureTheory.integral_indicator (s := U) (f := fun _ : α => (1 : ℝ)) hU)
      _ = μ.real U := by
        simpa using (MeasureTheory.setIntegral_one_eq_measureReal (μ := μ) (s := U))
      _ = measureProb μ (fun a => ∃ i ∈ s, p i a) := by
        simp [measureProb, Measure.real, U]
  have hInt := MeasureTheory.integral_mono hLInt hRHSInt hpoint
  simpa [hLHSInt, hRHSIntEq] using hInt

--  Bonferroni (finite even-order truncation lower bound)
theorem measureProb_biUnion_finset_bonferroni_even
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (s : Finset ι) (p : ι → α → Prop)
    (m : ℕ) (hm : ∀ i ∈ s, MeasurableSet {a : α | p i a}) (hme : Even m) :
    1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
      ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) ≤
      measureProb μ (fun a => ∃ i ∈ s, p i a) := by
  classical
  let U : Set α := {a : α | ∃ i ∈ s, p i a}
  have hU : MeasurableSet U := by
    have hU' : U = ⋃ i ∈ s, {a : α | p i a} := by
      ext a
      simp [U]
    rw [hU']
    exact Finset.measurableSet_biUnion (s := s) (f := fun i : ι => {a : α | p i a}) hm
  let LHS : α → ℝ := U.indicator (fun _ : α => (1 : ℝ))
  let RHS : α → ℝ :=
    fun ω =>
      1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
        ∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
  have hpoint :
      ∀ ω, RHS ω ≤ LHS ω := by
    intro ω
    by_cases hUω : ω ∈ U
    · have hnzero : 0 < (s.filter (fun i => p i ω)).card := by
        rcases hUω with ⟨i, his, hp⟩
        exact Finset.card_pos.mpr ⟨i, by simp [his, hp]⟩
      have hsum :
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
            ) ) = ((s.filter (fun i => p i ω)).card - 1).choose m := by
        calc
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
              )
              )
              = (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
                  ((s.filter (fun i => p i ω)).card.choose k : ℝ)) := by
                    refine Finset.sum_congr rfl ?_
                    intro k hk
                    rw [sum_filter_choose_eq (s := s) (p := p) (ω := ω) (k := k)]
          _ = ((s.filter (fun i => p i ω)).card - 1).choose m := by
                exact alternating_sum_choose_real_eq_even
                  (hm := hme) (n := (s.filter (fun i => p i ω)).card) hnzero
      have hchoose_nonneg : 0 ≤ (((s.filter (fun i => p i ω)).card - 1).choose m : ℝ) := by
        exact_mod_cast (Nat.zero_le (((s.filter (fun i => p i ω)).card - 1).choose m))
      have hrhs :
          RHS ω = 1 - (((s.filter (fun i => p i ω)).card - 1).choose m : ℝ) := by
        dsimp [RHS]
        nlinarith [hsum]
      have hLHS : LHS ω = (1 : ℝ) := by simp [LHS, hUω]
      rw [hrhs, hLHS]
      nlinarith
    · have hcard : (s.filter (fun i => p i ω)).card = 0 := by
        by_contra hcard
        rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hcard) with ⟨i, hi⟩
        exact hUω ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
      have hsum :
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
            ) ) = 1 := by
        calc
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
              )
              )
              = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
                  ((s.filter (fun i => p i ω)).card.choose k : ℝ) := by
                    refine Finset.sum_congr rfl ?_
                    intro k hk
                    rw [sum_filter_choose_eq (s := s) (p := p) (ω := ω) (k := k)]
              _ = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
                    ((0 : ℕ).choose k : ℝ) := by simp [hcard]
              _ = 1 := sum_choose_zero_eq_one m
      have hrhs : RHS ω = 0 := by
        dsimp [RHS]
        nlinarith [hsum]
      have hLHS : LHS ω = 0 := by simp [LHS, hUω]
      simpa [hLHS, hrhs]
  have hLInt : Integrable LHS μ := by
    refine (MeasureTheory.integrable_indicator_iff hU).2 ?_
    exact MeasureTheory.integrableOn_const (μ := μ) (s := U)
      (hs := measure_ne_top_of_subset (by simp) (measure_ne_top μ Set.univ))
  have hindicator_eq :
      ∀ (t : Finset ι), ∀ (ω : α),
        (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) =
          (⋂ i ∈ t, {a : α | p i a}).indicator (fun _ : α => (1 : ℝ)) ω := by
    intro t ω
    by_cases hforall : ∀ i ∈ t, p i ω
    · have hmem : ω ∈ ⋂ i ∈ t, {a : α | p i a} := by
        simpa [Set.mem_iInter] using hforall
      rw [if_pos hforall]
      simp [hmem]
    · have hnotmem : ω ∉ ⋂ i ∈ t, {a : α | p i a} := by
        intro hmem
        exact hforall (by simpa [Set.mem_iInter] using hmem)
      rw [if_neg hforall]
      simp [hnotmem]
  have hInnerInt :
      ∀ k, ∀ t ∈ s.powersetCard k,
      Integrable (fun ω => (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) μ := by
    intro k t ht
    let A : Set α := ⋂ i ∈ t, {a : α | p i a}
    have hA : MeasurableSet A := by
      refine t.measurableSet_biInter ?_
      intro i hi
      exact hm i ((Finset.mem_powersetCard.mp ht).1 hi)
    have hAint : Integrable (A.indicator (fun _ : α => (1 : ℝ))) μ := by
      refine (MeasureTheory.integrable_indicator_iff hA).2 ?_
      exact MeasureTheory.integrableOn_const (μ := μ) (s := A)
        (hs := measure_ne_top_of_subset (by simp) (measure_ne_top μ Set.univ))
    have hEq :
        (fun ω => (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
          = (fun ω => A.indicator (fun _ : α => (1 : ℝ)) ω) := by
      funext ω
      simpa [A] using hindicator_eq t ω
    exact hEq ▸ hAint
  have hInnerSumInt :
      ∀ k, Integrable (fun ω =>
        ∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) μ := by
    intro k
    refine MeasureTheory.integrable_finset_sum (s := s.powersetCard k) ?_
    intro t ht
    exact hInnerInt k t ht
  have hInnerMeasure :
      ∀ k,
      (∫ ω, (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ) =
        ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
    intro k
    calc
      (∫ ω, (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ)
          = ∑ t ∈ s.powersetCard k, ∫ ω, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) ∂μ := by
            refine MeasureTheory.integral_finset_sum (s := s.powersetCard k) ?_
            intro t ht
            exact hInnerInt k t ht
      _ = ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            let A : Set α := ⋂ i ∈ t, {a : α | p i a}
            have hA : MeasurableSet A := by
              refine t.measurableSet_biInter ?_
              intro i hi
              exact hm i ((Finset.mem_powersetCard.mp ht).1 hi)
            have hAeq : A = {a : α | ∀ i ∈ t, p i a} := by
              ext a
              simp [A, Set.mem_iInter]
            have hEq :
                (fun ω => (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
                  = (fun ω => A.indicator (fun _ : α => (1 : ℝ)) ω) := by
              funext ω
              simpa [A] using hindicator_eq t ω
            calc
              ∫ ω, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) ∂μ
                  = ∫ ω, A.indicator (fun _ : α => (1 : ℝ)) ω ∂μ := by
                    exact congrArg (fun g => ∫ ω, g ω ∂μ) hEq
              _ = ∫ ω in A, (1 : ℝ) ∂μ := by
                    rw [MeasureTheory.integral_indicator hA]
              _ = μ.real A := by
                    simpa using (MeasureTheory.setIntegral_one_eq_measureReal (μ := μ) (s := A))
              _ = measureProb μ (fun a => ∀ i ∈ t, p i a) := by
                    have hAeq' : μ.real A = μ.real {a : α | ∀ i ∈ t, p i a} := by
                      simpa [hAeq]
                    simpa [measureProb, Measure.real] using hAeq'
  have hOuterInt :
      Integrable (fun ω =>
        ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
          (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ) μ := by
    refine MeasureTheory.integrable_finset_sum (s := Finset.range (m + 1)) ?_
    intro k hk
    exact (hInnerSumInt k).const_mul ((-1 : ℝ)^k)
  have hRHSInt : Integrable RHS μ := by
    have hconstInt : Integrable (fun _ : α => (1 : ℝ)) μ := by
      simpa using (MeasureTheory.integrable_const (μ := μ) (c := (1 : ℝ)))
    exact (hconstInt.sub hOuterInt)
  have hOuterSum :
      (∫ ω, ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
        (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ)
          = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
    calc
      ∫ ω, ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
          (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ
          = ∑ k ∈ Finset.range (m + 1), ∫ ω, ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k,
                (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ := by
                exact MeasureTheory.integral_finset_sum (s := Finset.range (m + 1))
                  (f := fun k ω => ((-1 : ℝ)^k) *
                    (∑ t ∈ s.powersetCard k,
                      (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
                  ) (fun k hk => (hInnerSumInt k).const_mul ((-1 : ℝ)^k))
      _ = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
        ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          calc
            ∫ ω, ((-1 : ℝ)^k) *
                (∑ t ∈ s.powersetCard k,
                  (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ
                = ((-1 : ℝ)^k) * ∫ ω, (∑ t ∈ s.powersetCard k,
                    (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ := by
                      simpa using (MeasureTheory.integral_const_mul ((-1 : ℝ)^k)
                        (fun ω => ∑ t ∈ s.powersetCard k,
                          (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) )
              _ = ((-1 : ℝ)^k) * (∑ t ∈ s.powersetCard k,
                    measureProb μ (fun a => ∀ i ∈ t, p i a)) := by
                    rw [hInnerMeasure k]
  have hRHSIntEq :
      ∫ ω, RHS ω ∂μ =
        1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
          ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
    have hconstInt : Integrable (fun _ : α => (1 : ℝ)) μ := by
      simpa using (MeasureTheory.integrable_const (μ := μ) (c := (1 : ℝ)))
    calc
      (∫ ω, RHS ω ∂μ)
          = (∫ ω, (1 : ℝ) ∂μ) - ∫ ω, (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) ) ) ∂μ := by
                simpa [RHS] using (MeasureTheory.integral_sub hconstInt hOuterInt)
      _ = 1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
              rw [hOuterSum]
              simp [MeasureTheory.integral_const]
  have hLHSInt :
      (∫ ω, LHS ω ∂μ) = measureProb μ (fun a => ∃ i ∈ s, p i a) := by
    calc
      (∫ ω, LHS ω ∂μ) = ∫ ω, U.indicator (fun _ : α => (1 : ℝ)) ω ∂μ := by
        simp [LHS]
      _ = ∫ ω in U, (1 : ℝ) ∂μ := by
        simpa using (MeasureTheory.integral_indicator (s := U) (f := fun _ : α => (1 : ℝ)) hU)
      _ = μ.real U := by
        simpa using (MeasureTheory.setIntegral_one_eq_measureReal (μ := μ) (s := U))
      _ = measureProb μ (fun a => ∃ i ∈ s, p i a) := by
        simp [measureProb, Measure.real, U]
  have hInt := MeasureTheory.integral_mono hRHSInt hLInt hpoint
  simpa [hLHSInt, hRHSIntEq] using hInt

end AppliedModelingLib
