import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.Real

open scoped ENNReal unitInterval
open MeasureTheory

/-!
# Unit-interval power laws

The image of uniform mass on `[0, 1]` under `u ↦ u^a` has distribution
function `z ↦ z^(1/a)` on that interval when `a > 0`.  This elementary
construction is useful for power-CDF mixed strategies.
-/

namespace AppliedModelingLib.Probability

/-- Sample a power law by raising uniform unit-interval mass to a real power. -/
noncomputable def unitIntervalPowerSample (a : ℝ) (u : I) : ℝ :=
  (u : ℝ) ^ a

/-- The probability law of `U^a` for `U` uniform on the unit interval. -/
noncomputable def unitIntervalPowerLaw (a : ℝ) : Measure ℝ :=
  Measure.map (unitIntervalPowerSample a) (volume : Measure I)

theorem unitIntervalPowerSample_measurable (a : ℝ) :
    Measurable (unitIntervalPowerSample a) := by
  unfold unitIntervalPowerSample
  fun_prop

/-- A nonnegative power gives a continuous unit-interval sampler. -/
theorem unitIntervalPowerSample_continuous {a : ℝ} (ha : 0 ≤ a) :
    Continuous (unitIntervalPowerSample a) := by
  unfold unitIntervalPowerSample
  exact (Real.continuous_rpow_const ha).comp continuous_subtype_val

theorem unitIntervalPowerLaw_isProbabilityMeasure (a : ℝ) :
    IsProbabilityMeasure (unitIntervalPowerLaw a) := by
  unfold unitIntervalPowerLaw
  exact Measure.isProbabilityMeasure_map
    (unitIntervalPowerSample_measurable a).aemeasurable

theorem unitIntervalPowerSample_nonnegative (a : ℝ) (u : I) :
    0 ≤ unitIntervalPowerSample a u := by
  unfold unitIntervalPowerSample
  exact Real.rpow_nonneg u.2.1 a

theorem unitIntervalPowerSample_le_one {a : ℝ} (ha : 0 ≤ a) (u : I) :
    unitIntervalPowerSample a u ≤ 1 := by
  unfold unitIntervalPowerSample
  exact Real.rpow_le_one u.2.1 u.2.2 ha

/-- A positive power is injective on the unit interval. -/
theorem unitIntervalPowerSample_injOn {a : ℝ} (ha : 0 < a) :
    Set.InjOn (unitIntervalPowerSample a) Set.univ := by
  intro x _ y _ hxy
  apply Subtype.ext
  exact (Real.strictMonoOn_rpow_Ici_of_exponent_pos ha).injOn x.2.1 y.2.1
    (by simpa [unitIntervalPowerSample] using hxy)

/-- A positive-exponent unit-interval power law has no atoms. -/
theorem unitIntervalPowerLaw_noAtoms {a : ℝ} (ha : 0 < a) :
    NoAtoms (unitIntervalPowerLaw a) := by
  refine ⟨?_⟩
  intro z
  rw [unitIntervalPowerLaw,
    Measure.map_apply (unitIntervalPowerSample_measurable a) (measurableSet_singleton z)]
  have hsubsingleton : (unitIntervalPowerSample a ⁻¹' ({z} : Set ℝ)).Subsingleton := by
    intro x hx y hy
    apply unitIntervalPowerSample_injOn ha (Set.mem_univ _) (Set.mem_univ _)
    exact (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm
  exact hsubsingleton.measure_zero (volume : Measure I)

/-- A nonnegative-exponent power law is almost surely supported on `[0,1]`. -/
theorem unitIntervalPowerLaw_ae_mem_Icc {a : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ x ∂unitIntervalPowerLaw a, x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  change unitIntervalPowerLaw a (Set.Icc (0 : ℝ) 1)ᶜ = 0
  rw [unitIntervalPowerLaw,
    Measure.map_apply (unitIntervalPowerSample_measurable a) measurableSet_Icc.compl]
  have hpreimage : unitIntervalPowerSample a ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ = ∅ := by
    ext u
    change (unitIntervalPowerSample a u ∉ Set.Icc (0 : ℝ) 1) ↔ False
    constructor
    · intro h
      exact (h ⟨unitIntervalPowerSample_nonnegative a u,
        unitIntervalPowerSample_le_one ha u⟩).elim
    · simp
  rw [hpreimage]
  exact measure_empty

/--
The power-law CDF on its support.  Positivity of `a` is exactly what makes
`u ↦ u^a` invertible there with inverse exponent `a⁻¹`.
-/
theorem unitIntervalPowerLaw_cdf_on_unitInterval
    {a z : ℝ} (ha : 0 < a) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    unitIntervalPowerLaw a (Set.Iic z) = ENNReal.ofReal (z ^ a⁻¹) := by
  have hainv_pos : 0 < a⁻¹ := inv_pos.mpr ha
  have hthreshold_nonneg : 0 ≤ z ^ a⁻¹ :=
    Real.rpow_nonneg hz.1 a⁻¹
  have hthreshold_le_one : z ^ a⁻¹ ≤ 1 :=
    Real.rpow_le_one hz.1 hz.2 hainv_pos.le
  let threshold : I := ⟨z ^ a⁻¹, ⟨hthreshold_nonneg, hthreshold_le_one⟩⟩
  have hpreimage :
      {u : I | unitIntervalPowerSample a u ≤ z} = Set.Iic threshold := by
    ext u
    change (u : ℝ) ^ a ≤ z ↔ (u : ℝ) ≤ z ^ a⁻¹
    calc
      (u : ℝ) ^ a ≤ z ↔
          ((u : ℝ) ^ a) ^ a⁻¹ ≤ z ^ a⁻¹ :=
        (Real.rpow_le_rpow_iff (Real.rpow_nonneg u.2.1 a) hz.1 hainv_pos).symm
      _ ↔ (u : ℝ) ≤ z ^ a⁻¹ := by
        rw [← Real.rpow_mul u.2.1]
        have hmul : a * a⁻¹ = 1 := by
          field_simp [ne_of_gt ha]
        rw [hmul, Real.rpow_one]
  rw [unitIntervalPowerLaw,
    Measure.map_apply (unitIntervalPowerSample_measurable a) measurableSet_Iic]
  change (volume : Measure I) {u : I | unitIntervalPowerSample a u ≤ z} = _
  rw [hpreimage, unitInterval.volume_Iic]

/--
Every nonempty open subinterval of the unit interval has positive mass under a
positive-exponent power law.  Thus this law has full topological support on
`[0,1]`, even though its mean need not be one half.

The interval decomposition uses Mathlib's measure-union and no-atoms lemmas
from [`MeasureTheory/Measure`](https://github.com/leanprover-community/mathlib4/tree/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure),
at the repository-pinned Mathlib revision (Apache-2.0).  No external proof
code is copied or ported.
-/
theorem unitIntervalPowerLaw_measure_Ioo_pos
    {exponent a b : ℝ} (hexponent : 0 < exponent)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    0 < unitIntervalPowerLaw exponent (Set.Ioo a b) := by
  letI : NoAtoms (unitIntervalPowerLaw exponent) :=
    unitIntervalPowerLaw_noAtoms hexponent
  have hIoc : 0 < unitIntervalPowerLaw exponent (Set.Ioc a b) := by
    by_contra hnot
    have hzero : unitIntervalPowerLaw exponent (Set.Ioc a b) = 0 :=
      bot_unique (le_of_not_gt hnot)
    have hCDF : unitIntervalPowerLaw exponent (Set.Iic a) =
        unitIntervalPowerLaw exponent (Set.Iic b) := by
      calc
        unitIntervalPowerLaw exponent (Set.Iic a) =
            unitIntervalPowerLaw exponent (Set.Iic a) +
              unitIntervalPowerLaw exponent (Set.Ioc a b) := by
                rw [hzero, add_zero]
        _ = unitIntervalPowerLaw exponent (Set.Iic a ∪ Set.Ioc a b) := by
              rw [MeasureTheory.measure_union (Set.Iic_disjoint_Ioc le_rfl)
                measurableSet_Ioc]
        _ = unitIntervalPowerLaw exponent (Set.Iic b) := by
              rw [Set.Iic_union_Ioc_eq_Iic hab.le]
    have hpowpos : 0 < b ^ exponent⁻¹ :=
      Real.rpow_pos_of_pos (lt_of_le_of_lt ha hab) _
    have hpowlt : a ^ exponent⁻¹ < b ^ exponent⁻¹ :=
      Real.strictMonoOn_rpow_Ici_of_exponent_pos (inv_pos.mpr hexponent) ha
        (ha.trans hab.le) hab
    have hCDFlt : unitIntervalPowerLaw exponent (Set.Iic a) <
        unitIntervalPowerLaw exponent (Set.Iic b) := by
      rw [unitIntervalPowerLaw_cdf_on_unitInterval hexponent
          ⟨ha, hab.le.trans hb⟩,
        unitIntervalPowerLaw_cdf_on_unitInterval hexponent ⟨ha.trans hab.le, hb⟩]
      exact (ENNReal.ofReal_lt_ofReal_iff hpowpos).mpr hpowlt
    exact (ne_of_lt hCDFlt) hCDF
  have hset : Set.Ioo a b = Set.Ioc a b \ {b} := by
    ext x
    constructor
    · rintro ⟨hax, hxb⟩
      refine ⟨⟨hax, hxb.le⟩, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact hxb.ne
    · rintro ⟨⟨hax, hxb⟩, hne⟩
      exact ⟨hax, hxb.lt_of_ne hne⟩
  have hdiff : unitIntervalPowerLaw exponent (Set.Ioc a b \ {b}) =
      unitIntervalPowerLaw exponent (Set.Ioc a b) :=
    MeasureTheory.measure_diff_null (measure_singleton b)
  rw [hset, hdiff]
  exact hIoc

theorem unitIntervalPowerLaw_cdf_of_lt_zero
    {a z : ℝ} (hz : z < 0) :
    unitIntervalPowerLaw a (Set.Iic z) = 0 := by
  have hpreimage : {u : I | unitIntervalPowerSample a u ≤ z} = ∅ := by
    ext u
    change unitIntervalPowerSample a u ≤ z ↔ False
    constructor
    · intro h
      linarith [unitIntervalPowerSample_nonnegative a u]
    · simp
  rw [unitIntervalPowerLaw,
    Measure.map_apply (unitIntervalPowerSample_measurable a) measurableSet_Iic]
  change (volume : Measure I) {u : I | unitIntervalPowerSample a u ≤ z} = 0
  rw [hpreimage]
  exact measure_empty

theorem unitIntervalPowerLaw_cdf_of_one_le
    {a z : ℝ} (ha : 0 ≤ a) (hz : 1 ≤ z) :
    unitIntervalPowerLaw a (Set.Iic z) = 1 := by
  have hpreimage : {u : I | unitIntervalPowerSample a u ≤ z} = Set.univ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact (unitIntervalPowerSample_le_one ha u).trans hz
  rw [unitIntervalPowerLaw,
    Measure.map_apply (unitIntervalPowerSample_measurable a) measurableSet_Iic]
  change (volume : Measure I) {u : I | unitIntervalPowerSample a u ≤ z} = 1
  rw [hpreimage]
  exact measure_univ

end AppliedModelingLib.Probability
