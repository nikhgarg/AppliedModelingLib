import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import AppliedModelingLib.Foundations.Probability.RandomUtility

/-!
# Random-Utility Density Comparisons

Reusable finite-atom and continuous `withDensity` comparisons for
three-alternative additive random-utility models.

The pure pointwise rearrangement and contraction lemmas live in
`AppliedModelingLib.Foundations.Probability.RandomUtility`.  This file adds the
probability wrappers that use those inequalities to compare density-product
laws under coordinate swaps.

## Main declarations

- `rum3ScoreDensityENN`
- `rum3_swap12_mass_le_of_density_formula`
- `rum3_swap23_mass_le_of_density_formula`
- `rum3_withDensity_swap12_measure_le_of_density_formula`
- `rum3_withDensity_swap23_measure_lt_of_density_formula`
-/

open MeasureTheory
open scoped ENNReal

namespace AppliedModelingLib
namespace Probability

noncomputable section

/--
Three-coordinate RUM score density as an `ℝ≥0∞` density for `withDensity`.

This is the continuous analogue of the finite density-product formula used by
sample-space endpoints.
-/
def rum3ScoreDensityENN {Ω : Type*} (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) : Ω → ENNReal :=
  fun ω => ENNReal.ofReal
    (f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))

/-- Measurability of the three-coordinate score density. -/
theorem rum3ScoreDensityENN_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    {f : ℝ → ℝ} (hf : Measurable f)
    (x1 x2 x3 : ℝ) {r1 r2 r3 : Ω → ℝ}
    (hr1 : Measurable r1) (hr2 : Measurable r2) (hr3 : Measurable r3) :
    Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) := by
  unfold rum3ScoreDensityENN
  exact (((hf.comp (hr1.sub_const x1)).mul (hf.comp (hr2.sub_const x2))).mul
    (hf.comp (hr3.sub_const x3))).ennreal_ofReal

/-- Positive noise density makes the three-coordinate score density nonzero. -/
theorem rum3ScoreDensityENN_ne_zero_of_noise_pos
    {Ω : Type*} {f : ℝ → ℝ}
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hpos : ∀ z : ℝ, 0 < f z) (ω : Ω) :
    rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3 ω ≠ 0 := by
  unfold rum3ScoreDensityENN
  have hreal :
      0 < f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3) :=
    mul_pos (mul_pos (hpos (r1 ω - x1)) (hpos (r2 ω - x2)))
      (hpos (r3 ω - x3))
  exact ne_of_gt (ENNReal.ofReal_pos.2 hreal)

/--
Positive base mass of a region remains positive under a strictly positive
three-coordinate score density.
-/
theorem rum3ScoreDensity_withDensity_measure_ne_zero_of_base_measure_ne_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) {f : ℝ → ℝ}
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hpos : ∀ z : ℝ, 0 < f z)
    {s : Set Ω} (hs : MeasurableSet s) (hbase : base s ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) s ≠ 0 :=
  withDensity_measure_ne_zero_of_pos_on
    base (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) hD hs hbase
    (fun ω _ => rum3ScoreDensityENN_ne_zero_of_noise_pos
      x1 x2 x3 r1 r2 r3 hpos ω)

/-- Normalization criterion for the three-coordinate score density. -/
theorem rum3ScoreDensity_isProbabilityMeasure_of_lintegral_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hD :
      ∫⁻ ω, (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂base = 1) :
    IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)) :=
  isProbabilityMeasure_withDensity_of_lintegral_eq_one
    base (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) hD

/--
Any source-region density integral is finite once the full score density is
normalized.
-/
theorem rum3ScoreDensity_setLIntegral_ne_top_of_lintegral_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hD :
      ∫⁻ ω, (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂base = 1)
    (s : Set Ω) :
    (∫⁻ ω in s, (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂base) ≠ ∞ :=
  setLIntegral_ne_top_of_lintegral_eq_one
    base (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) hD s

/--
Mass comparison for a finite sample law whose atoms are represented by the
three-coordinate density product, under a top/middle coordinate swap.
-/
theorem rum3_swap12_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    ∀ ω, p ω → (ν ω).toReal ≤ (ν (swap ω)).toReal := by
  intro ω hp
  rw [hdens ω, hdens (swap ω), hswap1 ω, hswap2 ω, hswap3 ω]
  exact weaklyWellOrderedNoise_swap12_density3_le
    hf (hctx ω hp) hx12 (hscore ω hp)

/--
Strict mass comparison for a finite sample law represented by the
three-coordinate density product, under a top/middle coordinate swap.
-/
theorem rum3_swap12_mass_lt_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 < f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    ∀ ω, p ω → (ν ω).toReal < (ν (swap ω)).toReal := by
  intro ω hp
  rw [hdens ω, hdens (swap ω), hswap1 ω, hswap2 ω, hswap3 ω]
  exact strictlyWellOrderedNoise_swap12_density3_lt
    hf (hctx ω hp) hx12 (hscore ω hp)

/--
Mass comparison for a finite sample law whose atoms are represented by the
three-coordinate density product, under a middle/bottom coordinate swap.
-/
theorem rum3_swap23_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    ∀ ω, p ω → (ν ω).toReal ≤ (ν (swap ω)).toReal := by
  intro ω hp
  rw [hdens ω, hdens (swap ω), hswap1 ω, hswap2 ω, hswap3 ω]
  exact weaklyWellOrderedNoise_swap23_density3_le
    hf (hctx ω hp) hx23 (hscore ω hp)

/--
Strict mass comparison for a finite sample law represented by the
three-coordinate density product, under a middle/bottom coordinate swap.
-/
theorem rum3_swap23_mass_lt_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 < f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    ∀ ω, p ω → (ν ω).toReal < (ν (swap ω)).toReal := by
  intro ω hp
  rw [hdens ω, hdens (swap ω), hswap1 ω, hswap2 ω, hswap3 ω]
  exact strictlyWellOrderedNoise_swap23_density3_lt
    hf (hctx ω hp) hx23 (hscore ω hp)

/--
Continuous with-density mass comparison for a top/middle coordinate swap.

If a measurable equivalence preserves the base score measure, maps source
event `p` into target event `q`, and swaps the first two score coordinates,
then weak well-ordering plus the source score inequality gives the
corresponding mass comparison under the product density.
-/
theorem rum3_withDensity_swap12_measure_le_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} ≤
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} := by
  refine withDensity_measure_le_of_measurableEquiv_image_subset_density_le
    base swap hmp (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) hp hq hmap ?_
  intro ω hpω
  unfold rum3ScoreDensityENN
  rw [hswap1 ω, hswap2 ω, hswap3 ω]
  exact ENNReal.ofReal_le_ofReal
    (weaklyWellOrderedNoise_swap12_density3_le
      hf (hctx ω hpω) hx12 (hscore ω hpω))

/--
Continuous with-density mass comparison for a middle/bottom coordinate swap.
-/
theorem rum3_withDensity_swap23_measure_le_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} ≤
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} := by
  refine withDensity_measure_le_of_measurableEquiv_image_subset_density_le
    base swap hmp (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) hp hq hmap ?_
  intro ω hpω
  unfold rum3ScoreDensityENN
  rw [hswap1 ω, hswap2 ω, hswap3 ω]
  exact ENNReal.ofReal_le_ofReal
    (weaklyWellOrderedNoise_swap23_density3_le
      hf (hctx ω hpω) hx23 (hscore ω hpω))

/--
Strict continuous with-density mass comparison for a top/middle coordinate
swap.

The positive-base-measure source assumption is the continuous replacement for a
finite strict witness atom.
-/
theorem rum3_withDensity_swap12_measure_lt_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω)
    (hfi :
      (∫⁻ ω in {ω | p ω},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos : base {ω | p ω} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} := by
  refine withDensity_measure_lt_of_measurableEquiv_image_subset_density_lt_on
    base swap hmp (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) hD
    hp hq hp hmap ?_ hfi (fun _ h => h) hsource_pos ?_
  · intro ω hpω
    unfold rum3ScoreDensityENN
    rw [hswap1 ω, hswap2 ω, hswap3 ω]
    exact ENNReal.ofReal_le_ofReal
      (le_of_lt
        (strictlyWellOrderedNoise_swap12_density3_lt
          hf (hpos (r3 ω - x3)) hx12 (hscore ω hpω)))
  · intro ω hpω
    unfold rum3ScoreDensityENN
    rw [hswap1 ω, hswap2 ω, hswap3 ω]
    have hreal :
        f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3) <
          f (r2 ω - x1) * f (r1 ω - x2) * f (r3 ω - x3) :=
      strictlyWellOrderedNoise_swap12_density3_lt
        hf (hpos (r3 ω - x3)) hx12 (hscore ω hpω)
    have htarget_pos :
        0 < f (r2 ω - x1) * f (r1 ω - x2) * f (r3 ω - x3) := by
      exact mul_pos (mul_pos (hpos (r2 ω - x1)) (hpos (r1 ω - x2)))
        (hpos (r3 ω - x3))
    exact (ENNReal.ofReal_lt_ofReal_iff htarget_pos).mpr hreal

/--
Strict continuous with-density mass comparison for a middle/bottom coordinate
swap.
-/
theorem rum3_withDensity_swap23_measure_lt_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω)
    (hfi :
      (∫⁻ ω in {ω | p ω},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos : base {ω | p ω} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} := by
  refine withDensity_measure_lt_of_measurableEquiv_image_subset_density_lt_on
    base swap hmp (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) hD
    hp hq hp hmap ?_ hfi (fun _ h => h) hsource_pos ?_
  · intro ω hpω
    unfold rum3ScoreDensityENN
    rw [hswap1 ω, hswap2 ω, hswap3 ω]
    exact ENNReal.ofReal_le_ofReal
      (le_of_lt
        (strictlyWellOrderedNoise_swap23_density3_lt
          hf (hpos (r1 ω - x1)) hx23 (hscore ω hpω)))
  · intro ω hpω
    unfold rum3ScoreDensityENN
    rw [hswap1 ω, hswap2 ω, hswap3 ω]
    have hreal :
        f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3) <
          f (r1 ω - x1) * f (r3 ω - x2) * f (r2 ω - x3) :=
      strictlyWellOrderedNoise_swap23_density3_lt
        hf (hpos (r1 ω - x1)) hx23 (hscore ω hpω)
    have htarget_pos :
        0 < f (r1 ω - x1) * f (r3 ω - x2) * f (r2 ω - x3) := by
      exact mul_pos (mul_pos (hpos (r1 ω - x1)) (hpos (r3 ω - x2)))
        (hpos (r2 ω - x3))
    exact (ENNReal.ofReal_lt_ofReal_iff htarget_pos).mpr hreal

end

end Probability
end AppliedModelingLib
