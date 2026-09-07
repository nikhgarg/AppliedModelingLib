import AppliedModelingLib.Foundations.Probability.ForwardPoisson
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Translation of stationary Poisson intensity

The intensity measure of a stationary point process on the real line is a
multiple of Lebesgue measure. Translating each point by an independent mark
convolves that intensity with the mark measure. This file proves the
translation-invariance calculation underlying that displacement step.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory
open scoped ENNReal MeasureTheory

noncomputable section

/-- A Poisson counting measure specified through its finite measurable
restrictions. Values of `finiteCount` outside finite-intensity measurable sets
carry no semantics; this keeps a locally finite point process from being
misrepresented as a natural-valued count on unbounded sets. -/
structure PoissonCountingMeasureByLaw
    (Ω X : Type*) [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (intensity : Measure X) where
  /-- The carrier probability law. -/
  isProbability : IsProbabilityMeasure P
  /-- Count of points in a set, with semantics asserted below only on finite
  measurable intensity sets. -/
  finiteCount : Set X → Ω → ℕ
  finiteCount_measurable : ∀ s, Measurable (finiteCount s)
  finiteCount_empty_ae : ∀ᵐ ω ∂P, finiteCount ∅ ω = 0
  /-- On finite measurable sets, the count is pathwise monotone. -/
  finiteCount_mono : ∀ s t,
    MeasurableSet s → MeasurableSet t → intensity s ≠ ∞ → intensity t ≠ ∞ →
      s ⊆ t → ∀ ω, finiteCount s ω ≤ finiteCount t ω
  /-- Additivity on disjoint finite measurable sets. -/
  finiteCount_union_ae : ∀ s t,
    MeasurableSet s → MeasurableSet t → intensity s ≠ ∞ → intensity t ≠ ∞ →
      Disjoint s t →
      ∀ᵐ ω ∂P, finiteCount (s ∪ t) ω = finiteCount s ω + finiteCount t ω
  /-- Counts on every finite disjoint measurable family are independent. -/
  finiteCount_independent : ∀ (n : ℕ) (s : Fin n → Set X),
    (∀ i, MeasurableSet (s i)) → (∀ i, intensity (s i) ≠ ∞) →
      Pairwise (fun i j => Disjoint (s i) (s j)) →
      ProbabilityTheory.iIndepFun (fun i => finiteCount (s i)) P
  /-- The count on a finite measurable set has its Poisson law. -/
  finiteCount_hasLaw : ∀ s, MeasurableSet s → intensity s ≠ ∞ →
    ProbabilityTheory.HasLaw (finiteCount s)
      (ProbabilityTheory.poissonMeasure (intensity s).toNNReal) P

namespace PoissonCountingMeasureByLaw

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {P : Measure Ω} {intensity : Measure X}

/-- A finite-set count coordinate is measurable. -/
theorem measurable_finiteCount
    (M : PoissonCountingMeasureByLaw Ω X P intensity) (s : Set X) :
    Measurable (M.finiteCount s) :=
  M.finiteCount_measurable s

end PoissonCountingMeasureByLaw

/-- Convolving Lebesgue intensity with a finite displacement measure preserves
Lebesgue intensity, scaled by the displacement measure's total mass. -/
theorem volume_conv_eq_mass_smul (displacement : Measure ℝ)
    [IsFiniteMeasure displacement] :
    (volume : Measure ℝ) ∗ displacement = displacement Set.univ • volume := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_conv hf]
  calc
    (∫⁻ x, ∫⁻ y, f (x + y) ∂displacement ∂volume) =
        ∫⁻ y, ∫⁻ x, f (x + y) ∂volume ∂displacement := by
      rw [lintegral_lintegral_swap]
      exact (hf.comp (measurable_fst.add measurable_snd)).aemeasurable
    _ = ∫⁻ y, ∫⁻ x, f x ∂volume ∂displacement := by
      apply lintegral_congr
      intro y
      calc
        (∫⁻ x, f (x + y) ∂volume) =
            ∫⁻ x, f x ∂Measure.map (fun x : ℝ => x + y) volume := by
          simpa using (lintegral_map hf (measurable_id.add_const y)).symm
        _ = ∫⁻ x, f x ∂volume := by
          rw [Measure.IsAddRightInvariant.map_add_right_eq_self]
    _ = displacement Set.univ * ∫⁻ x, f x ∂volume := by
      rw [lintegral_const]
      exact mul_comm _ _
    _ = ∫⁻ x, f x ∂(displacement Set.univ • volume) := by
      rw [lintegral_smul_measure]
      rfl

/-- The intensity of displacement times falling in a calendar interval. The
birth coordinate has Lebesgue intensity and the second coordinate is the
finite retained-delay measure. -/
theorem smul_volume_prod_preimage_add_Ioc (rate : ℝ≥0∞)
    (displacement : Measure ℝ) [IsFiniteMeasure displacement]
    (a b : ℝ) :
    (rate • ((volume : Measure ℝ).prod displacement))
        ((fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' Set.Ioc a b) =
      rate * displacement Set.univ * volume (Set.Ioc a b) := by
  rw [Measure.smul_apply]
  rw [← Measure.map_apply (measurable_fst.add measurable_snd) measurableSet_Ioc]
  rw [show Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
      ((volume : Measure ℝ).prod displacement) = volume ∗ displacement by rfl]
  rw [volume_conv_eq_mass_smul]
  simp [mul_assoc]

end

end AppliedModelingLib.Probability
