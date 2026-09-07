import Mathlib.Probability.Kernel.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Normalized densities as Markov kernels

A jointly measurable density whose integral is one defines a Markov kernel.
For real-valued kernels, its upper-tail mass is jointly measurable in the
conditioning variable and the threshold.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-- A jointly measurable family of normalized densities relative to `μ`. -/
structure NormalizedKernelDensity
    (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure β) [SFinite μ] where
  density : α → β → ℝ≥0∞
  density_measurable : Measurable (Function.uncurry density)
  integral_eq_one : ∀ a, ∫⁻ b, density a b ∂μ = 1

namespace NormalizedKernelDensity

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure β} [SFinite μ]

/-- The kernel obtained by integrating the normalized density. -/
noncomputable def toKernel (D : NormalizedKernelDensity α β μ) : Kernel α β :=
  Kernel.withDensity (Kernel.const α μ) D.density

theorem toKernel_eq_withDensity (D : NormalizedKernelDensity α β μ) :
    D.toKernel = Kernel.withDensity (Kernel.const α μ) D.density :=
  rfl

/-- Normalization makes the density kernel a Markov kernel. -/
theorem toKernel_isMarkov (D : NormalizedKernelDensity α β μ) :
    IsMarkovKernel D.toKernel := by
  refine ⟨fun a => MeasureTheory.isProbabilityMeasure_iff.mpr ?_⟩
  rw [toKernel, Kernel.withDensity_apply' _ D.density_measurable]
  simpa using D.integral_eq_one a

/-- Upper-tail mass of a normalized real density is jointly measurable. -/
theorem measurable_tailMass
    {α : Type*} [MeasurableSpace α]
    {μ : Measure ℝ} [SFinite μ]
    (D : NormalizedKernelDensity α ℝ μ) :
    Measurable (fun p : α × ℝ => D.toKernel p.1 (Set.Ioi p.2)) := by
  have hf : Measurable (fun q : (α × ℝ) × ℝ =>
      (Set.Ioi q.1.2).indicator (fun y => D.density q.1.1 y) q.2) := by
    apply Measurable.indicator
    · exact D.density_measurable.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    · exact measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd
  have hlin : Measurable (fun p : α × ℝ =>
      ∫⁻ y, (Set.Ioi p.2).indicator (fun z => D.density p.1 z) y ∂μ) :=
    hf.lintegral_prod_right
  convert hlin using 1
  funext p
  rw [toKernel, Kernel.withDensity_apply' _ D.density_measurable]
  exact (MeasureTheory.lintegral_indicator measurableSet_Ioi _).symm

end NormalizedKernelDensity

end


end AppliedModelingLib.Probability
