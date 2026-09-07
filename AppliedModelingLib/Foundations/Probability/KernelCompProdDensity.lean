import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Composition products with a density on the base coordinate

This small measure-level bridge keeps a rate-dependent density on a path
coordinate separate from an arbitrary conditional response kernel.  In
particular, the response kernel may have atoms, which is essential for
stopping policies with deterministic caps.
-/

namespace MeasureTheory.Measure

open ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {alpha beta : Type*} {malpha : MeasurableSpace alpha}
  {mbeta : MeasurableSpace beta}
  {mu : Measure alpha} {kappa : Kernel alpha beta}
  {f : alpha -> ENNReal}

/-- Weighting the base measure before composing with a response kernel is the
same as weighting the joint law by that base-coordinate density. -/
theorem compProd_withDensity_left
    [SFinite mu] [IsSFiniteKernel kappa] (hf : Measurable f) :
    (mu.withDensity f) ⊗ₘ kappa =
      (mu ⊗ₘ kappa).withDensity (fun p => f p.1) := by
  ext s hs
  calc
    ((mu.withDensity f) ⊗ₘ kappa) s =
        ∫⁻ a, kappa a (Prod.mk a ⁻¹' s) ∂mu.withDensity f := by
      rw [compProd_apply hs]
    _ = ∫⁻ a, f a * kappa a (Prod.mk a ⁻¹' s) ∂mu := by
      simpa only [Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul mu hf
          (Kernel.measurable_kernel_prodMk_left hs))
    _ = ∫⁻ p in s, f p.1 ∂mu ⊗ₘ kappa := by
      rw [← lintegral_indicator hs, lintegral_compProd]
      · apply lintegral_congr
        intro a
        let sa : Set beta := Prod.mk a ⁻¹' s
        have hsa : MeasurableSet sa := measurable_prodMk_left hs
        have hfun :
            (fun b => s.indicator (fun p : alpha × beta => f p.1) (a, b)) =
              sa.indicator (fun _ => f a) := by
          funext b
          by_cases h : (a, b) ∈ s
          · have hb : b ∈ sa := by
              simpa [sa] using h
            rw [Set.indicator_of_mem h, Set.indicator_of_mem hb]
          · have hb : b ∉ sa := by
              simpa [sa] using h
            rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hb]
        rw [hfun, lintegral_indicator hsa]
        simp [sa]
      · exact (hf.comp measurable_fst).indicator hs
    _ = ((mu ⊗ₘ kappa).withDensity (fun p => f p.1)) s := by
      exact (withDensity_apply _ hs).symm

end

end MeasureTheory.Measure
