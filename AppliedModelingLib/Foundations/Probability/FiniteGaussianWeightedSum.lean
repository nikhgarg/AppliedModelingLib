import AppliedModelingLib.Foundations.Probability.GaussianSignalRCD
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Finite weighted sums of independent Gaussian coordinates

This module records the measure-level law of a finite weighted sum of
independent centred Gaussian coordinates.  It is intentionally independent
of any paper model or posterior construction.
-/

namespace AppliedModelingLib
namespace Probability

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- A finite weighted sum of independent centred Gaussian coordinates is
centred Gaussian, with the usual sum of weighted variances. -/
theorem gaussianPi_map_weighted_sum
    {ι : Type*} [Fintype ι]
    (variance : ι → ℝ≥0) (weight : ι → ℝ) :
    (Measure.pi fun i => gaussianReal 0 (variance i)).map
        (fun x => ∑ i, weight i * x i) =
      gaussianReal 0 (∑ i, (weight i ^ 2).toNNReal * variance i) := by
  classical
  let μ : ι → Measure ℝ := fun i => gaussianReal 0 (variance i)
  let P : Measure (ι → ℝ) := Measure.pi μ
  let X : ι → (ι → ℝ) → ℝ := fun i x => weight i * x i
  have hP : IsProbabilityMeasure P := by
    dsimp [P, μ]
    infer_instance
  have hX_meas : ∀ i, Measurable (X i) := by
    intro i
    dsimp [X]
    fun_prop
  have hX_map : ∀ i, P.map (X i) =
      gaussianReal 0 ((weight i ^ 2).toNNReal * variance i) := by
    intro i
    calc
      P.map (X i) = (μ i).map (fun x : ℝ => weight i * x) := by
        change (Measure.pi μ).map (fun x => weight i * x i) = _
        rw [show (fun x : ι → ℝ => weight i * x i) =
            (fun x : ℝ => weight i * x) ∘ (fun x : ι → ℝ => x i) by rfl]
        rw [← Measure.map_map (by fun_prop) (by fun_prop)]
        rw [(measurePreserving_eval μ i).map_eq]
      _ = gaussianReal 0 ((weight i ^ 2).toNNReal * variance i) := by
        dsimp [μ]
        convert gaussianReal_map_const_mul
          (μ := (0 : ℝ)) (v := variance i) (weight i) using 1
        apply (gaussianReal_ext_iff).2
        constructor
        · ring
        · apply Subtype.ext
          simp [Real.toNNReal_of_nonneg (sq_nonneg (weight i))]
  have hX_indep : iIndepFun X P := by
    have hbase : iIndepFun (fun i : ι => fun x : ι → ℝ => x i) P := by
      dsimp [P]
      exact iIndepFun_pi (X := fun _ : ι => id)
        (fun _ : ι => aemeasurable_id)
    simpa [X, Function.comp_def] using
      (hbase.comp (fun i : ι => fun x : ℝ => weight i * x)
        (fun _ => by fun_prop))
  apply Measure.ext_of_charFun
  ext t
  rw [show (Measure.pi fun i => gaussianReal 0 (variance i)).map
      (fun x => ∑ i, weight i * x i) = P.map (fun x => ∑ i, X i x) by rfl]
  rw [hX_indep.charFun_map_fun_sum_eq_prod]
  · simp_rw [hX_map]
    rw [Fintype.prod_apply]
    simp_rw [charFun_gaussianReal]
    rw [← Complex.exp_sum]
    congr 1
    simp [Finset.sum_mul,
      Real.toNNReal_of_nonneg (sq_nonneg _)]
    rw [Finset.sum_div]
  · exact fun i => (hX_meas i).aemeasurable

end

end Probability
end AppliedModelingLib
