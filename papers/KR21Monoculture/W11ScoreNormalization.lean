import KR21Monoculture.W11RankingCells

open AppliedModelingLib MeasureTheory Filter
open scoped Topology ENNReal

namespace KR21Monoculture

/-!
# Normalization of the corrected two-candidate score law

The corrected Theorem 5 score model uses one translated copy of the base
noise density for each candidate.  This file discharges the normalization of
the concrete two-coordinate law from the corresponding one-dimensional
normalization.  It does not assume the joint density has mass one.
-/

/-- Translating a measurable one-dimensional density preserves its extended-real mass. -/
theorem lintegral_ofReal_sub_right_eq_one
    (f : ℝ → ℝ) (hf : Measurable f)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) (u : ℝ) :
    ∫⁻ x, ENNReal.ofReal (f (x - u)) ∂volume = 1 := by
  calc
    ∫⁻ x, ENNReal.ofReal (f (x - u)) ∂volume =
        ∫⁻ x, ENNReal.ofReal (f x) ∂volume := by
      simpa only [Function.comp_apply] using
        (measurePreserving_sub_right volume u).lintegral_comp hf.ennreal_ofReal
    _ = 1 := hnormalized

/--
The concrete two-score density has total mass one whenever the base density
is measurable, pointwise nonnegative, and has total mass one.  The proof uses
the two independent volume coordinates and translation invariance; no
normalization of the joint law is an input.
-/
theorem twoCandidateScoreDensityENN_lintegral_eq_one_of_base_normalization
    (f : ℝ → ℝ) (hf : Measurable f) (h_nonnegative : ∀ x, 0 ≤ f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate 0 → ℝ) (theta : ℝ) :
    ∫⁻ z, twoCandidateScoreDensityENN f value theta z ∂volume.prod volume = 1 := by
  let f0 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f (x - theta * value 0))
  let f1 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f (x - theta * value 1))
  have hf0 : AEMeasurable f0 (volume : Measure ℝ) := by
    exact ((hf.comp (measurable_id.sub measurable_const)).ennreal_ofReal).aemeasurable
  have hf1 : AEMeasurable f1 (volume : Measure ℝ) := by
    exact ((hf.comp (measurable_id.sub measurable_const)).ennreal_ofReal).aemeasurable
  have h0 : ∫⁻ x, f0 x ∂volume = 1 := by
    exact lintegral_ofReal_sub_right_eq_one f hf hnormalized (theta * value 0)
  have h1 : ∫⁻ x, f1 x ∂volume = 1 := by
    exact lintegral_ofReal_sub_right_eq_one f hf hnormalized (theta * value 1)
  calc
    ∫⁻ z, twoCandidateScoreDensityENN f value theta z ∂volume.prod volume =
        ∫⁻ z : ℝ × ℝ, f0 z.1 * f1 z.2 ∂volume.prod volume := by
      apply lintegral_congr
      intro z
      simp only [twoCandidateScoreDensityENN, twoCandidateScoreDensity, f0, f1]
      rw [ENNReal.ofReal_mul (h_nonnegative _)]
    _ = (∫⁻ x, f0 x ∂volume) * ∫⁻ x, f1 x ∂volume := by
      rw [lintegral_prod_mul hf0 hf1]
    _ = 1 := by simp [h0, h1]

/-- The corrected two-score measure is probabilistic under base-density normalization. -/
theorem twoCandidateScoreLaw_isProbabilityMeasure_of_base_normalization
    (f : ℝ → ℝ) (hf : Measurable f) (h_nonnegative : ∀ x, 0 ≤ f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate 0 → ℝ) (theta : ℝ) :
    IsProbabilityMeasure (twoCandidateScoreLaw f value theta) :=
  twoCandidateScoreLaw_isProbabilityMeasure_of_lintegral_eq_one f value theta
    (twoCandidateScoreDensityENN_lintegral_eq_one_of_base_normalization
      f hf h_nonnegative hnormalized value theta)

end KR21Monoculture
