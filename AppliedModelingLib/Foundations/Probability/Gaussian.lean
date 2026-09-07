import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import AppliedModelingLib.Foundations.Math.AffineThreshold

open scoped BigOperators

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-!
# Gaussian Algebra and Testing-Paper Interfaces

Reusable Gaussian-facing algebra for admissions/testing papers.

This file deliberately separates two layers:

1. exact conjugate-normal precision algebra, which is formalized here; and
2. analytic normal CDF/density/hazard facts, which are exposed through API
   records. `GaussianMathlib` instantiates the basic CDF/density API from
   mathlib's `ProbabilityTheory.gaussianReal` and Gaussian PDF facts; quantile
   and inverse-Mills/hazard facts remain separate analytic interfaces.

## Main declarations

- `GaussianVarianceLaw`, `GaussianScaleLaw`
- `StandardGaussianCDFAPI`
- `GaussianLowerTailMeanCertificate`
- `GaussianPriorSignal`
- `GaussianSignalFamily`
- `GaussianOffsetSignalFamily`
- `GaussianOffsetSignalFamily.conditionalPosteriorMeanScaleLaw`
- `GaussianHazardCertificate`
-/

/-- A Gaussian law represented by mean and variance. -/
structure GaussianVarianceLaw where
  mean : ℝ
  variance : ℝ
  variance_pos : 0 < variance

/-- A Gaussian location-scale law represented by mean and positive scale. -/
structure GaussianScaleLaw where
  mean : ℝ
  scale : ℝ
  scale_pos : 0 < scale

namespace GaussianScaleLaw

/-- Extensionality for Gaussian location-scale laws. -/
theorem ext {L1 L2 : GaussianScaleLaw}
    (hmean : L1.mean = L2.mean) (hscale : L1.scale = L2.scale) :
    L1 = L2 := by
  cases L1
  cases L2
  simp at hmean hscale
  subst hmean
  subst hscale
  rfl

/-- Standardize a value relative to a Gaussian location-scale law. -/
def standardize (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  (x - L.mean) / L.scale

/-- Undo standardization relative to a Gaussian location-scale law. -/
def unstandardize (L : GaussianScaleLaw) (z : ℝ) : ℝ :=
  L.mean + L.scale * z

@[simp] theorem standardize_mean (L : GaussianScaleLaw) :
    L.standardize L.mean = 0 := by
  simp [standardize]

theorem standardize_unstandardize (L : GaussianScaleLaw) (z : ℝ) :
    L.standardize (L.unstandardize z) = z := by
  rw [standardize, unstandardize]
  calc
    (L.mean + L.scale * z - L.mean) / L.scale =
        (L.scale * z) / L.scale := by
      congr
      ring
    _ = z := by
      exact mul_div_cancel_left₀ z (ne_of_gt L.scale_pos)

theorem unstandardize_standardize (L : GaussianScaleLaw) (x : ℝ) :
    L.unstandardize (L.standardize x) = x := by
  rw [standardize, unstandardize]
  calc
    L.mean + L.scale * ((x - L.mean) / L.scale) =
        L.mean + (x - L.mean) := by
      rw [mul_div_cancel₀ _ (ne_of_gt L.scale_pos)]
    _ = x := by
      ring

theorem ne_of_mean_ne {L₁ L₂ : GaussianScaleLaw}
    (h : L₁.mean ≠ L₂.mean) : L₁ ≠ L₂ := by
  intro hEq
  exact h (congrArg GaussianScaleLaw.mean hEq)

theorem ne_of_mean_lt {L₁ L₂ : GaussianScaleLaw}
    (h : L₁.mean < L₂.mean) : L₁ ≠ L₂ :=
  ne_of_mean_ne (ne_of_lt h)

theorem ne_of_scale_ne {L₁ L₂ : GaussianScaleLaw}
    (h : L₁.scale ≠ L₂.scale) : L₁ ≠ L₂ := by
  intro hEq
  exact h (congrArg GaussianScaleLaw.scale hEq)

theorem ne_of_scale_lt {L₁ L₂ : GaussianScaleLaw}
    (h : L₁.scale < L₂.scale) : L₁ ≠ L₂ :=
  ne_of_scale_ne (ne_of_lt h)

theorem standardize_mono (L : GaussianScaleLaw) :
    Monotone L.standardize := by
  intro x y hxy
  exact div_le_div_of_nonneg_right
    (sub_le_sub_right hxy L.mean) L.scale_pos.le

theorem standardize_strictMono (L : GaussianScaleLaw) :
    StrictMono L.standardize := by
  intro x y hxy
  exact div_lt_div_of_pos_right
    (sub_lt_sub_right hxy L.mean) L.scale_pos

theorem standardize_le_standardize_of_mean_le_same_scale
    {L1 L2 : GaussianScaleLaw} (hscale : L1.scale = L2.scale)
    (hmean : L1.mean ≤ L2.mean) (x : ℝ) :
    L2.standardize x ≤ L1.standardize x := by
  rw [standardize, standardize, hscale]
  exact div_le_div_of_nonneg_right (sub_le_sub_left hmean x) L2.scale_pos.le

theorem standardize_le_standardize_of_same_mean_scale_le_of_mean_le
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale ≤ Llarge.scale)
    {x : ℝ} (hx : Lsmall.mean ≤ x) :
    Llarge.standardize x ≤ Lsmall.standardize x := by
  rw [standardize, standardize, ← hmean]
  exact div_le_div_of_nonneg_left
    (sub_nonneg.mpr hx) Lsmall.scale_pos hscale

theorem standardize_lt_standardize_of_same_mean_scale_lt_of_mean_lt
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale < Llarge.scale)
    {x : ℝ} (hx : Lsmall.mean < x) :
    Llarge.standardize x < Lsmall.standardize x := by
  rw [standardize, standardize, ← hmean]
  exact div_lt_div_of_pos_left
    (sub_pos.mpr hx) Lsmall.scale_pos hscale

theorem standardize_le_standardize_of_same_mean_scale_le_of_le_mean
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale ≤ Llarge.scale)
    {x : ℝ} (hx : x ≤ Lsmall.mean) :
    Lsmall.standardize x ≤ Llarge.standardize x := by
  rw [standardize, standardize, ← hmean]
  have hnum_nonpos : x - Lsmall.mean ≤ 0 := sub_nonpos.mpr hx
  have hinv : 1 / Llarge.scale ≤ 1 / Lsmall.scale :=
    one_div_le_one_div_of_le Lsmall.scale_pos hscale
  have hmul :
      (x - Lsmall.mean) * (1 / Lsmall.scale) ≤
        (x - Lsmall.mean) * (1 / Llarge.scale) :=
    mul_le_mul_of_nonpos_left hinv hnum_nonpos
  simpa [div_eq_mul_inv] using hmul

theorem standardize_lt_standardize_of_same_mean_scale_lt_of_lt_mean
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale < Llarge.scale)
    {x : ℝ} (hx : x < Lsmall.mean) :
    Lsmall.standardize x < Llarge.standardize x := by
  rw [standardize, standardize, ← hmean]
  have hnum_neg : x - Lsmall.mean < 0 := sub_neg.mpr hx
  have hinv : 1 / Llarge.scale < 1 / Lsmall.scale :=
    one_div_lt_one_div_of_lt Lsmall.scale_pos hscale
  have hmul :
      (x - Lsmall.mean) * (1 / Lsmall.scale) <
        (x - Lsmall.mean) * (1 / Llarge.scale) :=
    mul_lt_mul_of_neg_left hinv hnum_neg
  simpa [div_eq_mul_inv] using hmul

/-- Positive affine image of a Gaussian location-scale law. -/
def affineImage (L : GaussianScaleLaw) (a b : ℝ) (hb : 0 < b) :
    GaussianScaleLaw where
  mean := a + b * L.mean
  scale := b * L.scale
  scale_pos := mul_pos hb L.scale_pos

@[simp] theorem affineImage_mean (L : GaussianScaleLaw)
    (a b : ℝ) (hb : 0 < b) :
    (L.affineImage a b hb).mean = a + b * L.mean := rfl

@[simp] theorem affineImage_scale (L : GaussianScaleLaw)
    (a b : ℝ) (hb : 0 < b) :
    (L.affineImage a b hb).scale = b * L.scale := rfl

theorem standardize_affineImage_map (L : GaussianScaleLaw)
    (a : ℝ) {b : ℝ} (hb : 0 < b) (x : ℝ) :
    (L.affineImage a b hb).standardize (a + b * x) =
      L.standardize x := by
  rw [standardize, standardize, affineImage]
  field_simp [ne_of_gt hb, ne_of_gt L.scale_pos]
  ring

theorem standardize_affineImage_threshold (L : GaussianScaleLaw)
    (a : ℝ) {b : ℝ} (hb : 0 < b) (threshold : ℝ) :
    (L.affineImage a b hb).standardize threshold =
      L.standardize ((threshold - a) / b) := by
  rw [standardize, standardize, affineImage]
  field_simp [ne_of_gt hb, ne_of_gt L.scale_pos]
  ring

end GaussianScaleLaw

/-!
## Precision-Standardized Cutoff Algebra

Admissions/testing papers often rewrite Gaussian standardized thresholds in
precision form.  The next lemmas isolate the real algebra converting those
standardized-threshold comparisons into lower-cutoff rules for skill.
-/

/--
Two-threshold precision-standardized comparison.

When group `A` has larger square-root precision than group `B`, comparing the
two displayed standardized-threshold expressions is equivalent to requiring
skill `q` to exceed the induced lower cutoff.
-/
theorem precisionStandardizedThreshold_lt_iff_cutoff_lt_skill
    {priorPrecision sqrtPrecB sqrtPrecA thresholdA thresholdB mean q : ℝ}
    (hsqrtB_pos : 0 < sqrtPrecB) (hsqrtA_pos : 0 < sqrtPrecA)
    (hgap : sqrtPrecB < sqrtPrecA) :
    priorPrecision * (thresholdA - mean) / sqrtPrecA +
        sqrtPrecA * (thresholdA - q) <
      priorPrecision * (thresholdB - mean) / sqrtPrecB +
        sqrtPrecB * (thresholdB - q) ↔
      ((priorPrecision + sqrtPrecA ^ 2) / sqrtPrecA * thresholdA -
            (priorPrecision + sqrtPrecB ^ 2) / sqrtPrecB * thresholdB) /
          (sqrtPrecA - sqrtPrecB) +
        mean * priorPrecision / (sqrtPrecA * sqrtPrecB) <
        q := by
  have hfactor_pos : 0 < sqrtPrecA - sqrtPrecB := sub_pos.mpr hgap
  let cutoff :=
    ((priorPrecision + sqrtPrecA ^ 2) / sqrtPrecA * thresholdA -
          (priorPrecision + sqrtPrecB ^ 2) / sqrtPrecB * thresholdB) /
        (sqrtPrecA - sqrtPrecB) +
      mean * priorPrecision / (sqrtPrecA * sqrtPrecB)
  have hdiff :
      (priorPrecision * (thresholdA - mean) / sqrtPrecA +
          sqrtPrecA * (thresholdA - q)) -
        (priorPrecision * (thresholdB - mean) / sqrtPrecB +
          sqrtPrecB * (thresholdB - q)) =
        (sqrtPrecA - sqrtPrecB) * (cutoff - q) := by
    dsimp [cutoff]
    field_simp [ne_of_gt hsqrtA_pos, ne_of_gt hsqrtB_pos,
      ne_of_gt hfactor_pos]
    ring
  constructor
  · intro hstd
    have hneg :
        (sqrtPrecA - sqrtPrecB) * (cutoff - q) < 0 := by
      rw [← hdiff]
      linarith
    have hinner : cutoff - q < 0 := by
      have hneg' :
          (sqrtPrecA - sqrtPrecB) * (cutoff - q) <
            (sqrtPrecA - sqrtPrecB) * 0 := by
        simpa using hneg
      exact lt_of_mul_lt_mul_left hneg' hfactor_pos.le
    dsimp [cutoff] at hinner
    linarith
  · intro hq
    have hinner : cutoff - q < 0 := by
      dsimp [cutoff]
      linarith
    have hneg :
        (sqrtPrecA - sqrtPrecB) * (cutoff - q) < 0 := by
      simpa using mul_neg_of_pos_of_neg hfactor_pos hinner
    rw [← hdiff] at hneg
    linarith

/--
Same-threshold specialization of
`precisionStandardizedThreshold_lt_iff_cutoff_lt_skill`.
-/
theorem precisionStandardizedSameThreshold_lt_iff_cutoff_lt_skill
    {priorPrecision sqrtPrecB sqrtPrecA threshold mean q : ℝ}
    (hsqrtB_pos : 0 < sqrtPrecB) (hsqrtA_pos : 0 < sqrtPrecA)
    (hgap : sqrtPrecB < sqrtPrecA) :
    priorPrecision * (threshold - mean) / sqrtPrecA +
        sqrtPrecA * (threshold - q) <
      priorPrecision * (threshold - mean) / sqrtPrecB +
        sqrtPrecB * (threshold - q) ↔
      threshold -
          priorPrecision * (threshold - mean) / (sqrtPrecB * sqrtPrecA) <
        q := by
  have hfactor_pos : 0 < sqrtPrecA - sqrtPrecB := sub_pos.mpr hgap
  have hdiff :
      (priorPrecision * (threshold - mean) / sqrtPrecA +
          sqrtPrecA * (threshold - q)) -
        (priorPrecision * (threshold - mean) / sqrtPrecB +
          sqrtPrecB * (threshold - q)) =
        (sqrtPrecA - sqrtPrecB) *
          ((threshold - q) -
            priorPrecision * (threshold - mean) /
              (sqrtPrecB * sqrtPrecA)) := by
    field_simp [ne_of_gt hsqrtA_pos, ne_of_gt hsqrtB_pos]
    ring
  constructor
  · intro hstd
    have hneg :
        (sqrtPrecA - sqrtPrecB) *
          ((threshold - q) -
            priorPrecision * (threshold - mean) /
              (sqrtPrecB * sqrtPrecA)) < 0 := by
      rw [← hdiff]
      linarith
    have hinner :
        (threshold - q) -
            priorPrecision * (threshold - mean) /
              (sqrtPrecB * sqrtPrecA) < 0 := by
      have hneg' :
          (sqrtPrecA - sqrtPrecB) *
            ((threshold - q) -
              priorPrecision * (threshold - mean) /
                (sqrtPrecB * sqrtPrecA)) <
          (sqrtPrecA - sqrtPrecB) * 0 := by
        simpa using hneg
      exact lt_of_mul_lt_mul_left hneg' hfactor_pos.le
    linarith
  · intro hq
    have hinner :
        (threshold - q) -
            priorPrecision * (threshold - mean) /
              (sqrtPrecB * sqrtPrecA) < 0 := by
      linarith
    have hneg :
        (sqrtPrecA - sqrtPrecB) *
          ((threshold - q) -
            priorPrecision * (threshold - mean) /
              (sqrtPrecB * sqrtPrecA)) < 0 := by
      simpa using mul_neg_of_pos_of_neg hfactor_pos hinner
    rw [← hdiff] at hneg
    linarith

/--
Abstract standard-normal CDF/density API.

Analytic papers can instantiate this once a concrete normal CDF/density library
is available. Until then, caller-specific Gaussian proofs can state exactly
which normal facts they require without hiding them in theorem conclusions.
-/
structure StandardGaussianCDFAPI where
  cdf : ℝ → ℝ
  density : ℝ → ℝ
  cdf_continuous : Continuous cdf
  cdf_mono : Monotone cdf
  cdf_strictMono : StrictMono cdf
  cdf_zero_eq_half : cdf 0 = (1 / 2 : ℝ)
  density_nonneg : ∀ z, 0 ≤ density z
  cdf_nonneg : ∀ z, 0 ≤ cdf z
  cdf_le_one : ∀ z, cdf z ≤ 1

namespace StandardGaussianCDFAPI

/-- Normal CDF for an arbitrary location-scale law by standardization. -/
def normalCDF (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  api.cdf (L.standardize x)

/-- Normal upper tail for an arbitrary location-scale law. -/
def normalTail (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  1 - api.normalCDF L x

/-- Normal density for an arbitrary location-scale law, up to the usual scale factor. -/
def normalDensity (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  api.density (L.standardize x) / L.scale

theorem normalCDF_mono (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) :
    Monotone (api.normalCDF L) := by
  intro x y hxy
  exact api.cdf_mono (L.standardize_mono hxy)

theorem normalCDF_strictMono (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) :
    StrictMono (api.normalCDF L) := by
  intro x y hxy
  exact api.cdf_strictMono (L.standardize_strictMono hxy)

theorem normalCDF_continuous (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) :
    Continuous (api.normalCDF L) := by
  have hstd : Continuous L.standardize := by
    unfold GaussianScaleLaw.standardize
    fun_prop
  exact api.cdf_continuous.comp hstd

theorem normalCDF_nonneg (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) :
    0 ≤ api.normalCDF L x :=
  api.cdf_nonneg (L.standardize x)

theorem normalCDF_le_one (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) :
    api.normalCDF L x ≤ 1 :=
  api.cdf_le_one (L.standardize x)

theorem normalCDF_at_mean (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) :
    api.normalCDF L L.mean = (1 / 2 : ℝ) := by
  simp [normalCDF, api.cdf_zero_eq_half]

theorem normalTail_nonneg (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) :
    0 ≤ api.normalTail L x := by
  dsimp [normalTail]
  exact sub_nonneg.mpr (api.normalCDF_le_one L x)

theorem normalTail_le_one (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) :
    api.normalTail L x ≤ 1 := by
  dsimp [normalTail]
  exact sub_le_self 1 (api.normalCDF_nonneg L x)

theorem normalTail_at_mean (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) :
    api.normalTail L L.mean = (1 / 2 : ℝ) := by
  rw [normalTail, api.normalCDF_at_mean L]
  norm_num

theorem normalTail_antitone (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) :
    Antitone (api.normalTail L) := by
  intro x y hxy
  dsimp [normalTail, normalCDF]
  exact sub_le_sub_left (api.cdf_mono (L.standardize_mono hxy)) 1

theorem normalTail_strictAnti (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) :
    StrictAnti (api.normalTail L) := by
  intro x y hxy
  dsimp [normalTail, normalCDF]
  exact sub_lt_sub_left
    (api.cdf_strictMono (L.standardize_strictMono hxy)) 1

theorem normalTail_continuous (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) :
    Continuous (api.normalTail L) := by
  unfold normalTail
  exact continuous_const.sub (api.normalCDF_continuous L)

theorem standardTail_gt_iff_lt (api : StandardGaussianCDFAPI)
    {z₁ z₂ : ℝ} :
    1 - api.cdf z₁ > 1 - api.cdf z₂ ↔ z₁ < z₂ := by
  constructor
  · intro htail
    have hcdf : api.cdf z₁ < api.cdf z₂ := by
      linarith
    by_contra hnot
    have hle : z₂ ≤ z₁ := le_of_not_gt hnot
    have hcdf_le : api.cdf z₂ ≤ api.cdf z₁ := api.cdf_mono hle
    linarith
  · intro hz
    have hcdf : api.cdf z₁ < api.cdf z₂ := api.cdf_strictMono hz
    linarith

theorem normalTail_gt_iff_standardize_lt
    (api : StandardGaussianCDFAPI)
    {L₁ L₂ : GaussianScaleLaw} {threshold : ℝ} :
    api.normalTail L₁ threshold > api.normalTail L₂ threshold ↔
      L₁.standardize threshold < L₂.standardize threshold := by
  dsimp [normalTail, normalCDF]
  exact api.standardTail_gt_iff_lt

/-- Cross-threshold version of the upper-tail comparison. -/
theorem normalTail_gt_iff_standardize_lt_of_thresholds
    (api : StandardGaussianCDFAPI)
    {L₁ L₂ : GaussianScaleLaw} {threshold₁ threshold₂ : ℝ} :
    api.normalTail L₁ threshold₁ > api.normalTail L₂ threshold₂ ↔
      L₁.standardize threshold₁ < L₂.standardize threshold₂ := by
  dsimp [normalTail, normalCDF]
  exact api.standardTail_gt_iff_lt

theorem normalCDF_le_of_mean_le_same_scale (api : StandardGaussianCDFAPI)
    {L1 L2 : GaussianScaleLaw} (hscale : L1.scale = L2.scale)
    (hmean : L1.mean ≤ L2.mean) (x : ℝ) :
    api.normalCDF L2 x ≤ api.normalCDF L1 x := by
  exact api.cdf_mono
    (GaussianScaleLaw.standardize_le_standardize_of_mean_le_same_scale
      hscale hmean x)

theorem normalTail_le_of_mean_le_same_scale (api : StandardGaussianCDFAPI)
    {L1 L2 : GaussianScaleLaw} (hscale : L1.scale = L2.scale)
    (hmean : L1.mean ≤ L2.mean) (x : ℝ) :
    api.normalTail L1 x ≤ api.normalTail L2 x := by
  dsimp [normalTail]
  exact sub_le_sub_left
    (api.normalCDF_le_of_mean_le_same_scale hscale hmean x) 1

theorem normalCDF_le_of_same_mean_scale_le_of_mean_le
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale ≤ Llarge.scale)
    {threshold : ℝ} (hthreshold : Lsmall.mean ≤ threshold) :
    api.normalCDF Llarge threshold ≤ api.normalCDF Lsmall threshold := by
  dsimp [normalCDF]
  exact api.cdf_mono
    (GaussianScaleLaw.standardize_le_standardize_of_same_mean_scale_le_of_mean_le
      hmean hscale hthreshold)

theorem normalCDF_lt_of_same_mean_scale_lt_of_mean_lt
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale < Llarge.scale)
    {threshold : ℝ} (hthreshold : Lsmall.mean < threshold) :
    api.normalCDF Llarge threshold < api.normalCDF Lsmall threshold := by
  dsimp [normalCDF]
  exact api.cdf_strictMono
    (GaussianScaleLaw.standardize_lt_standardize_of_same_mean_scale_lt_of_mean_lt
      hmean hscale hthreshold)

theorem normalCDF_le_of_same_mean_scale_le_of_le_mean
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale ≤ Llarge.scale)
    {threshold : ℝ} (hthreshold : threshold ≤ Lsmall.mean) :
    api.normalCDF Lsmall threshold ≤ api.normalCDF Llarge threshold := by
  dsimp [normalCDF]
  exact api.cdf_mono
    (GaussianScaleLaw.standardize_le_standardize_of_same_mean_scale_le_of_le_mean
      hmean hscale hthreshold)

theorem normalCDF_lt_of_same_mean_scale_lt_of_lt_mean
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale < Llarge.scale)
    {threshold : ℝ} (hthreshold : threshold < Lsmall.mean) :
    api.normalCDF Lsmall threshold < api.normalCDF Llarge threshold := by
  dsimp [normalCDF]
  exact api.cdf_strictMono
    (GaussianScaleLaw.standardize_lt_standardize_of_same_mean_scale_lt_of_lt_mean
      hmean hscale hthreshold)

theorem normalCDF_same_mean_scale_le_crosses_at_mean
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale ≤ Llarge.scale) :
    (∀ {threshold : ℝ}, Lsmall.mean ≤ threshold →
      api.normalCDF Llarge threshold ≤ api.normalCDF Lsmall threshold) ∧
    (∀ {threshold : ℝ}, threshold ≤ Lsmall.mean →
      api.normalCDF Lsmall threshold ≤ api.normalCDF Llarge threshold) :=
  ⟨fun hthreshold =>
      api.normalCDF_le_of_same_mean_scale_le_of_mean_le
        hmean hscale hthreshold,
    fun hthreshold =>
      api.normalCDF_le_of_same_mean_scale_le_of_le_mean
        hmean hscale hthreshold⟩

theorem normalCDF_same_mean_scale_lt_strictly_crosses_at_mean
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale < Llarge.scale) :
    (∀ {threshold : ℝ}, Lsmall.mean < threshold →
      api.normalCDF Llarge threshold < api.normalCDF Lsmall threshold) ∧
    (∀ {threshold : ℝ}, threshold < Lsmall.mean →
      api.normalCDF Lsmall threshold < api.normalCDF Llarge threshold) :=
  ⟨fun hthreshold =>
      api.normalCDF_lt_of_same_mean_scale_lt_of_mean_lt
        hmean hscale hthreshold,
    fun hthreshold =>
      api.normalCDF_lt_of_same_mean_scale_lt_of_lt_mean
        hmean hscale hthreshold⟩

theorem normalCDF_large_scale_lt_small_scale_iff_mean_lt
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale < Llarge.scale)
    {threshold : ℝ} :
    api.normalCDF Llarge threshold < api.normalCDF Lsmall threshold ↔
      Lsmall.mean < threshold := by
  constructor
  · intro hcdf
    by_contra hnot
    have hthreshold : threshold ≤ Lsmall.mean := le_of_not_gt hnot
    have hle :
        api.normalCDF Lsmall threshold ≤
          api.normalCDF Llarge threshold :=
      api.normalCDF_le_of_same_mean_scale_le_of_le_mean
        hmean hscale.le hthreshold
    linarith
  · intro hthreshold
    exact api.normalCDF_lt_of_same_mean_scale_lt_of_mean_lt
      hmean hscale hthreshold

theorem normalCDF_small_scale_lt_large_scale_iff_lt_mean
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale < Llarge.scale)
    {threshold : ℝ} :
    api.normalCDF Lsmall threshold < api.normalCDF Llarge threshold ↔
      threshold < Lsmall.mean := by
  constructor
  · intro hcdf
    by_contra hnot
    have hthreshold : Lsmall.mean ≤ threshold := le_of_not_gt hnot
    have hle :
        api.normalCDF Llarge threshold ≤
          api.normalCDF Lsmall threshold :=
      api.normalCDF_le_of_same_mean_scale_le_of_mean_le
        hmean hscale.le hthreshold
    linarith
  · intro hthreshold
    exact api.normalCDF_lt_of_same_mean_scale_lt_of_lt_mean
      hmean hscale hthreshold

theorem normalTail_le_of_same_mean_scale_le_of_mean_le
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale ≤ Llarge.scale)
    {threshold : ℝ} (hthreshold : Lsmall.mean ≤ threshold) :
    api.normalTail Lsmall threshold ≤ api.normalTail Llarge threshold := by
  dsimp [normalTail, normalCDF]
  exact sub_le_sub_left
    (api.cdf_mono
      (GaussianScaleLaw.standardize_le_standardize_of_same_mean_scale_le_of_mean_le
        hmean hscale hthreshold)) 1

theorem normalTail_lt_of_same_mean_scale_lt_of_mean_lt
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale < Llarge.scale)
    {threshold : ℝ} (hthreshold : Lsmall.mean < threshold) :
    api.normalTail Lsmall threshold < api.normalTail Llarge threshold := by
  dsimp [normalTail, normalCDF]
  exact sub_lt_sub_left
    (api.cdf_strictMono
      (GaussianScaleLaw.standardize_lt_standardize_of_same_mean_scale_lt_of_mean_lt
        hmean hscale hthreshold)) 1

/-- Pass probability above a threshold for a Gaussian location-scale law. -/
def thresholdPassProb (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (threshold : ℝ) : ℝ :=
  api.normalTail L threshold

theorem thresholdPassProb_at_mean
    (api : StandardGaussianCDFAPI) (L : GaussianScaleLaw) :
    api.thresholdPassProb L L.mean = (1 / 2 : ℝ) :=
  api.normalTail_at_mean L

theorem thresholdPassProb_antitone_threshold
    (api : StandardGaussianCDFAPI) (L : GaussianScaleLaw) :
    Antitone (api.thresholdPassProb L) := by
  exact api.normalTail_antitone L

theorem thresholdPassProb_strictAnti_threshold
    (api : StandardGaussianCDFAPI) (L : GaussianScaleLaw) :
    StrictAnti (api.thresholdPassProb L) := by
  exact api.normalTail_strictAnti L

theorem thresholdPassProb_ge_half_of_threshold_le_mean
    (api : StandardGaussianCDFAPI) {L : GaussianScaleLaw} {threshold : ℝ}
    (hthreshold : threshold ≤ L.mean) :
    (1 / 2 : ℝ) ≤ api.thresholdPassProb L threshold := by
  have htail := api.thresholdPassProb_antitone_threshold L hthreshold
  simpa [api.thresholdPassProb_at_mean L] using htail

theorem thresholdPassProb_gt_half_of_threshold_lt_mean
    (api : StandardGaussianCDFAPI) {L : GaussianScaleLaw} {threshold : ℝ}
    (hthreshold : threshold < L.mean) :
    (1 / 2 : ℝ) < api.thresholdPassProb L threshold := by
  have htail := api.thresholdPassProb_strictAnti_threshold L hthreshold
  simpa [api.thresholdPassProb_at_mean L] using htail

theorem thresholdPassProb_continuous
    (api : StandardGaussianCDFAPI) (L : GaussianScaleLaw) :
    Continuous (api.thresholdPassProb L) := by
  exact api.normalTail_continuous L

theorem thresholdPassProb_gt_iff_standardize_lt
    (api : StandardGaussianCDFAPI)
    {L₁ L₂ : GaussianScaleLaw} {threshold : ℝ} :
    api.thresholdPassProb L₁ threshold >
        api.thresholdPassProb L₂ threshold ↔
      L₁.standardize threshold < L₂.standardize threshold :=
  api.normalTail_gt_iff_standardize_lt

/--
The difference of two upper-tail pass probabilities is positive exactly when
the first law has the lower standardized threshold.
-/
theorem thresholdPassProb_sub_pos_iff_standardize_lt
    (api : StandardGaussianCDFAPI)
    {L₁ L₂ : GaussianScaleLaw} {threshold : ℝ} :
    0 < api.thresholdPassProb L₁ threshold -
        api.thresholdPassProb L₂ threshold ↔
      L₁.standardize threshold < L₂.standardize threshold := by
  rw [sub_pos]
  exact api.thresholdPassProb_gt_iff_standardize_lt

theorem thresholdPassProb_gt_iff_standardize_lt_of_thresholds
    (api : StandardGaussianCDFAPI)
    {L₁ L₂ : GaussianScaleLaw} {threshold₁ threshold₂ : ℝ} :
    api.thresholdPassProb L₁ threshold₁ >
        api.thresholdPassProb L₂ threshold₂ ↔
      L₁.standardize threshold₁ < L₂.standardize threshold₂ :=
  api.normalTail_gt_iff_standardize_lt_of_thresholds

/--
Two possibly different thresholds: the difference of upper-tail pass
probabilities is positive exactly when the first standardized threshold is
lower.
-/
theorem thresholdPassProb_sub_pos_iff_standardize_lt_of_thresholds
    (api : StandardGaussianCDFAPI)
    {L₁ L₂ : GaussianScaleLaw} {threshold₁ threshold₂ : ℝ} :
    0 < api.thresholdPassProb L₁ threshold₁ -
        api.thresholdPassProb L₂ threshold₂ ↔
      L₁.standardize threshold₁ < L₂.standardize threshold₂ := by
  rw [sub_pos]
  exact api.thresholdPassProb_gt_iff_standardize_lt_of_thresholds

theorem thresholdPassProb_le_of_mean_le_same_scale
    (api : StandardGaussianCDFAPI)
    {L1 L2 : GaussianScaleLaw} (hscale : L1.scale = L2.scale)
    (hmean : L1.mean ≤ L2.mean) (threshold : ℝ) :
    api.thresholdPassProb L1 threshold ≤ api.thresholdPassProb L2 threshold := by
  exact api.normalTail_le_of_mean_le_same_scale hscale hmean threshold

theorem thresholdPassProb_le_of_same_mean_scale_le_of_mean_le
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale ≤ Llarge.scale)
    {threshold : ℝ} (hthreshold : Lsmall.mean ≤ threshold) :
    api.thresholdPassProb Lsmall threshold ≤
      api.thresholdPassProb Llarge threshold := by
  exact api.normalTail_le_of_same_mean_scale_le_of_mean_le
    hmean hscale hthreshold

theorem thresholdPassProb_lt_of_same_mean_scale_lt_of_mean_lt
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale < Llarge.scale)
    {threshold : ℝ} (hthreshold : Lsmall.mean < threshold) :
    api.thresholdPassProb Lsmall threshold <
      api.thresholdPassProb Llarge threshold := by
  exact api.normalTail_lt_of_same_mean_scale_lt_of_mean_lt
    hmean hscale hthreshold

theorem normalCDF_affineImage_pos (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (threshold : ℝ) :
    api.normalCDF (L.affineImage a b hb) threshold =
      api.normalCDF L ((threshold - a) / b) := by
  rw [normalCDF, normalCDF,
    GaussianScaleLaw.standardize_affineImage_threshold]

theorem normalTail_affineImage_pos (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (threshold : ℝ) :
    api.normalTail (L.affineImage a b hb) threshold =
      api.normalTail L ((threshold - a) / b) := by
  rw [normalTail, normalTail, api.normalCDF_affineImage_pos L a hb threshold]

theorem thresholdPassProb_affineImage_pos (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (threshold : ℝ) :
    api.thresholdPassProb (L.affineImage a b hb) threshold =
      api.thresholdPassProb L ((threshold - a) / b) := by
  exact api.normalTail_affineImage_pos L a hb threshold

section Mixture

variable {γ : Type*} [Fintype γ]

/-- Weighted admission mass above a common threshold for finitely many Gaussian groups. -/
def mixtureTailMass (api : StandardGaussianCDFAPI)
    (weight : γ → ℝ) (law : γ → GaussianScaleLaw)
    (threshold : ℝ) : ℝ :=
  ∑ g : γ, weight g * api.thresholdPassProb (law g) threshold

theorem mixtureTailMass_nonneg (api : StandardGaussianCDFAPI)
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw}
    (hweight : ∀ g, 0 ≤ weight g) (threshold : ℝ) :
    0 ≤ api.mixtureTailMass weight law threshold := by
  dsimp [mixtureTailMass]
  exact Finset.sum_nonneg (by
    intro g _
    exact mul_nonneg (hweight g)
      (api.normalTail_nonneg (law g) threshold))

theorem mixtureTailMass_le_sum_weights (api : StandardGaussianCDFAPI)
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw}
    (hweight : ∀ g, 0 ≤ weight g) (threshold : ℝ) :
    api.mixtureTailMass weight law threshold ≤ ∑ g : γ, weight g := by
  dsimp [mixtureTailMass]
  exact Finset.sum_le_sum (by
    intro g _
    simpa using
      mul_le_mul_of_nonneg_left
        (api.normalTail_le_one (law g) threshold)
        (hweight g))

theorem mixtureTailMass_antitone_threshold (api : StandardGaussianCDFAPI)
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw}
    (hweight : ∀ g, 0 ≤ weight g) :
    Antitone (api.mixtureTailMass weight law) := by
  intro x y hxy
  dsimp [mixtureTailMass]
  exact Finset.sum_le_sum (by
    intro g _
    exact mul_le_mul_of_nonneg_left
      (api.thresholdPassProb_antitone_threshold (law g) hxy)
      (hweight g))

theorem mixtureTailMass_strictAnti_threshold (api : StandardGaussianCDFAPI)
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw}
    (hweight : ∀ g, 0 ≤ weight g) (hpos : ∃ g, 0 < weight g) :
    StrictAnti (api.mixtureTailMass weight law) := by
  intro x y hxy
  dsimp [mixtureTailMass]
  exact Finset.sum_lt_sum
    (by
      intro g _hg
      exact mul_le_mul_of_nonneg_left
        (api.thresholdPassProb_antitone_threshold (law g) hxy.le)
        (hweight g))
    (by
      rcases hpos with ⟨g, hg⟩
      refine ⟨g, Finset.mem_univ g, ?_⟩
      exact mul_lt_mul_of_pos_left
        (api.thresholdPassProb_strictAnti_threshold (law g) hxy) hg)

/--
Certificate that a common Gaussian admission threshold realizes a target
capacity for a finite mixture of group score laws.
-/
structure MixtureThresholdCertificate
    (api : StandardGaussianCDFAPI) (γ : Type*) [Fintype γ] where
  weight : γ → ℝ
  law : γ → GaussianScaleLaw
  threshold : ℝ
  capacity : ℝ
  weight_nonneg : ∀ g, 0 ≤ weight g
  capacity_eq : api.mixtureTailMass weight law threshold = capacity

namespace MixtureThresholdCertificate

theorem capacity_nonneg {api : StandardGaussianCDFAPI}
    {γ : Type*} [Fintype γ]
    (C : MixtureThresholdCertificate api γ) :
    0 ≤ C.capacity := by
  rw [← C.capacity_eq]
  exact api.mixtureTailMass_nonneg C.weight_nonneg C.threshold

theorem capacity_le_sum_weights {api : StandardGaussianCDFAPI}
    {γ : Type*} [Fintype γ]
    (C : MixtureThresholdCertificate api γ) :
    C.capacity ≤ ∑ g : γ, C.weight g := by
  rw [← C.capacity_eq]
  exact api.mixtureTailMass_le_sum_weights C.weight_nonneg C.threshold

end MixtureThresholdCertificate

end Mixture

theorem normalDensity_nonneg (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) :
    0 ≤ api.normalDensity L x := by
  exact div_nonneg (api.density_nonneg (L.standardize x)) L.scale_pos.le

/-- Multiplying a location-scale Gaussian density by its scale recovers the
standard-normal density at the standardized point. -/
theorem scale_mul_normalDensity (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) :
    L.scale * api.normalDensity L x = api.density (L.standardize x) := by
  rw [normalDensity]
  field_simp [L.scale_pos.ne']

end StandardGaussianCDFAPI

/--
Certificate-level interface for the conditional mean below a threshold for a
location-scale Gaussian.

The concrete formula can be instantiated from a normal CDF/density library.
Many admissions/testing proofs only need the order fact that a nondegenerate
Gaussian conditional mean below a finite threshold lies strictly below that
threshold, so this lightweight certificate keeps those paper proofs independent
of the analytic lower-tail formula.
-/
structure GaussianLowerTailMeanCertificate where
  lowerTailMean : GaussianScaleLaw → ℝ → ℝ
  lowerTailMean_lt_threshold :
    ∀ (L : GaussianScaleLaw) (threshold : ℝ),
      lowerTailMean L threshold < threshold

namespace GaussianLowerTailMeanCertificate

theorem lowerTailMean_lt (C : GaussianLowerTailMeanCertificate)
    (L : GaussianScaleLaw) (threshold : ℝ) :
    C.lowerTailMean L threshold < threshold :=
  C.lowerTailMean_lt_threshold L threshold

end GaussianLowerTailMeanCertificate

namespace GaussianVarianceLaw

/-- Nondegenerate affine image of a Gaussian variance law. -/
def affineImage (L : GaussianVarianceLaw) (a b : ℝ) (hb : b ≠ 0) :
    GaussianVarianceLaw where
  mean := a + b * L.mean
  variance := b ^ 2 * L.variance
  variance_pos := by
    exact mul_pos (sq_pos_of_ne_zero hb) L.variance_pos

@[simp] theorem affineImage_mean (L : GaussianVarianceLaw)
    (a b : ℝ) (hb : b ≠ 0) :
    (L.affineImage a b hb).mean = a + b * L.mean := rfl

@[simp] theorem affineImage_variance (L : GaussianVarianceLaw)
    (a b : ℝ) (hb : b ≠ 0) :
    (L.affineImage a b hb).variance = b ^ 2 * L.variance := rfl

theorem eq_of_mean_eq_variance {L₁ L₂ : GaussianVarianceLaw}
    (hmean : L₁.mean = L₂.mean) (hvar : L₁.variance = L₂.variance) :
    L₁ = L₂ := by
  cases L₁
  cases L₂
  simp at hmean hvar
  subst hmean
  subst hvar
  congr

theorem ne_of_mean_ne {L₁ L₂ : GaussianVarianceLaw}
    (h : L₁.mean ≠ L₂.mean) : L₁ ≠ L₂ := by
  intro hEq
  exact h (congrArg GaussianVarianceLaw.mean hEq)

theorem ne_of_mean_lt {L₁ L₂ : GaussianVarianceLaw}
    (h : L₁.mean < L₂.mean) : L₁ ≠ L₂ :=
  ne_of_mean_ne (ne_of_lt h)

theorem ne_of_variance_ne {L₁ L₂ : GaussianVarianceLaw}
    (h : L₁.variance ≠ L₂.variance) : L₁ ≠ L₂ := by
  intro hEq
  exact h (congrArg GaussianVarianceLaw.variance hEq)

theorem ne_of_variance_lt {L₁ L₂ : GaussianVarianceLaw}
    (h : L₁.variance < L₂.variance) : L₁ ≠ L₂ :=
  ne_of_variance_ne (ne_of_lt h)

end GaussianVarianceLaw

/--
Conjugate Gaussian model with one noisy signal:

`θ ~ N(priorMean, priorVar)` and `x = θ + noise`, `noiseVar > 0`.
-/
structure GaussianPriorSignal where
  priorMean : ℝ
  priorVar : ℝ
  noiseVar : ℝ
  priorVar_pos : 0 < priorVar
  noiseVar_pos : 0 < noiseVar

namespace GaussianPriorSignal

def priorPrecision (M : GaussianPriorSignal) : ℝ :=
  M.priorVar⁻¹

def noisePrecision (M : GaussianPriorSignal) : ℝ :=
  M.noiseVar⁻¹

def posteriorPrecision (M : GaussianPriorSignal) : ℝ :=
  M.priorPrecision + M.noisePrecision

def posteriorVariance (M : GaussianPriorSignal) : ℝ :=
  M.posteriorPrecision⁻¹

def priorWeight (M : GaussianPriorSignal) : ℝ :=
  M.noiseVar / (M.priorVar + M.noiseVar)

def signalWeight (M : GaussianPriorSignal) : ℝ :=
  M.priorVar / (M.priorVar + M.noiseVar)

/-- Posterior mean after observing signal value `x`. -/
def posteriorMean (M : GaussianPriorSignal) (x : ℝ) : ℝ :=
  M.posteriorVariance *
    (M.priorPrecision * M.priorMean + M.noisePrecision * x)

/-- Marginal variance of the posterior mean as a random variable. -/
def posteriorMeanVariance (M : GaussianPriorSignal) : ℝ :=
  M.priorVar - M.posteriorVariance

/-- Marginal variance of the observed signal. -/
def signalVariance (M : GaussianPriorSignal) : ℝ :=
  M.priorVar + M.noiseVar

/-- Signal value whose posterior mean is exactly `threshold`. -/
def posteriorMeanSignalCutoff (M : GaussianPriorSignal)
    (threshold : ℝ) : ℝ :=
  M.priorMean + (threshold - M.priorMean) / M.signalWeight

theorem priorPrecision_pos (M : GaussianPriorSignal) :
    0 < M.priorPrecision := by
  exact inv_pos.mpr M.priorVar_pos

theorem noisePrecision_pos (M : GaussianPriorSignal) :
    0 < M.noisePrecision := by
  exact inv_pos.mpr M.noiseVar_pos

theorem posteriorPrecision_pos (M : GaussianPriorSignal) :
    0 < M.posteriorPrecision := by
  exact add_pos M.priorPrecision_pos M.noisePrecision_pos

theorem posteriorVariance_pos (M : GaussianPriorSignal) :
    0 < M.posteriorVariance := by
  exact inv_pos.mpr M.posteriorPrecision_pos

theorem signalVariance_pos (M : GaussianPriorSignal) :
    0 < M.signalVariance := by
  exact add_pos M.priorVar_pos M.noiseVar_pos

theorem priorWeight_pos (M : GaussianPriorSignal) :
    0 < M.priorWeight := by
  exact div_pos M.noiseVar_pos (add_pos M.priorVar_pos M.noiseVar_pos)

theorem signalWeight_pos (M : GaussianPriorSignal) :
    0 < M.signalWeight := by
  exact div_pos M.priorVar_pos (add_pos M.priorVar_pos M.noiseVar_pos)

theorem priorWeight_nonneg (M : GaussianPriorSignal) :
    0 ≤ M.priorWeight :=
  M.priorWeight_pos.le

theorem signalWeight_nonneg (M : GaussianPriorSignal) :
    0 ≤ M.signalWeight :=
  M.signalWeight_pos.le

theorem priorWeight_lt_one (M : GaussianPriorSignal) :
    M.priorWeight < 1 := by
  exact (div_lt_one (add_pos M.priorVar_pos M.noiseVar_pos)).mpr
    (lt_add_of_pos_left M.noiseVar M.priorVar_pos)

theorem signalWeight_lt_one (M : GaussianPriorSignal) :
    M.signalWeight < 1 := by
  exact (div_lt_one (add_pos M.priorVar_pos M.noiseVar_pos)).mpr
    (lt_add_of_pos_right M.priorVar M.noiseVar_pos)

theorem priorWeight_add_signalWeight (M : GaussianPriorSignal) :
    M.priorWeight + M.signalWeight = 1 := by
  have hsum : M.priorVar + M.noiseVar ≠ 0 :=
    ne_of_gt (add_pos M.priorVar_pos M.noiseVar_pos)
  rw [priorWeight, signalWeight]
  field_simp [hsum]
  ring_nf

theorem posteriorVariance_eq_mul_div (M : GaussianPriorSignal) :
    M.posteriorVariance =
      M.priorVar * M.noiseVar / (M.priorVar + M.noiseVar) := by
  have hp : M.priorVar ≠ 0 := ne_of_gt M.priorVar_pos
  have hn : M.noiseVar ≠ 0 := ne_of_gt M.noiseVar_pos
  have hsum : M.priorVar + M.noiseVar ≠ 0 :=
    ne_of_gt (add_pos M.priorVar_pos M.noiseVar_pos)
  rw [posteriorVariance, posteriorPrecision, priorPrecision, noisePrecision]
  field_simp [hp, hn, hsum]
  rw [add_comm M.noiseVar M.priorVar]
  exact div_self hsum

theorem posteriorVariance_lt_priorVar (M : GaussianPriorSignal) :
    M.posteriorVariance < M.priorVar := by
  have hlt : M.priorPrecision < M.posteriorPrecision := by
    dsimp [posteriorPrecision]
    exact lt_add_of_pos_right M.priorPrecision M.noisePrecision_pos
  have h :=
    one_div_lt_one_div_of_lt M.priorPrecision_pos hlt
  simpa [posteriorVariance, priorPrecision, one_div] using h

theorem posteriorVariance_lt_noiseVar (M : GaussianPriorSignal) :
    M.posteriorVariance < M.noiseVar := by
  have hlt : M.noisePrecision < M.posteriorPrecision := by
    dsimp [posteriorPrecision]
    exact lt_add_of_pos_left M.noisePrecision M.priorPrecision_pos
  have h :=
    one_div_lt_one_div_of_lt M.noisePrecision_pos hlt
  simpa [posteriorVariance, noisePrecision, posteriorPrecision, add_comm, one_div] using h

theorem posteriorMean_eq_weightedAverage (M : GaussianPriorSignal) (x : ℝ) :
    M.posteriorMean x =
      M.priorWeight * M.priorMean + M.signalWeight * x := by
  have hp : M.priorVar ≠ 0 := ne_of_gt M.priorVar_pos
  have hn : M.noiseVar ≠ 0 := ne_of_gt M.noiseVar_pos
  have hsum : M.priorVar + M.noiseVar ≠ 0 :=
    ne_of_gt (add_pos M.priorVar_pos M.noiseVar_pos)
  rw [posteriorMean, M.posteriorVariance_eq_mul_div, priorPrecision,
    noisePrecision, priorWeight, signalWeight]
  field_simp [hp, hn, hsum]

theorem posteriorMean_eq_priorMean_add_signalWeight_mul
    (M : GaussianPriorSignal) (x : ℝ) :
    M.posteriorMean x =
      M.priorMean + M.signalWeight * (x - M.priorMean) := by
  rw [M.posteriorMean_eq_weightedAverage x]
  have h : M.priorWeight = 1 - M.signalWeight := by
    linarith [M.priorWeight_add_signalWeight]
  rw [h]
  ring

theorem posteriorMean_mono (M : GaussianPriorSignal) :
    Monotone M.posteriorMean := by
  intro x y hxy
  rw [M.posteriorMean_eq_priorMean_add_signalWeight_mul x,
    M.posteriorMean_eq_priorMean_add_signalWeight_mul y]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hxy M.priorMean)
        M.signalWeight_nonneg) M.priorMean

theorem posteriorMean_posteriorMeanSignalCutoff
    (M : GaussianPriorSignal) (threshold : ℝ) :
    M.posteriorMean (M.posteriorMeanSignalCutoff threshold) =
      threshold := by
  rw [M.posteriorMean_eq_priorMean_add_signalWeight_mul,
    posteriorMeanSignalCutoff]
  calc
    M.priorMean +
        M.signalWeight *
          (M.priorMean +
              (threshold - M.priorMean) / M.signalWeight -
            M.priorMean) =
        M.priorMean +
          M.signalWeight *
            ((threshold - M.priorMean) / M.signalWeight) := by
      congr
      ring
    _ = M.priorMean + (threshold - M.priorMean) := by
      rw [mul_div_cancel₀ _ (ne_of_gt M.signalWeight_pos)]
    _ = threshold := by
      ring

theorem posteriorMean_le_threshold_iff
    (M : GaussianPriorSignal) {x threshold : ℝ} :
    M.posteriorMean x ≤ threshold ↔
      x ≤ M.posteriorMeanSignalCutoff threshold := by
  rw [M.posteriorMean_eq_priorMean_add_signalWeight_mul,
    posteriorMeanSignalCutoff]
  constructor
  · intro h
    have hsub :
        M.signalWeight * (x - M.priorMean) ≤
          threshold - M.priorMean := by
      linarith
    have hdiv :
        x - M.priorMean ≤
          (threshold - M.priorMean) / M.signalWeight := by
      rw [le_div_iff₀ M.signalWeight_pos]
      simpa [mul_comm] using hsub
    linarith
  · intro h
    have hsub :
        x - M.priorMean ≤
          (threshold - M.priorMean) / M.signalWeight := by
      linarith
    have hmul :
        M.signalWeight * (x - M.priorMean) ≤
          threshold - M.priorMean := by
      have := (le_div_iff₀ M.signalWeight_pos).mp hsub
      simpa [mul_comm] using this
    linarith

theorem threshold_le_posteriorMean_iff
    (M : GaussianPriorSignal) {x threshold : ℝ} :
    threshold ≤ M.posteriorMean x ↔
      M.posteriorMeanSignalCutoff threshold ≤ x := by
  rw [M.posteriorMean_eq_priorMean_add_signalWeight_mul,
    posteriorMeanSignalCutoff]
  constructor
  · intro h
    have hsub :
        threshold - M.priorMean ≤
          M.signalWeight * (x - M.priorMean) := by
      linarith
    have hdiv :
        (threshold - M.priorMean) / M.signalWeight ≤
          x - M.priorMean := by
      rw [div_le_iff₀ M.signalWeight_pos]
      simpa [mul_comm] using hsub
    linarith
  · intro h
    have hsub :
        (threshold - M.priorMean) / M.signalWeight ≤
          x - M.priorMean := by
      linarith
    have hmul :
        threshold - M.priorMean ≤
          M.signalWeight * (x - M.priorMean) := by
      have := (div_le_iff₀ M.signalWeight_pos).mp hsub
      simpa [mul_comm] using this
    linarith

theorem posteriorMeanVariance_pos (M : GaussianPriorSignal) :
    0 < M.posteriorMeanVariance := by
  dsimp [posteriorMeanVariance]
  exact sub_pos.mpr M.posteriorVariance_lt_priorVar

theorem posteriorMeanVariance_eq_priorVar_sq_div
    (M : GaussianPriorSignal) :
    M.posteriorMeanVariance =
      M.priorVar ^ 2 / (M.priorVar + M.noiseVar) := by
  rw [posteriorMeanVariance, posteriorVariance_eq_mul_div]
  have hsum : M.priorVar + M.noiseVar ≠ 0 :=
    ne_of_gt (add_pos M.priorVar_pos M.noiseVar_pos)
  field_simp [hsum]
  ring_nf

/-- Law of the raw signal as a Gaussian variance law. -/
def signalLaw (M : GaussianPriorSignal) : GaussianVarianceLaw where
  mean := M.priorMean
  variance := M.signalVariance
  variance_pos := M.signalVariance_pos

theorem posteriorMeanVariance_eq_signalWeight_sq_mul_signalVariance
    (M : GaussianPriorSignal) :
    M.posteriorMeanVariance =
      M.signalWeight ^ 2 * M.signalVariance := by
  rw [M.posteriorMeanVariance_eq_priorVar_sq_div, signalWeight,
    signalVariance]
  have hsum : M.priorVar + M.noiseVar ≠ 0 :=
    ne_of_gt (add_pos M.priorVar_pos M.noiseVar_pos)
  field_simp [hsum]

/-- Law of the posterior mean as a Gaussian variance law, using the standard conjugate formula. -/
def posteriorMeanLaw (M : GaussianPriorSignal) : GaussianVarianceLaw where
  mean := M.priorMean
  variance := M.posteriorMeanVariance
  variance_pos := M.posteriorMeanVariance_pos

/--
Location-scale law of the posterior mean obtained by applying the affine
posterior-mean map to a location-scale signal law.
-/
def posteriorMeanScaleLaw (M : GaussianPriorSignal)
    (signalLaw : GaussianScaleLaw) : GaussianScaleLaw :=
  signalLaw.affineImage (M.priorWeight * M.priorMean)
    M.signalWeight M.signalWeight_pos

theorem posteriorMeanScaleLaw_mean_of_signal_mean_eq
    (M : GaussianPriorSignal) {signalLaw : GaussianScaleLaw}
    (hmean : signalLaw.mean = M.priorMean) :
    (M.posteriorMeanScaleLaw signalLaw).mean = M.priorMean := by
  rw [posteriorMeanScaleLaw, GaussianScaleLaw.affineImage_mean, hmean]
  calc
    M.priorWeight * M.priorMean + M.signalWeight * M.priorMean =
        (M.priorWeight + M.signalWeight) * M.priorMean := by
      ring
    _ = M.priorMean := by
      rw [M.priorWeight_add_signalWeight]
      ring

theorem posteriorMeanSignalCutoff_eq_affineCutoff
    (M : GaussianPriorSignal) (threshold : ℝ) :
    M.posteriorMeanSignalCutoff threshold =
      (threshold - M.priorWeight * M.priorMean) / M.signalWeight := by
  rw [posteriorMeanSignalCutoff]
  have h : M.priorWeight = 1 - M.signalWeight := by
    linarith [M.priorWeight_add_signalWeight]
  rw [h]
  field_simp [ne_of_gt M.signalWeight_pos]
  ring

theorem thresholdPassProb_posteriorMeanScaleLaw
    (api : StandardGaussianCDFAPI) (M : GaussianPriorSignal)
    (signalLaw : GaussianScaleLaw) (threshold : ℝ) :
    api.thresholdPassProb (M.posteriorMeanScaleLaw signalLaw) threshold =
      api.thresholdPassProb signalLaw
        (M.posteriorMeanSignalCutoff threshold) := by
  rw [posteriorMeanScaleLaw,
    api.thresholdPassProb_affineImage_pos signalLaw
      (M.priorWeight * M.priorMean) M.signalWeight_pos threshold,
    M.posteriorMeanSignalCutoff_eq_affineCutoff threshold]

/-- Posterior mean from a raw signal whose noise has known mean. -/
def posteriorMeanOfSignalWithNoiseMean (M : GaussianPriorSignal)
    (noiseMean signal : ℝ) : ℝ :=
  M.posteriorMean (signal - noiseMean)

/-- Raw-signal cutoff corresponding to a posterior-mean threshold. -/
def posteriorMeanRawSignalCutoff (M : GaussianPriorSignal)
    (noiseMean threshold : ℝ) : ℝ :=
  noiseMean + M.posteriorMeanSignalCutoff threshold

theorem posteriorMeanOfSignalWithNoiseMean_eq
    (M : GaussianPriorSignal) (noiseMean signal : ℝ) :
    M.posteriorMeanOfSignalWithNoiseMean noiseMean signal =
      M.priorMean +
        M.signalWeight * (signal - noiseMean - M.priorMean) := by
  rw [posteriorMeanOfSignalWithNoiseMean,
    M.posteriorMean_eq_priorMean_add_signalWeight_mul]

theorem posteriorMeanOfSignalWithNoiseMean_le_threshold_iff
    (M : GaussianPriorSignal) {noiseMean signal threshold : ℝ} :
    M.posteriorMeanOfSignalWithNoiseMean noiseMean signal ≤ threshold ↔
      signal ≤ M.posteriorMeanRawSignalCutoff noiseMean threshold := by
  rw [posteriorMeanOfSignalWithNoiseMean,
    M.posteriorMean_le_threshold_iff,
    posteriorMeanRawSignalCutoff]
  constructor <;> intro h <;> linarith

theorem threshold_le_posteriorMeanOfSignalWithNoiseMean_iff
    (M : GaussianPriorSignal) {noiseMean signal threshold : ℝ} :
    threshold ≤ M.posteriorMeanOfSignalWithNoiseMean noiseMean signal ↔
      M.posteriorMeanRawSignalCutoff noiseMean threshold ≤ signal := by
  rw [posteriorMeanOfSignalWithNoiseMean,
    M.threshold_le_posteriorMean_iff,
    posteriorMeanRawSignalCutoff]
  constructor <;> intro h <;> linarith

/--
Location-scale law of the posterior mean obtained from a raw signal with
nonzero noise mean.
-/
def posteriorMeanRawSignalScaleLaw (M : GaussianPriorSignal)
    (noiseMean : ℝ) (rawSignalLaw : GaussianScaleLaw) :
    GaussianScaleLaw :=
  rawSignalLaw.affineImage
    (M.priorWeight * M.priorMean - M.signalWeight * noiseMean)
    M.signalWeight M.signalWeight_pos

theorem posteriorMeanRawSignalScaleLaw_mean_of_signal_mean_eq
    (M : GaussianPriorSignal) {noiseMean : ℝ}
    {rawSignalLaw : GaussianScaleLaw}
    (hmean : rawSignalLaw.mean = M.priorMean + noiseMean) :
    (M.posteriorMeanRawSignalScaleLaw noiseMean rawSignalLaw).mean =
      M.priorMean := by
  rw [posteriorMeanRawSignalScaleLaw, GaussianScaleLaw.affineImage_mean,
    hmean]
  calc
    M.priorWeight * M.priorMean - M.signalWeight * noiseMean +
        M.signalWeight * (M.priorMean + noiseMean) =
        (M.priorWeight + M.signalWeight) * M.priorMean := by
      ring
    _ = M.priorMean := by
      rw [M.priorWeight_add_signalWeight]
      ring

theorem posteriorMeanRawSignalCutoff_eq_affineCutoff
    (M : GaussianPriorSignal) (noiseMean threshold : ℝ) :
    M.posteriorMeanRawSignalCutoff noiseMean threshold =
      (threshold -
          (M.priorWeight * M.priorMean -
            M.signalWeight * noiseMean)) / M.signalWeight := by
  rw [posteriorMeanRawSignalCutoff,
    M.posteriorMeanSignalCutoff_eq_affineCutoff threshold]
  field_simp [ne_of_gt M.signalWeight_pos]
  ring

theorem thresholdPassProb_posteriorMeanRawSignalScaleLaw
    (api : StandardGaussianCDFAPI) (M : GaussianPriorSignal)
    (noiseMean : ℝ) (rawSignalLaw : GaussianScaleLaw)
    (threshold : ℝ) :
    api.thresholdPassProb
        (M.posteriorMeanRawSignalScaleLaw noiseMean rawSignalLaw)
        threshold =
      api.thresholdPassProb rawSignalLaw
        (M.posteriorMeanRawSignalCutoff noiseMean threshold) := by
  rw [posteriorMeanRawSignalScaleLaw,
    api.thresholdPassProb_affineImage_pos rawSignalLaw
      (M.priorWeight * M.priorMean - M.signalWeight * noiseMean)
      M.signalWeight_pos threshold,
    M.posteriorMeanRawSignalCutoff_eq_affineCutoff noiseMean threshold]

end GaussianPriorSignal

/-- Conjugate Gaussian model with a finite family of noisy signals. -/
structure GaussianSignalFamily (ι : Type*) [Fintype ι] where
  priorMean : ℝ
  priorVar : ℝ
  noiseVar : ι → ℝ
  priorVar_pos : 0 < priorVar
  noiseVar_pos : ∀ i, 0 < noiseVar i

namespace GaussianSignalFamily

variable {ι : Type*} [Fintype ι]

def priorPrecision (M : GaussianSignalFamily ι) : ℝ :=
  M.priorVar⁻¹

def signalPrecision (M : GaussianSignalFamily ι) (i : ι) : ℝ :=
  (M.noiseVar i)⁻¹

def signalPrecisionSum (M : GaussianSignalFamily ι) : ℝ :=
  ∑ i : ι, M.signalPrecision i

def posteriorPrecision (M : GaussianSignalFamily ι) : ℝ :=
  M.priorPrecision + ∑ i : ι, M.signalPrecision i

def posteriorVariance (M : GaussianSignalFamily ι) : ℝ :=
  M.posteriorPrecision⁻¹

def priorWeight (M : GaussianSignalFamily ι) : ℝ :=
  M.posteriorVariance * M.priorPrecision

def signalWeight (M : GaussianSignalFamily ι) (i : ι) : ℝ :=
  M.posteriorVariance * M.signalPrecision i

/-- Posterior mean from a finite vector of observed signal values. -/
def posteriorMean (M : GaussianSignalFamily ι) (x : ι → ℝ) : ℝ :=
  M.posteriorVariance *
    (M.priorPrecision * M.priorMean +
      ∑ i : ι, M.signalPrecision i * x i)

theorem priorPrecision_pos (M : GaussianSignalFamily ι) :
    0 < M.priorPrecision := by
  exact inv_pos.mpr M.priorVar_pos

theorem signalPrecision_pos (M : GaussianSignalFamily ι) (i : ι) :
    0 < M.signalPrecision i := by
  exact inv_pos.mpr (M.noiseVar_pos i)

theorem signalPrecisionSum_nonneg (M : GaussianSignalFamily ι) :
    0 ≤ M.signalPrecisionSum := by
  exact Finset.sum_nonneg (by
    intro i _
    exact (M.signalPrecision_pos i).le)

theorem signalPrecisionSum_pos [Nonempty ι]
    (M : GaussianSignalFamily ι) :
    0 < M.signalPrecisionSum :=
  Finset.sum_pos
    (fun i _ => M.signalPrecision_pos i)
    Finset.univ_nonempty

theorem posteriorPrecision_pos (M : GaussianSignalFamily ι) :
    0 < M.posteriorPrecision := by
  exact add_pos_of_pos_of_nonneg M.priorPrecision_pos
    (by simpa [signalPrecisionSum] using M.signalPrecisionSum_nonneg)

theorem posteriorVariance_pos (M : GaussianSignalFamily ι) :
    0 < M.posteriorVariance := by
  exact inv_pos.mpr M.posteriorPrecision_pos

theorem posteriorVariance_le_priorVar (M : GaussianSignalFamily ι) :
    M.posteriorVariance ≤ M.priorVar := by
  have hle : M.priorPrecision ≤ M.posteriorPrecision := by
    dsimp [posteriorPrecision]
    exact le_add_of_nonneg_right
      (by simpa [signalPrecisionSum] using M.signalPrecisionSum_nonneg)
  have h := one_div_le_one_div_of_le M.priorPrecision_pos hle
  simpa [posteriorVariance, priorPrecision, one_div] using h

theorem posteriorVariance_lt_priorVar [Nonempty ι]
    (M : GaussianSignalFamily ι) :
    M.posteriorVariance < M.priorVar := by
  have hlt : M.priorPrecision < M.posteriorPrecision := by
    dsimp [posteriorPrecision]
    exact lt_add_of_pos_right M.priorPrecision
      (by simpa [signalPrecisionSum] using M.signalPrecisionSum_pos)
  have h := one_div_lt_one_div_of_lt M.priorPrecision_pos hlt
  simpa [posteriorVariance, priorPrecision, one_div] using h

/-- Marginal variance of the posterior mean for a finite centered signal family. -/
def posteriorMeanVariance (M : GaussianSignalFamily ι) : ℝ :=
  M.priorVar - M.posteriorVariance

theorem posteriorMeanVariance_nonneg (M : GaussianSignalFamily ι) :
    0 ≤ M.posteriorMeanVariance := by
  dsimp [posteriorMeanVariance]
  exact sub_nonneg.mpr M.posteriorVariance_le_priorVar

theorem posteriorMeanVariance_pos [Nonempty ι]
    (M : GaussianSignalFamily ι) :
    0 < M.posteriorMeanVariance := by
  dsimp [posteriorMeanVariance]
  exact sub_pos.mpr M.posteriorVariance_lt_priorVar

/-- Law of the finite-feature posterior mean as a Gaussian variance law. -/
def posteriorMeanLaw [Nonempty ι]
    (M : GaussianSignalFamily ι) : GaussianVarianceLaw where
  mean := M.priorMean
  variance := M.posteriorMeanVariance
  variance_pos := M.posteriorMeanVariance_pos

/-- Location-scale law of the finite-feature posterior mean. -/
def posteriorMeanScaleLaw [Nonempty ι]
    (M : GaussianSignalFamily ι) : GaussianScaleLaw where
  mean := M.priorMean
  scale := Real.sqrt M.posteriorMeanVariance
  scale_pos := Real.sqrt_pos.mpr M.posteriorMeanVariance_pos

/--
Two finite Gaussian signal families induce the same posterior-mean
location-scale law when their prior means, prior variances, and total signal
precisions agree.
-/
theorem posteriorMeanScaleLaw_eq_of_priorMean_eq_priorVar_eq_signalPrecisionSum_eq
    {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ]
    (M1 : GaussianSignalFamily ι) (M2 : GaussianSignalFamily κ)
    (hmean : M1.priorMean = M2.priorMean)
    (hpriorVar : M1.priorVar = M2.priorVar)
    (hsignalPrecisionSum :
      M1.signalPrecisionSum = M2.signalPrecisionSum) :
    M1.posteriorMeanScaleLaw = M2.posteriorMeanScaleLaw := by
  apply GaussianScaleLaw.ext
  · simp [posteriorMeanScaleLaw, hmean]
  · dsimp [posteriorMeanScaleLaw, posteriorMeanVariance, posteriorVariance,
      posteriorPrecision, priorPrecision, signalPrecisionSum]
      at hsignalPrecisionSum ⊢
    rw [hpriorVar, hsignalPrecisionSum]

theorem priorWeight_pos (M : GaussianSignalFamily ι) :
    0 < M.priorWeight := by
  exact mul_pos M.posteriorVariance_pos M.priorPrecision_pos

theorem signalWeight_pos (M : GaussianSignalFamily ι) (i : ι) :
    0 < M.signalWeight i := by
  exact mul_pos M.posteriorVariance_pos (M.signalPrecision_pos i)

theorem priorWeight_nonneg (M : GaussianSignalFamily ι) :
    0 ≤ M.priorWeight :=
  M.priorWeight_pos.le

theorem signalWeight_nonneg (M : GaussianSignalFamily ι) (i : ι) :
    0 ≤ M.signalWeight i :=
  (M.signalWeight_pos i).le

theorem priorWeight_add_sum_signalWeight_eq_one
    (M : GaussianSignalFamily ι) :
    M.priorWeight + ∑ i : ι, M.signalWeight i = 1 := by
  change M.posteriorVariance * M.priorPrecision +
      ∑ i : ι, M.posteriorVariance * M.signalPrecision i = 1
  rw [← Finset.mul_sum, ← mul_add,
    posteriorVariance, posteriorPrecision]
  exact inv_mul_cancel₀ (ne_of_gt M.posteriorPrecision_pos)

theorem posteriorMean_eq_weighted_sum
    (M : GaussianSignalFamily ι) (x : ι → ℝ) :
    M.posteriorMean x =
      M.priorWeight * M.priorMean +
        ∑ i : ι, M.signalWeight i * x i := by
  change
    M.posteriorVariance *
        (M.priorPrecision * M.priorMean +
          ∑ i : ι, M.signalPrecision i * x i) =
      (M.posteriorVariance * M.priorPrecision) * M.priorMean +
        ∑ i : ι, (M.posteriorVariance * M.signalPrecision i) * x i
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl (by
      intro i _
      ring)

/--
Posterior mean in precision-weighted form: prior precision times prior mean
plus signal precisions times observed signals, divided by total posterior
precision.
-/
theorem posteriorMean_eq_precision_weighted_div
    (M : GaussianSignalFamily ι) (x : ι → ℝ) :
    M.posteriorMean x =
      (M.priorPrecision * M.priorMean +
        ∑ i : ι, M.signalPrecision i * x i) /
          M.posteriorPrecision := by
  rw [posteriorMean, posteriorVariance]
  rw [div_eq_mul_inv]
  ring

/--
Marginal variance of the posterior mean in finite-feature precision form: prior
variance times total signal precision over posterior precision.
-/
theorem posteriorMeanVariance_eq_priorVar_mul_sum_signalPrecision_div_posteriorPrecision
    (M : GaussianSignalFamily ι) :
    M.posteriorMeanVariance =
      M.priorVar * (∑ i : ι, M.signalPrecision i) / M.posteriorPrecision := by
  rw [posteriorMeanVariance, posteriorVariance, posteriorPrecision, priorPrecision]
  have hp : M.priorVar ≠ 0 := ne_of_gt M.priorVar_pos
  have hpost :
      M.priorVar⁻¹ + ∑ i : ι, M.signalPrecision i ≠ 0 := by
    exact ne_of_gt M.posteriorPrecision_pos
  have hsum_nonneg : 0 ≤ ∑ i : ι, M.signalPrecision i := by
    exact Finset.sum_nonneg (by
      intro i _
      exact (M.signalPrecision_pos i).le)
  have hden :
      1 + M.priorVar * (∑ i : ι, M.signalPrecision i) ≠ 0 := by
    exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg M.priorVar_pos.le hsum_nonneg))
  field_simp [hp, hpost, hden]
  ring

theorem posteriorMeanVariance_lt_of_priorVar_eq_sum_signalPrecision_lt
    {Mlow Mhigh : GaussianSignalFamily ι}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      (∑ i : ι, Mlow.signalPrecision i) <
        ∑ i : ι, Mhigh.signalPrecision i) :
    Mlow.posteriorMeanVariance < Mhigh.posteriorMeanVariance := by
  have hpriorPrecision :
      Mlow.priorPrecision = Mhigh.priorPrecision := by
    simp [priorPrecision, hpriorVar]
  have hposteriorPrecision :
      Mlow.posteriorPrecision < Mhigh.posteriorPrecision := by
    dsimp [posteriorPrecision]
    rw [hpriorPrecision]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_lt_add_left hsum Mhigh.priorPrecision
  have hposteriorVariance :
      Mhigh.posteriorVariance < Mlow.posteriorVariance := by
    have h := one_div_lt_one_div_of_lt
      Mlow.posteriorPrecision_pos hposteriorPrecision
    simpa [posteriorVariance, one_div] using h
  dsimp [posteriorMeanVariance]
  rw [hpriorVar]
  linarith

theorem posteriorMeanVariance_lt_iff_of_priorVar_eq_sum_signalPrecision
    {Mlow Mhigh : GaussianSignalFamily ι}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar) :
    Mlow.posteriorMeanVariance < Mhigh.posteriorMeanVariance ↔
      (∑ i : ι, Mlow.signalPrecision i) <
        ∑ i : ι, Mhigh.signalPrecision i := by
  constructor
  · intro hvar
    by_contra hnot
    have hle :
        (∑ i : ι, Mhigh.signalPrecision i) ≤
          ∑ i : ι, Mlow.signalPrecision i := le_of_not_gt hnot
    rcases lt_or_eq_of_le hle with hgt | heq
    · have hrev :
          Mhigh.posteriorMeanVariance < Mlow.posteriorMeanVariance :=
        posteriorMeanVariance_lt_of_priorVar_eq_sum_signalPrecision_lt
          (Mlow := Mhigh) (Mhigh := Mlow) hpriorVar.symm hgt
      exact not_lt_of_ge hrev.le hvar
    · have hvar_eq :
          Mlow.posteriorMeanVariance = Mhigh.posteriorMeanVariance := by
        rw [Mlow.posteriorMeanVariance_eq_priorVar_mul_sum_signalPrecision_div_posteriorPrecision,
          Mhigh.posteriorMeanVariance_eq_priorVar_mul_sum_signalPrecision_div_posteriorPrecision]
        simp [posteriorPrecision, priorPrecision, hpriorVar, heq]
      exact (lt_irrefl Mhigh.posteriorMeanVariance)
        (by simpa [hvar_eq] using hvar)
  · exact posteriorMeanVariance_lt_of_priorVar_eq_sum_signalPrecision_lt hpriorVar

theorem posteriorMeanVariance_lt_of_priorVar_eq_signalPrecisionSum_lt
    {κ : Type*} [Fintype κ]
    {Mlow : GaussianSignalFamily ι} {Mhigh : GaussianSignalFamily κ}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum : Mlow.signalPrecisionSum < Mhigh.signalPrecisionSum) :
    Mlow.posteriorMeanVariance < Mhigh.posteriorMeanVariance := by
  have hpriorPrecision :
      Mlow.priorPrecision = Mhigh.priorPrecision := by
    simp [priorPrecision, hpriorVar]
  have hposteriorPrecision :
      Mlow.posteriorPrecision < Mhigh.posteriorPrecision := by
    dsimp [posteriorPrecision]
    rw [hpriorPrecision]
    simpa [signalPrecisionSum, add_comm, add_left_comm, add_assoc] using
      add_lt_add_left hsum Mhigh.priorPrecision
  have hposteriorVariance :
      Mhigh.posteriorVariance < Mlow.posteriorVariance := by
    have h := one_div_lt_one_div_of_lt
      Mlow.posteriorPrecision_pos hposteriorPrecision
    simpa [posteriorVariance, one_div] using h
  dsimp [posteriorMeanVariance]
  rw [hpriorVar]
  linarith

theorem posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_sum_signalPrecision_lt
    [Nonempty ι]
    {Mlow Mhigh : GaussianSignalFamily ι}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      (∑ i : ι, Mlow.signalPrecision i) <
        ∑ i : ι, Mhigh.signalPrecision i) :
    (Mlow.posteriorMeanScaleLaw).scale <
      (Mhigh.posteriorMeanScaleLaw).scale := by
  exact Real.sqrt_lt_sqrt Mlow.posteriorMeanVariance_nonneg
    (posteriorMeanVariance_lt_of_priorVar_eq_sum_signalPrecision_lt
      hpriorVar hsum)

theorem posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
    [Nonempty ι] {κ : Type*} [Fintype κ] [Nonempty κ]
    {Mlow : GaussianSignalFamily ι} {Mhigh : GaussianSignalFamily κ}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum : Mlow.signalPrecisionSum < Mhigh.signalPrecisionSum) :
    (Mlow.posteriorMeanScaleLaw).scale <
      (Mhigh.posteriorMeanScaleLaw).scale := by
  exact Real.sqrt_lt_sqrt Mlow.posteriorMeanVariance_nonneg
    (posteriorMeanVariance_lt_of_priorVar_eq_signalPrecisionSum_lt
      hpriorVar hsum)

/-- The posterior mean is monotone in every observed signal coordinate. -/
theorem posteriorMean_mono_of_pointwise_le
    (M : GaussianSignalFamily ι) {x y : ι → ℝ}
    (hxy : ∀ i, x i ≤ y i) :
    M.posteriorMean x ≤ M.posteriorMean y := by
  dsimp [posteriorMean]
  refine mul_le_mul_of_nonneg_left ?_ M.posteriorVariance_pos.le
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left
      (Finset.sum_le_sum (by
        intro i _
        exact mul_le_mul_of_nonneg_left (hxy i) (M.signalPrecision_pos i).le))
      (M.priorPrecision * M.priorMean)

/--
The posterior mean is strictly increasing when all observed signals weakly
increase and at least one signal strictly increases.
-/
theorem posteriorMean_lt_of_pointwise_le_exists_lt
    (M : GaussianSignalFamily ι) {x y : ι → ℝ}
    (hxy : ∀ i, x i ≤ y i) (j : ι) (hstrict : x j < y j) :
    M.posteriorMean x < M.posteriorMean y := by
  dsimp [posteriorMean]
  refine mul_lt_mul_of_pos_left ?_ M.posteriorVariance_pos
  have hsum_lt :
      (∑ i : ι, M.signalPrecision i * x i) <
        ∑ i : ι, M.signalPrecision i * y i := by
    exact Finset.sum_lt_sum (by
      intro i _
      exact mul_le_mul_of_nonneg_left (hxy i) (M.signalPrecision_pos i).le)
      ⟨j, ⟨Finset.mem_univ j,
        mul_lt_mul_of_pos_left hstrict (M.signalPrecision_pos j)⟩⟩
  simpa [add_comm, add_left_comm, add_assoc] using
    add_lt_add_left hsum_lt (M.priorPrecision * M.priorMean)

/-- Holding all other coordinates fixed, the posterior mean is strictly
increasing in any one observed signal. -/
theorem posteriorMean_update_strictMono [DecidableEq ι]
    (M : GaussianSignalFamily ι) (x : ι → ℝ) (j : ι) :
    StrictMono (fun z : ℝ => M.posteriorMean (Function.update x j z)) := by
  intro a b hab
  refine M.posteriorMean_lt_of_pointwise_le_exists_lt ?_ j ?_
  · intro i
    by_cases h : i = j
    · subst h
      simp [Function.update, hab.le]
    · simp [Function.update, h]
  · simp [Function.update, hab]

/--
Holding all other coordinates fixed, the posterior mean is an affine function
of the selected coordinate, with slope equal to that coordinate's posterior
weight.
-/
theorem posteriorMean_update_eq_base_add_weight_mul_sub [DecidableEq ι]
    (M : GaussianSignalFamily ι) (x : ι → ℝ) (j : ι) (base z : ℝ) :
    M.posteriorMean (Function.update x j z) =
      M.posteriorMean (Function.update x j base) +
        M.signalWeight j * (z - base) := by
  classical
  have hsum (t : ℝ) :
      (∑ i : ι, M.signalWeight i * Function.update x j t i) =
        M.signalWeight j * t +
          ∑ i : ι, if i = j then 0 else M.signalWeight i * x i := by
    calc
      (∑ i : ι, M.signalWeight i * Function.update x j t i) =
          ∑ i : ι,
            ((if i = j then M.signalWeight i * t else 0) +
              if i = j then 0 else M.signalWeight i * x i) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : i = j <;> simp [Function.update, h]
      _ = (∑ i : ι, if i = j then M.signalWeight i * t else 0) +
            ∑ i : ι, if i = j then 0 else M.signalWeight i * x i := by
        rw [Finset.sum_add_distrib]
      _ = M.signalWeight j * t +
            ∑ i : ι, if i = j then 0 else M.signalWeight i * x i := by
        rw [Finset.sum_ite_eq']
        simp
  rw [M.posteriorMean_eq_weighted_sum, M.posteriorMean_eq_weighted_sum,
    hsum z, hsum base]
  ring

theorem posteriorMean_update_eq_base_add_weight_mul [DecidableEq ι]
    (M : GaussianSignalFamily ι) (x : ι → ℝ) (j : ι) (z : ℝ) :
    M.posteriorMean (Function.update x j z) =
      M.posteriorMean (Function.update x j 0) + M.signalWeight j * z := by
  simpa using M.posteriorMean_update_eq_base_add_weight_mul_sub x j 0 z

/--
Coordinate-threshold form for finite Gaussian posterior means: after fixing
all other signals, clearing a posterior-mean threshold is equivalent to the
selected signal exceeding the induced affine cutoff.
-/
theorem threshold_le_posteriorMean_update_iff_cutoff_le [DecidableEq ι]
    (M : GaussianSignalFamily ι) (x : ι → ℝ) (j : ι)
    (base threshold z : ℝ) :
    threshold ≤ M.posteriorMean (Function.update x j z) ↔
      AppliedModelingLib.affineCutoff
        (M.posteriorMean (Function.update x j base) -
          M.signalWeight j * base)
        (M.signalWeight j) threshold ≤ z := by
  rw [M.posteriorMean_update_eq_base_add_weight_mul_sub x j base z]
  have hscore :
      M.posteriorMean (Function.update x j base) +
          M.signalWeight j * (z - base) =
        (M.posteriorMean (Function.update x j base) -
          M.signalWeight j * base) + M.signalWeight j * z := by
    ring
  rw [hscore]
  exact AppliedModelingLib.threshold_le_affine_iff_cutoff_le
    (M.signalWeight_pos j)

/--
Holding all other signals fixed, a posterior-mean threshold in one Gaussian
signal coordinate is a lower-cutoff rule.
-/
theorem lowerCutoffStrategy_posteriorMean_update_threshold [DecidableEq ι]
    (M : GaussianSignalFamily ι) (x : ι → ℝ) (j : ι)
    (base threshold : ℝ) :
    AppliedModelingLib.LowerCutoffStrategy
      (fun z : ℝ => threshold ≤ M.posteriorMean (Function.update x j z)) := by
  refine ⟨AppliedModelingLib.affineCutoff
    (M.posteriorMean (Function.update x j base) - M.signalWeight j * base)
    (M.signalWeight j) threshold, ?_⟩
  intro z
  exact M.threshold_le_posteriorMean_update_iff_cutoff_le x j base threshold z

end GaussianSignalFamily

/--
Finite Gaussian signal family with nonzero signal-specific noise means.

The observed signal has the offset form `x i = q + noiseMean i + error i`;
posterior formulas are delegated to `GaussianSignalFamily` after centering each
coordinate by `noiseMean i`.
-/
structure GaussianOffsetSignalFamily (ι : Type*) [Fintype ι] where
  priorMean : ℝ
  priorVar : ℝ
  noiseMean : ι → ℝ
  noiseVar : ι → ℝ
  priorVar_pos : 0 < priorVar
  noiseVar_pos : ∀ i, 0 < noiseVar i

namespace GaussianOffsetSignalFamily

variable {ι : Type*} [Fintype ι]

def withExtraSignal (M : GaussianOffsetSignalFamily ι)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    GaussianOffsetSignalFamily (Option ι) where
  priorMean := M.priorMean
  priorVar := M.priorVar
  noiseMean
    | none => extraNoiseMean
    | some i => M.noiseMean i
  noiseVar
    | none => extraNoiseVar
    | some i => M.noiseVar i
  priorVar_pos := M.priorVar_pos
  noiseVar_pos
    | none => hextraNoiseVar
    | some i => M.noiseVar_pos i

@[simp] theorem withExtraSignal_priorMean
    (M : GaussianOffsetSignalFamily ι)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    (M.withExtraSignal extraNoiseMean extraNoiseVar
      hextraNoiseVar).priorMean = M.priorMean := rfl

@[simp] theorem withExtraSignal_priorVar
    (M : GaussianOffsetSignalFamily ι)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    (M.withExtraSignal extraNoiseMean extraNoiseVar
      hextraNoiseVar).priorVar = M.priorVar := rfl

def centeredFamily (M : GaussianOffsetSignalFamily ι) :
    GaussianSignalFamily ι where
  priorMean := M.priorMean
  priorVar := M.priorVar
  noiseVar := M.noiseVar
  priorVar_pos := M.priorVar_pos
  noiseVar_pos := M.noiseVar_pos

def centeredSignal (M : GaussianOffsetSignalFamily ι)
    (x : ι → ℝ) (i : ι) : ℝ :=
  x i - M.noiseMean i

def posteriorMean (M : GaussianOffsetSignalFamily ι)
    (x : ι → ℝ) : ℝ :=
  M.centeredFamily.posteriorMean (M.centeredSignal x)

theorem posteriorMean_eq_centered
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) :
    M.posteriorMean x =
      M.centeredFamily.posteriorMean (M.centeredSignal x) := rfl

theorem priorWeight_add_sum_signalWeight_eq_one
    (M : GaussianOffsetSignalFamily ι) :
    M.centeredFamily.priorWeight +
        ∑ i : ι, M.centeredFamily.signalWeight i = 1 :=
  M.centeredFamily.priorWeight_add_sum_signalWeight_eq_one

/-- Marginal variance of the offset-family posterior mean. -/
def posteriorMeanVariance (M : GaussianOffsetSignalFamily ι) : ℝ :=
  M.centeredFamily.posteriorMeanVariance

theorem posteriorMeanVariance_nonneg
    (M : GaussianOffsetSignalFamily ι) :
    0 ≤ M.posteriorMeanVariance :=
  M.centeredFamily.posteriorMeanVariance_nonneg

theorem posteriorMeanVariance_pos [Nonempty ι]
    (M : GaussianOffsetSignalFamily ι) :
    0 < M.posteriorMeanVariance :=
  M.centeredFamily.posteriorMeanVariance_pos

/-- Law of the offset-family posterior mean as a Gaussian variance law. -/
def posteriorMeanLaw [Nonempty ι]
    (M : GaussianOffsetSignalFamily ι) : GaussianVarianceLaw where
  mean := M.priorMean
  variance := M.posteriorMeanVariance
  variance_pos := M.posteriorMeanVariance_pos

/-- Location-scale law of the offset-family posterior mean. -/
def posteriorMeanScaleLaw [Nonempty ι]
    (M : GaussianOffsetSignalFamily ι) : GaussianScaleLaw where
  mean := M.priorMean
  scale := Real.sqrt M.posteriorMeanVariance
  scale_pos := Real.sqrt_pos.mpr M.posteriorMeanVariance_pos

/--
Two offset Gaussian signal families induce the same posterior-mean
location-scale law when their prior means, prior variances, and total centered
signal precisions agree.
-/
theorem posteriorMeanScaleLaw_eq_of_priorMean_eq_priorVar_eq_signalPrecisionSum_eq
    {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ]
    (M1 : GaussianOffsetSignalFamily ι) (M2 : GaussianOffsetSignalFamily κ)
    (hmean : M1.priorMean = M2.priorMean)
    (hpriorVar : M1.priorVar = M2.priorVar)
    (hsignalPrecisionSum :
      M1.centeredFamily.signalPrecisionSum =
        M2.centeredFamily.signalPrecisionSum) :
    M1.posteriorMeanScaleLaw = M2.posteriorMeanScaleLaw := by
  change
    M1.centeredFamily.posteriorMeanScaleLaw =
      M2.centeredFamily.posteriorMeanScaleLaw
  exact
    GaussianSignalFamily.posteriorMeanScaleLaw_eq_of_priorMean_eq_priorVar_eq_signalPrecisionSum_eq
      M1.centeredFamily M2.centeredFamily hmean hpriorVar
      hsignalPrecisionSum

/--
Conditional law of the posterior mean given true skill `q` for offset signals
of the form `x i = q + noiseMean i + centered noise i`.
-/
def conditionalPosteriorMeanScaleLaw [Nonempty ι]
    (M : GaussianOffsetSignalFamily ι) (q : ℝ) : GaussianScaleLaw where
  mean :=
    M.centeredFamily.priorWeight * M.priorMean +
      (∑ i : ι, M.centeredFamily.signalWeight i) * q
  scale :=
    M.centeredFamily.posteriorVariance *
      Real.sqrt M.centeredFamily.signalPrecisionSum
  scale_pos := by
    exact mul_pos M.centeredFamily.posteriorVariance_pos
      (Real.sqrt_pos.mpr M.centeredFamily.signalPrecisionSum_pos)

theorem posteriorMean_eq_weighted_sum
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) :
    M.posteriorMean x =
      M.centeredFamily.priorWeight * M.priorMean +
        ∑ i : ι,
          M.centeredFamily.signalWeight i *
            (x i - M.noiseMean i) := by
  rw [posteriorMean, GaussianSignalFamily.posteriorMean_eq_weighted_sum]
  rfl

/--
Posterior mean for offset signals in precision-weighted form. Each raw signal
is centered by its group-specific noise mean.
-/
theorem posteriorMean_eq_precision_weighted_div
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) :
    M.posteriorMean x =
      (M.centeredFamily.priorPrecision * M.priorMean +
        ∑ i : ι,
          M.centeredFamily.signalPrecision i * (x i - M.noiseMean i)) /
          M.centeredFamily.posteriorPrecision := by
  rw [posteriorMean, GaussianSignalFamily.posteriorMean_eq_precision_weighted_div]
  rfl

/--
Marginal variance of the offset-family posterior mean in precision notation.
-/
theorem posteriorMeanVariance_eq_priorVar_mul_sum_signalPrecision_div_posteriorPrecision
    (M : GaussianOffsetSignalFamily ι) :
    M.posteriorMeanVariance =
      M.priorVar * (∑ i : ι, M.centeredFamily.signalPrecision i) /
        M.centeredFamily.posteriorPrecision := by
  exact M.centeredFamily
    |>.posteriorMeanVariance_eq_priorVar_mul_sum_signalPrecision_div_posteriorPrecision

theorem posteriorMeanVariance_lt_of_priorVar_eq_sum_signalPrecision_lt
    {Mlow Mhigh : GaussianOffsetSignalFamily ι}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      (∑ i : ι, Mlow.centeredFamily.signalPrecision i) <
        ∑ i : ι, Mhigh.centeredFamily.signalPrecision i) :
    Mlow.posteriorMeanVariance < Mhigh.posteriorMeanVariance := by
  exact GaussianSignalFamily.posteriorMeanVariance_lt_of_priorVar_eq_sum_signalPrecision_lt
    (Mlow := Mlow.centeredFamily) (Mhigh := Mhigh.centeredFamily)
    hpriorVar hsum

theorem posteriorMeanVariance_lt_iff_of_priorVar_eq_sum_signalPrecision
    {Mlow Mhigh : GaussianOffsetSignalFamily ι}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar) :
    Mlow.posteriorMeanVariance < Mhigh.posteriorMeanVariance ↔
      (∑ i : ι, Mlow.centeredFamily.signalPrecision i) <
        ∑ i : ι, Mhigh.centeredFamily.signalPrecision i :=
  GaussianSignalFamily.posteriorMeanVariance_lt_iff_of_priorVar_eq_sum_signalPrecision
    (Mlow := Mlow.centeredFamily) (Mhigh := Mhigh.centeredFamily)
    hpriorVar

theorem posteriorMeanVariance_lt_of_priorVar_eq_signalPrecisionSum_lt
    {κ : Type*} [Fintype κ]
    {Mlow : GaussianOffsetSignalFamily ι} {Mhigh : GaussianOffsetSignalFamily κ}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      Mlow.centeredFamily.signalPrecisionSum <
        Mhigh.centeredFamily.signalPrecisionSum) :
    Mlow.posteriorMeanVariance < Mhigh.posteriorMeanVariance := by
  exact GaussianSignalFamily.posteriorMeanVariance_lt_of_priorVar_eq_signalPrecisionSum_lt
    (Mlow := Mlow.centeredFamily) (Mhigh := Mhigh.centeredFamily)
    hpriorVar hsum

theorem posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_sum_signalPrecision_lt
    [Nonempty ι]
    {Mlow Mhigh : GaussianOffsetSignalFamily ι}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      (∑ i : ι, Mlow.centeredFamily.signalPrecision i) <
        ∑ i : ι, Mhigh.centeredFamily.signalPrecision i) :
    (Mlow.posteriorMeanScaleLaw).scale <
      (Mhigh.posteriorMeanScaleLaw).scale := by
  exact Real.sqrt_lt_sqrt Mlow.posteriorMeanVariance_nonneg
    (posteriorMeanVariance_lt_of_priorVar_eq_sum_signalPrecision_lt
      hpriorVar hsum)

theorem posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
    [Nonempty ι] {κ : Type*} [Fintype κ] [Nonempty κ]
    {Mlow : GaussianOffsetSignalFamily ι} {Mhigh : GaussianOffsetSignalFamily κ}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      Mlow.centeredFamily.signalPrecisionSum <
        Mhigh.centeredFamily.signalPrecisionSum) :
    (Mlow.posteriorMeanScaleLaw).scale <
      (Mhigh.posteriorMeanScaleLaw).scale := by
  exact Real.sqrt_lt_sqrt Mlow.posteriorMeanVariance_nonneg
    (posteriorMeanVariance_lt_of_priorVar_eq_signalPrecisionSum_lt
      hpriorVar hsum)

theorem withExtraSignal_signalPrecisionSum_eq
    (M : GaussianOffsetSignalFamily ι)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    ((M.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).centeredFamily).signalPrecisionSum =
      M.centeredFamily.signalPrecisionSum + extraNoiseVar⁻¹ := by
  simp [withExtraSignal, centeredFamily, GaussianSignalFamily.signalPrecisionSum,
    GaussianSignalFamily.signalPrecision, add_comm]

theorem signalPrecisionSum_lt_withExtraSignal
    (M : GaussianOffsetSignalFamily ι)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    M.centeredFamily.signalPrecisionSum <
      ((M.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).centeredFamily).signalPrecisionSum := by
  rw [withExtraSignal_signalPrecisionSum_eq]
  exact lt_add_of_pos_right _
    (inv_pos.mpr hextraNoiseVar)

theorem posteriorMeanScaleLaw_scale_lt_withExtraSignal
    [Nonempty ι] (M : GaussianOffsetSignalFamily ι)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    (M.posteriorMeanScaleLaw).scale <
      ((M.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).posteriorMeanScaleLaw).scale :=
  posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
    (Mlow := M)
    (Mhigh := M.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar)
    rfl
    (signalPrecisionSum_lt_withExtraSignal M extraNoiseMean extraNoiseVar
      hextraNoiseVar)

/-- The offset-family posterior mean is monotone in every raw signal coordinate. -/
theorem posteriorMean_mono_of_pointwise_le
    (M : GaussianOffsetSignalFamily ι) {x y : ι → ℝ}
    (hxy : ∀ i, x i ≤ y i) :
    M.posteriorMean x ≤ M.posteriorMean y := by
  rw [posteriorMean, posteriorMean]
  exact M.centeredFamily.posteriorMean_mono_of_pointwise_le
    (fun i => sub_le_sub_right (hxy i) (M.noiseMean i))

/--
The offset-family posterior mean is strictly increasing when all raw signals
weakly increase and at least one raw signal strictly increases.
-/
theorem posteriorMean_lt_of_pointwise_le_exists_lt
    (M : GaussianOffsetSignalFamily ι) {x y : ι → ℝ}
    (hxy : ∀ i, x i ≤ y i) (j : ι) (hstrict : x j < y j) :
    M.posteriorMean x < M.posteriorMean y := by
  rw [posteriorMean, posteriorMean]
  exact M.centeredFamily.posteriorMean_lt_of_pointwise_le_exists_lt
    (fun i => sub_le_sub_right (hxy i) (M.noiseMean i)) j
    (sub_lt_sub_right hstrict (M.noiseMean j))

/-- Holding all other raw signals fixed, the offset-family posterior mean is
strictly increasing in any one raw signal. -/
theorem posteriorMean_update_strictMono [DecidableEq ι]
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) (j : ι) :
    StrictMono (fun z : ℝ => M.posteriorMean (Function.update x j z)) := by
  intro a b hab
  refine M.posteriorMean_lt_of_pointwise_le_exists_lt ?_ j ?_
  · intro i
    by_cases h : i = j
    · subst h
      simp [Function.update, hab.le]
    · simp [Function.update, h]
  · simp [Function.update, hab]

/--
Holding all other raw signals fixed, the offset-family posterior mean is an
affine function of the selected raw signal.
-/
theorem posteriorMean_update_eq_base_add_weight_mul_sub [DecidableEq ι]
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) (j : ι) (base z : ℝ) :
    M.posteriorMean (Function.update x j z) =
      M.posteriorMean (Function.update x j base) +
        M.centeredFamily.signalWeight j * (z - base) := by
  have hcenter (t : ℝ) :
      M.centeredSignal (Function.update x j t) =
        Function.update (M.centeredSignal x) j (t - M.noiseMean j) := by
    ext i
    by_cases h : i = j
    · subst h
      simp [centeredSignal, Function.update]
    · simp [centeredSignal, Function.update, h]
  rw [posteriorMean, posteriorMean, hcenter z, hcenter base,
    M.centeredFamily.posteriorMean_update_eq_base_add_weight_mul_sub
      (M.centeredSignal x) j (base - M.noiseMean j) (z - M.noiseMean j)]
  ring

theorem posteriorMean_update_eq_base_add_weight_mul [DecidableEq ι]
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) (j : ι) (z : ℝ) :
    M.posteriorMean (Function.update x j z) =
      M.posteriorMean (Function.update x j 0) +
        M.centeredFamily.signalWeight j * z := by
  simpa using M.posteriorMean_update_eq_base_add_weight_mul_sub x j 0 z

/--
Coordinate-threshold form for offset Gaussian posterior means: after fixing
all other raw signals, clearing a posterior-mean threshold is equivalent to the
selected raw signal exceeding the induced affine cutoff.
-/
theorem threshold_le_posteriorMean_update_iff_cutoff_le [DecidableEq ι]
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) (j : ι)
    (base threshold z : ℝ) :
    threshold ≤ M.posteriorMean (Function.update x j z) ↔
      AppliedModelingLib.affineCutoff
        (M.posteriorMean (Function.update x j base) -
          M.centeredFamily.signalWeight j * base)
        (M.centeredFamily.signalWeight j) threshold ≤ z := by
  rw [M.posteriorMean_update_eq_base_add_weight_mul_sub x j base z]
  have hscore :
      M.posteriorMean (Function.update x j base) +
          M.centeredFamily.signalWeight j * (z - base) =
        (M.posteriorMean (Function.update x j base) -
          M.centeredFamily.signalWeight j * base) +
          M.centeredFamily.signalWeight j * z := by
    ring
  rw [hscore]
  exact AppliedModelingLib.threshold_le_affine_iff_cutoff_le
    (M.centeredFamily.signalWeight_pos j)

/--
Holding all other offset signals fixed, a posterior-mean threshold in one
Gaussian signal coordinate is a lower-cutoff rule.
-/
theorem lowerCutoffStrategy_posteriorMean_update_threshold [DecidableEq ι]
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) (j : ι)
    (base threshold : ℝ) :
    AppliedModelingLib.LowerCutoffStrategy
      (fun z : ℝ => threshold ≤ M.posteriorMean (Function.update x j z)) := by
  refine ⟨AppliedModelingLib.affineCutoff
    (M.posteriorMean (Function.update x j base) -
      M.centeredFamily.signalWeight j * base)
    (M.centeredFamily.signalWeight j) threshold, ?_⟩
  intro z
  exact M.threshold_le_posteriorMean_update_iff_cutoff_le x j base threshold z

/--
Mean of the conditional posterior-score law in precision notation.
-/
theorem conditionalPosteriorMeanScaleLaw_mean_eq_precision_weighted_div
    [Nonempty ι] (M : GaussianOffsetSignalFamily ι) (q : ℝ) :
    (M.conditionalPosteriorMeanScaleLaw q).mean =
      (M.centeredFamily.priorPrecision * M.priorMean +
        M.centeredFamily.signalPrecisionSum * q) /
        M.centeredFamily.posteriorPrecision := by
  rw [conditionalPosteriorMeanScaleLaw]
  change
    M.centeredFamily.priorWeight * M.priorMean +
        (∑ i : ι, M.centeredFamily.signalWeight i) * q =
      (M.centeredFamily.priorPrecision * M.priorMean +
        M.centeredFamily.signalPrecisionSum * q) /
        M.centeredFamily.posteriorPrecision
  have hsum_weights :
      (∑ i : ι, M.centeredFamily.signalWeight i) =
        M.centeredFamily.posteriorVariance *
          M.centeredFamily.signalPrecisionSum := by
    simp [GaussianSignalFamily.signalWeight,
      GaussianSignalFamily.signalPrecisionSum, Finset.mul_sum]
  rw [GaussianSignalFamily.priorWeight, hsum_weights,
    GaussianSignalFamily.posteriorVariance]
  rw [div_eq_mul_inv]
  ring

/--
Scale of the conditional posterior-score law in precision notation.
-/
theorem conditionalPosteriorMeanScaleLaw_scale_eq
    [Nonempty ι] (M : GaussianOffsetSignalFamily ι) (q : ℝ) :
    (M.conditionalPosteriorMeanScaleLaw q).scale =
      M.centeredFamily.posteriorVariance *
        Real.sqrt M.centeredFamily.signalPrecisionSum := rfl

/--
Standardized threshold for the conditional posterior-score law, in
`numerator / sqrt(total signal precision)` form.
-/
theorem conditionalPosteriorMeanScaleLaw_standardize_threshold
    [Nonempty ι] (M : GaussianOffsetSignalFamily ι)
    (threshold q : ℝ) :
    (M.conditionalPosteriorMeanScaleLaw q).standardize threshold =
      (M.centeredFamily.priorPrecision * (threshold - M.priorMean) -
        M.centeredFamily.signalPrecisionSum * (q - threshold)) /
        Real.sqrt M.centeredFamily.signalPrecisionSum := by
  rw [GaussianScaleLaw.standardize,
    M.conditionalPosteriorMeanScaleLaw_mean_eq_precision_weighted_div q,
    M.conditionalPosteriorMeanScaleLaw_scale_eq q]
  have hpost : M.centeredFamily.posteriorPrecision ≠ 0 :=
    ne_of_gt M.centeredFamily.posteriorPrecision_pos
  have hsqrt : Real.sqrt M.centeredFamily.signalPrecisionSum ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr M.centeredFamily.signalPrecisionSum_pos)
  have hvar : M.centeredFamily.posteriorVariance ≠ 0 :=
    ne_of_gt M.centeredFamily.posteriorVariance_pos
  rw [GaussianSignalFamily.posteriorVariance] at hvar ⊢
  field_simp [hpost, hsqrt]
  rw [GaussianSignalFamily.posteriorPrecision,
    GaussianSignalFamily.signalPrecisionSum]
  ring

end GaussianOffsetSignalFamily

/--
Reusable certificate for normal-density/tail analytic facts.

Use this as the boundary between algebraic Gaussian formalization and hard
analytic facts about inverse Mills ratios or hazard rates.
-/
structure GaussianHazardCertificate where
  api : StandardGaussianCDFAPI
  hazard : ℝ → ℝ
  tail_pos : ∀ z, 0 < 1 - api.cdf z
  hazard_eq : ∀ z, hazard z = api.density z / (1 - api.cdf z)
  hazard_pos : ∀ z, 0 < hazard z
  hazard_gt_arg_of_pos : ∀ {z : ℝ}, 0 < z → z < hazard z
  hazard_mono : Monotone hazard
  scaled_hazard_mono :
    ∀ {a x y : ℝ}, 0 < a → 0 < x → x ≤ y →
      x * hazard (a / x) ≤ y * hazard (a / y)
  scaled_hazard_strictMono :
    ∀ {a x y : ℝ}, 0 < a → 0 < x → x < y →
      x * hazard (a / x) < y * hazard (a / y)

namespace GaussianHazardCertificate

theorem normalTail_pos (C : GaussianHazardCertificate)
    (L : GaussianScaleLaw) (threshold : ℝ) :
    0 < C.api.normalTail L threshold := by
  exact C.tail_pos (L.standardize threshold)

theorem normalDensity_div_normalTail_eq_hazard_div_scale
    (C : GaussianHazardCertificate) (L : GaussianScaleLaw)
    (threshold : ℝ) :
    C.api.normalDensity L threshold / C.api.normalTail L threshold =
      C.hazard (L.standardize threshold) / L.scale := by
  rw [StandardGaussianCDFAPI.normalDensity,
    StandardGaussianCDFAPI.normalTail,
    StandardGaussianCDFAPI.normalCDF,
    C.hazard_eq]
  field_simp [ne_of_gt (C.tail_pos (L.standardize threshold)),
    ne_of_gt L.scale_pos]

/--
Certificate-level formula for the conditional mean above a threshold for a
location-scale Gaussian, expressed through the standard-normal hazard.
-/
def normalUpperTailMean (C : GaussianHazardCertificate)
    (L : GaussianScaleLaw) (threshold : ℝ) : ℝ :=
  L.mean + L.scale * C.hazard (L.standardize threshold)

/--
Upper-tail means are invariant under equal Gaussian location-scale laws and
equal thresholds.

This is a small transport lemma for testing/admissions papers where a source
case analysis proves that an unaffected group's posterior law and cutoff are
unchanged, then needs the corresponding admitted-merit row equality.
-/
theorem normalUpperTailMean_congr
    (C : GaussianHazardCertificate) {L L' : GaussianScaleLaw}
    {threshold threshold' : ℝ}
    (hL : L = L') (hthreshold : threshold = threshold') :
    C.normalUpperTailMean L threshold =
      C.normalUpperTailMean L' threshold' := by
  subst hL
  subst hthreshold
  rfl

/--
Upper-tail means are invariant under primitive equality of the offset-Gaussian
parameters that determine the posterior-mean law.

This parameter-level version of `normalUpperTailMean_congr` lets callers
transport an admitted-merit quantity by proving equality of prior means, prior
variances, total signal precisions, and thresholds, without first materializing
the posterior-law equality.
-/
theorem normalUpperTailMean_congr_of_offset_prior_precision
    (C : GaussianHazardCertificate)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    {M : GaussianOffsetSignalFamily ι}
    {M' : GaussianOffsetSignalFamily κ}
    {threshold threshold' : ℝ}
    (hmean : M.priorMean = M'.priorMean)
    (hpriorVar : M.priorVar = M'.priorVar)
    (hsignalPrecisionSum :
      M.centeredFamily.signalPrecisionSum =
        M'.centeredFamily.signalPrecisionSum)
    (hthreshold : threshold = threshold') :
    C.normalUpperTailMean M.posteriorMeanScaleLaw threshold =
      C.normalUpperTailMean M'.posteriorMeanScaleLaw threshold' :=
  C.normalUpperTailMean_congr
    (GaussianOffsetSignalFamily.posteriorMeanScaleLaw_eq_of_priorMean_eq_priorVar_eq_signalPrecisionSum_eq
      M M' hmean hpriorVar hsignalPrecisionSum)
    hthreshold

theorem normalUpperTailMean_mono_threshold
    (C : GaussianHazardCertificate) (L : GaussianScaleLaw) :
    Monotone (C.normalUpperTailMean L) := by
  intro x y hxy
  dsimp [normalUpperTailMean]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left
      (mul_le_mul_of_nonneg_left
        (C.hazard_mono (L.standardize_mono hxy)) L.scale_pos.le)
      L.mean

/--
The conditional mean above a Gaussian threshold is strictly above the
threshold.  For nonpositive standardized thresholds this only uses positivity
of the hazard; for positive standardized thresholds it uses the Mills-ratio
fact packaged in `hazard_gt_arg_of_pos`.
-/
theorem normalUpperTailMean_gt_threshold
    (C : GaussianHazardCertificate)
    (L : GaussianScaleLaw) (threshold : ℝ) :
    threshold < C.normalUpperTailMean L threshold := by
  let z : ℝ := L.standardize threshold
  have hthreshold_std :
      L.mean + L.scale * L.standardize threshold = threshold := by
    simpa [GaussianScaleLaw.unstandardize] using
      L.unstandardize_standardize threshold
  have hcore : z < C.hazard z := by
    by_cases hz_nonpos : z ≤ 0
    · have hhaz_pos : 0 < C.hazard z := C.hazard_pos z
      linarith
    · have hz_pos : 0 < z := lt_of_not_ge hz_nonpos
      exact C.hazard_gt_arg_of_pos hz_pos
  have hmul :
      L.scale * z < L.scale * C.hazard z :=
    mul_lt_mul_of_pos_left hcore L.scale_pos
  calc
    threshold = L.mean + L.scale * z := by
      dsimp [z]
      exact hthreshold_std.symm
    _ < L.mean + L.scale * C.hazard z := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_lt_add_left hmul L.mean
    _ = C.normalUpperTailMean L threshold := by
      simp [normalUpperTailMean, z]

theorem normalUpperTailMean_le_of_same_mean_scale_le_above_mean
    (C : GaussianHazardCertificate)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale ≤ Llarge.scale)
    {threshold : ℝ} (hthreshold : Lsmall.mean < threshold) :
    C.normalUpperTailMean Lsmall threshold ≤
      C.normalUpperTailMean Llarge threshold := by
  have ha : 0 < threshold - Lsmall.mean := sub_pos.mpr hthreshold
  have hscaled :
      Lsmall.scale * C.hazard ((threshold - Lsmall.mean) / Lsmall.scale) ≤
        Llarge.scale * C.hazard ((threshold - Lsmall.mean) / Llarge.scale) :=
    C.scaled_hazard_mono ha Lsmall.scale_pos hscale
  rw [normalUpperTailMean, normalUpperTailMean, GaussianScaleLaw.standardize,
    GaussianScaleLaw.standardize, ← hmean]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left hscaled Lsmall.mean

theorem normalUpperTailMean_lt_of_same_mean_scale_lt_above_mean
    (C : GaussianHazardCertificate)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale < Llarge.scale)
    {threshold : ℝ} (hthreshold : Lsmall.mean < threshold) :
    C.normalUpperTailMean Lsmall threshold <
      C.normalUpperTailMean Llarge threshold := by
  have ha : 0 < threshold - Lsmall.mean := sub_pos.mpr hthreshold
  have hscaled :
      Lsmall.scale * C.hazard ((threshold - Lsmall.mean) / Lsmall.scale) <
        Llarge.scale * C.hazard ((threshold - Lsmall.mean) / Llarge.scale) :=
    C.scaled_hazard_strictMono ha Lsmall.scale_pos hscale
  rw [normalUpperTailMean, normalUpperTailMean, GaussianScaleLaw.standardize,
    GaussianScaleLaw.standardize, ← hmean]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_lt_add_left hscaled Lsmall.mean

section Mixture

variable {γ : Type*} [Fintype γ]

theorem mixtureTailMass_pos
    (C : GaussianHazardCertificate)
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw}
    (hweight : ∀ g, 0 ≤ weight g) (hpos : ∃ g, 0 < weight g)
    (threshold : ℝ) :
    0 < C.api.mixtureTailMass weight law threshold := by
  dsimp [StandardGaussianCDFAPI.mixtureTailMass]
  exact Finset.sum_pos' (by
    intro g _
    exact mul_nonneg (hweight g)
      (C.normalTail_pos (law g) threshold).le) (by
    rcases hpos with ⟨g, hg⟩
    exact ⟨g, Finset.mem_univ g,
      mul_pos hg (C.normalTail_pos (law g) threshold)⟩)

/-- Numerator for the finite-mixture mean of Gaussian scores above a threshold. -/
def mixtureUpperTailMeanNumerator
    (C : GaussianHazardCertificate)
    (weight : γ → ℝ) (law : γ → GaussianScaleLaw)
    (threshold : ℝ) : ℝ :=
  ∑ g : γ,
    weight g * C.api.thresholdPassProb (law g) threshold *
      C.normalUpperTailMean (law g) threshold

/-- Mean score among admitted students in a finite Gaussian mixture. -/
def mixtureUpperTailMean
    (C : GaussianHazardCertificate)
    (weight : γ → ℝ) (law : γ → GaussianScaleLaw)
    (threshold : ℝ) : ℝ :=
  C.mixtureUpperTailMeanNumerator weight law threshold /
    C.api.mixtureTailMass weight law threshold

theorem mixtureUpperTailMean_mul_tailMass_eq_numerator
    (C : GaussianHazardCertificate)
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw}
    {threshold : ℝ}
    (hmass : 0 < C.api.mixtureTailMass weight law threshold) :
    C.mixtureUpperTailMean weight law threshold *
        C.api.mixtureTailMass weight law threshold =
      C.mixtureUpperTailMeanNumerator weight law threshold := by
  rw [mixtureUpperTailMean]
  exact div_mul_cancel₀ _ (ne_of_gt hmass)

end Mixture

end GaussianHazardCertificate

end

end Probability
end AppliedModelingLib
