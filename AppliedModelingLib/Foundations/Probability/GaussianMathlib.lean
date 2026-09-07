import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Hom.Set
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic
import AppliedModelingLib.Foundations.Probability.CDFContinuity
import AppliedModelingLib.Foundations.Probability.Gaussian
import AppliedModelingLib.Foundations.Probability.GaussianDerivatives
import AppliedModelingLib.Foundations.Probability.GaussianHazardInverse
import AppliedModelingLib.Foundations.Probability.GaussianMills
import AppliedModelingLib.Foundations.Probability.GaussianQuantile

/-!
# Mathlib-backed Gaussian facts

Reusable bridges from mathlib's real Gaussian measure API to the smaller
standard-normal interfaces used by admissions and testing formalizations.

## Main declarations

- `continuous_cdf_of_noAtoms`
- `standardGaussianMeasure`
- `gaussianReal_singleton_eq_zero`
- `gaussianReal_Ioc_pos`
- `gaussianReal_Ico_pos`
- `gaussianReal_Ioo_pos`
- `gaussianReal_Icc_pos`
- `GaussianScaleLaw.toMeasure_singleton_eq_zero`
- `GaussianScaleLaw.toMeasure_Ioc_pos`
- `GaussianScaleLaw.toMeasure_Ico_pos`
- `GaussianScaleLaw.toMeasure_Ioo_pos`
- `GaussianScaleLaw.toMeasure_Icc_pos`
- `standardGaussianCDF_neg_eq_one_sub`
- `standardGaussianDensity_mul_affine_eq`
- `standardGaussianDensity_hasDerivAt`
- `standardGaussianTail_eq_integral_Ioi`
- `standardGaussianDensity_mul_affine_integral_Iic`
- `standardGaussianDensity_mul_affine_integral_interval`
- `standardGaussian_firstMoment_affineCDF_integral_Iic_of_integrable`
- `standardGaussian_firstMoment_affineCDF_integral_Iic`
- `standardGaussian_firstMoment_affineCDF_integral_interval`
- `standardGaussianCDFAPI`
- `standardGaussianCDFOrderIso`
- `standardGaussianLowerTailMeanCertificate`
- `standardGaussian_normalCDF_mul_lowerTailMean_sub_tendsto_atBot`
- `standardGaussianHazardInverseCertificate`
- `standardGaussian_normalUpperTailMean_gt_threshold`
- `standardGaussian_toMeasure_Ico_threshold_normalUpperTailMean_pos`
- `standardGaussian_affineUpperTail_delta_lt_eventually_of_same_side_slope_order`
-/

open Filter MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal Real Topology

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-- The standard real Gaussian measure, as supplied by mathlib. -/
def standardGaussianMeasure : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

/-- The standard Gaussian CDF, using mathlib's CDF construction. -/
def standardGaussianCDF (x : ℝ) : ℝ :=
  ProbabilityTheory.cdf standardGaussianMeasure x

/-- The standard Gaussian density, using mathlib's PDF construction. -/
def standardGaussianDensity (x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x

private theorem standardGaussianVariance_ne_zero : (1 : ℝ≥0) ≠ 0 := by
  norm_num

private instance : IsProbabilityMeasure standardGaussianMeasure := by
  unfold standardGaussianMeasure
  infer_instance

private instance : NoAtoms standardGaussianMeasure := by
  unfold standardGaussianMeasure
  exact ProbabilityTheory.noAtoms_gaussianReal standardGaussianVariance_ne_zero

/-- The mathlib-backed standard Gaussian CDF is continuous. -/
theorem standardGaussianCDF_continuous : Continuous standardGaussianCDF := by
  unfold standardGaussianCDF
  exact continuous_cdf_of_noAtoms standardGaussianMeasure

/-- The mathlib-backed standard Gaussian CDF is monotone. -/
theorem standardGaussianCDF_mono : Monotone standardGaussianCDF := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.monotone_cdf standardGaussianMeasure

/-- Every nonempty half-open interval has positive standard Gaussian mass. -/
theorem standardGaussianMeasure_Ioc_pos {x y : ℝ} (hxy : x < y) :
    0 < standardGaussianMeasure (Ioc x y) := by
  unfold standardGaussianMeasure
  rw [ProbabilityTheory.gaussianReal_apply 0 standardGaussianVariance_ne_zero (Ioc x y)]
  rw [MeasureTheory.setLIntegral_pos_iff
    (ProbabilityTheory.measurable_gaussianPDF 0 (1 : ℝ≥0))]
  rw [ProbabilityTheory.support_gaussianPDF
    (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) standardGaussianVariance_ne_zero]
  rw [univ_inter, Real.volume_Ioc]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)

/-- Every nonempty half-open interval has positive mass under a nondegenerate Gaussian. -/
theorem gaussianReal_Ioc_pos (mean : ℝ) {variance : ℝ≥0}
    (hvariance : variance ≠ 0) {x y : ℝ} (hxy : x < y) :
    0 < ProbabilityTheory.gaussianReal mean variance (Ioc x y) := by
  rw [ProbabilityTheory.gaussianReal_apply mean hvariance (Ioc x y)]
  rw [MeasureTheory.setLIntegral_pos_iff
    (ProbabilityTheory.measurable_gaussianPDF mean variance)]
  rw [ProbabilityTheory.support_gaussianPDF
    (μ := mean) (v := variance) hvariance]
  rw [univ_inter, Real.volume_Ioc]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)

/-- Every nonempty left-closed, right-open interval has positive mass under a nondegenerate Gaussian. -/
theorem gaussianReal_Ico_pos (mean : ℝ) {variance : ℝ≥0}
    (hvariance : variance ≠ 0) {x y : ℝ} (hxy : x < y) :
    0 < ProbabilityTheory.gaussianReal mean variance (Ico x y) := by
  let mid : ℝ := (x + y) / 2
  have hxmid : x < mid := by
    dsimp [mid]
    linarith
  have hmidy : mid < y := by
    dsimp [mid]
    linarith
  have hpos : 0 < ProbabilityTheory.gaussianReal mean variance (Ioc x mid) :=
    gaussianReal_Ioc_pos mean hvariance hxmid
  exact lt_of_lt_of_le hpos
    (measure_mono (fun z hz => ⟨le_of_lt hz.1, lt_of_le_of_lt hz.2 hmidy⟩))

/-- Nondegenerate real Gaussian laws have no mass at a point. -/
theorem gaussianReal_singleton_eq_zero (mean : ℝ) {variance : ℝ≥0}
    (hvariance : variance ≠ 0) (x : ℝ) :
    ProbabilityTheory.gaussianReal mean variance ({x} : Set ℝ) = 0 := by
  haveI : NoAtoms (ProbabilityTheory.gaussianReal mean variance) :=
    ProbabilityTheory.noAtoms_gaussianReal hvariance
  exact measure_singleton x

/-- Every nonempty open interval has positive mass under a nondegenerate Gaussian. -/
theorem gaussianReal_Ioo_pos (mean : ℝ) {variance : ℝ≥0}
    (hvariance : variance ≠ 0) {x y : ℝ} (hxy : x < y) :
    0 < ProbabilityTheory.gaussianReal mean variance (Ioo x y) := by
  let mid : ℝ := (x + y) / 2
  have hxmid : x < mid := by
    dsimp [mid]
    linarith
  have hmidy : mid < y := by
    dsimp [mid]
    linarith
  have hpos : 0 < ProbabilityTheory.gaussianReal mean variance (Ioc x mid) :=
    gaussianReal_Ioc_pos mean hvariance hxmid
  exact lt_of_lt_of_le hpos
    (measure_mono (fun z hz => ⟨hz.1, lt_of_le_of_lt hz.2 hmidy⟩))

/-- Every nonempty closed interval has positive mass under a nondegenerate Gaussian. -/
theorem gaussianReal_Icc_pos (mean : ℝ) {variance : ℝ≥0}
    (hvariance : variance ≠ 0) {x y : ℝ} (hxy : x < y) :
    0 < ProbabilityTheory.gaussianReal mean variance (Icc x y) := by
  exact lt_of_lt_of_le (gaussianReal_Ioc_pos mean hvariance hxy)
    (measure_mono (fun z hz => ⟨le_of_lt hz.1, hz.2⟩))

namespace GaussianScaleLaw

/-- The mathlib variance parameter associated with a positive scale law. -/
def varianceNNReal (L : GaussianScaleLaw) : ℝ≥0 :=
  ⟨L.scale ^ 2, sq_nonneg L.scale⟩

theorem varianceNNReal_ne_zero (L : GaussianScaleLaw) :
    L.varianceNNReal ≠ 0 := by
  have hscale_sq_pos : 0 < L.scale ^ 2 :=
    sq_pos_of_ne_zero (ne_of_gt L.scale_pos)
  have hvariance_pos : (0 : ℝ≥0) < L.varianceNNReal := by
    rw [← NNReal.coe_lt_coe]
    simpa [varianceNNReal] using hscale_sq_pos
  exact ne_of_gt hvariance_pos

/-- The concrete mathlib Gaussian measure represented by a location-scale law. -/
def toMeasure (L : GaussianScaleLaw) : Measure ℝ :=
  ProbabilityTheory.gaussianReal L.mean L.varianceNNReal

instance toMeasure_isProbabilityMeasure (L : GaussianScaleLaw) :
    IsProbabilityMeasure L.toMeasure := by
  dsimp [toMeasure]
  infer_instance

instance toMeasure_noAtoms (L : GaussianScaleLaw) :
    NoAtoms L.toMeasure := by
  dsimp [toMeasure]
  exact ProbabilityTheory.noAtoms_gaussianReal L.varianceNNReal_ne_zero

/-- A location-scale Gaussian law has no mass at a point. -/
theorem toMeasure_singleton_eq_zero (L : GaussianScaleLaw) (x : ℝ) :
    L.toMeasure ({x} : Set ℝ) = 0 := by
  exact measure_singleton x

/-- Every nonempty half-open interval has positive mass under a location-scale Gaussian law. -/
theorem toMeasure_Ioc_pos (L : GaussianScaleLaw) {x y : ℝ} (hxy : x < y) :
    0 < L.toMeasure (Ioc x y) := by
  exact gaussianReal_Ioc_pos L.mean L.varianceNNReal_ne_zero hxy

/-- Every nonempty left-closed, right-open interval has positive mass under a location-scale Gaussian law. -/
theorem toMeasure_Ico_pos (L : GaussianScaleLaw) {x y : ℝ} (hxy : x < y) :
    0 < L.toMeasure (Ico x y) := by
  exact gaussianReal_Ico_pos L.mean L.varianceNNReal_ne_zero hxy

/-- Every nonempty open interval has positive mass under a location-scale Gaussian law. -/
theorem toMeasure_Ioo_pos (L : GaussianScaleLaw) {x y : ℝ} (hxy : x < y) :
    0 < L.toMeasure (Ioo x y) := by
  exact gaussianReal_Ioo_pos L.mean L.varianceNNReal_ne_zero hxy

/-- Every nonempty closed interval has positive mass under a location-scale Gaussian law. -/
theorem toMeasure_Icc_pos (L : GaussianScaleLaw) {x y : ℝ} (hxy : x < y) :
    0 < L.toMeasure (Icc x y) := by
  exact gaussianReal_Icc_pos L.mean L.varianceNNReal_ne_zero hxy

end GaussianScaleLaw

/-- The standard Gaussian measure gives positive mass to every nonempty open set. -/
instance standardGaussianMeasure_isOpenPosMeasure :
    Measure.IsOpenPosMeasure standardGaussianMeasure := by
  refine ⟨fun U hU hUne hzero => ?_⟩
  rcases hUne with ⟨x, hxU⟩
  rcases Metric.isOpen_iff.1 hU x hxU with ⟨ε, hε_pos, hball⟩
  let a : ℝ := x - ε / 2
  let b : ℝ := x + ε / 2
  have hab : a < b := by
    dsimp [a, b]
    linarith
  have hIoc_subset : Set.Ioc a b ⊆ U := by
    intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hleft : x - ε / 2 < y := by
      simpa [a] using hy.1
    have hright : y ≤ x + ε / 2 := by
      simpa [b] using hy.2
    have h_abs : |y - x| ≤ ε / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hhalf_lt : ε / 2 < ε := by
      linarith
    exact lt_of_le_of_lt h_abs hhalf_lt
  have hpos : 0 < standardGaussianMeasure (Set.Ioc a b) :=
    standardGaussianMeasure_Ioc_pos hab
  exact (ne_of_gt (hpos.trans_le (measure_mono hIoc_subset))) hzero

/-- The mathlib-backed standard Gaussian CDF is strictly monotone. -/
theorem standardGaussianCDF_strictMono : StrictMono standardGaussianCDF := by
  intro x y hxy
  have hmass : 0 < standardGaussianMeasure (Ioc x y) :=
    standardGaussianMeasure_Ioc_pos hxy
  have hmeasure_cdf :
      (ProbabilityTheory.cdf standardGaussianMeasure).measure (Ioc x y) =
        standardGaussianMeasure (Ioc x y) := by
    rw [ProbabilityTheory.measure_cdf standardGaussianMeasure]
  have hst := (ProbabilityTheory.cdf standardGaussianMeasure).measure_Ioc x y
  have hofReal_pos :
      0 < ENNReal.ofReal (standardGaussianCDF y - standardGaussianCDF x) := by
    change
      0 < ENNReal.ofReal
        (ProbabilityTheory.cdf standardGaussianMeasure y -
          ProbabilityTheory.cdf standardGaussianMeasure x)
    rw [← hst, hmeasure_cdf]
    exact hmass
  have hsub_pos : 0 < standardGaussianCDF y - standardGaussianCDF x :=
    ENNReal.ofReal_pos.mp hofReal_pos
  linarith

/-- The standard Gaussian measure is symmetric around zero. -/
theorem standardGaussianMeasure_map_neg :
    standardGaussianMeasure.map (fun x : ℝ => -x) = standardGaussianMeasure := by
  unfold standardGaussianMeasure
  simpa using
    (ProbabilityTheory.gaussianReal_map_neg
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))

/-- The mathlib-backed standard Gaussian CDF takes value `1 / 2` at zero. -/
theorem standardGaussianCDF_zero_eq_half :
    standardGaussianCDF 0 = (1 / 2 : ℝ) := by
  unfold standardGaussianCDF
  rw [ProbabilityTheory.cdf_eq_real]
  have hIicIci_measure :
      standardGaussianMeasure (Iic (0 : ℝ)) =
        standardGaussianMeasure (Ici (0 : ℝ)) := by
    calc
      standardGaussianMeasure (Iic (0 : ℝ))
          = (standardGaussianMeasure.map (fun x : ℝ => -x)) (Iic (0 : ℝ)) := by
              rw [standardGaussianMeasure_map_neg]
      _ = standardGaussianMeasure
          ((fun x : ℝ => -x) ⁻¹' Iic (0 : ℝ)) := by
              rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
      _ = standardGaussianMeasure (Ici (0 : ℝ)) := by
              congr 1
              ext x
              simp
  have hIicIci_real :
      standardGaussianMeasure.real (Iic (0 : ℝ)) =
        standardGaussianMeasure.real (Ici (0 : ℝ)) := by
    simp [measureReal_def, hIicIci_measure]
  have hIciIoi_real :
      standardGaussianMeasure.real (Ici (0 : ℝ)) =
        standardGaussianMeasure.real (Ioi (0 : ℝ)) := by
    simpa using
      (MeasureTheory.measureReal_congr
        (μ := standardGaussianMeasure)
        ((MeasureTheory.Ioi_ae_eq_Ici
          (μ := standardGaussianMeasure) (a := (0 : ℝ))).symm))
  have hsym :
      standardGaussianMeasure.real (Iic (0 : ℝ)) =
        standardGaussianMeasure.real (Ioi (0 : ℝ)) :=
    hIicIci_real.trans hIciIoi_real
  have hcompl :
      standardGaussianMeasure.real (Ioi (0 : ℝ)) =
        1 - standardGaussianMeasure.real (Iic (0 : ℝ)) := by
    simpa using
      (MeasureTheory.probReal_compl_eq_one_sub
        (μ := standardGaussianMeasure) (s := Iic (0 : ℝ)) measurableSet_Iic)
  linarith

/-- Symmetry of the mathlib-backed standard Gaussian CDF. -/
theorem standardGaussianCDF_neg_eq_one_sub (z : ℝ) :
    standardGaussianCDF (-z) = 1 - standardGaussianCDF z := by
  unfold standardGaussianCDF
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  have hIicIci_measure :
      standardGaussianMeasure (Iic (-z)) =
        standardGaussianMeasure (Ici z) := by
    calc
      standardGaussianMeasure (Iic (-z))
          = (standardGaussianMeasure.map (fun x : ℝ => -x)) (Iic (-z)) := by
              rw [standardGaussianMeasure_map_neg]
      _ = standardGaussianMeasure
          ((fun x : ℝ => -x) ⁻¹' Iic (-z)) := by
              rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
      _ = standardGaussianMeasure (Ici z) := by
              congr 1
              ext x
              simp
  have hIicIci_real :
      standardGaussianMeasure.real (Iic (-z)) =
        standardGaussianMeasure.real (Ici z) := by
    simp [measureReal_def, hIicIci_measure]
  have hIciIoi_real :
      standardGaussianMeasure.real (Ici z) =
        standardGaussianMeasure.real (Ioi z) := by
    simpa using
      (MeasureTheory.measureReal_congr
        (μ := standardGaussianMeasure)
        ((MeasureTheory.Ioi_ae_eq_Ici
          (μ := standardGaussianMeasure) (a := z)).symm))
  have hcompl :
      standardGaussianMeasure.real (Ioi z) =
        1 - standardGaussianMeasure.real (Iic z) := by
    simpa using
      (MeasureTheory.probReal_compl_eq_one_sub
        (μ := standardGaussianMeasure) (s := Iic z) measurableSet_Iic)
  linarith

/-- The mathlib-backed standard Gaussian density is nonnegative. -/
theorem standardGaussianDensity_nonneg (z : ℝ) :
    0 ≤ standardGaussianDensity z := by
  unfold standardGaussianDensity
  exact ProbabilityTheory.gaussianPDFReal_nonneg 0 (1 : ℝ≥0) z

/-- The mathlib-backed standard Gaussian density is strictly positive. -/
theorem standardGaussianDensity_pos (z : ℝ) :
    0 < standardGaussianDensity z := by
  unfold standardGaussianDensity
  exact ProbabilityTheory.gaussianPDFReal_pos
    0 (1 : ℝ≥0) z standardGaussianVariance_ne_zero

/--
The mathlib-backed standard Gaussian density in elementary normalized form.
-/
theorem standardGaussianDensity_eq_mills_integrand (z : ℝ) :
    standardGaussianDensity z =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2) := by
  unfold standardGaussianDensity
  rw [ProbabilityTheory.gaussianPDFReal_def]
  simp

/-- Symmetry of the mathlib-backed standard Gaussian density. -/
theorem standardGaussianDensity_neg (z : ℝ) :
    standardGaussianDensity (-z) = standardGaussianDensity z := by
  rw [standardGaussianDensity_eq_mills_integrand,
    standardGaussianDensity_eq_mills_integrand]
  ring_nf

/-- The standard Gaussian density is integrable on the real line. -/
theorem standardGaussianDensity_integrable :
    Integrable standardGaussianDensity := by
  simpa [standardGaussianDensity] using
    (ProbabilityTheory.integrable_gaussianPDFReal 0 (1 : ℝ≥0))

/-- The normalizing constant in the standard Gaussian density is nonnegative. -/
theorem standardGaussianDensity_normConst_nonneg :
    0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  exact inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi))

/-- The standard Gaussian density is bounded by its normalizing constant. -/
theorem standardGaussianDensity_le_normConst (z : ℝ) :
    standardGaussianDensity z ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [standardGaussianDensity_eq_mills_integrand]
  have hexp_le : Real.exp (-(z ^ 2) / 2) ≤ 1 := by
    simpa using
      (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z] :
        -(z ^ 2) / 2 ≤ (0 : ℝ)))
  exact mul_le_of_le_one_right standardGaussianDensity_normConst_nonneg hexp_le

/--
Product-density completion of squares for the affine Owen integrand.

This is the algebraic density identity behind the first-moment version of
Owen's formula:
`phi(z) * phi(A * sqrt(1+c^2) + c z)
 = phi(A) * phi(sqrt(1+c^2) z + A c)`.
-/
theorem standardGaussianDensity_mul_affine_eq
    (c A z : ℝ) :
    standardGaussianDensity z *
        standardGaussianDensity (A * Real.sqrt (1 + c ^ 2) + c * z) =
      standardGaussianDensity A *
        standardGaussianDensity (Real.sqrt (1 + c ^ 2) * z + A * c) := by
  let normConst : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  let D : ℝ := Real.sqrt (1 + c ^ 2)
  have hDsq : D ^ 2 = 1 + c ^ 2 := by
    dsimp [D]
    exact Real.sq_sqrt (by positivity)
  have hexp :
      Real.exp (-(z ^ 2) / 2) *
          Real.exp (-((A * D + c * z) ^ 2) / 2) =
        Real.exp (-(A ^ 2) / 2) *
          Real.exp (-((D * z + A * c) ^ 2) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    nlinarith [hDsq]
  rw [standardGaussianDensity_eq_mills_integrand,
    standardGaussianDensity_eq_mills_integrand,
    standardGaussianDensity_eq_mills_integrand,
    standardGaussianDensity_eq_mills_integrand]
  change
    normConst * Real.exp (-(z ^ 2) / 2) *
        (normConst * Real.exp (-((A * D + c * z) ^ 2) / 2)) =
      normConst * Real.exp (-(A ^ 2) / 2) *
        (normConst * Real.exp (-((D * z + A * c) ^ 2) / 2))
  calc
    normConst * Real.exp (-(z ^ 2) / 2) *
        (normConst * Real.exp (-((A * D + c * z) ^ 2) / 2))
        =
      normConst * normConst *
        (Real.exp (-(z ^ 2) / 2) *
          Real.exp (-((A * D + c * z) ^ 2) / 2)) := by
          ring
    _ =
      normConst * normConst *
        (Real.exp (-(A ^ 2) / 2) *
          Real.exp (-((D * z + A * c) ^ 2) / 2)) := by
          rw [hexp]
    _ =
      normConst * Real.exp (-(A ^ 2) / 2) *
        (normConst * Real.exp (-((D * z + A * c) ^ 2) / 2)) := by
          ring

/-- Derivative of the mathlib-backed standard Gaussian density. -/
theorem standardGaussianDensity_hasDerivAt (z : ℝ) :
    HasDerivAt standardGaussianDensity
      (-z * standardGaussianDensity z) z := by
  let normConst : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hinner :
      HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-z) z := by
    convert ((hasDerivAt_id z).pow 2).neg.div_const 2 using 1
    · simp [id_eq]
      ring
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2))
        (-(Real.exp (-(z ^ 2) / 2) * z)) z := by
    simpa using hinner.exp
  have hscaled :
      HasDerivAt
        (fun x : ℝ => normConst * Real.exp (-(x ^ 2) / 2))
        (normConst * (-(Real.exp (-(z ^ 2) / 2) * z))) z :=
    hexp.const_mul normConst
  have hstd :
      HasDerivAt standardGaussianDensity
        (normConst * (-(Real.exp (-(z ^ 2) / 2) * z))) z :=
    hscaled.congr_of_eventuallyEq
      (Eventually.of_forall fun x => by
      rw [standardGaussianDensity_eq_mills_integrand])
  convert hstd using 1
  rw [standardGaussianDensity_eq_mills_integrand]
  ring

/-- The mathlib-backed standard Gaussian CDF is nonnegative. -/
theorem standardGaussianCDF_nonneg (z : ℝ) :
    0 ≤ standardGaussianCDF z := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.cdf_nonneg standardGaussianMeasure z

/-- The mathlib-backed standard Gaussian CDF is bounded by one. -/
theorem standardGaussianCDF_le_one (z : ℝ) :
    standardGaussianCDF z ≤ 1 := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.cdf_le_one standardGaussianMeasure z

/-- The mathlib-backed standard Gaussian CDF is strictly positive. -/
theorem standardGaussianCDF_pos (z : ℝ) :
    0 < standardGaussianCDF z := by
  have hmono := standardGaussianCDF_strictMono
    (show z - 1 < z by linarith)
  have hnonneg := standardGaussianCDF_nonneg (z - 1)
  linarith

/-- The mathlib-backed standard Gaussian CDF is strictly below one. -/
theorem standardGaussianCDF_lt_one (z : ℝ) :
    standardGaussianCDF z < 1 := by
  have hmono := standardGaussianCDF_strictMono
    (show z < z + 1 by linarith)
  have hle := standardGaussianCDF_le_one (z + 1)
  linarith

/-- The mathlib-backed standard Gaussian upper tail is strictly positive. -/
theorem standardGaussianTail_pos (z : ℝ) :
    0 < 1 - standardGaussianCDF z := by
  have hlt := standardGaussianCDF_lt_one z
  linarith

/-- The mathlib-backed standard Gaussian upper tail as a density integral. -/
theorem standardGaussianTail_eq_integral_Ioi (z : ℝ) :
    1 - standardGaussianCDF z =
      ∫ x in Ioi z, standardGaussianDensity x := by
  have hcompl :
      standardGaussianMeasure.real (Ioi z) = 1 - standardGaussianCDF z := by
    simpa [standardGaussianCDF, ProbabilityTheory.cdf_eq_real, compl_Iic] using
      (MeasureTheory.probReal_compl_eq_one_sub
        (μ := standardGaussianMeasure) (s := Iic z) measurableSet_Iic)
  have hmeasure :
      standardGaussianMeasure (Ioi z) =
        ENNReal.ofReal (∫ x in Ioi z, standardGaussianDensity x) := by
    unfold standardGaussianMeasure standardGaussianDensity
    simpa using
      (ProbabilityTheory.gaussianReal_apply_eq_integral
        0 standardGaussianVariance_ne_zero (Ioi z))
  have htail_integral :
      standardGaussianMeasure.real (Ioi z) =
        ∫ x in Ioi z, standardGaussianDensity x := by
    rw [measureReal_def, hmeasure]
    rw [ENNReal.toReal_ofReal]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun x _hx => standardGaussianDensity_nonneg x)
  rw [← hcompl, htail_integral]

private theorem integral_comp_add_right_Ioi_real (f : ℝ → ℝ) (a d : ℝ) :
    (∫ x in Ioi a, f (x + d)) =
      ∫ y in Ioi (a + d), f y := by
  have h :=
    (measurePreserving_add_right (volume : Measure ℝ) d).setIntegral_image_emb
      (MeasurableEquiv.addRight d).measurableEmbedding f (Ioi a)
  simpa [image_add_const_Ioi] using h.symm

private theorem integral_comp_add_right_Iic_real (f : ℝ → ℝ) (a d : ℝ) :
    (∫ x in Iic a, f (x + d)) =
      ∫ y in Iic (a + d), f y := by
  have himage : (fun x : ℝ => x + d) '' Iic a = Iic (a + d) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using add_le_add_right hx d
    · intro hy
      refine ⟨y - d, ?_, by ring⟩
      change y - d ≤ a
      have hy' : y ≤ a + d := hy
      linarith
  have h :=
    (measurePreserving_add_right (volume : Measure ℝ) d).setIntegral_image_emb
      (MeasurableEquiv.addRight d).measurableEmbedding f (Iic a)
  simpa [himage] using h.symm

private theorem integral_comp_mul_left_Iic_real (f : ℝ → ℝ) (a : ℝ)
    {b : ℝ} (hb : 0 < b) :
    (∫ x in Iic a, f (b * x)) =
      b⁻¹ * ∫ y in Iic (b * a), f y := by
  suffices (∫ x in Iic a, f (b * x)) =
      b⁻¹ • ∫ y in Iic (b * a), f y by
    simpa [smul_eq_mul] using this
  have hmeas : ∀ c : ℝ, MeasurableSet (Iic c) := fun _ => measurableSet_Iic
  rw [← integral_indicator (hmeas a), ← integral_indicator (hmeas (b * a)),
    ← abs_of_pos (inv_pos.mpr hb), ← Measure.integral_comp_mul_left]
  congr
  ext1 x
  rw [← indicator_comp_right, preimage_const_mul_Iic₀ _ hb,
    mul_div_cancel_left₀ _ hb.ne', Function.comp_def]

/--
Affine upper-tail integral of the Gaussian product appearing in Owen's
first-moment calculation.
-/
theorem standardGaussianDensity_mul_affine_integral_Ioi
    (c A B : ℝ) :
    (∫ z in Ioi B,
        standardGaussianDensity z *
          standardGaussianDensity
            (A * Real.sqrt (1 + c ^ 2) + c * z)) =
      standardGaussianDensity A * (Real.sqrt (1 + c ^ 2))⁻¹ *
        (1 - standardGaussianCDF
          (Real.sqrt (1 + c ^ 2) * B + A * c)) := by
  let D : ℝ := Real.sqrt (1 + c ^ 2)
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hpoint :
      EqOn
        (fun z : ℝ =>
          standardGaussianDensity z *
            standardGaussianDensity (A * D + c * z))
        (fun z : ℝ =>
          standardGaussianDensity A *
            standardGaussianDensity (D * z + A * c))
        (Ioi B) := by
    intro z _hz
    exact standardGaussianDensity_mul_affine_eq c A z
  have hscale :
      (∫ z in Ioi B, standardGaussianDensity (D * z + A * c)) =
        D⁻¹ * ∫ y in Ioi (D * B + A * c),
          standardGaussianDensity y := by
    have hmul :=
      MeasureTheory.integral_comp_mul_left_Ioi
        (g := fun y : ℝ => standardGaussianDensity (y + A * c))
        (a := B) hDpos
    have hshift :
        (∫ y in Ioi (D * B),
            standardGaussianDensity (y + A * c)) =
          ∫ y in Ioi (D * B + A * c),
            standardGaussianDensity y :=
      integral_comp_add_right_Ioi_real standardGaussianDensity (D * B) (A * c)
    calc
      (∫ z in Ioi B, standardGaussianDensity (D * z + A * c))
          =
        (∫ z in Ioi B,
          (fun y : ℝ => standardGaussianDensity (y + A * c)) (D * z)) := by
          rfl
      _ =
        D⁻¹ * ∫ y in Ioi (D * B),
          standardGaussianDensity (y + A * c) := by
          simpa [smul_eq_mul] using hmul
      _ =
        D⁻¹ * ∫ y in Ioi (D * B + A * c),
          standardGaussianDensity y := by
          rw [hshift]
  calc
    (∫ z in Ioi B,
        standardGaussianDensity z *
          standardGaussianDensity
            (A * Real.sqrt (1 + c ^ 2) + c * z))
        =
      ∫ z in Ioi B,
        standardGaussianDensity A *
          standardGaussianDensity (D * z + A * c) := by
        dsimp [D]
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpoint
    _ =
      standardGaussianDensity A *
        ∫ z in Ioi B, standardGaussianDensity (D * z + A * c) := by
        rw [integral_const_mul]
    _ =
      standardGaussianDensity A * (D⁻¹ *
        ∫ y in Ioi (D * B + A * c), standardGaussianDensity y) := by
        rw [hscale]
    _ =
      standardGaussianDensity A * D⁻¹ *
        (1 - standardGaussianCDF (D * B + A * c)) := by
        rw [← standardGaussianTail_eq_integral_Ioi]
        ring
    _ =
      standardGaussianDensity A * (Real.sqrt (1 + c ^ 2))⁻¹ *
        (1 - standardGaussianCDF
          (Real.sqrt (1 + c ^ 2) * B + A * c)) := by
        rfl

/--
The mathlib-backed standard Gaussian upper tail equals the normalized
unnormalized tail integral used by the Mills ratio.
-/
theorem standardGaussianTail_eq_const_mul_millsTail (z : ℝ) :
    1 - standardGaussianCDF z =
      (Real.sqrt (2 * Real.pi))⁻¹ * gaussianMillsTail z := by
  have hcompl :
      standardGaussianMeasure.real (Ioi z) = 1 - standardGaussianCDF z := by
    simpa [standardGaussianCDF, ProbabilityTheory.cdf_eq_real, compl_Iic] using
      (MeasureTheory.probReal_compl_eq_one_sub
        (μ := standardGaussianMeasure) (s := Iic z) measurableSet_Iic)
  have hmeasure :
      standardGaussianMeasure (Ioi z) =
        ENNReal.ofReal (∫ x in Ioi z, standardGaussianDensity x) := by
    unfold standardGaussianMeasure standardGaussianDensity
    simpa using
      (ProbabilityTheory.gaussianReal_apply_eq_integral
        0 standardGaussianVariance_ne_zero (Ioi z))
  have htail_integral :
      standardGaussianMeasure.real (Ioi z) =
        ∫ x in Ioi z, standardGaussianDensity x := by
    rw [measureReal_def, hmeasure]
    rw [ENNReal.toReal_ofReal]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun x _hx => standardGaussianDensity_nonneg x)
  have hintegral :
      (∫ x in Ioi z, standardGaussianDensity x) =
        (Real.sqrt (2 * Real.pi))⁻¹ * gaussianMillsTail z := by
    calc
      (∫ x in Ioi z, standardGaussianDensity x)
          = ∫ x in Ioi z,
              (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
                (fun x _hx => standardGaussianDensity_eq_mills_integrand x)
      _ = (Real.sqrt (2 * Real.pi))⁻¹ *
            ∫ x in Ioi z, Real.exp (-(x ^ 2) / 2) := by
              rw [integral_const_mul]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * gaussianMillsTail z := by
              rfl
  rw [← hcompl, htail_integral, hintegral]

/-- The mathlib-backed standard Gaussian CDF tends to zero at `-∞`. -/
theorem standardGaussianCDF_tendsto_atBot :
    Tendsto standardGaussianCDF atBot (𝓝 0) := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.tendsto_cdf_atBot standardGaussianMeasure

/-- The mathlib-backed standard Gaussian CDF tends to one at `+∞`. -/
theorem standardGaussianCDF_tendsto_atTop :
    Tendsto standardGaussianCDF atTop (𝓝 1) := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.tendsto_cdf_atTop standardGaussianMeasure

/--
Mills upper bound for the standard Gaussian left tail.

For `t > 0`, `Phi(-t)` is bounded above by the usual density-over-argument
quantity.
-/
theorem standardGaussianCDF_neg_lt_mills_upper {t : ℝ} (ht : 0 < t) :
    standardGaussianCDF (-t) <
      (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-(t ^ 2) / 2) / t) := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hc_pos : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr
      (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi))
  have htail_lt :
      gaussianMillsTail t < Real.exp (-(t ^ 2) / 2) / t := by
    simpa [gaussianMillsUpperGap, sub_pos] using
      gaussianMillsUpperGap_pos_of_pos ht
  calc
    standardGaussianCDF (-t) = 1 - standardGaussianCDF t := by
      rw [standardGaussianCDF_neg_eq_one_sub]
    _ = c * gaussianMillsTail t := by
      dsimp [c]
      rw [standardGaussianTail_eq_const_mul_millsTail]
    _ < c * (Real.exp (-(t ^ 2) / 2) / t) :=
      mul_lt_mul_of_pos_left htail_lt hc_pos

/--
Sampford's lower Mills comparison gives a lower bound for the standard
Gaussian left tail.
-/
theorem standardGaussianCDF_neg_mills_lower_lt {t : ℝ} :
    (Real.sqrt (2 * Real.pi))⁻¹ *
        (gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)) <
      standardGaussianCDF (-t) := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hc_pos : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr
      (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi))
  have hlower := gaussianSampfordLowerComparison_lt_millsRatio t
  have hmul :=
    mul_lt_mul_of_pos_right hlower (Real.exp_pos (-(t ^ 2) / 2))
  have htail :
      gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2) <
        gaussianMillsTail t := by
    unfold gaussianMillsRatio at hmul
    calc
      gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)
          < (Real.exp (t ^ 2 / 2) * gaussianMillsTail t) *
              Real.exp (-(t ^ 2) / 2) := hmul
      _ = gaussianMillsTail t := by
        calc
          (Real.exp (t ^ 2 / 2) * gaussianMillsTail t) *
              Real.exp (-(t ^ 2) / 2)
              =
            gaussianMillsTail t *
              (Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2) / 2)) := by
                ring
          _ = gaussianMillsTail t := by
            rw [← Real.exp_add]
            have hsum : t ^ 2 / 2 + -(t ^ 2) / 2 = 0 := by ring
            rw [hsum, Real.exp_zero, mul_one]
  calc
    c * (gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2))
        < c * gaussianMillsTail t := mul_lt_mul_of_pos_left htail hc_pos
    _ = 1 - standardGaussianCDF t := by
      dsimp [c]
      rw [standardGaussianTail_eq_const_mul_millsTail]
    _ = standardGaussianCDF (-t) := by
      rw [standardGaussianCDF_neg_eq_one_sub]

/--
Pointwise left-tail comparison used to bootstrap eventual dominance: if the
quadratic exponential factor is already below `eps`, then
`Phi(-lambda*t) < eps * Phi(-t)`.
-/
theorem standardGaussianCDF_neg_const_mul_lt_mul_neg_of_exp_small
    {lambda eps t : ℝ} (hlambda : 1 < lambda) (heps : 0 < eps)
    (ht : 1 ≤ t)
    (hsmall :
      (2 / lambda) *
          Real.exp (-(((lambda ^ 2 - 1) / 2) * t ^ 2)) <
        eps) :
    standardGaussianCDF (-(lambda * t)) <
      eps * standardGaussianCDF (-t) := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  let a : ℝ := (1 / (2 * t)) * Real.exp (-(t ^ 2) / 2)
  let b : ℝ := Real.exp (-((lambda * t) ^ 2) / 2) / (lambda * t)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr
      (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi))
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hlambda_pos : 0 < lambda := lt_trans zero_lt_one hlambda
  have hlt_pos : 0 < lambda * t := mul_pos hlambda_pos ht_pos
  have hupper := standardGaussianCDF_neg_lt_mills_upper hlt_pos
  have hupper_c :
      standardGaussianCDF (-(lambda * t)) < c * b := by
    simpa [c, b] using hupper
  have hlower := standardGaussianCDF_neg_mills_lower_lt (t := t)
  have hlower_c :
      c * (gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)) <
        standardGaussianCDF (-t) := by
    simpa [c] using hlower
  let L := gaussianSampfordLowerComparison t
  have hL_lower : 1 / (2 * t) < L := by
    have hquad :=
      gaussianSampfordLowerComparison_sq_add_one_mul_gt_arg ht_pos
    have hden_pos : 0 < t ^ 2 + 1 := by nlinarith [sq_nonneg t]
    have hdiv : t / (t ^ 2 + 1) < L := by
      rw [div_lt_iff₀ hden_pos]
      simpa [L, mul_comm] using hquad
    have hhalf : 1 / (2 * t) ≤ t / (t ^ 2 + 1) := by
      have hden1 : 0 < 2 * t := by positivity
      have hden2 : 0 < t ^ 2 + 1 := by nlinarith [sq_nonneg t]
      rw [div_le_div_iff₀ hden1 hden2]
      nlinarith [ht, sq_nonneg t]
    exact lt_of_le_of_lt hhalf hdiv
  have hlower_simple : c * a < standardGaussianCDF (-t) := by
    have hmulL :
        (1 / (2 * t)) * Real.exp (-(t ^ 2) / 2) <
          L * Real.exp (-(t ^ 2) / 2) :=
      mul_lt_mul_of_pos_right hL_lower (Real.exp_pos _)
    have h := (mul_lt_mul_of_pos_left hmulL hc_pos).trans hlower_c
    simpa [a, L] using h
  have hcore : b < eps * a := by
    have hpos : 0 < a := by
      dsimp [a]
      positivity
    have hmul := mul_lt_mul_of_pos_right hsmall hpos
    calc
      b =
          ((2 / lambda) *
              Real.exp (-(((lambda ^ 2 - 1) / 2) * t ^ 2)) *
            a) := by
            dsimp [a, b]
            have hexp :
                Real.exp (-((lambda * t) ^ 2) / 2) =
                  Real.exp (-(((lambda ^ 2 - 1) / 2) * t ^ 2)) *
                    Real.exp (-(t ^ 2) / 2) := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [hexp]
            field_simp [hlambda_pos.ne', ht_pos.ne']
      _ < eps * a := hmul
  refine hupper_c.trans ?_
  refine (mul_lt_mul_of_pos_left hcore hc_pos).trans ?_
  rw [show c * (eps * a) = eps * (c * a) by ring]
  exact mul_lt_mul_of_pos_left hlower_simple heps

/--
Gaussian left-tail dominance: for any `lambda > 1`,
`Phi(-lambda*t)` is eventually smaller than any positive multiple of
`Phi(-t)`.
-/
theorem standardGaussianCDF_neg_const_mul_lt_mul_neg_eventually
    {lambda eps : ℝ} (hlambda : 1 < lambda) (heps : 0 < eps) :
    ∀ᶠ t in atTop,
      standardGaussianCDF (-(lambda * t)) <
        eps * standardGaussianCDF (-t) := by
  let c : ℝ := (lambda ^ 2 - 1) / 2
  have hc_pos : 0 < c := by
    dsimp [c]
    nlinarith [hlambda]
  have harg : Tendsto (fun t : ℝ => -c * t ^ 2) atTop atBot := by
    exact tendsto_neg_const_mul_pow_atTop (n := 2) (by norm_num) (by linarith)
  have hdecay :
      Tendsto
        (fun t : ℝ => (2 / lambda) * Real.exp (-c * t ^ 2))
        atTop (nhds 0) := by
    have hexp :
        Tendsto (fun t : ℝ => Real.exp (-c * t ^ 2))
          atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp harg
    simpa using (tendsto_const_nhds (x := 2 / lambda)).mul hexp
  have hsmall_ev :
      ∀ᶠ t in atTop,
        (2 / lambda) * Real.exp (-c * t ^ 2) < eps :=
    hdecay.eventually (eventually_lt_nhds heps)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall_ev] with t ht hsmall
  exact
    standardGaussianCDF_neg_const_mul_lt_mul_neg_of_exp_small
      hlambda heps ht (by simpa [c] using hsmall)

/--
Affine left-tail dominance.  If the first affine standardized cutoff has the
larger positive skill slope, then its standard Gaussian left-tail CDF is
eventually smaller than any positive multiple of the slower affine left tail.
-/
theorem standardGaussianCDF_affine_leftTail_lt_mul_eventually_of_slope_lt
    {interceptFast slopeFast interceptSlow slopeSlow eps : ℝ}
    (hslopeSlow_pos : 0 < slopeSlow) (hslope : slopeSlow < slopeFast)
    (heps : 0 < eps) :
    ∀ᶠ q in atTop,
      standardGaussianCDF (interceptFast - slopeFast * q) <
        eps * standardGaussianCDF (interceptSlow - slopeSlow * q) := by
  let lambda : ℝ := (slopeFast + slopeSlow) / (2 * slopeSlow)
  have hlambda_gt_one : 1 < lambda := by
    dsimp [lambda]
    rw [lt_div_iff₀ (by positivity : 0 < 2 * slopeSlow)]
    nlinarith
  have hlambda_slope_lt : lambda * slopeSlow < slopeFast := by
    dsimp [lambda]
    field_simp [hslopeSlow_pos.ne']
    nlinarith
  have hslow_atTop :
      Tendsto (fun q : ℝ => slopeSlow * q - interceptSlow) atTop atTop := by
    have hmul :
        Tendsto (fun q : ℝ => slopeSlow * q + (-interceptSlow))
          atTop atTop :=
      ((Filter.tendsto_const_mul_atTop_of_pos hslopeSlow_pos).2
          Filter.tendsto_id).atTop_add
        tendsto_const_nhds
    simpa [sub_eq_add_neg] using hmul
  have htail_q :
      ∀ᶠ q in atTop,
        standardGaussianCDF (-(lambda * (slopeSlow * q - interceptSlow))) <
          eps * standardGaussianCDF (-(slopeSlow * q - interceptSlow)) := by
    exact hslow_atTop.eventually
      (standardGaussianCDF_neg_const_mul_lt_mul_neg_eventually
        hlambda_gt_one heps)
  obtain ⟨q0, horder⟩ :=
    StandardGaussianDerivativeAPI.exists_eventual_affineStandardized_lt_of_slope_lt
      (interceptFast := interceptFast) (slopeFast := slopeFast)
      (interceptSlow := lambda * interceptSlow)
      (slopeSlow := lambda * slopeSlow)
      hlambda_slope_lt
  filter_upwards [htail_q, eventually_gt_atTop q0] with q htailq hq
  have hstd :
      interceptFast - slopeFast * q <
        lambda * interceptSlow - (lambda * slopeSlow) * q :=
    horder q hq
  have hle :
      interceptFast - slopeFast * q ≤
        -(lambda * (slopeSlow * q - interceptSlow)) := by
    have heq :
        -(lambda * (slopeSlow * q - interceptSlow)) =
          lambda * interceptSlow - (lambda * slopeSlow) * q := by
      ring
    rw [heq]
    exact le_of_lt hstd
  have hcdf_le := standardGaussianCDF_mono hle
  have htailq' :
      standardGaussianCDF (-(lambda * (slopeSlow * q - interceptSlow))) <
        eps * standardGaussianCDF (interceptSlow - slopeSlow * q) := by
    simpa [sub_eq_add_neg] using htailq
  exact lt_of_le_of_lt hcdf_le htailq'

/-- Every probability in `(0,1)` is hit by the standard Gaussian CDF. -/
theorem standardGaussianCDF_mem_range_of_mem_Ioo {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    p ∈ Set.range standardGaussianCDF := by
  exact mem_range_of_exists_le_of_exists_ge standardGaussianCDF_continuous
    (by
      have hlt :
          ∀ᶠ x in atBot, standardGaussianCDF x < p :=
        standardGaussianCDF_tendsto_atBot.eventually
          (eventually_lt_nhds hp.1)
      rcases hlt.exists with ⟨x, hx⟩
      exact ⟨x, le_of_lt hx⟩)
    (by
      have hgt :
          ∀ᶠ x in atTop, p < standardGaussianCDF x :=
        standardGaussianCDF_tendsto_atTop.eventually
          (eventually_gt_nhds hp.2)
      rcases hgt.exists with ⟨x, hx⟩
      exact ⟨x, le_of_lt hx⟩)

/-- The image of the standard Gaussian CDF is exactly `(0,1)`. -/
theorem standardGaussianCDF_image_univ :
    standardGaussianCDF '' (Set.univ : Set ℝ) = Ioo (0 : ℝ) 1 := by
  ext p
  constructor
  · rintro ⟨x, _hx, rfl⟩
    exact ⟨standardGaussianCDF_pos x, standardGaussianCDF_lt_one x⟩
  · intro hp
    rcases standardGaussianCDF_mem_range_of_mem_Ioo hp with ⟨x, hx⟩
    exact ⟨x, mem_univ x, hx⟩

/--
The standard Gaussian CDF as an order isomorphism from `ℝ` to probabilities in
`(0,1)`.
-/
def standardGaussianCDFOrderIso : ℝ ≃o Ioo (0 : ℝ) 1 :=
  (standardGaussianCDF_strictMono.orderIso standardGaussianCDF).trans
    (OrderIso.setCongr _ _
      (by simpa [Set.image_univ] using standardGaussianCDF_image_univ))

/-- The true standard-normal quantile on probabilities in `(0,1)`. -/
def standardGaussianQuantileIoo (p : Ioo (0 : ℝ) 1) : ℝ :=
  standardGaussianCDFOrderIso.symm p

@[simp] theorem standardGaussianCDF_quantileIoo
    (p : Ioo (0 : ℝ) 1) :
    standardGaussianCDF (standardGaussianQuantileIoo p) = p := by
  exact Subtype.ext_iff.mp
    (standardGaussianCDFOrderIso.apply_symm_apply p)

@[simp] theorem standardGaussianQuantileIoo_cdf (z : ℝ) :
    standardGaussianQuantileIoo
      ⟨standardGaussianCDF z,
        standardGaussianCDF_pos z, standardGaussianCDF_lt_one z⟩ = z := by
  exact standardGaussianCDFOrderIso.symm_apply_apply z

/-- The true standard-normal quantile is monotone on `(0,1)`. -/
theorem standardGaussianQuantileIoo_mono :
    Monotone standardGaussianQuantileIoo :=
  standardGaussianCDFOrderIso.symm.monotone

/-- The true standard-normal quantile is continuous on `(0,1)`. -/
theorem standardGaussianQuantileIoo_continuous :
    Continuous standardGaussianQuantileIoo :=
  standardGaussianCDFOrderIso.symm.continuous

/-- Quantiles above the median are positive. -/
theorem standardGaussianQuantileIoo_pos_of_half_lt
    {p : Ioo (0 : ℝ) 1} (hp : (1 / 2 : ℝ) < p) :
    0 < standardGaussianQuantileIoo p := by
  have hcdf :
      standardGaussianCDF 0 < standardGaussianCDF (standardGaussianQuantileIoo p) := by
    rw [standardGaussianCDF_zero_eq_half,
      standardGaussianCDF_quantileIoo]
    exact hp
  exact standardGaussianCDF_strictMono.lt_iff_lt.mp hcdf

/--
The true standard-normal quantile, extended arbitrarily outside `(0,1)`.

The extension value is irrelevant for paper proofs; the API only uses
monotonicity and continuity on `(0,1)`.
-/
def standardGaussianQuantile (p : ℝ) : ℝ :=
  if hp : p ∈ Ioo (0 : ℝ) 1 then
    standardGaussianQuantileIoo ⟨p, hp⟩
  else
    0

@[simp] theorem standardGaussianQuantile_of_mem_Ioo
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    standardGaussianQuantile p =
      standardGaussianQuantileIoo ⟨p, hp⟩ := by
  simp [standardGaussianQuantile, hp]

/-- The extended true standard-normal quantile is monotone on `(0,1)`. -/
theorem standardGaussianQuantile_monoOn :
    MonotoneOn standardGaussianQuantile (Ioo (0 : ℝ) 1) := by
  intro p hp q hq hpq
  rw [standardGaussianQuantile_of_mem_Ioo hp,
    standardGaussianQuantile_of_mem_Ioo hq]
  exact standardGaussianQuantileIoo_mono hpq

/-- The extended true standard-normal quantile is continuous on `(0,1)`. -/
theorem standardGaussianQuantile_continuousOn :
    ContinuousOn standardGaussianQuantile (Ioo (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  exact standardGaussianQuantileIoo_continuous.congr (by
    intro p
    exact (standardGaussianQuantile_of_mem_Ioo p.property).symm)

/-- The extended true standard-normal quantile is positive above the median. -/
theorem standardGaussianQuantile_pos_of_half_lt
    {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) :
    0 < standardGaussianQuantile p := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  rw [standardGaussianQuantile_of_mem_Ioo hp01]
  exact standardGaussianQuantileIoo_pos_of_half_lt
    (p := ⟨p, hp01⟩) hp.1

/-- The extended true standard-normal quantile inverts the CDF on `(0,1)`. -/
theorem standardGaussianCDF_standardGaussianQuantile
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    standardGaussianCDF (standardGaussianQuantile p) = p := by
  rw [standardGaussianQuantile_of_mem_Ioo hp]
  exact standardGaussianCDF_quantileIoo ⟨p, hp⟩

/-- The standard normal hazard rate using the mathlib-backed CDF and PDF. -/
def standardGaussianHazard (z : ℝ) : ℝ :=
  standardGaussianDensity z / (1 - standardGaussianCDF z)

@[simp] theorem standardGaussianHazard_eq (z : ℝ) :
    standardGaussianHazard z =
      standardGaussianDensity z / (1 - standardGaussianCDF z) := rfl

/--
Left-tail CDF times right-tail hazard equals the density.  This is the
Gaussian symmetry identity used to control lower-tail conditional means.
-/
theorem standardGaussianCDF_neg_mul_hazard (t : ℝ) :
    standardGaussianCDF (-t) * standardGaussianHazard t =
      standardGaussianDensity t := by
  rw [standardGaussianCDF_neg_eq_one_sub, standardGaussianHazard_eq]
  field_simp [(standardGaussianTail_pos t).ne']

/-- The mathlib-backed standard normal hazard rate is strictly positive. -/
theorem standardGaussianHazard_pos (z : ℝ) :
    0 < standardGaussianHazard z := by
  rw [standardGaussianHazard_eq]
  exact div_pos (standardGaussianDensity_pos z) (standardGaussianTail_pos z)

/--
The mathlib-backed standard-normal hazard is the reciprocal of the unnormalized
Gaussian Mills ratio.
-/
theorem standardGaussianHazard_eq_millsHazard (z : ℝ) :
    standardGaussianHazard z = gaussianMillsHazard z := by
  rw [standardGaussianHazard_eq, standardGaussianDensity_eq_mills_integrand,
    standardGaussianTail_eq_const_mul_millsTail]
  unfold gaussianMillsHazard gaussianMillsRatio
  field_simp [Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi),
    gaussianMillsTail_pos z, Real.exp_pos (z ^ 2 / 2)]
  rw [← Real.exp_add]
  have hsum : -(z ^ 2 / 2) + z ^ 2 / 2 = 0 := by ring
  rw [hsum, Real.exp_zero]

/--
Concrete lower-tail conditional mean for a location-scale standard-normal law,
expressed by symmetry through the upper-tail hazard.
-/
def standardGaussianLowerTailMean
    (L : GaussianScaleLaw) (threshold : ℝ) : ℝ :=
  L.mean - L.scale * standardGaussianHazard (-(L.standardize threshold))

/--
The concrete Gaussian lower-tail mean is strictly below the threshold.
-/
theorem standardGaussianLowerTailMean_lt_threshold
    (L : GaussianScaleLaw) (threshold : ℝ) :
    standardGaussianLowerTailMean L threshold < threshold := by
  let z : ℝ := L.standardize threshold
  have hthreshold_std :
      L.mean + L.scale * L.standardize threshold = threshold := by
    simpa [GaussianScaleLaw.unstandardize] using
      L.unstandardize_standardize threshold
  have hcore : -standardGaussianHazard (-z) < z := by
    by_cases hz_nonneg : 0 ≤ z
    · have hhaz_pos : 0 < standardGaussianHazard (-z) :=
        standardGaussianHazard_pos (-z)
      linarith
    · have hz_neg : z < 0 := lt_of_not_ge hz_nonneg
      have hneg_pos : 0 < -z := by linarith
      have hhaz_gt : -z < standardGaussianHazard (-z) := by
        rw [standardGaussianHazard_eq_millsHazard]
        exact gaussianMillsHazard_gt_arg_of_pos hneg_pos
      linarith
  have hmul :
      L.scale * (-standardGaussianHazard (-z)) < L.scale * z :=
    mul_lt_mul_of_pos_left hcore L.scale_pos
  calc
    standardGaussianLowerTailMean L threshold =
        L.mean + L.scale * (-standardGaussianHazard (-z)) := by
      dsimp [standardGaussianLowerTailMean, z]
      ring
    _ < L.mean + L.scale * z := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_lt_add_left hmul L.mean
    _ = threshold := by
      dsimp [z]
      exact hthreshold_std

/--
Concrete Gaussian lower-tail mean certificate backed by mathlib's Gaussian CDF
and the Mills-ratio hazard facts.
-/
def standardGaussianLowerTailMeanCertificate :
    GaussianLowerTailMeanCertificate where
  lowerTailMean := standardGaussianLowerTailMean
  lowerTailMean_lt_threshold := standardGaussianLowerTailMean_lt_threshold

/-- The mathlib-backed standard-normal hazard is strictly increasing. -/
theorem standardGaussianHazard_strictMono :
    StrictMono standardGaussianHazard := by
  intro x y hxy
  rw [standardGaussianHazard_eq_millsHazard x,
    standardGaussianHazard_eq_millsHazard y]
  exact gaussianMillsHazard_strictMono hxy

/-- The mathlib-backed standard-normal hazard is monotone. -/
theorem standardGaussianHazard_mono :
    Monotone standardGaussianHazard :=
  standardGaussianHazard_strictMono.monotone

/-- The mathlib-backed standard Gaussian density is continuous. -/
theorem standardGaussianDensity_continuous :
    Continuous standardGaussianDensity := by
  unfold standardGaussianDensity ProbabilityTheory.gaussianPDFReal
  fun_prop

/-- Product of the standard Gaussian density with an affine-shifted density is integrable on
every upper tail. -/
theorem standardGaussianDensity_mul_affine_integrableOn_Ioi
    (offset c B : ℝ) :
    IntegrableOn
      (fun x : ℝ =>
        standardGaussianDensity x *
          standardGaussianDensity (offset + c * x))
      (Ioi B) := by
  let normConst : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hbase :
      Integrable (fun x : ℝ => normConst * standardGaussianDensity x)
        (volume.restrict (Ioi B)) := by
    exact (standardGaussianDensity_integrable.mono_measure
      Measure.restrict_le_self).const_mul normConst
  change Integrable
    (fun x : ℝ =>
      standardGaussianDensity x *
        standardGaussianDensity (offset + c * x))
    (volume.restrict (Ioi B))
  refine Integrable.mono' hbase ?_ ?_
  · have haff : Continuous fun x : ℝ => offset + c * x := by fun_prop
    exact ((standardGaussianDensity_continuous.mul
      (standardGaussianDensity_continuous.comp haff)).stronglyMeasurable).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      have hnonneg :
          0 ≤ standardGaussianDensity x *
            standardGaussianDensity (offset + c * x) :=
        mul_nonneg (standardGaussianDensity_nonneg x)
          (standardGaussianDensity_nonneg (offset + c * x))
      rw [Real.norm_of_nonneg hnonneg]
      have hmul := mul_le_mul_of_nonneg_left
        (standardGaussianDensity_le_normConst (offset + c * x))
        (standardGaussianDensity_nonneg x)
      simpa [normConst, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Product of the standard Gaussian density with an affine-shifted density is integrable on
every lower tail. -/
theorem standardGaussianDensity_mul_affine_integrableOn_Iic
    (offset c B : ℝ) :
    IntegrableOn
      (fun x : ℝ =>
        standardGaussianDensity x *
          standardGaussianDensity (offset + c * x))
      (Iic B) := by
  let normConst : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hbase :
      Integrable (fun x : ℝ => normConst * standardGaussianDensity x)
        (volume.restrict (Iic B)) := by
    exact (standardGaussianDensity_integrable.mono_measure
      Measure.restrict_le_self).const_mul normConst
  change Integrable
    (fun x : ℝ =>
      standardGaussianDensity x *
        standardGaussianDensity (offset + c * x))
    (volume.restrict (Iic B))
  refine Integrable.mono' hbase ?_ ?_
  · have haff : Continuous fun x : ℝ => offset + c * x := by fun_prop
    exact ((standardGaussianDensity_continuous.mul
      (standardGaussianDensity_continuous.comp haff)).stronglyMeasurable).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      have hnonneg :
          0 ≤ standardGaussianDensity x *
            standardGaussianDensity (offset + c * x) :=
        mul_nonneg (standardGaussianDensity_nonneg x)
          (standardGaussianDensity_nonneg (offset + c * x))
      rw [Real.norm_of_nonneg hnonneg]
      have hmul := mul_le_mul_of_nonneg_left
        (standardGaussianDensity_le_normConst (offset + c * x))
        (standardGaussianDensity_nonneg x)
      simpa [normConst, mul_comm, mul_left_comm, mul_assoc] using hmul

/--
Integral of the product of a standard Gaussian density and an affine-shifted
standard Gaussian density over a finite interval.
-/
theorem standardGaussianDensity_mul_affine_integral_interval
    (c A lower upper : ℝ) (hlower_upper : lower ≤ upper) :
    (∫ z in lower..upper,
        standardGaussianDensity z *
          standardGaussianDensity
            (A * Real.sqrt (1 + c ^ 2) + c * z)) =
      let denom := Real.sqrt (1 + c ^ 2)
      standardGaussianDensity A * denom⁻¹ *
        (standardGaussianCDF (denom * upper + A * c) -
          standardGaussianCDF (denom * lower + A * c)) := by
  have hint :
      IntegrableOn
        (fun z : ℝ =>
          standardGaussianDensity z *
            standardGaussianDensity
              (A * Real.sqrt (1 + c ^ 2) + c * z))
        (Ioi lower) :=
    standardGaussianDensity_mul_affine_integrableOn_Ioi
      (A * Real.sqrt (1 + c ^ 2)) c lower
  have htail :=
    intervalIntegral.integral_Ioi_sub_Ioi
      (f := fun z : ℝ =>
        standardGaussianDensity z *
          standardGaussianDensity
            (A * Real.sqrt (1 + c ^ 2) + c * z))
      hint hlower_upper
  rw [standardGaussianDensity_mul_affine_integral_Ioi c A lower,
    standardGaussianDensity_mul_affine_integral_Ioi c A upper] at htail
  rw [← htail]
  ring

/-- The standard Gaussian probability of `(-∞, x]` is the integral of its density. -/
theorem standardGaussianMeasure_real_Iic_eq_integral_density (x : ℝ) :
    standardGaussianMeasure.real (Iic x) =
      ∫ y in Iic x, standardGaussianDensity y := by
  have hmeasure :
      standardGaussianMeasure (Iic x) =
        ENNReal.ofReal (∫ y in Iic x, standardGaussianDensity y) := by
    unfold standardGaussianMeasure standardGaussianDensity
    simpa using
      (ProbabilityTheory.gaussianReal_apply_eq_integral
        0 standardGaussianVariance_ne_zero (Iic x))
  rw [measureReal_def, hmeasure]
  rw [ENNReal.toReal_ofReal]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Iic
    (fun y _hy => standardGaussianDensity_nonneg y)

/-- The mathlib-backed standard Gaussian CDF is the integral of its density. -/
theorem standardGaussianCDF_eq_integral_Iic (x : ℝ) :
    standardGaussianCDF x =
      ∫ y in Iic x, standardGaussianDensity y := by
  rw [standardGaussianCDF, ProbabilityTheory.cdf_eq_real]
  exact standardGaussianMeasure_real_Iic_eq_integral_density x

/--
Affine lower-tail integral of the Gaussian product appearing in Owen's
first-moment calculation.
-/
theorem standardGaussianDensity_mul_affine_integral_Iic
    (c A B : ℝ) :
    (∫ z in Iic B,
        standardGaussianDensity z *
          standardGaussianDensity
            (A * Real.sqrt (1 + c ^ 2) + c * z)) =
      standardGaussianDensity A * (Real.sqrt (1 + c ^ 2))⁻¹ *
        standardGaussianCDF
          (Real.sqrt (1 + c ^ 2) * B + A * c) := by
  let D : ℝ := Real.sqrt (1 + c ^ 2)
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hpoint :
      EqOn
        (fun z : ℝ =>
          standardGaussianDensity z *
            standardGaussianDensity (A * D + c * z))
        (fun z : ℝ =>
          standardGaussianDensity A *
            standardGaussianDensity (D * z + A * c))
        (Iic B) := by
    intro z _hz
    exact standardGaussianDensity_mul_affine_eq c A z
  have hscale :
      (∫ z in Iic B, standardGaussianDensity (D * z + A * c)) =
        D⁻¹ * ∫ y in Iic (D * B + A * c),
          standardGaussianDensity y := by
    have hmul :=
      integral_comp_mul_left_Iic_real
        (fun y : ℝ => standardGaussianDensity (y + A * c))
        B hDpos
    have hshift :
        (∫ y in Iic (D * B),
            standardGaussianDensity (y + A * c)) =
          ∫ y in Iic (D * B + A * c),
            standardGaussianDensity y :=
      integral_comp_add_right_Iic_real standardGaussianDensity (D * B) (A * c)
    calc
      (∫ z in Iic B, standardGaussianDensity (D * z + A * c))
          =
        (∫ z in Iic B,
          (fun y : ℝ => standardGaussianDensity (y + A * c)) (D * z)) := by
          rfl
      _ =
        D⁻¹ * ∫ y in Iic (D * B),
          standardGaussianDensity (y + A * c) := by
          simpa using hmul
      _ =
        D⁻¹ * ∫ y in Iic (D * B + A * c),
          standardGaussianDensity y := by
          rw [hshift]
  calc
    (∫ z in Iic B,
        standardGaussianDensity z *
          standardGaussianDensity
            (A * Real.sqrt (1 + c ^ 2) + c * z))
        =
      ∫ z in Iic B,
        standardGaussianDensity A *
          standardGaussianDensity (D * z + A * c) := by
        dsimp [D]
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Iic hpoint
    _ =
      standardGaussianDensity A *
        ∫ z in Iic B, standardGaussianDensity (D * z + A * c) := by
        rw [integral_const_mul]
    _ =
      standardGaussianDensity A * (D⁻¹ *
        ∫ y in Iic (D * B + A * c), standardGaussianDensity y) := by
        rw [hscale]
    _ =
      standardGaussianDensity A * D⁻¹ *
        standardGaussianCDF (D * B + A * c) := by
        rw [standardGaussianCDF_eq_integral_Iic]
        ring
    _ =
      standardGaussianDensity A * (Real.sqrt (1 + c ^ 2))⁻¹ *
        standardGaussianCDF
          (Real.sqrt (1 + c ^ 2) * B + A * c) := by
        rfl

/-- Derivative of the mathlib-backed standard Gaussian CDF. -/
theorem standardGaussianCDF_hasDerivAt_density (x : ℝ) :
    HasDerivAt standardGaussianCDF (standardGaussianDensity x) x := by
  let f : ℝ → ℝ := standardGaussianDensity
  have hfint : Integrable f := by
    simpa [f, standardGaussianDensity] using
      (ProbabilityTheory.integrable_gaussianPDFReal 0 (1 : ℝ≥0))
  have hcont : Continuous f := by
    simpa [f] using standardGaussianDensity_continuous
  have hIic_eq (u : ℝ) :
      (∫ y : ℝ in Iic u, f y) =
        (∫ y : ℝ in Iic (0 : ℝ), f y) + ∫ y : ℝ in (0 : ℝ)..u, f y := by
    have hfi0 : IntegrableOn f (Iic (0 : ℝ)) := hfint.integrableOn
    have hfiu : IntegrableOn f (Iic u) := hfint.integrableOn
    have hsub := intervalIntegral.integral_Iic_sub_Iic
      (f := f) (a := (0 : ℝ)) (b := u) hfi0 hfiu
    linarith
  have hIic_deriv :
      HasDerivAt (fun u : ℝ => ∫ y : ℝ in Iic u, f y) (f x) x := by
    have hderiv : HasDerivAt
        (fun u : ℝ =>
          (∫ y : ℝ in Iic (0 : ℝ), f y) + ∫ y : ℝ in (0 : ℝ)..u, f y)
        (f x) x := by
      exact (hcont.integral_hasStrictDerivAt (0 : ℝ) x).hasDerivAt.const_add
        (∫ y : ℝ in Iic (0 : ℝ), f y)
    refine hderiv.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun u => hIic_eq u
  refine hIic_deriv.congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun u => by
    simp [standardGaussianCDF_eq_integral_Iic, f]

/-- Doubled-log elementary form of the mathlib-backed standard Gaussian density. -/
theorem standardGaussianDoubledLogDensity_eq (z : ℝ) :
    2 * Real.log (standardGaussianDensity z) =
      - z ^ 2 + 2 * Real.log ((Real.sqrt (2 * Real.pi))⁻¹) := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hcpos : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi))
  have hexppos : 0 < Real.exp (-(z ^ 2) / 2) := Real.exp_pos _
  have hlog :
      Real.log (standardGaussianDensity z) =
        Real.log c + (-(z ^ 2) / 2) := by
    rw [standardGaussianDensity_eq_mills_integrand]
    dsimp [c]
    rw [Real.log_mul hcpos.ne' hexppos.ne']
    rw [Real.log_exp]
  calc
    2 * Real.log (standardGaussianDensity z)
        = 2 * (Real.log c + (-(z ^ 2) / 2)) := by rw [hlog]
    _ = - z ^ 2 + 2 * Real.log c := by ring
    _ = - z ^ 2 + 2 * Real.log ((Real.sqrt (2 * Real.pi))⁻¹) := by rfl

/-- The mathlib-backed standard normal hazard rate is continuous. -/
theorem standardGaussianHazard_continuous :
    Continuous standardGaussianHazard := by
  unfold standardGaussianHazard
  exact standardGaussianDensity_continuous.div
    (continuous_const.sub standardGaussianCDF_continuous)
    (fun z => (standardGaussianTail_pos z).ne')

/-- The standard Gaussian hazard is differentiable on the whole real line. -/
theorem standardGaussianHazard_differentiable :
    Differentiable ℝ standardGaussianHazard := by
  have hident : standardGaussianHazard = gaussianMillsHazard := by
    funext z
    exact standardGaussianHazard_eq_millsHazard z
  rw [hident]
  intro z
  exact (gaussianMillsHazard_hasDerivAt z).differentiableAt

/-- The standard Gaussian hazard has derivative norm at most one. -/
theorem standardGaussianHazard_nnnorm_deriv_le_one (z : ℝ) :
    ‖deriv standardGaussianHazard z‖₊ ≤ 1 := by
  have hident : standardGaussianHazard = gaussianMillsHazard := by
    funext x
    exact standardGaussianHazard_eq_millsHazard x
  rw [hident]
  obtain ⟨d, hd, hd_lt_one⟩ := gaussianMillsHazard_deriv_lt_one z
  have hderiv : deriv gaussianMillsHazard z = d := hd.deriv
  have hd_pos : 0 < d := by
    rw [← hderiv, (gaussianMillsHazard_hasDerivAt z).deriv]
    exact gaussianMillsHazard_deriv_pos z
  rw [← NNReal.coe_le_coe, coe_nnnorm, hderiv]
  exact abs_le.2 ⟨(neg_one_lt_zero.trans hd_pos).le, le_of_lt hd_lt_one⟩

/-- The standard Gaussian hazard is globally one-Lipschitz. -/
theorem standardGaussianHazard_lipschitzWith_one :
    LipschitzWith 1 standardGaussianHazard := by
  apply lipschitzWith_of_nnnorm_deriv_le standardGaussianHazard_differentiable
  exact standardGaussianHazard_nnnorm_deriv_le_one

/--
For a fixed Gaussian location-scale law, the concrete lower-tail conditional
mean is continuous in the finite threshold.
-/
theorem standardGaussianLowerTailMean_continuous (L : GaussianScaleLaw) :
    Continuous (fun threshold : ℝ =>
      standardGaussianLowerTailMean L threshold) := by
  dsimp [standardGaussianLowerTailMean]
  have hstd : Continuous (fun threshold : ℝ => L.standardize threshold) := by
    unfold GaussianScaleLaw.standardize
    fun_prop
  exact continuous_const.sub
    (continuous_const.mul (standardGaussianHazard_continuous.comp hstd.neg))

/-- The standard Gaussian density tends to zero at `-∞`. -/
theorem standardGaussianDensity_tendsto_atBot_zero :
    Tendsto standardGaussianDensity atBot (𝓝 0) := by
  have harg :
      Tendsto (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) atBot (𝓝 0) := by
    have hcomp := gaussianExpFactor_tendsto_atTop_zero.comp tendsto_neg_atBot_atTop
    refine hcomp.congr' ?_
    filter_upwards with t
    simp
  have hconst :=
    (tendsto_const_nhds
      (x := (Real.sqrt (2 * Real.pi))⁻¹)).mul harg
  have hdensity :
      Tendsto standardGaussianDensity atBot
        (𝓝 ((Real.sqrt (2 * Real.pi))⁻¹ * 0)) := by
    refine hconst.congr' ?_
    filter_upwards with t
    rw [standardGaussianDensity_eq_mills_integrand]
  simpa using hdensity

/-- The standard Gaussian density tends to zero at `+∞`. -/
theorem standardGaussianDensity_tendsto_atTop_zero :
    Tendsto standardGaussianDensity atTop (𝓝 0) := by
  have hconst :=
    (tendsto_const_nhds
      (x := (Real.sqrt (2 * Real.pi))⁻¹)).mul
        gaussianExpFactor_tendsto_atTop_zero
  have hdensity :
      Tendsto standardGaussianDensity atTop
        (𝓝 ((Real.sqrt (2 * Real.pi))⁻¹ * 0)) := by
    refine hconst.congr' ?_
    filter_upwards with t
    rw [standardGaussianDensity_eq_mills_integrand]
  simpa using hdensity

/--
Integration-by-parts identity for the affine-CDF first moment on an upper
tail, assuming the two integration-by-parts terms are integrable.

`offset = A * sqrt(1+c^2)`.
-/
theorem standardGaussian_firstMoment_affineCDF_integral_Ioi_of_integrable
    (offset c B : ℝ)
    (hleft :
      IntegrableOn
        ((fun x : ℝ => standardGaussianCDF (offset + c * x)) *
          (fun x : ℝ => -x * standardGaussianDensity x))
        (Ioi B))
    (hprod :
      IntegrableOn
        ((fun x : ℝ => c * standardGaussianDensity (offset + c * x)) *
          standardGaussianDensity)
        (Ioi B)) :
    (∫ x in Ioi B,
        x * standardGaussianDensity x *
          standardGaussianCDF (offset + c * x)) =
      standardGaussianDensity B * standardGaussianCDF (offset + c * B) +
        c * ∫ x in Ioi B,
          standardGaussianDensity x *
            standardGaussianDensity (offset + c * x) := by
  let u : ℝ → ℝ := fun x => standardGaussianCDF (offset + c * x)
  let u' : ℝ → ℝ := fun x => c * standardGaussianDensity (offset + c * x)
  let v : ℝ → ℝ := standardGaussianDensity
  let v' : ℝ → ℝ := fun x => -x * standardGaussianDensity x
  have hu : ∀ x ∈ Ioi B, HasDerivAt u (u' x) x := by
    intro x _hx
    have hlin : HasDerivAt (fun y : ℝ => offset + c * y) c x := by
      have hmul : HasDerivAt (fun y : ℝ => c * y) c x := by
        simpa using (hasDerivAt_id x).const_mul c
      change HasDerivAt ((fun _ : ℝ => offset) + fun y : ℝ => c * y) c x
      convert (hasDerivAt_const x offset).add hmul using 1
      ring
    simpa [u, u', mul_comm] using
      (standardGaussianCDF_hasDerivAt_density (offset + c * x)).comp x hlin
  have hv : ∀ x ∈ Ioi B, HasDerivAt v (v' x) x := by
    intro x _hx
    simpa [v, v'] using standardGaussianDensity_hasDerivAt x
  have hzero :
      Tendsto (u * v) (𝓝[>] B)
        (𝓝 (standardGaussianCDF (offset + c * B) *
          standardGaussianDensity B)) := by
    have hcont :
        Continuous fun x : ℝ =>
          standardGaussianCDF (offset + c * x) *
            standardGaussianDensity x := by
      exact (standardGaussianCDF_continuous.comp (by fun_prop)).mul
        standardGaussianDensity_continuous
    simpa [u, v, Pi.mul_apply] using
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hinfty :
      Tendsto (u * v) atTop (𝓝 0) := by
    have hsq :
        Tendsto
          (fun x : ℝ =>
            standardGaussianCDF (offset + c * x) *
              standardGaussianDensity x)
          atTop (𝓝 0) := by
      refine squeeze_zero
        (fun x => mul_nonneg
          (standardGaussianCDF_nonneg (offset + c * x))
          (standardGaussianDensity_nonneg x))
        (fun x => by
          exact mul_le_of_le_one_left
            (standardGaussianDensity_nonneg x)
            (standardGaussianCDF_le_one (offset + c * x)))
        standardGaussianDensity_tendsto_atTop_zero
    simpa [u, v, Pi.mul_apply] using hsq
  have hparts :=
    MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (a := B) (u := u) (u' := u') (v := v) (v' := v')
      hu hv hleft hprod hzero hinfty
  have hleft_eq :
      (∫ x in Ioi B, u x * v' x) =
        -∫ x in Ioi B,
          x * standardGaussianDensity x *
            standardGaussianCDF (offset + c * x) := by
    rw [← integral_neg]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun x _hx => by
        simp [u, v']
        ring)
  have hprod_eq :
      (∫ x in Ioi B, u' x * v x) =
        c * ∫ x in Ioi B,
          standardGaussianDensity x *
            standardGaussianDensity (offset + c * x) := by
    rw [← integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun x _hx => by
        simp [u', v]
        ring)
  rw [hleft_eq, hprod_eq] at hparts
  linarith

/--
Integration-by-parts identity for the affine-CDF first moment on a lower tail,
assuming the two integration-by-parts terms are integrable.

This is the lower-tail counterpart to
`standardGaussian_firstMoment_affineCDF_integral_Ioi_of_integrable` and is the
shape needed by `kappa` calculation.
-/
theorem standardGaussian_firstMoment_affineCDF_integral_Iic_of_integrable
    (offset c B : ℝ)
    (hleft :
      IntegrableOn
        ((fun x : ℝ => standardGaussianCDF (offset + c * x)) *
          (fun x : ℝ => -x * standardGaussianDensity x))
        (Iic B))
    (hprod :
      IntegrableOn
        ((fun x : ℝ => c * standardGaussianDensity (offset + c * x)) *
          standardGaussianDensity)
        (Iic B)) :
    (∫ x in Iic B,
        x * standardGaussianDensity x *
          standardGaussianCDF (offset + c * x)) =
      c * (∫ x in Iic B,
          standardGaussianDensity x *
            standardGaussianDensity (offset + c * x)) -
        standardGaussianDensity B * standardGaussianCDF (offset + c * B) := by
  let u : ℝ → ℝ := fun x => standardGaussianCDF (offset + c * x)
  let u' : ℝ → ℝ := fun x => c * standardGaussianDensity (offset + c * x)
  let v : ℝ → ℝ := standardGaussianDensity
  let v' : ℝ → ℝ := fun x => -x * standardGaussianDensity x
  have hu : ∀ x ∈ Iio B, HasDerivAt u (u' x) x := by
    intro x _hx
    have hlin : HasDerivAt (fun y : ℝ => offset + c * y) c x := by
      have hmul : HasDerivAt (fun y : ℝ => c * y) c x := by
        simpa using (hasDerivAt_id x).const_mul c
      change HasDerivAt ((fun _ : ℝ => offset) + fun y : ℝ => c * y) c x
      convert (hasDerivAt_const x offset).add hmul using 1
      ring
    simpa [u, u', mul_comm] using
      (standardGaussianCDF_hasDerivAt_density (offset + c * x)).comp x hlin
  have hv : ∀ x ∈ Iio B, HasDerivAt v (v' x) x := by
    intro x _hx
    simpa [v, v'] using standardGaussianDensity_hasDerivAt x
  have hzero :
      Tendsto (u * v) (𝓝[<] B)
        (𝓝 (standardGaussianCDF (offset + c * B) *
          standardGaussianDensity B)) := by
    have hcont :
        Continuous fun x : ℝ =>
          standardGaussianCDF (offset + c * x) *
            standardGaussianDensity x := by
      exact (standardGaussianCDF_continuous.comp (by fun_prop)).mul
        standardGaussianDensity_continuous
    simpa [u, v, Pi.mul_apply] using
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hinfty :
      Tendsto (u * v) atBot (𝓝 0) := by
    have hsq :
        Tendsto
          (fun x : ℝ =>
            standardGaussianCDF (offset + c * x) *
              standardGaussianDensity x)
          atBot (𝓝 0) := by
      refine squeeze_zero
        (fun x => mul_nonneg
          (standardGaussianCDF_nonneg (offset + c * x))
          (standardGaussianDensity_nonneg x))
        (fun x => by
          exact mul_le_of_le_one_left
            (standardGaussianDensity_nonneg x)
            (standardGaussianCDF_le_one (offset + c * x)))
        standardGaussianDensity_tendsto_atBot_zero
    simpa [u, v, Pi.mul_apply] using hsq
  have hparts :=
    MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul
      (a := B) (u := u) (u' := u') (v := v) (v' := v')
      hu hv hleft hprod hzero hinfty
  have hleft_eq :
      (∫ x in Iic B, u x * v' x) =
        -∫ x in Iic B,
          x * standardGaussianDensity x *
            standardGaussianCDF (offset + c * x) := by
    rw [← integral_neg]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      (fun x _hx => by
        simp [u, v']
        ring)
  have hprod_eq :
      (∫ x in Iic B, u' x * v x) =
        c * ∫ x in Iic B,
          standardGaussianDensity x *
            standardGaussianDensity (offset + c * x) := by
    rw [← integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      (fun x _hx => by
        simp [u', v]
        ring)
  rw [hleft_eq, hprod_eq] at hparts
  calc
    (∫ x in Iic B,
        x * standardGaussianDensity x *
          standardGaussianCDF (offset + c * x))
        =
      -(-∫ x in Iic B,
        x * standardGaussianDensity x *
          standardGaussianCDF (offset + c * x)) := by
        ring
    _ =
      -(standardGaussianCDF (offset + c * B) *
          standardGaussianDensity B - 0 -
        c * ∫ x in Iic B,
          standardGaussianDensity x *
            standardGaussianDensity (offset + c * x)) := by
        rw [hparts]
    _ =
      c * (∫ x in Iic B,
          standardGaussianDensity x *
            standardGaussianDensity (offset + c * x)) -
        standardGaussianDensity B * standardGaussianCDF (offset + c * B) := by
        ring

/--
Integration-by-parts identity for the affine-CDF first moment on an upper tail,
with the product-density integrability obligation discharged from the Gaussian
density bound.
-/
theorem standardGaussian_firstMoment_affineCDF_integral_Ioi_of_left_integrable
    (offset c B : ℝ)
    (hleft :
      IntegrableOn
        ((fun x : ℝ => standardGaussianCDF (offset + c * x)) *
          (fun x : ℝ => -x * standardGaussianDensity x))
        (Ioi B)) :
    (∫ x in Ioi B,
        x * standardGaussianDensity x *
          standardGaussianCDF (offset + c * x)) =
      standardGaussianDensity B * standardGaussianCDF (offset + c * B) +
        c * ∫ x in Ioi B,
          standardGaussianDensity x *
            standardGaussianDensity (offset + c * x) := by
  have hprodBase :
      Integrable
        (fun x : ℝ =>
          standardGaussianDensity x *
            standardGaussianDensity (offset + c * x))
        (volume.restrict (Ioi B)) :=
    standardGaussianDensity_mul_affine_integrableOn_Ioi offset c B
  have hprod :
      IntegrableOn
        ((fun x : ℝ => c * standardGaussianDensity (offset + c * x)) *
          standardGaussianDensity)
        (Ioi B) := by
    change Integrable
      (fun x : ℝ =>
        (c * standardGaussianDensity (offset + c * x)) *
          standardGaussianDensity x)
      (volume.restrict (Ioi B))
    exact (hprodBase.const_mul c).congr
      (Eventually.of_forall fun x => by ring)
  exact standardGaussian_firstMoment_affineCDF_integral_Ioi_of_integrable
    offset c B hleft hprod

/-- `-x * phi(x)` is integrable on every standard-Gaussian upper tail. -/
theorem standardGaussian_neg_id_mul_density_integrableOn_Ioi (B : ℝ) :
    IntegrableOn (fun x : ℝ => -x * standardGaussianDensity x) (Ioi B) := by
  have htail_nonneg :
      IntegrableOn (fun x : ℝ => -x * standardGaussianDensity x) (Ioi (max B 0)) := by
    have hmax_nonneg : 0 ≤ max B 0 := le_max_right B 0
    refine MeasureTheory.integrableOn_Ioi_deriv_of_nonpos'
      (a := max B 0) (g := standardGaussianDensity)
      (g' := fun x : ℝ => -x * standardGaussianDensity x)
      ?_ ?_ standardGaussianDensity_tendsto_atTop_zero
    · intro x _hx
      exact standardGaussianDensity_hasDerivAt x
    · intro x hx
      have hx_nonneg : 0 ≤ x := le_trans hmax_nonneg (le_of_lt hx)
      have hmul_nonneg : 0 ≤ x * standardGaussianDensity x :=
        mul_nonneg hx_nonneg (standardGaussianDensity_nonneg x)
      nlinarith
  by_cases hB : 0 ≤ B
  · simpa [max_eq_left hB] using htail_nonneg
  · have hBlt : B < 0 := lt_of_not_ge hB
    have hcompact :
        IntegrableOn (fun x : ℝ => -x * standardGaussianDensity x) (Ioc B 0) := by
      have hcont : Continuous fun x : ℝ => -x * standardGaussianDensity x := by
        exact continuous_id.neg.mul standardGaussianDensity_continuous
      exact (hcont.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have htail0 :
        IntegrableOn (fun x : ℝ => -x * standardGaussianDensity x) (Ioi 0) := by
      simpa [max_eq_right hBlt.le] using htail_nonneg
    have hunion :
        IntegrableOn (fun x : ℝ => -x * standardGaussianDensity x)
          (Ioc B 0 ∪ Ioi 0) :=
      hcompact.union htail0
    rw [Ioc_union_Ioi_eq_Ioi hBlt.le] at hunion
    exact hunion

/-- `x * phi(x)` is integrable on every standard-Gaussian upper tail. -/
theorem standardGaussian_id_mul_density_integrableOn_Ioi (B : ℝ) :
    IntegrableOn (fun x : ℝ => x * standardGaussianDensity x) (Ioi B) := by
  have hneg := (standardGaussian_neg_id_mul_density_integrableOn_Ioi B).neg
  simpa using hneg

/-- `-x * phi(x)` is integrable on every standard-Gaussian lower tail. -/
theorem standardGaussian_neg_id_mul_density_integrableOn_Iic (B : ℝ) :
    IntegrableOn (fun x : ℝ => -x * standardGaussianDensity x) (Iic B) := by
  have htail :
      IntegrableOn (fun y : ℝ => y * standardGaussianDensity y)
        (Ioi (-(B + 1))) :=
    standardGaussian_id_mul_density_integrableOn_Ioi (-(B + 1))
  have hcomp :
      IntegrableOn
        ((fun y : ℝ => y * standardGaussianDensity y) ∘ fun x : ℝ => -x)
        ((fun x : ℝ => -x) ⁻¹' Ioi (-(B + 1))) := by
    exact ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).2 htail
  have hsubset :
      Iic B ⊆ (fun x : ℝ => -x) ⁻¹' Ioi (-(B + 1)) := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_Ioi]
    have hxle : x ≤ B := hx
    linarith
  exact (hcomp.mono_set hsubset).congr (Eventually.of_forall fun x => by
    simp [standardGaussianDensity_neg])

/-- `x * phi(x)` is integrable on every standard-Gaussian lower tail. -/
theorem standardGaussian_id_mul_density_integrableOn_Iic (B : ℝ) :
    IntegrableOn (fun x : ℝ => x * standardGaussianDensity x) (Iic B) := by
  have hneg := (standardGaussian_neg_id_mul_density_integrableOn_Iic B).neg
  simpa using hneg

/--
The first integration-by-parts term for an affine Gaussian CDF is integrable on
every upper tail.
-/
theorem standardGaussian_affineCDF_mul_neg_id_density_integrableOn_Ioi
    (offset c B : ℝ) :
    IntegrableOn
      ((fun x : ℝ => standardGaussianCDF (offset + c * x)) *
        (fun x : ℝ => -x * standardGaussianDensity x))
      (Ioi B) := by
  have hbase :
      Integrable (fun x : ℝ => -x * standardGaussianDensity x)
        (volume.restrict (Ioi B)) :=
    standardGaussian_neg_id_mul_density_integrableOn_Ioi B
  change Integrable
    (fun x : ℝ =>
      standardGaussianCDF (offset + c * x) *
        (-x * standardGaussianDensity x))
    (volume.restrict (Ioi B))
  refine Integrable.mono' hbase.norm ?_ ?_
  · have haff : Continuous fun x : ℝ => offset + c * x := by fun_prop
    have hneg : Continuous fun x : ℝ => -x * standardGaussianDensity x :=
      continuous_id.neg.mul standardGaussianDensity_continuous
    have hcont := (standardGaussianCDF_continuous.comp haff).mul hneg
    exact hcont.stronglyMeasurable.aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [norm_mul]
      have hcdf_nonneg : 0 ≤ standardGaussianCDF (offset + c * x) :=
        standardGaussianCDF_nonneg (offset + c * x)
      rw [Real.norm_of_nonneg hcdf_nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (standardGaussianCDF_le_one (offset + c * x))

/--
The first integration-by-parts term for an affine Gaussian CDF is integrable on
every lower tail.
-/
theorem standardGaussian_affineCDF_mul_neg_id_density_integrableOn_Iic
    (offset c B : ℝ) :
    IntegrableOn
      ((fun x : ℝ => standardGaussianCDF (offset + c * x)) *
        (fun x : ℝ => -x * standardGaussianDensity x))
      (Iic B) := by
  have hbase :
      Integrable (fun x : ℝ => -x * standardGaussianDensity x)
        (volume.restrict (Iic B)) :=
    standardGaussian_neg_id_mul_density_integrableOn_Iic B
  change Integrable
    (fun x : ℝ =>
      standardGaussianCDF (offset + c * x) *
        (-x * standardGaussianDensity x))
    (volume.restrict (Iic B))
  refine Integrable.mono' hbase.norm ?_ ?_
  · have haff : Continuous fun x : ℝ => offset + c * x := by fun_prop
    have hneg : Continuous fun x : ℝ => -x * standardGaussianDensity x :=
      continuous_id.neg.mul standardGaussianDensity_continuous
    have hcont := (standardGaussianCDF_continuous.comp haff).mul hneg
    exact hcont.stronglyMeasurable.aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [norm_mul]
      have hcdf_nonneg : 0 ≤ standardGaussianCDF (offset + c * x) :=
        standardGaussianCDF_nonneg (offset + c * x)
      rw [Real.norm_of_nonneg hcdf_nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (standardGaussianCDF_le_one (offset + c * x))

/-- Affine-CDF first-moment identity on an upper tail, with all integrability
obligations discharged by Gaussian tail bounds. -/
theorem standardGaussian_firstMoment_affineCDF_integral_Ioi
    (offset c B : ℝ) :
    (∫ x in Ioi B,
        x * standardGaussianDensity x *
          standardGaussianCDF (offset + c * x)) =
      standardGaussianDensity B * standardGaussianCDF (offset + c * B) +
        c * ∫ x in Ioi B,
          standardGaussianDensity x *
            standardGaussianDensity (offset + c * x) :=
  standardGaussian_firstMoment_affineCDF_integral_Ioi_of_left_integrable
    offset c B
    (standardGaussian_affineCDF_mul_neg_id_density_integrableOn_Ioi
      offset c B)

/--
Integration-by-parts identity for the affine-CDF first moment on a lower tail,
with the product-density integrability obligation discharged from the Gaussian
density bound.
-/
theorem standardGaussian_firstMoment_affineCDF_integral_Iic_of_left_integrable
    (offset c B : ℝ)
    (hleft :
      IntegrableOn
        ((fun x : ℝ => standardGaussianCDF (offset + c * x)) *
          (fun x : ℝ => -x * standardGaussianDensity x))
        (Iic B)) :
    (∫ x in Iic B,
        x * standardGaussianDensity x *
          standardGaussianCDF (offset + c * x)) =
      c * (∫ x in Iic B,
          standardGaussianDensity x *
            standardGaussianDensity (offset + c * x)) -
        standardGaussianDensity B * standardGaussianCDF (offset + c * B) := by
  have hprodBase :
      Integrable
        (fun x : ℝ =>
          standardGaussianDensity x *
            standardGaussianDensity (offset + c * x))
        (volume.restrict (Iic B)) :=
    standardGaussianDensity_mul_affine_integrableOn_Iic offset c B
  have hprod :
      IntegrableOn
        ((fun x : ℝ => c * standardGaussianDensity (offset + c * x)) *
          standardGaussianDensity)
        (Iic B) := by
    change Integrable
      (fun x : ℝ =>
        (c * standardGaussianDensity (offset + c * x)) *
          standardGaussianDensity x)
      (volume.restrict (Iic B))
    exact (hprodBase.const_mul c).congr
      (Eventually.of_forall fun x => by ring)
  exact standardGaussian_firstMoment_affineCDF_integral_Iic_of_integrable
    offset c B hleft hprod

/-- Affine-CDF first-moment identity on a lower tail, with all integrability
obligations discharged by Gaussian tail bounds. -/
theorem standardGaussian_firstMoment_affineCDF_integral_Iic
    (offset c B : ℝ) :
    (∫ x in Iic B,
        x * standardGaussianDensity x *
          standardGaussianCDF (offset + c * x)) =
      c * (∫ x in Iic B,
          standardGaussianDensity x *
            standardGaussianDensity (offset + c * x)) -
        standardGaussianDensity B * standardGaussianCDF (offset + c * B) :=
  standardGaussian_firstMoment_affineCDF_integral_Iic_of_left_integrable
    offset c B
    (standardGaussian_affineCDF_mul_neg_id_density_integrableOn_Iic
      offset c B)

/--
Affine-CDF first-moment identity on a finite interval, obtained by subtracting
the two upper-tail identities.
-/
theorem standardGaussian_firstMoment_affineCDF_integral_interval
    (A c lower upper : ℝ) (hlower_upper : lower ≤ upper) :
    (∫ x in lower..upper,
        x * standardGaussianDensity x *
          standardGaussianCDF (A * Real.sqrt (1 + c ^ 2) + c * x)) =
      (let denom := Real.sqrt (1 + c ^ 2)
       standardGaussianDensity lower *
           standardGaussianCDF (A * denom + c * lower) +
         c * (standardGaussianDensity A * denom⁻¹ *
          (1 - standardGaussianCDF (denom * lower + A * c)))) -
        (let denom := Real.sqrt (1 + c ^ 2)
         standardGaussianDensity upper *
             standardGaussianCDF (A * denom + c * upper) +
           c * (standardGaussianDensity A * denom⁻¹ *
            (1 - standardGaussianCDF (denom * upper + A * c)))) := by
  let denom := Real.sqrt (1 + c ^ 2)
  have hint :
      IntegrableOn
        (fun x : ℝ =>
          x * standardGaussianDensity x *
            standardGaussianCDF (A * denom + c * x))
        (Ioi lower) := by
    have hbase :
        Integrable (fun x : ℝ => x * standardGaussianDensity x)
          (volume.restrict (Ioi lower)) :=
      standardGaussian_id_mul_density_integrableOn_Ioi lower
    change Integrable
      (fun x : ℝ =>
        x * standardGaussianDensity x *
          standardGaussianCDF (A * denom + c * x))
      (volume.restrict (Ioi lower))
    refine Integrable.mono' hbase.norm ?_ ?_
    · have haff : Continuous fun x : ℝ => A * denom + c * x := by fun_prop
      have hcont :=
        (continuous_id.mul standardGaussianDensity_continuous).mul
          (standardGaussianCDF_continuous.comp haff)
      exact hcont.stronglyMeasurable.aestronglyMeasurable
    · exact Eventually.of_forall fun x => by
        rw [norm_mul]
        have hcdf_nonneg : 0 ≤ standardGaussianCDF (A * denom + c * x) :=
          standardGaussianCDF_nonneg (A * denom + c * x)
        rw [Real.norm_of_nonneg hcdf_nonneg]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (standardGaussianCDF_le_one (A * denom + c * x))
  have htail :=
    intervalIntegral.integral_Ioi_sub_Ioi
      (f := fun x : ℝ =>
        x * standardGaussianDensity x *
          standardGaussianCDF (A * denom + c * x))
      hint hlower_upper
  rw [standardGaussian_firstMoment_affineCDF_integral_Ioi (A * denom) c lower,
    standardGaussian_firstMoment_affineCDF_integral_Ioi (A * denom) c upper] at htail
  rw [standardGaussianDensity_mul_affine_integral_Ioi c A lower,
    standardGaussianDensity_mul_affine_integral_Ioi c A upper] at htail
  exact htail.symm

/-- The left-tail probability times the positive tail coordinate tends to zero. -/
theorem standardGaussianCDF_neg_mul_id_tendsto_atTop_zero :
    Tendsto (fun t : ℝ => standardGaussianCDF (-t) * t) atTop (𝓝 0) := by
  let normalizingConst : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hconst_nonneg : 0 ≤ normalizingConst := by
    dsimp [normalizingConst]
    exact inv_nonneg.mpr
      (Real.sqrt_nonneg (2 * Real.pi))
  have hconst_exp :
      Tendsto (fun t : ℝ =>
          normalizingConst * Real.exp (-(t ^ 2) / 2))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds (x := normalizingConst)).mul
        gaussianExpFactor_tendsto_atTop_zero
  refine squeeze_zero' ?_ ?_ hconst_exp
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact mul_nonneg (standardGaussianCDF_nonneg (-t)) ht
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have htail_lt :
        gaussianMillsTail t < Real.exp (-(t ^ 2) / 2) / t := by
      simpa [gaussianMillsUpperGap, sub_pos] using
        gaussianMillsUpperGap_pos_of_pos ht
    have htail_mul_le :
        gaussianMillsTail t * t ≤ Real.exp (-(t ^ 2) / 2) := by
      have hmul := mul_lt_mul_of_pos_right htail_lt ht
      have hright :
          (Real.exp (-(t ^ 2) / 2) / t) * t =
            Real.exp (-(t ^ 2) / 2) := by
        field_simp [ht.ne']
      exact le_of_lt (by simpa [hright] using hmul)
    calc
      standardGaussianCDF (-t) * t =
          (1 - standardGaussianCDF t) * t := by
            rw [standardGaussianCDF_neg_eq_one_sub]
      _ = (normalizingConst * gaussianMillsTail t) * t := by
            rw [standardGaussianTail_eq_const_mul_millsTail]
      _ = normalizingConst * (gaussianMillsTail t * t) := by ring
      _ ≤ normalizingConst * Real.exp (-(t ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left htail_mul_le hconst_nonneg

/--
The product of a left-tail probability with the lower-tail hazard gap tends to
zero.  Equivalently, `Φ(-t) * (t - h(t)) -> 0` for the standard normal hazard
`h`.
-/
theorem standardGaussianCDF_neg_mul_hazard_gap_tendsto_atTop_zero :
    Tendsto
      (fun t : ℝ =>
        standardGaussianCDF (-t) * (t - standardGaussianHazard t))
      atTop (𝓝 0) := by
  have hdiff :=
    standardGaussianCDF_neg_mul_id_tendsto_atTop_zero.sub
      standardGaussianDensity_tendsto_atTop_zero
  have hdiff_zero :
      Tendsto
        (fun t : ℝ => standardGaussianCDF (-t) * t - standardGaussianDensity t)
        atTop (𝓝 0) := by
    simpa using hdiff
  refine hdiff_zero.congr' ?_
  filter_upwards with t
  rw [mul_sub, standardGaussianCDF_neg_mul_hazard]

/--
For any Gaussian location-scale law, the lower-tail conditional-mean gap is
small after multiplying by the left-tail mass.
-/
theorem standardGaussian_normalCDF_mul_lowerTailMean_sub_tendsto_atBot
    (L : GaussianScaleLaw) :
    Tendsto
      (fun cutoff : ℝ =>
        standardGaussianCDF (L.standardize cutoff) *
          (standardGaussianLowerTailMean L cutoff - cutoff))
      atBot (𝓝 0) := by
  have hstd :
      Tendsto (fun cutoff : ℝ => L.standardize cutoff) atBot atBot := by
    have hscale_inv_pos : 0 < L.scale⁻¹ := inv_pos.mpr L.scale_pos
    have hmul :
        Tendsto
          (fun cutoff : ℝ =>
            L.scale⁻¹ * cutoff + (-L.mean / L.scale))
          atBot atBot :=
      ((Filter.tendsto_const_mul_atBot_of_pos hscale_inv_pos).2
        Filter.tendsto_id).atBot_add tendsto_const_nhds
    convert hmul using 1
    ext cutoff
    rw [GaussianScaleLaw.standardize]
    field_simp [ne_of_gt L.scale_pos]
    ring
  have hneg :
      Tendsto (fun cutoff : ℝ => -L.standardize cutoff) atBot atTop :=
    tendsto_neg_atBot_atTop.comp hstd
  have htail :=
    standardGaussianCDF_neg_mul_hazard_gap_tendsto_atTop_zero.comp hneg
  have hscaled :=
    (tendsto_const_nhds (x := L.scale)).mul htail
  have hscaled_zero :
      Tendsto
        (fun cutoff : ℝ =>
          L.scale *
            (standardGaussianCDF (-(-L.standardize cutoff)) *
              ((-L.standardize cutoff) -
                standardGaussianHazard (-L.standardize cutoff))))
        atBot (𝓝 (L.scale * 0)) := by
    simpa using hscaled
  have hscaled_zero' :
      Tendsto
        (fun cutoff : ℝ =>
          L.scale *
            (standardGaussianCDF (-(-L.standardize cutoff)) *
              ((-L.standardize cutoff) -
                standardGaussianHazard (-L.standardize cutoff))))
        atBot (𝓝 0) := by
    simpa only [mul_zero] using hscaled_zero
  refine hscaled_zero'.congr' ?_
  filter_upwards with cutoff
  have hcutoff :
      L.mean + L.scale * L.standardize cutoff = cutoff := by
    simpa [GaussianScaleLaw.unstandardize] using
      L.unstandardize_standardize cutoff
  have hsub :
      standardGaussianLowerTailMean L cutoff - cutoff =
        L.scale *
          ((-L.standardize cutoff) -
            standardGaussianHazard (-L.standardize cutoff)) := by
    have hscale_std : L.scale * L.standardize cutoff = cutoff - L.mean := by
      linarith
    dsimp [standardGaussianLowerTailMean]
    nlinarith
  calc
    L.scale *
        (standardGaussianCDF (-(-L.standardize cutoff)) *
          ((-L.standardize cutoff) -
            standardGaussianHazard (-L.standardize cutoff)))
        =
      L.scale *
        (standardGaussianCDF (L.standardize cutoff) *
          ((-L.standardize cutoff) -
            standardGaussianHazard (-L.standardize cutoff))) := by
          ring_nf
    _ =
      standardGaussianCDF (L.standardize cutoff) *
        (standardGaussianLowerTailMean L cutoff - cutoff) := by
          rw [hsub]
          ring

/-- The standard normal hazard tends to zero at `-∞`. -/
theorem standardGaussianHazard_tendsto_atBot_zero :
    Tendsto standardGaussianHazard atBot (𝓝 0) := by
  have htail :
      Tendsto (fun z : ℝ => 1 - standardGaussianCDF z) atBot (𝓝 1) :=
    by simpa using
      (tendsto_const_nhds (x := (1 : ℝ))).sub
        standardGaussianCDF_tendsto_atBot
  have hdiv :=
    standardGaussianDensity_tendsto_atBot_zero.div htail (by norm_num : (1 : ℝ) ≠ 0)
  simpa [standardGaussianHazard_eq] using hdiv

/-- The standard normal hazard tends to `+∞` at `+∞`. -/
theorem standardGaussianHazard_tendsto_atTop_atTop :
    Tendsto standardGaussianHazard atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  rw [standardGaussianHazard_eq_millsHazard z]
  exact le_of_lt (gaussianMillsHazard_gt_arg_of_pos hz)

/-- Every positive real is attained by the standard Gaussian hazard. -/
theorem standardGaussianHazard_mem_range_of_pos {y : ℝ} (hy : 0 < y) :
    y ∈ Set.range standardGaussianHazard := by
  exact mem_range_of_exists_le_of_exists_ge standardGaussianHazard_continuous
    (by
      have hlt :
          ∀ᶠ x in atBot, standardGaussianHazard x < y :=
        standardGaussianHazard_tendsto_atBot_zero.eventually
          (eventually_lt_nhds hy)
      rcases hlt.exists with ⟨x, hx⟩
      exact ⟨x, le_of_lt hx⟩)
    (by
      have hgt :
          ∀ᶠ x in atTop, y < standardGaussianHazard x :=
        standardGaussianHazard_tendsto_atTop_atTop.eventually
          (eventually_gt_atTop y)
      rcases hgt.exists with ⟨x, hx⟩
      exact ⟨x, le_of_lt hx⟩)

/-- The image of the standard Gaussian hazard is exactly `(0,∞)`. -/
theorem standardGaussianHazard_image_univ :
    standardGaussianHazard '' (Set.univ : Set ℝ) = Set.Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨x, _hx, rfl⟩
    exact standardGaussianHazard_pos x
  · intro hy
    rcases standardGaussianHazard_mem_range_of_pos hy with ⟨x, hx⟩
    exact ⟨x, Set.mem_univ x, hx⟩

/-- The standard Gaussian hazard as an order isomorphism from `ℝ` to `(0,∞)`. -/
def standardGaussianHazardOrderIso : ℝ ≃o Set.Ioi (0 : ℝ) :=
  (standardGaussianHazard_strictMono.orderIso standardGaussianHazard).trans
    (OrderIso.setCongr _ _
      (by simpa [Set.image_univ] using standardGaussianHazard_image_univ))

/-- The concrete inverse of the standard Gaussian hazard on positive thresholds. -/
def standardGaussianHazardInv (y : ℝ) : ℝ :=
  if hy : y ∈ Set.Ioi (0 : ℝ) then
    standardGaussianHazardOrderIso.symm ⟨y, hy⟩
  else
    0

/-- Applying the concrete positive-threshold hazard inverse. -/
theorem standardGaussianHazard_le_iff_le_inv
    {z y : ℝ} (hy : 0 < y) :
    standardGaussianHazard z ≤ y ↔ z ≤ standardGaussianHazardInv y := by
  have hyIoi : y ∈ Set.Ioi (0 : ℝ) := hy
  rw [standardGaussianHazardInv, dif_pos hyIoi]
  change standardGaussianHazardOrderIso z ≤ (⟨y, hyIoi⟩ : Set.Ioi (0 : ℝ)) ↔
    z ≤ standardGaussianHazardOrderIso.symm ⟨y, hyIoi⟩
  exact (standardGaussianHazardOrderIso.le_symm_apply).symm

/-- Scaled standard-normal hazard monotonicity, proved through the Mills ratio. -/
theorem standardGaussian_scaled_hazard_mono
    {a x y : ℝ} (ha : 0 < a) (hx : 0 < x) (hxy : x ≤ y) :
    x * standardGaussianHazard (a / x) ≤
      y * standardGaussianHazard (a / y) := by
  rw [standardGaussianHazard_eq_millsHazard (a / x),
    standardGaussianHazard_eq_millsHazard (a / y)]
  exact gaussianMillsHazard_scaled_mono ha hx hxy

/-- Strict scaled standard-normal hazard monotonicity, proved through the Mills ratio. -/
theorem standardGaussian_scaled_hazard_strictMono
    {a x y : ℝ} (ha : 0 < a) (hx : 0 < x) (hxy : x < y) :
    x * standardGaussianHazard (a / x) <
      y * standardGaussianHazard (a / y) := by
  rw [standardGaussianHazard_eq_millsHazard (a / x),
    standardGaussianHazard_eq_millsHazard (a / y)]
  exact gaussianMillsHazard_scaled_strictMono ha hx hxy

/--
Concrete standard-normal CDF/density API backed by mathlib's `gaussianReal`
and `gaussianPDFReal`.
-/
def standardGaussianCDFAPI : StandardGaussianCDFAPI where
  cdf := standardGaussianCDF
  density := standardGaussianDensity
  cdf_continuous := standardGaussianCDF_continuous
  cdf_mono := standardGaussianCDF_mono
  cdf_strictMono := standardGaussianCDF_strictMono
  cdf_zero_eq_half := standardGaussianCDF_zero_eq_half
  density_nonneg := standardGaussianDensity_nonneg
  cdf_nonneg := standardGaussianCDF_nonneg
  cdf_le_one := standardGaussianCDF_le_one

/-- Concrete standard-normal derivative API backed by mathlib's Gaussian CDF/PDF. -/
def standardGaussianDerivativeAPI : StandardGaussianDerivativeAPI where
  api := standardGaussianCDFAPI
  cdf_hasDerivAt_density := standardGaussianCDF_hasDerivAt_density
  density_pos := standardGaussianDensity_pos

/--
Same-side affine upper-tail delta comparison for the concrete standard normal.

If a faster left tail is compared against a slower positive-slope reference in
both the A-sub and B-full terms, then the A full-minus-sub upper-tail change is
eventually smaller than the corresponding B full-minus-sub change.  This is the
source-neutral Gaussian left-tail dominance step used in admissions/testing
proofs where the same group remains the slow tail before and after a policy
change.
-/
theorem standardGaussian_affineUpperTail_delta_lt_eventually_of_same_side_slope_order
    {interceptAFull slopeAFull interceptASub slopeASub
      interceptBFull slopeBFull interceptBSub slopeBSub : ℝ}
    (hslopeBSub_pos : 0 < slopeBSub)
    (hsubSlope : slopeBSub < slopeASub)
    (hBPolicySlope : slopeBSub < slopeBFull) :
    ∃ qDelta : ℝ, ∀ q : ℝ, qDelta < q →
      standardGaussianDerivativeAPI.affineUpperTail interceptAFull slopeAFull q -
          standardGaussianDerivativeAPI.affineUpperTail interceptASub slopeASub q <
        standardGaussianDerivativeAPI.affineUpperTail interceptBFull slopeBFull q -
          standardGaussianDerivativeAPI.affineUpperTail interceptBSub slopeBSub q := by
  have heps : 0 < (1 / 3 : ℝ) := by norm_num
  have hASub_ev : ∀ᶠ q in Filter.atTop,
      standardGaussianCDF (interceptASub - slopeASub * q) <
        (1 / 3 : ℝ) * standardGaussianCDF (interceptBSub - slopeBSub * q) :=
    standardGaussianCDF_affine_leftTail_lt_mul_eventually_of_slope_lt
      hslopeBSub_pos hsubSlope heps
  have hBFull_ev : ∀ᶠ q in Filter.atTop,
      standardGaussianCDF (interceptBFull - slopeBFull * q) <
        (1 / 3 : ℝ) * standardGaussianCDF (interceptBSub - slopeBSub * q) :=
    standardGaussianCDF_affine_leftTail_lt_mul_eventually_of_slope_lt
      hslopeBSub_pos hBPolicySlope heps
  have hdelta_ev : ∀ᶠ q in Filter.atTop,
      standardGaussianDerivativeAPI.affineUpperTail interceptAFull slopeAFull q -
          standardGaussianDerivativeAPI.affineUpperTail interceptASub slopeASub q <
        standardGaussianDerivativeAPI.affineUpperTail interceptBFull slopeBFull q -
          standardGaussianDerivativeAPI.affineUpperTail interceptBSub slopeBSub q := by
    filter_upwards [hASub_ev, hBFull_ev] with q hASub hBFull
    let cdfAFull := standardGaussianCDF (interceptAFull - slopeAFull * q)
    let cdfASub := standardGaussianCDF (interceptASub - slopeASub * q)
    let cdfBFull := standardGaussianCDF (interceptBFull - slopeBFull * q)
    let cdfBSub := standardGaussianCDF (interceptBSub - slopeBSub * q)
    have hBSub_pos : 0 < cdfBSub := by
      dsimp [cdfBSub]
      exact standardGaussianCDF_pos _
    have hAF_pos : 0 < cdfAFull := by
      dsimp [cdfAFull]
      exact standardGaussianCDF_pos _
    have hASub' : cdfASub < (1 / 3 : ℝ) * cdfBSub := by
      simpa [cdfASub, cdfBSub] using hASub
    have hBFull' : cdfBFull < (1 / 3 : ℝ) * cdfBSub := by
      simpa [cdfBFull, cdfBSub] using hBFull
    have hsum : cdfASub + cdfBFull < cdfBSub := by
      nlinarith
    dsimp [StandardGaussianDerivativeAPI.affineUpperTail]
    dsimp [standardGaussianDerivativeAPI]
    change (1 - cdfAFull) - (1 - cdfASub) <
      (1 - cdfBFull) - (1 - cdfBSub)
    nlinarith
  obtain ⟨qDelta, hqDelta⟩ := Filter.eventually_atTop.1 hdelta_ev
  exact ⟨qDelta, fun q hq => hqDelta q (le_of_lt hq)⟩

/-- Concrete standard-normal doubled-log-density API. -/
def standardGaussianDoubledLogDensityAPI : StandardGaussianDoubledLogDensityAPI where
  derivativeAPI := standardGaussianDerivativeAPI
  logDensityConstant := 2 * Real.log ((Real.sqrt (2 * Real.pi))⁻¹)
  doubled_log_density_eq := standardGaussianDoubledLogDensity_eq

/-- Concrete standard-normal analytic API used by admissions threshold proofs. -/
def standardGaussianAnalyticAPI : StandardGaussianAnalyticAPI where
  logAPI := standardGaussianDoubledLogDensityAPI
  cdf_tendsto_atBot_zero := standardGaussianCDF_tendsto_atBot

/-- Concrete standard-normal quantile API backed by the mathlib CDF bridge. -/
def standardGaussianQuantileAPI : StandardGaussianQuantileAPI where
  cdfAPI := standardGaussianCDFAPI
  quantile := standardGaussianQuantile
  cdf_quantile := standardGaussianCDF_standardGaussianQuantile
  quantile_mono := standardGaussianQuantile_monoOn
  quantile_continuous := standardGaussianQuantile_continuousOn
  quantile_pos_of_half_lt := standardGaussianQuantile_pos_of_half_lt

/--
Concrete standard-normal hazard-inverse certificate backed by mathlib's
`gaussianReal` CDF/PDF API and the Mills-ratio analytic facts in
`GaussianMills`.
-/
def standardGaussianHazardInverseCertificate :
    GaussianHazardInverseCertificate where
  api := standardGaussianCDFAPI
  hazard := standardGaussianHazard
  tail_pos := standardGaussianTail_pos
  hazard_eq := by
    intro z
    rfl
  hazard_pos := standardGaussianHazard_pos
  hazard_gt_arg_of_pos := by
    intro z hz
    rw [standardGaussianHazard_eq_millsHazard]
    exact gaussianMillsHazard_gt_arg_of_pos hz
  hazard_mono := standardGaussianHazard_mono
  scaled_hazard_mono := standardGaussian_scaled_hazard_mono
  scaled_hazard_strictMono := standardGaussian_scaled_hazard_strictMono
  hazardInv := standardGaussianHazardInv
  hazard_le_iff_le_inv := standardGaussianHazard_le_iff_le_inv

/--
For a fixed location-scale Gaussian law, the mathlib-backed standard-normal
upper-tail conditional mean is continuous in the threshold.
-/
theorem standardGaussian_normalUpperTailMean_continuous
    (L : GaussianScaleLaw) :
    Continuous
      (standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
        |>.normalUpperTailMean L) := by
  have hstd : Continuous (fun threshold : ℝ => L.standardize threshold) := by
    unfold GaussianScaleLaw.standardize
    fun_prop
  simpa [GaussianHazardCertificate.normalUpperTailMean,
    standardGaussianHazardInverseCertificate] using
    continuous_const.add
      (continuous_const.mul (standardGaussianHazard_continuous.comp hstd))

/--
For a fixed location-scale Gaussian law, the mathlib-backed standard-normal
upper-tail conditional mean is strictly increasing in the threshold.
-/
theorem standardGaussian_normalUpperTailMean_strictMono_threshold
    (L : GaussianScaleLaw) :
    StrictMono
      (standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
        |>.normalUpperTailMean L) := by
  intro x y hxy
  have hstd : L.standardize x < L.standardize y :=
    L.standardize_strictMono hxy
  have hhaz :
      standardGaussianHazard (L.standardize x) <
        standardGaussianHazard (L.standardize y) :=
    standardGaussianHazard_strictMono hstd
  have hscaled :
      L.scale * standardGaussianHazard (L.standardize x) <
        L.scale * standardGaussianHazard (L.standardize y) :=
    mul_lt_mul_of_pos_left hhaz L.scale_pos
  have hadd :
      L.mean + L.scale * standardGaussianHazard (L.standardize x) <
        L.mean + L.scale * standardGaussianHazard (L.standardize y) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_lt_add_left hscaled L.mean
  simpa [GaussianHazardCertificate.normalUpperTailMean,
    standardGaussianHazardInverseCertificate] using hadd

/--
For a fixed location-scale Gaussian law, the mathlib-backed standard-normal
upper-tail conditional mean is strictly above the threshold.
-/
theorem standardGaussian_normalUpperTailMean_gt_threshold
    (L : GaussianScaleLaw) (threshold : ℝ) :
    threshold <
      (standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
        |>.normalUpperTailMean L threshold) :=
  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
    |>.normalUpperTailMean_gt_threshold L threshold

/--
The interval from a Gaussian threshold up to its upper-tail conditional mean has
positive Gaussian mass.
-/
theorem standardGaussian_toMeasure_Ico_threshold_normalUpperTailMean_pos
    (L : GaussianScaleLaw) (threshold : ℝ) :
    0 < L.toMeasure
      (Ico threshold
        (standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
          |>.normalUpperTailMean L threshold)) :=
  L.toMeasure_Ico_pos
    (standardGaussian_normalUpperTailMean_gt_threshold L threshold)

end

end Probability
end AppliedModelingLib
