import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Order.IntermediateValue
import AppliedModelingLib.Foundations.Math.ThresholdCharacterization
import AppliedModelingLib.Foundations.Probability.Gaussian

namespace AppliedModelingLib
namespace Probability

/-!
# Gaussian CDF Derivative Interfaces

Derivative-facing wrappers for the abstract Gaussian CDF API.

## Main declarations

- `StandardGaussianDerivativeAPI`
- `StandardGaussianDerivativeAPI.affineUpperTail`
- `StandardGaussianDerivativeAPI.density_mul_slope_pos`
- `StandardGaussianDerivativeAPI.affineUpperTail_continuous`
- `StandardGaussianDerivativeAPI.affineUpperTail_hasDerivAt`
- `StandardGaussianDerivativeAPI.affineUpperTail_gt_iff_standardized_lt`
- `StandardGaussianDerivativeAPI.affineUpperTail_gt_iff_cutoff_lt_of_slope_lt`
- `StandardGaussianDerivativeAPI.affineUpperTailDifference_continuous`
- `StandardGaussianDerivativeAPI.affineUpperTailDifference_hasDerivAt`
- `StandardGaussianDoubledLogDensityAPI`
- `StandardGaussianDoubledLogDensityAPI.doubled_log_density_mul_slope_eq`
- `StandardGaussianTailLimitAPI`
- `StandardGaussianTailLimitAPI.affineUpperTail_tendsto_one_atTop_of_slope_pos`
- `StandardGaussianAnalyticAPI`
-/

noncomputable section

/--
Analytic derivative extension of `StandardGaussianCDFAPI`: the standard CDF has
the declared density as its derivative, and the density is positive.
-/
structure StandardGaussianDerivativeAPI where
  api : StandardGaussianCDFAPI
  cdf_hasDerivAt_density : ∀ z : ℝ, HasDerivAt api.cdf (api.density z) z
  density_pos : ∀ z : ℝ, 0 < api.density z

namespace StandardGaussianDerivativeAPI

/-- Upper-tail probability of an affine standardization `intercept - slope * q`. -/
def affineUpperTail (A : StandardGaussianDerivativeAPI)
    (intercept slope q : ℝ) : ℝ :=
  1 - A.api.cdf (intercept - slope * q)

/-- Precision-standardized Gaussian cutoff in affine true-skill form. -/
theorem precision_standardized_eq_affine
    {precision priorTerm threshold q : ℝ}
    (hprecision_pos : 0 < precision) :
    (priorTerm - precision * (q - threshold)) / Real.sqrt precision =
      (priorTerm + precision * threshold) / Real.sqrt precision -
        Real.sqrt precision * q := by
  have hsqrt_ne : Real.sqrt precision ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hprecision_pos)
  field_simp [hsqrt_ne]
  rw [Real.sq_sqrt hprecision_pos.le]
  ring

/--
Affine upper-tail probabilities are larger exactly when their standardized
cutoffs are smaller.
-/
theorem affineUpperTail_gt_iff_standardized_lt
    (A : StandardGaussianDerivativeAPI)
    {interceptA slopeA interceptB slopeB q : ℝ} :
    A.affineUpperTail interceptA slopeA q >
        A.affineUpperTail interceptB slopeB q ↔
      interceptA - slopeA * q < interceptB - slopeB * q := by
  constructor
  · intro htail
    have hcdf :
        A.api.cdf (interceptA - slopeA * q) <
          A.api.cdf (interceptB - slopeB * q) := by
      dsimp [affineUpperTail] at htail
      linarith
    exact A.api.cdf_strictMono.lt_iff_lt.mp hcdf
  · intro hstd
    have hcdf :
        A.api.cdf (interceptA - slopeA * q) <
          A.api.cdf (interceptB - slopeB * q) :=
      A.api.cdf_strictMono hstd
    dsimp [affineUpperTail]
    linarith

/--
Two affine standardized cutoffs with different slopes cross at the displayed
cutoff.
-/
theorem affineStandardized_lt_iff_cutoff_lt_of_slope_lt
    {interceptA slopeA interceptB slopeB q : ℝ}
    (hslope : slopeB < slopeA) :
    interceptA - slopeA * q < interceptB - slopeB * q ↔
      (interceptA - interceptB) / (slopeA - slopeB) < q := by
  have hden_pos : 0 < slopeA - slopeB := sub_pos.mpr hslope
  constructor
  · intro h
    rw [div_lt_iff₀ hden_pos]
    nlinarith
  · intro h
    rw [div_lt_iff₀ hden_pos] at h
    nlinarith

/--
If one affine standardized cutoff has the larger skill slope, it is eventually
strictly lower at high skills.
-/
theorem exists_eventual_affineStandardized_lt_of_slope_lt
    {interceptFast slopeFast interceptSlow slopeSlow : ℝ}
    (hslope : slopeSlow < slopeFast) :
    ∃ q0 : ℝ, ∀ q : ℝ, q0 < q →
      interceptFast - slopeFast * q <
        interceptSlow - slopeSlow * q := by
  refine ⟨(interceptFast - interceptSlow) / (slopeFast - slopeSlow), ?_⟩
  intro q hq
  have hden_pos : 0 < slopeFast - slopeSlow := sub_pos.mpr hslope
  rw [div_lt_iff₀ hden_pos] at hq
  nlinarith

/--
Affine upper-tail probabilities cross exactly above the affine cutoff when the
first standardized cutoff has the larger skill slope.
-/
theorem affineUpperTail_gt_iff_cutoff_lt_of_slope_lt
    (A : StandardGaussianDerivativeAPI)
    {interceptA slopeA interceptB slopeB q : ℝ}
    (hslope : slopeB < slopeA) :
    A.affineUpperTail interceptA slopeA q >
        A.affineUpperTail interceptB slopeB q ↔
      (interceptA - interceptB) / (slopeA - slopeB) < q := by
  rw [A.affineUpperTail_gt_iff_standardized_lt]
  exact affineStandardized_lt_iff_cutoff_lt_of_slope_lt hslope

/--
Comparison of two full-minus-sub affine Gaussian upper-tail changes from
standardized-endpoint order.  This is the reusable core behind large-skill
two-policy comparisons: if A's full-policy standardized cutoff is no larger
than B's, while A's test-free cutoff is strictly larger than B's, then the
admission change from using the full policy is larger for A.
-/
theorem affineUpperTail_delta_gt_of_standardized_endpoint_order
    (A : StandardGaussianDerivativeAPI)
    {zAFull zASub zBFull zBSub : ℝ}
    (hfull : zAFull ≤ zBFull)
    (hsub : zBSub < zASub) :
    (1 - A.api.cdf zAFull) - (1 - A.api.cdf zASub) >
      (1 - A.api.cdf zBFull) - (1 - A.api.cdf zBSub) := by
  have hfull_cdf : A.api.cdf zAFull ≤ A.api.cdf zBFull :=
    A.api.cdf_mono hfull
  have hsub_cdf : A.api.cdf zBSub < A.api.cdf zASub :=
    A.api.cdf_strictMono hsub
  linarith

/--
Affine-tail specialization of
`affineUpperTail_delta_gt_of_standardized_endpoint_order`.
-/
theorem affineUpperTail_delta_gt_of_affine_endpoint_order
    (A : StandardGaussianDerivativeAPI)
    {interceptAFull slopeAFull interceptASub slopeASub
      interceptBFull slopeBFull interceptBSub slopeBSub q : ℝ}
    (hfull :
      interceptAFull - slopeAFull * q ≤
        interceptBFull - slopeBFull * q)
    (hsub :
      interceptBSub - slopeBSub * q <
        interceptASub - slopeASub * q) :
    A.affineUpperTail interceptAFull slopeAFull q -
        A.affineUpperTail interceptASub slopeASub q >
      A.affineUpperTail interceptBFull slopeBFull q -
        A.affineUpperTail interceptBSub slopeBSub q := by
  simpa [affineUpperTail] using
    A.affineUpperTail_delta_gt_of_standardized_endpoint_order hfull hsub

/--
Large-skill affine-tail delta comparison from eventual standardized-endpoint
order.
-/
theorem affineUpperTail_delta_gt_eventually_of_affine_endpoint_order
    (A : StandardGaussianDerivativeAPI)
    {interceptAFull slopeAFull interceptASub slopeASub
      interceptBFull slopeBFull interceptBSub slopeBSub qDelta : ℝ}
    (hfull :
      ∀ q : ℝ, qDelta < q →
        interceptAFull - slopeAFull * q ≤
          interceptBFull - slopeBFull * q)
    (hsub :
      ∀ q : ℝ, qDelta < q →
        interceptBSub - slopeBSub * q <
          interceptASub - slopeASub * q) :
    ∀ q : ℝ, qDelta < q →
      A.affineUpperTail interceptAFull slopeAFull q -
          A.affineUpperTail interceptASub slopeASub q >
        A.affineUpperTail interceptBFull slopeBFull q -
          A.affineUpperTail interceptBSub slopeBSub q := by
  intro q hq
  exact A.affineUpperTail_delta_gt_of_affine_endpoint_order
    (hfull q hq) (hsub q hq)

/--
Conditional posterior-score threshold probabilities generated by
`GaussianOffsetSignalFamily` are affine standard-normal upper tails in true
skill.  The affine slope is the square root of total signal precision.
-/
theorem thresholdPassProb_conditionalPosteriorMeanScaleLaw_eq_affineUpperTail
    (A : StandardGaussianDerivativeAPI)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (M : GaussianOffsetSignalFamily ι) (threshold q : ℝ) :
    A.api.thresholdPassProb (M.conditionalPosteriorMeanScaleLaw q) threshold =
      A.affineUpperTail
        ((M.centeredFamily.priorPrecision * (threshold - M.priorMean) +
            M.centeredFamily.signalPrecisionSum * threshold) /
          Real.sqrt M.centeredFamily.signalPrecisionSum)
        (Real.sqrt M.centeredFamily.signalPrecisionSum) q := by
  rw [StandardGaussianCDFAPI.thresholdPassProb,
    StandardGaussianCDFAPI.normalTail, StandardGaussianCDFAPI.normalCDF,
    affineUpperTail,
    GaussianOffsetSignalFamily.conditionalPosteriorMeanScaleLaw_standardize_threshold]
  rw [precision_standardized_eq_affine M.centeredFamily.signalPrecisionSum_pos]

/--
Conditional posterior-score threshold probabilities cross at the affine cutoff
determined by their total signal precisions.  The first law has larger total
signal precision, hence a larger true-skill slope in the affine
standardization.
-/
theorem thresholdPassProb_conditionalPosteriorMeanScaleLaw_gt_iff_cutoff_lt_of_signalPrecisionSum_lt
    (A : StandardGaussianDerivativeAPI)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {M_A M_B : GaussianOffsetSignalFamily ι} {threshold q : ℝ}
    (hprecision :
      M_B.centeredFamily.signalPrecisionSum <
        M_A.centeredFamily.signalPrecisionSum) :
    A.api.thresholdPassProb
          (M_A.conditionalPosteriorMeanScaleLaw q) threshold >
        A.api.thresholdPassProb
          (M_B.conditionalPosteriorMeanScaleLaw q) threshold ↔
      (((M_A.centeredFamily.priorPrecision * (threshold - M_A.priorMean) +
              M_A.centeredFamily.signalPrecisionSum * threshold) /
            Real.sqrt M_A.centeredFamily.signalPrecisionSum) -
          ((M_B.centeredFamily.priorPrecision * (threshold - M_B.priorMean) +
              M_B.centeredFamily.signalPrecisionSum * threshold) /
            Real.sqrt M_B.centeredFamily.signalPrecisionSum)) /
        (Real.sqrt M_A.centeredFamily.signalPrecisionSum -
          Real.sqrt M_B.centeredFamily.signalPrecisionSum) <
        q := by
  have hslope :
      Real.sqrt M_B.centeredFamily.signalPrecisionSum <
        Real.sqrt M_A.centeredFamily.signalPrecisionSum :=
    Real.sqrt_lt_sqrt M_B.centeredFamily.signalPrecisionSum_pos.le
      hprecision
  rw [A.thresholdPassProb_conditionalPosteriorMeanScaleLaw_eq_affineUpperTail
      M_A threshold q,
    A.thresholdPassProb_conditionalPosteriorMeanScaleLaw_eq_affineUpperTail
      M_B threshold q]
  exact A.affineUpperTail_gt_iff_cutoff_lt_of_slope_lt hslope

/--
Large-skill affine-tail delta comparison from slope order alone.  The returned
threshold is the maximum of the two affine crossing points where the required
standardized-endpoint orders become true.
-/
theorem exists_affineUpperTail_delta_gt_eventually_of_slope_order
    (A : StandardGaussianDerivativeAPI)
    {interceptAFull slopeAFull interceptASub slopeASub
      interceptBFull slopeBFull interceptBSub slopeBSub : ℝ}
    (hfullSlope : slopeBFull < slopeAFull)
    (hsubSlope : slopeASub < slopeBSub) :
    ∃ qDelta : ℝ, ∀ q : ℝ, qDelta < q →
      A.affineUpperTail interceptAFull slopeAFull q -
          A.affineUpperTail interceptASub slopeASub q >
        A.affineUpperTail interceptBFull slopeBFull q -
          A.affineUpperTail interceptBSub slopeBSub q := by
  obtain ⟨qFull, hfull⟩ :=
    exists_eventual_affineStandardized_lt_of_slope_lt
      (interceptFast := interceptAFull) (slopeFast := slopeAFull)
      (interceptSlow := interceptBFull) (slopeSlow := slopeBFull)
      hfullSlope
  obtain ⟨qSub, hsub⟩ :=
    exists_eventual_affineStandardized_lt_of_slope_lt
      (interceptFast := interceptBSub) (slopeFast := slopeBSub)
      (interceptSlow := interceptASub) (slopeSlow := slopeASub)
      hsubSlope
  refine ⟨max qFull qSub, ?_⟩
  intro q hq
  have hqFull : qFull < q := lt_of_le_of_lt (le_max_left qFull qSub) hq
  have hqSub : qSub < q := lt_of_le_of_lt (le_max_right qFull qSub) hq
  exact A.affineUpperTail_delta_gt_of_affine_endpoint_order
    (le_of_lt (hfull q hqFull)) (hsub q hqSub)

/-- A positive affine slope gives a positive density-weighted derivative factor. -/
theorem density_mul_slope_pos
    (A : StandardGaussianDerivativeAPI)
    {z slope : ℝ} (hslope : 0 < slope) :
    0 < A.api.density z * slope :=
  mul_pos (A.density_pos z) hslope

/-- Derivative of an affine standardized upper tail. -/
theorem affineUpperTail_hasDerivAt
    (A : StandardGaussianDerivativeAPI)
    {intercept slope q : ℝ} :
    HasDerivAt (fun x : ℝ => A.affineUpperTail intercept slope x)
      (A.api.density (intercept - slope * q) * slope) q := by
  have hlin :
      HasDerivAt (fun x : ℝ => intercept - slope * x) (-slope) q := by
    simpa using (hasDerivAt_const q intercept).sub
      ((hasDerivAt_id q).const_mul slope)
  have hcdf :
      HasDerivAt (fun x : ℝ => A.api.cdf (intercept - slope * x))
        (A.api.density (intercept - slope * q) * (-slope)) q :=
    (A.cdf_hasDerivAt_density (intercept - slope * q)).comp q hlin
  have htail := (hasDerivAt_const q (1 : ℝ)).sub hcdf
  simpa [affineUpperTail, mul_comm, mul_left_comm, mul_assoc] using htail

/-- Continuity of an affine standardized upper tail. -/
theorem affineUpperTail_continuous
    (A : StandardGaussianDerivativeAPI)
    {intercept slope : ℝ} :
    Continuous (fun x : ℝ => A.affineUpperTail intercept slope x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (A.affineUpperTail_hasDerivAt (intercept := intercept)
    (slope := slope) (q := x)).continuousAt

/-- Continuity of the difference of two affine standardized upper tails. -/
theorem affineUpperTailDifference_continuous
    (A : StandardGaussianDerivativeAPI)
    {interceptA slopeA interceptB slopeB : ℝ} :
    Continuous
      (fun x : ℝ =>
        A.affineUpperTail interceptA slopeA x -
          A.affineUpperTail interceptB slopeB x) :=
  (A.affineUpperTail_continuous (intercept := interceptA)
    (slope := slopeA)).sub
    (A.affineUpperTail_continuous (intercept := interceptB)
      (slope := slopeB))

/-- Derivative of the difference of two affine standardized upper tails. -/
theorem affineUpperTailDifference_hasDerivAt
    (A : StandardGaussianDerivativeAPI)
    {interceptA slopeA interceptB slopeB q : ℝ} :
    HasDerivAt
      (fun x : ℝ =>
        A.affineUpperTail interceptA slopeA x -
          A.affineUpperTail interceptB slopeB x)
      (A.api.density (interceptA - slopeA * q) * slopeA -
        A.api.density (interceptB - slopeB * q) * slopeB) q := by
  exact A.affineUpperTail_hasDerivAt.sub A.affineUpperTail_hasDerivAt

end StandardGaussianDerivativeAPI

/--
Standard Gaussian derivative API with the usual doubled-log density formula.

For a standard normal density `φ`, this records
`2 * log (φ z) = -z^2 + constant`; the normalizing constant cancels in the
density comparisons used by threshold-admissions proofs.
-/
structure StandardGaussianDoubledLogDensityAPI where
  derivativeAPI : StandardGaussianDerivativeAPI
  logDensityConstant : ℝ
  doubled_log_density_eq :
    ∀ z : ℝ,
      2 * Real.log (derivativeAPI.api.density z) =
        - z ^ 2 + logDensityConstant

namespace StandardGaussianDoubledLogDensityAPI

/--
Doubled log of a density-weighted positive affine slope.  The normalizing
constant is retained explicitly so paired comparisons can cancel it.
-/
theorem doubled_log_density_mul_slope_eq
    (A : StandardGaussianDoubledLogDensityAPI)
    {z slope : ℝ} (hslope : 0 < slope) :
    2 * Real.log (A.derivativeAPI.api.density z * slope) =
      - z ^ 2 + 2 * Real.log slope + A.logDensityConstant := by
  have hdensity_pos : 0 < A.derivativeAPI.api.density z :=
    A.derivativeAPI.density_pos z
  have hlog_mul :
      Real.log (A.derivativeAPI.api.density z * slope) =
        Real.log (A.derivativeAPI.api.density z) + Real.log slope :=
    Real.log_mul hdensity_pos.ne' hslope.ne'
  calc
    2 * Real.log (A.derivativeAPI.api.density z * slope)
        = 2 * (Real.log (A.derivativeAPI.api.density z) + Real.log slope) := by
          rw [hlog_mul]
    _ = 2 * Real.log (A.derivativeAPI.api.density z) +
          2 * Real.log slope := by
          ring
    _ = (- z ^ 2 + A.logDensityConstant) + 2 * Real.log slope := by
          rw [A.doubled_log_density_eq z]
    _ = - z ^ 2 + 2 * Real.log slope + A.logDensityConstant := by
          ring

end StandardGaussianDoubledLogDensityAPI

/--
Standard Gaussian CDF tail-limit API.  For admissions threshold proofs, the
needed analytic fact is that `cdf z -> 0` as `z -> -∞`, so affine upper-tail
admission probabilities with positive skill slope tend to one.
-/
structure StandardGaussianTailLimitAPI where
  derivativeAPI : StandardGaussianDerivativeAPI
  cdf_tendsto_atBot_zero :
    Filter.Tendsto derivativeAPI.api.cdf Filter.atBot (nhds 0)

namespace StandardGaussianTailLimitAPI

/-- Affine standardized upper-tail probabilities tend to one for high skill. -/
theorem affineUpperTail_tendsto_one_atTop_of_slope_pos
    (A : StandardGaussianTailLimitAPI)
    {intercept slope : ℝ} (hslope : 0 < slope) :
    Filter.Tendsto
      (fun q : ℝ => A.derivativeAPI.affineUpperTail intercept slope q)
      Filter.atTop (nhds 1) := by
  have hneg : -slope < 0 := by
    linarith
  have hlin :
      Filter.Tendsto (fun q : ℝ => intercept - slope * q)
        Filter.atTop Filter.atBot := by
    have hmul :
        Filter.Tendsto (fun q : ℝ => (-slope) * q + intercept)
          Filter.atTop Filter.atBot :=
      (Filter.Tendsto.const_mul_atTop_of_neg hneg Filter.tendsto_id).atBot_add
        tendsto_const_nhds
    convert hmul using 1
    ext q
    ring
  have hcdf :
      Filter.Tendsto
        (fun q : ℝ => A.derivativeAPI.api.cdf (intercept - slope * q))
        Filter.atTop (nhds 0) :=
    A.cdf_tendsto_atBot_zero.comp hlin
  simpa [StandardGaussianDerivativeAPI.affineUpperTail] using
    tendsto_const_nhds.sub hcdf

/--
The difference of two affine standardized upper-tail probabilities with
positive skill slopes tends to zero for high skill.
-/
theorem affineUpperTailDifference_tendsto_zero_atTop_of_slope_pos
    (A : StandardGaussianTailLimitAPI)
    {interceptA slopeA interceptB slopeB : ℝ}
    (hslopeA : 0 < slopeA) (hslopeB : 0 < slopeB) :
    Filter.Tendsto
      (fun q : ℝ =>
        A.derivativeAPI.affineUpperTail interceptA slopeA q -
          A.derivativeAPI.affineUpperTail interceptB slopeB q)
      Filter.atTop (nhds 0) := by
  have hA :=
    A.affineUpperTail_tendsto_one_atTop_of_slope_pos
      (intercept := interceptA) (slope := slopeA) hslopeA
  have hB :=
    A.affineUpperTail_tendsto_one_atTop_of_slope_pos
      (intercept := interceptB) (slope := slopeB) hslopeB
  simpa using hA.sub hB

end StandardGaussianTailLimitAPI

namespace StandardGaussianCDFAPI

theorem thresholdPassProb_tendsto_atBot_one
    (api : StandardGaussianCDFAPI)
    (hcdf_atBot : Filter.Tendsto api.cdf Filter.atBot (nhds 0))
    (L : GaussianScaleLaw) :
    Filter.Tendsto (api.thresholdPassProb L) Filter.atBot (nhds 1) := by
  have hlin :
      Filter.Tendsto (fun threshold : ℝ => L.standardize threshold)
        Filter.atBot Filter.atBot := by
    have hscale_inv_pos : 0 < L.scale⁻¹ := inv_pos.mpr L.scale_pos
    have hmul :
        Filter.Tendsto (fun threshold : ℝ => L.scale⁻¹ * threshold + (-L.mean / L.scale))
          Filter.atBot Filter.atBot :=
      ((Filter.tendsto_const_mul_atBot_of_pos hscale_inv_pos).2 Filter.tendsto_id).atBot_add
        tendsto_const_nhds
    convert hmul using 1
    ext threshold
    rw [GaussianScaleLaw.standardize]
    field_simp [ne_of_gt L.scale_pos]
    ring
  have hcdf :
      Filter.Tendsto (fun threshold : ℝ => api.cdf (L.standardize threshold))
        Filter.atBot (nhds 0) :=
    hcdf_atBot.comp hlin
  simpa [thresholdPassProb, normalTail, normalCDF] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub hcdf

theorem thresholdPassProb_tendsto_atTop_zero
    (api : StandardGaussianCDFAPI)
    (hcdf_atTop : Filter.Tendsto api.cdf Filter.atTop (nhds 1))
    (L : GaussianScaleLaw) :
    Filter.Tendsto (api.thresholdPassProb L) Filter.atTop (nhds 0) := by
  have hlin :
      Filter.Tendsto (fun threshold : ℝ => L.standardize threshold)
        Filter.atTop Filter.atTop := by
    have hscale_inv_pos : 0 < L.scale⁻¹ := inv_pos.mpr L.scale_pos
    have hmul :
        Filter.Tendsto (fun threshold : ℝ => L.scale⁻¹ * threshold + (-L.mean / L.scale))
          Filter.atTop Filter.atTop :=
      ((Filter.tendsto_const_mul_atTop_of_pos hscale_inv_pos).2 Filter.tendsto_id).atTop_add
        tendsto_const_nhds
    convert hmul using 1
    ext threshold
    rw [GaussianScaleLaw.standardize]
    field_simp [ne_of_gt L.scale_pos]
    ring
  have hcdf :
      Filter.Tendsto (fun threshold : ℝ => api.cdf (L.standardize threshold))
        Filter.atTop (nhds 1) :=
    hcdf_atTop.comp hlin
  have htail :
      Filter.Tendsto (fun threshold : ℝ => 1 - api.cdf (L.standardize threshold))
        Filter.atTop (nhds (1 - 1)) :=
    (tendsto_const_nhds (x := (1 : ℝ))).sub hcdf
  simpa [thresholdPassProb, normalTail, normalCDF] using htail

theorem mixtureTailMass_continuous
    (api : StandardGaussianCDFAPI)
    {γ : Type*} [Fintype γ]
    (weight : γ → ℝ) (law : γ → GaussianScaleLaw) :
    Continuous (api.mixtureTailMass weight law) := by
  change Continuous
    (fun threshold : ℝ => ∑ g : γ, weight g * api.thresholdPassProb (law g) threshold)
  exact continuous_finset_sum Finset.univ (by
    intro g _hg
    exact continuous_const.mul (api.thresholdPassProb_continuous (law g)))

theorem mixtureTailMass_tendsto_atBot_sum_weights
    (api : StandardGaussianCDFAPI)
    (hcdf_atBot : Filter.Tendsto api.cdf Filter.atBot (nhds 0))
    {γ : Type*} [Fintype γ]
    (weight : γ → ℝ) (law : γ → GaussianScaleLaw) :
    Filter.Tendsto (api.mixtureTailMass weight law) Filter.atBot
      (nhds (∑ g : γ, weight g)) := by
  simpa [mixtureTailMass] using
    tendsto_finset_sum Finset.univ (fun g _hg =>
      (tendsto_const_nhds (x := weight g)).mul
        (api.thresholdPassProb_tendsto_atBot_one hcdf_atBot (law g)))

theorem mixtureTailMass_tendsto_atTop_zero
    (api : StandardGaussianCDFAPI)
    (hcdf_atTop : Filter.Tendsto api.cdf Filter.atTop (nhds 1))
    {γ : Type*} [Fintype γ]
    (weight : γ → ℝ) (law : γ → GaussianScaleLaw) :
    Filter.Tendsto (api.mixtureTailMass weight law) Filter.atTop (nhds 0) := by
  simpa [mixtureTailMass] using
    tendsto_finset_sum Finset.univ (fun g _hg =>
      (tendsto_const_nhds (x := weight g)).mul
        (api.thresholdPassProb_tendsto_atTop_zero hcdf_atTop (law g)))

theorem exists_mixtureTailMass_eq_of_capacity_mem_Ioo
    (api : StandardGaussianCDFAPI)
    (hcdf_atBot : Filter.Tendsto api.cdf Filter.atBot (nhds 0))
    (hcdf_atTop : Filter.Tendsto api.cdf Filter.atTop (nhds 1))
    {γ : Type*} [Fintype γ]
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw} {capacity : ℝ}
    (hcapacity : capacity ∈ Set.Ioo (0 : ℝ) (∑ g : γ, weight g)) :
    ∃ threshold : ℝ, api.mixtureTailMass weight law threshold = capacity := by
  have htop :
      ∀ᶠ threshold in Filter.atTop,
        api.mixtureTailMass weight law threshold < capacity :=
    (api.mixtureTailMass_tendsto_atTop_zero hcdf_atTop weight law).eventually
      (eventually_lt_nhds hcapacity.1)
  have hbot :
      ∀ᶠ threshold in Filter.atBot,
        capacity < api.mixtureTailMass weight law threshold :=
    (api.mixtureTailMass_tendsto_atBot_sum_weights hcdf_atBot weight law).eventually
      (eventually_gt_nhds hcapacity.2)
  rcases htop.exists with ⟨thresholdTop, hthresholdTop⟩
  rcases hbot.exists with ⟨thresholdBot, hthresholdBot⟩
  rcases mem_range_of_exists_le_of_exists_ge
      (api.mixtureTailMass_continuous weight law)
      ⟨thresholdTop, le_of_lt hthresholdTop⟩
      ⟨thresholdBot, le_of_lt hthresholdBot⟩ with ⟨threshold, hthreshold⟩
  exact ⟨threshold, hthreshold⟩

theorem existsUnique_mixtureTailMass_eq_of_capacity_mem_Ioo
    (api : StandardGaussianCDFAPI)
    (hcdf_atBot : Filter.Tendsto api.cdf Filter.atBot (nhds 0))
    (hcdf_atTop : Filter.Tendsto api.cdf Filter.atTop (nhds 1))
    {γ : Type*} [Fintype γ]
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw} {capacity : ℝ}
    (hweight : ∀ g, 0 ≤ weight g) (hpos : ∃ g, 0 < weight g)
    (hcapacity : capacity ∈ Set.Ioo (0 : ℝ) (∑ g : γ, weight g)) :
    ∃! threshold : ℝ, api.mixtureTailMass weight law threshold = capacity := by
  rcases api.exists_mixtureTailMass_eq_of_capacity_mem_Ioo
      hcdf_atBot hcdf_atTop hcapacity with ⟨threshold, hthreshold⟩
  refine ⟨threshold, hthreshold, ?_⟩
  intro threshold' hthreshold'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict :=
      api.mixtureTailMass_strictAnti_threshold (law := law) hweight hpos hlt
    rw [hthreshold, hthreshold'] at hstrict
    exact (lt_irrefl capacity) hstrict
  · have hstrict :=
      api.mixtureTailMass_strictAnti_threshold (law := law) hweight hpos hgt
    rw [hthreshold', hthreshold] at hstrict
    exact (lt_irrefl capacity) hstrict

/--
Unique finite Gaussian-mixture capacity cutoff, including the threshold-region
characterization.

If the target capacity lies strictly between zero and the total mixture weight,
then the common threshold realizing that capacity is unique, and the set of
thresholds whose upper-tail mass is at most capacity is exactly the upper ray
above the capacity cutoff.
-/
theorem existsUnique_mixtureTailMass_eq_and_region_of_capacity_mem_Ioo
    (api : StandardGaussianCDFAPI)
    (hcdf_atBot : Filter.Tendsto api.cdf Filter.atBot (nhds 0))
    (hcdf_atTop : Filter.Tendsto api.cdf Filter.atTop (nhds 1))
    {γ : Type*} [Fintype γ]
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw} {capacity : ℝ}
    (hweight : ∀ g, 0 ≤ weight g) (hpos : ∃ g, 0 < weight g)
    (hcapacity : capacity ∈ Set.Ioo (0 : ℝ) (∑ g : γ, weight g)) :
    ∃! threshold : ℝ,
      api.mixtureTailMass weight law threshold = capacity ∧
        ∀ z : ℝ,
          api.mixtureTailMass weight law z ≤ capacity ↔ threshold ≤ z := by
  exact
    AppliedModelingLib.existsUnique_eq_and_upper_region_of_continuous_strictAnti_tendsto_atBot_atTop
      (api.mixtureTailMass_continuous weight law)
      (api.mixtureTailMass_strictAnti_threshold (law := law) hweight hpos)
      (api.mixtureTailMass_tendsto_atBot_sum_weights hcdf_atBot weight law)
      (api.mixtureTailMass_tendsto_atTop_zero hcdf_atTop weight law)
      hcapacity

end StandardGaussianCDFAPI

/--
Combined standard Gaussian analytic API for threshold-admissions papers:
differentiability, positive density, doubled-log density, and the left-tail CDF
limit share the same CDF/density implementation.
-/
structure StandardGaussianAnalyticAPI where
  logAPI : StandardGaussianDoubledLogDensityAPI
  cdf_tendsto_atBot_zero :
    Filter.Tendsto logAPI.derivativeAPI.api.cdf Filter.atBot (nhds 0)

namespace StandardGaussianAnalyticAPI

/-- Forget the doubled-log fields and expose the tail-limit API. -/
def tailLimitAPI (A : StandardGaussianAnalyticAPI) :
    StandardGaussianTailLimitAPI where
  derivativeAPI := A.logAPI.derivativeAPI
  cdf_tendsto_atBot_zero := A.cdf_tendsto_atBot_zero

end StandardGaussianAnalyticAPI

end

end Probability
end AppliedModelingLib
