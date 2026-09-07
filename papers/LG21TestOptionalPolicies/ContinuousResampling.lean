import LG21TestOptionalPolicies.MainTheorems
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Continuous conditional resampling for LG21 Definition 6 and Theorem 4.4

The original paper has real Gaussian signals.  A PMF cannot represent those
signals, so this file gives the continuous measure-kernel version of the
resampling policy.  Access and no-access students use the same conditional
test kernel and the same posterior-estimate map.  Their conditional estimate
kernels therefore agree, and integrating those equal kernels against the
common base-profile law gives demographic equality.

The final section instantiates the construction with a real Gaussian test law
and proves the affine Gaussian pushforward used in the paper's Equation (2).
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open MeasureTheory
open ProbabilityTheory

/-! ## Continuous Definition 6 -/

/--
Continuous-kernel form of Definition 6.

`testGivenBase` is the conditional law of the optional test given the observed
base profile.  `posteriorEstimate base test` is the Bayesian posterior estimate
after adding that test value.  `posteriorEstimateKernel` packages the resulting
base-indexed pushforward as a measurable Markov kernel; the final field records
its pointwise pushforward identity.
-/
structure LG21ContinuousResamplingExperiment
    (Base Test Estimate : Type*)
    [MeasurableSpace Base] [MeasurableSpace Test] [MeasurableSpace Estimate]
    where
  baseLaw : Measure Base
  testGivenBase : Kernel Base Test
  posteriorEstimate : Base → Test → Estimate
  posteriorEstimate_measurable :
    ∀ base, Measurable (posteriorEstimate base)
  posteriorEstimateKernel : Kernel Base Estimate
  posteriorEstimateKernel_apply :
    ∀ base,
      posteriorEstimateKernel base =
        (testGivenBase base).map (posteriorEstimate base)
  baseLaw_isProbability : IsProbabilityMeasure baseLaw
  testGivenBase_isMarkov : IsMarkovKernel testGivenBase
  posteriorEstimateKernel_isMarkov : IsMarkovKernel posteriorEstimateKernel

/--
Definition 6 access-side estimate kernel: draw the actual conditional test and
apply the Bayesian posterior-estimate map.
-/
def lg21ContinuousAccessEstimateKernel
    {Base Test Estimate : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test] [MeasurableSpace Estimate]
    (e : LG21ContinuousResamplingExperiment Base Test Estimate) :
    Kernel Base Estimate :=
  e.posteriorEstimateKernel

/--
Definition 6 no-access estimate kernel: independently draw a synthetic test
from the same conditional test law and apply the same posterior-estimate map.
-/
def lg21ContinuousResamplingEstimateKernel
    {Base Test Estimate : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test] [MeasurableSpace Estimate]
    (e : LG21ContinuousResamplingExperiment Base Test Estimate) :
    Kernel Base Estimate :=
  e.posteriorEstimateKernel

/-- Access-side conditional estimate law is the stated continuous pushforward. -/
theorem paper_definition6_continuous_access_estimate_law
    {Base Test Estimate : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test] [MeasurableSpace Estimate]
    (e : LG21ContinuousResamplingExperiment Base Test Estimate)
    (base : Base) :
    lg21ContinuousAccessEstimateKernel e base =
      (e.testGivenBase base).map (e.posteriorEstimate base) :=
  e.posteriorEstimateKernel_apply base

/-- No-access resampling law is the same continuous pushforward. -/
theorem paper_definition6_continuous_no_access_resampling_law
    {Base Test Estimate : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test] [MeasurableSpace Estimate]
    (e : LG21ContinuousResamplingExperiment Base Test Estimate)
    (base : Base) :
    lg21ContinuousResamplingEstimateKernel e base =
      (e.testGivenBase base).map (e.posteriorEstimate base) :=
  e.posteriorEstimateKernel_apply base

/--
Theorem 4.4 observable-fairness core for arbitrary continuous conditional
kernels: the access and resampled no-access estimate laws agree at every base
profile.
-/
theorem paper_theorem4_4_continuous_resampling_observably_fair
    {Base Test Estimate : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test] [MeasurableSpace Estimate]
    (e : LG21ContinuousResamplingExperiment Base Test Estimate) :
    ∀ base,
      lg21ContinuousAccessEstimateKernel e base =
        lg21ContinuousResamplingEstimateKernel e base := by
  intro base
  rfl

/-- Demographic access-side estimate law after mixing over base profiles. -/
def lg21ContinuousDemographicAccessEstimateLaw
    {Base Test Estimate : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test] [MeasurableSpace Estimate]
    (e : LG21ContinuousResamplingExperiment Base Test Estimate) :
    Measure Estimate :=
  Measure.bind e.baseLaw (lg21ContinuousAccessEstimateKernel e)

/-- Demographic no-access estimate law after the same base-profile mixture. -/
def lg21ContinuousDemographicResamplingEstimateLaw
    {Base Test Estimate : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test] [MeasurableSpace Estimate]
    (e : LG21ContinuousResamplingExperiment Base Test Estimate) :
    Measure Estimate :=
  Measure.bind e.baseLaw (lg21ContinuousResamplingEstimateKernel e)

/-- The access demographic estimate law is a probability measure. -/
theorem lg21ContinuousDemographicAccessEstimateLaw_isProbability
    {Base Test Estimate : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test] [MeasurableSpace Estimate]
    (e : LG21ContinuousResamplingExperiment Base Test Estimate) :
    IsProbabilityMeasure (lg21ContinuousDemographicAccessEstimateLaw e) := by
  letI : IsProbabilityMeasure e.baseLaw := e.baseLaw_isProbability
  letI : IsMarkovKernel e.posteriorEstimateKernel :=
    e.posteriorEstimateKernel_isMarkov
  change IsProbabilityMeasure
    (Measure.bind e.baseLaw e.posteriorEstimateKernel)
  infer_instance

/-- The resampled no-access demographic estimate law is a probability measure. -/
theorem lg21ContinuousDemographicResamplingEstimateLaw_isProbability
    {Base Test Estimate : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test] [MeasurableSpace Estimate]
    (e : LG21ContinuousResamplingExperiment Base Test Estimate) :
    IsProbabilityMeasure (lg21ContinuousDemographicResamplingEstimateLaw e) := by
  letI : IsProbabilityMeasure e.baseLaw := e.baseLaw_isProbability
  letI : IsMarkovKernel e.posteriorEstimateKernel :=
    e.posteriorEstimateKernel_isMarkov
  change IsProbabilityMeasure
    (Measure.bind e.baseLaw e.posteriorEstimateKernel)
  infer_instance

/--
Theorem 4.4 demographic-fairness core: pointwise equality of the conditional
estimate kernels survives integration over the common continuous base law.
-/
theorem paper_theorem4_4_continuous_resampling_demographically_fair
    {Base Test Estimate : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test] [MeasurableSpace Estimate]
    (e : LG21ContinuousResamplingExperiment Base Test Estimate) :
    lg21ContinuousDemographicAccessEstimateLaw e =
      lg21ContinuousDemographicResamplingEstimateLaw e := by
  rfl

/-- Continuous observable and demographic conclusions of Theorem 4.4. -/
theorem paper_theorem4_4_continuous_resampling_fair
    {Base Test Estimate : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test] [MeasurableSpace Estimate]
    (e : LG21ContinuousResamplingExperiment Base Test Estimate) :
    (∀ base,
      lg21ContinuousAccessEstimateKernel e base =
        lg21ContinuousResamplingEstimateKernel e base) ∧
      lg21ContinuousDemographicAccessEstimateLaw e =
        lg21ContinuousDemographicResamplingEstimateLaw e :=
  ⟨paper_theorem4_4_continuous_resampling_observably_fair e,
    paper_theorem4_4_continuous_resampling_demographically_fair e⟩

/-! ## Threshold-acceptance interpretation following Theorem 4.4 -/

/--
The no-access student's threshold-acceptance probability is exactly the
conditional probability that the synthetic test would have produced a
posterior estimate above the threshold.
-/
theorem paper_theorem4_4_continuous_resampling_threshold_acceptance_probability
    {Base Test : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test]
    (e : LG21ContinuousResamplingExperiment Base Test ℝ)
    (base : Base) (cutoff : ℝ) :
    lg21ContinuousResamplingEstimateKernel e base (Set.Ici cutoff) =
      e.testGivenBase base
        {test | cutoff ≤ e.posteriorEstimate base test} := by
  rw [paper_definition6_continuous_no_access_resampling_law e base]
  rw [Measure.map_apply
    (e.posteriorEstimate_measurable base) measurableSet_Ici]
  rfl

/--
Access and no-access students have the same threshold-acceptance probability
at every observed base profile.
-/
theorem paper_theorem4_4_continuous_access_no_access_threshold_probability_eq
    {Base Test : Type*}
    [MeasurableSpace Base] [MeasurableSpace Test]
    (e : LG21ContinuousResamplingExperiment Base Test ℝ)
    (base : Base) (cutoff : ℝ) :
    lg21ContinuousAccessEstimateKernel e base (Set.Ici cutoff) =
      lg21ContinuousResamplingEstimateKernel e base (Set.Ici cutoff) := by
  rw [paper_theorem4_4_continuous_resampling_observably_fair e base]

/-! ## Gaussian Equation (2) -/

/--
Affine image of a real Gaussian measure.  This is the continuous probability
identity required to turn the Definition 6 pushforward into Equation (2).
-/
theorem lg21_gaussianReal_map_affine
    (mean : ℝ) (variance : NNReal) (intercept slope : ℝ) :
    (gaussianReal mean variance).map
        (fun test => intercept + slope * test) =
      gaussianReal (intercept + slope * mean)
        (NNReal.mk (slope ^ 2) (sq_nonneg slope) * variance) := by
  calc
    (gaussianReal mean variance).map
          (fun test => intercept + slope * test) =
        ((gaussianReal mean variance).map (fun test => slope * test)).map
          (fun estimate => intercept + estimate) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (gaussianReal (slope * mean)
          (NNReal.mk (slope ^ 2) (sq_nonneg slope) * variance)).map
          (fun estimate => intercept + estimate) := by
      rw [gaussianReal_map_const_mul]
    _ = gaussianReal (intercept + slope * mean)
          (NNReal.mk (slope ^ 2) (sq_nonneg slope) * variance) := by
      simpa [add_comm] using
        gaussianReal_map_const_add
          (μ := slope * mean)
          (v := NNReal.mk (slope ^ 2) (sq_nonneg slope) * variance)
          intercept

/--
One-base Gaussian instantiation of continuous Definition 6.  At a fixed base
profile the conditional test law is Gaussian and the posterior mean is affine
in the realized or synthetic test score.
-/
noncomputable def lg21GaussianContinuousResamplingAtBase
    (testMean : ℝ) (testVariance : NNReal) (intercept slope : ℝ) :
    LG21ContinuousResamplingExperiment PUnit ℝ ℝ where
  baseLaw := Measure.dirac PUnit.unit
  testGivenBase := Kernel.const PUnit (gaussianReal testMean testVariance)
  posteriorEstimate := fun _base test => intercept + slope * test
  posteriorEstimate_measurable := fun _base => by fun_prop
  posteriorEstimateKernel :=
    Kernel.const PUnit
      (gaussianReal (intercept + slope * testMean)
        (NNReal.mk (slope ^ 2) (sq_nonneg slope) * testVariance))
  posteriorEstimateKernel_apply := by
    intro base
    rw [Kernel.const_apply, Kernel.const_apply]
    exact
      (lg21_gaussianReal_map_affine
        testMean testVariance intercept slope).symm
  baseLaw_isProbability := by infer_instance
  testGivenBase_isMarkov := by infer_instance
  posteriorEstimateKernel_isMarkov := by infer_instance

/--
Continuous Gaussian Equation (2), in affine form: access and resampled
no-access estimates share the same Gaussian law.
-/
theorem paper_theorem4_4_common_gaussian_estimate_law_affine
    (testMean : ℝ) (testVariance : NNReal) (intercept slope : ℝ) :
    let e :=
      lg21GaussianContinuousResamplingAtBase
        testMean testVariance intercept slope
    lg21ContinuousAccessEstimateKernel e PUnit.unit =
        gaussianReal (intercept + slope * testMean)
          (NNReal.mk (slope ^ 2) (sq_nonneg slope) * testVariance) ∧
      lg21ContinuousResamplingEstimateKernel e PUnit.unit =
        gaussianReal (intercept + slope * testMean)
          (NNReal.mk (slope ^ 2) (sq_nonneg slope) * testVariance) := by
  dsimp [lg21GaussianContinuousResamplingAtBase,
    lg21ContinuousAccessEstimateKernel,
    lg21ContinuousResamplingEstimateKernel]
  exact ⟨rfl, rfl⟩

/-- Equation (2) mean simplification in precision notation. -/
theorem lg21_equation2_mean_precision
    (baseNumerator basePrecision testPrecision : ℝ)
    (hbase : basePrecision ≠ 0)
    (htotal : basePrecision + testPrecision ≠ 0) :
    baseNumerator / (basePrecision + testPrecision) +
        (testPrecision / (basePrecision + testPrecision)) *
          (baseNumerator / basePrecision) =
      baseNumerator / basePrecision := by
  field_simp [hbase, htotal]

/-- Equation (2) variance simplification in precision notation. -/
theorem lg21_equation2_variance_precision
    (basePrecision testPrecision : ℝ)
    (hbase : basePrecision ≠ 0)
    (htest : testPrecision ≠ 0)
    (htotal : basePrecision + testPrecision ≠ 0) :
    (testPrecision / (basePrecision + testPrecision)) ^ 2 *
        (1 / basePrecision + 1 / testPrecision) =
      1 / basePrecision - 1 / (basePrecision + testPrecision) := by
  field_simp [hbase, htest, htotal]
  ring

/--
Source-parameter Equation (2).  `baseNumerator / basePrecision` is the
posterior mean from the first `K-1` features; adding the test changes the
posterior with slope `testPrecision / (basePrecision + testPrecision)`.
The common access/resampling estimate law has the displayed tower-property
mean and variance reduction.
-/
theorem paper_theorem4_4_common_gaussian_estimate_law_equation2
    (baseNumerator basePrecision testPrecision : ℝ)
    (hbase : 0 < basePrecision) (htest : 0 < testPrecision) :
    let testMean := baseNumerator / basePrecision
    let testVariance : NNReal :=
      NNReal.mk (1 / basePrecision + 1 / testPrecision)
        (le_of_lt (add_pos (one_div_pos.mpr hbase) (one_div_pos.mpr htest)))
    let intercept := baseNumerator / (basePrecision + testPrecision)
    let slope := testPrecision / (basePrecision + testPrecision)
    let commonVariance : NNReal :=
      NNReal.mk
        (1 / basePrecision - 1 / (basePrecision + testPrecision))
        (by
          have htotal : 0 < basePrecision + testPrecision := add_pos hbase htest
          exact sub_nonneg.mpr
            (one_div_le_one_div_of_le hbase (le_add_of_nonneg_right htest.le)))
    let e :=
      lg21GaussianContinuousResamplingAtBase
        testMean testVariance intercept slope
    lg21ContinuousAccessEstimateKernel e PUnit.unit =
        gaussianReal testMean commonVariance ∧
      lg21ContinuousResamplingEstimateKernel e PUnit.unit =
        gaussianReal testMean commonVariance := by
  dsimp only
  have htotal : 0 < basePrecision + testPrecision := add_pos hbase htest
  have hmean :=
    lg21_equation2_mean_precision
      baseNumerator basePrecision testPrecision
      (ne_of_gt hbase) (ne_of_gt htotal)
  have hvariance :=
    lg21_equation2_variance_precision
      basePrecision testPrecision
      (ne_of_gt hbase) (ne_of_gt htest) (ne_of_gt htotal)
  have hvarianceNN :
      NNReal.mk
          ((testPrecision / (basePrecision + testPrecision)) ^ 2)
          (sq_nonneg (testPrecision / (basePrecision + testPrecision))) *
        NNReal.mk (1 / basePrecision + 1 / testPrecision)
          (le_of_lt (add_pos (one_div_pos.mpr hbase) (one_div_pos.mpr htest))) =
      NNReal.mk
          (1 / basePrecision - 1 / (basePrecision + testPrecision))
          (by
            exact sub_nonneg.mpr
              (one_div_le_one_div_of_le hbase
                (le_add_of_nonneg_right htest.le))) := by
    ext
    simpa using hvariance
  dsimp [lg21GaussianContinuousResamplingAtBase,
    lg21ContinuousAccessEstimateKernel,
    lg21ContinuousResamplingEstimateKernel]
  constructor <;> rw [hmean, hvarianceNN]

end

end LG21TestOptionalPolicies
