import KR21Monoculture.Simulation
import KR21Monoculture.OuterConditional
import AppliedModelingLib.Foundations.Probability.RenewalReward

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter Function
open scoped Topology BigOperators

namespace KR21Monoculture

/-!
# Semantically scoped simulation procedure for KR21

Source anchor: `2101.05853.txt:549-554` says that Definitions 2 and 3 can be
tested efficiently by simulation when the noise law and candidate law can be
sampled.  The source does not state a sampling oracle model, an accuracy or
confidence parameter, a lower margin, a boundedness/tail condition, or a
finite parameter domain.

This module records exactly what follows from simulation without adding those
unstated requirements:

* the Definition-2 score estimates the *unnormalized* disagreement gain;
* with positive disagreement probability, its sign is the source conditional
  sign;
* at a fixed parameter, IID integrable samples eventually identify a strictly
  positive score almost surely; and
* a finite parameter grid admits a union bound and can cover a domain only
  after an explicit quantitative regularity certificate.

It deliberately does not claim an efficient universal test over the real
parameters in Definitions 2 and 3.
-/

/-- The existing Definition-2 sample score is exactly the pairwise
independent-reranking gain.  In particular it is zero on first-choice
agreement, so it estimates the numerator of the source conditional
expectation rather than a differently conditioned quantity. -/
theorem definition2SampleScore_eq_rerankingGainOnPair {n : ℕ}
    (value : Candidate n → ℝ) (own independentFirst : Ranking n) :
    definition2SampleScore value own independentFirst =
      rerankingGainOnPair value own independentFirst := by
  by_cases h : firstChoice own = firstChoice independentFirst
  · have h0 : own 0 = independentFirst 0 := by
      simpa [firstChoice] using h
    simp [definition2SampleScore, rerankingGainOnPair, bestRemainingAfter,
      firstChoice, secondChoice, h0]
  · have h0 : own 0 ≠ independentFirst 0 := by
      simpa [firstChoice] using h
    simp [definition2SampleScore, rerankingGainOnPair, bestRemainingAfter,
      firstChoice, secondChoice, h0]

/-- After the outer draw from `D`, the Definition-2 simulation target is the
actual joint disagreement-gain numerator. -/
theorem definition2OuterSampleMean_eq_outerDisagreementGainNumerator {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) :
    definition2OuterSampleMean F D theta =
      F.outerDisagreementGainNumerator D theta := by
  rw [DistributionalAccuracyFamily.outerDisagreementGainNumerator_eq_outerExpected]
  unfold definition2OuterSampleMean DistributionalAccuracyFamily.outerExpected
  apply integral_congr_ae
  filter_upwards [] with value
  unfold expectedRerankingGain
  simp_rw [definition2SampleScore_eq_rerankingGainOnPair]

/-- With a non-null disagreement event, a positive Definition-2 simulation
target is equivalent to a positive source conditional gain.  The explicit
positivity premise is necessary because the source conditional expectation is
not meaningful on a zero-probability event. -/
theorem definition2OuterSampleMean_pos_iff_outerDisagreementConditionalGain_pos_of_pos
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (theta : ℝ)
    (hdisagreement : 0 < F.outerDisagreementProbability D theta) :
    0 < definition2OuterSampleMean F D theta ↔
      0 < F.outerDisagreementConditionalGain D theta := by
  rw [definition2OuterSampleMean_eq_outerDisagreementGainNumerator]
  unfold DistributionalAccuracyFamily.outerDisagreementConditionalGain
  rw [if_neg hdisagreement.ne']
  exact (zero_lt_div_iff_pos_right hdisagreement).symm

/-- A fixed-parameter positive score is eventually accepted almost surely by
the empirical sign test under IID integrable sampling.  This is consistency,
not a finite sample-complexity claim. -/
theorem ae_eventually_empiricalPositiveMarginTest_of_iid_positive_mean
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (X : ℕ → Omega → ℝ) (hintegrable : Integrable (X 0) mu)
    (hindep : Pairwise ((· ⟂ᵢ[mu] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) mu mu)
    (hmean : 0 < ∫ omega, X 0 omega ∂mu) :
    ∀ᵐ omega ∂mu, ∀ᶠ sampleCount : ℕ in atTop,
      empiricalPositiveMarginTest (Finset.range sampleCount) X omega := by
  have hlln := ae_tendsto_empirical_mean_real_of_iid
    X hintegrable hindep hident
  filter_upwards [hlln] with omega hlimit
  have hpositive : ∀ᶠ sampleCount : ℕ in atTop,
      0 < (∑ i ∈ Finset.range sampleCount, X i omega) / sampleCount :=
    hlimit.eventually_const_lt hmean
  filter_upwards [hpositive] with sampleCount hsampleCount
  simpa [empiricalPositiveMarginTest, empiricalMean] using hsampleCount

/-- The fixed-parameter consistency theorem combines over a finite grid.  It
still says nothing about parameters outside that supplied grid. -/
theorem ae_eventually_forall_empiricalPositiveMarginTest_on_finite_grid
    {Omega Parameter : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (grid : Finset Parameter) (X : Parameter → ℕ → Omega → ℝ)
    (hintegrable : ∀ parameter ∈ grid, Integrable (X parameter 0) mu)
    (hindep : ∀ parameter ∈ grid,
      Pairwise ((· ⟂ᵢ[mu] ·) on X parameter))
    (hident : ∀ parameter ∈ grid, ∀ i,
      IdentDistrib (X parameter i) (X parameter 0) mu mu)
    (hmean : ∀ parameter ∈ grid, 0 < ∫ omega, X parameter 0 omega ∂mu) :
    ∀ᵐ omega ∂mu, ∀ᶠ sampleCount : ℕ in atTop,
      ∀ parameter ∈ grid,
        empiricalPositiveMarginTest (Finset.range sampleCount)
          (X parameter) omega := by
  have hfixed : ∀ parameter ∈ grid, ∀ᵐ omega ∂mu,
      ∀ᶠ sampleCount : ℕ in atTop,
        empiricalPositiveMarginTest (Finset.range sampleCount)
          (X parameter) omega := by
    intro parameter hparameter
    exact ae_eventually_empiricalPositiveMarginTest_of_iid_positive_mean mu
      (X parameter) (hintegrable parameter hparameter)
      (hindep parameter hparameter) (hident parameter hparameter)
      (hmean parameter hparameter)
  have hall : ∀ᵐ omega ∂mu, ∀ parameter ∈ grid,
      ∀ᶠ sampleCount : ℕ in atTop,
        empiricalPositiveMarginTest (Finset.range sampleCount)
          (X parameter) omega := by
    rw [Finset.eventually_all]
    exact hfixed
  filter_upwards [hall] with omega homega
  rw [Finset.eventually_all]
  exact homega

/-- For a nonempty finite sample, failure of the empirical positive-sign test
is exactly a nonpositive empirical score sum. -/
theorem not_empiricalPositiveMarginTest_iff_sum_nonpositive_of_nonempty
    {Omega I : Type*} (samples : Finset I) (X : I → Omega → ℝ)
    (omega : Omega) (hsamples : samples.Nonempty) :
    ¬ empiricalPositiveMarginTest samples X omega ↔
      ∑ i ∈ samples, X i omega ≤ 0 := by
  have hcard : 0 < (samples.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hsamples
  unfold empiricalPositiveMarginTest empiricalMean
  rw [div_pos_iff_of_pos_right hcard]
  exact not_lt

/-- The finite-grid false-negative event for a family of pointwise score
tests.  No independence between different grid points is assumed or needed for
the union bound. -/
theorem measureReal_finiteGrid_any_false_negative_le_sum_hoeffding
    {Omega I Parameter : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (grid : Finset Parameter) (X : Parameter → I → Omega → ℝ)
    (samples : Finset I) (a b margin : Parameter → ℝ)
    (h_indep : ∀ parameter ∈ grid, iIndepFun (X parameter) mu)
    (h_meas : ∀ parameter ∈ grid, ∀ i ∈ samples,
      AEMeasurable (X parameter i) mu)
    (h_bound : ∀ parameter ∈ grid, ∀ i ∈ samples,
      ∀ᵐ omega ∂mu, X parameter i omega ∈ Set.Icc
        (a parameter) (b parameter))
    (hmargin : ∀ parameter ∈ grid, 0 < margin parameter)
    (hmean : ∀ parameter ∈ grid, ∀ i ∈ samples,
      margin parameter ≤ ∫ omega, X parameter i omega ∂mu) :
    mu.real {omega | ∃ parameter ∈ grid,
      ∑ i ∈ samples, X parameter i omega ≤ 0} ≤
      ∑ parameter ∈ grid, Real.exp
        (-((samples.card : ℝ) * margin parameter) ^ 2 /
          (2 * ((∑ _ ∈ samples,
            ((‖b parameter - a parameter‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  let failure : Parameter → Set Omega := fun parameter =>
    {omega | ∑ i ∈ samples, X parameter i omega ≤ 0}
  have hset : {omega | ∃ parameter ∈ grid,
      ∑ i ∈ samples, X parameter i omega ≤ 0} =
      ⋃ parameter ∈ grid, failure parameter := by
    ext omega
    simp [failure]
  rw [hset]
  calc
    mu.real (⋃ parameter ∈ grid, failure parameter) ≤
        ∑ parameter ∈ grid, mu.real (failure parameter) :=
      measureReal_biUnion_finset_le grid failure
    _ ≤ ∑ parameter ∈ grid, Real.exp
        (-((samples.card : ℝ) * margin parameter) ^ 2 /
          (2 * ((∑ _ ∈ samples,
            ((‖b parameter - a parameter‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
      refine Finset.sum_le_sum ?_
      intro parameter hparameter
      exact empirical_nonpositive_probability_le_hoeffding mu
        (h_indep parameter hparameter)
        (h_meas parameter hparameter)
        (h_bound parameter hparameter)
        (hmargin parameter hparameter)
        (hmean parameter hparameter)

/-- The finite-grid Hoeffding result stated directly for the implemented sign
test.  A nonempty sample set is the only additional algebraic premise needed
to replace a nonpositive sum by test failure. -/
theorem measureReal_finiteGrid_any_empirical_test_failure_le_sum_hoeffding
    {Omega I Parameter : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (grid : Finset Parameter) (X : Parameter → I → Omega → ℝ)
    (samples : Finset I) (a b margin : Parameter → ℝ)
    (hsamples : samples.Nonempty)
    (h_indep : ∀ parameter ∈ grid, iIndepFun (X parameter) mu)
    (h_meas : ∀ parameter ∈ grid, ∀ i ∈ samples,
      AEMeasurable (X parameter i) mu)
    (h_bound : ∀ parameter ∈ grid, ∀ i ∈ samples,
      ∀ᵐ omega ∂mu, X parameter i omega ∈ Set.Icc
        (a parameter) (b parameter))
    (hmargin : ∀ parameter ∈ grid, 0 < margin parameter)
    (hmean : ∀ parameter ∈ grid, ∀ i ∈ samples,
      margin parameter ≤ ∫ omega, X parameter i omega ∂mu) :
    mu.real {omega | ∃ parameter ∈ grid,
      ¬ empiricalPositiveMarginTest samples (X parameter) omega} ≤
      ∑ parameter ∈ grid, Real.exp
        (-((samples.card : ℝ) * margin parameter) ^ 2 /
          (2 * ((∑ _ ∈ samples,
            ((‖b parameter - a parameter‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  have hset : {omega | ∃ parameter ∈ grid,
      ¬ empiricalPositiveMarginTest samples (X parameter) omega} =
      {omega | ∃ parameter ∈ grid,
        ∑ i ∈ samples, X parameter i omega ≤ 0} := by
    ext omega
    constructor
    · rintro ⟨parameter, hparameter, hfailure⟩
      exact ⟨parameter, hparameter,
        (not_empiricalPositiveMarginTest_iff_sum_nonpositive_of_nonempty
          samples (X parameter) omega hsamples).mp hfailure⟩
    · rintro ⟨parameter, hparameter, hfailure⟩
      exact ⟨parameter, hparameter,
        (not_empiricalPositiveMarginTest_iff_sum_nonpositive_of_nonempty
          samples (X parameter) omega hsamples).mpr hfailure⟩
  rw [hset]
  exact measureReal_finiteGrid_any_false_negative_le_sum_hoeffding mu
    grid X samples a b margin h_indep h_meas h_bound hmargin hmean

/-- A finite grid certifies positivity on a parameter domain only after a
quantitative coverage and Lipschitz-margin condition.  This is the missing
bridge from finite simulation to the universal quantifiers in the source
Definitions 2 and 3. -/
theorem score_pos_on_domain_of_finite_grid_lipschitz_margin
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (domain : Set Parameter) (grid : Finset Parameter)
    (score : Parameter → ℝ) (radius lipschitz : ℝ)
    (hlipschitz_nonneg : 0 ≤ lipschitz)
    (hcover : ∀ parameter ∈ domain, ∃ gridPoint ∈ grid,
      dist parameter gridPoint ≤ radius)
    (hlipschitz : ∀ parameter ∈ domain, ∀ gridPoint ∈ grid,
      |score parameter - score gridPoint| ≤
        lipschitz * dist parameter gridPoint)
    (hgridMargin : ∀ gridPoint ∈ grid,
      lipschitz * radius < score gridPoint) :
    ∀ parameter ∈ domain, 0 < score parameter := by
  intro parameter hparameter
  rcases hcover parameter hparameter with ⟨gridPoint, hgridPoint, hdistance⟩
  have herror : |score parameter - score gridPoint| ≤ lipschitz * radius := by
    exact (hlipschitz parameter hparameter gridPoint hgridPoint).trans
      (mul_le_mul_of_nonneg_left hdistance hlipschitz_nonneg)
  have hlower : score gridPoint - lipschitz * radius ≤ score parameter := by
    linarith [neg_le_of_abs_le herror]
  have hpositive : 0 < score gridPoint - lipschitz * radius := by
    linarith [hgridMargin gridPoint hgridPoint]
  exact hpositive.trans_le hlower

end KR21Monoculture
