import AppliedModelingLib.Queueing.PoissonAsymptotics
import AppliedModelingLib.Foundations.Math.NonnegativeSequenceCompactness
import AppliedModelingLib.Foundations.Probability.GaussianMathlib
import Mathlib.Tactic

/-!
# QED limits for many-server queues

This module isolates the algebraic part of the Halfin--Whitt (QED) stationary
limit: once the finite head and geometric-tail normalizer components converge,
the Erlang-C delay probability has the corresponding ratio limit.  Proving the
Poisson and Stirling component limits is a separate analytic layer.
-/

namespace AppliedModelingLib
namespace Probability
namespace Queueing

open Filter Topology

/-- The classical Halfin--Whitt limit for the Erlang-C delay probability at a
strictly positive spare-capacity parameter. -/
noncomputable def halfinWhittDelayLimit (beta : ℝ) : ℝ :=
  (1 + Real.sqrt (2 * Real.pi) * beta * standardGaussianCDF beta *
    Real.exp (beta ^ 2 / 2))⁻¹

/-- At a positive spare-capacity parameter, the Halfin--Whitt delay limit is
strictly positive. -/
theorem halfinWhittDelayLimit_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < halfinWhittDelayLimit beta := by
  unfold halfinWhittDelayLimit
  apply inv_pos.mpr
  have hroot_pos : 0 < Real.sqrt (2 * Real.pi) := by
    apply Real.sqrt_pos.2
    exact mul_pos (by norm_num) Real.pi_pos
  have hterm_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) * beta *
      standardGaussianCDF beta * Real.exp (beta ^ 2 / 2) := by
    exact (mul_pos (mul_pos (mul_pos hroot_pos hbeta) (standardGaussianCDF_pos beta))
      (Real.exp_pos _)).le
  linarith

/-- At a positive spare-capacity parameter, the Halfin--Whitt delay limit is
strictly below one. -/
theorem halfinWhittDelayLimit_lt_one {beta : ℝ} (hbeta : 0 < beta) :
    halfinWhittDelayLimit beta < 1 := by
  unfold halfinWhittDelayLimit
  apply inv_lt_one_of_one_lt₀
  have hroot_pos : 0 < Real.sqrt (2 * Real.pi) := by
    apply Real.sqrt_pos.2
    exact mul_pos (by norm_num) Real.pi_pos
  have hterm_pos : 0 < Real.sqrt (2 * Real.pi) * beta *
      standardGaussianCDF beta * Real.exp (beta ^ 2 / 2) := by
    exact mul_pos (mul_pos (mul_pos hroot_pos hbeta) (standardGaussianCDF_pos beta))
      (Real.exp_pos _)
  linarith

/-- On positive spare-capacity parameters, the limiting delay probability is
strictly decreasing. -/
theorem halfinWhittDelayLimit_strictAntiOn_Ioi :
    StrictAntiOn halfinWhittDelayLimit (Set.Ioi 0) := by
  intro first hfirst second hsecond hfirst_second
  have hfirst_pos : 0 < first := hfirst
  have hsecond_pos : 0 < second := hsecond
  have hroot_pos : 0 < Real.sqrt (2 * Real.pi) := by
    apply Real.sqrt_pos.2
    exact mul_pos (by norm_num) Real.pi_pos
  have hcdf_first_pos : 0 < standardGaussianCDF first :=
    standardGaussianCDF_pos first
  have hsquares : first ^ 2 < second ^ 2 := by
    nlinarith
  have hexp : Real.exp (first ^ 2 / 2) < Real.exp (second ^ 2 / 2) := by
    apply Real.exp_lt_exp.mpr
    linarith
  have hterms :
      first * standardGaussianCDF first * Real.exp (first ^ 2 / 2) <
        second * standardGaussianCDF second * Real.exp (second ^ 2 / 2) := by
    calc
      first * standardGaussianCDF first * Real.exp (first ^ 2 / 2) <
          second * standardGaussianCDF first * Real.exp (first ^ 2 / 2) := by
        gcongr
      _ ≤ second * standardGaussianCDF second * Real.exp (first ^ 2 / 2) := by
        gcongr
        exact standardGaussianCDF_mono hfirst_second.le
      _ < second * standardGaussianCDF second * Real.exp (second ^ 2 / 2) := by
        gcongr
        exact mul_pos hsecond_pos (standardGaussianCDF_pos second)
  have hden_first_pos : 0 <
      1 + Real.sqrt (2 * Real.pi) * first * standardGaussianCDF first *
        Real.exp (first ^ 2 / 2) := by
    positivity
  have hden_lt :
      1 + Real.sqrt (2 * Real.pi) * first * standardGaussianCDF first *
        Real.exp (first ^ 2 / 2) <
      1 + Real.sqrt (2 * Real.pi) * second * standardGaussianCDF second *
        Real.exp (second ^ 2 / 2) := by
    nlinarith [mul_lt_mul_of_pos_left hterms hroot_pos]
  unfold halfinWhittDelayLimit
  exact inv_strictAnti₀ hden_first_pos hden_lt

/-- The limiting geometric-tail normalizer under Halfin--Whitt scaling. -/
noncomputable def halfinWhittTailNormalizerLimit (beta : ℝ) : ℝ :=
  Real.exp (-(beta ^ 2 / 2)) / (beta * Real.sqrt (2 * Real.pi))

/-- The usual closed form of the Halfin--Whitt Erlang-C limit is the ratio of
the limiting tail normalizer to the sum of the Gaussian head and tail
normalizers. -/
theorem halfinWhittDelayLimit_eq_componentRatio
    {beta : ℝ} (hbeta : 0 < beta) :
    halfinWhittDelayLimit beta =
      halfinWhittTailNormalizerLimit beta /
        (standardGaussianCDF beta + halfinWhittTailNormalizerLimit beta) := by
  have hroot_pos : 0 < Real.sqrt (2 * Real.pi) := by
    apply Real.sqrt_pos.2
    exact mul_pos (by norm_num) Real.pi_pos
  have hcdf_pos : 0 < standardGaussianCDF beta := standardGaussianCDF_pos beta
  have htail_pos : 0 < halfinWhittTailNormalizerLimit beta := by
    unfold halfinWhittTailNormalizerLimit
    exact div_pos (Real.exp_pos _) (mul_pos hbeta hroot_pos)
  have hproduct_pos : 0 <
      Real.sqrt (2 * Real.pi) * beta * standardGaussianCDF beta *
        Real.exp (beta ^ 2 / 2) := by
    exact mul_pos (mul_pos (mul_pos hroot_pos hbeta) hcdf_pos) (Real.exp_pos _)
  have hleft_ne : 1 + Real.sqrt (2 * Real.pi) * beta *
      standardGaussianCDF beta * Real.exp (beta ^ 2 / 2) ≠ 0 := by
    nlinarith
  have hright_ne : standardGaussianCDF beta +
      halfinWhittTailNormalizerLimit beta ≠ 0 := by
    exact ne_of_gt (add_pos hcdf_pos htail_pos)
  have hscale_ne : beta * Real.sqrt (2 * Real.pi) ≠ 0 :=
    mul_ne_zero (ne_of_gt hbeta) (ne_of_gt hroot_pos)
  unfold halfinWhittDelayLimit halfinWhittTailNormalizerLimit
  field_simp [hleft_ne, hright_ne, hscale_ne]
  have hexp : Real.exp (beta ^ 2 / 2) * Real.exp (-(beta ^ 2 / 2)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    Real.sqrt (2 * Real.pi) * beta * standardGaussianCDF beta +
        Real.exp (-(beta ^ 2 / 2)) =
      Real.sqrt (2 * Real.pi) * beta * standardGaussianCDF beta * 1 +
        Real.exp (-(beta ^ 2 / 2)) := by ring
    _ = Real.sqrt (2 * Real.pi) * beta * standardGaussianCDF beta *
        (Real.exp (beta ^ 2 / 2) * Real.exp (-(beta ^ 2 / 2))) +
        Real.exp (-(beta ^ 2 / 2)) := by rw [hexp]
    _ = (1 + Real.sqrt (2 * Real.pi) * beta * standardGaussianCDF beta *
        Real.exp (beta ^ 2 / 2)) * Real.exp (-(beta ^ 2 / 2)) := by ring

/-- The Halfin--Whitt delay limit is equivalently the ratio of the local
Gaussian point-mass limit to the scaled lower-tail denominator. -/
theorem halfinWhittDelayLimit_eq_poissonComponentRatio
    {beta : ℝ} (hbeta : 0 < beta) :
    halfinWhittDelayLimit beta =
      standardGaussianDensity beta /
        (beta * standardGaussianCDF beta + standardGaussianDensity beta) := by
  rw [halfinWhittDelayLimit_eq_componentRatio hbeta,
    standardGaussianDensity_eq_mills_integrand]
  unfold halfinWhittTailNormalizerLimit
  have hroot_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp [hbeta.ne', hroot_ne]

/-- Convergence of the finite and tail normalizer components implies
convergence of the corresponding Erlang-C delay probabilities. -/
theorem tendsto_manyServerDelayProbability_of_component_limits
    {trafficIntensity : ℕ → ℝ} {headLimit tailLimit : ℝ}
    (hhead : Tendsto
      (fun n : ℕ => manyServerHeadNormalizer (trafficIntensity n) n)
      atTop (𝓝 headLimit))
    (htail : Tendsto
      (fun n : ℕ => manyServerTailNormalizer (trafficIntensity n) n)
      atTop (𝓝 tailLimit))
    (hnormalizer : headLimit + tailLimit ≠ 0) :
    Tendsto
      (fun n : ℕ => manyServerDelayProbability (trafficIntensity n) n)
      atTop (𝓝 (tailLimit / (headLimit + tailLimit))) := by
  have hratio := htail.div (hhead.add htail) hnormalizer
  apply (Tendsto.congr (fun n => ?_)) hratio
  rw [manyServerDelayProbability_eq_tailNormalizer_div_normalizer,
    manyServerStationaryNormalizer_eq_head_add_tail]
  rfl

/-- The exact Poisson representation of Erlang-C has a finite QED-scale
limit: the Poisson point mass and spare capacity are both multiplied by the
square-root server scale before taking the ratio. -/
theorem tendsto_manyServerDelayProbability_of_scaled_poisson_component_limits
    {trafficIntensity : ℕ → NNReal} {servers : ℕ → ℕ}
    {lowerTailLimit scaledPointLimit scaledGapLimit : ℝ}
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hservers_pos : ∀ᶠ n : ℕ in atTop, 0 < servers n)
    (hlowerTail : Tendsto
      (fun n : ℕ => poissonLowerTailProbability (servers n * trafficIntensity n) (servers n))
      atTop (𝓝 lowerTailLimit))
    (hscaledPoint : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) *
        poissonPointProbability (servers n * trafficIntensity n) (servers n))
      atTop (𝓝 scaledPointLimit))
    (hscaledGap : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop (𝓝 scaledGapLimit))
    (hdenominator : scaledGapLimit * lowerTailLimit + scaledPointLimit ≠ 0) :
    Tendsto
      (fun n : ℕ => manyServerDelayProbability (trafficIntensity n : ℝ) (servers n))
      atTop
      (𝓝 (scaledPointLimit /
        (scaledGapLimit * lowerTailLimit + scaledPointLimit))) := by
  have hscaledDenominator := (hscaledGap.mul hlowerTail).add hscaledPoint
  have hratio := hscaledPoint.div hscaledDenominator hdenominator
  refine Tendsto.congr' ?_ hratio
  filter_upwards [hservers_pos] with n hn
  rw [manyServerDelayProbability_eq_poissonRatio (trafficIntensity n) (servers n)
    (htraffic_lt_one n)]
  have hnat_pos : 0 < (servers n : ℝ) := by
    exact_mod_cast hn
  have hsqrt_ne : Real.sqrt (servers n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hnat_pos).ne'
  change
    (Real.sqrt (servers n : ℝ) *
        poissonPointProbability (servers n * trafficIntensity n) (servers n) /
        ((Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ))) *
            poissonLowerTailProbability (servers n * trafficIntensity n) (servers n) +
          Real.sqrt (servers n : ℝ) *
            poissonPointProbability (servers n * trafficIntensity n) (servers n))) =
      poissonPointProbability (servers n * trafficIntensity n) (servers n) /
        ((1 - (trafficIntensity n : ℝ)) *
            poissonLowerTailProbability (servers n * trafficIntensity n) (servers n) +
          poissonPointProbability (servers n * trafficIntensity n) (servers n))
  field_simp [hsqrt_ne]

/-- Along any positive server-count sequence tending to infinity, a finite
positive square-root spare-capacity limit gives the corresponding limiting
Erlang-C delay probability. -/
theorem tendsto_manyServerDelayProbability_of_tendsto_scaled_spareCapacity
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → NNReal} {beta : ℝ}
    (hservers : Tendsto servers atTop atTop) (hservers_pos : ∀ n, 0 < servers n)
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hbeta : 0 < beta)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop (𝓝 beta)) :
    Tendsto
      (fun n : ℕ => manyServerDelayProbability (trafficIntensity n : ℝ) (servers n))
      atTop (𝓝 (halfinWhittDelayLimit beta)) := by
  have hservers_real : Tendsto (fun n : ℕ => (servers n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hservers
  have htraffic : Tendsto (fun n : ℕ => (trafficIntensity n : ℝ))
      atTop (𝓝 1) :=
    tendsto_trafficIntensity_of_tendsto_scaled_spareCapacity hservers hscaled
  have hmean_pos (n : ℕ) : 0 < ((servers n : NNReal) * trafficIntensity n) := by
    exact mul_pos (by exact_mod_cast hservers_pos n) (htraffic_pos n)
  have hmean : Tendsto
      (fun n : ℕ => (((servers n : NNReal) * trafficIntensity n : NNReal) : ℝ))
      atTop atTop := by
    have hproduct := htraffic.pos_mul_atTop (by norm_num : (0 : ℝ) < 1)
      hservers_real
    simpa only [NNReal.coe_mul, NNReal.coe_natCast, mul_comm] using hproduct
  have hlowerTail := tendsto_poissonLowerTailProbability_of_tendsto_serverThreshold
    hmean_pos hservers_pos hmean
    (tendsto_serverThreshold_of_tendsto_scaled_spareCapacity hservers hscaled)
  have hpoint :=
    tendsto_sqrtServer_mul_poissonPointProbability_of_tendsto_scaled_spareCapacity
      hservers hscaled
  have hdenominator :
      beta * standardGaussianCDF beta + standardGaussianDensity beta ≠ 0 := by
    exact ne_of_gt (add_pos
      (mul_pos hbeta (standardGaussianCDF_pos beta))
      (standardGaussianDensity_pos beta))
  rw [halfinWhittDelayLimit_eq_poissonComponentRatio hbeta]
  exact tendsto_manyServerDelayProbability_of_scaled_poisson_component_limits
    htraffic_lt_one (Filter.Eventually.of_forall hservers_pos)
    hlowerTail hpoint hscaled hdenominator

/-- Two positive finite square-root spare-capacity subsequential limits are
equal whenever the corresponding many-server delay probabilities have one
common limit. This is the uniqueness step used in converse QED
characterizations. -/
theorem eq_of_tendsto_delay_of_two_scaled_spareCapacity_subsequence_limits
    {trafficIntensity : ℕ → NNReal} {delayLimit firstLimit secondLimit : ℝ}
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hdelay : Tendsto
      (fun n : ℕ => manyServerDelayProbability (trafficIntensity (n + 1) : ℝ) (n + 1))
      atTop (𝓝 delayLimit))
    (firstIndex secondIndex : ℕ → ℕ)
    (hfirstIndex : Tendsto firstIndex atTop atTop)
    (hsecondIndex : Tendsto secondIndex atTop atTop)
    (hfirstLimit : 0 < firstLimit) (hsecondLimit : 0 < secondLimit)
    (hfirstScaled : Tendsto
      (fun n : ℕ => Real.sqrt ((firstIndex n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (firstIndex n + 1) : ℝ)))
      atTop (𝓝 firstLimit))
    (hsecondScaled : Tendsto
      (fun n : ℕ => Real.sqrt ((secondIndex n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (secondIndex n + 1) : ℝ)))
      atTop (𝓝 secondLimit)) :
    firstLimit = secondLimit := by
  let firstServers : ℕ → ℕ := fun n => firstIndex n + 1
  let secondServers : ℕ → ℕ := fun n => secondIndex n + 1
  let firstTraffic : ℕ → NNReal := fun n => trafficIntensity (firstIndex n + 1)
  let secondTraffic : ℕ → NNReal := fun n => trafficIntensity (secondIndex n + 1)
  have hfirstServers : Tendsto firstServers atTop atTop := by
    exact (tendsto_add_atTop_nat 1).comp hfirstIndex
  have hsecondServers : Tendsto secondServers atTop atTop := by
    exact (tendsto_add_atTop_nat 1).comp hsecondIndex
  have hfirstDelay := tendsto_manyServerDelayProbability_of_tendsto_scaled_spareCapacity
    hfirstServers (fun n => Nat.succ_pos _) (fun n => htraffic_pos _)
    (fun n => htraffic_lt_one _) hfirstLimit (by
      simpa [firstServers, firstTraffic] using hfirstScaled)
  have hsecondDelay := tendsto_manyServerDelayProbability_of_tendsto_scaled_spareCapacity
    hsecondServers (fun n => Nat.succ_pos _) (fun n => htraffic_pos _)
    (fun n => htraffic_lt_one _) hsecondLimit (by
      simpa [secondServers, secondTraffic] using hsecondScaled)
  have hfirstBaseDelay : Tendsto
      (fun n : ℕ => manyServerDelayProbability
        (trafficIntensity (firstIndex n + 1) : ℝ) (firstIndex n + 1))
      atTop (𝓝 delayLimit) :=
    hdelay.comp hfirstIndex
  have hsecondBaseDelay : Tendsto
      (fun n : ℕ => manyServerDelayProbability
        (trafficIntensity (secondIndex n + 1) : ℝ) (secondIndex n + 1))
      atTop (𝓝 delayLimit) :=
    hdelay.comp hsecondIndex
  have hfirst_eq : halfinWhittDelayLimit firstLimit = delayLimit := by
    apply tendsto_nhds_unique hfirstDelay
    simpa [firstServers, firstTraffic] using hfirstBaseDelay
  have hsecond_eq : halfinWhittDelayLimit secondLimit = delayLimit := by
    apply tendsto_nhds_unique hsecondDelay
    simpa [secondServers, secondTraffic] using hsecondBaseDelay
  symm
  apply (halfinWhittDelayLimit_strictAntiOn_Ioi.eq_iff_eq hfirstLimit hsecondLimit).mp
  exact hfirst_eq.trans hsecond_eq.symm

/-- If the square-root-scaled spare capacity vanishes along a diverging
positive server-count sequence, the corresponding Erlang-C delay probability
tends to one. -/
theorem tendsto_manyServerDelayProbability_of_tendsto_zero_scaled_spareCapacity
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → NNReal}
    (hservers : Tendsto servers atTop atTop) (hservers_pos : ∀ n, 0 < servers n)
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ => manyServerDelayProbability (trafficIntensity n : ℝ) (servers n))
      atTop (𝓝 1) := by
  have hservers_real : Tendsto (fun n : ℕ => (servers n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hservers
  have htraffic : Tendsto (fun n : ℕ => (trafficIntensity n : ℝ))
      atTop (𝓝 1) :=
    tendsto_trafficIntensity_of_tendsto_scaled_spareCapacity hservers hscaled
  have hmean_pos (n : ℕ) : 0 < ((servers n : NNReal) * trafficIntensity n) := by
    exact mul_pos (by exact_mod_cast hservers_pos n) (htraffic_pos n)
  have hmean : Tendsto
      (fun n : ℕ => (((servers n : NNReal) * trafficIntensity n : NNReal) : ℝ))
      atTop atTop := by
    have hproduct := htraffic.pos_mul_atTop (by norm_num : (0 : ℝ) < 1)
      hservers_real
    simpa only [NNReal.coe_mul, NNReal.coe_natCast, mul_comm] using hproduct
  have hlowerTail := tendsto_poissonLowerTailProbability_of_tendsto_serverThreshold
    hmean_pos hservers_pos hmean
    (tendsto_serverThreshold_of_tendsto_scaled_spareCapacity hservers hscaled)
  have hpoint :=
    tendsto_sqrtServer_mul_poissonPointProbability_of_tendsto_scaled_spareCapacity
      hservers hscaled
  have hdensity_ne : standardGaussianDensity (0 : ℝ) ≠ 0 :=
    ne_of_gt (standardGaussianDensity_pos 0)
  have hdelay := tendsto_manyServerDelayProbability_of_scaled_poisson_component_limits
    htraffic_lt_one (Filter.Eventually.of_forall hservers_pos)
    hlowerTail hpoint hscaled (by simpa using hdensity_ne)
  simpa [hdensity_ne] using hdelay

/-- If the square-root spare capacity diverges, the Erlang-C delay
probability vanishes. -/
theorem tendsto_manyServerDelayProbability_of_tendsto_scaledSpareCapacity_atTop
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → NNReal}
    (hservers : Tendsto servers atTop atTop) (hservers_pos : ∀ n, 0 < servers n)
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop atTop) :
    Tendsto
      (fun n : ℕ => manyServerDelayProbability (trafficIntensity n : ℝ) (servers n))
      atTop (𝓝 0) := by
  have htraffic_le_one : ∀ n, (trafficIntensity n : ℝ) ≤ 1 := by
    intro n
    exact_mod_cast (htraffic_lt_one n).le
  have hlowerTail :=
    tendsto_poissonLowerTailProbability_of_tendsto_scaledSpareCapacity_atTop
      (fun n => by exact_mod_cast htraffic_pos n) htraffic_le_one hscaled
  have hpointOverGap :=
    tendsto_scaledPoissonPoint_div_scaledSpareCapacity_of_tendsto_atTop
      hservers hservers_pos (fun n => by exact_mod_cast htraffic_pos n)
      htraffic_le_one hscaled
  have hratio := hpointOverGap.div hlowerTail one_ne_zero
  have hratioZero : Tendsto
      (fun n : ℕ =>
        (Real.sqrt (servers n : ℝ) *
          poissonPointProbability (servers n * trafficIntensity n) (servers n) /
          (Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))) /
          poissonLowerTailProbability (servers n * trafficIntensity n) (servers n))
      atTop (𝓝 0) := by
    simpa using hratio
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hratioZero ?_ ?_
  · filter_upwards with n
    exact (manyServerDelayProbability_pos (servers n)
      (by exact_mod_cast htraffic_pos n)
      (by exact_mod_cast htraffic_lt_one n)).le
  · filter_upwards with n
    let point := poissonPointProbability (servers n * trafficIntensity n) (servers n)
    let lowerTail := poissonLowerTailProbability
      (servers n * trafficIntensity n) (servers n)
    let gap : ℝ := 1 - (trafficIntensity n : ℝ)
    have hgap_pos : 0 < gap := by
      dsimp [gap]
      exact sub_pos.mpr (by exact_mod_cast htraffic_lt_one n)
    have hhead_pos : 0 < manyServerHeadNormalizer (trafficIntensity n : ℝ) (servers n) :=
      manyServerHeadNormalizer_pos (trafficIntensity n : ℝ) (hservers_pos n)
        NNReal.zero_le_coe
    have hlowerTail_pos : 0 < lowerTail := by
      rw [manyServerHeadNormalizer_eq_exp_mul_poissonLowerTail] at hhead_pos
      exact pos_of_mul_pos_left (by simpa [lowerTail, mul_comm] using hhead_pos)
        (Real.exp_pos _).le
    have hpoint_nonneg : 0 ≤ point := by
      dsimp [point, poissonPointProbability]
      exact MeasureTheory.measureReal_nonneg
    have hhead_scale_pos : 0 < gap * lowerTail :=
      mul_pos hgap_pos hlowerTail_pos
    have hden_pos : 0 < gap * lowerTail + point :=
      add_pos_of_pos_of_nonneg hhead_scale_pos hpoint_nonneg
    have hsqrt_pos : 0 < Real.sqrt (servers n : ℝ) := by
      apply Real.sqrt_pos.2
      exact_mod_cast hservers_pos n
    have hsmaller : point / (gap * lowerTail + point) ≤ point / (gap * lowerTail) := by
      apply (div_le_div_iff₀ hden_pos hhead_scale_pos).mpr
      nlinarith [mul_nonneg hpoint_nonneg hpoint_nonneg]
    have hscaled_eq :
        (Real.sqrt (servers n : ℝ) * point /
          (Real.sqrt (servers n : ℝ) * gap)) / lowerTail =
          point / (gap * lowerTail) := by
      field_simp [hsqrt_pos.ne', hgap_pos.ne', hlowerTail_pos.ne']
    rw [manyServerDelayProbability_eq_poissonRatio (trafficIntensity n) (servers n)
      (htraffic_lt_one n)]
    change point / (gap * lowerTail + point) ≤
      (Real.sqrt (servers n : ℝ) * point /
        (Real.sqrt (servers n : ℝ) * gap)) / lowerTail
    exact hsmaller.trans_eq hscaled_eq.symm

/-- An interior limiting delay probability rules out a diverging
square-root-scaled spare-capacity sequence. -/
theorem not_tendsto_scaledSpareCapacity_atTop_of_tendsto_delay_ne_zero
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → NNReal} {delayLimit : ℝ}
    (hservers : Tendsto servers atTop atTop) (hservers_pos : ∀ n, 0 < servers n)
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hdelay : Tendsto
      (fun n : ℕ => manyServerDelayProbability (trafficIntensity n : ℝ) (servers n))
      atTop (𝓝 delayLimit))
    (hdelay_ne_zero : delayLimit ≠ 0) :
    ¬ Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop atTop := by
  intro hscaled
  have hzero := tendsto_manyServerDelayProbability_of_tendsto_scaledSpareCapacity_atTop
    hservers hservers_pos htraffic_pos htraffic_lt_one hscaled
  apply hdelay_ne_zero
  exact tendsto_nhds_unique hdelay hzero

/-- An interior limiting delay probability rules out a vanishing
square-root-scaled spare-capacity sequence. -/
theorem not_tendsto_zero_scaled_spareCapacity_of_tendsto_delay_ne_one
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → NNReal} {delayLimit : ℝ}
    (hservers : Tendsto servers atTop atTop) (hservers_pos : ∀ n, 0 < servers n)
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hdelay : Tendsto
      (fun n : ℕ => manyServerDelayProbability (trafficIntensity n : ℝ) (servers n))
      atTop (𝓝 delayLimit))
    (hdelay_ne_one : delayLimit ≠ 1) :
    ¬ Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop (𝓝 0) := by
  intro hscaled
  have hzero := tendsto_manyServerDelayProbability_of_tendsto_zero_scaled_spareCapacity
    hservers hservers_pos htraffic_pos htraffic_lt_one hscaled
  apply hdelay_ne_one
  exact tendsto_nhds_unique hdelay hzero

/-- The converse stationary QED characterization: an interior limiting
Erlang-C delay probability forces the square-root spare capacity to converge
to a strictly positive finite parameter. -/
theorem exists_pos_tendsto_scaledSpareCapacity_of_tendsto_delay
    {trafficIntensity : ℕ → NNReal} {delayLimit : ℝ}
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hdelay : Tendsto
      (fun n : ℕ => manyServerDelayProbability (trafficIntensity (n + 1) : ℝ) (n + 1))
      atTop (𝓝 delayLimit))
    (hdelay_pos : 0 < delayLimit) (hdelay_lt_one : delayLimit < 1) :
    ∃ beta : ℝ, 0 < beta ∧
      Tendsto
        (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
          (1 - (trafficIntensity (n + 1) : ℝ)))
        atTop (𝓝 beta) ∧
      delayLimit = halfinWhittDelayLimit beta := by
  let scaledSpareCapacity : ℕ → ℝ := fun n =>
    Real.sqrt ((n + 1 : ℕ) : ℝ) * (1 - (trafficIntensity (n + 1) : ℝ))
  have hscaled_nonneg (n : ℕ) : 0 ≤ scaledSpareCapacity n := by
    dsimp [scaledSpareCapacity]
    exact mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr (by
      exact_mod_cast (htraffic_lt_one (n + 1)).le))
  have hnot_zero : ∀ index : ℕ → ℕ, Tendsto index atTop atTop →
      ¬ Tendsto (scaledSpareCapacity ∘ index) atTop (𝓝 0) := by
    intro index hindex hindex_scaled
    have hservers : Tendsto (fun n : ℕ => index n + 1) atTop atTop :=
      (tendsto_add_atTop_nat 1).comp hindex
    have hdelay_index : Tendsto
        (fun n : ℕ => manyServerDelayProbability
          (trafficIntensity (index n + 1) : ℝ) (index n + 1))
        atTop (𝓝 delayLimit) := by
      simpa [Function.comp_def] using hdelay.comp hindex
    apply not_tendsto_zero_scaled_spareCapacity_of_tendsto_delay_ne_one
      hservers (fun n => Nat.succ_pos _) (fun n => htraffic_pos (index n + 1))
      (fun n => htraffic_lt_one (index n + 1)) hdelay_index (ne_of_lt hdelay_lt_one)
    simpa [scaledSpareCapacity, Function.comp_def] using hindex_scaled
  have hnot_top : ∀ index : ℕ → ℕ, Tendsto index atTop atTop →
      ¬ Tendsto (scaledSpareCapacity ∘ index) atTop atTop := by
    intro index hindex hindex_scaled
    have hservers : Tendsto (fun n : ℕ => index n + 1) atTop atTop :=
      (tendsto_add_atTop_nat 1).comp hindex
    have hdelay_index : Tendsto
        (fun n : ℕ => manyServerDelayProbability
          (trafficIntensity (index n + 1) : ℝ) (index n + 1))
        atTop (𝓝 delayLimit) := by
      simpa [Function.comp_def] using hdelay.comp hindex
    apply not_tendsto_scaledSpareCapacity_atTop_of_tendsto_delay_ne_zero
      hservers (fun n => Nat.succ_pos _) (fun n => htraffic_pos (index n + 1))
      (fun n => htraffic_lt_one (index n + 1)) hdelay_index (ne_of_gt hdelay_pos)
    simpa [scaledSpareCapacity, Function.comp_def] using hindex_scaled
  obtain ⟨beta, subsequence, hbeta, hsubsequence, hsubsequence_limit⟩ :=
    Sequence.exists_positive_subsequence_tendsto_of_nonneg hscaled_nonneg hnot_zero
      (hnot_top id tendsto_id)
  have hscaled : Tendsto scaledSpareCapacity atTop (𝓝 beta) :=
    Sequence.tendsto_of_nonneg_of_cofinal_subsequence_limits hscaled_nonneg hnot_zero
      hnot_top (by
        intro cluster index hindex hindex_cluster hcluster_pos
        exact eq_of_tendsto_delay_of_two_scaled_spareCapacity_subsequence_limits
          htraffic_pos htraffic_lt_one hdelay index subsequence hindex
          hsubsequence.tendsto_atTop hcluster_pos hbeta
          (by simpa [scaledSpareCapacity, Function.comp_def] using hindex_cluster)
          (by simpa [scaledSpareCapacity, Function.comp_def] using hsubsequence_limit))
  refine ⟨beta, hbeta, ?_, ?_⟩
  · simpa [scaledSpareCapacity] using hscaled
  · have hforward := tendsto_manyServerDelayProbability_of_tendsto_scaled_spareCapacity
      (servers := fun n : ℕ => n + 1)
      (trafficIntensity := fun n : ℕ => trafficIntensity (n + 1))
      (tendsto_add_atTop_nat 1) (fun n => Nat.succ_pos _)
      (fun n => htraffic_pos (n + 1)) (fun n => htraffic_lt_one (n + 1)) hbeta (by
        simpa [scaledSpareCapacity] using hscaled)
    exact tendsto_nhds_unique hdelay hforward

/-- The stationary many-server delay probabilities have an interior limit if
and only if the square-root spare capacity has a strictly positive finite
limit. -/
theorem nondegenerate_tendsto_manyServerDelayProbability_iff_exists_pos_tendsto_scaledSpareCapacity
    {trafficIntensity : ℕ → NNReal}
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1) :
    (∃ delayLimit : ℝ, 0 < delayLimit ∧ delayLimit < 1 ∧
      Tendsto
        (fun n : ℕ => manyServerDelayProbability (trafficIntensity (n + 1) : ℝ) (n + 1))
        atTop (𝓝 delayLimit)) ↔
    ∃ beta : ℝ, 0 < beta ∧ Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta) := by
  constructor
  · rintro ⟨delayLimit, hdelay_pos, hdelay_lt_one, hdelay⟩
    obtain ⟨beta, hbeta, hscaled, _⟩ :=
      exists_pos_tendsto_scaledSpareCapacity_of_tendsto_delay
        htraffic_pos htraffic_lt_one hdelay hdelay_pos hdelay_lt_one
    exact ⟨beta, hbeta, hscaled⟩
  · rintro ⟨beta, hbeta, hscaled⟩
    refine ⟨halfinWhittDelayLimit beta, halfinWhittDelayLimit_pos hbeta,
      halfinWhittDelayLimit_lt_one hbeta, ?_⟩
    exact tendsto_manyServerDelayProbability_of_tendsto_scaled_spareCapacity
      (servers := fun n : ℕ => n + 1)
      (trafficIntensity := fun n : ℕ => trafficIntensity (n + 1))
      (tendsto_add_atTop_nat 1) (fun n => Nat.succ_pos _)
      (fun n => htraffic_pos (n + 1)) (fun n => htraffic_lt_one (n + 1)) hbeta hscaled

/-- The QED spare-capacity condition yields the Halfin--Whitt Erlang-C delay
limit along the positive server sequence `n + 1`.  The proof uses the
moving-cutoff Poisson lower-tail limit and the local Stirling point-mass limit,
both through their reusable APIs. -/
theorem tendsto_manyServerDelayProbability_of_qed_spareCapacity_succ
    {trafficIntensity : ℕ → NNReal} {beta : ℝ}
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hbeta : 0 < beta)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta)) :
    Tendsto
      (fun n : ℕ =>
        manyServerDelayProbability (trafficIntensity (n + 1) : ℝ) (n + 1))
      atTop (𝓝 (halfinWhittDelayLimit beta)) := by
  have hservers : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hservers_real : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hservers
  have htraffic : Tendsto (fun n : ℕ => (trafficIntensity (n + 1) : ℝ))
      atTop (𝓝 1) :=
    tendsto_qed_succ_trafficIntensity hscaled
  have hmean_pos (n : ℕ) :
      0 < ((n + 1 : ℕ) : NNReal) * trafficIntensity (n + 1) := by
    exact mul_pos (by exact_mod_cast Nat.succ_pos n) (htraffic_pos (n + 1))
  have hmean : Tendsto
      (fun n : ℕ =>
        ((((n + 1 : ℕ) : NNReal) * trafficIntensity (n + 1) : NNReal) : ℝ))
      atTop atTop := by
    have hproduct := htraffic.pos_mul_atTop (by norm_num : (0 : ℝ) < 1)
      hservers_real
    simpa only [NNReal.coe_mul, NNReal.coe_natCast, mul_comm] using hproduct
  have hlowerTail := tendsto_poissonLowerTailProbability_of_tendsto_serverThreshold
    hmean_pos (fun n => Nat.succ_pos n) hmean
    (tendsto_qed_succ_serverThreshold hscaled)
  have hpoint :=
    tendsto_sqrtServer_mul_poissonPointProbability_of_tendsto_scaled_spareCapacity
      hservers hscaled
  have hdenominator :
      beta * standardGaussianCDF beta + standardGaussianDensity beta ≠ 0 := by
    exact ne_of_gt (add_pos
      (mul_pos hbeta (standardGaussianCDF_pos beta))
      (standardGaussianDensity_pos beta))
  rw [halfinWhittDelayLimit_eq_poissonComponentRatio hbeta]
  exact tendsto_manyServerDelayProbability_of_scaled_poisson_component_limits
    (fun n => htraffic_lt_one (n + 1))
    (hservers.eventually_gt_atTop 0)
    hlowerTail hpoint hscaled hdenominator

/-- Under QED scaling, the stationary mass at least a square-root-scale
offset above full occupancy is the Erlang-C limit times its geometric-tail
factor. -/
theorem tendsto_manyServerStationaryDelayedTailMass_of_qed_spareCapacity_succ
    {trafficIntensity : ℕ → NNReal} {beta delta : ℝ} {tailOffset : ℕ → ℕ}
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hbeta : 0 < beta)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta))
    (htailOffset : Tendsto
      (fun n : ℕ => (tailOffset n : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 delta)) :
    Tendsto
      (fun n : ℕ => manyServerStationaryDelayedTailMass
        (trafficIntensity (n + 1) : ℝ) (n + 1) (tailOffset n))
      atTop (𝓝 (halfinWhittDelayLimit beta * Real.exp (-(beta * delta)))) := by
  have hservers : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hdelay := tendsto_manyServerDelayProbability_of_qed_spareCapacity_succ
    htraffic_pos htraffic_lt_one hbeta hscaled
  have hpower := tendsto_trafficIntensity_pow_of_tendsto_scaled_tailOffset
    hservers (fun n => htraffic_pos (n + 1)) hscaled htailOffset
  have hproduct := hpower.mul hdelay
  have hproduct' : Tendsto
      (fun n : ℕ =>
        (trafficIntensity (n + 1) : ℝ) ^ tailOffset n *
          manyServerDelayProbability (trafficIntensity (n + 1) : ℝ) (n + 1))
      atTop (𝓝 (halfinWhittDelayLimit beta * Real.exp (-(beta * delta)))) := by
    convert hproduct using 1
    all_goals ring_nf
  refine Tendsto.congr' ?_ hproduct'
  filter_upwards with n
  rw [manyServerStationaryDelayedTailMass_eq]
  · exact NNReal.zero_le_coe
  · exact_mod_cast htraffic_lt_one (n + 1)

/-- Under QED scaling, the stationary tail beyond a square-root-scale offset,
conditional on full occupancy, has its limiting exponential form. -/
theorem tendsto_manyServerStationaryDelayedTailConditionalMass_of_qed_spareCapacity_succ
    {trafficIntensity : ℕ → NNReal} {beta delta : ℝ} {tailOffset : ℕ → ℕ}
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta))
    (htailOffset : Tendsto
      (fun n : ℕ => (tailOffset n : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 delta)) :
    Tendsto
      (fun n : ℕ => manyServerStationaryDelayedTailConditionalMass
        (trafficIntensity (n + 1) : ℝ) (n + 1) (tailOffset n))
      atTop (𝓝 (Real.exp (-(beta * delta)))) := by
  have hservers : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hpower := tendsto_trafficIntensity_pow_of_tendsto_scaled_tailOffset
    hservers (fun n => htraffic_pos (n + 1)) hscaled htailOffset
  refine Tendsto.congr' ?_ hpower
  filter_upwards with n
  rw [manyServerStationaryDelayedTailConditionalMass_eq]
  · exact_mod_cast htraffic_pos (n + 1)
  · exact_mod_cast htraffic_lt_one (n + 1)

/-- Under QED scaling, the conditional stationary mass at a square-root-scale
delayed offset has the corresponding exponential local limit. -/
theorem tendsto_sqrtServer_mul_manyServerStationaryDelayedPointConditionalMass_of_qed_spareCapacity_succ
    {trafficIntensity : ℕ → NNReal} {beta delta : ℝ} {tailOffset : ℕ → ℕ}
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta))
    (htailOffset : Tendsto
      (fun n : ℕ => (tailOffset n : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 delta)) :
    Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        manyServerStationaryDelayedPointConditionalMass
          (trafficIntensity (n + 1) : ℝ) (n + 1) (tailOffset n))
      atTop (𝓝 (beta * Real.exp (-(beta * delta)))) := by
  have hservers : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hpower := tendsto_trafficIntensity_pow_of_tendsto_scaled_tailOffset
    hservers (fun n => htraffic_pos (n + 1)) hscaled htailOffset
  have hproduct := hscaled.mul hpower
  refine Tendsto.congr' ?_ hproduct
  filter_upwards with n
  rw [manyServerStationaryDelayedPointConditionalMass_eq]
  · ring
  · exact_mod_cast htraffic_pos (n + 1)
  · exact_mod_cast htraffic_lt_one (n + 1)

/-- Under QED scaling, the stationary cumulative mass below a cutoff on the
lower square-root scale, conditional on not reaching full occupancy, has the
corresponding Gaussian conditional limit. -/
theorem tendsto_manyServerStationaryHeadConditionalCumulativeMass_of_qed_spareCapacity_succ
    {trafficIntensity : ℕ → NNReal} {beta delta : ℝ} {cutoff : ℕ → ℕ}
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta))
    (hcutoff_pos : ∀ n, 0 < cutoff n)
    (hcutoff : ∀ n, cutoff n ≤ n + 1)
    (hcutoffGap : Tendsto
      (fun n : ℕ => ((n + 1 - cutoff n : ℕ) : ℝ) /
        Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 delta)) :
    Tendsto
      (fun n : ℕ => manyServerStationaryHeadConditionalCumulativeMass
        (trafficIntensity (n + 1)) (n + 1) (cutoff n))
      atTop (𝓝 (standardGaussianCDF (beta - delta) /
        standardGaussianCDF beta)) := by
  have hservers : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hserversReal : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hservers
  have htraffic : Tendsto (fun n : ℕ => (trafficIntensity (n + 1) : ℝ))
      atTop (𝓝 1) :=
    tendsto_qed_succ_trafficIntensity hscaled
  have hmean_pos (n : ℕ) :
      0 < ((n + 1 : ℕ) : NNReal) * trafficIntensity (n + 1) := by
    exact mul_pos (by exact_mod_cast Nat.succ_pos n) (htraffic_pos (n + 1))
  have hmean : Tendsto
      (fun n : ℕ =>
        ((((n + 1 : ℕ) : NNReal) * trafficIntensity (n + 1) : NNReal) : ℝ))
      atTop atTop := by
    have hproduct := htraffic.pos_mul_atTop (by norm_num : (0 : ℝ) < 1)
      hserversReal
    simpa only [NNReal.coe_mul, NNReal.coe_natCast, mul_comm] using hproduct
  have hdenominator := tendsto_poissonLowerTailProbability_of_tendsto_serverThreshold
    hmean_pos (fun n => Nat.succ_pos n) hmean
    (tendsto_qed_succ_serverThreshold hscaled)
  have hcutoffNumerator :=
    tendsto_poissonLowerTailProbability_of_tendsto_serverThreshold
      (mean := fun n : ℕ => ((n + 1 : ℕ) : NNReal) * trafficIntensity (n + 1))
      (servers := cutoff) hmean_pos hcutoff_pos hmean
      (tendsto_qed_succ_cutoffThreshold
        (trafficIntensity := trafficIntensity) (cutoff := cutoff)
        hcutoff hscaled hcutoffGap)
  have hratio := hcutoffNumerator.div hdenominator
    (ne_of_gt (standardGaussianCDF_pos beta))
  refine Tendsto.congr' ?_ hratio
  filter_upwards with n
  rw [manyServerStationaryHeadConditionalCumulativeMass_eq_poissonRatio]
  · rfl
  · exact Nat.succ_pos n
  · exact hcutoff n
  · exact htraffic_lt_one (n + 1)

/-- Under QED scaling, the stationary conditional point mass at a lower
square-root-scale cutoff has the Gaussian local limit. -/
theorem tendsto_sqrtServer_mul_manyServerStationaryHeadConditionalPointMass_of_qed_spareCapacity_succ
    {trafficIntensity : ℕ → NNReal} {beta delta : ℝ} {cutoff : ℕ → ℕ}
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (htraffic_lt_one : ∀ n, trafficIntensity n < 1)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta))
    (hcutoff_pos : ∀ n, 0 < cutoff n)
    (hcutoff : ∀ n, cutoff n ≤ n + 1)
    (hcutoff_lt : ∀ᶠ n : ℕ in atTop, cutoff n < n + 1)
    (hcutoffGap : Tendsto
      (fun n : ℕ => ((n + 1 - cutoff n : ℕ) : ℝ) /
        Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 delta)) :
    Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        manyServerStationaryHeadConditionalPointMass
          (trafficIntensity (n + 1)) (n + 1) (cutoff n))
      atTop (𝓝 (standardGaussianDensity (beta - delta) /
        standardGaussianCDF beta)) := by
  have hservers : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hserversReal : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hservers
  have htraffic : Tendsto (fun n : ℕ => (trafficIntensity (n + 1) : ℝ))
      atTop (𝓝 1) :=
    tendsto_qed_succ_trafficIntensity hscaled
  have hmean_pos (n : ℕ) :
      0 < ((n + 1 : ℕ) : NNReal) * trafficIntensity (n + 1) := by
    exact mul_pos (by exact_mod_cast Nat.succ_pos n) (htraffic_pos (n + 1))
  have hmean : Tendsto
      (fun n : ℕ =>
        ((((n + 1 : ℕ) : NNReal) * trafficIntensity (n + 1) : NNReal) : ℝ))
      atTop atTop := by
    have hproduct := htraffic.pos_mul_atTop (by norm_num : (0 : ℝ) < 1)
      hserversReal
    simpa only [NNReal.coe_mul, NNReal.coe_natCast, mul_comm] using hproduct
  have hdenominator := tendsto_poissonLowerTailProbability_of_tendsto_serverThreshold
    hmean_pos (fun n => Nat.succ_pos n) hmean
    (tendsto_qed_succ_serverThreshold hscaled)
  have hpoint := tendsto_sqrtServer_mul_poissonPointProbability_of_qed_succ_cutoff
    htraffic_pos hcutoff_pos hcutoff hscaled hcutoffGap
  have hratio := hpoint.div hdenominator
    (ne_of_gt (standardGaussianCDF_pos beta))
  refine Tendsto.congr' ?_ hratio
  filter_upwards [hcutoff_lt] with n hcutoff_lt
  rw [manyServerStationaryHeadConditionalPointMass_eq_poissonRatio]
  · change
      (Real.sqrt ((n + 1 : ℕ) : ℝ) *
        poissonPointProbability
          (((n + 1 : ℕ) : NNReal) * trafficIntensity (n + 1)) (cutoff n)) /
          poissonLowerTailProbability
            (((n + 1 : ℕ) : NNReal) * trafficIntensity (n + 1)) (n + 1) =
        Real.sqrt ((n + 1 : ℕ) : ℝ) *
          (poissonPointProbability
            (((n + 1 : ℕ) : NNReal) * trafficIntensity (n + 1)) (cutoff n) /
            poissonLowerTailProbability
              (((n + 1 : ℕ) : NNReal) * trafficIntensity (n + 1)) (n + 1))
    ring
  · exact Nat.succ_pos n
  · exact hcutoff_lt
  · exact htraffic_lt_one (n + 1)

/-- The two analytic normalizer limits in the Halfin--Whitt regime imply the
classical Erlang-C delay limit. -/
theorem tendsto_manyServerDelayProbability_of_qed_component_limits
    {trafficIntensity : ℕ → ℝ} {beta : ℝ} (hbeta : 0 < beta)
    (hhead : Tendsto
      (fun n : ℕ => manyServerHeadNormalizer (trafficIntensity n) n)
      atTop (𝓝 (standardGaussianCDF beta)))
    (htail : Tendsto
      (fun n : ℕ => manyServerTailNormalizer (trafficIntensity n) n)
      atTop (𝓝 (halfinWhittTailNormalizerLimit beta))) :
    Tendsto
      (fun n : ℕ => manyServerDelayProbability (trafficIntensity n) n)
      atTop (𝓝 (halfinWhittDelayLimit beta)) := by
  rw [halfinWhittDelayLimit_eq_componentRatio hbeta]
  apply tendsto_manyServerDelayProbability_of_component_limits hhead htail
  exact ne_of_gt (add_pos (standardGaussianCDF_pos beta) (by
    unfold halfinWhittTailNormalizerLimit
    exact div_pos (Real.exp_pos _) (mul_pos hbeta (Real.sqrt_pos.2
      (mul_pos (by norm_num) Real.pi_pos)))))

end Queueing
end Probability
end AppliedModelingLib
