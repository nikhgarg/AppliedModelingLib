import PG24NoisyMatchingMarkets.Theorem1IntegerGrouping
import PG24NoisyMatchingMarkets.Theorem1SourceProofHelpers
import PG24NoisyMatchingMarkets.Theorem3ChebyshevRates
import Mathlib.Tactic

/-!
# PG24 Theorem 1 rounded dense-block Chebyshev rates

This module makes the source's `C ^ phi_2` dense-block scale an explicit
integer sequence, and derives its maximum-deviation rate from the actual
beta-max variance source condition.  The rounding is visible throughout: no
real-valued power is used as a `Fin` cardinality or partition size.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

open Filter MeasureTheory
open AppliedModelingLib.Matching

/--
Positive integer version of the source dense-block size.  For every positive
market size it is exactly the ceiling of `C ^ phi_2`; `max 1` only totalizes
the zero-market case so the associated iid maximum is always well typed.
-/
def theorem1DenseGroupSize (C : ℕ) (beta gamma : ℝ) : ℕ :=
  max 1 ⌈Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma)⌉₊

/-- The `n` index whose source iid law is on `Fin (n + 1)`. -/
def theorem1DenseGroupIndex (C : ℕ) (beta gamma : ℝ) : ℕ :=
  theorem1DenseGroupSize C beta gamma - 1

/-- Exact integer union-factor count for the source's `C / C^phi_2` step. -/
def theorem1DenseGroupCount (C : ℕ) (beta gamma : ℝ) : ℕ :=
  C / theorem1DenseGroupSize C beta gamma + 1

/-- Same count using the source-law `n + 1` cardinality representation. -/
def theorem1DenseSampleGroupCount (C : ℕ) (beta gamma : ℝ) : ℕ :=
  C / (theorem1DenseGroupIndex C beta gamma + 1) + 1

/-- The source dense-window radius. -/
def theorem1DenseDeviationRadius (C : ℕ) (beta gamma : ℝ) : ℝ :=
  Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma)

/-- Expected iid maximum at the exact rounded dense-block size. -/
def theorem1DenseGroupCenter (noiseLaw : Measure ℝ)
    (C : ℕ) (beta gamma : ℝ) : ℝ :=
  AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
    (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
    (theorem1DenseGroupIndex C beta gamma)

theorem theorem1DenseGroupSize_pos (C : ℕ) (beta gamma : ℝ) :
    0 < theorem1DenseGroupSize C beta gamma := by
  unfold theorem1DenseGroupSize
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

instance theorem1DenseGroupSize_neZero (C : ℕ) (beta gamma : ℝ) :
    NeZero (theorem1DenseGroupSize C beta gamma) :=
  ⟨Nat.ne_of_gt (theorem1DenseGroupSize_pos C beta gamma)⟩

theorem theorem1DenseGroupSize_eq_ceil_of_pos
    {C : ℕ} {beta gamma : ℝ} (hC_pos : 0 < C) :
    theorem1DenseGroupSize C beta gamma =
      ⌈Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma)⌉₊ := by
  unfold theorem1DenseGroupSize
  apply Nat.max_eq_right
  apply Nat.one_le_iff_ne_zero.mpr
  apply Nat.ne_of_gt
  rw [Nat.ceil_pos]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hC_pos) _

theorem theorem1DenseGroupSize_real_le
    (C : ℕ) (beta gamma : ℝ) :
    Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) ≤
      (theorem1DenseGroupSize C beta gamma : ℝ) := by
  unfold theorem1DenseGroupSize
  calc
    Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) ≤
        (⌈Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma)⌉₊ : ℝ) :=
      Nat.le_ceil _
    _ ≤ (max 1 ⌈Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma)⌉₊ : ℕ) := by
      exact_mod_cast Nat.le_max_right 1 _

theorem theorem1DenseGroupSize_le_marketSize
    {C : ℕ} {beta gamma : ℝ} (hC_one : 1 ≤ C)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    theorem1DenseGroupSize C beta gamma ≤ C := by
  have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
  rw [theorem1DenseGroupSize_eq_ceil_of_pos hC_pos, Nat.ceil_le]
  calc
    Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) ≤
        Real.rpow (C : ℝ) 1 :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hC_one)
        (theorem1TailPhi2_lt_one hbeta hgamma).le
    _ = (C : ℝ) := Real.rpow_one _

theorem theorem1DenseGroupIndex_add_one
    (C : ℕ) (beta gamma : ℝ) :
    theorem1DenseGroupIndex C beta gamma + 1 =
      theorem1DenseGroupSize C beta gamma := by
  unfold theorem1DenseGroupIndex
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (theorem1DenseGroupSize_pos C beta gamma)))

theorem theorem1DenseSampleGroupCount_eq_denseGroupCount
    (C : ℕ) (beta gamma : ℝ) :
    theorem1DenseSampleGroupCount C beta gamma =
      theorem1DenseGroupCount C beta gamma := by
  unfold theorem1DenseSampleGroupCount theorem1DenseGroupCount
  rw [theorem1DenseGroupIndex_add_one]

theorem theorem1DenseGroupIndex_tendsto_atTop
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    Tendsto (fun C : ℕ => theorem1DenseGroupIndex C beta gamma)
      atTop atTop := by
  have hpow : Tendsto
      (fun C : ℕ => Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma))
      atTop atTop :=
    (tendsto_rpow_atTop (theorem1TailPhi2_pos hbeta hgamma)).comp
      tendsto_natCast_atTop_atTop
  refine tendsto_atTop.2 ?_
  intro target
  filter_upwards [hpow.eventually_ge_atTop (((target + 1 : ℕ) : ℝ))]
    with C hC
  have hsize : target + 1 ≤ theorem1DenseGroupSize C beta gamma := by
    have hsize_real : ((target + 1 : ℕ) : ℝ) ≤
        (theorem1DenseGroupSize C beta gamma : ℝ) := by
      exact hC.trans (theorem1DenseGroupSize_real_le C beta gamma)
    exact_mod_cast hsize_real
  unfold theorem1DenseGroupIndex
  omega

theorem theorem1DenseGroupIndex_properties
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    Tendsto (fun C : ℕ => theorem1DenseGroupIndex C beta gamma)
      atTop atTop ∧
    (∀ᶠ C : ℕ in atTop,
      Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) ≤
        ((theorem1DenseGroupIndex C beta gamma + 1 : ℕ) : ℝ)) := by
  constructor
  · exact theorem1DenseGroupIndex_tendsto_atTop hbeta hgamma
  · filter_upwards with C
    rw [theorem1DenseGroupIndex_add_one]
    exact theorem1DenseGroupSize_real_le C beta gamma

/--
The exact integer quotient/remainder count is bounded by twice the source
real union factor once the market has at least one college.  The factor two is
the visible cost of the final remainder slot.
-/
theorem theorem1DenseGroupCount_le_two_mul_rpow_one_sub_phi2
    {C : ℕ} {beta gamma : ℝ} (hC_one : 1 ≤ C)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    (theorem1DenseGroupCount C beta gamma : ℝ) ≤
      2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
  let m := theorem1DenseGroupSize C beta gamma
  have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
  have hC_real_pos : 0 < (C : ℝ) := by
    exact_mod_cast hC_pos
  have hC_real_one : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hC_one
  have hm_real_pos : 0 < (m : ℝ) := by
    exact_mod_cast theorem1DenseGroupSize_pos C beta gamma
  have hpower_pos : 0 < Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) :=
    Real.rpow_pos_of_pos hC_real_pos _
  have hm_lower : Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) ≤ (m : ℝ) := by
    simpa [m] using theorem1DenseGroupSize_real_le C beta gamma
  have hdiv_cast : ((C / m : ℕ) : ℝ) ≤ (C : ℝ) / (m : ℝ) :=
    Nat.cast_div_le
  have hdiv_power : (C : ℝ) / (m : ℝ) ≤
      (C : ℝ) / Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) :=
    by exact div_le_div_of_nonneg_left (Nat.cast_nonneg C) hpower_pos hm_lower
  have hquotient : ((C / m : ℕ) : ℝ) ≤
      Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
    calc
      ((C / m : ℕ) : ℝ) ≤ (C : ℝ) / (m : ℝ) := hdiv_cast
      _ ≤ (C : ℝ) / Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) :=
        hdiv_power
      _ = Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
        calc
          (C : ℝ) / Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) =
              Real.rpow (C : ℝ) 1 /
                Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) := by
            exact congrArg (fun x : ℝ =>
              x / Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma))
              (Real.rpow_one (C : ℝ)).symm
          _ = Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) :=
            (Real.rpow_sub hC_real_pos 1 (theorem1TailPhi2 beta gamma)).symm
  have hscale_one : 1 ≤ Real.rpow (C : ℝ)
      (1 - theorem1TailPhi2 beta gamma) :=
    Real.one_le_rpow hC_real_one
      (theorem1Tail_one_sub_phi2_pos hbeta hgamma).le
  change ((C / m + 1 : ℕ) : ℝ) ≤ _
  calc
    ((C / m + 1 : ℕ) : ℝ) = ((C / m : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) + 1 :=
      by simpa [add_comm] using add_le_add_right hquotient 1
    _ ≤ 2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
      linarith

theorem theorem1DenseSampleGroupCount_le_two_mul_rpow_one_sub_phi2
    {C : ℕ} {beta gamma : ℝ} (hC_one : 1 ≤ C)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    (theorem1DenseSampleGroupCount C beta gamma : ℝ) ≤
      2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
  rw [theorem1DenseSampleGroupCount_eq_denseGroupCount]
  exact theorem1DenseGroupCount_le_two_mul_rpow_one_sub_phi2
    hC_one hbeta hgamma

/--
Chebyshev at the exact rounded dense-block size, derived from the source
beta-max variance condition rather than assumed as a tail estimate.
-/
theorem theorem1DenseGroup_deviation_eventually_le_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta gamma : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
            (theorem1DenseGroupCenter noiseLaw C beta gamma)
            (theorem1DenseDeviationRadius C beta gamma) ≤
          A * Real.rpow (C : ℝ)
            (-beta * theorem1TailPhi2 beta gamma -
              2 * theorem1TailPhi1 beta gamma) := by
  rcases theorem1DenseGroupIndex_properties hbeta.1 hgamma with
    ⟨hindex_atTop, hindex_lower⟩
  rcases theorem3_iidMaximum_powerDeviation_eventually_le_of_beta
    (blockExponent := theorem1TailPhi2 beta gamma)
    (deviationExponent := theorem1TailPhi1 beta gamma)
    noiseLaw hbeta hvariance
    (fun C : ℕ => theorem1DenseGroupIndex C beta gamma)
    hindex_atTop hindex_lower with ⟨A, hA_nonneg, hbound⟩
  refine ⟨A, hA_nonneg, ?_⟩
  filter_upwards [hbound] with C hC
  simpa [theorem1DenseGroupCenter, theorem1DenseDeviationRadius] using hC

/--
The source Case-1 low-side union/Chebyshev estimate for an arbitrary sequence
of finite cutoff blocks.  Its only non-arithmetic inputs are the actual
lower-cutoff and score-separation geometry; the iid deviation rate is derived
from beta-max variance above.
-/
theorem theorem1DenseGroup_cutoff_affordance_eventually_le_source_rate_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta gamma : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (block : ∀ C : ℕ, Finset (Fin C))
    (cutoff : ∀ C : ℕ, Fin C → ℝ)
    (value pivot : ℕ → ℝ)
    (hlower : ∀ᶠ C : ℕ in atTop,
      ∀ c ∈ block C, pivot C ≤ cutoff C c)
    (hseparation : ∀ᶠ C : ℕ in atTop,
      theorem1DenseGroupCenter noiseLaw C beta gamma +
        theorem1DenseDeviationRadius C beta gamma ≤ pivot C - value C) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ C : ℕ in atTop,
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin C => noiseLaw))
            (block C) (value C) (cutoff C) ≤
          A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
  rcases theorem1DenseGroup_deviation_eventually_le_of_beta
    noiseLaw hbeta hgamma hvariance with ⟨A, hA_nonneg, hdeviation⟩
  refine ⟨2 * A, mul_nonneg (by norm_num) hA_nonneg, ?_⟩
  filter_upwards [eventually_ge_atTop 1, hdeviation, hlower, hseparation]
    with C hC_one hdeviation_C hlower_C hseparation_C
  let m : ℕ := theorem1DenseGroupIndex C beta gamma + 1
  have hgroup_bound :=
    theorem1_iid_cutoff_affordance_le_index_div_add_one_mul_deviation
      (m := m) noiseLaw (block C) (cutoff C) hlower_C hseparation_C
  have hcount : (theorem1DenseSampleGroupCount C beta gamma : ℝ) ≤
      2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) :=
    theorem1DenseSampleGroupCount_le_two_mul_rpow_one_sub_phi2
      hC_one hbeta.1 hgamma
  have hdeviation_nonneg : 0 ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin m => noiseLaw))
        (theorem1DenseGroupCenter noiseLaw C beta gamma)
        (theorem1DenseDeviationRadius C beta gamma) :=
    theorem1_iid_topOrderDeviationProbability_nonneg
      (m := m) noiseLaw _ _
  have hfactor_nonneg : 0 ≤ 2 *
      Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
    exact mul_nonneg (by norm_num)
      (le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hC_one) _))
  have hexponent :
      (1 - theorem1TailPhi2 beta gamma) +
          (-beta * theorem1TailPhi2 beta gamma -
            2 * theorem1TailPhi1 beta gamma) =
        -(theorem1TailK beta gamma) := by
    calc
      (1 - theorem1TailPhi2 beta gamma) +
          (-beta * theorem1TailPhi2 beta gamma -
            2 * theorem1TailPhi1 beta gamma) =
          1 - 2 * theorem1TailPhi1 beta gamma -
            (1 + beta) * theorem1TailPhi2 beta gamma := by ring
      _ = -(theorem1TailK beta gamma) :=
        theorem1Tail_case1_chebyshev_exp_eq_neg_K hbeta.1 hgamma
  have hC_real_pos : 0 < (C : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC_one)
  calc
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin C => noiseLaw))
        (block C) (value C) (cutoff C) ≤
        ((C / m + 1 : ℕ) : ℝ) *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin m => noiseLaw))
            (theorem1DenseGroupCenter noiseLaw C beta gamma)
            (theorem1DenseDeviationRadius C beta gamma) := hgroup_bound
    _ = (theorem1DenseSampleGroupCount C beta gamma : ℝ) *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin m => noiseLaw))
            (theorem1DenseGroupCenter noiseLaw C beta gamma)
            (theorem1DenseDeviationRadius C beta gamma) := by
      rfl
    _ ≤ (2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin m => noiseLaw))
            (theorem1DenseGroupCenter noiseLaw C beta gamma)
            (theorem1DenseDeviationRadius C beta gamma) :=
      mul_le_mul_of_nonneg_right hcount hdeviation_nonneg
    _ ≤ (2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
          (A * Real.rpow (C : ℝ)
            (-beta * theorem1TailPhi2 beta gamma -
              2 * theorem1TailPhi1 beta gamma)) :=
      mul_le_mul_of_nonneg_left hdeviation_C hfactor_nonneg
    _ = (2 * A) * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
      calc
        (2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
            (A * Real.rpow (C : ℝ)
              (-beta * theorem1TailPhi2 beta gamma -
                2 * theorem1TailPhi1 beta gamma)) =
            (2 * A) *
              (Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) *
                Real.rpow (C : ℝ)
                  (-beta * theorem1TailPhi2 beta gamma -
                    2 * theorem1TailPhi1 beta gamma)) := by ring
        _ = (2 * A) * Real.rpow (C : ℝ)
              ((1 - theorem1TailPhi2 beta gamma) +
                (-beta * theorem1TailPhi2 beta gamma -
                  2 * theorem1TailPhi1 beta gamma)) := by
          exact congrArg (fun x : ℝ => (2 * A) * x)
            (Real.rpow_add hC_real_pos
              (1 - theorem1TailPhi2 beta gamma)
              (-beta * theorem1TailPhi2 beta gamma -
                2 * theorem1TailPhi1 beta gamma)).symm
        _ = (2 * A) * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
          rw [hexponent]

/--
The rounded low-side pointwise Chebyshev estimate integrates over the literal
closed low-value region.  The proof uses value monotonicity and the probability
mass of that region; no uniform cutoff-tail integral is accepted as a premise.
-/
theorem theorem1DenseGroup_low_affordance_integral_eventually_le_source_rate_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta gamma : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (block : ∀ C : ℕ, Finset (Fin C))
    (cutoff : ∀ C : ℕ, Fin C → ℝ)
    (lowValue pivot : ℕ → ℝ)
    (hlower : ∀ᶠ C : ℕ in atTop,
      ∀ c ∈ block C, pivot C ≤ cutoff C c)
    (hseparation : ∀ᶠ C : ℕ in atTop,
      theorem1DenseGroupCenter noiseLaw C beta gamma +
        theorem1DenseDeviationRadius C beta gamma ≤ pivot C - lowValue C) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ C : ℕ in atTop,
        (∫ v : ℝ,
          (Set.Iic (lowValue C)).indicator
            (fun v => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin C => noiseLaw))
              (block C) v (cutoff C)) v ∂valueLaw) ≤
          A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
  rcases theorem1DenseGroup_cutoff_affordance_eventually_le_source_rate_of_beta
    noiseLaw hbeta hgamma hvariance block cutoff lowValue pivot
    hlower hseparation with ⟨A, hA_nonneg, hpointwise_rate⟩
  refine ⟨A, hA_nonneg, ?_⟩
  filter_upwards [eventually_ge_atTop 1, hpointwise_rate]
    with C hC_one hpointwise_rate_C
  let p : ℝ → ℝ := fun v => cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin C => noiseLaw)) (block C) v (cutoff C)
  have hp : Integrable p valueLaw := by
    simpa [p, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        (Measure.pi (fun _ : Fin C => noiseLaw)) valueLaw (block C) (cutoff C))
  have hC_pos : 0 < (C : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC_one)
  have hrate_nonneg :
      0 ≤ A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) :=
    mul_nonneg hA_nonneg
      (le_of_lt (Real.rpow_pos_of_pos hC_pos _))
  have hpointwise : ∀ v ∈ Set.Iic (lowValue C),
      p v ≤ A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
    intro v hv
    calc
      p v ≤ p (lowValue C) := by
        exact cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin C => noiseLaw)) hv
      _ ≤ A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
        simpa [p] using hpointwise_rate_C
  change (∫ v : ℝ, (Set.Iic (lowValue C)).indicator p v ∂valueLaw) ≤
    A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma))
  rw [integral_indicator measurableSet_Iic]
  calc
    (∫ v in Set.Iic (lowValue C), p v ∂valueLaw) ≤
        valueLaw.real (Set.Iic (lowValue C)) *
          (A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma))) :=
      theorem1_setIntegral_le_measureReal_mul_of_pointwise_le
        valueLaw p hp measurableSet_Iic hpointwise
    _ ≤ A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
      have hmass : valueLaw.real (Set.Iic (lowValue C)) ≤ 1 :=
        measureReal_le_one (μ := valueLaw)
      nlinarith

/--
The high-side iid estimate only needs a dense block of *at least* `m`
coordinates.  This is the source condition after ceiling rounding; requiring
an exact cardinality would be an unjustified strengthening.
-/
theorem theorem1_one_sub_iid_cutoff_affordance_le_top_deviation_of_card_ge_upper_cutoff
    {n m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ)
    [IsProbabilityMeasure noiseAtomLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    {v ceiling center deviation : ℝ}
    (hcard : m ≤ active.card)
    (hupper : ∀ c ∈ active, cutoff c ≤ ceiling)
    (hdeviation_pos : 0 < deviation)
    (hseparation : ceiling - v < center - deviation) :
    1 - cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v cutoff ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  let base : ℝ := AppliedModelingLib.Probability.lowerCDFMass noiseAtomLaw (ceiling - v)
  have hbase_nonneg : 0 ≤ base := by
    exact AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseAtomLaw _
  have hbase_le_one : base ≤ 1 := by
    exact AppliedModelingLib.Probability.lowerCDFMass_le_one noiseAtomLaw _
  have hpow : base ^ active.card ≤ base ^ m :=
    pow_right_anti₀ hbase_nonneg hbase_le_one hcard
  have hconstant_le :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v (fun _ => ceiling) ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v cutoff :=
    AppliedModelingLib.Matching.constantCutoffProbability_le_of_cutoff_le
      (Measure.pi (fun _ : Fin n => noiseAtomLaw)) hupper
  calc
    1 - cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v cutoff ≤
        1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v (fun _ => ceiling) := by
      linarith
    _ = base ^ active.card := by
      change 1 - AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v (fun _ => ceiling) = _
      dsimp [base]
      rw [AppliedModelingLib.Matching.cutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass_pow_card]
      ring
    _ ≤ base ^ m := hpow
    _ = 1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw))
            (Finset.univ : Finset (Fin m)) v (fun _ => ceiling) := by
      change base ^ m = 1 - AppliedModelingLib.Matching.cutoffCrossingProbability
        (Measure.pi (fun _ : Fin m => noiseAtomLaw))
          (Finset.univ : Finset (Fin m)) v (fun _ => ceiling)
      rw [AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow]
      simp [base]
    _ ≤ AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation :=
      AppliedModelingLib.Matching.one_sub_cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_lt_center_sub
        (Measure.pi (fun _ : Fin m => noiseAtomLaw)) hdeviation_pos hseparation

/-- Lift the rounded dense-block estimate to any upper cutoff block containing it. -/
theorem theorem1_one_sub_iid_cutoff_affordance_le_deviation_of_dense_card_ge
    {n m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ)
    [IsProbabilityMeasure noiseAtomLaw]
    {dense upper : Finset (Fin n)} (cutoff : Fin n → ℝ)
    {v ceiling center deviation : ℝ}
    (hdense_subset : dense ⊆ upper)
    (hcard : m ≤ dense.card)
    (hupper : ∀ c ∈ dense, cutoff c ≤ ceiling)
    (hdeviation_pos : 0 < deviation)
    (hseparation : ceiling - v < center - deviation) :
    1 - cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) upper v cutoff ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  have hdense_le_upper :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) dense v cutoff ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) upper v cutoff :=
    cutoffAffordanceProbability_mono_active
      (Measure.pi (fun _ : Fin n => noiseAtomLaw)) hdense_subset
  have hdense_error :=
    theorem1_one_sub_iid_cutoff_affordance_le_top_deviation_of_card_ge_upper_cutoff
      noiseAtomLaw dense cutoff hcard hupper hdeviation_pos hseparation
  linarith

/--
At positive market sizes, the source real dense-window condition is exactly
equivalent to containing at least the rounded integer group size.
-/
theorem theorem1DenseGroupSize_le_card_iff_source_dense
    {C : ℕ} {beta gamma : ℝ} {ι : Type*} (window : Finset ι)
    (hC_pos : 0 < C) :
    theorem1DenseGroupSize C beta gamma ≤ window.card ↔
      Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) ≤ (window.card : ℝ) := by
  rw [theorem1DenseGroupSize_eq_ceil_of_pos hC_pos, Nat.ceil_le]

/--
The source Case-1 high-side estimate at a dense window satisfying its literal
``at least `C ^ phi_2`'' cardinality condition.  No equality rounding is
introduced: the preceding cardinality equivalence supplies the integer block
required by the iid maximum event.
-/
theorem theorem1DenseGroup_one_sub_cutoff_affordance_eventually_le_chebyshev_rate_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta gamma : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (dense upper : ∀ C : ℕ, Finset (Fin C))
    (cutoff : ∀ C : ℕ, Fin C → ℝ)
    (value ceiling : ℕ → ℝ)
    (hdense_subset : ∀ᶠ C : ℕ in atTop, dense C ⊆ upper C)
    (hdense_card : ∀ᶠ C : ℕ in atTop,
      Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) ≤ (dense C).card)
    (hupper : ∀ᶠ C : ℕ in atTop,
      ∀ c ∈ dense C, cutoff C c ≤ ceiling C)
    (hseparation : ∀ᶠ C : ℕ in atTop,
      ceiling C - value C < theorem1DenseGroupCenter noiseLaw C beta gamma -
        theorem1DenseDeviationRadius C beta gamma) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ C : ℕ in atTop,
        1 - cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin C => noiseLaw))
            (upper C) (value C) (cutoff C) ≤
          A * Real.rpow (C : ℝ)
            (-beta * theorem1TailPhi2 beta gamma -
              2 * theorem1TailPhi1 beta gamma) := by
  rcases theorem1DenseGroup_deviation_eventually_le_of_beta
    noiseLaw hbeta hgamma hvariance with ⟨A, hA_nonneg, hdeviation⟩
  refine ⟨A, hA_nonneg, ?_⟩
  filter_upwards [eventually_ge_atTop 1, hdeviation, hdense_subset,
    hdense_card, hupper, hseparation]
    with C hC_one hdeviation_C hdense_subset_C hdense_card_C hupper_C hseparation_C
  let m : ℕ := theorem1DenseGroupIndex C beta gamma + 1
  have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
  have hm_card : m ≤ (dense C).card := by
    change theorem1DenseGroupIndex C beta gamma + 1 ≤ (dense C).card
    rw [theorem1DenseGroupIndex_add_one]
    exact (theorem1DenseGroupSize_le_card_iff_source_dense
      (dense C) hC_pos).mpr hdense_card_C
  have hradius_pos : 0 < theorem1DenseDeviationRadius C beta gamma := by
    unfold theorem1DenseDeviationRadius
    exact Real.rpow_pos_of_pos (by exact_mod_cast hC_pos) _
  have hfailure :=
    theorem1_one_sub_iid_cutoff_affordance_le_deviation_of_dense_card_ge
      (m := m) noiseLaw (cutoff := cutoff C)
      hdense_subset_C hm_card hupper_C hradius_pos hseparation_C
  calc
    1 - cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin C => noiseLaw))
        (upper C) (value C) (cutoff C) ≤
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) := hfailure
    _ ≤ A * Real.rpow (C : ℝ)
          (-beta * theorem1TailPhi2 beta gamma -
            2 * theorem1TailPhi1 beta gamma) := hdeviation_C

end

end PG24NoisyMatchingMarkets
