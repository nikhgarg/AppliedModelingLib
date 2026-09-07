import AppliedModelingLib.Foundations.Math.Asymptotics
import FalahatgarEtAl2017MaxingRanking.SourceOptMaximizeAsymptotics
import FalahatgarEtAl2017MaxingRanking.PickAnchorCost

/-!
# Pick-Anchor resource asymptotics at the OPT-Maximize cutoff

Lemma 3 has an exact ceiling-corrected finite cap for every cutoff.  This
module records the asymptotic seam needed by the source's rounded
square-root cutoff in OPT-Maximize: the complete Pick-Anchor comparison cap
is little-o of the population at fixed positive accuracy and valid confidence.
It deliberately does not recast the paper's two-parameter display as a
one-variable statement.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib Asymptotics

/--
Lemma 3's literal ceiling-corrected comparison count has a uniform source
rate at the actual capped Pick-Anchor sample size.  This keeps the source's
`min` cap and integral rounding visible, rather than silently replacing the
sample size by an unbounded real expression.
-/
theorem pickAnchorSource_ceilingComparisonCap_real_le_sampleRateForm
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (epsilon delta : ℝ)
    (hcutoff : 0 < cutoff) (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (((pickAnchorSampleCount (Fintype.card Arm) cutoff delta - 1) *
      fixedSampleBudget 0 epsilon
        ((delta / 2) / (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)) : ℕ) : ℝ) ≤
      5 * (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ) *
        (1 + Real.log
          ((pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ) / delta)) /
        epsilon ^ 2 := by
  let count : ℕ := pickAnchorSampleCount (Fintype.card Arm) cutoff delta
  let logFactor : ℝ := Real.log ((count : ℝ) / delta)
  let envelope : ℝ := 1 + logFactor
  have hcount : 0 < count := by
    dsimp [count]
    exact pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta Fintype.card_pos
      hcutoff hdelta hdeltaLeOne
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hcountOne : 1 ≤ (count : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hcount
  have hratioPos : 0 < (count : ℝ) / delta := div_pos hcountReal hdelta
  have hratioGeOne : 1 ≤ (count : ℝ) / delta := by
    apply (le_div_iff₀ hdelta).mpr
    nlinarith
  have hlogFactorNonnegative : 0 ≤ logFactor := by
    dsimp [logFactor]
    exact Real.log_nonneg hratioGeOne
  have hlogTwoLeOne : Real.log (2 : ℝ) ≤ 1 := by
    apply (Real.exp_le_exp).mp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simpa [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hlogFourLeTwo : Real.log (4 : ℝ) ≤ 2 := by
    calc
      Real.log (4 : ℝ) = Real.log 2 + Real.log 2 := by
        rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
      _ ≤ 2 := by linarith
  have hlogBudgetLe : Real.log (4 * (count : ℝ) / delta) ≤ 2 * envelope := by
    have hlogSplit : Real.log (4 * (count : ℝ) / delta) =
        Real.log 4 + logFactor := by
      dsimp [logFactor]
      rw [show 4 * (count : ℝ) / delta = 4 * ((count : ℝ) / delta) by
        field_simp [ne_of_gt hdelta]]
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hratioPos)]
    rw [hlogSplit]
    dsimp [envelope]
    nlinarith
  have hepsilonSqPos : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hepsilonSqLeOne : epsilon ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ hepsilon.le (by norm_num)).mpr hepsilonLeOne
  have hinvEpsilonSqGeOne : 1 ≤ 1 / epsilon ^ 2 := by
    apply (le_div_iff₀ hepsilonSqPos).mpr
    simpa using hepsilonSqLeOne
  have henvelopeOverEpsilonSqGeOne : 1 ≤ envelope / epsilon ^ 2 := by
    calc
      1 ≤ 1 / epsilon ^ 2 := hinvEpsilonSqGeOne
      _ ≤ envelope / epsilon ^ 2 := by
        exact div_le_div_of_nonneg_right (by dsimp [envelope]; linarith)
          hepsilonSqPos.le
  have hlogOverEpsilonSq :
      Real.log (4 * (count : ℝ) / delta) / epsilon ^ 2 ≤
        2 * envelope / epsilon ^ 2 := by
    exact div_le_div_of_nonneg_right hlogBudgetLe hepsilonSqPos.le
  have hbatchBound :
      2 / epsilon ^ 2 * Real.log (4 * (count : ℝ) / delta) + 1 ≤
        5 * envelope / epsilon ^ 2 := by
    calc
      2 / epsilon ^ 2 * Real.log (4 * (count : ℝ) / delta) + 1 =
          2 * (Real.log (4 * (count : ℝ) / delta) / epsilon ^ 2) + 1 := by
            field_simp [hepsilonSqPos.ne']
      _ ≤ 2 * (2 * envelope / epsilon ^ 2) + envelope / epsilon ^ 2 := by
        gcongr
      _ = 5 * envelope / epsilon ^ 2 := by ring
  have hbatchNonnegative : 0 ≤
      2 / epsilon ^ 2 * Real.log (4 * (count : ℝ) / delta) + 1 := by
    have hlogNonnegative : 0 ≤ Real.log (4 * (count : ℝ) / delta) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ hdelta).mpr
      nlinarith
    positivity
  have hcountMinusOne : ((count - 1 : ℕ) : ℝ) ≤ (count : ℝ) := by
    exact_mod_cast Nat.sub_le count 1
  have hsource := pickAnchorSample_ceilingComparisonCap count epsilon delta hcount hdelta
    hdeltaLeOne
  have hlog : Real.log (2 / ((delta / 2) / (count : ℝ))) =
      Real.log (4 * (count : ℝ) / delta) := by
    congr 1
    field_simp [ne_of_gt hdelta, ne_of_gt hcountReal]
    norm_num
  change
    (((count - 1) * fixedSampleBudget 0 epsilon ((delta / 2) / (count : ℝ)) : ℕ) : ℝ) ≤ _
  rw [hlog] at hsource
  calc
    (((count - 1) * fixedSampleBudget 0 epsilon ((delta / 2) / (count : ℝ)) : ℕ) : ℝ) ≤
        ((count - 1 : ℕ) : ℝ) *
          (2 / epsilon ^ 2 * Real.log (4 * (count : ℝ) / delta) + 1) := hsource
    _ ≤ (count : ℝ) * (5 * envelope / epsilon ^ 2) := by
      gcongr
    _ = 5 * (count : ℝ) * (1 + Real.log ((count : ℝ) / delta)) / epsilon ^ 2 := by
      dsimp [envelope, logFactor]
      ring

/--
Lemma 3's exact capped-sample cost is bounded by a finite expression in the
source parameters.  The additive one is the explicit price of the source's
integer ceiling; retaining it makes this bound valid uniformly, including
the finite endpoint `delta = 1`.
-/
theorem pickAnchorSource_ceilingComparisonCap_real_le_sourceRateForm
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (epsilon delta : ℝ)
    (hcutoff : 0 < cutoff) (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (((pickAnchorSampleCount (Fintype.card Arm) cutoff delta - 1) *
      fixedSampleBudget 0 epsilon
        ((delta / 2) / (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)) : ℕ) : ℝ) ≤
      5 *
          ((Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta) + 1) *
        (1 + Real.log
          (((Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta) + 1) / delta)) /
        epsilon ^ 2 := by
  let count : ℕ := pickAnchorSampleCount (Fintype.card Arm) cutoff delta
  let sampleEnvelope : ℝ :=
    (Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta) + 1
  have hpopulation : 0 < (Fintype.card Arm : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcutoffReal : 0 < (cutoff : ℝ) := by exact_mod_cast hcutoff
  have hlogTwoOverDeltaNonnegative : 0 ≤ Real.log (2 / delta) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hdelta).mpr
    nlinarith
  have hrawNonnegative : 0 ≤
      (Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta) := by
    positivity
  have hsampleEnvelopePos : 0 < sampleEnvelope := by
    dsimp [sampleEnvelope]
    linarith
  have hcountLe : (count : ℝ) ≤ sampleEnvelope := by
    dsimp [count, sampleEnvelope]
    exact le_of_lt (pickAnchorSampleCount_real_lt_sourceFormula_add_one
      (Fintype.card Arm) cutoff delta Fintype.card_pos hcutoff hdelta hdeltaLeOne)
  have hcount : 0 < count := by
    dsimp [count]
    exact pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta Fintype.card_pos
      hcutoff hdelta hdeltaLeOne
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hratioGeOne : 1 ≤ (count : ℝ) / delta := by
    apply (le_div_iff₀ hdelta).mpr
    have hcountOne : 1 ≤ (count : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr hcount
    nlinarith
  have hsampleLogNonnegative : 0 ≤ 1 + Real.log ((count : ℝ) / delta) := by
    have : 0 ≤ Real.log ((count : ℝ) / delta) := Real.log_nonneg hratioGeOne
    linarith
  have hlogLe : Real.log ((count : ℝ) / delta) ≤
      Real.log (sampleEnvelope / delta) := by
    apply Real.log_le_log
    · exact div_pos hcountReal hdelta
    · exact (div_le_div_iff_of_pos_right hdelta).mpr hcountLe
  have hfactorLe : 1 + Real.log ((count : ℝ) / delta) ≤
      1 + Real.log (sampleEnvelope / delta) := by linarith
  have hsampleEnvelopeNonnegative : 0 ≤ sampleEnvelope := hsampleEnvelopePos.le
  have hrightFactorNonnegative : 0 ≤ 1 + Real.log (sampleEnvelope / delta) := by
    calc
      0 ≤ 1 + Real.log ((count : ℝ) / delta) := hsampleLogNonnegative
      _ ≤ 1 + Real.log (sampleEnvelope / delta) := hfactorLe
  have hproductLe : (count : ℝ) * (1 + Real.log ((count : ℝ) / delta)) ≤
      sampleEnvelope * (1 + Real.log (sampleEnvelope / delta)) := by
    calc
      (count : ℝ) * (1 + Real.log ((count : ℝ) / delta)) ≤
          sampleEnvelope * (1 + Real.log ((count : ℝ) / delta)) :=
        mul_le_mul_of_nonneg_right hcountLe hsampleLogNonnegative
      _ ≤ sampleEnvelope * (1 + Real.log (sampleEnvelope / delta)) :=
        mul_le_mul_of_nonneg_left hfactorLe hsampleEnvelopeNonnegative
  have hepsilonSqPos : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hrateScaleNonnegative : 0 ≤ 5 / epsilon ^ 2 := by positivity
  have hsample := pickAnchorSource_ceilingComparisonCap_real_le_sampleRateForm
    (Arm := Arm) cutoff epsilon delta hcutoff hepsilon hepsilonLeOne hdelta hdeltaLeOne
  change
    (((count - 1) * fixedSampleBudget 0 epsilon ((delta / 2) / (count : ℝ)) : ℕ) : ℝ) ≤ _
  calc
    (((count - 1) * fixedSampleBudget 0 epsilon ((delta / 2) / (count : ℝ)) : ℕ) : ℝ) ≤
        5 * (count : ℝ) * (1 + Real.log ((count : ℝ) / delta)) / epsilon ^ 2 := by
          simpa only [count] using hsample
    _ = (5 / epsilon ^ 2) *
        ((count : ℝ) * (1 + Real.log ((count : ℝ) / delta))) := by
          field_simp [hepsilonSqPos.ne']
    _ ≤ (5 / epsilon ^ 2) *
        (sampleEnvelope * (1 + Real.log (sampleEnvelope / delta))) :=
      mul_le_mul_of_nonneg_left hproductLe hrateScaleNonnegative
    _ = 5 * sampleEnvelope * (1 + Real.log (sampleEnvelope / delta)) / epsilon ^ 2 := by
      field_simp [hepsilonSqPos.ne']

/--
The real source envelope for Lemma 3's ceiling-corrected Pick-Anchor cost at
the rounded cutoff used by OPT-Maximize.
-/
noncomputable def sourceOptMaximizePickAnchorComparisonEnvelope
    (armCount : ℕ) (lower anchorDelta : ℝ) : ℝ :=
  ((pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta - 1 : ℕ) : ℝ) *
    (2 / lower ^ 2 *
      Real.log
        (4 *
          (pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta : ℝ) /
            anchorDelta) + 1)

/--
At the OPT-Maximize cutoff, Lemma 3's complete source envelope divided by the
population tends to zero.  All sample-count and comparison ceilings remain in
the displayed function.
-/
theorem tendsto_sourceOptMaximizePickAnchorComparisonEnvelope_div_nat_nhds_zero
    {lower anchorDelta : ℝ} (hlower : 0 < lower)
    (hanchorDelta : 0 < anchorDelta) (hanchorDeltaLeOne : anchorDelta ≤ 1) :
    Filter.Tendsto
      (fun armCount : ℕ =>
        sourceOptMaximizePickAnchorComparisonEnvelope armCount lower anchorDelta /
          (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  simpa [sourceOptMaximizePickAnchorComparisonEnvelope] using
    tendsto_sourceOptMaximizePickAnchorComparisonFraction_nhds_zero
      (lower := lower) hlower hanchorDelta hanchorDeltaLeOne

/--
The rounded-cutoff instance of Lemma 3's finite comparison envelope is
strictly sublinear in the population at fixed parameters.
-/
theorem sourceOptMaximizePickAnchorComparisonEnvelope_isLittleO_linear
    {lower anchorDelta : ℝ} (hlower : 0 < lower)
    (hanchorDelta : 0 < anchorDelta) (hanchorDeltaLeOne : anchorDelta ≤ 1) :
    (fun armCount : ℕ =>
      sourceOptMaximizePickAnchorComparisonEnvelope armCount lower anchorDelta) =o[Filter.atTop]
      fun armCount : ℕ => (armCount : ℝ) := by
  refine (isLittleO_iff_tendsto' ?_).mpr
    (tendsto_sourceOptMaximizePickAnchorComparisonEnvelope_div_nat_nhds_zero
      hlower hanchorDelta hanchorDeltaLeOne)
  filter_upwards [Filter.eventually_gt_atTop 0] with armCount harmCount hzero
  have harmCountReal : 0 < (armCount : ℝ) := by exact_mod_cast harmCount
  exact (harmCountReal.ne' hzero).elim

end FalahatgarEtAl2017MaxingRanking
