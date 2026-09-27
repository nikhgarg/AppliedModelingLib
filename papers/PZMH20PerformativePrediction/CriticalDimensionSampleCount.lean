import PZMH20PerformativePrediction.CriticalDimensionCount
import PZMH20PerformativePrediction.SampleCountRates

/-!
# Sharp dimension-two joint sample counts

The repository's all-dimensional count deliberately uses a fourth-power
inversion for the logarithmic depth term in dimension two.  This paper-local
selector keeps the exact logarithmic-depth estimate instead.  Its compact-head
requirement is the maximum of the checked `r⁻² log²(C/r)` count and the four
remaining quadratic or linear gates.  The complete selector then takes the
maximum with the existing all-shell mass and source square-rate requirements.

The conservative all-dimensional selector is not changed.
-/

namespace PZMH20PerformativePrediction

open AppliedModelingLib
open MeasureTheory

/-- The two exact logarithmic-depth gates remain valid at every larger count.
This is what permits the sharp critical count to be placed inside a joint
maximum with the mass and source-rate requirements. -/
theorem criticalDimensionLogSquaredCount_depth_gates_of_criticalCount_le
    (tailConstant : ℝ) {radius : ℝ} (hradius : 0 < radius)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailConstant)
    {count : ℕ}
    (hcount : criticalDimensionLogSquaredCount tailConstant radius ≤ count) :
    4 * (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) ≤ radius / 6 ∧
      (4 * (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ)) *
          Probability.selectedShellGeometricTailMultiplier tailConstant ≤ radius / 6 := by
  let baseCount := criticalDimensionLogSquaredCount tailConstant radius
  let coefficient := criticalDimensionDepthCoefficient tailConstant
  let ratio := coefficient / radius
  let logarithm := Real.log ratio
  let threshold := (ratio * logarithm) ^ 2
  let tailMultiplier := Probability.selectedShellGeometricTailMultiplier tailConstant
  let multiplier := max 1 tailMultiplier
  have hcoefficient_pos : 0 < coefficient := by
    dsimp [coefficient]
    exact criticalDimensionDepthCoefficient_pos tailConstant
  have hratio_exp : Real.exp 2 ≤ ratio := by
    dsimp [ratio]
    exact (le_div_iff₀ hradius).mpr (by simpa [mul_comm] using hsmall)
  have hratio_pos : 0 < ratio := div_pos hcoefficient_pos hradius
  have hlogarithm : 2 ≤ logarithm := by
    dsimp [logarithm]
    have hlog := Real.log_le_log (Real.exp_pos 2) hratio_exp
    simpa using hlog
  have hlogarithm_pos : 0 < logarithm := lt_of_lt_of_le (by norm_num) hlogarithm
  have hproduct_pos : 0 < ratio * logarithm := mul_pos hratio_pos hlogarithm_pos
  have hthreshold_exp : Real.exp 2 ≤ threshold := by
    have hexp_one : 1 ≤ Real.exp 2 := by
      simpa using (Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 2))
    have hproduct_exp : Real.exp 2 ≤ ratio * logarithm := by
      calc
        Real.exp 2 ≤ Real.exp 2 * 2 := by nlinarith [Real.exp_pos 2]
        _ ≤ ratio * logarithm :=
          mul_le_mul hratio_exp hlogarithm (by norm_num) hratio_pos.le
    dsimp [threshold]
    nlinarith [sq_nonneg (ratio * logarithm - 1)]
  have hthreshold_le_base : threshold ≤ (baseCount : ℝ) := by
    dsimp [threshold, logarithm, ratio, coefficient, baseCount]
    exact (criticalDimensionLogSquaredCount_bounds tailConstant hradius hsmall).1
  have hbase_le_count : (baseCount : ℝ) ≤ count := by exact_mod_cast hcount
  have hbase_exp : Real.exp 2 ≤ (baseCount : ℝ) :=
    hthreshold_exp.trans hthreshold_le_base
  have hcount_exp : Real.exp 2 ≤ (count : ℝ) :=
    hbase_exp.trans hbase_le_count
  have hlog_rate : Real.log (count : ℝ) / Real.sqrt (count : ℝ) ≤
      4 * radius / coefficient := by
    calc
      Real.log (count : ℝ) / Real.sqrt (count : ℝ) ≤
          Real.log (baseCount : ℝ) / Real.sqrt (baseCount : ℝ) :=
        Real.log_div_sqrt_antitoneOn hbase_exp hcount_exp hbase_le_count
      _ ≤ 4 * radius / coefficient := by
        dsimp [baseCount, coefficient]
        exact log_count_div_sqrt_criticalDimensionLogSquaredCount_le
          tailConstant hradius hsmall
  have hbase64 : 64 ≤ baseCount := by
    have hreal : (64 : ℝ) ≤ baseCount := by
      calc
        (64 : ℝ) ≤
            max 64 (criticalDimensionLogSquaredThreshold tailConstant radius) :=
          le_max_left _ _
        _ ≤ baseCount := Math.le_positiveNatCeil _
    exact_mod_cast hreal
  have hcount64 : 64 ≤ count := hbase64.trans hcount
  have hcount_pos : 0 < (count : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 64) hcount64)
  have hsqrt_pos : 0 < Real.sqrt (count : ℝ) := Real.sqrt_pos.2 hcount_pos
  have hdepth_le_log := dyadicEffectiveCountDepth_two_le_log_count count hcount64
  have hlogFour_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hdepth_rate :
      (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) ≤
        4 * radius / (coefficient * Real.log 4) := by
    calc
      (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) ≤
          (Real.log (count : ℝ) / Real.log 4) / Real.sqrt (count : ℝ) :=
        div_le_div_of_nonneg_right hdepth_le_log hsqrt_pos.le
      _ = (1 / Real.log 4) *
          (Real.log (count : ℝ) / Real.sqrt (count : ℝ)) := by ring
      _ ≤ (1 / Real.log 4) * (4 * radius / coefficient) :=
        mul_le_mul_of_nonneg_left hlog_rate (one_div_nonneg.mpr hlogFour_pos.le)
      _ = 4 * radius / (coefficient * Real.log 4) := by ring
  have hmultiplier_one : 1 ≤ multiplier := le_max_left _ _
  have hmultiplier_pos : 0 < multiplier := lt_of_lt_of_le zero_lt_one hmultiplier_one
  have htail_nonneg : 0 ≤ tailMultiplier := by
    dsimp [tailMultiplier, Probability.selectedShellGeometricTailMultiplier]
    positivity
  have htail_le : tailMultiplier ≤ multiplier := le_max_right _ _
  have hraw :
      4 * (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) ≤ radius / (6 * multiplier) := by
    calc
      4 * (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) =
          4 * ((Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
            Real.sqrt (count : ℝ)) := by ring
      _ ≤ 4 * (4 * radius / (coefficient * Real.log 4)) :=
        mul_le_mul_of_nonneg_left hdepth_rate (by norm_num)
      _ = radius / (6 * multiplier) := by
        dsimp [coefficient, criticalDimensionDepthCoefficient, multiplier, tailMultiplier]
        field_simp [hlogFour_pos.ne', hmultiplier_pos.ne']
        <;> ring
  constructor
  · exact hraw.trans (div_le_div_of_nonneg_left hradius.le (by norm_num)
      (by nlinarith [hmultiplier_one]))
  · calc
      (4 * (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ)) * tailMultiplier ≤
          (radius / (6 * multiplier)) * tailMultiplier :=
        mul_le_mul_of_nonneg_right hraw htail_nonneg
      _ ≤ (radius / (6 * multiplier)) * multiplier :=
        mul_le_mul_of_nonneg_left htail_le (by positivity)
      _ = radius / 6 := by field_simp [hmultiplier_pos.ne']

/-- The sharp dimension-two compact-head requirement: one exact logarithmic
count and the four remaining finite quadratic or linear gates. -/
noncomputable def criticalDimensionSharpHeadEffectiveCountRequirement
    (cutoff : ℕ) (confidence tailConstant radius : ℝ) : ℝ :=
  max (criticalDimensionLogSquaredCount tailConstant radius : ℝ)
    (max
      (6 ^ 2 *
        Probability.selectedShellGeometricDimensionTwoCentralRootCoefficient confidence ^ 2 /
          radius ^ 2)
      (max
        (6 * Probability.selectedShellGeometricDimensionTwoCentralCountCoefficient confidence /
          radius)
        (max
          (6 ^ 2 *
            Probability.selectedShellGeometricDimensionTwoSuccessorRootCoefficient cutoff
              confidence tailConstant ^ 2 / radius ^ 2)
          (6 ^ 2 *
            Probability.selectedShellGeometricDimensionTwoSuccessorSqrtCoefficient cutoff
              confidence tailConstant ^ 2 / radius ^ 2))))

/-- Any positive count above the sharp critical head requirement controls the
actual selected-shell dimension-two head. -/
theorem selectedShellGeometricHeadSchedule_dimensionTwo_le_of_sharpRequirement_le
    (cutoff count : ℕ) (confidence tailConstant : ℝ) {radius : ℝ}
    (hcount : 0 < count) (hradius : 0 < radius)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailConstant)
    (hrequirement :
      criticalDimensionSharpHeadEffectiveCountRequirement cutoff confidence tailConstant radius ≤
        (count : ℝ)) :
    Probability.selectedShellGeometricHeadSchedule_dimensionTwo cutoff count confidence
        tailConstant ≤ ENNReal.ofReal radius := by
  let requirement :=
    criticalDimensionSharpHeadEffectiveCountRequirement cutoff confidence tailConstant radius
  have hcritical : criticalDimensionLogSquaredCount tailConstant radius ≤ count := by
    have hreal : (criticalDimensionLogSquaredCount tailConstant radius : ℝ) ≤ count := by
      exact (le_max_left _ _).trans hrequirement
    exact_mod_cast hreal
  obtain ⟨hcentralDepth, hsuccessorDepth⟩ :=
    criticalDimensionLogSquaredCount_depth_gates_of_criticalCount_le tailConstant hradius hsmall
      hcritical
  have hgateOne :
      6 ^ 2 *
          Probability.selectedShellGeometricDimensionTwoCentralRootCoefficient confidence ^ 2 /
          radius ^ 2 ≤ requirement := by
    dsimp [requirement, criticalDimensionSharpHeadEffectiveCountRequirement]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hgateTwo :
      6 * Probability.selectedShellGeometricDimensionTwoCentralCountCoefficient confidence /
          radius ≤ requirement := by
    dsimp [requirement, criticalDimensionSharpHeadEffectiveCountRequirement]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hgateThree :
      6 ^ 2 *
          Probability.selectedShellGeometricDimensionTwoSuccessorRootCoefficient cutoff confidence
            tailConstant ^ 2 / radius ^ 2 ≤ requirement := by
    dsimp [requirement, criticalDimensionSharpHeadEffectiveCountRequirement]
    exact (((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)
  have hgateFour :
      6 ^ 2 *
          Probability.selectedShellGeometricDimensionTwoSuccessorSqrtCoefficient cutoff confidence
            tailConstant ^ 2 / radius ^ 2 ≤ requirement := by
    dsimp [requirement, criticalDimensionSharpHeadEffectiveCountRequirement]
    exact (((le_max_right _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)
  apply Probability.selectedShellGeometricHeadSchedule_dimensionTwo_le_of_sixth_component_bounds
    cutoff count confidence tailConstant radius hradius.le
  · apply AppliedModelingLib.Math.div_sqrt_nat_le_div_of_sq_mul_le count hcount
      (Probability.selectedShellGeometricDimensionTwoCentralRootCoefficient_nonneg confidence)
      hradius.le (by norm_num)
    apply (div_le_iff₀ (sq_pos_of_pos hradius)).mp
    exact hgateOne.trans hrequirement
  · exact hcentralDepth
  · apply AppliedModelingLib.Math.div_nat_le_div_of_mul_le count hcount (by norm_num)
    apply (div_le_iff₀ hradius).mp
    exact hgateTwo.trans hrequirement
  · apply AppliedModelingLib.Math.div_sqrt_nat_le_div_of_sq_mul_le count hcount
      (Probability.selectedShellGeometricDimensionTwoSuccessorRootCoefficient_nonneg cutoff
        confidence tailConstant) hradius.le (by norm_num)
    apply (div_le_iff₀ (sq_pos_of_pos hradius)).mp
    exact hgateThree.trans hrequirement
  · exact hsuccessorDepth
  · apply AppliedModelingLib.Math.div_sqrt_nat_le_div_of_sq_mul_le count hcount
      (Probability.selectedShellGeometricDimensionTwoSuccessorSqrtCoefficient_nonneg cutoff
        confidence tailConstant) hradius.le (by norm_num)
    apply (div_le_iff₀ (sq_pos_of_pos hradius)).mp
    exact hgateFour.trans hrequirement

/-- The complete sharp dimension-two requirement combines the exact critical
head with the common mass and source square-rate gates. -/
noncomputable def criticalDimensionAllShellEffectiveCountRequirement
    (cutoff : ℕ) (eta alpha gamma tailBound deviation scaledDeviation confidence radius
      tolerance : ℝ) : ℝ :=
  max
    (criticalDimensionSharpHeadEffectiveCountRequirement cutoff confidence tailBound radius)
    (max
      (Probability.pOneFournierGuillinUniformAllShellMassEffectiveCountRequirement eta deviation
        scaledDeviation gamma tailBound tolerance)
      (Probability.pOneFournierGuillinUniformSquareRateEffectiveCountRequirement eta alpha gamma
        tailBound scaledDeviation))

/-- The actual positive natural count selected by the complete sharp
dimension-two requirement. -/
noncomputable def criticalDimensionAllShellEffectiveCount
    (cutoff : ℕ) (eta alpha gamma tailBound deviation scaledDeviation confidence radius
      tolerance : ℝ) : ℕ :=
  Math.positiveNatCeil
    (criticalDimensionAllShellEffectiveCountRequirement cutoff eta alpha gamma tailBound deviation
      scaledDeviation confidence radius tolerance)

theorem one_le_criticalDimensionAllShellEffectiveCount
    (cutoff : ℕ) (eta alpha gamma tailBound deviation scaledDeviation confidence radius
      tolerance : ℝ) :
    1 ≤ criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
      scaledDeviation confidence radius tolerance := by
  unfold criticalDimensionAllShellEffectiveCount
  exact Math.one_le_positiveNatCeil _

theorem criticalDimensionAllShellEffectiveCountRequirement_le_count
    (cutoff : ℕ) (eta alpha gamma tailBound deviation scaledDeviation confidence radius
      tolerance : ℝ) :
    criticalDimensionAllShellEffectiveCountRequirement cutoff eta alpha gamma tailBound deviation
        scaledDeviation confidence radius tolerance ≤
      criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
        scaledDeviation confidence radius tolerance := by
  unfold criticalDimensionAllShellEffectiveCount
  exact Math.le_positiveNatCeil _

/-- The complete sharp natural count controls the actual dimension-two head. -/
theorem selectedShellGeometricHeadSchedule_dimensionTwo_le_of_criticalAllShellCount
    (cutoff : ℕ) {eta alpha gamma tailBound deviation scaledDeviation confidence radius
      tolerance : ℝ}
    (hradius : 0 < radius)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailBound) :
    Probability.selectedShellGeometricHeadSchedule_dimensionTwo cutoff
        (criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
          scaledDeviation confidence radius tolerance)
        confidence tailBound ≤ ENNReal.ofReal radius := by
  let count := criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
    scaledDeviation confidence radius tolerance
  apply selectedShellGeometricHeadSchedule_dimensionTwo_le_of_sharpRequirement_le
    cutoff count confidence tailBound
  · exact lt_of_lt_of_le zero_lt_one
      (one_le_criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
        scaledDeviation confidence radius tolerance)
  · exact hradius
  · exact hsmall
  · calc
      criticalDimensionSharpHeadEffectiveCountRequirement cutoff confidence tailBound radius ≤
          criticalDimensionAllShellEffectiveCountRequirement cutoff eta alpha gamma tailBound
            deviation scaledDeviation confidence radius tolerance := by
        unfold criticalDimensionAllShellEffectiveCountRequirement
        exact le_max_left _ _
      _ ≤ count :=
        criticalDimensionAllShellEffectiveCountRequirement_le_count cutoff eta alpha gamma
          tailBound deviation scaledDeviation confidence radius tolerance

/-- The complete sharp natural count meets the common all-shell mass budget. -/
theorem criticalDimensionAllShellMassBudget_le
    (cutoff : ℕ) {eta alpha gamma tailBound deviation scaledDeviation confidence radius
      tolerance : ℝ}
    (heta : 0 < eta) (hdeviation : 0 < deviation) (hscaledDeviation : 0 < scaledDeviation)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound) (htolerance : 0 < tolerance) :
    Probability.pOneFournierGuillinUniformAllShellMassSquareRateBudget
      (criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
        scaledDeviation confidence radius tolerance)
      eta deviation scaledDeviation gamma tailBound ≤ tolerance := by
  let count := criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
    scaledDeviation confidence radius tolerance
  apply Probability.pOneFournierGuillinUniformAllShellMassSquareRateBudget_le_of_requirement_le
    count heta hdeviation hscaledDeviation hgamma htailBound htolerance
  · exact lt_of_lt_of_le zero_lt_one
      (one_le_criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
        scaledDeviation confidence radius tolerance)
  · calc
      Probability.pOneFournierGuillinUniformAllShellMassEffectiveCountRequirement eta deviation
          scaledDeviation gamma tailBound tolerance ≤
          criticalDimensionAllShellEffectiveCountRequirement cutoff eta alpha gamma tailBound
            deviation scaledDeviation confidence radius tolerance := by
        unfold criticalDimensionAllShellEffectiveCountRequirement
        exact (le_max_left _ _).trans (le_max_right _ _)
      _ ≤ count :=
        criticalDimensionAllShellEffectiveCountRequirement_le_count cutoff eta alpha gamma
          tailBound deviation scaledDeviation confidence radius tolerance

/-- The complete sharp natural count meets all three common source square-rate
gates, with no new concentration assumption. -/
theorem criticalDimensionAllShellSquareRateGates
    (cutoff : ℕ) {eta alpha gamma tailBound deviation scaledDeviation confidence radius
      tolerance : ℝ}
    (heta : 0 < eta) (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hscaledDeviation : 0 < scaledDeviation) (halphaGap : 1 + eta < alpha) :
    let count := criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
      scaledDeviation confidence radius tolerance
    1 ≤ (count : ℝ) * Probability.pOneFournierGuillinShellCoefficient eta ^ 2 *
        scaledDeviation ^ 2 / (18 * tailBound) ∧
      1 ≤ (count : ℝ) * Probability.pOneFournierGuillinShellCoefficient eta *
        Real.rpow 2 (-(1 + eta)) * scaledDeviation ^ 2 * Real.log 9 / 8 ∧
      1 ≤ ((count : ℝ) * Probability.pOneFournierGuillinShellCoefficient eta *
        scaledDeviation ^ 2 * gamma / 4) *
          (Real.rpow 2 (alpha - 1 - eta) - 1) := by
  dsimp only
  let count := criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
    scaledDeviation confidence radius tolerance
  apply Probability.pOneFournierGuillinUniformSquareRateGates_of_requirement_le count heta hgamma
    htailBound hscaledDeviation halphaGap
  calc
    Probability.pOneFournierGuillinUniformSquareRateEffectiveCountRequirement eta alpha gamma
        tailBound scaledDeviation ≤
        criticalDimensionAllShellEffectiveCountRequirement cutoff eta alpha gamma tailBound
          deviation scaledDeviation confidence radius tolerance := by
      unfold criticalDimensionAllShellEffectiveCountRequirement
      exact (le_max_right _ _).trans (le_max_right _ _)
    _ ≤ count :=
      criticalDimensionAllShellEffectiveCountRequirement_le_count cutoff eta alpha gamma tailBound
        deviation scaledDeviation confidence radius tolerance

/-- The roundwise sharp critical schedule with the same confidence split used
by the existing Theorem 3.10 schedules. -/
noncomputable def criticalDimensionAllShellConcreteCountSchedule
    (cutoff : ℕ) (eta alpha gamma tailBound deviation scaledDeviation : ℝ)
    (failureBudget radiusSchedule : ℕ → ℝ) : ℕ → ℕ := fun round =>
  criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
    scaledDeviation (Math.expConfidenceForHalfBudget (failureBudget round))
    (radiusSchedule round) (failureBudget round / 2)

/-- Under the common radial-tail envelope, the complete sharp count bounds the
actual adaptive compact-head budget, not merely its deterministic schedule. -/
theorem selectedShellGeometricCompactHeadBudget_dimensionTwo_le_of_criticalAllShellCount
    (cutoff : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {eta alpha gamma tailBound deviation scaledDeviation confidence radius tolerance : ℝ}
    (hconfidence : 0 ≤ confidence) (halpha : 1 ≤ alpha) (hgamma : 0 < gamma)
    (hmoment : Probability.HasExponentialRadialMoment law alpha gamma)
    (htail : Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound)
    (hradius : 0 < radius)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailBound) :
    Probability.selectedShellGeometricCompactHeadBudget 2 cutoff
      (criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
        scaledDeviation confidence radius tolerance)
      law
      (Probability.selectedShellGeometricEffectiveHeadDepth 2 cutoff
        (criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
          scaledDeviation confidence radius tolerance)
        law confidence) confidence ≤ ENNReal.ofReal radius := by
  let count := criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
    scaledDeviation confidence radius tolerance
  have hcount : 0 < count := lt_of_lt_of_le zero_lt_one
    (one_le_criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
      scaledDeviation confidence radius tolerance)
  calc
    Probability.selectedShellGeometricCompactHeadBudget 2 cutoff count law
        (Probability.selectedShellGeometricEffectiveHeadDepth 2 cutoff count law confidence)
        confidence ≤
        Probability.selectedShellGeometricHeadSchedule_dimensionTwo cutoff count confidence
          tailBound :=
      Probability.selectedShellGeometricCompactHeadBudget_dimensionTwo_le_headSchedule_of_tail_le
        cutoff count law hcount hconfidence halpha hgamma hmoment htail
    _ ≤ ENNReal.ofReal radius :=
      selectedShellGeometricHeadSchedule_dimensionTwo_le_of_criticalAllShellCount
        cutoff hradius hsmall

/-- The sharp critical schedule supplies both pieces needed by the adaptive
Theorem 3.10 path: an actual compact-head bound and a measurable certificate
whose probability is within the allocated round budget.  Every probability
bound is derived from the existing all-count concentration theorem; no
certificate is assumed. -/
theorem exists_pOneFournierGuillin_uniformSelectedShellPartitionCertificate_criticalDimensionConcreteCountSchedule
    (cutoff : ℕ)
    {eta alpha gamma momentBound deviation scaledDeviation tailBound : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (halpha_pos : 0 < alpha) (hgamma_pos : 0 < gamma)
    (halpha_gap : 1 + eta < alpha)
    (hscaled : scaledDeviation = deviation * Real.rpow 2 (-(1 + eta)))
    (hscaled_pos : 0 < scaledDeviation) (hscaled_le_one : scaledDeviation ≤ 1)
    (htailBound_pos : 0 < tailBound)
    (htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
      Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
        Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound)
    (failureBudget radiusSchedule : ℕ → ℝ)
    (hfailureBudget : ∀ round, 0 < failureBudget round)
    (hradius : ∀ round, 0 < radiusSchedule round)
    (hsmall : ∀ round,
      Real.exp 2 * radiusSchedule round ≤ criticalDimensionDepthCoefficient tailBound) :
    ∃ gateScale : ℕ,
      scaledDeviation ≤ Probability.pOneFournierGuillinHeadGateRadius eta gateScale →
      ∀ round (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))),
        Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
        let count := criticalDimensionAllShellConcreteCountSchedule cutoff eta alpha gamma
          tailBound deviation scaledDeviation failureBudget radiusSchedule round
        let confidence := Math.expConfidenceForHalfBudget (failureBudget round)
        Probability.selectedShellGeometricCompactHeadBudget 2 cutoff count law
              (Probability.selectedShellGeometricEffectiveHeadDepth 2 cutoff count law confidence)
              confidence ≤ ENNReal.ofReal (radiusSchedule round) ∧
          (Probability.finiteIIDSampleLaw
              (law : Measure (EuclideanSpace ℝ (Fin 2))) count).real
            (Probability.pOneFournierGuillinSelectedShellPartitionCertificate
              2 law count eta deviation
              (Probability.selectedShellGeometricEffectiveHeadDepth 2 cutoff count law confidence)
              confidence) ≤ failureBudget round := by
  obtain ⟨gateScale, hconcentration⟩ :=
    Probability.exists_pOneFournierGuillin_uniformSelectedShellPartitionCertificateEffectiveHead_smallDeviation_squareRate_allCounts
      2 cutoff (by norm_num) heta_pos heta_le_one halpha_pos hgamma_pos halpha_gap
  refine ⟨gateScale, fun hscaled_gate round law hmoment => ?_⟩
  let confidence := Math.expConfidenceForHalfBudget (failureBudget round)
  let tolerance := failureBudget round / 2
  let count := criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
    scaledDeviation confidence (radiusSchedule round) tolerance
  have hconfidence : 0 ≤ confidence := Math.expConfidenceForHalfBudget_nonneg _
  have htolerance : 0 < tolerance := half_pos (hfailureBudget round)
  have hcount : 0 < count := lt_of_lt_of_le zero_lt_one
    (one_le_criticalDimensionAllShellEffectiveCount cutoff eta alpha gamma tailBound deviation
      scaledDeviation confidence (radiusSchedule round) tolerance)
  letI : Nonempty (Fin count) := Fin.pos_iff_nonempty.mp hcount
  have htailActual := htailEnvelope law hmoment
  have htailActual_pos :
      0 < Probability.fifthOrderExponentialRadialTailConstant law alpha gamma :=
    Probability.fifthOrderExponentialRadialTailConstant_pos law hgamma_pos
      hmoment.hasExponentialRadialMoment
  obtain ⟨hboundedRate, hheadRate, htailRate⟩ :=
    criticalDimensionAllShellSquareRateGates cutoff heta_pos hgamma_pos htailBound_pos hscaled_pos
      halpha_gap (deviation := deviation) (confidence := confidence)
      (radius := radiusSchedule round) (tolerance := tolerance)
  have hnumerator_nonneg : 0 ≤
      (count : ℝ) * Probability.pOneFournierGuillinShellCoefficient eta ^ 2 *
        scaledDeviation ^ 2 := by
    positivity
  have hboundedRateActual :
      1 ≤ (count : ℝ) * Probability.pOneFournierGuillinShellCoefficient eta ^ 2 *
        scaledDeviation ^ 2 /
          (18 * Probability.fifthOrderExponentialRadialTailConstant law alpha gamma) := by
    apply hboundedRate.trans
    apply div_le_div_of_nonneg_left hnumerator_nonneg
    · exact mul_pos (by norm_num) htailActual_pos
    · exact mul_le_mul_of_nonneg_left htailActual (by norm_num)
  have hcertificate := hconcentration confidence hconfidence count hcount law hmoment
    hscaled hscaled_pos hscaled_le_one hscaled_gate hboundedRateActual hheadRate htailRate
  have hmassActual :=
    Probability.pOneFournierGuillinAllShellMassSquareRateBudget_le_uniform_of_tail_le
      law count eta deviation scaledDeviation alpha gamma tailBound hgamma_pos
      hmoment.hasExponentialRadialMoment htailBound_pos htailActual
  have hdeviation_pos : 0 < deviation := by
    have hdecay_pos : 0 < Real.rpow 2 (-(1 + eta)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    apply pos_of_mul_pos_left (by simpa [hscaled] using hscaled_pos) hdecay_pos.le
  have hmassUniform := criticalDimensionAllShellMassBudget_le cutoff heta_pos hdeviation_pos
    hscaled_pos hgamma_pos htailBound_pos htolerance
    (alpha := alpha) (confidence := confidence) (radius := radiusSchedule round)
  have hhead :=
    selectedShellGeometricCompactHeadBudget_dimensionTwo_le_of_criticalAllShellCount
      cutoff law hconfidence (by linarith) hgamma_pos hmoment.hasExponentialRadialMoment
      htailActual (hradius round) (hsmall round)
      (eta := eta) (deviation := deviation) (scaledDeviation := scaledDeviation)
      (tolerance := tolerance)
  change
    Probability.selectedShellGeometricCompactHeadBudget 2 cutoff count law
          (Probability.selectedShellGeometricEffectiveHeadDepth 2 cutoff count law confidence)
          confidence ≤ ENNReal.ofReal (radiusSchedule round) ∧
      (Probability.finiteIIDSampleLaw
          (law : Measure (EuclideanSpace ℝ (Fin 2))) count).real
        (Probability.pOneFournierGuillinSelectedShellPartitionCertificate
          2 law count eta deviation
          (Probability.selectedShellGeometricEffectiveHeadDepth 2 cutoff count law confidence)
          confidence) ≤ failureBudget round
  refine ⟨hhead, ?_⟩
  calc
    (Probability.finiteIIDSampleLaw
        (law : Measure (EuclideanSpace ℝ (Fin 2))) count).real
        (Probability.pOneFournierGuillinSelectedShellPartitionCertificate
          2 law count eta deviation
          (Probability.selectedShellGeometricEffectiveHeadDepth 2 cutoff count law confidence)
          confidence) ≤
        Probability.pOneFournierGuillinAllShellMassSquareRateBudget law count eta deviation
          scaledDeviation alpha gamma + Real.exp (-confidence) := hcertificate
    _ ≤ Probability.pOneFournierGuillinUniformAllShellMassSquareRateBudget count eta deviation
          scaledDeviation gamma tailBound + Real.exp (-confidence) := by
      simpa [add_comm] using add_le_add_left hmassActual (Real.exp (-confidence))
    _ ≤ tolerance + Real.exp (-confidence) := by
      simpa [add_comm] using add_le_add_left hmassUniform (Real.exp (-confidence))
    _ ≤ tolerance + tolerance := by
      simpa [confidence, tolerance, add_comm] using
        add_le_add_right
          (Math.exp_neg_expConfidenceForHalfBudget_le_half (hfailureBudget round)) tolerance
    _ = failureBudget round := by dsimp [tolerance]; ring

end PZMH20PerformativePrediction
