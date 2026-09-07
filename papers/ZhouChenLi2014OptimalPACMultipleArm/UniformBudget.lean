import ZhouChenLi2014OptimalPACMultipleArm.UniformConcentration

/-!
# Executable uniform-final-stage budget

This is the ceiling version of the supplement's uniform-sampling final stage.
It is stated for an arbitrary finite surviving set; when QE has reduced that
set to at most four arms, its logarithmic arm-count term is a constant.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/--
The natural-number per-arm budget for the supplement's uniform final stage.
It is the ceiling of the two-sided Hoeffding target for all remaining arms.
-/
noncomputable def uniformBernoulliBatchSampleBudget
    (armCount : ℕ) (epsilon delta : ℝ) : ℕ :=
  ⌈2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta)⌉₊

theorem uniformBernoulliBatchSampleBudget_realTarget_le
    (armCount : ℕ) (epsilon delta : ℝ) :
    2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) ≤
      (uniformBernoulliBatchSampleBudget armCount epsilon delta : ℝ) :=
  Nat.le_ceil _

theorem uniformBernoulliBatchSampleBudget_pos
    (armCount : ℕ) (epsilon delta : ℝ)
    (hcard : 0 < armCount) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    0 < uniformBernoulliBatchSampleBudget armCount epsilon delta := by
  have hcardReal : 0 < (armCount : ℝ) := by exact_mod_cast hcard
  have hratio : 1 < 2 * (armCount : ℝ) / delta := by
    apply (lt_div_iff₀ hdelta).mpr
    have hcardGeOne : 1 ≤ (armCount : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hcard)
    nlinarith
  have hlog : 0 < Real.log (2 * (armCount : ℝ) / delta) := Real.log_pos hratio
  have htarget : 0 < 2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) := by
    exact mul_pos (div_pos (by norm_num) (sq_pos_of_pos hepsilon)) hlog
  have hceiling := uniformBernoulliBatchSampleBudget_realTarget_le armCount epsilon delta
  have hbudgetReal : 0 < (uniformBernoulliBatchSampleBudget armCount epsilon delta : ℝ) :=
    lt_of_lt_of_le htarget hceiling
  exact_mod_cast hbudgetReal

/-- The executable ceiling budget differs from its positive Hoeffding target
by at most one pull.  This is the resource-side companion to
`uniformBernoulliBatchSampleBudget_realTarget_le`; the positivity hypotheses
are exactly those under which the final-stage concentration theorem operates.
-/
theorem uniformBernoulliBatchSampleBudget_real_le_target_add_one
    (armCount : ℕ) (epsilon delta : ℝ)
    (hcard : 0 < armCount) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (uniformBernoulliBatchSampleBudget armCount epsilon delta : ℝ) ≤
      2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) + 1 := by
  have hcardReal : 0 < (armCount : ℝ) := by exact_mod_cast hcard
  have hratio : 1 < 2 * (armCount : ℝ) / delta := by
    apply (lt_div_iff₀ hdelta).mpr
    have hcardGeOne : 1 ≤ (armCount : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hcard)
    nlinarith
  have hlog : 0 < Real.log (2 * (armCount : ℝ) / delta) := Real.log_pos hratio
  have htarget : 0 ≤ 2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) := by
    exact mul_nonneg (le_of_lt (div_pos (by norm_num) (sq_pos_of_pos hepsilon))) hlog.le
  unfold uniformBernoulliBatchSampleBudget
  exact (Nat.ceil_lt_add_one htarget).le

/-- A Hoeffding tail with a sufficient real budget is at most its confidence. -/
theorem uniformBernoulliBatch_tail_le_confidence_of_budget
    (sampleCount : ℕ) (epsilon confidence : ℝ)
    (hcount : 0 < (sampleCount : ℝ)) (hepsilon : 0 < epsilon)
    (hconfidence : 0 < confidence)
    (hbudget : 2 / epsilon ^ 2 * Real.log (2 / confidence) ≤ (sampleCount : ℝ)) :
    2 * Real.exp (-((sampleCount : ℝ) * (epsilon / 2)) ^ 2 /
      (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) ≤ confidence := by
  have hepsilonSqPos : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hepsilonSqNe : epsilon ^ 2 ≠ 0 := ne_of_gt hepsilonSqPos
  have hfactorPos : 0 < epsilon ^ 2 / 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hbudget (le_of_lt hfactorPos)
  have hlogBound : Real.log (2 / confidence) ≤ (sampleCount : ℝ) * epsilon ^ 2 / 2 := by
    calc
      Real.log (2 / confidence) =
          (2 / epsilon ^ 2 * Real.log (2 / confidence)) * (epsilon ^ 2 / 2) := by
            field_simp [hepsilonSqNe]
      _ ≤ (sampleCount : ℝ) * (epsilon ^ 2 / 2) := hscaled
      _ = (sampleCount : ℝ) * epsilon ^ 2 / 2 := by ring
  have hexponent : -(sampleCount : ℝ) * epsilon ^ 2 / 2 ≤ -Real.log (2 / confidence) := by
    linarith
  have hratioPos : 0 < 2 / confidence := div_pos (by norm_num) hconfidence
  have hnegativeLogExp : Real.exp (-Real.log (2 / confidence)) = confidence / 2 := by
    rw [Real.exp_neg, Real.exp_log hratioPos]
    field_simp [ne_of_gt hconfidence]
  have htailFormula :
      -((sampleCount : ℝ) * (epsilon / 2)) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ)) =
          -(sampleCount : ℝ) * epsilon ^ 2 / 2 := by
    have hcountNe : (sampleCount : ℝ) ≠ 0 := ne_of_gt hcount
    field_simp [hcountNe]
    ring
  calc
    2 * Real.exp (-((sampleCount : ℝ) * (epsilon / 2)) ^ 2 /
      (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) =
        2 * Real.exp (-(sampleCount : ℝ) * epsilon ^ 2 / 2) := by rw [htailFormula]
    _ ≤ 2 * Real.exp (-Real.log (2 / confidence)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)
    _ = confidence := by rw [hnegativeLogExp]; ring

/--
At its executable per-arm budget, the uniform final stage returns an
epsilon-PAC arm with failure probability at most `delta`.
-/
theorem uniformBernoulliBatchBestArm_failure_probability_of_budget {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (uniformBernoulliBatchLaw mean hmean
      (uniformBernoulliBatchSampleBudget (Fintype.card Arm) epsilon delta)).toMeasure.real
      {labelTable | ¬ EpsilonPACBestArm mean epsilon
        (uniformBernoulliBatchBestArm
          (uniformBernoulliBatchSampleBudget (Fintype.card Arm) epsilon delta) labelTable)} ≤ delta := by
  let sampleCount := uniformBernoulliBatchSampleBudget (Fintype.card Arm) epsilon delta
  have hcard : 0 < Fintype.card Arm := Fintype.card_pos
  have hcardReal : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcard
  have hcountNat : 0 < sampleCount :=
    uniformBernoulliBatchSampleBudget_pos (Fintype.card Arm) epsilon delta
      hcard hepsilon hdelta hdeltaLeOne
  have hcount : 0 < (sampleCount : ℝ) := by exact_mod_cast hcountNat
  have htarget : 2 / epsilon ^ 2 * Real.log (2 / (delta / (Fintype.card Arm : ℝ))) ≤
      (sampleCount : ℝ) := by
    have hbudget := uniformBernoulliBatchSampleBudget_realTarget_le
      (Fintype.card Arm) epsilon delta
    rw [show 2 / (delta / (Fintype.card Arm : ℝ)) =
        2 * (Fintype.card Arm : ℝ) / delta by field_simp [ne_of_gt hcardReal, ne_of_gt hdelta]]
    exact hbudget
  have htail : 2 * Real.exp (-((sampleCount : ℝ) * (epsilon / 2)) ^ 2 /
      (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) ≤ delta / (Fintype.card Arm : ℝ) :=
    uniformBernoulliBatch_tail_le_confidence_of_budget sampleCount epsilon
      (delta / (Fintype.card Arm : ℝ)) hcount hepsilon
      (div_pos hdelta hcardReal) htarget
  change
    (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure.real
      {labelTable | ¬ EpsilonPACBestArm mean epsilon
        (uniformBernoulliBatchBestArm sampleCount labelTable)} ≤ delta
  calc
    (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure.real
        {labelTable | ¬ EpsilonPACBestArm mean epsilon
          (uniformBernoulliBatchBestArm sampleCount labelTable)} ≤
        (Fintype.card Arm : ℝ) * 2 * Real.exp
          (-((sampleCount : ℝ) * (epsilon / 2)) ^ 2 /
            (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) :=
      uniformBernoulliBatchBestArm_failure_probability mean hmean sampleCount
        hcountNat epsilon hepsilon.le
    _ ≤ (Fintype.card Arm : ℝ) * (delta / (Fintype.card Arm : ℝ)) := by
      nlinarith [htail]
    _ = delta := by field_simp [ne_of_gt hcardReal]

end ZhouChenLi2014OptimalPACMultipleArm
