import ZhouChenLi2014OptimalPACMultipleArm.QuartileSourceSchedule

/-!
# Finite accuracy budget for the source QE schedule

The source gives its round radii and total budget only up to big-O constants.
This file keeps the source's geometric `Q_r` and `delta_r` schedules, while
making one fully finite *formalizer-specified* accuracy budget explicit.  It
is not presented as the source's hidden optimal constant.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL
open scoped BigOperators

/-- A geometric per-round radius whose two-sided accumulated loss is at most
the QE accuracy allowance.  The decay is the one already displayed in the
source confidence schedule. -/
noncomputable def quartileSourceAccuracyTarget
    (epsilonQE : ℝ) (round : ℕ) : ℝ :=
  epsilonQE * (1 - quartileSourceFailureDecay) * quartileSourceFailureDecay ^ round / 2

/-- The least per-arm batch size that makes the explicit source radius no
larger than `quartileSourceAccuracyTarget`. -/
noncomputable def quartileSourceAccuracyPerArmRequirement
    (epsilonQE delta : ℝ) (round : ℕ) : ℕ :=
  ⌈(2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
    (2 * quartileSourceAccuracyTarget epsilonQE round ^ 2)⌉₊

/-- The least source total budget that gives the deterministic round its
required number of samples per surviving arm, under the documented floor
convention for `Q_r`. -/
noncomputable def quartileSourceAccuracyRoundBudgetRequirement
    (initialCount : ℕ) (epsilonQE delta : ℝ) (round : ℕ) : ℕ :=
  ⌈((quartileSurvivorCountIter round initialCount : ℝ) *
      quartileSourceAccuracyPerArmRequirement epsilonQE delta round) /
    quartileSourceRoundBudgetWeight round⌉₊

/-- The finite maximum of the accuracy requirements over the selected QE
horizon. -/
noncomputable def quartileSourceAccuracyTotalBudgetRequirement
    (initialCount roundCount : ℕ) (epsilonQE delta : ℝ) : ℕ :=
  (Finset.range roundCount).sup
    (quartileSourceAccuracyRoundBudgetRequirement initialCount epsilonQE delta)

theorem quartileSourceAccuracyTarget_pos {epsilonQE : ℝ} (hepsilonQE : 0 < epsilonQE)
    (round : ℕ) :
    0 < quartileSourceAccuracyTarget epsilonQE round := by
  unfold quartileSourceAccuracyTarget
  exact div_pos
    (mul_pos (mul_pos hepsilonQE (sub_pos.mpr quartileSourceFailureDecay_lt_one))
      (pow_pos quartileSourceFailureDecay_pos _)) (by norm_num)

theorem quartileSourceAccuracyTarget_nonneg {epsilonQE : ℝ} (hepsilonQE : 0 ≤ epsilonQE)
    (round : ℕ) :
    0 ≤ quartileSourceAccuracyTarget epsilonQE round := by
  unfold quartileSourceAccuracyTarget
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg hepsilonQE (sub_nonneg.mpr quartileSourceFailureDecay_lt_one.le))
      (pow_nonneg quartileSourceFailureDecay_pos.le _)) (by norm_num)

theorem quartileSourceAccuracyTarget_sum_two_le
    (epsilonQE : ℝ) (hepsilonQE : 0 ≤ epsilonQE) (roundCount : ℕ) :
    ∑ round ∈ Finset.range roundCount,
      2 * quartileSourceAccuracyTarget epsilonQE round ≤ epsilonQE := by
  have hsum := quartileSourceFailureBudget_sum_le epsilonQE hepsilonQE roundCount
  calc
    (∑ round ∈ Finset.range roundCount,
        2 * quartileSourceAccuracyTarget epsilonQE round) =
        ∑ round ∈ Finset.range roundCount,
          quartileSourceFailureBudget epsilonQE round := by
            apply Finset.sum_congr rfl
            intro round hround
            simp only [quartileSourceAccuracyTarget, quartileSourceFailureBudget]
            ring
    _ ≤ epsilonQE := hsum

/-- A positive accuracy and confidence budget require at least one sample in
every nonterminal QE batch. -/
theorem quartileSourceAccuracyPerArmRequirement_pos
    (epsilonQE delta : ℝ) (round : ℕ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hepsilonQE : 0 < epsilonQE) :
    0 < quartileSourceAccuracyPerArmRequirement epsilonQE delta round := by
  have hconfidencePos : 0 < quartileSourceFailureBudget delta round :=
    quartileSourceFailureBudget_pos hdelta round
  have hconfidenceLeOne : quartileSourceFailureBudget delta round ≤ 1 :=
    (quartileSourceFailureBudget_le_total hdelta.le round).trans hdeltaLeOne
  have hratio : 1 ≤ 2 / quartileSourceFailureBudget delta round := by
    apply (le_div_iff₀ hconfidencePos).mpr
    linarith
  have htargetPos : 0 < quartileSourceAccuracyTarget epsilonQE round :=
    quartileSourceAccuracyTarget_pos hepsilonQE round
  apply Nat.ceil_pos.mpr
  apply div_pos
  · have hlog : 0 ≤ Real.log (2 / quartileSourceFailureBudget delta round) :=
      Real.log_nonneg hratio
    linarith
  · positivity

/-- A per-arm batch meeting its finite ceiling requirement makes the source
square-root radius no larger than the declared round target. -/
theorem quartileSourceError_le_accuracyTarget_of_perArmRequirement
    (totalBudget initialCount : ℕ) (epsilonQE delta : ℝ) (round : ℕ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hepsilonQE : 0 < epsilonQE)
    (hcount : quartileSourceAccuracyPerArmRequirement epsilonQE delta round ≤
      quartileSourceScheduledPerArmSampleCount totalBudget initialCount round) :
    quartileSourceError totalBudget initialCount delta round ≤
      quartileSourceAccuracyTarget epsilonQE round := by
  let numerator : ℝ := 2 + Real.log (2 / quartileSourceFailureBudget delta round)
  let target : ℝ := quartileSourceAccuracyTarget epsilonQE round
  let required : ℕ := quartileSourceAccuracyPerArmRequirement epsilonQE delta round
  let sampleCount : ℕ := quartileSourceScheduledPerArmSampleCount totalBudget initialCount round
  have hconfidencePos : 0 < quartileSourceFailureBudget delta round :=
    quartileSourceFailureBudget_pos hdelta round
  have hconfidenceLeOne : quartileSourceFailureBudget delta round ≤ 1 :=
    (quartileSourceFailureBudget_le_total hdelta.le round).trans hdeltaLeOne
  have hratio : 1 ≤ 2 / quartileSourceFailureBudget delta round := by
    apply (le_div_iff₀ hconfidencePos).mpr
    linarith
  have hnumNonneg : 0 ≤ numerator := by
    dsimp [numerator]
    have hlog : 0 ≤ Real.log (2 / quartileSourceFailureBudget delta round) :=
      Real.log_nonneg hratio
    linarith
  have htargetPos : 0 < target := by
    dsimp [target]
    exact quartileSourceAccuracyTarget_pos hepsilonQE round
  have hrequiredReal : numerator / (2 * target ^ 2) ≤ (required : ℝ) := by
    dsimp [required]
    exact Nat.le_ceil _
  have hcountReal : (required : ℝ) ≤ sampleCount := by
    exact_mod_cast hcount
  have hsamplePos : 0 < (sampleCount : ℝ) := by
    have hrequiredPos : 0 < (required : ℝ) := by
      exact_mod_cast quartileSourceAccuracyPerArmRequirement_pos epsilonQE delta round
        hdelta hdeltaLeOne hepsilonQE
    exact hrequiredPos.trans_le hcountReal
  have hinside : numerator / (2 * (sampleCount : ℝ)) ≤ target ^ 2 := by
    have hscaled : numerator ≤ (sampleCount : ℝ) * (2 * target ^ 2) := by
      have hfirst : numerator ≤ (required : ℝ) * (2 * target ^ 2) := by
        exact (div_le_iff₀ (by positivity : 0 < 2 * target ^ 2)).mp hrequiredReal
      have hsecond : (required : ℝ) * (2 * target ^ 2) ≤
          (sampleCount : ℝ) * (2 * target ^ 2) :=
        mul_le_mul_of_nonneg_right hcountReal (by positivity)
      exact hfirst.trans hsecond
    apply (div_le_iff₀ (by positivity : 0 < 2 * (sampleCount : ℝ))).mpr
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hinside
  change Real.sqrt (numerator / (2 * (sampleCount : ℝ))) ≤ target
  calc
    Real.sqrt (numerator / (2 * (sampleCount : ℝ))) ≤ Real.sqrt (target ^ 2) := hsqrt
    _ = target := Real.sqrt_sq htargetPos.le

/-- An explicit accuracy-round requirement bounds the full number of pulls
needed in that deterministic QE round. -/
theorem quartileSourceAccuracyRequiredPulls_le_roundBudget
    (totalBudget initialCount : ℕ) (epsilonQE delta : ℝ) (round : ℕ)
    (hrequirement :
      quartileSourceAccuracyRoundBudgetRequirement initialCount epsilonQE delta round ≤
        totalBudget) :
    quartileSurvivorCountIter round initialCount *
        quartileSourceAccuracyPerArmRequirement epsilonQE delta round ≤
      quartileSourceRoundBudget totalBudget round := by
  have hweightPos : 0 < quartileSourceRoundBudgetWeight round :=
    quartileSourceRoundBudgetWeight_pos round
  have hceil :
      ((quartileSurvivorCountIter round initialCount : ℝ) *
          quartileSourceAccuracyPerArmRequirement epsilonQE delta round) /
        quartileSourceRoundBudgetWeight round ≤
      (quartileSourceAccuracyRoundBudgetRequirement initialCount epsilonQE delta round : ℝ) := by
    exact Nat.le_ceil _
  have hrequirementReal :
      (quartileSourceAccuracyRoundBudgetRequirement initialCount epsilonQE delta round : ℝ) ≤
        totalBudget := by
    exact_mod_cast hrequirement
  unfold quartileSourceRoundBudget
  apply Nat.le_floor
  rw [Nat.cast_mul]
  change
    (quartileSurvivorCountIter round initialCount : ℝ) *
        quartileSourceAccuracyPerArmRequirement epsilonQE delta round ≤
      quartileSourceRoundBudgetWeight round * (totalBudget : ℝ)
  have hscaled :
      (quartileSurvivorCountIter round initialCount : ℝ) *
          quartileSourceAccuracyPerArmRequirement epsilonQE delta round ≤
        (totalBudget : ℝ) * quartileSourceRoundBudgetWeight round :=
    (div_le_iff₀ hweightPos).mp (hceil.trans hrequirementReal)
  simpa [mul_comm] using hscaled

/-- The round allocation induced by an accuracy requirement has at least the
declared number of samples for every deterministic survivor. -/
theorem quartileSourceAccuracyPerArmRequirement_le_scheduledSampleCount
    (totalBudget initialCount : ℕ) (epsilonQE delta : ℝ) (round : ℕ)
    (hactive : 0 < quartileSurvivorCountIter round initialCount)
    (hrequirement :
      quartileSourceAccuracyRoundBudgetRequirement initialCount epsilonQE delta round ≤
        totalBudget) :
    quartileSourceAccuracyPerArmRequirement epsilonQE delta round ≤
      quartileSourceScheduledPerArmSampleCount totalBudget initialCount round := by
  unfold quartileSourceScheduledPerArmSampleCount
  apply (Nat.le_div_iff_mul_le hactive).mpr
  simpa [Nat.mul_comm] using
    (quartileSourceAccuracyRequiredPulls_le_roundBudget totalBudget initialCount
      epsilonQE delta round hrequirement)

/-- A finite maximum of the accuracy requirements covers every selected QE
round. -/
theorem quartileSourceAccuracyRoundBudgetRequirement_le_totalBudgetRequirement
    (initialCount roundCount : ℕ) (epsilonQE delta : ℝ) (round : ℕ)
    (hround : round < roundCount) :
    quartileSourceAccuracyRoundBudgetRequirement initialCount epsilonQE delta round ≤
      quartileSourceAccuracyTotalBudgetRequirement initialCount roundCount epsilonQE delta := by
  unfold quartileSourceAccuracyTotalBudgetRequirement
  exact Finset.le_sup (Finset.mem_range.mpr hround)

/-- Tie-broken QE preserves a positive deterministic cardinality. -/
theorem quartileSurvivorCountIter_pos :
    ∀ round initialCount, 0 < initialCount →
      0 < quartileSurvivorCountIter round initialCount := by
  intro round
  induction round with
  | zero =>
      intro initialCount hinitial
      simpa [quartileSurvivorCountIter] using hinitial
  | succ round ih =>
      intro initialCount hinitial
      rw [quartileSurvivorCountIter]
      apply ih
      unfold quartileSurvivorCount
      omega

/-- When all selected rounds meet their accuracy requirements, every source
radius is bounded by its declared geometric target. -/
theorem quartileSourceError_le_accuracyTarget_of_roundRequirements
    (totalBudget initialCount : ℕ) (epsilonQE delta : ℝ) (roundCount : ℕ)
    (hinitial : 0 < initialCount)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hepsilonQE : 0 < epsilonQE)
    (hrequirement : ∀ round, round < roundCount →
      quartileSourceAccuracyRoundBudgetRequirement initialCount epsilonQE delta round ≤
        totalBudget) :
    ∀ round, round < roundCount →
      quartileSourceError totalBudget initialCount delta round ≤
        quartileSourceAccuracyTarget epsilonQE round := by
  intro round hround
  apply quartileSourceError_le_accuracyTarget_of_perArmRequirement
    totalBudget initialCount epsilonQE delta round hdelta hdeltaLeOne hepsilonQE
  exact quartileSourceAccuracyPerArmRequirement_le_scheduledSampleCount
    totalBudget initialCount epsilonQE delta round
    (quartileSurvivorCountIter_pos round initialCount hinitial)
    (hrequirement round hround)

/-- The finite accuracy requirements imply the transparent accumulated QE
loss target. -/
theorem quartileSourceError_sum_two_le_epsilonQE_of_roundRequirements
    (totalBudget initialCount : ℕ) (epsilonQE delta : ℝ) (roundCount : ℕ)
    (hinitial : 0 < initialCount)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hepsilonQE : 0 < epsilonQE)
    (hrequirement : ∀ round, round < roundCount →
      quartileSourceAccuracyRoundBudgetRequirement initialCount epsilonQE delta round ≤
        totalBudget) :
    ∑ round ∈ Finset.range roundCount,
      2 * quartileSourceError totalBudget initialCount delta round ≤ epsilonQE := by
  calc
    (∑ round ∈ Finset.range roundCount,
        2 * quartileSourceError totalBudget initialCount delta round) ≤
        ∑ round ∈ Finset.range roundCount,
          2 * quartileSourceAccuracyTarget epsilonQE round := by
            apply Finset.sum_le_sum
            intro round hround
            nlinarith [quartileSourceError_le_accuracyTarget_of_roundRequirements
              totalBudget initialCount epsilonQE delta roundCount hinitial hdelta hdeltaLeOne
              hepsilonQE hrequirement round (Finset.mem_range.mp hround)]
    _ ≤ epsilonQE := quartileSourceAccuracyTarget_sum_two_le epsilonQE hepsilonQE.le roundCount

/-- The finite maximum accuracy budget bounds the accumulated source QE
radius with no remaining numerical radius premise. -/
theorem quartileSourceError_sum_two_le_epsilonQE_of_totalRequirement
    (initialCount roundCount : ℕ) (epsilonQE delta : ℝ)
    (hinitial : 0 < initialCount)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hepsilonQE : 0 < epsilonQE) :
    ∑ round ∈ Finset.range roundCount,
      2 * quartileSourceError
        (quartileSourceAccuracyTotalBudgetRequirement initialCount roundCount epsilonQE delta)
        initialCount delta round ≤ epsilonQE := by
  apply quartileSourceError_sum_two_le_epsilonQE_of_roundRequirements
    (quartileSourceAccuracyTotalBudgetRequirement initialCount roundCount epsilonQE delta)
    initialCount epsilonQE delta roundCount hinitial hdelta hdeltaLeOne hepsilonQE
  intro round hround
  exact quartileSourceAccuracyRoundBudgetRequirement_le_totalBudgetRequirement
    initialCount roundCount epsilonQE delta round hround

/-- The same finite accuracy requirement also implies the one-sample
nonterminal budget condition needed by the QE probability theorem. -/
theorem quartileSurvivorCountIter_le_sourceRoundBudget_of_accuracyRequirement
    (totalBudget initialCount : ℕ) (epsilonQE delta : ℝ) (round : ℕ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hepsilonQE : 0 < epsilonQE)
    (hrequirement :
      quartileSourceAccuracyRoundBudgetRequirement initialCount epsilonQE delta round ≤
        totalBudget) :
    quartileSurvivorCountIter round initialCount ≤
      quartileSourceRoundBudget totalBudget round := by
  calc
    quartileSurvivorCountIter round initialCount ≤
        quartileSurvivorCountIter round initialCount *
          quartileSourceAccuracyPerArmRequirement epsilonQE delta round :=
      Nat.le_mul_of_pos_right _
        (quartileSourceAccuracyPerArmRequirement_pos epsilonQE delta round
          hdelta hdeltaLeOne hepsilonQE)
    _ ≤ quartileSourceRoundBudget totalBudget round :=
      quartileSourceAccuracyRequiredPulls_le_roundBudget totalBudget initialCount
        epsilonQE delta round hrequirement

end ZhouChenLi2014OptimalPACMultipleArm
