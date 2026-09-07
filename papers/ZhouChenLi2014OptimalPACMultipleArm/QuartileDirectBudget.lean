import ZhouChenLi2014OptimalPACMultipleArm.QuartileAccuracyBudget

/-!
# Direct finite budget for the source QE rate calculation

This module records the exact ceiling requirements induced by the source
geometric error envelope.  Unlike the conservative per-round accuracy target,
the envelope includes the source decay before taking the round maximum; this
is the finite allocation boundary needed for Corollary 4.4's sharp rate.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL

/-- The least per-arm count sufficient for a source geometric envelope at one
QE round. -/
noncomputable def quartileSourceGeometricEnvelopePerArmRequirement
    (delta scale : ℝ) (round : ℕ) : ℕ :=
  ⌈(2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
    (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2)⌉₊

/-- The least total source allocation that supplies the direct-envelope
per-arm count to every deterministic survivor in one round, using the
documented floor convention for `Q_r`. -/
noncomputable def quartileSourceGeometricEnvelopeRoundBudgetRequirement
    (initialCount : ℕ) (delta scale : ℝ) (round : ℕ) : ℕ :=
  ⌈((quartileSurvivorCountIter round initialCount : ℝ) *
      quartileSourceGeometricEnvelopePerArmRequirement delta scale round) /
    quartileSourceRoundBudgetWeight round⌉₊

/-- The finite total-budget convention that simultaneously meets the direct
envelope requirement over a selected QE horizon. -/
noncomputable def quartileSourceGeometricEnvelopeTotalBudgetRequirement
    (initialCount roundCount : ℕ) (delta scale : ℝ) : ℕ :=
  (Finset.range roundCount).sup
    (quartileSourceGeometricEnvelopeRoundBudgetRequirement initialCount delta scale)

/-- The source rate only requires direct-envelope samples before the
deterministic three-arm terminal condition.  This finite maximum therefore
excludes rounds whose QE update is inert; the fixed-horizon policy may retain
those coordinates as padding, but they make no contribution to its source
sample budget. -/
noncomputable def quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement
    (initialCount roundCount : ℕ) (delta scale : ℝ) : ℕ :=
  (Finset.filter (fun round => 4 ≤ quartileSurvivorCountIter round initialCount)
    (Finset.range roundCount)).sup
    (quartileSourceGeometricEnvelopeRoundBudgetRequirement initialCount delta scale)

/-- Before terminal QE stopping, the rounded survivor recurrence is bounded
by four times the source's geometric survivor envelope.  The factor four
absorbs the exact three-arm fixed point without adding a late-round term. -/
theorem quartileSurvivorCountIter_real_le_four_mul_geometric_of_nonterminal
    (round initialCount : ℕ)
    (hnonterminal : 4 ≤ quartileSurvivorCountIter round initialCount) :
    (quartileSurvivorCountIter round initialCount : ℝ) ≤
      4 * ((3 : ℝ) / 4) ^ round * initialCount := by
  have hinitial : 3 ≤ initialCount := by
    by_contra hnot
    have hsmall : initialCount ≤ 3 := by omega
    have hfixed := quartileSurvivorCountIter_eq_of_le_three round initialCount hsmall
    rw [hfixed] at hnonterminal
    omega
  have hsurvivor :=
    quartileSurvivorCountIter_real_le_three_add_geometric round initialCount hinitial
  have hnonterminalReal : 4 ≤ (quartileSurvivorCountIter round initialCount : ℝ) := by
    exact_mod_cast hnonterminal
  have htail : 1 ≤ ((3 : ℝ) / 4) ^ round * ((initialCount : ℝ) - 3) := by
    linarith
  have hfourTail :
      (quartileSurvivorCountIter round initialCount : ℝ) ≤
        4 * (((3 : ℝ) / 4) ^ round * ((initialCount : ℝ) - 3)) := by
    nlinarith
  have hpowerNonneg : 0 ≤ ((3 : ℝ) / 4) ^ round := by positivity
  have hinitialLe : (initialCount : ℝ) - 3 ≤ initialCount := by linarith
  have htailLe : ((3 : ℝ) / 4) ^ round * ((initialCount : ℝ) - 3) ≤
      ((3 : ℝ) / 4) ^ round * initialCount :=
    mul_le_mul_of_nonneg_left hinitialLe hpowerNonneg
  calc
    (quartileSurvivorCountIter round initialCount : ℝ) ≤
        4 * (((3 : ℝ) / 4) ^ round * ((initialCount : ℝ) - 3)) := hfourTail
    _ ≤ 4 * (((3 : ℝ) / 4) ^ round * initialCount) :=
      mul_le_mul_of_nonneg_left htailLe (by norm_num)
    _ = 4 * ((3 : ℝ) / 4) ^ round * initialCount := by ring

/-- The three source schedules cancel exactly in every QE round. -/
theorem quartileSourceGeometricSchedule_cancellation (round : ℕ) :
    ((3 : ℝ) / 4) ^ round /
        (quartileSourceBudgetDecay ^ round * quartileSourceFailureDecay ^ (2 * round)) = 1 := by
  have hbase : quartileSourceBudgetDecay * quartileSourceFailureDecay ^ 2 = (3 / 4 : ℝ) := by
    rw [mul_comm]
    exact quartileSourceFailureDecay_sq_mul_budgetDecay
  have hpower : quartileSourceBudgetDecay ^ round *
      quartileSourceFailureDecay ^ (2 * round) = ((3 : ℝ) / 4) ^ round := by
    rw [pow_mul, ← mul_pow, hbase]
  rw [hpower]
  exact div_self (pow_ne_zero _ (by norm_num))

/-- The survivor-to-budget geometric ratio is the squared confidence decay. -/
theorem quartileSourceGeometricSurvivorBudgetRatio_eq_confidenceDecaySq
    (round : ℕ) :
    ((3 : ℝ) / 4) ^ round / quartileSourceBudgetDecay ^ round =
      quartileSourceFailureDecay ^ (2 * round) := by
  have hbase : quartileSourceBudgetDecay * quartileSourceFailureDecay ^ 2 = (3 / 4 : ℝ) := by
    rw [mul_comm]
    exact quartileSourceFailureDecay_sq_mul_budgetDecay
  have hpower : quartileSourceBudgetDecay ^ round *
      quartileSourceFailureDecay ^ (2 * round) = ((3 : ℝ) / 4) ^ round := by
    rw [pow_mul, ← mul_pow, hbase]
  apply (div_eq_iff (pow_ne_zero _ quartileSourceBudgetDecay_pos.ne')).mpr
  simpa [mul_comm] using hpower.symm

/-- The explicit finite rate factor obtained from the source's geometric
survivor, budget, and confidence schedules. -/
noncomputable def quartileSourceGeometricEnvelopeRateFactor (delta scale : ℝ) : ℝ :=
  8 * (21 / 10 + Real.log (2 / ((1 - quartileSourceFailureDecay) * delta))) /
      ((1 - quartileSourceBudgetDecay) * scale ^ 2) +
    4 / (1 - quartileSourceBudgetDecay) + 1

/-- A parameter-independent coefficient for the source-rate budget. -/
noncomputable def quartileSourceGeometricEnvelopeRateCoefficient : ℝ :=
  8 * (31 / 10 + Real.log (2 / (1 - quartileSourceFailureDecay))) /
      (1 - quartileSourceBudgetDecay) +
    4 / (1 - quartileSourceBudgetDecay) + 1

/-- A natural total budget at the source rate, with all ceiling effects made
explicit. -/
noncomputable def quartileSourceGeometricEnvelopeRateBudget
    (initialCount : ℕ) (delta scale : ℝ) : ℕ :=
  ⌈(initialCount : ℝ) * quartileSourceGeometricEnvelopeRateFactor delta scale⌉₊

/-- The explicit rate factor is bounded by the paper's one-log confidence
form whenever the requested accuracy is at most one. -/
theorem quartileSourceGeometricEnvelopeRateFactor_le_sourceRateForm
    (delta scale : ℝ) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hscale : 0 < scale) (hscaleLeOne : scale ≤ 1) :
    quartileSourceGeometricEnvelopeRateFactor delta scale ≤
      quartileSourceGeometricEnvelopeRateCoefficient *
        (1 + Real.log (1 / delta)) / scale ^ 2 := by
  let gap : ℝ := 1 - quartileSourceFailureDecay
  let budgetGap : ℝ := 1 - quartileSourceBudgetDecay
  let logFactor : ℝ := Real.log (1 / delta)
  let base : ℝ := 21 / 10 + Real.log (2 / gap)
  let tail : ℝ := 4 / budgetGap + 1
  have hgapPos : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr quartileSourceFailureDecay_lt_one
  have hbudgetGapPos : 0 < budgetGap := by
    dsimp [budgetGap]
    exact sub_pos.mpr quartileSourceBudgetDecay_lt_one
  have hlogNonneg : 0 ≤ logFactor := by
    dsimp [logFactor]
    apply Real.log_nonneg
    apply (le_div_iff₀ hdelta).mpr
    linarith
  have hgapLeOne : gap ≤ 1 := by
    dsimp [gap]
    linarith [quartileSourceFailureDecay_pos]
  have hratio : 1 ≤ 2 / gap := by
    apply (le_div_iff₀ hgapPos).mpr
    linarith
  have hbaseNonneg : 0 ≤ base := by
    dsimp [base]
    have hlog : 0 ≤ Real.log (2 / gap) := Real.log_nonneg hratio
    linarith
  have hbaseGrowth : base + logFactor ≤ (base + 1) * (1 + logFactor) := by
    nlinarith
  have hscaleSqPos : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hdenomPos : 0 < budgetGap * scale ^ 2 :=
    mul_pos hbudgetGapPos hscaleSqPos
  have hfirst :
      8 * (base + logFactor) / (budgetGap * scale ^ 2) ≤
        8 * (base + 1) * (1 + logFactor) / (budgetGap * scale ^ 2) := by
    apply div_le_div_of_nonneg_right _ hdenomPos.le
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hbaseGrowth (show (0 : ℝ) ≤ 8 by norm_num)
  have hscaleSqLeOne : scale ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ hscale.le (by norm_num)).mpr hscaleLeOne
  have hfactorGeOne : 1 ≤ (1 + logFactor) / scale ^ 2 := by
    apply (le_div_iff₀ hscaleSqPos).mpr
    linarith
  have htailNonneg : 0 ≤ tail := by
    dsimp [tail]
    exact add_nonneg (div_nonneg (by norm_num) hbudgetGapPos.le) (by norm_num)
  have hsecond : tail ≤ tail * ((1 + logFactor) / scale ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hfactorGeOne htailNonneg]
  unfold quartileSourceGeometricEnvelopeRateFactor
    quartileSourceGeometricEnvelopeRateCoefficient
  rw [quartileSourceLogFactor_split delta hdelta]
  have hleftRewrite :
      21 / 10 + (Real.log (2 / (1 - quartileSourceFailureDecay)) + Real.log (1 / delta)) =
        base + logFactor := by
    dsimp [base, logFactor, gap]
    ring
  have hrightRewrite :
      31 / 10 + Real.log (2 / (1 - quartileSourceFailureDecay)) = base + 1 := by
    dsimp [base, gap]
    ring
  rw [hleftRewrite, hrightRewrite]
  have hbound :
      8 * (base + logFactor) / (budgetGap * scale ^ 2) + tail ≤
        (8 * (base + 1) / budgetGap + tail) * (1 + logFactor) / scale ^ 2 := by
    calc
      8 * (base + logFactor) / (budgetGap * scale ^ 2) + tail ≤
          8 * (base + 1) * (1 + logFactor) / (budgetGap * scale ^ 2) +
            tail * ((1 + logFactor) / scale ^ 2) :=
        add_le_add hfirst hsecond
      _ = (8 * (base + 1) / budgetGap + tail) * (1 + logFactor) / scale ^ 2 := by
        ring_nf
  simpa [budgetGap, logFactor, tail, add_assoc] using hbound

/-- The natural source-rate budget, including its outer ceiling, is bounded
by an explicit multiple of `n / scale² * (1 + log (1 / delta))`. -/
theorem quartileSourceGeometricEnvelopeRateBudget_real_le_sourceRateForm
    (initialCount : ℕ) (delta scale : ℝ) (hinitial : 0 < initialCount)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hscale : 0 < scale) (hscaleLeOne : scale ≤ 1) :
    (quartileSourceGeometricEnvelopeRateBudget initialCount delta scale : ℝ) ≤
      2 * quartileSourceGeometricEnvelopeRateCoefficient * initialCount *
        (1 + Real.log (1 / delta)) / scale ^ 2 := by
  have hpopulationNonneg : (0 : ℝ) ≤ initialCount := Nat.cast_nonneg initialCount
  have hpopulationOne : (1 : ℝ) ≤ initialCount := by
    exact_mod_cast hinitial
  have hgapPos : 0 < 1 - quartileSourceFailureDecay :=
    sub_pos.mpr quartileSourceFailureDecay_lt_one
  have hbudgetGapPos : 0 < 1 - quartileSourceBudgetDecay :=
    sub_pos.mpr quartileSourceBudgetDecay_lt_one
  have hconfidenceDenomPos : 0 < (1 - quartileSourceFailureDecay) * delta :=
    mul_pos hgapPos hdelta
  have hconfidenceDenomLeOne : (1 - quartileSourceFailureDecay) * delta ≤ 1 := by
    have hgapLeOne : 1 - quartileSourceFailureDecay ≤ 1 := by
      linarith [quartileSourceFailureDecay_pos]
    calc
      (1 - quartileSourceFailureDecay) * delta ≤
          (1 - quartileSourceFailureDecay) * 1 :=
        mul_le_mul_of_nonneg_left hdeltaLeOne hgapPos.le
      _ = 1 - quartileSourceFailureDecay := by ring
      _ ≤ 1 := hgapLeOne
  have hconfidenceLogNonneg : 0 ≤
      Real.log (2 / ((1 - quartileSourceFailureDecay) * delta)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hconfidenceDenomPos).mpr
    linarith
  have hrateFactorNonneg : 0 ≤ quartileSourceGeometricEnvelopeRateFactor delta scale := by
    unfold quartileSourceGeometricEnvelopeRateFactor
    apply add_nonneg
    · apply add_nonneg
      · exact div_nonneg
          (mul_nonneg (show (0 : ℝ) ≤ 8 by norm_num) (by linarith))
          (mul_nonneg hbudgetGapPos.le (sq_nonneg scale))
      · exact div_nonneg (show (0 : ℝ) ≤ 4 by norm_num) hbudgetGapPos.le
    · norm_num
  have hfactorBound := quartileSourceGeometricEnvelopeRateFactor_le_sourceRateForm
    delta scale hdelta hdeltaLeOne hscale hscaleLeOne
  have hlogNonneg : 0 ≤ Real.log (1 / delta) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hdelta).mpr
    linarith
  have hscaleSqPos : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hsourceFactorGeOne : 1 ≤
      (1 + Real.log (1 / delta)) / scale ^ 2 := by
    apply (le_div_iff₀ hscaleSqPos).mpr
    have hscaleSqLeOne : scale ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ hscale.le (by norm_num)).mpr hscaleLeOne
    linarith
  have hcoefficientGeOne : 1 ≤ quartileSourceGeometricEnvelopeRateCoefficient := by
    unfold quartileSourceGeometricEnvelopeRateCoefficient
    have hbaseNonneg : 0 ≤ 31 / 10 +
        Real.log (2 / (1 - quartileSourceFailureDecay)) := by
      have hratio : 1 ≤ 2 / (1 - quartileSourceFailureDecay) := by
        apply (le_div_iff₀ hgapPos).mpr
        linarith [quartileSourceFailureDecay_pos]
      have hlog : 0 ≤ Real.log (2 / (1 - quartileSourceFailureDecay)) :=
        Real.log_nonneg hratio
      linarith
    have hfirstNonneg : 0 ≤
        8 * (31 / 10 + Real.log (2 / (1 - quartileSourceFailureDecay))) /
          (1 - quartileSourceBudgetDecay) :=
      div_nonneg (mul_nonneg (by norm_num) hbaseNonneg) hbudgetGapPos.le
    have htailGeOne : 1 ≤ 4 / (1 - quartileSourceBudgetDecay) + 1 := by
      have : 0 ≤ 4 / (1 - quartileSourceBudgetDecay) :=
        div_nonneg (by norm_num) hbudgetGapPos.le
      linarith
    linarith
  have hrateFormGeOne : 1 ≤ quartileSourceGeometricEnvelopeRateCoefficient *
      (1 + Real.log (1 / delta)) / scale ^ 2 := by
    have hproduct : 0 ≤ (quartileSourceGeometricEnvelopeRateCoefficient - 1) *
        ((1 + Real.log (1 / delta)) / scale ^ 2 - 1) :=
      mul_nonneg (sub_nonneg.mpr hcoefficientGeOne) (sub_nonneg.mpr hsourceFactorGeOne)
    rw [show quartileSourceGeometricEnvelopeRateCoefficient *
        (1 + Real.log (1 / delta)) / scale ^ 2 =
        quartileSourceGeometricEnvelopeRateCoefficient *
          ((1 + Real.log (1 / delta)) / scale ^ 2) by ring]
    nlinarith
  have hscaledBound : (initialCount : ℝ) *
      quartileSourceGeometricEnvelopeRateFactor delta scale ≤
        initialCount * (quartileSourceGeometricEnvelopeRateCoefficient *
          (1 + Real.log (1 / delta)) / scale ^ 2) :=
    mul_le_mul_of_nonneg_left hfactorBound hpopulationNonneg
  have hwholeGeOne : 1 ≤ (initialCount : ℝ) *
      (quartileSourceGeometricEnvelopeRateCoefficient *
        (1 + Real.log (1 / delta)) / scale ^ 2) := by
    have hproduct : 0 ≤ ((initialCount : ℝ) - 1) *
        (quartileSourceGeometricEnvelopeRateCoefficient *
          (1 + Real.log (1 / delta)) / scale ^ 2 - 1) :=
      mul_nonneg (sub_nonneg.mpr hpopulationOne) (sub_nonneg.mpr hrateFormGeOne)
    nlinarith
  have hceil : (quartileSourceGeometricEnvelopeRateBudget initialCount delta scale : ℝ) ≤
      initialCount * quartileSourceGeometricEnvelopeRateFactor delta scale + 1 := by
    unfold quartileSourceGeometricEnvelopeRateBudget
    exact (Nat.ceil_lt_add_one (mul_nonneg hpopulationNonneg hrateFactorNonneg)).le
  calc
    (quartileSourceGeometricEnvelopeRateBudget initialCount delta scale : ℝ) ≤
        initialCount * quartileSourceGeometricEnvelopeRateFactor delta scale + 1 := hceil
    _ ≤ initialCount * (quartileSourceGeometricEnvelopeRateCoefficient *
          (1 + Real.log (1 / delta)) / scale ^ 2) + 1 :=
      by linarith
    _ ≤ 2 * (initialCount * (quartileSourceGeometricEnvelopeRateCoefficient *
          (1 + Real.log (1 / delta)) / scale ^ 2)) := by
      linarith
    _ = 2 * quartileSourceGeometricEnvelopeRateCoefficient * initialCount *
        (1 + Real.log (1 / delta)) / scale ^ 2 := by ring

/-- At the paper's half-accuracy split, the explicit natural QE budget has
the source `n / epsilon²` confidence-rate form in the nontrivial
`0 < epsilon ≤ 1` regime. -/
theorem quartileSourceGeometricEnvelopeSourceRateBudget_real_le
    (initialCount : ℕ) (epsilon delta : ℝ) (hinitial : 0 < initialCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (quartileSourceGeometricEnvelopeRateBudget initialCount (delta / 2)
      (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2) : ℝ) ≤
      2 * quartileSourceGeometricEnvelopeRateCoefficient * initialCount *
        (1 + Real.log (1 / (delta / 2))) /
        (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2) ^ 2 := by
  have hgapPos : 0 < 1 - quartileSourceFailureDecay :=
    sub_pos.mpr quartileSourceFailureDecay_lt_one
  have hgapLeOne : 1 - quartileSourceFailureDecay ≤ 1 := by
    linarith [quartileSourceFailureDecay_pos]
  have hscale : 0 < epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2 := by
    positivity
  have hgapSqLeOne : (1 - quartileSourceFailureDecay) ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ hgapPos.le (by norm_num)).mpr hgapLeOne
  have hscaleLeOne : epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2 ≤ 1 := by
    apply mul_le_one₀
    · linarith
    · positivity
    · exact hgapSqLeOne
  exact quartileSourceGeometricEnvelopeRateBudget_real_le_sourceRateForm
    initialCount (delta / 2) (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2)
    hinitial (by linarith) (by linarith) hscale hscaleLeOne

/-- Multiplying the direct geometric threshold by the live-survivor envelope
and dividing by the source round weight cancels every round-dependent
geometric factor. -/
theorem quartileSourceWeightedGeometricThreshold_eq
    (round : ℕ) (population numerator scale : ℝ) (hscale : 0 < scale) :
    (4 * ((3 : ℝ) / 4) ^ round * population *
        (2 * numerator /
          (scale ^ 2 * ((round + 1 : ℕ) : ℝ) ^ 2 *
            quartileSourceFailureDecay ^ (2 * round)))) /
        ((1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round) =
      8 * population * (numerator / ((round + 1 : ℕ) : ℝ) ^ 2) /
        ((1 - quartileSourceBudgetDecay) * scale ^ 2) := by
  have hgeom : quartileSourceBudgetDecay ^ round *
      quartileSourceFailureDecay ^ (2 * round) = ((3 : ℝ) / 4) ^ round := by
    have hbase : quartileSourceBudgetDecay * quartileSourceFailureDecay ^ 2 = (3 / 4 : ℝ) := by
      rw [mul_comm]
      exact quartileSourceFailureDecay_sq_mul_budgetDecay
    rw [pow_mul, ← mul_pow, hbase]
  rw [← hgeom]
  field_simp [hscale.ne', quartileSourceFailureDecay_pos.ne',
    quartileSourceBudgetDecay_pos.ne', (sub_pos.mpr quartileSourceBudgetDecay_lt_one).ne']
  ring

/-- The ceiling-one part of a live-survivor direct allocation is bounded
uniformly in the QE round. -/
theorem quartileSourceWeightedGeometricSurvivor_le
    (round : ℕ) (population : ℝ) (hpopulation : 0 ≤ population) :
    (4 * ((3 : ℝ) / 4) ^ round * population) /
        ((1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round) ≤
      4 * population / (1 - quartileSourceBudgetDecay) := by
  have hratio := quartileSourceGeometricSurvivorBudgetRatio_eq_confidenceDecaySq round
  have hdecayPowLeOne : quartileSourceFailureDecay ^ (2 * round) ≤ 1 :=
    pow_le_one₀ quartileSourceFailureDecay_pos.le quartileSourceFailureDecay_lt_one.le
  have hdenomPos : 0 < 1 - quartileSourceBudgetDecay :=
    sub_pos.mpr quartileSourceBudgetDecay_lt_one
  calc
    (4 * ((3 : ℝ) / 4) ^ round * population) /
        ((1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round) =
        (4 * population / (1 - quartileSourceBudgetDecay)) *
          (((3 : ℝ) / 4) ^ round / quartileSourceBudgetDecay ^ round) := by
      field_simp [hdenomPos.ne', quartileSourceBudgetDecay_pos.ne']
    _ = (4 * population / (1 - quartileSourceBudgetDecay)) *
          quartileSourceFailureDecay ^ (2 * round) := by rw [hratio]
    _ ≤ (4 * population / (1 - quartileSourceBudgetDecay)) * 1 := by
      gcongr
    _ = 4 * population / (1 - quartileSourceBudgetDecay) := by ring

/-- The direct one-round threshold has an explicit form in which the source
confidence decay appears only as a squared geometric factor. -/
theorem quartileSourceGeometricEnvelopeThreshold_eq
    (delta scale : ℝ) (round : ℕ) (hscale : 0 < scale) :
    (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) =
      2 * (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        (scale ^ 2 * ((round + 1 : ℕ) : ℝ) ^ 2 *
          quartileSourceFailureDecay ^ (2 * round)) := by
  unfold quartileSourceGeometricTailEnvelope
  rw [pow_mul]
  field_simp [hscale.ne', quartileSourceFailureDecay_pos.ne']
  ring

/-- A direct-envelope per-arm ceiling is at most its real threshold plus one. -/
theorem quartileSourceGeometricEnvelopePerArmRequirement_real_le_threshold_add_one
    (delta scale : ℝ) (round : ℕ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hscale : 0 < scale) :
    (quartileSourceGeometricEnvelopePerArmRequirement delta scale round : ℝ) ≤
      (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
          (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) + 1 := by
  let confidence := quartileSourceFailureBudget delta round
  let envelope := quartileSourceGeometricTailEnvelope scale round
  have hconfidencePos : 0 < confidence := quartileSourceFailureBudget_pos hdelta round
  have hconfidenceLeOne : confidence ≤ 1 :=
    (quartileSourceFailureBudget_le_total hdelta.le round).trans hdeltaLeOne
  have hratio : 1 ≤ 2 / confidence := by
    apply (le_div_iff₀ hconfidencePos).mpr
    linarith
  have hnumerator : 0 ≤ 2 + Real.log (2 / confidence) := by
    have hlog : 0 ≤ Real.log (2 / confidence) := Real.log_nonneg hratio
    linarith
  have henvelope : 0 < envelope := by
    dsimp [envelope]
    exact quartileSourceGeometricTailEnvelope_pos hscale round
  have hthresholdNonneg : 0 ≤
      (2 + Real.log (2 / confidence)) / (2 * (envelope / 2) ^ 2) := by
    exact div_nonneg hnumerator (by positivity)
  exact (Nat.ceil_lt_add_one hthresholdNonneg).le

/-- Every live QE round's exact ceiling requirement is covered by the explicit
source-rate budget.  The proof keeps the survivor, allocation, confidence,
and ceiling contributions separate so that no hidden asymptotic constant is
used. -/
theorem quartileSourceGeometricEnvelopeRoundBudgetRequirement_le_rateBudget
    (initialCount : ℕ) (delta scale : ℝ) (round : ℕ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hscale : 0 < scale)
    (hnonterminal : 4 ≤ quartileSurvivorCountIter round initialCount) :
    quartileSourceGeometricEnvelopeRoundBudgetRequirement initialCount delta scale round ≤
      quartileSourceGeometricEnvelopeRateBudget initialCount delta scale := by
  have hinitialPos : 0 < initialCount := by
    by_contra hnot
    have hsmall : initialCount ≤ 3 := by omega
    have hfixed := quartileSurvivorCountIter_eq_of_le_three round initialCount hsmall
    rw [hfixed] at hnonterminal
    omega
  have hinitialOne : (1 : ℝ) ≤ initialCount := by
    exact_mod_cast hinitialPos
  have hpopulationNonneg : (0 : ℝ) ≤ initialCount := Nat.cast_nonneg initialCount
  have hweightPos : 0 <
      (1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round := by
    exact mul_pos (sub_pos.mpr quartileSourceBudgetDecay_lt_one)
      (pow_pos quartileSourceBudgetDecay_pos _)
  have hsurvivor :=
    quartileSurvivorCountIter_real_le_four_mul_geometric_of_nonterminal round initialCount
      hnonterminal
  have hperArm :=
    quartileSourceGeometricEnvelopePerArmRequirement_real_le_threshold_add_one
      delta scale round hdelta hdeltaLeOne hscale
  have hmul :
      (quartileSurvivorCountIter round initialCount : ℝ) *
          quartileSourceGeometricEnvelopePerArmRequirement delta scale round ≤
        (4 * ((3 : ℝ) / 4) ^ round * initialCount) *
          ((2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
            (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) + 1) := by
    gcongr
  have hbody :
      ((quartileSurvivorCountIter round initialCount : ℝ) *
          quartileSourceGeometricEnvelopePerArmRequirement delta scale round) /
          ((1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round) ≤
        (initialCount : ℝ) * quartileSourceGeometricEnvelopeRateFactor delta scale := by
    calc
      ((quartileSurvivorCountIter round initialCount : ℝ) *
          quartileSourceGeometricEnvelopePerArmRequirement delta scale round) /
          ((1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round) ≤
          ((4 * ((3 : ℝ) / 4) ^ round * initialCount) *
            ((2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
              (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) + 1)) /
            ((1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round) :=
        div_le_div_of_nonneg_right hmul hweightPos.le
      _ =
          ((4 * ((3 : ℝ) / 4) ^ round * initialCount) *
            ((2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
              (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2))) /
              ((1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round) +
            (4 * ((3 : ℝ) / 4) ^ round * initialCount) /
              ((1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round) := by ring
      _ =
          8 * initialCount *
            ((2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
              ((round + 1 : ℕ) : ℝ) ^ 2) /
              ((1 - quartileSourceBudgetDecay) * scale ^ 2) +
            (4 * ((3 : ℝ) / 4) ^ round * initialCount) /
              ((1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round) := by
        rw [quartileSourceGeometricEnvelopeThreshold_eq delta scale round hscale]
        rw [quartileSourceWeightedGeometricThreshold_eq round initialCount
          (2 + Real.log (2 / quartileSourceFailureBudget delta round)) scale hscale]
      _ ≤
          8 * initialCount *
            (21 / 10 + Real.log (2 / ((1 - quartileSourceFailureDecay) * delta))) /
              ((1 - quartileSourceBudgetDecay) * scale ^ 2) +
            4 * initialCount / (1 - quartileSourceBudgetDecay) := by
        apply add_le_add
        · have hconfidence := quartileSourceConfidenceNumerator_div_sq_le
            delta hdelta hdeltaLeOne round
          have hcoefficientNonneg : 0 ≤
              8 * initialCount / ((1 - quartileSourceBudgetDecay) * scale ^ 2) := by
            exact div_nonneg (mul_nonneg (by norm_num) hpopulationNonneg)
              (mul_nonneg (sub_nonneg.mpr quartileSourceBudgetDecay_lt_one.le)
                (sq_nonneg scale))
          calc
            8 * initialCount *
                ((2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
                  ((round + 1 : ℕ) : ℝ) ^ 2) /
                  ((1 - quartileSourceBudgetDecay) * scale ^ 2) =
                (8 * initialCount / ((1 - quartileSourceBudgetDecay) * scale ^ 2)) *
                  ((2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
                    ((round + 1 : ℕ) : ℝ) ^ 2) := by ring
            _ ≤ (8 * initialCount / ((1 - quartileSourceBudgetDecay) * scale ^ 2)) *
                (21 / 10 + Real.log (2 / ((1 - quartileSourceFailureDecay) * delta))) :=
              mul_le_mul_of_nonneg_left hconfidence hcoefficientNonneg
            _ = 8 * initialCount *
                (21 / 10 + Real.log (2 / ((1 - quartileSourceFailureDecay) * delta))) /
                  ((1 - quartileSourceBudgetDecay) * scale ^ 2) := by ring
        · exact quartileSourceWeightedGeometricSurvivor_le round initialCount
            hpopulationNonneg
      _ ≤ (initialCount : ℝ) * quartileSourceGeometricEnvelopeRateFactor delta scale := by
        calc
          8 * initialCount *
              (21 / 10 + Real.log (2 / ((1 - quartileSourceFailureDecay) * delta))) /
                ((1 - quartileSourceBudgetDecay) * scale ^ 2) +
              4 * initialCount / (1 - quartileSourceBudgetDecay) ≤
              8 * initialCount *
                (21 / 10 + Real.log (2 / ((1 - quartileSourceFailureDecay) * delta))) /
                  ((1 - quartileSourceBudgetDecay) * scale ^ 2) +
                4 * initialCount / (1 - quartileSourceBudgetDecay) + initialCount := by
              linarith
          _ = (initialCount : ℝ) * quartileSourceGeometricEnvelopeRateFactor delta scale := by
            unfold quartileSourceGeometricEnvelopeRateFactor
            ring
  unfold quartileSourceGeometricEnvelopeRoundBudgetRequirement
    quartileSourceGeometricEnvelopeRateBudget
  exact Nat.ceil_le_ceil hbody

/-- A round total meeting its ceiling requirement allocates every required
direct-envelope sample before the source round's inert padding. -/
theorem quartileSourceGeometricEnvelopeRequiredPulls_le_roundBudget
    (totalBudget initialCount : ℕ) (delta scale : ℝ) (round : ℕ)
    (hrequirement :
      quartileSourceGeometricEnvelopeRoundBudgetRequirement initialCount delta scale round ≤
        totalBudget) :
    quartileSurvivorCountIter round initialCount *
        quartileSourceGeometricEnvelopePerArmRequirement delta scale round ≤
      quartileSourceRoundBudget totalBudget round := by
  have hweightPos : 0 < quartileSourceRoundBudgetWeight round :=
    quartileSourceRoundBudgetWeight_pos round
  have hceil :
      ((quartileSurvivorCountIter round initialCount : ℝ) *
          quartileSourceGeometricEnvelopePerArmRequirement delta scale round) /
        quartileSourceRoundBudgetWeight round ≤
        (quartileSourceGeometricEnvelopeRoundBudgetRequirement initialCount delta scale round : ℝ) :=
    Nat.le_ceil _
  have hrequirementReal :
      (quartileSourceGeometricEnvelopeRoundBudgetRequirement initialCount delta scale round : ℝ) ≤
        totalBudget := by
    exact_mod_cast hrequirement
  unfold quartileSourceRoundBudget
  apply Nat.le_floor
  rw [Nat.cast_mul]
  change
    (quartileSurvivorCountIter round initialCount : ℝ) *
        quartileSourceGeometricEnvelopePerArmRequirement delta scale round ≤
      quartileSourceRoundBudgetWeight round * (totalBudget : ℝ)
  have hscaled :
      (quartileSurvivorCountIter round initialCount : ℝ) *
          quartileSourceGeometricEnvelopePerArmRequirement delta scale round ≤
        (totalBudget : ℝ) * quartileSourceRoundBudgetWeight round :=
    (div_le_iff₀ hweightPos).mp (hceil.trans hrequirementReal)
  simpa [mul_comm] using hscaled

/-- The source round quotient contains the direct-envelope per-arm count when
its round requirement is met. -/
theorem quartileSourceGeometricEnvelopePerArmRequirement_le_scheduledSampleCount
    (totalBudget initialCount : ℕ) (delta scale : ℝ) (round : ℕ)
    (hinitial : 0 < initialCount)
    (hrequirement :
      quartileSourceGeometricEnvelopeRoundBudgetRequirement initialCount delta scale round ≤
        totalBudget) :
    quartileSourceGeometricEnvelopePerArmRequirement delta scale round ≤
      quartileSourceScheduledPerArmSampleCount totalBudget initialCount round := by
  unfold quartileSourceScheduledPerArmSampleCount
  apply (Nat.le_div_iff_mul_le
    (quartileSurvivorCountIter_pos round initialCount hinitial)).mpr
  simpa [Nat.mul_comm] using
    (quartileSourceGeometricEnvelopeRequiredPulls_le_roundBudget
      totalBudget initialCount delta scale round hrequirement)

/-- A direct-envelope natural ceiling dominates its underlying real threshold. -/
theorem quartileSourceGeometricEnvelopePerArmRequirement_real_le
    (delta scale : ℝ) (round : ℕ) :
    (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) ≤
      (quartileSourceGeometricEnvelopePerArmRequirement delta scale round : ℝ) :=
  Nat.le_ceil _

/-- The total direct-envelope maximum meets every selected round requirement. -/
theorem quartileSourceGeometricEnvelopeRoundBudgetRequirement_le_totalBudgetRequirement
    (initialCount roundCount : ℕ) (delta scale : ℝ) (round : ℕ)
    (hround : round < roundCount) :
    quartileSourceGeometricEnvelopeRoundBudgetRequirement initialCount delta scale round ≤
      quartileSourceGeometricEnvelopeTotalBudgetRequirement initialCount roundCount delta scale := by
  unfold quartileSourceGeometricEnvelopeTotalBudgetRequirement
  exact Finset.le_sup (Finset.mem_range.mpr hround)

/-- Every live QE round is covered by the terminal-aware direct-envelope
total. -/
theorem quartileSourceGeometricEnvelopeRoundBudgetRequirement_le_nonterminalTotalBudgetRequirement
    (initialCount roundCount : ℕ) (delta scale : ℝ) (round : ℕ)
    (hround : round < roundCount)
    (hnonterminal : 4 ≤ quartileSurvivorCountIter round initialCount) :
    quartileSourceGeometricEnvelopeRoundBudgetRequirement initialCount delta scale round ≤
      quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement
        initialCount roundCount delta scale := by
  unfold quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hround, hnonterminal⟩)

/-- The direct-envelope total budget proves the real one-round sample lower
bound required by the geometric error summation. -/
theorem quartileSourceGeometricEnvelope_sampleThreshold_le_scheduledSampleCount
    (initialCount roundCount : ℕ) (delta scale : ℝ) (round : ℕ)
    (hinitial : 0 < initialCount) (hround : round < roundCount) :
    (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) ≤
      (quartileSourceScheduledPerArmSampleCount
        (quartileSourceGeometricEnvelopeTotalBudgetRequirement initialCount roundCount delta scale)
        initialCount round : ℝ) := by
  calc
    (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) ≤
        (quartileSourceGeometricEnvelopePerArmRequirement delta scale round : ℝ) :=
      quartileSourceGeometricEnvelopePerArmRequirement_real_le delta scale round
    _ ≤ (quartileSourceScheduledPerArmSampleCount
        (quartileSourceGeometricEnvelopeTotalBudgetRequirement initialCount roundCount delta scale)
        initialCount round : ℝ) := by
      exact_mod_cast
        quartileSourceGeometricEnvelopePerArmRequirement_le_scheduledSampleCount
          (quartileSourceGeometricEnvelopeTotalBudgetRequirement initialCount roundCount delta scale)
          initialCount delta scale round hinitial
          (quartileSourceGeometricEnvelopeRoundBudgetRequirement_le_totalBudgetRequirement
            initialCount roundCount delta scale round hround)

/-- The terminal-aware total gives the geometric-envelope sample threshold at
every and only every live QE round. -/
theorem quartileSourceGeometricEnvelope_sampleThreshold_le_scheduledSampleCount_of_nonterminalTotalBudget
    (initialCount roundCount : ℕ) (delta scale : ℝ) (round : ℕ)
    (hinitial : 0 < initialCount) (hround : round < roundCount)
    (hnonterminal : 4 ≤ quartileSurvivorCountIter round initialCount) :
    (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) ≤
      (quartileSourceScheduledPerArmSampleCount
        (quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement
          initialCount roundCount delta scale)
        initialCount round : ℝ) := by
  calc
    (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) ≤
        (quartileSourceGeometricEnvelopePerArmRequirement delta scale round : ℝ) :=
      quartileSourceGeometricEnvelopePerArmRequirement_real_le delta scale round
    _ ≤ (quartileSourceScheduledPerArmSampleCount
        (quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement
          initialCount roundCount delta scale)
        initialCount round : ℝ) := by
      exact_mod_cast
        quartileSourceGeometricEnvelopePerArmRequirement_le_scheduledSampleCount
          (quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement
            initialCount roundCount delta scale)
          initialCount delta scale round hinitial
          (quartileSourceGeometricEnvelopeRoundBudgetRequirement_le_nonterminalTotalBudgetRequirement
            initialCount roundCount delta scale round hround hnonterminal)

/-- A scheduled count is positive whenever it meets the positive direct
geometric-envelope threshold. -/
theorem quartileSourceGeometricEnvelope_scheduledSampleCount_pos_of_threshold
    (totalBudget initialCount : ℕ) (delta scale : ℝ) (round : ℕ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hscale : 0 < scale)
    (hthreshold :
      (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
          (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) ≤
        (quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ)) :
    0 < quartileSourceScheduledPerArmSampleCount totalBudget initialCount round := by
  let confidence := quartileSourceFailureBudget delta round
  let envelope := quartileSourceGeometricTailEnvelope scale round
  let threshold : ℝ :=
    (2 + Real.log (2 / confidence)) / (2 * (envelope / 2) ^ 2)
  have hconfidencePos : 0 < confidence := quartileSourceFailureBudget_pos hdelta round
  have hconfidenceLeOne : confidence ≤ 1 :=
    (quartileSourceFailureBudget_le_total hdelta.le round).trans hdeltaLeOne
  have hratio : 1 ≤ 2 / confidence := by
    apply (le_div_iff₀ hconfidencePos).mpr
    linarith
  have hnumerator : 0 < 2 + Real.log (2 / confidence) := by
    have hlog : 0 ≤ Real.log (2 / confidence) := Real.log_nonneg hratio
    linarith
  have henvelope : 0 < envelope := by
    dsimp [envelope]
    exact quartileSourceGeometricTailEnvelope_pos hscale round
  have hthresholdPos : 0 < threshold := by
    dsimp [threshold]
    exact div_pos hnumerator (by positivity)
  have hbound : threshold ≤
      (quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ) := by
    simpa [threshold, confidence, envelope] using hthreshold
  have hreal : 0 <
      (quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ) :=
    hthresholdPos.trans_le hbound
  exact_mod_cast hreal

/-- Every nonterminal direct-envelope batch contains at least one sample per
surviving arm under the fully specified total budget. -/
theorem quartileSourceGeometricEnvelope_scheduledSampleCount_pos
    (initialCount roundCount : ℕ) (delta scale : ℝ) (round : ℕ)
    (hinitial : 0 < initialCount) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hscale : 0 < scale) (hround : round < roundCount) :
    0 < quartileSourceScheduledPerArmSampleCount
      (quartileSourceGeometricEnvelopeTotalBudgetRequirement initialCount roundCount delta scale)
      initialCount round := by
  let confidence := quartileSourceFailureBudget delta round
  let envelope := quartileSourceGeometricTailEnvelope scale round
  let threshold : ℝ :=
    (2 + Real.log (2 / confidence)) / (2 * (envelope / 2) ^ 2)
  have hconfidencePos : 0 < confidence := quartileSourceFailureBudget_pos hdelta round
  have hconfidenceLeOne : confidence ≤ 1 :=
    (quartileSourceFailureBudget_le_total hdelta.le round).trans hdeltaLeOne
  have hratio : 1 ≤ 2 / confidence := by
    apply (le_div_iff₀ hconfidencePos).mpr
    linarith
  have hnumerator : 0 < 2 + Real.log (2 / confidence) := by
    have hlog : 0 ≤ Real.log (2 / confidence) := Real.log_nonneg hratio
    linarith
  have henvelope : 0 < envelope := by
    dsimp [envelope]
    exact quartileSourceGeometricTailEnvelope_pos hscale round
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    exact div_pos hnumerator (by positivity)
  have hbound : threshold ≤
      (quartileSourceScheduledPerArmSampleCount
        (quartileSourceGeometricEnvelopeTotalBudgetRequirement initialCount roundCount delta scale)
        initialCount round : ℝ) := by
    simpa [threshold, confidence, envelope] using
      (quartileSourceGeometricEnvelope_sampleThreshold_le_scheduledSampleCount
        initialCount roundCount delta scale round hinitial hround)
  have hreal : 0 <
      (quartileSourceScheduledPerArmSampleCount
        (quartileSourceGeometricEnvelopeTotalBudgetRequirement initialCount roundCount delta scale)
        initialCount round : ℝ) :=
    hthreshold.trans_le hbound
  exact_mod_cast hreal

/-- The direct-envelope total budget has a fully closed terminal-aware QE
loss bound.  It is the finite source-budget theorem from which the remaining
sharp-rate task is to bound this explicit ceiling maximum by the paper's
`n / epsilon² (1 + log (1 / delta))` scale. -/
theorem quartileSourceTerminalError_sum_le_closed_of_geometricTotalBudget
    (initialCount roundCount : ℕ) (delta scale : ℝ)
    (hinitial : 0 < initialCount) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hscale : 0 < scale) :
    (∑ round ∈ Finset.range roundCount,
      2 * quartileSourceTerminalError
        (quartileSourceGeometricEnvelopeTotalBudgetRequirement
          initialCount roundCount delta scale)
        initialCount delta round) ≤
      scale / (1 - quartileSourceFailureDecay) ^ 2 := by
  apply quartileSourceTerminalError_sum_le_closed_of_scheduledSampleCount
    (quartileSourceGeometricEnvelopeTotalBudgetRequirement
      initialCount roundCount delta scale)
    initialCount delta scale roundCount hdelta hdeltaLeOne hscale
  intro round hround _
  exact quartileSourceGeometricEnvelope_sampleThreshold_le_scheduledSampleCount
    initialCount roundCount delta scale round hinitial hround

/-- The terminal-aware direct-envelope maximum gives the same closed QE-loss
bound while assigning no accuracy budget to source rounds after stopping. -/
theorem quartileSourceTerminalError_sum_le_closed_of_geometricNonterminalTotalBudget
    (initialCount roundCount : ℕ) (delta scale : ℝ)
    (hinitial : 0 < initialCount) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hscale : 0 < scale) :
    (∑ round ∈ Finset.range roundCount,
      2 * quartileSourceTerminalError
        (quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement
          initialCount roundCount delta scale)
        initialCount delta round) ≤
      scale / (1 - quartileSourceFailureDecay) ^ 2 := by
  apply quartileSourceTerminalError_sum_le_closed_of_scheduledSampleCount
    (quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement
      initialCount roundCount delta scale)
    initialCount delta scale roundCount hdelta hdeltaLeOne hscale
  intro round hround hnonterminal
  exact quartileSourceGeometricEnvelope_sampleThreshold_le_scheduledSampleCount_of_nonterminalTotalBudget
    initialCount roundCount delta scale round hinitial hround hnonterminal

/-- The explicit source-rate budget supplies the direct threshold at every
live QE round. -/
theorem quartileSourceGeometricEnvelope_sampleThreshold_le_scheduledSampleCount_of_rateBudget
    (initialCount : ℕ) (delta scale : ℝ) (round : ℕ)
    (hinitial : 0 < initialCount) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hscale : 0 < scale)
    (hnonterminal : 4 ≤ quartileSurvivorCountIter round initialCount) :
    (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) ≤
      (quartileSourceScheduledPerArmSampleCount
        (quartileSourceGeometricEnvelopeRateBudget initialCount delta scale)
        initialCount round : ℝ) := by
  calc
    (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) ≤
        (quartileSourceGeometricEnvelopePerArmRequirement delta scale round : ℝ) :=
      quartileSourceGeometricEnvelopePerArmRequirement_real_le delta scale round
    _ ≤ (quartileSourceScheduledPerArmSampleCount
        (quartileSourceGeometricEnvelopeRateBudget initialCount delta scale)
        initialCount round : ℝ) := by
      exact_mod_cast
        quartileSourceGeometricEnvelopePerArmRequirement_le_scheduledSampleCount
          (quartileSourceGeometricEnvelopeRateBudget initialCount delta scale)
          initialCount delta scale round hinitial
          (quartileSourceGeometricEnvelopeRoundBudgetRequirement_le_rateBudget
            initialCount delta scale round hdelta hdeltaLeOne hscale hnonterminal)

/-- The rate budget has the same closed terminal-aware QE-loss guarantee as
the exact live-round maximum. -/
theorem quartileSourceTerminalError_sum_le_closed_of_geometricRateBudget
    (initialCount roundCount : ℕ) (delta scale : ℝ)
    (hinitial : 0 < initialCount) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hscale : 0 < scale) :
    (∑ round ∈ Finset.range roundCount,
      2 * quartileSourceTerminalError
        (quartileSourceGeometricEnvelopeRateBudget initialCount delta scale)
        initialCount delta round) ≤
      scale / (1 - quartileSourceFailureDecay) ^ 2 := by
  apply quartileSourceTerminalError_sum_le_closed_of_scheduledSampleCount
    (quartileSourceGeometricEnvelopeRateBudget initialCount delta scale)
    initialCount delta scale roundCount hdelta hdeltaLeOne hscale
  intro round _ hnonterminal
  exact quartileSourceGeometricEnvelope_sampleThreshold_le_scheduledSampleCount_of_rateBudget
    initialCount delta scale round hinitial hdelta hdeltaLeOne hscale hnonterminal

/-- The terminal-only maximum is itself bounded by the explicit source-rate
budget; this records the finite resource comparison independently of the
policy correctness theorem. -/
theorem quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement_le_rateBudget
    (initialCount roundCount : ℕ) (delta scale : ℝ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hscale : 0 < scale) :
    quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement
      initialCount roundCount delta scale ≤
      quartileSourceGeometricEnvelopeRateBudget initialCount delta scale := by
  unfold quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement
  apply Finset.sup_le
  intro round hround
  rcases Finset.mem_filter.mp hround with ⟨_, hnonterminal⟩
  exact quartileSourceGeometricEnvelopeRoundBudgetRequirement_le_rateBudget
    initialCount delta scale round hdelta hdeltaLeOne hscale hnonterminal

end ZhouChenLi2014OptimalPACMultipleArm
