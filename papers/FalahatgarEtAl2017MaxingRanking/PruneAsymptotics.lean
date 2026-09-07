import AppliedModelingLib.Foundations.Math.Asymptotics
import FalahatgarEtAl2017MaxingRanking.SourceOptMaximizeAsymptotics
import FalahatgarEtAl2017MaxingRanking.PruneRoundContraction

/-!
# Prune resource asymptotics at the rounded source cutoff

Lemma 15's finite sharp geometric envelope separates the contracting bad-arm
mass from the cutoff term.  This module evaluates that exact envelope at the
rounded square-root cutoff used by OPT-Maximize.  The result is deliberately
fixed-parameter: it is a certified specialization of the finite envelope, not
a replacement for the source's simultaneous parameter display.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib Asymptotics

/--
Lemma 15's sharp finite source envelope at Algorithm 3's rounded cutoff, with
the initial bad-arm count bounded by the whole population.
-/
noncomputable def sourceLemma15PruneRateEnvelope
    (armCount : ℕ) (lower upper delta : ℝ) : ℝ :=
  let cutoff := sourceOptMaximizeCutoff armCount
  let roundCount := Nat.log 2 armCount - 1
  (2 / (upper - lower) ^ 2) *
      ((cutoff : ℝ) * (roundCount : ℝ) *
          (Real.log (2 / delta) + ((roundCount : ℝ) + 1) * Real.log 2) +
        (armCount : ℝ) * (2 * Real.log (2 / delta) + 6 * Real.log 2)) +
    (roundCount : ℝ) * (cutoff : ℝ) + 2 * (armCount : ℝ)

/--
The sharp finite Lemma-15 Prune comparison envelope is bounded by its
population-only rounded-cutoff rate envelope whenever the initial bad set is
a subset of the arm population.
-/
theorem pruneComparisonEnvelope_sourceLemma15_le_rateEnvelope
    (armCount badCount : ℕ) (lower upper delta : ℝ)
    (hbadCount : badCount ≤ armCount) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ 1 / 2) :
    ∑ round : Fin (Nat.log 2 armCount - 1),
      ((sourceOptMaximizeCutoff armCount : ℝ) + delta ^ round.val * (badCount : ℝ)) *
        (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val) : ℝ) ≤
      sourceLemma15PruneRateEnvelope armCount lower upper delta := by
  let roundCount : ℕ := Nat.log 2 armCount - 1
  let cutoff : ℕ := sourceOptMaximizeCutoff armCount
  let sourceFactor : ℝ := 2 / (upper - lower) ^ 2
  let badLinear : ℝ := 2 * Real.log (2 / delta) + 6 * Real.log 2
  have hsource := pruneComparisonEnvelope_le_sharpGeometricSourceLogEnvelope
    roundCount cutoff badCount lower upper delta hdelta hdeltaHalf
  have hbadCountReal : (badCount : ℝ) ≤ (armCount : ℝ) := by exact_mod_cast hbadCount
  have hlogGlobalNonnegative : 0 ≤ Real.log (2 / delta) := by
    apply Real.log_nonneg
    apply (one_le_div₀ hdelta).mpr
    linarith
  have hbadLinearNonnegative : 0 ≤ badLinear := by
    dsimp [badLinear]
    positivity
  have hsourceFactorNonnegative : 0 ≤ sourceFactor := by
    dsimp [sourceFactor]
    positivity
  have hbadTerm : (badCount : ℝ) * badLinear ≤ (armCount : ℝ) * badLinear :=
    mul_le_mul_of_nonneg_right hbadCountReal hbadLinearNonnegative
  have hinner :
      (cutoff : ℝ) * (roundCount : ℝ) *
          (Real.log (2 / delta) + ((roundCount : ℝ) + 1) * Real.log 2) +
        (badCount : ℝ) * badLinear ≤
      (cutoff : ℝ) * (roundCount : ℝ) *
          (Real.log (2 / delta) + ((roundCount : ℝ) + 1) * Real.log 2) +
        (armCount : ℝ) * badLinear :=
    add_le_add_right hbadTerm _
  have hscaled := mul_le_mul_of_nonneg_left hinner hsourceFactorNonnegative
  change
    ∑ round : Fin roundCount,
      ((cutoff : ℝ) + delta ^ round.val * (badCount : ℝ)) *
        (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val) : ℝ) ≤ _
  calc
    ∑ round : Fin roundCount,
      ((cutoff : ℝ) + delta ^ round.val * (badCount : ℝ)) *
        (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val) : ℝ) ≤
        sourceFactor *
          ((cutoff : ℝ) * (roundCount : ℝ) *
              (Real.log (2 / delta) + ((roundCount : ℝ) + 1) * Real.log 2) +
            (badCount : ℝ) * badLinear) +
          ((roundCount : ℝ) * (cutoff : ℝ) + 2 * (badCount : ℝ)) := by
      simpa [roundCount, cutoff, sourceFactor, badLinear] using hsource
    _ ≤ sourceFactor *
          ((cutoff : ℝ) * (roundCount : ℝ) *
              (Real.log (2 / delta) + ((roundCount : ℝ) + 1) * Real.log 2) +
            (armCount : ℝ) * badLinear) +
          ((roundCount : ℝ) * (cutoff : ℝ) + 2 * (armCount : ℝ)) := by
      gcongr
    _ = sourceLemma15PruneRateEnvelope armCount lower upper delta := by
      simp only [sourceLemma15PruneRateEnvelope, roundCount, cutoff, sourceFactor, badLinear]
      ring

/--
At fixed valid confidence, the rounded-cutoff sharp Prune envelope divided by
the population tends to the source's noncontracting bad-arm contribution.
-/
theorem tendsto_sourceLemma15PruneRateEnvelope_div_nat
    {lower upper delta : ℝ} (_hdelta : 0 < delta) :
    Filter.Tendsto
      (fun armCount : ℕ =>
        sourceLemma15PruneRateEnvelope armCount lower upper delta /
          (armCount : ℝ))
      Filter.atTop
      (nhds
        ((2 / (upper - lower) ^ 2) *
            (2 * Real.log (2 / delta) + 6 * Real.log 2) + 2)) := by
  let pruneFactor : ℝ := 2 / (upper - lower) ^ 2
  let confidenceLog : ℝ := Real.log (2 / delta)
  let pruneLinear : ℝ := 2 * confidenceLog + 6 * Real.log 2
  have hpopulationRatio :
      Filter.Tendsto (fun armCount : ℕ => (armCount : ℝ) / (armCount : ℝ))
        Filter.atTop (nhds 1) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop 0] with armCount harmCount
    field_simp [ne_of_gt (show 0 < (armCount : ℝ) by exact_mod_cast harmCount)]
  have hcutoffHorizon :=
    tendsto_sourceOptMaximizeCutoff_mul_sourceHorizon_div_nat_nhds_zero
  have hcutoffHorizonSq :=
    tendsto_sourceOptMaximizeCutoff_mul_sourceHorizon_sq_div_nat_nhds_zero
  have hpruneCore :
      Filter.Tendsto
        (fun armCount : ℕ =>
          (sourceOptMaximizeCutoff armCount : ℝ) *
            ((Nat.log 2 armCount - 1 : ℕ) : ℝ) *
            (confidenceLog +
              (((Nat.log 2 armCount - 1 : ℕ) : ℝ) + 1) * Real.log 2) /
              (armCount : ℝ))
        Filter.atTop (nhds 0) := by
    have hsum := hcutoffHorizon.const_mul confidenceLog |>.add
      ((hcutoffHorizonSq.add hcutoffHorizon).const_mul (Real.log 2))
    refine Filter.Tendsto.congr' ?_ (by simpa using hsum)
    filter_upwards with armCount
    dsimp [confidenceLog]
    ring
  have hpruneLinear :
      Filter.Tendsto
        (fun armCount : ℕ => pruneLinear * ((armCount : ℝ) / (armCount : ℝ)))
        Filter.atTop (nhds pruneLinear) := by
    simpa using hpopulationRatio.const_mul pruneLinear
  have hprune :
      Filter.Tendsto
        (fun armCount : ℕ =>
          pruneFactor *
            ((sourceOptMaximizeCutoff armCount : ℝ) *
                ((Nat.log 2 armCount - 1 : ℕ) : ℝ) *
                (confidenceLog +
                  (((Nat.log 2 armCount - 1 : ℕ) : ℝ) + 1) * Real.log 2) /
                (armCount : ℝ) +
              (armCount : ℝ) / (armCount : ℝ) * pruneLinear))
        Filter.atTop (nhds (pruneFactor * pruneLinear)) := by
    have hsum := (hpruneCore.add hpruneLinear).const_mul pruneFactor
    refine Filter.Tendsto.congr' ?_ (by simpa using hsum)
    filter_upwards with armCount
    ring
  have hretained :
      Filter.Tendsto
        (fun armCount : ℕ =>
          (sourceOptMaximizeCutoff armCount : ℝ) *
              ((Nat.log 2 armCount - 1 : ℕ) : ℝ) / (armCount : ℝ) +
            2 * ((armCount : ℝ) / (armCount : ℝ)))
        Filter.atTop (nhds 2) := by
    simpa using hcutoffHorizon.add (hpopulationRatio.const_mul (2 : ℝ))
  have htotal := hprune.add hretained
  refine Filter.Tendsto.congr' ?_
    (by simpa [pruneFactor, confidenceLog, pruneLinear] using htotal)
  filter_upwards with armCount
  unfold sourceLemma15PruneRateEnvelope
  dsimp [pruneFactor, confidenceLog, pruneLinear]
  ring

/--
The preceding exact limit yields a fixed-parameter linear comparison rate for
Lemma 15's sharp rounded-cutoff Prune envelope.
-/
theorem sourceLemma15PruneRateEnvelope_isBigO_linear
    {lower upper delta : ℝ} (hdelta : 0 < delta) :
    IsBigO Filter.atTop
      (fun armCount : ℕ => sourceLemma15PruneRateEnvelope armCount lower upper delta)
      (fun armCount : ℕ => (armCount : ℝ)) := by
  let rateLimit : ℝ :=
    (2 / (upper - lower) ^ 2) *
      (2 * Real.log (2 / delta) + 6 * Real.log 2) + 2
  have hlimit :
      Filter.Tendsto
        (fun armCount : ℕ =>
          sourceLemma15PruneRateEnvelope armCount lower upper delta /
            (armCount : ℝ))
        Filter.atTop (nhds rateLimit) := by
    simpa [rateLimit] using
      tendsto_sourceLemma15PruneRateEnvelope_div_nat (lower := lower) (upper := upper) hdelta
  have hupper :
      ∀ᶠ armCount : ℕ in Filter.atTop,
        sourceLemma15PruneRateEnvelope armCount lower upper delta /
            (armCount : ℝ) < rateLimit + 1 :=
    hlimit.eventually (eventually_lt_nhds (by norm_num))
  have hlower :
      ∀ᶠ armCount : ℕ in Filter.atTop,
        rateLimit - 1 <
          sourceLemma15PruneRateEnvelope armCount lower upper delta /
            (armCount : ℝ) :=
    hlimit.eventually (eventually_gt_nhds (by norm_num))
  have hratioBound :
      ∀ᶠ armCount : ℕ in Filter.atTop,
        |sourceLemma15PruneRateEnvelope armCount lower upper delta /
            (armCount : ℝ)| ≤ |rateLimit| + 1 := by
    filter_upwards [hupper, hlower] with armCount hupperArmCount hlowerArmCount
    rw [abs_le]
    constructor
    · calc
        -(|rateLimit| + 1) ≤ rateLimit - 1 := by
          nlinarith [neg_abs_le rateLimit]
        _ ≤ sourceLemma15PruneRateEnvelope armCount lower upper delta /
              (armCount : ℝ) := hlowerArmCount.le
    · calc
        sourceLemma15PruneRateEnvelope armCount lower upper delta /
            (armCount : ℝ) ≤ rateLimit + 1 := hupperArmCount.le
        _ ≤ |rateLimit| + 1 := by gcongr; exact le_abs_self rateLimit
  rw [isBigO_iff]
  refine ⟨|rateLimit| + 1, ?_⟩
  filter_upwards [hratioBound, Filter.eventually_gt_atTop 0] with armCount hratio harmCount
  have harmCountReal : 0 < (armCount : ℝ) := by exact_mod_cast harmCount
  have hscaled :
      |sourceLemma15PruneRateEnvelope armCount lower upper delta| ≤
        (|rateLimit| + 1) * (armCount : ℝ) := by
    rw [abs_div] at hratio
    exact (div_le_iff₀ harmCountReal).mp
      (by simpa [abs_of_pos harmCountReal] using hratio)
  simpa [Real.norm_eq_abs, abs_of_pos harmCountReal] using hscaled

/--
Lemma 15's Prune resource display is uniform in valid varying confidence and
accuracy-gap parameters.  The source conditions tying the confidence to the
cutoff are needed for the probability guarantee; the comparison-count
envelope itself has this stronger uniform rate statement throughout the
normalised `0 < upper - lower ≤ 1`, `0 < delta ≤ 1 / 2` regime.
-/
theorem sourceLemma15PruneRateEnvelope_isBigO_parametric_sourceRateShape
    (lower upper delta : ℕ → ℝ)
    (hparameters : ∀ᶠ armCount : ℕ in Filter.atTop,
      0 < upper armCount - lower armCount ∧ upper armCount - lower armCount ≤ 1 ∧
        0 < delta armCount ∧ delta armCount ≤ 1 / 2) :
    IsBigO Filter.atTop
      (fun armCount : ℕ =>
        sourceLemma15PruneRateEnvelope armCount (lower armCount) (upper armCount)
          (delta armCount))
      (fun armCount : ℕ =>
        (armCount : ℝ) * (1 + Real.log (1 / delta armCount)) /
          (upper armCount - lower armCount) ^ 2) := by
  have hcutoffHorizonRatio : ∀ᶠ armCount : ℕ in Filter.atTop,
      (sourceOptMaximizeCutoff armCount : ℝ) *
          ((Nat.log 2 armCount - 1 : ℕ) : ℝ) / (armCount : ℝ) < 1 :=
    tendsto_sourceOptMaximizeCutoff_mul_sourceHorizon_div_nat_nhds_zero.eventually
      (eventually_lt_nhds (by norm_num))
  have hcutoffHorizonSqRatio : ∀ᶠ armCount : ℕ in Filter.atTop,
      (sourceOptMaximizeCutoff armCount : ℝ) *
          ((Nat.log 2 armCount - 1 : ℕ) : ℝ) ^ 2 / (armCount : ℝ) < 1 :=
    tendsto_sourceOptMaximizeCutoff_mul_sourceHorizon_sq_div_nat_nhds_zero.eventually
      (eventually_lt_nhds (by norm_num))
  rw [isBigO_iff]
  refine ⟨25, ?_⟩
  filter_upwards [hparameters, hcutoffHorizonRatio, hcutoffHorizonSqRatio,
      Filter.eventually_gt_atTop 0] with armCount hparameters hcutoffHorizon
        hcutoffHorizonSq harmCount
  rcases hparameters with ⟨hgap, hgapLeOne, hdelta, hdeltaHalf⟩
  let gap := upper armCount - lower armCount
  let confidenceLog := Real.log (1 / delta armCount)
  let envelope := 1 + confidenceLog
  let cutoff := (sourceOptMaximizeCutoff armCount : ℝ)
  let roundCount := ((Nat.log 2 armCount - 1 : ℕ) : ℝ)
  let population := (armCount : ℝ)
  have hpopulationPos : 0 < population := by
    dsimp [population]
    exact_mod_cast harmCount
  have hpopulationNonnegative : 0 ≤ population := hpopulationPos.le
  have hgapPos : 0 < gap := by simpa [gap] using hgap
  have hgapNonnegative : 0 ≤ gap := hgapPos.le
  have hgapSqPos : 0 < gap ^ 2 := sq_pos_of_pos hgapPos
  have hgapSqLeOne : gap ^ 2 ≤ 1 := by
    simpa using
      ((sq_le_sq₀ hgapNonnegative (by norm_num : (0 : ℝ) ≤ 1)).mpr hgapLeOne)
  have hinvGapSqGeOne : 1 ≤ 1 / gap ^ 2 := by
    apply (le_div_iff₀ hgapSqPos).mpr
    nlinarith
  have hconfidenceNonnegative : 0 ≤ confidenceLog := by
    dsimp [confidenceLog]
    apply Real.log_nonneg
    apply (one_le_div₀ hdelta).mpr
    linarith
  have henvelopeGeOne : 1 ≤ envelope := by
    dsimp [envelope]
    linarith
  have henvelopeNonnegative : 0 ≤ envelope := by linarith
  have hlogTwoLeOne : Real.log (2 : ℝ) ≤ 1 := by
    apply (Real.exp_le_exp).mp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simpa [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hlogSplit : Real.log (2 / delta armCount) = Real.log 2 + confidenceLog := by
    dsimp [confidenceLog]
    rw [show 2 / delta armCount = 2 * (1 / delta armCount) by
      field_simp [ne_of_gt hdelta]]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (one_div_ne_zero hdelta.ne')]
  have hcutoffNonnegative : 0 ≤ cutoff := by
    dsimp [cutoff]
    exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount)
  have hroundCountNonnegative : 0 ≤ roundCount := by
    dsimp [roundCount]
    exact_mod_cast Nat.zero_le (Nat.log 2 armCount - 1)
  have hcutoffHorizonLe : cutoff * roundCount ≤ population := by
    dsimp [cutoff, roundCount, population] at hcutoffHorizon ⊢
    simpa using
      ((div_lt_iff₀ (by exact_mod_cast harmCount)).mp hcutoffHorizon).le
  have hcutoffHorizonSqLe : cutoff * roundCount ^ 2 ≤ population := by
    dsimp [cutoff, roundCount, population] at hcutoffHorizonSq ⊢
    simpa using
      ((div_lt_iff₀ (by exact_mod_cast harmCount)).mp hcutoffHorizonSq).le
  have hlogBudgetLe : Real.log (2 / delta armCount) ≤ envelope := by
    rw [hlogSplit]
    dsimp [envelope]
    linarith
  have hroundLogLe : (roundCount + 1) * Real.log 2 ≤ roundCount + 1 := by
    calc
      (roundCount + 1) * Real.log 2 ≤ (roundCount + 1) * 1 := by
        apply mul_le_mul_of_nonneg_left hlogTwoLeOne
        linarith
      _ = roundCount + 1 := by ring
  have hcutoffConfidence :
      cutoff * roundCount * Real.log (2 / delta armCount) ≤ population * envelope := by
    calc
      cutoff * roundCount * Real.log (2 / delta armCount) ≤
          cutoff * roundCount * envelope := by
            apply mul_le_mul_of_nonneg_left hlogBudgetLe
            positivity
      _ ≤ population * envelope := by
            exact mul_le_mul_of_nonneg_right hcutoffHorizonLe henvelopeNonnegative
  have hcutoffRoundOverhead :
      cutoff * roundCount * ((roundCount + 1) * Real.log 2) ≤
        2 * population * envelope := by
    calc
      cutoff * roundCount * ((roundCount + 1) * Real.log 2) ≤
          cutoff * roundCount * (roundCount + 1) := by
            apply mul_le_mul_of_nonneg_left hroundLogLe
            positivity
      _ = cutoff * roundCount ^ 2 + cutoff * roundCount := by ring
      _ ≤ population + population := by gcongr
      _ ≤ 2 * population * envelope := by nlinarith
  have hcutoffTerm :
      cutoff * roundCount *
          (Real.log (2 / delta armCount) + (roundCount + 1) * Real.log 2) ≤
        3 * population * envelope := by
    calc
      cutoff * roundCount *
          (Real.log (2 / delta armCount) + (roundCount + 1) * Real.log 2) =
          cutoff * roundCount * Real.log (2 / delta armCount) +
            cutoff * roundCount * ((roundCount + 1) * Real.log 2) := by ring
      _ ≤ population * envelope + 2 * population * envelope :=
        add_le_add hcutoffConfidence hcutoffRoundOverhead
      _ = 3 * population * envelope := by ring
  have hbadTerm :
      population * (2 * Real.log (2 / delta armCount) + 6 * Real.log 2) ≤
        8 * population * envelope := by
    have hinside : 2 * Real.log (2 / delta armCount) + 6 * Real.log 2 ≤
        8 * envelope := by
      rw [hlogSplit]
      dsimp [envelope]
      nlinarith
    calc
      population * (2 * Real.log (2 / delta armCount) + 6 * Real.log 2) ≤
          population * (8 * envelope) :=
        mul_le_mul_of_nonneg_left hinside hpopulationNonnegative
      _ = 8 * population * envelope := by ring
  have hinner :
      cutoff * roundCount *
          (Real.log (2 / delta armCount) + (roundCount + 1) * Real.log 2) +
          population * (2 * Real.log (2 / delta armCount) + 6 * Real.log 2) ≤
        11 * population * envelope := by
    calc
      cutoff * roundCount *
          (Real.log (2 / delta armCount) + (roundCount + 1) * Real.log 2) +
          population * (2 * Real.log (2 / delta armCount) + 6 * Real.log 2) ≤
          3 * population * envelope + 8 * population * envelope :=
        add_le_add hcutoffTerm hbadTerm
      _ = 11 * population * envelope := by ring
  have hscaledInner : (2 / gap ^ 2) *
      (cutoff * roundCount *
          (Real.log (2 / delta armCount) + (roundCount + 1) * Real.log 2) +
          population * (2 * Real.log (2 / delta armCount) + 6 * Real.log 2)) ≤
        22 * population * envelope / gap ^ 2 := by
    calc
      (2 / gap ^ 2) *
          (cutoff * roundCount *
            (Real.log (2 / delta armCount) + (roundCount + 1) * Real.log 2) +
            population * (2 * Real.log (2 / delta armCount) + 6 * Real.log 2)) ≤
          (2 / gap ^ 2) * (11 * population * envelope) := by
            gcongr
      _ = 22 * population * envelope / gap ^ 2 := by
            field_simp [hgapSqPos.ne']
            ring
  have htail : roundCount * cutoff + 2 * population ≤ 3 * population := by
    calc
      roundCount * cutoff + 2 * population = cutoff * roundCount + 2 * population := by ring
      _ ≤ population + 2 * population := by gcongr
      _ = 3 * population := by ring
  have hpopulationRate : population ≤ population * envelope / gap ^ 2 := by
    calc
      population ≤ population * envelope := by nlinarith
      _ ≤ population * envelope / gap ^ 2 := by
        apply (le_div_iff₀ hgapSqPos).mpr
        exact mul_le_of_le_one_right
          (mul_nonneg hpopulationNonnegative henvelopeNonnegative) hgapSqLeOne
  have htailRate : roundCount * cutoff + 2 * population ≤
      3 * population * envelope / gap ^ 2 := by
    calc
      roundCount * cutoff + 2 * population ≤ 3 * population := htail
      _ ≤ 3 * (population * envelope / gap ^ 2) := by gcongr
      _ = 3 * population * envelope / gap ^ 2 := by ring
  have hsourceRate :
      sourceLemma15PruneRateEnvelope armCount (lower armCount) (upper armCount)
          (delta armCount) ≤ 25 * population * envelope / gap ^ 2 := by
    unfold sourceLemma15PruneRateEnvelope
    dsimp only
    change (2 / gap ^ 2) *
          (cutoff * roundCount *
              (Real.log (2 / delta armCount) + (roundCount + 1) * Real.log 2) +
            population * (2 * Real.log (2 / delta armCount) + 6 * Real.log 2)) +
          roundCount * cutoff + 2 * population ≤
        25 * population * envelope / gap ^ 2
    calc
      (2 / gap ^ 2) *
            (cutoff * roundCount *
                (Real.log (2 / delta armCount) + (roundCount + 1) * Real.log 2) +
              population * (2 * Real.log (2 / delta armCount) + 6 * Real.log 2)) +
            roundCount * cutoff + 2 * population =
          (2 / gap ^ 2) *
            (cutoff * roundCount *
                (Real.log (2 / delta armCount) + (roundCount + 1) * Real.log 2) +
              population * (2 * Real.log (2 / delta armCount) + 6 * Real.log 2)) +
            (roundCount * cutoff + 2 * population) := by ring
      _ ≤
          22 * population * envelope / gap ^ 2 +
            3 * population * envelope / gap ^ 2 := by
              exact add_le_add hscaledInner htailRate
      _ = 25 * population * envelope / gap ^ 2 := by ring
  have hsourceNonnegative : 0 ≤
      sourceLemma15PruneRateEnvelope armCount (lower armCount) (upper armCount)
        (delta armCount) := by
    unfold sourceLemma15PruneRateEnvelope
    dsimp only
    change 0 ≤ (2 / gap ^ 2) *
          (cutoff * roundCount *
              (Real.log (2 / delta armCount) + (roundCount + 1) * Real.log 2) +
            population * (2 * Real.log (2 / delta armCount) + 6 * Real.log 2)) +
          roundCount * cutoff + 2 * population
    have hlogNonnegative : 0 ≤ Real.log (2 / delta armCount) := by
      rw [hlogSplit]
      exact add_nonneg (Real.log_nonneg (by norm_num)) hconfidenceNonnegative
    positivity
  have hrateNonnegative : 0 ≤ population * envelope / gap ^ 2 := by positivity
  change ‖sourceLemma15PruneRateEnvelope armCount (lower armCount) (upper armCount)
      (delta armCount)‖ ≤
    25 * ‖(armCount : ℝ) * (1 + Real.log (1 / delta armCount)) /
      (upper armCount - lower armCount) ^ 2‖
  rw [Real.norm_eq_abs, abs_of_nonneg hsourceNonnegative, Real.norm_eq_abs,
    abs_of_nonneg hrateNonnegative]
  have hrateShape :
      25 * population * envelope / gap ^ 2 =
        25 * ((armCount : ℝ) * (1 + Real.log (1 / delta armCount)) /
          (upper armCount - lower armCount) ^ 2) := by
    simp [gap, confidenceLog, envelope, population]
    ring
  rw [← hrateShape]
  exact hsourceRate

end FalahatgarEtAl2017MaxingRanking
