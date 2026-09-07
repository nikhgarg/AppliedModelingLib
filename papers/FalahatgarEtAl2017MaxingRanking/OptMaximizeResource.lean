import FalahatgarEtAl2017MaxingRanking.FreshFinalCheck

/-!
# OPT-Maximize final-tail comparison caps

This file records the finite, ceiling-corrected comparison caps for Algorithm
3's steps 8--13.  They are execution caps: a final loop may return earlier,
and adaptive Compare may stop before its batch cap, but neither effect can
increase these source-budgeted totals.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL

/-- The maximum number of observations allocated to the final comparison loop. -/
noncomputable def optMaximizeFinalCheckComparisonCap {Arm : Type*}
    (candidates : Finset Arm) (lower upper eta : ℝ) : ℕ :=
  candidates.card * fixedSampleBudget lower upper eta

/--
The maximum number of observations allocated to the fallback Seq-Eliminate
call.  On an empty retained set the totalized fallback makes zero calls.
-/
noncomputable def optMaximizeFallbackComparisonCap {Arm : Type*}
    (candidates : Finset Arm) (epsilon delta : ℝ) : ℕ :=
  (candidates.card - 1) * fixedSampleBudget 0 epsilon (delta / (candidates.card : ℝ))

/-- The comparison cap of Algorithm 3's whole-set Seq-Eliminate base branch. -/
noncomputable def optMaximizeBaseComparisonCap {Arm : Type*} [Fintype Arm]
    (epsilon delta : ℝ) : ℕ :=
  optMaximizeFallbackComparisonCap (Finset.univ : Finset Arm) epsilon delta

/-- The source finite cap for Algorithm 3's final loop plus its possible fallback. -/
noncomputable def optMaximizeFinalTailComparisonCap {Arm : Type*}
    (candidates : Finset Arm) (lower upper finalEta fallbackEpsilon fallbackDelta : ℝ) : ℕ :=
  optMaximizeFinalCheckComparisonCap candidates lower upper finalEta +
    optMaximizeFallbackComparisonCap candidates fallbackEpsilon fallbackDelta

/--
The `δ / 4` confidence allocation used by Algorithm 3 contributes a fixed
`log (8 / δ)` term plus the cardinality-specific confidence term.
-/
theorem log_two_div_quarter_delta_div_card
    (delta : ℝ) (card : ℕ) (hdelta : 0 < delta) (hcard : 0 < card) :
    Real.log (2 / ((delta / 4) / (card : ℝ))) =
      Real.log (8 / delta) + Real.log (card : ℝ) := by
  have hdeltaNe : delta ≠ 0 := ne_of_gt hdelta
  have hcardNe : (card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hcard
  have hglobalNe : (8 / delta : ℝ) ≠ 0 := div_ne_zero (by norm_num) hdeltaNe
  have hfactor : 2 / ((delta / 4) / (card : ℝ)) =
      (8 / delta) * (card : ℝ) := by
    field_simp [hdeltaNe, hcardNe]
    norm_num
  rw [hfactor, Real.log_mul hglobalNe hcardNe]

/-- A final loop with one fresh Compare batch per retained arm has the stated ceiling cap. -/
theorem optMaximizeFinalCheckComparisonCap_real_le_sourceBudget {Arm : Type*}
    (candidates : Finset Arm) (lower upper eta : ℝ)
    (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    (optMaximizeFinalCheckComparisonCap candidates lower upper eta : ℝ) ≤
      (candidates.card : ℝ) *
        (2 / (upper - lower) ^ 2 * Real.log (2 / eta) + 1) := by
  exact finiteCallCount_ceilingBudget_real_le_sourceBudget candidates.card lower upper eta
    heta hetaLeOne

/--
On a nonempty retained set, the fallback's actual `|S'|-1` Seq-Eliminate
calls have the source ceiling cap at allocation `δ / |S'|`.
-/
theorem optMaximizeFallbackComparisonCap_real_le_sourceBudget {Arm : Type*}
    (candidates : Finset Arm) (epsilon delta : ℝ)
    (hnonempty : candidates.Nonempty)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (optMaximizeFallbackComparisonCap candidates epsilon delta : ℝ) ≤
      (candidates.card - 1 : ℕ) *
        (2 / epsilon ^ 2 * Real.log (2 / (delta / (candidates.card : ℝ))) + 1) := by
  have hcardPositiveNat : 0 < candidates.card := Finset.card_pos.mpr hnonempty
  have hcardPositive : 0 < (candidates.card : ℝ) := by exact_mod_cast hcardPositiveNat
  have heta : 0 < delta / (candidates.card : ℝ) := div_pos hdelta hcardPositive
  have hcardOne : (1 : ℝ) ≤ candidates.card := by
    exact_mod_cast Nat.succ_le_iff.mpr hcardPositiveNat
  have hetaLeOne : delta / (candidates.card : ℝ) ≤ 1 := by
    calc
      delta / (candidates.card : ℝ) ≤ delta :=
        div_le_self (le_of_lt hdelta) hcardOne
      _ ≤ 1 := hdeltaLeOne
  simpa only [optMaximizeFallbackComparisonCap, sub_zero] using
    (finiteCallCount_ceilingBudget_real_le_sourceBudget (candidates.card - 1) 0 epsilon
      (delta / (candidates.card : ℝ)) heta hetaLeOne)

/-- The source base branch inherits the whole-set Seq-Eliminate ceiling cap. -/
theorem optMaximizeBaseComparisonCap_real_le_sourceBudget {Arm : Type*}
    [Fintype Arm] [Nonempty Arm] (epsilon delta : ℝ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (optMaximizeBaseComparisonCap (Arm := Arm) epsilon delta : ℝ) ≤
      (Fintype.card Arm - 1 : ℕ) *
        (2 / epsilon ^ 2 * Real.log (2 / (delta / (Fintype.card Arm : ℝ))) + 1) := by
  simpa only [optMaximizeBaseComparisonCap, Finset.card_univ] using
    (optMaximizeFallbackComparisonCap_real_le_sourceBudget (Finset.univ : Finset Arm)
      epsilon delta (Finset.univ_nonempty) hdelta hdeltaLeOne)

/--
The base branch's joint source event: Seq-Eliminate returns an `ε`-maximum
while its full-arm source allocation obeys the finite ceiling-corrected cap.
The comparison cap is deterministic, so no additional failure budget is spent.
-/
noncomputable def canonicalOptMaximizeBaseSourceJointResourceProbability {Arm : Type*}
    [Fintype Arm] [Nonempty Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) : ℝ := by
  classical
  exact pmfProbClassical
    (canonicalOptMaximizeBaseSourceOutputLaw preferenceGap hprobability epsilon delta)
    (fun output => EpsilonMaximum preferenceGap epsilon output ∧
      (optMaximizeBaseComparisonCap (Arm := Arm) epsilon delta : ℝ) ≤
        (Fintype.card Arm - 1 : ℕ) *
          (2 / epsilon ^ 2 * Real.log (2 / (delta / (Fintype.card Arm : ℝ))) + 1))

/--
Algorithm 3's `δ ≤ 1/n` branch has its output and finite source resource cap
on one event of probability at least `1 - δ`.
-/
theorem canonicalOptMaximizeBaseSource_joint_resource_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (maximum : Arm) (hmaximum : AbsoluteMaximum preferenceGap maximum) :
    1 - delta ≤
      canonicalOptMaximizeBaseSourceJointResourceProbability preferenceGap hprobability epsilon delta := by
  classical
  have houtput := canonicalOptMaximizeBaseSource_epsilonMaximum_probability preferenceGap
    hprobability epsilon delta hantisymmetric hself hsst hepsilon hdelta hdeltaLeOne maximum hmaximum
  have hcap := optMaximizeBaseComparisonCap_real_le_sourceBudget (Arm := Arm) epsilon delta
    hdelta hdeltaLeOne
  unfold canonicalOptMaximizeBaseSourceEpsilonMaximumProbability at houtput
  unfold canonicalOptMaximizeBaseSourceJointResourceProbability
  rw [pmfProbClassical_eq_pmfProb] at houtput ⊢
  exact houtput.trans (pmfProb_le_of_imp _ _ _ (by
    intro output hsuccess
    exact ⟨hsuccess, hcap⟩))

/--
The final-tail cap is the sum of its separately source-budgeted components;
this is the exact finite precursor to Lemma 18's asymptotic resource display.
-/
theorem optMaximizeFinalTailComparisonCap_real_le_sourceBudget {Arm : Type*}
    (candidates : Finset Arm) (lower upper finalEta fallbackEpsilon fallbackDelta : ℝ)
    (heta : 0 < finalEta) (hetaLeOne : finalEta ≤ 1)
    (hnonempty : candidates.Nonempty)
    (hfallbackDelta : 0 < fallbackDelta) (hfallbackDeltaLeOne : fallbackDelta ≤ 1) :
    (optMaximizeFinalTailComparisonCap candidates lower upper finalEta fallbackEpsilon fallbackDelta : ℝ) ≤
      (candidates.card : ℝ) *
        (2 / (upper - lower) ^ 2 * Real.log (2 / finalEta) + 1) +
      (candidates.card - 1 : ℕ) *
        (2 / fallbackEpsilon ^ 2 *
          Real.log (2 / (fallbackDelta / (candidates.card : ℝ))) + 1) := by
  unfold optMaximizeFinalTailComparisonCap
  rw [Nat.cast_add]
  exact add_le_add
    (optMaximizeFinalCheckComparisonCap_real_le_sourceBudget candidates lower upper finalEta
      heta hetaLeOne)
    (optMaximizeFallbackComparisonCap_real_le_sourceBudget candidates fallbackEpsilon fallbackDelta
      hnonempty hfallbackDelta hfallbackDeltaLeOne)

/--
Algorithm 3's `δ / 4` tail allocations give a finite source-log budget for
the final checks and the conditional fallback.  This is the exact precursor
to the tail portion of Theorem 6's displayed rate.
-/
theorem optMaximizeFinalTailComparisonCap_real_le_algorithm3SourceBudget
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (candidates : Finset Arm) (lower upper epsilon delta : ℝ)
    (hcandidates : candidates.Nonempty)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (optMaximizeFinalTailComparisonCap candidates lower upper
      ((delta / 4) / (Fintype.card Arm : ℝ)) epsilon (delta / 4) : ℝ) ≤
      (candidates.card : ℝ) *
        (2 / (upper - lower) ^ 2 *
          (Real.log (8 / delta) + Real.log (Fintype.card Arm : ℝ)) + 1) +
      (candidates.card - 1 : ℕ) *
        (2 / epsilon ^ 2 *
          (Real.log (8 / delta) + Real.log (candidates.card : ℝ)) + 1) := by
  have hcard : 0 < Fintype.card Arm := Fintype.card_pos_iff.mpr inferInstance
  have hcardReal : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcard
  have hcardGeOne : 1 ≤ (Fintype.card Arm : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hcard
  have hquarterPos : 0 < delta / 4 := by positivity
  have hquarterLeOne : delta / 4 ≤ 1 := by linarith
  have hfinalEtaPos : 0 < (delta / 4) / (Fintype.card Arm : ℝ) :=
    div_pos hquarterPos hcardReal
  have hfinalEtaLeOne : (delta / 4) / (Fintype.card Arm : ℝ) ≤ 1 := by
    calc
      (delta / 4) / (Fintype.card Arm : ℝ) ≤ delta / 4 :=
        div_le_self (le_of_lt hquarterPos) hcardGeOne
      _ ≤ 1 := hquarterLeOne
  have hsource := optMaximizeFinalTailComparisonCap_real_le_sourceBudget candidates lower upper
    ((delta / 4) / (Fintype.card Arm : ℝ)) epsilon (delta / 4)
    hfinalEtaPos hfinalEtaLeOne hcandidates hquarterPos hquarterLeOne
  rw [log_two_div_quarter_delta_div_card delta (Fintype.card Arm) hdelta hcard] at hsource
  rw [log_two_div_quarter_delta_div_card delta candidates.card hdelta
    (Finset.card_pos.mpr hcandidates)] at hsource
  exact hsource

/--
The total finite source-log envelope for Algorithm 3's tail.  The empty
retained-set branch has zero comparisons, while the nonempty branch exposes
the final-check and fallback logarithms separately.
-/
noncomputable def optMaximizeFinalTailAlgorithm3SourceBudget {Arm : Type*} [Fintype Arm]
    (candidates : Finset Arm) (lower upper epsilon delta : ℝ) : ℝ := by
  classical
  exact if candidates.Nonempty then
    (candidates.card : ℝ) *
      (2 / (upper - lower) ^ 2 *
        (Real.log (8 / delta) + Real.log (Fintype.card Arm : ℝ)) + 1) +
    (candidates.card - 1 : ℕ) *
      (2 / epsilon ^ 2 *
        (Real.log (8 / delta) + Real.log (candidates.card : ℝ)) + 1)
  else 0

/-- The literal Algorithm-3 tail envelope is bounded by its population form. -/
theorem optMaximizeFinalTailAlgorithm3SourceBudget_le_cardEnvelope
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (candidates : Finset Arm) (cutoff : ℕ) (lower upper epsilon delta : ℝ)
    (hcard : candidates.card ≤ 2 * cutoff)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    optMaximizeFinalTailAlgorithm3SourceBudget candidates lower upper epsilon delta ≤
      2 * (cutoff : ℝ) *
          (2 / (upper - lower) ^ 2 *
            (Real.log (8 / delta) + Real.log (Fintype.card Arm : ℝ)) + 1) +
        2 * (cutoff : ℝ) *
          (2 / epsilon ^ 2 *
            (Real.log (8 / delta) + Real.log (Fintype.card Arm : ℝ)) + 1) := by
  classical
  have hpopulationNat : 0 < Fintype.card Arm := Fintype.card_pos_iff.mpr inferInstance
  have hpopulationLog : 0 ≤ Real.log (Fintype.card Arm : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_iff.mpr hpopulationNat
  have hglobalLog : 0 < Real.log (8 / delta) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hdelta).mpr
    nlinarith
  let finalFactor : ℝ :=
    2 / (upper - lower) ^ 2 *
      (Real.log (8 / delta) + Real.log (Fintype.card Arm : ℝ)) + 1
  let fallbackFactor : ℝ :=
    2 / epsilon ^ 2 *
      (Real.log (8 / delta) + Real.log (Fintype.card Arm : ℝ)) + 1
  have hfinalFactor : 0 ≤ finalFactor := by
    dsimp [finalFactor]
    positivity
  have hfallbackFactor : 0 ≤ fallbackFactor := by
    dsimp [fallbackFactor]
    positivity
  by_cases hnonempty : candidates.Nonempty
  · have hcandidateNat : 0 < candidates.card := Finset.card_pos.mpr hnonempty
    have hcandidate : 0 < (candidates.card : ℝ) := by exact_mod_cast hcandidateNat
    have hcandidateLePopulationNat : candidates.card ≤ Fintype.card Arm :=
      Finset.card_le_univ _
    have hcandidateLePopulation : (candidates.card : ℝ) ≤ (Fintype.card Arm : ℝ) := by
      exact_mod_cast hcandidateLePopulationNat
    have hlogCandidate : Real.log (candidates.card : ℝ) ≤
        Real.log (Fintype.card Arm : ℝ) :=
      Real.log_le_log hcandidate hcandidateLePopulation
    have hcardReal : (candidates.card : ℝ) ≤ 2 * (cutoff : ℝ) := by
      exact_mod_cast hcard
    have hsubCardReal : ((candidates.card - 1 : ℕ) : ℝ) ≤ 2 * (cutoff : ℝ) := by
      calc
        ((candidates.card - 1 : ℕ) : ℝ) ≤ (candidates.card : ℝ) := by
          exact_mod_cast Nat.sub_le _ _
        _ ≤ 2 * (cutoff : ℝ) := hcardReal
    have hfallbackCandidate :
        2 / epsilon ^ 2 *
            (Real.log (8 / delta) + Real.log (candidates.card : ℝ)) + 1 ≤
          fallbackFactor := by
      dsimp [fallbackFactor]
      gcongr
    rw [optMaximizeFinalTailAlgorithm3SourceBudget, if_pos hnonempty]
    change
      (candidates.card : ℝ) * finalFactor +
          (candidates.card - 1 : ℕ) *
            (2 / epsilon ^ 2 *
              (Real.log (8 / delta) + Real.log (candidates.card : ℝ)) + 1) ≤
        2 * (cutoff : ℝ) * finalFactor + 2 * (cutoff : ℝ) * fallbackFactor
    calc
      (candidates.card : ℝ) * finalFactor +
          (candidates.card - 1 : ℕ) *
            (2 / epsilon ^ 2 *
              (Real.log (8 / delta) + Real.log (candidates.card : ℝ)) + 1) ≤
          (candidates.card : ℝ) * finalFactor +
            (candidates.card - 1 : ℕ) * fallbackFactor := by
          gcongr
      _ ≤ 2 * (cutoff : ℝ) * finalFactor + 2 * (cutoff : ℝ) * fallbackFactor := by
          gcongr
  · rw [optMaximizeFinalTailAlgorithm3SourceBudget, if_neg hnonempty]
    positivity

/-- The source-tail cap is bounded by its total finite source-log envelope. -/
theorem optMaximizeFinalTailComparisonCap_real_le_algorithm3SourceEnvelope
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (candidates : Finset Arm) (lower upper epsilon delta : ℝ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (optMaximizeFinalTailComparisonCap candidates lower upper
      ((delta / 4) / (Fintype.card Arm : ℝ)) epsilon (delta / 4) : ℝ) ≤
      optMaximizeFinalTailAlgorithm3SourceBudget candidates lower upper epsilon delta := by
  classical
  by_cases hnonempty : candidates.Nonempty
  · simpa only [optMaximizeFinalTailAlgorithm3SourceBudget, if_pos hnonempty] using
      (optMaximizeFinalTailComparisonCap_real_le_algorithm3SourceBudget candidates lower upper
        epsilon delta hnonempty hdelta hdeltaLeOne)
  · have hempty : candidates = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp [hempty, optMaximizeFinalTailComparisonCap,
      optMaximizeFinalCheckComparisonCap, optMaximizeFallbackComparisonCap,
      optMaximizeFinalTailAlgorithm3SourceBudget]

end FalahatgarEtAl2017MaxingRanking
