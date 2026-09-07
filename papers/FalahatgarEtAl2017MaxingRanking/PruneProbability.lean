import FalahatgarEtAl2017MaxingRanking.PruneRetention
import FalahatgarEtAl2017MaxingRanking.CoreDefinitions
import FalahatgarEtAl2017MaxingRanking.SampleBudget
import FalahatgarEtAl2017MaxingRanking.AdaptiveCompareProbability

/-!
# Fixed-sample Prune retention probability

This file connects the fixed-sample Compare theorem to Lemma 13's Prune
retention event for a fixed scheduled collection of rounds.  It does not yet
model the source algorithm's adaptive histories; its hypotheses name the
independence and mean conditions for every scheduled protected-arm batch.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- Prune rounds indexed in source order by `0, ..., roundCount - 1`. -/
noncomputable def indexedPruneRounds {Ω Arm : Type*} [DecidableEq Arm]
    (roundCount : ℕ) (decision : ℕ → Arm → Ω → CompareDecision)
    (outcome : Ω) (active : Finset Arm) : Finset Arm :=
  pruneRounds (List.range roundCount |>.map fun index arm => decision index arm outcome) active

/-- Extending an indexed schedule by one round applies that round to its prefix result. -/
theorem indexedPruneRounds_succ {Ω Arm : Type*} [DecidableEq Arm]
    (roundCount : ℕ) (decision : ℕ → Arm → Ω → CompareDecision)
    (outcome : Ω) (active : Finset Arm) :
    indexedPruneRounds (roundCount + 1) decision outcome active =
      pruneRound (indexedPruneRounds roundCount decision outcome active)
        (fun arm => decision roundCount arm outcome) := by
  unfold indexedPruneRounds
  rw [List.range_succ, List.map_append, pruneRounds_append]
  simp [pruneRounds]

/-- The fixed-sample Compare decision used for a specified Prune round and arm. -/
noncomputable def fixedSamplePruneDecision {Ω Arm : Type*}
    (observation : ℕ → Arm → ℕ → Ω → ℝ)
    (lower upper delta : ℝ) (round : ℕ) (arm : Arm) (outcome : Ω) : CompareDecision :=
  fixedSampleCompare (observation round arm) (fixedSampleBudget lower upper delta) lower upper outcome

/-- All upper decisions for an arm imply its retention in the indexed Prune result. -/
theorem mem_indexedPruneRounds_of_allUpper {Ω Arm : Type*} [DecidableEq Arm]
    (roundCount : ℕ) (decision : ℕ → Arm → Ω → CompareDecision)
    (outcome : Ω) (active : Finset Arm) (kept : Arm)
    (hmem : kept ∈ active)
    (hupper : ∀ round < roundCount, decision round kept outcome = .upper) :
    kept ∈ indexedPruneRounds roundCount decision outcome active := by
  unfold indexedPruneRounds
  apply mem_pruneRounds_of_allUpper
  · exact hmem
  · intro roundDecision hroundDecision
    simp only [List.mem_map] at hroundDecision
    rcases hroundDecision with ⟨round, hround, rfl⟩
    exact hupper round (List.mem_range.mp hround)

/--
Finite union-bound retention for any scheduled Prune decisions with a common
per-round upper-decision failure budget.
-/
theorem indexedPruneRounds_retention_probability
    {Ω Arm : Type*} [MeasurableSpace Ω] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (roundCount : ℕ) (decision : ℕ → Arm → Ω → CompareDecision)
    (active : Finset Arm) (kept : Arm) (failureBudget : ℝ)
    (hmem : kept ∈ active)
    (hmeasurable : ∀ round < roundCount,
      MeasurableSet {outcome | decision round kept outcome = .upper})
    (hfailure : ∀ round < roundCount,
      law.real {outcome | decision round kept outcome ≠ .upper} ≤ failureBudget) :
    1 - (roundCount : ℝ) * failureBudget ≤
      law.real {outcome | kept ∈ indexedPruneRounds roundCount decision outcome active} := by
  have hallGood := finiteSequential_goodEvent_probability law roundCount
    (fun round outcome => decision round kept outcome = .upper) failureBudget
    hmeasurable hfailure
  calc
    1 - (roundCount : ℝ) * failureBudget ≤
        law.real {outcome | ∀ round < roundCount, decision round kept outcome = .upper} := hallGood
    _ ≤ law.real {outcome | kept ∈ indexedPruneRounds roundCount decision outcome active} := by
      refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
      intro outcome hall
      change ∀ round < roundCount, decision round kept outcome = .upper at hall
      exact mem_indexedPruneRounds_of_allUpper roundCount decision outcome active kept hmem hall

/--
The same Prune retention argument with a round-varying confidence allocation.
This is the finite-union form used by the geometric schedule in Lemma 13.
-/
theorem indexedPruneRounds_retention_probability_of_varyingFailure
    {Ω Arm : Type*} [MeasurableSpace Ω] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (roundCount : ℕ) (decision : ℕ → Arm → Ω → CompareDecision)
    (active : Finset Arm) (kept : Arm) (failureBudget : ℕ → ℝ)
    (hmem : kept ∈ active)
    (hmeasurable : ∀ round < roundCount,
      MeasurableSet {outcome | decision round kept outcome = .upper})
    (hfailure : ∀ round < roundCount,
      law.real {outcome | decision round kept outcome ≠ .upper} ≤ failureBudget round) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      law.real {outcome | kept ∈ indexedPruneRounds roundCount decision outcome active} := by
  classical
  let badUnion : Set Ω := ⋃ round ∈ Finset.range roundCount,
    {outcome | decision round kept outcome ≠ .upper}
  let allUpper : Set Ω := {outcome | ∀ round < roundCount,
    decision round kept outcome = .upper}
  have hbadUnionMeasurable : MeasurableSet badUnion := by
    dsimp [badUnion]
    refine Finset.measurableSet_biUnion (s := Finset.range roundCount) ?_
    intro round hround
    exact (hmeasurable round (Finset.mem_range.mp hround)).compl
  have hcomplement : allUpper = badUnionᶜ := by
    ext outcome
    simp [allUpper, badUnion]
  have hunion : law.real badUnion ≤
      ∑ round ∈ Finset.range roundCount,
        law.real {outcome | decision round kept outcome ≠ .upper} := by
    dsimp [badUnion]
    simpa using (measureReal_biUnion_finset_le (μ := law)
      (Finset.range roundCount) (fun round =>
        {outcome | decision round kept outcome ≠ .upper}))
  have hsum :
      (∑ round ∈ Finset.range roundCount,
        law.real {outcome | decision round kept outcome ≠ .upper}) ≤
        ∑ round ∈ Finset.range roundCount, failureBudget round := by
    apply Finset.sum_le_sum
    intro round hround
    exact hfailure round (Finset.mem_range.mp hround)
  have hgood :
      1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
        law.real allUpper := by
    have hmeasureComplement : law.real badUnionᶜ = 1 - law.real badUnion :=
      probReal_compl_eq_one_sub (μ := law) hbadUnionMeasurable
    rw [hcomplement]
    rw [hmeasureComplement]
    linarith
  calc
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤ law.real allUpper := hgood
    _ ≤ law.real {outcome | kept ∈ indexedPruneRounds roundCount decision outcome active} := by
      refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
      intro outcome hall
      exact mem_indexedPruneRounds_of_allUpper roundCount decision outcome active kept hmem hall

/--
The failure-side counterpart of the varying-budget retention theorem.  It is
the form consumed by OPT-Maximize's final union bound and does not require
measurability of the composite membership event.
-/
theorem indexedPruneRounds_failure_probability_of_varyingFailure
    {Ω Arm : Type*} [MeasurableSpace Ω] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (roundCount : ℕ) (decision : ℕ → Arm → Ω → CompareDecision)
    (active : Finset Arm) (kept : Arm) (failureBudget : ℕ → ℝ)
    (hmem : kept ∈ active)
    (hfailure : ∀ round < roundCount,
      law.real {outcome | decision round kept outcome ≠ .upper} ≤ failureBudget round) :
    law.real {outcome | kept ∉ indexedPruneRounds roundCount decision outcome active} ≤
      ∑ round ∈ Finset.range roundCount, failureBudget round := by
  classical
  let badUnion : Set Ω := ⋃ round ∈ Finset.range roundCount,
    {outcome | decision round kept outcome ≠ .upper}
  have hsubset :
      {outcome | kept ∉ indexedPruneRounds roundCount decision outcome active} ⊆ badUnion := by
    intro outcome hfailureEvent
    by_contra hnotBadUnion
    apply hfailureEvent
    apply mem_indexedPruneRounds_of_allUpper roundCount decision outcome active kept hmem
    intro round hround
    by_contra hnotUpper
    exact hnotBadUnion (by
      simp only [badUnion, Set.mem_iUnion]
      exact ⟨round, ⟨Finset.mem_range.mpr hround, hnotUpper⟩⟩)
  have hunion : law.real badUnion ≤
      ∑ round ∈ Finset.range roundCount,
        law.real {outcome | decision round kept outcome ≠ .upper} := by
    dsimp [badUnion]
    exact measureReal_biUnion_finset_le (Finset.range roundCount)
      (fun round => {outcome | decision round kept outcome ≠ .upper})
  have hsum :
      (∑ round ∈ Finset.range roundCount,
        law.real {outcome | decision round kept outcome ≠ .upper}) ≤
        ∑ round ∈ Finset.range roundCount, failureBudget round := by
    apply Finset.sum_le_sum
    intro round hround
    exact hfailure round (Finset.mem_range.mp hround)
  exact (measureReal_mono hsubset (measure_ne_top law _)).trans (hunion.trans hsum)

/-- Lemma 13's source schedule, with source round `t = round + 1`. -/
noncomputable def adaptivePruneRoundDelta (delta : ℝ) (round : ℕ) : ℝ :=
  delta / (2 : ℝ) ^ (round + 2)

/-- The adaptive Compare decision in one scheduled Prune round. -/
noncomputable def adaptivePruneDecision {Ω Arm : Type*}
    (observation : ℕ → Arm → ℕ → Ω → ℝ) (lower upper delta : ℝ)
    (round : ℕ) (arm : Arm) (outcome : Ω) : CompareDecision :=
  adaptiveCompare (observation round arm)
    (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round))
    lower upper (adaptivePruneRoundDelta delta round) outcome

theorem adaptivePruneRoundDelta_sum
    (delta : ℝ) (roundCount : ℕ) :
    (∑ round ∈ Finset.range roundCount, adaptivePruneRoundDelta delta round) =
      delta / 2 - delta / (2 : ℝ) ^ (roundCount + 1) := by
  induction roundCount with
  | zero => norm_num [adaptivePruneRoundDelta]
  | succ round ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [adaptivePruneRoundDelta]
      rw [show Nat.succ round + 1 = round + 2 by omega]
      have hpower : (2 : ℝ) ^ (round + 2) = (2 : ℝ) ^ (round + 1) * 2 := by
        rw [show round + 2 = (round + 1) + 1 by omega, pow_succ]
      rw [hpower]
      field_simp
      ring

theorem adaptivePruneRoundDelta_sum_le_half
    (delta : ℝ) (hdelta : 0 ≤ delta) (roundCount : ℕ) :
    ∑ round ∈ Finset.range roundCount, adaptivePruneRoundDelta delta round ≤ delta / 2 := by
  rw [adaptivePruneRoundDelta_sum]
  have hnonnegative : 0 ≤ delta / (2 : ℝ) ^ (roundCount + 1) := by positivity
  linarith

/--
Lemma 13's protected-arm retention event with its exact geometric outer
confidence allocation.  Each round uses the adaptive Compare cap and the
total failure probability is at most `delta / 2`.
-/
theorem adaptivePrune_retention_probability
    {Ω Arm : Type*} [MeasurableSpace Ω] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (roundCount : ℕ) (observation : ℕ → Arm → ℕ → Ω → ℝ)
    (active : Finset Arm) (kept : Arm)
    (lower upper centeredGap delta : ℝ)
    (hmem : kept ∈ active)
    (hindependent : ∀ round < roundCount,
      iIndepFun (observation round kept) law)
    (hmeasurable : ∀ round < roundCount, ∀ sample,
      Measurable (observation round kept sample))
    (hbounded : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
        ∀ᵐ outcome ∂law, observation round kept sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
        law[observation round kept sample] = 1 / 2 + centeredGap)
    (hdecisionMeasurable : ∀ round < roundCount,
      MeasurableSet {outcome |
        adaptivePruneDecision observation lower upper delta round kept outcome = .upper})
    (hgap : upper ≤ centeredGap)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    1 - delta / 2 ≤
      law.real {outcome | kept ∈ indexedPruneRounds roundCount
        (adaptivePruneDecision observation lower upper delta) outcome active} := by
  have hschedule := adaptivePruneRoundDelta_sum_le_half delta (le_of_lt hdelta) roundCount
  calc
    1 - delta / 2 ≤
        1 - ∑ round ∈ Finset.range roundCount, adaptivePruneRoundDelta delta round := by
          linarith
    _ ≤ law.real {outcome | kept ∈ indexedPruneRounds roundCount
          (adaptivePruneDecision observation lower upper delta) outcome active} := by
      apply indexedPruneRounds_retention_probability_of_varyingFailure law roundCount
        (adaptivePruneDecision observation lower upper delta) active kept
        (adaptivePruneRoundDelta delta) hmem
      · intro round hround
        exact hdecisionMeasurable round hround
      · intro round hround
        change law.real {outcome | adaptiveCompare (observation round kept)
          (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round)) lower upper
          (adaptivePruneRoundDelta delta round) outcome ≠ .upper} ≤
          adaptivePruneRoundDelta delta round
        apply adaptiveCompare_upper_failure_probability_of_ceilingBudget law
          (observation round kept) lower upper centeredGap
          (adaptivePruneRoundDelta delta round)
        · exact hindependent round hround
        · exact hmeasurable round hround
        · exact hbounded round hround
        · exact hmean round hround
        · exact hgap
        · exact hseparation
        · exact div_pos hdelta (by positivity)
        · apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (round + 2))).mpr
          have hpower : 1 ≤ (2 : ℝ) ^ (round + 2) := one_le_pow₀ (by norm_num)
          nlinarith

/--
Lemma 13's adaptive Prune bound in failure-event form.  This is equivalent in
content to the retention statement above, but is composable with the other
OPT-Maximize failure events without a measurability assumption on the full
iterated output.
-/
theorem adaptivePrune_failure_probability
    {Ω Arm : Type*} [MeasurableSpace Ω] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (roundCount : ℕ) (observation : ℕ → Arm → ℕ → Ω → ℝ)
    (active : Finset Arm) (kept : Arm)
    (lower upper centeredGap delta : ℝ)
    (hmem : kept ∈ active)
    (hindependent : ∀ round < roundCount,
      iIndepFun (observation round kept) law)
    (hmeasurable : ∀ round < roundCount, ∀ sample,
      Measurable (observation round kept sample))
    (hbounded : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
        ∀ᵐ outcome ∂law, observation round kept sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
        law[observation round kept sample] = 1 / 2 + centeredGap)
    (hgap : upper ≤ centeredGap)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | kept ∉ indexedPruneRounds roundCount
      (adaptivePruneDecision observation lower upper delta) outcome active} ≤ delta / 2 := by
  have hschedule := adaptivePruneRoundDelta_sum_le_half delta (le_of_lt hdelta) roundCount
  calc
    law.real {outcome | kept ∉ indexedPruneRounds roundCount
        (adaptivePruneDecision observation lower upper delta) outcome active} ≤
        ∑ round ∈ Finset.range roundCount, adaptivePruneRoundDelta delta round := by
          apply indexedPruneRounds_failure_probability_of_varyingFailure law roundCount
            (adaptivePruneDecision observation lower upper delta) active kept
            (adaptivePruneRoundDelta delta) hmem
          intro round hround
          change law.real {outcome | adaptiveCompare (observation round kept)
            (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round)) lower upper
            (adaptivePruneRoundDelta delta round) outcome ≠ .upper} ≤
            adaptivePruneRoundDelta delta round
          apply adaptiveCompare_upper_failure_probability_of_ceilingBudget law
            (observation round kept) lower upper centeredGap
            (adaptivePruneRoundDelta delta round)
          · exact hindependent round hround
          · exact hmeasurable round hround
          · exact hbounded round hround
          · exact hmean round hround
          · exact hgap
          · exact hseparation
          · exact div_pos hdelta (by positivity)
          · apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (round + 2))).mpr
            have hpower : 1 ≤ (2 : ℝ) ^ (round + 2) := one_le_pow₀ (by norm_num)
            nlinarith
    _ ≤ delta / 2 := hschedule

/--
Lemma 13 specialized to OPT-Maximize's protected arm.  If the anchor is not
an `upper`-maximum, SST makes the absolute maximum's gap at least `upper`, so
the geometric Prune-retention guarantee applies to that arm directly.
-/
theorem adaptivePrune_absoluteMaximum_retention_probability_of_anchorNotEpsilonMaximum
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (roundCount : ℕ) (observation : ℕ → Arm → ℕ → Ω → ℝ)
    (active : Finset Arm) (maximum anchor : Arm)
    (preferenceGap : Arm → Arm → ℝ) (lower upper delta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hmaximumMem : maximum ∈ active)
    (hanchorNotMaximum : ¬ EpsilonMaximum preferenceGap upper anchor)
    (hindependent : ∀ round < roundCount,
      iIndepFun (observation round maximum) law)
    (hmeasurable : ∀ round < roundCount, ∀ sample,
      Measurable (observation round maximum sample))
    (hbounded : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
        ∀ᵐ outcome ∂law, observation round maximum sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
        law[observation round maximum sample] =
          1 / 2 + preferenceGap maximum anchor)
    (hdecisionMeasurable : ∀ round < roundCount,
      MeasurableSet {outcome |
        adaptivePruneDecision observation lower upper delta round maximum outcome = .upper})
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    1 - delta / 2 ≤
      law.real {outcome | maximum ∈ indexedPruneRounds roundCount
        (adaptivePruneDecision observation lower upper delta) outcome active} := by
  apply adaptivePrune_retention_probability law roundCount observation active maximum lower upper
    (preferenceGap maximum anchor) delta hmaximumMem hindependent hmeasurable hbounded hmean
    hdecisionMeasurable
  · exact le_of_lt (absoluteMaximum_gap_gt_of_not_epsilonMaximum preferenceGap upper
      hantisymmetric hsst hupperNonnegative maximum anchor hmaximum hanchorNotMaximum)
  · exact hseparation
  · exact hdelta
  · exact hdeltaLeOne

/--
Failure-event version of the protected-absolute-maximum specialization.  This
is the precise candidate-loss budget passed into OPT-Maximize's endgame.
-/
theorem adaptivePrune_absoluteMaximum_failure_probability_of_anchorNotEpsilonMaximum
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (roundCount : ℕ) (observation : ℕ → Arm → ℕ → Ω → ℝ)
    (active : Finset Arm) (maximum anchor : Arm)
    (preferenceGap : Arm → Arm → ℝ) (lower upper delta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hmaximumMem : maximum ∈ active)
    (hanchorNotMaximum : ¬ EpsilonMaximum preferenceGap upper anchor)
    (hindependent : ∀ round < roundCount,
      iIndepFun (observation round maximum) law)
    (hmeasurable : ∀ round < roundCount, ∀ sample,
      Measurable (observation round maximum sample))
    (hbounded : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
        ∀ᵐ outcome ∂law, observation round maximum sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
        law[observation round maximum sample] =
          1 / 2 + preferenceGap maximum anchor)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | maximum ∉ indexedPruneRounds roundCount
      (adaptivePruneDecision observation lower upper delta) outcome active} ≤ delta / 2 := by
  apply adaptivePrune_failure_probability law roundCount observation active maximum lower upper
    (preferenceGap maximum anchor) delta hmaximumMem hindependent hmeasurable hbounded hmean
  · exact le_of_lt (absoluteMaximum_gap_gt_of_not_epsilonMaximum preferenceGap upper
      hantisymmetric hsst hupperNonnegative maximum anchor hmaximum hanchorNotMaximum)
  · exact hseparation
  · exact hdelta
  · exact hdeltaLeOne

/--
Lemma 13's fixed-schedule high-probability retention statement with the
source's ceiling Compare budget.  Its `centeredGap` is the protected arm's
pairwise centered preference against the fixed Prune anchor.
-/
theorem fixedSamplePrune_retention_probability
    {Ω Arm : Type*} [MeasurableSpace Ω] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (roundCount : ℕ) (observation : ℕ → Arm → ℕ → Ω → ℝ)
    (active : Finset Arm) (kept : Arm)
    (lower upper centeredGap delta : ℝ)
    (hmem : kept ∈ active)
    (hindependent : ∀ round < roundCount,
      iIndepFun (observation round kept) law)
    (hmeasurable : ∀ round < roundCount, ∀ sample,
      Measurable (observation round kept sample))
    (hbounded : ∀ round < roundCount, ∀ sample < fixedSampleBudget lower upper delta,
      ∀ᵐ outcome ∂law, observation round kept sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ round < roundCount, ∀ sample < fixedSampleBudget lower upper delta,
      law[observation round kept sample] = 1 / 2 + centeredGap)
    (hdecisionMeasurable : ∀ round < roundCount,
      MeasurableSet {outcome |
        fixedSamplePruneDecision observation lower upper delta round kept outcome = .upper})
    (hgap : upper ≤ centeredGap)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    1 - (roundCount : ℝ) * delta ≤
      law.real {outcome | kept ∈
        indexedPruneRounds roundCount
          (fixedSamplePruneDecision observation lower upper delta) outcome active} := by
  apply indexedPruneRounds_retention_probability law roundCount
    (fixedSamplePruneDecision observation lower upper delta) active kept delta hmem
  · intro round hround
    exact hdecisionMeasurable round hround
  · intro round hround
    exact fixedSampleCompare_upper_failure_probability_of_ceilingBudget law
      (observation round kept) lower upper centeredGap delta
      (hindependent round hround) (hmeasurable round hround)
      (hbounded round hround) (hmean round hround) hgap hseparation hdelta hdeltaLeOne

end FalahatgarEtAl2017MaxingRanking
