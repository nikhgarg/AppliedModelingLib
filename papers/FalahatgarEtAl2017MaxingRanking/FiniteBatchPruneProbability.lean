import FalahatgarEtAl2017MaxingRanking.PruneProbability
import FalahatgarEtAl2017MaxingRanking.FiniteBatchAdaptiveCompareProbability

/-!
# Finite-batch Prune retention

Lemma 13 applies adaptive Compare to a protected arm in each scheduled Prune
round.  Each call reads only its finite ceiling-budgeted batch, so the
retention theorem uses finite-coordinate independence in every round.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- Lemma 13's protected-arm retention bound with finite comparison batches. -/
theorem finiteBatchAdaptivePrune_retention_probability
    {Ω Arm : Type*} [MeasurableSpace Ω] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (roundCount : ℕ) (observation : ℕ → Arm → ℕ → Ω → ℝ)
    (active : Finset Arm) (kept : Arm)
    (lower upper centeredGap delta : ℝ)
    (hmem : kept ∈ active)
    (hindependent : ∀ round < roundCount,
      iIndepFun (fun sample : Fin (fixedSampleBudget lower upper
        (adaptivePruneRoundDelta delta round)) => observation round kept sample.val) law)
    (hmeasurable : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
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
        apply finiteBatchAdaptiveCompare_upper_failure_probability_of_ceilingBudget law
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

/-- The finite-batch failure-event form of Lemma 13's protected-arm guarantee. -/
theorem finiteBatchAdaptivePrune_failure_probability
    {Ω Arm : Type*} [MeasurableSpace Ω] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (roundCount : ℕ) (observation : ℕ → Arm → ℕ → Ω → ℝ)
    (active : Finset Arm) (kept : Arm)
    (lower upper centeredGap delta : ℝ)
    (hmem : kept ∈ active)
    (hindependent : ∀ round < roundCount,
      iIndepFun (fun sample : Fin (fixedSampleBudget lower upper
        (adaptivePruneRoundDelta delta round)) => observation round kept sample.val) law)
    (hmeasurable : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
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
          apply finiteBatchAdaptiveCompare_upper_failure_probability_of_ceilingBudget law
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

end FalahatgarEtAl2017MaxingRanking
