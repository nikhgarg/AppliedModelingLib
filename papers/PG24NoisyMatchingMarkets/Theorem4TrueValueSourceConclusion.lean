import PG24NoisyMatchingMarkets.Theorem4TrueValueSourceBridge
import Mathlib.Tactic

/-!
# PG24 Theorem 4 true-value source conclusion

This theorem composes the extended source model's true-value-vector condition
with the checked student-typed fixed-eta coalition conclusion.  In particular,
the source-level common-value and score conditions are sufficient; no raw
outcome-level coalition-score premise appears in the statement.
-/

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w x

/--
The fixed-eta Theorem 4 conclusion directly from the extended source model's
student true values and approximate scores.  The threshold is chosen before
the arbitrary source economy, while `fixed_eta` is intentionally fixed before
the tolerance.
-/
theorem theorem4_trueValue_source_coalition_amplification_fixed_eta_of_longTailed
    (noiseLaw fixed_eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure fixed_eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ C : ℕ, N ≤ C →
        ∀ (StudentType : Type u) [MeasurableSpace StudentType]
          (Outcome : Type v) [MeasurableSpace Outcome]
          (GlobalCollege : Type w) [Fintype GlobalCollege]
          (Cutoff : Type x)
          (sampling :
            PG24CoalitionSourceSampling C noiseLaw fixed_eta StudentType Outcome)
          (rankOfStudent : StudentType → GlobalCollege → ℕ)
          (rankOfStudent_injective :
            ∀ student : StudentType, Function.Injective (rankOfStudent student))
          (cutoffCoordinates : Cutoff → GlobalCollege → ℝ)
          (globalScore : Cutoff → Outcome → GlobalCollege → ℝ)
          (singletonDemandMeasurable :
            ∀ P : Cutoff, ∀ college : GlobalCollege,
              MeasurableSet
                {outcome : Outcome |
                  theorem4DemandFromPreferences
                      (fun outcome college =>
                        rankOfStudent (sampling.sourceStudent outcome) college)
                      cutoffCoordinates globalScore P outcome = some college})
          (capacity : GlobalCollege → ℝ)
          (totalCapacity_eq :
            (∑ college : GlobalCollege, capacity college) = totalSupply)
          (selectedCutoff : Cutoff)
          (selectedCutoff_clearing :
            ∀ college : GlobalCollege,
              eventMass sampling.outcomeLaw
                (fun outcome =>
                  theorem4DemandFromPreferences
                      (fun outcome college =>
                        rankOfStudent (sampling.sourceStudent outcome) college)
                      cutoffCoordinates globalScore selectedCutoff outcome = some college) =
                capacity college)
          (approximateScore : Outcome → GlobalCollege → ℝ)
          (globalScore_eq_approximateScore :
            ∀ (P : Cutoff) (outcome : Outcome) (college : GlobalCollege),
              globalScore P outcome college = approximateScore outcome college)
          (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
          (trueValue : StudentType → GlobalCollege → ℝ)
          (hcoalition_trueValue :
            ∀ᵐ student ∂sampling.studentLaw,
              ∀ college : Fin (C + 1),
                trueValue student (coalitionEmbedding college) =
                  sampling.commonValue student)
          (hscore_trueValue :
            ∀ᵐ outcome ∂sampling.outcomeLaw,
              ∀ college : Fin (C + 1),
                approximateScore outcome (coalitionEmbedding college) =
                  trueValue (sampling.sourceStudent outcome)
                    (coalitionEmbedding college) +
                    sampling.coalitionNoise outcome college),
          ∃ effectiveSupply : ℝ,
          ∃ actualCoalition : Finset GlobalCollege,
          ∃ actualLargeSubset :
            Theorem4ActualCoalitionSubset coalitionEmbedding,
          ∃ regularSet : Set ℝ,
            actualCoalition = theorem4ActualCoalition coalitionEmbedding ∧
              CoalitionLargeSubset actualCoalition actualLargeSubset.actualSubset epsilon ∧
              N < actualCoalition.card ∧
              fixed_eta.real regularSetᶜ ≤ epsilon ∧
              (∀ value ∈ regularSet,
                |PG24StudentTypedSourceStableData.pMuOnActualCoalitionSubset
                    (PG24StudentTypedSourceStableData.ofTrueValueSource
                      sampling rankOfStudent rankOfStudent_injective cutoffCoordinates
                      globalScore singletonDemandMeasurable capacity totalCapacity_eq
                      selectedCutoff selectedCutoff_clearing approximateScore
                      globalScore_eq_approximateScore coalitionEmbedding trueValue
                      hcoalition_trueValue hscore_trueValue)
                    value actualLargeSubset - effectiveSupply| < epsilon) := by
  intro epsilon hepsilon_pos
  rcases PG24StudentTypedSourceStableData.theorem4_studentTyped_source_coalition_amplification_fixed_eta_of_longTailed
      noiseLaw fixed_eta hlong htotalSupply_pos htotalSupply_lt_one
      epsilon hepsilon_pos with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro C hthreshold StudentType _ Outcome _ GlobalCollege _ Cutoff sampling
    rankOfStudent rankOfStudent_injective cutoffCoordinates globalScore
    singletonDemandMeasurable capacity totalCapacity_eq selectedCutoff
    selectedCutoff_clearing approximateScore globalScore_eq_approximateScore
    coalitionEmbedding trueValue hcoalition_trueValue hscore_trueValue
  let data := PG24StudentTypedSourceStableData.ofTrueValueSource
    sampling rankOfStudent rankOfStudent_injective cutoffCoordinates globalScore
    singletonDemandMeasurable capacity totalCapacity_eq selectedCutoff
    selectedCutoff_clearing approximateScore globalScore_eq_approximateScore
    coalitionEmbedding trueValue hcoalition_trueValue hscore_trueValue
  simpa [data] using
    (hN C hthreshold StudentType Outcome GlobalCollege Cutoff data)

end

end PG24NoisyMatchingMarkets
