import PG24NoisyMatchingMarkets.Theorem4LiteralSourceConclusion
import Mathlib.Tactic

/-!
# PG24 Theorem 4 Student-Typed Source Adapter

This adapter makes source preferences a function of the rich student state,
not of the realized coalition-noise outcome.  It also exposes actual-coalition
subsets only together with their containment certificate.
-/

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w x

/-- The actual coalition carried by an indexed coalition embedding. -/
def theorem4ActualCoalition
    {n : ℕ} {GlobalCollege : Type u}
    (embedding : Fin n ↪ GlobalCollege) : Finset GlobalCollege :=
  theorem4EmbeddedCoalition embedding

/-- An actual subset is usable by `p_mu` only after proving that it is a coalition subset. -/
structure Theorem4ActualCoalitionSubset
    {n : ℕ} {GlobalCollege : Type u}
    (embedding : Fin n ↪ GlobalCollege) where
  actualSubset : Finset GlobalCollege
  subset_actualCoalition : actualSubset ⊆ theorem4ActualCoalition embedding

namespace Theorem4ActualCoalitionSubset

variable {n : ℕ} {GlobalCollege : Type u}
variable (embedding : Fin n ↪ GlobalCollege)

/-- Embed an indexed coalition subset as a verified actual coalition subset. -/
def ofIndexed (indexedSubset : Finset (Fin n)) :
    Theorem4ActualCoalitionSubset embedding where
  actualSubset := theorem4EmbeddedCoalitionSubset embedding indexedSubset
  subset_actualCoalition := by
    simpa [theorem4ActualCoalition] using
      theorem4EmbeddedCoalitionSubset_subset embedding indexedSubset

/-- A verified actual subset contains no college outside the embedded coalition. -/
theorem subset_embeddedCoalition
    (actualSubset : Theorem4ActualCoalitionSubset embedding) :
    actualSubset.actualSubset ⊆ theorem4EmbeddedCoalition embedding := by
  simpa [theorem4ActualCoalition] using actualSubset.subset_actualCoalition

end Theorem4ActualCoalitionSubset

/-- Pullback followed by re-embedding is exact for a verified coalition subset. -/
theorem theorem4EmbeddedCoalitionSubset_pullback_eq
    {n : ℕ} {GlobalCollege : Type u}
    (embedding : Fin n ↪ GlobalCollege) (actualSubset : Finset GlobalCollege)
    (hsubset : actualSubset ⊆ theorem4ActualCoalition embedding) :
    theorem4EmbeddedCoalitionSubset embedding
        (theorem4PullbackCoalitionSubset embedding actualSubset) =
      actualSubset := by
  classical
  ext college
  constructor
  · intro hcollege
    rcases Finset.mem_map.1 hcollege with ⟨index, hindex, rfl⟩
    simpa [theorem4PullbackCoalitionSubset] using hindex
  · intro hcollege
    have hcoalition : college ∈ theorem4EmbeddedCoalition embedding := by
      simpa [theorem4ActualCoalition] using hsubset hcollege
    rcases Finset.mem_map.1 hcoalition with ⟨index, _hindex, hindex_eq⟩
    subst college
    apply Finset.mem_map.2
    refine ⟨index, ?_, rfl⟩
    simpa [theorem4PullbackCoalitionSubset] using hcollege

/-- The embedding/pullback equality for the bundled safe subset API. -/
theorem theorem4EmbeddedCoalitionSubset_pullback_eq_ofVerified
    {n : ℕ} {GlobalCollege : Type u}
    (embedding : Fin n ↪ GlobalCollege)
    (actualSubset : Theorem4ActualCoalitionSubset embedding) :
    theorem4EmbeddedCoalitionSubset embedding
        (theorem4PullbackCoalitionSubset embedding actualSubset.actualSubset) =
      actualSubset.actualSubset :=
  theorem4EmbeddedCoalitionSubset_pullback_eq embedding actualSubset.actualSubset
    actualSubset.subset_actualCoalition

/--
Literal extended-model data whose preferences come from the source student
state.  The realized outcome may include coalition noise, but the preference
rank is definitionally insensitive to that coordinate.
-/
structure PG24StudentTypedSourceStableData
    (C : ℕ) (noiseLaw eta : Measure ℝ) (totalSupply : ℝ)
    (StudentType : Type u) [MeasurableSpace StudentType]
    (Outcome : Type v) [MeasurableSpace Outcome]
    (GlobalCollege : Type w) [Fintype GlobalCollege]
    (Cutoff : Type x) where
  sampling : PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome
  rankOfStudent : StudentType → GlobalCollege → ℕ
  rankOfStudent_injective :
    ∀ student : StudentType, Function.Injective (rankOfStudent student)
  cutoffCoordinates : Cutoff → GlobalCollege → ℝ
  globalScore : Cutoff → Outcome → GlobalCollege → ℝ
  singletonDemandMeasurable :
    ∀ P : Cutoff, ∀ college : GlobalCollege,
      MeasurableSet
        {outcome : Outcome |
          theorem4DemandFromPreferences
              (fun outcome college =>
                rankOfStudent (sampling.sourceStudent outcome) college)
              cutoffCoordinates globalScore P outcome = some college}
  capacity : GlobalCollege → ℝ
  totalCapacity_eq : (∑ college : GlobalCollege, capacity college) = totalSupply
  selectedCutoff : Cutoff
  selectedCutoff_clearing :
    ∀ college : GlobalCollege,
      eventMass sampling.outcomeLaw
        (fun outcome =>
          theorem4DemandFromPreferences
              (fun outcome college =>
                rankOfStudent (sampling.sourceStudent outcome) college)
              cutoffCoordinates globalScore selectedCutoff outcome = some college) =
        capacity college
  approximateScore : Outcome → GlobalCollege → ℝ
  globalScore_eq_approximateScore :
    ∀ (P : Cutoff) (outcome : Outcome) (college : GlobalCollege),
      globalScore P outcome college = approximateScore outcome college
  coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege
  coalition_score_ae :
    ∀ᵐ outcome ∂sampling.outcomeLaw,
      ∀ college : Fin (C + 1),
        approximateScore outcome (coalitionEmbedding college) =
          (sampling.localCoordinates outcome).1 +
            (sampling.localCoordinates outcome).2 college

namespace PG24StudentTypedSourceStableData

variable {C : ℕ} {noiseLaw eta : Measure ℝ} {totalSupply : ℝ}
variable {StudentType : Type u} [MeasurableSpace StudentType]
variable {Outcome : Type v} [MeasurableSpace Outcome]
variable {GlobalCollege : Type w} [Fintype GlobalCollege]
variable {Cutoff : Type x}

/-- The finite preferred-demand model induced by source-student preferences. -/
noncomputable def demand
    (data :
      PG24StudentTypedSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    PG24FinitePreferredDemand Outcome GlobalCollege Cutoff where
  outcomeLaw := data.sampling.outcomeLaw
  preferenceRank := fun outcome college =>
    data.rankOfStudent (data.sampling.sourceStudent outcome) college
  preferenceRank_injective := by
    intro outcome
    exact data.rankOfStudent_injective (data.sampling.sourceStudent outcome)
  cutoffCoordinates := data.cutoffCoordinates
  globalScore := data.globalScore
  singletonDemandMeasurable := data.singletonDemandMeasurable

/-- The constructed rank is exactly the source-student rank at every outcome. -/
theorem demand_preferenceRank_apply
    (data :
      PG24StudentTypedSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (outcome : Outcome) (college : GlobalCollege) :
    data.demand.preferenceRank outcome college =
      data.rankOfStudent (data.sampling.sourceStudent outcome) college :=
  rfl

/-- The constructed demand rank factors through `sampling.sourceStudent`. -/
theorem demand_preferenceRank_factors_through_sourceStudent
    (data :
      PG24StudentTypedSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    data.demand.preferenceRank =
      fun outcome college =>
        data.rankOfStudent (data.sampling.sourceStudent outcome) college :=
  rfl

/-- Construct literal source data without allowing outcome/noise-dependent preferences. -/
noncomputable def toLiteralSourceStableData
    (data :
      PG24StudentTypedSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    PG24LiteralSourceStableData C noiseLaw eta totalSupply
      StudentType Outcome GlobalCollege Cutoff where
  demand := data.demand
  sampling := data.sampling
  sampling_outcomeLaw_eq := rfl
  capacity := data.capacity
  totalCapacity_eq := data.totalCapacity_eq
  selectedCutoff := data.selectedCutoff
  selectedCutoff_clearing := by
    intro college
    simpa [demand, PG24FinitePreferredDemand.aggregateDemand,
      PG24FinitePreferredDemand.demandAt] using
      data.selectedCutoff_clearing college
  approximateScore := data.approximateScore
  demand_globalScore_eq_approximateScore := data.globalScore_eq_approximateScore
  coalitionEmbedding := data.coalitionEmbedding
  coalition_score_ae := data.coalition_score_ae

/-- The literal adapter preserves the source-student preference factorization. -/
theorem toLiteralSourceStableData_preferenceRank_apply
    (data :
      PG24StudentTypedSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (outcome : Outcome) (college : GlobalCollege) :
    data.toLiteralSourceStableData.demand.preferenceRank outcome college =
      data.rankOfStudent (data.sampling.sourceStudent outcome) college :=
  data.demand_preferenceRank_apply outcome college

/-- Safe actual-carrier `p_mu`: the subset is bundled with its coalition containment proof. -/
noncomputable def pMuOnActualCoalitionSubset
    (data :
      PG24StudentTypedSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (value : ℝ)
    (actualSubset : Theorem4ActualCoalitionSubset data.coalitionEmbedding) : ℝ :=
  data.toLiteralSourceStableData.toExtendedCoalitionSourceStableInstance.pMu value
    (theorem4PullbackCoalitionSubset data.coalitionEmbedding
      actualSubset.actualSubset)

/-- The safe actual-carrier API agrees with indexed `p_mu` on embedded subsets. -/
theorem pMuOnActualCoalitionSubset_ofIndexed_eq_indexed
    (data :
      PG24StudentTypedSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (value : ℝ) (indexedSubset : Finset (Fin (C + 1))) :
    data.pMuOnActualCoalitionSubset value
        (Theorem4ActualCoalitionSubset.ofIndexed data.coalitionEmbedding
          indexedSubset) =
      data.toLiteralSourceStableData.toExtendedCoalitionSourceStableInstance.pMu
        value indexedSubset := by
  change
    data.toLiteralSourceStableData.toExtendedCoalitionSourceStableInstance.pMu value
        (theorem4PullbackCoalitionSubset data.coalitionEmbedding
          (theorem4EmbeddedCoalitionSubset data.coalitionEmbedding indexedSubset)) =
      data.toLiteralSourceStableData.toExtendedCoalitionSourceStableInstance.pMu
        value indexedSubset
  rw [theorem4PullbackCoalitionSubset_embedded_eq]

/-- A safe actual subset is recovered exactly after pullback and re-embedding. -/
theorem embedded_pullback_actualSubset_eq
    (data :
      PG24StudentTypedSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (actualSubset : Theorem4ActualCoalitionSubset data.coalitionEmbedding) :
    theorem4EmbeddedCoalitionSubset data.coalitionEmbedding
        (theorem4PullbackCoalitionSubset data.coalitionEmbedding
          actualSubset.actualSubset) = actualSubset.actualSubset :=
  theorem4EmbeddedCoalitionSubset_pullback_eq_ofVerified
    data.coalitionEmbedding actualSubset

/--
The fixed-eta theorem specialized to literal data whose preferences factor
through the source student state and whose actual subset is containment-safe.
-/
theorem theorem4_studentTyped_source_coalition_amplification_fixed_eta_of_longTailed
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
          (data :
            PG24StudentTypedSourceStableData C noiseLaw fixed_eta totalSupply
              StudentType Outcome GlobalCollege Cutoff),
          ∃ effectiveSupply : ℝ,
          ∃ actualCoalition : Finset GlobalCollege,
          ∃ actualLargeSubset :
            Theorem4ActualCoalitionSubset data.coalitionEmbedding,
          ∃ regularSet : Set ℝ,
            actualCoalition = theorem4ActualCoalition data.coalitionEmbedding ∧
              CoalitionLargeSubset actualCoalition actualLargeSubset.actualSubset epsilon ∧
              N < actualCoalition.card ∧
              fixed_eta.real regularSetᶜ ≤ epsilon ∧
              (∀ value ∈ regularSet,
                |data.pMuOnActualCoalitionSubset value actualLargeSubset -
                    effectiveSupply| < epsilon) := by
  intro epsilon hepsilon_pos
  rcases theorem4_literal_source_coalition_amplification_fixed_eta_of_longTailed
      noiseLaw fixed_eta hlong htotalSupply_pos htotalSupply_lt_one
      epsilon hepsilon_pos with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro C hthreshold StudentType _ Outcome _ GlobalCollege _ Cutoff data
  rcases hN C hthreshold StudentType Outcome GlobalCollege Cutoff
      data.toLiteralSourceStableData with
    ⟨effectiveSupply, indexedLargeSubset, actualCoalition, actualLargeSubset,
      regularSet, hcoalition_eq, hlargeSubset_eq, hlarge, hcard,
      hregular, hclose⟩
  refine ⟨effectiveSupply, theorem4ActualCoalition data.coalitionEmbedding,
    Theorem4ActualCoalitionSubset.ofIndexed data.coalitionEmbedding
      indexedLargeSubset,
    regularSet, rfl, ?_, ?_, hregular, ?_⟩
  · simpa [theorem4ActualCoalition,
      Theorem4ActualCoalitionSubset.ofIndexed, hcoalition_eq,
      hlargeSubset_eq] using hlarge
  · simpa [theorem4ActualCoalition, hcoalition_eq] using hcard
  · intro value hvalue
    rw [pMuOnActualCoalitionSubset_ofIndexed_eq_indexed]
    have hclose' := hclose value hvalue
    rw [hlargeSubset_eq,
      data.toLiteralSourceStableData.pMuOnActualSubset_embedded_eq_indexed
        value indexedLargeSubset] at hclose'
    exact hclose'

end PG24StudentTypedSourceStableData

end

end PG24NoisyMatchingMarkets
