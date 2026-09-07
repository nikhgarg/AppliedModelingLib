import PG24NoisyMatchingMarkets.Theorem4SourceDemandSemantics
import PG24NoisyMatchingMarkets.Theorem4SourceStableInstance
import Mathlib.Tactic

/-!
# PG24 Theorem 4 Literal Source-to-Stable Adapter

This adapter constructs the selected stable source instance used by the
extended theorem from literal finite-preference demand.  Its aggregate demand
is a singleton demand-event mass, and clearing is exactly equality of that
mass to capacity at every global college.
-/

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w x

/--
Primitive extended-model data at one explicit selected cutoff.

`approximateScore` is intentionally independent of the cutoff.  The equality
to the reusable demand model's score makes that source fact available when
the generic cutoff interface is instantiated below.
-/
structure PG24LiteralSourceStableData
    (C : ℕ) (noiseLaw eta : Measure ℝ) (totalSupply : ℝ)
    (StudentType : Type u) [MeasurableSpace StudentType]
    (Outcome : Type v) [MeasurableSpace Outcome]
    (GlobalCollege : Type w) [Fintype GlobalCollege]
    (Cutoff : Type x) where
  demand : PG24FinitePreferredDemand Outcome GlobalCollege Cutoff
  sampling : PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome
  sampling_outcomeLaw_eq : sampling.outcomeLaw = demand.outcomeLaw
  capacity : GlobalCollege → ℝ
  totalCapacity_eq : (∑ college : GlobalCollege, capacity college) = totalSupply
  selectedCutoff : Cutoff
  selectedCutoff_clearing :
    ∀ college : GlobalCollege,
      demand.aggregateDemand selectedCutoff college = capacity college
  approximateScore : Outcome → GlobalCollege → ℝ
  demand_globalScore_eq_approximateScore :
    ∀ (P : Cutoff) (outcome : Outcome) (college : GlobalCollege),
      demand.globalScore P outcome college = approximateScore outcome college
  coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege
  coalition_score_ae :
    ∀ᵐ outcome ∂sampling.outcomeLaw,
      ∀ college : Fin (C + 1),
        approximateScore outcome (coalitionEmbedding college) =
          (sampling.localCoordinates outcome).1 +
            (sampling.localCoordinates outcome).2 college

namespace PG24LiteralSourceStableData

variable {C : ℕ} {noiseLaw eta : Measure ℝ} {totalSupply : ℝ}
variable {StudentType : Type u} [MeasurableSpace StudentType]
variable {Outcome : Type v} [MeasurableSpace Outcome]
variable {GlobalCollege : Type w} [Fintype GlobalCollege]
variable {Cutoff : Type x}

/-- Exact source clearing: each singleton demand-event mass fills capacity. -/
def marketClearing
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (P : Cutoff) : Prop :=
  ∀ college : GlobalCollege,
    data.demand.aggregateDemand P college = data.capacity college

/-- A source matching is stable precisely when it is clearing cutoff demand. -/
def isStable
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (matching : Outcome → Option GlobalCollege) : Prop :=
  ∃ P : Cutoff,
    data.marketClearing P ∧ matching = data.demand.demandAt P

/-- The literal source cutoff market with event-mass aggregate demand. -/
noncomputable def sourceMarket
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    PG24SourceCutoffMarket Outcome GlobalCollege Cutoff where
  demandAt := data.demand.demandAt
  aggregateDemand := data.demand.aggregateDemand
  capacity := data.capacity
  isStable := data.isStable
  marketClearing := data.marketClearing
  representedByCutoff := fun matching P => matching = data.demand.demandAt P

/-- Stable matchings and source clearing are definitionally connected. -/
theorem stable_iff_exists_marketClearing_cutoff
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (matching : Outcome → Option GlobalCollege) :
    data.sourceMarket.toCutoffMarket.Stable matching ↔
      ∃ P : Cutoff,
        data.sourceMarket.toCutoffMarket.MarketClearing P ∧
          data.sourceMarket.toCutoffMarket.RepresentedByCutoff matching P := by
  rfl

/-- The literal source market satisfies the generic stable/cutoff interface. -/
noncomputable def supplyDemand
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    SupplyDemandInterface data.sourceMarket.toCutoffMarket where
  stable_iff_exists_marketClearing_cutoff :=
    data.stable_iff_exists_marketClearing_cutoff
  marketClearing_induces_stable := by
    intro P hclearing
    refine ⟨data.demand.demandAt P, ?_, ?_⟩
    · exact ⟨P, hclearing, rfl⟩
    · rfl

/-- Exact clearing supplies the generic capacity interface without a new axiom. -/
noncomputable def clearingCapacity
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    MarketClearingCapacityInterface data.sourceMarket.toCutoffMarket where
  marketClearing_aggregateDemand_eq_capacity := by
    intro P hclearing college
    exact hclearing college

/-- The selected source matching is the literal demand rule at the explicit cutoff. -/
noncomputable def selectedMatching
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    Outcome → Option GlobalCollege :=
  data.demand.demandAt data.selectedCutoff

/-- The supplied selected cutoff is clearing in the literal source market. -/
theorem selectedCutoff_marketClearing
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    data.sourceMarket.toCutoffMarket.MarketClearing data.selectedCutoff :=
  data.selectedCutoff_clearing

/-- The literal selected demand rule is stable by definition. -/
theorem selectedMatching_stable
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    data.sourceMarket.toCutoffMarket.Stable data.selectedMatching :=
  ⟨data.selectedCutoff, data.selectedCutoff_clearing, rfl⟩

/-- The selected matching is represented by its explicit selected cutoff. -/
theorem selectedMatching_represents_selectedCutoff
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    data.sourceMarket.toCutoffMarket.RepresentedByCutoff
      data.selectedMatching data.selectedCutoff :=
  rfl

/-- The source sampling law is finite at the demand model's identical outcome law. -/
theorem demandOutcomeProbability
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    IsProbabilityMeasure data.demand.outcomeLaw := by
  rw [← data.sampling_outcomeLaw_eq]
  exact data.sampling.outcomeLaw_isProbability

/--
The whole-market selected choice mass is derived from the literal singleton
demand events and then transported across the source-law equality.
-/
theorem selected_choiceMass_eq_aggregateDemand
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    choiceMass data.sampling.outcomeLaw data.selectedMatching
        (Finset.univ : Finset GlobalCollege) =
      ∑ college : GlobalCollege,
        data.sourceMarket.aggregateDemand data.selectedCutoff college := by
  letI : IsProbabilityMeasure data.demand.outcomeLaw := data.demandOutcomeProbability
  simpa [sourceMarket, selectedMatching, data.sampling_outcomeLaw_eq] using
    (data.demand.choiceMass_eq_sum_aggregateDemand data.selectedCutoff)

/--
The literal selected demand rule is unmatched exactly when no cutoff-independent
source score crosses the selected global cutoff.
-/
theorem demand_none_iff_no_global_cutoff_crossing
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (outcome : Outcome) :
    data.sourceMarket.demandAt data.selectedCutoff outcome = none ↔
      ¬ cutoffCrossed (data.approximateScore outcome)
        (data.demand.cutoffCoordinates data.selectedCutoff) := by
  have hscore :
      data.demand.globalScore data.selectedCutoff outcome =
        data.approximateScore outcome := by
    funext college
    exact data.demand_globalScore_eq_approximateScore
      data.selectedCutoff outcome college
  simpa [sourceMarket, hscore] using
    (data.demand.demandAt_none_iff_no_global_cutoff_crossing
      data.selectedCutoff outcome)

/--
Construct the existing selected stable-instance surface from literal source
demand.  Its two former semantic bridge fields are filled by the theorems
above, rather than supplied as inputs.
-/
noncomputable def toExtendedCoalitionSourceStableInstance
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    PG24ExtendedCoalitionSourceStableInstance C noiseLaw eta totalSupply
      StudentType Outcome GlobalCollege Cutoff where
  sourceMarket := data.sourceMarket
  supplyDemand := data.supplyDemand
  clearingCapacity := data.clearingCapacity
  sampling := data.sampling
  selectedMatching := data.selectedMatching
  selectedStable := data.selectedMatching_stable
  selectedCutoff := data.selectedCutoff
  selectedCutoff_marketClearing := data.selectedCutoff_marketClearing
  selectedCutoff_represents := data.selectedMatching_represents_selectedCutoff
  selectedMatching_eq_demandAt := by
    intro outcome
    rfl
  selected_choiceMass_eq_aggregateDemand :=
    data.selected_choiceMass_eq_aggregateDemand
  totalCapacity_eq := data.totalCapacity_eq
  cutoffCoordinates := data.demand.cutoffCoordinates
  globalScore := fun _ => data.approximateScore
  coalitionEmbedding := data.coalitionEmbedding
  coalition_score_ae := data.coalition_score_ae
  demand_none_iff_no_global_cutoff_crossing := by
    intro outcome
    exact data.demand_none_iff_no_global_cutoff_crossing outcome

end PG24LiteralSourceStableData

end

end PG24NoisyMatchingMarkets
