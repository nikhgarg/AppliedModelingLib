import AppliedModelingLib.Markets.Matching.Affordability
import Mathlib.Tactic

/-!
# PG24 Theorem 4 Source-Native Demand Semantics

The extended source model defines demand as the most-preferred affordable
college.  This module makes that definition literal for a finite global
college set.  Aggregate demand is then the outcome-law mass of each singleton
demand event, rather than an independent capacity-side assumption.
-/

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w

/-- The finite set of globally affordable colleges at one cutoff and outcome. -/
noncomputable def theorem4AffordableColleges
    {Outcome : Type u} {GlobalCollege : Type v} [Fintype GlobalCollege]
    {Cutoff : Type w}
    (cutoffCoordinates : Cutoff → GlobalCollege → ℝ)
    (globalScore : Cutoff → Outcome → GlobalCollege → ℝ)
    (P : Cutoff) (outcome : Outcome) : Finset GlobalCollege :=
  Finset.univ.filter
    (fun college => cutoffCoordinates P college < globalScore P outcome college)

/--
The demand rule picks the affordable college with the least preference rank.
Lower ranks are more preferred.  A strict per-outcome rank permits arbitrary
outcome-dependent student preferences while resolving every finite tie.
-/
noncomputable def theorem4DemandFromPreferences
    {Outcome : Type u} {GlobalCollege : Type v} [Fintype GlobalCollege]
    {Cutoff : Type w}
    (preferenceRank : Outcome → GlobalCollege → ℕ)
    (cutoffCoordinates : Cutoff → GlobalCollege → ℝ)
    (globalScore : Cutoff → Outcome → GlobalCollege → ℝ)
    (P : Cutoff) (outcome : Outcome) : Option GlobalCollege :=
  (theorem4AffordableColleges cutoffCoordinates globalScore P outcome).toList.argmin
    (preferenceRank outcome)

/-- A college is affordable and has weakly best rank among affordable colleges. -/
def Theorem4MostPreferredAffordable
    {Outcome : Type u} {GlobalCollege : Type v} {Cutoff : Type w}
    (preferenceRank : Outcome → GlobalCollege → ℕ)
    (cutoffCoordinates : Cutoff → GlobalCollege → ℝ)
    (globalScore : Cutoff → Outcome → GlobalCollege → ℝ)
    (P : Cutoff) (outcome : Outcome) (college : GlobalCollege) : Prop :=
  cutoffCoordinates P college < globalScore P outcome college ∧
    ∀ other : GlobalCollege,
      cutoffCoordinates P other < globalScore P outcome other →
        preferenceRank outcome college ≤ preferenceRank outcome other

/-- The literal demand rule is unmatched exactly when no global cutoff is crossed. -/
theorem theorem4DemandFromPreferences_none_iff_no_cutoffCrossed
    {Outcome : Type u} {GlobalCollege : Type v} [Fintype GlobalCollege]
    {Cutoff : Type w}
    (preferenceRank : Outcome → GlobalCollege → ℕ)
    (cutoffCoordinates : Cutoff → GlobalCollege → ℝ)
    (globalScore : Cutoff → Outcome → GlobalCollege → ℝ)
    (P : Cutoff) (outcome : Outcome) :
    theorem4DemandFromPreferences preferenceRank cutoffCoordinates globalScore P outcome = none ↔
      ¬ cutoffCrossed (globalScore P outcome) (cutoffCoordinates P) := by
  classical
  simp [theorem4DemandFromPreferences, theorem4AffordableColleges,
    cutoffCrossed]

/-- A selected college is literally an affordable college of minimum rank. -/
theorem theorem4DemandFromPreferences_some_is_mostPreferredAffordable
    {Outcome : Type u} {GlobalCollege : Type v} [Fintype GlobalCollege]
    {Cutoff : Type w}
    (preferenceRank : Outcome → GlobalCollege → ℕ)
    (cutoffCoordinates : Cutoff → GlobalCollege → ℝ)
    (globalScore : Cutoff → Outcome → GlobalCollege → ℝ)
    (P : Cutoff) (outcome : Outcome) {college : GlobalCollege}
    (hdemand :
      theorem4DemandFromPreferences preferenceRank cutoffCoordinates globalScore P outcome =
        some college) :
    Theorem4MostPreferredAffordable preferenceRank cutoffCoordinates globalScore
      P outcome college := by
  classical
  constructor
  · have hmem :
        college ∈
          (theorem4AffordableColleges cutoffCoordinates globalScore P outcome).toList := by
      exact List.argmin_mem (by
        simpa [theorem4DemandFromPreferences] using hdemand)
    simpa [theorem4AffordableColleges] using hmem
  · intro other hother
    exact List.le_of_mem_argmin
      (l :=
        (theorem4AffordableColleges cutoffCoordinates globalScore P outcome).toList)
      (by simpa [theorem4AffordableColleges] using hother)
      (by simpa [theorem4DemandFromPreferences] using hdemand)

/-- A strict per-outcome rank makes the most-preferred affordable college unique. -/
theorem theorem4MostPreferredAffordable_unique_of_rank_injective
    {Outcome : Type u} {GlobalCollege : Type v} {Cutoff : Type w}
    (preferenceRank : Outcome → GlobalCollege → ℕ)
    (hstrict : ∀ outcome : Outcome, Function.Injective (preferenceRank outcome))
    (cutoffCoordinates : Cutoff → GlobalCollege → ℝ)
    (globalScore : Cutoff → Outcome → GlobalCollege → ℝ)
    (P : Cutoff) (outcome : Outcome) {first second : GlobalCollege}
    (hfirst :
      Theorem4MostPreferredAffordable preferenceRank cutoffCoordinates globalScore
        P outcome first)
    (hsecond :
      Theorem4MostPreferredAffordable preferenceRank cutoffCoordinates globalScore
        P outcome second) :
    first = second := by
  apply hstrict outcome
  apply le_antisymm
  · exact hfirst.2 second hsecond.1
  · exact hsecond.2 first hfirst.1

/--
Primitive source inputs for finite, outcome-dependent preference demand.

The only measurability datum is that each singleton event of the literal
demand rule is measurable.  This is a regularity condition on the source
probability model, not a capacity or demand-mass conclusion.
-/
structure PG24FinitePreferredDemand
    (Outcome : Type u) [MeasurableSpace Outcome]
    (GlobalCollege : Type v) [Fintype GlobalCollege]
    (Cutoff : Type w) where
  outcomeLaw : Measure Outcome
  preferenceRank : Outcome → GlobalCollege → ℕ
  preferenceRank_injective :
    ∀ outcome : Outcome, Function.Injective (preferenceRank outcome)
  cutoffCoordinates : Cutoff → GlobalCollege → ℝ
  globalScore : Cutoff → Outcome → GlobalCollege → ℝ
  singletonDemandMeasurable :
    ∀ P : Cutoff, ∀ college : GlobalCollege,
      MeasurableSet
        {outcome : Outcome |
          theorem4DemandFromPreferences preferenceRank cutoffCoordinates globalScore
            P outcome = some college}

namespace PG24FinitePreferredDemand

variable {Outcome : Type u} [MeasurableSpace Outcome]
variable {GlobalCollege : Type v} [Fintype GlobalCollege]
variable {Cutoff : Type w}

/-- The source-defined demand map at a cutoff. -/
noncomputable def demandAt
    (model : PG24FinitePreferredDemand Outcome GlobalCollege Cutoff) :
    Cutoff → Outcome → Option GlobalCollege :=
  theorem4DemandFromPreferences model.preferenceRank model.cutoffCoordinates
    model.globalScore

/-- Aggregate demand is the source law's singleton demand-event mass. -/
noncomputable def aggregateDemand
    (model : PG24FinitePreferredDemand Outcome GlobalCollege Cutoff) :
    Cutoff → GlobalCollege → ℝ :=
  fun P college =>
    eventMass model.outcomeLaw
      (fun outcome => model.demandAt P outcome = some college)

/-- The source aggregate-demand definition exposes its singleton event mass. -/
theorem aggregateDemand_eq_singleton_eventMass
    (model : PG24FinitePreferredDemand Outcome GlobalCollege Cutoff)
    (P : Cutoff) (college : GlobalCollege) :
    model.aggregateDemand P college =
      eventMass model.outcomeLaw
        (fun outcome => model.demandAt P outcome = some college) :=
  rfl

/-- The source-defined demand is unmatched exactly when no global cutoff is crossed. -/
theorem demandAt_none_iff_no_global_cutoff_crossing
    (model : PG24FinitePreferredDemand Outcome GlobalCollege Cutoff)
    (P : Cutoff) (outcome : Outcome) :
    model.demandAt P outcome = none ↔
      ¬ cutoffCrossed (model.globalScore P outcome) (model.cutoffCoordinates P) :=
  theorem4DemandFromPreferences_none_iff_no_cutoffCrossed
    model.preferenceRank model.cutoffCoordinates model.globalScore P outcome

/-- Every selected source demand is the unique most-preferred affordable college. -/
theorem demandAt_some_is_unique_mostPreferredAffordable
    (model : PG24FinitePreferredDemand Outcome GlobalCollege Cutoff)
    (P : Cutoff) (outcome : Outcome) {college : GlobalCollege}
    (hdemand : model.demandAt P outcome = some college) :
    Theorem4MostPreferredAffordable model.preferenceRank model.cutoffCoordinates
      model.globalScore P outcome college ∧
      ∀ other : GlobalCollege,
        Theorem4MostPreferredAffordable model.preferenceRank model.cutoffCoordinates
          model.globalScore P outcome other → other = college := by
  constructor
  · exact theorem4DemandFromPreferences_some_is_mostPreferredAffordable
      model.preferenceRank model.cutoffCoordinates model.globalScore P outcome hdemand
  · intro other hother
    symm
    exact theorem4MostPreferredAffordable_unique_of_rank_injective
      model.preferenceRank model.preferenceRank_injective model.cutoffCoordinates
      model.globalScore P outcome
      (theorem4DemandFromPreferences_some_is_mostPreferredAffordable
        model.preferenceRank model.cutoffCoordinates model.globalScore P outcome hdemand)
      hother

/-- Singleton demand events are measurable by the primitive source regularity input. -/
theorem singletonDemandMeasurable_at
    (model : PG24FinitePreferredDemand Outcome GlobalCollege Cutoff)
    (P : Cutoff) (college : GlobalCollege) :
    MeasurableSet {outcome : Outcome | model.demandAt P outcome = some college} :=
  model.singletonDemandMeasurable P college

/--
Whole-market choice mass is the sum of source-defined aggregate demand.
This is derived from disjoint singleton demand events; it is not an instance
field or an independent market-clearing premise.
-/
theorem choiceMass_eq_sum_aggregateDemand
    (model : PG24FinitePreferredDemand Outcome GlobalCollege Cutoff)
    (P : Cutoff) [IsFiniteMeasure model.outcomeLaw] :
    choiceMass model.outcomeLaw (model.demandAt P)
        (Finset.univ : Finset GlobalCollege) =
      ∑ college : GlobalCollege, model.aggregateDemand P college := by
  classical
  simpa [aggregateDemand] using
    (choiceMass_eq_sum_aggregateDemand_of_singleton_eventMass_eq
      model.outcomeLaw (model.demandAt P)
      (Finset.univ : Finset GlobalCollege)
      (fun college _ => model.singletonDemandMeasurable P college)
      (fun _ _ => rfl))

/--
The two semantic facts needed by the selected-cutoff capacity argument are
both consequences of one literal source demand model.
-/
theorem selected_cutoff_capacity_semantics
    (model : PG24FinitePreferredDemand Outcome GlobalCollege Cutoff)
    (P : Cutoff) [IsFiniteMeasure model.outcomeLaw] :
    (∀ outcome : Outcome,
      model.demandAt P outcome = none ↔
        ¬ cutoffCrossed (model.globalScore P outcome) (model.cutoffCoordinates P)) ∧
      choiceMass model.outcomeLaw (model.demandAt P)
          (Finset.univ : Finset GlobalCollege) =
        ∑ college : GlobalCollege, model.aggregateDemand P college := by
  exact ⟨fun outcome => model.demandAt_none_iff_no_global_cutoff_crossing P outcome,
    model.choiceMass_eq_sum_aggregateDemand P⟩

end PG24FinitePreferredDemand

end

end PG24NoisyMatchingMarkets
