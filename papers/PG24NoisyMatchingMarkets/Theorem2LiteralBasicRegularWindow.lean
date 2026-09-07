import PG24NoisyMatchingMarkets.Theorem2TwoScaleAmplificationClosure
import PG24NoisyMatchingMarkets.Theorem4LiteralSourceStableAdapter
import Mathlib.Tactic

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

/--
One basic-model source instance for the two-scale argument.  The literal demand
model supplies choice semantics; the remaining fields are the paper's value,
sampling, coordinate, and capacity-regularity inputs.
-/
structure PG24LiteralBasicTwoScaleInstance
    (C : ℕ) (noiseLaw eta : Measure ℝ) (totalSupply alpha : ℝ)
    (StudentType : Type u) [MeasurableSpace StudentType]
    (Cutoff : Type v) where
  studentLaw : Measure StudentType
  studentLaw_isProbability : IsProbabilityMeasure studentLaw
  value : StudentType → ℝ
  value_measurable : Measurable value
  value_marginal : Measure.map value studentLaw = eta
  literal :
    PG24LiteralSourceStableData C noiseLaw eta totalSupply
      StudentType (StudentType × (Fin (C + 1) → ℝ)) (Fin (C + 1)) Cutoff
  sampling_outcomeLaw_eq_iid :
    literal.sampling.outcomeLaw =
      studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
  coalitionEmbedding_id : ∀ c : Fin (C + 1), literal.coalitionEmbedding c = c
  basic_score :
    ∀ (P : Cutoff) (outcome : StudentType × (Fin (C + 1) → ℝ))
      (college : Fin (C + 1)),
      literal.demand.globalScore P outcome college = value outcome.1 + outcome.2 college
  capacity_regular : capacityRegular literal.capacity alpha (C + 1)

namespace PG24FinitePreferredDemand

/-- Literal finite-preference demand gives the aggregate-demand identity on every block. -/
theorem choiceMass_eq_sum_aggregateDemand_on
    {Outcome : Type u} [MeasurableSpace Outcome]
    {GlobalCollege : Type v} [Fintype GlobalCollege]
    {Cutoff : Type w}
    (model : PG24FinitePreferredDemand Outcome GlobalCollege Cutoff)
    (P : Cutoff) (active : Finset GlobalCollege) [IsFiniteMeasure model.outcomeLaw] :
    choiceMass model.outcomeLaw (model.demandAt P) active =
      ∑ college ∈ active, model.aggregateDemand P college := by
  classical
  simpa [aggregateDemand] using
    (choiceMass_eq_sum_aggregateDemand_of_singleton_eventMass_eq
      model.outcomeLaw (model.demandAt P) active
      (fun college _ => model.singletonDemandMeasurable P college)
      (fun _ _ => rfl))

end PG24FinitePreferredDemand

namespace PG24LiteralBasicTwoScaleInstance

variable {C : ℕ} {noiseLaw eta : Measure ℝ} {totalSupply alpha : ℝ}
variable {StudentType : Type u} [MeasurableSpace StudentType]
variable {Cutoff : Type v}

/-- The selected basic cutoff, in the canonical `Fin (C+1)` coordinates. -/
noncomputable def selectedCutoffVector
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff) : Fin (C + 1) → ℝ :=
  inst.literal.demand.cutoffCoordinates inst.literal.selectedCutoff

theorem selectedCutoffVector_eq_localCutoff
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff) :
    inst.selectedCutoffVector =
    inst.literal.toExtendedCoalitionSourceStableInstance.localCutoff := by
  funext c
  change
    inst.literal.demand.cutoffCoordinates inst.literal.selectedCutoff c =
      inst.literal.demand.cutoffCoordinates inst.literal.selectedCutoff
        (inst.literal.coalitionEmbedding c)
  rw [inst.coalitionEmbedding_id c]

theorem demandOutcomeLaw_eq_iid
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff) :
    inst.literal.demand.outcomeLaw =
      inst.studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) := by
  calc
    inst.literal.demand.outcomeLaw = inst.literal.sampling.outcomeLaw :=
      inst.literal.sampling_outcomeLaw_eq.symm
    _ = inst.studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) :=
      inst.sampling_outcomeLaw_eq_iid

theorem selected_choiceMass_eq_aggregateDemand
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    (active : Finset (Fin (C + 1))) :
    choiceMass
        (inst.studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (inst.literal.demand.demandAt inst.literal.selectedCutoff) active =
      ∑ college ∈ active,
        inst.literal.demand.aggregateDemand inst.literal.selectedCutoff college := by
  letI : IsProbabilityMeasure inst.literal.demand.outcomeLaw :=
    inst.literal.demandOutcomeProbability
  simpa [inst.demandOutcomeLaw_eq_iid] using
    (inst.literal.demand.choiceMass_eq_sum_aggregateDemand_on
      inst.literal.selectedCutoff active)

theorem selected_demand_none_iff_no_crossed
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    (outcome : StudentType × (Fin (C + 1) → ℝ)) :
    inst.literal.demand.demandAt inst.literal.selectedCutoff outcome = none ↔
      ¬ cutoffCrossedOn (Finset.univ : Finset (Fin (C + 1)))
        (noisyScore (inst.value outcome.1) outcome.2) inst.selectedCutoffVector := by
  rw [cutoffCrossedOn_univ_iff_cutoffCrossed]
  have hscore :
      inst.literal.demand.globalScore inst.literal.selectedCutoff outcome =
        noisyScore (inst.value outcome.1) outcome.2 := by
    funext college
    simpa [noisyScore] using
      (inst.basic_score inst.literal.selectedCutoff outcome college)
  simpa [selectedCutoffVector, hscore] using
    (inst.literal.demand.demandAt_none_iff_no_global_cutoff_crossing
      inst.literal.selectedCutoff outcome)

theorem selected_demand_feasible
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    (outcome : StudentType × (Fin (C + 1) → ℝ))
    (college : Fin (C + 1))
    (hdemand :
      inst.literal.demand.demandAt inst.literal.selectedCutoff outcome = some college) :
    inst.selectedCutoffVector college < inst.value outcome.1 + outcome.2 college := by
  have haffordable :=
    (inst.literal.demand.demandAt_some_is_unique_mostPreferredAffordable
      inst.literal.selectedCutoff outcome hdemand).1.1
  simpa [selectedCutoffVector, inst.basic_score] using haffordable

theorem selected_clearing
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff) :
    ∀ college : Fin (C + 1),
      inst.literal.demand.aggregateDemand inst.literal.selectedCutoff college =
      inst.literal.capacity college :=
  inst.literal.selectedCutoff_clearing

/-- A semantic non-low block certificate bounds the complementary low block. -/
theorem lowCutoffIndexSet_card_le_of_coalitionLargeSubset_nonLow
    {C : ℕ} {cutoff : Fin (C + 1) → ℝ} {floor delta : ℝ}
    (hlarge :
      CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
        (nonLowCutoffIndexSet cutoff floor) delta) :
    ((lowCutoffIndexSet cutoff floor).card : ℝ) ≤
      delta * ((C + 1 : ℕ) : ℝ) := by
  classical
  have hlow_subset :
      lowCutoffIndexSet cutoff floor ⊆ (Finset.univ : Finset (Fin (C + 1))) := by
    intro c _hc
    simp
  have hcard_nat :
      (Finset.univ : Finset (Fin (C + 1))).card =
        (lowCutoffIndexSet cutoff floor).card +
          (nonLowCutoffIndexSet cutoff floor).card := by
    rw [nonLowCutoffIndexSet]
    have h :=
      Finset.card_sdiff_add_card_eq_card
        (s := lowCutoffIndexSet cutoff floor)
        (t := (Finset.univ : Finset (Fin (C + 1)))) hlow_subset
    rw [add_comm] at h
    exact h.symm
  have hcard_real :
      ((Finset.univ : Finset (Fin (C + 1))).card : ℝ) =
        ((lowCutoffIndexSet cutoff floor).card : ℝ) +
          ((nonLowCutoffIndexSet cutoff floor).card : ℝ) := by
    exact_mod_cast hcard_nat
  have hcomplement :
      ((lowCutoffIndexSet cutoff floor).card : ℝ) /
          ((Finset.univ : Finset (Fin (C + 1))).card : ℝ) =
        1 -
          ((nonLowCutoffIndexSet cutoff floor).card : ℝ) /
            ((Finset.univ : Finset (Fin (C + 1))).card : ℝ) := by
    have hden_ne :
        ((Finset.univ : Finset (Fin (C + 1))).card : ℝ) ≠ 0 :=
      ne_of_gt hlarge.coalition_card_pos
    field_simp [hden_ne]
    linarith
  have hlow_fraction :
      ((lowCutoffIndexSet cutoff floor).card : ℝ) /
          ((Finset.univ : Finset (Fin (C + 1))).card : ℝ) < delta := by
    rw [hcomplement]
    linarith [hlarge.large_ratio]
  have hlow_raw :
      ((lowCutoffIndexSet cutoff floor).card : ℝ) <
        delta * ((Finset.univ : Finset (Fin (C + 1))).card : ℝ) :=
    (div_lt_iff₀ hlarge.coalition_card_pos).mp hlow_fraction
  have hden_eq :
      ((Finset.univ : Finset (Fin (C + 1))).card : ℝ) =
        ((C + 1 : ℕ) : ℝ) := by
    simp
  rw [hden_eq] at hlow_raw
  exact le_of_lt hlow_raw

/--
The fixed-`C` two-scale window for a literal basic-model instance.  The
finite-preference demand rule supplies the choice-mass identities, no-choice
semantics, feasibility, and clearing used by the generic argument.
-/
theorem theorem2_twoScaleRegularWindow_of_literalBasic_checked_bounds
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    (small large : Finset (Fin (C + 1)))
    (hdisjoint : Disjoint small large)
    (hcover : small ∪ large = (Finset.univ : Finset (Fin (C + 1))))
    {largeRegion smallRegion : Set ℝ}
    {delta endpoint sigma vLow vHigh vStar v : ℝ}
    (hlargeRegion_meas : MeasurableSet largeRegion)
    (hlargeRegion_mass : 1 - delta ≤ eta.real largeRegion)
    (hlargeRegion_ge : ∀ w : ℝ, w ∈ largeRegion -> vLow ≤ w)
    (hlargeRegion_le_high : ∀ w : ℝ, w ∈ largeRegion -> w ≤ vHigh)
    (hsmallRegion_meas : MeasurableSet smallRegion)
    (hsmallRegion_mass : Real.sqrt delta ≤ eta.real smallRegion)
    (hsmallRegion_ge : ∀ w : ℝ, w ∈ smallRegion -> vStar ≤ w)
    (hsmallRegion_le_high : ∀ w : ℝ, w ∈ smallRegion -> w ≤ vHigh)
    (hdelta_pos : 0 < delta)
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_delta_lt_one : totalSupply + delta < 1)
    (hdenom_nonneg :
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hendpoint_nonneg : 0 ≤ endpoint) (hsigma_nonneg : 0 ≤ sigma)
    (hv_low : vLow ≤ v) (hv_high : v ≤ vHigh) (hv_star : v ≤ vStar)
    (hfailure_ratio :
      ∀ c ∈ large,
        Real.exp (-(2 * endpoint * sigma / ((C + 1 : ℕ) : ℝ))) ≤
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (inst.selectedCutoffVector c - vHigh)) /
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (inst.selectedCutoffVector c - vLow)))
    (hlow_failure_pos :
      ∀ c ∈ large,
        0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (inst.selectedCutoffVector c - vLow))
    (hlow_failure_le_one :
      ∀ c ∈ large,
        1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (inst.selectedCutoffVector c - vLow) ≤ 1)
    (hsmall_card : (small.card : ℝ) ≤ delta * ((C + 1 : ℕ) : ℝ))
    (halpha_nonneg : 0 ≤ alpha)
    (hden_pos :
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma) :
    theorem2TwoScaleRegularWindow totalSupply alpha delta endpoint sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) v inst.selectedCutoffVector) := by
  letI : IsProbabilityMeasure inst.studentLaw := inst.studentLaw_isProbability
  have hn_pos : 0 < ((C + 1 : ℕ) : ℝ) := by
    positivity
  exact theorem2_twoScaleCutoffRegularWindow_of_sourceModel_checked_bounds
    inst.studentLaw inst.value inst.value_measurable eta inst.value_marginal
    noiseLaw small large hdisjoint hcover inst.selectedCutoffVector
    hlargeRegion_meas hlargeRegion_mass hlargeRegion_ge hlargeRegion_le_high
    hsmallRegion_meas hsmallRegion_mass hsmallRegion_ge hsmallRegion_le_high
    hdelta_pos htotalSupply_nonneg htotalSupply_delta_lt_one hdenom_nonneg
    hendpoint_nonneg hsigma_nonneg hn_pos hv_low hv_high hv_star
    hfailure_ratio hlow_failure_pos hlow_failure_le_one
    (inst.literal.demand.demandAt inst.literal.selectedCutoff)
    inst.selected_demand_none_iff_no_crossed inst.selected_demand_feasible
    (inst.literal.demand.aggregateDemand inst.literal.selectedCutoff)
    inst.literal.capacity
    (inst.selected_choiceMass_eq_aggregateDemand Finset.univ)
    (inst.selected_choiceMass_eq_aggregateDemand small)
    (inst.selected_choiceMass_eq_aggregateDemand large)
    inst.selected_clearing inst.literal.totalCapacity_eq hsmall_card
    halpha_nonneg inst.capacity_regular hden_pos

end PG24LiteralBasicTwoScaleInstance

end

end PG24NoisyMatchingMarkets
