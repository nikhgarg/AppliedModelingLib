import PG24NoisyMatchingMarkets.Theorem4GlobalChoiceSemantics
import PG24NoisyMatchingMarkets.Theorem4GlobalCoalitionUniformResolution
import Mathlib.Tactic

open Filter Topology
open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
Global-coalition low-cutoff resolution with the extended source model's demand
semantics stated directly.  A locally affordable coalition college witnesses a
globally affordable college; since unmatched is equivalent to no global
affordability, the student is matched somewhere in the broader market.
-/
theorem eventually_theorem4_global_coalition_low_cutoff_count_of_source_demand_semantics
    {StudentSeq : ℕ → Type u} {GlobalCollegeSeq : ℕ → Type v}
    [∀ C, Fintype (GlobalCollegeSeq C)]
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (GlobalCollegeSeq C))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    {Admissible : ℕ → Type w}
    (selected : ∀ C : ℕ, Admissible C →
      { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (coalitionEmbedding : ∀ C : ℕ, Admissible C →
      Fin (C + 1) ↪ GlobalCollegeSeq C)
    (globalCutoff : ∀ C : ℕ,
      (Mseq C).Cutoff → GlobalCollegeSeq C → ℝ)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ,
      (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (globalChoice : ∀ C : ℕ,
      (Mseq C).Cutoff → OutcomeSeq C → Option (GlobalCollegeSeq C))
    (globalScore : ∀ C : ℕ,
      (Mseq C).Cutoff → OutcomeSeq C → GlobalCollegeSeq C → ℝ)
    (localCoordinates : ∀ C : ℕ, Admissible C →
      OutcomeSeq C → ℝ × (Fin (C + 1) → ℝ))
    {totalSupply tol vHigh : ℝ}
    (htol_pos : 0 < tol) (htotalSupply_lt_one : totalSupply < 1)
    (houtcome_finite : ∀ C : ℕ, ∀ P : (Mseq C).Cutoff,
      IsFiniteMeasure (outcomeLaw C P))
    (hchoice_mass_eq_aggregateDemand :
      ∀ C : ℕ, ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
        choiceMass (outcomeLaw C P) (globalChoice C P)
            (Finset.univ : Finset (GlobalCollegeSeq C)) =
          ∑ c : GlobalCollegeSeq C, (Mseq C).aggregateDemand P c)
    (hcapacity_sum : ∀ C : ℕ,
      (∑ c : GlobalCollegeSeq C, (Mseq C).capacity c) = totalSupply)
    (hlocalCoordinates_measurable : ∀ C : ℕ, ∀ a : Admissible C,
      Measurable (localCoordinates C a))
    (hlocalCoordinates_map : ∀ C : ℕ, ∀ a : Admissible C,
      Measure.map (localCoordinates C a)
        (outcomeLaw C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2)) =
          eta.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
    (hcoalition_score :
      ∀ C : ℕ, ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
        ∀ outcome : OutcomeSeq C, ∀ c : Fin (C + 1),
          globalScore C P outcome (coalitionEmbedding C a c) =
            (localCoordinates C a outcome).1 +
              (localCoordinates C a outcome).2 c)
    (hunmatched_iff_no_global_affordance :
      ∀ C : ℕ, ∀ P : (Mseq C).Cutoff, ∀ outcome : OutcomeSeq C,
        globalChoice C P outcome = none ↔
          ¬ cutoffCrossed (globalScore C P outcome) (globalCutoff C P)) :
    ∃ sigma valueFloor : ℝ,
      0 < sigma ∧ valueFloor < vHigh ∧
        ∀ᶠ C : ℕ in atTop,
          ∀ a : Admissible C,
            (lowCutoffIndexSet
              (coalitionCutoffRestriction (coalitionEmbedding C a) (globalCutoff C)
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2))
              (vHigh + theorem4HighTailQuantile noiseLaw sigma C)).card ≤
                epsilonFloorSplitIndex (tol / 2) C := by
  refine
    eventually_theorem4_global_coalition_low_cutoff_count_of_longTailed
      Mseq Iseq Kseq selected coalitionEmbedding globalCutoff noiseLaw eta hlong
      outcomeLaw globalChoice localCoordinates htol_pos htotalSupply_lt_one
      houtcome_finite hchoice_mass_eq_aggregateDemand hcapacity_sum
      hlocalCoordinates_measurable hlocalCoordinates_map ?_
  intro C a active outcome hlocal
  let P : (Mseq C).Cutoff :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := (selected C a).1) (selected C a).2
  exact
    theorem4_local_affordance_implies_global_match_of_unmatched_iff_no_global_affordance
      (coalitionEmbedding C a) (globalCutoff C P) (globalScore C P)
      (globalChoice C P) (localCoordinates C a)
      (hcoalition_score C a P) (hunmatched_iff_no_global_affordance C P)
      active
      (coalitionCutoffRestriction (coalitionEmbedding C a) (globalCutoff C) P)
      (fun _ => rfl) outcome (by simpa [P] using hlocal)

end

end PG24NoisyMatchingMarkets
