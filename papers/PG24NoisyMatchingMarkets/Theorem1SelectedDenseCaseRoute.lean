import PG24NoisyMatchingMarkets.Theorem1SelectedCase1Route
import PG24NoisyMatchingMarkets.Theorem1SelectedCutoffGeometry

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/--
The canonical dense-window branch supplies the sparse lower cutoff block
required by Case 1.  The result applies the source decomposition to the
actual selected stable cutoff, with no pre-sorted college indexing.
-/
theorem theorem1_selectedStable_low_matched_mass_le_rankedDense_case1_components_iid
    {StudentType : Type u} {C : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin (C + 1)))
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    {matching : M.Matching} (hstable : M.Stable matching)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin (C + 1) -> ℝ)
    (demand : StudentType × (Fin (C + 1) -> ℝ) -> Option (Fin (C + 1)))
    (alpha beta gamma : ℝ)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) (hC_pos : 0 < C)
    (start : ℕ)
    (hstart_window :
      start + theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) ≤
        theorem3DenseGapBlockCount C
          (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
          theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma))
    (hdense : theorem1TailDenseRankWindow (theorem3RankedCutoffNat C cutoff)
      start (theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma))
      (theorem1DenseDeviationRadius C beta gamma))
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin (C + 1) -> ℝ)) (college : Fin (C + 1)),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (hchoice_mass_eq_aggregate_demand_lower :
      ∀ start : ℕ, start ≤ C ->
        choiceMass
          (studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
          demand
          (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
            cutoff (theorem3RankedCutoffNat C cutoff start)) =
          ∑ college ∈ theorem1CutoffBelowBlock
            (Finset.univ : Finset (Fin (C + 1))) cutoff
            (theorem3RankedCutoffNat C cutoff start),
            M.aggregateDemand (I.marketClearingCutoffOfStable hstable) college)
    (halpha_nonneg : 0 ≤ alpha)
    (hcapacity : ∀ college ∈ (Finset.univ : Finset (Fin (C + 1))),
      M.capacity college ≤ alpha / (C : ℝ))
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) -> ℝ) =>
          value outcome.1 ∈ region ∧
            chosenInActive demand (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
      alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
        ∫ v : ℝ,
          region.indicator
            (fun v => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (theorem1CutoffAtOrAboveBlock
                (Finset.univ : Finset (Fin (C + 1))) cutoff
                (theorem3RankedCutoffNat C cutoff start))
              v cutoff) v
          ∂valueLaw := by
  have hstart : start ≤ C := by
    calc
      start ≤ start + theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) :=
        Nat.le_add_right _ _
      _ ≤ theorem3DenseGapBlockCount C
          (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
          theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) :=
        hstart_window
      _ ≤ theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma) :=
        theorem3DenseGapBlockCount_mul_denseWindowCount_le_earlyPrefixRank
          C (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma)
      _ ≤ C := by
        have hC_one : 1 ≤ C := Nat.succ_le_iff.mpr hC_pos
        have hC_real_one : (1 : ℝ) ≤ (C : ℝ) := by
          exact_mod_cast hC_one
        have hphi3_le_one : theorem1TailPhi3 beta gamma ≤ 1 := by
          have hK_nonneg : 0 ≤ theorem1TailK beta gamma :=
            (theorem1TailK_pos hbeta hgamma).le
          linarith [theorem1Tail_one_sub_phi3_eq_K beta gamma]
        have hfloor : (theorem3EarlyPrefixRank C
            (theorem1TailPhi3 beta gamma) : ℝ) ≤
            Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) := by
          unfold theorem3EarlyPrefixRank
          exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg C) _)
        have hpower : Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) ≤
            (C : ℝ) := by
          calc
            Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) ≤
                Real.rpow (C : ℝ) 1 :=
              Real.rpow_le_rpow_of_exponent_le hC_real_one hphi3_le_one
            _ = (C : ℝ) := Real.rpow_one _
        exact_mod_cast hfloor.trans hpower
  have hsparse_nat :
      (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1))) cutoff
        (theorem3RankedCutoffNat C cutoff start)).card ≤ start := by
    simpa [theorem3RankedCutoffNat_eq_rankedCutoff C cutoff hstart] using
      (theorem1CutoffBelowBlock_card_le_rank_start C start cutoff hstart)
  have hsparse_real :
      ((theorem1CutoffBelowBlock
        (Finset.univ : Finset (Fin (C + 1))) cutoff
        (theorem3RankedCutoffNat C cutoff start)).card : ℝ) ≤
        Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) := by
    have hstart_early : start ≤ theorem3EarlyPrefixRank C
        (theorem1TailPhi3 beta gamma) := by
      calc
        start ≤ start + theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) :=
          Nat.le_add_right _ _
        _ ≤ theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
            theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) :=
          hstart_window
        _ ≤ theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma) :=
          theorem3DenseGapBlockCount_mul_denseWindowCount_le_earlyPrefixRank
            C (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma)
    have hprefix_real : (theorem3EarlyPrefixRank C
        (theorem1TailPhi3 beta gamma) : ℝ) ≤
        Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) := by
      unfold theorem3EarlyPrefixRank
      exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg C) _)
    exact le_trans (by exact_mod_cast le_trans hsparse_nat hstart_early)
      hprefix_real
  exact theorem1_selectedStable_low_matched_mass_le_case1_sparse_components_iid
    (C := C) M I K hstable studentLaw value hvalue valueLaw hvalue_marginal
    noiseLaw cutoff demand (theorem3RankedCutoffNat C cutoff start)
    alpha beta gamma hchosen_feasible
    (hchoice_mass_eq_aggregate_demand_lower start hstart)
    (by exact_mod_cast hC_pos) halpha_nonneg hsparse_real hcapacity hregion

end

end PG24NoisyMatchingMarkets
