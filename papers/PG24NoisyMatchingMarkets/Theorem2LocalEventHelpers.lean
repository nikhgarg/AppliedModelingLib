import PG24NoisyMatchingMarkets.Assumptions

/-!
# PG24 Theorem 2 local-event helpers

This module keeps the amplification appendix's local-event obligations in a
standalone proof-support file.  It does not state the final Theorem 2
conclusion; instead it derives the selected-stable local probability-event
clauses used by the existing Theorem 2 route from the paper's bundled
large/small interval-event source package.
-/

open Filter MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/--
The selected-stable local probability-event clauses consumed by the checked
Theorem 2 amplification route.

This is the semantic target obtained from the source's local interval/event
construction in `source_tex/proof-amplifying.tex`: the large-firm interval
integral gives the low-endpoint mass bound, the high-endpoint event gives the
large-block choice-mass bound, and the small-firm interval integral gives the
small-block matched-event bound.
-/
def Theorem2SelectedStableLocalProbabilityEventSourceClauses
    {StudentSeq : ℕ → Type u}
    (_η : Measure ℝ)
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (totalSupply : ℝ) : Prop :=
  ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
    0 <
      1 - totalSupply - epsilon -
        (1 - Real.exp (-(2 * epsilon * sigma))) →
    ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
      ∃ largeIntervalEvent smallMatchedIntervalEvent :
          ∀ C : ℕ,
            { μ : (Mseq C).Matching // (Mseq C).Stable μ } →
              OutcomeSeq C → Prop,
      vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
            lowerCutoff C ≤
            cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := μ.1) μ.2) c) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ _μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff C - vHigh) ≤
              sigma / ((C + 1 : ℕ) : ℝ)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          (1 - epsilon) *
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2)) ≤
            AppliedModelingLib.Matching.eventMass
              (outcomeLaw C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (largeIntervalEvent C μ)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ ω : OutcomeSeq C,
            largeIntervalEvent C μ ω →
              AppliedModelingLib.Matching.chosenInActive
                (chosenCollege C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2))
                (Finset.univ : Finset (Fin (C + 1))) ω) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          AppliedModelingLib.Matching.choiceMass
              (outcomeLaw C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (chosenCollege C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) -
              epsilon ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
              vHigh
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          Real.sqrt epsilon *
              (1 - totalSupply - epsilon -
                (1 - Real.exp (-(2 * epsilon * sigma)))) *
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                vStar
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2)) ≤
            AppliedModelingLib.Matching.eventMass
              (outcomeLaw C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (smallMatchedIntervalEvent C μ)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ ω : OutcomeSeq C,
            smallMatchedIntervalEvent C μ ω →
              AppliedModelingLib.Matching.chosenInActive
                (chosenCollege C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2))
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                ω)

/--
The source local interval/event package implies the selected-stable local
probability-event clauses used downstream by Theorem 2.

Source anchors:
* `proof-amplifying.tex:174-181` for the large-firm interval/capacity
  low-endpoint bound.
* `proof-amplifying.tex:183-193` and `:194-207` for the high-endpoint
  large-block bound.
* `proof-amplifying.tex:220-250` for the small-firm interval integral and
  capacity comparison.
-/
theorem theorem2_selectedStable_local_probabilityEvent_source_clauses_of_local_interval_event_clauses
    {StudentSeq : ℕ → Type u}
    {η : Measure ℝ} [IsProbabilityMeasure η]
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : Measure ℝ} [IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (houtcome_prob :
      ∀ C : ℕ, ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
        IsProbabilityMeasure
          (outcomeLaw C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := μ.1) μ.2)))
    (hsource :
      source_assumption_theorem2_local_interval_event_clauses
        η Mseq Iseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
        (totalSupply := totalSupply)) :
    Theorem2SelectedStableLocalProbabilityEventSourceClauses
      η Mseq Iseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
      totalSupply := by
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      largeEndpointEvent, smallMatchedIntervalEvent, largeInterval,
      smallInterval, hvLow, hvHigh, hvStar, hvStrict, hlower_atTop,
      hcutoff_lower, htail_floor, hlarge_meas, hlarge_mass,
      hlarge_ge, hlarge_integral_event, hlarge_event_chosen,
      hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound,
      hsmall_meas, hsmall_mass, hsmall_ge, hsmall_integral_event,
      hsmall_event_chosen⟩
  have hlarge_int :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          Integrable
            (fun w : ℝ =>
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                w
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2))) η := by
    exact Filter.Eventually.of_forall (fun C μ => by
      let P :=
        (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
      simpa [cutoffAffordanceProbability, P] using
        (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) η
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (cutoffOut C P)))
  have hsmall_int :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          Integrable
            (fun w : ℝ =>
              (1 - totalSupply - epsilon -
                (1 - Real.exp (-(2 * epsilon * sigma)))) *
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  w
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))) η := by
    exact Filter.Eventually.of_forall (fun C μ => by
      let P :=
        (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
      have hbase :
          Integrable
            (fun w : ℝ =>
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                w (cutoffOut C P)) η := by
        simpa [cutoffAffordanceProbability, P] using
          (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) η
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            (cutoffOut C P))
      simpa [P] using
        hbase.const_mul
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma)))))
  have hlarge_endpoint_choice :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          AppliedModelingLib.Matching.choiceMass
              (outcomeLaw C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (chosenCollege C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) -
              epsilon ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
              vHigh
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) := by
    filter_upwards
      [hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound] with
      C hchosenC hboundC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
    haveI : IsProbabilityMeasure (outcomeLaw C P) :=
      houtcome_prob C μ
    haveI : IsFiniteMeasure (outcomeLaw C P) := by infer_instance
    exact
      theorem2_largeFirm_highEndpoint_choiceMass_bound_of_event_imp
        (outcomeLaw C P)
        (chosenCollege C P)
        (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
        (event := largeEndpointEvent C μ)
        (le_of_lt hepsilon)
        (hchosenC μ)
        (hboundC μ)
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      smallMatchedIntervalEvent, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, htail_floor, ?_, hlarge_event_chosen,
      hlarge_endpoint_choice, ?_, hsmall_event_chosen⟩
  · filter_upwards
      [hlarge_meas, hlarge_int, hlarge_mass, hlarge_ge,
        hlarge_integral_event] with
      C hmeasC hintC hmassC hgeC hintegralC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
    have hpLarge_mono :
        Monotone (fun w : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            w (cutoffOut C P)) := by
      intro x y hxy
      exact
        cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (active := indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (cutoff := cutoffOut C P) hxy
    have hpLow_nonneg :
        0 ≤
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            vLow (cutoffOut C P) :=
      cutoffAffordanceProbability_nonneg
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
        vLow (cutoffOut C P)
    have hnonneg_compl :
        ∀ w : ℝ, w ∉ largeInterval C μ →
          0 ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
              w (cutoffOut C P) := by
      intro w _hw
      exact
        cutoffAffordanceProbability_nonneg
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          w (cutoffOut C P)
    exact
      theorem2_largeFirm_eventMass_lower_bound_of_interval_integral
        η
        (region := largeInterval C μ)
        (mass := 1 - epsilon)
        (eventMass :=
          AppliedModelingLib.Matching.eventMass
            (outcomeLaw C P) (largeIntervalEvent C μ))
        (pLarge := fun w : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            w (cutoffOut C P))
        (vLow := vLow)
        (hmeasC μ) (hintC μ) (hmassC μ) hpLow_nonneg
        hpLarge_mono (hgeC μ) hnonneg_compl (hintegralC μ)
  · filter_upwards
      [hsmall_meas, hsmall_int, hsmall_mass, hsmall_ge,
        hsmall_integral_event] with
      C hmeasC hintC hmassC hgeC hintegralC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
    have hpSmall_mono :
        Monotone (fun w : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            w (cutoffOut C P)) := by
      intro x y hxy
      exact
        cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (active := indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
          (cutoff := cutoffOut C P) hxy
    have hpStar_nonneg :
        0 ≤
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            vStar (cutoffOut C P) :=
      cutoffAffordanceProbability_nonneg
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        vStar (cutoffOut C P)
    have hnonneg_compl :
        ∀ w : ℝ, w ∉ smallInterval C μ →
          0 ≤
            (1 - totalSupply - epsilon -
              (1 - Real.exp (-(2 * epsilon * sigma)))) *
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
              w (cutoffOut C P) := by
      intro w _hw
      exact
        mul_nonneg (le_of_lt hden)
          (cutoffAffordanceProbability_nonneg
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            w (cutoffOut C P))
    exact
      theorem2_smallFirm_matchedMass_lower_bound_of_interval_integral
        η
        (region := smallInterval C μ)
        (mass := Real.sqrt epsilon)
        (denom :=
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))))
        (matchedMass :=
          AppliedModelingLib.Matching.eventMass
            (outcomeLaw C P) (smallMatchedIntervalEvent C μ))
        (pSmall := fun w : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            w (cutoffOut C P))
        (vStar := vStar)
        (hmeasC μ) (hintC μ) (hmassC μ) (le_of_lt hden)
        hpStar_nonneg hpSmall_mono (hgeC μ) hnonneg_compl
        (hintegralC μ)

/--
No-divergence local interval/event source clauses imply the same selected-stable
local probability-event clauses once long-tailed survival and stable-matching
existence derive the missing cutoff-divergence conjunct.
-/
theorem theorem2_selectedStable_local_probabilityEvent_source_clauses_of_local_interval_event_clauses_no_divergence
    {StudentSeq : ℕ → Type u}
    {η : Measure ℝ} [IsProbabilityMeasure η]
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : Measure ℝ} [IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (hstable_nonempty :
      source_assumption_selected_stable_nonempty Mseq)
    (houtcome_prob :
      ∀ C : ℕ, ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
        IsProbabilityMeasure
          (outcomeLaw C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := μ.1) μ.2)))
    (hsource :
      source_assumption_theorem2_local_interval_event_clauses_no_divergence
        η Mseq Iseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
        (totalSupply := totalSupply)) :
    Theorem2SelectedStableLocalProbabilityEventSourceClauses
      η Mseq Iseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
      totalSupply :=
  theorem2_selectedStable_local_probabilityEvent_source_clauses_of_local_interval_event_clauses
    (houtcome_prob := houtcome_prob)
    (source_assumption_theorem2_local_interval_event_clauses_of_no_divergence
      hlong hstable_nonempty hsource)

end
end PG24NoisyMatchingMarkets
