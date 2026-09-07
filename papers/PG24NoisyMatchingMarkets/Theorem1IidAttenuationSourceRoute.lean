import PG24NoisyMatchingMarkets.Theorem1RoundedChebyshevRates
import PG24NoisyMatchingMarkets.Theorem1SourceDemandBridge

open Filter MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/--
The checked Theorem 1 attenuation route on the actual source sampling space.
The remaining inputs are concrete selected-cutoff geometry, demand semantics,
choice-to-aggregate-demand identification, and the source capacity
normalization.  The polynomial low-tail bound is derived from beta-max
variance and the literal closed low set is transported to both matching tails.
-/
theorem theorem1_selectedStable_iid_low_high_tail_mass_eventually_le_rate_of_beta
    {StudentType : Type u} [MeasurableSpace StudentType]
    (Mseq : ∀ C : ℕ, CutoffMarket StudentType (Fin C))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    (selected : ∀ C : ℕ,
      { matching : (Mseq C).Matching // (Mseq C).Stable matching })
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ -> ℝ} {beta gamma : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff -> Fin C -> ℝ)
    (lowValue pivot : ℕ -> ℝ)
    (demand : ∀ C : ℕ,
      StudentType × (Fin C -> ℝ) -> Option (Fin C))
    (hdemand_none_iff_no_crossed :
      ∀ (C : ℕ) (outcome : StudentType × (Fin C -> ℝ)),
        demand C outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin C))
            (noisyScore (value outcome.1) outcome.2)
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (selected C).2)))
    (hchosen_feasible :
      ∀ (C : ℕ) (outcome : StudentType × (Fin C -> ℝ)) (college : Fin C),
        demand C outcome = some college ->
          cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (selected C).2) college <
            value outcome.1 + outcome.2 college)
    (hchoice_mass_eq_aggregate_demand :
      ∀ C : ℕ,
        choiceMass
          (studentLaw.prod (Measure.pi (fun _ : Fin C => noiseLaw)))
          (demand C) (Finset.univ : Finset (Fin C)) =
          ∑ college : Fin C,
            (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable (selected C).2) college)
    (hcapacity_eq_high_value_mass :
      ∀ C : ℕ,
        (∑ college : Fin C, (Mseq C).capacity college) =
          valueLaw.real (Set.Iic (lowValue C))ᶜ)
    (hlower_selected : ∀ᶠ C : ℕ in atTop,
      ∀ college : Fin C,
        pivot C ≤ cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable (selected C).2) college)
    (hseparation_selected : ∀ᶠ C : ℕ in atTop,
      theorem1DenseGroupCenter noiseLaw C beta gamma +
        theorem1DenseDeviationRadius C beta gamma ≤ pivot C - lowValue C) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ C : ℕ in atTop,
        eventMass
            (studentLaw.prod (Measure.pi (fun _ : Fin C => noiseLaw)))
            (fun outcome : StudentType × (Fin C -> ℝ) =>
              value outcome.1 ∈ Set.Iic (lowValue C) ∧
                chosenInActive (demand C) (Finset.univ : Finset (Fin C)) outcome) ≤
          A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) ∧
        eventMass
            (studentLaw.prod (Measure.pi (fun _ : Fin C => noiseLaw)))
            (fun outcome : StudentType × (Fin C -> ℝ) =>
              value outcome.1 ∈ (Set.Iic (lowValue C))ᶜ ∧
                ¬ chosenInActive (demand C) (Finset.univ : Finset (Fin C)) outcome) ≤
          A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
  have hlower_univ : ∀ᶠ C : ℕ in atTop,
      ∀ college ∈ (Finset.univ : Finset (Fin C)),
        pivot C ≤ cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable (selected C).2) college := by
    filter_upwards [hlower_selected] with C hC college _hcollege
    exact hC college
  rcases theorem1DenseGroup_low_affordance_integral_eventually_le_source_rate_of_beta
    noiseLaw hbeta hgamma hvariance valueLaw
    (fun C => (Finset.univ : Finset (Fin C)))
    (fun C => cutoffOut C
      ((Iseq C).marketClearingCutoffOfStable (selected C).2))
    lowValue pivot hlower_univ hseparation_selected with
      ⟨A, hA_nonneg, hlow_integral_rate⟩
  refine ⟨A, hA_nonneg, ?_⟩
  filter_upwards [hlow_integral_rate] with C hlow_integral_C
  have hmatched_low :=
    theorem1_sourceDemand_value_restricted_matched_mass_eq_integral_affordance_iid
      studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
      (cutoffOut C
        ((Iseq C).marketClearingCutoffOfStable (selected C).2))
      (demand C) (hdemand_none_iff_no_crossed C) (hchosen_feasible C)
      (region := Set.Iic (lowValue C)) measurableSet_Iic
  have hmatched_all :=
    theorem1_sourceDemand_value_restricted_matched_mass_eq_integral_affordance_iid
      studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
      (cutoffOut C
        ((Iseq C).marketClearingCutoffOfStable (selected C).2))
      (demand C) (hdemand_none_iff_no_crossed C) (hchosen_feasible C)
      (region := Set.univ) MeasurableSet.univ
  have hwhole_choice_capacity :=
    sourceDemand_selectedStable_choiceMass_eq_activeCapacity_iid
      (Mseq C) (Iseq C) (Kseq C) (selected C).2
      studentLaw noiseLaw (demand C) (Finset.univ : Finset (Fin C))
      (by simpa using hchoice_mass_eq_aggregate_demand C)
  have hwhole_integral :
      (∫ v : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin C => noiseLaw))
          (Finset.univ : Finset (Fin C)) v
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable (selected C).2)) ∂valueLaw) =
        ∑ college : Fin C, (Mseq C).capacity college := by
    calc
      (∫ v : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin C => noiseLaw))
          (Finset.univ : Finset (Fin C)) v
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable (selected C).2)) ∂valueLaw) =
          eventMass
            (studentLaw.prod (Measure.pi (fun _ : Fin C => noiseLaw)))
            (fun outcome : StudentType × (Fin C -> ℝ) =>
              chosenInActive (demand C) (Finset.univ : Finset (Fin C)) outcome) := by
        simpa using hmatched_all.symm
      _ = choiceMass
          (studentLaw.prod (Measure.pi (fun _ : Fin C => noiseLaw)))
          (demand C) (Finset.univ : Finset (Fin C)) := rfl
      _ = activeCapacity (Finset.univ : Finset (Fin C)) (Mseq C).capacity :=
        hwhole_choice_capacity
      _ = ∑ college : Fin C, (Mseq C).capacity college := by
        simp [activeCapacity]
  have hcapacity_balance :
      (∫ v : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin C => noiseLaw))
          (Finset.univ : Finset (Fin C)) v
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable (selected C).2)) ∂valueLaw) =
        valueLaw.real (Set.Iic (lowValue C))ᶜ :=
    hwhole_integral.trans (hcapacity_eq_high_value_mass C)
  have hmatch :=
    theorem1_sourceDemand_chosenInAll_iff_affordance
      value
      (cutoffOut C
        ((Iseq C).marketClearingCutoffOfStable (selected C).2))
      (demand C) (hdemand_none_iff_no_crossed C) (hchosen_feasible C)
  have hconservation :=
    theorem1_source_model_low_matched_mass_eq_high_unmatched_mass_of_capacity_balance
      studentLaw value hvalue valueLaw hvalue_marginal
      (Measure.pi (fun _ : Fin C => noiseLaw))
      (cutoffOut C
        ((Iseq C).marketClearingCutoffOfStable (selected C).2))
      (demand C) hmatch (lowValues := Set.Iic (lowValue C))
      measurableSet_Iic hcapacity_balance
  have hlow_bound :
      eventMass
          (studentLaw.prod (Measure.pi (fun _ : Fin C => noiseLaw)))
          (fun outcome : StudentType × (Fin C -> ℝ) =>
            value outcome.1 ∈ Set.Iic (lowValue C) ∧
              chosenInActive (demand C) (Finset.univ : Finset (Fin C)) outcome) ≤
        A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
    rw [hmatched_low]
    exact hlow_integral_C
  constructor
  · exact hlow_bound
  · rw [← hconservation]
    exact hlow_bound

end

end PG24NoisyMatchingMarkets
