import PG24NoisyMatchingMarkets.Theorem1IidAttenuationSourceRoute

open Filter MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/--
The source defines the threshold by the strict upper-tail identity
`eta((vS, infinity)) = totalSupply`.  Since the complement of the literal
closed low-value set is that same strict upper tail, the source capacity sum
gives the conservation normalization without a separate tail-mass premise.
-/
theorem theorem1_capacity_eq_high_value_mass_of_total_capacity_and_threshold
    {StudentType : Type u} {n : ℕ}
    (M : CutoffMarket StudentType (Fin n))
    (valueLaw : Measure ℝ) {totalSupply vS : ℝ}
    (hcapacity_sum : (∑ college : Fin n, M.capacity college) = totalSupply)
    (hthreshold : valueLaw.real (Set.Ioi vS) = totalSupply) :
    (∑ college : Fin n, M.capacity college) =
      valueLaw.real (Set.Iic vS)ᶜ := by
  calc
    (∑ college : Fin n, M.capacity college) = totalSupply := hcapacity_sum
    _ = valueLaw.real (Set.Ioi vS) := hthreshold.symm
    _ = valueLaw.real (Set.Iic vS)ᶜ := by simp

/--
Eventual form of the source threshold/capacity normalization.  The capacity
sum is only required on the same eventual tail as the asymptotic conclusion.
-/
theorem theorem1_eventually_capacity_eq_high_value_mass_of_total_capacity_and_threshold
    {StudentType : Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket StudentType (Fin C))
    (valueLaw : Measure ℝ) {totalSupply vS : ℝ}
    (hcapacity_sum : ∀ᶠ C : ℕ in atTop,
      (∑ college : Fin C, (Mseq C).capacity college) = totalSupply)
    (hthreshold : valueLaw.real (Set.Ioi vS) = totalSupply) :
    ∀ᶠ C : ℕ in atTop,
      (∑ college : Fin C, (Mseq C).capacity college) =
        valueLaw.real (Set.Iic vS)ᶜ := by
  filter_upwards [hcapacity_sum] with C hcapacity_C
  exact theorem1_capacity_eq_high_value_mass_of_total_capacity_and_threshold
    (Mseq C) valueLaw hcapacity_C hthreshold

/--
Selected-stable iid attenuation with the source threshold selected by its
strict upper-tail mass.  This route derives the capacity/high-value balance
on the asymptotic tail from the paper's two source facts, rather than taking
that balance as a theorem premise.
-/
theorem theorem1_selectedStable_iid_low_high_tail_mass_eventually_le_rate_of_beta_of_total_capacity_and_threshold
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
    (vS totalSupply : ℝ) (pivot : ℕ -> ℝ)
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
    (hcapacity_sum : ∀ᶠ C : ℕ in atTop,
      (∑ college : Fin C, (Mseq C).capacity college) = totalSupply)
    (hthreshold : valueLaw.real (Set.Ioi vS) = totalSupply)
    (hlower_selected : ∀ᶠ C : ℕ in atTop,
      ∀ college : Fin C,
        pivot C ≤ cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable (selected C).2) college)
    (hseparation_selected : ∀ᶠ C : ℕ in atTop,
      theorem1DenseGroupCenter noiseLaw C beta gamma +
        theorem1DenseDeviationRadius C beta gamma ≤ pivot C - vS) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ C : ℕ in atTop,
        eventMass
            (studentLaw.prod (Measure.pi (fun _ : Fin C => noiseLaw)))
            (fun outcome : StudentType × (Fin C -> ℝ) =>
              value outcome.1 ∈ Set.Iic vS ∧
                chosenInActive (demand C) (Finset.univ : Finset (Fin C)) outcome) ≤
          A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) ∧
        eventMass
            (studentLaw.prod (Measure.pi (fun _ : Fin C => noiseLaw)))
            (fun outcome : StudentType × (Fin C -> ℝ) =>
              value outcome.1 ∈ (Set.Iic vS)ᶜ ∧
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
    (fun _ => vS) pivot hlower_univ hseparation_selected with
      ⟨A, hA_nonneg, hlow_integral_rate⟩
  have hcapacity_eq_high_value_mass :=
    theorem1_eventually_capacity_eq_high_value_mass_of_total_capacity_and_threshold
      Mseq valueLaw hcapacity_sum hthreshold
  refine ⟨A, hA_nonneg, ?_⟩
  filter_upwards [hlow_integral_rate, hcapacity_eq_high_value_mass]
    with C hlow_integral_C hcapacity_C
  exact theorem1_sourceDemand_low_high_tail_mass_le_of_cutoff_tail_bound_iid
    (Mseq C) (Kseq C)
    ((Iseq C).marketClearingCutoffOfStable_marketClearing (selected C).2)
    studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
    (cutoffOut C
      ((Iseq C).marketClearingCutoffOfStable (selected C).2))
    (demand C) (hdemand_none_iff_no_crossed C) (hchosen_feasible C)
    (by simpa using hchoice_mass_eq_aggregate_demand C)
    measurableSet_Iic hcapacity_C hlow_integral_C

end

end PG24NoisyMatchingMarkets
