import PG24NoisyMatchingMarkets.Theorem2TwoScaleSmallBound

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

theorem theorem2_sourceDemand_chosenInActive_implies_affordance
    {StudentType : Type u} {n : ℕ}
    (value : StudentType -> ℝ) (active : Finset (Fin n))
    (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college) :
    ∀ outcome : StudentType × (Fin n -> ℝ),
      chosenInActive demand active outcome ->
        theorem2StudentTypeAffordanceEvent value active cutoff outcome := by
  intro outcome hchosen
  rcases hchosen with ⟨college, hcollege, hdemand⟩
  exact ⟨college, hcollege, by
    simpa [noisyScore] using hchosen_feasible outcome college hdemand⟩

theorem theorem2_sourceModel_integral_largeAffordance_lower_of_clearing
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n))
    (hdisjoint : Disjoint small large)
    (hcover : small ∪ large = (Finset.univ : Finset (Fin n)))
    {totalSupply alpha delta : ℝ} (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (aggregateDemand capacity : Fin n -> ℝ)
    (hlarge_choice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand large = ∑ c ∈ large, aggregateDemand c)
    (hclearing : ∀ c : Fin n, aggregateDemand c = capacity c)
    (htotal_capacity : (∑ c : Fin n, capacity c) = totalSupply)
    (hsmall_capacity : activeCapacity small capacity ≤ alpha * delta) :
    totalSupply - alpha * delta ≤
      ∫ v : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large v cutoff
        ∂valueLaw := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  let outcomeLaw : Measure (StudentType × (Fin n -> ℝ)) :=
    studentLaw.prod productLaw
  haveI : IsProbabilityMeasure outcomeLaw := by
    dsimp [outcomeLaw]
    infer_instance
  have htotal_active :
      activeCapacity (Finset.univ : Finset (Fin n)) capacity = totalSupply := by
    simpa [activeCapacity] using htotal_capacity
  have hlarge_capacity :
      totalSupply - alpha * delta ≤ activeCapacity large capacity := by
    exact activeCapacity_right_ge_totalLower_sub_leftUpper_of_partition
      capacity hcover.symm hdisjoint (le_of_eq htotal_active.symm) hsmall_capacity
  have hlarge_choice_eq_capacity :
      choiceMass outcomeLaw demand large = activeCapacity large capacity := by
    exact choiceMass_eq_activeCapacity_of_aggregateDemand_eq_capacity
      outcomeLaw demand large
      (by simpa [outcomeLaw, productLaw] using hlarge_choice_mass)
      (fun c _hc => hclearing c)
  have hchoice_le_event :
      choiceMass outcomeLaw demand large ≤
        eventMass outcomeLaw
          (theorem2StudentTypeAffordanceEvent value large cutoff) := by
    exact choiceMass_le_eventMass_of_imp outcomeLaw
      (theorem2_sourceDemand_chosenInActive_implies_affordance
        value large cutoff demand hchosen_feasible)
  have hevent_eq_integral :
      eventMass outcomeLaw
          (theorem2StudentTypeAffordanceEvent value large cutoff) =
        ∫ v : ℝ,
          cutoffAffordanceProbability productLaw large v cutoff
          ∂valueLaw := by
    simpa [outcomeLaw, productLaw] using
      (theorem2_sourceModel_affordance_eventMass_eq_integral
        studentLaw value hvalue valueLaw hvalue_marginal noiseLaw large cutoff)
  calc
    totalSupply - alpha * delta ≤ activeCapacity large capacity := hlarge_capacity
    _ = choiceMass outcomeLaw demand large := hlarge_choice_eq_capacity.symm
    _ ≤ eventMass outcomeLaw
          (theorem2StudentTypeAffordanceEvent value large cutoff) := hchoice_le_event
    _ = ∫ v : ℝ,
          cutoffAffordanceProbability productLaw large v cutoff
          ∂valueLaw := hevent_eq_integral
    _ = ∫ v : ℝ,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin n => noiseLaw)) large v cutoff
          ∂valueLaw := by
      rfl

theorem theorem2_largeHighEndpoint_lower_of_integral_and_regular_region
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    {region : Set ℝ} {totalSupply alpha delta vHigh : ℝ}
    {pLarge : ℝ -> ℝ}
    (hregion_meas : MeasurableSet region)
    (hintegrable : Integrable pLarge valueLaw)
    (hregion_mass : 1 - delta ≤ valueLaw.real region)
    (hp_mono : Monotone pLarge)
    (hregion_le_high : ∀ w : ℝ, w ∈ region -> w ≤ vHigh)
    (hp_high_nonneg : 0 ≤ pLarge vHigh)
    (hp_le_one : ∀ w : ℝ, pLarge w ≤ 1)
    (hintegral_lower : totalSupply - alpha * delta ≤ ∫ w : ℝ, pLarge w ∂valueLaw) :
    totalSupply - (1 + alpha) * delta ≤ pLarge vHigh := by
  have hintegral_upper :
      (∫ w : ℝ, pLarge w ∂valueLaw) ≤
        pLarge vHigh * valueLaw.real region + valueLaw.real regionᶜ := by
    simpa using
      (AppliedModelingLib.integral_le_measureReal_mul_add_compl_of_le_on_of_le_on_compl
        valueLaw hregion_meas hintegrable
        (fun w hw => hp_mono (hregion_le_high w hw))
        (fun w _hw => hp_le_one w))
  have hmass_sum :
      valueLaw.real region + valueLaw.real regionᶜ = 1 := by
    simpa using
      (MeasureTheory.measureReal_add_measureReal_compl (μ := valueLaw) hregion_meas)
  have hregion_le_one : valueLaw.real region ≤ 1 := by
    exact measureReal_le_one
  have hdelta_nonneg : 0 ≤ delta := by
    linarith
  have hcompl_le_delta : valueLaw.real regionᶜ ≤ delta := by
    linarith [hmass_sum, hregion_mass]
  have hfactor_nonneg : 0 ≤ 1 - pLarge vHigh := by
    linarith [hp_le_one vHigh]
  have hfactor_le_one : 1 - pLarge vHigh ≤ 1 := by
    linarith
  have houtside_term_le :
      (1 - pLarge vHigh) * valueLaw.real regionᶜ ≤ delta := by
    calc
      (1 - pLarge vHigh) * valueLaw.real regionᶜ ≤
          (1 - pLarge vHigh) * delta :=
        mul_le_mul_of_nonneg_left hcompl_le_delta hfactor_nonneg
      _ ≤ 1 * delta :=
        mul_le_mul_of_nonneg_right hfactor_le_one hdelta_nonneg
      _ = delta := by ring
  have hintegral_upper' :
      (∫ w : ℝ, pLarge w ∂valueLaw) ≤ pLarge vHigh + delta := by
    calc
      (∫ w : ℝ, pLarge w ∂valueLaw) ≤
          pLarge vHigh * valueLaw.real region + valueLaw.real regionᶜ :=
        hintegral_upper
      _ = pLarge vHigh +
          (1 - pLarge vHigh) * valueLaw.real regionᶜ := by
        calc
          pLarge vHigh * valueLaw.real region + valueLaw.real regionᶜ =
              pLarge vHigh *
                (valueLaw.real region + valueLaw.real regionᶜ) +
                (1 - pLarge vHigh) * valueLaw.real regionᶜ := by ring
          _ = pLarge vHigh +
                (1 - pLarge vHigh) * valueLaw.real regionᶜ := by
            rw [hmass_sum]
            ring
      _ ≤ pLarge vHigh + delta := by linarith
  linarith

theorem theorem2_sourceModel_largeHigh_lower_of_clearing_and_regular_region
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n))
    (hdisjoint : Disjoint small large)
    (hcover : small ∪ large = (Finset.univ : Finset (Fin n)))
    {region : Set ℝ} {totalSupply alpha delta vHigh : ℝ}
    (cutoff : Fin n -> ℝ)
    (hregion_meas : MeasurableSet region)
    (hregion_mass : 1 - delta ≤ valueLaw.real region)
    (hregion_le_high : ∀ w : ℝ, w ∈ region -> w ≤ vHigh)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (aggregateDemand capacity : Fin n -> ℝ)
    (hlarge_choice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand large = ∑ c ∈ large, aggregateDemand c)
    (hclearing : ∀ c : Fin n, aggregateDemand c = capacity c)
    (htotal_capacity : (∑ c : Fin n, capacity c) = totalSupply)
    (hsmall_capacity : activeCapacity small capacity ≤ alpha * delta) :
    totalSupply - (1 + alpha) * delta ≤
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) large vHigh cutoff := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  let pLarge : ℝ -> ℝ :=
    fun w => cutoffAffordanceProbability productLaw large w cutoff
  have hp_integrable : Integrable pLarge valueLaw := by
    simpa [pLarge, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        productLaw valueLaw large cutoff)
  have hintegral_lower :
      totalSupply - alpha * delta ≤ ∫ w : ℝ, pLarge w ∂valueLaw := by
    simpa [pLarge, productLaw] using
      (theorem2_sourceModel_integral_largeAffordance_lower_of_clearing
        studentLaw value hvalue valueLaw hvalue_marginal noiseLaw small large
        hdisjoint hcover cutoff demand hchosen_feasible aggregateDemand capacity
        hlarge_choice_mass hclearing htotal_capacity hsmall_capacity)
  change totalSupply - (1 + alpha) * delta ≤ pLarge vHigh
  exact theorem2_largeHighEndpoint_lower_of_integral_and_regular_region
    valueLaw hregion_meas hp_integrable hregion_mass
    (fun x y hxy => cutoffAffordanceProbability_mono_value productLaw hxy)
    hregion_le_high
    (cutoffAffordanceProbability_nonneg productLaw large vHigh cutoff)
    (fun w => cutoffAffordanceProbability_le_one productLaw large w cutoff)
    hintegral_lower

theorem theorem2_sourceModel_largeHigh_lower_of_capacityRegular
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n))
    (hdisjoint : Disjoint small large)
    (hcover : small ∪ large = (Finset.univ : Finset (Fin n)))
    {region : Set ℝ} {totalSupply alpha delta vHigh : ℝ}
    (cutoff : Fin n -> ℝ)
    (hregion_meas : MeasurableSet region)
    (hregion_mass : 1 - delta ≤ valueLaw.real region)
    (hregion_le_high : ∀ w : ℝ, w ∈ region -> w ≤ vHigh)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (aggregateDemand capacity : Fin n -> ℝ)
    (hlarge_choice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand large = ∑ c ∈ large, aggregateDemand c)
    (hclearing : ∀ c : Fin n, aggregateDemand c = capacity c)
    (htotal_capacity : (∑ c : Fin n, capacity c) = totalSupply)
    (hsmall_card : (small.card : ℝ) ≤ delta * (n : ℝ))
    (halpha_nonneg : 0 ≤ alpha) (hn_pos : 0 < (n : ℝ))
    (hcapacity_regular : capacityRegular capacity alpha n) :
    totalSupply - (1 + alpha) * delta ≤
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) large vHigh cutoff := by
  apply theorem2_sourceModel_largeHigh_lower_of_clearing_and_regular_region
    studentLaw value hvalue valueLaw hvalue_marginal noiseLaw small large
    hdisjoint hcover cutoff hregion_meas hregion_mass hregion_le_high demand
    hchosen_feasible aggregateDemand capacity hlarge_choice_mass hclearing
    htotal_capacity
  simpa [mul_comm] using
    (smallActiveSet_capacity_le_epsilon_mul_alpha
      (epsilon := delta) (alpha := alpha) (C := n)
      small capacity hsmall_card halpha_nonneg hn_pos
      (fun c hc => capacityRegular.le hcapacity_regular c))

end

end PG24NoisyMatchingMarkets
