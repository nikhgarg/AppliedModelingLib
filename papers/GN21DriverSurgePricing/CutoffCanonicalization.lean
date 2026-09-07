import GN21DriverSurgePricing.DomainBridge

/-!
# Direct Cutoff Canonicalization for GN21 Theorem 2

This module contains the analytic replacement steps used to repair the
optimizer-existence portion of GN21 Theorem 2.  It does not use theorem-facing
certificates: each result is a direct statement about a fixed response,
feasible policy, or aggregate-reward replacement.
-/

open AppliedModelingLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal symmDiff

namespace GN21DriverSurgePricing

/-- The fixed-current positive-response policy for the non-surge component. -/
def gn21LeftPositiveResponsePolicy
    (μ : Fin 2 → Measure TripLength) (arrival m : Fin 2 → ℝ)
    (switch12 switch21 : ℝ) (ρ : Fin 2 → TripPolicy) : TripPolicy :=
  lemma5PositiveResponsePolicy
    (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1))

/-- The fixed-current positive-response policy for the surge component. -/
def gn21RightPositiveResponsePolicy
    (μ : Fin 2 → Measure TripLength) (arrival m : Fin 2 → ℝ)
    (switch12 switch21 : ℝ) (ρ : Fin 2 → TripPolicy) : TripPolicy :=
  lemma5PositiveResponsePolicy
    (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1))

/-- Updating one source-open component with another source-open policy keeps
the two-state policy in the source domain. -/
theorem dynamicFeasibleOpenPolicy_update
    {ρ : Fin 2 → TripPolicy} (hρ : dynamicFeasibleOpenPolicy ρ)
    (i : Fin 2) (candidate : TripPolicy)
    (hcandidate_subset : candidate ⊆ acceptAllPolicy)
    (hcandidate_open : IsOpen candidate) :
    dynamicFeasibleOpenPolicy (Function.update ρ i candidate) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using ⟨hcandidate_subset, hcandidate_open⟩
  · simpa [Function.update, hji] using hρ j

/-- A continuous strictly decreasing response is either positive everywhere,
has a positive zero, or is negative everywhere on the source trip domain. -/
theorem gn21_strictAntiOn_sign_partition
    (response : TripLength → ℝ)
    (hcont : ContinuousOn response (Set.Ioi 0))
    (hanti : StrictAntiOn response (Set.Ioi 0)) :
    (∀ τ : TripLength, 0 < τ → 0 < response τ) ∨
      (∃ t : ℝ, 0 < t ∧ response t = 0) ∨
        ∀ τ : TripLength, 0 < τ → response τ < 0 := by
  by_cases hpositive : ∀ τ : TripLength, 0 < τ → 0 < response τ
  · exact Or.inl hpositive
  push Not at hpositive
  rcases hpositive with ⟨u, hu_pos, hu_nonpos⟩
  by_cases hzero : ∃ t : ℝ, 0 < t ∧ response t = 0
  · exact Or.inr (Or.inl hzero)
  right
  right
  have hu_neg : response u < 0 := by
    rcases lt_or_eq_of_le hu_nonpos with hu_neg | hu_zero
    · exact hu_neg
    · exact False.elim (hzero ⟨u, hu_pos, hu_zero⟩)
  intro τ hτ_pos
  by_contra hτ_notneg
  have hτ_nonneg : 0 ≤ response τ := le_of_not_gt hτ_notneg
  rcases lt_or_eq_of_le hτ_nonneg with hτ_response_pos | hτ_zero
  · have hτ_lt_u : τ < u := by
      by_contra hnot_lt
      have hu_le_τ : u ≤ τ := le_of_not_gt hnot_lt
      rcases lt_or_eq_of_le hu_le_τ with hu_lt_τ | hu_eq_τ
      · have hresponse_lt : response τ < response u :=
          hanti hu_pos hτ_pos hu_lt_τ
        linarith
      · subst τ
        linarith
    have hcont_interval : ContinuousOn response (Set.Icc τ u) :=
      hcont.mono (fun x hx => hτ_pos.trans_le hx.1)
    have hzero_between : (0 : ℝ) ∈ Set.Icc (response u) (response τ) :=
      ⟨le_of_lt hu_neg, le_of_lt hτ_response_pos⟩
    rcases intermediate_value_Icc' (le_of_lt hτ_lt_u) hcont_interval
        hzero_between with ⟨t, ht, ht_zero⟩
    exact hzero ⟨t, hτ_pos.trans_le ht.1, ht_zero⟩
  · exact False.elim (hzero ⟨τ, hτ_pos, hτ_zero.symm⟩)

/-- A continuous strictly increasing response has the analogous trichotomy. -/
theorem gn21_strictMonoOn_sign_partition
    (response : TripLength → ℝ)
    (hcont : ContinuousOn response (Set.Ioi 0))
    (hmono : StrictMonoOn response (Set.Ioi 0)) :
    (∀ τ : TripLength, 0 < τ → 0 < response τ) ∨
      (∃ t : ℝ, 0 < t ∧ response t = 0) ∨
        ∀ τ : TripLength, 0 < τ → response τ < 0 := by
  by_cases hpositive : ∀ τ : TripLength, 0 < τ → 0 < response τ
  · exact Or.inl hpositive
  push Not at hpositive
  rcases hpositive with ⟨u, hu_pos, hu_nonpos⟩
  by_cases hzero : ∃ t : ℝ, 0 < t ∧ response t = 0
  · exact Or.inr (Or.inl hzero)
  right
  right
  have hu_neg : response u < 0 := by
    rcases lt_or_eq_of_le hu_nonpos with hu_neg | hu_zero
    · exact hu_neg
    · exact False.elim (hzero ⟨u, hu_pos, hu_zero⟩)
  intro τ hτ_pos
  by_contra hτ_notneg
  have hτ_nonneg : 0 ≤ response τ := le_of_not_gt hτ_notneg
  rcases lt_or_eq_of_le hτ_nonneg with hτ_response_pos | hτ_zero
  · have hu_lt_τ : u < τ := by
      by_contra hnot_lt
      have hτ_le_u : τ ≤ u := le_of_not_gt hnot_lt
      rcases lt_or_eq_of_le hτ_le_u with hτ_lt_u | hτ_eq_u
      · have hresponse_lt : response τ < response u :=
          hmono hτ_pos hu_pos hτ_lt_u
        linarith
      · subst τ
        linarith
    have hcont_interval : ContinuousOn response (Set.Icc u τ) :=
      hcont.mono (fun x hx => hu_pos.trans_le hx.1)
    have hzero_between : (0 : ℝ) ∈ Set.Icc (response u) (response τ) :=
      ⟨le_of_lt hu_neg, le_of_lt hτ_response_pos⟩
    rcases intermediate_value_Icc (le_of_lt hu_lt_τ) hcont_interval
        hzero_between with ⟨t, ht, ht_zero⟩
    exact hzero ⟨t, hu_pos.trans_le ht.1, ht_zero⟩
  · exact False.elim (hzero ⟨τ, hτ_pos, hτ_zero.symm⟩)

/-- A positive pointwise scale preserves the fixed-response positive set. -/
theorem lemma5PositiveResponsePolicy_eq_of_pos_scale
    (base marginal scale : TripLength → ℝ)
    (hscale_pos : ∀ τ : TripLength, 0 < τ → 0 < scale τ)
    (hscale : ∀ τ : TripLength, 0 < τ → marginal τ = scale τ * base τ) :
    lemma5PositiveResponsePolicy marginal = lemma5PositiveResponsePolicy base := by
  ext τ
  constructor
  · rintro ⟨hτ_pos, hmarginal_pos⟩
    rw [hscale τ hτ_pos] at hmarginal_pos
    rcases (mul_pos_iff.mp hmarginal_pos) with hpos | hneg
    · exact ⟨hτ_pos, hpos.2⟩
    · exact False.elim (not_lt_of_ge (le_of_lt (hscale_pos τ hτ_pos)) hneg.1)
  · rintro ⟨hτ_pos, hbase_pos⟩
    exact ⟨hτ_pos, by
      rw [hscale τ hτ_pos]
      exact mul_pos (hscale_pos τ hτ_pos) hbase_pos⟩

/-- The positive-response policy of an everywhere-positive response is
accept-all exactly, not merely almost everywhere. -/
theorem lemma5PositiveResponsePolicy_eq_acceptAll_of_positive
    (response : TripLength → ℝ)
    (hpositive : ∀ τ : TripLength, 0 < τ → 0 < response τ) :
    lemma5PositiveResponsePolicy response = acceptAllPolicy := by
  ext τ
  constructor
  · intro hτ
    exact hτ.1
  · intro hτ
    exact ⟨hτ, hpositive τ hτ⟩

/-- The positive-response policy of an everywhere-negative response is empty. -/
theorem lemma5PositiveResponsePolicy_eq_empty_of_negative
    (response : TripLength → ℝ)
    (hnegative : ∀ τ : TripLength, 0 < τ → response τ < 0) :
    lemma5PositiveResponsePolicy response = ∅ := by
  ext τ
  constructor
  · intro hτ
    have hneg : response τ < 0 := hnegative τ hτ.1
    exact False.elim (by linarith [hτ.2])
  · simp

/-- A decreasing zero crossing gives the exact finite reject-long policy. -/
theorem lemma5PositiveResponsePolicy_eq_rejectLong_of_strictAnti_zero
    (response : TripLength → ℝ) {t : ℝ}
    (ht_pos : 0 < t)
    (hanti : StrictAntiOn response (Set.Ioi 0))
    (hzero : response t = 0) :
    lemma5PositiveResponsePolicy response = rejectLongTripsPolicy t := by
  apply eq_rejectLongTripsPolicy_of_rejectsLongTrips_of_subset_acceptAll
  · intro τ hτ_pos
    constructor
    · intro hτ_mem
      by_contra hnot_lt
      have ht_le_τ : t ≤ τ := le_of_not_gt hnot_lt
      rcases lt_or_eq_of_le ht_le_τ with ht_lt_τ | ht_eq_τ
      · have hresponse_lt : response τ < response t :=
          hanti ht_pos hτ_pos ht_lt_τ
        rw [hzero] at hresponse_lt
        linarith [hτ_mem.2]
      · subst τ
        have hresponse_pos : 0 < response t := hτ_mem.2
        rw [hzero] at hresponse_pos
        linarith
    · intro hτ_lt
      have hresponse_lt : response t < response τ :=
        hanti hτ_pos ht_pos hτ_lt
      exact ⟨hτ_pos, by linarith [hzero]⟩
  · exact lemma5PositiveResponsePolicy_subset_acceptAll response

/-- An increasing zero crossing gives the exact finite reject-short policy. -/
theorem lemma5PositiveResponsePolicy_eq_rejectShort_of_strictMono_zero
    (response : TripLength → ℝ) {t : ℝ}
    (ht_pos : 0 < t)
    (hmono : StrictMonoOn response (Set.Ioi 0))
    (hzero : response t = 0) :
    lemma5PositiveResponsePolicy response = rejectShortTripsPolicy t := by
  apply eq_rejectShortTripsPolicy_of_rejectsShortTrips_of_subset_acceptAll
  · intro τ hτ_pos
    constructor
    · intro hτ_mem
      by_contra hnot_lt
      have hτ_le_t : τ ≤ t := le_of_not_gt hnot_lt
      rcases lt_or_eq_of_le hτ_le_t with hτ_lt_t | hτ_eq_t
      · have hresponse_lt : response τ < response t :=
          hmono hτ_pos ht_pos hτ_lt_t
        rw [hzero] at hresponse_lt
        linarith [hτ_mem.2]
      · subst τ
        have hresponse_pos : 0 < response t := hτ_mem.2
        rw [hzero] at hresponse_pos
        linarith
    · intro ht_lt_τ
      have hresponse_lt : response t < response τ :=
        hmono ht_pos hτ_pos ht_lt_τ
      exact ⟨hτ_pos, by linarith [hzero]⟩
  · exact lemma5PositiveResponsePolicy_subset_acceptAll response

/-- A decreasing response's positive-response policy is source-open and has
the non-surge Theorem-2 cutoff form, including the empty and accept-all
endpoints. -/
theorem lemma5PositiveResponsePolicy_open_left_cutoff_of_strictAnti
    (response : TripLength → ℝ)
    (hcont : ContinuousOn response (Set.Ioi 0))
    (hanti : StrictAntiOn response (Set.Ioi 0)) :
    IsOpen (lemma5PositiveResponsePolicy response) ∧
      rejectsLongTripsFiniteOrInfiniteCutoff
        (lemma5PositiveResponsePolicy response) := by
  rcases gn21_strictAntiOn_sign_partition response hcont hanti with
      hpositive | hzero | hnegative
  · rw [lemma5PositiveResponsePolicy_eq_acceptAll_of_positive response hpositive]
    constructor
    · simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using
        (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    · exact Or.inr (fun _ hτ => hτ)
  · rcases hzero with ⟨t, ht_pos, ht_zero⟩
    rw [lemma5PositiveResponsePolicy_eq_rejectLong_of_strictAnti_zero
      response ht_pos hanti ht_zero]
    constructor
    · exact isOpen_Ioi.inter isOpen_Iio
    · exact Or.inl ⟨t, rejectsLongTrips_rejectLongTripsPolicy t⟩
  · rw [lemma5PositiveResponsePolicy_eq_empty_of_negative response hnegative]
    constructor
    · exact isOpen_empty
    · exact Or.inl ⟨0, by
        intro τ hτ
        simp [not_lt_of_ge (le_of_lt hτ)]⟩

/-- An increasing response's positive-response policy is source-open and has
the surge Theorem-2 cutoff form, including the empty endpoint. -/
theorem lemma5PositiveResponsePolicy_open_right_cutoff_of_strictMono
    (response : TripLength → ℝ)
    (hcont : ContinuousOn response (Set.Ioi 0))
    (hmono : StrictMonoOn response (Set.Ioi 0)) :
    IsOpen (lemma5PositiveResponsePolicy response) ∧
      ((∃ t : ℝ, rejectsShortTrips t (lemma5PositiveResponsePolicy response)) ∨
        lemma5PositiveResponsePolicy response = ∅) := by
  rcases gn21_strictMonoOn_sign_partition response hcont hmono with
      hpositive | hzero | hnegative
  · rw [lemma5PositiveResponsePolicy_eq_acceptAll_of_positive response hpositive]
    constructor
    · simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using
        (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    · left
      exact ⟨0, rejectsShortTrips_zero_of_acceptsAllTrips (fun _ hτ => hτ)⟩
  · rcases hzero with ⟨t, ht_pos, ht_zero⟩
    rw [lemma5PositiveResponsePolicy_eq_rejectShort_of_strictMono_zero
      response ht_pos hmono ht_zero]
    constructor
    · exact isOpen_Ioi.inter isOpen_Ioi
    · exact Or.inl ⟨t, rejectsShortTrips_rejectShortTripsPolicy t⟩
  · rw [lemma5PositiveResponsePolicy_eq_empty_of_negative response hnegative]
    exact ⟨isOpen_empty, Or.inr rfl⟩

/-- Replacing the non-surge component by its fixed-current positive-response
policy weakly improves the actual Appendix-D aggregate reward. -/
theorem gn21AggregateMultiplicativeDynamicReward_le_update_left_positiveResponse
    (μ : Fin 2 → Measure TripLength)
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    {ρ : Fin 2 → TripPolicy} (hρ : dynamicFeasibleMeasurablePolicy ρ) :
    gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m ρ ≤
      gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m
        (Function.update ρ 0
          (lemma5PositiveResponsePolicy
            (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
              (arrival 0) (arrival 1) switch12 switch21
              (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
              (ρ 0) (ρ 1)))) := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hq0 :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0) :=
    integrableOn_gn21SwitchProb_of_time_integrable (μ 0) switch12 switch21
      acceptAllPolicy (le_of_lt hswitch12_pos) hsum0
      (fun _ hτ => hτ) measurableSet_acceptAllPolicy htime0
  have hw0 : IntegrableOn (multiplicativePricing (m 0)) acceptAllPolicy (μ 0) :=
    integrableOn_multiplicativePricing (μ 0) (m 0) acceptAllPolicy htime0
  let response :=
    gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1)
  have hresponse_measurable : Measurable response := by
    dsimp [response]
    exact measurable_gn21MeasuredLeftMarginalResponseAtCurrent
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1) (continuous_multiplicativePricing (m 0)).measurable
  have hresponse_integrable : IntegrableOn response acceptAllPolicy (μ 0) := by
    dsimp [response]
    exact integrableOn_gn21MeasuredLeftMarginalResponseAtCurrent
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1) acceptAllPolicy hq0 hw0 htime0
  exact
    gn21AggregateMultiplicativeDynamicReward_le_update_left_of_marginal_le
      μ arrival m switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos htime0 hρ
      (lemma5PositiveResponsePolicy response)
      (lemma5PositiveResponsePolicy_subset_acceptAll response)
      (measurableSet_lemma5PositiveResponsePolicy response hresponse_measurable)
      (lemma5MarginalSetReward_le_positiveResponsePolicy
        (μ 0) response (ρ 0) hresponse_measurable hresponse_integrable
        (hρ 0).2 (hρ 0).1)

/-- State-swapped positive-response replacement for the surge component. -/
theorem gn21AggregateMultiplicativeDynamicReward_le_update_right_positiveResponse
    (μ : Fin 2 → Measure TripLength)
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime1 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    {ρ : Fin 2 → TripPolicy} (hρ : dynamicFeasibleMeasurablePolicy ρ) :
    gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m ρ ≤
      gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m
        (Function.update ρ 1
          (lemma5PositiveResponsePolicy
            (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
              (arrival 0) (arrival 1) switch12 switch21
              (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
              (ρ 0) (ρ 1)))) := by
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hq1 :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1) :=
    integrableOn_gn21SwitchProb_of_time_integrable (μ 1) switch21 switch12
      acceptAllPolicy (le_of_lt hswitch21_pos) hsum1
      (fun _ hτ => hτ) measurableSet_acceptAllPolicy htime1
  have hw1 : IntegrableOn (multiplicativePricing (m 1)) acceptAllPolicy (μ 1) :=
    integrableOn_multiplicativePricing (μ 1) (m 1) acceptAllPolicy htime1
  let response :=
    gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1)
  have hresponse_measurable : Measurable response := by
    dsimp [response]
    exact measurable_gn21MeasuredRightMarginalResponseAtCurrent
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1) (continuous_multiplicativePricing (m 1)).measurable
  have hresponse_integrable : IntegrableOn response acceptAllPolicy (μ 1) := by
    dsimp [response]
    exact integrableOn_gn21MeasuredRightMarginalResponseAtCurrent
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1) acceptAllPolicy hq1 hw1 htime1
  exact
    gn21AggregateMultiplicativeDynamicReward_le_update_right_of_marginal_le
      μ arrival m switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos htime1 hρ
      (lemma5PositiveResponsePolicy response)
      (lemma5PositiveResponsePolicy_subset_acceptAll response)
      (measurableSet_lemma5PositiveResponsePolicy response hresponse_measurable)
      (lemma5MarginalSetReward_le_positiveResponsePolicy
        (μ 1) response (ρ 1) hresponse_measurable hresponse_integrable
        (hρ 1).2 (hρ 1).1)

/-- A positively scaled strictly decreasing base response yields a source-open
non-surge cutoff replacement. -/
theorem gn21_open_left_cutoff_of_pos_scale
    (base marginal scale : TripLength → ℝ)
    (hcont : ContinuousOn base (Set.Ioi 0))
    (hanti : StrictAntiOn base (Set.Ioi 0))
    (hscale_pos : ∀ τ : TripLength, 0 < τ → 0 < scale τ)
    (hscale : ∀ τ : TripLength, 0 < τ → marginal τ = scale τ * base τ) :
    IsOpen (lemma5PositiveResponsePolicy marginal) ∧
      rejectsLongTripsFiniteOrInfiniteCutoff
        (lemma5PositiveResponsePolicy marginal) := by
  rw [lemma5PositiveResponsePolicy_eq_of_pos_scale base marginal scale
    hscale_pos hscale]
  exact lemma5PositiveResponsePolicy_open_left_cutoff_of_strictAnti
    base hcont hanti

/-- A positively scaled strictly increasing base response yields a source-open
surge cutoff replacement. -/
theorem gn21_open_right_cutoff_of_pos_scale
    (base marginal scale : TripLength → ℝ)
    (hcont : ContinuousOn base (Set.Ioi 0))
    (hmono : StrictMonoOn base (Set.Ioi 0))
    (hscale_pos : ∀ τ : TripLength, 0 < τ → 0 < scale τ)
    (hscale : ∀ τ : TripLength, 0 < τ → marginal τ = scale τ * base τ) :
    IsOpen (lemma5PositiveResponsePolicy marginal) ∧
      ((∃ t : ℝ, rejectsShortTrips t (lemma5PositiveResponsePolicy marginal)) ∨
        lemma5PositiveResponsePolicy marginal = ∅) := by
  rw [lemma5PositiveResponsePolicy_eq_of_pos_scale base marginal scale
    hscale_pos hscale]
  exact lemma5PositiveResponsePolicy_open_right_cutoff_of_strictMono
    base hcont hmono

/-- At a state-rate-ordered feasible pair, the actual non-surge marginal
positive-response policy is an open source cutoff. -/
theorem gn21MeasuredLeftPositiveResponse_open_cutoff_of_rate_lt
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    {ρ : Fin 2 → TripPolicy} (hρ : dynamicFeasibleMeasurablePolicy ρ)
    (hrate_lt :
      gn21MeasuredStateRewardRate (μ 0) (arrival 0)
          (multiplicativePricing (m 0)) (ρ 0) <
        gn21MeasuredStateRewardRate (μ 1) (arrival 1)
          (multiplicativePricing (m 1)) (ρ 1)) :
    IsOpen
        (lemma5PositiveResponsePolicy
          (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
            (ρ 0) (ρ 1))) ∧
      rejectsLongTripsFiniteOrInfiniteCutoff
        (lemma5PositiveResponsePolicy
          (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
            (ρ 0) (ρ 1))) := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hρ0_subset : ρ 0 ⊆ acceptAllPolicy := (hρ 0).1
  have hρ0_measurable : MeasurableSet (ρ 0) := (hρ 0).2
  have hρ1_subset : ρ 1 ⊆ acceptAllPolicy := (hρ 1).1
  have hρ1_measurable : MeasurableSet (ρ 1) := (hρ 1).2
  have hT0_pos : 0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
      (le_of_lt harrival0_pos) hρ0_measurable hρ0_subset
  have hT1_pos : 0 < gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (ρ 1)
      (le_of_lt harrival1_pos) hρ1_measurable hρ1_subset
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0) switch12
      switch21 (ρ 0) (le_of_lt harrival0_pos) hswitch12_pos hsum0
      hρ0_measurable hρ0_subset
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1) switch21
      switch12 (ρ 1) (le_of_lt harrival1_pos) hswitch21_pos hsum1
      hρ1_measurable hρ1_subset
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  let Ri := gn21MeasuredStateRewardRate (μ 0) (arrival 0)
    (multiplicativePricing (m 0)) (ρ 0)
  let Rj := gn21MeasuredStateRewardRate (μ 1) (arrival 1)
    (multiplicativePricing (m 1)) (ρ 1)
  let base :=
    gn21MeasuredLeftLemma6ResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (ρ 0) (ρ 1) Ri Rj
  let marginal :=
    gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1)
  let scale :=
    gn21MeasuredLeftLemma6ScaleAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21 (ρ 0) (ρ 1)
  have hWi :
      gn21ScaledStateEarning (μ 0) (arrival 0)
          (multiplicativePricing (m 0)) (ρ 0) =
        Ri * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 0) (arrival 0) Ri (multiplicativePricing (m 0)) (ρ 0)
      harrival0_pos hρ0_measurable hρ0_subset rfl
  have hWj :
      gn21ScaledStateEarning (μ 1) (arrival 1)
          (multiplicativePricing (m 1)) (ρ 1) =
        Rj * gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 1) (arrival 1) Rj (multiplicativePricing (m 1)) (ρ 1)
      harrival1_pos hρ1_measurable hρ1_subset rfl
  have hcont : ContinuousOn base (Set.Ioi 0) := by
    dsimp [base]
    exact continuousOn_gn21MeasuredLeftLemma6ResponseAtCurrent_multiplicative
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21 (m 0) Ri Rj
      (ρ 0) (ρ 1)
  have hanti : StrictAntiOn base (Set.Ioi 0) := by
    dsimp [base]
    exact strictAntiOn_gn21MeasuredLeftLemma6ResponseAtCurrent_multiplicative
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21 (m 0) Ri Rj
      (ρ 0) (ρ 1) (by simpa [Ri, Rj] using hrate_lt) hswitch12_pos hsum0
  have hscale_pos : ∀ τ : TripLength, 0 < τ → 0 < scale τ := by
    intro τ hτ
    dsimp [scale]
    exact gn21MeasuredLeftLemma6ScaleAtCurrent_pos
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (ρ 0) (ρ 1) hQ1_pos hT0_pos hT1_pos hden_pos hτ
  have hscale : ∀ τ : TripLength, 0 < τ → marginal τ = scale τ * base τ := by
    intro τ hτ
    dsimp [marginal, scale, base]
    exact gn21MeasuredLeftMarginalResponse_eq_scale_mul_lemma6ResponseAtCurrent
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1) Ri Rj τ (ne_of_gt hden_pos) (ne_of_gt hτ)
      (ne_of_gt hT0_pos) (ne_of_gt hT1_pos) hWi hWj
  simpa [marginal] using
    gn21_open_left_cutoff_of_pos_scale base marginal scale hcont hanti
      hscale_pos hscale

/-- At a state-rate-ordered feasible pair, the actual surge marginal
positive-response policy is an open source cutoff. -/
theorem gn21MeasuredRightPositiveResponse_open_cutoff_of_rate_lt
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    {ρ : Fin 2 → TripPolicy} (hρ : dynamicFeasibleMeasurablePolicy ρ)
    (hrate_lt :
      gn21MeasuredStateRewardRate (μ 0) (arrival 0)
          (multiplicativePricing (m 0)) (ρ 0) <
        gn21MeasuredStateRewardRate (μ 1) (arrival 1)
          (multiplicativePricing (m 1)) (ρ 1)) :
    IsOpen
        (lemma5PositiveResponsePolicy
          (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
            (ρ 0) (ρ 1))) ∧
      ((∃ t : ℝ,
          rejectsShortTrips t
            (lemma5PositiveResponsePolicy
              (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                (arrival 0) (arrival 1) switch12 switch21
                (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
                (ρ 0) (ρ 1)))) ∨
        lemma5PositiveResponsePolicy
          (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
            (ρ 0) (ρ 1)) = ∅) := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hρ0_subset : ρ 0 ⊆ acceptAllPolicy := (hρ 0).1
  have hρ0_measurable : MeasurableSet (ρ 0) := (hρ 0).2
  have hρ1_subset : ρ 1 ⊆ acceptAllPolicy := (hρ 1).1
  have hρ1_measurable : MeasurableSet (ρ 1) := (hρ 1).2
  have hT0_pos : 0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
      (le_of_lt harrival0_pos) hρ0_measurable hρ0_subset
  have hT1_pos : 0 < gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (ρ 1)
      (le_of_lt harrival1_pos) hρ1_measurable hρ1_subset
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0) switch12
      switch21 (ρ 0) (le_of_lt harrival0_pos) hswitch12_pos hsum0
      hρ0_measurable hρ0_subset
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1) switch21
      switch12 (ρ 1) (le_of_lt harrival1_pos) hswitch21_pos hsum1
      hρ1_measurable hρ1_subset
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  let Ri := gn21MeasuredStateRewardRate (μ 0) (arrival 0)
    (multiplicativePricing (m 0)) (ρ 0)
  let Rj := gn21MeasuredStateRewardRate (μ 1) (arrival 1)
    (multiplicativePricing (m 1)) (ρ 1)
  let base :=
    gn21MeasuredRightLemma6ResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 1)) (ρ 0) (ρ 1) Ri Rj
  let marginal :=
    gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1)
  let scale :=
    gn21MeasuredRightLemma6ScaleAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21 (ρ 0) (ρ 1)
  have hWi :
      gn21ScaledStateEarning (μ 0) (arrival 0)
          (multiplicativePricing (m 0)) (ρ 0) =
        Ri * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 0) (arrival 0) Ri (multiplicativePricing (m 0)) (ρ 0)
      harrival0_pos hρ0_measurable hρ0_subset rfl
  have hWj :
      gn21ScaledStateEarning (μ 1) (arrival 1)
          (multiplicativePricing (m 1)) (ρ 1) =
        Rj * gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 1) (arrival 1) Rj (multiplicativePricing (m 1)) (ρ 1)
      harrival1_pos hρ1_measurable hρ1_subset rfl
  have hcont : ContinuousOn base (Set.Ioi 0) := by
    dsimp [base]
    exact continuousOn_gn21MeasuredRightLemma6ResponseAtCurrent_multiplicative
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21 (m 1) Ri Rj
      (ρ 0) (ρ 1)
  have hmono : StrictMonoOn base (Set.Ioi 0) := by
    dsimp [base]
    exact strictMonoOn_gn21MeasuredRightLemma6ResponseAtCurrent_multiplicative
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21 (m 1) Ri Rj
      (ρ 0) (ρ 1) (by simpa [Ri, Rj] using hrate_lt) hswitch21_pos hsum1
  have hscale_pos : ∀ τ : TripLength, 0 < τ → 0 < scale τ := by
    intro τ hτ
    dsimp [scale]
    exact gn21MeasuredRightLemma6ScaleAtCurrent_pos
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (ρ 0) (ρ 1) hQ0_pos hT0_pos hT1_pos hden_pos hτ
  have hscale : ∀ τ : TripLength, 0 < τ → marginal τ = scale τ * base τ := by
    intro τ hτ
    dsimp [marginal, scale, base]
    exact gn21MeasuredRightMarginalResponse_eq_scale_mul_lemma6ResponseAtCurrent
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1) Ri Rj τ (ne_of_gt hden_pos) (ne_of_gt hτ)
      (ne_of_gt hT0_pos) (ne_of_gt hT1_pos) hWi hWj
  simpa [marginal] using
    gn21_open_right_cutoff_of_pos_scale base marginal scale hcont hmono
      hscale_pos hscale

/-- The source surge-state witness is a strict aggregate-reward improvement
whenever the current surge-state reward rate is no greater than the non-surge
rate.  The witness remains available as a universal rate-dominating right
policy for the subsequent cutoff replacement. -/
theorem gn21SourceSurgeStateDominance_exists_right_improvement_of_rate_le
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hsurge : gn21SourceSurgeStateDominance μ arrival w)
    {ρ : Fin 2 → TripPolicy} (hρ : dynamicFeasibleOpenPolicy ρ)
    (hrate_le :
      gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) (ρ 1) ≤
        gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) (ρ 0)) :
    ∃ σ2 : TripPolicy,
      σ2 ⊆ acceptAllPolicy ∧ IsOpen σ2 ∧
        (∀ σ1 : TripPolicy, σ1 ⊆ acceptAllPolicy → IsOpen σ1 →
          gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) σ1 <
            gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) σ2) ∧
        gn21AggregateDynamicRewardFunctional μ arrival switch12 switch21 w ρ <
          gn21AggregateDynamicRewardFunctional μ arrival switch12 switch21 w
            (Function.update ρ 1 σ2) := by
  rcases hsurge with ⟨σ2, hσ2_subset, hσ2_open, hdominates⟩
  refine ⟨σ2, hσ2_subset, hσ2_open, hdominates, ?_⟩
  have hρ_meas : dynamicFeasibleMeasurablePolicy ρ := hρ.to_measurable
  have hσ2_meas : MeasurableSet σ2 := hσ2_open.measurableSet
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hQi_pos :
      0 < gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0) switch12 switch21
      (ρ 0) (le_of_lt harrival0_pos) hswitch12_pos hsum0
      (hρ_meas 0).2 (hρ_meas 0).1
  have hQj_pos :
      0 < gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1) switch21 switch12
      (ρ 1) (le_of_lt harrival1_pos) hswitch21_pos hsum1
      (hρ_meas 1).2 (hρ_meas 1).1
  have hQj'_pos :
      0 < gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 σ2 :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1) switch21 switch12
      σ2 (le_of_lt harrival1_pos) hswitch21_pos hsum1 hσ2_meas hσ2_subset
  have hTi_pos : 0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
      (le_of_lt harrival0_pos) (hρ_meas 0).2 (hρ_meas 0).1
  have hTj_pos : 0 < gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (ρ 1)
      (le_of_lt harrival1_pos) (hρ_meas 1).2 (hρ_meas 1).1
  have hTj'_pos : 0 < gn21ScaledStateTime (μ 1) (arrival 1) σ2 :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) σ2
      (le_of_lt harrival1_pos) hσ2_meas hσ2_subset
  have hRi_lt_Rj' :
      gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) (ρ 0) <
        gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) σ2 :=
    hdominates (ρ 0) (hρ 0).1 (hρ 0).2
  have hWi :
      gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0) =
        gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) (ρ 0) *
          gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 0) (arrival 0)
      (gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) (ρ 0))
      (w 0) (ρ 0) harrival0_pos (hρ_meas 0).2 (hρ_meas 0).1 rfl
  have hWj :
      gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1) =
        gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) (ρ 1) *
          gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 1) (arrival 1)
      (gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) (ρ 1))
      (w 1) (ρ 1) harrival1_pos (hρ_meas 1).2 (hρ_meas 1).1 rfl
  have hWj' :
      gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) σ2 =
        gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) σ2 *
          gn21ScaledStateTime (μ 1) (arrival 1) σ2 :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 1) (arrival 1)
      (gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) σ2)
      (w 1) σ2 harrival1_pos hσ2_meas hσ2_subset rfl
  change
    gn21MeasuredAggregateRewardPrimitives
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (ρ 0) (ρ 1) <
      gn21MeasuredAggregateRewardPrimitives
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) ((Function.update ρ 1 σ2) 0)
        ((Function.update ρ 1 σ2) 1)
  simpa [gn21MeasuredAggregateRewardPrimitives] using
    gn21AggregateDynamicReward_lt_of_right_rate_crosses_left
      (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 σ2)
      (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
      (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
      (gn21ScaledStateTime (μ 1) (arrival 1) σ2)
      (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0))
      (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1))
      (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) σ2)
      (gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) (ρ 0))
      (gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) (ρ 1))
      (gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) σ2)
      hQi_pos hQj_pos hQj'_pos hTi_pos hTj_pos hTj'_pos hWi hWj hWj'
      hrate_le hRi_lt_Rj'

/-- Under a strict state-rate order, replace the non-surge component by an
open cutoff without decreasing aggregate reward. -/
theorem gn21_exists_open_left_cutoff_improvement_of_rate_lt
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    {ρ : Fin 2 → TripPolicy} (hρ : dynamicFeasibleOpenPolicy ρ)
    (hrate_lt :
      gn21MeasuredStateRewardRate (μ 0) (arrival 0)
          (multiplicativePricing (m 0)) (ρ 0) <
        gn21MeasuredStateRewardRate (μ 1) (arrival 1)
          (multiplicativePricing (m 1)) (ρ 1)) :
    ∃ κ : Fin 2 → TripPolicy,
      dynamicFeasibleOpenPolicy κ ∧
        gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m ρ ≤
          gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m κ ∧
        rejectsLongTripsFiniteOrInfiniteCutoff (κ 0) ∧ κ 1 = ρ 1 := by
  let candidate := gn21LeftPositiveResponsePolicy μ arrival m switch12 switch21 ρ
  have hcandidate_open_shape :
      IsOpen candidate ∧ rejectsLongTripsFiniteOrInfiniteCutoff candidate := by
    dsimp [candidate, gn21LeftPositiveResponsePolicy]
    exact gn21MeasuredLeftPositiveResponse_open_cutoff_of_rate_lt
      μ arrival m switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos hρ.to_measurable hrate_lt
  have hcandidate_subset : candidate ⊆ acceptAllPolicy := by
    dsimp [candidate, gn21LeftPositiveResponsePolicy]
    exact lemma5PositiveResponsePolicy_subset_acceptAll _
  let κ : Fin 2 → TripPolicy := Function.update ρ 0 candidate
  have hκ_open : dynamicFeasibleOpenPolicy κ := by
    dsimp [κ]
    exact dynamicFeasibleOpenPolicy_update hρ 0 candidate hcandidate_subset
      hcandidate_open_shape.1
  have hreward :
      gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m ρ ≤
        gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m κ := by
    dsimp [κ, candidate, gn21LeftPositiveResponsePolicy]
    exact gn21AggregateMultiplicativeDynamicReward_le_update_left_positiveResponse
      μ arrival m switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos htime0 hρ.to_measurable
  refine ⟨κ, hκ_open, hreward, ?_, ?_⟩
  · simpa [κ] using hcandidate_open_shape.2
  · simp [κ]

/-- Under a strict state-rate order, replace the surge component by an open
cutoff without decreasing aggregate reward. -/
theorem gn21_exists_open_right_cutoff_improvement_of_rate_lt
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime1 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    {ρ : Fin 2 → TripPolicy} (hρ : dynamicFeasibleOpenPolicy ρ)
    (hleft_shape : rejectsLongTripsFiniteOrInfiniteCutoff (ρ 0))
    (hrate_lt :
      gn21MeasuredStateRewardRate (μ 0) (arrival 0)
          (multiplicativePricing (m 0)) (ρ 0) <
        gn21MeasuredStateRewardRate (μ 1) (arrival 1)
          (multiplicativePricing (m 1)) (ρ 1)) :
    ∃ κ : Fin 2 → TripPolicy,
      dynamicFeasibleOpenPolicy κ ∧
        gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m ρ ≤
          gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m κ ∧
        rejectsLongTripsFiniteOrInfiniteCutoff (κ 0) ∧
          ((∃ t : ℝ, rejectsShortTrips t (κ 1)) ∨ κ 1 = ∅) := by
  let candidate := gn21RightPositiveResponsePolicy μ arrival m switch12 switch21 ρ
  have hcandidate_open_shape :
      IsOpen candidate ∧
        ((∃ t : ℝ, rejectsShortTrips t candidate) ∨ candidate = ∅) := by
    dsimp [candidate, gn21RightPositiveResponsePolicy]
    exact gn21MeasuredRightPositiveResponse_open_cutoff_of_rate_lt
      μ arrival m switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos hρ.to_measurable hrate_lt
  have hcandidate_subset : candidate ⊆ acceptAllPolicy := by
    dsimp [candidate, gn21RightPositiveResponsePolicy]
    exact lemma5PositiveResponsePolicy_subset_acceptAll _
  let κ : Fin 2 → TripPolicy := Function.update ρ 1 candidate
  have hκ_open : dynamicFeasibleOpenPolicy κ := by
    dsimp [κ]
    exact dynamicFeasibleOpenPolicy_update hρ 1 candidate hcandidate_subset
      hcandidate_open_shape.1
  have hreward :
      gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m ρ ≤
        gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m κ := by
    dsimp [κ, candidate, gn21RightPositiveResponsePolicy]
    exact gn21AggregateMultiplicativeDynamicReward_le_update_right_positiveResponse
      μ arrival m switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos htime1 hρ.to_measurable
  refine ⟨κ, hκ_open, hreward, ?_, ?_⟩
  · simpa [κ] using hleft_shape
  · simpa [κ] using hcandidate_open_shape.2

/-- Every source-open multiplicative policy is weakly dominated by an open
pair of the exact Theorem-2 cutoff forms.  The proof repairs the source's
rate-order gap: after the left replacement it checks the rate order again and
uses the surge witness only when that order has reversed. -/
theorem gn21_exists_open_multiplicative_cutoff_dominating_policy
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime1 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hsurge : gn21SourceSurgeStateDominance μ arrival
      (fun i => multiplicativePricing (m i)))
    (ρ : Fin 2 → TripPolicy) (hρ : dynamicFeasibleOpenPolicy ρ) :
    ∃ κ : Fin 2 → TripPolicy,
      dynamicFeasibleOpenPolicy κ ∧
        gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m ρ ≤
          gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m κ ∧
        rejectsLongTripsFiniteOrInfiniteCutoff (κ 0) ∧
          ((∃ t : ℝ, rejectsShortTrips t (κ 1)) ∨ κ 1 = ∅) := by
  let R := gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m
  let rate0 : (Fin 2 → TripPolicy) → ℝ := fun σ =>
    gn21MeasuredStateRewardRate (μ 0) (arrival 0)
      (multiplicativePricing (m 0)) (σ 0)
  let rate1 : (Fin 2 → TripPolicy) → ℝ := fun σ =>
    gn21MeasuredStateRewardRate (μ 1) (arrival 1)
      (multiplicativePricing (m 1)) (σ 1)
  by_cases hrate_le : rate1 ρ ≤ rate0 ρ
  · rcases
        gn21SourceSurgeStateDominance_exists_right_improvement_of_rate_le
          μ arrival switch12 switch21
          (fun i => multiplicativePricing (m i))
          harrival0_pos harrival1_pos hswitch12_pos hswitch21_pos hsurge hρ
          (by simpa [rate0, rate1] using hrate_le) with
      ⟨σ2, hσ2_subset, hσ2_open, hdominates, hsource_improves⟩
    let ρA : Fin 2 → TripPolicy := Function.update ρ 1 σ2
    have hρA_open : dynamicFeasibleOpenPolicy ρA := by
      dsimp [ρA]
      exact dynamicFeasibleOpenPolicy_update hρ 1 σ2 hσ2_subset hσ2_open
    have hsource_improves_R : R ρ < R ρA := by
      simpa [R, ρA, gn21AggregateMultiplicativeDynamicReward] using
        hsource_improves
    have hρA_rate_lt : rate0 ρA < rate1 ρA := by
      have h := hdominates (ρA 0) (hρA_open 0).1 (hρA_open 0).2
      simpa [rate0, rate1, ρA] using h
    rcases gn21_exists_open_left_cutoff_improvement_of_rate_lt
        μ arrival m switch12 switch21 harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos htime0 hρA_open
        (by simpa [rate0, rate1] using hρA_rate_lt) with
      ⟨ρB, hρB_open, hA_le_B, hleft_B, hρB_one⟩
    have hρA_one : ρA 1 = σ2 := by simp [ρA]
    have hρB_one' : ρB 1 = σ2 := hρB_one.trans hρA_one
    have hρB_rate_lt : rate0 ρB < rate1 ρB := by
      have h := hdominates (ρB 0) (hρB_open 0).1 (hρB_open 0).2
      simpa [rate0, rate1, hρB_one'] using h
    rcases gn21_exists_open_right_cutoff_improvement_of_rate_lt
        μ arrival m switch12 switch21 harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos htime1 hρB_open hleft_B
        (by simpa [rate0, rate1] using hρB_rate_lt) with
      ⟨κ, hκ_open, hB_le_κ, hleft_κ, hright_κ⟩
    refine ⟨κ, hκ_open, ?_, hleft_κ, hright_κ⟩
    exact (le_of_lt hsource_improves_R).trans (hA_le_B.trans hB_le_κ)
  · have hρ_rate_lt : rate0 ρ < rate1 ρ := lt_of_not_ge hrate_le
    rcases gn21_exists_open_left_cutoff_improvement_of_rate_lt
        μ arrival m switch12 switch21 harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos htime0 hρ
        (by simpa [rate0, rate1] using hρ_rate_lt) with
      ⟨ρB, hρB_open, hρ_le_B, hleft_B, hρB_one⟩
    by_cases hρB_rate_le : rate1 ρB ≤ rate0 ρB
    · rcases
          gn21SourceSurgeStateDominance_exists_right_improvement_of_rate_le
            μ arrival switch12 switch21
            (fun i => multiplicativePricing (m i))
            harrival0_pos harrival1_pos hswitch12_pos hswitch21_pos hsurge
            hρB_open (by simpa [rate0, rate1] using hρB_rate_le) with
        ⟨σ2, hσ2_subset, hσ2_open, hdominates, hsource_improves⟩
      let ρC : Fin 2 → TripPolicy := Function.update ρB 1 σ2
      have hρC_open : dynamicFeasibleOpenPolicy ρC := by
        dsimp [ρC]
        exact dynamicFeasibleOpenPolicy_update hρB_open 1 σ2 hσ2_subset hσ2_open
      have hsource_improves_R : R ρB < R ρC := by
        simpa [R, ρC, gn21AggregateMultiplicativeDynamicReward] using
          hsource_improves
      have hleft_C : rejectsLongTripsFiniteOrInfiniteCutoff (ρC 0) := by
        simpa [ρC] using hleft_B
      have hρC_one : ρC 1 = σ2 := by simp [ρC]
      have hρC_rate_lt : rate0 ρC < rate1 ρC := by
        have h := hdominates (ρC 0) (hρC_open 0).1 (hρC_open 0).2
        simpa [rate0, rate1, hρC_one] using h
      rcases gn21_exists_open_right_cutoff_improvement_of_rate_lt
          μ arrival m switch12 switch21 harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos htime1 hρC_open hleft_C
          (by simpa [rate0, rate1] using hρC_rate_lt) with
        ⟨κ, hκ_open, hC_le_κ, hleft_κ, hright_κ⟩
      refine ⟨κ, hκ_open, ?_, hleft_κ, hright_κ⟩
      exact hρ_le_B.trans ((le_of_lt hsource_improves_R).trans hC_le_κ)
    · have hρB_rate_lt : rate0 ρB < rate1 ρB := lt_of_not_ge hρB_rate_le
      rcases gn21_exists_open_right_cutoff_improvement_of_rate_lt
          μ arrival m switch12 switch21 harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos htime1 hρB_open hleft_B
          (by simpa [rate0, rate1] using hρB_rate_lt) with
        ⟨κ, hκ_open, hB_le_κ, hleft_κ, hright_κ⟩
      exact ⟨κ, hκ_open, hρ_le_B.trans hB_le_κ, hleft_κ, hright_κ⟩

end GN21DriverSurgePricing
