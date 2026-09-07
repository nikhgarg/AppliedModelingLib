import GN21DriverSurgePricing.CutoffCanonicalization

/-!
# Cutoff-Family Attainment for GN21 Theorem 2

The source proof replaces arbitrary open policies by cutoff policies but does
not justify that the resulting noncompact parameter family has a maximizer.
This module closes that gap by adjoining the two source endpoints explicitly:
`∞` means accept-all for the non-surge cutoff and the empty policy for the
surge cutoff.
-/

open AppliedModelingLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal symmDiff

namespace GN21DriverSurgePricing

/-- An extended non-surge cutoff.  The `∞` endpoint is the source's
accept-all policy. -/
def gn21LeftExtendedCutoffPolicy (t : ℝ≥0∞) : TripPolicy :=
  ENNReal.recTopCoe acceptAllPolicy
    (fun u : NNReal => rejectLongTripsPolicy (u : ℝ)) t

/-- An extended surge cutoff.  The `∞` endpoint is the source's empty policy. -/
def gn21RightExtendedCutoffPolicy (t : ℝ≥0∞) : TripPolicy :=
  ENNReal.recTopCoe (∅ : TripPolicy)
    (fun u : NNReal => rejectShortTripsPolicy (u : ℝ)) t

@[simp] theorem gn21LeftExtendedCutoffPolicy_top :
    gn21LeftExtendedCutoffPolicy (∞ : ℝ≥0∞) = acceptAllPolicy := rfl

@[simp] theorem gn21LeftExtendedCutoffPolicy_coe (t : NNReal) :
    gn21LeftExtendedCutoffPolicy (t : ℝ≥0∞) =
      rejectLongTripsPolicy (t : ℝ) := rfl

@[simp] theorem gn21RightExtendedCutoffPolicy_top :
    gn21RightExtendedCutoffPolicy (∞ : ℝ≥0∞) = ∅ := rfl

@[simp] theorem gn21RightExtendedCutoffPolicy_coe (t : NNReal) :
    gn21RightExtendedCutoffPolicy (t : ℝ≥0∞) =
      rejectShortTripsPolicy (t : ℝ) := rfl

/-- The two-state policy induced by a pair of extended cutoff parameters. -/
def gn21ExtendedCutoffDynamicPolicy (left right : ℝ≥0∞) : Fin 2 → TripPolicy :=
  ![gn21LeftExtendedCutoffPolicy left, gn21RightExtendedCutoffPolicy right]

@[simp] theorem gn21ExtendedCutoffDynamicPolicy_zero (left right : ℝ≥0∞) :
    gn21ExtendedCutoffDynamicPolicy left right 0 =
      gn21LeftExtendedCutoffPolicy left := by
  rfl

@[simp] theorem gn21ExtendedCutoffDynamicPolicy_one (left right : ℝ≥0∞) :
    gn21ExtendedCutoffDynamicPolicy left right 1 =
      gn21RightExtendedCutoffPolicy right := by
  rfl

/-- The compact parameter domain contains nonnegative finite cutoffs and the
two source `∞` endpoints. -/
def gn21CutoffParameterSpace : Set (ℝ≥0∞ × ℝ≥0∞) := Set.univ

theorem isCompact_gn21CutoffParameterSpace :
    IsCompact gn21CutoffParameterSpace := by
  simpa [gn21CutoffParameterSpace] using
    (isCompact_univ.prod isCompact_univ : IsCompact (Set.univ ×ˢ Set.univ))

theorem gn21CutoffParameterSpace_nonempty :
    gn21CutoffParameterSpace.Nonempty := by
  refine ⟨(0, 0), ?_⟩
  simp [gn21CutoffParameterSpace]

theorem gn21LeftExtendedCutoffPolicy_subset_acceptAll (t : ℝ≥0∞) :
    gn21LeftExtendedCutoffPolicy t ⊆ acceptAllPolicy := by
  cases t using ENNReal.recTopCoe with
  | top => exact fun _ h => h
  | coe t => exact rejectLongTripsPolicy_subset_acceptAll (t : ℝ)

theorem gn21RightExtendedCutoffPolicy_subset_acceptAll (t : ℝ≥0∞) :
    gn21RightExtendedCutoffPolicy t ⊆ acceptAllPolicy := by
  cases t using ENNReal.recTopCoe with
  | top => simp
  | coe t => exact rejectShortTripsPolicy_subset_acceptAll (t : ℝ)

theorem gn21LeftExtendedCutoffPolicy_open (t : ℝ≥0∞) :
    IsOpen (gn21LeftExtendedCutoffPolicy t) := by
  cases t using ENNReal.recTopCoe with
  | top =>
      simpa [gn21LeftExtendedCutoffPolicy, acceptAllPolicy,
        positiveTripLengths, positiveRealAcceptAll] using
        (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
  | coe t =>
      simpa [gn21LeftExtendedCutoffPolicy, rejectLongTripsPolicy] using
        ((isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).inter
          (isOpen_Iio : IsOpen (Set.Iio (t : ℝ))))

theorem gn21RightExtendedCutoffPolicy_open (t : ℝ≥0∞) :
    IsOpen (gn21RightExtendedCutoffPolicy t) := by
  cases t using ENNReal.recTopCoe with
  | top =>
      change IsOpen (∅ : TripPolicy)
      exact isOpen_empty
  | coe t =>
      simpa [gn21RightExtendedCutoffPolicy, rejectShortTripsPolicy] using
        ((isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).inter
          (isOpen_Ioi : IsOpen (Set.Ioi (t : ℝ))))

theorem dynamicFeasibleOpenPolicy_gn21ExtendedCutoffDynamicPolicy
    (left right : ℝ≥0∞) :
    dynamicFeasibleOpenPolicy (gn21ExtendedCutoffDynamicPolicy left right) := by
  intro i
  fin_cases i
  · exact ⟨gn21LeftExtendedCutoffPolicy_subset_acceptAll left,
      gn21LeftExtendedCutoffPolicy_open left⟩
  · exact ⟨gn21RightExtendedCutoffPolicy_subset_acceptAll right,
      gn21RightExtendedCutoffPolicy_open right⟩

/-- A nonpositive finite non-surge cutoff is the empty policy on the source
positive-trip domain. -/
theorem gn21_rejectLongTripsPolicy_eq_empty_of_nonpos
    {t : ℝ} (ht : t ≤ 0) : rejectLongTripsPolicy t = ∅ := by
  ext τ
  constructor
  · intro hτ
    have hτ' : 0 < τ ∧ τ < t := by
      simpa [rejectLongTripsPolicy] using hτ
    exact False.elim (by linarith [hτ'.1, hτ'.2, ht])
  · simp

/-- A nonpositive finite surge cutoff is accept-all on the source
positive-trip domain. -/
theorem gn21_rejectShortTripsPolicy_eq_acceptAll_of_nonpos
    {t : ℝ} (ht : t ≤ 0) : rejectShortTripsPolicy t = acceptAllPolicy := by
  ext τ
  constructor
  · intro hτ
    exact hτ.1
  · intro hτ
    have ht_lt_τ : t < τ := lt_of_le_of_lt ht hτ
    exact ⟨hτ, ht_lt_τ⟩

@[simp] theorem gn21LeftExtendedCutoffPolicy_zero :
    gn21LeftExtendedCutoffPolicy (0 : ℝ≥0∞) = ∅ := by
  change rejectLongTripsPolicy (0 : ℝ) = ∅
  exact gn21_rejectLongTripsPolicy_eq_empty_of_nonpos le_rfl

@[simp] theorem gn21RightExtendedCutoffPolicy_zero :
    gn21RightExtendedCutoffPolicy (0 : ℝ≥0∞) = acceptAllPolicy := by
  change rejectShortTripsPolicy (0 : ℝ) = acceptAllPolicy
  exact gn21_rejectShortTripsPolicy_eq_acceptAll_of_nonpos le_rfl

/-- Every feasible source non-surge cutoff form has an exact representative in
the compact extended-cutoff family. -/
theorem gn21_exists_leftExtendedCutoffPolicy_eq_of_shape
    {σ : TripPolicy} (hσ_subset : σ ⊆ acceptAllPolicy)
    (hshape : rejectsLongTripsFiniteOrInfiniteCutoff σ) :
    ∃ t : ℝ≥0∞, σ = gn21LeftExtendedCutoffPolicy t := by
  rcases hshape with ⟨r, hr⟩ | hall
  · have hσ_eq : σ = rejectLongTripsPolicy r :=
      eq_rejectLongTripsPolicy_of_rejectsLongTrips_of_subset_acceptAll hr hσ_subset
    by_cases hr_pos : 0 < r
    · let u : NNReal := ⟨r, le_of_lt hr_pos⟩
      refine ⟨(u : ℝ≥0∞), ?_⟩
      calc
        σ = rejectLongTripsPolicy r := hσ_eq
        _ = gn21LeftExtendedCutoffPolicy (u : ℝ≥0∞) := by
          have hu : (u : ℝ) = r := by rfl
          simp [hu]
    · have hr_nonpos : r ≤ 0 := le_of_not_gt hr_pos
      have hσ_empty : σ = ∅ :=
        hσ_eq.trans (gn21_rejectLongTripsPolicy_eq_empty_of_nonpos hr_nonpos)
      exact ⟨0, by simpa using hσ_empty⟩
  · have hσ_all : σ = acceptAllPolicy := by
      ext τ
      constructor
      · intro hτ
        exact hσ_subset hτ
      · intro hτ
        exact hall hτ
    exact ⟨∞, by simpa using hσ_all⟩

/-- Every feasible source surge cutoff form, including its empty `∞` endpoint,
has an exact representative in the compact extended-cutoff family. -/
theorem gn21_exists_rightExtendedCutoffPolicy_eq_of_shape
    {σ : TripPolicy} (hσ_subset : σ ⊆ acceptAllPolicy)
    (hshape : (∃ t : ℝ, rejectsShortTrips t σ) ∨ σ = ∅) :
    ∃ t : ℝ≥0∞, σ = gn21RightExtendedCutoffPolicy t := by
  rcases hshape with ⟨r, hr⟩ | hσ_empty
  · have hσ_eq : σ = rejectShortTripsPolicy r :=
      eq_rejectShortTripsPolicy_of_rejectsShortTrips_of_subset_acceptAll hr hσ_subset
    by_cases hr_pos : 0 < r
    · let u : NNReal := ⟨r, le_of_lt hr_pos⟩
      refine ⟨(u : ℝ≥0∞), ?_⟩
      calc
        σ = rejectShortTripsPolicy r := hσ_eq
        _ = gn21RightExtendedCutoffPolicy (u : ℝ≥0∞) := by
          have hu : (u : ℝ) = r := by rfl
          simp [hu]
    · have hr_nonpos : r ≤ 0 := le_of_not_gt hr_pos
      have hσ_all : σ = acceptAllPolicy :=
        hσ_eq.trans (gn21_rejectShortTripsPolicy_eq_acceptAll_of_nonpos hr_nonpos)
      exact ⟨0, by simpa using hσ_all⟩
  · exact ⟨∞, by simpa using hσ_empty⟩

/-- Nearby finite non-surge cutoffs differ only in the interval between their
thresholds. -/
theorem gn21_symmDiff_rejectLongTripsPolicy_subset_Icc (a b : ℝ) :
    rejectLongTripsPolicy a ∆ rejectLongTripsPolicy b ⊆
      Set.Icc (a - |b - a|) (a + |b - a|) := by
  intro τ hτ
  rw [Set.mem_symmDiff] at hτ
  rcases hτ with ⟨hτa, hτb⟩ | ⟨hτb, hτa⟩
  · have hτa' : 0 < τ ∧ τ < a := by
      simpa [rejectLongTripsPolicy] using hτa
    have hb_le_τ : b ≤ τ := by
      by_contra hb_le
      have hτ_lt_b : τ < b := lt_of_not_ge hb_le
      exact hτb (by simpa [rejectLongTripsPolicy] using ⟨hτa'.1, hτ_lt_b⟩)
    constructor
    · have habs : a - |b - a| ≤ b := by
        linarith [neg_abs_le (b - a)]
      exact habs.trans hb_le_τ
    · have habs : a ≤ a + |b - a| := by linarith [abs_nonneg (b - a)]
      exact (le_of_lt hτa'.2).trans habs
  · have hτb' : 0 < τ ∧ τ < b := by
      simpa [rejectLongTripsPolicy] using hτb
    have ha_le_τ : a ≤ τ := by
      by_contra ha_le
      have hτ_lt_a : τ < a := lt_of_not_ge ha_le
      exact hτa (by simpa [rejectLongTripsPolicy] using ⟨hτb'.1, hτ_lt_a⟩)
    constructor
    · have habs : a - |b - a| ≤ a := by linarith [abs_nonneg (b - a)]
      exact habs.trans ha_le_τ
    · have habs : b ≤ a + |b - a| := by
        linarith [le_abs_self (b - a)]
      exact (le_of_lt hτb'.2).trans habs

/-- Nearby finite surge cutoffs differ only in the interval between their
thresholds. -/
theorem gn21_symmDiff_rejectShortTripsPolicy_subset_Icc (a b : ℝ) :
    rejectShortTripsPolicy a ∆ rejectShortTripsPolicy b ⊆
      Set.Icc (a - |b - a|) (a + |b - a|) := by
  intro τ hτ
  rw [Set.mem_symmDiff] at hτ
  rcases hτ with ⟨hτa, hτb⟩ | ⟨hτb, hτa⟩
  · have hτa' : 0 < τ ∧ a < τ := by
      simpa [rejectShortTripsPolicy] using hτa
    have hτ_le_b : τ ≤ b := by
      by_contra hτ_le
      have hb_lt_τ : b < τ := lt_of_not_ge hτ_le
      exact hτb (by simpa [rejectShortTripsPolicy] using ⟨hτa'.1, hb_lt_τ⟩)
    constructor
    · have habs : a - |b - a| ≤ a := by linarith [abs_nonneg (b - a)]
      exact habs.trans (le_of_lt hτa'.2)
    · have habs : b ≤ a + |b - a| := by
        linarith [le_abs_self (b - a)]
      exact hτ_le_b.trans habs
  · have hτb' : 0 < τ ∧ b < τ := by
      simpa [rejectShortTripsPolicy] using hτb
    have hτ_le_a : τ ≤ a := by
      by_contra hτ_le
      have ha_lt_τ : a < τ := lt_of_not_ge hτ_le
      exact hτa (by simpa [rejectShortTripsPolicy] using ⟨hτb'.1, ha_lt_τ⟩)
    constructor
    · have habs : a - |b - a| ≤ b := by
        linarith [neg_abs_le (b - a)]
      exact habs.trans (le_of_lt hτb'.2)
    · have habs : a ≤ a + |b - a| := by linarith [abs_nonneg (b - a)]
      exact hτ_le_a.trans habs

/-- Finite non-surge cutoff integrals are continuous under a nonatomic finite
source measure. -/
theorem continuousAt_gn21FiniteLeftCutoff_setIntegral
    (μ : Measure TripLength) [NoAtoms μ] [IsFiniteMeasure μ]
    (f : TripLength → ℝ)
    (hfin : IntegrableOn f acceptAllPolicy μ) (a : NNReal) :
    ContinuousAt
      (fun b : NNReal => ∫ τ in rejectLongTripsPolicy (b : ℝ), f τ ∂μ) a := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  rcases setIntegral_symmDiffContinuousAt_of_integrableOn μ f hfin
      (measurableSet_rejectLongTripsPolicy (a : ℝ))
      (rejectLongTripsPolicy_subset_acceptAll (a : ℝ)) ε hε with
    ⟨δ, hδ_ne, hδ⟩
  have hδ_pos : 0 < δ := pos_iff_ne_zero.mpr hδ_ne
  have hdist :
      Filter.Tendsto (fun b : NNReal => |(b : ℝ) - (a : ℝ)|) (𝓝 a) (𝓝 0) := by
    simpa only [ContinuousAt, sub_self, abs_zero] using
      ((NNReal.continuous_coe.sub continuous_const).abs.continuousAt :
        ContinuousAt (fun b : NNReal => |(b : ℝ) - (a : ℝ)|) a)
  have hmeasure :
      Filter.Tendsto
        (fun b : NNReal =>
          μ (Set.Icc ((a : ℝ) - |(b : ℝ) - (a : ℝ)|)
            ((a : ℝ) + |(b : ℝ) - (a : ℝ)|)))
        (𝓝 a) (𝓝 0) :=
    (tendsto_measure_Icc μ (a : ℝ)).comp hdist
  have hsmall : ∀ᶠ b : NNReal in 𝓝 a,
      μ (Set.Icc ((a : ℝ) - |(b : ℝ) - (a : ℝ)|)
        ((a : ℝ) + |(b : ℝ) - (a : ℝ)|)) < δ :=
    (tendsto_order.1 hmeasure).2 δ hδ_pos
  filter_upwards [hsmall] with b hb
  have hsymm :
      μ (rejectLongTripsPolicy (a : ℝ) ∆ rejectLongTripsPolicy (b : ℝ)) < δ :=
    lt_of_le_of_lt
      (measure_mono
        (gn21_symmDiff_rejectLongTripsPolicy_subset_Icc (a : ℝ) (b : ℝ))) hb
  simpa [Real.dist_eq] using
    hδ (rejectLongTripsPolicy (b : ℝ))
      (measurableSet_rejectLongTripsPolicy (b : ℝ))
      (rejectLongTripsPolicy_subset_acceptAll (b : ℝ)) hsymm

/-- Finite surge cutoff integrals are continuous under a nonatomic finite
source measure. -/
theorem continuousAt_gn21FiniteRightCutoff_setIntegral
    (μ : Measure TripLength) [NoAtoms μ] [IsFiniteMeasure μ]
    (f : TripLength → ℝ)
    (hfin : IntegrableOn f acceptAllPolicy μ) (a : NNReal) :
    ContinuousAt
      (fun b : NNReal => ∫ τ in rejectShortTripsPolicy (b : ℝ), f τ ∂μ) a := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  rcases setIntegral_symmDiffContinuousAt_of_integrableOn μ f hfin
      (measurableSet_rejectShortTripsPolicy (a : ℝ))
      (rejectShortTripsPolicy_subset_acceptAll (a : ℝ)) ε hε with
    ⟨δ, hδ_ne, hδ⟩
  have hδ_pos : 0 < δ := pos_iff_ne_zero.mpr hδ_ne
  have hdist :
      Filter.Tendsto (fun b : NNReal => |(b : ℝ) - (a : ℝ)|) (𝓝 a) (𝓝 0) := by
    simpa only [ContinuousAt, sub_self, abs_zero] using
      ((NNReal.continuous_coe.sub continuous_const).abs.continuousAt :
        ContinuousAt (fun b : NNReal => |(b : ℝ) - (a : ℝ)|) a)
  have hmeasure :
      Filter.Tendsto
        (fun b : NNReal =>
          μ (Set.Icc ((a : ℝ) - |(b : ℝ) - (a : ℝ)|)
            ((a : ℝ) + |(b : ℝ) - (a : ℝ)|)))
        (𝓝 a) (𝓝 0) :=
    (tendsto_measure_Icc μ (a : ℝ)).comp hdist
  have hsmall : ∀ᶠ b : NNReal in 𝓝 a,
      μ (Set.Icc ((a : ℝ) - |(b : ℝ) - (a : ℝ)|)
        ((a : ℝ) + |(b : ℝ) - (a : ℝ)|)) < δ :=
    (tendsto_order.1 hmeasure).2 δ hδ_pos
  filter_upwards [hsmall] with b hb
  have hsymm :
      μ (rejectShortTripsPolicy (a : ℝ) ∆ rejectShortTripsPolicy (b : ℝ)) < δ :=
    lt_of_le_of_lt
      (measure_mono
        (gn21_symmDiff_rejectShortTripsPolicy_subset_Icc (a : ℝ) (b : ℝ))) hb
  simpa [Real.dist_eq] using
    hδ (rejectShortTripsPolicy (b : ℝ))
      (measurableSet_rejectShortTripsPolicy (b : ℝ))
      (rejectShortTripsPolicy_subset_acceptAll (b : ℝ)) hsymm

/-- At a large extended non-surge cutoff, the difference from accept-all lies
inside the corresponding strict upper tail. -/
theorem gn21_symmDiff_acceptAll_leftExtendedCutoff_subset_Ioi
    (N : ℕ) {t : ℝ≥0∞}
    (hN_lt_t : (↑(N : NNReal) : ℝ≥0∞) < t) :
    acceptAllPolicy ∆ gn21LeftExtendedCutoffPolicy t ⊆ Set.Ioi (N : ℝ) := by
  cases t using ENNReal.recTopCoe with
  | top =>
      change acceptAllPolicy ∆ acceptAllPolicy ⊆ Set.Ioi (N : ℝ)
      simp
  | coe u =>
      have hN_lt_u_nn : (N : NNReal) < u := ENNReal.coe_lt_coe.mp hN_lt_t
      have hN_lt_u : (N : ℝ) < (u : ℝ) := NNReal.coe_lt_coe.mp hN_lt_u_nn
      intro τ hτ
      rw [Set.mem_symmDiff] at hτ
      rcases hτ with ⟨haccept, hnotcut⟩ | ⟨hcut, hnotaccept⟩
      · have haccept' : 0 < τ := haccept
        have hnotcut' : τ ∉ rejectLongTripsPolicy (u : ℝ) := by
          simpa [gn21LeftExtendedCutoffPolicy] using hnotcut
        have hu_le_τ : (u : ℝ) ≤ τ := by
          by_contra hu_le
          have hτ_lt_u : τ < (u : ℝ) := lt_of_not_ge hu_le
          exact hnotcut' (by simpa [rejectLongTripsPolicy] using ⟨haccept', hτ_lt_u⟩)
        exact hN_lt_u.trans_le hu_le_τ
      · have hcut' : 0 < τ :=
          (by
            have : τ ∈ rejectLongTripsPolicy (u : ℝ) := by
              simpa [gn21LeftExtendedCutoffPolicy] using hcut
            exact this.1)
        exact False.elim (hnotaccept hcut')

/-- At a large extended surge cutoff, the policy itself lies inside the
corresponding strict upper tail. -/
theorem gn21_symmDiff_empty_rightExtendedCutoff_subset_Ioi
    (N : ℕ) {t : ℝ≥0∞}
    (hN_lt_t : (↑(N : NNReal) : ℝ≥0∞) < t) :
    (∅ : TripPolicy) ∆ gn21RightExtendedCutoffPolicy t ⊆ Set.Ioi (N : ℝ) := by
  cases t using ENNReal.recTopCoe with
  | top =>
      change (∅ : TripPolicy) ∆ ∅ ⊆ Set.Ioi (N : ℝ)
      simp
  | coe u =>
      have hN_lt_u_nn : (N : NNReal) < u := ENNReal.coe_lt_coe.mp hN_lt_t
      have hN_lt_u : (N : ℝ) < (u : ℝ) := NNReal.coe_lt_coe.mp hN_lt_u_nn
      intro τ hτ
      rw [Set.mem_symmDiff] at hτ
      rcases hτ with ⟨hempty, _⟩ | ⟨hcut, _⟩
      · simp at hempty
      · have hcut' : (u : ℝ) < τ := by
          have : τ ∈ rejectShortTripsPolicy (u : ℝ) := by
            simpa [gn21RightExtendedCutoffPolicy] using hcut
          exact this.2
        exact hN_lt_u.trans hcut'

/-- The finite measure of a strict upper tail vanishes as the threshold tends
to infinity. -/
theorem gn21_tendsto_measure_Ioi_nat_atTop
    (μ : Measure TripLength) [IsFiniteMeasure μ] :
    Filter.Tendsto (fun n : ℕ => μ (Set.Ioi (n : ℝ))) Filter.atTop (𝓝 0) := by
  have hinter : (⋂ n : ℕ, Set.Ioi (n : ℝ)) = (∅ : Set TripLength) := by
    ext τ
    constructor
    · intro hτ
      rcases exists_nat_ge τ with ⟨n, hn⟩
      have hτn : τ ∈ Set.Ioi (n : ℝ) := Set.mem_iInter.mp hτ n
      exact False.elim ((not_lt_of_ge hn) hτn)
    · simp
  have hmono : Antitone (fun n : ℕ => Set.Ioi (n : ℝ)) := by
    intro m n hmn
    exact Set.Ioi_subset_Ioi (by exact_mod_cast hmn)
  have hmeasure :=
    tendsto_measure_iInter_atTop (μ := μ)
      (fun n : ℕ => (measurableSet_Ioi : MeasurableSet (Set.Ioi (n : ℝ))).nullMeasurableSet)
      hmono ⟨0, measure_ne_top μ _⟩
  simpa [Function.comp_def, hinter] using hmeasure

/-- The non-surge extended-cutoff integral is continuous at the source's
accept-all (`∞`) endpoint. -/
theorem continuousAt_gn21LeftExtendedCutoff_setIntegral_top
    (μ : Measure TripLength) [NoAtoms μ] [IsFiniteMeasure μ]
    (f : TripLength → ℝ)
    (hfin : IntegrableOn f acceptAllPolicy μ) :
    ContinuousAt
      (fun t : ℝ≥0∞ => ∫ τ in gn21LeftExtendedCutoffPolicy t, f τ ∂μ) ∞ := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  rcases setIntegral_symmDiffContinuousAt_of_integrableOn μ f hfin
      measurableSet_acceptAllPolicy (fun _ hτ => hτ) ε hε with
    ⟨δ, hδ_ne, hδ⟩
  have hδ_pos : 0 < δ := pos_iff_ne_zero.mpr hδ_ne
  have htail : ∀ᶠ n : ℕ in Filter.atTop, μ (Set.Ioi (n : ℝ)) < δ :=
    (tendsto_order.1 (gn21_tendsto_measure_Ioi_nat_atTop μ)).2 δ hδ_pos
  rcases Filter.eventually_atTop.1 htail with ⟨N, hN⟩
  have htailN : μ (Set.Ioi (N : ℝ)) < δ := hN N le_rfl
  have hnear : ∀ᶠ t : ℝ≥0∞ in 𝓝 ∞,
      (↑(N : NNReal) : ℝ≥0∞) < t := by
    exact ENNReal.nhds_top_basis.mem_iff.mpr
      ⟨(↑(N : NNReal) : ℝ≥0∞), ENNReal.coe_lt_top, Set.Subset.rfl⟩
  filter_upwards [hnear] with t ht
  have hsymm : μ (acceptAllPolicy ∆ gn21LeftExtendedCutoffPolicy t) < δ :=
    lt_of_le_of_lt
      (measure_mono
        (gn21_symmDiff_acceptAll_leftExtendedCutoff_subset_Ioi N ht)) htailN
  simpa [Real.dist_eq] using
    hδ (gn21LeftExtendedCutoffPolicy t)
      (gn21LeftExtendedCutoffPolicy_open t).measurableSet
      (gn21LeftExtendedCutoffPolicy_subset_acceptAll t) hsymm

/-- The surge extended-cutoff integral is continuous at the source's empty
(`∞`) endpoint. -/
theorem continuousAt_gn21RightExtendedCutoff_setIntegral_top
    (μ : Measure TripLength) [NoAtoms μ] [IsFiniteMeasure μ]
    (f : TripLength → ℝ)
    (hfin : IntegrableOn f acceptAllPolicy μ) :
    ContinuousAt
      (fun t : ℝ≥0∞ => ∫ τ in gn21RightExtendedCutoffPolicy t, f τ ∂μ) ∞ := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  rcases setIntegral_symmDiffContinuousAt_of_integrableOn μ f hfin
      MeasurableSet.empty (Set.empty_subset _) ε hε with
    ⟨δ, hδ_ne, hδ⟩
  have hδ_pos : 0 < δ := pos_iff_ne_zero.mpr hδ_ne
  have htail : ∀ᶠ n : ℕ in Filter.atTop, μ (Set.Ioi (n : ℝ)) < δ :=
    (tendsto_order.1 (gn21_tendsto_measure_Ioi_nat_atTop μ)).2 δ hδ_pos
  rcases Filter.eventually_atTop.1 htail with ⟨N, hN⟩
  have htailN : μ (Set.Ioi (N : ℝ)) < δ := hN N le_rfl
  have hnear : ∀ᶠ t : ℝ≥0∞ in 𝓝 ∞,
      (↑(N : NNReal) : ℝ≥0∞) < t := by
    exact ENNReal.nhds_top_basis.mem_iff.mpr
      ⟨(↑(N : NNReal) : ℝ≥0∞), ENNReal.coe_lt_top, Set.Subset.rfl⟩
  filter_upwards [hnear] with t ht
  have hsymm : μ ((∅ : TripPolicy) ∆ gn21RightExtendedCutoffPolicy t) < δ :=
    lt_of_le_of_lt
      (measure_mono
        (gn21_symmDiff_empty_rightExtendedCutoff_subset_Ioi N ht)) htailN
  simpa [Real.dist_eq] using
    hδ (gn21RightExtendedCutoffPolicy t)
      (gn21RightExtendedCutoffPolicy_open t).measurableSet
      (gn21RightExtendedCutoffPolicy_subset_acceptAll t) hsymm

/-- Set integrals over the full extended non-surge cutoff family are
continuous. -/
theorem continuous_gn21LeftExtendedCutoff_setIntegral
    (μ : Measure TripLength) [NoAtoms μ] [IsFiniteMeasure μ]
    (f : TripLength → ℝ)
    (hfin : IntegrableOn f acceptAllPolicy μ) :
    Continuous
      (fun t : ℝ≥0∞ => ∫ τ in gn21LeftExtendedCutoffPolicy t, f τ ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro t
  cases t using ENNReal.recTopCoe with
  | top => exact continuousAt_gn21LeftExtendedCutoff_setIntegral_top μ f hfin
  | coe a =>
      rw [ContinuousAt, ENNReal.nhds_coe, Filter.tendsto_map'_iff]
      simpa [Function.comp_def] using
        continuousAt_gn21FiniteLeftCutoff_setIntegral μ f hfin a

/-- Set integrals over the full extended surge cutoff family are continuous. -/
theorem continuous_gn21RightExtendedCutoff_setIntegral
    (μ : Measure TripLength) [NoAtoms μ] [IsFiniteMeasure μ]
    (f : TripLength → ℝ)
    (hfin : IntegrableOn f acceptAllPolicy μ) :
    Continuous
      (fun t : ℝ≥0∞ => ∫ τ in gn21RightExtendedCutoffPolicy t, f τ ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro t
  cases t using ENNReal.recTopCoe with
  | top => exact continuousAt_gn21RightExtendedCutoff_setIntegral_top μ f hfin
  | coe a =>
      rw [ContinuousAt, ENNReal.nhds_coe, Filter.tendsto_map'_iff]
      simpa [Function.comp_def] using
        continuousAt_gn21FiniteRightCutoff_setIntegral μ f hfin a

/-- The actual Appendix-D aggregate reward is continuous on the compact pair
of extended cutoff parameters. -/
theorem continuous_gn21AggregateMultiplicativeDynamicReward_extendedCutoffs
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime1 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1)) :
    Continuous (fun p : ℝ≥0∞ × ℝ≥0∞ =>
      gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m
        (gn21ExtendedCutoffDynamicPolicy p.1 p.2)) := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hq0fin :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0) :=
    integrableOn_gn21SwitchProb_of_time_integrable (μ 0) switch12 switch21
      acceptAllPolicy (le_of_lt hswitch12_pos) hsum0 (fun _ hτ => hτ)
      measurableSet_acceptAllPolicy htime0
  have hq1fin :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1) :=
    integrableOn_gn21SwitchProb_of_time_integrable (μ 1) switch21 switch12
      acceptAllPolicy (le_of_lt hswitch21_pos) hsum1 (fun _ hτ => hτ)
      measurableSet_acceptAllPolicy htime1
  let I0 : ℝ≥0∞ × ℝ≥0∞ → ℝ := fun p =>
    ∫ τ in gn21LeftExtendedCutoffPolicy p.1, τ ∂(μ 0)
  let J0 : ℝ≥0∞ × ℝ≥0∞ → ℝ := fun p =>
    ∫ τ in gn21LeftExtendedCutoffPolicy p.1,
      gn21SwitchProb switch12 switch21 τ ∂(μ 0)
  let I1 : ℝ≥0∞ × ℝ≥0∞ → ℝ := fun p =>
    ∫ τ in gn21RightExtendedCutoffPolicy p.2, τ ∂(μ 1)
  let J1 : ℝ≥0∞ × ℝ≥0∞ → ℝ := fun p =>
    ∫ τ in gn21RightExtendedCutoffPolicy p.2,
      gn21SwitchProb switch21 switch12 τ ∂(μ 1)
  have hI0 : Continuous I0 := by
    dsimp [I0]
    exact
      (continuous_gn21LeftExtendedCutoff_setIntegral (μ 0)
        (fun τ : TripLength => τ) htime0).comp continuous_fst
  have hJ0 : Continuous J0 := by
    dsimp [J0]
    exact
      (continuous_gn21LeftExtendedCutoff_setIntegral (μ 0)
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ) hq0fin).comp
        continuous_fst
  have hI1 : Continuous I1 := by
    dsimp [I1]
    exact
      (continuous_gn21RightExtendedCutoff_setIntegral (μ 1)
        (fun τ : TripLength => τ) htime1).comp continuous_snd
  have hJ1 : Continuous J1 := by
    dsimp [J1]
    exact
      (continuous_gn21RightExtendedCutoff_setIntegral (μ 1)
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ) hq1fin).comp
        continuous_snd
  let Q0 : ℝ≥0∞ × ℝ≥0∞ → ℝ := fun p =>
    gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
      (gn21LeftExtendedCutoffPolicy p.1)
  let Q1 : ℝ≥0∞ × ℝ≥0∞ → ℝ := fun p =>
    gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
      (gn21RightExtendedCutoffPolicy p.2)
  let T0 : ℝ≥0∞ × ℝ≥0∞ → ℝ := fun p =>
    gn21ScaledStateTime (μ 0) (arrival 0) (gn21LeftExtendedCutoffPolicy p.1)
  let T1 : ℝ≥0∞ × ℝ≥0∞ → ℝ := fun p =>
    gn21ScaledStateTime (μ 1) (arrival 1) (gn21RightExtendedCutoffPolicy p.2)
  have hQ0 : Continuous Q0 := by
    simpa [Q0, gn21ExitWeightIntegral] using
      (continuous_const.add (continuous_const.mul hJ0))
  have hQ1 : Continuous Q1 := by
    simpa [Q1, gn21ExitWeightIntegral] using
      (continuous_const.add (continuous_const.mul hJ1))
  have hT0 : Continuous T0 := by
    simpa [T0, gn21ScaledStateTime, singleStateTripTime] using
      (continuous_const.add (continuous_const.mul hI0))
  have hT1 : Continuous T1 := by
    simpa [T1, gn21ScaledStateTime, singleStateTripTime] using
      (continuous_const.add (continuous_const.mul hI1))
  let W0 : ℝ≥0∞ × ℝ≥0∞ → ℝ := fun p => m 0 * (T0 p - 1)
  let W1 : ℝ≥0∞ × ℝ≥0∞ → ℝ := fun p => m 1 * (T1 p - 1)
  have hW0 : Continuous W0 := by
    dsimp [W0]
    exact continuous_const.mul (hT0.sub continuous_const)
  have hW1 : Continuous W1 := by
    dsimp [W1]
    exact continuous_const.mul (hT1.sub continuous_const)
  let F : ℝ≥0∞ × ℝ≥0∞ → ℝ := fun p =>
    (Q0 p * W1 p + Q1 p * W0 p) / (Q0 p * T1 p + Q1 p * T0 p)
  have hnum : Continuous (fun p => Q0 p * W1 p + Q1 p * W0 p) :=
    (hQ0.mul hW1).add (hQ1.mul hW0)
  have hden : Continuous (fun p => Q0 p * T1 p + Q1 p * T0 p) :=
    (hQ0.mul hT1).add (hQ1.mul hT0)
  have hden_ne : ∀ p : ℝ≥0∞ × ℝ≥0∞, Q0 p * T1 p + Q1 p * T0 p ≠ 0 := by
    intro p
    have hp := dynamicFeasibleOpenPolicy_gn21ExtendedCutoffDynamicPolicy p.1 p.2
    have hQ0_pos : 0 < Q0 p := by
      dsimp [Q0]
      exact gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0)
        switch12 switch21 (gn21LeftExtendedCutoffPolicy p.1)
        (le_of_lt harrival0_pos) hswitch12_pos hsum0
        (hp 0).2.measurableSet (hp 0).1
    have hQ1_pos : 0 < Q1 p := by
      dsimp [Q1]
      exact gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1)
        switch21 switch12 (gn21RightExtendedCutoffPolicy p.2)
        (le_of_lt harrival1_pos) hswitch21_pos hsum1
        (hp 1).2.measurableSet (hp 1).1
    have hT0_pos : 0 < T0 p := by
      dsimp [T0]
      exact gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0)
        (gn21LeftExtendedCutoffPolicy p.1) (le_of_lt harrival0_pos)
        (hp 0).2.measurableSet (hp 0).1
    have hT1_pos : 0 < T1 p := by
      dsimp [T1]
      exact gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1)
        (gn21RightExtendedCutoffPolicy p.2) (le_of_lt harrival1_pos)
        (hp 1).2.measurableSet (hp 1).1
    exact (gn21AggregateDenominator_pos_of_pos
      (Q0 p) (Q1 p) (T0 p) (T1 p) hQ0_pos hQ1_pos hT0_pos hT1_pos).ne'
  have hF : Continuous F := by
    dsimp [F]
    exact hnum.div hden hden_ne
  have hF_eq (p : ℝ≥0∞ × ℝ≥0∞) :
      F p =
        gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m
          (gn21ExtendedCutoffDynamicPolicy p.1 p.2) := by
    dsimp [F, Q0, Q1, T0, T1, W0, W1]
    rw [gn21AggregateMultiplicativeDynamicReward_apply]
    simp only [gn21ExtendedCutoffDynamicPolicy_zero,
      gn21ExtendedCutoffDynamicPolicy_one]
    unfold gn21MeasuredAggregateRewardPrimitives gn21AggregateDynamicReward
    rw [gn21ScaledStateEarning_multiplicativePricing,
      gn21ScaledStateEarning_multiplicativePricing]
  have heq :
      (fun p : ℝ≥0∞ × ℝ≥0∞ =>
        gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m
          (gn21ExtendedCutoffDynamicPolicy p.1 p.2)) = F := by
    funext p
    exact (hF_eq p).symm
  rw [heq]
  exact hF

/-- The compact extended cutoff family contains a maximizer of the actual
aggregate multiplicative reward. -/
theorem gn21_exists_extendedCutoffDynamicPolicy_reward_maximum
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime1 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1)) :
    ∃ left right : ℝ≥0∞,
      dynamicFeasibleOpenPolicy (gn21ExtendedCutoffDynamicPolicy left right) ∧
        ∀ left' right' : ℝ≥0∞,
          gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m
              (gn21ExtendedCutoffDynamicPolicy left' right') ≤
            gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m
              (gn21ExtendedCutoffDynamicPolicy left right) := by
  let F : ℝ≥0∞ × ℝ≥0∞ → ℝ := fun p =>
    gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m
      (gn21ExtendedCutoffDynamicPolicy p.1 p.2)
  have hF : Continuous F := by
    dsimp [F]
    exact continuous_gn21AggregateMultiplicativeDynamicReward_extendedCutoffs
      μ arrival m switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos htime0 htime1
  rcases isCompact_gn21CutoffParameterSpace.exists_isMaxOn
      gn21CutoffParameterSpace_nonempty hF.continuousOn with
    ⟨p, hp_mem, hp_max⟩
  rw [isMaxOn_iff] at hp_max
  refine ⟨p.1, p.2,
    dynamicFeasibleOpenPolicy_gn21ExtendedCutoffDynamicPolicy p.1 p.2, ?_⟩
  intro left right
  have hmax := hp_max (left, right) (by simp [gn21CutoffParameterSpace])
  simpa [F] using hmax

/-- The source open-policy domain has an actual aggregate-reward optimizer.
Every source-open policy is first canonically dominated by an extended cutoff
pair, and compactness then supplies a maximal such pair. -/
theorem gn21_exists_dynamicOpenOptimal_multiplicative_of_source_primitives
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime1 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hsurge : gn21SourceSurgeStateDominance μ arrival
      (fun i => multiplicativePricing (m i))) :
    ∃ ρ : Fin 2 → TripPolicy,
      dynamicOpenOptimal
        (gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m)
        ρ := by
  rcases gn21_exists_extendedCutoffDynamicPolicy_reward_maximum
      μ arrival m switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos htime0 htime1 with
    ⟨left, right, hmax_feasible, hmax⟩
  refine ⟨gn21ExtendedCutoffDynamicPolicy left right, hmax_feasible, ?_⟩
  intro ρ hρ
  rcases gn21_exists_open_multiplicative_cutoff_dominating_policy
      μ arrival m switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos htime0 htime1 hsurge ρ hρ with
    ⟨κ, hκ_feasible, hρ_le_κ, hleft_shape, hright_shape⟩
  rcases gn21_exists_leftExtendedCutoffPolicy_eq_of_shape
      (hκ_feasible 0).1 hleft_shape with ⟨leftκ, hleftκ⟩
  rcases gn21_exists_rightExtendedCutoffPolicy_eq_of_shape
      (hκ_feasible 1).1 hright_shape with ⟨rightκ, hrightκ⟩
  have hκ_eq : κ = gn21ExtendedCutoffDynamicPolicy leftκ rightκ := by
    funext i
    fin_cases i
    · simpa using hleftκ
    · simpa using hrightκ
  have hκ_le_max :
      gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m κ ≤
        gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m
          (gn21ExtendedCutoffDynamicPolicy left right) := by
    rw [hκ_eq]
    exact hmax leftκ rightκ
  exact hρ_le_κ.trans hκ_le_max

end GN21DriverSurgePricing
