import PG24NoisyMatchingMarkets.Theorem2HolderNoAtoms
import Mathlib.Tactic

open Filter MeasureTheory Topology

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- Under atomlessness, the strict and closed upper tails at a threshold agree. -/
theorem theorem2_upperTailMass_eq_real_Ici_of_noAtoms
    (eta : Measure ℝ) [IsFiniteMeasure eta] [NoAtoms eta] (x : ℝ) :
    AppliedModelingLib.Probability.upperTailMass eta x = eta.real (Set.Ici x) := by
  have hIciIoi : eta.real (Set.Ici x) = eta.real (Set.Ioi x) := by
    simpa using
      (MeasureTheory.measureReal_congr
        (μ := eta)
        ((MeasureTheory.Ioi_ae_eq_Ici (μ := eta) (a := x)).symm))
  simpa [AppliedModelingLib.Probability.upperTailMass] using hIciIoi.symm

/-- Under atomlessness, the open and closed lower tails at a threshold agree. -/
theorem theorem2_real_Iio_eq_lowerCDFMass_of_noAtoms
    (eta : Measure ℝ) [IsFiniteMeasure eta] [NoAtoms eta] (x : ℝ) :
    eta.real (Set.Iio x) = AppliedModelingLib.Probability.lowerCDFMass eta x := by
  have hIioIic : eta.real (Set.Iio x) = eta.real (Set.Iic x) := by
    simpa using
      (MeasureTheory.measureReal_congr
        (μ := eta)
        (MeasureTheory.Iio_ae_eq_Iic (μ := eta) (a := x)))
  simpa [AppliedModelingLib.Probability.lowerCDFMass] using hIioIic

/-- Every strictly interior lower-tail target is realized by an open tail. -/
theorem theorem2_exists_lowerTailQuantile_eq_of_noAtoms
    (eta : Measure ℝ) [IsProbabilityMeasure eta] [NoAtoms eta]
    {target : ℝ} (htarget_pos : 0 < target) (htarget_lt_one : target < 1) :
    ∃ x : ℝ, eta.real (Set.Iio x) = target := by
  rcases AppliedModelingLib.Probability.exists_measureReal_Iio_Iic_bracket
      eta htarget_pos htarget_lt_one with
    ⟨x, hIio, hIic⟩
  have htails : eta.real (Set.Iio x) = eta.real (Set.Iic x) := by
    simpa using
      (MeasureTheory.measureReal_congr
        (μ := eta)
        (MeasureTheory.Iio_ae_eq_Iic (μ := eta) (a := x)) )
  refine ⟨x, le_antisymm hIio ?_⟩
  rw [htails]
  exact hIic

/-- Every strictly interior upper-tail target is realized by a strict tail. -/
theorem theorem2_exists_upperTailQuantile_eq_of_noAtoms
    (eta : Measure ℝ) [IsProbabilityMeasure eta] [NoAtoms eta]
    {target : ℝ} (htarget_pos : 0 < target) (htarget_lt_one : target < 1) :
    ∃ x : ℝ, AppliedModelingLib.Probability.upperTailMass eta x = target := by
  rcases AppliedModelingLib.Probability.exists_upperTailMass_Ici_bracket
      eta htarget_pos htarget_lt_one with
    ⟨x, hstrict, hclosed⟩
  refine ⟨x, le_antisymm hstrict ?_⟩
  rw [theorem2_upperTailMass_eq_real_Ici_of_noAtoms eta x]
  exact hclosed

/-- The exact source quantile data for one two-scale error level. -/
structure Theorem2ExactQuantileWindow
    (eta : Measure ℝ) (epsilon vLow vHigh vStar : ℝ) : Prop where
  lower_tail : eta.real (Set.Iio vLow) = epsilon / 2
  upper_tail : AppliedModelingLib.Probability.upperTailMass eta vHigh = epsilon / 2
  middle_mass : eta.real (Set.Ioo vStar vHigh) = Real.sqrt epsilon
  lower_lt_upper : vLow < vHigh
  star_lt_upper : vStar < vHigh
  central_mass : eta.real (Set.Icc vLow vHigh) = 1 - epsilon

/--
Construct the three source quantiles at one error level.  The exact interval
mass for `(vStar, vHigh)` supplies both the coverage and small-region clauses
of the two-scale proof.
-/
theorem theorem2_exists_exactQuantileWindow_of_noAtoms
    (eta : Measure ℝ) [IsProbabilityMeasure eta] [NoAtoms eta]
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    (hstar_target_lt_one : Real.sqrt epsilon + epsilon / 2 < 1) :
    ∃ vLow vHigh vStar : ℝ,
      Theorem2ExactQuantileWindow eta epsilon vLow vHigh vStar := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt epsilon := Real.sqrt_nonneg epsilon
  have hhalf_pos : 0 < epsilon / 2 := by linarith
  have hhalf_lt_one : epsilon / 2 < 1 := by linarith
  have hsqrt_sq : (Real.sqrt epsilon) ^ 2 = epsilon :=
    Real.sq_sqrt hepsilon_pos.le
  have hepsilon_lt_one : epsilon < 1 := by
    nlinarith
  have hstar_target_pos : 0 < Real.sqrt epsilon + epsilon / 2 := by
    have hsqrt_pos : 0 < Real.sqrt epsilon := Real.sqrt_pos.2 hepsilon_pos
    linarith
  rcases theorem2_exists_lowerTailQuantile_eq_of_noAtoms
      eta hhalf_pos hhalf_lt_one with
    ⟨vLow, hlow⟩
  rcases theorem2_exists_upperTailQuantile_eq_of_noAtoms
      eta hhalf_pos hhalf_lt_one with
    ⟨vHigh, hhigh⟩
  rcases theorem2_exists_upperTailQuantile_eq_of_noAtoms
      eta hstar_target_pos hstar_target_lt_one with
    ⟨vStar, hstar⟩
  have htail_low :
      AppliedModelingLib.Probability.upperTailMass eta vLow = 1 - epsilon / 2 := by
    have hsum := AppliedModelingLib.Probability.lowerCDFMass_add_upperTailMass_eq_one
      eta vLow
    have hlower : AppliedModelingLib.Probability.lowerCDFMass eta vLow = epsilon / 2 := by
      rw [← theorem2_real_Iio_eq_lowerCDFMass_of_noAtoms eta vLow]
      exact hlow
    linarith
  have hvLow_lt_vHigh : vLow < vHigh := by
    by_contra hnot
    have hhigh_low : vHigh ≤ vLow := le_of_not_gt hnot
    have htail_mono := AppliedModelingLib.Probability.upperTailMass_antitone eta hhigh_low
    rw [htail_low, hhigh] at htail_mono
    linarith
  have hvStar_lt_vHigh : vStar < vHigh := by
    by_contra hnot
    have hhigh_star : vHigh ≤ vStar := le_of_not_gt hnot
    have htail_mono := AppliedModelingLib.Probability.upperTailMass_antitone eta hhigh_star
    rw [hstar, hhigh] at htail_mono
    have hsqrt_pos : 0 < Real.sqrt epsilon := Real.sqrt_pos.2 hepsilon_pos
    linarith
  have hinterval_disjoint : Disjoint (Set.Ioo vStar vHigh) (Set.Ici vHigh) := by
    rw [Set.disjoint_left]
    intro x hxInterval hxHigh
    exact (not_le_of_gt hxInterval.2) hxHigh
  have hinterval_union :
      Set.Ioo vStar vHigh ∪ Set.Ici vHigh = Set.Ioi vStar :=
    Set.Ioo_union_Ici_eq_Ioi hvStar_lt_vHigh
  have hinterval_sum :
      eta.real (Set.Ioo vStar vHigh) + eta.real (Set.Ici vHigh) =
        eta.real (Set.Ioi vStar) := by
    calc
      eta.real (Set.Ioo vStar vHigh) + eta.real (Set.Ici vHigh) =
          eta.real (Set.Ioo vStar vHigh ∪ Set.Ici vHigh) :=
        (MeasureTheory.measureReal_union (μ := eta)
          hinterval_disjoint measurableSet_Ici).symm
      _ = eta.real (Set.Ioi vStar) := by rw [hinterval_union]
  have hhigh_closed : eta.real (Set.Ici vHigh) = epsilon / 2 := by
    rw [← theorem2_upperTailMass_eq_real_Ici_of_noAtoms eta vHigh]
    exact hhigh
  have hstar_real : eta.real (Set.Ioi vStar) =
      Real.sqrt epsilon + epsilon / 2 := by
    simpa [AppliedModelingLib.Probability.upperTailMass] using hstar
  have hinterval : eta.real (Set.Ioo vStar vHigh) = Real.sqrt epsilon := by
    rw [hstar_real, hhigh_closed] at hinterval_sum
    linarith
  have houter_disjoint : Disjoint (Set.Iio vLow) (Set.Ioi vHigh) := by
    rw [Set.disjoint_left]
    intro x hxLow hxHigh
    exact (not_lt_of_ge hvLow_lt_vHigh.le) (lt_trans hxHigh hxLow)
  have houter_complement :
      (Set.Icc vLow vHigh)ᶜ = Set.Iio vLow ∪ Set.Ioi vHigh := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union,
      Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro hx
      by_cases hxLow : x < vLow
      · exact Or.inl hxLow
      · right
        have hxLow' : vLow ≤ x := le_of_not_gt hxLow
        exact lt_of_not_ge (fun hxHigh => hx ⟨hxLow', hxHigh⟩)
    · rintro (hxLow | hxHigh) hx
      · exact (not_lt_of_ge hx.1) hxLow
      · exact (not_lt_of_ge hx.2) hxHigh
  have houter_mass : eta.real ((Set.Icc vLow vHigh)ᶜ) = epsilon := by
    rw [houter_complement,
      MeasureTheory.measureReal_union houter_disjoint measurableSet_Ioi,
      hlow]
    simpa [AppliedModelingLib.Probability.upperTailMass] using
      (show epsilon / 2 +
          AppliedModelingLib.Probability.upperTailMass eta vHigh = epsilon by
        rw [hhigh]
        ring)
  have hlarge_mass : eta.real (Set.Icc vLow vHigh) = 1 - epsilon := by
    have hcompl :=
      MeasureTheory.measureReal_compl (μ := eta) (s := Set.Icc vLow vHigh)
        measurableSet_Icc
    rw [MeasureTheory.probReal_univ, houter_mass] at hcompl
    linarith
  exact ⟨vLow, vHigh, vStar, hlow, hhigh, hinterval,
    hvLow_lt_vHigh, hvStar_lt_vHigh, hlarge_mass⟩

/-- The exact quantiles instantiate the two eta regions used in the local route. -/
theorem Theorem2ExactQuantileWindow.valueRegions
    {eta : Measure ℝ} {epsilon vLow vHigh vStar : ℝ}
    (hwindow : Theorem2ExactQuantileWindow eta epsilon vLow vHigh vStar) :
    MeasurableSet (Set.Icc vLow vHigh) ∧
      1 - epsilon ≤ eta.real (Set.Icc vLow vHigh) ∧
      (∀ w : ℝ, w ∈ Set.Icc vLow vHigh -> vLow ≤ w) ∧
      (∀ w : ℝ, w ∈ Set.Icc vLow vHigh -> w ≤ vHigh) ∧
      MeasurableSet (Set.Ioo vStar vHigh) ∧
      Real.sqrt epsilon ≤ eta.real (Set.Ioo vStar vHigh) ∧
      (∀ w : ℝ, w ∈ Set.Ioo vStar vHigh -> vStar ≤ w) ∧
      (∀ w : ℝ, w ∈ Set.Ioo vStar vHigh -> w ≤ vHigh) := by
  refine ⟨measurableSet_Icc, ?_, ?_, ?_, measurableSet_Ioo, ?_, ?_, ?_⟩
  · exact le_of_eq hwindow.central_mass.symm
  · intro w hw
    exact hw.1
  · intro w hw
    exact hw.2
  · exact le_of_eq hwindow.middle_mass.symm
  · intro w hw
    exact hw.1.le
  · intro w hw
    exact hw.2.le

/-- Select exact source quantiles pointwise for any admissible error schedule. -/
theorem theorem2_exists_exactQuantileSchedule_of_noAtoms
    (eta : Measure ℝ) [IsProbabilityMeasure eta] [NoAtoms eta]
    (epsilon : ℕ → ℝ)
    (hepsilon_pos : ∀ n : ℕ, 0 < epsilon n)
    (hstar_target_lt_one :
      ∀ n : ℕ, Real.sqrt (epsilon n) + epsilon n / 2 < 1) :
    ∃ vLow vHigh vStar : ℕ → ℝ,
      ∀ n : ℕ,
        Theorem2ExactQuantileWindow eta (epsilon n)
          (vLow n) (vHigh n) (vStar n) := by
  choose vLow vHigh vStar hwindow using
    fun n => theorem2_exists_exactQuantileWindow_of_noAtoms
      eta (hepsilon_pos n) (hstar_target_lt_one n)
  exact ⟨vLow, vHigh, vStar, hwindow⟩

/--
Holder regularity supplies the atomlessness needed to construct exact quantile
schedules, and the resulting schedule covers every fixed support-interior
target eventually.
-/
theorem theorem2_exists_interiorQuantileSchedule_of_holder
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hregular : PG24HolderIntervalRegular eta)
    (epsilon : ℕ → ℝ)
    (hepsilon_pos : ∀ n : ℕ, 0 < epsilon n)
    (hstar_target_lt_one :
      ∀ n : ℕ, Real.sqrt (epsilon n) + epsilon n / 2 < 1)
    (hepsilon_zero : Tendsto epsilon atTop (nhds 0))
    {v : ℝ}
    (hvLower : 0 < eta.real (Set.Iio v))
    (hvUpper : 0 < eta.real (Set.Ioi v)) :
    ∃ vLow vHigh vStar : ℕ → ℝ,
      (∀ n : ℕ,
        Theorem2ExactQuantileWindow eta (epsilon n)
          (vLow n) (vHigh n) (vStar n)) ∧
      ∀ᶠ n : ℕ in atTop,
        theorem2_localWindowMembership (vLow n) (vHigh n) (vStar n) v := by
  letI : NoAtoms eta := hregular.noAtoms
  rcases theorem2_exists_exactQuantileSchedule_of_noAtoms
      eta epsilon hepsilon_pos hstar_target_lt_one with
    ⟨vLow, vHigh, vStar, hwindow⟩
  refine ⟨vLow, vHigh, vStar, hwindow, ?_⟩
  exact theorem2_localWindowMembership_eventually_of_quantileWindows_holder
    eta hregular hepsilon_zero
    (Filter.Eventually.of_forall fun n =>
      le_of_eq (hwindow n).lower_tail)
    (Filter.Eventually.of_forall fun n =>
      le_of_eq (hwindow n).middle_mass)
    (Filter.Eventually.of_forall fun n =>
      le_of_eq (hwindow n).upper_tail)
    (Filter.Eventually.of_forall fun n =>
      le_of_lt (hwindow n).star_lt_upper)
    hvLower hvUpper

end

end PG24NoisyMatchingMarkets
