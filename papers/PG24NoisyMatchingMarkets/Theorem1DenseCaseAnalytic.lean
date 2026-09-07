import PG24NoisyMatchingMarkets.Theorem1RoundedChebyshevRates

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
The dense Case 1 analytic bound with a dense block of at least the required
integer size.  The source says "at least" at this point; this theorem retains
that direction rather than replacing it with an equality of rounded counts.
-/
theorem theorem1_iid_atOrAbove_low_affordance_integral_le_of_dense_card_ge
    {n m : ℕ} [NeZero m]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (active dense : Finset (Fin n)) (cutoff : Fin n -> ℝ)
    (pivot width : ℝ)
    {center radius lowPivot highPivot vS totalSupply middleMass : ℝ}
    (hdense_subset : dense ⊆
      theorem1CutoffAtOrAboveBlock active cutoff pivot)
    (hdense_card : m ≤ dense.card)
    (hdense_upper : ∀ college ∈ dense, cutoff college ≤ pivot + width)
    (hradius_pos : 0 < radius)
    (hradius_le_half :
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin m => noiseLaw)) center radius ≤ 1 / 2)
    (hlow_separation : ∀ v ∈ Set.Iio lowPivot,
      center + radius ≤ pivot - v)
    (hhigh_separation : ∀ v ∈ Set.Ioi highPivot,
      pivot + width - v < center - radius)
    (hfull_capacity :
      (∫ v : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (Finset.univ : Finset (Fin n)) v cutoff ∂valueLaw) = totalSupply)
    (htail_normalization : valueLaw.real (Set.Ioi vS) = totalSupply)
    (hlow_high : lowPivot ≤ highPivot)
    (hhigh_vS : highPivot ≤ vS)
    (hmiddle : valueLaw.real (Set.Icc lowPivot highPivot) ≤ middleMass) :
    (∫ v : ℝ,
      (Set.Iic vS).indicator
        (fun v => cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (theorem1CutoffAtOrAboveBlock active cutoff pivot) v cutoff) v
      ∂valueLaw) ≤
      (theorem1IntegerGroupCount
        (theorem1CutoffAtOrAboveBlock active cutoff pivot) m : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseLaw)) center radius +
        middleMass + 2 * totalSupply *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin m => noiseLaw)) center radius := by
  let upper : Finset (Fin n) := theorem1CutoffAtOrAboveBlock active cutoff pivot
  let p : ℝ -> ℝ := fun v => cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin n => noiseLaw)) upper v cutoff
  let fullP : ℝ -> ℝ := fun v => cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin n => noiseLaw))
      (Finset.univ : Finset (Fin n)) v cutoff
  let error : ℝ := AppliedModelingLib.Matching.topOrderDeviationProbability
    (Measure.pi (fun _ : Fin m => noiseLaw)) center radius
  have hp : Integrable p valueLaw := by
    simpa [p, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        (Measure.pi (fun _ : Fin n => noiseLaw)) valueLaw upper cutoff)
  have hfullP : Integrable fullP valueLaw := by
    simpa [fullP, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        (Measure.pi (fun _ : Fin n => noiseLaw)) valueLaw
        (Finset.univ : Finset (Fin n)) cutoff)
  have hp_nonneg : ∀ v, 0 ≤ p v := by
    intro v
    exact cutoffAffordanceProbability_nonneg
      (Measure.pi (fun _ : Fin n => noiseLaw)) upper v cutoff
  have hp_le_one : ∀ v, p v ≤ 1 := by
    intro v
    exact cutoffAffordanceProbability_le_one
      (Measure.pi (fun _ : Fin n => noiseLaw)) upper v cutoff
  have herror_nonneg : 0 ≤ error := by
    exact theorem1_iid_topOrderDeviationProbability_nonneg noiseLaw center radius
  have hupper_le_full : ∀ v, p v ≤ fullP v := by
    intro v
    exact cutoffAffordanceProbability_mono_active
      (Measure.pi (fun _ : Fin n => noiseLaw)) (Finset.subset_univ upper)
  have htotal : (∫ v, p v ∂valueLaw) ≤ totalSupply := by
    calc
      (∫ v, p v ∂valueLaw) ≤ ∫ v, fullP v ∂valueLaw :=
        integral_mono hp hfullP hupper_le_full
      _ = totalSupply := by
        simpa [fullP] using hfull_capacity
  have hlow : ∀ v ∈ Set.Iio lowPivot,
      p v ≤ (theorem1IntegerGroupCount upper m : ℝ) * error := by
    intro v hv
    simpa [p, upper, error] using
      (theorem1_iid_atOrAbove_affordance_le_integer_group_count_mul_deviation
        (m := m) noiseLaw active cutoff pivot (hlow_separation v hv))
  have hhigh : ∀ v ∈ Set.Ioi highPivot, 1 - error ≤ p v := by
    intro v hv
    have hfailure :=
      theorem1_one_sub_iid_cutoff_affordance_le_deviation_of_dense_card_ge
        (m := m) noiseLaw (cutoff := cutoff)
        hdense_subset hdense_card hdense_upper hradius_pos
        (hhigh_separation v hv)
    dsimp [p, upper, error]
    linarith
  have hclosed := theorem1_low_affordance_integral_le_of_analytic_primitives
    valueLaw p hp hp_nonneg hp_le_one
    (mul_nonneg (by exact_mod_cast (theorem1IntegerGroupCount upper m).zero_le)
      herror_nonneg)
    herror_nonneg (by simpa [error] using hradius_le_half)
    hlow_high hhigh_vS hlow hhigh htotal htail_normalization hmiddle
  simpa [p, upper, error] using hclosed

end

end PG24NoisyMatchingMarkets
