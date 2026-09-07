import PG24NoisyMatchingMarkets.MainTheorems

/-!
# PG24 Theorem 3 iid maximum tail bridge

These lemmas translate a deviation probability for an iid maximum into the
lower-CDF power bounds consumed by the dense and large-gap affordability
arguments.  They are probability identities and event inclusions, not source
endpoint assumptions.
-/

open MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- A threshold at least one deviation above the maximum's center has iid
crossing probability bounded by the deviation event. -/
theorem theorem3_iidMaximum_upper_crossing_le_deviation
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (n : ℕ) {center deviation threshold : ℝ}
    (hseparation : center + deviation ≤ threshold) :
    1 - (AppliedModelingLib.Probability.lowerCDFMass noiseLaw threshold) ^ (n + 1) ≤
      AppliedModelingLib.Probability.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) center deviation := by
  rw [← AppliedModelingLib.Probability.topOrderCrossingProbability_iidProduct_eq_one_sub_lowerCDFMass_pow]
  exact
    AppliedModelingLib.Probability.topOrderCrossingProbability_le_deviationProbability_of_center_add_le
      (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) hseparation

/-- A threshold strictly one deviation below the maximum's center has iid
no-crossing probability bounded by the deviation event. -/
theorem theorem3_iidMaximum_lower_noCrossing_le_deviation
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (n : ℕ) {center deviation threshold : ℝ}
    (hdeviation_pos : 0 < deviation)
    (hseparation : threshold < center - deviation) :
    (AppliedModelingLib.Probability.lowerCDFMass noiseLaw threshold) ^ (n + 1) ≤
      AppliedModelingLib.Probability.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) center deviation := by
  have h :=
    AppliedModelingLib.Probability.one_sub_topOrderCrossingProbability_le_deviationProbability_of_lt_center_sub
      (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) hdeviation_pos hseparation
  rw [AppliedModelingLib.Probability.topOrderCrossingProbability_iidProduct_eq_one_sub_lowerCDFMass_pow] at h
  linarith

/-- A small maximum deviation probability gives the dense branch's high
crossing estimate at every threshold strictly below `center - deviation`. -/
theorem theorem3_iidMaximum_high_crossing_gt_one_sub_of_deviation_lt
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (n : ℕ) {center deviation threshold epsilon : ℝ}
    (hdeviation_pos : 0 < deviation)
    (hseparation : threshold < center - deviation)
    (hsmall :
      AppliedModelingLib.Probability.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) center deviation <
          epsilon) :
    1 - epsilon <
      1 - (AppliedModelingLib.Probability.lowerCDFMass noiseLaw threshold) ^ (n + 1) := by
  have hno_crossing := theorem3_iidMaximum_lower_noCrossing_le_deviation
    noiseLaw n hdeviation_pos hseparation
  linarith

end

end PG24NoisyMatchingMarkets
