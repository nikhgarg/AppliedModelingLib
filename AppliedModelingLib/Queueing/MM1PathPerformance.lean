import AppliedModelingLib.Queueing.MM1.ForwardReverse.PostTagCount
import AppliedModelingLib.Queueing.StationaryPerformance

/-!
# Performance of the direct stationary M/M/1 path

This module turns the response-tail theorem for the selected uniformized
stationary M/M/1 path into its mean-response consequence.  It uses the
literal state-indexed false-mark stopping time on that path; no auxiliary
count certificate is supplied by the caller.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

open Probability.Queueing

/-- The literal tagged false-mark response time on the selected stable
uniformized M/M/1 path has mean reciprocal spare capacity. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_integral_falseMarkResponse_eq_inv_spareCapacity_of_rates
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
    let hrate : 0 < rate := by
      exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
    let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
    let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
    let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
      (lt_trans harrival_pos hstable)
    ∫ z, postTagFalseMarkResponseFromState z ∂
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag =
      (((serviceRate : ℝ) - (arrivalRate : ℝ))⁻¹) := by
  dsimp only
  let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
  let hrate : 0 < rate := by
    exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
  let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
  let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
  let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
    (lt_trans harrival_pos hstable)
  let selected := (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
    hrate rho hrho).conditionOn
      (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
      (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
        hrate rho hrho hrho_pos)
  let P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) := selected.Ptag
  letI : IsProbabilityMeasure P := selected.isProbability
  have hnonnegative : 0 ≤ᵐ[P] postTagFalseMarkResponseFromState := by
    have hbusy :=
      geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_postTagFalseMarkBusyUntil_nonneg_of_rates
        harrival_pos hstable
    have hle :=
      geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_postTagFalseMarkBusyUntil_le_response_of_rates
        harrival_pos hstable
    filter_upwards [hbusy, hle] with z hbusy_z hle_z
    exact le_trans hbusy_z hle_z
  have hrate_pos : 0 < (serviceRate : ℝ) - (arrivalRate : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hstable)
  have htail : ∀ t : ℝ, 0 ≤ t →
      P.real {z | t < postTagFalseMarkResponseFromState z} =
        Real.exp (-(((serviceRate : ℝ) - (arrivalRate : ℝ)) * t)) := by
    intro t ht
    simpa [P, selected, rate, rho, hrho, hrho_pos] using
      (geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_strict_falseMarkResponse_tail_of_rates
        harrival_pos hstable ht)
  simpa [P, selected] using
    (integral_eq_inv_of_exponential_responseTail_of_finite P
      postTagFalseMarkResponseFromState ((serviceRate : ℝ) - (arrivalRate : ℝ))
      measurable_postTagFalseMarkResponseFromState.aestronglyMeasurable
      hnonnegative hrate_pos htail)

end

end AppliedModelingLib.Queueing
