import AppliedModelingLib.Foundations.Probability.Processes.Palm.SelectedMarkedTransport
import AppliedModelingLib.Queueing.MM1.Marked.Uniformization

/-!
# Selected-mark rate for the uniformized M/M/1 clock

This leaf specializes the generic selected-event Campbell transport to the
uniformized M/M/1 arrival mark probability.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open PoissonProcess

/-- For the uniformized M/M/1 clock, the selected true-mark intensity is the
physical arrival rate: `(arrivalRate + serviceRate) * p = arrivalRate`. -/
theorem selected_true_mark_campbell_rate_eq_arrival
    {arrivalRate serviceRate : ℝ≥0}
    (hservice_pos : 0 < serviceRate)
    {base : Palm.ShiftInvariantProbabilityLaw
      (GoodSuspensionState × (ℤ → Bool))}
    {selectedTagged : TaggedArrivalAtZero ((ℤ → ℝ) × (ℤ → Bool))}
    (H : HasTimedEmbeddedTrueMarkCampbellTransport
      (rate := ((arrivalRate + serviceRate : ℝ≥0) : ℝ))
      (p := (uniformizedBirthProbability
        (mm1TrafficIntensityNN arrivalRate serviceRate) : ℝ))
      base selectedTagged)
    (s : Set ((ℤ → ℝ) × (ℤ → Bool))) (hs : MeasurableSet s) :
    ∫⁻ z, (Palm.trueMarkedUnitWindowCampbellCount timedEmbeddedArrivalIndices
      timedEmbeddedRecenterAt (fun z i => z.2 i) s z : ENNReal) ∂base.Pbase =
      ENNReal.ofReal (arrivalRate : ℝ) * selectedTagged.Ptag s := by
  rw [H s hs]
  rw [total_uniformized_rate_mul_birthProbability_ennreal hservice_pos]

end AppliedModelingLib.Probability.Queueing
