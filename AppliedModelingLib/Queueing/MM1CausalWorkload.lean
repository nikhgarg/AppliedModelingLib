import AppliedModelingLib.Foundations.Probability.ExponentialMoments
import AppliedModelingLib.Foundations.Probability.ExponentialReflectedDifference

/-!
# Stationary M/M/1 pre-arrival workload laws

This module records the probability law that is invariant under the
one-customer Lindley update for a stable M/M/1 workload.  It is deliberately
only a law-level API: a queue-specific construction must separately
prove that its literal causal workload has this law.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The positive spare service rate of a stable M/M/1 queue. -/
def mm1SlackRate (arrivalRate serviceRate : ℝ) : ℝ :=
  serviceRate - arrivalRate

/-- The stationary pre-arrival workload law of a stable M/M/1 queue: an atom
at zero together with an exponential positive branch. -/
def mm1PreArrivalWorkloadLaw (arrivalRate serviceRate : ℝ) : Measure ℝ :=
  ENNReal.ofReal (mm1SlackRate arrivalRate serviceRate / serviceRate) •
      Measure.dirac 0 +
    ENNReal.ofReal (arrivalRate / serviceRate) •
      expMeasure (mm1SlackRate arrivalRate serviceRate)

/-- The M/M/1 pre-arrival law is the reflected difference of independent
spare-capacity and arrival clocks. -/
theorem mm1PreArrivalWorkloadLaw_eq_reflectedDifference
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    mm1PreArrivalWorkloadLaw arrivalRate serviceRate =
      Measure.map Probability.exponentialReflectedDifference
        ((expMeasure (mm1SlackRate arrivalRate serviceRate)).prod
          (expMeasure arrivalRate)) := by
  have hslack : 0 < mm1SlackRate arrivalRate serviceRate := by
    exact sub_pos.mpr hstable
  have hsum : mm1SlackRate arrivalRate serviceRate + arrivalRate = serviceRate := by
    unfold mm1SlackRate
    linarith
  simpa [mm1PreArrivalWorkloadLaw, hsum] using
    (Probability.map_exponentialReflectedDifference_expMeasure_prod hslack harrival).symm

/-- The M/M/1 pre-arrival workload law is a probability measure. -/
theorem isProbabilityMeasure_mm1PreArrivalWorkloadLaw
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    IsProbabilityMeasure (mm1PreArrivalWorkloadLaw arrivalRate serviceRate) := by
  letI : IsProbabilityMeasure (expMeasure (mm1SlackRate arrivalRate serviceRate)) :=
    isProbabilityMeasure_expMeasure (sub_pos.mpr hstable)
  letI : IsProbabilityMeasure (expMeasure arrivalRate) :=
    isProbabilityMeasure_expMeasure harrival
  rw [mm1PreArrivalWorkloadLaw_eq_reflectedDifference harrival hstable]
  exact Measure.isProbabilityMeasure_map
    Probability.measurable_exponentialReflectedDifference.aemeasurable

/-- The stationary M/M/1 pre-arrival workload is nonnegative almost surely. -/
theorem ae_nonnegative_mm1PreArrivalWorkloadLaw
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    ∀ᵐ w ∂mm1PreArrivalWorkloadLaw arrivalRate serviceRate, 0 ≤ w := by
  rw [mm1PreArrivalWorkloadLaw_eq_reflectedDifference harrival hstable]
  rw [MeasureTheory.ae_map_iff
    Probability.measurable_exponentialReflectedDifference.aemeasurable measurableSet_Ici]
  filter_upwards with pair
  exact le_max_right _ _

/-- The stable M/M/1 pre-arrival workload has a finite first moment. -/
theorem integrable_id_mm1PreArrivalWorkloadLaw
    {arrivalRate serviceRate : ℝ}
    (hstable : arrivalRate < serviceRate) :
    Integrable (fun w : ℝ => w) (mm1PreArrivalWorkloadLaw arrivalRate serviceRate) := by
  unfold mm1PreArrivalWorkloadLaw
  rw [integrable_add_measure]
  constructor
  · exact (integrable_dirac (by simp)).smul_measure
      ENNReal.ofReal_ne_top
  · exact (Probability.integrable_id_expMeasure (sub_pos.mpr hstable)).smul_measure
      ENNReal.ofReal_ne_top

/-- The squared stationary M/M/1 pre-arrival workload is integrable. -/
theorem integrable_sq_mm1PreArrivalWorkloadLaw
    {arrivalRate serviceRate : ℝ}
    (hstable : arrivalRate < serviceRate) :
    Integrable (fun w : ℝ => w ^ 2)
      (mm1PreArrivalWorkloadLaw arrivalRate serviceRate) := by
  unfold mm1PreArrivalWorkloadLaw
  rw [integrable_add_measure]
  constructor
  · exact (integrable_dirac (by simp)).smul_measure
      ENNReal.ofReal_ne_top
  · exact (Probability.integrable_sq_expMeasure (sub_pos.mpr hstable)).smul_measure
      ENNReal.ofReal_ne_top

end

end AppliedModelingLib.Queueing
