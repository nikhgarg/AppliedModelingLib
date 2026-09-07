import AppliedModelingLib.Foundations.Probability.ExponentialInterarrival
import AppliedModelingLib.Queueing.Core

/-!
# Canonical renewal service and the FCFS tagged comparator

This module gives the deterministic bridge between the canonical exponential
renewal path used for potential service completions and the tagged-job FCFS
comparator.  It does not construct an arrival process or a stationary queue.
-/

namespace AppliedModelingLib.Probability.Queueing

open PoissonProcess

noncomputable section

/-- Time by which the `q` jobs ahead of the tag have used their potential
service completions. -/
def preTagBusyUntil (q : ℕ) (g : ℕ → ℝ) : ℝ :=
  match q with
  | 0 => 0
  | n + 1 => arrivalTime n g

/-- The tagged FCFS job has the service requirement corresponding to the
`q`th exponential potential-service gap. -/
def taggedServiceWork (rate : ℝ) (q : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun n => if n = 0 then rate * interarrival q g else 0

/-- The isolated comparator fragment has no post-tag arrivals. -/
def tagOnlyArrival : ℕ → ℝ := fun _ => 0

/-- The tagged FCFS response is exactly the canonical renewal time of the
`(q + 1)`st potential completion. -/
theorem canonicalRenewalResponse_eq_fcfsTaggedResponse
    {rate : ℝ} (hrate : 0 < rate) (q : ℕ) (g : ℕ → ℝ)
    (hpos : ∀ i : ℕ, 0 < interarrival i g) :
    responseTime tagOnlyArrival
      (fcfsDepartureFrom (preTagBusyUntil q g) tagOnlyArrival
        (taggedServiceWork rate q g) rate) 0 =
      arrivalTime q g := by
  cases q with
  | zero =>
      simp [responseTime, fcfsDepartureFrom, tagOnlyArrival, taggedServiceWork,
        preTagBusyUntil, arrivalTime, interarrival, hrate.ne']
  | succ q =>
      have hnonneg : 0 ≤ arrivalTime q g := by
        unfold arrivalTime
        exact Finset.sum_nonneg fun i hi => (hpos i).le
      have hdiv : rate * interarrival (q + 1) g / rate =
          interarrival (q + 1) g := by
        field_simp [hrate.ne']
      simp only [responseTime, fcfsDepartureFrom, tagOnlyArrival,
        taggedServiceWork, preTagBusyUntil, if_pos, sub_zero]
      rw [max_eq_right hnonneg, hdiv]
      simp [arrivalTime, Finset.sum_range_succ, Nat.add_assoc]

end

end AppliedModelingLib.Probability.Queueing
