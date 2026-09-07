import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCount

/-!
# Renewal paths assembled from a head and tail

This module records the elementary renewal-time behavior of a path formed by
prepending one interarrival coordinate to a tail path.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open Filter

noncomputable section

/-- Prepend one interarrival coordinate to a renewal tail. -/
def prependInterarrival (head : ℝ) (tail : ℕ → ℝ) : ℕ → ℝ
  | 0 => head
  | n + 1 => tail n

/-- Renewal epochs beyond the prepended coordinate are exactly the tail
epochs shifted by the head length. -/
theorem arrivalTime_prependInterarrival (head : ℝ) (tail : ℕ → ℝ) (n : ℕ) :
    arrivalTime (n + 1) (prependInterarrival head tail) = head + arrivalTime n tail := by
  induction n with
  | zero =>
      simp [arrivalTime, interarrival, prependInterarrival, Finset.sum_range_succ]
  | succ n ih =>
      rw [show arrivalTime ((n + 1) + 1) (prependInterarrival head tail) =
          arrivalTime (n + 1) (prependInterarrival head tail) +
            interarrival ((n + 1) + 1) (prependInterarrival head tail) by
        simp [arrivalTime, Finset.sum_range_succ], ih]
      rw [show arrivalTime (n + 1) tail = arrivalTime n tail +
          interarrival (n + 1) tail by simp [arrivalTime, Finset.sum_range_succ]]
      change head + arrivalTime n tail + tail (n + 1) =
        head + (arrivalTime n tail + tail (n + 1))
      ring

/-- A nonexplosive tail remains nonexplosive after one interarrival is
prepended. -/
theorem tendsto_arrivalTime_prependInterarrival
    (head : ℝ) (tail : ℕ → ℝ)
    (htail : Tendsto (fun n : ℕ => arrivalTime n tail) atTop atTop) :
    Tendsto (fun n : ℕ => arrivalTime n (prependInterarrival head tail)) atTop atTop := by
  have hshift : Tendsto (fun n : ℕ => head + arrivalTime (n - 1) tail) atTop atTop := by
    exact (tendsto_atTop_add_const_left atTop head htail).comp (tendsto_sub_atTop_nat 1)
  apply hshift.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [show n = (n - 1) + 1 by omega, arrivalTime_prependInterarrival]
  congr 2

/-- Once the prepended first gap has elapsed, the renewal count is one plus
the count of the literal tail at the remaining elapsed time.  This is a
pathwise identity; no distributional or memorylessness premise is used. -/
theorem canonicalRenewalCount_head_add_prependInterarrival
    (head : ℝ) (tail : ℕ → ℝ)
    (htail : Tendsto (fun n : ℕ => arrivalTime n tail) atTop atTop)
    (t : ℝ) (ht : 0 ≤ t) :
    canonicalRenewalCount (head + t) (prependInterarrival head tail) =
      canonicalRenewalCount t tail + 1 := by
  let n := canonicalRenewalCount t tail
  have hfuture : ∃ m : ℕ, t < arrivalTime m tail :=
    exists_arrivalTime_gt_of_tendsto_atTop tail htail t
  change canonicalRenewalCount (head + t) (prependInterarrival head tail) = n + 1
  apply (canonicalRenewalCount_eq_succ_iff (head + t)
    (prependInterarrival head tail) n).mpr
  constructor
  · rw [arrivalTime_prependInterarrival]
    have hnext := lt_arrivalTime_canonicalRenewalCount t tail hfuture
    linarith
  · intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp only [arrivalTime, interarrival, prependInterarrival,
        Finset.sum_range_succ, Finset.sum_range_zero]
      linarith
    · have hmne : m ≠ 0 := Nat.ne_of_gt hmpos
      obtain ⟨k, hkEq⟩ := Nat.exists_eq_succ_of_ne_zero hmne
      subst m
      have hk : k < n := Nat.lt_of_succ_lt_succ hm
      have hle := arrivalTime_le_of_lt_canonicalRenewalCount t tail hfuture hk
      rw [arrivalTime_prependInterarrival]
      linarith

end

end AppliedModelingLib.Probability.PoissonProcess
