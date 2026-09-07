import AppliedModelingLib.Foundations.Probability.PoissonSuspensionFlow

/-!
# Reindexing nonexplosive two-sided renewal paths

This module shows that for a positive two-sided gap path, nonexplosion of the
forward and backward renewal halves at one origin automatically persists
after every deterministic integer reindexing.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter

noncomputable section

private theorem tendsto_future_suspensionGapShift_ofNat
    (omega : ℤ → ℝ) (q : ℕ)
    (hfuture : Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath omega)) atTop atTop) :
    Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath (suspensionGapShift (Int.ofNat q) omega)))
      atTop atTop := by
  have hshift : Tendsto (fun n : ℕ =>
      arrivalTime (q + n) (suspensionFuturePath omega)) atTop atTop := by
    simpa [add_comm] using hfuture.comp (tendsto_add_atTop_nat q)
  have hsub : Tendsto (fun n : ℕ =>
      arrivalTime (q + n) (suspensionFuturePath omega) -
        candidatePalmArrival omega (Int.ofNat q)) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-candidatePalmArrival omega (Int.ofNat q)) hshift
  apply hsub.congr'
  filter_upwards [] with n
  rw [← candidateFutureEpoch_succ_eq_arrivalTime_suspension,
    ← candidateFutureEpoch_succ_eq_arrivalTime_suspension]
  change candidatePalmArrival omega (Int.ofNat (q + n + 1)) -
      candidatePalmArrival omega (Int.ofNat q) =
    candidatePalmArrival (suspensionGapShift (Int.ofNat q) omega) (Int.ofNat (n + 1))
  rw [candidatePalmArrival_suspensionGapShift]
  congr 1

private theorem tendsto_future_suspensionGapShift_negSucc
    (omega : ℤ → ℝ) (q : ℕ)
    (hfuture : Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath omega)) atTop atTop) :
    Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath (suspensionGapShift (Int.negSucc q) omega)))
      atTop atTop := by
  have hshift : Tendsto (fun n : ℕ =>
      arrivalTime (n - (q + 1)) (suspensionFuturePath omega)) atTop atTop := by
    exact hfuture.comp (tendsto_sub_atTop_nat (q + 1))
  have hsub : Tendsto (fun n : ℕ =>
      arrivalTime (n - (q + 1)) (suspensionFuturePath omega) -
        candidatePalmArrival omega (Int.negSucc q)) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-candidatePalmArrival omega (Int.negSucc q)) hshift
  apply hsub.congr'
  filter_upwards [eventually_ge_atTop (q + 1)] with n hn
  rw [← candidateFutureEpoch_succ_eq_arrivalTime_suspension,
    ← candidateFutureEpoch_succ_eq_arrivalTime_suspension]
  change candidatePalmArrival omega (Int.ofNat (n - (q + 1) + 1)) -
      candidatePalmArrival omega (Int.negSucc q) =
    candidatePalmArrival (suspensionGapShift (Int.negSucc q) omega) (Int.ofNat (n + 1))
  rw [candidatePalmArrival_suspensionGapShift]
  congr 1
  apply congrArg (candidatePalmArrival omega)
  have hnat : n - (q + 1) + 1 = n - q := by omega
  rw [hnat]
  change (↑(n - q) : ℤ) = Int.negSucc q + ↑(n + 1)
  rw [Int.ofNat_sub (by omega : q ≤ n), Int.negSucc_eq]
  push_cast
  ring

private theorem tendsto_past_suspensionGapShift_ofNat
    (omega : ℤ → ℝ) (q : ℕ)
    (hpast : Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionPastPath omega)) atTop atTop) :
    Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionPastPath (suspensionGapShift (Int.ofNat q) omega)))
      atTop atTop := by
  have hshift : Tendsto (fun n : ℕ =>
      arrivalTime (n - q) (suspensionPastPath omega)) atTop atTop := by
    exact hpast.comp (tendsto_sub_atTop_nat q)
  have hadd : Tendsto (fun n : ℕ =>
      candidatePalmArrival omega (Int.ofNat q) +
        arrivalTime (n - q) (suspensionPastPath omega)) atTop atTop := by
    exact tendsto_atTop_add_const_left atTop
      (candidatePalmArrival omega (Int.ofNat q)) hshift
  apply hadd.congr'
  filter_upwards [eventually_ge_atTop q] with n hn
  rw [← candidatePastGapSum_succ_eq_arrivalTime_suspension,
    ← candidatePastGapSum_succ_eq_arrivalTime_suspension]
  have hleft : candidatePastGapSum omega (n - q + 1) =
      -candidatePalmArrival omega (Int.negSucc (n - q)) := by
    rw [candidatePalmArrival_negSucc]
    ring
  have hright : candidatePastGapSum (suspensionGapShift (Int.ofNat q) omega) (n + 1) =
      -candidatePalmArrival (suspensionGapShift (Int.ofNat q) omega) (Int.negSucc n) := by
    rw [candidatePalmArrival_negSucc]
    ring
  rw [hleft, hright]
  rw [candidatePalmArrival_suspensionGapShift]
  ring_nf
  congr 1
  apply congrArg (candidatePalmArrival omega)
  change Int.negSucc (n - q) = Int.ofNat q + Int.negSucc n
  rw [Int.negSucc_eq, Int.ofNat_sub hn, Int.negSucc_eq]
  simp only [Int.ofNat_eq_natCast]
  ring

private theorem tendsto_past_suspensionGapShift_negSucc
    (omega : ℤ → ℝ) (q : ℕ)
    (hpast : Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionPastPath omega)) atTop atTop) :
    Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionPastPath (suspensionGapShift (Int.negSucc q) omega)))
      atTop atTop := by
  have hshift : Tendsto (fun n : ℕ =>
      arrivalTime (q + 1 + n) (suspensionPastPath omega)) atTop atTop := by
    simpa [add_assoc, add_comm, add_left_comm] using
      hpast.comp (tendsto_add_atTop_nat (q + 1))
  have hadd : Tendsto (fun n : ℕ =>
      candidatePalmArrival omega (Int.negSucc q) +
        arrivalTime (q + 1 + n) (suspensionPastPath omega)) atTop atTop := by
    exact tendsto_atTop_add_const_left atTop
      (candidatePalmArrival omega (Int.negSucc q)) hshift
  apply hadd.congr'
  filter_upwards [] with n
  rw [← candidatePastGapSum_succ_eq_arrivalTime_suspension,
    ← candidatePastGapSum_succ_eq_arrivalTime_suspension]
  have hleft : candidatePastGapSum omega (q + 1 + n + 1) =
      -candidatePalmArrival omega (Int.negSucc (q + 1 + n)) := by
    rw [candidatePalmArrival_negSucc]
    ring
  have hright : candidatePastGapSum (suspensionGapShift (Int.negSucc q) omega) (n + 1) =
      -candidatePalmArrival (suspensionGapShift (Int.negSucc q) omega) (Int.negSucc n) := by
    rw [candidatePalmArrival_negSucc]
    ring
  rw [hleft, hright]
  rw [candidatePalmArrival_suspensionGapShift]
  ring_nf
  congr 1
  apply congrArg (candidatePalmArrival omega)
  change Int.negSucc (1 + q + n) = Int.negSucc q + Int.negSucc n
  simp only [Int.negSucc_eq]
  push_cast
  ring

/-- Positive gaps whose ordinary forward and backward renewal halves do not
accumulate in finite time remain nonexplosive after every integer reindexing. -/
theorem suspensionGoodGapPath_of_positive_of_future_past
    (omega : ℤ → ℝ) (hpositive : ∀ i : ℤ, 0 < twoSidedGap i omega)
    (hfuture : Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath omega)) atTop atTop)
    (hpast : Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionPastPath omega)) atTop atTop) :
    suspensionGoodGapPath omega := by
  refine ⟨hpositive, ?_⟩
  intro k
  cases k with
  | ofNat q =>
      exact ⟨tendsto_future_suspensionGapShift_ofNat omega q hfuture,
        tendsto_past_suspensionGapShift_ofNat omega q hpast⟩
  | negSucc q =>
      exact ⟨tendsto_future_suspensionGapShift_negSucc omega q hfuture,
        tendsto_past_suspensionGapShift_negSucc omega q hpast⟩

end

end AppliedModelingLib.Probability.PoissonProcess
