import AppliedModelingLib.Foundations.Probability.PoissonSuspensionEquilibriumSection
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionBaseArrivals
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalHeadTail
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalTimeSliceReconstruction

/-!
# A deterministic continuation for equilibrium renewal time slices

The complete pre-clock history of an equilibrium renewal path can be joined
to a positive continuation drawn from its exposed backward half.  This gives
an explicit good suspension state using no residual future-gap coordinate.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open Filter

noncomputable section

/-- Rebuilding an equilibrium path from its deterministic pre-clock history
and its exposed backward renewal half produces a valid good suspension when
the stated pointwise positivity and nonexplosion hypotheses hold. -/
theorem equilibriumToSuspension_reconstructPastTail_mem_good
    (s : ℝ) (future past : ℕ → ℝ)
    (hs : 0 ≤ s)
    (hfuture : ∃ m : ℕ, s < arrivalTime m future)
    (hfuturePos : ∀ n, 0 < interarrival n future)
    (hpastZero : 0 ≤ past 0)
    (hpastTailPos : ∀ n, 0 < interarrival n (fun m => past (m + 1)))
    (hpastTail : Tendsto (fun n : ℕ =>
      arrivalTime n (fun m => past (m + 1))) atTop atTop) :
    equilibriumToSuspension
      (reconstructCanonicalRenewalPath s (canonicalRenewalPastHistory s future)
        (fun n => past (n + 1)), past) ∈
      {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1} := by
  have hreconPos : ∀ n, 0 < interarrival n
      (reconstructCanonicalRenewalPath s (canonicalRenewalPastHistory s future)
        (fun m => past (m + 1))) :=
    all_interarrival_pos_reconstructCanonicalRenewalPath s future
      (fun m => past (m + 1)) hs hfuture hfuturePos hpastTailPos
  have hrecon : Tendsto (fun n : ℕ => arrivalTime n
      (reconstructCanonicalRenewalPath s (canonicalRenewalPastHistory s future)
        (fun m => past (m + 1)))) atTop atTop :=
    tendsto_arrivalTime_reconstructCanonicalRenewalPath s future
      (fun m => past (m + 1)) hpastTail
  have hpast : Tendsto (fun n : ℕ => arrivalTime n past) atTop atTop := by
    have hpastEq : past = prependInterarrival (past 0) (fun m => past (m + 1)) := by
      funext n
      cases n <;> rfl
    rw [hpastEq]
    exact tendsto_arrivalTime_prependInterarrival (past 0)
      (fun m => past (m + 1)) hpastTail
  exact equilibriumToSuspension_mem_good_of_positive_of_future_past
    _ _ hreconPos hpastTailPos hpastZero hrecon hpast

/-- The forward renewal epochs of the equilibrium representation are the
future suspension renewal epochs shifted to the physical origin. -/
theorem arrivalTime_suspensionToEquilibrium_future_eq_sub
    (p : GoodSuspensionState) (n : ℕ) :
    arrivalTime n (suspensionToEquilibrium p.1).1 =
      arrivalTime n (suspensionFuturePath p.1.1) - p.1.2 := by
  induction n with
    | zero =>
        simp [arrivalTime, suspensionToEquilibrium, suspensionFuturePath,
          interarrival, twoSidedGap]
    | succ n ih =>
        rw [show arrivalTime (n + 1) (suspensionToEquilibrium p.1).1 =
            arrivalTime n (suspensionToEquilibrium p.1).1 +
              interarrival (n + 1) (suspensionToEquilibrium p.1).1 by
          simp [arrivalTime, Finset.sum_range_succ], ih]
        have hgap : interarrival (n + 1) (suspensionToEquilibrium p.1).1 =
            interarrival (n + 1) (suspensionFuturePath p.1.1) := by
          simp [interarrival, suspensionToEquilibrium, suspensionFuturePath,
            twoSidedGap]
        rw [hgap]
        rw [show arrivalTime (n + 1) (suspensionFuturePath p.1.1) =
            arrivalTime n (suspensionFuturePath p.1.1) +
              interarrival (n + 1) (suspensionFuturePath p.1.1) by
          simp [arrivalTime, Finset.sum_range_succ]]
        ring

/-- The future equilibrium half of a literal good suspension is nonexplosive.
In particular, its renewal epochs escape every deterministic time bound. -/
theorem tendsto_arrivalTime_suspensionToEquilibrium_future_of_goodSuspension
    (p : GoodSuspensionState) :
    Tendsto (fun n : ℕ => arrivalTime n
      (suspensionToEquilibrium p.1).1) atTop atTop := by
  have hsuspension := suspensionGoodGapPath_future p.1.1 p.2.2
  have hsub : Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath p.1.1) - p.1.2) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-p.1.2) hsuspension
  apply hsub.congr'
  filter_upwards [] with n
  exact (arrivalTime_suspensionToEquilibrium_future_eq_sub p n).symm

/-- Physical-time counting from a good stationary suspension agrees with the
canonical renewal count of its equilibrium forward representation. -/
theorem canonicalRenewalCount_suspensionToEquilibrium_future_eq_suspensionBaseFutureCount
    (p : GoodSuspensionState) (t : ℝ) :
    canonicalRenewalCount t (suspensionToEquilibrium p.1).1 =
      suspensionBaseFutureCount p t := by
  classical
  have heq : ∀ n : ℕ,
      t < arrivalTime n (suspensionToEquilibrium p.1).1 ↔
        p.1.2 + t < arrivalTime n (suspensionFuturePath p.1.1) := by
    intro n
    rw [arrivalTime_suspensionToEquilibrium_future_eq_sub]
    constructor <;> intro hn <;> linarith
  have hfutureEquilibrium : ∃ n : ℕ,
      t < arrivalTime n (suspensionToEquilibrium p.1).1 :=
    (tendsto_arrivalTime_suspensionToEquilibrium_future_of_goodSuspension p
      |>.eventually_gt_atTop t).exists
  have hfutureSuspension : ∃ n : ℕ,
      p.1.2 + t < arrivalTime n (suspensionFuturePath p.1.1) :=
    (suspensionGoodGapPath_future p.1.1 p.2.2
      |>.eventually_gt_atTop (p.1.2 + t)).exists
  rw [canonicalRenewalCount_eq_find t _ hfutureEquilibrium,
    show suspensionBaseFutureCount p t =
      canonicalRenewalCount (p.1.2 + t) (suspensionFuturePath p.1.1) by rfl,
    canonicalRenewalCount_eq_find _ _ hfutureSuspension]
  exact Nat.find_congr' (fun {_} => heq _)

/-- The future equilibrium half of a literal good suspension has arrivals
beyond every deterministic clock. -/
theorem exists_arrivalTime_gt_suspensionToEquilibrium_future_of_goodSuspension
    (s : ℝ) (p : GoodSuspensionState) :
    ∃ m : ℕ, s < arrivalTime m (suspensionToEquilibrium p.1).1 := by
  have hfutureTendsto :=
    tendsto_arrivalTime_suspensionToEquilibrium_future_of_goodSuspension p
  obtain ⟨m, hm⟩ :=
    eventually_atTop.1 (hfutureTendsto.eventually_gt_atTop s)
  exact ⟨m, hm m le_rfl⟩

/-- A literal suspension state supplies the positive, nonexplosive equilibrium
halves required to continue a deterministic renewal time slice with its own
exposed backward tail. -/
theorem equilibriumToSuspension_reconstructPastTail_mem_good_of_goodSuspension
    (s : ℝ) (p : GoodSuspensionState) (hs : 0 ≤ s) :
    equilibriumToSuspension
      (reconstructCanonicalRenewalPath s
        (canonicalRenewalPastHistory s (suspensionToEquilibrium p.1).1)
        (fun n => (suspensionToEquilibrium p.1).2 (n + 1)),
      (suspensionToEquilibrium p.1).2) ∈
      {q : (ℤ → ℝ) × ℝ | q ∈ suspensionCarrier ∧ suspensionGoodGapPath q.1} := by
  have hfuturePos : ∀ n, 0 < interarrival n (suspensionToEquilibrium p.1).1 := by
    intro n
    cases n with
    | zero =>
        change 0 < twoSidedGap 0 p.1.1 - p.1.2
        linarith [p.2.1.2]
    | succ n =>
        simpa [interarrival, suspensionToEquilibrium, twoSidedGap] using
          p.2.2.1 (Int.ofNat (n + 1))
  have hpastZero : 0 ≤ (suspensionToEquilibrium p.1).2 0 := by
    simpa [suspensionToEquilibrium] using p.2.1.1
  have hpastTailPos : ∀ n, 0 < interarrival n
      (fun m => (suspensionToEquilibrium p.1).2 (m + 1)) := by
    intro n
    simpa [interarrival, suspensionToEquilibrium, twoSidedGap] using
      p.2.2.1 (Int.negSucc n)
  have hpastTail : Tendsto (fun n : ℕ => arrivalTime n
      (fun m => (suspensionToEquilibrium p.1).2 (m + 1))) atTop atTop := by
    have hpast := suspensionGoodGapPath_past p.1.1 p.2.2
    simpa [suspensionPastPath, suspensionToEquilibrium, twoSidedGap] using hpast
  have hfuture :=
    exists_arrivalTime_gt_suspensionToEquilibrium_future_of_goodSuspension s p
  exact equilibriumToSuspension_reconstructPastTail_mem_good s
    (suspensionToEquilibrium p.1).1 (suspensionToEquilibrium p.1).2 hs hfuture
    hfuturePos hpastZero hpastTailPos hpastTail

end

end AppliedModelingLib.Probability.PoissonProcess
