import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.Campbell

/-!
# Selected marked points in a timed embedded suspension

This module proves the physical-time covariance of the point set retained by
an arbitrary Boolean mark read from a synchronized embedded path.  It is the
stationarity field needed by a marked Campbell/Palm certificate; it does not
assume that the selected points have been separately re-enumerated.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

open PoissonProcess

/-- The physical epochs whose synchronized embedded mark is `true`. -/
def timedEmbeddedSelectedPointSet
    {α : Type*} (mark : α → Bool)
    (z : GoodSuspensionState × (ℤ → α)) : Set ℝ :=
  {u | ∃ i, mark (z.2 i) = true ∧ timedEmbeddedArrival z i = u}

/-- The selected physical point set covaries pointwise under the timed
suspension flow. -/
theorem timedEmbeddedSelectedPointSet_flow
    {α : Type*} (mark : α → Bool)
    (z : GoodSuspensionState × (ℤ → α)) (t : ℝ) :
    timedEmbeddedSelectedPointSet mark
      (timedEmbeddedSuspensionFlow (α := α) t z) =
      (fun u : ℝ => u - t) '' timedEmbeddedSelectedPointSet mark z := by
  ext u
  constructor
  · rintro ⟨j, hjmark, hjarrival⟩
    let c : ℤ := suspensionCrossingIndexPastClosed t z.1.1
    refine ⟨timedEmbeddedArrival z (c + j), ?_, ?_⟩
    · refine ⟨c + j, ?_, rfl⟩
      simpa [c, timedEmbeddedSelectedPointSet] using hjmark
    · rw [← hjarrival]
      simpa [c] using (timedEmbeddedArrival_flow z t j).symm
  · rintro ⟨v, ⟨i, himark, hiarrival⟩, rfl⟩
    let c : ℤ := suspensionCrossingIndexPastClosed t z.1.1
    refine ⟨i - c, ?_, ?_⟩
    · change mark (timedEmbeddedState
        (timedEmbeddedSuspensionFlow (α := α) t z) (i - c)) = true
      rw [timedEmbeddedState_flow]
      simpa [c] using himark
    · rw [timedEmbeddedArrival_flow]
      simp [c, hiarrival]

end

end AppliedModelingLib.Probability.Queueing
