import FalahatgarEtAl2017MaxingRanking.PickAnchorSampling
import FalahatgarEtAl2017MaxingRanking.SampleBudget

/-!
# Pick-Anchor comparison cap

The source's asymptotic display is preceded by an exact finite cap: one
source-budgeted Compare batch for each of the `|Q| - 1` Seq-Eliminate calls.
-/

namespace FalahatgarEtAl2017MaxingRanking

/-- The exact ceiling-corrected cap for a Pick-Anchor sample of positive size. -/
theorem pickAnchorSample_ceilingComparisonCap
    (count : ℕ) (epsilon delta : ℝ)
    (hcount : 0 < count) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (((count - 1) * fixedSampleBudget 0 epsilon ((delta / 2) / (count : ℝ)) : ℕ) : ℝ) ≤
      ((count - 1 : ℕ) : ℝ) *
        (2 / epsilon ^ 2 * Real.log (2 / ((delta / 2) / (count : ℝ))) + 1) := by
  have hcountNat : 1 ≤ count := by omega
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hcountOne : (1 : ℝ) ≤ (count : ℝ) := by exact_mod_cast hcountNat
  have heta : 0 < (delta / 2) / (count : ℝ) := by positivity
  have hetaLeOne : (delta / 2) / (count : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hcountReal]
    nlinarith
  simpa only [sub_zero] using
    (finiteCallCount_ceilingBudget_real_le_sourceBudget (count - 1) 0 epsilon
      ((delta / 2) / (count : ℝ)) heta hetaLeOne)

/-- Lemma 3's exact finite comparison cap at the source's ceiling-and-cap sample size. -/
theorem pickAnchorSource_ceilingComparisonCap
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (delta epsilon : ℝ)
    (hcutoff : 0 < cutoff) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (((pickAnchorSampleCount (Fintype.card Arm) cutoff delta - 1) *
      fixedSampleBudget 0 epsilon
        ((delta / 2) / (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)) : ℕ) : ℝ) ≤
      ((pickAnchorSampleCount (Fintype.card Arm) cutoff delta - 1 : ℕ) : ℝ) *
        (2 / epsilon ^ 2 * Real.log
          (2 / ((delta / 2) /
            (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ))) + 1) := by
  apply pickAnchorSample_ceilingComparisonCap
  · exact pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta
      Fintype.card_pos hcutoff hdelta hdeltaLeOne
  · exact hdelta
  · exact hdeltaLeOne

end FalahatgarEtAl2017MaxingRanking
