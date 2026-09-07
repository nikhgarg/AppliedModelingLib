import GHW01DigitalGoods.RankedCutoff
import GHW01DigitalGoods.Section11FixedSizeBridge

/-!
# Fixed ranked-prefix sampling for Section 11

This module proves only the fixed-population concentration step needed by a
future repaired Section 11 proof.  The ranked prefix is selected from the full
bid profile before the half-sample is drawn.  It is therefore not a statement
about the adaptive sampled `opt_k` mechanism, its revenue, or its cap
rejections.
-/

namespace GHW01DigitalGoods

open AppliedModelingLib
open AppliedModelingLib.Auction

noncomputable section

/--
For an even population, the uniformly chosen half-sample underrepresents the
fixed full-population ranked optimal winner set with the stated lower-tail
probability.  The source scale assumption supplies the cardinal lower bound
on that fixed set; Lemma 6.1 then supplies the without-replacement tail bound.

This is intentionally a fixed-prefix result.  It does **not** assert a bound
for a threshold selected after observing the random sample.
-/
theorem fixed_rankedOptimalPrefix_halfSample_lower_tail
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (capacity m : ℕ)
    (hpopulation : Fintype.card Agent = 2 * m)
    (hm_pos : 0 < m)
    (hsample_lt : m < Fintype.card Agent)
    {h alpha delta : ℝ}
    (hh_pos : 0 < h) (hvalues_le : ∀ i : Agent, values i ≤ h)
    (hscale : alpha * h < boundedSupplyFixedPriceBenchmark values capacity)
    (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    (pmfEventProbability
        (uniformFixedSizeSampleLaw (Agent := Agent) m hsample_lt.le)
        (fun sample =>
          (fixedSizeHitCount (rankedBoundedOptimalWinnerSet values capacity)
            sample.1 : ℝ) <
            (1 - delta) *
              ((rankedBoundedOptimalWinnerSet values capacity).card : ℝ) / 2) <
      Real.exp (-(alpha * delta ^ 2 / 4))) := by
  let rankedWinners := rankedBoundedOptimalWinnerSet values capacity
  have hrankedWinners_gt : alpha < (rankedWinners.card : ℝ) := by
    simpa [rankedWinners] using
      (rankedBoundedOptimalWinnerSet_card_gt_of_scale
        values capacity hh_pos hvalues_le hscale)
  have hN_real : (Fintype.card Agent : ℝ) = 2 * (m : ℝ) := by
    exact_mod_cast hpopulation
  have hm_real_ne : (m : ℝ) ≠ 0 := by
    positivity
  have hthreshold :
      (1 - delta) * (rankedWinners.card : ℝ) * (m : ℝ) /
          (Fintype.card Agent : ℝ) =
        (1 - delta) * (rankedWinners.card : ℝ) / 2 := by
    rw [hN_real]
    field_simp
  have hexponent :
      -((rankedWinners.card : ℝ) * (m : ℝ) * delta ^ 2 /
          (2 * (Fintype.card Agent : ℝ))) =
        -((rankedWinners.card : ℝ) * delta ^ 2 / 4) := by
    rw [hN_real]
    field_simp
    norm_num
  have hlower := uniformFixedSizeSampleLaw_lower_tail
    rankedWinners hm_pos hsample_lt hdelta_pos hdelta_le_one
  rw [hthreshold, hexponent] at hlower
  have hfactor_pos : 0 < delta ^ 2 / 4 := by
    positivity
  have hscaled : alpha * (delta ^ 2 / 4) <
      (rankedWinners.card : ℝ) * (delta ^ 2 / 4) :=
    mul_lt_mul_of_pos_right hrankedWinners_gt hfactor_pos
  have hexponent_lt : -((rankedWinners.card : ℝ) * delta ^ 2 / 4) <
      -(alpha * delta ^ 2 / 4) := by
    calc
      -((rankedWinners.card : ℝ) * delta ^ 2 / 4) =
          -((rankedWinners.card : ℝ) * (delta ^ 2 / 4)) := by ring
      _ < -(alpha * (delta ^ 2 / 4)) := neg_lt_neg hscaled
      _ = -(alpha * delta ^ 2 / 4) := by ring
  have hexp_lt : Real.exp (-((rankedWinners.card : ℝ) * delta ^ 2 / 4)) <
      Real.exp (-(alpha * delta ^ 2 / 4)) :=
    Real.exp_lt_exp.mpr hexponent_lt
  simpa [rankedWinners] using hlower.trans hexp_lt

end

end GHW01DigitalGoods
