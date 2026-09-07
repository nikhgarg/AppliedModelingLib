import AppliedModelingLib.Foundations.Probability.FiniteIidEmpiricalFrequency
import AppliedModelingLib.Learning.HumanFeedback.PairwiseReportCounts

/-!
# Deterministic finite-sample bounds for literal pairwise reports

These lemmas preserve the literal ordered-pair/Boolean-report experiment while
relating its empirical atom frequencies to the directed counts used by the
finite pairwise MLE.  They are the deterministic component of a finite-data
MLE consistency argument.
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback
namespace PairwiseCountDataset

open Probability

/-- Every CDF-like link separates a compact interior probability interval from
its two score tails by one finite positive score bound. -/
theorem CDFLikePairwiseLink.exists_pos_tailBand
    (link : CDFLikePairwiseLink) (threshold : ℝ)
    (hthreshold_pos : 0 < threshold) (hthreshold_lt_one : threshold < 1) :
    ∃ bound : ℝ, 0 < bound ∧ link (-bound) < threshold ∧ 1 - threshold < link bound := by
  have hlow_event : ∀ᶠ gap in Filter.atBot, link gap < threshold :=
    link.tendsto_atBot_zero.eventually (Iio_mem_nhds hthreshold_pos)
  obtain ⟨lowGap, hlowGap, hlow_le_neg_one⟩ :=
    (hlow_event.and (Filter.eventually_le_atBot (-1 : ℝ))).exists
  let lowBound : ℝ := -lowGap
  have hlowBound_pos : 0 < lowBound := by
    dsimp [lowBound]
    linarith
  have hlow : link (-lowBound) < threshold := by
    dsimp [lowBound]
    simpa only [neg_neg] using hlowGap
  have hhigh_event : ∀ᶠ gap in Filter.atTop, 1 - threshold < link gap :=
    link.tendsto_atTop_one.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨highBound, hhigh, hone_le_high⟩ :=
    (hhigh_event.and (Filter.eventually_ge_atTop (1 : ℝ))).exists
  let bound : ℝ := max lowBound highBound
  refine ⟨bound, lt_of_lt_of_le hlowBound_pos (le_max_left _ _), ?_, ?_⟩
  · have hneg : -bound ≤ -lowBound := neg_le_neg (le_max_left _ _)
    exact lt_of_le_of_lt (link.monotone hneg) hlow
  · exact lt_of_lt_of_le hhigh (link.monotone (le_max_right _ _))

/-- A direct-true report count is bounded by the corresponding aggregated
directed winner count. -/
theorem empiricalCount_directTrueBinaryReport_le_ofBinaryReports_count
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (winner loser : Alternative) (hneq : winner ≠ loser) :
    Probability.empiricalCount sample (directTrueBinaryReport winner loser) ≤
      (ofBinaryReports sample).count winner loser := by
  classical
  unfold Probability.empiricalCount successIndexSet ofBinaryReports
  change ((Finset.univ : Finset (Fin horizon)).filter
      (fun index => sample index = directTrueBinaryReport winner loser)).card ≤
    ((Finset.univ : Finset (Fin horizon)).filter
      (fun index => binaryReportWin winner loser (sample index))).card
  apply Finset.card_le_card
  intro index hindex
  simp only [Finset.mem_filter] at hindex ⊢
  refine ⟨hindex.1, ?_⟩
  rw [hindex.2]
  exact binaryReportWin_direct_true hneq

/-- A literal report cannot simultaneously record both directions of one
non-diagonal pair as wins. -/
theorem not_binaryReportWin_and_reverse
    {Alternative : Type*} [DecidableEq Alternative]
    (winner loser : Alternative) (hneq : winner ≠ loser)
    (report : BinaryPairwiseReport Alternative) :
    ¬ (binaryReportWin winner loser report ∧ binaryReportWin loser winner report) := by
  intro hboth
  rcases hboth.1 with ⟨_, hforward⟩
  rcases hboth.2 with ⟨_, hreverse⟩
  rcases hforward with hforward | hforward <;>
    rcases hreverse with hreverse | hreverse
  all_goals simp_all

/-- The two directed counts for one non-diagonal pair use disjoint subsets of
the `horizon` literal reports, so their sum is at most that horizon. -/
theorem ofBinaryReports_count_add_reverse_le_horizon
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (winner loser : Alternative) (hneq : winner ≠ loser) :
    (ofBinaryReports sample).count winner loser +
      (ofBinaryReports sample).count loser winner ≤ horizon := by
  classical
  let forward : Finset (Fin horizon) :=
    (Finset.univ : Finset (Fin horizon)).filter
      (fun index => binaryReportWin winner loser (sample index))
  let reverse : Finset (Fin horizon) :=
    (Finset.univ : Finset (Fin horizon)).filter
      (fun index => binaryReportWin loser winner (sample index))
  have hdisjoint : Disjoint forward reverse := by
    rw [Finset.disjoint_left]
    intro index hforward hreverse
    exact not_binaryReportWin_and_reverse winner loser hneq (sample index)
      ⟨(Finset.mem_filter.mp hforward).2, (Finset.mem_filter.mp hreverse).2⟩
  have hsubset : forward ∪ reverse ⊆ (Finset.univ : Finset (Fin horizon)) := by
    intro index _
    simp
  change forward.card + reverse.card ≤ horizon
  calc
    forward.card + reverse.card = (forward ∪ reverse).card :=
      (Finset.card_union_of_disjoint hdisjoint).symm
    _ ≤ (Finset.univ : Finset (Fin horizon)).card := Finset.card_le_card hsubset
    _ = horizon := Fintype.card_fin horizon

/-- If the two direct-true report atoms of a displayed pair both occur with
at least a `threshold` fraction of the literal sample, the empirical directed
win frequency lies in `[threshold, 1 - threshold]`. -/
theorem empiricalWinFrequency_mem_Icc_of_directTrueLowerFrequency
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (winner loser : Alternative) (hneq : winner ≠ loser) (threshold : ℝ)
    (horizon_pos : 0 < horizon) (hthreshold : 0 < threshold)
    (hforward : (horizon : ℝ) * threshold ≤
      (Probability.empiricalCount sample (directTrueBinaryReport winner loser) : ℝ))
    (hreverse : (horizon : ℝ) * threshold ≤
      (Probability.empiricalCount sample (directTrueBinaryReport loser winner) : ℝ)) :
    (0 < (ofBinaryReports sample).count winner loser) ∧
      (0 < (ofBinaryReports sample).count loser winner) ∧
      threshold ≤
        ((ofBinaryReports sample).count winner loser : ℝ) /
          ((ofBinaryReports sample).count winner loser +
            (ofBinaryReports sample).count loser winner) ∧
      ((ofBinaryReports sample).count winner loser : ℝ) /
          ((ofBinaryReports sample).count winner loser +
            (ofBinaryReports sample).count loser winner) ≤ 1 - threshold := by
  let dataset := ofBinaryReports sample
  have hdirect_forward :=
    empiricalCount_directTrueBinaryReport_le_ofBinaryReports_count sample winner loser hneq
  have hdirect_reverse :=
    empiricalCount_directTrueBinaryReport_le_ofBinaryReports_count sample loser winner hneq.symm
  have hforward_real :
      (Probability.empiricalCount sample (directTrueBinaryReport winner loser) : ℝ) ≤
        (dataset.count winner loser : ℝ) := by
    exact_mod_cast hdirect_forward
  have hreverse_real :
      (Probability.empiricalCount sample (directTrueBinaryReport loser winner) : ℝ) ≤
        (dataset.count loser winner : ℝ) := by
    exact_mod_cast hdirect_reverse
  have hcount_forward : (horizon : ℝ) * threshold ≤ (dataset.count winner loser : ℝ) :=
    hforward.trans hforward_real
  have hcount_reverse : (horizon : ℝ) * threshold ≤ (dataset.count loser winner : ℝ) :=
    hreverse.trans hreverse_real
  have hsum_nat := ofBinaryReports_count_add_reverse_le_horizon sample winner loser hneq
  have hsum :
      (dataset.count winner loser : ℝ) + (dataset.count loser winner : ℝ) ≤ horizon := by
    exact_mod_cast hsum_nat
  have hn_pos : (0 : ℝ) < horizon := by exact_mod_cast horizon_pos
  have hforward_pos : 0 < dataset.count winner loser := by
    by_contra hnot
    have hzero : dataset.count winner loser = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hcount_forward
    norm_num at hcount_forward
    have : 0 < (horizon : ℝ) * threshold := by
      nlinarith [hforward]
    linarith
  have hreverse_pos : 0 < dataset.count loser winner := by
    by_contra hnot
    have hzero : dataset.count loser winner = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hcount_reverse
    norm_num at hcount_reverse
    have : 0 < (horizon : ℝ) * threshold := by
      nlinarith [hreverse]
    linarith
  have hden_pos :
      0 < (dataset.count winner loser : ℝ) + (dataset.count loser winner : ℝ) := by
    exact add_pos (by exact_mod_cast hforward_pos) (by exact_mod_cast hreverse_pos)
  refine ⟨hforward_pos, hreverse_pos, ?_, ?_⟩
  · apply (le_div_iff₀ hden_pos).2
    calc
      threshold * ((dataset.count winner loser : ℝ) + (dataset.count loser winner : ℝ)) ≤
          threshold * (horizon : ℝ) := by
        exact mul_le_mul_of_nonneg_left hsum hthreshold.le
      _ = (horizon : ℝ) * threshold := by ring
      _ ≤ (dataset.count winner loser : ℝ) := hcount_forward
  · apply (div_le_iff₀ hden_pos).2
    have hscaled_reverse :
        threshold * ((dataset.count winner loser : ℝ) + (dataset.count loser winner : ℝ)) ≤
          (dataset.count loser winner : ℝ) := by
      calc
        threshold * ((dataset.count winner loser : ℝ) + (dataset.count loser winner : ℝ)) ≤
            threshold * (horizon : ℝ) := by
          exact mul_le_mul_of_nonneg_left hsum hthreshold.le
        _ = (horizon : ℝ) * threshold := by ring
        _ ≤ (dataset.count loser winner : ℝ) := hcount_reverse
    linarith

/-- Interior empirical directed-win frequencies force the corresponding
perfect-fit score distance into the finite score interval identified by the
CDF-like link tails. -/
theorem perfectFitDistance_mem_Icc_of_directTrueLowerFrequency
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ))
    (winner loser : Alternative) (hneq : winner ≠ loser)
    (threshold bound : ℝ) (horizon_pos : 0 < horizon) (hthreshold : 0 < threshold)
    (hforward : (horizon : ℝ) * threshold ≤
      (Probability.empiricalCount sample (directTrueBinaryReport winner loser) : ℝ))
    (hreverse : (horizon : ℝ) * threshold ≤
      (Probability.empiricalCount sample (directTrueBinaryReport loser winner) : ℝ))
    (hlow : link (-bound) < threshold) (hhigh : 1 - threshold < link bound) :
    -bound ≤ (ofBinaryReports sample).perfectFitDistance link hcontinuous winner loser ∧
      (ofBinaryReports sample).perfectFitDistance link hcontinuous winner loser ≤ bound := by
  let dataset := ofBinaryReports sample
  obtain ⟨hforward_pos, hreverse_pos, hfrequency_lower, hfrequency_upper⟩ :=
    empiricalWinFrequency_mem_Icc_of_directTrueLowerFrequency sample winner loser hneq threshold
      horizon_pos hthreshold hforward hreverse
  have hfit := link_perfectFitDistance_eq_empirical_frequency dataset link hcontinuous winner loser
    hforward_pos hreverse_pos
  constructor
  · by_contra hnot
    have hlt : dataset.perfectFitDistance link hcontinuous winner loser < -bound :=
      lt_of_not_ge hnot
    have hlink_lt :
        link (dataset.perfectFitDistance link hcontinuous winner loser) < threshold :=
      (hstrict hlt).trans hlow
    rw [hfit] at hlink_lt
    exact (not_lt_of_ge hfrequency_lower) hlink_lt
  · by_contra hnot
    have hlt : bound < dataset.perfectFitDistance link hcontinuous winner loser :=
      lt_of_not_ge hnot
    have hlink_lt : 1 - threshold <
        link (dataset.perfectFitDistance link hcontinuous winner loser) :=
      hhigh.trans (hstrict hlt)
    rw [hfit] at hlink_lt
    exact (not_lt_of_ge hfrequency_upper) hlink_lt

/-- On a literal report batch in which every directed direct-true atom has a
common positive linear frequency, every fixed-reference finite MLE belongs to
one deterministic score cube. -/
theorem scoreSupNorm_le_card_mul_bound_of_directTrueLowerFrequency
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) (reference : Alternative)
    (score : ScoreVector Alternative)
    (hmle : isPairwiseMLE (ofBinaryReports sample) link reference score)
    (threshold bound : ℝ) (horizon_pos : 0 < horizon) (hthreshold : 0 < threshold)
    (hdirect : ∀ winner loser, winner ≠ loser →
      (horizon : ℝ) * threshold ≤
        (Probability.empiricalCount sample (directTrueBinaryReport winner loser) : ℝ))
    (hbound_pos : 0 < bound) (hlow : link (-bound) < threshold)
    (hhigh : 1 - threshold < link bound) :
    scoreSupNorm reference score ≤ (Fintype.card Alternative : ℝ) * bound := by
  let dataset := ofBinaryReports sample
  have hn_pos : (0 : ℝ) < horizon := by exact_mod_cast horizon_pos
  have hcomplete : ∀ winner loser, winner ≠ loser → 0 < dataset.count winner loser := by
    intro winner loser hneq
    have hcount : (horizon : ℝ) * threshold ≤ (dataset.count winner loser : ℝ) := by
      exact (hdirect winner loser hneq).trans
        (by
          exact_mod_cast
            (empiricalCount_directTrueBinaryReport_le_ofBinaryReports_count
              sample winner loser hneq))
    have hpositive : 0 < (dataset.count winner loser : ℝ) := by
      exact lt_of_lt_of_le (mul_pos hn_pos hthreshold) hcount
    exact_mod_cast hpositive
  have hmax : dataset.maxPerfectFitDistance link hcontinuous reference ≤ bound := by
    unfold maxPerfectFitDistance
    apply Finset.max'_le
    rintro value hvalue
    rcases Finset.mem_image.mp hvalue with ⟨pair, _hpair, rfl⟩
    rcases pair with ⟨winner, loser⟩
    by_cases hneq : winner ≠ loser
    · exact
        (perfectFitDistance_mem_Icc_of_directTrueLowerFrequency sample link hcontinuous hstrict
          winner loser hneq threshold bound horizon_pos hthreshold
          (hdirect winner loser hneq) (hdirect loser winner hneq.symm) hlow hhigh).2
    · have heq : winner = loser := not_ne_iff.mp hneq
      subst loser
      rw [perfectFitDistance_self]
      exact hbound_pos.le
  exact (scoreSupNorm_le_card_mul_maxPerfectFitDistance_of_pairwiseMLE
    dataset link hcontinuous hstrict reference score hmle hcomplete).trans
      (mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _))

end PairwiseCountDataset
end HumanFeedback
end Learning
end AppliedModelingLib
