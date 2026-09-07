import GJ19OptimalBinaryRatingSystems.MainTheorems

/-!
# Appendix B.3 matching-rate comparative statics

This module proves Lemma B.1.  The proof follows the source's two common-rate
cases, but packages the coordinate propagation as a finite crossing argument:
if the pivot level moved the wrong way, an adjacent interval at the boundary
of the crossing would have a strict rate comparison contradicting the two
equalized common rates.
-/

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open AppliedModelingLib.Probability

/--
Lemma B.1 (matching-rate shift).  Above an interior pivot `k`, the new sample
rates weakly increase; below `k`, they weakly decrease; at `k`, they agree.
The equalized optimal level at the pivot therefore moves weakly upward.
-/
theorem lemmaB1_matching_rate_shift
    {m k : ℕ} (hk0 : 0 < k) (hkm : k < m + 1)
    (sampleRate shiftedRate : Fin (m + 2) → ℝ)
    (levels shiftedLevels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (hshiftedLevels : BinaryEndpointLevelVector shiftedLevels)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hshiftedEq :
      BinaryEndpointAwareAdjacentRatesEqualize shiftedLevels shiftedRate)
    (hsample_pos : ∀ i : Fin (m + 2), 0 < sampleRate i)
    (hshifted_pos : ∀ i : Fin (m + 2), 0 < shiftedRate i)
    (habove :
      ∀ i : Fin (m + 2), k < i.val → shiftedRate i ≤ sampleRate i)
    (hbelow :
      ∀ i : Fin (m + 2), i.val < k → sampleRate i ≤ shiftedRate i)
    (hpivot :
      sampleRate ⟨k, by omega⟩ = shiftedRate ⟨k, by omega⟩) :
    shiftedLevels ⟨k, by omega⟩ ≤ levels ⟨k, by omega⟩ := by
  let pivot : Fin (m + 2) := ⟨k, by omega⟩
  let first : Fin (m + 1) := firstAdjacentIndex
  let r : ℝ := binaryEndpointAwareAdjacentRate levels sampleRate first
  let shiftedR : ℝ :=
    binaryEndpointAwareAdjacentRate shiftedLevels shiftedRate first
  have hr :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate levels sampleRate i = r := by
    intro i
    exact heq i first
  have hshiftedR :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate shiftedLevels shiftedRate i = shiftedR := by
    intro i
    exact hshiftedEq i first
  have habove' :
      ∀ i : Fin (m + 2), k ≤ i.val → shiftedRate i ≤ sampleRate i := by
    intro i hki
    rcases hki.eq_or_lt with hEq | hlt
    · have hi : i = pivot := by
        ext
        simpa [pivot] using hEq.symm
      subst i
      simpa [pivot] using hpivot.symm.le
    · exact habove i hlt
  have hbelow' :
      ∀ i : Fin (m + 2), i.val ≤ k → sampleRate i ≤ shiftedRate i := by
    intro i hik
    rcases hik.eq_or_lt with hEq | hlt
    · have hi : i = pivot := by
        ext
        simpa [pivot] using hEq
      subst i
      simpa [pivot] using hpivot.le
    · exact hbelow i hlt
  by_contra hnot
  have hpivot_lt : levels pivot < shiftedLevels pivot := by
    simpa [pivot] using lt_of_not_ge hnot
  rcases le_or_gt r shiftedR with hr_le | hshiftedR_lt
  · -- Follow the source proof backward from the equal top endpoint.
    let crossed : ℕ → Bool := fun n =>
      if hn : n < m + 2 then
        decide (shiftedLevels ⟨n, hn⟩ ≤ levels ⟨n, hn⟩)
      else true
    have hcrossed_pivot : crossed k = false := by
      have hklt : k < m + 2 := by omega
      have hpivot_lt' :
          levels ⟨k, hklt⟩ < shiftedLevels ⟨k, hklt⟩ := by
        simpa [pivot] using hpivot_lt
      simp [crossed, hklt, not_le_of_gt hpivot_lt']
    have hcrossed_top : crossed (m + 1) = true := by
      have htop : m + 1 < m + 2 := by omega
      simp [crossed, htop, hlevels.2.1, hshiftedLevels.2.1]
    obtain ⟨s, hks, hs_top, hs_prev, hs_now⟩ :=
      AppliedModelingLib.FiniteSum.exists_bool_transition crossed
        (lo := k) (hi := m + 1) (by omega)
        hcrossed_pivot hcrossed_top
    have hs_pos : 0 < s := hk0.trans hks
    have hs_le_m1 : s ≤ m + 1 := hs_top
    have hprev_lt_m2 : s - 1 < m + 2 := by omega
    have hs_lt_m2 : s < m + 2 := by omega
    have hlow_lt_raw :
        levels ⟨s - 1, hprev_lt_m2⟩ <
          shiftedLevels ⟨s - 1, hprev_lt_m2⟩ := by
      have hnot_le :
          ¬ shiftedLevels ⟨s - 1, hprev_lt_m2⟩ ≤
            levels ⟨s - 1, hprev_lt_m2⟩ := by
        simpa [crossed, hprev_lt_m2] using hs_prev
      exact lt_of_not_ge hnot_le
    have hhigh_ge_raw :
        shiftedLevels ⟨s, hs_lt_m2⟩ ≤ levels ⟨s, hs_lt_m2⟩ := by
      simpa [crossed, hs_lt_m2] using hs_now
    let j : Fin (m + 1) := ⟨s - 1, by omega⟩
    have hj_ge_k : k ≤ j.val := by
      dsimp [j]
      omega
    have hj_ne_zero : j.val ≠ 0 := by omega
    have hlow_lt :
        levels (adjacentLowIndex j) < shiftedLevels (adjacentLowIndex j) := by
      simpa [j, adjacentLowIndex] using hlow_lt_raw
    have hhigh_ge :
        shiftedLevels (adjacentHighIndex j) ≤ levels (adjacentHighIndex j) := by
      have hs_pred : s - 1 + 1 = s := Nat.sub_add_cancel hs_pos
      simpa [j, adjacentHighIndex, hs_pred] using hhigh_ge_raw
    have hrate_lt :
        binaryEndpointAwareAdjacentRate shiftedLevels shiftedRate j <
          binaryEndpointAwareAdjacentRate levels sampleRate j := by
      by_cases hj_last : j.val = m
      · have hweights :
            shiftedRate (adjacentLowIndex j) ≤
              sampleRate (adjacentLowIndex j) :=
          habove' (adjacentLowIndex j) (by
            simpa [adjacentLowIndex] using hj_ge_k)
        have hshifted_low_pos :
            0 < shiftedLevels (adjacentLowIndex j) :=
          BinaryEndpointLevelVector_pos_of_not_first hshiftedLevels
            (adjacentLowIndex j) (by
              simpa [adjacentLowIndex] using hj_ne_zero)
        have hlevels_low_pos :
            0 < levels (adjacentLowIndex j) :=
          BinaryEndpointLevelVector_pos_of_not_first hlevels
            (adjacentLowIndex j) (by
              simpa [adjacentLowIndex] using hj_ne_zero)
        have hlog_nonneg :
            0 ≤ -Real.log (shiftedLevels (adjacentLowIndex j)) := by
          have hle_one :=
            BinaryEndpointLevelVector_le_one hshiftedLevels
              (adjacentLowIndex j)
          exact neg_nonneg.mpr
            (Real.log_nonpos hshifted_low_pos.le hle_one)
        have hweight_le :
            shiftedRate (adjacentLowIndex j) *
                (-Real.log (shiftedLevels (adjacentLowIndex j))) ≤
              sampleRate (adjacentLowIndex j) *
                (-Real.log (shiftedLevels (adjacentLowIndex j))) :=
          mul_le_mul_of_nonneg_right hweights hlog_nonneg
        have hendpoint_lt :
            sampleRate (adjacentLowIndex j) *
                (-Real.log (shiftedLevels (adjacentLowIndex j))) <
              sampleRate (adjacentLowIndex j) *
                (-Real.log (levels (adjacentLowIndex j))) :=
          binaryEndpointLastRate_strictAntiOn
            (hsample_pos (adjacentLowIndex j))
            hlevels_low_pos hshifted_low_pos hlow_lt
        rw [binaryEndpointAwareAdjacentRate_last shiftedLevels shiftedRate j
              hj_ne_zero hj_last,
          binaryEndpointAwareAdjacentRate_last levels sampleRate j
              hj_ne_zero hj_last]
        exact hweight_le.trans_lt hendpoint_lt
      · rw [binaryEndpointAwareAdjacentRate_interior shiftedLevels shiftedRate j
              hj_ne_zero hj_last,
          binaryEndpointAwareAdjacentRate_interior levels sampleRate j
              hj_ne_zero hj_last]
        have hlow_weight :
            shiftedRate (adjacentLowIndex j) ≤
              sampleRate (adjacentLowIndex j) :=
          habove' (adjacentLowIndex j) (by
            simpa [adjacentLowIndex] using hj_ge_k)
        have hhigh_weight :
            shiftedRate (adjacentHighIndex j) ≤
              sampleRate (adjacentHighIndex j) :=
          habove' (adjacentHighIndex j) (by
            simp [adjacentHighIndex]
            omega)
        have hpLo0 : 0 < levels (adjacentLowIndex j) :=
          BinaryEndpointLevelVector_pos_of_not_first hlevels
            (adjacentLowIndex j) (by
              simpa [adjacentLowIndex] using hj_ne_zero)
        have hpHi1 : levels (adjacentHighIndex j) < 1 :=
          BinaryEndpointLevelVector_lt_one_of_not_last hlevels
            (adjacentHighIndex j) (by
              simp [adjacentHighIndex]
              omega)
        have hweight_compare :
            weightedBernoulliClosedThresholdRate
                (shiftedRate (adjacentHighIndex j))
                (shiftedRate (adjacentLowIndex j))
                (shiftedLevels (adjacentHighIndex j))
                (shiftedLevels (adjacentLowIndex j)) ≤
              weightedBernoulliClosedThresholdRate
                (sampleRate (adjacentHighIndex j))
                (sampleRate (adjacentLowIndex j))
                (shiftedLevels (adjacentHighIndex j))
                (shiftedLevels (adjacentLowIndex j)) :=
          weightedBernoulliClosedThresholdRate_le_of_weights_le
            (hshifted_pos (adjacentHighIndex j))
            (hshifted_pos (adjacentLowIndex j))
            (hsample_pos (adjacentHighIndex j))
            (hsample_pos (adjacentLowIndex j))
            hhigh_weight hlow_weight
            (BinaryEndpointLevelVector_pos_of_not_first hshiftedLevels
              (adjacentHighIndex j) (by simp [adjacentHighIndex]))
            (BinaryEndpointLevelVector_lt_one_of_not_last hshiftedLevels
              (adjacentHighIndex j) (by
                simp [adjacentHighIndex]
                omega))
            (BinaryEndpointLevelVector_pos_of_not_first hshiftedLevels
              (adjacentLowIndex j) (by
                simpa [adjacentLowIndex] using hj_ne_zero))
            (BinaryEndpointLevelVector_lt_one_of_not_last hshiftedLevels
              (adjacentLowIndex j) (by
                simp [adjacentLowIndex]
                omega))
        exact hweight_compare.trans_lt
          (weightedBernoulliClosedThresholdRate_lt_of_shrink_lo_lt
            (hsample_pos (adjacentHighIndex j))
            (hsample_pos (adjacentLowIndex j)) hpLo0 hlow_lt
            (BinaryEndpointLevelVector_adjacent_ordered hshiftedLevels j)
            hhigh_ge hpHi1)
    have : shiftedR < r := by
      calc
        shiftedR =
            binaryEndpointAwareAdjacentRate shiftedLevels shiftedRate j :=
          (hshiftedR j).symm
        _ < binaryEndpointAwareAdjacentRate levels sampleRate j := hrate_lt
        _ = r := hr j
    exact (not_lt_of_ge hr_le) this
  · -- Follow the source proof forward from the common bottom endpoint.
    let crossed : ℕ → Bool := fun n =>
      if hn : n < m + 2 then
        decide (levels ⟨n, hn⟩ < shiftedLevels ⟨n, hn⟩)
      else false
    have hcrossed_zero : crossed 0 = false := by
      have hzero_ge : shiftedLevels (0 : Fin (m + 2)) ≤ levels 0 := by
        change shiftedLevels firstLevelIndex ≤ levels firstLevelIndex
        rw [hshiftedLevels.1, hlevels.1]
      simp [crossed, not_lt_of_ge hzero_ge]
    have hcrossed_pivot : crossed k = true := by
      have hklt : k < m + 2 := by omega
      have hpivot_lt' :
          levels ⟨k, hklt⟩ < shiftedLevels ⟨k, hklt⟩ := by
        simpa [pivot] using hpivot_lt
      simp [crossed, hklt, hpivot_lt']
    obtain ⟨s, hs_pos, hs_le_k, hs_prev, hs_now⟩ :=
      AppliedModelingLib.FiniteSum.exists_bool_transition crossed
        (lo := 0) (hi := k) hk0 hcrossed_zero hcrossed_pivot
    have hs_le_m1 : s ≤ m + 1 := hs_le_k.trans hkm.le
    have hprev_lt_m2 : s - 1 < m + 2 := by omega
    have hs_lt_m2 : s < m + 2 := by omega
    have hlow_ge_raw :
        shiftedLevels ⟨s - 1, hprev_lt_m2⟩ ≤
          levels ⟨s - 1, hprev_lt_m2⟩ := by
      have hnot_lt :
          ¬ levels ⟨s - 1, hprev_lt_m2⟩ <
            shiftedLevels ⟨s - 1, hprev_lt_m2⟩ := by
        simpa [crossed, hprev_lt_m2] using hs_prev
      exact le_of_not_gt hnot_lt
    have hhigh_lt_raw :
        levels ⟨s, hs_lt_m2⟩ < shiftedLevels ⟨s, hs_lt_m2⟩ := by
      simpa [crossed, hs_lt_m2] using hs_now
    let j : Fin (m + 1) := ⟨s - 1, by omega⟩
    have hj_lt_k : j.val < k := by
      dsimp [j]
      omega
    have hj_ne_last : j.val ≠ m := by omega
    have hlow_ge :
        shiftedLevels (adjacentLowIndex j) ≤ levels (adjacentLowIndex j) := by
      simpa [j, adjacentLowIndex] using hlow_ge_raw
    have hhigh_lt :
        levels (adjacentHighIndex j) < shiftedLevels (adjacentHighIndex j) := by
      have hs_pred : s - 1 + 1 = s := Nat.sub_add_cancel hs_pos
      simpa [j, adjacentHighIndex, hs_pred] using hhigh_lt_raw
    have hrate_lt :
        binaryEndpointAwareAdjacentRate levels sampleRate j <
          binaryEndpointAwareAdjacentRate shiftedLevels shiftedRate j := by
      by_cases hj_first : j.val = 0
      · have hweights :
            sampleRate (adjacentHighIndex j) ≤
              shiftedRate (adjacentHighIndex j) :=
          hbelow' (adjacentHighIndex j) (by
            simp [adjacentHighIndex]
            omega)
        have hlog_nonneg :
            0 ≤ -Real.log (1 - levels (adjacentHighIndex j)) := by
          have hpos :=
            BinaryEndpointLevelVector_pos_of_not_first hlevels
              (adjacentHighIndex j) (by simp [adjacentHighIndex])
          have hle :=
            BinaryEndpointLevelVector_le_one hlevels (adjacentHighIndex j)
          exact neg_nonneg.mpr
            (Real.log_nonpos (by linarith) (by linarith))
        have hweight_le :
            sampleRate (adjacentHighIndex j) *
                (-Real.log (1 - levels (adjacentHighIndex j))) ≤
              shiftedRate (adjacentHighIndex j) *
                (-Real.log (1 - levels (adjacentHighIndex j))) :=
          mul_le_mul_of_nonneg_right hweights hlog_nonneg
        have hendpoint_lt :
            shiftedRate (adjacentHighIndex j) *
                (-Real.log (1 - levels (adjacentHighIndex j))) <
              shiftedRate (adjacentHighIndex j) *
                (-Real.log (1 - shiftedLevels (adjacentHighIndex j))) :=
          binaryEndpointFirstRate_strictMonoOn
            (hshifted_pos (adjacentHighIndex j))
            (BinaryEndpointLevelVector_lt_one_of_not_last hlevels
              (adjacentHighIndex j) (by
                simp [adjacentHighIndex]
                omega))
            (BinaryEndpointLevelVector_lt_one_of_not_last hshiftedLevels
              (adjacentHighIndex j) (by
                simp [adjacentHighIndex]
                omega))
            hhigh_lt
        rw [binaryEndpointAwareAdjacentRate_first levels sampleRate j hj_first,
          binaryEndpointAwareAdjacentRate_first shiftedLevels shiftedRate j
            hj_first]
        exact hweight_le.trans_lt hendpoint_lt
      · rw [binaryEndpointAwareAdjacentRate_interior levels sampleRate j
              hj_first hj_ne_last,
          binaryEndpointAwareAdjacentRate_interior shiftedLevels shiftedRate j
              hj_first hj_ne_last]
        have hlow_weight :
            sampleRate (adjacentLowIndex j) ≤
              shiftedRate (adjacentLowIndex j) :=
          hbelow' (adjacentLowIndex j) (by
            simpa [adjacentLowIndex] using hj_lt_k.le)
        have hhigh_weight :
            sampleRate (adjacentHighIndex j) ≤
              shiftedRate (adjacentHighIndex j) :=
          hbelow' (adjacentHighIndex j) (by
            simp [adjacentHighIndex]
            omega)
        have hpLo0 : 0 < shiftedLevels (adjacentLowIndex j) :=
          BinaryEndpointLevelVector_pos_of_not_first hshiftedLevels
            (adjacentLowIndex j) (by
              simpa [adjacentLowIndex] using hj_first)
        have hpHi1 : shiftedLevels (adjacentHighIndex j) < 1 :=
          BinaryEndpointLevelVector_lt_one_of_not_last hshiftedLevels
            (adjacentHighIndex j) (by
              simp [adjacentHighIndex]
              omega)
        have hweight_compare :
            weightedBernoulliClosedThresholdRate
                (sampleRate (adjacentHighIndex j))
                (sampleRate (adjacentLowIndex j))
                (levels (adjacentHighIndex j))
                (levels (adjacentLowIndex j)) ≤
              weightedBernoulliClosedThresholdRate
                (shiftedRate (adjacentHighIndex j))
                (shiftedRate (adjacentLowIndex j))
                (levels (adjacentHighIndex j))
                (levels (adjacentLowIndex j)) :=
          weightedBernoulliClosedThresholdRate_le_of_weights_le
            (hsample_pos (adjacentHighIndex j))
            (hsample_pos (adjacentLowIndex j))
            (hshifted_pos (adjacentHighIndex j))
            (hshifted_pos (adjacentLowIndex j))
            hhigh_weight hlow_weight
            (BinaryEndpointLevelVector_pos_of_not_first hlevels
              (adjacentHighIndex j) (by simp [adjacentHighIndex]))
            (BinaryEndpointLevelVector_lt_one_of_not_last hlevels
              (adjacentHighIndex j) (by
                simp [adjacentHighIndex]
                omega))
            (BinaryEndpointLevelVector_pos_of_not_first hlevels
              (adjacentLowIndex j) (by
                simpa [adjacentLowIndex] using hj_first))
            (BinaryEndpointLevelVector_lt_one_of_not_last hlevels
              (adjacentLowIndex j) (by
                simp [adjacentLowIndex]
                omega))
        exact hweight_compare.trans_lt
          (weightedBernoulliClosedThresholdRate_lt_of_shrink_hi_lt
            (hshifted_pos (adjacentHighIndex j))
            (hshifted_pos (adjacentLowIndex j)) hpLo0 hlow_ge
            (BinaryEndpointLevelVector_adjacent_ordered hlevels j)
            hhigh_lt hpHi1)
    have : r < shiftedR := by
      calc
        r = binaryEndpointAwareAdjacentRate levels sampleRate j := (hr j).symm
        _ < binaryEndpointAwareAdjacentRate shiftedLevels shiftedRate j := hrate_lt
        _ = shiftedR := hshiftedR j
    exact (not_lt_of_ge hshiftedR_lt.le) this

end

end GJ19OptimalBinaryRatingSystems
