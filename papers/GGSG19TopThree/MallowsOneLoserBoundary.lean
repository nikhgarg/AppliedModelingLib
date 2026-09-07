import GGSG19TopThree.MallowsBoundary
import GGSG19TopThree.MallowsOneLoser

/-!
# Mallows One-Loser Boundary Rate

High-level boundary-minimizer theorem for all-but-one approval.  The
probability calculation lives in `MallowsOneLoser`; this file only connects
that calculation to the generic `TopWSelectionPair` boundary reducer.
-/

namespace GGSG19TopThree

noncomputable section

open AppliedModelingLib.SocialChoice.Ranking

private theorem topWSelectionPair_lo_rank_eq_oneLoserLastRank {n : ℕ}
    {ρ : Ranking n} (pair : TopWSelectionPair ρ (oneLoserLastRank n)) :
    rankOf ρ pair.lo = oneLoserLastRank n := by
  apply le_antisymm
  · change (rankOf ρ pair.lo).val ≤ (oneLoserLastRank n).val
    have hlt : (rankOf ρ pair.lo).val < n + 2 := (rankOf ρ pair.lo).isLt
    simp [oneLoserLastRank]
    omega
  · exact pair.cut_le_rank_lo

private theorem topWBoundaryPair_oneLoser_lo_rank {n : ℕ}
    (ρ : Ranking n) :
    rankOf ρ
        (topWBoundaryPair ρ (oneLoserLastRank n)
          (oneLoserLastRank_pos n)).lo =
      oneLoserLastRank n := by
  simp [topWBoundaryPair, TopWSelectionPair.lo, rankOf]

private theorem topWBoundaryPair_oneLoser_hi_rank_val {n : ℕ}
    (ρ : Ranking n) :
    (rankOf ρ
        (topWBoundaryPair ρ (oneLoserLastRank n)
          (oneLoserLastRank_pos n)).hi).val = n := by
  simp [topWBoundaryPair, TopWSelectionPair.hi, rankOf, oneLoserLastRank]

theorem mallowsTopWOneLoserApprovalOutcomeRate_eq_boundary {n : ℕ}
    (M : MallowsSpec n) (hq_lt : M.q < 1) :
    mallowsTopWKApprovalOutcomeRate M (oneLoserLastRank n)
        (oneLoserLastRank_pos n) (n + 1) =
      mallowsTopWKApprovalPairRate M (oneLoserLastRank n) (n + 1)
        (topWBoundaryPair M.center (oneLoserLastRank n)
          (oneLoserLastRank_pos n)) := by
  let boundary :=
    topWBoundaryPair M.center (oneLoserLastRank n)
      (oneLoserLastRank_pos n)
  have hq_le : M.q ≤ 1 := le_of_lt hq_lt
  refine
    mallowsTopWKApprovalOutcomeRate_eq_boundary_of_pair_prob_monotone
      M (oneLoserLastRank n) (oneLoserLastRank_pos n) (n + 1)
      ?hbase_pos ?hdown_le_up ?hup_le ?hdown_ge
  · intro pair
    have hup :
        mallowsTopWKApprovalPairUpProb M (oneLoserLastRank n) (n + 1) pair =
          mallowsOneLoserLastRankProb M pair.lo := by
      unfold mallowsTopWKApprovalPairUpProb
      exact kApprovalPairUpProb_oneLoser_eq_mallowsLastRankProb
        M pair.hi_ne_lo
    have hdown :
        mallowsTopWKApprovalPairDownProb M (oneLoserLastRank n) (n + 1) pair =
          mallowsOneLoserLastRankProb M pair.hi := by
      unfold mallowsTopWKApprovalPairDownProb
      exact kApprovalPairDownProb_oneLoser_eq_mallowsLastRankProb
        M pair.hi_ne_lo
    rw [hup, hdown]
    exact approvalPairwiseBase_pos_of_pos_sum_le
      (mallowsOneLoserLastRankProb_pos M pair.lo)
      (mallowsOneLoserLastRankProb_pos M pair.hi)
      (by
        simpa [add_comm] using
          mallowsOneLoserLastRankProb_add_le_one M pair.hi_ne_lo)
  · intro pair
    have hup :
        mallowsTopWKApprovalPairUpProb M (oneLoserLastRank n) (n + 1) pair =
          mallowsOneLoserLastRankProb M pair.lo := by
      unfold mallowsTopWKApprovalPairUpProb
      exact kApprovalPairUpProb_oneLoser_eq_mallowsLastRankProb
        M pair.hi_ne_lo
    have hdown :
        mallowsTopWKApprovalPairDownProb M (oneLoserLastRank n) (n + 1) pair =
          mallowsOneLoserLastRankProb M pair.hi := by
      unfold mallowsTopWKApprovalPairDownProb
      exact kApprovalPairDownProb_oneLoser_eq_mallowsLastRankProb
        M pair.hi_ne_lo
    rw [hdown, hup]
    exact mallowsOneLoserLastRankProb_le_of_rank_le M hq_le
      (le_of_lt pair.rank_hi_lt_rank_lo)
  · intro pair
    have hboundary_up :
        mallowsTopWKApprovalPairUpProb M (oneLoserLastRank n) (n + 1) boundary =
          mallowsOneLoserLastRankProb M boundary.lo := by
      unfold mallowsTopWKApprovalPairUpProb
      exact kApprovalPairUpProb_oneLoser_eq_mallowsLastRankProb
        M boundary.hi_ne_lo
    have hpair_up :
        mallowsTopWKApprovalPairUpProb M (oneLoserLastRank n) (n + 1) pair =
          mallowsOneLoserLastRankProb M pair.lo := by
      unfold mallowsTopWKApprovalPairUpProb
      exact kApprovalPairUpProb_oneLoser_eq_mallowsLastRankProb
        M pair.hi_ne_lo
    rw [hboundary_up, hpair_up]
    have hrank :
        rankOf M.center boundary.lo ≤ rankOf M.center pair.lo := by
      rw [topWBoundaryPair_oneLoser_lo_rank]
      exact pair.cut_le_rank_lo
    exact mallowsOneLoserLastRankProb_le_of_rank_le M hq_le hrank
  · intro pair
    have hpair_down :
        mallowsTopWKApprovalPairDownProb M (oneLoserLastRank n) (n + 1) pair =
          mallowsOneLoserLastRankProb M pair.hi := by
      unfold mallowsTopWKApprovalPairDownProb
      exact kApprovalPairDownProb_oneLoser_eq_mallowsLastRankProb
        M pair.hi_ne_lo
    have hboundary_down :
        mallowsTopWKApprovalPairDownProb M (oneLoserLastRank n) (n + 1)
            boundary =
          mallowsOneLoserLastRankProb M boundary.hi := by
      unfold mallowsTopWKApprovalPairDownProb
      exact kApprovalPairDownProb_oneLoser_eq_mallowsLastRankProb
        M boundary.hi_ne_lo
    rw [hpair_down, hboundary_down]
    have hrank :
        rankOf M.center pair.hi ≤ rankOf M.center boundary.hi := by
      change (rankOf M.center pair.hi).val ≤
        (rankOf M.center boundary.hi).val
      rw [topWBoundaryPair_oneLoser_hi_rank_val]
      have hpair_lt :
          (rankOf M.center pair.hi).val < n + 1 := by
        have hpair_lt_fin := pair.rank_hi_lt_cut
        change (rankOf M.center pair.hi).val <
          (oneLoserLastRank n).val at hpair_lt_fin
        simpa [oneLoserLastRank] using hpair_lt_fin
      omega
    exact mallowsOneLoserLastRankProb_le_of_rank_le M hq_le hrank

end

end GGSG19TopThree
