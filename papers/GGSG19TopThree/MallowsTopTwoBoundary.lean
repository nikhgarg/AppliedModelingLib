import GGSG19TopThree.MallowsApproval
import GGSG19TopThree.MallowsBoundary

/-!
# Mallows Top-Two Boundary Rate

Boundary-minimizer theorem for two-approval under a finite Mallows law.  The
rank-kernel algebra lives in `MallowsApproval` and `RankPower`; this file only
connects those inequalities to the generic `TopWSelectionPair` reducer.
-/

namespace GGSG19TopThree

noncomputable section

open AppliedModelingLib.SocialChoice.Ranking

private theorem mallowsTopWTwoApprovalPairUpProb_boundary_le_pair {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization)
    (W : Candidate n) (hW : 0 < W.val) (hq_le : M.q ≤ 1)
    (pair : TopWSelectionPair M.center W) :
    mallowsTopWKApprovalPairUpProb M W 2
        (topWBoundaryPair M.center W hW) ≤
      mallowsTopWKApprovalPairUpProb M W 2 pair := by
  let boundary := topWBoundaryPair M.center W hW
  have hscale_nonneg :
      0 ≤ (1 + M.q) * fac.firstSecondTail := by
    exact mul_nonneg (by linarith [M.q_pos])
      (le_of_lt fac.firstSecondTail_pos)
  have hpair_hi_le_boundary_hi :
      rankOf M.center pair.hi ≤ rankOf M.center boundary.hi := by
    exact topWBoundaryPair_pair_hi_rank_le_boundary_hi M.center W hW pair
  have hboundary_lo_le_pair_lo :
      rankOf M.center boundary.lo ≤ rankOf M.center pair.lo := by
    exact topWBoundaryPair_boundary_lo_rank_le_pair_lo M.center W hW pair
  have hpair_hi_lt_boundary_lo :
      rankOf M.center pair.hi < rankOf M.center boundary.lo := by
    rw [topWBoundaryPair_rank_lo]
    exact pair.rank_hi_lt_cut
  have hkernel_first :
      candidateRankTopTwoPairKernel n M.q
          (rankOf M.center boundary.hi) (rankOf M.center boundary.lo) ≤
        candidateRankTopTwoPairKernel n M.q
          (rankOf M.center pair.hi) (rankOf M.center boundary.lo) := by
    exact candidateRankTopTwoPairKernel_le_of_first_le n M.q_pos.le hq_le
      hpair_hi_le_boundary_hi
      (ne_of_gt hpair_hi_lt_boundary_lo)
      (ne_of_gt boundary.rank_hi_lt_rank_lo)
  have hkernel_excluded :
      candidateRankTopTwoPairKernel n M.q
          (rankOf M.center pair.hi) (rankOf M.center boundary.lo) ≤
        candidateRankTopTwoPairKernel n M.q
          (rankOf M.center pair.hi) (rankOf M.center pair.lo) := by
    exact candidateRankTopTwoPairKernel_le_of_excluded_le n M.q_pos.le hq_le
      hboundary_lo_le_pair_lo
      (ne_of_lt hpair_hi_lt_boundary_lo)
      (ne_of_lt pair.rank_hi_lt_rank_lo)
  unfold mallowsTopWKApprovalPairUpProb
  rw [kApprovalPairUpProb_two_eq_mallows_rank_kernel_div_partition
      M fac boundary.hi_ne_lo,
    kApprovalPairUpProb_two_eq_mallows_rank_kernel_div_partition
      M fac pair.hi_ne_lo]
  refine div_le_div_of_nonneg_right ?_ (le_of_lt M.partition_pos)
  exact mul_le_mul_of_nonneg_left
    (le_trans hkernel_first hkernel_excluded) hscale_nonneg

private theorem mallowsTopWTwoApprovalPairDownProb_pair_le_boundary {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization)
    (W : Candidate n) (hW : 0 < W.val) (hq_le : M.q ≤ 1)
    (pair : TopWSelectionPair M.center W) :
    mallowsTopWKApprovalPairDownProb M W 2 pair ≤
      mallowsTopWKApprovalPairDownProb M W 2
        (topWBoundaryPair M.center W hW) := by
  let boundary := topWBoundaryPair M.center W hW
  have hscale_nonneg :
      0 ≤ (1 + M.q) * fac.firstSecondTail := by
    exact mul_nonneg (by linarith [M.q_pos])
      (le_of_lt fac.firstSecondTail_pos)
  have hboundary_lo_le_pair_lo :
      rankOf M.center boundary.lo ≤ rankOf M.center pair.lo := by
    exact topWBoundaryPair_boundary_lo_rank_le_pair_lo M.center W hW pair
  have hpair_hi_le_boundary_hi :
      rankOf M.center pair.hi ≤ rankOf M.center boundary.hi := by
    exact topWBoundaryPair_pair_hi_rank_le_boundary_hi M.center W hW pair
  have hpair_hi_lt_boundary_lo :
      rankOf M.center pair.hi < rankOf M.center boundary.lo := by
    rw [topWBoundaryPair_rank_lo]
    exact pair.rank_hi_lt_cut
  have hkernel_first :
      candidateRankTopTwoPairKernel n M.q
          (rankOf M.center pair.lo) (rankOf M.center pair.hi) ≤
        candidateRankTopTwoPairKernel n M.q
          (rankOf M.center boundary.lo) (rankOf M.center pair.hi) := by
    exact candidateRankTopTwoPairKernel_le_of_first_le n M.q_pos.le hq_le
      hboundary_lo_le_pair_lo
      (ne_of_lt hpair_hi_lt_boundary_lo)
      (ne_of_lt pair.rank_hi_lt_rank_lo)
  have hkernel_excluded :
      candidateRankTopTwoPairKernel n M.q
          (rankOf M.center boundary.lo) (rankOf M.center pair.hi) ≤
        candidateRankTopTwoPairKernel n M.q
          (rankOf M.center boundary.lo) (rankOf M.center boundary.hi) := by
    exact candidateRankTopTwoPairKernel_le_of_excluded_le n M.q_pos.le hq_le
      hpair_hi_le_boundary_hi
      (ne_of_gt hpair_hi_lt_boundary_lo)
      (ne_of_gt boundary.rank_hi_lt_rank_lo)
  unfold mallowsTopWKApprovalPairDownProb
  rw [kApprovalPairDownProb_two_eq_mallows_rank_kernel_div_partition
      M fac pair.hi_ne_lo,
    kApprovalPairDownProb_two_eq_mallows_rank_kernel_div_partition
      M fac boundary.hi_ne_lo]
  refine div_le_div_of_nonneg_right ?_ (le_of_lt M.partition_pos)
  exact mul_le_mul_of_nonneg_left
    (le_trans hkernel_first hkernel_excluded) hscale_nonneg

theorem mallowsTopWTwoApprovalOutcomeRate_eq_boundary {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization) (hn : 0 < n)
    (W : Candidate n) (hW : 0 < W.val) (hq_lt : M.q < 1) :
    mallowsTopWKApprovalOutcomeRate M W hW 2 =
      mallowsTopWKApprovalPairRate M W 2
        (topWBoundaryPair M.center W hW) := by
  have hq_le : M.q ≤ 1 := le_of_lt hq_lt
  refine
    mallowsTopWKApprovalOutcomeRate_eq_boundary_of_pair_prob_monotone
      M W hW 2 ?hbase_pos ?hdown_le_up ?hup_le ?hdown_ge
  · intro pair
    exact approvalPairwiseBase_pos_of_pos_sum_le
      (by
        unfold mallowsTopWKApprovalPairUpProb
        exact kApprovalPairUpProb_two_pos M fac hn pair.hi_ne_lo)
      (by
        unfold mallowsTopWKApprovalPairDownProb
        exact kApprovalPairDownProb_two_pos M fac hn pair.hi_ne_lo)
      (by
        unfold mallowsTopWKApprovalPairUpProb mallowsTopWKApprovalPairDownProb
        exact kApprovalPairUpProb_add_downProb_le_one
          M.law 2 pair.hi pair.lo)
  · intro pair
    unfold mallowsTopWKApprovalPairUpProb mallowsTopWKApprovalPairDownProb
    exact kApprovalPairDownProb_two_le_up_of_rank_le M fac hq_le
      pair.hi_ne_lo (le_of_lt pair.rank_hi_lt_rank_lo)
  · intro pair
    exact mallowsTopWTwoApprovalPairUpProb_boundary_le_pair
      M fac W hW hq_le pair
  · intro pair
    exact mallowsTopWTwoApprovalPairDownProb_pair_le_boundary
      M fac W hW hq_le pair

end

end GGSG19TopThree
