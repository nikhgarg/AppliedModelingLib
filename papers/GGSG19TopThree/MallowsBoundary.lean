import GGSG19TopThree.MainTheorems
import AppliedModelingLib.Foundations.Probability.Weighted
import AppliedModelingLib.SocialChoice.Ranking.MallowsRankFactorization

/-!
# Mallows Boundary Pairs

Paper-local Mallows boundary-pair lemmas for W-selection.  This file starts
with the tractable `K = 1` case: one-approval pair probabilities are
first-choice probabilities, and Mallows first-choice masses are normalized
geometric rank powers.
-/

open scoped BigOperators

namespace GGSG19TopThree

noncomputable section

open AppliedModelingLib.Probability
open AppliedModelingLib.SocialChoice.Ranking

/-- Cross-tier ordered pairs for selecting the center top `W` candidates. -/
def TopWSelectionPair {n : ℕ}
    (ρ : Ranking n) (W : Candidate n) : Type :=
  { pair : Candidate n × Candidate n //
    rankOf ρ pair.1 < W ∧ W ≤ rankOf ρ pair.2 }

namespace TopWSelectionPair

variable {n : ℕ} {ρ : Ranking n} {W : Candidate n}

/-- Higher-tier candidate in a W-selection pair. -/
def hi (pair : TopWSelectionPair ρ W) : Candidate n := pair.1.1

/-- Lower-tier candidate in a W-selection pair. -/
def lo (pair : TopWSelectionPair ρ W) : Candidate n := pair.1.2

theorem rank_hi_lt_cut (pair : TopWSelectionPair ρ W) :
    rankOf ρ pair.hi < W := pair.2.1

theorem cut_le_rank_lo (pair : TopWSelectionPair ρ W) :
    W ≤ rankOf ρ pair.lo := pair.2.2

theorem rank_hi_lt_rank_lo (pair : TopWSelectionPair ρ W) :
    rankOf ρ pair.hi < rankOf ρ pair.lo :=
  lt_of_lt_of_le pair.rank_hi_lt_cut pair.cut_le_rank_lo

theorem hi_ne_lo (pair : TopWSelectionPair ρ W) :
    pair.hi ≠ pair.lo := by
  intro h
  have hlt : rankOf ρ pair.hi < rankOf ρ pair.hi := by
    simpa [h] using pair.rank_hi_lt_rank_lo
  exact (lt_irrefl _) hlt

instance instFintype : Fintype (TopWSelectionPair ρ W) := by
  unfold TopWSelectionPair
  infer_instance

end TopWSelectionPair

/-- The adjacent boundary pair `(W, W+1)` in zero-indexed Lean ranks. -/
def topWBoundaryPair {n : ℕ}
    (ρ : Ranking n) (W : Candidate n) (hW : 0 < W.val) :
    TopWSelectionPair ρ W :=
  let pred : Candidate n := ⟨W.val - 1, by
    have hWlt : W.val < n + 2 := W.isLt
    omega⟩
  ⟨(ρ pred, ρ W), by
    constructor
    · have hrank : rankOf ρ (ρ pred) = pred := by
        simp [rankOf]
      rw [hrank]
      change pred.val < W.val
      simp [pred]
      exact hW
    · simp [rankOf]⟩

instance instNonemptyTopWSelectionPair {n : ℕ}
    (ρ : Ranking n) (W : Candidate n) (hW : 0 < W.val) :
    Nonempty (TopWSelectionPair ρ W) :=
  ⟨topWBoundaryPair ρ W hW⟩

theorem topWBoundaryPair_rank_hi_val {n : ℕ}
    (ρ : Ranking n) (W : Candidate n) (hW : 0 < W.val) :
    (rankOf ρ (topWBoundaryPair ρ W hW).hi).val = W.val - 1 := by
  simp [topWBoundaryPair, TopWSelectionPair.hi, rankOf]

theorem topWBoundaryPair_rank_lo {n : ℕ}
    (ρ : Ranking n) (W : Candidate n) (hW : 0 < W.val) :
    rankOf ρ (topWBoundaryPair ρ W hW).lo = W := by
  simp [topWBoundaryPair, TopWSelectionPair.lo, rankOf]

theorem topWBoundaryPair_pair_hi_rank_le_boundary_hi {n : ℕ}
    (ρ : Ranking n) (W : Candidate n) (hW : 0 < W.val)
    (pair : TopWSelectionPair ρ W) :
    rankOf ρ pair.hi ≤ rankOf ρ (topWBoundaryPair ρ W hW).hi := by
  change (rankOf ρ pair.hi).val ≤
    (rankOf ρ (topWBoundaryPair ρ W hW).hi).val
  rw [topWBoundaryPair_rank_hi_val]
  have hpair_lt : (rankOf ρ pair.hi).val < W.val :=
    pair.rank_hi_lt_cut
  omega

theorem topWBoundaryPair_boundary_lo_rank_le_pair_lo {n : ℕ}
    (ρ : Ranking n) (W : Candidate n) (hW : 0 < W.val)
    (pair : TopWSelectionPair ρ W) :
    rankOf ρ (topWBoundaryPair ρ W hW).lo ≤ rankOf ρ pair.lo := by
  rw [topWBoundaryPair_rank_lo]
  exact pair.cut_le_rank_lo

/-- One-approval pairwise learning rate for a Mallows W-selection pair. -/
def mallowsTopWOneApprovalPairRate {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n)
    (pair : TopWSelectionPair M.center W) : ℝ :=
  approvalPairwiseRate
    (firstChoiceProb M.law pair.hi)
    (firstChoiceProb M.law pair.lo)

/-- Finite W-selection learning rate for one-approval under a Mallows law. -/
def mallowsTopWOneApprovalOutcomeRate {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val) : ℝ :=
  @finiteOutcomeLearningRate (TopWSelectionPair M.center W) inferInstance
    (instNonemptyTopWSelectionPair M.center W hW)
    (mallowsTopWOneApprovalPairRate M W)

/-- K-approval up-probability for a Mallows W-selection pair. -/
def mallowsTopWKApprovalPairUpProb {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (K : ℕ)
    (pair : TopWSelectionPair M.center W) : ℝ :=
  kApprovalPairUpProb M.law K pair.hi pair.lo

/-- K-approval down-probability for a Mallows W-selection pair. -/
def mallowsTopWKApprovalPairDownProb {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (K : ℕ)
    (pair : TopWSelectionPair M.center W) : ℝ :=
  kApprovalPairDownProb M.law K pair.hi pair.lo

/-- K-approval pairwise learning rate for a Mallows W-selection pair. -/
def mallowsTopWKApprovalPairRate {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (K : ℕ)
    (pair : TopWSelectionPair M.center W) : ℝ :=
  approvalPairwiseRate
    (mallowsTopWKApprovalPairUpProb M W K pair)
    (mallowsTopWKApprovalPairDownProb M W K pair)

/-- Finite W-selection learning rate for K-approval under a Mallows law. -/
def mallowsTopWKApprovalOutcomeRate {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val) (K : ℕ) : ℝ :=
  @finiteOutcomeLearningRate (TopWSelectionPair M.center W) inferInstance
    (instNonemptyTopWSelectionPair M.center W hW)
    (mallowsTopWKApprovalPairRate M W K)

/--
Generic boundary-pair reduction for K-approval W-selection: if the adjacent
boundary pair has weakly smaller favorable probability and weakly larger
unfavorable probability than every other cross-tier pair, then it realizes the
finite outcome-learning minimum.
-/
theorem mallowsTopWKApprovalOutcomeRate_eq_boundary_of_pair_prob_monotone
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val) (K : ℕ)
    (hbase_pos :
      ∀ pair : TopWSelectionPair M.center W,
        0 < approvalPairwiseBase
          (mallowsTopWKApprovalPairUpProb M W K pair)
          (mallowsTopWKApprovalPairDownProb M W K pair))
    (hdown_le_up :
      ∀ pair : TopWSelectionPair M.center W,
        mallowsTopWKApprovalPairDownProb M W K pair ≤
          mallowsTopWKApprovalPairUpProb M W K pair)
    (hup_le :
      ∀ pair : TopWSelectionPair M.center W,
        mallowsTopWKApprovalPairUpProb M W K
            (topWBoundaryPair M.center W hW) ≤
          mallowsTopWKApprovalPairUpProb M W K pair)
    (hdown_ge :
      ∀ pair : TopWSelectionPair M.center W,
        mallowsTopWKApprovalPairDownProb M W K pair ≤
          mallowsTopWKApprovalPairDownProb M W K
            (topWBoundaryPair M.center W hW)) :
    mallowsTopWKApprovalOutcomeRate M W hW K =
      mallowsTopWKApprovalPairRate M W K (topWBoundaryPair M.center W hW) := by
  unfold mallowsTopWKApprovalOutcomeRate finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le (mallowsTopWKApprovalPairRate M W K)
      (by simp : topWBoundaryPair M.center W hW ∈
        (Finset.univ : Finset (TopWSelectionPair M.center W)))
  · exact Finset.le_inf' _ _ (by
      intro pair _
      unfold mallowsTopWKApprovalPairRate
      exact approvalPairwiseRate_le_of_up_le_down_ge
        (kApprovalPairUpProb_nonneg M.law K _ _)
        (kApprovalPairDownProb_nonneg M.law K _ _)
        (kApprovalPairUpProb_nonneg M.law K _ _)
        (kApprovalPairDownProb_nonneg M.law K _ _)
        (hbase_pos (topWBoundaryPair M.center W hW))
        (hbase_pos pair)
        (hdown_le_up (topWBoundaryPair M.center W hW))
        (hdown_le_up pair)
        (hup_le pair)
        (hdown_ge pair))

theorem mallowsTopWKApprovalPairDownProb_le_up_of_rank_lt {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (K : ℕ)
    (hq_le_one : M.q ≤ 1)
    (pair : TopWSelectionPair M.center W) :
    mallowsTopWKApprovalPairDownProb M W K pair ≤
      mallowsTopWKApprovalPairUpProb M W K pair := by
  simpa [mallowsTopWKApprovalPairUpProb, mallowsTopWKApprovalPairDownProb] using
    M.kApprovalPairDownProb_le_up_of_rank_lt K pair.rank_hi_lt_rank_lo hq_le_one

theorem mallowsTopWKApprovalBoundary_upProb_le_pair {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val) (K : ℕ)
    (hq_le_one : M.q ≤ 1)
    (pair : TopWSelectionPair M.center W) :
    mallowsTopWKApprovalPairUpProb M W K
        (topWBoundaryPair M.center W hW) ≤
      mallowsTopWKApprovalPairUpProb M W K pair := by
  let boundary := topWBoundaryPair M.center W hW
  have hpair_hi_lt_boundary_lo :
      rankOf M.center pair.hi < rankOf M.center boundary.lo := by
    rw [show rankOf M.center boundary.lo = W by
      simpa [boundary] using topWBoundaryPair_rank_lo M.center W hW]
    exact pair.rank_hi_lt_cut
  have hboundary_lo_ne_pair_hi : boundary.lo ≠ pair.hi := by
    intro h
    rw [h] at hpair_hi_lt_boundary_lo
    exact (lt_irrefl _) hpair_hi_lt_boundary_lo
  have hselected :
      kApprovalPairUpProb M.law K boundary.hi boundary.lo ≤
        kApprovalPairUpProb M.law K pair.hi boundary.lo := by
    exact M.kApprovalPairUpProb_le_of_selected_rank_le K
      (topWBoundaryPair_pair_hi_rank_le_boundary_hi M.center W hW pair)
      hboundary_lo_ne_pair_hi
      (Ne.symm boundary.hi_ne_lo)
      hq_le_one
  have hexcluded :
      kApprovalPairUpProb M.law K pair.hi boundary.lo ≤
        kApprovalPairUpProb M.law K pair.hi pair.lo := by
    exact M.kApprovalPairUpProb_le_of_excluded_rank_le K
      (topWBoundaryPair_boundary_lo_rank_le_pair_lo M.center W hW pair)
      (Ne.symm hboundary_lo_ne_pair_hi)
      pair.hi_ne_lo
      hq_le_one
  simpa [mallowsTopWKApprovalPairUpProb, boundary] using
    le_trans hselected hexcluded

theorem mallowsTopWKApprovalPair_downProb_le_boundary {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val) (K : ℕ)
    (hq_le_one : M.q ≤ 1)
    (pair : TopWSelectionPair M.center W) :
    mallowsTopWKApprovalPairDownProb M W K pair ≤
      mallowsTopWKApprovalPairDownProb M W K
        (topWBoundaryPair M.center W hW) := by
  let boundary := topWBoundaryPair M.center W hW
  have hpair_hi_lt_boundary_lo :
      rankOf M.center pair.hi < rankOf M.center boundary.lo := by
    rw [show rankOf M.center boundary.lo = W by
      simpa [boundary] using topWBoundaryPair_rank_lo M.center W hW]
    exact pair.rank_hi_lt_cut
  have hboundary_lo_ne_pair_hi : boundary.lo ≠ pair.hi := by
    intro h
    rw [h] at hpair_hi_lt_boundary_lo
    exact (lt_irrefl _) hpair_hi_lt_boundary_lo
  have hselected :
      kApprovalPairUpProb M.law K pair.lo pair.hi ≤
        kApprovalPairUpProb M.law K boundary.lo pair.hi := by
    exact M.kApprovalPairUpProb_le_of_selected_rank_le K
      (topWBoundaryPair_boundary_lo_rank_le_pair_lo M.center W hW pair)
      (Ne.symm hboundary_lo_ne_pair_hi)
      pair.hi_ne_lo
      hq_le_one
  have hexcluded :
      kApprovalPairUpProb M.law K boundary.lo pair.hi ≤
        kApprovalPairUpProb M.law K boundary.lo boundary.hi := by
    exact M.kApprovalPairUpProb_le_of_excluded_rank_le K
      (topWBoundaryPair_pair_hi_rank_le_boundary_hi M.center W hW pair)
      hboundary_lo_ne_pair_hi
      (Ne.symm boundary.hi_ne_lo)
      hq_le_one
  simpa [mallowsTopWKApprovalPairDownProb, kApprovalPairDownProb_eq_pairUpProb_swap,
    boundary] using le_trans hselected hexcluded

theorem mallowsTopWKApprovalPairUpProb_pos {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (K : ℕ)
    (hK_pos : 0 < K) (hK_lt : K < n + 2)
    (pair : TopWSelectionPair M.center W) :
    0 < mallowsTopWKApprovalPairUpProb M W K pair := by
  simpa [mallowsTopWKApprovalPairUpProb] using
    kApprovalPairUpProb_pos_of_full_support M.law K pair.hi_ne_lo
      hK_pos hK_lt M.law_apply_toReal_pos

theorem mallowsTopWKApprovalPairDownProb_pos {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (K : ℕ)
    (hK_pos : 0 < K) (hK_lt : K < n + 2)
    (pair : TopWSelectionPair M.center W) :
    0 < mallowsTopWKApprovalPairDownProb M W K pair := by
  simpa [mallowsTopWKApprovalPairDownProb] using
    kApprovalPairDownProb_pos_of_full_support M.law K pair.hi_ne_lo
      hK_pos hK_lt M.law_apply_toReal_pos

theorem mallowsTopWKApprovalPairBase_pos {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (K : ℕ)
    (hK_pos : 0 < K) (hK_lt : K < n + 2)
    (pair : TopWSelectionPair M.center W) :
    0 < approvalPairwiseBase
      (mallowsTopWKApprovalPairUpProb M W K pair)
      (mallowsTopWKApprovalPairDownProb M W K pair) := by
  refine approvalPairwiseBase_pos_of_pos_sum_le
    (mallowsTopWKApprovalPairUpProb_pos M W K hK_pos hK_lt pair)
    (mallowsTopWKApprovalPairDownProb_pos M W K hK_pos hK_lt pair)
    ?_
  simpa [mallowsTopWKApprovalPairUpProb, mallowsTopWKApprovalPairDownProb] using
    kApprovalPairUpProb_add_downProb_le_one M.law K pair.hi pair.lo

theorem mallowsTopWKApprovalOutcomeRate_eq_boundary {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val) (K : ℕ)
    (hK_pos : 0 < K) (hK_lt : K < n + 2)
    (hq_lt : M.q < 1) :
    mallowsTopWKApprovalOutcomeRate M W hW K =
      mallowsTopWKApprovalPairRate M W K
        (topWBoundaryPair M.center W hW) := by
  exact mallowsTopWKApprovalOutcomeRate_eq_boundary_of_pair_prob_monotone
    M W hW K
    (fun pair => mallowsTopWKApprovalPairBase_pos M W K hK_pos hK_lt pair)
    (fun pair =>
      mallowsTopWKApprovalPairDownProb_le_up_of_rank_lt
        M W K (le_of_lt hq_lt) pair)
    (fun pair =>
      mallowsTopWKApprovalBoundary_upProb_le_pair
        M W hW K (le_of_lt hq_lt) pair)
    (fun pair =>
      mallowsTopWKApprovalPair_downProb_le_boundary
        M W hW K (le_of_lt hq_lt) pair)

/--
Exact-rate certificate for all cross-tier Top-W K-approval pair errors under a
finite Mallows law.
-/
noncomputable def mallowsTopWKApprovalRateCertificate {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (K : ℕ)
    (hK_pos : 0 < K) (hK_lt : K < n + 2)
    (hq_lt : M.q < 1) :
    FiniteErrorRateCertificate (TopWSelectionPair M.center W) :=
  kApprovalRelevantPairRateCertificate_of_probabilities
    M.law K
    (fun pair : TopWSelectionPair M.center W => pair.hi)
    (fun pair : TopWSelectionPair M.center W => pair.lo)
    (fun pair => by
      simpa [mallowsTopWKApprovalPairUpProb] using
        mallowsTopWKApprovalPairUpProb_pos M W K hK_pos hK_lt pair)
    (fun pair => by
      simpa [mallowsTopWKApprovalPairDownProb] using
        mallowsTopWKApprovalPairDownProb_pos M W K hK_pos hK_lt pair)
    (fun pair => by
      simpa [mallowsTopWKApprovalPairUpProb, mallowsTopWKApprovalPairDownProb] using
        mallowsTopWKApprovalPairDownProb_le_up_of_rank_lt
          M W K (le_of_lt hq_lt) pair)

theorem mallowsTopWKApprovalOutcomeError_hasExponentialRate_eq_boundary
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val) (K : ℕ)
    (hK_pos : 0 < K) (hK_lt : K < n + 2)
    (hq_lt : M.q < 1)
    {pairWeight : TopWSelectionPair M.center W → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((mallowsTopWKApprovalRateCertificate M W K hK_pos hK_lt hq_lt)
        |>.aggregateError pairWeight)
      (mallowsTopWKApprovalPairRate M W K
        (topWBoundaryPair M.center W hW)) := by
  classical
  haveI : Nonempty (TopWSelectionPair M.center W) :=
    instNonemptyTopWSelectionPair M.center W hW
  have hrate :
      HasExponentialRate
        ((mallowsTopWKApprovalRateCertificate M W K hK_pos hK_lt hq_lt)
          |>.aggregateError pairWeight)
        (mallowsTopWKApprovalOutcomeRate M W hW K) := by
    simpa [mallowsTopWKApprovalRateCertificate, mallowsTopWKApprovalOutcomeRate,
      mallowsTopWKApprovalPairRate, mallowsTopWKApprovalPairUpProb,
      mallowsTopWKApprovalPairDownProb] using
      outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_at_finiteOutcomeLearningRate
        M.law K
        (fun pair : TopWSelectionPair M.center W => pair.hi)
        (fun pair : TopWSelectionPair M.center W => pair.lo)
        (fun pair : TopWSelectionPair M.center W =>
          kApprovalPairUpProb M.law K pair.hi pair.lo)
        (fun pair : TopWSelectionPair M.center W =>
          kApprovalPairDownProb M.law K pair.hi pair.lo)
        (fun pair => by
          simpa [mallowsTopWKApprovalPairUpProb] using
            mallowsTopWKApprovalPairUpProb_pos M W K hK_pos hK_lt pair)
        (fun pair => by
          simpa [mallowsTopWKApprovalPairDownProb] using
            mallowsTopWKApprovalPairDownProb_pos M W K hK_pos hK_lt pair)
        (fun pair => by
          simpa [mallowsTopWKApprovalPairUpProb,
            mallowsTopWKApprovalPairDownProb] using
            mallowsTopWKApprovalPairDownProb_le_up_of_rank_lt
              M W K (le_of_lt hq_lt) pair)
        (fun _pair => rfl)
        (fun _pair => rfl)
        hweight hweight_pos
  simpa [mallowsTopWKApprovalOutcomeRate_eq_boundary
    M W hW K hK_pos hK_lt hq_lt] using hrate

/-- Mixed up-probability at a pair for a randomized finite family of K-approval rules. -/
def mallowsTopWRandomizedKApprovalPairUpProb {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (pair : TopWSelectionPair M.center W) : ℝ :=
  ∑ rule : Rule,
    weight rule * mallowsTopWKApprovalPairUpProb M W (K rule) pair

/-- Mixed down-probability at a pair for a randomized finite family of K-approval rules. -/
def mallowsTopWRandomizedKApprovalPairDownProb {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (pair : TopWSelectionPair M.center W) : ℝ :=
  ∑ rule : Rule,
    weight rule * mallowsTopWKApprovalPairDownProb M W (K rule) pair

/-- Mixed K-approval pairwise learning rate under a randomized finite rule family. -/
def mallowsTopWRandomizedKApprovalPairRate {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (pair : TopWSelectionPair M.center W) : ℝ :=
  approvalPairwiseRate
    (mallowsTopWRandomizedKApprovalPairUpProb M W K weight pair)
    (mallowsTopWRandomizedKApprovalPairDownProb M W K weight pair)

/-- Finite W-selection rate for a randomized finite family of K-approval rules. -/
def mallowsTopWRandomizedKApprovalOutcomeRate {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (K : Rule → ℕ) (weight : Rule → ℝ) : ℝ :=
  @finiteOutcomeLearningRate (TopWSelectionPair M.center W) inferInstance
    (instNonemptyTopWSelectionPair M.center W hW)
    (mallowsTopWRandomizedKApprovalPairRate M W K weight)

/--
One-voter law for a randomized K-approval rule: first draw the rule from the
finite weight vector, then draw the ranking from the supplied ranking law.
-/
noncomputable def randomizedKApprovalSamplingLaw {n : ℕ}
    {Rule : Type*} [Fintype Rule] [DecidableEq Rule]
    (law : PMF (Ranking n)) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    PMF (Rule × Ranking n) :=
  let ruleLaw : PMF Rule :=
    AppliedModelingLib.finiteWeightedPMF weight hweight
      (by simpa [hsum] using zero_lt_one)
  ruleLaw.bind (fun rule => law.map (fun ranking => (rule, ranking)))

theorem randomizedKApprovalSamplingLaw_upProb {n : ℕ}
    {Rule : Type*} [Fintype Rule] [DecidableEq Rule]
    (law : PMF (Ranking n)) (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n) :
    AppliedModelingLib.pmfProb
        (randomizedKApprovalSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Ranking n =>
          kApprovalScore (K signal.1) signal.2 hi -
              kApprovalScore (K signal.1) signal.2 lo =
            1) =
      ∑ rule : Rule,
        weight rule * kApprovalPairUpProb law (K rule) hi lo := by
  classical
  unfold randomizedKApprovalSamplingLaw
  rw [AppliedModelingLib.pmfProb_bind]
  have hpoint :
      ∀ rule : Rule,
        AppliedModelingLib.pmfProb
            (law.map (fun ranking => (rule, ranking)))
            (fun signal : Rule × Ranking n =>
              kApprovalScore (K signal.1) signal.2 hi -
                  kApprovalScore (K signal.1) signal.2 lo =
                1) =
          kApprovalPairUpProb law (K rule) hi lo := by
    intro rule
    rw [AppliedModelingLib.pmfProb_map]
    exact (kApprovalPairUpProb_eq_score_gap_one law (K rule) hi lo).symm
  calc
    AppliedModelingLib.pmfExp
        (AppliedModelingLib.finiteWeightedPMF weight hweight
          (by simpa [hsum] using zero_lt_one))
        (fun rule =>
          AppliedModelingLib.pmfProb
            (law.map (fun ranking => (rule, ranking)))
            (fun signal : Rule × Ranking n =>
              kApprovalScore (K signal.1) signal.2 hi -
                  kApprovalScore (K signal.1) signal.2 lo =
                1))
        =
        AppliedModelingLib.pmfExp
          (AppliedModelingLib.finiteWeightedPMF weight hweight
            (by simpa [hsum] using zero_lt_one))
          (fun rule => kApprovalPairUpProb law (K rule) hi lo) := by
          exact
            AppliedModelingLib.pmfExp_congr
              (AppliedModelingLib.finiteWeightedPMF weight hweight
                (by simpa [hsum] using zero_lt_one))
              hpoint
    _ = ∑ rule : Rule,
        weight rule * kApprovalPairUpProb law (K rule) hi lo := by
          unfold AppliedModelingLib.pmfExp
          simp [AppliedModelingLib.finiteWeightedPMF_apply_toReal, hsum]

theorem randomizedKApprovalSamplingLaw_downProb {n : ℕ}
    {Rule : Type*} [Fintype Rule] [DecidableEq Rule]
    (law : PMF (Ranking n)) (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n) :
    AppliedModelingLib.pmfProb
        (randomizedKApprovalSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Ranking n =>
          kApprovalScore (K signal.1) signal.2 hi -
              kApprovalScore (K signal.1) signal.2 lo =
            -1) =
      ∑ rule : Rule,
        weight rule * kApprovalPairDownProb law (K rule) hi lo := by
  classical
  unfold randomizedKApprovalSamplingLaw
  rw [AppliedModelingLib.pmfProb_bind]
  have hpoint :
      ∀ rule : Rule,
        AppliedModelingLib.pmfProb
            (law.map (fun ranking => (rule, ranking)))
            (fun signal : Rule × Ranking n =>
              kApprovalScore (K signal.1) signal.2 hi -
                  kApprovalScore (K signal.1) signal.2 lo =
                -1) =
          kApprovalPairDownProb law (K rule) hi lo := by
    intro rule
    rw [AppliedModelingLib.pmfProb_map]
    exact (kApprovalPairDownProb_eq_score_gap_neg_one law (K rule) hi lo).symm
  calc
    AppliedModelingLib.pmfExp
        (AppliedModelingLib.finiteWeightedPMF weight hweight
          (by simpa [hsum] using zero_lt_one))
        (fun rule =>
          AppliedModelingLib.pmfProb
            (law.map (fun ranking => (rule, ranking)))
            (fun signal : Rule × Ranking n =>
              kApprovalScore (K signal.1) signal.2 hi -
                  kApprovalScore (K signal.1) signal.2 lo =
                -1))
        =
        AppliedModelingLib.pmfExp
          (AppliedModelingLib.finiteWeightedPMF weight hweight
            (by simpa [hsum] using zero_lt_one))
          (fun rule => kApprovalPairDownProb law (K rule) hi lo) := by
          exact
            AppliedModelingLib.pmfExp_congr
              (AppliedModelingLib.finiteWeightedPMF weight hweight
                (by simpa [hsum] using zero_lt_one))
              hpoint
    _ = ∑ rule : Rule,
        weight rule * kApprovalPairDownProb law (K rule) hi lo := by
          unfold AppliedModelingLib.pmfExp
          simp [AppliedModelingLib.finiteWeightedPMF_apply_toReal, hsum]

theorem randomizedKApprovalPairwiseError_exponentialRateCertificate
    {n : ℕ}
    {Rule : Type*} [Fintype Rule] [DecidableEq Rule]
    (law : PMF (Ranking n)) (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hUpProb :
      (∑ rule : Rule, weight rule * kApprovalPairUpProb law (K rule) hi lo) =
        pUp)
    (hDownProb :
      (∑ rule : Rule, weight rule * kApprovalPairDownProb law (K rule) hi lo) =
        pDown) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb
        (randomizedKApprovalSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Ranking n =>
          kApprovalScore (K signal.1) signal.2 hi)
        (fun signal : Rule × Ranking n =>
          kApprovalScore (K signal.1) signal.2 lo))
      (approvalPairwiseRate pUp pDown) := by
  classical
  refine
    approvalPairwiseError_exponentialRateCertificate_of_ternary_scores
      (randomizedKApprovalSamplingLaw law weight hweight hsum)
      (fun signal : Rule × Ranking n =>
        kApprovalScore (K signal.1) signal.2 hi)
      (fun signal : Rule × Ranking n =>
        kApprovalScore (K signal.1) signal.2 lo)
      hUp hDown hle ?_ ?_ ?_
  · intro signal
    exact kApprovalScore_gap_ternary (K signal.1) signal.2 hi lo
  · rw [← hUpProb]
    exact randomizedKApprovalSamplingLaw_upProb
      law K weight hweight hsum hi lo
  · rw [← hDownProb]
    exact randomizedKApprovalSamplingLaw_downProb
      law K weight hweight hsum hi lo

/--
Source-shaped fixed-pair randomized approval theorem: the actual randomized
one-voter law has the exact mixed K-approval pairwise exponent, and some static
K-approval rule weakly beats that mixed exponent for the same ordered pair.
-/
theorem randomizedKApprovalPairwiseError_exactRate_and_exists_static_rate_ge
    {n : ℕ}
    {Rule : Type*} [Fintype Rule] [Nonempty Rule] [DecidableEq Rule]
    (law : PMF (Ranking n)) (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n)
    (hmixedUp_pos :
      0 <
        ∑ rule : Rule,
          weight rule * kApprovalPairUpProb law (K rule) hi lo)
    (hmixedDown_pos :
      0 <
        ∑ rule : Rule,
          weight rule * kApprovalPairDownProb law (K rule) hi lo)
    (hmixedDown_le_up :
      (∑ rule : Rule,
          weight rule * kApprovalPairDownProb law (K rule) hi lo) ≤
        ∑ rule : Rule,
          weight rule * kApprovalPairUpProb law (K rule) hi lo)
    (hbase_pos :
      ∀ rule,
        0 <
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) hi lo)
            (kApprovalPairDownProb law (K rule) hi lo))
    (hmixed_base_pos :
      0 <
        approvalPairwiseBase
          (∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo)) :
    ExponentialRateCertificate
        (pairwiseScoringErrorProb
          (randomizedKApprovalSamplingLaw law weight hweight hsum)
          (fun signal : Rule × Ranking n =>
            kApprovalScore (K signal.1) signal.2 hi)
          (fun signal : Rule × Ranking n =>
            kApprovalScore (K signal.1) signal.2 lo))
        (approvalPairwiseRate
          (∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo)) ∧
      ∃ rule : Rule,
        approvalPairwiseRate
            (∑ rule : Rule,
              weight rule * kApprovalPairUpProb law (K rule) hi lo)
            (∑ rule : Rule,
              weight rule * kApprovalPairDownProb law (K rule) hi lo) ≤
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) hi lo)
            (kApprovalPairDownProb law (K rule) hi lo) := by
  constructor
  · exact
      randomizedKApprovalPairwiseError_exponentialRateCertificate
        law K weight hweight hsum hi lo
        (pUp :=
          ∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
        (pDown :=
          ∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo)
        hmixedUp_pos hmixedDown_pos hmixedDown_le_up rfl rfl
  · exact
      randomizedApproval_pairwiseRate_le_static
        weight
        (fun rule => kApprovalPairUpProb law (K rule) hi lo)
        (fun rule => kApprovalPairDownProb law (K rule) hi lo)
        rfl rfl hweight hsum
        (fun rule => kApprovalPairUpProb_nonneg law (K rule) hi lo)
        (fun rule => kApprovalPairDownProb_nonneg law (K rule) hi lo)
        hbase_pos hmixed_base_pos

/--
Finite relevant-pair exact-rate certificate for a randomized K-approval rule.
The one-voter signal first draws a rule from the finite weight vector and then
draws a ranking from `law`; each relevant pair has ternary score gaps with the
supplied mixed up/down probabilities.
-/
noncomputable def randomizedKApprovalRelevantPairRateCertificate
    {n : ℕ} {Rule Pair : Type*} [Fintype Rule] [DecidableEq Rule]
    (law : PMF (Ranking n)) (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Pair → Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hle : ∀ pair, pDown pair ≤ pUp pair)
    (hUpProb :
      ∀ pair,
        (∑ rule : Rule,
          weight rule * kApprovalPairUpProb law (K rule)
            (hi pair) (lo pair)) =
          pUp pair)
    (hDownProb :
      ∀ pair,
        (∑ rule : Rule,
          weight rule * kApprovalPairDownProb law (K rule)
            (hi pair) (lo pair)) =
          pDown pair) :
    FiniteErrorRateCertificate Pair where
  errorProb :=
    fun pair =>
      pairwiseScoringErrorProb
        (randomizedKApprovalSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Ranking n =>
          kApprovalScore (K signal.1) signal.2 (hi pair))
        (fun signal : Rule × Ranking n =>
          kApprovalScore (K signal.1) signal.2 (lo pair))
  rate := fun pair => approvalPairwiseRate (pUp pair) (pDown pair)
  has_rate := by
    intro pair
    exact
      randomizedKApprovalPairwiseError_exponentialRateCertificate
        law K weight hweight hsum (hi pair) (lo pair)
        (hUp pair) (hDown pair) (hle pair)
        (hUpProb pair) (hDownProb pair)

/--
Exact finite aggregation theorem for randomized K-approval relevant pairs.
Positive pair weights make the aggregate exponent the finite minimum of the
mixed pairwise approval exponents.
-/
theorem randomizedKApprovalRelevantPairRateCertificate_aggregate_hasExponentialRate_at_finiteOutcomeLearningRate
    {n : ℕ} {Rule Pair : Type*} [Fintype Rule] [DecidableEq Rule]
    [Fintype Pair] [Nonempty Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Pair → Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hle : ∀ pair, pDown pair ≤ pUp pair)
    (hUpProb :
      ∀ pair,
        (∑ rule : Rule,
          weight rule * kApprovalPairUpProb law (K rule)
            (hi pair) (lo pair)) =
          pUp pair)
    (hDownProb :
      ∀ pair,
        (∑ rule : Rule,
          weight rule * kApprovalPairDownProb law (K rule)
            (hi pair) (lo pair)) =
          pDown pair)
    {pairWeight : Pair → ℝ}
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((randomizedKApprovalRelevantPairRateCertificate
          law K weight hweight hsum hi lo pUp pDown
          hUp hDown hle hUpProb hDownProb)
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Pair => approvalPairwiseRate (pUp pair) (pDown pair))) := by
  let C : FiniteErrorRateCertificate Pair :=
    randomizedKApprovalRelevantPairRateCertificate
      law K weight hweight hsum hi lo pUp pDown
      hUp hDown hle hUpProb hDownProb
  rcases finiteOutcomeLearningRate_exists_minimizer C.rate with
    ⟨pairMin, hrate_min, hrate_ge⟩
  have hcert :
      HasExponentialRate
        (C.aggregateError pairWeight)
        (finiteOutcomeLearningRate C.rate) :=
    C.aggregateError_hasExponentialRate_of_min_component
      hpairWeight pairMin (hpairWeight_pos pairMin)
      hrate_min.symm hrate_ge
  simpa [C, randomizedKApprovalRelevantPairRateCertificate]
    using hcert

/-- The constructed counterexample randomizes uniformly between K=1 and K=2. -/
def constructedWSelectionRandomizedApprovalK (rule : Fin 2) : ℕ :=
  rule.val + 1

/-- Uniform 50/50 weights for the constructed K=1/K=2 randomized rule. -/
def constructedWSelectionRandomizedApprovalWeight (_rule : Fin 2) : ℝ :=
  (1 : ℝ) / 2

theorem constructedWSelectionRandomizedApprovalWeight_nonneg :
    ∀ rule : Fin 2, 0 ≤ constructedWSelectionRandomizedApprovalWeight rule := by
  intro rule
  norm_num [constructedWSelectionRandomizedApprovalWeight]

theorem constructedWSelectionRandomizedApprovalWeight_sum :
    (∑ rule : Fin 2, constructedWSelectionRandomizedApprovalWeight rule) =
      1 := by
  rw [Fin.sum_univ_two]
  norm_num [constructedWSelectionRandomizedApprovalWeight]

theorem constructedWSelectionRanking1RandomizedApprovalUp_pos
    (pair : ConstructedWSelectionPair) :
    0 < constructedWSelectionRanking1RandomizedApprovalUp pair := by
  rw [constructedWSelectionRanking1RandomizedApprovalUp_eq]
  cases pair <;> norm_num [constructedWSelectionRandomizedUp]

theorem constructedWSelectionRanking1RandomizedApprovalDown_pos
    (pair : ConstructedWSelectionPair) :
    0 < constructedWSelectionRanking1RandomizedApprovalDown pair := by
  rw [constructedWSelectionRanking1RandomizedApprovalDown_eq]
  cases pair <;> norm_num [constructedWSelectionRandomizedDown]

theorem constructedWSelectionRanking1RandomizedApprovalDown_lt_up
    (pair : ConstructedWSelectionPair) :
    constructedWSelectionRanking1RandomizedApprovalDown pair <
      constructedWSelectionRanking1RandomizedApprovalUp pair := by
  rw [constructedWSelectionRanking1RandomizedApprovalUp_eq,
    constructedWSelectionRanking1RandomizedApprovalDown_eq]
  cases pair <;>
    norm_num [constructedWSelectionRandomizedUp,
      constructedWSelectionRandomizedDown]

theorem constructedWSelectionRanking1RandomizedApprovalUp_sum_eq
    (pair : ConstructedWSelectionPair) :
    (∑ rule : Fin 2,
        constructedWSelectionRandomizedApprovalWeight rule *
          kApprovalPairUpProb constructedWSelectionRanking1Law
            (constructedWSelectionRandomizedApprovalK rule)
            (constructedWSelectionPairWinnerToRanking1 pair)
            (constructedWSelectionPairLoserToRanking1 pair)) =
      constructedWSelectionRanking1RandomizedApprovalUp pair := by
  rw [Fin.sum_univ_two]
  simp [constructedWSelectionRandomizedApprovalWeight,
    constructedWSelectionRandomizedApprovalK,
    constructedWSelectionPairWinnerToRanking1,
    constructedWSelectionRanking1RandomizedApprovalUp]
  ring_nf

theorem constructedWSelectionRanking1RandomizedApprovalDown_sum_eq
    (pair : ConstructedWSelectionPair) :
    (∑ rule : Fin 2,
        constructedWSelectionRandomizedApprovalWeight rule *
          kApprovalPairDownProb constructedWSelectionRanking1Law
            (constructedWSelectionRandomizedApprovalK rule)
            (constructedWSelectionPairWinnerToRanking1 pair)
            (constructedWSelectionPairLoserToRanking1 pair)) =
      constructedWSelectionRanking1RandomizedApprovalDown pair := by
  rw [Fin.sum_univ_two]
  simp [constructedWSelectionRandomizedApprovalWeight,
    constructedWSelectionRandomizedApprovalK,
    constructedWSelectionPairWinnerToRanking1,
    constructedWSelectionRanking1RandomizedApprovalDown]
  ring_nf

/--
Actual one-voter law for the constructed 50/50 randomized approval rule:
first draw K=1 or K=2 uniformly, then draw a ranking from the explicit
six-ranking law.
-/
noncomputable def constructedWSelectionRanking1RandomizedApprovalSamplingLaw :
    PMF (Fin 2 × Ranking 1) :=
  randomizedKApprovalSamplingLaw
    constructedWSelectionRanking1Law
    constructedWSelectionRandomizedApprovalWeight
    constructedWSelectionRandomizedApprovalWeight_nonneg
    constructedWSelectionRandomizedApprovalWeight_sum

/--
Exact finite pairwise-rate certificate for the constructed 50/50 randomized
approval rule over the two relevant W-selection loser pairs.
-/
noncomputable def constructedWSelectionRanking1RandomizedApprovalRateCertificate :
    FiniteErrorRateCertificate ConstructedWSelectionPair where
  errorProb :=
    fun pair =>
      pairwiseScoringErrorProb
        constructedWSelectionRanking1RandomizedApprovalSamplingLaw
        (fun signal : Fin 2 × Ranking 1 =>
          kApprovalScore
            (constructedWSelectionRandomizedApprovalK signal.1)
            signal.2
            (constructedWSelectionPairWinnerToRanking1 pair))
        (fun signal : Fin 2 × Ranking 1 =>
          kApprovalScore
            (constructedWSelectionRandomizedApprovalK signal.1)
            signal.2
            (constructedWSelectionPairLoserToRanking1 pair))
  rate := constructedWSelectionRanking1RandomizedApprovalRate
  has_rate := by
    intro pair
    simpa [constructedWSelectionRanking1RandomizedApprovalSamplingLaw,
      constructedWSelectionRanking1RandomizedApprovalRate] using
      randomizedKApprovalPairwiseError_exponentialRateCertificate
        constructedWSelectionRanking1Law
        constructedWSelectionRandomizedApprovalK
        constructedWSelectionRandomizedApprovalWeight
        constructedWSelectionRandomizedApprovalWeight_nonneg
        constructedWSelectionRandomizedApprovalWeight_sum
        (constructedWSelectionPairWinnerToRanking1 pair)
        (constructedWSelectionPairLoserToRanking1 pair)
        (pUp := constructedWSelectionRanking1RandomizedApprovalUp pair)
        (pDown := constructedWSelectionRanking1RandomizedApprovalDown pair)
        (constructedWSelectionRanking1RandomizedApprovalUp_pos pair)
        (constructedWSelectionRanking1RandomizedApprovalDown_pos pair)
        (constructedWSelectionRanking1RandomizedApprovalDown_lt_up pair).le
        (constructedWSelectionRanking1RandomizedApprovalUp_sum_eq pair)
        (constructedWSelectionRanking1RandomizedApprovalDown_sum_eq pair)

theorem constructedWSelectionRanking1RandomizedApproval_outcomeError_hasExponentialRate
    {pairWeight : ConstructedWSelectionPair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      (constructedWSelectionRanking1RandomizedApprovalRateCertificate
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        constructedWSelectionRanking1RandomizedApprovalRate) := by
  let C : FiniteErrorRateCertificate ConstructedWSelectionPair :=
    constructedWSelectionRanking1RandomizedApprovalRateCertificate
  rcases finiteOutcomeLearningRate_exists_minimizer C.rate with
    ⟨pairMin, hrate_min, hrate_ge⟩
  have hcert :
      HasExponentialRate
        (C.aggregateError pairWeight)
        (finiteOutcomeLearningRate C.rate) :=
    C.aggregateError_hasExponentialRate_of_min_component
      hweight pairMin (hweight_pos pairMin)
      hrate_min.symm hrate_ge
  simpa [C, constructedWSelectionRanking1RandomizedApprovalRateCertificate]
    using hcert

def constructedWSelectionPairUnitWeight (_pair : ConstructedWSelectionPair) :
    ℝ := 1

theorem constructedWSelectionPairUnitWeight_nonneg :
    ∀ pair : ConstructedWSelectionPair,
      0 ≤ constructedWSelectionPairUnitWeight pair := by
  intro pair
  norm_num [constructedWSelectionPairUnitWeight]

theorem constructedWSelectionPairUnitWeight_pos :
    ∀ pair : ConstructedWSelectionPair,
      0 < constructedWSelectionPairUnitWeight pair := by
  intro pair
  norm_num [constructedWSelectionPairUnitWeight]

/--
Closed source-facing endpoint for the constructed W-selection counterexample:
the explicit six-ranking law is consistent for every reasonable prefix-score
rule, the actual voter-level 50/50 randomized approval process has the stated
finite aggregate exponent, and that exponent strictly beats every static
K-approval cutoff for the three-candidate law.
-/
theorem constructedWSelectionRanking1_consistency_exactRandomizedApprovalRate_and_improves_all_staticK :
    (∀ diff : RankingProperPrefixCut 1 → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb constructedWSelectionRanking1Law
            (rankingPrefixScore diff)
            constructedWSelectionRanking1WinnerSet
            (fun _voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                constructedWSelectionRanking1WinnerSet))
          Filter.atTop (nhds 0)) ∧
      HasExponentialRate
        (constructedWSelectionRanking1RandomizedApprovalRateCertificate
          |>.aggregateError constructedWSelectionPairUnitWeight)
        (finiteOutcomeLearningRate
          constructedWSelectionRanking1RandomizedApprovalRate) ∧
        (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
            (fun K =>
              finiteOutcomeLearningRate
                (constructedWSelectionRanking1StaticKRate K)) <
          finiteOutcomeLearningRate
            constructedWSelectionRanking1RandomizedApprovalRate :=
  ⟨constructedWSelectionRanking1Law_allReasonablePrefixScoreConsistency,
    constructedWSelectionRanking1RandomizedApproval_outcomeError_hasExponentialRate
      constructedWSelectionPairUnitWeight_nonneg
      constructedWSelectionPairUnitWeight_pos,
    constructedWSelectionRanking1ActualRandomizedApproval_improves_all_staticK⟩

theorem mallowsTopWRandomizedKApprovalPairUpProb_nonneg {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (pair : TopWSelectionPair M.center W) :
    0 ≤ mallowsTopWRandomizedKApprovalPairUpProb M W K weight pair := by
  unfold mallowsTopWRandomizedKApprovalPairUpProb
  exact Finset.sum_nonneg (fun rule _ =>
    mul_nonneg (hweight rule)
      (kApprovalPairUpProb_nonneg M.law (K rule) pair.hi pair.lo))

theorem mallowsTopWRandomizedKApprovalPairDownProb_nonneg {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (pair : TopWSelectionPair M.center W) :
    0 ≤ mallowsTopWRandomizedKApprovalPairDownProb M W K weight pair := by
  unfold mallowsTopWRandomizedKApprovalPairDownProb
  exact Finset.sum_nonneg (fun rule _ =>
    mul_nonneg (hweight rule)
      (kApprovalPairDownProb_nonneg M.law (K rule) pair.hi pair.lo))

theorem mallowsTopWRandomizedKApprovalPairUpProb_pos {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (pair : TopWSelectionPair M.center W) :
    0 < mallowsTopWRandomizedKApprovalPairUpProb M W K weight pair := by
  unfold mallowsTopWRandomizedKApprovalPairUpProb
  exact weighted_sum_pos_of_nonneg_sum_eq_one weight
    (fun rule => mallowsTopWKApprovalPairUpProb M W (K rule) pair)
    hweight hsum
    (fun rule =>
      mallowsTopWKApprovalPairUpProb_pos
        M W (K rule) (hK_pos rule) (hK_lt rule) pair)

theorem mallowsTopWRandomizedKApprovalPairDownProb_pos {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (pair : TopWSelectionPair M.center W) :
    0 < mallowsTopWRandomizedKApprovalPairDownProb M W K weight pair := by
  unfold mallowsTopWRandomizedKApprovalPairDownProb
  exact weighted_sum_pos_of_nonneg_sum_eq_one weight
    (fun rule => mallowsTopWKApprovalPairDownProb M W (K rule) pair)
    hweight hsum
    (fun rule =>
      mallowsTopWKApprovalPairDownProb_pos
        M W (K rule) (hK_pos rule) (hK_lt rule) pair)

theorem mallowsTopWRandomizedKApprovalPairUpDownProb_add_le_one {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (pair : TopWSelectionPair M.center W) :
    mallowsTopWRandomizedKApprovalPairUpProb M W K weight pair +
        mallowsTopWRandomizedKApprovalPairDownProb M W K weight pair ≤ 1 := by
  let up : Rule → ℝ := fun rule =>
    mallowsTopWKApprovalPairUpProb M W (K rule) pair
  let down : Rule → ℝ := fun rule =>
    mallowsTopWKApprovalPairDownProb M W (K rule) pair
  have hsum_le :
      (∑ rule : Rule, weight rule * (up rule + down rule)) ≤
        ∑ rule : Rule, weight rule * 1 := by
    refine Finset.sum_le_sum ?_
    intro rule _
    exact mul_le_mul_of_nonneg_left
      (by
        simpa [up, down, mallowsTopWKApprovalPairUpProb,
          mallowsTopWKApprovalPairDownProb] using
          kApprovalPairUpProb_add_downProb_le_one
            M.law (K rule) pair.hi pair.lo)
      (hweight rule)
  calc
    mallowsTopWRandomizedKApprovalPairUpProb M W K weight pair +
        mallowsTopWRandomizedKApprovalPairDownProb M W K weight pair
        =
        ∑ rule : Rule, weight rule * (up rule + down rule) := by
          simp [mallowsTopWRandomizedKApprovalPairUpProb,
            mallowsTopWRandomizedKApprovalPairDownProb, up, down,
            Finset.sum_add_distrib, mul_add]
    _ ≤ ∑ rule : Rule, weight rule * 1 := hsum_le
    _ = 1 := by simpa [hsum]

theorem mallowsTopWRandomizedKApprovalPairBase_pos {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (pair : TopWSelectionPair M.center W) :
    0 < approvalPairwiseBase
      (mallowsTopWRandomizedKApprovalPairUpProb M W K weight pair)
      (mallowsTopWRandomizedKApprovalPairDownProb M W K weight pair) := by
  exact approvalPairwiseBase_pos_of_pos_sum_le
    (mallowsTopWRandomizedKApprovalPairUpProb_pos
      M W K weight hweight hsum hK_pos hK_lt pair)
    (mallowsTopWRandomizedKApprovalPairDownProb_pos
      M W K weight hweight hsum hK_pos hK_lt pair)
    (mallowsTopWRandomizedKApprovalPairUpDownProb_add_le_one
      M W K weight hweight hsum pair)

theorem mallowsTopWRandomizedKApprovalPairDownProb_le_up_of_rank_lt {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hq_lt : M.q < 1)
    (pair : TopWSelectionPair M.center W) :
    mallowsTopWRandomizedKApprovalPairDownProb M W K weight pair ≤
      mallowsTopWRandomizedKApprovalPairUpProb M W K weight pair := by
  unfold mallowsTopWRandomizedKApprovalPairDownProb
    mallowsTopWRandomizedKApprovalPairUpProb
  refine Finset.sum_le_sum ?_
  intro rule _
  exact mul_le_mul_of_nonneg_left
    (mallowsTopWKApprovalPairDownProb_le_up_of_rank_lt
      M W (K rule) (le_of_lt hq_lt) pair)
    (hweight rule)

theorem mallowsTopWRandomizedKApprovalBoundary_upProb_le_pair {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hq_lt : M.q < 1)
    (pair : TopWSelectionPair M.center W) :
    mallowsTopWRandomizedKApprovalPairUpProb M W K weight
        (topWBoundaryPair M.center W hW) ≤
      mallowsTopWRandomizedKApprovalPairUpProb M W K weight pair := by
  unfold mallowsTopWRandomizedKApprovalPairUpProb
  refine Finset.sum_le_sum ?_
  intro rule _
  exact mul_le_mul_of_nonneg_left
    (mallowsTopWKApprovalBoundary_upProb_le_pair
      M W hW (K rule) (le_of_lt hq_lt) pair)
    (hweight rule)

theorem mallowsTopWRandomizedKApprovalPair_downProb_le_boundary {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hq_lt : M.q < 1)
    (pair : TopWSelectionPair M.center W) :
    mallowsTopWRandomizedKApprovalPairDownProb M W K weight pair ≤
      mallowsTopWRandomizedKApprovalPairDownProb M W K weight
        (topWBoundaryPair M.center W hW) := by
  unfold mallowsTopWRandomizedKApprovalPairDownProb
  refine Finset.sum_le_sum ?_
  intro rule _
  exact mul_le_mul_of_nonneg_left
    (mallowsTopWKApprovalPair_downProb_le_boundary
      M W hW (K rule) (le_of_lt hq_lt) pair)
    (hweight rule)

theorem mallowsTopWRandomizedKApprovalOutcomeRate_eq_boundary {n : ℕ}
    {Rule : Type*} [Fintype Rule]
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (hq_lt : M.q < 1) :
    mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight =
      mallowsTopWRandomizedKApprovalPairRate M W K weight
        (topWBoundaryPair M.center W hW) := by
  classical
  unfold mallowsTopWRandomizedKApprovalOutcomeRate finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le (mallowsTopWRandomizedKApprovalPairRate M W K weight)
      (by simp : topWBoundaryPair M.center W hW ∈
        (Finset.univ : Finset (TopWSelectionPair M.center W)))
  · exact Finset.le_inf' _ _ (by
      intro pair _
      unfold mallowsTopWRandomizedKApprovalPairRate
      exact approvalPairwiseRate_le_of_up_le_down_ge
        (mallowsTopWRandomizedKApprovalPairUpProb_nonneg
          M W K weight hweight (topWBoundaryPair M.center W hW))
        (mallowsTopWRandomizedKApprovalPairDownProb_nonneg
          M W K weight hweight (topWBoundaryPair M.center W hW))
        (mallowsTopWRandomizedKApprovalPairUpProb_nonneg
          M W K weight hweight pair)
        (mallowsTopWRandomizedKApprovalPairDownProb_nonneg
          M W K weight hweight pair)
        (mallowsTopWRandomizedKApprovalPairBase_pos
          M W K weight hweight hsum hK_pos hK_lt
          (topWBoundaryPair M.center W hW))
        (mallowsTopWRandomizedKApprovalPairBase_pos
          M W K weight hweight hsum hK_pos hK_lt pair)
        (mallowsTopWRandomizedKApprovalPairDownProb_le_up_of_rank_lt
          M W K weight hweight hq_lt (topWBoundaryPair M.center W hW))
        (mallowsTopWRandomizedKApprovalPairDownProb_le_up_of_rank_lt
          M W K weight hweight hq_lt pair)
        (mallowsTopWRandomizedKApprovalBoundary_upProb_le_pair
          M W hW K weight hweight hq_lt pair)
        (mallowsTopWRandomizedKApprovalPair_downProb_le_boundary
          M W hW K weight hweight hq_lt pair))

/--
Exact-rate certificate for all cross-tier Top-W randomized K-approval pair
errors under a finite Mallows law.  The one-voter randomized signal is the
independent draw of a rule and a ranking, so each pairwise score gap is still
ternary with the mixed up/down probabilities.
-/
noncomputable def mallowsTopWRandomizedKApprovalRateCertificate {n : ℕ}
    {Rule : Type*} [Fintype Rule] [DecidableEq Rule]
    (M : MallowsSpec n) (W : Candidate n)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (hq_lt : M.q < 1) :
    FiniteErrorRateCertificate (TopWSelectionPair M.center W) where
  errorProb :=
    fun pair =>
      pairwiseScoringErrorProb
        (randomizedKApprovalSamplingLaw M.law weight hweight hsum)
        (fun signal : Rule × Ranking n =>
          kApprovalScore (K signal.1) signal.2 pair.hi)
        (fun signal : Rule × Ranking n =>
          kApprovalScore (K signal.1) signal.2 pair.lo)
  rate := fun pair => mallowsTopWRandomizedKApprovalPairRate M W K weight pair
  has_rate := by
    intro pair
    exact
      randomizedKApprovalPairwiseError_exponentialRateCertificate
        M.law K weight hweight hsum pair.hi pair.lo
        (pUp := mallowsTopWRandomizedKApprovalPairUpProb M W K weight pair)
        (pDown := mallowsTopWRandomizedKApprovalPairDownProb M W K weight pair)
        (mallowsTopWRandomizedKApprovalPairUpProb_pos
          M W K weight hweight hsum hK_pos hK_lt pair)
        (mallowsTopWRandomizedKApprovalPairDownProb_pos
          M W K weight hweight hsum hK_pos hK_lt pair)
        (mallowsTopWRandomizedKApprovalPairDownProb_le_up_of_rank_lt
          M W K weight hweight hq_lt pair)
        rfl rfl

theorem mallowsTopWRandomizedKApprovalOutcomeError_hasExponentialRate_eq_boundary
    {n : ℕ}
    {Rule : Type*} [Fintype Rule] [DecidableEq Rule]
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (hq_lt : M.q < 1)
    {pairWeight : TopWSelectionPair M.center W → ℝ}
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((mallowsTopWRandomizedKApprovalRateCertificate
          M W K weight hweight hsum hK_pos hK_lt hq_lt)
        |>.aggregateError pairWeight)
      (mallowsTopWRandomizedKApprovalPairRate M W K weight
        (topWBoundaryPair M.center W hW)) := by
  classical
  haveI : Nonempty (TopWSelectionPair M.center W) :=
    instNonemptyTopWSelectionPair M.center W hW
  let C : FiniteErrorRateCertificate (TopWSelectionPair M.center W) :=
    mallowsTopWRandomizedKApprovalRateCertificate
      M W K weight hweight hsum hK_pos hK_lt hq_lt
  let boundary := topWBoundaryPair M.center W hW
  have hboundary :
      finiteOutcomeLearningRate C.rate = C.rate boundary := by
    simpa [C, boundary, mallowsTopWRandomizedKApprovalRateCertificate] using
      mallowsTopWRandomizedKApprovalOutcomeRate_eq_boundary
        M W hW K weight hweight hsum hK_pos hK_lt hq_lt
  have hcert :
      HasExponentialRate (C.aggregateError pairWeight) (C.rate boundary) :=
    C.aggregateError_hasExponentialRate_of_min_component
      hpairWeight boundary (hpairWeight_pos boundary) rfl
      (by
        intro pair
        calc
          C.rate boundary = finiteOutcomeLearningRate C.rate := hboundary.symm
          _ ≤ C.rate pair := finiteOutcomeLearningRate_le C.rate pair)
  simpa [C, boundary, mallowsTopWRandomizedKApprovalRateCertificate] using hcert

/--
Finite-candidate Mallows no-randomization theorem for randomized finite
families of nontrivial K-approval rules.  Under `q < 1`, the same adjacent
boundary pair realizes the static and randomized finite outcome rates, so the
pairwise K-approval no-randomization inequality lifts directly to W-selection.
-/
theorem mallowsTopWRandomizedKApproval_noRandomization {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    ∃ rule : Rule,
      mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight ≤
        mallowsTopWKApprovalOutcomeRate M W hW (K rule) := by
  classical
  let boundary := topWBoundaryPair M.center W hW
  let pUp : Rule → ℝ := fun rule =>
    mallowsTopWKApprovalPairUpProb M W (K rule) boundary
  let pDown : Rule → ℝ := fun rule =>
    mallowsTopWKApprovalPairDownProb M W (K rule) boundary
  let staticPairRate : Rule → TopWSelectionPair M.center W → ℝ := fun rule pair =>
    mallowsTopWKApprovalPairRate M W (K rule) pair
  let randomizedPairRate : TopWSelectionPair M.center W → ℝ := fun pair =>
    mallowsTopWRandomizedKApprovalPairRate M W K weight pair
  haveI : Nonempty (TopWSelectionPair M.center W) :=
    instNonemptyTopWSelectionPair M.center W hW
  rcases
      kApprovalOutcome_no_randomization_of_common_pivotal_pair_positive
        (weight := weight)
        (pUp := pUp)
        (pDown := pDown)
        (staticPairRate := staticPairRate)
        (randomizedPairRate := randomizedPairRate)
        (pivotal := boundary)
        (mixedUp :=
          mallowsTopWRandomizedKApprovalPairUpProb M W K weight boundary)
        (mixedDown :=
          mallowsTopWRandomizedKApprovalPairDownProb M W K weight boundary)
        (by
          simp [mallowsTopWRandomizedKApprovalPairUpProb, pUp])
        (by
          simp [mallowsTopWRandomizedKApprovalPairDownProb, pDown])
        hweight hsum
        (fun rule =>
          le_of_lt (mallowsTopWKApprovalPairUpProb_pos
            M W (K rule) (hK_pos rule) (hK_lt rule) boundary))
        (fun rule =>
          le_of_lt (mallowsTopWKApprovalPairDownProb_pos
            M W (K rule) (hK_pos rule) (hK_lt rule) boundary))
        (fun rule =>
          mallowsTopWKApprovalPairBase_pos
            M W (K rule) (hK_pos rule) (hK_lt rule) boundary)
        (mallowsTopWRandomizedKApprovalPairBase_pos
          M W K weight hweight hsum hK_pos hK_lt boundary)
        (fun rule => by
          simpa [staticPairRate, mallowsTopWKApprovalOutcomeRate, boundary] using
            mallowsTopWKApprovalOutcomeRate_eq_boundary
              M W hW (K rule) (hK_pos rule) (hK_lt rule) hq_lt)
        (fun rule => by
          rfl)
        (by
          simpa [randomizedPairRate, mallowsTopWRandomizedKApprovalOutcomeRate,
            boundary] using
            mallowsTopWRandomizedKApprovalOutcomeRate_eq_boundary
              M W hW K weight hweight hsum hK_pos hK_lt hq_lt)
        (by
          rfl) with
    ⟨rule, hrule⟩
  exact ⟨rule, by simpa [staticPairRate, randomizedPairRate] using hrule⟩

/--
Finite-candidate Mallows no-randomization theorem in the source corollary's
"approval-rate optimal" form.  Among all proper K-approval cutoffs, choose a
static cutoff maximizing the finite W-selection learning rate; it weakly
dominates every randomized finite family of nontrivial K-approval rules.
-/
theorem mallowsTopWRandomizedKApproval_noRandomization_to_optimalStatic
    {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    ∃ cut : RankingProperPrefixCut n,
      (∀ cut' : RankingProperPrefixCut n,
        mallowsTopWKApprovalOutcomeRate M W hW (cut'.val + 1) ≤
          mallowsTopWKApprovalOutcomeRate M W hW (cut.val + 1)) ∧
      mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight ≤
        mallowsTopWKApprovalOutcomeRate M W hW (cut.val + 1) := by
  classical
  let staticRate : RankingProperPrefixCut n → ℝ :=
    fun cut => mallowsTopWKApprovalOutcomeRate M W hW (cut.val + 1)
  haveI : Nonempty (RankingProperPrefixCut n) :=
    ⟨⟨0, Nat.succ_pos n⟩⟩
  rcases (Finset.univ : Finset (RankingProperPrefixCut n)).exists_mem_eq_sup'
      finiteUnivNonempty staticRate with
    ⟨best, _, hbest⟩
  rcases mallowsTopWRandomizedKApproval_noRandomization
      M W hW hq_lt K hK_pos hK_lt weight hweight hsum with
    ⟨rule, hrule⟩
  let ruleCut : RankingProperPrefixCut n :=
    ⟨K rule - 1,
      by
        have hk_le : K rule ≤ n + 1 := Nat.le_of_lt_succ (hK_lt rule)
        have hle : K rule - 1 ≤ n := by
          omega
        exact lt_of_le_of_lt hle (Nat.lt_succ_self n)⟩
  have hruleCut : ruleCut.val + 1 = K rule := by
    dsimp [ruleCut]
    exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (hK_pos rule))
  refine ⟨best, ?_, ?_⟩
  · intro cut'
    calc
      staticRate cut' ≤
          (Finset.univ : Finset (RankingProperPrefixCut n)).sup'
            finiteUnivNonempty staticRate :=
        Finset.le_sup' staticRate (Finset.mem_univ cut')
      _ = staticRate best := hbest
  · calc
      mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight ≤
          mallowsTopWKApprovalOutcomeRate M W hW (K rule) := hrule
      _ = staticRate ruleCut := by rw [← hruleCut]
      _ ≤ staticRate best := by
        calc
          staticRate ruleCut ≤
              (Finset.univ : Finset (RankingProperPrefixCut n)).sup'
                finiteUnivNonempty staticRate :=
            Finset.le_sup' staticRate (Finset.mem_univ ruleCut)
          _ = staticRate best := hbest

theorem mallowsFirstChoiceProb_pos {n : ℕ}
    (M : MallowsSpec n) (c : Candidate n) :
    0 < firstChoiceProb M.law c := by
  rw [M.firstChoiceProb_eq_rank_pow_div_rankPowerSum c]
  exact div_pos (pow_pos M.q_pos _) (candidateRankPowerSum_pos n M.q_pos)

theorem mallowsFirstChoiceProb_le_of_rank_le {n : ℕ}
    (M : MallowsSpec n) (hq_le : M.q ≤ 1)
    {a b : Candidate n}
    (hrank : rankOf M.center a ≤ rankOf M.center b) :
    firstChoiceProb M.law b ≤ firstChoiceProb M.law a := by
  rw [M.firstChoiceProb_eq_rank_pow_div_rankPowerSum b,
    M.firstChoiceProb_eq_rank_pow_div_rankPowerSum a]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_of_le_one M.q_pos.le hq_le hrank)
    (le_of_lt (candidateRankPowerSum_pos n M.q_pos))

theorem mallowsTopWOneApproval_boundary_rate_le_pair_rate {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1) (pair : TopWSelectionPair M.center W) :
    mallowsTopWOneApprovalPairRate M W (topWBoundaryPair M.center W hW) ≤
      mallowsTopWOneApprovalPairRate M W pair := by
  let boundary := topWBoundaryPair M.center W hW
  have hq_le : M.q ≤ 1 := le_of_lt hq_lt
  have hboundary_down_le_up :
      firstChoiceProb M.law boundary.lo ≤ firstChoiceProb M.law boundary.hi := by
    exact mallowsFirstChoiceProb_le_of_rank_le M hq_le
      (le_of_lt boundary.rank_hi_lt_rank_lo)
  have hpair_down_le_up :
      firstChoiceProb M.law pair.lo ≤ firstChoiceProb M.law pair.hi := by
    exact mallowsFirstChoiceProb_le_of_rank_le M hq_le
      (le_of_lt pair.rank_hi_lt_rank_lo)
  have hup_le :
      firstChoiceProb M.law boundary.hi ≤ firstChoiceProb M.law pair.hi := by
    exact mallowsFirstChoiceProb_le_of_rank_le M hq_le
      (by
        change (rankOf M.center pair.hi).val ≤
          (rankOf M.center boundary.hi).val
        have hboundary_rank_val :
            (rankOf M.center boundary.hi).val = W.val - 1 := by
          simp [boundary, topWBoundaryPair, TopWSelectionPair.hi, rankOf]
        rw [hboundary_rank_val]
        have hpair_lt : (rankOf M.center pair.hi).val < W.val := by
          exact pair.rank_hi_lt_cut
        omega)
  have hdown_ge :
      firstChoiceProb M.law pair.lo ≤ firstChoiceProb M.law boundary.lo := by
    exact mallowsFirstChoiceProb_le_of_rank_le M hq_le
      (by
        change (rankOf M.center boundary.lo).val ≤
          (rankOf M.center pair.lo).val
        have hboundary_rank_val :
            (rankOf M.center boundary.lo).val = W.val := by
          simp [boundary, topWBoundaryPair, TopWSelectionPair.lo, rankOf]
        rw [hboundary_rank_val]
        exact pair.cut_le_rank_lo)
  unfold mallowsTopWOneApprovalPairRate
  refine approvalPairwiseRate_le_of_up_le_down_ge
    ?_ ?_ ?_ ?_ ?_ ?_ hboundary_down_le_up hpair_down_le_up hup_le hdown_ge
  · exact le_of_lt (mallowsFirstChoiceProb_pos M boundary.hi)
  · exact le_of_lt (mallowsFirstChoiceProb_pos M boundary.lo)
  · exact le_of_lt (mallowsFirstChoiceProb_pos M pair.hi)
  · exact le_of_lt (mallowsFirstChoiceProb_pos M pair.lo)
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (mallowsFirstChoiceProb_pos M boundary.hi)
      (mallowsFirstChoiceProb_pos M boundary.lo)
      (firstChoiceProb_add_le_one M.law boundary.hi_ne_lo)
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (mallowsFirstChoiceProb_pos M pair.hi)
      (mallowsFirstChoiceProb_pos M pair.lo)
      (firstChoiceProb_add_le_one M.law pair.hi_ne_lo)

theorem mallowsTopWOneApprovalOutcomeRate_eq_boundary {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1) :
    mallowsTopWOneApprovalOutcomeRate M W hW =
      mallowsTopWOneApprovalPairRate M W (topWBoundaryPair M.center W hW) := by
  unfold mallowsTopWOneApprovalOutcomeRate finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le (mallowsTopWOneApprovalPairRate M W)
      (by simp : topWBoundaryPair M.center W hW ∈
        (Finset.univ : Finset (TopWSelectionPair M.center W)))
  · exact Finset.le_inf' _ _ (by
      intro pair _
      exact mallowsTopWOneApproval_boundary_rate_le_pair_rate M W hW hq_lt pair)

/-- The generic K-approval pair-rate API specializes to one-approval at `K = 1`. -/
theorem mallowsTopWKApprovalPairRate_one_eq_oneApproval {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n)
    (pair : TopWSelectionPair M.center W) :
    mallowsTopWKApprovalPairRate M W 1 pair =
      mallowsTopWOneApprovalPairRate M W pair := by
  unfold mallowsTopWKApprovalPairRate mallowsTopWKApprovalPairUpProb
    mallowsTopWKApprovalPairDownProb mallowsTopWOneApprovalPairRate
  rw [kApprovalPairUpProb_one_eq_firstChoiceProb M.law pair.hi_ne_lo]
  rw [kApprovalPairDownProb_eq_pairUpProb_swap]
  rw [kApprovalPairUpProb_one_eq_firstChoiceProb M.law
    (Ne.symm pair.hi_ne_lo)]

/-- The generic K-approval outcome-rate API specializes to one-approval at `K = 1`. -/
theorem mallowsTopWKApprovalOutcomeRate_one_eq_oneApproval {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val) :
    mallowsTopWKApprovalOutcomeRate M W hW 1 =
      mallowsTopWOneApprovalOutcomeRate M W hW := by
  unfold mallowsTopWKApprovalOutcomeRate mallowsTopWOneApprovalOutcomeRate
  congr 1
  funext pair
  exact mallowsTopWKApprovalPairRate_one_eq_oneApproval M W pair

theorem mallowsTopWKApprovalOutcomeRate_one_eq_boundary {n : ℕ}
    (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1) :
    mallowsTopWKApprovalOutcomeRate M W hW 1 =
      mallowsTopWKApprovalPairRate M W 1 (topWBoundaryPair M.center W hW) := by
  rw [mallowsTopWKApprovalOutcomeRate_one_eq_oneApproval]
  rw [mallowsTopWOneApprovalOutcomeRate_eq_boundary M W hW hq_lt]
  rw [mallowsTopWKApprovalPairRate_one_eq_oneApproval]

/--
Arbitrary finite-candidate Mallows no-randomization bridge for finite families
of nontrivial K-approval rules.  The static pivotal-pair hypotheses are
discharged by the Mallows boundary theorem; the randomized mechanism only has
to expose its boundary-pair mixed up/down probabilities.
-/
theorem mallowsTopWKApproval_noRandomization_of_static_boundary
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (randomizedPairRate : TopWSelectionPair M.center W → ℝ)
    {mixedUp mixedDown : ℝ}
    (hmixedUp :
      mixedUp =
        ∑ rule : Rule,
          weight rule *
            mallowsTopWKApprovalPairUpProb M W (K rule)
              (topWBoundaryPair M.center W hW))
    (hmixedDown :
      mixedDown =
        ∑ rule : Rule,
          weight rule *
            mallowsTopWKApprovalPairDownProb M W (K rule)
              (topWBoundaryPair M.center W hW))
    (hmixed_base_pos : 0 < approvalPairwiseBase mixedUp mixedDown)
    (hrandomized_boundary :
      randomizedPairRate (topWBoundaryPair M.center W hW) =
        approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule,
      @finiteOutcomeLearningRate (TopWSelectionPair M.center W) inferInstance
          (instNonemptyTopWSelectionPair M.center W hW) randomizedPairRate ≤
        mallowsTopWKApprovalOutcomeRate M W hW (K rule) := by
  classical
  let boundary := topWBoundaryPair M.center W hW
  let pUp : Rule → ℝ := fun rule =>
    mallowsTopWKApprovalPairUpProb M W (K rule) boundary
  let pDown : Rule → ℝ := fun rule =>
    mallowsTopWKApprovalPairDownProb M W (K rule) boundary
  let staticPairRate : Rule → TopWSelectionPair M.center W → ℝ := fun rule pair =>
    mallowsTopWKApprovalPairRate M W (K rule) pair
  haveI : Nonempty (TopWSelectionPair M.center W) :=
    instNonemptyTopWSelectionPair M.center W hW
  rcases
      kApprovalOutcome_no_randomization_of_static_pivotal_pair_positive
        (weight := weight)
        (pUp := pUp)
        (pDown := pDown)
        (staticPairRate := staticPairRate)
        (randomizedPairRate := randomizedPairRate)
        (pivotal := boundary)
        (mixedUp := mixedUp)
        (mixedDown := mixedDown)
        (by simpa [pUp, boundary] using hmixedUp)
        (by simpa [pDown, boundary] using hmixedDown)
        hweight hsum
        (fun rule =>
          le_of_lt (mallowsTopWKApprovalPairUpProb_pos
            M W (K rule) (hK_pos rule) (hK_lt rule) boundary))
        (fun rule =>
          le_of_lt (mallowsTopWKApprovalPairDownProb_pos
            M W (K rule) (hK_pos rule) (hK_lt rule) boundary))
        (fun rule =>
          mallowsTopWKApprovalPairBase_pos
            M W (K rule) (hK_pos rule) (hK_lt rule) boundary)
        hmixed_base_pos
        (fun rule => by
          simpa [staticPairRate, mallowsTopWKApprovalOutcomeRate, boundary] using
            mallowsTopWKApprovalOutcomeRate_eq_boundary
              M W hW (K rule) (hK_pos rule) (hK_lt rule) hq_lt)
        (fun rule => by
          rfl)
        (by simpa [boundary] using hrandomized_boundary) with
    ⟨rule, hrule⟩
  exact ⟨rule, by simpa [staticPairRate] using hrule⟩

/--
Arbitrary finite-candidate Mallows no-randomization bridge for finite families
of nontrivial K-approval rules, allowing the supplied randomized boundary
pair to be on the real-valued mixed-base boundary.  This is the reusable
Mallows-facing form when a caller has static boundary-pair pivotality but has
not separately proved positive mixed base for the randomized rule.
-/
theorem mallowsTopWKApproval_noRandomization_of_static_boundary_or_mixed_boundary
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (randomizedPairRate : TopWSelectionPair M.center W → ℝ)
    {mixedUp mixedDown : ℝ}
    (hmixedUp :
      mixedUp =
        ∑ rule : Rule,
          weight rule *
            mallowsTopWKApprovalPairUpProb M W (K rule)
              (topWBoundaryPair M.center W hW))
    (hmixedDown :
      mixedDown =
        ∑ rule : Rule,
          weight rule *
            mallowsTopWKApprovalPairDownProb M W (K rule)
              (topWBoundaryPair M.center W hW))
    (hrandomized_boundary :
      randomizedPairRate (topWBoundaryPair M.center W hW) =
        approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule,
      @finiteOutcomeLearningRate (TopWSelectionPair M.center W) inferInstance
          (instNonemptyTopWSelectionPair M.center W hW) randomizedPairRate ≤
        mallowsTopWKApprovalOutcomeRate M W hW (K rule) := by
  classical
  let boundary := topWBoundaryPair M.center W hW
  let pUp : Rule → ℝ := fun rule =>
    mallowsTopWKApprovalPairUpProb M W (K rule) boundary
  let pDown : Rule → ℝ := fun rule =>
    mallowsTopWKApprovalPairDownProb M W (K rule) boundary
  let staticPairRate : Rule → TopWSelectionPair M.center W → ℝ := fun rule pair =>
    mallowsTopWKApprovalPairRate M W (K rule) pair
  haveI : Nonempty (TopWSelectionPair M.center W) :=
    instNonemptyTopWSelectionPair M.center W hW
  rcases
      kApprovalOutcome_no_randomization_of_static_pivotal_pair_or_mixed_boundary
        (weight := weight)
        (pUp := pUp)
        (pDown := pDown)
        (staticPairRate := staticPairRate)
        (randomizedPairRate := randomizedPairRate)
        (pivotal := boundary)
        (mixedUp := mixedUp)
        (mixedDown := mixedDown)
        (by simpa [pUp, boundary] using hmixedUp)
        (by simpa [pDown, boundary] using hmixedDown)
        hweight hsum
        (fun rule =>
          le_of_lt (mallowsTopWKApprovalPairUpProb_pos
            M W (K rule) (hK_pos rule) (hK_lt rule) boundary))
        (fun rule =>
          le_of_lt (mallowsTopWKApprovalPairDownProb_pos
            M W (K rule) (hK_pos rule) (hK_lt rule) boundary))
        (fun rule =>
          by
            simpa [pUp, pDown, boundary, mallowsTopWKApprovalPairUpProb,
              mallowsTopWKApprovalPairDownProb] using
              kApprovalPairUpProb_add_downProb_le_one
                M.law (K rule) boundary.hi boundary.lo)
        (fun rule =>
          mallowsTopWKApprovalPairBase_pos
            M W (K rule) (hK_pos rule) (hK_lt rule) boundary)
        (fun rule => by
          simpa [staticPairRate, mallowsTopWKApprovalOutcomeRate, boundary] using
            mallowsTopWKApprovalOutcomeRate_eq_boundary
              M W hW (K rule) (hK_pos rule) (hK_lt rule) hq_lt)
        (fun rule => by
          rfl)
        (by simpa [boundary] using hrandomized_boundary) with
    ⟨rule, hrule⟩
  exact ⟨rule, by simpa [staticPairRate] using hrule⟩

end

end GGSG19TopThree
