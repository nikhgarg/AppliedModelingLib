import GGSG19TopThree.MainTheorems
import AppliedModelingLib.SocialChoice.Ranking.MallowsRankFactorization

open scoped BigOperators

namespace GGSG19TopThree

noncomputable section

open AppliedModelingLib.SocialChoice.Ranking
open AppliedModelingLib.Probability

/-!
# Mallows Approval Examples

Finite Mallows rank-factorization calculations used by the paper's approval
examples.  The first target is the `M = 4`, `W = 3` high-noise example: for
the source pair `(3,4)`, the `K = 2` approval probabilities can be derived
from the reusable first/top-two Mallows rank-factorization API.
-/

/--
Unnormalised Mallows mass of rankings where `hi` is in the top two positions
and `lo` is not.  This is the `K = 2` approval up-event for the ordered pair
`(hi, lo)`.
-/
def mallowsTopTwoPairUpWeight {n : ℕ}
    (M : MallowsSpec n) (hi lo : Candidate n) : ℝ :=
  ∑ other : Candidate n,
    if other ≠ hi ∧ other ≠ lo then
      M.firstSecondWeight hi other + M.firstSecondWeight other hi
    else 0

/--
Probability that `hi` is in the top two positions and `lo` is not, written as
a finite sum over ordered top-two probabilities.
-/
def mallowsTopTwoPairUpProb {n : ℕ}
    (M : MallowsSpec n) (hi lo : Candidate n) : ℝ :=
  ∑ other : Candidate n,
    if other ≠ hi ∧ other ≠ lo then
      M.firstSecondChoiceProb hi other + M.firstSecondChoiceProb other hi
    else 0

/-- The top-two approval probability is its unnormalised weight divided by `Z`. -/
theorem mallowsTopTwoPairUpProb_eq_weight_div_partition {n : ℕ}
    (M : MallowsSpec n) (hi lo : Candidate n) :
    mallowsTopTwoPairUpProb M hi lo =
      mallowsTopTwoPairUpWeight M hi lo / M.partition := by
  unfold mallowsTopTwoPairUpProb mallowsTopTwoPairUpWeight
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro other _
  by_cases h : other ≠ hi ∧ other ≠ lo
  · simp [h, M.firstSecondChoiceProb_eq_firstSecondWeight_div_partition]
    ring
  · simp [h]

/--
The paper-local `K = 2` up-event is the generic two-approval up-event for
distinct candidates.
-/
theorem mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb {n : ℕ}
    (M : MallowsSpec n) {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    mallowsTopTwoPairUpProb M hi lo =
      kApprovalPairUpProb M.law 2 hi lo := by
  rw [kApprovalPairUpProb_two_eq_firstSecondChoiceSum M.law hhi_lo]
  rfl

/--
Generic rank-factorized form of the two-approval up-event weight.  Each
eligible companion candidate contributes the unordered top-two fiber for
`hi` and that companion.
-/
theorem mallowsTopTwoPairUpWeight_eq_rank_sum {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization)
    (hi lo : Candidate n) :
    mallowsTopTwoPairUpWeight M hi lo =
      ∑ other : Candidate n,
        if other ≠ hi ∧ other ≠ lo then
          (1 + M.q) *
            (M.q ^ ((rankOf M.center hi : ℕ) +
                (rankOf M.center other : ℕ) - 1) *
              fac.firstSecondTail)
        else 0 := by
  unfold mallowsTopTwoPairUpWeight
  refine Finset.sum_congr rfl ?_
  intro other _
  by_cases hother : other ≠ hi ∧ other ≠ lo
  · have hhi_other : hi ≠ other := hother.1.symm
    simp [hother,
      MallowsSpec.firstSecondWeight_add_swap_eq_rank_sum M fac hhi_other]
  · simp [hother]

/-- Factored rank-kernel form of the two-approval up-event weight. -/
theorem mallowsTopTwoPairUpWeight_eq_rank_kernel {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization)
    (hi lo : Candidate n) :
    mallowsTopTwoPairUpWeight M hi lo =
      (1 + M.q) * fac.firstSecondTail *
        candidateRankTopTwoPairKernel n M.q
          (rankOf M.center hi) (rankOf M.center lo) := by
  rw [mallowsTopTwoPairUpWeight_eq_rank_sum M fac hi lo]
  unfold candidateRankTopTwoPairKernel
  calc
    (∑ other : Candidate n,
        if other ≠ hi ∧ other ≠ lo then
          (1 + M.q) *
            (M.q ^ ((rankOf M.center hi : ℕ) +
                (rankOf M.center other : ℕ) - 1) *
              fac.firstSecondTail)
        else 0)
        =
      ∑ r : Candidate n,
        if M.center r ≠ hi ∧ M.center r ≠ lo then
          (1 + M.q) *
            (M.q ^ ((rankOf M.center hi : ℕ) + (r : ℕ) - 1) *
              fac.firstSecondTail)
        else 0 := by
      simpa [rankOf] using
        (Equiv.sum_comp M.center
          (fun other : Candidate n =>
            if other ≠ hi ∧ other ≠ lo then
              (1 + M.q) *
                (M.q ^ ((rankOf M.center hi : ℕ) +
                    (rankOf M.center other : ℕ) - 1) *
                  fac.firstSecondTail)
            else 0)).symm
    _ =
      ∑ r : Candidate n,
        if r ≠ rankOf M.center hi ∧ r ≠ rankOf M.center lo then
          (1 + M.q) *
            (M.q ^ ((rankOf M.center hi : ℕ) + (r : ℕ) - 1) *
              fac.firstSecondTail)
        else 0 := by
      refine Finset.sum_congr rfl ?_
      intro r _
      have hhi_iff :
          M.center r ≠ hi ↔ r ≠ rankOf M.center hi := by
        constructor
        · intro h hr
          apply h
          rw [hr]
          simp [rankOf]
        · intro h hc
          apply h
          simpa [rankOf] using congrArg M.center.symm hc
      have hlo_iff :
          M.center r ≠ lo ↔ r ≠ rankOf M.center lo := by
        constructor
        · intro h hr
          apply h
          rw [hr]
          simp [rankOf]
        · intro h hc
          apply h
          simpa [rankOf] using congrArg M.center.symm hc
      by_cases hr :
          r ≠ rankOf M.center hi ∧ r ≠ rankOf M.center lo
      · rw [if_pos ⟨hhi_iff.2 hr.1, hlo_iff.2 hr.2⟩, if_pos hr]
      · rw [if_neg (by
          intro h
          exact hr ⟨hhi_iff.1 h.1, hlo_iff.1 h.2⟩), if_neg hr]
    _ =
      (1 + M.q) * fac.firstSecondTail *
        (∑ r : Candidate n,
          if r ≠ rankOf M.center hi ∧ r ≠ rankOf M.center lo then
            M.q ^ ((rankOf M.center hi : ℕ) + (r : ℕ) - 1)
          else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          by_cases hr : r ≠ rankOf M.center hi ∧ r ≠ rankOf M.center lo
          · simp [hr]
            ring
          · simp [hr]

/-- Normalized rank-sum form of the two-approval up-event probability. -/
theorem mallowsTopTwoPairUpProb_eq_rank_sum_div_partition {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization)
    (hi lo : Candidate n) :
    mallowsTopTwoPairUpProb M hi lo =
      (∑ other : Candidate n,
        if other ≠ hi ∧ other ≠ lo then
          (1 + M.q) *
            (M.q ^ ((rankOf M.center hi : ℕ) +
                (rankOf M.center other : ℕ) - 1) *
              fac.firstSecondTail)
        else 0) / M.partition := by
  rw [mallowsTopTwoPairUpProb_eq_weight_div_partition]
  rw [mallowsTopTwoPairUpWeight_eq_rank_sum M fac hi lo]

/-- Normalized rank-kernel form of the two-approval up-event probability. -/
theorem mallowsTopTwoPairUpProb_eq_rank_kernel_div_partition {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization)
    (hi lo : Candidate n) :
    mallowsTopTwoPairUpProb M hi lo =
      ((1 + M.q) * fac.firstSecondTail *
          candidateRankTopTwoPairKernel n M.q
            (rankOf M.center hi) (rankOf M.center lo)) / M.partition := by
  rw [mallowsTopTwoPairUpProb_eq_weight_div_partition]
  rw [mallowsTopTwoPairUpWeight_eq_rank_kernel M fac hi lo]

/--
K=2 approval up-probability under a finite Mallows law, in normalized
rank-sum form.
-/
theorem kApprovalPairUpProb_two_eq_mallows_rank_sum_div_partition {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization)
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairUpProb M.law 2 hi lo =
      (∑ other : Candidate n,
        if other ≠ hi ∧ other ≠ lo then
          (1 + M.q) *
            (M.q ^ ((rankOf M.center hi : ℕ) +
                (rankOf M.center other : ℕ) - 1) *
              fac.firstSecondTail)
        else 0) / M.partition := by
  rw [← mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb M hhi_lo]
  exact mallowsTopTwoPairUpProb_eq_rank_sum_div_partition M fac hi lo

/--
K=2 approval up-probability under a finite Mallows law, in normalized
rank-kernel form.
-/
theorem kApprovalPairUpProb_two_eq_mallows_rank_kernel_div_partition {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization)
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairUpProb M.law 2 hi lo =
      ((1 + M.q) * fac.firstSecondTail *
          candidateRankTopTwoPairKernel n M.q
            (rankOf M.center hi) (rankOf M.center lo)) / M.partition := by
  rw [← mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb M hhi_lo]
  exact mallowsTopTwoPairUpProb_eq_rank_kernel_div_partition M fac hi lo

/--
K=2 approval down-probability under a finite Mallows law, in normalized
rank-sum form.
-/
theorem kApprovalPairDownProb_two_eq_mallows_rank_sum_div_partition {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization)
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairDownProb M.law 2 hi lo =
      (∑ other : Candidate n,
        if other ≠ lo ∧ other ≠ hi then
          (1 + M.q) *
            (M.q ^ ((rankOf M.center lo : ℕ) +
                (rankOf M.center other : ℕ) - 1) *
              fac.firstSecondTail)
        else 0) / M.partition := by
  rw [kApprovalPairDownProb_eq_pairUpProb_swap]
  exact kApprovalPairUpProb_two_eq_mallows_rank_sum_div_partition
    M fac (Ne.symm hhi_lo)

/--
K=2 approval down-probability under a finite Mallows law, in normalized
rank-kernel form.
-/
theorem kApprovalPairDownProb_two_eq_mallows_rank_kernel_div_partition {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization)
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairDownProb M.law 2 hi lo =
      ((1 + M.q) * fac.firstSecondTail *
          candidateRankTopTwoPairKernel n M.q
            (rankOf M.center lo) (rankOf M.center hi)) / M.partition := by
  rw [kApprovalPairDownProb_eq_pairUpProb_swap]
  exact kApprovalPairUpProb_two_eq_mallows_rank_kernel_div_partition
    M fac (Ne.symm hhi_lo)

theorem kApprovalPairUpProb_two_pos {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization) (hn : 0 < n)
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    0 < kApprovalPairUpProb M.law 2 hi lo := by
  rw [kApprovalPairUpProb_two_eq_mallows_rank_kernel_div_partition
    M fac hhi_lo]
  refine div_pos ?_ M.partition_pos
  refine mul_pos ?_ (candidateRankTopTwoPairKernel_pos n M.q_pos hn _ _)
  refine mul_pos ?_ fac.firstSecondTail_pos
  linarith [M.q_pos]

theorem kApprovalPairDownProb_two_pos {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization) (hn : 0 < n)
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    0 < kApprovalPairDownProb M.law 2 hi lo := by
  rw [kApprovalPairDownProb_eq_pairUpProb_swap]
  exact kApprovalPairUpProb_two_pos M fac hn (Ne.symm hhi_lo)

theorem kApprovalPairDownProb_two_le_up_of_rank_le {n : ℕ}
    (M : MallowsSpec n) (fac : M.RankFactorization) (hq_le : M.q ≤ 1)
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo)
    (hrank : rankOf M.center hi ≤ rankOf M.center lo) :
    kApprovalPairDownProb M.law 2 hi lo ≤
      kApprovalPairUpProb M.law 2 hi lo := by
  rw [kApprovalPairDownProb_two_eq_mallows_rank_sum_div_partition M fac hhi_lo,
    kApprovalPairUpProb_two_eq_mallows_rank_sum_div_partition M fac hhi_lo]
  refine div_le_div_of_nonneg_right ?_ (le_of_lt M.partition_pos)
  refine Finset.sum_le_sum ?_
  intro other _
  have hswap :
      (other ≠ lo ∧ other ≠ hi) ↔ (other ≠ hi ∧ other ≠ lo) := by
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩
  by_cases hother : other ≠ hi ∧ other ≠ lo
  · have hpow :
        M.q ^ ((rankOf M.center lo : ℕ) +
            (rankOf M.center other : ℕ) - 1) ≤
          M.q ^ ((rankOf M.center hi : ℕ) +
            (rankOf M.center other : ℕ) - 1) := by
      exact pow_le_pow_of_le_one M.q_pos.le hq_le (by
        have hrank_nat :
            (rankOf M.center hi : ℕ) ≤
              (rankOf M.center lo : ℕ) := hrank
        omega)
    have hinner :
        M.q ^ ((rankOf M.center lo : ℕ) +
            (rankOf M.center other : ℕ) - 1) *
            fac.firstSecondTail ≤
          M.q ^ ((rankOf M.center hi : ℕ) +
            (rankOf M.center other : ℕ) - 1) *
            fac.firstSecondTail :=
      mul_le_mul_of_nonneg_right hpow (le_of_lt fac.firstSecondTail_pos)
    have hconst : 0 ≤ 1 + M.q := by linarith [M.q_pos]
    simpa [hother, hswap] using mul_le_mul_of_nonneg_left hinner hconst
  · simp [hother, hswap]

/--
For a four-candidate Mallows law centered at the identity ranking, the `K = 2`
approval up-event weight for the center ranks `(2, 3)` is
`q + 2 q^2 + q^3`, times the common top-two tail.
-/
theorem mallowsTopTwoPairUpWeight_23_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (fac : M.RankFactorization) :
    mallowsTopTwoPairUpWeight M (2 : Candidate 2) (3 : Candidate 2) =
      (M.q + 2 * M.q ^ 2 + M.q ^ 3) * fac.firstSecondTail := by
  have h02 :
      rankOf M.center (0 : Candidate 2) <
        rankOf M.center (2 : Candidate 2) := by
    rw [hcenter]
    decide
  have h12 :
      rankOf M.center (1 : Candidate 2) <
        rankOf M.center (2 : Candidate 2) := by
    rw [hcenter]
    decide
  have w20 :
      M.firstSecondWeight (2 : Candidate 2) (0 : Candidate 2) =
        M.q ^ 2 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_swap_eq_of_lt
        (0 : Candidate 2) (2 : Candidate 2) h02
    calc
      M.firstSecondWeight (2 : Candidate 2) (0 : Candidate 2)
          = M.q * (M.q * fac.firstSecondTail) := by
            simpa [hcenter, rankOf] using h
      _ = M.q ^ 2 * fac.firstSecondTail := by ring
  have w02 :
      M.firstSecondWeight (0 : Candidate 2) (2 : Candidate 2) =
        M.q * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_eq_of_lt
        (0 : Candidate 2) (2 : Candidate 2) h02
    simpa [hcenter, rankOf] using h
  have w21 :
      M.firstSecondWeight (2 : Candidate 2) (1 : Candidate 2) =
        M.q ^ 3 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_swap_eq_of_lt
        (1 : Candidate 2) (2 : Candidate 2) h12
    calc
      M.firstSecondWeight (2 : Candidate 2) (1 : Candidate 2)
          = M.q * (M.q ^ 2 * fac.firstSecondTail) := by
            simpa [hcenter, rankOf] using h
      _ = M.q ^ 3 * fac.firstSecondTail := by ring
  have w12 :
      M.firstSecondWeight (1 : Candidate 2) (2 : Candidate 2) =
        M.q ^ 2 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_eq_of_lt
        (1 : Candidate 2) (2 : Candidate 2) h12
    simpa [hcenter, rankOf] using h
  unfold mallowsTopTwoPairUpWeight
  rw [Fin.sum_univ_four]
  simp [w20, w02, w21, w12]
  ring_nf

/--
For the reverse ordered pair, the corresponding `K = 2` approval up-event
weight is `q^2 + 2 q^3 + q^4`, times the common top-two tail.
-/
theorem mallowsTopTwoPairUpWeight_32_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (fac : M.RankFactorization) :
    mallowsTopTwoPairUpWeight M (3 : Candidate 2) (2 : Candidate 2) =
      (M.q ^ 2 + 2 * M.q ^ 3 + M.q ^ 4) * fac.firstSecondTail := by
  have h03 :
      rankOf M.center (0 : Candidate 2) <
        rankOf M.center (3 : Candidate 2) := by
    rw [hcenter]
    decide
  have h13 :
      rankOf M.center (1 : Candidate 2) <
        rankOf M.center (3 : Candidate 2) := by
    rw [hcenter]
    decide
  have w30 :
      M.firstSecondWeight (3 : Candidate 2) (0 : Candidate 2) =
        M.q ^ 3 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_swap_eq_of_lt
        (0 : Candidate 2) (3 : Candidate 2) h03
    calc
      M.firstSecondWeight (3 : Candidate 2) (0 : Candidate 2)
          = M.q * (M.q ^ 2 * fac.firstSecondTail) := by
            simpa [hcenter, rankOf] using h
      _ = M.q ^ 3 * fac.firstSecondTail := by ring
  have w03 :
      M.firstSecondWeight (0 : Candidate 2) (3 : Candidate 2) =
        M.q ^ 2 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_eq_of_lt
        (0 : Candidate 2) (3 : Candidate 2) h03
    simpa [hcenter, rankOf] using h
  have w31 :
      M.firstSecondWeight (3 : Candidate 2) (1 : Candidate 2) =
        M.q ^ 4 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_swap_eq_of_lt
        (1 : Candidate 2) (3 : Candidate 2) h13
    calc
      M.firstSecondWeight (3 : Candidate 2) (1 : Candidate 2)
          = M.q * (M.q ^ 3 * fac.firstSecondTail) := by
            simpa [hcenter, rankOf] using h
      _ = M.q ^ 4 * fac.firstSecondTail := by ring
  have w13 :
      M.firstSecondWeight (1 : Candidate 2) (3 : Candidate 2) =
        M.q ^ 3 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_eq_of_lt
        (1 : Candidate 2) (3 : Candidate 2) h13
    simpa [hcenter, rankOf] using h
  unfold mallowsTopTwoPairUpWeight
  rw [Fin.sum_univ_four]
  simp [w30, w03, w31, w13]
  ring_nf

/-- The `K = 2` approval up-event weight for center ranks `(0, 3)`. -/
theorem mallowsTopTwoPairUpWeight_03_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (fac : M.RankFactorization) :
    mallowsTopTwoPairUpWeight M (0 : Candidate 2) (3 : Candidate 2) =
      (1 + 2 * M.q + M.q ^ 2) * fac.firstSecondTail := by
  have h01 :
      rankOf M.center (0 : Candidate 2) <
        rankOf M.center (1 : Candidate 2) := by
    rw [hcenter]
    decide
  have h02 :
      rankOf M.center (0 : Candidate 2) <
        rankOf M.center (2 : Candidate 2) := by
    rw [hcenter]
    decide
  have w01 :
      M.firstSecondWeight (0 : Candidate 2) (1 : Candidate 2) =
        fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_eq_of_lt
        (0 : Candidate 2) (1 : Candidate 2) h01
    simpa [hcenter, rankOf] using h
  have w10 :
      M.firstSecondWeight (1 : Candidate 2) (0 : Candidate 2) =
        M.q * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_swap_eq_of_lt
        (0 : Candidate 2) (1 : Candidate 2) h01
    simpa [hcenter, rankOf] using h
  have w02 :
      M.firstSecondWeight (0 : Candidate 2) (2 : Candidate 2) =
        M.q * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_eq_of_lt
        (0 : Candidate 2) (2 : Candidate 2) h02
    simpa [hcenter, rankOf] using h
  have w20 :
      M.firstSecondWeight (2 : Candidate 2) (0 : Candidate 2) =
        M.q ^ 2 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_swap_eq_of_lt
        (0 : Candidate 2) (2 : Candidate 2) h02
    calc
      M.firstSecondWeight (2 : Candidate 2) (0 : Candidate 2)
          = M.q * (M.q * fac.firstSecondTail) := by
            simpa [hcenter, rankOf] using h
      _ = M.q ^ 2 * fac.firstSecondTail := by ring
  unfold mallowsTopTwoPairUpWeight
  rw [Fin.sum_univ_four]
  simp [w01, w10, w02, w20]
  ring_nf

/-- The reverse `K = 2` approval up-event weight for center ranks `(3, 0)`. -/
theorem mallowsTopTwoPairUpWeight_30_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (fac : M.RankFactorization) :
    mallowsTopTwoPairUpWeight M (3 : Candidate 2) (0 : Candidate 2) =
      (M.q ^ 3 + 2 * M.q ^ 4 + M.q ^ 5) * fac.firstSecondTail := by
  have h13 :
      rankOf M.center (1 : Candidate 2) <
        rankOf M.center (3 : Candidate 2) := by
    rw [hcenter]
    decide
  have h23 :
      rankOf M.center (2 : Candidate 2) <
        rankOf M.center (3 : Candidate 2) := by
    rw [hcenter]
    decide
  have w31 :
      M.firstSecondWeight (3 : Candidate 2) (1 : Candidate 2) =
        M.q ^ 4 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_swap_eq_of_lt
        (1 : Candidate 2) (3 : Candidate 2) h13
    calc
      M.firstSecondWeight (3 : Candidate 2) (1 : Candidate 2)
          = M.q * (M.q ^ 3 * fac.firstSecondTail) := by
            simpa [hcenter, rankOf] using h
      _ = M.q ^ 4 * fac.firstSecondTail := by ring
  have w13 :
      M.firstSecondWeight (1 : Candidate 2) (3 : Candidate 2) =
        M.q ^ 3 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_eq_of_lt
        (1 : Candidate 2) (3 : Candidate 2) h13
    simpa [hcenter, rankOf] using h
  have w32 :
      M.firstSecondWeight (3 : Candidate 2) (2 : Candidate 2) =
        M.q ^ 5 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_swap_eq_of_lt
        (2 : Candidate 2) (3 : Candidate 2) h23
    calc
      M.firstSecondWeight (3 : Candidate 2) (2 : Candidate 2)
          = M.q * (M.q ^ 4 * fac.firstSecondTail) := by
            simpa [hcenter, rankOf] using h
      _ = M.q ^ 5 * fac.firstSecondTail := by ring
  have w23 :
      M.firstSecondWeight (2 : Candidate 2) (3 : Candidate 2) =
        M.q ^ 4 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_eq_of_lt
        (2 : Candidate 2) (3 : Candidate 2) h23
    simpa [hcenter, rankOf] using h
  unfold mallowsTopTwoPairUpWeight
  rw [Fin.sum_univ_four]
  simp [w31, w13, w32, w23]
  ring_nf

/-- The `K = 2` approval up-event weight for center ranks `(1, 3)`. -/
theorem mallowsTopTwoPairUpWeight_13_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (fac : M.RankFactorization) :
    mallowsTopTwoPairUpWeight M (1 : Candidate 2) (3 : Candidate 2) =
      (1 + M.q + M.q ^ 2 + M.q ^ 3) * fac.firstSecondTail := by
  have h01 :
      rankOf M.center (0 : Candidate 2) <
        rankOf M.center (1 : Candidate 2) := by
    rw [hcenter]
    decide
  have h12 :
      rankOf M.center (1 : Candidate 2) <
        rankOf M.center (2 : Candidate 2) := by
    rw [hcenter]
    decide
  have w10 :
      M.firstSecondWeight (1 : Candidate 2) (0 : Candidate 2) =
        M.q * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_swap_eq_of_lt
        (0 : Candidate 2) (1 : Candidate 2) h01
    simpa [hcenter, rankOf] using h
  have w01 :
      M.firstSecondWeight (0 : Candidate 2) (1 : Candidate 2) =
        fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_eq_of_lt
        (0 : Candidate 2) (1 : Candidate 2) h01
    simpa [hcenter, rankOf] using h
  have w12 :
      M.firstSecondWeight (1 : Candidate 2) (2 : Candidate 2) =
        M.q ^ 2 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_eq_of_lt
        (1 : Candidate 2) (2 : Candidate 2) h12
    simpa [hcenter, rankOf] using h
  have w21 :
      M.firstSecondWeight (2 : Candidate 2) (1 : Candidate 2) =
        M.q ^ 3 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_swap_eq_of_lt
        (1 : Candidate 2) (2 : Candidate 2) h12
    calc
      M.firstSecondWeight (2 : Candidate 2) (1 : Candidate 2)
          = M.q * (M.q ^ 2 * fac.firstSecondTail) := by
            simpa [hcenter, rankOf] using h
      _ = M.q ^ 3 * fac.firstSecondTail := by ring
  unfold mallowsTopTwoPairUpWeight
  rw [Fin.sum_univ_four]
  simp [w10, w01, w12, w21]
  ring_nf

/-- The reverse `K = 2` approval up-event weight for center ranks `(3, 1)`. -/
theorem mallowsTopTwoPairUpWeight_31_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (fac : M.RankFactorization) :
    mallowsTopTwoPairUpWeight M (3 : Candidate 2) (1 : Candidate 2) =
      (M.q ^ 2 + M.q ^ 3 + M.q ^ 4 + M.q ^ 5) *
        fac.firstSecondTail := by
  have h03 :
      rankOf M.center (0 : Candidate 2) <
        rankOf M.center (3 : Candidate 2) := by
    rw [hcenter]
    decide
  have h23 :
      rankOf M.center (2 : Candidate 2) <
        rankOf M.center (3 : Candidate 2) := by
    rw [hcenter]
    decide
  have w30 :
      M.firstSecondWeight (3 : Candidate 2) (0 : Candidate 2) =
        M.q ^ 3 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_swap_eq_of_lt
        (0 : Candidate 2) (3 : Candidate 2) h03
    calc
      M.firstSecondWeight (3 : Candidate 2) (0 : Candidate 2)
          = M.q * (M.q ^ 2 * fac.firstSecondTail) := by
            simpa [hcenter, rankOf] using h
      _ = M.q ^ 3 * fac.firstSecondTail := by ring
  have w03 :
      M.firstSecondWeight (0 : Candidate 2) (3 : Candidate 2) =
        M.q ^ 2 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_eq_of_lt
        (0 : Candidate 2) (3 : Candidate 2) h03
    simpa [hcenter, rankOf] using h
  have w32 :
      M.firstSecondWeight (3 : Candidate 2) (2 : Candidate 2) =
        M.q ^ 5 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_swap_eq_of_lt
        (2 : Candidate 2) (3 : Candidate 2) h23
    calc
      M.firstSecondWeight (3 : Candidate 2) (2 : Candidate 2)
          = M.q * (M.q ^ 4 * fac.firstSecondTail) := by
            simpa [hcenter, rankOf] using h
      _ = M.q ^ 5 * fac.firstSecondTail := by ring
  have w23 :
      M.firstSecondWeight (2 : Candidate 2) (3 : Candidate 2) =
        M.q ^ 4 * fac.firstSecondTail := by
    have h :=
      fac.firstSecondWeight_eq_of_lt
        (2 : Candidate 2) (3 : Candidate 2) h23
    simpa [hcenter, rankOf] using h
  unfold mallowsTopTwoPairUpWeight
  rw [Fin.sum_univ_four]
  simp [w30, w03, w32, w23]
  ring_nf

/-- The four-candidate rank-factorized Mallows partition in the paper's notation. -/
theorem mallowsRankFactorization_partition_eq_w3
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (fac : M.RankFactorization) :
    M.partition =
      mallowsW3N4 M.q * (fac.firstSecondTail * mallowsW3N3 M.q) := by
  have hfirst :
      fac.firstTail = fac.firstSecondTail * mallowsW3N3 M.q := by
    have h :=
      M.firstTail_eq_firstSecondTail_mul_removalPowerSum
        fac (2 : Candidate 2)
    rw [hcenter] at h
    norm_num [rankOf, candidateRankRemovalPowerSum_eq_range,
      mallowsW3N3, Finset.sum_range_succ] at h
    exact h
  rw [fac.partition_eq, hfirst]
  norm_num [candidateRankPowerSum, AppliedModelingLib.SocialChoice.Ranking.Candidate,
    mallowsW3N4, Fin.sum_univ_eq_sum_range, Finset.sum_range_succ]

private theorem mallowsW3N3_ne_zero_of_mallows (M : MallowsSpec 2) :
    mallowsW3N3 M.q ≠ 0 := by
  have hpos : 0 < mallowsW3N3 M.q := by
    have hq2 : 0 ≤ M.q ^ 2 := sq_nonneg M.q
    unfold mallowsW3N3
    nlinarith [M.q_pos]
  exact ne_of_gt hpos

private theorem mallowsW3N4_ne_zero_of_mallows (M : MallowsSpec 2) :
    mallowsW3N4 M.q ≠ 0 := by
  have hpos : 0 < mallowsW3N4 M.q := by
    have hq2 : 0 ≤ M.q ^ 2 := sq_nonneg M.q
    have hq3 : 0 ≤ M.q ^ 3 := pow_nonneg (le_of_lt M.q_pos) 3
    unfold mallowsW3N4
    nlinarith [M.q_pos]
  exact ne_of_gt hpos

theorem mallowsTopTwoPairUpProb_03_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopTwoPairUpProb M (0 : Candidate 2) (3 : Candidate 2) =
      (1 + 2 * M.q + M.q ^ 2) / (mallowsW3N3 M.q * mallowsW3N4 M.q) := by
  let fac : M.RankFactorization := M.rankFactorization
  rw [mallowsTopTwoPairUpProb_eq_weight_div_partition,
    mallowsTopTwoPairUpWeight_03_eq M hcenter fac,
    mallowsRankFactorization_partition_eq_w3 M hcenter fac]
  have htail : fac.firstSecondTail ≠ 0 := ne_of_gt fac.firstSecondTail_pos
  have hN3 : mallowsW3N3 M.q ≠ 0 := mallowsW3N3_ne_zero_of_mallows M
  have hN4 : mallowsW3N4 M.q ≠ 0 := mallowsW3N4_ne_zero_of_mallows M
  field_simp [mallowsW3N3, mallowsW3N4, htail, hN3, hN4]

theorem mallowsTopTwoPairUpProb_03_eq_mallowsW3K2Up0
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopTwoPairUpProb M (0 : Candidate 2) (3 : Candidate 2) =
      mallowsW3K2Up0 M.q := by
  simpa [mallowsW3K2Up0] using mallowsTopTwoPairUpProb_03_eq M hcenter

theorem mallowsTopTwoPairUpProb_30_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopTwoPairUpProb M (3 : Candidate 2) (0 : Candidate 2) =
      (M.q ^ 3 + 2 * M.q ^ 4 + M.q ^ 5) /
        (mallowsW3N3 M.q * mallowsW3N4 M.q) := by
  let fac : M.RankFactorization := M.rankFactorization
  rw [mallowsTopTwoPairUpProb_eq_weight_div_partition,
    mallowsTopTwoPairUpWeight_30_eq M hcenter fac,
    mallowsRankFactorization_partition_eq_w3 M hcenter fac]
  have htail : fac.firstSecondTail ≠ 0 := ne_of_gt fac.firstSecondTail_pos
  have hN3 : mallowsW3N3 M.q ≠ 0 := mallowsW3N3_ne_zero_of_mallows M
  have hN4 : mallowsW3N4 M.q ≠ 0 := mallowsW3N4_ne_zero_of_mallows M
  field_simp [mallowsW3N3, mallowsW3N4, htail, hN3, hN4]

theorem mallowsTopTwoPairUpProb_30_eq_mallowsW3K2Down0
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopTwoPairUpProb M (3 : Candidate 2) (0 : Candidate 2) =
      mallowsW3K2Down0 M.q := by
  simpa [mallowsW3K2Down0] using mallowsTopTwoPairUpProb_30_eq M hcenter

theorem mallowsTopTwoPairUpProb_13_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopTwoPairUpProb M (1 : Candidate 2) (3 : Candidate 2) =
      (1 + M.q + M.q ^ 2 + M.q ^ 3) /
        (mallowsW3N3 M.q * mallowsW3N4 M.q) := by
  let fac : M.RankFactorization := M.rankFactorization
  rw [mallowsTopTwoPairUpProb_eq_weight_div_partition,
    mallowsTopTwoPairUpWeight_13_eq M hcenter fac,
    mallowsRankFactorization_partition_eq_w3 M hcenter fac]
  have htail : fac.firstSecondTail ≠ 0 := ne_of_gt fac.firstSecondTail_pos
  have hN3 : mallowsW3N3 M.q ≠ 0 := mallowsW3N3_ne_zero_of_mallows M
  have hN4 : mallowsW3N4 M.q ≠ 0 := mallowsW3N4_ne_zero_of_mallows M
  field_simp [mallowsW3N3, mallowsW3N4, htail, hN3, hN4]

theorem mallowsTopTwoPairUpProb_13_eq_mallowsW3K2Up1
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopTwoPairUpProb M (1 : Candidate 2) (3 : Candidate 2) =
      mallowsW3K2Up1 M.q := by
  simpa [mallowsW3K2Up1] using mallowsTopTwoPairUpProb_13_eq M hcenter

theorem mallowsTopTwoPairUpProb_31_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopTwoPairUpProb M (3 : Candidate 2) (1 : Candidate 2) =
      (M.q ^ 2 + M.q ^ 3 + M.q ^ 4 + M.q ^ 5) /
        (mallowsW3N3 M.q * mallowsW3N4 M.q) := by
  let fac : M.RankFactorization := M.rankFactorization
  rw [mallowsTopTwoPairUpProb_eq_weight_div_partition,
    mallowsTopTwoPairUpWeight_31_eq M hcenter fac,
    mallowsRankFactorization_partition_eq_w3 M hcenter fac]
  have htail : fac.firstSecondTail ≠ 0 := ne_of_gt fac.firstSecondTail_pos
  have hN3 : mallowsW3N3 M.q ≠ 0 := mallowsW3N3_ne_zero_of_mallows M
  have hN4 : mallowsW3N4 M.q ≠ 0 := mallowsW3N4_ne_zero_of_mallows M
  field_simp [mallowsW3N3, mallowsW3N4, htail, hN3, hN4]

theorem mallowsTopTwoPairUpProb_31_eq_mallowsW3K2Down1
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopTwoPairUpProb M (3 : Candidate 2) (1 : Candidate 2) =
      mallowsW3K2Down1 M.q := by
  simpa [mallowsW3K2Down1] using mallowsTopTwoPairUpProb_31_eq M hcenter

/--
The paper's source formula for `t^3_34(2)` follows from the reusable
canonical rank-factorization theorem.
-/
theorem mallowsTopTwoPairUpProb_23_eq_mallowsW3K2Up
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopTwoPairUpProb M (2 : Candidate 2) (3 : Candidate 2) =
      mallowsW3K2Up M.q := by
  let fac : M.RankFactorization := M.rankFactorization
  rw [mallowsTopTwoPairUpProb_eq_weight_div_partition,
    mallowsTopTwoPairUpWeight_23_eq M hcenter fac,
    mallowsRankFactorization_partition_eq_w3 M hcenter fac,
    mallowsW3K2Up]
  have htail : fac.firstSecondTail ≠ 0 := ne_of_gt fac.firstSecondTail_pos
  have hN3 : mallowsW3N3 M.q ≠ 0 := mallowsW3N3_ne_zero_of_mallows M
  have hN4 : mallowsW3N4 M.q ≠ 0 := mallowsW3N4_ne_zero_of_mallows M
  field_simp [mallowsW3N3, mallowsW3N4, htail, hN3, hN4]

/--
The paper's source formula for `t^4_34(2)` follows from the reusable
canonical rank-factorization theorem.
-/
theorem mallowsTopTwoPairUpProb_32_eq_mallowsW3K2Down
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopTwoPairUpProb M (3 : Candidate 2) (2 : Candidate 2) =
      mallowsW3K2Down M.q := by
  let fac : M.RankFactorization := M.rankFactorization
  rw [mallowsTopTwoPairUpProb_eq_weight_div_partition,
    mallowsTopTwoPairUpWeight_32_eq M hcenter fac,
    mallowsRankFactorization_partition_eq_w3 M hcenter fac,
    mallowsW3K2Down]
  have htail : fac.firstSecondTail ≠ 0 := ne_of_gt fac.firstSecondTail_pos
  have hN3 : mallowsW3N3 M.q ≠ 0 := mallowsW3N3_ne_zero_of_mallows M
  have hN4 : mallowsW3N4 M.q ≠ 0 := mallowsW3N4_ne_zero_of_mallows M
  field_simp [mallowsW3N3, mallowsW3N4, htail, hN3, hN4]

/-! ## K = 3 / last-position approval probabilities -/

/-- Reverse the positions of a four-candidate ranking. -/
def reversePositions (π : Ranking 2) : Ranking 2 :=
  (Fin.revPerm : Equiv.Perm (Candidate 2)).trans π

private def reversePositionsEquiv : Ranking 2 ≃ Ranking 2 where
  toFun := reversePositions
  invFun := reversePositions
  left_inv π := by
    ext i
    simp [reversePositions]
  right_inv π := by
    ext i
    simp [reversePositions]

@[simp] theorem reversePositions_apply_zero (π : Ranking 2) :
    reversePositions π 0 = π 3 := by
  simp [reversePositions, Candidate]

@[simp] theorem reversePositions_apply_three (π : Ranking 2) :
    reversePositions π 3 = π 0 := by
  simp [reversePositions, Candidate]

@[simp] theorem firstChoice_reversePositions (π : Ranking 2) :
    firstChoice (reversePositions π) = π 3 := by
  simp [firstChoice]

private theorem invertedPair_revPerm_iff_refl_reversePositions
    (π : Ranking 2) (ab : Candidate 2 × Candidate 2) :
    invertedPair (Fin.revPerm : Ranking 2) π ab ↔
      invertedPair (Equiv.refl (Candidate 2)) (reversePositions π) (ab.2, ab.1) := by
  unfold invertedPair reversePositions rankOf Candidate
  simp

private theorem kendallTau_refl_reversePositions_eq_revPerm
    (π : Ranking 2) :
    kendallTau (Equiv.refl (Candidate 2)) (reversePositions π) =
      kendallTau (Fin.revPerm : Ranking 2) π := by
  classical
  unfold kendallTau
  refine (Finset.card_bij
    (s := inversionFinset (Fin.revPerm : Ranking 2) π)
    (t := inversionFinset (Equiv.refl (Candidate 2)) (reversePositions π))
    (i := fun ab _ => (ab.2, ab.1)) ?hi ?hinj ?hsurj).symm
  · intro ab hab
    have hinv :
        invertedPair (Fin.revPerm : Ranking 2) π ab := by
      simpa [inversionFinset] using hab
    have hinv' :
        invertedPair (Equiv.refl (Candidate 2)) (reversePositions π)
          (ab.2, ab.1) :=
      (invertedPair_revPerm_iff_refl_reversePositions π ab).1 hinv
    simpa [inversionFinset] using hinv'
  · intro ab _ cd _ h
    exact Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1
  · intro ab hab
    have hinv :
        invertedPair (Equiv.refl (Candidate 2)) (reversePositions π) ab := by
      simpa [inversionFinset] using hab
    let pre : Candidate 2 × Candidate 2 := (ab.2, ab.1)
    have hinvPre :
        invertedPair (Fin.revPerm : Ranking 2) π pre := by
      exact
        (invertedPair_revPerm_iff_refl_reversePositions π pre).2
          (by simpa [pre] using hinv)
    refine ⟨pre, ?_, ?_⟩
    · simpa [inversionFinset] using hinvPre
    · simp [pre]

/-- In the four-candidate source example, the last-ranked candidate. -/
def mallowsLastChoice (π : Ranking 2) : Candidate 2 :=
  π 3

/-- Unnormalised Mallows mass of rankings where `c` is last. -/
def mallowsLastWeight (M : MallowsSpec 2) (c : Candidate 2) : ℝ :=
  ∑ π : Ranking 2,
    if c = mallowsLastChoice π then mallowsWeight M.q M.center π else 0

private theorem mallowsLastWeight_eq_firstWeightKernel_revPerm
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (c : Candidate 2) :
    mallowsLastWeight M c =
      MallowsSpec.firstWeightKernel M.q (Fin.revPerm : Ranking 2) c := by
  classical
  unfold mallowsLastWeight MallowsSpec.firstWeightKernel mallowsLastChoice
  calc
    (∑ π : Ranking 2,
        if c = π 3
        then mallowsWeight M.q M.center π
        else 0)
        =
      ∑ π : Ranking 2,
        if c = π 3
        then mallowsWeight M.q (Equiv.refl (Candidate 2)) π
        else 0 := by
          rw [hcenter]
    _ =
      ∑ σ : Ranking 2,
        if c = reversePositions σ 3
        then mallowsWeight M.q (Equiv.refl (Candidate 2)) (reversePositions σ)
        else 0 := by
          simpa using
            (Equiv.sum_comp reversePositionsEquiv
              (fun π : Ranking 2 =>
                if c = π 3
                then mallowsWeight M.q (Equiv.refl (Candidate 2)) π
                else 0)).symm
    _ =
      ∑ σ : Ranking 2,
        if c = firstChoice σ
        then mallowsWeight M.q (Fin.revPerm : Ranking 2) σ
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          have hkendall :
              kendallTau (Equiv.refl (Candidate 2)) (reversePositions σ) =
                kendallTau (Fin.revPerm : Ranking 2) σ :=
            kendallTau_refl_reversePositions_eq_revPerm σ
          by_cases hσ : c = firstChoice σ
          · rw [if_pos (by simpa [firstChoice] using hσ), if_pos hσ]
            simp [mallowsWeight, hkendall]
          · rw [if_neg (by
              intro h
              exact hσ (by simpa [firstChoice] using h)), if_neg hσ]

private theorem mallowsLastWeight_eq_reverse_rank_pow_tail
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (c : Candidate 2) :
    mallowsLastWeight M c =
      M.q ^ (rankOf (Fin.revPerm : Ranking 2) c : ℕ) *
        MallowsSpec.firstTailKernel 2 M.q := by
  rw [mallowsLastWeight_eq_firstWeightKernel_revPerm M hcenter c]
  exact
    MallowsSpec.firstWeightKernel_eq_rank_pow_mul_firstTailKernel
      M.q_pos (Fin.revPerm : Ranking 2) c

private theorem mallows_partition_eq_w3_firstTailKernel
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    M.partition =
      mallowsW3N4 M.q * MallowsSpec.firstTailKernel 2 M.q := by
  rw [M.partition_eq_sum, hcenter]
  rw [MallowsSpec.mallowsPartition_eq_rankPowerSum_mul_firstTailKernel
    M.q_pos (Equiv.refl (Candidate 2))]
  norm_num [candidateRankPowerSum, mallowsW3N4, Fin.sum_univ_eq_sum_range,
    Finset.sum_range_succ]

/--
Four-candidate first-choice probabilities under an identity-centered Mallows
law have the usual normalized geometric rank weights.
-/
theorem mallowsFirstChoiceProb_eq_rank_pow_div_w3N4
    (M : MallowsSpec 2) (c : Candidate 2) :
    firstChoiceProb M.law c =
      M.q ^ (rankOf M.center c : ℕ) / mallowsW3N4 M.q := by
  rw [M.firstChoiceProb_eq_firstWeight_div_partition]
  rw [M.firstWeight_eq_rank_pow_mul_firstTailCanonical c,
    M.partition_eq_rankPowerSum_mul_firstTailCanonical]
  have htail : M.firstTailCanonical ≠ 0 :=
    ne_of_gt M.firstTailCanonical_pos
  have hN4 : mallowsW3N4 M.q ≠ 0 :=
    mallowsW3N4_ne_zero_of_mallows M
  have hsum : candidateRankPowerSum 2 M.q = mallowsW3N4 M.q := by
    norm_num [candidateRankPowerSum, mallowsW3N4,
      Fin.sum_univ_eq_sum_range, Finset.sum_range_succ]
  field_simp [htail, hN4]
  rw [hsum]
  field_simp [hN4]

/-- In the source four-candidate Mallows example, candidate `0` is first with mass `1/N4`. -/
theorem mallowsFirstChoiceProb_0_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    firstChoiceProb M.law (0 : Candidate 2) =
      1 / mallowsW3N4 M.q := by
  rw [mallowsFirstChoiceProb_eq_rank_pow_div_w3N4 M, hcenter]
  norm_num [rankOf]

/-- In the source four-candidate Mallows example, candidate `1` is first with mass `q/N4`. -/
theorem mallowsFirstChoiceProb_1_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    firstChoiceProb M.law (1 : Candidate 2) =
      M.q / mallowsW3N4 M.q := by
  rw [mallowsFirstChoiceProb_eq_rank_pow_div_w3N4 M, hcenter]
  norm_num [rankOf]

/-- In the source four-candidate Mallows example, candidate `2` is first with mass `q^2/N4`. -/
theorem mallowsFirstChoiceProb_2_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    firstChoiceProb M.law (2 : Candidate 2) =
      M.q ^ 2 / mallowsW3N4 M.q := by
  rw [mallowsFirstChoiceProb_eq_rank_pow_div_w3N4 M, hcenter]
  norm_num [rankOf]

/-- In the source four-candidate Mallows example, candidate `3` is first with mass `q^3/N4`. -/
theorem mallowsFirstChoiceProb_3_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    firstChoiceProb M.law (3 : Candidate 2) =
      M.q ^ 3 / mallowsW3N4 M.q := by
  rw [mallowsFirstChoiceProb_eq_rank_pow_div_w3N4 M, hcenter]
  norm_num [rankOf]

/-- Mallows probability that `c` is last. -/
def mallowsLastChoiceProb (M : MallowsSpec 2) (c : Candidate 2) : ℝ :=
  AppliedModelingLib.pmfProb M.law (fun π => c = mallowsLastChoice π)

/-- Last-position probabilities reduce to finite Mallows weights. -/
theorem mallowsLastChoiceProb_eq_lastWeight_div_partition
    (M : MallowsSpec 2) (c : Candidate 2) :
    mallowsLastChoiceProb M c = mallowsLastWeight M c / M.partition := by
  classical
  unfold mallowsLastChoiceProb AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp mallowsLastWeight
  calc
    ∑ π : Ranking 2, (M.law π).toReal *
        (if c = mallowsLastChoice π then (1 : ℝ) else 0)
        = ∑ π : Ranking 2,
            (mallowsWeight M.q M.center π / M.partition) *
              (if c = mallowsLastChoice π then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking 2,
          (if c = mallowsLastChoice π then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = mallowsLastChoice π
          · simp [h]
          · simp [h]
    _ = (∑ π : Ranking 2,
          if c = mallowsLastChoice π then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          rw [Finset.sum_div]

/--
Unnormalised Mallows mass of the `K = 3` approval up-event for an ordered pair:
`hi` is approved by being in the top three, while `lo` is not approved because
it is last.
-/
def mallowsTopThreePairUpWeight
    (M : MallowsSpec 2) (hi lo : Candidate 2) : ℝ :=
  ∑ π : Ranking 2,
    if rankOf π hi < (3 : Candidate 2) ∧ rankOf π lo = (3 : Candidate 2)
    then mallowsWeight M.q M.center π
    else 0

/-- Probability of the `K = 3` approval up-event for an ordered pair. -/
def mallowsTopThreePairUpProb
    (M : MallowsSpec 2) (hi lo : Candidate 2) : ℝ :=
  AppliedModelingLib.pmfProb M.law
    (fun π =>
      rankOf π hi < (3 : Candidate 2) ∧ rankOf π lo = (3 : Candidate 2))

/-- The top-three approval probability is its unnormalised weight divided by `Z`. -/
theorem mallowsTopThreePairUpProb_eq_weight_div_partition
    (M : MallowsSpec 2) (hi lo : Candidate 2) :
    mallowsTopThreePairUpProb M hi lo =
      mallowsTopThreePairUpWeight M hi lo / M.partition := by
  classical
  unfold mallowsTopThreePairUpProb AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp
    mallowsTopThreePairUpWeight
  calc
    ∑ π : Ranking 2, (M.law π).toReal *
        (if rankOf π hi < (3 : Candidate 2) ∧
            rankOf π lo = (3 : Candidate 2) then (1 : ℝ) else 0)
        = ∑ π : Ranking 2,
            (mallowsWeight M.q M.center π / M.partition) *
              (if rankOf π hi < (3 : Candidate 2) ∧
                  rankOf π lo = (3 : Candidate 2) then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking 2,
          (if rankOf π hi < (3 : Candidate 2) ∧
              rankOf π lo = (3 : Candidate 2)
            then mallowsWeight M.q M.center π else 0) / M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h :
              rankOf π hi < (3 : Candidate 2) ∧
                rankOf π lo = (3 : Candidate 2)
          · simp [h]
          · simp [h]
    _ = (∑ π : Ranking 2,
          if rankOf π hi < (3 : Candidate 2) ∧
              rankOf π lo = (3 : Candidate 2)
            then mallowsWeight M.q M.center π else 0) / M.partition := by
          rw [Finset.sum_div]

/--
The paper-local `K = 3` up-event is the generic three-approval up-event for
distinct candidates in the four-candidate universe.
-/
theorem mallowsTopThreePairUpProb_eq_kApprovalPairUpProb
    (M : MallowsSpec 2) {hi lo : Candidate 2} (hhi_lo : hi ≠ lo) :
    mallowsTopThreePairUpProb M hi lo =
      kApprovalPairUpProb M.law 3 hi lo := by
  rw [kApprovalPairUpProb_three_eq_rankOf_lastProb M.law hhi_lo]
  unfold mallowsTopThreePairUpProb
  refine (AppliedModelingLib.pmfProb_congr M.law ?_).trans rfl
  intro π
  constructor
  · intro h
    exact h.2
  · intro hlo_last
    constructor
    · have hhi_ne_last : rankOf π hi ≠ (3 : Candidate 2) := by
        intro hhi_last
        have hsame : hi = lo := by
          calc
            hi = π (rankOf π hi) := by simp [rankOf]
            _ = π (rankOf π lo) := by rw [hhi_last, hlo_last]
            _ = lo := by simp [rankOf]
        exact hhi_lo hsame
      change (rankOf π hi).val < 3
      by_contra hnot
      have hval : (rankOf π hi).val = 3 := by
        omega
      exact hhi_ne_last (Fin.ext hval)
    · exact hlo_last

private theorem mallowsTopThreePairUpWeight_eq_lastWeight
    (M : MallowsSpec 2) {hi lo : Candidate 2} (hhi_lo : hi ≠ lo) :
    mallowsTopThreePairUpWeight M hi lo = mallowsLastWeight M lo := by
  classical
  unfold mallowsTopThreePairUpWeight mallowsLastWeight mallowsLastChoice
  refine Finset.sum_congr rfl ?_
  intro π _
  have hlast_iff : rankOf π lo = (3 : Candidate 2) ↔ lo = π 3 := by
    constructor
    · intro h
      have hπ : π (rankOf π lo) = lo := by simp [rankOf]
      simpa [h] using hπ.symm
    · intro h
      apply π.injective
      simpa [rankOf, h]
  by_cases hlo : rankOf π lo = (3 : Candidate 2)
  · have hhi_not_last : rankOf π hi ≠ (3 : Candidate 2) := by
      intro hhi
      have hsame : hi = lo := by
        calc
          hi = π (rankOf π hi) := by simp [rankOf]
          _ = π (rankOf π lo) := by rw [hhi, hlo]
          _ = lo := by simp [rankOf]
      exact hhi_lo hsame
    have hhi_lt : rankOf π hi < (3 : Candidate 2) := by
      change (rankOf π hi).val < 3
      have hle : (rankOf π hi).val ≤ 3 := by omega
      have hne : (rankOf π hi).val ≠ 3 := by
        intro hval
        exact hhi_not_last (Fin.ext hval)
      omega
    rw [if_pos ⟨hhi_lt, hlo⟩, if_pos (hlast_iff.mp hlo)]
  · have hlo_last_ne : lo ≠ π 3 := by
      intro h
      exact hlo (hlast_iff.mpr h)
    rw [if_neg (by intro h; exact hlo h.2), if_neg hlo_last_ne]

/--
For `K = 3` in a four-candidate Mallows law, the approval up-event for
`(hi, lo)` is exactly the event that `lo` is last.  Under an identity center,
its probability is the reversed-center first-choice rank factor divided by the
four-candidate partition factor.
-/
theorem mallowsTopThreePairUpProb_eq_reverse_rank_div_w3N4
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    {hi lo : Candidate 2} (hhi_lo : hi ≠ lo) :
    mallowsTopThreePairUpProb M hi lo =
      M.q ^ (rankOf (Fin.revPerm : Ranking 2) lo : ℕ) / mallowsW3N4 M.q := by
  rw [mallowsTopThreePairUpProb_eq_weight_div_partition,
    mallowsTopThreePairUpWeight_eq_lastWeight M hhi_lo,
    mallowsLastWeight_eq_reverse_rank_pow_tail M hcenter lo,
    mallows_partition_eq_w3_firstTailKernel M hcenter]
  have htail :
      MallowsSpec.firstTailKernel 2 M.q ≠ 0 := by
    exact ne_of_gt (by
      simpa [MallowsSpec.firstTailCanonical] using
        (MallowsSpec.firstTailCanonical_pos M))
  have hN4 : mallowsW3N4 M.q ≠ 0 := mallowsW3N4_ne_zero_of_mallows M
  field_simp [htail, hN4]

theorem mallowsTopThreePairUpProb_03_eq_mallowsW3K3Up
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopThreePairUpProb M (0 : Candidate 2) (3 : Candidate 2) =
      mallowsW3K3Up M.q := by
  have h03 : (0 : Candidate 2) ≠ (3 : Candidate 2) := by decide
  rw [mallowsTopThreePairUpProb_eq_reverse_rank_div_w3N4 M hcenter h03,
    mallowsW3K3Up]
  norm_num [rankOf, Candidate]

theorem mallowsTopThreePairUpProb_30_eq_mallowsW3K3Down0
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopThreePairUpProb M (3 : Candidate 2) (0 : Candidate 2) =
      mallowsW3K3Down0 M.q := by
  have h30 : (3 : Candidate 2) ≠ (0 : Candidate 2) := by decide
  rw [mallowsTopThreePairUpProb_eq_reverse_rank_div_w3N4 M hcenter h30,
    mallowsW3K3Down0]
  norm_num [rankOf, Candidate]

theorem mallowsTopThreePairUpProb_13_eq_mallowsW3K3Up
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopThreePairUpProb M (1 : Candidate 2) (3 : Candidate 2) =
      mallowsW3K3Up M.q := by
  have h13 : (1 : Candidate 2) ≠ (3 : Candidate 2) := by decide
  rw [mallowsTopThreePairUpProb_eq_reverse_rank_div_w3N4 M hcenter h13,
    mallowsW3K3Up]
  norm_num [rankOf, Candidate]

theorem mallowsTopThreePairUpProb_31_eq_mallowsW3K3Down1
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopThreePairUpProb M (3 : Candidate 2) (1 : Candidate 2) =
      mallowsW3K3Down1 M.q := by
  have h31 : (3 : Candidate 2) ≠ (1 : Candidate 2) := by decide
  rw [mallowsTopThreePairUpProb_eq_reverse_rank_div_w3N4 M hcenter h31,
    mallowsW3K3Down1]
  norm_num [rankOf, Candidate]

/-- The paper's source formula for `t^3_34(3)`: candidate 4 is last. -/
theorem mallowsTopThreePairUpProb_23_eq_mallowsW3K3Up
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopThreePairUpProb M (2 : Candidate 2) (3 : Candidate 2) =
      mallowsW3K3Up M.q := by
  have h23 : (2 : Candidate 2) ≠ (3 : Candidate 2) := by decide
  rw [mallowsTopThreePairUpProb_eq_weight_div_partition,
    mallowsTopThreePairUpWeight_eq_lastWeight M h23,
    mallowsLastWeight_eq_reverse_rank_pow_tail M hcenter (3 : Candidate 2),
    mallows_partition_eq_w3_firstTailKernel M hcenter,
    mallowsW3K3Up]
  have htail :
      MallowsSpec.firstTailKernel 2 M.q ≠ 0 := by
    exact ne_of_gt (by
      simpa [MallowsSpec.firstTailCanonical] using
        (MallowsSpec.firstTailCanonical_pos M))
  have hN4 : mallowsW3N4 M.q ≠ 0 := mallowsW3N4_ne_zero_of_mallows M
  norm_num [rankOf, Candidate]
  field_simp [htail, hN4]

/-- The paper's source formula for `t^4_34(3)`: candidate 3 is last. -/
theorem mallowsTopThreePairUpProb_32_eq_mallowsW3K3Down
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopThreePairUpProb M (3 : Candidate 2) (2 : Candidate 2) =
      mallowsW3K3Down M.q := by
  have h32 : (3 : Candidate 2) ≠ (2 : Candidate 2) := by decide
  rw [mallowsTopThreePairUpProb_eq_weight_div_partition,
    mallowsTopThreePairUpWeight_eq_lastWeight M h32,
    mallowsLastWeight_eq_reverse_rank_pow_tail M hcenter (2 : Candidate 2),
    mallows_partition_eq_w3_firstTailKernel M hcenter,
    mallowsW3K3Down]
  have htail :
      MallowsSpec.firstTailKernel 2 M.q ≠ 0 := by
    exact ne_of_gt (by
      simpa [MallowsSpec.firstTailCanonical] using
        (MallowsSpec.firstTailCanonical_pos M))
  have hN4 : mallowsW3N4 M.q ≠ 0 := mallowsW3N4_ne_zero_of_mallows M
  norm_num [rankOf, Candidate]
  field_simp [htail, hN4]

/--
End-to-end high-noise Mallows example for the source pivotal pair: in the
four-candidate identity-centered Mallows law with `q = 4/5`, 2-approval has a
strictly larger pairwise learning rate than 3-approval for candidates `(3,4)`.
-/
theorem mallowsHighNoiseW3K2_rate_gt_K3_rate_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    approvalPairwiseRate
        (mallowsTopThreePairUpProb M (2 : Candidate 2) (3 : Candidate 2))
        (mallowsTopThreePairUpProb M (3 : Candidate 2) (2 : Candidate 2)) <
      approvalPairwiseRate
        (mallowsTopTwoPairUpProb M (2 : Candidate 2) (3 : Candidate 2))
        (mallowsTopTwoPairUpProb M (3 : Candidate 2) (2 : Candidate 2)) := by
  rw [mallowsTopThreePairUpProb_23_eq_mallowsW3K3Up M hcenter,
    mallowsTopThreePairUpProb_32_eq_mallowsW3K3Down M hcenter,
    mallowsTopTwoPairUpProb_23_eq_mallowsW3K2Up M hcenter,
    mallowsTopTwoPairUpProb_32_eq_mallowsW3K2Down M hcenter,
    hq]
  exact mallowsHighNoiseW3K2_rate_gt_K3_rate

/-- The high-noise inverse Mallows parameter is positive. -/
theorem mallowsHighNoisePhi_pos : 0 < mallowsHighNoisePhi := by
  norm_num [mallowsHighNoisePhi]

/--
The concrete four-candidate identity-centered high-noise Mallows law used in
the paper's `W = 3` counterexample to W-approval optimality.
-/
def mallowsHighNoiseW3Spec : MallowsSpec 2 :=
  MallowsSpec.ofQ (Equiv.refl (Candidate 2)) mallowsHighNoisePhi
    mallowsHighNoisePhi_pos

/--
Concrete end-to-end high-noise Mallows example: for the normalized Mallows PMF
with identity center and `q = 4/5`, 2-approval has a strictly larger pairwise
learning rate than 3-approval for the source pivotal pair `(3,4)`.
-/
theorem mallowsHighNoiseW3K2_rate_gt_K3_rate_concrete :
    approvalPairwiseRate
        (mallowsTopThreePairUpProb mallowsHighNoiseW3Spec
          (2 : Candidate 2) (3 : Candidate 2))
        (mallowsTopThreePairUpProb mallowsHighNoiseW3Spec
          (3 : Candidate 2) (2 : Candidate 2)) <
      approvalPairwiseRate
        (mallowsTopTwoPairUpProb mallowsHighNoiseW3Spec
          (2 : Candidate 2) (3 : Candidate 2))
        (mallowsTopTwoPairUpProb mallowsHighNoiseW3Spec
          (3 : Candidate 2) (2 : Candidate 2)) :=
  mallowsHighNoiseW3K2_rate_gt_K3_rate_of_mallows
    mallowsHighNoiseW3Spec rfl rfl

/--
Exact iid pairwise rate certificate for the concrete high-noise Mallows
`K = 2` approval pivotal pair `(3,4)`.
-/
theorem mallowsHighNoiseW3K2_pair23_exact_rate_certificate_concrete :
    AppliedModelingLib.Probability.ExponentialRateCertificate
      (pairwiseScoringErrorProb mallowsHighNoiseW3Spec.law
        (fun π => kApprovalScore 2 π (2 : Candidate 2))
        (fun π => kApprovalScore 2 π (3 : Candidate 2)))
      (approvalPairwiseRate
        (mallowsW3K2Up mallowsHighNoisePhi)
        (mallowsW3K2Down mallowsHighNoisePhi)) := by
  refine
    kApprovalPairwiseError_exponentialRateCertificate
      mallowsHighNoiseW3Spec.law 2
      (2 : Candidate 2) (3 : Candidate 2)
      ?_ ?_ ?_ ?_ ?_
  · norm_num [mallowsW3K2Up, mallowsHighNoisePhi, mallowsW3N3,
      mallowsW3N4]
  · norm_num [mallowsW3K2Down, mallowsHighNoisePhi, mallowsW3N3,
      mallowsW3N4]
  · norm_num [mallowsW3K2Up, mallowsW3K2Down, mallowsHighNoisePhi,
      mallowsW3N3, mallowsW3N4]
  · rw [← mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb
      mallowsHighNoiseW3Spec (by decide :
        (2 : Candidate 2) ≠ (3 : Candidate 2))]
    rw [mallowsTopTwoPairUpProb_23_eq_mallowsW3K2Up
      mallowsHighNoiseW3Spec rfl]
    rfl
  · rw [kApprovalPairDownProb_eq_pairUpProb_swap]
    rw [← mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb
      mallowsHighNoiseW3Spec (by decide :
        (3 : Candidate 2) ≠ (2 : Candidate 2))]
    rw [mallowsTopTwoPairUpProb_32_eq_mallowsW3K2Down
      mallowsHighNoiseW3Spec rfl]
    rfl

/--
Exact iid pairwise rate certificate for the concrete high-noise Mallows
`K = 1` approval pivotal pair `(3,4)`.
-/
theorem mallowsHighNoiseW3K1_pair23_exact_rate_certificate_concrete :
    AppliedModelingLib.Probability.ExponentialRateCertificate
      (pairwiseScoringErrorProb mallowsHighNoiseW3Spec.law
        (fun π => kApprovalScore 1 π (2 : Candidate 2))
        (fun π => kApprovalScore 1 π (3 : Candidate 2)))
      (approvalPairwiseRate
        (mallowsW3K1Up mallowsHighNoisePhi)
        (mallowsW3K1Down mallowsHighNoisePhi)) := by
  refine
    kApprovalPairwiseError_exponentialRateCertificate
      mallowsHighNoiseW3Spec.law 1
      (2 : Candidate 2) (3 : Candidate 2)
      ?_ ?_ ?_ ?_ ?_
  · norm_num [mallowsW3K1Up, mallowsHighNoisePhi, mallowsW3N4]
  · norm_num [mallowsW3K1Down, mallowsHighNoisePhi, mallowsW3N4]
  · norm_num [mallowsW3K1Up, mallowsW3K1Down, mallowsHighNoisePhi,
      mallowsW3N4]
  · rw [kApprovalPairUpProb_one_eq_firstChoiceProb
      mallowsHighNoiseW3Spec.law (by decide :
        (2 : Candidate 2) ≠ (3 : Candidate 2))]
    rw [mallowsFirstChoiceProb_2_eq mallowsHighNoiseW3Spec rfl]
    rfl
  · rw [kApprovalPairDownProb_eq_pairUpProb_swap]
    rw [kApprovalPairUpProb_one_eq_firstChoiceProb
      mallowsHighNoiseW3Spec.law (by decide :
        (3 : Candidate 2) ≠ (2 : Candidate 2))]
    rw [mallowsFirstChoiceProb_3_eq mallowsHighNoiseW3Spec rfl]
    rfl

/--
Exact iid pairwise rate certificate for the concrete high-noise Mallows
`K = 3` approval pivotal pair `(3,4)`.
-/
theorem mallowsHighNoiseW3K3_pair23_exact_rate_certificate_concrete :
    AppliedModelingLib.Probability.ExponentialRateCertificate
      (pairwiseScoringErrorProb mallowsHighNoiseW3Spec.law
        (fun π => kApprovalScore 3 π (2 : Candidate 2))
        (fun π => kApprovalScore 3 π (3 : Candidate 2)))
      (approvalPairwiseRate
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down mallowsHighNoisePhi)) := by
  refine
    kApprovalPairwiseError_exponentialRateCertificate
      mallowsHighNoiseW3Spec.law 3
      (2 : Candidate 2) (3 : Candidate 2)
      ?_ ?_ ?_ ?_ ?_
  · norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4]
  · norm_num [mallowsW3K3Down, mallowsHighNoisePhi, mallowsW3N4]
  · norm_num [mallowsW3K3Up, mallowsW3K3Down, mallowsHighNoisePhi,
      mallowsW3N4]
  · rw [← mallowsTopThreePairUpProb_eq_kApprovalPairUpProb
      mallowsHighNoiseW3Spec (by decide :
        (2 : Candidate 2) ≠ (3 : Candidate 2))]
    rw [mallowsTopThreePairUpProb_23_eq_mallowsW3K3Up
      mallowsHighNoiseW3Spec rfl]
    rfl
  · rw [kApprovalPairDownProb_eq_pairUpProb_swap]
    rw [← mallowsTopThreePairUpProb_eq_kApprovalPairUpProb
      mallowsHighNoiseW3Spec (by decide :
        (3 : Candidate 2) ≠ (2 : Candidate 2))]
    rw [mallowsTopThreePairUpProb_32_eq_mallowsW3K3Down
      mallowsHighNoiseW3Spec rfl]
    rfl

/-! ## Four-candidate `W = 3` finite outcome rates -/

/-- The three true winners in the paper's four-candidate `W = 3` example. -/
def mallowsW3WinnerCandidate (i : Fin 3) : Candidate 2 :=
  ⟨i.val, by omega⟩

/-- The true loser in the paper's four-candidate `W = 3` example. -/
def mallowsW3LoserCandidate : Candidate 2 := 3

/-- Pairwise `K = 1` approval rate for one winner against the loser. -/
def mallowsW3K1PairRate (M : MallowsSpec 2) (i : Fin 3) : ℝ :=
  approvalPairwiseRate
    (firstChoiceProb M.law (mallowsW3WinnerCandidate i))
    (firstChoiceProb M.law mallowsW3LoserCandidate)

/-- Pairwise `K = 2` approval rate for one winner against the loser. -/
def mallowsW3K2PairRate (M : MallowsSpec 2) (i : Fin 3) : ℝ :=
  approvalPairwiseRate
    (mallowsTopTwoPairUpProb M (mallowsW3WinnerCandidate i)
      mallowsW3LoserCandidate)
    (mallowsTopTwoPairUpProb M mallowsW3LoserCandidate
      (mallowsW3WinnerCandidate i))

/-- Pairwise `K = 3` approval rate for one winner against the loser. -/
def mallowsW3K3PairRate (M : MallowsSpec 2) (i : Fin 3) : ℝ :=
  approvalPairwiseRate
    (mallowsTopThreePairUpProb M (mallowsW3WinnerCandidate i)
      mallowsW3LoserCandidate)
      (mallowsTopThreePairUpProb M mallowsW3LoserCandidate
      (mallowsW3WinnerCandidate i))

/-- Finite W-selection outcome-learning rate for `K = 1` approval. -/
def mallowsW3K1OutcomeRate (M : MallowsSpec 2) : ℝ :=
  finiteOutcomeLearningRate (mallowsW3K1PairRate M)

/-- Finite W-selection outcome-learning rate for `K = 2` approval. -/
def mallowsW3K2OutcomeRate (M : MallowsSpec 2) : ℝ :=
  finiteOutcomeLearningRate (mallowsW3K2PairRate M)

/-- Finite W-selection outcome-learning rate for `K = 3` approval. -/
def mallowsW3K3OutcomeRate (M : MallowsSpec 2) : ℝ :=
  finiteOutcomeLearningRate (mallowsW3K3PairRate M)

/-- The three nontrivial static K-approval pair-rate surfaces in the `W = 3` example. -/
def mallowsW3StaticKApprovalPairRate
    (M : MallowsSpec 2) (rule : Fin 3) (i : Fin 3) : ℝ :=
  if rule = (0 : Fin 3) then
    mallowsW3K1PairRate M i
  else if rule = (1 : Fin 3) then
    mallowsW3K2PairRate M i
  else
    mallowsW3K3PairRate M i

/-- Concrete high-noise up-event table for `K = 1,2,3` and pairs `(1,4),(2,4),(3,4)`. -/
def mallowsHighNoiseW3PairUpOfRule (rule i : Fin 3) : ℝ :=
  if rule = (0 : Fin 3) then
    if i = (0 : Fin 3) then
      mallowsW3K1Up0 mallowsHighNoisePhi
    else if i = (1 : Fin 3) then
      mallowsW3K1Up1 mallowsHighNoisePhi
    else
      mallowsW3K1Up mallowsHighNoisePhi
  else if rule = (1 : Fin 3) then
    if i = (0 : Fin 3) then
      mallowsW3K2Up0 mallowsHighNoisePhi
    else if i = (1 : Fin 3) then
      mallowsW3K2Up1 mallowsHighNoisePhi
    else
      mallowsW3K2Up mallowsHighNoisePhi
  else
    mallowsW3K3Up mallowsHighNoisePhi

/-- Concrete high-noise down-event table for `K = 1,2,3` and pairs `(1,4),(2,4),(3,4)`. -/
def mallowsHighNoiseW3PairDownOfRule (rule i : Fin 3) : ℝ :=
  if rule = (0 : Fin 3) then
    mallowsW3K1Down mallowsHighNoisePhi
  else if rule = (1 : Fin 3) then
    if i = (0 : Fin 3) then
      mallowsW3K2Down0 mallowsHighNoisePhi
    else if i = (1 : Fin 3) then
      mallowsW3K2Down1 mallowsHighNoisePhi
    else
      mallowsW3K2Down mallowsHighNoisePhi
  else
    if i = (0 : Fin 3) then
      mallowsW3K3Down0 mallowsHighNoisePhi
    else if i = (1 : Fin 3) then
      mallowsW3K3Down1 mallowsHighNoisePhi
    else
      mallowsW3K3Down mallowsHighNoisePhi

/--
Finite pair-rate surface for a randomized K-approval rule in the concrete
high-noise `M = 4`, `W = 3` Mallows example.
-/
def mallowsHighNoiseW3RandomizedKApprovalPairRate
    (weight : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  approvalPairwiseRate
    (∑ rule : Fin 3,
      weight rule * mallowsHighNoiseW3PairUpOfRule rule i)
    (∑ rule : Fin 3,
      weight rule * mallowsHighNoiseW3PairDownOfRule rule i)

/-- Parametric up-event table for `K = 1,2,3` and pairs `(1,4),(2,4),(3,4)`. -/
def mallowsW3PairUpOfRule (phi : ℝ) (rule i : Fin 3) : ℝ :=
  if rule = (0 : Fin 3) then
    if i = (0 : Fin 3) then
      mallowsW3K1Up0 phi
    else if i = (1 : Fin 3) then
      mallowsW3K1Up1 phi
    else
      mallowsW3K1Up phi
  else if rule = (1 : Fin 3) then
    if i = (0 : Fin 3) then
      mallowsW3K2Up0 phi
    else if i = (1 : Fin 3) then
      mallowsW3K2Up1 phi
    else
      mallowsW3K2Up phi
  else
    mallowsW3K3Up phi

/-- Parametric down-event table for `K = 1,2,3` and pairs `(1,4),(2,4),(3,4)`. -/
def mallowsW3PairDownOfRule (phi : ℝ) (rule i : Fin 3) : ℝ :=
  if rule = (0 : Fin 3) then
    mallowsW3K1Down phi
  else if rule = (1 : Fin 3) then
    if i = (0 : Fin 3) then
      mallowsW3K2Down0 phi
    else if i = (1 : Fin 3) then
      mallowsW3K2Down1 phi
    else
      mallowsW3K2Down phi
  else
    if i = (0 : Fin 3) then
      mallowsW3K3Down0 phi
    else if i = (1 : Fin 3) then
      mallowsW3K3Down1 phi
    else
      mallowsW3K3Down phi

/--
Finite pair-rate surface for a randomized K-approval rule in the symbolic
four-candidate `W = 3` Mallows table.
-/
def mallowsW3RandomizedKApprovalPairRate
    (phi : ℝ) (weight : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  approvalPairwiseRate
    (∑ rule : Fin 3, weight rule * mallowsW3PairUpOfRule phi rule i)
    (∑ rule : Fin 3, weight rule * mallowsW3PairDownOfRule phi rule i)

private theorem mallowsW3BoundaryPairUp_pos_of_phi_pos
    {phi : ℝ} (hphi : 0 < phi) (rule : Fin 3) :
    0 < mallowsW3PairUpOfRule phi rule (2 : Fin 3) := by
  have hN3 : 0 < mallowsW3N3 phi := mallowsW3N3_pos_of_pos hphi
  have hN4 : 0 < mallowsW3N4 phi := mallowsW3N4_pos_of_pos hphi
  fin_cases rule
  · simpa [mallowsW3PairUpOfRule, mallowsW3K1Up] using
      div_pos (pow_pos hphi 2) hN4
  · have hnum : 0 < phi + 2 * phi ^ 2 + phi ^ 3 := by
      have hphi2 : 0 < phi ^ 2 := sq_pos_of_pos hphi
      have hphi3 : 0 < phi ^ 3 := pow_pos hphi 3
      nlinarith
    simpa [mallowsW3PairUpOfRule, mallowsW3K2Up] using
      div_pos hnum (mul_pos hN3 hN4)
  · simpa [mallowsW3PairUpOfRule, mallowsW3K3Up] using
      div_pos (by norm_num : (0 : ℝ) < 1) hN4

private theorem mallowsW3BoundaryPairDown_pos_of_phi_pos
    {phi : ℝ} (hphi : 0 < phi) (rule : Fin 3) :
    0 < mallowsW3PairDownOfRule phi rule (2 : Fin 3) := by
  have hN3 : 0 < mallowsW3N3 phi := mallowsW3N3_pos_of_pos hphi
  have hN4 : 0 < mallowsW3N4 phi := mallowsW3N4_pos_of_pos hphi
  fin_cases rule
  · simpa [mallowsW3PairDownOfRule, mallowsW3K1Down] using
      div_pos (pow_pos hphi 3) hN4
  · have hnum : 0 < phi ^ 2 + 2 * phi ^ 3 + phi ^ 4 := by
      have hphi2 : 0 < phi ^ 2 := sq_pos_of_pos hphi
      have hphi3 : 0 < phi ^ 3 := pow_pos hphi 3
      have hphi4 : 0 < phi ^ 4 := pow_pos hphi 4
      nlinarith
    simpa [mallowsW3PairDownOfRule, mallowsW3K2Down] using
      div_pos hnum (mul_pos hN3 hN4)
  · simpa [mallowsW3PairDownOfRule, mallowsW3K3Down] using
      div_pos hphi hN4

private theorem mallowsW3BoundaryPair_sum_le_one_of_phi_pos
    {phi : ℝ} (hphi : 0 < phi) (rule : Fin 3) :
    mallowsW3PairUpOfRule phi rule (2 : Fin 3) +
        mallowsW3PairDownOfRule phi rule (2 : Fin 3) ≤ 1 := by
  have hN3 : 0 < mallowsW3N3 phi := mallowsW3N3_pos_of_pos hphi
  have hN4 : 0 < mallowsW3N4 phi := mallowsW3N4_pos_of_pos hphi
  fin_cases rule
  · simp [mallowsW3PairUpOfRule, mallowsW3PairDownOfRule,
      mallowsW3K1Up, mallowsW3K1Down, mallowsW3N4]
    field_simp [hN4.ne']
    ring_nf
    nlinarith [hphi]
  · have hden : 0 < mallowsW3N3 phi * mallowsW3N4 phi := mul_pos hN3 hN4
    simp [mallowsW3PairUpOfRule, mallowsW3PairDownOfRule,
      mallowsW3K2Up, mallowsW3K2Down, mallowsW3N3, mallowsW3N4]
    field_simp [hden.ne']
    ring_nf
    have hphi4 : 0 ≤ phi ^ 4 := pow_nonneg hphi.le 4
    have hphi5 : 0 ≤ phi ^ 5 := pow_nonneg hphi.le 5
    nlinarith [hphi, hphi4, hphi5]
  · simp [mallowsW3PairUpOfRule, mallowsW3PairDownOfRule,
      mallowsW3K3Up, mallowsW3K3Down, mallowsW3N4]
    field_simp [hN4.ne']
    ring_nf
    have hphi2 : 0 ≤ phi ^ 2 := sq_nonneg phi
    have hphi3 : 0 ≤ phi ^ 3 := pow_nonneg hphi.le 3
    nlinarith [hphi2, hphi3]

private theorem mallowsW3BoundaryPair_base_pos_of_phi_pos
    {phi : ℝ} (hphi : 0 < phi) (rule : Fin 3) :
    0 <
      approvalPairwiseBase
        (mallowsW3PairUpOfRule phi rule (2 : Fin 3))
        (mallowsW3PairDownOfRule phi rule (2 : Fin 3)) :=
  approvalPairwiseBase_pos_of_pos_sum_le
    (mallowsW3BoundaryPairUp_pos_of_phi_pos hphi rule)
    (mallowsW3BoundaryPairDown_pos_of_phi_pos hphi rule)
    (mallowsW3BoundaryPair_sum_le_one_of_phi_pos hphi rule)

private theorem mallowsW3BoundaryDown_eq_phi_mul_up
    (phi : ℝ) (rule : Fin 3) :
    mallowsW3PairDownOfRule phi rule (2 : Fin 3) =
      phi * mallowsW3PairUpOfRule phi rule (2 : Fin 3) := by
  fin_cases rule <;>
    simp [mallowsW3PairDownOfRule, mallowsW3PairUpOfRule,
      mallowsW3K1Down, mallowsW3K1Up, mallowsW3K2Down, mallowsW3K2Up,
      mallowsW3K3Down, mallowsW3K3Up] <;>
    ring

theorem mallowsW3K1PairRate_zero_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsW3K1PairRate M 0 =
      approvalPairwiseRate (mallowsW3K1Up0 M.q) (mallowsW3K1Down M.q) := by
  change
    approvalPairwiseRate
        (firstChoiceProb M.law (0 : Candidate 2))
        (firstChoiceProb M.law (3 : Candidate 2)) =
      approvalPairwiseRate (mallowsW3K1Up0 M.q) (mallowsW3K1Down M.q)
  rw [mallowsFirstChoiceProb_0_eq M hcenter,
    mallowsFirstChoiceProb_3_eq M hcenter]
  rfl

theorem mallowsW3K1PairRate_one_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsW3K1PairRate M 1 =
      approvalPairwiseRate (mallowsW3K1Up1 M.q) (mallowsW3K1Down M.q) := by
  change
    approvalPairwiseRate
        (firstChoiceProb M.law (1 : Candidate 2))
        (firstChoiceProb M.law (3 : Candidate 2)) =
      approvalPairwiseRate (mallowsW3K1Up1 M.q) (mallowsW3K1Down M.q)
  rw [mallowsFirstChoiceProb_1_eq M hcenter,
    mallowsFirstChoiceProb_3_eq M hcenter]
  rfl

theorem mallowsW3K1PairRate_two_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsW3K1PairRate M 2 =
      approvalPairwiseRate (mallowsW3K1Up M.q) (mallowsW3K1Down M.q) := by
  change
    approvalPairwiseRate
        (firstChoiceProb M.law (2 : Candidate 2))
        (firstChoiceProb M.law (3 : Candidate 2)) =
      approvalPairwiseRate (mallowsW3K1Up M.q) (mallowsW3K1Down M.q)
  rw [mallowsFirstChoiceProb_2_eq M hcenter,
    mallowsFirstChoiceProb_3_eq M hcenter]
  rfl

theorem mallowsW3K2PairRate_zero_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsW3K2PairRate M 0 =
      approvalPairwiseRate (mallowsW3K2Up0 M.q) (mallowsW3K2Down0 M.q) := by
  change
    approvalPairwiseRate
        (mallowsTopTwoPairUpProb M (0 : Candidate 2) (3 : Candidate 2))
        (mallowsTopTwoPairUpProb M (3 : Candidate 2) (0 : Candidate 2)) =
      approvalPairwiseRate (mallowsW3K2Up0 M.q) (mallowsW3K2Down0 M.q)
  rw [mallowsTopTwoPairUpProb_03_eq_mallowsW3K2Up0 M hcenter,
    mallowsTopTwoPairUpProb_30_eq_mallowsW3K2Down0 M hcenter]

theorem mallowsW3K2PairRate_one_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsW3K2PairRate M 1 =
      approvalPairwiseRate (mallowsW3K2Up1 M.q) (mallowsW3K2Down1 M.q) := by
  change
    approvalPairwiseRate
        (mallowsTopTwoPairUpProb M (1 : Candidate 2) (3 : Candidate 2))
        (mallowsTopTwoPairUpProb M (3 : Candidate 2) (1 : Candidate 2)) =
      approvalPairwiseRate (mallowsW3K2Up1 M.q) (mallowsW3K2Down1 M.q)
  rw [mallowsTopTwoPairUpProb_13_eq_mallowsW3K2Up1 M hcenter,
    mallowsTopTwoPairUpProb_31_eq_mallowsW3K2Down1 M hcenter]

theorem mallowsW3K2PairRate_two_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsW3K2PairRate M 2 =
      approvalPairwiseRate (mallowsW3K2Up M.q) (mallowsW3K2Down M.q) := by
  change
    approvalPairwiseRate
        (mallowsTopTwoPairUpProb M (2 : Candidate 2) (3 : Candidate 2))
        (mallowsTopTwoPairUpProb M (3 : Candidate 2) (2 : Candidate 2)) =
      approvalPairwiseRate (mallowsW3K2Up M.q) (mallowsW3K2Down M.q)
  rw [mallowsTopTwoPairUpProb_23_eq_mallowsW3K2Up M hcenter,
    mallowsTopTwoPairUpProb_32_eq_mallowsW3K2Down M hcenter]

theorem mallowsW3K3PairRate_zero_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsW3K3PairRate M 0 =
      approvalPairwiseRate (mallowsW3K3Up M.q) (mallowsW3K3Down0 M.q) := by
  change
    approvalPairwiseRate
        (mallowsTopThreePairUpProb M (0 : Candidate 2) (3 : Candidate 2))
        (mallowsTopThreePairUpProb M (3 : Candidate 2) (0 : Candidate 2)) =
      approvalPairwiseRate (mallowsW3K3Up M.q) (mallowsW3K3Down0 M.q)
  rw [mallowsTopThreePairUpProb_03_eq_mallowsW3K3Up M hcenter,
    mallowsTopThreePairUpProb_30_eq_mallowsW3K3Down0 M hcenter]

theorem mallowsW3K3PairRate_one_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsW3K3PairRate M 1 =
      approvalPairwiseRate (mallowsW3K3Up M.q) (mallowsW3K3Down1 M.q) := by
  change
    approvalPairwiseRate
        (mallowsTopThreePairUpProb M (1 : Candidate 2) (3 : Candidate 2))
        (mallowsTopThreePairUpProb M (3 : Candidate 2) (1 : Candidate 2)) =
      approvalPairwiseRate (mallowsW3K3Up M.q) (mallowsW3K3Down1 M.q)
  rw [mallowsTopThreePairUpProb_13_eq_mallowsW3K3Up M hcenter,
    mallowsTopThreePairUpProb_31_eq_mallowsW3K3Down1 M hcenter]

theorem mallowsW3K3PairRate_two_eq
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsW3K3PairRate M 2 =
      approvalPairwiseRate (mallowsW3K3Up M.q) (mallowsW3K3Down M.q) := by
  change
    approvalPairwiseRate
        (mallowsTopThreePairUpProb M (2 : Candidate 2) (3 : Candidate 2))
        (mallowsTopThreePairUpProb M (3 : Candidate 2) (2 : Candidate 2)) =
      approvalPairwiseRate (mallowsW3K3Up M.q) (mallowsW3K3Down M.q)
  rw [mallowsTopThreePairUpProb_23_eq_mallowsW3K3Up M hcenter,
    mallowsTopThreePairUpProb_32_eq_mallowsW3K3Down M hcenter]

theorem mallowsHighNoiseW3K1OutcomeRate_eq_pair2_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    mallowsW3K1OutcomeRate M = mallowsW3K1PairRate M (2 : Fin 3) := by
  unfold mallowsW3K1OutcomeRate finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le (mallowsW3K1PairRate M)
      (by simp : (2 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)))
  · exact Finset.le_inf' _ _ (by
      intro i _
      fin_cases i
      · rw [mallowsW3K1PairRate_two_eq M hcenter]
        change approvalPairwiseRate (mallowsW3K1Up M.q) (mallowsW3K1Down M.q) ≤
          mallowsW3K1PairRate M (0 : Fin 3)
        rw [mallowsW3K1PairRate_zero_eq M hcenter, hq]
        exact mallowsHighNoiseW3K1_pair2_rate_lt_pair0_rate.le
      · rw [mallowsW3K1PairRate_two_eq M hcenter]
        change approvalPairwiseRate (mallowsW3K1Up M.q) (mallowsW3K1Down M.q) ≤
          mallowsW3K1PairRate M (1 : Fin 3)
        rw [mallowsW3K1PairRate_one_eq M hcenter, hq]
        exact mallowsHighNoiseW3K1_pair2_rate_lt_pair1_rate.le
      · rfl)

theorem mallowsHighNoiseW3K2OutcomeRate_eq_pair2_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    mallowsW3K2OutcomeRate M = mallowsW3K2PairRate M (2 : Fin 3) := by
  unfold mallowsW3K2OutcomeRate finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le (mallowsW3K2PairRate M)
      (by simp : (2 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)))
  · exact Finset.le_inf' _ _ (by
      intro i _
      fin_cases i
      · rw [mallowsW3K2PairRate_two_eq M hcenter]
        change approvalPairwiseRate (mallowsW3K2Up M.q) (mallowsW3K2Down M.q) ≤
          mallowsW3K2PairRate M (0 : Fin 3)
        rw [mallowsW3K2PairRate_zero_eq M hcenter, hq]
        exact mallowsHighNoiseW3K2_pair2_rate_lt_pair0_rate.le
      · rw [mallowsW3K2PairRate_two_eq M hcenter]
        change approvalPairwiseRate (mallowsW3K2Up M.q) (mallowsW3K2Down M.q) ≤
          mallowsW3K2PairRate M (1 : Fin 3)
        rw [mallowsW3K2PairRate_one_eq M hcenter, hq]
        exact mallowsHighNoiseW3K2_pair2_rate_lt_pair1_rate.le
      · rfl)

theorem mallowsHighNoiseW3K3OutcomeRate_eq_pair2_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    mallowsW3K3OutcomeRate M = mallowsW3K3PairRate M (2 : Fin 3) := by
  unfold mallowsW3K3OutcomeRate finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le (mallowsW3K3PairRate M)
      (by simp : (2 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)))
  · exact Finset.le_inf' _ _ (by
      intro i _
      fin_cases i
      · rw [mallowsW3K3PairRate_two_eq M hcenter]
        change approvalPairwiseRate (mallowsW3K3Up M.q) (mallowsW3K3Down M.q) ≤
          mallowsW3K3PairRate M (0 : Fin 3)
        rw [mallowsW3K3PairRate_zero_eq M hcenter, hq]
        exact mallowsHighNoiseW3K3_pair2_rate_lt_pair0_rate.le
      · rw [mallowsW3K3PairRate_two_eq M hcenter]
        change approvalPairwiseRate (mallowsW3K3Up M.q) (mallowsW3K3Down M.q) ≤
          mallowsW3K3PairRate M (1 : Fin 3)
        rw [mallowsW3K3PairRate_one_eq M hcenter, hq]
        exact mallowsHighNoiseW3K3_pair2_rate_lt_pair1_rate.le
      · rfl)

/-- For any identity-centered four-candidate Mallows law with `0 < q < 1`, the
`K = 1` W-selection finite minimum is the boundary pair `(3,4)`. -/
theorem mallowsW3K1OutcomeRate_eq_pair2_of_mallows_q_lt_one
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq_lt : M.q < 1) :
    mallowsW3K1OutcomeRate M = mallowsW3K1PairRate M (2 : Fin 3) := by
  unfold mallowsW3K1OutcomeRate finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le (mallowsW3K1PairRate M)
      (by simp : (2 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)))
  · exact Finset.le_inf' _ _ (by
      intro i _
      fin_cases i
      · rw [mallowsW3K1PairRate_two_eq M hcenter]
        change approvalPairwiseRate (mallowsW3K1Up M.q) (mallowsW3K1Down M.q) ≤
          mallowsW3K1PairRate M (0 : Fin 3)
        rw [mallowsW3K1PairRate_zero_eq M hcenter]
        exact mallowsW3K1_pair2_rate_le_pair0_rate_of_q_lt_one
          M.q_pos hq_lt
      · rw [mallowsW3K1PairRate_two_eq M hcenter]
        change approvalPairwiseRate (mallowsW3K1Up M.q) (mallowsW3K1Down M.q) ≤
          mallowsW3K1PairRate M (1 : Fin 3)
        rw [mallowsW3K1PairRate_one_eq M hcenter]
        exact mallowsW3K1_pair2_rate_le_pair1_rate_of_q_lt_one
          M.q_pos hq_lt
      · rfl)

/-- For any identity-centered four-candidate Mallows law with `0 < q < 1`, the
`K = 2` W-selection finite minimum is the boundary pair `(3,4)`. -/
theorem mallowsW3K2OutcomeRate_eq_pair2_of_mallows_q_lt_one
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq_lt : M.q < 1) :
    mallowsW3K2OutcomeRate M = mallowsW3K2PairRate M (2 : Fin 3) := by
  unfold mallowsW3K2OutcomeRate finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le (mallowsW3K2PairRate M)
      (by simp : (2 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)))
  · exact Finset.le_inf' _ _ (by
      intro i _
      fin_cases i
      · rw [mallowsW3K2PairRate_two_eq M hcenter]
        change approvalPairwiseRate (mallowsW3K2Up M.q) (mallowsW3K2Down M.q) ≤
          mallowsW3K2PairRate M (0 : Fin 3)
        rw [mallowsW3K2PairRate_zero_eq M hcenter]
        exact mallowsW3K2_pair2_rate_le_pair0_rate_of_q_lt_one
          M.q_pos hq_lt
      · rw [mallowsW3K2PairRate_two_eq M hcenter]
        change approvalPairwiseRate (mallowsW3K2Up M.q) (mallowsW3K2Down M.q) ≤
          mallowsW3K2PairRate M (1 : Fin 3)
        rw [mallowsW3K2PairRate_one_eq M hcenter]
        exact mallowsW3K2_pair2_rate_le_pair1_rate_of_q_lt_one
          M.q_pos hq_lt
      · rfl)

/-- For any identity-centered four-candidate Mallows law with `0 < q < 1`, the
`K = 3` W-selection finite minimum is the boundary pair `(3,4)`. -/
theorem mallowsW3K3OutcomeRate_eq_pair2_of_mallows_q_lt_one
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq_lt : M.q < 1) :
    mallowsW3K3OutcomeRate M = mallowsW3K3PairRate M (2 : Fin 3) := by
  unfold mallowsW3K3OutcomeRate finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le (mallowsW3K3PairRate M)
      (by simp : (2 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)))
  · exact Finset.le_inf' _ _ (by
      intro i _
      fin_cases i
      · rw [mallowsW3K3PairRate_two_eq M hcenter]
        change approvalPairwiseRate (mallowsW3K3Up M.q) (mallowsW3K3Down M.q) ≤
          mallowsW3K3PairRate M (0 : Fin 3)
        rw [mallowsW3K3PairRate_zero_eq M hcenter]
        exact mallowsW3K3_pair2_rate_le_pair0_rate_of_q_lt_one
          M.q_pos hq_lt
      · rw [mallowsW3K3PairRate_two_eq M hcenter]
        change approvalPairwiseRate (mallowsW3K3Up M.q) (mallowsW3K3Down M.q) ≤
          mallowsW3K3PairRate M (1 : Fin 3)
        rw [mallowsW3K3PairRate_one_eq M hcenter]
        exact mallowsW3K3_pair2_rate_le_pair1_rate_of_q_lt_one
          M.q_pos hq_lt
      · rfl)

/--
Symbolic high-noise outcome-rate theorem: in a four-candidate
identity-centered Mallows law with `0 < q < 1` and `1 < q^2 + q^3`,
2-approval has a strictly larger finite W-selection learning rate than
3-approval.
-/
theorem mallowsW3K2_outcomeRate_gt_K3_outcomeRate_of_mallows_q_high_noise
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq_lt : M.q < 1) (hhigh : 1 < M.q ^ 2 + M.q ^ 3) :
    mallowsW3K3OutcomeRate M < mallowsW3K2OutcomeRate M := by
  rw [mallowsW3K3OutcomeRate_eq_pair2_of_mallows_q_lt_one
      M hcenter hq_lt,
    mallowsW3K2OutcomeRate_eq_pair2_of_mallows_q_lt_one
      M hcenter hq_lt,
    mallowsW3K3PairRate_two_eq M hcenter,
    mallowsW3K2PairRate_two_eq M hcenter]
  exact mallowsW3K2_rate_gt_K3_rate_of_q_high_noise M.q_pos hq_lt hhigh

/--
For every four-candidate identity-centered Mallows law with `0 < q < 1`,
2-approval has a strictly larger finite W-selection learning rate than
1-approval.
-/
theorem mallowsW3K2_outcomeRate_gt_K1_outcomeRate_of_mallows_q_lt_one
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq_lt : M.q < 1) :
    mallowsW3K1OutcomeRate M < mallowsW3K2OutcomeRate M := by
  rw [mallowsW3K1OutcomeRate_eq_pair2_of_mallows_q_lt_one
      M hcenter hq_lt,
    mallowsW3K2OutcomeRate_eq_pair2_of_mallows_q_lt_one
      M hcenter hq_lt,
    mallowsW3K1PairRate_two_eq M hcenter,
    mallowsW3K2PairRate_two_eq M hcenter]
  exact mallowsW3K2_rate_gt_K1_rate_of_q_lt_one M.q_pos hq_lt

/--
Symbolic nontrivial-K certificate for the four-candidate `W = 3` Mallows
example: under the explicit high-noise condition `1 < q^2 + q^3`, `K = 2`
strictly beats both other nontrivial static K-approval rules.
-/
theorem mallowsW3_K2_best_among_nontrivial_static_K_of_mallows_q_high_noise
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq_lt : M.q < 1) (hhigh : 1 < M.q ^ 2 + M.q ^ 3) :
    mallowsW3K1OutcomeRate M = mallowsW3K1PairRate M (2 : Fin 3) ∧
      mallowsW3K2OutcomeRate M = mallowsW3K2PairRate M (2 : Fin 3) ∧
      mallowsW3K3OutcomeRate M = mallowsW3K3PairRate M (2 : Fin 3) ∧
      mallowsW3K1OutcomeRate M < mallowsW3K2OutcomeRate M ∧
      mallowsW3K3OutcomeRate M < mallowsW3K2OutcomeRate M := by
  exact
    ⟨mallowsW3K1OutcomeRate_eq_pair2_of_mallows_q_lt_one M hcenter hq_lt,
      mallowsW3K2OutcomeRate_eq_pair2_of_mallows_q_lt_one M hcenter hq_lt,
      mallowsW3K3OutcomeRate_eq_pair2_of_mallows_q_lt_one M hcenter hq_lt,
      mallowsW3K2_outcomeRate_gt_K1_outcomeRate_of_mallows_q_lt_one
        M hcenter hq_lt,
      mallowsW3K2_outcomeRate_gt_K3_outcomeRate_of_mallows_q_high_noise
        M hcenter hq_lt hhigh⟩

/-- The high-noise `K = 1` Mallows W-selection outcome rate is positive. -/
theorem mallowsHighNoiseW3K1OutcomeRate_pos_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    0 < mallowsW3K1OutcomeRate M := by
  rw [mallowsHighNoiseW3K1OutcomeRate_eq_pair2_of_mallows M hcenter hq,
    mallowsW3K1PairRate_two_eq M hcenter, hq]
  exact
    approvalPairwiseRate_pos_of_down_lt_up
      (by
        norm_num [mallowsW3K1Up, mallowsHighNoisePhi, mallowsW3N4])
      (by
        norm_num [mallowsW3K1Down, mallowsHighNoisePhi, mallowsW3N4])
      (by
        norm_num [mallowsW3K1Up, mallowsW3K1Down, mallowsHighNoisePhi,
          mallowsW3N4])
      (by
        norm_num [mallowsW3K1Up, mallowsW3K1Down, mallowsHighNoisePhi,
          mallowsW3N4])

/-- The high-noise `K = 2` Mallows W-selection outcome rate is positive. -/
theorem mallowsHighNoiseW3K2OutcomeRate_pos_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    0 < mallowsW3K2OutcomeRate M := by
  rw [mallowsHighNoiseW3K2OutcomeRate_eq_pair2_of_mallows M hcenter hq,
    mallowsW3K2PairRate_two_eq M hcenter, hq]
  exact
    approvalPairwiseRate_pos_of_down_lt_up
      (by
        norm_num [mallowsW3K2Up, mallowsHighNoisePhi, mallowsW3N3,
          mallowsW3N4])
      (by
        norm_num [mallowsW3K2Down, mallowsHighNoisePhi, mallowsW3N3,
          mallowsW3N4])
      (by
        norm_num [mallowsW3K2Up, mallowsW3K2Down, mallowsHighNoisePhi,
          mallowsW3N3, mallowsW3N4])
      (by
        norm_num [mallowsW3K2Up, mallowsW3K2Down, mallowsHighNoisePhi,
          mallowsW3N3, mallowsW3N4])

/-- The high-noise `K = 3` Mallows W-selection outcome rate is positive. -/
theorem mallowsHighNoiseW3K3OutcomeRate_pos_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    0 < mallowsW3K3OutcomeRate M := by
  rw [mallowsHighNoiseW3K3OutcomeRate_eq_pair2_of_mallows M hcenter hq,
    mallowsW3K3PairRate_two_eq M hcenter, hq]
  exact
    approvalPairwiseRate_pos_of_down_lt_up
      (by
        norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4])
      (by
        norm_num [mallowsW3K3Down, mallowsHighNoisePhi, mallowsW3N4])
      (by
        norm_num [mallowsW3K3Up, mallowsW3K3Down, mallowsHighNoisePhi,
          mallowsW3N4])
      (by
        norm_num [mallowsW3K3Up, mallowsW3K3Down, mallowsHighNoisePhi,
          mallowsW3N4])

/--
W-selection high-noise outcome-rate theorem: in any four-candidate
identity-centered Mallows law with `q = 4/5`, the finite W-selection learning
rate of 3-approval is strictly lower than the finite W-selection learning rate
of 2-approval.
-/
theorem mallowsHighNoiseW3K2_outcomeRate_gt_K3_outcomeRate_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    mallowsW3K3OutcomeRate M < mallowsW3K2OutcomeRate M := by
  rw [mallowsHighNoiseW3K3OutcomeRate_eq_pair2_of_mallows
      M hcenter hq,
    mallowsHighNoiseW3K2OutcomeRate_eq_pair2_of_mallows
      M hcenter hq,
    mallowsW3K3PairRate_two_eq M hcenter,
    mallowsW3K2PairRate_two_eq M hcenter,
    hq]
  exact mallowsHighNoiseW3K2_rate_gt_K3_rate

/--
W-selection high-noise outcome-rate theorem: in any four-candidate
identity-centered Mallows law with `q = 4/5`, the finite W-selection learning
rate of 1-approval is also strictly lower than the finite W-selection learning
rate of 2-approval.
-/
theorem mallowsHighNoiseW3K2_outcomeRate_gt_K1_outcomeRate_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    mallowsW3K1OutcomeRate M < mallowsW3K2OutcomeRate M := by
  rw [mallowsHighNoiseW3K1OutcomeRate_eq_pair2_of_mallows
      M hcenter hq,
    mallowsHighNoiseW3K2OutcomeRate_eq_pair2_of_mallows
      M hcenter hq,
    mallowsW3K1PairRate_two_eq M hcenter,
    mallowsW3K2PairRate_two_eq M hcenter,
    hq]
  exact mallowsHighNoiseW3K2_rate_gt_K1_rate

/--
Closed high-noise pivotal-pair certificate: for any four-candidate
identity-centered Mallows law with `q = 4/5`, both `K = 2` approval and
`K = 3` approval have their finite W-selection minimum at the source pair
`(3,4)`, represented by pair index `2`; the displayed closed min-rates then
imply that W-approval is not outcome-rate optimal.
-/
theorem mallowsHighNoiseW3_pivotalPair_minRates_and_WApproval_not_optimal_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    mallowsW3K2OutcomeRate M = mallowsW3K2PairRate M (2 : Fin 3) ∧
      mallowsW3K2PairRate M (2 : Fin 3) =
        approvalPairwiseRate
          (mallowsW3K2Up mallowsHighNoisePhi)
          (mallowsW3K2Down mallowsHighNoisePhi) ∧
      mallowsW3K3OutcomeRate M = mallowsW3K3PairRate M (2 : Fin 3) ∧
      mallowsW3K3PairRate M (2 : Fin 3) =
        approvalPairwiseRate
          (mallowsW3K3Up mallowsHighNoisePhi)
          (mallowsW3K3Down mallowsHighNoisePhi) ∧
      mallowsW3K3OutcomeRate M < mallowsW3K2OutcomeRate M := by
  have hK2min :=
    mallowsHighNoiseW3K2OutcomeRate_eq_pair2_of_mallows M hcenter hq
  have hK3min :=
    mallowsHighNoiseW3K3OutcomeRate_eq_pair2_of_mallows M hcenter hq
  have hK2rate :
      mallowsW3K2PairRate M (2 : Fin 3) =
        approvalPairwiseRate
          (mallowsW3K2Up mallowsHighNoisePhi)
          (mallowsW3K2Down mallowsHighNoisePhi) := by
    rw [mallowsW3K2PairRate_two_eq M hcenter, hq]
  have hK3rate :
      mallowsW3K3PairRate M (2 : Fin 3) =
        approvalPairwiseRate
          (mallowsW3K3Up mallowsHighNoisePhi)
          (mallowsW3K3Down mallowsHighNoisePhi) := by
    rw [mallowsW3K3PairRate_two_eq M hcenter, hq]
  refine ⟨hK2min, hK2rate, hK3min, hK3rate, ?_⟩
  rw [hK3min, hK2min, hK3rate, hK2rate]
  exact mallowsHighNoiseW3K2_rate_gt_K3_rate

/--
Closed high-noise nontrivial-K certificate: for any four-candidate
identity-centered Mallows law with `q = 4/5`, `K = 1`, `K = 2`, and `K = 3`
all have their finite W-selection minimum at the source boundary pair `(3,4)`,
and the K=2 outcome rate strictly beats both alternatives.
-/
theorem mallowsHighNoiseW3_K2_best_among_nontrivial_static_K_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    mallowsW3K1OutcomeRate M = mallowsW3K1PairRate M (2 : Fin 3) ∧
      mallowsW3K2OutcomeRate M = mallowsW3K2PairRate M (2 : Fin 3) ∧
      mallowsW3K3OutcomeRate M = mallowsW3K3PairRate M (2 : Fin 3) ∧
      mallowsW3K1OutcomeRate M < mallowsW3K2OutcomeRate M ∧
      mallowsW3K3OutcomeRate M < mallowsW3K2OutcomeRate M := by
  exact
    ⟨mallowsHighNoiseW3K1OutcomeRate_eq_pair2_of_mallows M hcenter hq,
      mallowsHighNoiseW3K2OutcomeRate_eq_pair2_of_mallows M hcenter hq,
      mallowsHighNoiseW3K3OutcomeRate_eq_pair2_of_mallows M hcenter hq,
      mallowsHighNoiseW3K2_outcomeRate_gt_K1_outcomeRate_of_mallows
        M hcenter hq,
      mallowsHighNoiseW3K2_outcomeRate_gt_K3_outcomeRate_of_mallows
        M hcenter hq⟩

/--
Concrete W-selection high-noise outcome-rate theorem for the normalized
four-candidate identity-centered Mallows law at `q = 4/5`.
-/
theorem mallowsHighNoiseW3K2_outcomeRate_gt_K3_outcomeRate_concrete :
    mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec <
      mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec :=
  mallowsHighNoiseW3K2_outcomeRate_gt_K3_outcomeRate_of_mallows
    mallowsHighNoiseW3Spec rfl rfl

/--
Concrete high-noise outcome-rate theorem: for the normalized Mallows law,
2-approval strictly beats 1-approval as well.
-/
theorem mallowsHighNoiseW3K2_outcomeRate_gt_K1_outcomeRate_concrete :
    mallowsW3K1OutcomeRate mallowsHighNoiseW3Spec <
      mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec :=
  mallowsHighNoiseW3K2_outcomeRate_gt_K1_outcomeRate_of_mallows
    mallowsHighNoiseW3Spec rfl rfl

/-- Concrete high-noise certificate that 2-approval is best among K=1,2,3. -/
theorem mallowsHighNoiseW3_K2_best_among_nontrivial_static_K_concrete :
    mallowsW3K1OutcomeRate mallowsHighNoiseW3Spec =
        mallowsW3K1PairRate mallowsHighNoiseW3Spec (2 : Fin 3) ∧
      mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec =
        mallowsW3K2PairRate mallowsHighNoiseW3Spec (2 : Fin 3) ∧
      mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec =
        mallowsW3K3PairRate mallowsHighNoiseW3Spec (2 : Fin 3) ∧
      mallowsW3K1OutcomeRate mallowsHighNoiseW3Spec <
        mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec ∧
      mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec <
        mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec :=
  mallowsHighNoiseW3_K2_best_among_nontrivial_static_K_of_mallows
    mallowsHighNoiseW3Spec rfl rfl

/--
Source-shaped high-noise counterexample for `lem:mallowsnotWK`: under the
Mallows model and W-selection goal, W-approval need not be approval-rate
optimal.
-/
theorem mallowsW3_WApproval_not_approvalRateOptimal_counterexample :
    ∃ M : MallowsSpec 2,
      M.center = Equiv.refl (Candidate 2) ∧
        M.q = mallowsHighNoisePhi ∧
          ∃ better : Fin 3,
            better ≠ (2 : Fin 3) ∧
              finiteOutcomeLearningRate
                  (mallowsW3StaticKApprovalPairRate M (2 : Fin 3)) <
                finiteOutcomeLearningRate
                  (mallowsW3StaticKApprovalPairRate M better) := by
  refine ⟨mallowsHighNoiseW3Spec, rfl, rfl, (1 : Fin 3), by decide, ?_⟩
  simpa [mallowsW3StaticKApprovalPairRate, mallowsW3K2OutcomeRate,
    mallowsW3K3OutcomeRate] using
    mallowsHighNoiseW3K2_outcomeRate_gt_K3_outcomeRate_concrete

/--
Four-candidate Mallows W-selection no-randomization theorem: for any
identity-centered Mallows law with `0 < q < 1`, any randomized mechanism over
the nontrivial static rules `K = 1,2,3` is weakly dominated in finite
W-selection learning rate by one of those static K-approval rules.
-/
theorem mallowsW3_randomizedKApproval_no_improvement_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq_lt : M.q < 1)
    (weight : Fin 3 → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Fin 3, weight rule) = 1) :
    ∃ rule : Fin 3,
      finiteOutcomeLearningRate
          (mallowsW3RandomizedKApprovalPairRate M.q weight) ≤
        finiteOutcomeLearningRate
          (mallowsW3StaticKApprovalPairRate M rule) := by
  let pUp : Fin 3 → ℝ :=
    fun rule => mallowsW3PairUpOfRule M.q rule (2 : Fin 3)
  let pDown : Fin 3 → ℝ :=
    fun rule => mallowsW3PairDownOfRule M.q rule (2 : Fin 3)
  have hratio : ∀ rule : Fin 3, pDown rule = M.q * pUp rule := by
    intro rule
    simpa [pUp, pDown] using
      mallowsW3BoundaryDown_eq_phi_mul_up M.q rule
  have hbase_pos :
      ∀ rule : Fin 3, 0 < approvalPairwiseBase (pUp rule) (pDown rule) := by
    intro rule
    simpa [pUp, pDown] using
      mallowsW3BoundaryPair_base_pos_of_phi_pos M.q_pos rule
  have hmixed_base_pos :
      0 <
        approvalPairwiseBase
          (∑ rule : Fin 3, weight rule * pUp rule)
          (∑ rule : Fin 3, weight rule * pDown rule) := by
    have hdown_sum :
        (∑ rule : Fin 3, weight rule * pDown rule) =
          ∑ rule : Fin 3, weight rule * (M.q * pUp rule) := by
      refine Finset.sum_congr rfl ?_
      intro rule _
      rw [hratio rule]
    have hbase_eq :
        approvalPairwiseBase
            (∑ rule : Fin 3, weight rule * pUp rule)
            (∑ rule : Fin 3, weight rule * pDown rule) =
          ∑ rule : Fin 3,
            weight rule *
              approvalPairwiseBase (pUp rule) (M.q * pUp rule) := by
      exact
        approvalPairwiseBase_weighted_eq_same_ratio
          weight pUp M.q
          (∑ rule : Fin 3, weight rule * pUp rule)
          (∑ rule : Fin 3, weight rule * pDown rule)
          rfl hdown_sum hweight hsum
          (by
            intro rule
            exact le_of_lt
              (mallowsW3BoundaryPairUp_pos_of_phi_pos M.q_pos rule))
          M.q_pos.le
    rw [hbase_eq]
    exact
      weighted_sum_pos_of_nonneg_sum_eq_one
        weight
        (fun rule : Fin 3 =>
          approvalPairwiseBase (pUp rule) (M.q * pUp rule))
        hweight hsum
        (by
          intro rule
          change 0 < approvalPairwiseBase (pUp rule) (M.q * pUp rule)
          rw [← hratio rule]
          exact hbase_pos rule)
  exact
    kApprovalOutcome_no_randomization_of_static_pivotal_pair_positive
      weight pUp pDown
      (mallowsW3StaticKApprovalPairRate M)
      (mallowsW3RandomizedKApprovalPairRate M.q weight)
      (2 : Fin 3)
      (mixedUp := ∑ rule : Fin 3, weight rule * pUp rule)
      (mixedDown := ∑ rule : Fin 3, weight rule * pDown rule)
      rfl rfl hweight hsum
      (by
        intro rule
        exact le_of_lt
          (mallowsW3BoundaryPairUp_pos_of_phi_pos M.q_pos rule))
      (by
        intro rule
        exact le_of_lt
          (mallowsW3BoundaryPairDown_pos_of_phi_pos M.q_pos rule))
      hbase_pos hmixed_base_pos
      (by
        intro rule
        fin_cases rule
        · simpa [mallowsW3StaticKApprovalPairRate, mallowsW3K1OutcomeRate]
            using
              mallowsW3K1OutcomeRate_eq_pair2_of_mallows_q_lt_one
                M hcenter hq_lt
        · simpa [mallowsW3StaticKApprovalPairRate, mallowsW3K2OutcomeRate]
            using
              mallowsW3K2OutcomeRate_eq_pair2_of_mallows_q_lt_one
                M hcenter hq_lt
        · simpa [mallowsW3StaticKApprovalPairRate, mallowsW3K3OutcomeRate]
            using
              mallowsW3K3OutcomeRate_eq_pair2_of_mallows_q_lt_one
                M hcenter hq_lt)
      (by
        intro rule
        fin_cases rule
        · simpa [mallowsW3StaticKApprovalPairRate, pUp, pDown,
            mallowsW3PairUpOfRule, mallowsW3PairDownOfRule] using
            mallowsW3K1PairRate_two_eq M hcenter
        · simpa [mallowsW3StaticKApprovalPairRate, pUp, pDown,
            mallowsW3PairUpOfRule, mallowsW3PairDownOfRule] using
            mallowsW3K2PairRate_two_eq M hcenter
        · simpa [mallowsW3StaticKApprovalPairRate, pUp, pDown,
            mallowsW3PairUpOfRule, mallowsW3PairDownOfRule] using
            mallowsW3K3PairRate_two_eq M hcenter)
      (by
        simp [mallowsW3RandomizedKApprovalPairRate, pUp, pDown])

private theorem mallowsHighNoiseW3BoundaryDown_eq_phi_mul_up
    (rule : Fin 3) :
    mallowsHighNoiseW3PairDownOfRule rule (2 : Fin 3) =
      mallowsHighNoisePhi *
        mallowsHighNoiseW3PairUpOfRule rule (2 : Fin 3) := by
  fin_cases rule <;>
    simp [mallowsHighNoiseW3PairDownOfRule,
      mallowsHighNoiseW3PairUpOfRule, mallowsW3K1Down, mallowsW3K1Up,
      mallowsW3K2Down, mallowsW3K2Up, mallowsW3K3Down, mallowsW3K3Up,
      mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4] <;> norm_num

/--
Concrete high-noise Mallows no-randomization theorem: for the normalized
four-candidate identity-centered Mallows law at `q = 4/5`, any randomized
mechanism over the nontrivial static rules `K = 1,2,3` is weakly dominated in
finite W-selection learning rate by one of those static K-approval rules.
-/
theorem mallowsHighNoiseW3_randomizedKApproval_no_improvement_concrete
    (weight : Fin 3 → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Fin 3, weight rule) = 1) :
    ∃ rule : Fin 3,
      finiteOutcomeLearningRate
          (mallowsHighNoiseW3RandomizedKApprovalPairRate weight) ≤
        finiteOutcomeLearningRate
          (mallowsW3StaticKApprovalPairRate mallowsHighNoiseW3Spec rule) := by
  let pUp : Fin 3 → ℝ :=
    fun rule => mallowsHighNoiseW3PairUpOfRule rule (2 : Fin 3)
  let pDown : Fin 3 → ℝ :=
    fun rule => mallowsHighNoiseW3PairDownOfRule rule (2 : Fin 3)
  have hbase_pos :
      ∀ rule : Fin 3, 0 < approvalPairwiseBase (pUp rule) (pDown rule) := by
    intro rule
    fin_cases rule
    · simpa [pUp, pDown, mallowsHighNoiseW3PairUpOfRule,
        mallowsHighNoiseW3PairDownOfRule] using
        mallowsHighNoiseW3K1_base_pos
    · simpa [pUp, pDown, mallowsHighNoiseW3PairUpOfRule,
        mallowsHighNoiseW3PairDownOfRule] using
        mallowsHighNoiseW3K2_base_pos
    · simpa [pUp, pDown, mallowsHighNoiseW3PairUpOfRule,
        mallowsHighNoiseW3PairDownOfRule] using
        mallowsHighNoiseW3K3_base_pos
  have hmixed_base_pos :
      0 <
        approvalPairwiseBase
          (∑ rule : Fin 3, weight rule * pUp rule)
          (∑ rule : Fin 3, weight rule * pDown rule) := by
    have hratio : ∀ rule : Fin 3,
        pDown rule = mallowsHighNoisePhi * pUp rule := by
      intro rule
      simpa [pUp, pDown] using
        mallowsHighNoiseW3BoundaryDown_eq_phi_mul_up rule
    have hdown_sum :
        (∑ rule : Fin 3, weight rule * pDown rule) =
          ∑ rule : Fin 3,
            weight rule * (mallowsHighNoisePhi * pUp rule) := by
      refine Finset.sum_congr rfl ?_
      intro rule _
      rw [hratio rule]
    have hbase_eq :
        approvalPairwiseBase
            (∑ rule : Fin 3, weight rule * pUp rule)
            (∑ rule : Fin 3, weight rule * pDown rule) =
          ∑ rule : Fin 3,
            weight rule *
              approvalPairwiseBase
                (pUp rule) (mallowsHighNoisePhi * pUp rule) := by
      exact
        approvalPairwiseBase_weighted_eq_same_ratio
          weight pUp mallowsHighNoisePhi
          (∑ rule : Fin 3, weight rule * pUp rule)
          (∑ rule : Fin 3, weight rule * pDown rule)
          rfl hdown_sum hweight hsum
          (by
            intro rule
            fin_cases rule <;>
              simp [pUp, mallowsHighNoiseW3PairUpOfRule,
                mallowsW3K1Up, mallowsW3K2Up, mallowsW3K3Up,
                mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4] <;>
              norm_num)
          (by norm_num [mallowsHighNoisePhi])
    rw [hbase_eq]
    exact
      weighted_sum_pos_of_nonneg_sum_eq_one
        weight
        (fun rule : Fin 3 =>
          approvalPairwiseBase
            (pUp rule) (mallowsHighNoisePhi * pUp rule))
        hweight hsum
        (by
          intro rule
          change
            0 <
              approvalPairwiseBase
                (pUp rule) (mallowsHighNoisePhi * pUp rule)
          rw [← hratio rule]
          exact hbase_pos rule)
  exact
    kApprovalOutcome_no_randomization_of_static_pivotal_pair_positive
      weight pUp pDown
      (mallowsW3StaticKApprovalPairRate mallowsHighNoiseW3Spec)
      (mallowsHighNoiseW3RandomizedKApprovalPairRate weight)
      (2 : Fin 3)
      (mixedUp := ∑ rule : Fin 3, weight rule * pUp rule)
      (mixedDown := ∑ rule : Fin 3, weight rule * pDown rule)
      rfl rfl hweight hsum
      (by
        intro rule
        fin_cases rule <;>
          simp [pUp, mallowsHighNoiseW3PairUpOfRule, mallowsW3K1Up,
            mallowsW3K2Up, mallowsW3K3Up, mallowsHighNoisePhi,
            mallowsW3N3, mallowsW3N4] <;>
          norm_num)
      (by
        intro rule
        fin_cases rule <;>
          simp [pDown, mallowsHighNoiseW3PairDownOfRule,
            mallowsW3K1Down, mallowsW3K2Down, mallowsW3K3Down,
            mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4] <;>
          norm_num)
      hbase_pos hmixed_base_pos
      (by
        intro rule
        fin_cases rule
        · simpa [mallowsW3StaticKApprovalPairRate, mallowsW3K1OutcomeRate]
            using
              mallowsHighNoiseW3K1OutcomeRate_eq_pair2_of_mallows
                mallowsHighNoiseW3Spec rfl rfl
        · simpa [mallowsW3StaticKApprovalPairRate, mallowsW3K2OutcomeRate]
            using
              mallowsHighNoiseW3K2OutcomeRate_eq_pair2_of_mallows
                mallowsHighNoiseW3Spec rfl rfl
        · simpa [mallowsW3StaticKApprovalPairRate, mallowsW3K3OutcomeRate]
            using
              mallowsHighNoiseW3K3OutcomeRate_eq_pair2_of_mallows
                mallowsHighNoiseW3Spec rfl rfl)
      (by
        intro rule
        fin_cases rule
        · simpa [mallowsW3StaticKApprovalPairRate, pUp, pDown,
            mallowsHighNoiseW3PairUpOfRule,
            mallowsHighNoiseW3PairDownOfRule, mallowsHighNoiseW3Spec,
            MallowsSpec.ofQ] using
            mallowsW3K1PairRate_two_eq mallowsHighNoiseW3Spec rfl
        · simpa [mallowsW3StaticKApprovalPairRate, pUp, pDown,
            mallowsHighNoiseW3PairUpOfRule,
            mallowsHighNoiseW3PairDownOfRule, mallowsHighNoiseW3Spec,
            MallowsSpec.ofQ] using
            mallowsW3K2PairRate_two_eq mallowsHighNoiseW3Spec rfl
        · simpa [mallowsW3StaticKApprovalPairRate, pUp, pDown,
            mallowsHighNoiseW3PairUpOfRule,
            mallowsHighNoiseW3PairDownOfRule, mallowsHighNoiseW3Spec,
            MallowsSpec.ofQ] using
            mallowsW3K3PairRate_two_eq mallowsHighNoiseW3Spec rfl)
      (by
        simp [mallowsHighNoiseW3RandomizedKApprovalPairRate, pUp, pDown])

/-- Finite W-selection outcome-error probability for `K = 1` in a Mallows law. -/
def mallowsW3K1OutcomeErrorProbOf (M : MallowsSpec 2) (n : ℕ) : ℝ :=
  ∑ i : Fin 3,
    pairwiseScoringErrorProb M.law
      (fun π => kApprovalScore 1 π (mallowsW3WinnerCandidate i))
      (fun π => kApprovalScore 1 π mallowsW3LoserCandidate)
      n

/-- Finite W-selection outcome-error probability for `K = 2` in a Mallows law. -/
def mallowsW3K2OutcomeErrorProbOf (M : MallowsSpec 2) (n : ℕ) : ℝ :=
  ∑ i : Fin 3,
    pairwiseScoringErrorProb M.law
      (fun π => kApprovalScore 2 π (mallowsW3WinnerCandidate i))
      (fun π => kApprovalScore 2 π mallowsW3LoserCandidate)
      n

/-- Finite W-selection outcome-error probability for `K = 3` in a Mallows law. -/
def mallowsW3K3OutcomeErrorProbOf (M : MallowsSpec 2) (n : ℕ) : ℝ :=
  ∑ i : Fin 3,
    pairwiseScoringErrorProb M.law
      (fun π => kApprovalScore 3 π (mallowsW3WinnerCandidate i))
      (fun π => kApprovalScore 3 π mallowsW3LoserCandidate)
      n

/-- Concrete finite W-selection outcome-error probability for `K = 1`. -/
def mallowsHighNoiseW3K1OutcomeErrorProb (n : ℕ) : ℝ :=
  mallowsW3K1OutcomeErrorProbOf mallowsHighNoiseW3Spec n

/-- Concrete finite W-selection outcome-error probability for `K = 2`. -/
def mallowsHighNoiseW3K2OutcomeErrorProb (n : ℕ) : ℝ :=
  mallowsW3K2OutcomeErrorProbOf mallowsHighNoiseW3Spec n

/-- Concrete finite W-selection outcome-error probability for `K = 3`. -/
def mallowsHighNoiseW3K3OutcomeErrorProb (n : ℕ) : ℝ :=
  mallowsW3K3OutcomeErrorProbOf mallowsHighNoiseW3Spec n

private theorem mallowsHighNoiseW3K2_pairUp_pos (i : Fin 3) :
    0 <
      mallowsTopTwoPairUpProb mallowsHighNoiseW3Spec
        (mallowsW3WinnerCandidate i) mallowsW3LoserCandidate := by
  fin_cases i
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopTwoPairUpProb_03_eq_mallowsW3K2Up0
      mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K2Up0, mallowsHighNoisePhi, mallowsW3N3,
      mallowsW3N4, mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopTwoPairUpProb_13_eq_mallowsW3K2Up1
      mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K2Up1, mallowsHighNoisePhi, mallowsW3N3,
      mallowsW3N4, mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopTwoPairUpProb_23_eq_mallowsW3K2Up
      mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K2Up, mallowsHighNoisePhi, mallowsW3N3,
      mallowsW3N4, mallowsHighNoiseW3Spec, MallowsSpec.ofQ]

private theorem mallowsHighNoiseW3K2_pairDown_pos (i : Fin 3) :
    0 <
      mallowsTopTwoPairUpProb mallowsHighNoiseW3Spec
        mallowsW3LoserCandidate (mallowsW3WinnerCandidate i) := by
  fin_cases i
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopTwoPairUpProb_30_eq_mallowsW3K2Down0
      mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K2Down0, mallowsHighNoisePhi, mallowsW3N3,
      mallowsW3N4, mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopTwoPairUpProb_31_eq_mallowsW3K2Down1
      mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K2Down1, mallowsHighNoisePhi, mallowsW3N3,
      mallowsW3N4, mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopTwoPairUpProb_32_eq_mallowsW3K2Down
      mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K2Down, mallowsHighNoisePhi, mallowsW3N3,
      mallowsW3N4, mallowsHighNoiseW3Spec, MallowsSpec.ofQ]

private theorem mallowsHighNoiseW3K2_pairDown_le_pairUp (i : Fin 3) :
    mallowsTopTwoPairUpProb mallowsHighNoiseW3Spec
        mallowsW3LoserCandidate (mallowsW3WinnerCandidate i) ≤
      mallowsTopTwoPairUpProb mallowsHighNoiseW3Spec
        (mallowsW3WinnerCandidate i) mallowsW3LoserCandidate := by
  fin_cases i
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopTwoPairUpProb_30_eq_mallowsW3K2Down0
        mallowsHighNoiseW3Spec rfl,
      mallowsTopTwoPairUpProb_03_eq_mallowsW3K2Up0
        mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K2Up0, mallowsW3K2Down0, mallowsHighNoisePhi,
      mallowsW3N3, mallowsW3N4, mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopTwoPairUpProb_31_eq_mallowsW3K2Down1
        mallowsHighNoiseW3Spec rfl,
      mallowsTopTwoPairUpProb_13_eq_mallowsW3K2Up1
        mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K2Up1, mallowsW3K2Down1, mallowsHighNoisePhi,
      mallowsW3N3, mallowsW3N4, mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopTwoPairUpProb_32_eq_mallowsW3K2Down
        mallowsHighNoiseW3Spec rfl,
      mallowsTopTwoPairUpProb_23_eq_mallowsW3K2Up
        mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K2Up, mallowsW3K2Down, mallowsHighNoisePhi,
      mallowsW3N3, mallowsW3N4, mallowsHighNoiseW3Spec, MallowsSpec.ofQ]

private theorem mallowsHighNoiseW3K3_pairUp_pos (i : Fin 3) :
    0 <
      mallowsTopThreePairUpProb mallowsHighNoiseW3Spec
        (mallowsW3WinnerCandidate i) mallowsW3LoserCandidate := by
  fin_cases i
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopThreePairUpProb_03_eq_mallowsW3K3Up
      mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4,
      mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopThreePairUpProb_13_eq_mallowsW3K3Up
      mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4,
      mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopThreePairUpProb_23_eq_mallowsW3K3Up
      mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4,
      mallowsHighNoiseW3Spec, MallowsSpec.ofQ]

private theorem mallowsHighNoiseW3K3_pairDown_pos (i : Fin 3) :
    0 <
      mallowsTopThreePairUpProb mallowsHighNoiseW3Spec
        mallowsW3LoserCandidate (mallowsW3WinnerCandidate i) := by
  fin_cases i
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopThreePairUpProb_30_eq_mallowsW3K3Down0
      mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K3Down0, mallowsHighNoisePhi, mallowsW3N4,
      mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopThreePairUpProb_31_eq_mallowsW3K3Down1
      mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K3Down1, mallowsHighNoisePhi, mallowsW3N4,
      mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopThreePairUpProb_32_eq_mallowsW3K3Down
      mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K3Down, mallowsHighNoisePhi, mallowsW3N4,
      mallowsHighNoiseW3Spec, MallowsSpec.ofQ]

private theorem mallowsHighNoiseW3K3_pairDown_le_pairUp (i : Fin 3) :
    mallowsTopThreePairUpProb mallowsHighNoiseW3Spec
        mallowsW3LoserCandidate (mallowsW3WinnerCandidate i) ≤
      mallowsTopThreePairUpProb mallowsHighNoiseW3Spec
        (mallowsW3WinnerCandidate i) mallowsW3LoserCandidate := by
  fin_cases i
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopThreePairUpProb_30_eq_mallowsW3K3Down0
        mallowsHighNoiseW3Spec rfl,
      mallowsTopThreePairUpProb_03_eq_mallowsW3K3Up
        mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K3Up, mallowsW3K3Down0, mallowsHighNoisePhi,
      mallowsW3N4, mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopThreePairUpProb_31_eq_mallowsW3K3Down1
        mallowsHighNoiseW3Spec rfl,
      mallowsTopThreePairUpProb_13_eq_mallowsW3K3Up
        mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K3Up, mallowsW3K3Down1, mallowsHighNoisePhi,
      mallowsW3N4, mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  · dsimp [mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
    rw [mallowsTopThreePairUpProb_32_eq_mallowsW3K3Down
        mallowsHighNoiseW3Spec rfl,
      mallowsTopThreePairUpProb_23_eq_mallowsW3K3Up
        mallowsHighNoiseW3Spec rfl]
    norm_num [mallowsW3K3Up, mallowsW3K3Down, mallowsHighNoisePhi,
      mallowsW3N4, mallowsHighNoiseW3Spec, MallowsSpec.ofQ]

private theorem mallowsW3Winner_ne_loser (i : Fin 3) :
    mallowsW3WinnerCandidate i ≠ mallowsW3LoserCandidate := by
  fin_cases i <;> decide

/--
Model-parametric `K = 1` W-selection aggregate exact-rate theorem: for any
identity-centered four-candidate Mallows law with `q = 4/5`, the finite sum of
the three winner-vs-loser iid pairwise error probabilities has exponential
rate equal to the finite 1-approval outcome-learning rate.
-/
theorem mallowsHighNoiseW3K1_outcome_error_exact_rate_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    HasExponentialRate
      (mallowsW3K1OutcomeErrorProbOf M)
      (mallowsW3K1OutcomeRate M) := by
  let pUp : Fin 3 → ℝ := fun i =>
    firstChoiceProb M.law (mallowsW3WinnerCandidate i)
  let pDown : Fin 3 → ℝ := fun _ =>
    firstChoiceProb M.law mallowsW3LoserCandidate
  have h :=
    outcomeError_hasExponentialRate_of_kApproval_relevant_pairs
      (law := M.law)
      (K := 1)
      (hi := mallowsW3WinnerCandidate)
      (lo := fun _ => mallowsW3LoserCandidate)
      (pUp := pUp)
      (pDown := pDown)
      (pairWeight := fun _ : Fin 3 => (1 : ℝ))
      (minRate := mallowsW3K1OutcomeRate M)
      (pairMin := (2 : Fin 3))
      (hUp := by
        intro i
        fin_cases i
        · dsimp [pUp, mallowsW3WinnerCandidate]
          rw [mallowsFirstChoiceProb_0_eq M hcenter, hq]
          norm_num [mallowsW3N4, mallowsHighNoisePhi]
        · dsimp [pUp, mallowsW3WinnerCandidate]
          rw [mallowsFirstChoiceProb_1_eq M hcenter, hq]
          norm_num [mallowsW3N4, mallowsHighNoisePhi]
        · dsimp [pUp, mallowsW3WinnerCandidate]
          rw [mallowsFirstChoiceProb_2_eq M hcenter, hq]
          norm_num [mallowsW3N4, mallowsHighNoisePhi])
      (hDown := by
        intro i
        dsimp [pDown, mallowsW3LoserCandidate]
        rw [mallowsFirstChoiceProb_3_eq M hcenter, hq]
        norm_num [mallowsW3N4, mallowsHighNoisePhi])
      (hle := by
        intro i
        fin_cases i
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate,
            mallowsW3LoserCandidate]
          rw [mallowsFirstChoiceProb_0_eq M hcenter,
            mallowsFirstChoiceProb_3_eq M hcenter, hq]
          norm_num [mallowsW3N4, mallowsHighNoisePhi]
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate,
            mallowsW3LoserCandidate]
          rw [mallowsFirstChoiceProb_1_eq M hcenter,
            mallowsFirstChoiceProb_3_eq M hcenter, hq]
          norm_num [mallowsW3N4, mallowsHighNoisePhi]
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate,
            mallowsW3LoserCandidate]
          rw [mallowsFirstChoiceProb_2_eq M hcenter,
            mallowsFirstChoiceProb_3_eq M hcenter, hq]
          norm_num [mallowsW3N4, mallowsHighNoisePhi])
      (hUpProb := by
        intro i
        rw [kApprovalPairUpProb_one_eq_firstChoiceProb
          M.law (mallowsW3Winner_ne_loser i)])
      (hDownProb := by
        intro i
        rw [kApprovalPairDownProb_eq_pairUpProb_swap]
        rw [kApprovalPairUpProb_one_eq_firstChoiceProb
          M.law (Ne.symm (mallowsW3Winner_ne_loser i))])
      (hweight := by intro i; norm_num)
      (hweight_pos := by norm_num)
      (hrate_min := by
        change
          mallowsW3K1PairRate M (2 : Fin 3) =
            mallowsW3K1OutcomeRate M
        exact (mallowsHighNoiseW3K1OutcomeRate_eq_pair2_of_mallows
          M hcenter hq).symm)
      (hrate_ge := by
        intro i
        change
          mallowsW3K1OutcomeRate M ≤ mallowsW3K1PairRate M i
        unfold mallowsW3K1OutcomeRate finiteOutcomeLearningRate
        exact Finset.inf'_le _ (by simp))
  convert h using 1
  ext n
  simp [mallowsW3K1OutcomeErrorProbOf,
    kApprovalRelevantPairRateCertificate,
    AppliedModelingLib.Probability.FiniteErrorRateCertificate.aggregateError]

/--
Model-parametric `K = 1` W-selection aggregate convergence theorem: in any
identity-centered four-candidate Mallows law with `q = 4/5`, the finite sum of
the three winner-vs-loser iid pairwise error probabilities tends to zero.
-/
theorem mallowsHighNoiseW3K1_outcome_error_tendsto_zero_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    Filter.Tendsto
      (mallowsW3K1OutcomeErrorProbOf M)
      Filter.atTop (nhds 0) := by
  let pUp : Fin 3 → ℝ := fun i =>
    firstChoiceProb M.law (mallowsW3WinnerCandidate i)
  let pDown : Fin 3 → ℝ := fun _ =>
    firstChoiceProb M.law mallowsW3LoserCandidate
  have h :=
    outcomeError_tendsto_zero_of_kApproval_relevant_pairs
      (law := M.law)
      (K := 1)
      (hi := mallowsW3WinnerCandidate)
      (lo := fun _ => mallowsW3LoserCandidate)
      (pUp := pUp)
      (pDown := pDown)
      (pairWeight := fun _ : Fin 3 => (1 : ℝ))
      (rateFloor := mallowsW3K1OutcomeRate M)
      (hUp := by
        intro i
        fin_cases i
        · dsimp [pUp, mallowsW3WinnerCandidate]
          rw [mallowsFirstChoiceProb_0_eq M hcenter, hq]
          norm_num [mallowsW3N4, mallowsHighNoisePhi]
        · dsimp [pUp, mallowsW3WinnerCandidate]
          rw [mallowsFirstChoiceProb_1_eq M hcenter, hq]
          norm_num [mallowsW3N4, mallowsHighNoisePhi]
        · dsimp [pUp, mallowsW3WinnerCandidate]
          rw [mallowsFirstChoiceProb_2_eq M hcenter, hq]
          norm_num [mallowsW3N4, mallowsHighNoisePhi])
      (hDown := by
        intro i
        dsimp [pDown, mallowsW3LoserCandidate]
        rw [mallowsFirstChoiceProb_3_eq M hcenter, hq]
        norm_num [mallowsW3N4, mallowsHighNoisePhi])
      (hle := by
        intro i
        fin_cases i
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate,
            mallowsW3LoserCandidate]
          rw [mallowsFirstChoiceProb_0_eq M hcenter,
            mallowsFirstChoiceProb_3_eq M hcenter, hq]
          norm_num [mallowsW3N4, mallowsHighNoisePhi]
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate,
            mallowsW3LoserCandidate]
          rw [mallowsFirstChoiceProb_1_eq M hcenter,
            mallowsFirstChoiceProb_3_eq M hcenter, hq]
          norm_num [mallowsW3N4, mallowsHighNoisePhi]
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate,
            mallowsW3LoserCandidate]
          rw [mallowsFirstChoiceProb_2_eq M hcenter,
            mallowsFirstChoiceProb_3_eq M hcenter, hq]
          norm_num [mallowsW3N4, mallowsHighNoisePhi])
      (hUpProb := by
        intro i
        rw [kApprovalPairUpProb_one_eq_firstChoiceProb
          M.law (mallowsW3Winner_ne_loser i)])
      (hDownProb := by
        intro i
        rw [kApprovalPairDownProb_eq_pairUpProb_swap]
        rw [kApprovalPairUpProb_one_eq_firstChoiceProb
          M.law (Ne.symm (mallowsW3Winner_ne_loser i))])
      (hweight := by intro i; norm_num)
      (hrateFloor_pos :=
        mallowsHighNoiseW3K1OutcomeRate_pos_of_mallows M hcenter hq)
      (hrateFloor := by
        intro i
        change
          mallowsW3K1OutcomeRate M ≤ mallowsW3K1PairRate M i
        unfold mallowsW3K1OutcomeRate finiteOutcomeLearningRate
        exact Finset.inf'_le _ (by simp))
  convert h using 1
  ext n
  simp [mallowsW3K1OutcomeErrorProbOf,
    kApprovalRelevantPairRateCertificate,
    AppliedModelingLib.Probability.FiniteErrorRateCertificate.aggregateError]

/--
Model-parametric `K = 2` W-selection aggregate exact-rate theorem: for any
identity-centered four-candidate Mallows law with `q = 4/5`, the finite sum of
the three winner-vs-loser iid pairwise error probabilities has exponential
rate equal to the finite 2-approval outcome-learning rate.
-/
theorem mallowsHighNoiseW3K2_outcome_error_exact_rate_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    HasExponentialRate
      (mallowsW3K2OutcomeErrorProbOf M)
      (mallowsW3K2OutcomeRate M) := by
  let pUp : Fin 3 → ℝ := fun i =>
    mallowsTopTwoPairUpProb M
      (mallowsW3WinnerCandidate i) mallowsW3LoserCandidate
  let pDown : Fin 3 → ℝ := fun i =>
    mallowsTopTwoPairUpProb M
      mallowsW3LoserCandidate (mallowsW3WinnerCandidate i)
  have h :=
    outcomeError_hasExponentialRate_of_kApproval_relevant_pairs
      (law := M.law)
      (K := 2)
      (hi := mallowsW3WinnerCandidate)
      (lo := fun _ => mallowsW3LoserCandidate)
      (pUp := pUp)
      (pDown := pDown)
      (pairWeight := fun _ : Fin 3 => (1 : ℝ))
      (minRate := mallowsW3K2OutcomeRate M)
      (pairMin := (2 : Fin 3))
      (hUp := by
        intro i
        fin_cases i
        · dsimp [pUp, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_03_eq_mallowsW3K2Up0 M hcenter,
            hq]
          norm_num [mallowsW3K2Up0, mallowsHighNoisePhi, mallowsW3N3,
            mallowsW3N4]
        · dsimp [pUp, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_13_eq_mallowsW3K2Up1 M hcenter,
            hq]
          norm_num [mallowsW3K2Up1, mallowsHighNoisePhi, mallowsW3N3,
            mallowsW3N4]
        · dsimp [pUp, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_23_eq_mallowsW3K2Up M hcenter,
            hq]
          norm_num [mallowsW3K2Up, mallowsHighNoisePhi, mallowsW3N3,
            mallowsW3N4])
      (hDown := by
        intro i
        fin_cases i
        · dsimp [pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_30_eq_mallowsW3K2Down0 M hcenter,
            hq]
          norm_num [mallowsW3K2Down0, mallowsHighNoisePhi, mallowsW3N3,
            mallowsW3N4]
        · dsimp [pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_31_eq_mallowsW3K2Down1 M hcenter,
            hq]
          norm_num [mallowsW3K2Down1, mallowsHighNoisePhi, mallowsW3N3,
            mallowsW3N4]
        · dsimp [pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_32_eq_mallowsW3K2Down M hcenter,
            hq]
          norm_num [mallowsW3K2Down, mallowsHighNoisePhi, mallowsW3N3,
            mallowsW3N4])
      (hle := by
        intro i
        fin_cases i
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_30_eq_mallowsW3K2Down0 M hcenter,
            mallowsTopTwoPairUpProb_03_eq_mallowsW3K2Up0 M hcenter,
            hq]
          norm_num [mallowsW3K2Up0, mallowsW3K2Down0,
            mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4]
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_31_eq_mallowsW3K2Down1 M hcenter,
            mallowsTopTwoPairUpProb_13_eq_mallowsW3K2Up1 M hcenter,
            hq]
          norm_num [mallowsW3K2Up1, mallowsW3K2Down1,
            mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4]
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_32_eq_mallowsW3K2Down M hcenter,
            mallowsTopTwoPairUpProb_23_eq_mallowsW3K2Up M hcenter,
            hq]
          norm_num [mallowsW3K2Up, mallowsW3K2Down,
            mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4])
      (hUpProb := by
        intro i
        rw [← mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb
          M (mallowsW3Winner_ne_loser i)])
      (hDownProb := by
        intro i
        rw [kApprovalPairDownProb_eq_pairUpProb_swap]
        rw [← mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb
          M (Ne.symm (mallowsW3Winner_ne_loser i))])
      (hweight := by intro i; norm_num)
      (hweight_pos := by norm_num)
      (hrate_min := by
        change
          mallowsW3K2PairRate M (2 : Fin 3) =
            mallowsW3K2OutcomeRate M
        exact (mallowsHighNoiseW3K2OutcomeRate_eq_pair2_of_mallows
          M hcenter hq).symm)
      (hrate_ge := by
        intro i
        change
          mallowsW3K2OutcomeRate M ≤ mallowsW3K2PairRate M i
        unfold mallowsW3K2OutcomeRate finiteOutcomeLearningRate
        exact Finset.inf'_le _ (by simp))
  convert h using 1
  ext n
  simp [mallowsW3K2OutcomeErrorProbOf,
    kApprovalRelevantPairRateCertificate,
    AppliedModelingLib.Probability.FiniteErrorRateCertificate.aggregateError]

/--
Model-parametric `K = 2` W-selection aggregate convergence theorem: in any
identity-centered four-candidate Mallows law with `q = 4/5`, the finite sum of
the three winner-vs-loser iid pairwise error probabilities tends to zero.
-/
theorem mallowsHighNoiseW3K2_outcome_error_tendsto_zero_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    Filter.Tendsto
      (mallowsW3K2OutcomeErrorProbOf M)
      Filter.atTop (nhds 0) := by
  let pUp : Fin 3 → ℝ := fun i =>
    mallowsTopTwoPairUpProb M
      (mallowsW3WinnerCandidate i) mallowsW3LoserCandidate
  let pDown : Fin 3 → ℝ := fun i =>
    mallowsTopTwoPairUpProb M
      mallowsW3LoserCandidate (mallowsW3WinnerCandidate i)
  have h :=
    outcomeError_tendsto_zero_of_kApproval_relevant_pairs
      (law := M.law)
      (K := 2)
      (hi := mallowsW3WinnerCandidate)
      (lo := fun _ => mallowsW3LoserCandidate)
      (pUp := pUp)
      (pDown := pDown)
      (pairWeight := fun _ : Fin 3 => (1 : ℝ))
      (rateFloor := mallowsW3K2OutcomeRate M)
      (hUp := by
        intro i
        fin_cases i
        · dsimp [pUp, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_03_eq_mallowsW3K2Up0 M hcenter,
            hq]
          norm_num [mallowsW3K2Up0, mallowsHighNoisePhi, mallowsW3N3,
            mallowsW3N4]
        · dsimp [pUp, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_13_eq_mallowsW3K2Up1 M hcenter,
            hq]
          norm_num [mallowsW3K2Up1, mallowsHighNoisePhi, mallowsW3N3,
            mallowsW3N4]
        · dsimp [pUp, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_23_eq_mallowsW3K2Up M hcenter,
            hq]
          norm_num [mallowsW3K2Up, mallowsHighNoisePhi, mallowsW3N3,
            mallowsW3N4])
      (hDown := by
        intro i
        fin_cases i
        · dsimp [pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_30_eq_mallowsW3K2Down0 M hcenter,
            hq]
          norm_num [mallowsW3K2Down0, mallowsHighNoisePhi, mallowsW3N3,
            mallowsW3N4]
        · dsimp [pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_31_eq_mallowsW3K2Down1 M hcenter,
            hq]
          norm_num [mallowsW3K2Down1, mallowsHighNoisePhi, mallowsW3N3,
            mallowsW3N4]
        · dsimp [pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_32_eq_mallowsW3K2Down M hcenter,
            hq]
          norm_num [mallowsW3K2Down, mallowsHighNoisePhi, mallowsW3N3,
            mallowsW3N4])
      (hle := by
        intro i
        fin_cases i
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_30_eq_mallowsW3K2Down0 M hcenter,
            mallowsTopTwoPairUpProb_03_eq_mallowsW3K2Up0 M hcenter,
            hq]
          norm_num [mallowsW3K2Up0, mallowsW3K2Down0,
            mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4]
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_31_eq_mallowsW3K2Down1 M hcenter,
            mallowsTopTwoPairUpProb_13_eq_mallowsW3K2Up1 M hcenter,
            hq]
          norm_num [mallowsW3K2Up1, mallowsW3K2Down1,
            mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4]
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopTwoPairUpProb_32_eq_mallowsW3K2Down M hcenter,
            mallowsTopTwoPairUpProb_23_eq_mallowsW3K2Up M hcenter,
            hq]
          norm_num [mallowsW3K2Up, mallowsW3K2Down,
            mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4])
      (hUpProb := by
        intro i
        rw [← mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb
          M (mallowsW3Winner_ne_loser i)])
      (hDownProb := by
        intro i
        rw [kApprovalPairDownProb_eq_pairUpProb_swap]
        rw [← mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb
          M (Ne.symm (mallowsW3Winner_ne_loser i))])
      (hweight := by intro i; norm_num)
      (hrateFloor_pos :=
        mallowsHighNoiseW3K2OutcomeRate_pos_of_mallows M hcenter hq)
      (hrateFloor := by
        intro i
        change
          mallowsW3K2OutcomeRate M ≤ mallowsW3K2PairRate M i
        unfold mallowsW3K2OutcomeRate finiteOutcomeLearningRate
        exact Finset.inf'_le _ (by simp))
  convert h using 1
  ext n
  simp [mallowsW3K2OutcomeErrorProbOf,
    kApprovalRelevantPairRateCertificate,
    AppliedModelingLib.Probability.FiniteErrorRateCertificate.aggregateError]

/--
Concrete `K = 1` W-selection aggregate exact-rate theorem: the finite sum of
the three winner-vs-loser iid pairwise error probabilities has exponential
rate equal to the proved finite outcome-learning rate.
-/
theorem mallowsHighNoiseW3K1_outcome_error_exact_rate_concrete :
    HasExponentialRate
      mallowsHighNoiseW3K1OutcomeErrorProb
      (mallowsW3K1OutcomeRate mallowsHighNoiseW3Spec) := by
  simpa [mallowsHighNoiseW3K1OutcomeErrorProb] using
    mallowsHighNoiseW3K1_outcome_error_exact_rate_of_mallows
      mallowsHighNoiseW3Spec rfl rfl

/-- The concrete high-noise `K = 1` Mallows W-selection outcome rate is positive. -/
theorem mallowsHighNoiseW3K1OutcomeRate_pos_concrete :
    0 < mallowsW3K1OutcomeRate mallowsHighNoiseW3Spec :=
  mallowsHighNoiseW3K1OutcomeRate_pos_of_mallows
    mallowsHighNoiseW3Spec rfl rfl

/--
Concrete `K = 1` W-selection aggregate convergence theorem: the finite sum of
the three winner-vs-loser iid pairwise error probabilities tends to zero.
-/
theorem mallowsHighNoiseW3K1_outcome_error_tendsto_zero_concrete :
    Filter.Tendsto
      mallowsHighNoiseW3K1OutcomeErrorProb
      Filter.atTop (nhds 0) := by
  simpa [mallowsHighNoiseW3K1OutcomeErrorProb] using
    mallowsHighNoiseW3K1_outcome_error_tendsto_zero_of_mallows
      mallowsHighNoiseW3Spec rfl rfl

/--
Concrete `K = 2` W-selection aggregate exact-rate theorem: the finite sum of
the three winner-vs-loser iid pairwise error probabilities has exponential
rate equal to the proved finite outcome-learning rate.
-/
theorem mallowsHighNoiseW3K2_outcome_error_exact_rate_concrete :
    HasExponentialRate
      mallowsHighNoiseW3K2OutcomeErrorProb
      (mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec) := by
  let pUp : Fin 3 → ℝ := fun i =>
    mallowsTopTwoPairUpProb mallowsHighNoiseW3Spec
      (mallowsW3WinnerCandidate i) mallowsW3LoserCandidate
  let pDown : Fin 3 → ℝ := fun i =>
    mallowsTopTwoPairUpProb mallowsHighNoiseW3Spec
      mallowsW3LoserCandidate (mallowsW3WinnerCandidate i)
  have h :=
    outcomeError_hasExponentialRate_of_kApproval_relevant_pairs
      (law := mallowsHighNoiseW3Spec.law)
      (K := 2)
      (hi := mallowsW3WinnerCandidate)
      (lo := fun _ => mallowsW3LoserCandidate)
      (pUp := pUp)
      (pDown := pDown)
      (pairWeight := fun _ : Fin 3 => (1 : ℝ))
      (minRate := mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec)
      (pairMin := (2 : Fin 3))
      (hUp := by
        intro i
        exact mallowsHighNoiseW3K2_pairUp_pos i)
      (hDown := by
        intro i
        exact mallowsHighNoiseW3K2_pairDown_pos i)
      (hle := by
        intro i
        exact mallowsHighNoiseW3K2_pairDown_le_pairUp i)
      (hUpProb := by
        intro i
        rw [← mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb
          mallowsHighNoiseW3Spec (mallowsW3Winner_ne_loser i)]
        )
      (hDownProb := by
        intro i
        rw [kApprovalPairDownProb_eq_pairUpProb_swap]
        rw [← mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb
          mallowsHighNoiseW3Spec
            (Ne.symm (mallowsW3Winner_ne_loser i))]
        )
      (hweight := by intro i; norm_num)
      (hweight_pos := by norm_num)
      (hrate_min := by
        change
          mallowsW3K2PairRate mallowsHighNoiseW3Spec (2 : Fin 3) =
            mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec
        exact (mallowsHighNoiseW3K2OutcomeRate_eq_pair2_of_mallows
          mallowsHighNoiseW3Spec rfl rfl).symm)
      (hrate_ge := by
        intro i
        change
          mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec ≤
            mallowsW3K2PairRate mallowsHighNoiseW3Spec i
        unfold mallowsW3K2OutcomeRate finiteOutcomeLearningRate
        exact Finset.inf'_le _ (by simp))
  convert h using 1
  ext n
  simp [mallowsHighNoiseW3K2OutcomeErrorProb,
    mallowsW3K2OutcomeErrorProbOf,
    kApprovalRelevantPairRateCertificate,
    AppliedModelingLib.Probability.FiniteErrorRateCertificate.aggregateError]

/-- The concrete high-noise `K = 2` Mallows W-selection outcome rate is positive. -/
theorem mallowsHighNoiseW3K2OutcomeRate_pos_concrete :
    0 < mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec :=
  mallowsHighNoiseW3K2OutcomeRate_pos_of_mallows
    mallowsHighNoiseW3Spec rfl rfl

/--
Concrete `K = 2` W-selection aggregate convergence theorem: the finite sum of
the three winner-vs-loser iid pairwise error probabilities tends to zero.
-/
theorem mallowsHighNoiseW3K2_outcome_error_tendsto_zero_concrete :
    Filter.Tendsto
      mallowsHighNoiseW3K2OutcomeErrorProb
      Filter.atTop (nhds 0) :=
  by
    simpa [mallowsHighNoiseW3K2OutcomeErrorProb] using
      mallowsHighNoiseW3K2_outcome_error_tendsto_zero_of_mallows
        mallowsHighNoiseW3Spec rfl rfl

/--
Model-parametric `K = 3` W-selection aggregate exact-rate theorem: for any
identity-centered four-candidate Mallows law with `q = 4/5`, the finite sum of
the three winner-vs-loser iid pairwise error probabilities has exponential
rate equal to the finite 3-approval outcome-learning rate.
-/
theorem mallowsHighNoiseW3K3_outcome_error_exact_rate_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    HasExponentialRate
      (mallowsW3K3OutcomeErrorProbOf M)
      (mallowsW3K3OutcomeRate M) := by
  let pUp : Fin 3 → ℝ := fun i =>
    mallowsTopThreePairUpProb M
      (mallowsW3WinnerCandidate i) mallowsW3LoserCandidate
  let pDown : Fin 3 → ℝ := fun i =>
    mallowsTopThreePairUpProb M
      mallowsW3LoserCandidate (mallowsW3WinnerCandidate i)
  have h :=
    outcomeError_hasExponentialRate_of_kApproval_relevant_pairs
      (law := M.law)
      (K := 3)
      (hi := mallowsW3WinnerCandidate)
      (lo := fun _ => mallowsW3LoserCandidate)
      (pUp := pUp)
      (pDown := pDown)
      (pairWeight := fun _ : Fin 3 => (1 : ℝ))
      (minRate := mallowsW3K3OutcomeRate M)
      (pairMin := (2 : Fin 3))
      (hUp := by
        intro i
        fin_cases i
        · dsimp [pUp, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_03_eq_mallowsW3K3Up M hcenter,
            hq]
          norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4]
        · dsimp [pUp, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_13_eq_mallowsW3K3Up M hcenter,
            hq]
          norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4]
        · dsimp [pUp, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_23_eq_mallowsW3K3Up M hcenter,
            hq]
          norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4])
      (hDown := by
        intro i
        fin_cases i
        · dsimp [pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_30_eq_mallowsW3K3Down0 M hcenter,
            hq]
          norm_num [mallowsW3K3Down0, mallowsHighNoisePhi, mallowsW3N4]
        · dsimp [pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_31_eq_mallowsW3K3Down1 M hcenter,
            hq]
          norm_num [mallowsW3K3Down1, mallowsHighNoisePhi, mallowsW3N4]
        · dsimp [pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_32_eq_mallowsW3K3Down M hcenter,
            hq]
          norm_num [mallowsW3K3Down, mallowsHighNoisePhi, mallowsW3N4])
      (hle := by
        intro i
        fin_cases i
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_30_eq_mallowsW3K3Down0 M hcenter,
            mallowsTopThreePairUpProb_03_eq_mallowsW3K3Up M hcenter,
            hq]
          norm_num [mallowsW3K3Up, mallowsW3K3Down0,
            mallowsHighNoisePhi, mallowsW3N4]
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_31_eq_mallowsW3K3Down1 M hcenter,
            mallowsTopThreePairUpProb_13_eq_mallowsW3K3Up M hcenter,
            hq]
          norm_num [mallowsW3K3Up, mallowsW3K3Down1,
            mallowsHighNoisePhi, mallowsW3N4]
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_32_eq_mallowsW3K3Down M hcenter,
            mallowsTopThreePairUpProb_23_eq_mallowsW3K3Up M hcenter,
            hq]
          norm_num [mallowsW3K3Up, mallowsW3K3Down,
            mallowsHighNoisePhi, mallowsW3N4])
      (hUpProb := by
        intro i
        rw [← mallowsTopThreePairUpProb_eq_kApprovalPairUpProb
          M (mallowsW3Winner_ne_loser i)])
      (hDownProb := by
        intro i
        rw [kApprovalPairDownProb_eq_pairUpProb_swap]
        rw [← mallowsTopThreePairUpProb_eq_kApprovalPairUpProb
          M (Ne.symm (mallowsW3Winner_ne_loser i))])
      (hweight := by intro i; norm_num)
      (hweight_pos := by norm_num)
      (hrate_min := by
        change
          mallowsW3K3PairRate M (2 : Fin 3) =
            mallowsW3K3OutcomeRate M
        exact (mallowsHighNoiseW3K3OutcomeRate_eq_pair2_of_mallows
          M hcenter hq).symm)
      (hrate_ge := by
        intro i
        change
          mallowsW3K3OutcomeRate M ≤ mallowsW3K3PairRate M i
        unfold mallowsW3K3OutcomeRate finiteOutcomeLearningRate
        exact Finset.inf'_le _ (by simp))
  convert h using 1
  ext n
  simp [mallowsW3K3OutcomeErrorProbOf,
    kApprovalRelevantPairRateCertificate,
    AppliedModelingLib.Probability.FiniteErrorRateCertificate.aggregateError]

/--
Model-parametric `K = 3` W-selection aggregate convergence theorem: in any
identity-centered four-candidate Mallows law with `q = 4/5`, the finite sum of
the three winner-vs-loser iid pairwise error probabilities tends to zero.
-/
theorem mallowsHighNoiseW3K3_outcome_error_tendsto_zero_of_mallows
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    Filter.Tendsto
      (mallowsW3K3OutcomeErrorProbOf M)
      Filter.atTop (nhds 0) := by
  let pUp : Fin 3 → ℝ := fun i =>
    mallowsTopThreePairUpProb M
      (mallowsW3WinnerCandidate i) mallowsW3LoserCandidate
  let pDown : Fin 3 → ℝ := fun i =>
    mallowsTopThreePairUpProb M
      mallowsW3LoserCandidate (mallowsW3WinnerCandidate i)
  have h :=
    outcomeError_tendsto_zero_of_kApproval_relevant_pairs
      (law := M.law)
      (K := 3)
      (hi := mallowsW3WinnerCandidate)
      (lo := fun _ => mallowsW3LoserCandidate)
      (pUp := pUp)
      (pDown := pDown)
      (pairWeight := fun _ : Fin 3 => (1 : ℝ))
      (rateFloor := mallowsW3K3OutcomeRate M)
      (hUp := by
        intro i
        fin_cases i
        · dsimp [pUp, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_03_eq_mallowsW3K3Up M hcenter,
            hq]
          norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4]
        · dsimp [pUp, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_13_eq_mallowsW3K3Up M hcenter,
            hq]
          norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4]
        · dsimp [pUp, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_23_eq_mallowsW3K3Up M hcenter,
            hq]
          norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4])
      (hDown := by
        intro i
        fin_cases i
        · dsimp [pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_30_eq_mallowsW3K3Down0 M hcenter,
            hq]
          norm_num [mallowsW3K3Down0, mallowsHighNoisePhi, mallowsW3N4]
        · dsimp [pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_31_eq_mallowsW3K3Down1 M hcenter,
            hq]
          norm_num [mallowsW3K3Down1, mallowsHighNoisePhi, mallowsW3N4]
        · dsimp [pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_32_eq_mallowsW3K3Down M hcenter,
            hq]
          norm_num [mallowsW3K3Down, mallowsHighNoisePhi, mallowsW3N4])
      (hle := by
        intro i
        fin_cases i
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_30_eq_mallowsW3K3Down0 M hcenter,
            mallowsTopThreePairUpProb_03_eq_mallowsW3K3Up M hcenter,
            hq]
          norm_num [mallowsW3K3Up, mallowsW3K3Down0,
            mallowsHighNoisePhi, mallowsW3N4]
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_31_eq_mallowsW3K3Down1 M hcenter,
            mallowsTopThreePairUpProb_13_eq_mallowsW3K3Up M hcenter,
            hq]
          norm_num [mallowsW3K3Up, mallowsW3K3Down1,
            mallowsHighNoisePhi, mallowsW3N4]
        · dsimp [pUp, pDown, mallowsW3WinnerCandidate, mallowsW3LoserCandidate]
          rw [mallowsTopThreePairUpProb_32_eq_mallowsW3K3Down M hcenter,
            mallowsTopThreePairUpProb_23_eq_mallowsW3K3Up M hcenter,
            hq]
          norm_num [mallowsW3K3Up, mallowsW3K3Down,
            mallowsHighNoisePhi, mallowsW3N4])
      (hUpProb := by
        intro i
        rw [← mallowsTopThreePairUpProb_eq_kApprovalPairUpProb
          M (mallowsW3Winner_ne_loser i)])
      (hDownProb := by
        intro i
        rw [kApprovalPairDownProb_eq_pairUpProb_swap]
        rw [← mallowsTopThreePairUpProb_eq_kApprovalPairUpProb
          M (Ne.symm (mallowsW3Winner_ne_loser i))])
      (hweight := by intro i; norm_num)
      (hrateFloor_pos :=
        mallowsHighNoiseW3K3OutcomeRate_pos_of_mallows M hcenter hq)
      (hrateFloor := by
        intro i
        change
          mallowsW3K3OutcomeRate M ≤ mallowsW3K3PairRate M i
        unfold mallowsW3K3OutcomeRate finiteOutcomeLearningRate
        exact Finset.inf'_le _ (by simp))
  convert h using 1
  ext n
  simp [mallowsW3K3OutcomeErrorProbOf,
    kApprovalRelevantPairRateCertificate,
    AppliedModelingLib.Probability.FiniteErrorRateCertificate.aggregateError]

/--
Concrete `K = 3` W-selection aggregate exact-rate theorem: the finite sum of
the three winner-vs-loser iid pairwise error probabilities has exponential
rate equal to the proved finite outcome-learning rate.
-/
theorem mallowsHighNoiseW3K3_outcome_error_exact_rate_concrete :
    HasExponentialRate
      mallowsHighNoiseW3K3OutcomeErrorProb
      (mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec) := by
  let pUp : Fin 3 → ℝ := fun i =>
    mallowsTopThreePairUpProb mallowsHighNoiseW3Spec
      (mallowsW3WinnerCandidate i) mallowsW3LoserCandidate
  let pDown : Fin 3 → ℝ := fun i =>
    mallowsTopThreePairUpProb mallowsHighNoiseW3Spec
      mallowsW3LoserCandidate (mallowsW3WinnerCandidate i)
  have h :=
    outcomeError_hasExponentialRate_of_kApproval_relevant_pairs
      (law := mallowsHighNoiseW3Spec.law)
      (K := 3)
      (hi := mallowsW3WinnerCandidate)
      (lo := fun _ => mallowsW3LoserCandidate)
      (pUp := pUp)
      (pDown := pDown)
      (pairWeight := fun _ : Fin 3 => (1 : ℝ))
      (minRate := mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec)
      (pairMin := (2 : Fin 3))
      (hUp := by
        intro i
        exact mallowsHighNoiseW3K3_pairUp_pos i)
      (hDown := by
        intro i
        exact mallowsHighNoiseW3K3_pairDown_pos i)
      (hle := by
        intro i
        exact mallowsHighNoiseW3K3_pairDown_le_pairUp i)
      (hUpProb := by
        intro i
        rw [← mallowsTopThreePairUpProb_eq_kApprovalPairUpProb
          mallowsHighNoiseW3Spec (mallowsW3Winner_ne_loser i)]
        )
      (hDownProb := by
        intro i
        rw [kApprovalPairDownProb_eq_pairUpProb_swap]
        rw [← mallowsTopThreePairUpProb_eq_kApprovalPairUpProb
          mallowsHighNoiseW3Spec
            (Ne.symm (mallowsW3Winner_ne_loser i))]
        )
      (hweight := by intro i; norm_num)
      (hweight_pos := by norm_num)
      (hrate_min := by
        change
          mallowsW3K3PairRate mallowsHighNoiseW3Spec (2 : Fin 3) =
            mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec
        exact (mallowsHighNoiseW3K3OutcomeRate_eq_pair2_of_mallows
          mallowsHighNoiseW3Spec rfl rfl).symm)
      (hrate_ge := by
        intro i
        change
          mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec ≤
            mallowsW3K3PairRate mallowsHighNoiseW3Spec i
        unfold mallowsW3K3OutcomeRate finiteOutcomeLearningRate
        exact Finset.inf'_le _ (by simp))
  convert h using 1
  ext n
  simp [mallowsHighNoiseW3K3OutcomeErrorProb,
    mallowsW3K3OutcomeErrorProbOf,
    kApprovalRelevantPairRateCertificate,
    AppliedModelingLib.Probability.FiniteErrorRateCertificate.aggregateError]

/-- The concrete high-noise `K = 3` Mallows W-selection outcome rate is positive. -/
theorem mallowsHighNoiseW3K3OutcomeRate_pos_concrete :
    0 < mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec :=
  mallowsHighNoiseW3K3OutcomeRate_pos_of_mallows
    mallowsHighNoiseW3Spec rfl rfl

/--
Concrete `K = 3` W-selection aggregate convergence theorem: the finite sum of
the three winner-vs-loser iid pairwise error probabilities tends to zero.
-/
theorem mallowsHighNoiseW3K3_outcome_error_tendsto_zero_concrete :
    Filter.Tendsto
      mallowsHighNoiseW3K3OutcomeErrorProb
      Filter.atTop (nhds 0) :=
  by
    simpa [mallowsHighNoiseW3K3OutcomeErrorProb] using
      mallowsHighNoiseW3K3_outcome_error_tendsto_zero_of_mallows
        mallowsHighNoiseW3Spec rfl rfl

end

end GGSG19TopThree
