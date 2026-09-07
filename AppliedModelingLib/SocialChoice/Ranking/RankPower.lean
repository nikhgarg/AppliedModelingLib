import AppliedModelingLib.Foundations.Math.FiniteSigns
import AppliedModelingLib.SocialChoice.Ranking.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# Rank-Power Algebra

Paper-neutral finite geometric sums over ranking positions.  These lemmas are
useful for Mallows-style rank-factorization arguments and for sequential
selection proofs that remove one rank and renormalize the remaining positions.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

noncomputable section

/-- The geometric rank-power sum over the candidate positions. -/
def candidateRankPowerSum (n : ℕ) (q : ℝ) : ℝ :=
  ∑ i : Candidate n, q ^ (i : ℕ)

/-- The same geometric rank-power sum, indexed from the worst rank downward. -/
def candidateRankReversePowerSum (n : ℕ) (q : ℝ) : ℝ :=
  ∑ i : Candidate n, q ^ (n + 1 - (i : ℕ))

/-- The geometric rank-power sum over the prefix of ranks up to `k`. -/
def candidateRankPrefixPowerSum
    (n : ℕ) (q : ℝ) (k : Fin (n + 1)) : ℝ :=
  ∑ i : Candidate n, if (i : ℕ) ≤ k.val then q ^ (i : ℕ) else 0

/--
Rank-power sum over all candidates except the removed rank, with lower ranks
unchanged and higher ranks shifted down by one.
-/
def candidateRankRemovalPowerSum
    (n : ℕ) (q : ℝ) (k : Candidate n) : ℝ :=
  ∑ r : Candidate n,
    if r < k then q ^ (r : ℕ)
    else if k < r then q ^ ((r : ℕ) - 1)
    else 0

/-- Rank-only numerator weight for the best remaining candidate after center
rank `k` has been removed. -/
def candidateRankBestAfterRemovalWeight
    (n : ℕ) (q : ℝ) (k r : Candidate n) : ℝ :=
  if r < k then
    q ^ (r : ℕ) * candidateRankRemovalPowerSum n q k + q ^ ((r : ℕ) + (k : ℕ))
  else if k < r then
    q ^ (r : ℕ) * candidateRankRemovalPowerSum n q k +
      q ^ ((k : ℕ) + (r : ℕ) - 1)
  else
    0

/-- Rank-only kernel for the K=2 up-event with selected rank `r` and excluded
rank `s`. -/
def candidateRankTopTwoPairKernel
    (n : ℕ) (q : ℝ) (r s : Candidate n) : ℝ :=
  ∑ t : Candidate n,
    if t ≠ r ∧ t ≠ s then q ^ ((r : ℕ) + (t : ℕ) - 1) else 0

theorem candidateRankTopTwoPairKernel_nonneg
    (n : ℕ) {q : ℝ} (hq_nonneg : 0 ≤ q) (r s : Candidate n) :
    0 ≤ candidateRankTopTwoPairKernel n q r s := by
  classical
  unfold candidateRankTopTwoPairKernel
  refine Finset.sum_nonneg ?_
  intro t _
  by_cases ht : t ≠ r ∧ t ≠ s
  · simp [ht, pow_nonneg hq_nonneg]
  · simp [ht]

theorem candidateRankTopTwoPairKernel_pos
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (hn : 0 < n)
    (r s : Candidate n) :
    0 < candidateRankTopTwoPairKernel n q r s := by
  classical
  rcases Fin.exists_ne_and_ne_of_two_lt r s (by omega : 2 < n + 2) with
    ⟨t, htr, hts⟩
  unfold candidateRankTopTwoPairKernel
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg (a₀ := t)
  · simp [htr, hts, pow_pos hq_pos]
  · intro u
    by_cases hu : u ≠ r ∧ u ≠ s
    · simp [hu, pow_nonneg hq_pos.le]
    · simp [hu]

theorem candidateRankTopTwoPairKernel_le_of_first_le
    (n : ℕ) {q : ℝ} (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    {r s x : Candidate n} (hrs : r ≤ s) (hxr : x ≠ r) (hxs : x ≠ s) :
    candidateRankTopTwoPairKernel n q s x ≤
      candidateRankTopTwoPairKernel n q r x := by
  classical
  unfold candidateRankTopTwoPairKernel
  calc
    (∑ t : Candidate n,
      if t ≠ s ∧ t ≠ x then q ^ ((s : ℕ) + (t : ℕ) - 1) else 0)
        =
      ∑ t : Candidate n,
        if Equiv.swap r s t ≠ s ∧ Equiv.swap r s t ≠ x then
          q ^ ((s : ℕ) + (Equiv.swap r s t : ℕ) - 1)
        else 0 := by
          simpa using
            (Equiv.sum_comp (Equiv.swap r s)
              (fun t : Candidate n =>
                if t ≠ s ∧ t ≠ x then
                  q ^ ((s : ℕ) + (t : ℕ) - 1)
                else 0)).symm
    _ ≤ ∑ t : Candidate n,
        if t ≠ r ∧ t ≠ x then q ^ ((r : ℕ) + (t : ℕ) - 1) else 0 := by
      refine Finset.sum_le_sum ?_
      intro t _
      have hswap_x : Equiv.swap r s x = x :=
        Equiv.swap_apply_of_ne_of_ne hxr hxs
      have hswap_ne_s : Equiv.swap r s t ≠ s ↔ t ≠ r := by
        rw [ne_eq, Equiv.swap_apply_eq_iff]
        simp
      have hswap_ne_x : Equiv.swap r s t ≠ x ↔ t ≠ x := by
        constructor
        · intro h ht
          apply h
          rw [ht, hswap_x]
        · intro h ht
          apply h
          have hswap_swap := congrArg (Equiv.swap r s) ht
          simpa [hswap_x] using hswap_swap
      have hcond :
          (Equiv.swap r s t ≠ s ∧ Equiv.swap r s t ≠ x) ↔
            (t ≠ r ∧ t ≠ x) := by
        constructor
        · intro h
          exact ⟨hswap_ne_s.1 h.1, hswap_ne_x.1 h.2⟩
        · intro h
          exact ⟨hswap_ne_s.2 h.1, hswap_ne_x.2 h.2⟩
      by_cases ht : t ≠ r ∧ t ≠ x
      · rw [if_pos (hcond.2 ht), if_pos ht]
        by_cases hts : t = s
        · rw [hts, Equiv.swap_apply_right]
          have hpow_arg :
              (s : ℕ) + (r : ℕ) - 1 = (r : ℕ) + (s : ℕ) - 1 := by
            omega
          rw [hpow_arg]
        · have hswap_t : Equiv.swap r s t = t :=
            Equiv.swap_apply_of_ne_of_ne ht.1 hts
          rw [hswap_t]
          exact pow_le_pow_of_le_one hq_nonneg hq_le_one (by
            have hrs_nat : (r : ℕ) ≤ (s : ℕ) := hrs
            omega)
      · rw [if_neg (by
          intro h
          exact ht (hcond.1 h)), if_neg ht]

theorem candidateRankTopTwoPairKernel_le_of_excluded_le
    (n : ℕ) {q : ℝ} (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    {r x y : Candidate n} (hxy : x ≤ y) (hrx : r ≠ x) (hry : r ≠ y) :
    candidateRankTopTwoPairKernel n q r x ≤
      candidateRankTopTwoPairKernel n q r y := by
  classical
  unfold candidateRankTopTwoPairKernel
  calc
    (∑ t : Candidate n,
      if t ≠ r ∧ t ≠ x then q ^ ((r : ℕ) + (t : ℕ) - 1) else 0)
        =
      ∑ t : Candidate n,
        if Equiv.swap x y t ≠ r ∧ Equiv.swap x y t ≠ x then
          q ^ ((r : ℕ) + (Equiv.swap x y t : ℕ) - 1)
        else 0 := by
          simpa using
            (Equiv.sum_comp (Equiv.swap x y)
              (fun t : Candidate n =>
                if t ≠ r ∧ t ≠ x then
                  q ^ ((r : ℕ) + (t : ℕ) - 1)
                else 0)).symm
    _ ≤ ∑ t : Candidate n,
        if t ≠ r ∧ t ≠ y then q ^ ((r : ℕ) + (t : ℕ) - 1) else 0 := by
      refine Finset.sum_le_sum ?_
      intro t _
      have hswap_r : Equiv.swap x y r = r :=
        Equiv.swap_apply_of_ne_of_ne hrx hry
      have hswap_ne_r : Equiv.swap x y t ≠ r ↔ t ≠ r := by
        constructor
        · intro h ht
          apply h
          rw [ht, hswap_r]
        · intro h ht
          apply h
          have hswap_swap := congrArg (Equiv.swap x y) ht
          simpa [hswap_r] using hswap_swap
      have hswap_ne_x : Equiv.swap x y t ≠ x ↔ t ≠ y := by
        rw [ne_eq, Equiv.swap_apply_eq_iff]
        simp
      have hcond :
          (Equiv.swap x y t ≠ r ∧ Equiv.swap x y t ≠ x) ↔
            (t ≠ r ∧ t ≠ y) := by
        constructor
        · intro h
          exact ⟨hswap_ne_r.1 h.1, hswap_ne_x.1 h.2⟩
        · intro h
          exact ⟨hswap_ne_r.2 h.1, hswap_ne_x.2 h.2⟩
      by_cases ht : t ≠ r ∧ t ≠ y
      · rw [if_pos (hcond.2 ht), if_pos ht]
        by_cases htx : t = x
        · rw [htx, Equiv.swap_apply_left]
          exact pow_le_pow_of_le_one hq_nonneg hq_le_one (by
            have hxy_nat : (x : ℕ) ≤ (y : ℕ) := hxy
            omega)
        · have hswap_t : Equiv.swap x y t = t :=
            Equiv.swap_apply_of_ne_of_ne htx ht.2
          rw [hswap_t]
      · rw [if_neg (by
          intro h
          exact ht (hcond.1 h)), if_neg ht]

theorem candidateRankRemovalPowerSum_pos
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (k : Candidate n) :
    0 < candidateRankRemovalPowerSum n q k := by
  classical
  unfold candidateRankRemovalPowerSum
  by_cases hk0 : k = (0 : Candidate n)
  · apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg (a₀ := (1 : Candidate n))
    · have hk_lt_one : k < (1 : Candidate n) := by
        rw [hk0]
        change (0 : ℕ) < 1
        omega
      have hnot : ¬(1 : Candidate n) < k := not_lt_of_gt hk_lt_one
      simp [hnot, hk_lt_one]
    · intro r
      by_cases hrk : r < k
      · simp [hrk, pow_nonneg (le_of_lt hq_pos) (r : ℕ)]
      · by_cases hkr : k < r
        · simp [hrk, hkr, pow_nonneg (le_of_lt hq_pos) ((r : ℕ) - 1)]
        · simp [hrk, hkr]
  · apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg (a₀ := (0 : Candidate n))
    · have hzero_lt : (0 : Candidate n) < k := by
        change 0 < (k : ℕ)
        by_contra hnot
        have hkval : (k : ℕ) = 0 := by omega
        exact hk0 (Fin.ext hkval)
      simp [hzero_lt]
    · intro r
      by_cases hrk : r < k
      · simp [hrk, pow_nonneg (le_of_lt hq_pos) (r : ℕ)]
      · by_cases hkr : k < r
        · simp [hrk, hkr, pow_nonneg (le_of_lt hq_pos) ((r : ℕ) - 1)]
        · simp [hrk, hkr]

theorem candidateRankRemovalPowerSum_nonneg
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (k : Candidate n) :
    0 ≤ candidateRankRemovalPowerSum n q k :=
  le_of_lt (candidateRankRemovalPowerSum_pos n hq_pos k)

theorem candidateRankBestAfterRemovalWeight_nonneg
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (k r : Candidate n) :
    0 ≤ candidateRankBestAfterRemovalWeight n q k r := by
  unfold candidateRankBestAfterRemovalWeight
  by_cases hrk : r < k
  · rw [if_pos hrk]
    exact add_nonneg
      (mul_nonneg (pow_nonneg (le_of_lt hq_pos) (r : ℕ))
        (candidateRankRemovalPowerSum_nonneg n hq_pos k))
      (pow_nonneg (le_of_lt hq_pos) ((r : ℕ) + (k : ℕ)))
  · rw [if_neg hrk]
    by_cases hkr : k < r
    · rw [if_pos hkr]
      exact add_nonneg
        (mul_nonneg (pow_nonneg (le_of_lt hq_pos) (r : ℕ))
          (candidateRankRemovalPowerSum_nonneg n hq_pos k))
        (pow_nonneg (le_of_lt hq_pos) ((k : ℕ) + (r : ℕ) - 1))
    · rw [if_neg hkr]

theorem candidateRankTopTwoPairKernel_eq_mul_sub_of_pos
    (n : ℕ) (q : ℝ) {r s : Candidate n}
    (hr_pos : 0 < (r : ℕ)) (hrs : r ≠ s) :
    candidateRankTopTwoPairKernel n q r s =
      q ^ ((r : ℕ) - 1) *
        (candidateRankPowerSum n q - q ^ (r : ℕ) - q ^ (s : ℕ)) := by
  classical
  have hpow :
      ∀ t : Candidate n,
        q ^ ((r : ℕ) + (t : ℕ) - 1) =
          q ^ ((r : ℕ) - 1) * q ^ (t : ℕ) := by
    intro t
    have hnat :
        (r : ℕ) + (t : ℕ) - 1 = ((r : ℕ) - 1) + (t : ℕ) := by
      omega
    rw [hnat, pow_add]
  have hfilter :
      (∑ t : Candidate n,
        if t ≠ r ∧ t ≠ s then q ^ (t : ℕ) else 0) =
        candidateRankPowerSum n q - q ^ (r : ℕ) - q ^ (s : ℕ) := by
    unfold candidateRankPowerSum
    have hs_mem : s ∈ (Finset.univ.erase r : Finset (Candidate n)) := by
      simp [Finset.mem_erase, hrs.symm]
    have hfilter_set :
        (Finset.univ.filter
            (fun t : Candidate n => t ≠ r ∧ t ≠ s)) =
          (Finset.univ.erase r).erase s := by
      ext t
      by_cases htr : t = r
      · simp [htr]
      · by_cases hts : t = s <;> simp [htr, hts]
    calc
      (∑ t : Candidate n,
        if t ≠ r ∧ t ≠ s then q ^ (t : ℕ) else 0)
          = (Finset.univ.filter
              (fun t : Candidate n => t ≠ r ∧ t ≠ s)).sum
                (fun t => q ^ (t : ℕ)) := by
            rw [Finset.sum_filter]
      _ = ((Finset.univ.erase r).erase s).sum
            (fun t : Candidate n => q ^ (t : ℕ)) := by
            rw [hfilter_set]
      _ = (Finset.univ.erase r).sum
            (fun t : Candidate n => q ^ (t : ℕ)) - q ^ (s : ℕ) := by
            rw [Finset.sum_erase_eq_sub hs_mem]
      _ = (∑ t : Candidate n, q ^ (t : ℕ)) - q ^ (r : ℕ) - q ^ (s : ℕ) := by
            rw [Finset.sum_erase_eq_sub (Finset.mem_univ r)]
  unfold candidateRankTopTwoPairKernel
  calc
    (∑ t : Candidate n,
      if t ≠ r ∧ t ≠ s then q ^ ((r : ℕ) + (t : ℕ) - 1) else 0)
        = ∑ t : Candidate n,
          if t ≠ r ∧ t ≠ s then
            q ^ ((r : ℕ) - 1) * q ^ (t : ℕ)
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro t _
            by_cases ht : t ≠ r ∧ t ≠ s
            · rw [if_pos ht, if_pos ht, hpow]
            · rw [if_neg ht, if_neg ht]
    _ = q ^ ((r : ℕ) - 1) *
        (∑ t : Candidate n,
          if t ≠ r ∧ t ≠ s then q ^ (t : ℕ) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro t _
          by_cases ht : t ≠ r ∧ t ≠ s <;> simp [ht]
    _ = q ^ ((r : ℕ) - 1) *
        (candidateRankPowerSum n q - q ^ (r : ℕ) - q ^ (s : ℕ)) := by
          rw [hfilter]

theorem candidateRankRemovalPowerSum_eq_range
    (n : ℕ) (q : ℝ) (k : Candidate n) :
    candidateRankRemovalPowerSum n q k =
      ∑ m ∈ Finset.range (n + 1), q ^ m := by
  classical
  unfold candidateRankRemovalPowerSum Candidate
  change
    (∑ x : Fin (n + 2),
      if x.val < k.val then q ^ x.val
      else if k.val < x.val then q ^ (x.val - 1)
      else 0) =
      ∑ m ∈ Finset.range (n + 1), q ^ m
  rw [Fin.sum_univ_eq_sum_range
    (fun x : ℕ =>
      if x < k.val then q ^ x
      else if k.val < x then q ^ (x - 1)
      else 0)
    (n + 2)]
  let a : ℕ := k.val
  have ha_le : a ≤ n + 1 := by
    have ha_lt : a < n + 2 := by
      simp [a]
    omega
  have hfilter_lt :
      (Finset.range (n + 2)).filter (fun i : ℕ => i < a) =
        Finset.range a := by
    ext i
    simp [a]
    omega
  have hfilter_gt :
      (Finset.range (n + 2)).filter (fun i : ℕ => a < i) =
        Finset.Ico (a + 1) (n + 2) := by
    ext i
    simp [Finset.mem_Ico]
    omega
  have hsplit :
      (∑ i ∈ Finset.range (n + 2),
        if i < a then q ^ i else if a < i then q ^ (i - 1) else 0) =
        (∑ i ∈ (Finset.range (n + 2)).filter (fun i : ℕ => i < a),
          q ^ i) +
          (∑ i ∈ (Finset.range (n + 2)).filter (fun i : ℕ => a < i),
            q ^ (i - 1)) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases hia : i < a
    · have hai_not : ¬a < i := not_lt_of_gt hia
      simp [hia, hai_not]
    · by_cases hai : a < i
      · simp [hia, hai]
      · simp [hia, hai]
  have hshift :
      (∑ i ∈ Finset.Ico (a + 1) (n + 2), q ^ (i - 1)) =
        ∑ i ∈ Finset.Ico a (n + 1), q ^ i := by
    have h :=
      (Finset.sum_Ico_add'
        (fun x : ℕ => q ^ (x - 1)) a (n + 1) 1).symm
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  calc
    (∑ i ∈ Finset.range (n + 2),
        if i < ↑k then q ^ i else if ↑k < i then q ^ (i - 1) else 0)
        =
        (∑ i ∈ Finset.range (n + 2),
          if i < a then q ^ i else if a < i then q ^ (i - 1) else 0) := by
          simp [a]
    _ = (∑ i ∈ Finset.range a, q ^ i) +
          (∑ i ∈ Finset.Ico (a + 1) (n + 2), q ^ (i - 1)) := by
          rw [hsplit, hfilter_lt, hfilter_gt]
    _ = (∑ i ∈ Finset.range a, q ^ i) +
          (∑ i ∈ Finset.Ico a (n + 1), q ^ i) := by
          rw [hshift]
    _ = ∑ m ∈ Finset.range (n + 1), q ^ m := by
          exact Finset.sum_range_add_sum_Ico (fun m : ℕ => q ^ m) ha_le

theorem candidateRankRemovalPowerSum_mul_one_sub
    (n : ℕ) (q : ℝ) (k : Candidate n) :
    candidateRankRemovalPowerSum n q k * (1 - q) = 1 - q ^ (n + 1) := by
  rw [candidateRankRemovalPowerSum_eq_range]
  exact geom_sum_mul_neg q (n + 1)

@[simp] theorem candidateRankBestAfterRemovalWeight_self
    (n : ℕ) (q : ℝ) (k : Candidate n) :
    candidateRankBestAfterRemovalWeight n q k k = 0 := by
  unfold candidateRankBestAfterRemovalWeight
  simp

theorem candidateRankBestAfterRemovalWeight_of_lt
    (n : ℕ) (q : ℝ) {k r : Candidate n} (hrk : r < k) :
    candidateRankBestAfterRemovalWeight n q k r =
      q ^ (r : ℕ) *
        (candidateRankRemovalPowerSum n q k + q ^ (k : ℕ)) := by
  unfold candidateRankBestAfterRemovalWeight
  rw [if_pos hrk]
  rw [pow_add]
  ring

theorem candidateRankBestAfterRemovalWeight_of_gt
    (n : ℕ) (q : ℝ) {k r : Candidate n} (hkr : k < r) :
    candidateRankBestAfterRemovalWeight n q k r =
      q ^ ((r : ℕ) - 1) *
        (q * candidateRankRemovalPowerSum n q k + q ^ (k : ℕ)) := by
  unfold candidateRankBestAfterRemovalWeight
  rw [if_neg (not_lt_of_gt hkr), if_pos hkr]
  have hr_pos : 0 < (r : ℕ) :=
    lt_of_le_of_lt (Nat.zero_le (k : ℕ)) hkr
  have hpow_r : q ^ (r : ℕ) = q ^ ((r : ℕ) - 1) * q := by
    calc
      q ^ (r : ℕ) = q ^ (((r : ℕ) - 1) + 1) := by
        congr 1
        omega
      _ = q ^ ((r : ℕ) - 1) * q := by rw [pow_add, pow_one]
  have hpow_kr :
      q ^ ((k : ℕ) + (r : ℕ) - 1) =
        q ^ (((r : ℕ) - 1) + (k : ℕ)) := by
    congr 1
    omega
  rw [hpow_r, hpow_kr, pow_add]
  ring

theorem candidateRankPowerSum_pos (n : ℕ) {q : ℝ} (hq_pos : 0 < q) :
    0 < candidateRankPowerSum n q := by
  classical
  unfold candidateRankPowerSum
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg (a₀ := (0 : Candidate n))
  · simp
  · intro i
    exact pow_nonneg (le_of_lt hq_pos) (i : ℕ)

theorem candidateRankReversePowerSum_pos (n : ℕ) {q : ℝ} (hq_pos : 0 < q) :
    0 < candidateRankReversePowerSum n q := by
  classical
  unfold candidateRankReversePowerSum
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
    (a₀ := (⟨n + 1, by omega⟩ : Candidate n))
  · simp
  · intro i
    exact pow_nonneg (le_of_lt hq_pos) _

theorem candidateRankPowerSum_strict_mono
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_nonneg : 0 ≤ q₁) (hq_lt : q₁ < q₂) :
    candidateRankPowerSum n q₁ < candidateRankPowerSum n q₂ := by
  classical
  unfold candidateRankPowerSum
  refine Finset.sum_lt_sum ?hle ?hstrict
  · intro i _
    exact pow_le_pow_left₀ hq₁_nonneg (le_of_lt hq_lt) (i : ℕ)
  · refine ⟨(1 : Candidate n), Finset.mem_univ _, ?_⟩
    simpa using hq_lt

theorem natPower_mul_lt_mul_natPower
    {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {i j : ℕ} (hij : i < j) :
    q₁ ^ j * q₂ ^ i < q₁ ^ i * q₂ ^ j := by
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  obtain ⟨d, hd_pos, hd_eq⟩ :
      ∃ d : ℕ, 0 < d ∧ j = i + d := by
    refine ⟨j - i, Nat.sub_pos_of_lt hij, ?_⟩
    exact (Nat.add_sub_of_le (le_of_lt hij)).symm
  have hpow : q₁ ^ d < q₂ ^ d := by
    exact pow_lt_pow_left₀ hq_lt (le_of_lt hq₁_pos) (Nat.ne_of_gt hd_pos)
  have hscale : 0 < q₁ ^ i * q₂ ^ i :=
    mul_pos (pow_pos hq₁_pos i) (pow_pos hq₂_pos i)
  have hmul := mul_lt_mul_of_pos_left hpow hscale
  rw [hd_eq, pow_add, pow_add]
  nlinarith

theorem natPower_cross_nonneg_of_le
    {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {a b : ℕ} (hab : a ≤ b) :
    0 ≤ q₁ ^ a * q₂ ^ b - q₂ ^ a * q₁ ^ b := by
  by_cases h_eq : a = b
  · subst b
    have hzero :
        q₁ ^ a * q₂ ^ a - q₂ ^ a * q₁ ^ a = 0 := by
      ring
    rw [hzero]
  · have hlt_ab : a < b := lt_of_le_of_ne hab h_eq
    exact le_of_lt (by
      have h := natPower_mul_lt_mul_natPower
        (q₁ := q₁) (q₂ := q₂) hq₁_pos hq_lt hlt_ab
      exact sub_pos.mpr (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h))

theorem candidateRankPowerSum_mul_one_sub (n : ℕ) (q : ℝ) :
    candidateRankPowerSum n q * (1 - q) = 1 - q ^ (n + 2) := by
  simpa [candidateRankPowerSum, Candidate, Fin.sum_univ_eq_sum_range] using
    (geom_sum_mul_neg q (n + 2))

theorem candidateRankPowerSum_inner_nonneg
    {n : ℕ} {q : ℝ} (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    {r s : Candidate n} (hrs : r < s) :
    0 ≤ (candidateRankPowerSum n q - q ^ (r : ℕ)) -
      q * (candidateRankPowerSum n q - q ^ (s : ℕ)) := by
  have hgeom := candidateRankPowerSum_mul_one_sub n q
  have hs_succ_le : s.val + 1 ≤ n + 2 := s.2
  have hpow_succ_le : q ^ (n + 2) ≤ q ^ (s.val + 1) :=
    pow_le_pow_of_le_one hq_nonneg hq_le_one hs_succ_le
  have hpow_r_le_one : q ^ (r : ℕ) ≤ 1 :=
    pow_le_one₀ hq_nonneg hq_le_one
  have hmain : 0 ≤ (1 - q ^ (r : ℕ)) + (q ^ (s.val + 1) - q ^ (n + 2)) := by
    exact add_nonneg (sub_nonneg.mpr hpow_r_le_one) (sub_nonneg.mpr hpow_succ_le)
  have hpow_succ : q * q ^ (s : ℕ) = q ^ (s.val + 1) := by
    rw [pow_succ']
  nlinarith

theorem candidateRankPowerSum_inner_pos_zero_one
    {n : ℕ} (hn : 0 < n) {q : ℝ} (hq_pos : 0 < q) (hq_lt_one : q < 1) :
    0 < (candidateRankPowerSum n q - q ^ (0 : ℕ)) -
      q * (candidateRankPowerSum n q - q ^ (1 : ℕ)) := by
  have hgeom := candidateRankPowerSum_mul_one_sub n q
  have hpow_lt : q ^ (n + 2) < q ^ (2 : ℕ) := by
    exact pow_lt_pow_right_of_lt_one₀ hq_pos hq_lt_one (by omega)
  nlinarith [hgeom, hpow_lt]

end

end Ranking
end SocialChoice
end AppliedModelingLib
