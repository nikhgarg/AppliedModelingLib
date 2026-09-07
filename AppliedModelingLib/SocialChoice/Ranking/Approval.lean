import AppliedModelingLib.SocialChoice.Ranking.Probability
import AppliedModelingLib.SocialChoice.Ranking.Sequential

/-!
# K-Approval on Finite Rankings

Reusable finite K-approval primitives for ranking laws.  These definitions are
probability-level and do not assume a Mallows law; Mallows-specific fiber
calculations can specialize the pair up/down probabilities.

## Main declarations

- `approvedByK`, `kApprovalScore`
- `kApprovalPairUpProb`, `kApprovalPairDownProb`, `kApprovalPairZeroProb`
- `lastRank`
- `approvedByK_allButOne_iff_rankOf_ne_lastRank`
- `kApprovalPairUpProb_allButOne_eq_rankOf_lastProb`
- `kApprovalPairDownProb_allButOne_eq_rankOf_lastProb`
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

noncomputable section

/-- Candidate `c` is approved by the top-`K` approval rule on ranking `π`. -/
def approvedByK {n : ℕ} (K : ℕ) (π : Ranking n) (c : Candidate n) : Prop :=
  (rankOf π c).val < K

instance instDecidableApprovedByK {n : ℕ}
    (K : ℕ) (π : Ranking n) (c : Candidate n) :
    Decidable (approvedByK K π c) := by
  unfold approvedByK
  infer_instance

instance instDecidablePredApprovedByK {n : ℕ}
    (K : ℕ) (c : Candidate n) :
    DecidablePred (fun π : Ranking n => approvedByK K π c) := by
  intro π
  infer_instance

/-- Real-valued K-approval score indicator. -/
def kApprovalScore {n : ℕ} (K : ℕ) (π : Ranking n) (c : Candidate n) : ℝ :=
  if approvedByK K π c then 1 else 0

/-- Probability that `hi` is approved and `lo` is not approved. -/
def kApprovalPairUpProb {n : ℕ}
    (μ : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n) : ℝ :=
  AppliedModelingLib.pmfProb μ
    (fun π => approvedByK K π hi ∧ ¬ approvedByK K π lo)

/-- Probability that `lo` is approved and `hi` is not approved. -/
def kApprovalPairDownProb {n : ℕ}
    (μ : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n) : ℝ :=
  AppliedModelingLib.pmfProb μ
    (fun π => approvedByK K π lo ∧ ¬ approvedByK K π hi)

/-- Probability that `hi` and `lo` receive the same K-approval score. -/
def kApprovalPairZeroProb {n : ℕ}
    (μ : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n) : ℝ :=
  AppliedModelingLib.pmfProb μ
    (fun π => kApprovalScore K π hi - kApprovalScore K π lo = 0)

/--
K-approval up-event as a rank cut: `hi` is above the approval cutoff and `lo`
is weakly below it.
-/
theorem kApprovalPairUpProb_eq_rank_cut {n : ℕ}
    (μ : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n) :
    kApprovalPairUpProb μ K hi lo =
      AppliedModelingLib.pmfProb μ
        (fun π : Ranking n => (rankOf π hi).val < K ∧ K ≤ (rankOf π lo).val) := by
  unfold kApprovalPairUpProb
  exact AppliedModelingLib.pmfProb_congr μ
    (fun π => by
      unfold approvedByK
      constructor
      · intro h
        exact ⟨h.1, Nat.le_of_not_gt h.2⟩
      · intro h
        exact ⟨h.1, Nat.not_lt.mpr h.2⟩)

/-- The last rank in a `Candidate n` universe. -/
def lastRank (n : ℕ) : Candidate n :=
  ⟨n + 1, by omega⟩

@[simp] theorem lastRank_val (n : ℕ) :
    (lastRank n).val = n + 1 := rfl

theorem lastRank_pos (n : ℕ) :
    0 < (lastRank n).val := by
  simp [lastRank]

theorem zero_ne_lastRank (n : ℕ) :
    (0 : Candidate n) ≠ lastRank n := by
  intro h
  have hval : (0 : ℕ) = n + 1 := by
    simpa [lastRank] using congrArg Fin.val h
  omega

@[simp] theorem not_approvedByK_zero {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    ¬ approvedByK 0 π c := by
  unfold approvedByK
  omega

@[simp] theorem approvedByK_all {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    approvedByK (n + 2) π c := by
  unfold approvedByK
  exact (rankOf π c).isLt

@[simp] theorem kApprovalScore_zero {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    kApprovalScore 0 π c = 0 := by
  simp [kApprovalScore]

@[simp] theorem kApprovalScore_all {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    kApprovalScore (n + 2) π c = 1 := by
  simp [kApprovalScore]

/--
The K-approval score gap is `+1` exactly when `hi` is approved and `lo` is not.
-/
theorem kApprovalScore_gap_eq_one_iff {n : ℕ}
    (K : ℕ) (π : Ranking n) (hi lo : Candidate n) :
    kApprovalScore K π hi - kApprovalScore K π lo = 1 ↔
      approvedByK K π hi ∧ ¬ approvedByK K π lo := by
  classical
  by_cases hhi : approvedByK K π hi <;>
    by_cases hlo : approvedByK K π lo <;>
      norm_num [kApprovalScore, hhi, hlo]

/--
The K-approval score gap is `-1` exactly when `lo` is approved and `hi` is not.
-/
theorem kApprovalScore_gap_eq_neg_one_iff {n : ℕ}
    (K : ℕ) (π : Ranking n) (hi lo : Candidate n) :
    kApprovalScore K π hi - kApprovalScore K π lo = -1 ↔
      approvedByK K π lo ∧ ¬ approvedByK K π hi := by
  classical
  by_cases hhi : approvedByK K π hi <;>
    by_cases hlo : approvedByK K π lo <;>
      norm_num [kApprovalScore, hhi, hlo]

/-- Every one-voter K-approval score gap is ternary. -/
theorem kApprovalScore_gap_ternary {n : ℕ}
    (K : ℕ) (π : Ranking n) (hi lo : Candidate n) :
    kApprovalScore K π hi - kApprovalScore K π lo = 1 ∨
      kApprovalScore K π hi - kApprovalScore K π lo = 0 ∨
      kApprovalScore K π hi - kApprovalScore K π lo = -1 := by
  classical
  by_cases hhi : approvedByK K π hi <;>
    by_cases hlo : approvedByK K π lo <;>
      norm_num [kApprovalScore, hhi, hlo]

theorem kApprovalPairUpProb_eq_score_gap_one {n : ℕ}
    (μ : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n) :
    kApprovalPairUpProb μ K hi lo =
      AppliedModelingLib.pmfProb μ
        (fun π => kApprovalScore K π hi - kApprovalScore K π lo = 1) := by
  exact AppliedModelingLib.pmfProb_congr μ
    (fun π => (kApprovalScore_gap_eq_one_iff K π hi lo).symm)

theorem kApprovalPairDownProb_eq_score_gap_neg_one {n : ℕ}
    (μ : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n) :
    kApprovalPairDownProb μ K hi lo =
      AppliedModelingLib.pmfProb μ
        (fun π => kApprovalScore K π hi - kApprovalScore K π lo = -1) := by
  exact AppliedModelingLib.pmfProb_congr μ
    (fun π => (kApprovalScore_gap_eq_neg_one_iff K π hi lo).symm)

/-- The down-event for `(hi, lo)` is the up-event for the swapped pair. -/
theorem kApprovalPairDownProb_eq_pairUpProb_swap {n : ℕ}
    (μ : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n) :
    kApprovalPairDownProb μ K hi lo =
      kApprovalPairUpProb μ K lo hi := by
  rfl

/-- One-approval approves exactly the first-choice candidate. -/
theorem approvedByK_one_iff_firstChoice {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    approvedByK 1 π c ↔ c = firstChoice π := by
  constructor
  · intro h
    unfold approvedByK at h
    have hzero : (rankOf π c).val = 0 := by omega
    have hrank : rankOf π c = (0 : Candidate n) := Fin.ext hzero
    have hc : π (0 : Candidate n) = c := by
      simpa [rankOf] using congrArg π hrank.symm
    simpa [firstChoice] using hc.symm
  · intro h
    rw [h]
    simp [approvedByK, firstChoice, rankOf]

/--
The one-approval up-event for a distinct pair is exactly the event that the
higher candidate is ranked first.
-/
theorem kApprovalPairUp_one_iff_firstChoice {n : ℕ}
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) (π : Ranking n) :
    approvedByK 1 π hi ∧ ¬ approvedByK 1 π lo ↔
      hi = firstChoice π := by
  constructor
  · intro h
    exact (approvedByK_one_iff_firstChoice π hi).1 h.1
  · intro hhi_first
    refine ⟨(approvedByK_one_iff_firstChoice π hi).2 hhi_first, ?_⟩
    intro hlo_approved
    have hlo_first : lo = firstChoice π :=
      (approvedByK_one_iff_firstChoice π lo).1 hlo_approved
    exact hhi_lo (hhi_first.trans hlo_first.symm)

/-- One-approval pair-up probability is first-choice probability. -/
theorem kApprovalPairUpProb_one_eq_firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairUpProb μ 1 hi lo = firstChoiceProb μ hi := by
  unfold kApprovalPairUpProb firstChoiceProb
  exact AppliedModelingLib.pmfProb_congr μ
    (fun π => kApprovalPairUp_one_iff_firstChoice hhi_lo π)

/-- Top-`n + 1` approval is equivalent to not being ranked last. -/
theorem approvedByK_allButOne_iff_rankOf_ne_lastRank {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    approvedByK (n + 1) π c ↔ rankOf π c ≠ lastRank n := by
  constructor
  · intro happroved hlast
    unfold approvedByK at happroved
    have hval : (rankOf π c).val = n + 1 := by
      simpa [lastRank] using congrArg Fin.val hlast
    omega
  · intro hnot_last
    unfold approvedByK
    by_contra hnot_approved
    have hval : (rankOf π c).val = n + 1 := by
      have hlt : (rankOf π c).val < n + 2 := (rankOf π c).isLt
      omega
    exact hnot_last (Fin.ext hval)

/-- Failing top-`n + 1` approval is equivalent to being ranked last. -/
theorem not_approvedByK_allButOne_iff_rankOf_lastRank {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    ¬ approvedByK (n + 1) π c ↔ rankOf π c = lastRank n := by
  rw [approvedByK_allButOne_iff_rankOf_ne_lastRank]
  constructor
  · intro h
    by_contra hnot_last
    exact h hnot_last
  · intro hlast hnot_last
    exact hnot_last hlast

/--
For all-but-one approval, the ordered-pair up-event is exactly that the lower
candidate is ranked last.
-/
theorem kApprovalPairUp_allButOne_iff_rankOf_lo_lastRank {n : ℕ}
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) (π : Ranking n) :
    approvedByK (n + 1) π hi ∧ ¬ approvedByK (n + 1) π lo ↔
      rankOf π lo = lastRank n := by
  constructor
  · intro h
    exact (not_approvedByK_allButOne_iff_rankOf_lastRank π lo).1 h.2
  · intro hlo_last
    have hhi_ne_last : rankOf π hi ≠ lastRank n := by
      intro hhi_last
      exact hhi_lo (eq_of_rankOf_eq π (hhi_last.trans hlo_last.symm))
    exact
      ⟨(approvedByK_allButOne_iff_rankOf_ne_lastRank π hi).2 hhi_ne_last,
        (not_approvedByK_allButOne_iff_rankOf_lastRank π lo).2 hlo_last⟩

/--
For all-but-one approval, the ordered-pair down-event is exactly that the higher
candidate is ranked last.
-/
theorem kApprovalPairDown_allButOne_iff_rankOf_hi_lastRank {n : ℕ}
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) (π : Ranking n) :
    approvedByK (n + 1) π lo ∧ ¬ approvedByK (n + 1) π hi ↔
      rankOf π hi = lastRank n :=
  kApprovalPairUp_allButOne_iff_rankOf_lo_lastRank (Ne.symm hhi_lo) π

/-- All-but-one ordered-pair up probability as a last-rank probability. -/
theorem kApprovalPairUpProb_allButOne_eq_rankOf_lastProb {n : ℕ}
    (μ : PMF (Ranking n)) {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairUpProb μ (n + 1) hi lo =
      AppliedModelingLib.pmfProb μ (fun π : Ranking n => rankOf π lo = lastRank n) := by
  unfold kApprovalPairUpProb
  exact AppliedModelingLib.pmfProb_congr μ
    (fun π => kApprovalPairUp_allButOne_iff_rankOf_lo_lastRank hhi_lo π)

/-- All-but-one ordered-pair down probability as a last-rank probability. -/
theorem kApprovalPairDownProb_allButOne_eq_rankOf_lastProb {n : ℕ}
    (μ : PMF (Ranking n)) {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairDownProb μ (n + 1) hi lo =
      AppliedModelingLib.pmfProb μ (fun π : Ranking n => rankOf π hi = lastRank n) := by
  unfold kApprovalPairDownProb
  exact AppliedModelingLib.pmfProb_congr μ
    (fun π => kApprovalPairDown_allButOne_iff_rankOf_hi_lastRank hhi_lo π)

/-- Two-approval means first or second place in any finite candidate universe. -/
theorem approvedByK_two_iff_first_or_second {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    approvedByK 2 π c ↔ c = firstChoice π ∨ c = secondChoice π := by
  constructor
  · intro h
    unfold approvedByK at h
    have hval : (rankOf π c).val = 0 ∨ (rankOf π c).val = 1 := by
      omega
    rcases hval with hzero | hone
    · left
      have hrank : rankOf π c = (0 : Candidate n) := Fin.ext hzero
      have hc : π (0 : Candidate n) = c := by
        simpa [rankOf] using congrArg π hrank.symm
      simpa [firstChoice] using hc.symm
    · right
      have hrank : rankOf π c = (1 : Candidate n) := Fin.ext hone
      have hc : π (1 : Candidate n) = c := by
        simpa [rankOf] using congrArg π hrank.symm
      simpa [secondChoice] using hc.symm
  · intro h
    rcases h with hfirst | hsecond
    · rw [hfirst]
      simp [approvedByK, firstChoice, rankOf]
    · rw [hsecond]
      simp [approvedByK, secondChoice, rankOf]

/-- In the four-candidate universe, three-approval means not being ranked last. -/
theorem approvedByK_three_iff_rankOf_ne_last
    (π : Ranking 2) (c : Candidate 2) :
    approvedByK 3 π c ↔ rankOf π c ≠ (3 : Candidate 2) := by
  constructor
  · intro h hlast
    unfold approvedByK at h
    have hval : (rankOf π c).val = 3 := by
      simpa using congrArg Fin.val hlast
    omega
  · intro h
    unfold approvedByK
    by_contra hnot
    have hval : (rankOf π c).val = 3 := by
      omega
    exact h (Fin.ext hval)

/-- In the four-candidate universe, failing three-approval means being ranked last. -/
theorem not_approvedByK_three_iff_rankOf_last
    (π : Ranking 2) (c : Candidate 2) :
    ¬ approvedByK 3 π c ↔ rankOf π c = (3 : Candidate 2) := by
  rw [approvedByK_three_iff_rankOf_ne_last]
  constructor
  · intro h
    by_contra hne
    exact h hne
  · intro hlast hne
    exact hne hlast

/--
For four candidates, the three-approval up-event for a distinct pair is
equivalent to the lower candidate being ranked last.
-/
theorem kApprovalPairUp_three_iff_rankOf_lo_last
    {hi lo : Candidate 2} (hhi_lo : hi ≠ lo) (π : Ranking 2) :
    approvedByK 3 π hi ∧ ¬ approvedByK 3 π lo ↔
      rankOf π lo = (3 : Candidate 2) := by
  constructor
  · intro h
    exact (not_approvedByK_three_iff_rankOf_last π lo).1 h.2
  · intro hlo_last
    have hhi_ne_last : rankOf π hi ≠ (3 : Candidate 2) := by
      intro hhi_last
      have hsame : hi = lo := by
        calc
          hi = π (rankOf π hi) := by simp [rankOf]
          _ = π (rankOf π lo) := by rw [hhi_last, hlo_last]
          _ = lo := by simp [rankOf]
      exact hhi_lo hsame
    exact
      ⟨(approvedByK_three_iff_rankOf_ne_last π hi).2 hhi_ne_last,
        (not_approvedByK_three_iff_rankOf_last π lo).2 hlo_last⟩

/--
Four-candidate three-approval up-probability is the probability that `lo` is
ranked last.
-/
theorem kApprovalPairUpProb_three_eq_rankOf_lastProb
    (μ : PMF (Ranking 2)) {hi lo : Candidate 2} (hhi_lo : hi ≠ lo) :
    kApprovalPairUpProb μ 3 hi lo =
      AppliedModelingLib.pmfProb μ
        (fun π : Ranking 2 => rankOf π lo = (3 : Candidate 2)) := by
  unfold kApprovalPairUpProb
  exact AppliedModelingLib.pmfProb_congr μ
    (fun π => kApprovalPairUp_three_iff_rankOf_lo_last hhi_lo π)

/--
Pointwise indicator decomposition for a two-approval up-event: `hi` is approved
and `lo` is not iff the first two positions are `hi` and some candidate other
than `hi` and `lo`, in either order.
-/
theorem kApprovalPairUpIndicator_two_eq_firstSecondSum {n : ℕ}
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) (π : Ranking n) :
    (if approvedByK 2 π hi ∧ ¬ approvedByK 2 π lo then (1 : ℝ) else 0) =
      ∑ other : Candidate n,
        if other ≠ hi ∧ other ≠ lo then
          (if hi = firstChoice π ∧ other = secondChoice π then (1 : ℝ) else 0) +
            (if other = firstChoice π ∧ hi = secondChoice π then (1 : ℝ) else 0)
        else 0 := by
  classical
  by_cases hhi_first : hi = firstChoice π
  · have hhi_not_second : hi ≠ secondChoice π := by
      intro hsecond
      exact firstChoice_ne_secondChoice π (hhi_first.symm.trans hsecond)
    by_cases hsecond_lo : secondChoice π = lo
    · have hnot_event : ¬(approvedByK 2 π hi ∧ ¬ approvedByK 2 π lo) := by
        intro h
        apply h.2
        exact (approvedByK_two_iff_first_or_second π lo).2
          (Or.inr hsecond_lo.symm)
      have hsum :
          (∑ other : Candidate n,
            if other ≠ hi ∧ other ≠ lo then
              (if hi = firstChoice π ∧ other = secondChoice π then (1 : ℝ) else 0) +
                (if other = firstChoice π ∧ hi = secondChoice π then (1 : ℝ) else 0)
            else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro other _
        by_cases hother_second : other = secondChoice π
        · have hother_lo : other = lo := hother_second.trans hsecond_lo
          have hπ1_lo : π (1 : Candidate n) = lo := by
            simpa [secondChoice] using hsecond_lo
          simp [firstChoice, secondChoice, hhi_first, hother_second, hπ1_lo]
        · have hother_ne_π1 : other ≠ π (1 : Candidate n) := by
            simpa [secondChoice] using hother_second
          simp [firstChoice, secondChoice, hhi_first, hother_ne_π1]
      simpa [hnot_event] using hsum.symm
    · have hsecond_not_hi : secondChoice π ≠ hi := by
        intro hsecond_hi
        exact hhi_not_second hsecond_hi.symm
      have hπ1_not_lo : π (1 : Candidate n) ≠ lo := by
        simpa [secondChoice] using hsecond_lo
      have hsum :
          (∑ other : Candidate n,
            if other ≠ hi ∧ other ≠ lo then
              (if hi = firstChoice π ∧ other = secondChoice π then (1 : ℝ) else 0) +
                (if other = firstChoice π ∧ hi = secondChoice π then (1 : ℝ) else 0)
            else 0) = 1 := by
        rw [Finset.sum_eq_single (secondChoice π)]
        · simp [firstChoice, secondChoice, hhi_first, hπ1_not_lo]
        · intro other _ hother_ne
          have hother_ne_π1 : other ≠ π (1 : Candidate n) := by
            simpa [secondChoice] using hother_ne
          simp [firstChoice, secondChoice, hhi_first, hother_ne_π1]
        · intro hnot_mem
          simp at hnot_mem
      have hnot_lo_approved : ¬ approvedByK 2 π lo := by
        intro hlo
        rcases (approvedByK_two_iff_first_or_second π lo).1 hlo with
          hlo_first | hlo_second
        · exact hhi_lo (hhi_first.trans hlo_first.symm)
        · exact hsecond_lo hlo_second.symm
      have hevent : approvedByK 2 π hi ∧ ¬ approvedByK 2 π lo := by
        exact ⟨(approvedByK_two_iff_first_or_second π hi).2 (Or.inl hhi_first),
          hnot_lo_approved⟩
      simpa [hevent] using hsum.symm
  · by_cases hhi_second : hi = secondChoice π
    · by_cases hfirst_lo : firstChoice π = lo
      · have hnot_event : ¬(approvedByK 2 π hi ∧ ¬ approvedByK 2 π lo) := by
          intro h
          apply h.2
          exact (approvedByK_two_iff_first_or_second π lo).2
            (Or.inl hfirst_lo.symm)
        have hsum :
              (∑ other : Candidate n,
                if other ≠ hi ∧ other ≠ lo then
                  (if hi = firstChoice π ∧ other = secondChoice π then (1 : ℝ) else 0) +
                    (if other = firstChoice π ∧ hi = secondChoice π then (1 : ℝ) else 0)
                else 0) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro other _
          by_cases hother_first : other = firstChoice π
          · have hother_lo : other = lo := hother_first.trans hfirst_lo
            have hπ0_lo : π (0 : Candidate n) = lo := by
              simpa [firstChoice] using hfirst_lo
            simp [firstChoice, secondChoice, hhi_second, hother_first, hπ0_lo]
          · have hother_ne_π0 : other ≠ π (0 : Candidate n) := by
              simpa [firstChoice] using hother_first
            simp [firstChoice, secondChoice, hhi_second, hother_ne_π0]
        simpa [hnot_event] using hsum.symm
      · have hπ0_not_lo : π (0 : Candidate n) ≠ lo := by
          simpa [firstChoice] using hfirst_lo
        have hsum :
            (∑ other : Candidate n,
              if other ≠ hi ∧ other ≠ lo then
                (if hi = firstChoice π ∧ other = secondChoice π then (1 : ℝ) else 0) +
                  (if other = firstChoice π ∧ hi = secondChoice π then (1 : ℝ) else 0)
            else 0) = 1 := by
          rw [Finset.sum_eq_single (firstChoice π)]
          · simp [firstChoice, secondChoice, hhi_second, hπ0_not_lo]
          · intro other _ hother_ne
            have hother_ne_π0 : other ≠ π (0 : Candidate n) := by
              simpa [firstChoice] using hother_ne
            simp [firstChoice, secondChoice, hhi_second, hother_ne_π0]
          · intro hnot_mem
            simp at hnot_mem
        have hnot_lo_approved : ¬ approvedByK 2 π lo := by
          intro hlo
          rcases (approvedByK_two_iff_first_or_second π lo).1 hlo with
            hlo_first | hlo_second
          · exact hfirst_lo hlo_first.symm
          · exact hhi_lo (hhi_second.trans hlo_second.symm)
        have hevent : approvedByK 2 π hi ∧ ¬ approvedByK 2 π lo := by
          exact ⟨(approvedByK_two_iff_first_or_second π hi).2 (Or.inr hhi_second),
            hnot_lo_approved⟩
        simpa [hevent] using hsum.symm
    · have hnot_hi_approved : ¬ approvedByK 2 π hi := by
        intro hhi
        rcases (approvedByK_two_iff_first_or_second π hi).1 hhi with
          hfirst | hsecond
        · exact hhi_first hfirst
        · exact hhi_second hsecond
      have hnot_event : ¬(approvedByK 2 π hi ∧ ¬ approvedByK 2 π lo) := by
        intro h
        exact hnot_hi_approved h.1
      have hsum :
          (∑ other : Candidate n,
            if other ≠ hi ∧ other ≠ lo then
              (if hi = firstChoice π ∧ other = secondChoice π then (1 : ℝ) else 0) +
                (if other = firstChoice π ∧ hi = secondChoice π then (1 : ℝ) else 0)
            else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro other _
        have hhi_ne_π0 : hi ≠ π (0 : Candidate n) := by
          simpa [firstChoice] using hhi_first
        have hhi_ne_π1 : hi ≠ π (1 : Candidate n) := by
          simpa [secondChoice] using hhi_second
        simp [firstChoice, secondChoice, hhi_ne_π0, hhi_ne_π1]
      simpa [hnot_event] using hsum.symm

/--
Two-approval up-probability as a sum over ordered first/second choice events.
-/
theorem kApprovalPairUpProb_two_eq_firstSecondChoiceSum {n : ℕ}
    (μ : PMF (Ranking n)) {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairUpProb μ 2 hi lo =
      ∑ other : Candidate n,
        if other ≠ hi ∧ other ≠ lo then
          AppliedModelingLib.pmfProb μ
              (fun π : Ranking n => hi = firstChoice π ∧ other = secondChoice π) +
            AppliedModelingLib.pmfProb μ
              (fun π : Ranking n => other = firstChoice π ∧ hi = secondChoice π)
        else 0 := by
  classical
  unfold kApprovalPairUpProb AppliedModelingLib.pmfProb
  have hsplit :
      (∑ other : Candidate n,
        if other ≠ hi ∧ other ≠ lo then
          AppliedModelingLib.pmfExp μ
              (fun π : Ranking n =>
                if hi = firstChoice π ∧ other = secondChoice π then (1 : ℝ) else 0) +
            AppliedModelingLib.pmfExp μ
              (fun π : Ranking n =>
                if other = firstChoice π ∧ hi = secondChoice π then (1 : ℝ) else 0)
        else 0) =
        ∑ other : Candidate n,
          AppliedModelingLib.pmfExp μ
            (fun π : Ranking n =>
              if other ≠ hi ∧ other ≠ lo then
                (if hi = firstChoice π ∧ other = secondChoice π then (1 : ℝ) else 0) +
                  (if other = firstChoice π ∧ hi = secondChoice π then (1 : ℝ) else 0)
              else 0) := by
    refine Finset.sum_congr rfl ?_
    intro other _
    by_cases hother : other ≠ hi ∧ other ≠ lo
    · rw [if_pos hother]
      rw [← AppliedModelingLib.pmfExp_add]
      refine AppliedModelingLib.pmfExp_congr μ ?_
      intro π
      simp [hother]
    · simp [hother]
  rw [hsplit]
  rw [← AppliedModelingLib.pmfExp_finset_sum (μ := μ) (s := Finset.univ)
    (f := fun other π =>
      if other ≠ hi ∧ other ≠ lo then
        (if hi = firstChoice π ∧ other = secondChoice π then (1 : ℝ) else 0) +
          (if other = firstChoice π ∧ hi = secondChoice π then (1 : ℝ) else 0)
      else 0)]
  refine AppliedModelingLib.pmfExp_congr μ ?_
  intro π
  simpa using (kApprovalPairUpIndicator_two_eq_firstSecondSum (hi := hi)
    (lo := lo) hhi_lo π)

theorem kApprovalPairUpProb_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n) :
    0 ≤ kApprovalPairUpProb μ K hi lo :=
  by
    unfold kApprovalPairUpProb
    exact AppliedModelingLib.pmfProb_nonneg μ _

theorem kApprovalPairDownProb_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n) :
    0 ≤ kApprovalPairDownProb μ K hi lo :=
  by
    unfold kApprovalPairDownProb
    exact AppliedModelingLib.pmfProb_nonneg μ _

theorem kApprovalPairUpProb_add_downProb_le_one {n : ℕ}
    (μ : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n) :
    kApprovalPairUpProb μ K hi lo +
        kApprovalPairDownProb μ K hi lo ≤ 1 := by
  classical
  have hdisjoint :
      ∀ π : Ranking n,
        (approvedByK K π hi ∧ ¬ approvedByK K π lo) →
          (approvedByK K π lo ∧ ¬ approvedByK K π hi) → False := by
    intro π hup hdown
    exact hup.2 hdown.1
  have hunion :
      AppliedModelingLib.pmfProb μ
          (fun π : Ranking n =>
            (approvedByK K π hi ∧ ¬ approvedByK K π lo) ∨
              (approvedByK K π lo ∧ ¬ approvedByK K π hi)) =
        kApprovalPairUpProb μ K hi lo +
          kApprovalPairDownProb μ K hi lo := by
    simpa [kApprovalPairUpProb, kApprovalPairDownProb] using
      (AppliedModelingLib.pmfProb_or_eq_add_of_disjoint μ
        (fun π : Ranking n => approvedByK K π hi ∧ ¬ approvedByK K π lo)
        (fun π : Ranking n => approvedByK K π lo ∧ ¬ approvedByK K π hi)
        hdisjoint)
  rw [← hunion]
  exact AppliedModelingLib.pmfProb_le_one μ
    (fun π : Ranking n =>
      (approvedByK K π hi ∧ ¬ approvedByK K π lo) ∨
        (approvedByK K π lo ∧ ¬ approvedByK K π hi))

@[simp] theorem approvedByK_swapCandidatePositions_left {n : ℕ}
    (K : ℕ) (π : Ranking n) (c d : Candidate n) :
    approvedByK K (swapCandidatePositions π c d) c ↔
      approvedByK K π d := by
  unfold approvedByK
  simp

@[simp] theorem approvedByK_swapCandidatePositions_right {n : ℕ}
    (K : ℕ) (π : Ranking n) (c d : Candidate n) :
    approvedByK K (swapCandidatePositions π c d) d ↔
      approvedByK K π c := by
  unfold approvedByK
  simp

theorem approvedByK_swapCandidatePositions_of_ne {n : ℕ}
    (K : ℕ) (π : Ranking n) {c d e : Candidate n}
    (hec : e ≠ c) (hed : e ≠ d) :
    approvedByK K (swapCandidatePositions π c d) e ↔
      approvedByK K π e := by
  unfold approvedByK
  rw [rankOf_swapCandidatePositions_of_ne π hec hed]

theorem kApprovalPairUp_event_swapCandidatePositions {n : ℕ}
    (K : ℕ) (π : Ranking n) (hi lo : Candidate n) :
    (approvedByK K (swapCandidatePositions π hi lo) hi ∧
        ¬ approvedByK K (swapCandidatePositions π hi lo) lo) ↔
      (approvedByK K π lo ∧ ¬ approvedByK K π hi) := by
  simp

theorem kApprovalPairUp_event_swapCandidatePositions_left_of_ne {n : ℕ}
    (K : ℕ) (π : Ranking n) {c d x : Candidate n}
    (hxc : x ≠ c) (hxd : x ≠ d) :
    (approvedByK K (swapCandidatePositions π c d) c ∧
        ¬ approvedByK K (swapCandidatePositions π c d) x) ↔
      (approvedByK K π d ∧ ¬ approvedByK K π x) := by
  rw [approvedByK_swapCandidatePositions_left]
  rw [approvedByK_swapCandidatePositions_of_ne K π hxc hxd]

theorem kApprovalPairUp_event_swapCandidatePositions_right_of_ne {n : ℕ}
    (K : ℕ) (π : Ranking n) {c d x : Candidate n}
    (hxc : x ≠ c) (hxd : x ≠ d) :
    (approvedByK K (swapCandidatePositions π c d) x ∧
        ¬ approvedByK K (swapCandidatePositions π c d) d) ↔
      (approvedByK K π x ∧ ¬ approvedByK K π c) := by
  rw [approvedByK_swapCandidatePositions_right]
  rw [approvedByK_swapCandidatePositions_of_ne K π hxc hxd]

theorem exists_kApprovalPairUp_event {n : ℕ}
    (K : ℕ) (hK_pos : 0 < K) (hK_lt : K < n + 2)
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    ∃ π : Ranking n, approvedByK K π hi ∧ ¬ approvedByK K π lo := by
  classical
  let outside : Candidate n := ⟨K, hK_lt⟩
  let f : Fin 2 → Candidate n := fun i =>
    if i = 0 then (0 : Candidate n) else outside
  let g : Fin 2 → Candidate n := fun i =>
    if i = 0 then hi else lo
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · have hval : (0 : ℕ) = K := by
        simpa [f, outside] using congrArg Fin.val hij
      omega
    · have hval : K = (0 : ℕ) := by
        simpa [f, outside] using congrArg Fin.val hij
      omega
    · rfl
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hhi_lo (by simpa [g] using hij))
    · exact False.elim (hhi_lo.symm (by simpa [g] using hij))
    · rfl
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hπ0 : π (0 : Candidate n) = hi := by
    simpa [f, g] using hπ (0 : Fin 2)
  have hπK : π outside = lo := by
    simpa [f, g] using hπ (1 : Fin 2)
  refine ⟨π, ?_⟩
  constructor
  · unfold approvedByK
    have hrank : rankOf π hi = (0 : Candidate n) := by
      unfold rankOf
      rw [← hπ0]
      simp
    rw [hrank]
    simpa using hK_pos
  · unfold approvedByK
    have hrank : rankOf π lo = outside := by
      unfold rankOf
      rw [← hπK]
      simp
    rw [hrank]
    simp [outside]

theorem exists_kApprovalPairDown_event {n : ℕ}
    (K : ℕ) (hK_pos : 0 < K) (hK_lt : K < n + 2)
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    ∃ π : Ranking n, approvedByK K π lo ∧ ¬ approvedByK K π hi := by
  exact exists_kApprovalPairUp_event K hK_pos hK_lt hhi_lo.symm

theorem kApprovalPairUpProb_pos_of_full_support {n : ℕ}
    (μ : PMF (Ranking n)) (K : ℕ) {hi lo : Candidate n}
    (hhi_lo : hi ≠ lo) (hK_pos : 0 < K) (hK_lt : K < n + 2)
    (hμ_pos : ∀ π : Ranking n, 0 < (μ π).toReal) :
    0 < kApprovalPairUpProb μ K hi lo := by
  classical
  rcases exists_kApprovalPairUp_event K hK_pos hK_lt hhi_lo with ⟨π, hπ⟩
  exact AppliedModelingLib.pmfProb_pos_of_mass μ
    (fun π : Ranking n => approvedByK K π hi ∧ ¬ approvedByK K π lo)
    π hπ (hμ_pos π)

theorem kApprovalPairDownProb_pos_of_full_support {n : ℕ}
    (μ : PMF (Ranking n)) (K : ℕ) {hi lo : Candidate n}
    (hhi_lo : hi ≠ lo) (hK_pos : 0 < K) (hK_lt : K < n + 2)
    (hμ_pos : ∀ π : Ranking n, 0 < (μ π).toReal) :
    0 < kApprovalPairDownProb μ K hi lo := by
  classical
  rcases exists_kApprovalPairDown_event K hK_pos hK_lt hhi_lo with ⟨π, hπ⟩
  exact AppliedModelingLib.pmfProb_pos_of_mass μ
    (fun π : Ranking n => approvedByK K π lo ∧ ¬ approvedByK K π hi)
    π hπ (hμ_pos π)

end

end Ranking
end SocialChoice
end AppliedModelingLib
