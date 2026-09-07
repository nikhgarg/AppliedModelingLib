import AppliedModelingLib.SocialChoice.Ranking.Kendall
import AppliedModelingLib.SocialChoice.Ranking.Probability
import AppliedModelingLib.SocialChoice.Ranking.Approval
import AppliedModelingLib.SocialChoice.Ranking.RankPower
import AppliedModelingLib.Foundations.Math.FiniteSigns
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators
namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

/--
Unnormalised real Mallows weight.  This file uses the inverse of the paper
parameter: if the paper writes mass proportional to `Φ^{-d}` with `Φ > 1`,
then this file writes the same mass as `q^d` with `q = Φ⁻¹` and `0 < q < 1`.
-/
noncomputable def mallowsWeight {n : ℕ} (q : ℝ) (ρ π : Ranking n) : ℝ :=
  q ^ kendallTau ρ π

@[simp] theorem mallowsWeight_center {n : ℕ} (q : ℝ) (ρ : Ranking n) :
    mallowsWeight q ρ ρ = 1 := by
  simp [mallowsWeight]

/-- Mallows weights are strictly positive for positive inverse parameter. -/
theorem mallowsWeight_pos {n : ℕ} {q : ℝ} (hq : 0 < q)
    (ρ π : Ranking n) :
    0 < mallowsWeight q ρ π := by
  unfold mallowsWeight
  exact pow_pos hq _

/-- Mallows weights are nonnegative for positive inverse parameter. -/
theorem mallowsWeight_nonneg {n : ℕ} {q : ℝ} (hq : 0 < q)
    (ρ π : Ranking n) :
    0 ≤ mallowsWeight q ρ π :=
  le_of_lt (mallowsWeight_pos (hq := hq) ρ π)

theorem mallowsWeight_le_swapCandidatePositions_of_rank_lt_of_rank_gt
    {n : ℕ} {q : ℝ} (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (ρ π : Ranking n) {c d : Candidate n}
    (hcenter : rankOf ρ c < rankOf ρ d)
    (hpos : rankOf π d < rankOf π c) :
    mallowsWeight q ρ π ≤
      mallowsWeight q ρ (swapCandidatePositions π c d) := by
  unfold mallowsWeight
  exact pow_le_pow_of_le_one hq_pos.le hq_le_one
    (kendallTau_swapCandidatePositions_le_of_rank_lt_of_rank_gt
      ρ π hcenter hpos)

theorem mallowsWeight_swapCandidatePositions_cross_nonneg
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (ρ π : Ranking n) {c d : Candidate n}
    (hcenter : rankOf ρ c < rankOf ρ d)
    (hpos : rankOf π d < rankOf π c) :
    0 ≤
      mallowsWeight qMore ρ (swapCandidatePositions π c d) *
          mallowsWeight qLess ρ π -
        mallowsWeight qMore ρ π *
          mallowsWeight qLess ρ (swapCandidatePositions π c d) := by
  unfold mallowsWeight
  have hle :
      kendallTau ρ (swapCandidatePositions π c d) ≤ kendallTau ρ π :=
    kendallTau_swapCandidatePositions_le_of_rank_lt_of_rank_gt ρ π hcenter hpos
  have h :=
    natPower_cross_nonneg_of_le
      (q₁ := qMore) (q₂ := qLess) hqMore_pos hq_lt hle
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- The finite partition function for the real-weight Mallows kernel. -/
noncomputable def mallowsPartition {n : ℕ} (q : ℝ) (ρ : Ranking n) : ℝ :=
  ∑ π : Ranking n, mallowsWeight q ρ π

/-- The finite Mallows partition function is strictly positive for `q > 0`. -/
theorem mallowsPartition_pos {n : ℕ} {q : ℝ} (hq : 0 < q)
    (ρ : Ranking n) :
    0 < mallowsPartition q ρ := by
  classical
  unfold mallowsPartition
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg (a₀ := ρ)
  · simpa using mallowsWeight_pos (hq := hq) ρ ρ
  · intro π
    exact mallowsWeight_nonneg (hq := hq) ρ π

/-- The finite Mallows PMF obtained by normalizing the real weights. -/
noncomputable def mallowsPMF {n : ℕ} (q : ℝ) (ρ : Ranking n)
    (hq : 0 < q) : PMF (Ranking n) :=
  PMF.ofFintype
    (fun π : Ranking n =>
      ENNReal.ofReal (mallowsWeight q ρ π / mallowsPartition q ρ))
    (by
      classical
      have hpartition_pos : 0 < mallowsPartition q ρ :=
        mallowsPartition_pos (hq := hq) ρ
      have hnonneg :
          ∀ π ∈ (Finset.univ : Finset (Ranking n)),
            0 ≤ mallowsWeight q ρ π / mallowsPartition q ρ := by
        intro π _
        exact div_nonneg (mallowsWeight_nonneg (hq := hq) ρ π)
          (le_of_lt hpartition_pos)
      have hsum :
          (∑ π : Ranking n, mallowsWeight q ρ π / mallowsPartition q ρ) =
            1 := by
        rw [(Finset.sum_div
          (s := (Finset.univ : Finset (Ranking n)))
          (f := fun π : Ranking n => mallowsWeight q ρ π)
          (a := mallowsPartition q ρ)).symm]
        have hsum_pos : 0 < ∑ π : Ranking n, mallowsWeight q ρ π := by
          simpa [mallowsPartition] using hpartition_pos
        unfold mallowsPartition
        field_simp [ne_of_gt hsum_pos]
      calc
        (∑ π : Ranking n,
            ENNReal.ofReal (mallowsWeight q ρ π / mallowsPartition q ρ))
            =
            ENNReal.ofReal
              (∑ π : Ranking n, mallowsWeight q ρ π / mallowsPartition q ρ) := by
              rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
        _ = 1 := by
              rw [hsum]
              simp)

@[simp] theorem mallowsPMF_apply_toReal {n : ℕ} {q : ℝ}
    (hq : 0 < q) (ρ π : Ranking n) :
    ((mallowsPMF q ρ hq) π).toReal =
      mallowsWeight q ρ π / mallowsPartition q ρ := by
  unfold mallowsPMF
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal
    (div_nonneg (mallowsWeight_nonneg (hq := hq) ρ π)
      (le_of_lt (mallowsPartition_pos (hq := hq) ρ)))

/--
A Mallows distribution packaged as an actual `PMF` plus the real finite-sum facts
that identify its probabilities with normalized Mallows weights.

This deliberately avoids making the first implementation depend on a delicate
`ENNReal` construction.  A later file can replace this specification with a
constructor using `PMF.ofFintype` or `PMF.normalize`.
-/
structure MallowsSpec (n : ℕ) where
  center : Ranking n
  /-- Inverse Mallows parameter `q`; alternate conventions may use `q⁻¹`. -/
  q : ℝ
  law : PMF (Ranking n)
  partition : ℝ
  q_pos : 0 < q
  partition_pos : 0 < partition
  partition_eq_sum : partition = mallowsPartition q center
  law_apply_toReal : ∀ π : Ranking n,
    (law π).toReal = mallowsWeight q center π / partition

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/-- Concrete finite Mallows specification at center `ρ` and inverse parameter `q`. -/
noncomputable def ofQ (ρ : Ranking n) (q : ℝ) (hq : 0 < q) :
    MallowsSpec n where
  center := ρ
  q := q
  law := mallowsPMF q ρ hq
  partition := mallowsPartition q ρ
  q_pos := hq
  partition_pos := mallowsPartition_pos (hq := hq) ρ
  partition_eq_sum := rfl
  law_apply_toReal := by
    intro π
    exact mallowsPMF_apply_toReal hq ρ π

/-- The true/central first candidate. -/
def centerFirst : Candidate n := firstChoice M.center

/-- The true/central second candidate. -/
def centerSecond : Candidate n := secondChoice M.center

@[simp] theorem partition_ne_zero : M.partition ≠ 0 := by
  exact ne_of_gt M.partition_pos

theorem law_apply_toReal_pos (π : Ranking n) :
    0 < (M.law π).toReal := by
  rw [M.law_apply_toReal]
  exact div_pos (mallowsWeight_pos (hq := M.q_pos) M.center π)
    M.partition_pos

/-- The unnormalised mass of rankings whose first choice is `c`. -/
noncomputable def firstWeight (c : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if c = firstChoice π then mallowsWeight M.q M.center π else 0

/-- The unnormalised mass of rankings whose first two choices are `c,d`. -/
noncomputable def firstSecondWeight (c d : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if c = firstChoice π ∧ d = secondChoice π
    then mallowsWeight M.q M.center π
    else 0

/-- Raw Mallows mass of a K-approval up-event for an ordered pair. -/
noncomputable def kApprovalPairUpWeight
    (K : ℕ) (hi lo : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if approvedByK K π hi ∧ ¬ approvedByK K π lo
    then mallowsWeight M.q M.center π
    else 0

/-- First-choice probabilities reduce to finite Mallows weights. -/
theorem firstChoiceProb_eq_firstWeight_div_partition (c : Candidate n) :
    firstChoiceProb M.law c = M.firstWeight c / M.partition := by
  classical
  unfold firstChoiceProb pmfProb pmfExp firstWeight
  calc
    ∑ π : Ranking n, (M.law π).toReal *
        (if c = firstChoice π then (1 : ℝ) else 0)
        = ∑ π : Ranking n,
            (mallowsWeight M.q M.center π / M.partition) *
              (if c = firstChoice π then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking n,
          (if c = firstChoice π then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = firstChoice π
          · have h' : c = π 0 := by simpa [firstChoice] using h
            simp [h']
          · have h' : c ≠ π 0 := by simpa [firstChoice] using h
            simp [h']
    _ = (∑ π : Ranking n,
          if c = firstChoice π then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          rw [Finset.sum_div]

/-- K-approval up-event probabilities reduce to finite Mallows weights. -/
theorem kApprovalPairUpProb_eq_weight_div_partition
    (K : ℕ) (hi lo : Candidate n) :
    kApprovalPairUpProb M.law K hi lo =
      M.kApprovalPairUpWeight K hi lo / M.partition := by
  classical
  unfold kApprovalPairUpProb pmfProb pmfExp kApprovalPairUpWeight
  calc
    ∑ π : Ranking n, (M.law π).toReal *
        (if approvedByK K π hi ∧ ¬ approvedByK K π lo then (1 : ℝ) else 0)
        = ∑ π : Ranking n,
            (mallowsWeight M.q M.center π / M.partition) *
              (if approvedByK K π hi ∧ ¬ approvedByK K π lo
                then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking n,
          (if approvedByK K π hi ∧ ¬ approvedByK K π lo
            then mallowsWeight M.q M.center π else 0) / M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : approvedByK K π hi ∧ ¬ approvedByK K π lo
          · simp [h]
          · simp [h]
    _ = (∑ π : Ranking n,
          if approvedByK K π hi ∧ ¬ approvedByK K π lo
            then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          rw [Finset.sum_div]

theorem kApprovalPairUpWeight_swap_le_of_rank_lt
    (K : ℕ) {hi lo : Candidate n}
    (hcenter : rankOf M.center hi < rankOf M.center lo)
    (hq_le_one : M.q ≤ 1) :
    M.kApprovalPairUpWeight K lo hi ≤
      M.kApprovalPairUpWeight K hi lo := by
  classical
  unfold kApprovalPairUpWeight
  calc
    (∑ π : Ranking n,
        if approvedByK K π lo ∧ ¬ approvedByK K π hi
        then mallowsWeight M.q M.center π
        else 0)
        =
        ∑ π : Ranking n,
          if approvedByK K (swapCandidatePositions π hi lo) lo ∧
              ¬ approvedByK K (swapCandidatePositions π hi lo) hi
          then mallowsWeight M.q M.center (swapCandidatePositions π hi lo)
          else 0 := by
          simpa [swapCandidatePositionsEquiv] using
            (Equiv.sum_comp (swapCandidatePositionsEquiv hi lo)
              (fun π : Ranking n =>
                if approvedByK K π lo ∧ ¬ approvedByK K π hi
                then mallowsWeight M.q M.center π
                else 0)).symm
    _ =
        ∑ π : Ranking n,
          if approvedByK K π hi ∧ ¬ approvedByK K π lo
          then mallowsWeight M.q M.center (swapCandidatePositions π hi lo)
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hiff :
              (approvedByK K (swapCandidatePositions π hi lo) lo ∧
                  ¬ approvedByK K (swapCandidatePositions π hi lo) hi) ↔
                (approvedByK K π hi ∧ ¬ approvedByK K π lo) := by
            simpa [swapCandidatePositions_comm] using
              (kApprovalPairUp_event_swapCandidatePositions K π lo hi)
          by_cases h :
              approvedByK K π hi ∧ ¬ approvedByK K π lo
          · rw [if_pos (hiff.mpr h), if_pos h]
          · rw [if_neg (fun hleft => h (hiff.mp hleft)), if_neg h]
    _ ≤
        ∑ π : Ranking n,
          if approvedByK K π hi ∧ ¬ approvedByK K π lo
          then mallowsWeight M.q M.center π
          else 0 := by
          refine Finset.sum_le_sum ?_
          intro π _
          by_cases h :
              approvedByK K π hi ∧ ¬ approvedByK K π lo
          · rw [if_pos h, if_pos h]
            have hπ_rank : rankOf π hi < rankOf π lo := by
              unfold approvedByK at h
              change (rankOf π hi).val < (rankOf π lo).val
              omega
            have hsource_rank :
                rankOf (swapCandidatePositions π hi lo) lo <
                  rankOf (swapCandidatePositions π hi lo) hi := by
              simpa using hπ_rank
            have hle :=
              mallowsWeight_le_swapCandidatePositions_of_rank_lt_of_rank_gt
                M.q_pos hq_le_one M.center
                (swapCandidatePositions π hi lo) hcenter hsource_rank
            simpa [swapCandidatePositions_involutive] using hle
          · simp [h]

theorem kApprovalPairDownProb_le_up_of_rank_lt
    (K : ℕ) {hi lo : Candidate n}
    (hcenter : rankOf M.center hi < rankOf M.center lo)
    (hq_le_one : M.q ≤ 1) :
    kApprovalPairDownProb M.law K hi lo ≤
      kApprovalPairUpProb M.law K hi lo := by
  rw [kApprovalPairDownProb_eq_pairUpProb_swap]
  rw [M.kApprovalPairUpProb_eq_weight_div_partition K lo hi,
    M.kApprovalPairUpProb_eq_weight_div_partition K hi lo]
  exact div_le_div_of_nonneg_right
    (M.kApprovalPairUpWeight_swap_le_of_rank_lt K hcenter hq_le_one)
    (le_of_lt M.partition_pos)

theorem kApprovalPairUpProb_le_of_selected_rank_lt
    (K : ℕ) {better worse excluded : Candidate n}
    (hcenter : rankOf M.center better < rankOf M.center worse)
    (hexcluded_better : excluded ≠ better)
    (hexcluded_worse : excluded ≠ worse)
    (hq_le_one : M.q ≤ 1) :
    kApprovalPairUpProb M.law K worse excluded ≤
      kApprovalPairUpProb M.law K better excluded := by
  classical
  unfold kApprovalPairUpProb
  refine pmfProb_le_of_cross_event_equiv_mass_le M.law
    (swapCandidatePositionsEquiv better worse)
    (fun π : Ranking n =>
      approvedByK K π worse ∧ ¬ approvedByK K π excluded)
    (fun π : Ranking n =>
      approvedByK K π better ∧ ¬ approvedByK K π excluded)
    ?hmap ?hmass
  · intro π hp
    rcases hp with ⟨⟨hworse, hexcluded⟩, hnot_target⟩
    have hbetter_not : ¬ approvedByK K π better := by
      intro hbetter
      exact hnot_target ⟨hbetter, hexcluded⟩
    constructor
    · constructor
      · change approvedByK K (swapCandidatePositions π better worse) better
        rw [approvedByK_swapCandidatePositions_left]
        exact hworse
      · have hiff :=
          approvedByK_swapCandidatePositions_of_ne K π
            (c := better) (d := worse) (e := excluded)
            hexcluded_better hexcluded_worse
        exact fun hexcluded_swap => hexcluded (hiff.mp hexcluded_swap)
    · intro hsource_swap
      exact hbetter_not
        ((approvedByK_swapCandidatePositions_right K π better worse).1
          hsource_swap.1)
  · intro π hp
    rcases hp with ⟨⟨hworse, hexcluded⟩, hnot_target⟩
    have hbetter_not : ¬ approvedByK K π better := by
      intro hbetter
      exact hnot_target ⟨hbetter, hexcluded⟩
    have hpos : rankOf π worse < rankOf π better := by
      unfold approvedByK at hworse hbetter_not
      change (rankOf π worse).val < (rankOf π better).val
      omega
    rw [M.law_apply_toReal, M.law_apply_toReal]
    exact div_le_div_of_nonneg_right
      (mallowsWeight_le_swapCandidatePositions_of_rank_lt_of_rank_gt
        M.q_pos hq_le_one M.center π hcenter hpos)
      (le_of_lt M.partition_pos)

theorem kApprovalPairUpProb_le_of_selected_rank_le
    (K : ℕ) {better worse excluded : Candidate n}
    (hcenter : rankOf M.center better ≤ rankOf M.center worse)
    (hexcluded_better : excluded ≠ better)
    (hexcluded_worse : excluded ≠ worse)
    (hq_le_one : M.q ≤ 1) :
    kApprovalPairUpProb M.law K worse excluded ≤
      kApprovalPairUpProb M.law K better excluded := by
  rcases lt_or_eq_of_le hcenter with hlt | heq
  · exact M.kApprovalPairUpProb_le_of_selected_rank_lt K hlt
      hexcluded_better hexcluded_worse hq_le_one
  · have hsame : better = worse := eq_of_rankOf_eq M.center heq
    subst worse
    rfl

theorem kApprovalPairUpProb_le_of_excluded_rank_lt
    (K : ℕ) {selected betterExcluded worseExcluded : Candidate n}
    (hcenter :
      rankOf M.center betterExcluded < rankOf M.center worseExcluded)
    (hselected_better : selected ≠ betterExcluded)
    (hselected_worse : selected ≠ worseExcluded)
    (hq_le_one : M.q ≤ 1) :
    kApprovalPairUpProb M.law K selected betterExcluded ≤
      kApprovalPairUpProb M.law K selected worseExcluded := by
  classical
  unfold kApprovalPairUpProb
  refine pmfProb_le_of_cross_event_equiv_mass_le M.law
    (swapCandidatePositionsEquiv betterExcluded worseExcluded)
    (fun π : Ranking n =>
      approvedByK K π selected ∧ ¬ approvedByK K π betterExcluded)
    (fun π : Ranking n =>
      approvedByK K π selected ∧ ¬ approvedByK K π worseExcluded)
    ?hmap ?hmass
  · intro π hp
    rcases hp with ⟨⟨hselected, hbetter_not⟩, hnot_target⟩
    have hworse : approvedByK K π worseExcluded := by
      by_contra hworse_not
      exact hnot_target ⟨hselected, hworse_not⟩
    constructor
    · constructor
      · have hiff :=
          approvedByK_swapCandidatePositions_of_ne K π
            (c := betterExcluded) (d := worseExcluded) (e := selected)
            hselected_better hselected_worse
        exact hiff.mpr hselected
      · exact fun hworse_swap =>
          hbetter_not
            ((approvedByK_swapCandidatePositions_right
                K π betterExcluded worseExcluded).1 hworse_swap)
    · intro hsource_swap
      exact hsource_swap.2
        (by
          change
            approvedByK K
              (swapCandidatePositions π betterExcluded worseExcluded)
              betterExcluded
          rw [approvedByK_swapCandidatePositions_left]
          exact hworse)
  · intro π hp
    rcases hp with ⟨⟨hselected, hbetter_not⟩, hnot_target⟩
    have hworse : approvedByK K π worseExcluded := by
      by_contra hworse_not
      exact hnot_target ⟨hselected, hworse_not⟩
    have hpos : rankOf π worseExcluded < rankOf π betterExcluded := by
      unfold approvedByK at hworse hbetter_not
      change (rankOf π worseExcluded).val < (rankOf π betterExcluded).val
      omega
    rw [M.law_apply_toReal, M.law_apply_toReal]
    exact div_le_div_of_nonneg_right
      (mallowsWeight_le_swapCandidatePositions_of_rank_lt_of_rank_gt
        M.q_pos hq_le_one M.center π hcenter hpos)
      (le_of_lt M.partition_pos)

theorem kApprovalPairUpProb_le_of_excluded_rank_le
    (K : ℕ) {selected betterExcluded worseExcluded : Candidate n}
    (hcenter :
      rankOf M.center betterExcluded ≤ rankOf M.center worseExcluded)
    (hselected_better : selected ≠ betterExcluded)
    (hselected_worse : selected ≠ worseExcluded)
    (hq_le_one : M.q ≤ 1) :
    kApprovalPairUpProb M.law K selected betterExcluded ≤
      kApprovalPairUpProb M.law K selected worseExcluded := by
  rcases lt_or_eq_of_le hcenter with hlt | heq
  · exact M.kApprovalPairUpProb_le_of_excluded_rank_lt K hlt
      hselected_better hselected_worse hq_le_one
  · have hsame : betterExcluded = worseExcluded := eq_of_rankOf_eq M.center heq
    subst worseExcluded
    rfl

/-- Probability that a Mallows draw begins with the ordered pair `(c,d)`. -/
noncomputable def firstSecondChoiceProb (c d : Candidate n) : ℝ :=
  pmfProb M.law (fun π => c = firstChoice π ∧ d = secondChoice π)

/-- Unnormalised mass of rankings that correctly order the center-ordered pair
`(c,d)`.  The guard `rankOf M.center c < rankOf M.center d` keeps the definition
paper-facing: `c` is the better item and `d` is the worse item. -/
noncomputable def pairCorrectWeight (c d : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if rankOf M.center c < rankOf M.center d ∧ rankOf π c < rankOf π d
    then mallowsWeight M.q M.center π
    else 0

/-- Probability that a Mallows draw correctly orders the center-ordered pair
`(c,d)`. -/
noncomputable def pairCorrectProb (c d : Candidate n) : ℝ :=
  pmfProb M.law
    (fun π => rankOf M.center c < rankOf M.center d ∧
      rankOf π c < rankOf π d)

/-- Unnormalised mass of rankings that incorrectly order the center-ordered
pair `(c,d)`. -/
noncomputable def pairWrongWeight (c d : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if rankOf M.center c < rankOf M.center d ∧ rankOf π d < rankOf π c
    then mallowsWeight M.q M.center π
    else 0

/-- Probability that a Mallows draw incorrectly orders the center-ordered pair
`(c,d)`. -/
noncomputable def pairWrongProb (c d : Candidate n) : ℝ :=
  pmfProb M.law
    (fun π => rankOf M.center c < rankOf M.center d ∧
      rankOf π d < rankOf π c)

/-- First/second-choice probabilities reduce to finite Mallows weights. -/
theorem firstSecondChoiceProb_eq_firstSecondWeight_div_partition
    (c d : Candidate n) :
    M.firstSecondChoiceProb c d = M.firstSecondWeight c d / M.partition := by
  classical
  unfold firstSecondChoiceProb pmfProb pmfExp firstSecondWeight
  calc
    ∑ π : Ranking n, (M.law π).toReal *
        (if c = firstChoice π ∧ d = secondChoice π then (1 : ℝ) else 0)
        = ∑ π : Ranking n,
            (mallowsWeight M.q M.center π / M.partition) *
              (if c = firstChoice π ∧ d = secondChoice π then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking n,
          (if c = firstChoice π ∧ d = secondChoice π
            then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = firstChoice π ∧ d = secondChoice π
          · have hc : c = π 0 := by simpa [firstChoice] using h.1
            have hd : d = π 1 := by simpa [secondChoice] using h.2
            simp [hc, hd]
          · have h' : ¬(c = π 0 ∧ d = π 1) := by
              intro hraw
              apply h
              exact ⟨by simpa [firstChoice] using hraw.1,
                by simpa [secondChoice] using hraw.2⟩
            simp [h']
    _ = (∑ π : Ranking n,
          if c = firstChoice π ∧ d = secondChoice π
            then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          rw [Finset.sum_div]

/-- Pair-correct probabilities reduce to finite Mallows weights. -/
theorem pairCorrectProb_eq_pairCorrectWeight_div_partition
    (c d : Candidate n) :
    M.pairCorrectProb c d = M.pairCorrectWeight c d / M.partition := by
  classical
  unfold pairCorrectProb pmfProb pmfExp pairCorrectWeight
  calc
    ∑ π : Ranking n, (M.law π).toReal *
        (if rankOf M.center c < rankOf M.center d ∧
            rankOf π c < rankOf π d then (1 : ℝ) else 0)
        = ∑ π : Ranking n,
            (mallowsWeight M.q M.center π / M.partition) *
              (if rankOf M.center c < rankOf M.center d ∧
                  rankOf π c < rankOf π d then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking n,
          (if rankOf M.center c < rankOf M.center d ∧
              rankOf π c < rankOf π d
            then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h :
              rankOf M.center c < rankOf M.center d ∧
                rankOf π c < rankOf π d
          · simp [h]
          · simp [h]
    _ = (∑ π : Ranking n,
          if rankOf M.center c < rankOf M.center d ∧
              rankOf π c < rankOf π d
            then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          rw [Finset.sum_div]

/-- Pair-wrong probabilities reduce to finite Mallows weights. -/
theorem pairWrongProb_eq_pairWrongWeight_div_partition
    (c d : Candidate n) :
    M.pairWrongProb c d = M.pairWrongWeight c d / M.partition := by
  classical
  unfold pairWrongProb pmfProb pmfExp pairWrongWeight
  calc
    ∑ π : Ranking n, (M.law π).toReal *
        (if rankOf M.center c < rankOf M.center d ∧
            rankOf π d < rankOf π c then (1 : ℝ) else 0)
        = ∑ π : Ranking n,
            (mallowsWeight M.q M.center π / M.partition) *
              (if rankOf M.center c < rankOf M.center d ∧
                  rankOf π d < rankOf π c then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking n,
          (if rankOf M.center c < rankOf M.center d ∧
              rankOf π d < rankOf π c
            then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h :
              rankOf M.center c < rankOf M.center d ∧
                rankOf π d < rankOf π c
          · simp [h]
          · simp [h]
    _ = (∑ π : Ranking n,
          if rankOf M.center c < rankOf M.center d ∧
              rankOf π d < rankOf π c
            then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          rw [Finset.sum_div]

/-- Correct and wrong pair-order weights partition the Mallows mass for a
center-ordered pair. -/
theorem pairCorrectWeight_add_pairWrongWeight_eq_partition
    {c d : Candidate n} (hcd : rankOf M.center c < rankOf M.center d) :
    M.pairCorrectWeight c d + M.pairWrongWeight c d = M.partition := by
  classical
  unfold pairCorrectWeight pairWrongWeight
  rw [← Finset.sum_add_distrib]
  rw [M.partition_eq_sum]
  unfold mallowsPartition
  refine Finset.sum_congr rfl ?_
  intro π _
  have hcd_ne : c ≠ d := by
    intro h
    rw [h] at hcd
    exact (lt_irrefl (rankOf M.center d)) hcd
  have hrank_ne : rankOf π c ≠ rankOf π d := by
    intro h
    apply hcd_ne
    have hc : π (rankOf π c) = c := by simp [rankOf]
    have hd : π (rankOf π d) = d := by simp [rankOf]
    rw [← hc, h, hd]
  rcases lt_or_gt_of_ne hrank_ne with hcorr | hwrong
  · have hnot_wrong : ¬rankOf π d < rankOf π c := not_lt_of_gt hcorr
    simp [hcd, hcorr, hnot_wrong]
  · have hnot_corr : ¬rankOf π c < rankOf π d := not_lt_of_gt hwrong
    simp [hcd, hwrong, hnot_corr]

/-- Correct pair probability as normalized correct-vs-wrong pair mass. -/
theorem pairCorrectProb_eq_pairCorrectWeight_div_correct_add_wrong
    {c d : Candidate n} (hcd : rankOf M.center c < rankOf M.center d) :
    M.pairCorrectProb c d =
      M.pairCorrectWeight c d /
        (M.pairCorrectWeight c d + M.pairWrongWeight c d) := by
  rw [M.pairCorrectProb_eq_pairCorrectWeight_div_partition]
  rw [M.pairCorrectWeight_add_pairWrongWeight_eq_partition hcd]

/-- The first-choice weights partition the Mallows partition function. -/
theorem sum_firstWeight_eq_partition :
    (∑ c : Candidate n, M.firstWeight c) = M.partition := by
  classical
  unfold firstWeight
  rw [M.partition_eq_sum]
  unfold mallowsPartition
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro π _
  have hsum :
      (∑ c : Candidate n,
        if c = firstChoice π then mallowsWeight M.q M.center π else 0) =
        mallowsWeight M.q M.center π := by
    simpa using
      (Finset.sum_ite_eq' Finset.univ (firstChoice π)
        (fun _ : Candidate n => mallowsWeight M.q M.center π))
  rw [hsum]

/-- For a fixed first candidate, summing over second candidates recovers first mass. -/
theorem sum_firstSecondWeight_right_eq_firstWeight (c : Candidate n) :
    (∑ d : Candidate n, M.firstSecondWeight c d) = M.firstWeight c := by
  classical
  unfold firstSecondWeight firstWeight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro π _
  by_cases hc : c = firstChoice π
  · have hsum :
      (∑ d : Candidate n,
        if d = secondChoice π then mallowsWeight M.q M.center π else 0) =
        mallowsWeight M.q M.center π := by
        simpa using
          (Finset.sum_ite_eq' Finset.univ (secondChoice π)
            (fun _ : Candidate n => mallowsWeight M.q M.center π))
    simpa [hc] using hsum
  · have hc' : c ≠ π 0 := by simpa [firstChoice] using hc
    simp [hc']

/-- The probability version of `sum_firstSecondWeight_right_eq_firstWeight`. -/
theorem sum_firstSecondChoiceProb_right_eq_firstChoiceProb (c : Candidate n) :
    (∑ d : Candidate n, M.firstSecondChoiceProb c d) = firstChoiceProb M.law c := by
  classical
  rw [M.firstChoiceProb_eq_firstWeight_div_partition c]
  calc
    ∑ d : Candidate n, M.firstSecondChoiceProb c d
        = ∑ d : Candidate n, M.firstSecondWeight c d / M.partition := by
          refine Finset.sum_congr rfl ?_
          intro d _
          rw [M.firstSecondChoiceProb_eq_firstSecondWeight_div_partition c d]
    _ = (∑ d : Candidate n, M.firstSecondWeight c d) / M.partition := by
          rw [Finset.sum_div]
    _ = M.firstWeight c / M.partition := by
          rw [M.sum_firstSecondWeight_right_eq_firstWeight c]

/-- First-choice probability of the center's first candidate in weight form. -/
theorem centerFirstProb_eq :
    firstChoiceProb M.law M.centerFirst = M.firstWeight M.centerFirst / M.partition :=
  M.firstChoiceProb_eq_firstWeight_div_partition M.centerFirst

/-- First/second probability of the center's first two candidates in weight form. -/
theorem centerFirstSecondProb_eq :
    M.firstSecondChoiceProb M.centerFirst M.centerSecond =
      M.firstSecondWeight M.centerFirst M.centerSecond / M.partition :=
  M.firstSecondChoiceProb_eq_firstSecondWeight_div_partition M.centerFirst M.centerSecond

end MallowsSpec

end Ranking
end SocialChoice
end AppliedModelingLib
