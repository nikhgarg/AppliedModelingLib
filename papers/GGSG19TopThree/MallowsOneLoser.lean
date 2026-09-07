import AppliedModelingLib.SocialChoice.Ranking.MallowsRankFactorization

/-!
# Mallows One-Loser Boundary

Production lemmas for the all-but-one W-selection boundary case.  In a
`Candidate n` universe there are `n + 2` candidates, so selecting all but one
candidate has approval cutoff `K = n + 1` and excludes exactly the candidate
ranked last by the center ranking.
-/

namespace GGSG19TopThree

open AppliedModelingLib.SocialChoice.Ranking

noncomputable section

/-- The last rank in a `Candidate n` universe. -/
def oneLoserLastRank (n : ℕ) : Candidate n :=
  lastRank n

/-- Reverse the rank positions of a ranking in an arbitrary finite candidate universe. -/
def reverseRankingPositions {n : ℕ} (π : Ranking n) : Ranking n :=
  (Fin.revPerm : Equiv.Perm (Candidate n)).trans π

/-- The center-last candidate, i.e. the unique loser in all-but-one selection. -/
def oneLoserLoser {n : ℕ} (ρ : Ranking n) : Candidate n :=
  ρ (oneLoserLastRank n)

/-- The winner set for all-but-one selection under center ranking `ρ`. -/
def oneLoserWinnerSet {n : ℕ} (ρ : Ranking n) : Finset (Candidate n) :=
  Finset.univ.erase (oneLoserLoser ρ)

@[simp] theorem oneLoserLastRank_val (n : ℕ) :
    (oneLoserLastRank n).val = n + 1 := rfl

theorem oneLoserLastRank_pos (n : ℕ) :
    0 < (oneLoserLastRank n).val := by
  simpa [oneLoserLastRank] using lastRank_pos n

@[simp] theorem reverseRankingPositions_apply_zero {n : ℕ} (π : Ranking n) :
    reverseRankingPositions π 0 = π (oneLoserLastRank n) := by
  change π (Fin.rev (0 : Candidate n)) = π (oneLoserLastRank n)
  congr 1

@[simp] theorem reverseRankingPositions_apply_lastRank {n : ℕ} (π : Ranking n) :
    reverseRankingPositions π (oneLoserLastRank n) = π 0 := by
  change π (Fin.rev (oneLoserLastRank n)) = π (0 : Candidate n)
  congr 1
  ext
  simp [oneLoserLastRank]

@[simp] theorem firstChoice_reverseRankingPositions {n : ℕ} (π : Ranking n) :
    firstChoice (reverseRankingPositions π) = π (oneLoserLastRank n) := by
  simp [firstChoice]

private def reverseRankingPositionsEquiv {n : ℕ} : Ranking n ≃ Ranking n where
  toFun := reverseRankingPositions
  invFun := reverseRankingPositions
  left_inv π := by
    ext i
    simp [reverseRankingPositions]
  right_inv π := by
    ext i
    simp [reverseRankingPositions]

private theorem invertedPair_center_reverseRankingPositions_iff {n : ℕ}
    (ρ π : Ranking n) (ab : Candidate n × Candidate n) :
    invertedPair ρ (reverseRankingPositions π) ab ↔
      invertedPair (reverseRankingPositions ρ) π (ab.2, ab.1) := by
  unfold invertedPair reverseRankingPositions rankOf
  simp

private theorem kendallTau_reverseRankingPositions_eq {n : ℕ}
    (ρ π : Ranking n) :
    kendallTau ρ (reverseRankingPositions π) =
      kendallTau (reverseRankingPositions ρ) π := by
  classical
  unfold kendallTau
  refine (Finset.card_bij
    (s := inversionFinset (reverseRankingPositions ρ) π)
    (t := inversionFinset ρ (reverseRankingPositions π))
    (i := fun ab _ => (ab.2, ab.1)) ?hi ?hinj ?hsurj).symm
  · intro ab hab
    have hinv :
        invertedPair (reverseRankingPositions ρ) π ab := by
      simpa [inversionFinset] using hab
    have hinv' :
        invertedPair ρ (reverseRankingPositions π) (ab.2, ab.1) := by
      exact (invertedPair_center_reverseRankingPositions_iff ρ π (ab.2, ab.1)).2
        (by simpa using hinv)
    simpa [inversionFinset] using hinv'
  · intro ab _ cd _ h
    exact Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1
  · intro ab hab
    have hinv :
        invertedPair ρ (reverseRankingPositions π) ab := by
      simpa [inversionFinset] using hab
    let pre : Candidate n × Candidate n := (ab.2, ab.1)
    have hinvPre :
        invertedPair (reverseRankingPositions ρ) π pre := by
      exact
        (invertedPair_center_reverseRankingPositions_iff ρ π ab).1 hinv
    refine ⟨pre, ?_, ?_⟩
    · simpa [inversionFinset] using hinvPre
    · simp [pre]

theorem zero_ne_oneLoserLastRank (n : ℕ) :
    (0 : Candidate n) ≠ oneLoserLastRank n := by
  simpa [oneLoserLastRank] using zero_ne_lastRank n

@[simp] theorem rankOf_oneLoserLoser {n : ℕ} (ρ : Ranking n) :
    rankOf ρ (oneLoserLoser ρ) = oneLoserLastRank n := by
  simp [rankOf, oneLoserLoser]

@[simp] theorem mem_oneLoserWinnerSet_iff {n : ℕ} (ρ : Ranking n)
    (c : Candidate n) :
    c ∈ oneLoserWinnerSet ρ ↔ c ≠ oneLoserLoser ρ := by
  classical
  simp [oneLoserWinnerSet]

/-- Any candidate other than the center-last candidate has center rank above last. -/
theorem rankOf_lt_oneLoserLastRank_of_ne_loser {n : ℕ}
    (ρ : Ranking n) {c : Candidate n}
    (hc : c ≠ oneLoserLoser ρ) :
    rankOf ρ c < oneLoserLastRank n := by
  have hrank_ne : rankOf ρ c ≠ oneLoserLastRank n := by
    intro hrank
    apply hc
    have happly := congrArg ρ hrank
    simpa [rankOf, oneLoserLoser] using happly
  change (rankOf ρ c).val < (oneLoserLastRank n).val
  have hlt : (rankOf ρ c).val < n + 2 := (rankOf ρ c).isLt
  have hne : (rankOf ρ c).val ≠ n + 1 := by
    intro hval
    exact hrank_ne (Fin.ext hval)
  simp [oneLoserLastRank]
  omega

/-- Relevant ordered pairs for all-but-one selection: each winner versus the loser. -/
abbrev OneLoserSelectionPair {n : ℕ} (ρ : Ranking n) :=
  { hi : Candidate n // hi ∈ oneLoserWinnerSet ρ }

namespace OneLoserSelectionPair

variable {n : ℕ} {ρ : Ranking n}

/-- Higher-tier candidate of a one-loser selection pair. -/
def hi (pair : OneLoserSelectionPair ρ) : Candidate n := pair.1

/-- Lower-tier candidate of every one-loser selection pair. -/
def lo (_pair : OneLoserSelectionPair ρ) : Candidate n :=
  oneLoserLoser ρ

@[simp] theorem hi_mem (pair : OneLoserSelectionPair ρ) :
    pair.hi ∈ oneLoserWinnerSet ρ := pair.2

theorem hi_ne_lo (pair : OneLoserSelectionPair ρ) :
    pair.hi ≠ pair.lo := by
  simpa [hi, lo] using (mem_oneLoserWinnerSet_iff ρ pair.1).1 pair.2

@[simp] theorem rankOf_lo (pair : OneLoserSelectionPair ρ) :
    rankOf ρ pair.lo = oneLoserLastRank n := by
  simp [lo]

theorem rankOf_hi_lt_lastRank (pair : OneLoserSelectionPair ρ) :
    rankOf ρ pair.hi < oneLoserLastRank n :=
  rankOf_lt_oneLoserLastRank_of_ne_loser ρ pair.hi_ne_lo

theorem rankOf_hi_lt_lo (pair : OneLoserSelectionPair ρ) :
    rankOf ρ pair.hi < rankOf ρ pair.lo := by
  rw [pair.rankOf_lo]
  exact pair.rankOf_hi_lt_lastRank

instance instNonempty (ρ : Ranking n) : Nonempty (OneLoserSelectionPair ρ) := by
  refine ⟨⟨ρ 0, ?_⟩⟩
  rw [mem_oneLoserWinnerSet_iff]
  intro h
  have hidx : (0 : Candidate n) = oneLoserLastRank n := by
    simpa [oneLoserLoser] using congrArg ρ.symm h
  exact zero_ne_oneLoserLastRank n hidx

end OneLoserSelectionPair

/--
Cross-tier ordered pairs at the all-but-one cutoff.  The first candidate lies
above the cutoff and the second candidate lies at or below it.
-/
def OneLoserRelevantPair {n : ℕ} (ρ : Ranking n) : Type :=
  { pair : Candidate n × Candidate n //
    rankOf ρ pair.1 < oneLoserLastRank n ∧
      oneLoserLastRank n ≤ rankOf ρ pair.2 }

namespace OneLoserRelevantPair

variable {n : ℕ} {ρ : Ranking n}

/-- Higher-tier candidate in an all-but-one relevant pair. -/
def hi (pair : OneLoserRelevantPair ρ) : Candidate n := pair.1.1

/-- Lower-tier candidate in an all-but-one relevant pair. -/
def lo (pair : OneLoserRelevantPair ρ) : Candidate n := pair.1.2

theorem rankOf_hi_lt_lastRank (pair : OneLoserRelevantPair ρ) :
    rankOf ρ pair.hi < oneLoserLastRank n := pair.2.1

theorem lastRank_le_rankOf_lo (pair : OneLoserRelevantPair ρ) :
    oneLoserLastRank n ≤ rankOf ρ pair.lo := pair.2.2

@[simp] theorem rankOf_lo (pair : OneLoserRelevantPair ρ) :
    rankOf ρ pair.lo = oneLoserLastRank n := by
  apply le_antisymm
  · change (rankOf ρ pair.lo).val ≤ (oneLoserLastRank n).val
    have hlt : (rankOf ρ pair.lo).val < n + 2 := (rankOf ρ pair.lo).isLt
    simp [oneLoserLastRank]
    omega
  · exact pair.lastRank_le_rankOf_lo

@[simp] theorem lo_eq_loser (pair : OneLoserRelevantPair ρ) :
    pair.lo = oneLoserLoser ρ := by
  have h : rankOf ρ pair.lo = rankOf ρ (oneLoserLoser ρ) := by
    rw [pair.rankOf_lo, rankOf_oneLoserLoser]
  have happly := congrArg ρ h
  simpa [rankOf] using happly

theorem hi_mem_winnerSet (pair : OneLoserRelevantPair ρ) :
    pair.hi ∈ oneLoserWinnerSet ρ := by
  rw [mem_oneLoserWinnerSet_iff]
  intro h
  have hlt : rankOf ρ (oneLoserLoser ρ) < oneLoserLastRank n := by
    simpa [h] using pair.rankOf_hi_lt_lastRank
  rw [rankOf_oneLoserLoser] at hlt
  exact (lt_irrefl _) hlt

theorem hi_ne_lo (pair : OneLoserRelevantPair ρ) :
    pair.hi ≠ pair.lo := by
  rw [pair.lo_eq_loser]
  exact (mem_oneLoserWinnerSet_iff ρ pair.hi).1 pair.hi_mem_winnerSet

end OneLoserRelevantPair

/--
At the all-but-one cutoff `W = n + 1`, the generic cross-tier relevant pairs
are exactly winner-versus-center-last pairs.
-/
def oneLoserRelevantPairEquivSelectionPair {n : ℕ} (ρ : Ranking n) :
    OneLoserRelevantPair ρ ≃ OneLoserSelectionPair ρ where
  toFun pair := ⟨pair.hi, pair.hi_mem_winnerSet⟩
  invFun pair :=
    ⟨(pair.hi, pair.lo),
      ⟨pair.rankOf_hi_lt_lastRank, by rw [pair.rankOf_lo]⟩⟩
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (OneLoserRelevantPair.lo_eq_loser pair).symm
  right_inv pair := by
    apply Subtype.ext
    rfl

theorem eq_of_rankOf_eq {n : ℕ} {π : Ranking n} {a b : Candidate n}
    (h : rankOf π a = rankOf π b) :
    a = b := by
  exact AppliedModelingLib.SocialChoice.Ranking.eq_of_rankOf_eq π h

/-- Top-`n + 1` approval is equivalent to not being ranked last. -/
theorem approvedByK_oneLoser_iff_rankOf_ne_lastRank {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    approvedByK (n + 1) π c ↔ rankOf π c ≠ oneLoserLastRank n := by
  simpa [oneLoserLastRank] using
    (approvedByK_allButOne_iff_rankOf_ne_lastRank π c)

/-- Failing top-`n + 1` approval is equivalent to being ranked last. -/
theorem not_approvedByK_oneLoser_iff_rankOf_lastRank {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    ¬ approvedByK (n + 1) π c ↔ rankOf π c = oneLoserLastRank n := by
  simpa [oneLoserLastRank] using
    (not_approvedByK_allButOne_iff_rankOf_lastRank π c)

/--
For one-loser approval, the ordered-pair up-event is exactly that the lower
candidate is ranked last.
-/
theorem kApprovalPairUp_oneLoser_iff_rankOf_lo_lastRank {n : ℕ}
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) (π : Ranking n) :
    approvedByK (n + 1) π hi ∧ ¬ approvedByK (n + 1) π lo ↔
      rankOf π lo = oneLoserLastRank n := by
  simpa [oneLoserLastRank] using
    (kApprovalPairUp_allButOne_iff_rankOf_lo_lastRank hhi_lo π)

/--
For one-loser approval, the ordered-pair down-event is exactly that the higher
candidate is ranked last.
-/
theorem kApprovalPairDown_oneLoser_iff_rankOf_hi_lastRank {n : ℕ}
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) (π : Ranking n) :
    approvedByK (n + 1) π lo ∧ ¬ approvedByK (n + 1) π hi ↔
      rankOf π hi = oneLoserLastRank n :=
  by
    simpa [oneLoserLastRank] using
      (kApprovalPairDown_allButOne_iff_rankOf_hi_lastRank hhi_lo π)

/-- One-loser ordered-pair up probability as a last-rank probability. -/
theorem kApprovalPairUpProb_oneLoser_eq_rankOf_lastProb {n : ℕ}
    (μ : PMF (Ranking n)) {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairUpProb μ (n + 1) hi lo =
      AppliedModelingLib.pmfProb μ (fun π : Ranking n => rankOf π lo = oneLoserLastRank n) := by
  simpa [oneLoserLastRank] using
    (kApprovalPairUpProb_allButOne_eq_rankOf_lastProb μ hhi_lo)

/-- One-loser ordered-pair down probability as a last-rank probability. -/
theorem kApprovalPairDownProb_oneLoser_eq_rankOf_lastProb {n : ℕ}
    (μ : PMF (Ranking n)) {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairDownProb μ (n + 1) hi lo =
      AppliedModelingLib.pmfProb μ (fun π : Ranking n => rankOf π hi = oneLoserLastRank n) := by
  simpa [oneLoserLastRank] using
    (kApprovalPairDownProb_allButOne_eq_rankOf_lastProb μ hhi_lo)

/-- Boundary-pair up probability as the probability that the center-loser is last. -/
theorem kApprovalPairUpProb_oneLoser_pair_eq_rankOf_lo_lastProb {n : ℕ}
    (μ : PMF (Ranking n)) {ρ : Ranking n} (pair : OneLoserSelectionPair ρ) :
    kApprovalPairUpProb μ (n + 1) pair.hi pair.lo =
      AppliedModelingLib.pmfProb μ
        (fun π : Ranking n => rankOf π pair.lo = oneLoserLastRank n) :=
  kApprovalPairUpProb_oneLoser_eq_rankOf_lastProb μ pair.hi_ne_lo

/-- Boundary-pair down probability as the probability that the winner is last. -/
theorem kApprovalPairDownProb_oneLoser_pair_eq_rankOf_hi_lastProb {n : ℕ}
    (μ : PMF (Ranking n)) {ρ : Ranking n} (pair : OneLoserSelectionPair ρ) :
    kApprovalPairDownProb μ (n + 1) pair.hi pair.lo =
      AppliedModelingLib.pmfProb μ
        (fun π : Ranking n => rankOf π pair.hi = oneLoserLastRank n) :=
  kApprovalPairDownProb_oneLoser_eq_rankOf_lastProb μ pair.hi_ne_lo

/--
Unnormalised Mallows mass of rankings where `c` is ranked last.  For
one-loser approval this is the corresponding ordered-pair up or down event
mass, depending on which side of the pair contains `c`.
-/
def mallowsOneLoserLastRankWeight {n : ℕ}
    (M : MallowsSpec n) (c : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if rankOf π c = oneLoserLastRank n
    then mallowsWeight M.q M.center π
    else 0

private theorem rankOf_eq_iff_apply_eq {n : ℕ}
    (π : Ranking n) (c r : Candidate n) :
    rankOf π c = r ↔ c = π r := by
  constructor
  · intro h
    rw [← h]
    simp [rankOf]
  · intro h
    rw [h]
    simp [rankOf]

@[simp] theorem rankOf_reverseRankingPositions {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    rankOf (reverseRankingPositions π) c =
      Fin.rev (rankOf π c) := by
  simp [rankOf, reverseRankingPositions]

theorem mallowsOneLoserLastRankWeight_eq_firstWeightKernel_reverseCenter {n : ℕ}
    (M : MallowsSpec n) (c : Candidate n) :
    mallowsOneLoserLastRankWeight M c =
      MallowsSpec.firstWeightKernel M.q (reverseRankingPositions M.center) c := by
  classical
  unfold mallowsOneLoserLastRankWeight MallowsSpec.firstWeightKernel
  calc
    (∑ π : Ranking n,
        if rankOf π c = oneLoserLastRank n
        then mallowsWeight M.q M.center π
        else 0)
        =
      ∑ π : Ranking n,
        if c = π (oneLoserLastRank n)
        then mallowsWeight M.q M.center π
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hiff := rankOf_eq_iff_apply_eq π c (oneLoserLastRank n)
          by_cases hπ : rankOf π c = oneLoserLastRank n
          · rw [if_pos hπ, if_pos (hiff.1 hπ)]
          · rw [if_neg hπ, if_neg (by intro h; exact hπ (hiff.2 h))]
    _ =
      ∑ σ : Ranking n,
        if c = σ 0
        then mallowsWeight M.q M.center (reverseRankingPositions σ)
        else 0 := by
          simpa [reverseRankingPositionsEquiv] using
            (Equiv.sum_comp (reverseRankingPositionsEquiv : Ranking n ≃ Ranking n)
              (fun π : Ranking n =>
                if c = π (oneLoserLastRank n)
                then mallowsWeight M.q M.center π
                else 0)).symm
    _ =
      ∑ σ : Ranking n,
        if c = firstChoice σ
        then mallowsWeight M.q (reverseRankingPositions M.center) σ
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          have hkendall :
              kendallTau M.center (reverseRankingPositions σ) =
                kendallTau (reverseRankingPositions M.center) σ :=
            kendallTau_reverseRankingPositions_eq M.center σ
          by_cases hσ : c = firstChoice σ
          · rw [if_pos (by simpa [firstChoice] using hσ), if_pos hσ]
            simp [mallowsWeight, hkendall]
          · rw [if_neg (by
              intro h
              exact hσ (by simpa [firstChoice] using h)), if_neg hσ]

theorem mallowsOneLoserLastRankWeight_eq_reverse_rank_pow_tail {n : ℕ}
    (M : MallowsSpec n) (c : Candidate n) :
    mallowsOneLoserLastRankWeight M c =
      M.q ^ (rankOf (reverseRankingPositions M.center) c : ℕ) *
        MallowsSpec.firstTailKernel n M.q := by
  rw [mallowsOneLoserLastRankWeight_eq_firstWeightKernel_reverseCenter M c]
  exact
    MallowsSpec.firstWeightKernel_eq_rank_pow_mul_firstTailKernel
      M.q_pos (reverseRankingPositions M.center) c

/-- Probability that `c` is ranked last under a Mallows law. -/
def mallowsOneLoserLastRankProb {n : ℕ}
    (M : MallowsSpec n) (c : Candidate n) : ℝ :=
  AppliedModelingLib.pmfProb M.law
    (fun π : Ranking n => rankOf π c = oneLoserLastRank n)

/-- One-loser ordered-pair up probability as a Mallows last-rank probability. -/
theorem kApprovalPairUpProb_oneLoser_eq_mallowsLastRankProb {n : ℕ}
    (M : MallowsSpec n) {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairUpProb M.law (n + 1) hi lo =
      mallowsOneLoserLastRankProb M lo := by
  exact kApprovalPairUpProb_oneLoser_eq_rankOf_lastProb M.law hhi_lo

/-- One-loser ordered-pair down probability as a Mallows last-rank probability. -/
theorem kApprovalPairDownProb_oneLoser_eq_mallowsLastRankProb {n : ℕ}
    (M : MallowsSpec n) {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairDownProb M.law (n + 1) hi lo =
      mallowsOneLoserLastRankProb M hi := by
  exact kApprovalPairDownProb_oneLoser_eq_rankOf_lastProb M.law hhi_lo

/-- The one-loser last-rank probability is its unnormalised mass divided by `Z`. -/
theorem mallowsOneLoserLastRankProb_eq_weight_div_partition {n : ℕ}
    (M : MallowsSpec n) (c : Candidate n) :
    mallowsOneLoserLastRankProb M c =
      mallowsOneLoserLastRankWeight M c / M.partition := by
  classical
  unfold mallowsOneLoserLastRankProb mallowsOneLoserLastRankWeight
  unfold AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp
  calc
    ∑ π : Ranking n, (M.law π).toReal *
        (if rankOf π c = oneLoserLastRank n then (1 : ℝ) else 0)
        = ∑ π : Ranking n,
            (mallowsWeight M.q M.center π / M.partition) *
              (if rankOf π c = oneLoserLastRank n then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking n,
          (if rankOf π c = oneLoserLastRank n
            then mallowsWeight M.q M.center π
            else 0) / M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : rankOf π c = oneLoserLastRank n <;> simp [h]
    _ = (∑ π : Ranking n,
          if rankOf π c = oneLoserLastRank n
          then mallowsWeight M.q M.center π
          else 0) / M.partition := by
          rw [Finset.sum_div]

theorem mallowsOneLoserLastRankWeight_pos {n : ℕ}
    (M : MallowsSpec n) (c : Candidate n) :
    0 < mallowsOneLoserLastRankWeight M c := by
  rw [mallowsOneLoserLastRankWeight_eq_reverse_rank_pow_tail M c]
  exact mul_pos (pow_pos M.q_pos _)
    (by simpa [MallowsSpec.firstTailCanonical] using M.firstTailCanonical_pos)

theorem mallowsOneLoserLastRankProb_pos {n : ℕ}
    (M : MallowsSpec n) (c : Candidate n) :
    0 < mallowsOneLoserLastRankProb M c := by
  rw [mallowsOneLoserLastRankProb_eq_weight_div_partition M c]
  exact div_pos (mallowsOneLoserLastRankWeight_pos M c) M.partition_pos

theorem mallowsOneLoserLastRankProb_add_le_one {n : ℕ}
    (M : MallowsSpec n) {a b : Candidate n} (hab : a ≠ b) :
    mallowsOneLoserLastRankProb M a +
      mallowsOneLoserLastRankProb M b ≤ 1 := by
  classical
  have hdisjoint :
      ∀ π : Ranking n,
        rankOf π a = oneLoserLastRank n →
          rankOf π b = oneLoserLastRank n → False := by
    intro π ha hb
    apply hab
    exact eq_of_rankOf_eq (ha.trans hb.symm)
  have hunion :
      AppliedModelingLib.pmfProb M.law
          (fun π : Ranking n =>
            rankOf π a = oneLoserLastRank n ∨
              rankOf π b = oneLoserLastRank n) =
        mallowsOneLoserLastRankProb M a +
          mallowsOneLoserLastRankProb M b := by
    simpa [mallowsOneLoserLastRankProb] using
      (AppliedModelingLib.pmfProb_or_eq_add_of_disjoint M.law
        (fun π : Ranking n => rankOf π a = oneLoserLastRank n)
        (fun π : Ranking n => rankOf π b = oneLoserLastRank n)
        hdisjoint)
  rw [← hunion]
  exact AppliedModelingLib.pmfProb_le_one M.law
    (fun π : Ranking n =>
      rankOf π a = oneLoserLastRank n ∨
        rankOf π b = oneLoserLastRank n)

theorem mallowsOneLoserLastRankWeight_le_of_rank_le {n : ℕ}
    (M : MallowsSpec n) (hq_le : M.q ≤ 1)
    {a b : Candidate n}
    (hrank : rankOf M.center a ≤ rankOf M.center b) :
    mallowsOneLoserLastRankWeight M a ≤
      mallowsOneLoserLastRankWeight M b := by
  rw [mallowsOneLoserLastRankWeight_eq_reverse_rank_pow_tail M a,
    mallowsOneLoserLastRankWeight_eq_reverse_rank_pow_tail M b]
  have hrev :
      rankOf (reverseRankingPositions M.center) b ≤
        rankOf (reverseRankingPositions M.center) a := by
    rw [rankOf_reverseRankingPositions, rankOf_reverseRankingPositions]
    exact
      (Fin.rev_le_iff
        (i := rankOf M.center b)
        (j := Fin.rev (rankOf M.center a))).2
        (by simpa using hrank)
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one M.q_pos.le hq_le hrev)
    (le_of_lt (by
      simpa [MallowsSpec.firstTailCanonical] using M.firstTailCanonical_pos))

theorem mallowsOneLoserLastRankProb_le_of_rank_le {n : ℕ}
    (M : MallowsSpec n) (hq_le : M.q ≤ 1)
    {a b : Candidate n}
    (hrank : rankOf M.center a ≤ rankOf M.center b) :
    mallowsOneLoserLastRankProb M a ≤
      mallowsOneLoserLastRankProb M b := by
  rw [mallowsOneLoserLastRankProb_eq_weight_div_partition M a,
    mallowsOneLoserLastRankProb_eq_weight_div_partition M b]
  exact div_le_div_of_nonneg_right
    (mallowsOneLoserLastRankWeight_le_of_rank_le M hq_le hrank)
    (le_of_lt M.partition_pos)

/-- Mallows one-loser up probability in normalized weight form. -/
theorem kApprovalPairUpProb_oneLoser_eq_mallowsLastRankWeight_div_partition {n : ℕ}
    (M : MallowsSpec n) {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairUpProb M.law (n + 1) hi lo =
      mallowsOneLoserLastRankWeight M lo / M.partition := by
  rw [kApprovalPairUpProb_oneLoser_eq_rankOf_lastProb M.law hhi_lo]
  exact mallowsOneLoserLastRankProb_eq_weight_div_partition M lo

/-- Mallows one-loser down probability in normalized weight form. -/
theorem kApprovalPairDownProb_oneLoser_eq_mallowsLastRankWeight_div_partition {n : ℕ}
    (M : MallowsSpec n) {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairDownProb M.law (n + 1) hi lo =
      mallowsOneLoserLastRankWeight M hi / M.partition := by
  rw [kApprovalPairDownProb_oneLoser_eq_rankOf_lastProb M.law hhi_lo]
  exact mallowsOneLoserLastRankProb_eq_weight_div_partition M hi

end

end GGSG19TopThree
