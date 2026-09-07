import AppliedModelingLib.SocialChoice.Ranking.Kendall

/-!
# Sequential Choice Helpers for Rankings

Probability-free ranking operations for sequential choice arguments: the best
remaining candidate in a finite feasible set, candidate-position swaps, and
deterministic value comparisons after correcting inverted pairs.
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

noncomputable section

/--
The best candidate in a finite remaining set according to a ranking.

For the empty set this returns the first choice as a harmless default; all
sequential optimality predicates should use feasible histories with a nonempty
remaining set.
-/
def bestInSet {n : ℕ} (π : Ranking n)
    (remaining : Finset (Candidate n)) : Candidate n :=
  if h : remaining.Nonempty then
    π ((remaining.image (rankOf π)).min' (Finset.image_nonempty.mpr h))
  else
    firstChoice π

/-- Characterization of `bestInSet` from a pointwise least rank in the set. -/
theorem bestInSet_eq_of_forall_rank_le {n : ℕ} (π : Ranking n)
    (remaining : Finset (Candidate n)) {c : Candidate n}
    (hc : c ∈ remaining)
    (hmin : ∀ d : Candidate n, d ∈ remaining → rankOf π c ≤ rankOf π d) :
    bestInSet π remaining = c := by
  classical
  unfold bestInSet
  have hnonempty : remaining.Nonempty := ⟨c, hc⟩
  rw [dif_pos hnonempty]
  have hmin' :
      (remaining.image (rankOf π)).min' (Finset.image_nonempty.mpr hnonempty) =
        rankOf π c := by
    rw [Finset.min'_eq_iff]
    constructor
    · exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    · intro r hr
      rcases Finset.mem_image.mp hr with ⟨d, hd, hrd⟩
      rw [← hrd]
      exact hmin d hd
  rw [hmin']
  simp [rankOf]

/-- The best element of a nonempty remaining set is itself remaining. -/
theorem bestInSet_mem {n : ℕ} (π : Ranking n)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty) :
    bestInSet π remaining ∈ remaining := by
  classical
  unfold bestInSet
  rw [dif_pos hremaining]
  have hmin :
      (remaining.image (rankOf π)).min' (Finset.image_nonempty.mpr hremaining) ∈
        remaining.image (rankOf π) :=
    Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmin with ⟨c, hc, hc_rank⟩
  rw [← hc_rank]
  simpa [rankOf] using hc

/-- The best element has weakly minimal rank among the remaining candidates. -/
theorem rankOf_bestInSet_le {n : ℕ} (π : Ranking n)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    {d : Candidate n} (hd : d ∈ remaining) :
    rankOf π (bestInSet π remaining) ≤ rankOf π d := by
  classical
  unfold bestInSet
  rw [dif_pos hremaining]
  have hd_image : rankOf π d ∈ remaining.image (rankOf π) :=
    Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hmin_le :
      (remaining.image (rankOf π)).min' (Finset.image_nonempty.mpr hremaining) ≤
        rankOf π d :=
    Finset.min'_le _ _ hd_image
  simpa [rankOf] using hmin_le

/-- If all candidates remain, `bestInSet` is the first choice. -/
@[simp] theorem bestInSet_univ {n : ℕ} (π : Ranking n) :
    bestInSet π Finset.univ = firstChoice π := by
  classical
  refine bestInSet_eq_of_forall_rank_le π Finset.univ
    (c := firstChoice π) (Finset.mem_univ _) ?_
  intro d _
  rw [rankOf_firstChoice]
  exact Fin.zero_le _

/-- If exactly candidate `c` has been removed, `bestInSet` is `bestRemainingAfter`. -/
theorem bestInSet_univ_sdiff_singleton {n : ℕ} (π : Ranking n)
    (c : Candidate n) :
    bestInSet π (Finset.univ \ ({c} : Finset (Candidate n))) =
      bestRemainingAfter π c := by
  classical
  by_cases hfirst : firstChoice π = c
  · have hmem : secondChoice π ∈
        (Finset.univ \ ({c} : Finset (Candidate n))) := by
      simp [hfirst.symm]
    have hmin :
        ∀ d : Candidate n,
          d ∈ (Finset.univ \ ({c} : Finset (Candidate n))) →
            rankOf π (secondChoice π) ≤ rankOf π d := by
      intro d hd
      have hd_ne_c : d ≠ c := by
        simpa using hd
      have hd_ne_first : d ≠ firstChoice π := by
        intro hd_first
        exact hd_ne_c (hd_first.trans hfirst)
      by_cases hd_second : d = secondChoice π
      · simp [hd_second]
      · rw [rankOf_secondChoice]
        exact le_of_lt
          (one_lt_rankOf_of_ne_first_second π hd_ne_first hd_second)
    calc
      bestInSet π (Finset.univ \ ({c} : Finset (Candidate n)))
          = secondChoice π :=
            bestInSet_eq_of_forall_rank_le π
              (Finset.univ \ ({c} : Finset (Candidate n)))
              hmem hmin
      _ = bestRemainingAfter π c := by
            rw [← hfirst, bestRemainingAfter_of_eq]
  · have hmem : firstChoice π ∈
        (Finset.univ \ ({c} : Finset (Candidate n))) := by
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, by simpa using hfirst⟩
    have hmin :
        ∀ d : Candidate n,
          d ∈ (Finset.univ \ ({c} : Finset (Candidate n))) →
            rankOf π (firstChoice π) ≤ rankOf π d := by
      intro d hd
      rw [rankOf_firstChoice]
      exact Fin.zero_le _
    calc
      bestInSet π (Finset.univ \ ({c} : Finset (Candidate n)))
          = firstChoice π :=
            bestInSet_eq_of_forall_rank_le π
              (Finset.univ \ ({c} : Finset (Candidate n)))
              hmem hmin
      _ = bestRemainingAfter π c := by
            rw [bestRemainingAfter_of_ne π hfirst]

/-- If exactly one candidate remains, that candidate is chosen under every ranking. -/
@[simp] theorem bestInSet_singleton {n : ℕ} (π : Ranking n)
    (c : Candidate n) :
    bestInSet π ({c} : Finset (Candidate n)) = c := by
  classical
  refine bestInSet_eq_of_forall_rank_le π ({c} : Finset (Candidate n))
    (c := c) ?_ ?_
  · simp
  · intro d hd
    have hd_eq : d = c := by
      simpa using hd
    rw [hd_eq]

/-- On a two-element feasible set, `bestInSet` chooses the lower-ranked candidate. -/
theorem bestInSet_pair_eq_if_rank_lt {n : ℕ} (π : Ranking n)
    {c d : Candidate n} (hcd : c ≠ d) :
    bestInSet π ({c, d} : Finset (Candidate n)) =
      if rankOf π c < rankOf π d then c else d := by
  classical
  by_cases hlt : rankOf π c < rankOf π d
  · rw [if_pos hlt]
    refine bestInSet_eq_of_forall_rank_le π ({c, d} : Finset (Candidate n))
      (c := c) ?_ ?_
    · simp
    · intro e he
      have he_cases : e = c ∨ e = d := by
        simpa using he
      rcases he_cases with rfl | rfl
      · rfl
      · exact le_of_lt hlt
  · rw [if_neg hlt]
    have hdc : rankOf π d < rankOf π c := by
      have hle : rankOf π d ≤ rankOf π c := le_of_not_gt hlt
      have hne : rankOf π d ≠ rankOf π c := by
        intro hrank
        exact hcd (by
          simpa [rankOf] using congrArg π hrank.symm)
      exact lt_of_le_of_ne hle hne
    refine bestInSet_eq_of_forall_rank_le π ({c, d} : Finset (Candidate n))
      (c := d) ?_ ?_
    · simp
    · intro e he
      have he_cases : e = c ∨ e = d := by
        simpa using he
      rcases he_cases with rfl | rfl
      · exact le_of_lt hdc
      · rfl

@[simp] theorem rankOf_trans_center_symm {n : ℕ}
    (ρ π : Ranking n) (c : Candidate n) :
    rankOf (π.trans ρ.symm) (rankOf ρ c) = rankOf π c := by
  simp [rankOf]

/--
After relabeling candidates by center rank, the best remaining candidate is the
center rank of the original best remaining candidate.
-/
theorem bestInSet_trans_center_symm
    {n : ℕ} (ρ π : Ranking n) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    bestInSet (π.trans ρ.symm) (remaining.image (rankOf ρ)) =
      rankOf ρ (bestInSet π remaining) := by
  classical
  refine bestInSet_eq_of_forall_rank_le
    (π.trans ρ.symm) (remaining.image (rankOf ρ))
    (c := rankOf ρ (bestInSet π remaining)) ?_ ?_
  · exact Finset.mem_image.mpr
      ⟨bestInSet π remaining, bestInSet_mem π hremaining, rfl⟩
  · intro r hr
    rcases Finset.mem_image.mp hr with ⟨d, hd, rfl⟩
    rw [rankOf_trans_center_symm, rankOf_trans_center_symm]
    exact rankOf_bestInSet_le π hremaining hd

/-- Swapping the positions of two candidates in a ranking. -/
def swapCandidatePositions {n : ℕ} (π : Ranking n)
    (c d : Candidate n) : Ranking n :=
  (Equiv.swap (rankOf π c) (rankOf π d)).trans π

@[simp] theorem rankOf_swapCandidatePositions_left {n : ℕ}
    (π : Ranking n) (c d : Candidate n) :
    rankOf (swapCandidatePositions π c d) c = rankOf π d := by
  classical
  unfold swapCandidatePositions rankOf
  simp

@[simp] theorem rankOf_swapCandidatePositions_right {n : ℕ}
    (π : Ranking n) (c d : Candidate n) :
    rankOf (swapCandidatePositions π c d) d = rankOf π c := by
  classical
  unfold swapCandidatePositions rankOf
  simp

theorem rankOf_swapCandidatePositions_of_ne {n : ℕ}
    (π : Ranking n) {c d e : Candidate n}
    (hec : e ≠ c) (hed : e ≠ d) :
    rankOf (swapCandidatePositions π c d) e = rankOf π e := by
  classical
  unfold swapCandidatePositions rankOf
  have hrank_ne_c : π.symm e ≠ π.symm c := by
    intro h
    exact hec (π.symm.injective h)
  have hrank_ne_d : π.symm e ≠ π.symm d := by
    intro h
    exact hed (π.symm.injective h)
  exact Equiv.swap_apply_of_ne_of_ne hrank_ne_c hrank_ne_d

theorem swapCandidatePositions_comm {n : ℕ}
    (π : Ranking n) (c d : Candidate n) :
    swapCandidatePositions π c d = swapCandidatePositions π d c := by
  unfold swapCandidatePositions
  rw [Equiv.swap_comm (rankOf π c) (rankOf π d)]

theorem swapCandidatePositions_involutive {n : ℕ}
    (π : Ranking n) (c d : Candidate n) :
    swapCandidatePositions (swapCandidatePositions π c d) c d = π := by
  classical
  rw [swapCandidatePositions_comm (swapCandidatePositions π c d) c d]
  change
    (Equiv.swap (rankOf (swapCandidatePositions π c d) d)
        (rankOf (swapCandidatePositions π c d) c)).trans
      (swapCandidatePositions π c d) = π
  rw [rankOf_swapCandidatePositions_right, rankOf_swapCandidatePositions_left]
  rw [Equiv.swap_comm (rankOf π c) (rankOf π d)]
  unfold swapCandidatePositions
  apply Equiv.ext
  intro x
  apply π.injective
  simp [Equiv.swap_comm]

/-- Swapping two candidates' positions is an involutive equivalence on rankings. -/
def swapCandidatePositionsEquiv {n : ℕ} (c d : Candidate n) :
    Ranking n ≃ Ranking n where
  toFun π := swapCandidatePositions π c d
  invFun π := swapCandidatePositions π c d
  left_inv π := swapCandidatePositions_involutive π c d
  right_inv π := swapCandidatePositions_involutive π c d

/-- Rankings are equal when every candidate has the same position. -/
theorem ranking_ext_of_rankOf {n : ℕ} {π σ : Ranking n}
    (h : ∀ c : Candidate n, rankOf π c = rankOf σ c) :
    π = σ := by
  apply Equiv.ext
  intro i
  have hi := h (π i)
  change π.symm (π i) = σ.symm (π i) at hi
  simp only [Equiv.symm_apply_apply] at hi
  have hσ := congrArg σ hi
  simpa using hσ.symm

theorem apply_eq_of_rankOf {n : ℕ} (π : Ranking n)
    {x c : Candidate n} (h : rankOf π c = x) : π x = c := by
  have hπ := congrArg π h
  simpa [rankOf] using hπ.symm

theorem eq_of_rankOf_eq {n : ℕ} (π : Ranking n)
    {c d : Candidate n} (h : rankOf π c = rankOf π d) : c = d := by
  have hπ := congrArg π h
  simpa [rankOf] using hπ

/--
Map an inversion of the ranking with `i` and `j` swapped back to an inversion
of the original ranking, in center coordinates. The cases are the four ways an
inversion can involve one of the two swapped labels.
-/
def swapInversionMap {n : ℕ} (i j : Candidate n)
    (p : Candidate n × Candidate n) : Candidate n × Candidate n :=
  if p.2 = i then
    (p.1, j)
  else if p.1 = j then
    (i, p.2)
  else if p.1 = i ∧ j < p.2 then
    (j, p.2)
  else if p.2 = j ∧ p.1 < i then
    (p.1, i)
  else
    p

/-- Inverse decoder for `swapInversionMap` on its source inversion set. -/
def swapInversionMapInv {n : ℕ} (i j : Candidate n)
    (p : Candidate n × Candidate n) : Candidate n × Candidate n :=
  if p.2 = j ∧ p.1 < i then
    (p.1, i)
  else if p.1 = i ∧ j < p.2 then
    (j, p.2)
  else if p.1 = j then
    (i, p.2)
  else if p.2 = i then
    (p.1, j)
  else
    p

theorem swapInversionMapInv_left
    {n : ℕ} {i j : Candidate n} (hij : i < j)
    {p : Candidate n × Candidate n} (hp : p.1 < p.2) :
    swapInversionMapInv i j (swapInversionMap i j p) = p := by
  classical
  rcases p with ⟨a, b⟩
  dsimp at hp
  unfold swapInversionMap swapInversionMapInv
  by_cases hbi : b = i
  · subst b
    have hai : a < i := hp
    have haj : a < j := lt_trans hai hij
    simp [hai]
  · rw [if_neg hbi]
    by_cases haj_eq : a = j
    · subst a
      have hjb : j < b := hp
      have hbj : b ≠ j := ne_of_gt hjb
      simp [hjb, hbj]
    · rw [if_neg haj_eq]
      by_cases hai_jb : a = i ∧ j < b
      · rcases hai_jb with ⟨hai_eq, hjb⟩
        subst a
        have hbj : b ≠ j := ne_of_gt hjb
        have hji_not : ¬j < i := not_lt_of_gt hij
        simp [hjb, hbj, hji_not]
      · rw [if_neg hai_jb]
        by_cases hbj_ai : b = j ∧ a < i
        · rcases hbj_ai with ⟨hbj_eq, hai⟩
          subst b
          have hai_ne : a ≠ i := ne_of_lt hai
          have haj_ne : a ≠ j := ne_of_lt (lt_trans hai hij)
          simp [hai, hai_ne, haj_ne]
        · rw [if_neg hbj_ai]
          simp [hbi, haj_eq, hai_jb, hbj_ai]

/--
For an identity-center ranking, an inversion after swapping the positions of a
center-ordered inverted pair maps to an inversion of the original ranking.
-/
theorem swapInversionMap_mem_inversionFinset_refl
    {n : ℕ} (τ : Ranking n) {i j : Candidate n}
    (hij : i < j) (hpos : rankOf τ j < rankOf τ i)
    {p : Candidate n × Candidate n}
    (hp : p ∈ inversionFinset (Equiv.refl (Candidate n))
        (swapCandidatePositions τ i j)) :
    swapInversionMap i j p ∈
      inversionFinset (Equiv.refl (Candidate n)) τ := by
  classical
  rcases p with ⟨a, b⟩
  have hinv :
      invertedPair (Equiv.refl (Candidate n))
        (swapCandidatePositions τ i j) (a, b) := by
    simpa [inversionFinset] using hp
  have hab : a < b := by
    simpa [invertedPair, rankOf] using hinv.1
  have hrank :
      rankOf (swapCandidatePositions τ i j) b <
        rankOf (swapCandidatePositions τ i j) a := by
    simpa [invertedPair] using hinv.2
  unfold swapInversionMap
  by_cases hbi : b = i
  · rw [if_pos hbi]
    subst b
    have hai : a < i := hab
    have haj : a < j := lt_trans hai hij
    have ha_ne_i : a ≠ i := ne_of_lt hai
    have ha_ne_j : a ≠ j := ne_of_lt haj
    have hrank_a :
        rankOf (swapCandidatePositions τ i j) a = rankOf τ a :=
      rankOf_swapCandidatePositions_of_ne τ ha_ne_i ha_ne_j
    have hlt_rank : rankOf τ j < rankOf τ a := by
      simpa [hrank_a] using hrank
    have htarget :
        invertedPair (Equiv.refl (Candidate n)) τ (a, j) :=
      ⟨by simpa [rankOf] using haj, hlt_rank⟩
    simpa [inversionFinset] using htarget
  · rw [if_neg hbi]
    by_cases haj_eq : a = j
    · rw [if_pos haj_eq]
      subst a
      have hjb : j < b := hab
      have hb_ne_i : b ≠ i := by
        intro hb
        subst b
        exact (not_lt_of_gt hij) hjb
      have hb_ne_j : b ≠ j := ne_of_gt hjb
      have hrank_b :
          rankOf (swapCandidatePositions τ i j) b = rankOf τ b :=
        rankOf_swapCandidatePositions_of_ne τ hb_ne_i hb_ne_j
      have hlt_rank : rankOf τ b < rankOf τ i := by
        simpa [hrank_b] using hrank
      have htarget :
          invertedPair (Equiv.refl (Candidate n)) τ (i, b) :=
        ⟨by simpa [rankOf] using lt_trans hij hjb, hlt_rank⟩
      simpa [inversionFinset] using htarget
    · rw [if_neg haj_eq]
      by_cases hai_jb : a = i ∧ j < b
      · rw [if_pos hai_jb]
        rcases hai_jb with ⟨hai_eq, hjb⟩
        subst a
        have hb_ne_i : b ≠ i := by
          intro hb
          subst b
          exact (not_lt_of_gt hij) hjb
        have hb_ne_j : b ≠ j := ne_of_gt hjb
        have hrank_b :
            rankOf (swapCandidatePositions τ i j) b = rankOf τ b :=
          rankOf_swapCandidatePositions_of_ne τ hb_ne_i hb_ne_j
        have hlt_rank : rankOf τ b < rankOf τ j := by
          simpa [hrank_b] using hrank
        have htarget :
            invertedPair (Equiv.refl (Candidate n)) τ (j, b) :=
          ⟨by simpa [rankOf] using hjb, hlt_rank⟩
        simpa [inversionFinset] using htarget
      · rw [if_neg hai_jb]
        by_cases hbj_ai : b = j ∧ a < i
        · rw [if_pos hbj_ai]
          rcases hbj_ai with ⟨hbj_eq, hai⟩
          subst b
          have ha_ne_i : a ≠ i := ne_of_lt hai
          have ha_ne_j : a ≠ j := ne_of_lt (lt_trans hai hij)
          have hrank_a :
              rankOf (swapCandidatePositions τ i j) a = rankOf τ a :=
            rankOf_swapCandidatePositions_of_ne τ ha_ne_i ha_ne_j
          have hlt_rank : rankOf τ i < rankOf τ a := by
            simpa [hrank_a] using hrank
          have htarget :
              invertedPair (Equiv.refl (Candidate n)) τ (a, i) :=
            ⟨by simpa [rankOf] using hai, hlt_rank⟩
          simpa [inversionFinset] using htarget
        · rw [if_neg hbj_ai]
          by_cases hai : a = i
          · subst a
            have hib : i < b := hab
            have hnot_jb : ¬j < b := by
              intro hjb
              exact hai_jb ⟨rfl, hjb⟩
            have hb_ne_j : b ≠ j := by
              intro hbj
              subst b
              have hbad : rankOf τ i < rankOf τ j := by
                simpa using hrank
              exact (not_lt_of_gt hpos) hbad
            have hb_ne_i : b ≠ i := hbi
            have hrank_b :
                rankOf (swapCandidatePositions τ i j) b = rankOf τ b :=
              rankOf_swapCandidatePositions_of_ne τ hb_ne_i hb_ne_j
            have hlt_rank_bj : rankOf τ b < rankOf τ j := by
              simpa [hrank_b] using hrank
            have hlt_rank : rankOf τ b < rankOf τ i :=
              lt_trans hlt_rank_bj hpos
            have htarget :
                invertedPair (Equiv.refl (Candidate n)) τ (i, b) :=
              ⟨by simpa [rankOf] using hib, hlt_rank⟩
            simpa [inversionFinset] using htarget
          · by_cases hbj : b = j
            · subst b
              have haj_lt : a < j := hab
              have hnot_ai : ¬a < i := by
                intro hai_lt
                exact hbj_ai ⟨rfl, hai_lt⟩
              have ha_ne_i : a ≠ i := by
                intro hai_eq
                subst a
                have hbad : rankOf τ i < rankOf τ j := by
                  simpa using hrank
                exact (not_lt_of_gt hpos) hbad
              have ha_ne_j : a ≠ j := haj_eq
              have hrank_a :
                  rankOf (swapCandidatePositions τ i j) a = rankOf τ a :=
                rankOf_swapCandidatePositions_of_ne τ ha_ne_i ha_ne_j
              have hlt_rank_ia : rankOf τ i < rankOf τ a := by
                simpa [hrank_a] using hrank
              have hlt_rank : rankOf τ j < rankOf τ a :=
                lt_trans hpos hlt_rank_ia
              have htarget :
                  invertedPair (Equiv.refl (Candidate n)) τ (a, j) :=
                ⟨by simpa [rankOf] using haj_lt, hlt_rank⟩
              simpa [inversionFinset] using htarget
            · have ha_ne_i : a ≠ i := hai
              have ha_ne_j : a ≠ j := haj_eq
              have hb_ne_i : b ≠ i := hbi
              have hb_ne_j : b ≠ j := hbj
              have hrank_a :
                  rankOf (swapCandidatePositions τ i j) a = rankOf τ a :=
                rankOf_swapCandidatePositions_of_ne τ ha_ne_i ha_ne_j
              have hrank_b :
                  rankOf (swapCandidatePositions τ i j) b = rankOf τ b :=
                rankOf_swapCandidatePositions_of_ne τ hb_ne_i hb_ne_j
              have hlt_rank : rankOf τ b < rankOf τ a := by
                simpa [hrank_a, hrank_b] using hrank
              have htarget :
                  invertedPair (Equiv.refl (Candidate n)) τ (a, b) :=
                ⟨by simpa [rankOf] using hab, hlt_rank⟩
              simpa [inversionFinset] using htarget

/--
Swapping a center-ordered inverted pair in an identity-center ranking weakly
lowers Kendall tau.
-/
theorem kendallTau_refl_swapCandidatePositions_le
    {n : ℕ} (τ : Ranking n) {i j : Candidate n}
    (hij : i < j) (hpos : rankOf τ j < rankOf τ i) :
    kendallTau (Equiv.refl (Candidate n)) (swapCandidatePositions τ i j) ≤
      kendallTau (Equiv.refl (Candidate n)) τ := by
  classical
  unfold kendallTau
  refine Finset.card_le_card_of_injOn
    (swapInversionMap i j) ?hmaps ?hinj
  · intro p hp
    exact swapInversionMap_mem_inversionFinset_refl τ hij hpos hp
  · intro p hp q hq hpq
    have hp_inv :
        invertedPair (Equiv.refl (Candidate n))
          (swapCandidatePositions τ i j) p := by
      simpa [inversionFinset] using hp
    have hq_inv :
        invertedPair (Equiv.refl (Candidate n))
          (swapCandidatePositions τ i j) q := by
      simpa [inversionFinset] using hq
    have hp_order : p.1 < p.2 := by
      simpa [invertedPair, rankOf] using hp_inv.1
    have hq_order : q.1 < q.2 := by
      simpa [invertedPair, rankOf] using hq_inv.1
    have hp_left :
        swapInversionMapInv i j (swapInversionMap i j p) = p :=
      swapInversionMapInv_left hij hp_order
    have hq_left :
        swapInversionMapInv i j (swapInversionMap i j q) = q :=
      swapInversionMapInv_left hij hq_order
    rw [← hp_left, ← hq_left, hpq]

/--
Swapping a center-ordered inverted pair weakly lowers Kendall tau for an
arbitrary center ranking.
-/
theorem kendallTau_swapCandidatePositions_le_of_rank_lt_of_rank_gt
    {n : ℕ} (ρ π : Ranking n) {c d : Candidate n}
    (hcenter : rankOf ρ c < rankOf ρ d)
    (hpos : rankOf π d < rankOf π c) :
    kendallTau ρ (swapCandidatePositions π c d) ≤ kendallTau ρ π := by
  classical
  let τ : Ranking n := π.trans ρ.symm
  let i : Candidate n := rankOf ρ c
  let j : Candidate n := rankOf ρ d
  have hij : i < j := by simpa [i, j] using hcenter
  have hc : ρ i = c := by simp [i, rankOf]
  have hd : ρ j = d := by simp [j, rankOf]
  have hposτ : rankOf τ j < rankOf τ i := by
    simpa [τ, i, j, hc, hd, rankOf] using hpos
  have hπ : τ.trans ρ = π := by
    ext x
    simp [τ]
  have hswap :
      swapCandidatePositions π c d =
        (swapCandidatePositions τ i j).trans ρ := by
    ext x
    simp [swapCandidatePositions, τ, i, j, rankOf]
  calc
    kendallTau ρ (swapCandidatePositions π c d)
        = kendallTau ρ ((swapCandidatePositions τ i j).trans ρ) := by
          rw [hswap]
    _ = kendallTau (Equiv.refl (Candidate n))
          (swapCandidatePositions τ i j) := by
          rw [kendallTau_center_trans]
    _ ≤ kendallTau (Equiv.refl (Candidate n)) τ :=
          kendallTau_refl_swapCandidatePositions_le τ hij hposτ
    _ = kendallTau ρ (τ.trans ρ) := by
          rw [kendallTau_center_trans]
    _ = kendallTau ρ π := by
          rw [hπ]

/--
If `d` is best in a remaining set containing both `c` and `d`, then swapping
the positions of `c` and `d` makes `c` best in that same remaining set.
-/
theorem bestInSet_swapCandidatePositions_of_bestInSet_eq
    {n : ℕ} (π : Ranking n) {remaining : Finset (Candidate n)}
    {c d : Candidate n} (hc : c ∈ remaining) (hd : d ∈ remaining)
    (hbest : bestInSet π remaining = d) :
    bestInSet (swapCandidatePositions π c d) remaining = c := by
  classical
  refine bestInSet_eq_of_forall_rank_le
    (swapCandidatePositions π c d) remaining hc ?_
  intro e he
  have hremaining : remaining.Nonempty := ⟨d, hd⟩
  have hminπ :
      rankOf π d ≤ rankOf π e := by
    simpa [hbest] using rankOf_bestInSet_le π hremaining he
  by_cases hec : e = c
  · simp [hec]
  · by_cases hed' : e = d
    · subst e
      have hmin_c :
          rankOf π d ≤ rankOf π c := by
        simpa [hbest] using rankOf_bestInSet_le π hremaining hc
      simpa using hmin_c
    · rw [rankOf_swapCandidatePositions_left]
      rw [rankOf_swapCandidatePositions_of_ne π hec hed']
      exact hminπ

theorem bestInSet_swapCandidatePositions_eq_iff
    {n : ℕ} (π : Ranking n) {remaining : Finset (Candidate n)}
    {c d : Candidate n} (hc : c ∈ remaining) (hd : d ∈ remaining) :
    c = bestInSet (swapCandidatePositions π c d) remaining ↔
      d = bestInSet π remaining := by
  constructor
  · intro h
    have hbest :
        bestInSet (swapCandidatePositions π c d) remaining = c := h.symm
    have hswap := bestInSet_swapCandidatePositions_of_bestInSet_eq
      (swapCandidatePositions π c d) hd hc hbest
    rw [swapCandidatePositions_comm (swapCandidatePositions π c d) d c,
      swapCandidatePositions_involutive] at hswap
    exact hswap.symm
  · intro h
    exact (bestInSet_swapCandidatePositions_of_bestInSet_eq
      π hc hd h.symm).symm

/--
If `d` is not the best remaining candidate and `d` precedes `c`, then moving
`c` into `d`'s position and `d` into `c`'s position leaves the best remaining
candidate unchanged.
-/
theorem bestInSet_swapCandidatePositions_of_not_best
    {n : ℕ} (π : Ranking n) {remaining : Finset (Candidate n)}
    {c d : Candidate n} (hc : c ∈ remaining) (hd : d ∈ remaining)
    (hpos : rankOf π d < rankOf π c)
    (hnot : d ≠ bestInSet π remaining) :
    bestInSet (swapCandidatePositions π c d) remaining =
      bestInSet π remaining := by
  classical
  have hremaining : remaining.Nonempty := ⟨d, hd⟩
  let b : Candidate n := bestInSet π remaining
  have hb_mem : b ∈ remaining := bestInSet_mem π hremaining
  have hb_le_d : rankOf π b ≤ rankOf π d :=
    rankOf_bestInSet_le π hremaining hd
  have hb_ne_d : b ≠ d := by
    intro hbd
    exact hnot hbd.symm
  have hb_rank_ne_d : rankOf π b ≠ rankOf π d := by
    intro h
    exact hb_ne_d (by
      simpa [rankOf] using congrArg π h)
  have hb_lt_d : rankOf π b < rankOf π d :=
    lt_of_le_of_ne hb_le_d hb_rank_ne_d
  have hb_lt_c : rankOf π b < rankOf π c := lt_trans hb_lt_d hpos
  have hb_ne_c : b ≠ c := by
    intro hbc
    have hb_le_d' : rankOf π c ≤ rankOf π d := by
      simpa [hbc] using hb_le_d
    exact (not_lt_of_ge hb_le_d') hpos
  refine bestInSet_eq_of_forall_rank_le
    (swapCandidatePositions π c d) remaining hb_mem ?_
  intro e he
  have hb_swap :
      rankOf (swapCandidatePositions π c d) b = rankOf π b :=
    rankOf_swapCandidatePositions_of_ne π hb_ne_c hb_ne_d
  by_cases hec : e = c
  · subst e
    rw [hb_swap, rankOf_swapCandidatePositions_left]
    exact le_of_lt hb_lt_d
  · by_cases hed' : e = d
    · subst e
      rw [hb_swap, rankOf_swapCandidatePositions_right]
      exact le_of_lt hb_lt_c
    · rw [hb_swap, rankOf_swapCandidatePositions_of_ne π hec hed']
      exact rankOf_bestInSet_le π hremaining he

/--
Correcting an inverted center-ordered pair inside the remaining set weakly
improves the deterministic value of the best remaining candidate.
-/
theorem bestInSet_value_le_swapCandidatePositions
    {n : ℕ} (ρ π : Ranking n) {remaining : Finset (Candidate n)}
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hvalue : WeaklyOrderedBy ρ value)
    (hcenter : rankOf ρ c < rankOf ρ d)
    (hc : c ∈ remaining) (hd : d ∈ remaining)
    (hpos : rankOf π d < rankOf π c) :
    value (bestInSet π remaining) ≤
      value (bestInSet (swapCandidatePositions π c d) remaining) := by
  classical
  by_cases hbest : d = bestInSet π remaining
  · have hswap :
        bestInSet (swapCandidatePositions π c d) remaining = c :=
      bestInSet_swapCandidatePositions_of_bestInSet_eq
        π hc hd hbest.symm
    rw [← hbest, hswap]
    exact hvalue hcenter
  · have hswap :
        bestInSet (swapCandidatePositions π c d) remaining =
          bestInSet π remaining :=
      bestInSet_swapCandidatePositions_of_not_best
        π hc hd hpos hbest
    rw [hswap]

theorem le_castSucc_of_le_succ_of_ne
    {n : ℕ} {k : Fin (n + 1)} {x : Fin (n + 2)}
    (hx : x ≤ k.succ) (hne : x ≠ k.succ) :
    x ≤ k.castSucc := by
  rw [Fin.le_iff_val_le_val] at hx ⊢
  change x.val ≤ k.val
  change x.val ≤ k.val + 1 at hx
  have hne_val : x.val ≠ k.val + 1 := by
    intro hval
    exact hne (Fin.ext hval)
  omega

theorem succ_le_of_castSucc_le_of_ne
    {n : ℕ} {k : Fin (n + 1)} {x : Fin (n + 2)}
    (hx : k.castSucc ≤ x) (hne : x ≠ k.castSucc) :
    k.succ ≤ x := by
  rw [Fin.le_iff_val_le_val] at hx ⊢
  change k.val + 1 ≤ x.val
  change k.val ≤ x.val at hx
  have hne_val : x.val ≠ k.val := by
    intro hval
    exact hne (Fin.ext hval)
  omega

/--
Correcting an adjacent inverted pair weakly improves the deterministic
best-in-set value. Unlike arbitrary position swaps, this remains true for
proper remaining subsets: if only one of the adjacent candidates remains, their
swap does not change the relative order of remaining candidates.
-/
theorem bestInSet_value_le_adjacent_swapCandidatePositions
    {n : ℕ} (ρ π : Ranking n) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy ρ value)
    (k : Fin (n + 1))
    (hcenter :
      rankOf ρ (π k.succ) < rankOf ρ (π k.castSucc)) :
    value (bestInSet π remaining) ≤
      value
        (bestInSet
          (swapCandidatePositions π (π k.succ) (π k.castSucc))
          remaining) := by
  classical
  let c : Candidate n := π k.succ
  let d : Candidate n := π k.castSucc
  have hpos : rankOf π d < rankOf π c := by
    simp [c, d, rankOf]
  by_cases hc : c ∈ remaining
  · by_cases hd : d ∈ remaining
    · exact bestInSet_value_le_swapCandidatePositions
        ρ π hvalue (by simpa [c, d] using hcenter) hc hd hpos
    · let b : Candidate n := bestInSet π remaining
      have hb_mem : b ∈ remaining := bestInSet_mem π hremaining
      by_cases hbc : b = c
      · have hbest_swap :
            bestInSet
                (swapCandidatePositions π c d) remaining = c := by
          refine bestInSet_eq_of_forall_rank_le
            (swapCandidatePositions π c d) remaining hc ?_
          intro e he
          by_cases hec : e = c
          · simp [hec]
          · have hed : e ≠ d := by
              intro hed
              exact hd (by simpa [hed] using he)
            rw [rankOf_swapCandidatePositions_left]
            rw [rankOf_swapCandidatePositions_of_ne π hec hed]
            have hc_le_e : rankOf π c ≤ rankOf π e := by
              simpa [b, hbc] using
                rankOf_bestInSet_le π hremaining he
            exact le_trans (le_of_lt hpos) hc_le_e
        simpa [c, d, hbest_swap, b, hbc]
      · have hb_ne_d : b ≠ d := by
          intro hbd
          exact hd (by simpa [b, hbd] using hb_mem)
        have hbest_swap :
            bestInSet
                (swapCandidatePositions π c d) remaining = b := by
          refine bestInSet_eq_of_forall_rank_le
            (swapCandidatePositions π c d) remaining hb_mem ?_
          intro e he
          have hb_rank_swap :
              rankOf (swapCandidatePositions π c d) b = rankOf π b :=
            rankOf_swapCandidatePositions_of_ne π hbc hb_ne_d
          by_cases hec : e = c
          · rw [hb_rank_swap, hec, rankOf_swapCandidatePositions_left]
            have hb_le_c : rankOf π b ≤ rankOf π c := by
              simpa [b] using rankOf_bestInSet_le π hremaining hc
            have hb_ne_c_rank : rankOf π b ≠ rankOf π c := by
              intro hr
              exact hbc (by simpa [rankOf] using congrArg π hr)
            simpa [d, rankOf] using
              le_castSucc_of_le_succ_of_ne
                (k := k) (x := rankOf π b)
                (by simpa [c, rankOf] using hb_le_c)
                (by simpa [c, rankOf] using hb_ne_c_rank)
          · have hed : e ≠ d := by
              intro hed
              exact hd (by simpa [hed] using he)
            rw [hb_rank_swap,
              rankOf_swapCandidatePositions_of_ne π hec hed]
            exact rankOf_bestInSet_le π hremaining he
        simpa [b, c, d, hbest_swap]
  · by_cases hd : d ∈ remaining
    · let b : Candidate n := bestInSet π remaining
      have hb_mem : b ∈ remaining := bestInSet_mem π hremaining
      by_cases hbd : b = d
      · have hbest_swap :
            bestInSet
                (swapCandidatePositions π c d) remaining = d := by
          refine bestInSet_eq_of_forall_rank_le
            (swapCandidatePositions π c d) remaining hd ?_
          intro e he
          by_cases hed : e = d
          · simp [hed]
          · have hec : e ≠ c := by
              intro hec
              exact hc (by simpa [hec] using he)
            rw [rankOf_swapCandidatePositions_right]
            rw [rankOf_swapCandidatePositions_of_ne π hec hed]
            have hd_le_e : rankOf π d ≤ rankOf π e := by
              simpa [b, hbd] using
                rankOf_bestInSet_le π hremaining he
            have hd_ne_e_rank : rankOf π e ≠ rankOf π d := by
              intro hr
              exact hed (by simpa [rankOf] using congrArg π hr)
            simpa [c, rankOf] using
              succ_le_of_castSucc_le_of_ne
                (k := k) (x := rankOf π e)
                (by simpa [d, rankOf] using hd_le_e)
                (by simpa [d, rankOf] using hd_ne_e_rank)
        simpa [c, d, hbest_swap, b, hbd]
      · have hb_ne_c : b ≠ c := by
          intro hbc
          exact hc (by simpa [b, hbc] using hb_mem)
        have hbest_swap :
            bestInSet
                (swapCandidatePositions π c d) remaining = b := by
          refine bestInSet_eq_of_forall_rank_le
            (swapCandidatePositions π c d) remaining hb_mem ?_
          intro e he
          have hb_rank_swap :
              rankOf (swapCandidatePositions π c d) b = rankOf π b :=
            rankOf_swapCandidatePositions_of_ne π hb_ne_c hbd
          by_cases hec : e = c
          · exact False.elim (hc (by simpa [hec] using he))
          · by_cases hed : e = d
            · rw [hb_rank_swap, hed, rankOf_swapCandidatePositions_right]
              have hb_le_d : rankOf π b ≤ rankOf π d := by
                simpa [b] using rankOf_bestInSet_le π hremaining hd
              exact le_trans hb_le_d (le_of_lt hpos)
            · rw [hb_rank_swap,
                rankOf_swapCandidatePositions_of_ne π hec hed]
              exact rankOf_bestInSet_le π hremaining he
        rw [hbest_swap]
    · let b : Candidate n := bestInSet π remaining
      have hb_mem : b ∈ remaining := bestInSet_mem π hremaining
      have hb_ne_c : b ≠ c := by
        intro hbc
        exact hc (by simpa [b, hbc] using hb_mem)
      have hb_ne_d : b ≠ d := by
        intro hbd
        exact hd (by simpa [b, hbd] using hb_mem)
      have hbest_swap :
          bestInSet
              (swapCandidatePositions π c d) remaining = b := by
        refine bestInSet_eq_of_forall_rank_le
          (swapCandidatePositions π c d) remaining hb_mem ?_
        intro e he
        have hec : e ≠ c := by
          intro hec
          exact hc (by simpa [hec] using he)
        have hed : e ≠ d := by
          intro hed
          exact hd (by simpa [hed] using he)
        rw [rankOf_swapCandidatePositions_of_ne π hb_ne_c hb_ne_d]
        rw [rankOf_swapCandidatePositions_of_ne π hec hed]
        exact rankOf_bestInSet_le π hremaining he
      rw [hbest_swap]

/--
A payoff improves when an adjacent pair of candidates is swapped to correct an
inversion relative to the center ranking.
-/
def AdjacentSwapImproves {n : ℕ}
    (ρ : Ranking n) (F : Ranking n → ℝ) : Prop :=
  ∀ π : Ranking n, ∀ k : Fin (n + 1),
    rankOf ρ (π k.succ) < rankOf ρ (π k.castSucc) →
      F π ≤ F (swapCandidatePositions π (π k.succ) (π k.castSucc))

/-- One adjacent correction step in the weak order induced by a center ranking. -/
def AdjacentCorrection {n : ℕ} (ρ : Ranking n)
    (π σ : Ranking n) : Prop :=
  ∃ k : Fin (n + 1),
    rankOf ρ (π k.succ) < rankOf ρ (π k.castSucc) ∧
      σ = swapCandidatePositions π (π k.succ) (π k.castSucc)

/--
Weak-order reachability generated by adjacent inversion corrections. The
orientation is from a noisier ranking to a weakly corrected ranking.
-/
def WeakBruhatLe {n : ℕ} (ρ : Ranking n)
    (π σ : Ranking n) : Prop :=
  Relation.ReflTransGen (AdjacentCorrection ρ) π σ

theorem AdjacentSwapImproves.le_of_adjacentCorrection
    {n : ℕ} {ρ : Ranking n} {F : Ranking n → ℝ}
    (hF : AdjacentSwapImproves ρ F) {π σ : Ranking n}
    (hstep : AdjacentCorrection ρ π σ) :
    F π ≤ F σ := by
  rcases hstep with ⟨k, hcenter, rfl⟩
  exact hF π k hcenter

theorem AdjacentSwapImproves.le_of_weakBruhatLe
    {n : ℕ} {ρ : Ranking n} {F : Ranking n → ℝ}
    (hF : AdjacentSwapImproves ρ F) {π σ : Ranking n}
    (hpath : WeakBruhatLe ρ π σ) :
    F π ≤ F σ := by
  induction hpath using Relation.ReflTransGen.trans_induction_on with
  | refl => exact le_rfl
  | single hstep => exact hF.le_of_adjacentCorrection hstep
  | trans _ _ hleft hright => exact le_trans hleft hright

/-- The best-in-set payoff is monotone under adjacent inversion corrections. -/
theorem adjacentSwapImproves_bestInSet_value
    {n : ℕ} (ρ : Ranking n) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy ρ value) :
    AdjacentSwapImproves ρ
      (fun π : Ranking n => value (bestInSet π remaining)) := by
  intro π k hcenter
  exact bestInSet_value_le_adjacent_swapCandidatePositions
    ρ π hremaining hvalue k hcenter

/--
For a fixed remaining set, a payoff is monotone under corrections of inverted
center-ordered pairs inside that remaining set.
-/
def SwapImprovesOn {n : ℕ} (remaining : Finset (Candidate n))
    (ρ : Ranking n) (F : Ranking n → ℝ) : Prop :=
  ∀ π : Ranking n, ∀ c d : Candidate n,
    c ∈ remaining → d ∈ remaining →
      rankOf ρ c < rankOf ρ d → rankOf π d < rankOf π c →
        F π ≤ F (swapCandidatePositions π c d)

/-- The deterministic best-in-set payoff is monotone under such corrections. -/
theorem swapImprovesOn_bestInSet_value
    {n : ℕ} (ρ : Ranking n) (remaining : Finset (Candidate n))
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy ρ value) :
    SwapImprovesOn remaining ρ
      (fun π : Ranking n => value (bestInSet π remaining)) := by
  intro π c d hc hd hcenter hpos
  exact bestInSet_value_le_swapCandidatePositions
    ρ π hvalue hcenter hc hd hpos

/--
Prefix cut after deleting a first-choice candidate. If the deleted center rank
lies before the cut, the cut shifts down by one; otherwise it is unchanged.
-/
def deleteFirstChoicePrefixCut {n : ℕ}
    (r : Candidate (n + 1)) (cut : ℕ) : ℕ :=
  if (r : ℕ) < cut then cut - 1 else cut

theorem succAbove_val_lt_deleteFirstChoicePrefixCut_iff
    {n : ℕ} (r : Candidate (n + 1)) (c : Candidate n) (cut : ℕ) :
    ((r.succAbove c : Candidate (n + 1)) : ℕ) < cut ↔
      (c : ℕ) < deleteFirstChoicePrefixCut r cut := by
  unfold deleteFirstChoicePrefixCut
  by_cases hcr : c.castSucc < r
  · have hcr_nat : (c : ℕ) < (r : ℕ) := by exact hcr
    rw [Fin.succAbove_of_castSucc_lt r c hcr]
    by_cases hrcut : (r : ℕ) < cut
    · simp [hrcut]
      omega
    · simp [hrcut]
  · have hrc : r ≤ c.castSucc := le_of_not_gt hcr
    have hrc_nat : (r : ℕ) ≤ (c : ℕ) := by exact hrc
    rw [Fin.succAbove_of_le_castSucc r c hrc]
    by_cases hrcut : (r : ℕ) < cut
    · simp [hrcut]
      omega
    · have hcut_le_r : cut ≤ (r : ℕ) := by omega
      simp [hrcut]
      omega

/--
Cut-form first-hit indicator. This generalizes a fixed top-prefix indicator:
`cut = 0` is the empty prefix and cuts beyond the candidate universe are the
full prefix.
-/
noncomputable def bestInSetPrefixCutIndicator {n : ℕ}
    (remaining : Finset (Candidate n)) (cut : ℕ)
    (τ : Ranking n) : ℝ :=
  if ((bestInSet τ remaining : Candidate n) : ℕ) < cut then 1 else 0

theorem bestInSetPrefixCutIndicator_nonneg {n : ℕ}
    (remaining : Finset (Candidate n)) (cut : ℕ) (τ : Ranking n) :
    0 ≤ bestInSetPrefixCutIndicator remaining cut τ := by
  unfold bestInSetPrefixCutIndicator
  by_cases hcut : ((bestInSet τ remaining : Candidate n) : ℕ) < cut
  · simp [hcut]
  · simp [hcut]

theorem bestInSetPrefixCutIndicator_le_one {n : ℕ}
    (remaining : Finset (Candidate n)) (cut : ℕ) (τ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut τ ≤ 1 := by
  unfold bestInSetPrefixCutIndicator
  by_cases hcut : ((bestInSet τ remaining : Candidate n) : ℕ) < cut
  · simp [hcut]
  · simp [hcut]

theorem bestInSetPrefixCutIndicator_eq_of_adjacent_cut_not_mem
    {n : ℕ} {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {k : Candidate n}
    (hk : k ∉ remaining) (τ : Ranking n) :
    bestInSetPrefixCutIndicator remaining (k : ℕ) τ =
      bestInSetPrefixCutIndicator remaining ((k : ℕ) + 1) τ := by
  classical
  unfold bestInSetPrefixCutIndicator
  have hb_mem : bestInSet τ remaining ∈ remaining :=
    bestInSet_mem τ hremaining
  have hb_ne : bestInSet τ remaining ≠ k := by
    intro h
    exact hk (by simpa [h] using hb_mem)
  have hb_val_ne :
      ((bestInSet τ remaining : Candidate n) : ℕ) ≠ (k : ℕ) := by
    intro hval
    exact hb_ne (Fin.ext hval)
  have hiff :
      ((bestInSet τ remaining : Candidate n) : ℕ) < (k : ℕ) ↔
        ((bestInSet τ remaining : Candidate n) : ℕ) < (k : ℕ) + 1 := by
    omega
  by_cases hcut : ((bestInSet τ remaining : Candidate n) : ℕ) < (k : ℕ)
  · rw [if_pos hcut, if_pos (hiff.mp hcut)]
  · rw [if_neg hcut, if_neg (fun h => hcut (hiff.mpr h))]

/-- Cut-form prefix value in identity-center coordinates. -/
noncomputable def centerPrefixCutValue {n : ℕ} (cut : ℕ)
    (c : Candidate n) : ℝ :=
  if (c : ℕ) < cut then 1 else 0

theorem weaklyOrderedBy_centerPrefixCutValue {n : ℕ} (cut : ℕ) :
    WeaklyOrderedBy (Equiv.refl (Candidate n)) (centerPrefixCutValue cut) := by
  intro c d hcd
  unfold centerPrefixCutValue
  by_cases hd : (d : ℕ) < cut
  · have hc : (c : ℕ) < cut := by
      have hcd_nat : (c : ℕ) < (d : ℕ) := by simpa [rankOf] using hcd
      omega
    simp [hc, hd]
  · by_cases hc : (c : ℕ) < cut
    · simp [hc, hd]
    · simp [hc, hd]

theorem bestInSetPrefixCutIndicator_eq_centerPrefixCutValue
    {n : ℕ} (remaining : Finset (Candidate n)) (cut : ℕ)
    (τ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut τ =
      centerPrefixCutValue cut (bestInSet τ remaining) := by
  rfl

theorem adjacentSwapImproves_bestInSetPrefixCutIndicator
    {n : ℕ} {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) (cut : ℕ) :
    AdjacentSwapImproves (Equiv.refl (Candidate n))
      (bestInSetPrefixCutIndicator remaining cut) := by
  simpa [bestInSetPrefixCutIndicator, centerPrefixCutValue] using
    adjacentSwapImproves_bestInSet_value
      (Equiv.refl (Candidate n)) hremaining
      (weaklyOrderedBy_centerPrefixCutValue cut)

end

end Ranking
end SocialChoice
end AppliedModelingLib
