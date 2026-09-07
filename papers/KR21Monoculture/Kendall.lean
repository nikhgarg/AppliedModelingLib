import KR21Monoculture.FirstChoice
import AppliedModelingLib.SocialChoice.Ranking.Kendall

open scoped BigOperators

namespace KR21Monoculture

export AppliedModelingLib.SocialChoice.Ranking
  (invertedPair
    inversionFinset
    inversionFinsetInvolving
    inversionFinsetNotInvolving
    inversionFinsetInvolvingSecondNotFirst
    kendallTau
    invertedPair_self_false
    inversionFinset_self
    kendallTau_self
    rankOf_ne_zero_of_ne_firstChoice
    zero_lt_rankOf_of_ne_firstChoice
    inversionFinsetInvolving_firstChoice_eq_image_Iio
    inversionFinsetInvolving_firstChoice_card
    inversionFinsetInvolving_card_add_notInvolving_card
    kendallTau_eq_firstChoice_rank_add_notInvolving_card
    rankOf_eq_zero_iff_eq_firstChoice
    rankOf_lt_one_eq_zero
    one_le_of_ne_zero
    candidate_val_add_one_of_lt
    inversionFinsetInvolvingSecondNotFirst_eq_map_Ico
    inversionFinsetInvolvingSecondNotFirst_card
    inversionFinsetInvolving_secondChoice_eq_involvingSecondNotFirst
    inversionFinsetInvolving_secondChoice_card_of_first_zero
    cycleRange_lt_cycleRange_iff_of_ne
    cycleIcc_one_apply_of_ne
    cycleIcc_one_val_of_ne
    cycleIcc_one_lt_cycleIcc_one_iff_of_ne
    invertedPair_refl_trans_cycleIcc_one_iff_of_ne
    inversionFinsetNotInvolving_secondChoice_card_eq_cycleIcc_one
    kendallTau_eq_secondChoice_sub_one_add_cycleIcc_one
    firstChoice_trans
    secondChoice_trans
    rankOf_trans_apply
    rankingRightTransEquiv
    invertedPair_refl_trans_cycleRange_iff_of_ne
    firstChoice_trans_cycleRange_firstChoice
    inversionFinsetNotInvolving_firstChoice_card_eq_cycleRange
    kendallTau_eq_firstChoice_add_cycleRange
    kendallTau_center_trans
    eq_of_forall_not_invertedPair
    exists_invertedPair_of_ne
    apply_ne_apply_of_ne
    rankOf_center_first_lt_second
    StrictlyOrderedBy
    WeaklyOrderedBy)

theorem center_valueGap_pos_of_strictlyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy ρ value) :
    0 < valueGap value ρ := by
  simpa [valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap,
    AppliedModelingLib.SocialChoice.Ranking.topTwoValueGap] using
    AppliedModelingLib.SocialChoice.Ranking.center_topTwoValueGap_pos_of_strictlyOrderedBy
      (ρ := ρ) (value := value) hvalue

theorem center_valueGap_nonneg_of_weaklyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : WeaklyOrderedBy ρ value) :
    0 ≤ valueGap value ρ := by
  simpa [valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap,
    AppliedModelingLib.SocialChoice.Ranking.topTwoValueGap] using
    AppliedModelingLib.SocialChoice.Ranking.center_topTwoValueGap_nonneg_of_weaklyOrderedBy
      (ρ := ρ) (value := value) hvalue

end KR21Monoculture
