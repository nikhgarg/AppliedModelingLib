import AppliedModelingLib.SocialChoice.Ranking.Basic

/-!
# KR21 Ranking Compatibility Layer

KR21 originally introduced finite ranking primitives in this file. The
paper-independent definitions now live in
`AppliedModelingLib.SocialChoice.Ranking.Basic`; this file preserves the existing
KR21 names for downstream paper proofs.
-/

namespace KR21Monoculture

export AppliedModelingLib.SocialChoice.Ranking
  (Candidate
    Ranking
    firstChoice
    secondChoice
    swapTopTwo
    rankOf
    bestRemainingAfter
    firstChoice_apply_zero
    secondChoice_apply_one
    firstChoice_swapTopTwo
    secondChoice_swapTopTwo
    rankOf_firstChoice
    rankOf_secondChoice
    rankOf_swapTopTwo_firstChoice
    rankOf_swapTopTwo_secondChoice
    rankOf_swapTopTwo_of_ne_first_second
    one_lt_rankOf_of_ne_first_second
    firstChoice_ne_secondChoice
    swapTopTwo_firstChoice_ne
    bestRemainingAfter_of_eq
    bestRemainingAfter_apply_zero
    bestRemainingAfter_apply_eq_zero_right
    bestRemainingAfter_of_ne
    bestRemainingAfter_ne_removed)

end KR21Monoculture
