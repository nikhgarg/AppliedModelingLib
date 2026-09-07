import AppliedModelingLib.SocialChoice.Ranking.Basic
import AppliedModelingLib.SocialChoice.Ranking.Kendall
import AppliedModelingLib.SocialChoice.Ranking.Probability
import AppliedModelingLib.SocialChoice.Ranking.Mallows
import AppliedModelingLib.SocialChoice.Ranking.Payoff
import AppliedModelingLib.SocialChoice.Ranking.MallowsPayoff
import AppliedModelingLib.SocialChoice.Ranking.RankPower
import AppliedModelingLib.SocialChoice.Ranking.Approval
import AppliedModelingLib.SocialChoice.Ranking.MallowsRankFactorization
import AppliedModelingLib.SocialChoice.Ranking.Score
import AppliedModelingLib.SocialChoice.Ranking.Sequential
import AppliedModelingLib.SocialChoice.Ranking.SequentialPayoff
import AppliedModelingLib.SocialChoice.Ranking.MallowsSequential

/-!
# Ranking

Aggregate import for finite ranking primitives.

Includes base ranking operations, Kendall distance, probability-law bridges,
K-approval score/event probabilities, Mallows laws and rank-factorization
algebra, Mallows first-choice payoff denominators, Mallows best-in-set payoff
decompositions, first-choice payoff decompositions, pure score-induced three-candidate ranking maps,
probability-free sequential choice helpers, and expected best-feasible-candidate
payoffs.
-/
