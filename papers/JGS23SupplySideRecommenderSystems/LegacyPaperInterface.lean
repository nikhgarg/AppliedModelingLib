import JGS23SupplySideRecommenderSystems.MainTheorems
import JGS23SupplySideRecommenderSystems.Assumptions

/-!
# Human-Facing Paper Interface: Supply-Side Equilibria in Recommender Systems

This compact interface exposes the first source-facing definitions from
Jagadeesan, Garg, and Steinhardt (NeurIPS 2023 full version).  The full paper is
not yet formalized; the closed rows below cover the Section 2 finite model
surface used by later theorem statements.
-/

namespace JGS23SupplySideRecommenderSystems

open scoped Topology
open AppliedModelingLib.Optimization
open MeasureTheory

/--
Section 2 model primitive: the inferred value of content vector `p` for user
vector `u` is the dot product `⟨u,p⟩`.
-/
noncomputable abbrev paper_inferred_user_value {D : ℕ}
    (u p : Content D) : ℝ :=
  score u p

/--
Section 2 quality monotonicity: if content is scaled upward along a
nonnegative direction, every nonnegative user's inferred value weakly
increases.
-/
theorem paper_quality_scale_monotone {D : ℕ} {a b : ℝ}
    {u p : Content D}
    (hu : NonnegativeContent u) (hp : NonnegativeContent p) (hab : a ≤ b) :
    paper_inferred_user_value u (scaleContent a p) ≤
      paper_inferred_user_value u (scaleContent b p) :=
  score_scaleContent_mono_of_nonnegative hu hp hab

/--
Proposition `pure`, tie-perturbation score step: perturbing content by a
positive multiple of a nonzero nonnegative user vector strictly increases that
user's own inferred value.
-/
theorem paper_pure_tie_perturbation_strict_score {D : ℕ} {u p : Content D} {ε : ℝ}
    (hu : NonnegativeContent u) (hzero : NonzeroContent u) (hε : 0 < ε) :
    paper_inferred_user_value u p <
      paper_inferred_user_value u (fun d => p d + ε * u d) :=
  score_perturb_self_strict hu hzero hε

/--
Proposition `pure`, top-tie perturbation step: if producer `j` is one of
multiple tied maximizers for a nonzero user, then perturbing `j`'s content in
that user's direction strictly increases `j`'s tie-breaking share for that
user.
-/
theorem paper_top_tie_share_strictly_increases_after_perturbation {D P : ℕ}
    {u : Content D} {profile : Fin P → Content D} {j : Fin P} {ε : ℝ}
    (hu : NonnegativeContent u) (hzero : NonzeroContent u)
    (hwin : j ∈ winningProducers u profile)
    (hcard : 1 < (winningProducers u profile).card)
    (hε : 0 < ε) :
    tieShare u profile j <
      tieShare u (deviateProfile profile j (fun d => profile j d + ε * u d)) j :=
  tieShare_strictly_increases_for_top_tie_perturb hu hzero hwin hcard hε

/--
Proposition `pure`, top-tie assignment step: if producer `j` is tied for the
top recommendation of a nonzero user, then perturbing `j`'s content in that
user's direction strictly increases the producer's total expected
recommendation mass across all users.
-/
theorem paper_top_tie_perturbation_strictly_increases_users_won {D N P : ℕ}
    {users : Fin N → Content D} {profile : Fin P → Content D}
    {i0 : Fin N} {j : Fin P} {ε : ℝ}
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hwin : j ∈ winningProducers (users i0) profile)
    (hcard : 1 < (winningProducers (users i0) profile).card)
    (hε : 0 < ε) :
    usersWon users profile j <
      usersWon users
        (deviateProfile profile j (fun d => profile j d + ε * users i0 d)) j :=
  usersWon_lt_deviate_perturb_of_top_tie husers_nonneg hzero hwin hcard hε

/--
Proposition `pure`, top-tie discontinuity size: a tied top recommendation
leaves a strictly positive share jump available to the producer.
-/
theorem paper_top_tie_share_jump_positive {D P : ℕ}
    {u : Content D} {profile : Fin P → Content D} {j : Fin P}
    (hwin : j ∈ winningProducers u profile)
    (hcard : 1 < (winningProducers u profile).card) :
    0 < 1 - tieShare u profile j :=
  top_tie_share_jump_pos hwin hcard

/--
Perturbation monotonicity: adding a nonnegative vector to content cannot reduce
any nonnegative user's inferred value.
-/
theorem paper_perturbation_nonnegative_score_mono {D : ℕ} {v u p : Content D} {ε : ℝ}
    (hv : NonnegativeContent v) (hu : NonnegativeContent u) (hε : 0 ≤ ε) :
    paper_inferred_user_value v p ≤
      paper_inferred_user_value v (fun d => p d + ε * u d) :=
  score_perturb_nonnegative_mono hv hu hε

/--
Section 2 personalized recommendation rule: a winning producer maximizes
dot-product score for the user.
-/
noncomputable abbrev paper_winning_producers {D P : ℕ}
    (u : Content D) (profile : Fin P → Content D) : Finset (Fin P) :=
  winningProducers u profile

/--
Equation (1): source profit formula for a pure content profile, with tie shares
computed by uniform random choice among maximizers.
-/
noncomputable abbrev paper_profit_formula {D N P : ℕ}
    (users : Fin N → Content D) (cost : Content D → ℝ)
    (profile : Fin P → Content D) (j : Fin P) : ℝ :=
  pureProfit users cost profile j

/--
Proposition `pure`, top-tie profitable deviation: if the cost increase from a
small perturbation is smaller than the discontinuous recommendation-share jump,
then the perturbation strictly improves producer profit.
-/
theorem paper_top_tie_perturbation_profitable_if_cost_below_share_jump {D N P : ℕ}
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {profile : Fin P → Content D} {i0 : Fin N} {j : Fin P} {ε : ℝ}
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hwin : j ∈ winningProducers (users i0) profile)
    (hε : 0 < ε)
    (hcost :
      cost (fun d => profile j d + ε * users i0 d) - cost (profile j) <
        1 - tieShare (users i0) profile j) :
    paper_profit_formula users cost profile j <
      paper_profit_formula users cost
        (deviateProfile profile j (fun d => profile j d + ε * users i0 d)) j :=
  pureProfit_lt_of_top_tie_perturb_cost_lt_share_jump husers_nonneg hzero hwin hε hcost

/--
Proposition `pure`, cost-reduction algebra: if a deviation preserves assigned
users and strictly lowers cost, it strictly improves producer profit.
-/
theorem paper_pure_profit_improves_if_same_users_and_lower_cost {D N P : ℕ}
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {profile profile' : Fin P → Content D} {j : Fin P}
    (husers : usersWon users profile j = usersWon users profile' j)
    (hcost : cost (profile' j) < cost (profile j)) :
    paper_profit_formula users cost profile j <
      paper_profit_formula users cost profile' j :=
  pureProfit_lt_of_same_usersWon_and_cost_lt husers hcost

/--
Proposition `pure`, discontinuity algebra: if the assignment-mass gain exceeds
the cost increase, it strictly improves producer profit.
-/
theorem paper_pure_profit_improves_if_user_gain_exceeds_cost_increase {D N P : ℕ}
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {profile profile' : Fin P → Content D} {j : Fin P}
    (hgain :
      cost (profile' j) - cost (profile j) <
        usersWon users profile' j - usersWon users profile j) :
    paper_profit_formula users cost profile j <
      paper_profit_formula users cost profile' j :=
  pureProfit_lt_of_userGain_gt_costIncrease hgain

/--
Profit accounting: at a realized pure profile, total producer profit is at
most the total user mass `N` whenever all realized production costs are
nonnegative.
-/
theorem paper_total_pure_profit_le_user_count {D N P : ℕ} [Nonempty (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {profile : Fin P → Content D}
    (hcost_nonneg : ∀ j : Fin P, 0 ≤ cost (profile j)) :
    (∑ j : Fin P, paper_profit_formula users cost profile j) ≤ (N : ℝ) :=
  sum_pureProfit_le_card_of_cost_nonneg hcost_nonneg

/--
Source support-bound accounting: at a realized profile, any individual
producer's profit is at most the total user mass `N` when its realized cost is
nonnegative.
-/
theorem paper_pure_profit_le_user_count_of_cost_nonnegative {D N P : ℕ}
    [Nonempty (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {profile : Fin P → Content D} {j : Fin P}
    (hcost_nonneg : 0 ≤ cost (profile j)) :
    paper_profit_formula users cost profile j ≤ (N : ℝ) :=
  pureProfit_le_card_of_cost_nonneg hcost_nonneg

/--
Source support-bound accounting: if the realized cost of one producer exceeds
the total user mass `N`, then that producer's realized pure-profile profit is
negative.
-/
theorem paper_pure_profit_negative_if_cost_exceeds_user_count {D N P : ℕ}
    [Nonempty (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {profile : Fin P → Content D} {j : Fin P}
    (hcost_gt : (N : ℝ) < cost (profile j)) :
    paper_profit_formula users cost profile j < 0 :=
  pureProfit_lt_zero_of_cost_gt_card hcost_gt

/--
Saturation accounting: if total producer profit is at most the total user mass
and all producers receive the same profit, that common profit is at most
`N / P`.
-/
theorem paper_common_profit_le_user_count_div_producers {N P : ℕ}
    [Nonempty (Fin P)]
    {profit : Fin P → ℝ} {π : ℝ}
    (hsum_le : (∑ j : Fin P, profit j) ≤ (N : ℝ))
    (hcommon : ∀ j : Fin P, profit j = π) :
    π ≤ (N : ℝ) / (P : ℝ) :=
  common_profit_le_card_div_of_sum_le hsum_le hcommon

/--
Symmetric/common-profit accounting: if all producers receive the same realized
pure-profile profit, the common profit is at most `N / P`.
-/
theorem paper_common_pure_profit_le_user_count_div_producers {D N P : ℕ}
    [Nonempty (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {profile : Fin P → Content D} {π : ℝ}
    (hcost_nonneg : ∀ j : Fin P, 0 ≤ cost (profile j))
    (hcommon : ∀ j : Fin P, paper_profit_formula users cost profile j = π) :
    π ≤ (N : ℝ) / (P : ℝ) :=
  common_pureProfit_le_card_div_of_cost_nonneg hcost_nonneg hcommon

/--
Profit accounting for the source norm-power costs: an individual realized
pure-profile producer profit is at most the total user mass `N`.
-/
theorem paper_norm_rpow_pure_profit_le_user_count {D N P : ℕ}
    [Nonempty (Fin P)]
    (ν : SourceNorm D) (β : ℝ)
    {users : Fin N → Content D} {profile : Fin P → Content D} {j : Fin P} :
    paper_profit_formula users (normRpowCost ν β) profile j ≤ (N : ℝ) :=
  pureProfit_le_card_normRpowCost ν β

/--
Profit accounting for the source norm-power costs: total realized pure-profile
producer profit is at most the total user mass `N`.
-/
theorem paper_total_norm_rpow_pure_profit_le_user_count {D N P : ℕ}
    [Nonempty (Fin P)]
    (ν : SourceNorm D) (β : ℝ)
    {users : Fin N → Content D} {profile : Fin P → Content D} :
    (∑ j : Fin P, paper_profit_formula users (normRpowCost ν β) profile j) ≤
      (N : ℝ) :=
  sum_pureProfit_normRpowCost_le_card ν β

/--
Saturation accounting for the source norm-power costs: if all producers have
the same realized pure-profile profit, that common profit is at most `N / P`.
-/
theorem paper_common_norm_rpow_pure_profit_le_user_count_div_producers
    {D N P : ℕ} [Nonempty (Fin P)]
    (ν : SourceNorm D) (β : ℝ)
    {users : Fin N → Content D} {profile : Fin P → Content D} {π : ℝ}
    (hcommon : ∀ j : Fin P,
      paper_profit_formula users (normRpowCost ν β) profile j = π) :
    π ≤ (N : ℝ) / (P : ℝ) :=
  common_pureProfit_normRpowCost_le_card_div ν β hcommon

/--
Section 2 pure-strategy Nash equilibrium predicate: no producer can improve by
unilaterally deviating to another nonnegative content vector.
-/
abbrev paper_pure_nash_equilibrium {D N P : ℕ}
    (users : Fin N → Content D) (cost : Content D → ℝ)
    (profile : Fin P → Content D) : Prop :=
  PureNashEquilibrium users cost profile

/--
Pure-deviation principle: any nonnegative unilateral deviation that strictly
improves the deviating producer's profit rules out a pure Nash equilibrium.
-/
theorem paper_not_pure_nash_of_profitable_deviation {D N P : ℕ}
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {profile : Fin P → Content D} {j : Fin P} {p : Content D}
    (hp : NonnegativeContent p)
    (hprofit :
      pureProfit users cost profile j <
        pureProfit users cost (deviateProfile profile j p) j) :
    ¬ paper_pure_nash_equilibrium users cost profile :=
  not_pureNash_of_profitable_deviation hp hprofit

/--
Proposition `pure`, top-tie Nash contradiction: a source-small perturbation
whose cost increase is below the discontinuous share jump rules out a pure
Nash equilibrium.
-/
theorem paper_not_pure_nash_of_top_tie_cost_below_share_jump {D N P : ℕ}
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {profile : Fin P → Content D} {i0 : Fin N} {j : Fin P} {ε : ℝ}
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hprofile_nonneg : ∀ k : Fin P, NonnegativeContent (profile k))
    (hzero : NonzeroContent (users i0))
    (hwin : j ∈ winningProducers (users i0) profile)
    (hε : 0 < ε)
    (hcost :
      cost (fun d => profile j d + ε * users i0 d) - cost (profile j) <
        1 - tieShare (users i0) profile j) :
    ¬ paper_pure_nash_equilibrium users cost profile :=
  not_pureNash_of_top_tie_perturb_cost_lt_share_jump husers_nonneg
    hprofile_nonneg hzero hwin hε hcost

/--
Source cost-continuity condition used in the top-tie half of Proposition
`pure`: perturbing a content vector by a small positive multiple of a user
vector changes cost continuously from the right.
-/
abbrev paper_perturbation_cost_continuous {D : ℕ}
    (cost : Content D → ℝ) : Prop :=
  PerturbationCostContinuous cost

/--
Proposition `pure`: for a finite nonnegative user population containing at
least one nonzero user and at least two producers, any profile is not a pure
Nash equilibrium when production costs strictly decrease under radial
scale-downs and are right-continuous under the source top-tie perturbations.
-/
theorem paper_not_pure_nash_radial_cost_and_perturbation_continuity {D N P : ℕ}
    [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {profile : Fin P → Content D}
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hexists_nonzero : ∃ i : Fin N, NonzeroContent (users i))
    (hcost_radial : RadialStrictCost cost)
    (hcost_cont : paper_perturbation_cost_continuous cost) :
    ¬ paper_pure_nash_equilibrium users cost profile :=
  not_pureNash_of_exists_nonzeroUser_of_radialStrictCost_and_perturbationCostContinuous
    husers_nonneg hexists_nonzero hcost_radial hcost_cont

/--
Proposition `pure`, finite-margin no-tie step: when all original scores are
untied, there exists a scale factor strictly below one that preserves every
user originally won by the producer.
-/
theorem paper_exists_scale_down_preserving_winners_under_no_ties {D N P : ℕ}
    [Nontrivial (Fin P)]
    {users : Fin N → Content D} {profile : Fin P → Content D} {j : Fin P}
    (hno : NoScoreTies users profile)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hprofile_nonneg : ∀ k : Fin P, NonnegativeContent (profile k)) :
    ∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧
      ∀ i : Fin N, j ∈ winningProducers (users i) profile →
        StrictWinner (users i)
          (deviateProfile profile j (scaleContent a (profile j))) j :=
  exists_scale_down_preserving_winners_of_noScoreTies hno husers_nonneg
    hprofile_nonneg

/--
Proposition `pure`, no-tie case: under the source radial cost property of
`||p||^β`, every no-tie pure profile has a profitable scale-down deviation, so
it cannot be a pure Nash equilibrium.
-/
theorem paper_not_pure_nash_no_ties_radial_cost {D N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {profile : Fin P → Content D}
    (hno : NoScoreTies users profile)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hcost : RadialStrictCost cost) :
    ¬ paper_pure_nash_equilibrium users cost profile :=
  not_pureNash_noScoreTies_of_radialStrictCost hno husers_nonneg hcost

/--
Proposition `pure`, stronger no-top-tie case: the scale-down contradiction only
requires every user's winning producer to be unique; equal lower scores among
non-winners are irrelevant.
-/
theorem paper_not_pure_nash_unique_top_winners_radial_cost {D N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {profile : Fin P → Content D}
    (huniq : UniqueWinningProducers users profile)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hcost : RadialStrictCost cost) :
    ¬ paper_pure_nash_equilibrium users cost profile :=
  not_pureNash_uniqueWinners_of_radialStrictCost huniq husers_nonneg hcost

/--
Source cost family: if `ν` is a norm-like production magnitude and `β` is a
positive integer exponent, then `c(p)=ν(p)^β` is radially strictly lowered by
scaling any nonzero content vector down.
-/
theorem paper_norm_power_cost_radial_strict {D : ℕ}
    (ν : SourceNorm D) {β : ℕ} (hβ : 0 < β) :
    RadialStrictCost (normPowerCost ν β) :=
  radialStrictCost_normPowerCost ν hβ

/--
Source cost-continuity instance for integer-exponent norm-power costs: if the
underlying norm is right-continuous along the paper's perturbation rays, then
`c(p)=ν(p)^β` satisfies the perturbation-continuity condition used in
Proposition `pure`.
-/
theorem paper_norm_power_cost_perturbation_continuous {D : ℕ}
    (ν : SourceNorm D) {β : ℕ}
    (hcont : SourceNormPerturbationContinuous ν) :
    paper_perturbation_cost_continuous (normPowerCost ν β) :=
  perturbationCostContinuous_normPowerCost ν hcont

/--
Source real-exponent cost family: `c(p)=ν(p)^β`, matching the paper's
`||p||^β` notation.
-/
noncomputable abbrev paper_norm_rpow_cost {D : ℕ}
    (ν : SourceNorm D) (β : ℝ) (p : Content D) : ℝ :=
  normRpowCost ν β p

/--
Check of the source-model's excluded all-zero population: the all-zero content
profile is a pure Nash equilibrium under every positive norm-power cost.  The
source-facing nonexistence theorem therefore makes the active-user convention
visible.
-/
theorem paper_counterexample_pure_all_zero_users
    {D N P : ℕ} [Nonempty (Fin P)]
    (ν : SourceNorm D) {β : ℝ} (hβ : 0 < β) :
    paper_pure_nash_equilibrium (fun _ : Fin N => (0 : Content D))
      (paper_norm_rpow_cost ν β) (fun _ : Fin P => (0 : Content D)) :=
  zeroUsers_zeroProfile_is_pureNash_normRpowCost ν hβ

/--
Proposition `pure` cost fact for real exponents: if `β > 0`, then
`c(p)=ν(p)^β` strictly decreases under radial scale-down of nonzero content.
-/
theorem paper_norm_rpow_cost_radial_strict {D : ℕ}
    (ν : SourceNorm D) {β : ℝ} (hβ : 0 < β) :
    RadialStrictCost (normRpowCost ν β) :=
  radialStrictCost_normRpowCost ν hβ

/--
Proposition `pure` cost fact for real exponents: if the underlying norm is
right-continuous along perturbation rays and `β >= 0`, then
`c(p)=ν(p)^β` has the perturbation-continuity property used in the top-tie
branch.
-/
theorem paper_norm_rpow_cost_perturbation_continuous {D : ℕ}
    (ν : SourceNorm D) {β : ℝ} (hβ : 0 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν) :
    paper_perturbation_cost_continuous (normRpowCost ν β) :=
  perturbationCostContinuous_normRpowCost ν hβ hcont

/-- Compact sublevel premise required by the truncated action space in Proposition `existence`. -/
abbrev paper_source_norm_compact_sublevels {D : ℕ} (ν : SourceNorm D) : Prop :=
  SourceNormCompactSublevels ν

/-- Convex sublevel premise required by the truncated action space in Proposition `existence`. -/
abbrev paper_source_norm_convex_sublevels {D : ℕ} (ν : SourceNorm D) : Prop :=
  SourceNormConvexSublevels ν

/-- The nonnegative, radius-truncated action space used in the existence proof. -/
abbrev paper_truncated_content_action_set {D : ℕ}
    (ν : SourceNorm D) (R : ℝ) : Set (Content D) :=
  sourceTruncatedActionSet ν R

/-- Proposition `existence` action-space compactness under explicit properness. -/
theorem paper_truncated_content_action_set_isCompact {D : ℕ}
    (ν : SourceNorm D) (R : ℝ)
    (hcompact : paper_source_norm_compact_sublevels ν) :
    IsCompact (paper_truncated_content_action_set ν R) :=
  isCompact_sourceTruncatedActionSet_of_compactSublevels ν R hcompact

/-- Proposition `existence` action-space convexity under explicit norm-ball convexity. -/
theorem paper_truncated_content_action_set_convex {D : ℕ}
    (ν : SourceNorm D) (R : ℝ)
    (hconvex : paper_source_norm_convex_sublevels ν) :
    Convex ℝ (paper_truncated_content_action_set ν R) :=
  convex_sourceTruncatedActionSet_of_convexSublevels ν R hconvex

/-- The finite-coordinate Euclidean source norm discharges both action-space premises. -/
theorem paper_l2_truncated_content_action_set_isCompact_and_convex
    (D : ℕ) (R : ℝ) :
    IsCompact (paper_truncated_content_action_set (SourceNorm.l2 D) R) ∧
      Convex ℝ (paper_truncated_content_action_set (SourceNorm.l2 D) R) :=
  ⟨paper_truncated_content_action_set_isCompact (SourceNorm.l2 D) R
      (SourceNorm.l2_compactSublevels D),
    paper_truncated_content_action_set_convex (SourceNorm.l2 D) R
      (SourceNorm.l2_convexSublevels D)⟩

/-- Positive finite `Lq` source norms at `q >= 1` discharge both action-space premises. -/
theorem paper_lp_truncated_content_action_set_isCompact_and_convex
    {D : ℕ} {q : ℝ} (hq : 1 ≤ q) (R : ℝ) :
    IsCompact (paper_truncated_content_action_set
      (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) R) ∧
      Convex ℝ (paper_truncated_content_action_set
        (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) R) :=
  ⟨paper_truncated_content_action_set_isCompact
      (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) R
      (SourceNorm.lp_compactSublevels (lt_of_lt_of_le zero_lt_one hq)),
    paper_truncated_content_action_set_convex
      (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) R
      (SourceNorm.lp_convexSublevels hq)⟩

/--
Proposition `existence` support-cap step: for `c(p)=ν(p)^β`, any content with
`ν(p) > N^(1/β)` has production cost greater than the maximum possible user
mass.
-/
theorem paper_norm_rpow_cost_exceeds_user_count_above_support_cap {D N : ℕ}
    [Nonempty (Fin N)]
    (ν : SourceNorm D) {β : ℝ} {p : Content D}
    (hβ : 0 < β) (hcap : (N : ℝ) ^ β⁻¹ < ν.norm p) :
    (N : ℝ) < paper_norm_rpow_cost ν β p :=
  normRpowCost_gt_card_of_support_cap_lt_norm ν hβ hcap

/--
Proposition `existence` support-cap step: actions outside the radius
`N^(1/β)` have negative realized pure-profile profit under the source
norm-power cost.
-/
theorem paper_pure_profit_negative_above_support_cap_norm_rpow_cost {D N P : ℕ}
    [Nonempty (Fin N)] [Nonempty (Fin P)]
    (ν : SourceNorm D) {β : ℝ}
    {users : Fin N → Content D} {profile : Fin P → Content D} {j : Fin P}
    (hβ : 0 < β) (hcap : (N : ℝ) ^ β⁻¹ < ν.norm (profile j)) :
    paper_profit_formula users (paper_norm_rpow_cost ν β) profile j < 0 :=
  pureProfit_lt_zero_of_support_cap_lt_normRpowCost ν hβ hcap

/--
Proposition `existence` support-cap contrapositive: any source norm-power
action with nonnegative realized profit lies within the radius `N^(1/β)`.
-/
theorem paper_norm_bounded_by_support_cap_of_nonnegative_profit {D N P : ℕ}
    [Nonempty (Fin N)] [Nonempty (Fin P)]
    (ν : SourceNorm D) {β : ℝ}
    {users : Fin N → Content D} {profile : Fin P → Content D} {j : Fin P}
    (hβ : 0 < β)
    (hprofit : 0 ≤ paper_profit_formula users (paper_norm_rpow_cost ν β) profile j) :
    ν.norm (profile j) ≤ (N : ℝ) ^ β⁻¹ :=
  norm_le_support_cap_of_nonnegative_pureProfit_normRpowCost ν hβ hprofit

/--
Proposition `existence` outside-option step: deviating to zero content has
nonnegative realized profit under the source norm-power cost.
-/
theorem paper_zero_content_deviation_has_nonnegative_profit_norm_rpow_cost {D N P : ℕ}
    (ν : SourceNorm D) {β : ℝ}
    {users : Fin N → Content D} {profile : Fin P → Content D} {j : Fin P}
    (hβ : 0 < β) :
    0 ≤ paper_profit_formula users (paper_norm_rpow_cost ν β)
      (deviateProfile profile j (0 : Content D)) j :=
  pureProfit_zero_deviation_nonneg_normRpowCost ν hβ

/--
Proposition `existence` support-cap step: in a pure Nash profile under the
source norm-power cost, every realized content vector lies within the
source radius `N^(1/β)`.
-/
theorem paper_pure_nash_actions_within_support_cap_norm_rpow_cost {D N P : ℕ}
    [Nonempty (Fin N)] [Nonempty (Fin P)]
    (ν : SourceNorm D) {β : ℝ}
    {users : Fin N → Content D} {profile : Fin P → Content D} {j : Fin P}
    (hβ : 0 < β)
    (hne : paper_pure_nash_equilibrium users (paper_norm_rpow_cost ν β) profile) :
    ν.norm (profile j) ≤ (N : ℝ) ^ β⁻¹ :=
  pureNash_norm_le_support_cap_normRpowCost ν hβ hne

/--
Proposition `existence` support-slack step: the source's compact action space
uses radius `2 N^(1/β)`, and any equilibrium-relevant norm-power action lies
strictly inside that slack radius.
-/
theorem paper_pure_nash_actions_inside_double_support_cap_norm_rpow_cost
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)]
    (ν : SourceNorm D) {β : ℝ}
    {users : Fin N → Content D} {profile : Fin P → Content D} {j : Fin P}
    (hβ : 0 < β)
    (hne : paper_pure_nash_equilibrium users (paper_norm_rpow_cost ν β) profile) :
    ν.norm (profile j) < 2 * ((N : ℝ) ^ β⁻¹) :=
  pureNash_norm_lt_double_support_cap_normRpowCost ν hβ hne

/--
Proposition `existence` compact-action step for the Euclidean source cost:
in a pure Nash profile, each nonnegative coordinate of every producer action
lies in the box `[0, N^(1/β)]`.
-/
theorem paper_pure_nash_l2_actions_within_support_box {D N P : ℕ}
    [Nonempty (Fin N)] [Nonempty (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {profile : Fin P → Content D}
    (hβ : 0 < β)
    (hne : paper_pure_nash_equilibrium users
      (paper_norm_rpow_cost (SourceNorm.l2 D) β) profile)
    (j : Fin P) (d : Fin D) :
    0 ≤ profile j d ∧ profile j d ≤ (N : ℝ) ^ β⁻¹ :=
  pureNash_l2_coord_mem_support_box_normRpowCost hβ hne j d

/--
Proposition `existence` compact-action step for finite `Lq` source costs:
in a pure Nash profile, each nonnegative coordinate of every producer action
lies in the box `[0, N^(1/β)]`.
-/
theorem paper_pure_nash_lp_actions_within_support_box {D N P : ℕ}
    [Nonempty (Fin N)] [Nonempty (Fin P)]
    {q β : ℝ} {users : Fin N → Content D} {profile : Fin P → Content D}
    (hq : 0 < q) (hβ : 0 < β)
    (hne : paper_pure_nash_equilibrium users
      (paper_norm_rpow_cost (SourceNorm.lp D hq) β) profile)
    (j : Fin P) (d : Fin D) :
    0 ≤ profile j d ∧ profile j d ≤ (N : ℝ) ^ β⁻¹ :=
  pureNash_lp_coord_mem_support_box_normRpowCost hq hβ hne j d

/--
Proposition `pure`, source cost version: for `c(p)=ν(p)^β` with `β > 0`, a
norm continuous along the paper's perturbation rays, and at least one nonzero
user, finite pure-strategy Nash equilibria do not exist.
-/
theorem paper_not_pure_nash_norm_rpow_cost {D N P : ℕ}
    [Nontrivial (Fin P)]
    {users : Fin N → Content D} {profile : Fin P → Content D}
    (ν : SourceNorm D) {β : ℝ} (hβ : 0 < β)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hexists_nonzero : ∃ i : Fin N, NonzeroContent (users i))
    (hcont : SourceNormPerturbationContinuous ν) :
    ¬ paper_pure_nash_equilibrium users (normRpowCost ν β) profile :=
  not_pureNash_normRpowCost_of_exists_nonzeroUser ν hβ husers_nonneg
    hexists_nonzero hcont

/--
Proposition `pure`, source exponent form: for `c(p)=ν(p)^β` with `β >= 1`
and a norm continuous along the paper's perturbation rays, finite pure-strategy
Nash equilibria do not exist.
-/
theorem paper_not_pure_nash_norm_rpow_cost_of_one_le {D N P : ℕ}
    [Nontrivial (Fin P)]
    {users : Fin N → Content D} {profile : Fin P → Content D}
    (ν : SourceNorm D) {β : ℝ} (hβ : 1 ≤ β)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hexists_nonzero : ∃ i : Fin N, NonzeroContent (users i))
    (hcont : SourceNormPerturbationContinuous ν) :
    ¬ paper_pure_nash_equilibrium users (normRpowCost ν β) profile :=
  not_pureNash_normRpowCost_of_exists_nonzeroUser_of_one_le ν hβ
    husers_nonneg hexists_nonzero hcont

/-- Source finite `Lq` norm `||p||_q` on finite-coordinate content vectors. -/
noncomputable abbrev paper_lp_source_norm (D : ℕ) {q : ℝ} (hq : 0 < q) :
    SourceNorm D :=
  SourceNorm.lp D hq

/--
Proposition `pure`, finite `Lq` source-cost version: for
`c(p)=||p||_q^β` with `q > 0` and `β > 0`, finite pure-strategy Nash
equilibria do not exist.
-/
theorem paper_not_pure_nash_lp_rpow_cost {D N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {profile : Fin P → Content D}
    {q β : ℝ} (hq : 0 < q) (hβ : 0 < β)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i)) :
    ¬ paper_pure_nash_equilibrium users
      (normRpowCost (paper_lp_source_norm D hq) β) profile :=
  not_pureNash_lpRpowCost hq hβ husers_nonneg husers_nonzero

/--
Proposition `pure`, finite `Lq` source-cost version with the paper's printed
condition `β >= 1`.
-/
theorem paper_not_pure_nash_lp_rpow_cost_of_one_le {D N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {profile : Fin P → Content D}
    {q β : ℝ} (hq : 0 < q) (hβ : 1 ≤ β)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i)) :
    ¬ paper_pure_nash_equilibrium users
      (normRpowCost (paper_lp_source_norm D hq) β) profile :=
  not_pureNash_lpRpowCost_of_one_le hq hβ husers_nonneg husers_nonzero

/-- Source Euclidean norm `||p||_2` on finite-coordinate content vectors. -/
noncomputable abbrev paper_l2_source_norm (D : ℕ) : SourceNorm D :=
  SourceNorm.l2 D

/--
Proposition `pure`, Euclidean source-cost version: for
`c(p)=||p||_2^β` with `β > 0`, finite pure-strategy Nash equilibria do not
exist. The paper assumes `β >= 1`, which implies this exponent condition.
-/
theorem paper_not_pure_nash_l2_rpow_cost {D N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {profile : Fin P → Content D}
    {β : ℝ} (hβ : 0 < β)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i)) :
    ¬ paper_pure_nash_equilibrium users
      (normRpowCost (paper_l2_source_norm D) β) profile :=
  not_pureNash_l2RpowCost hβ husers_nonneg husers_nonzero

/--
Proposition `pure`, Euclidean source-cost version with the paper's printed
condition `β >= 1`.
-/
theorem paper_not_pure_nash_l2_rpow_cost_of_one_le {D N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {profile : Fin P → Content D}
    {β : ℝ} (hβ : 1 ≤ β)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i)) :
    ¬ paper_pure_nash_equilibrium users
      (normRpowCost (paper_l2_source_norm D) β) profile :=
  not_pureNash_l2RpowCost_of_one_le hβ husers_nonneg husers_nonzero

/--
Lemma `regionscolor`, abstract Hessian sign condition: if the graph Hessian
difference from the two-user proof is negative semidefinite, then the graph
slope times the cross-partial has nonpositive sign.
-/
abbrev paper_negative_semidefinite_quadratic2 (a11 a12 a22 : ℝ) : Prop :=
  NegativeSemidefiniteQuadratic2 a11 a12 a22

theorem paper_regionscolor_hessian_cross_sign
    {slope cross : ℝ}
    (hneg :
      paper_negative_semidefinite_quadratic2
        (slope * cross) (-cross) (slope⁻¹ * cross)) :
    slope * cross ≤ 0 :=
  graphHessian_cross_sign_of_negativeSemidefinite hneg

/--
Lemma `regionscolor`, algebraic second-order bridge: the differentiated FOC
identities of a support graph turn the objective SOC into the graph-Hessian
form. The local graph and differentiability hypotheses remain explicit.
-/
theorem paper_regionscolor_graph_hessian_of_objective_soc_and_graph_foc_derivatives
    {a11 a12 a22 slope h1prime h2prime : ℝ}
    (hsoc :
      paper_negative_semidefinite_quadratic2
        (h1prime - a11) (-a12) (h2prime - a22))
    (hfirst : h1prime = a11 + slope * a12)
    (hsecond : h2prime = a22 + slope⁻¹ * a12) :
    paper_negative_semidefinite_quadratic2
      (slope * a12) (-a12) (slope⁻¹ * a12) :=
  graphHessian_negativeSemidefinite_of_objectiveSOC_and_graphFOCDerivatives
    hsoc hfirst hsecond

/--
Lemma `inducedcost`, canonical two-user quadratic: in rotated coordinates
`u_1=e_1`, `u_2=(cos θ, sin θ)`, the content vector realizing values
`(z_1,z_2)` has Euclidean norm squared equal to the source quadratic divided
by `sin^2 θ`.
-/
noncomputable abbrev paper_two_user_induced_cost_quadratic
    (θ z1 z2 : ℝ) : ℝ :=
  twoUserInducedCostQuadratic θ z1 z2

noncomputable abbrev paper_two_user_induced_cost
    (α β θ z1 z2 : ℝ) : ℝ :=
  twoUserInducedCost α β θ z1 z2

/--
The induced two-user cost is strictly positive away from the value-space origin
under positive source parameters and a nonsingular canonical angle.
-/
theorem paper_two_user_induced_cost_pos_of_pair_ne_zero
    {α β θ z1 z2 : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hpair : z1 ≠ 0 ∨ z2 ≠ 0) :
    0 < paper_two_user_induced_cost α β θ z1 z2 :=
  twoUserInducedCost_pos_of_pair_ne_zero hα hβ hsin hpair

/--
Proposition `uniqueness`, C1 endpoint bridge.  A value-support point with both
marginal rewards zero must be the origin if the feasible zero action also has
zero reward and cost.  Establishing the CDF-zero endpoint from the source
hypotheses remains a separate obligation.
-/
theorem paper_two_user_zero_endpoint_of_C1_zero_marginal_rewards
    {H1 H2 : ℝ → ℝ} {α β θ z1 z2 : ℝ} {feasible : Set (ℝ × ℝ)}
    (hmax : IsMaxOn
      (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
        paper_two_user_induced_cost α β θ z.1 z.2) feasible (z1, z2))
    (hzero_feasible : (0, 0) ∈ feasible)
    (hzero_cost : paper_two_user_induced_cost α β θ 0 0 = 0)
    (hzero_rewards : H1 0 = 0 ∧ H2 0 = 0)
    (hz_rewards : H1 z1 = 0 ∧ H2 z2 = 0)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ) :
    z1 = 0 ∧ z2 = 0 :=
  canonicalTwoUser_eq_zero_of_isMaxOn_of_zero_marginal_rewards
    hmax hzero_feasible hzero_cost hzero_rewards hz_rewards hα hβ hsin

/--
Proposition `uniqueness`, compact C1/C2 lower-endpoint bridge.  When the
canonical value law has compact strictly ordered graph support, its represented
coordinatewise minimum has zero atomless iid-max rewards.  C1 then identifies
that endpoint with the feasible origin.  Strict graph order, compactness, C1,
and score-law absolute continuity are deliberately displayed: the source's
stated a.e. regularity does not by itself establish the pointwise graph regime.
-/
theorem paper_two_user_zero_value_support_of_compact_strict_ordered_iid_C1
    {P : ℕ} {θ : ℝ} {μ : Measure (Content 2)} [IsProbabilityMeasure μ]
    {α β : ℝ}
    (hP : 1 < P)
    (hcompact : IsCompact (Measure.map (canonicalTwoUserValueMap θ) μ).support)
    (hinj : (Measure.map (canonicalTwoUserValueMap θ) μ).support.InjOn Prod.fst)
    (hstrict : ∀ p ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      ∀ q ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
        p.1 < q.1 → p.2 < q.2)
    (hmax : ∀ z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      IsMaxOn
        (fun w : ℝ × ℝ =>
          AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1)
              (Measure.map (fun q : Content 2 => score canonicalTwoUserFirst q) μ) w.1 +
            AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1)
              (Measure.map (fun q : Content 2 =>
                score (canonicalTwoUserSecond θ) q) μ) w.2 -
              paper_two_user_induced_cost α β θ w.1 w.2)
        (canonicalTwoUserFeasibleValueSet θ) z)
    (hscore_ac : ∀ i : Fin 2,
      Measure.map
        (fun q : Content 2 =>
          score (if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ) q) μ ≪
        volume)
    (hfeasible : ∀ z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      z ∈ canonicalTwoUserFeasibleValueSet θ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsin : 0 < Real.sin θ) (hcos : 0 ≤ Real.cos θ) :
    (0, 0) ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support :=
  canonicalTwoUser_zero_mem_valueSupport_of_compact_strict_ordered_iidC1
    hP hcompact hinj hstrict hmax hscore_ac hfeasible hα hβ hsin hcos

theorem paper_two_user_canonical_norm_sq_eq_induced_cost_quadratic
    {θ z1 z2 : ℝ} (hsin : Real.sin θ ≠ 0) :
    z1 ^ 2 + ((z2 - z1 * Real.cos θ) / Real.sin θ) ^ 2 =
      paper_two_user_induced_cost_quadratic θ z1 z2 :=
  twoUserCanonicalNormSq_eq_inducedCostQuadratic hsin

/--
Lemma `inducedcost`, cone-safe dimension-two form: for any linearly
independent unit user pair in ambient dimension two, the Gram induced-cost
quadratic of a content action is exactly its squared Euclidean norm.  Unlike
the source's informal rotation, this statement does not change the
nonnegative action cone.
-/
theorem paper_two_user_induced_cost_quadratic_eq_score_self_dim_two
    {u v p : Content 2} {θ : ℝ}
    (hu : score u u = 1) (hv : score v v = 1)
    (huv : score u v = Real.cos θ) (hsin : Real.sin θ ≠ 0) :
    paper_two_user_induced_cost_quadratic θ (score u p) (score v p) = score p p :=
  twoUserInducedCostQuadratic_eq_score_self_of_unit_score_pair_dim_two hu hv huv hsin

/--
The corresponding dimension-two source cost is exactly the L2 power cost at
every content action.  The conclusion is deliberately restricted to ambient
dimension two; in larger dimension the source quadratic is only a lower
bound, not an equality.
-/
theorem paper_two_user_induced_cost_eq_l2_rpow_dim_two
    {u v p : Content 2} {β θ : ℝ}
    (hu : score u u = 1) (hv : score v v = 1)
    (huv : score u v = Real.cos θ) (hsin : 0 < Real.sin θ) :
    paper_two_user_induced_cost 1 β θ (score u p) (score v p) =
      AppliedModelingLib.FiniteDimensionalNorms.l2 p ^ β :=
  twoUserInducedCost_eq_l2_rpow_of_unit_score_pair_dim_two hu hv huv hsin

/--
Lemma `FOC`, first partial derivative of the canonical two-user induced-cost
formula with respect to the first realized value coordinate.
-/
theorem paper_hasDerivAt_two_user_induced_cost_z1
    {α β θ z1 z2 : ℝ}
    (hbase : twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2) :
    HasDerivAt (fun x : ℝ => paper_two_user_induced_cost α β θ x z2)
      (β * α * (Real.sin θ) ^ (-β) *
        (twoUserInducedCostNumerator θ z1 z2) ^ (β / 2 - 1) *
          (z1 - z2 * Real.cos θ)) z1 :=
  hasDerivAt_twoUserInducedCost_z1 hbase

/--
Lemma `FOC`, first partial derivative of the canonical two-user induced-cost
formula with respect to the second realized value coordinate.
-/
theorem paper_hasDerivAt_two_user_induced_cost_z2
    {α β θ z1 z2 : ℝ}
    (hbase : twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2) :
    HasDerivAt (fun y : ℝ => paper_two_user_induced_cost α β θ z1 y)
      (β * α * (Real.sin θ) ^ (-β) *
        (twoUserInducedCostNumerator θ z1 z2) ^ (β / 2 - 1) *
          (z2 - z1 * Real.cos θ)) z2 :=
  hasDerivAt_twoUserInducedCost_z2 hbase

/--
Lemma `secondderiv`, canonical cross-partial formula: differentiating the
first-order expression with respect to the second realized-value coordinate
gives the source bracket that later determines the sign of the support curve.
-/
noncomputable abbrev paper_two_user_induced_cost_cross_partial
    (α β θ z1 z2 : ℝ) : ℝ :=
  twoUserInducedCostCrossPartial α β θ z1 z2

theorem paper_hasDerivAt_two_user_induced_cost_cross_partial
    {α β θ z1 z2 : ℝ}
    (hbase : twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1) :
    HasDerivAt
      (fun y : ℝ =>
        β * α * (Real.sin θ) ^ (-β) *
          (twoUserInducedCostNumerator θ z1 y) ^ (β / 2 - 1) *
            (z1 - y * Real.cos θ))
      (paper_two_user_induced_cost_cross_partial α β θ z1 z2) z2 :=
  hasDerivAt_twoUserInducedCost_z1_derivative_z2 hbase

/--
Proposition `uniqueness`, corrected Step-1 calculus bridge: if the canonical
cross-partial is strictly negative throughout a vertical open interval, then
the displayed first induced-cost partial is strictly decreasing on its closed
vertical closure.  The interval and derivative-base hypotheses are explicit;
this does not infer a support graph or its no-gap property.
-/
theorem paper_two_user_induced_cost_first_partial_strictAntiOn_vertical_of_cross_partial_neg
    {α β θ z1 a b : ℝ}
    (hbase : ∀ z2, z2 ∈ Set.Icc a b →
      twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hcross : ∀ z2, z2 ∈ Set.Ioo a b →
      paper_two_user_induced_cost_cross_partial α β θ z1 z2 < 0) :
    StrictAntiOn
      (fun z2 : ℝ => β * α * (Real.sin θ) ^ (-β) *
        (twoUserInducedCostNumerator θ z1 z2) ^ (β / 2 - 1) *
          (z1 - z2 * Real.cos θ))
      (Set.Icc a b) :=
  twoUserInducedCostFirstPartial_strictAntiOn_vertical_of_crossPartial_neg
    hbase hcross

/--
Proposition `uniqueness`, corrected support-fibre consequence: two vertical
coordinates in the same explicitly supplied interval cannot both satisfy the
same first induced-cost partial value when the cross-partial is strictly
negative there.  This does not derive support membership, a common FOC, or an
interval/no-gap property from equilibrium.
-/
theorem paper_two_user_eq_vertical_coordinate_of_first_partial_eq_of_cross_partial_neg
    {α β θ z1 z2 z2' a b h : ℝ}
    (hbase : ∀ z, z ∈ Set.Icc a b →
      twoUserInducedCostNumerator θ z1 z ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hcross : ∀ z, z ∈ Set.Ioo a b →
      paper_two_user_induced_cost_cross_partial α β θ z1 z < 0)
    (hz2 : z2 ∈ Set.Icc a b)
    (hz2' : z2' ∈ Set.Icc a b)
    (hfirst : β * α * (Real.sin θ) ^ (-β) *
      (twoUserInducedCostNumerator θ z1 z2) ^ (β / 2 - 1) *
        (z1 - z2 * Real.cos θ) = h)
    (hfirst' : β * α * (Real.sin θ) ^ (-β) *
      (twoUserInducedCostNumerator θ z1 z2') ^ (β / 2 - 1) *
        (z1 - z2' * Real.cos θ) = h) :
    z2 = z2' :=
  twoUser_eq_verticalCoordinate_of_firstPartial_eq_of_crossPartial_neg
    hbase hcross hz2 hz2' hfirst hfirst'

/--
Proposition `uniqueness`, global graph extraction.  Under the actual global
first-partial and cross-partial hypotheses, the value support is a graph over
its first projection.  This does not claim the projection has no gaps or that
the graph reaches a boundary; those are separate source obligations.
-/
theorem paper_two_user_exists_graphOn_value_support_of_common_first_partial
    {α β θ : ℝ} {H : ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hbase : ∀ z1 z2 : ℝ,
      twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hcross : ∀ z1 z2 : ℝ,
      paper_two_user_induced_cost_cross_partial α β θ z1 z2 < 0)
    (hfirst : ∀ z : ℝ × ℝ, z ∈ S →
      β * α * (Real.sin θ) ^ (-β) *
          (twoUserInducedCostNumerator θ z.1 z.2) ^ (β / 2 - 1) *
            (z.1 - z.2 * Real.cos θ) = H z.1) :
    ∃ g : ℝ → ℝ, S = (Prod.fst '' S).graphOn g :=
  twoUser_exists_graphOn_support_of_common_firstPartial_of_crossPartial_neg
    hbase hcross hfirst

/--
Proposition `uniqueness`, second-coordinate support-fibre consequence.  The
common second induced-cost partial together with a strictly negative cross
partial makes the second coordinate injective on the value support.
-/
theorem paper_two_user_value_support_injOn_snd_of_common_second_partial
    {α β θ : ℝ} {H : ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hbase : ∀ z1 z2 : ℝ,
      twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hcross : ∀ z1 z2 : ℝ,
      paper_two_user_induced_cost_cross_partial α β θ z1 z2 < 0)
    (hsecond : ∀ z : ℝ × ℝ, z ∈ S →
      β * α * (Real.sin θ) ^ (-β) *
          (twoUserInducedCostNumerator θ z.1 z.2) ^ (β / 2 - 1) *
            (z.2 - z.1 * Real.cos θ) = H z.2) :
    S.InjOn Prod.snd :=
  twoUser_support_injOn_snd_of_common_secondPartial_of_crossPartial_neg
    hbase hcross hsecond

/--
Proposition `uniqueness`, corrected global ordering step.  C1 maximization,
strictly negative induced-cost cross-partials, and the source's canonical
nonnegative feasible cone rule out a reversal between two value-support
points.  This is a global ordering fact; it does not yet establish that the
two marginal supports have no gaps or that the graph reaches an endpoint.
-/
theorem paper_two_user_value_support_ordered_of_C1_cross_partial_neg
    {α β θ : ℝ} {H1 H2 : ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hsin : 0 < Real.sin θ) (hcos : 0 ≤ Real.cos θ)
    (hSfeasible : S ⊆ canonicalTwoUserFeasibleValueSet θ)
    (hmax : ∀ z : ℝ × ℝ, z ∈ S →
      IsMaxOn (fun w : ℝ × ℝ => H1 w.1 + H2 w.2 -
        paper_two_user_induced_cost α β θ w.1 w.2)
        (canonicalTwoUserFeasibleValueSet θ) z)
    (hbase : ∀ z1 z2 : ℝ,
      twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hcross : ∀ z1 z2 : ℝ,
      paper_two_user_induced_cost_cross_partial α β θ z1 z2 < 0) :
    ∀ p ∈ S, ∀ q ∈ S, p.1 < q.1 → p.2 ≤ q.2 :=
  canonicalTwoUser_ordered_snd_of_isMaxOn_of_crossPartial_neg
    hsin hcos hSfeasible hmax hbase hcross

/--
Proposition `uniqueness`, C2 graph transport.  If the canonical realized-value
law lies on a measurable graph that is strictly increasing on its first score
support, the second iid maximum-CDF value equals the first one along that
graph.  This proves the measure-theoretic C2 equality only; the source must
still derive the graph and the pointwise derivative regime needed for its ODE.
-/
theorem paper_two_user_c2_iidMaximumCdf_graph_transport
    {P : ℕ} {θ : ℝ} {μ : Measure (Content 2)} [IsProbabilityMeasure μ]
    {g : ℝ → ℝ} (hg : Measurable g)
    (hgraph : ∀ z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      z.2 = g z.1)
    (hstrict : ∀ x ∈
      (Measure.map (fun q : Content 2 => score canonicalTwoUserFirst q) μ).support,
      ∀ y ∈
        (Measure.map (fun q : Content 2 => score canonicalTwoUserFirst q) μ).support,
        x < y → g x < g y)
    {x : ℝ}
    (hx : x ∈
      (Measure.map (fun q : Content 2 => score canonicalTwoUserFirst q) μ).support) :
    AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1)
        (Measure.map (fun q : Content 2 => score (canonicalTwoUserSecond θ) q) μ)
        (g x) =
      AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1)
        (Measure.map (fun q : Content 2 => score canonicalTwoUserFirst q) μ) x :=
  canonicalTwoUser_iidMaximumCdf_second_eq_first_of_valueSupport_graph_strictMonoOn
    hg hgraph hstrict hx

/--
Proposition `uniqueness`, topological and measure-transport completion of the
C2 graph step.  A compact ordered value support with injective coordinate
projections and first raw-score support `Icc 0 B` produces a continuous,
strictly increasing graph; C2's iid maximum-CDF equality then holds along it.
The graph's pointwise differentiability remains a separate premise for the
subsequent ODE step.
-/
theorem paper_two_user_exists_continuous_strict_graph_c2_of_compact_ordered_first_support_interval
    {P : ℕ} {θ B : ℝ} {μ : Measure (Content 2)} [IsProbabilityMeasure μ]
    (hB : 0 ≤ B)
    (hcompact : IsCompact (Measure.map (canonicalTwoUserValueMap θ) μ).support)
    (hinjfst : (Measure.map (canonicalTwoUserValueMap θ) μ).support.InjOn Prod.fst)
    (hinjsnd : (Measure.map (canonicalTwoUserValueMap θ) μ).support.InjOn Prod.snd)
    (hordered : ∀ p ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      ∀ q ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
        p.1 < q.1 → p.2 ≤ q.2)
    (hfirst_support :
      (Measure.map (fun q : Content 2 => score canonicalTwoUserFirst q) μ).support =
        Set.Icc 0 B) :
    ∃ g : ℝ → ℝ, Continuous g ∧
      (∀ x ∈ Set.Icc 0 B,
        (x, g x) ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support) ∧
      (∀ z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support, z.2 = g z.1) ∧
      (∀ x ∈ Set.Icc 0 B, ∀ y ∈ Set.Icc 0 B, x < y → g x < g y) ∧
      (∀ x ∈ Set.Icc 0 B,
        AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1)
            (Measure.map (fun q : Content 2 => score (canonicalTwoUserSecond θ) q) μ)
            (g x) =
          AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1)
            (Measure.map (fun q : Content 2 => score canonicalTwoUserFirst q) μ) x) :=
  canonicalTwoUser_exists_continuous_strictGraph_c2_of_compact_of_ordered_of_firstScoreSupport_eq_Icc
    hB hcompact hinjfst hinjsnd hordered hfirst_support

/--
Proposition `uniqueness`, compact projection-to-aligned-gap bridge.  Under a
compact strictly ordered canonical value support, a first-score marginal gap
ending at a represented value induces a second-score marginal gap ending at
the matching second coordinate.  The compactness, strict order, endpoint, and
left-support premises are explicit and are not inferred from equilibrium.
-/
theorem paper_two_user_second_score_gap_of_compact_strict_value_support_first_gap
    {θ : ℝ} {μ : Measure (Content 2)} {a b d : ℝ}
    (hcompact : IsCompact (Measure.map (canonicalTwoUserValueMap θ) μ).support)
    (hinj : (Measure.map (canonicalTwoUserValueMap θ) μ).support.InjOn Prod.fst)
    (hstrict : ∀ p ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      ∀ q ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
        p.1 < q.1 → p.2 < q.2)
    (hab : a < b)
    (hgap : Set.Ioo a b ⊆
      (Measure.map (fun q : Content 2 => score canonicalTwoUserFirst q) μ).supportᶜ)
    (hleft : ∃ p ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support, p.1 ≤ a)
    (hbd : (b, d) ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support) :
    ∃ c : ℝ, c < d ∧ Set.Ioo c d ⊆
      (Measure.map (fun q : Content 2 => score (canonicalTwoUserSecond θ) q) μ).supportᶜ :=
  canonicalTwoUser_exists_secondScore_gap_of_compact_strict_valueSupport_firstScore_gap
    hcompact hinj hstrict hab hgap hleft hbd

/--
Proposition `uniqueness`, weak-order form of the compact
projection-to-aligned-gap bridge.  Existing C1 maximization supplies the weak
support order; injectivity of both coordinate projections supplies the
strictness needed for the gap conclusion.  Those injectivity and endpoint
conditions remain explicit source obligations.
-/
theorem paper_two_user_second_score_gap_of_compact_ordered_value_support
    {θ : ℝ} {μ : Measure (Content 2)} {a b d : ℝ}
    (hcompact : IsCompact (Measure.map (canonicalTwoUserValueMap θ) μ).support)
    (hinjfst : (Measure.map (canonicalTwoUserValueMap θ) μ).support.InjOn Prod.fst)
    (hinjsnd : (Measure.map (canonicalTwoUserValueMap θ) μ).support.InjOn Prod.snd)
    (hordered : ∀ p ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      ∀ q ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
        p.1 < q.1 → p.2 ≤ q.2)
    (hab : a < b)
    (hgap : Set.Ioo a b ⊆
      (Measure.map (fun q : Content 2 => score canonicalTwoUserFirst q) μ).supportᶜ)
    (hleft : ∃ p ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support, p.1 ≤ a)
    (hbd : (b, d) ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support) :
    ∃ c : ℝ, c < d ∧ Set.Ioo c d ⊆
      (Measure.map (fun q : Content 2 => score (canonicalTwoUserSecond θ) q) μ).supportᶜ :=
  canonicalTwoUser_exists_secondScore_gap_of_compact_ordered_valueSupport_injOn_snd
    hcompact hinjfst hinjsnd hordered hab hgap hleft hbd

/--
Proposition `uniqueness`, common-FOC form of the compact
projection-to-aligned-gap bridge.  Both coordinate injections are proved from
the two displayed marginal first-order identities.  The global order,
compactness, first marginal gap, and support endpoints remain explicit.
-/
theorem paper_two_user_second_score_gap_of_compact_ordered_value_support_common_partials
    {α β θ : ℝ} {μ : Measure (Content 2)} {H1 H2 : ℝ → ℝ} {a b d : ℝ}
    (hbase : ∀ z1 z2 : ℝ,
      twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hcross : ∀ z1 z2 : ℝ,
      paper_two_user_induced_cost_cross_partial α β θ z1 z2 < 0)
    (hfirst : ∀ z : ℝ × ℝ,
      z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support →
      β * α * (Real.sin θ) ^ (-β) *
          (twoUserInducedCostNumerator θ z.1 z.2) ^ (β / 2 - 1) *
            (z.1 - z.2 * Real.cos θ) = H1 z.1)
    (hsecond : ∀ z : ℝ × ℝ,
      z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support →
      β * α * (Real.sin θ) ^ (-β) *
          (twoUserInducedCostNumerator θ z.1 z.2) ^ (β / 2 - 1) *
            (z.2 - z.1 * Real.cos θ) = H2 z.2)
    (hcompact : IsCompact (Measure.map (canonicalTwoUserValueMap θ) μ).support)
    (hordered : ∀ p ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      ∀ q ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
        p.1 < q.1 → p.2 ≤ q.2)
    (hab : a < b)
    (hgap : Set.Ioo a b ⊆
      (Measure.map (fun q : Content 2 => score canonicalTwoUserFirst q) μ).supportᶜ)
    (hleft : ∃ p ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support, p.1 ≤ a)
    (hbd : (b, d) ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support) :
    ∃ c : ℝ, c < d ∧ Set.Ioo c d ⊆
      (Measure.map (fun q : Content 2 => score (canonicalTwoUserSecond θ) q) μ).supportᶜ :=
  canonicalTwoUser_exists_secondScore_gap_of_compact_ordered_valueSupport_common_partials
    hbase hcross hfirst hsecond hcompact hordered hab hgap hleft hbd

/--
Proposition `uniqueness`, C1-derived form of the compact support-gap bridge.
At every realized value, strict interior feasibility and differentiability of
the marginal reward functions derive the two displayed FOCs from C1 itself.
The source does not currently establish those pointwise regularity premises,
so they remain visible here.
-/
theorem paper_two_user_second_score_gap_of_compact_ordered_value_support_isMaxOn
    {α β θ : ℝ} {μ : Measure (Content 2)} {H1 H2 : ℝ → ℝ} {a b d : ℝ}
    (hbase : ∀ z1 z2 : ℝ,
      twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hcross : ∀ z1 z2 : ℝ,
      paper_two_user_induced_cost_cross_partial α β θ z1 z2 < 0)
    (hsin : 0 < Real.sin θ)
    (hmax : ∀ z : ℝ × ℝ,
      z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support →
      IsMaxOn
        (fun w : ℝ × ℝ => H1 w.1 + H2 w.2 - paper_two_user_induced_cost α β θ w.1 w.2)
        (canonicalTwoUserFeasibleValueSet θ) z)
    (hinterior : ∀ z : ℝ × ℝ,
      z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support →
        0 < z.1 ∧ z.1 * Real.cos θ < z.2)
    (hderiv1 : ∀ z : ℝ × ℝ,
      z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support →
      HasDerivAt H1 (deriv H1 z.1) z.1)
    (hderiv2 : ∀ z : ℝ × ℝ,
      z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support →
      HasDerivAt H2 (deriv H2 z.2) z.2)
    (hcompact : IsCompact (Measure.map (canonicalTwoUserValueMap θ) μ).support)
    (hordered : ∀ p ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      ∀ q ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
        p.1 < q.1 → p.2 ≤ q.2)
    (hab : a < b)
    (hgap : Set.Ioo a b ⊆
      (Measure.map (fun q : Content 2 => score canonicalTwoUserFirst q) μ).supportᶜ)
    (hleft : ∃ p ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support, p.1 ≤ a)
    (hbd : (b, d) ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support) :
    ∃ c : ℝ, c < d ∧ Set.Ioo c d ⊆
      (Measure.map (fun q : Content 2 => score (canonicalTwoUserSecond θ) q) μ).supportᶜ :=
  canonicalTwoUser_exists_secondScore_gap_of_compact_ordered_valueSupport_isMaxOn
    hbase hcross hsin hmax hinterior hderiv1 hderiv2 hcompact hordered hab hgap hleft hbd

/--
Proposition `uniqueness`, boundary-safe C1-derived compact support-gap bridge.
The C1 first-order conditions and reward derivatives are required only away
from the zero value.  At a zero coordinate the strict canonical cone identifies
the value with the origin, so no first-order condition is applied at that
boundary point.
-/
theorem paper_two_user_second_score_gap_of_compact_ordered_value_support_isMaxOn_away_from_origin
    {α β θ : ℝ} {μ : Measure (Content 2)} {H1 H2 : ℝ → ℝ} {a b d : ℝ}
    (hbase : ∀ z1 z2 : ℝ,
      twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hcross : ∀ z1 z2 : ℝ,
      paper_two_user_induced_cost_cross_partial α β θ z1 z2 < 0)
    (hsin : 0 < Real.sin θ) (hcos : 0 ≤ Real.cos θ)
    (hmax : ∀ z : ℝ × ℝ,
      z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support →
      IsMaxOn
        (fun w : ℝ × ℝ => H1 w.1 + H2 w.2 - paper_two_user_induced_cost α β θ w.1 w.2)
        (canonicalTwoUserFeasibleValueSet θ) z)
    (hinterior : ∀ z : ℝ × ℝ,
      z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support → z ≠ (0, 0) →
        0 < z.1 ∧ z.1 * Real.cos θ < z.2)
    (hderiv1 : ∀ z : ℝ × ℝ,
      z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support → z ≠ (0, 0) →
      HasDerivAt H1 (deriv H1 z.1) z.1)
    (hderiv2 : ∀ z : ℝ × ℝ,
      z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support → z ≠ (0, 0) →
      HasDerivAt H2 (deriv H2 z.2) z.2)
    (hcompact : IsCompact (Measure.map (canonicalTwoUserValueMap θ) μ).support)
    (hordered : ∀ p ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      ∀ q ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
        p.1 < q.1 → p.2 ≤ q.2)
    (hab : a < b)
    (hgap : Set.Ioo a b ⊆
      (Measure.map (fun q : Content 2 => score canonicalTwoUserFirst q) μ).supportᶜ)
    (hleft : ∃ p ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support, p.1 ≤ a)
    (hbd : (b, d) ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support) :
    ∃ c : ℝ, c < d ∧ Set.Ioo c d ⊆
      (Measure.map (fun q : Content 2 => score (canonicalTwoUserSecond θ) q) μ).supportᶜ :=
  canonicalTwoUser_exists_secondScore_gap_of_compact_ordered_valueSupport_isMaxOn_awayOrigin
    hbase hcross hsin hcos hmax hinterior hderiv1 hderiv2 hcompact hordered hab hgap hleft hbd

/--
Proposition `uniqueness`, compact-support consequence of the actual canonical
two-user Nash model. Positive scaled Euclidean norm-power cost bounds every
support action by `((number of users) / α)^(1 / β)`; continuity then transports
that compactness to the joint realized-value support.
-/
theorem paper_two_user_compact_value_support_of_scaled_norm_rpow_cost_nash
    {P : ℕ} [Nonempty (Fin P)] {α β θ : ℝ} {μ : Measure (Content 2)}
    [IsProbabilityMeasure μ]
    (hnash : SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ)
      (fun p => α * normRpowCost (SourceNorm.l2 2) β p) μ)
    (hα : 0 < α) (hβ : 0 < β) :
    IsCompact (Measure.map (canonicalTwoUserValueMap θ) μ).support :=
  canonicalTwoUser_isCompact_valueSupport_of_scaledNormRpowCostNash hnash hα hβ

/--
Proposition `uniqueness`, the geometric no-gap substep.  Given two positive
coordinate gaps, one common scale factor moves both upper endpoints into their
respective open gaps.  A source-level no-gap proof must additionally prove
that the CDF rewards are unchanged there and that this scaled value is a
feasible strict cost reduction.
-/
theorem paper_two_user_exists_unit_scaling_mem_two_open_intervals
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hc : 0 ≤ c) (hcd : c < d) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      a < t * b ∧ t * b < b ∧ c < t * d ∧ t * d < d :=
 exists_unit_scaling_mem_two_open_intervals_of_nonneg ha hab hc hcd

/--
Proposition uniqueness, corrected no-gap contradiction. If a common strict
scale reduction is feasible and leaves both marginal CDF rewards unchanged,
it contradicts C1 maximization. The two nonlocal premises remain explicit.
-/
theorem paper_two_user_no_gap_of_strict_scale_same_marginals
    {H1 H2 : ℝ → ℝ} {α β θ z1 z2 t : ℝ} {feasible : Set (ℝ × ℝ)}
    (hmax : IsMaxOn
      (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
        paper_two_user_induced_cost α β θ z.1 z.2)
      feasible (z1, z2))
    (hscaled_feasible : (t * z1, t * z2) ∈ feasible)
    (hH1 : H1 (t * z1) = H1 z1)
    (hH2 : H2 (t * z2) = H2 z2)
    (hcost : paper_two_user_induced_cost α β θ (t * z1) (t * z2) <
      paper_two_user_induced_cost α β θ z1 z2) :
    False :=
  twoUser_not_isMaxOn_of_strictScale_same_marginals
    hmax hscaled_feasible hH1 hH2 hcost

/--
Proposition `uniqueness`, fully measure-aware local no-gap contradiction.
For atomless marginal laws, if both open intervals immediately below a C1
support value are disjoint from their marginal supports and a common scale
enters them, the iid-maximum CDF rewards are unchanged and C1 is impossible.
The nonlocal task of producing the aligned second gap remains separate.
-/
theorem paper_two_user_no_gap_of_two_atomless_marginal_open_gaps
    {P : ℕ} {μ1 μ2 : Measure ℝ} [IsProbabilityMeasure μ1]
    [IsProbabilityMeasure μ2] [NoAtoms μ1] [NoAtoms μ2]
    {α β θ a b c d t : ℝ}
    (hmax : IsMaxOn
      (fun z : ℝ × ℝ =>
        AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1) μ1 z.1 +
          AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1) μ2 z.2 -
            paper_two_user_induced_cost α β θ z.1 z.2)
      (canonicalTwoUserFeasibleValueSet θ) (b, d))
    (hbd : (b, d) ∈ canonicalTwoUserFeasibleValueSet θ)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (ht : 0 < t) (ht_one : t < 1)
    (hpair : b ≠ 0 ∨ d ≠ 0)
    (hgap1 : Set.Ioo a b ⊆ μ1.supportᶜ)
    (hgap2 : Set.Ioo c d ⊆ μ2.supportᶜ)
    (htb : t * b ∈ Set.Ioo a b)
    (htd : t * d ∈ Set.Ioo c d) :
    False :=
  canonicalTwoUser_not_isMaxOn_iidMaximumCdf_of_two_marginal_open_gaps
    hmax hbd hα hβ hsin ht ht_one hpair hgap1 hgap2 htb htd

/--
Proposition `uniqueness`, conditional monotonicity completion: a supplied
continuous injective support graph with nonnegative local slope on an interval
is strictly increasing there.  This leaves the source's graph construction,
regularity, and no-gap claims as visible hypotheses.
-/
theorem paper_two_user_graph_strictMonoOn_of_continuousOn_hasDerivAt_nonneg_injOn
    {g g' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn g (Set.Icc a b))
    (hderiv : ∀ w, w ∈ Set.Ioo a b → HasDerivAt g (g' w) w)
    (hnonneg : ∀ w, w ∈ Set.Ioo a b → 0 ≤ g' w)
    (hinj : (Set.Icc a b).InjOn g) :
    StrictMonoOn g (Set.Icc a b) :=
  twoUser_graph_strictMonoOn_of_continuousOn_hasDerivAt_nonneg_injOn
    hcont hderiv hnonneg hinj

/-- Lemma `secondderiv`, source sign bracket. -/
noncomputable abbrev paper_two_user_second_deriv_sign_bracket
    (β θ φ : ℝ) : ℝ :=
  twoUserSecondDerivSignBracket β θ φ

/--
Lemma `secondderiv`, trigonometric reduction of the cross-partial bracket to
the source expression.
-/
theorem paper_two_user_second_deriv_source_bracket_identity
    {β θ φ : ℝ} (hβ : β ≠ 0) :
    (β - 2) * Real.sin φ * Real.sin (θ - φ) - Real.cos θ =
      (β / 2) * paper_two_user_second_deriv_sign_bracket β θ φ :=
  twoUser_secondDeriv_source_bracket_identity hβ

/--
Proposition `supportrestriction`, analytic substep: if the source
`secondderiv` bracket vanishes on a nonempty open angle interval, then beta is
two and the user-angle cosine is zero. This does not assert the source's
equilibrium-to-support reduction.
-/
theorem paper_supportrestriction_bracket_zero_interval_implies_degenerate
    {β θ a b : ℝ} (hβ : 0 < β) (hab : a < b)
    (hzero : ∀ φ, φ ∈ Set.Ioo a b →
      paper_two_user_second_deriv_sign_bracket β θ φ = 0) :
    β = 2 ∧ Real.cos θ = 0 :=
  twoUserSecondDerivSignBracket_eq_zero_on_Ioo_implies_degenerate hβ hab hzero

/--
Proposition `supportrestriction`, source-angle version of the analytic
substep: on every nonempty open interval, the bracket has a nonzero point
under the source angle range and printed nondegeneracy condition. This is not
a support-restriction or equilibrium conclusion.
-/
theorem paper_supportrestriction_bracket_nonzero_on_nonempty_interval
    {β θ a b : ℝ} (hβ : 0 < β) (hab : a < b)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2) :
    ∃ φ, φ ∈ Set.Ioo a b ∧
      paper_two_user_second_deriv_sign_bracket β θ φ ≠ 0 :=
  twoUserSecondDerivSignBracket_exists_ne_zero_on_Ioo_of_source_nondegenerate
    hβ hab hθ_nonneg hθ_le_half_pi hnondegenerate

/--
Lemma `secondderiv` bracket geometry: for beta above two, the bracket is
strictly increasing on the left half of an angle interval below pi. This is a
local analytic fact and does not supply the source's support-graph step.
-/
theorem paper_two_user_second_deriv_sign_bracket_strict_mono_left_of_two_lt_beta
    {β θ : ℝ} (hβ : 2 < β) (hθ_lt_pi : θ < Real.pi) :
    StrictMonoOn (fun φ => paper_two_user_second_deriv_sign_bracket β θ φ)
      (Set.Icc 0 (θ / 2)) :=
  twoUserSecondDerivSignBracket_strictMonoOn_left_of_two_lt_beta hβ hθ_lt_pi

/--
Lemma `secondderiv` bracket geometry: for beta above two, the bracket is
strictly decreasing on the right half of an angle interval below pi. Together
with the left-half result it is bracket geometry, not the omitted global
finite-genre fiber classification.
-/
theorem paper_two_user_second_deriv_sign_bracket_strict_anti_right_of_two_lt_beta
    {β θ : ℝ} (hβ : 2 < β) (hθ_lt_pi : θ < Real.pi) :
    StrictAntiOn (fun φ => paper_two_user_second_deriv_sign_bracket β θ φ)
      (Set.Icc (θ / 2) θ) :=
  twoUserSecondDerivSignBracket_strictAntiOn_right_of_two_lt_beta hβ hθ_lt_pi

/--
Proposition `supportrestriction`, local FOC derivation: a local maximum of the
displayed reparameterized objective, an explicit first-marginal derivative,
and the induced-cost derivative give the first-partial formula. This does not
infer local maximality or differentiability from C1, support, or equilibrium
semantics.
-/
theorem paper_supportrestriction_first_partial_eq_marginal_derivative_of_local_max
    {H1 H2 h1 : ℝ → ℝ} {α β θ z1 z2 : ℝ}
    (hbase : twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2)
    (hH1 : HasDerivAt H1 (h1 z1) z1)
    (hmax : IsLocalMax
      (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
        twoUserInducedCost α β θ z.1 z.2) (z1, z2)) :
    β * α * (Real.sin θ) ^ (-β) *
        (twoUserInducedCostNumerator θ z1 z2) ^ (β / 2 - 1) *
          (z1 - z2 * Real.cos θ) = h1 z1 :=
  twoUserInducedCostFirstPartial_eq_marginalDerivative_of_isLocalMax
    hbase hH1 hmax

/--
Proposition `supportrestriction`, ball-wide FOC derivation: visible local
maximality and derivative premises at each point of the source-shaped ball give
the first-partial identity throughout that ball. This is not a support or
equilibrium conclusion.
-/
theorem paper_supportrestriction_first_partial_eq_marginal_derivative_on_l2_ball_of_local_max
    {H1 H2 h1 : ℝ → ℝ} {α β θ z1 z2 ε : ℝ}
    (hbase : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hH1 : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        HasDerivAt H1 (h1 x) x)
    (hmax : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        IsLocalMax
          (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
            twoUserInducedCost α β θ z.1 z.2) (x, y)) :
    ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        β * α * (Real.sin θ) ^ (-β) *
            (twoUserInducedCostNumerator θ x y) ^ (β / 2 - 1) *
              (x - y * Real.cos θ) = h1 x :=
  twoUserInducedCostFirstPartial_eq_marginalDerivative_on_l2Ball_of_isLocalMax
    hbase hH1 hmax

/--
Proposition `supportrestriction`, C1-style support-ball FOC bridge: if each
point of the visible support ball maximizes the displayed objective over a
visible feasible set and the ball lies in that set, Lean derives the local
maximum and first-partial identity. It does not infer C1, ball inclusion, or
feasible interior from an equilibrium.
-/
theorem paper_supportrestriction_first_partial_eq_marginal_derivative_of_c1_support_ball
    {H1 H2 h1 : ℝ → ℝ} {α β θ z1 z2 ε : ℝ}
    {S feasible : Set (ℝ × ℝ)}
    (hbase : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hH1 : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        HasDerivAt H1 (h1 x) x)
    (hball_support : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → (x, y) ∈ S)
    (hC1 : ∀ z : ℝ × ℝ, z ∈ S →
      IsMaxOn
        (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
          twoUserInducedCost α β θ z.1 z.2) feasible z)
    (hball_feasible : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → (x, y) ∈ feasible) :
    ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        β * α * (Real.sin θ) ^ (-β) *
            (twoUserInducedCostNumerator θ x y) ^ (β / 2 - 1) *
              (x - y * Real.cos θ) = h1 x :=
  twoUserInducedCostFirstPartial_eq_marginalDerivative_on_l2Ball_of_supportMaximizers
    hbase hH1 hball_support hC1 hball_feasible

/--
Proposition `supportrestriction`, local FOC calculus step: if the displayed
first-partial expression is constant on a vertical open interval, its
cross-partial is zero at an interior point. The interval constancy and
differentiability premise are visible; no C1 or equilibrium package is used.
-/
theorem paper_supportrestriction_cross_partial_zero_of_foc_constant_on_interval
    {α β θ z1 z2 a b h : ℝ}
    (hz2 : z2 ∈ Set.Ioo a b)
    (hbase : twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hconstant : ∀ y, y ∈ Set.Ioo a b →
      β * α * (Real.sin θ) ^ (-β) *
          (twoUserInducedCostNumerator θ z1 y) ^ (β / 2 - 1) *
            (z1 - y * Real.cos θ) = h) :
    paper_two_user_induced_cost_cross_partial α β θ z1 z2 = 0 :=
  twoUserInducedCostCrossPartial_eq_zero_of_firstPartial_eq_on_Ioo
    hz2 hbase hconstant

/--
Proposition `supportrestriction`, a.e. FOC repair.  On an open rectangle, an
almost-everywhere common first-partial identity plus continuity in the first
coordinate implies the pointwise cross-partial conclusion.  This is the
source-valid replacement for applying a density-defined derivative at every
point.
-/
theorem paper_supportrestriction_cross_partial_zero_of_ae_foc_on_rectangle
    {α β θ a b c d x y : ℝ} {h1 : ℝ → ℝ}
    (hab : a < b) (hcd : c < d)
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo c d)
    (hbase : ∀ u v : ℝ, u ∈ Set.Ioo a b → v ∈ Set.Ioo c d →
      twoUserInducedCostNumerator θ u v ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hpartial_cont : ∀ v : ℝ, v ∈ Set.Ioo c d →
      ContinuousOn
        (fun u : ℝ => β * α * (Real.sin θ) ^ (-β) *
          (twoUserInducedCostNumerator θ u v) ^ (β / 2 - 1) *
            (u - v * Real.cos θ))
        (Set.Ioo a b))
    (hfirst_ae : ∀ᵐ u ∂volume, u ∈ Set.Ioo a b → ∀ v : ℝ,
      v ∈ Set.Ioo c d → β * α * (Real.sin θ) ^ (-β) *
        (twoUserInducedCostNumerator θ u v) ^ (β / 2 - 1) *
          (u - v * Real.cos θ) = h1 u) :
    paper_two_user_induced_cost_cross_partial α β θ x y = 0 :=
  twoUserInducedCostCrossPartial_eq_zero_of_ae_firstPartial_eq_on_rectangle
    hab hcd hx hy hbase hpartial_cont hfirst_ae

/--
Proposition `supportrestriction`, ball-to-cross-partial local bridge: a visible
first-partial identity on a positive-radius Euclidean ball yields zero
cross-partial at its center. It does not infer the ball or FOC identity from a
support or equilibrium premise.
-/
theorem paper_supportrestriction_cross_partial_zero_of_foc_on_l2_ball
    {α β θ z1 z2 ε : ℝ} (hε : 0 < ε)
    (hbase : twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1)
    {h1 : ℝ → ℝ}
    (hfoc : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        β * α * (Real.sin θ) ^ (-β) *
            (twoUserInducedCostNumerator θ x y) ^ (β / 2 - 1) *
              (x - y * Real.cos θ) = h1 x) :
    paper_two_user_induced_cost_cross_partial α β θ z1 z2 = 0 :=
  twoUserInducedCostCrossPartial_eq_zero_of_firstPartial_eq_on_l2Ball
    hε hbase hfoc

/--
Proposition `supportrestriction`, local-max-to-cross-partial bridge: a
positive-radius ball of local maxima for the displayed reparameterized
objective, together with visible marginal and induced-cost differentiability,
forces zero cross-partial at the center. It does not infer its premises from a
support or equilibrium.
-/
theorem paper_supportrestriction_cross_partial_zero_of_local_max_on_l2_ball
    {H1 H2 h1 : ℝ → ℝ} {α β θ z1 z2 ε : ℝ}
    (hε : 0 < ε)
    (hbase_cross : twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hbase_first : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hH1 : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        HasDerivAt H1 (h1 x) x)
    (hmax : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        IsLocalMax
          (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
            twoUserInducedCost α β θ z.1 z.2) (x, y)) :
    paper_two_user_induced_cost_cross_partial α β θ z1 z2 = 0 :=
  twoUserInducedCostCrossPartial_eq_zero_of_isLocalMax_on_l2Ball
    hε hbase_cross hbase_first hH1 hmax

/--
Proposition `supportrestriction`, C1-style support-ball-to-cross-partial
bridge: explicit support-ball, feasible-domain, C1-style maximizer, and
derivative premises yield zero cross-partial at the ball center. This is not an
equilibrium or support-restriction conclusion.
-/
theorem paper_supportrestriction_cross_partial_zero_of_c1_support_ball
    {H1 H2 h1 : ℝ → ℝ} {α β θ z1 z2 ε : ℝ}
    {S feasible : Set (ℝ × ℝ)}
    (hε : 0 < ε)
    (hbase_cross : twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hbase_first : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hH1 : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        HasDerivAt H1 (h1 x) x)
    (hball_support : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → (x, y) ∈ S)
    (hC1 : ∀ z : ℝ × ℝ, z ∈ S →
      IsMaxOn
        (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
          twoUserInducedCost α β θ z.1 z.2) feasible z)
    (hball_feasible : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → (x, y) ∈ feasible) :
    paper_two_user_induced_cost_cross_partial α β θ z1 z2 = 0 :=
  twoUserInducedCostCrossPartial_eq_zero_of_supportMaximizers_on_l2Ball
    hε hbase_cross hbase_first hH1 hball_support hC1 hball_feasible

/--
Proposition `supportrestriction`, support-ball transport: an explicit l2 ball
in the topological support of the canonical content law yields an l2 ball in
the topological support of its realized-value pushforward. It does not infer
the content ball, C1, or an equilibrium from the source assumptions.
-/
theorem paper_supportrestriction_realized_value_support_ball_of_content_support_ball
    {θ ε : ℝ} {μ : Measure (Content 2)} {p0 : Content 2}
    (hε : 0 < ε) (hsin : Real.sin θ ≠ 0)
    (hcontent_ball : ∀ p : Content 2,
      (p 0 - p0 0) ^ 2 + (p 1 - p0 1) ^ 2 < ε ^ 2 →
      p ∈ μ.support) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x y : ℝ,
        (x - (canonicalTwoUserValueMap θ p0).1) ^ 2 +
            (y - (canonicalTwoUserValueMap θ p0).2) ^ 2 < δ ^ 2 →
        (x, y) ∈
          (Measure.map (canonicalTwoUserValueMap θ) μ).support :=
  canonicalTwoUserValueMap_exists_l2Ball_subset_map_support_of_content_l2Ball_subset_support
    hε hsin hcontent_ball

/--
Proposition `supportrestriction`, feasible-ball bridge: a realized-value
support ball lies in a visible closed feasible set when the canonical value law
is almost everywhere feasible. It does not infer closedness, a.e. feasibility,
C1, or an equilibrium.
-/
theorem paper_supportrestriction_feasible_ball_of_realized_value_support_ball
    {θ : ℝ} {μ : Measure (Content 2)} {feasible : Set (ℝ × ℝ)}
    {z1 z2 ε : ℝ}
    (hfeasible_closed : IsClosed feasible)
    (hae_feasible : ∀ᵐ p ∂μ, canonicalTwoUserValueMap θ p ∈ feasible)
    (hball_support : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
      (x, y) ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support) :
    ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
      (x, y) ∈ feasible :=
  canonicalTwoUserValueMap_l2Ball_subset_feasible_of_ae_feasible
    hfeasible_closed hae_feasible hball_support

/--
Proposition `supportrestriction`, canonical feasible-domain bridge: if the
canonical coordinates are nonsingular, then an almost-everywhere nonnegative
content law makes every point of a realized-value support ball feasible in the
actual value-map image of the nonnegative source action domain. It does not
infer C1, an equilibrium, or validity of the source's literal generic C1
domain display.
-/
theorem paper_supportrestriction_canonical_feasible_ball_of_ae_nonnegative
    {θ : ℝ} {μ : Measure (Content 2)} {z1 z2 ε : ℝ}
    (hsin : Real.sin θ ≠ 0)
    (hae_nonnegative : ∀ᵐ p ∂μ, NonnegativeContent p)
    (hball_support : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
      (x, y) ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support) :
    ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
      (x, y) ∈ canonicalTwoUserValueMap θ ''
        {p : Content 2 | NonnegativeContent p} :=
  canonicalTwoUserValueMap_l2Ball_subset_image_nonnegative_of_ae_nonnegative
    hsin hae_nonnegative hball_support

/--
Proposition `supportrestriction`, source-parametrized sign transfer: a zero
cross-partial yields a zero `secondderiv` bracket when the exact positive
factor premises are supplied. This is a direct calculus implication, not a
support or equilibrium conclusion.
-/
theorem paper_supportrestriction_bracket_zero_of_cross_partial_zero_at_source_param
    {α β θ φ r : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hNpos : 0 < r ^ 2 * (Real.sin θ) ^ 2)
    (hcross : paper_two_user_induced_cost_cross_partial α β θ
      (r * Real.cos φ) (r * Real.cos (θ - φ)) = 0) :
    paper_two_user_second_deriv_sign_bracket β θ φ = 0 :=
  twoUserSecondDerivSignBracket_eq_zero_of_crossPartial_eq_zero_param
    hα hβ hsin hNpos hcross

/--
Proposition `supportrestriction`, completed angle-interval contradiction: away
from the beta-two/right-angle degeneracy, the canonical cross-partial cannot
vanish throughout a nonempty source-parametrized angle interval.  The premise
is the interval conclusion itself; this theorem does not infer that chart from
a support ball or infer C1 from equilibrium semantics.
-/
theorem paper_supportrestriction_no_parametric_angle_interval_cross_partial_zero
    {α β θ r a b : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2)
    (hr : 0 < r) (hab : a < b)
    (hcross : ∀ φ, φ ∈ Set.Ioo a b →
      paper_two_user_induced_cost_cross_partial α β θ
        (r * Real.cos φ) (r * Real.cos (θ - φ)) = 0) :
    False :=
  twoUser_no_parametric_angleInterval_crossPartial_zero_of_source_nondegenerate
    hα hβ hsin hθ_nonneg hθ_le_half_pi hnondegenerate hr hab hcross

/--
Proposition `supportrestriction`, C1/open-support angle-interval form.  The
visible open-support C1, differentiability, and parametrized-support premises
are sufficient for the source contradiction.  It intentionally does not
bundle an unproved support-ball-to-angle-chart or Nash-to-C1 bridge.
-/
theorem paper_supportrestriction_no_parametric_angle_interval_c1_support_maximizers
    {H1 H2 h1 : ℝ → ℝ} {α β θ r a b : ℝ}
    {S feasible : Set (ℝ × ℝ)}
    (hopen : IsOpen S) (hS_feasible : S ⊆ feasible)
    (hbase_cross : ∀ x y : ℝ, (x, y) ∈ S →
      twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hbase_first : ∀ x y : ℝ, (x, y) ∈ S →
      twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hH1 : ∀ x y : ℝ, (x, y) ∈ S → HasDerivAt H1 (h1 x) x)
    (hC1 : ∀ z : ℝ × ℝ, z ∈ S →
      IsMaxOn
        (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
          twoUserInducedCost α β θ z.1 z.2) feasible z)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2)
    (hr : 0 < r) (hab : a < b)
    (hparam_support : ∀ φ, φ ∈ Set.Ioo a b →
      (r * Real.cos φ, r * Real.cos (θ - φ)) ∈ S) :
    False :=
  twoUser_no_parametric_angleInterval_supportMaximizers_of_source_nondegenerate
    hopen hS_feasible hbase_cross hbase_first hH1 hC1 hα hβ hsin
    hθ_nonneg hθ_le_half_pi hnondegenerate hr hab hparam_support

/--
Proposition `supportrestriction`, pointwise open-support endpoint.  Under the
visible C1/FOC hypotheses, nondegeneracy excludes a canonical
source-parametrized point from the open support: continuity of that chart and
openness supply the angle interval internally.  This does not claim that the
source support ball contains such a point or that Nash behavior yields C1.
-/
theorem paper_supportrestriction_no_open_c1_support_maximizer_at_source_param_point
    {H1 H2 h1 : ℝ → ℝ} {α β θ r φ : ℝ}
    {S feasible : Set (ℝ × ℝ)}
    (hopen : IsOpen S) (hS_feasible : S ⊆ feasible)
    (hbase_cross : ∀ x y : ℝ, (x, y) ∈ S →
      twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hbase_first : ∀ x y : ℝ, (x, y) ∈ S →
      twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hH1 : ∀ x y : ℝ, (x, y) ∈ S → HasDerivAt H1 (h1 x) x)
    (hC1 : ∀ z : ℝ × ℝ, z ∈ S →
      IsMaxOn
        (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
          twoUserInducedCost α β θ z.1 z.2) feasible z)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2)
    (hr : 0 < r)
    (hpoint : (r * Real.cos φ, r * Real.cos (θ - φ)) ∈ S) :
    False :=
  twoUser_no_open_supportMaximizer_at_paramPoint_of_source_nondegenerate
    hopen hS_feasible hbase_cross hbase_first hH1 hC1 hα hβ hsin
    hθ_nonneg hθ_le_half_pi hnondegenerate hr hpoint

/--
Proposition `supportrestriction`, completed open-support analytic endpoint.
For a nonempty open realized-value region, the source polar chart and a
nonempty angle interval now follow from nonsingularity and topology.  Thus the
visible C1/FOC and pointwise differentiability premises contradict
nondegeneracy.  This remains deliberately conditional on those premises: the
paper's Nash-to-C1 and a.e.-to-pointwise regularity transitions are not
silently assumed.
-/
theorem paper_supportrestriction_no_nonempty_open_c1_support_maximizers
    {H1 H2 h1 : ℝ → ℝ} {α β θ : ℝ}
    {S feasible : Set (ℝ × ℝ)}
    (hopen : IsOpen S) (hS_nonempty : S.Nonempty) (hS_feasible : S ⊆ feasible)
    (hbase_cross : ∀ x y : ℝ, (x, y) ∈ S →
      twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hbase_first : ∀ x y : ℝ, (x, y) ∈ S →
      twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hH1 : ∀ x y : ℝ, (x, y) ∈ S → HasDerivAt H1 (h1 x) x)
    (hC1 : ∀ z : ℝ × ℝ, z ∈ S →
      IsMaxOn
        (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
          twoUserInducedCost α β θ z.1 z.2) feasible z)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2) :
    False :=
  twoUser_no_nonempty_open_supportMaximizers_of_source_nondegenerate
    hopen hS_nonempty hS_feasible hbase_cross hbase_first hH1 hC1 hα hβ hsin
    hθ_nonneg hθ_le_half_pi hnondegenerate

/--
Proposition `supportrestriction`, C1-ball endpoint.  A positive-radius
realized-value L2 ball supplies the nonempty open region and source polar
chart internally; under the visible local C1/FOC, derivative, feasibility, and
base-cost conditions, it contradicts the source nondegeneracy condition.  The
unproved transition from an equilibrium and absolutely continuous marginals to
these pointwise C1 premises is intentionally outside this theorem.
-/
theorem paper_supportrestriction_no_c1_l2_support_ball
    {H1 H2 h1 : ℝ → ℝ} {α β θ z1 z2 ε : ℝ}
    {feasible : Set (ℝ × ℝ)}
    (hε : 0 < ε)
    (hball_feasible : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → (x, y) ∈ feasible)
    (hbase_cross : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hbase_first : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hH1 : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → HasDerivAt H1 (h1 x) x)
    (hC1 : ∀ z : ℝ × ℝ,
      (z.1 - z1) ^ 2 + (z.2 - z2) ^ 2 < ε ^ 2 →
        IsMaxOn
          (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
            twoUserInducedCost α β θ z.1 z.2) feasible z)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2) :
    False :=
  twoUser_no_l2Ball_supportMaximizers_of_source_nondegenerate
    hε hball_feasible hbase_cross hbase_first hH1 hC1 hα hβ hsin
    hθ_nonneg hθ_le_half_pi hnondegenerate

/--
Proposition `supportrestriction`, a.e.-differentiability C1-ball endpoint.
This matches the source proof's intended regularity: the marginal derivative
is supplied almost everywhere, while the visible derivative-side base condition
proves continuity of the induced-cost partial and upgrades the FOC before the
polar contradiction.  Deriving the displayed C1 and a.e.-derivative premises
from the paper's equilibrium setup is kept explicit.
-/
theorem paper_supportrestriction_no_c1_l2_support_ball_ae
    {H1 H2 h1 : ℝ → ℝ} {α β θ z1 z2 ε : ℝ}
    {feasible : Set (ℝ × ℝ)}
    (hε : 0 < ε)
    (hball_feasible : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → (x, y) ∈ feasible)
    (hbase_cross : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hbase_first : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hH1_ae : ∀ᵐ x ∂volume, HasDerivAt H1 (h1 x) x)
    (hC1 : ∀ z : ℝ × ℝ,
      (z.1 - z1) ^ 2 + (z.2 - z2) ^ 2 < ε ^ 2 →
        IsMaxOn
          (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
            twoUserInducedCost α β θ z.1 z.2) feasible z)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2) :
    False :=
  twoUser_no_l2Ball_supportMaximizers_ae_of_source_nondegenerate
    hε hball_feasible hbase_cross hbase_first hH1_ae hC1
    hα hβ hsin hθ_nonneg hθ_le_half_pi hnondegenerate

/--
Proposition `supportrestriction`, local-absolute-continuity C1-ball endpoint.
Absolute continuity of the first marginal is used only on an interval covering
the horizontal projection of the value-support ball, where it supplies the
required a.e. derivative.  The source's CDF construction and its
equilibrium-to-C1 implication remain separate obligations.
-/
theorem paper_supportrestriction_no_c1_l2_support_ball_of_H1_AC
    {H1 H2 : ℝ → ℝ} {α β θ z1 z2 ε a b : ℝ}
    {feasible : Set (ℝ × ℝ)}
    (hε : 0 < ε)
    (hball_feasible : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → (x, y) ∈ feasible)
    (hbase_cross : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hbase_first : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hH1_AC : AbsolutelyContinuousOnInterval H1 a b)
    (hball_x_interval : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → x ∈ Set.uIcc a b)
    (hC1 : ∀ z : ℝ × ℝ,
      (z.1 - z1) ^ 2 + (z.2 - z2) ^ 2 < ε ^ 2 →
        IsMaxOn
          (fun z : ℝ × ℝ => H1 z.1 + H2 z.2 -
            twoUserInducedCost α β θ z.1 z.2) feasible z)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2) :
    False :=
  twoUser_no_l2Ball_supportMaximizers_of_source_nondegenerate_of_H1_AC
    hε hball_feasible hbase_cross hbase_first hH1_AC hball_x_interval hC1
    hα hβ hsin hθ_nonneg hθ_le_half_pi hnondegenerate

/--
Proposition `supportrestriction`, marginal-CDF form of the local-AC endpoint.
When the maximum-value CDF is identified with the `n`th power of a
marginal CDF, local absolute continuity of that marginal supplies the first
marginal regularity required by the ball contradiction.  The iid maximum-CDF
identity and the equilibrium-to-C1 bridge are not asserted here.
-/
theorem paper_supportrestriction_no_c1_l2_support_ball_of_marginalCdf_AC
    {F1 H2 : ℝ → ℝ} {n : ℕ} {α β θ z1 z2 ε a b : ℝ}
    {feasible : Set (ℝ × ℝ)}
    (hε : 0 < ε)
    (hball_feasible : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → (x, y) ∈ feasible)
    (hbase_cross : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hbase_first : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hF1_AC : AbsolutelyContinuousOnInterval F1 a b)
    (hball_x_interval : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → x ∈ Set.uIcc a b)
    (hC1 : ∀ z : ℝ × ℝ,
      (z.1 - z1) ^ 2 + (z.2 - z2) ^ 2 < ε ^ 2 →
        IsMaxOn
          (fun z : ℝ × ℝ => F1 z.1 ^ n + H2 z.2 -
            twoUserInducedCost α β θ z.1 z.2) feasible z)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2) :
    False :=
  twoUser_no_l2Ball_supportMaximizers_of_source_nondegenerate_of_marginalCdf_AC
    hε hball_feasible hbase_cross hbase_first hF1_AC hball_x_interval hC1
    hα hβ hsin hθ_nonneg hθ_le_half_pi hnondegenerate

/--
Proposition `supportrestriction`, iid-marginal form of the C1-ball endpoint.
The maximum over the source's `P - 1` independent other-producer draws is now
identified with the corresponding natural power of the marginal CDF by the
shared order-statistics library. This endpoint still leaves the concrete
marginal absolute-continuity and equilibrium-to-C1 bridges explicit.
-/
theorem paper_supportrestriction_no_c1_l2_support_ball_of_source_iid_marginals_AC
    {μ1 μ2 : Measure ℝ} {P : ℕ} [IsProbabilityMeasure μ1] [IsProbabilityMeasure μ2]
    {α β θ z1 z2 ε a b : ℝ} {feasible : Set (ℝ × ℝ)}
    (hε : 0 < ε)
    (hball_feasible : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → (x, y) ∈ feasible)
    (hbase_cross : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hbase_first : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hfirst_marginal_AC : AbsolutelyContinuousOnInterval
      (AppliedModelingLib.Probability.lowerCDFMass μ1) a b)
    (hball_x_interval : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → x ∈ Set.uIcc a b)
    (hC1 : ∀ z : ℝ × ℝ,
      (z.1 - z1) ^ 2 + (z.2 - z2) ^ 2 < ε ^ 2 →
        IsMaxOn
          (fun z : ℝ × ℝ =>
            AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1) μ1 z.1 +
              AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1) μ2 z.2 -
              twoUserInducedCost α β θ z.1 z.2) feasible z)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2) :
    False :=
  twoUser_no_l2Ball_supportMaximizers_of_source_nondegenerate_of_source_iidMarginalCdf_AC
    hε hball_feasible hbase_cross hbase_first hfirst_marginal_AC hball_x_interval hC1
    hα hβ hsin hθ_nonneg hθ_le_half_pi hnondegenerate

/--
Proposition `supportrestriction`, source-marginal-measure form of the C1-ball
endpoint. The paper's Lebesgue absolute-continuity assumption on the first raw
marginal is converted to an absolutely continuous CDF by the shared
Radon--Nikodym/CDF result; the iid maximum-CDF identity is also checked. The
equilibrium-to-C1 bridge remains an explicit separate premise.
-/
theorem paper_supportrestriction_no_c1_l2_support_ball_of_source_iid_marginalMeasureAC
    {μ1 μ2 : Measure ℝ} {P : ℕ} [IsProbabilityMeasure μ1] [IsProbabilityMeasure μ2]
    {α β θ z1 z2 ε a b : ℝ} {feasible : Set (ℝ × ℝ)}
    (hε : 0 < ε)
    (hball_feasible : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → (x, y) ∈ feasible)
    (hbase_cross : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hbase_first : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hμ1 : μ1 ≪ volume)
    (hball_x_interval : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → x ∈ Set.uIcc a b)
    (hC1 : ∀ z : ℝ × ℝ,
      (z.1 - z1) ^ 2 + (z.2 - z2) ^ 2 < ε ^ 2 →
        IsMaxOn
          (fun z : ℝ × ℝ =>
            AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1) μ1 z.1 +
              AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1) μ2 z.2 -
              twoUserInducedCost α β θ z.1 z.2) feasible z)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2) :
    False :=
  twoUser_no_l2Ball_supportMaximizers_of_source_nondegenerate_of_source_iidMarginalMeasureAC
    hε hball_feasible hbase_cross hbase_first hμ1 hball_x_interval hC1
    hα hβ hsin hθ_nonneg hθ_le_half_pi hnondegenerate

/--
Proposition `supportrestriction`, source-faithful equilibrium endpoint for
the canonical two-user L2 cost.  A tie-aware symmetric mixed Nash law with
the original cost `α ‖p‖₂^β` cannot have the displayed positive-radius ball in
its realized-value support outside the source's beta-two/right-angle
degeneracy.  Raw score-law absolute continuity is used to derive the iid CDF
objective, not silently assumed as a C1 premise.  The local derivative-base
and geometric hypotheses are retained explicitly because they are the visible
calculus conditions used by the source proof on that ball.
-/
theorem paper_supportrestriction_no_l2_value_support_ball_of_source_symmetric_mixed_nash
    {P : ℕ} [Nonempty (Fin P)] {α β θ z1 z2 ε a b : ℝ}
    {μ : Measure (Content 2)} [IsProbabilityMeasure μ]
    (hε : 0 < ε)
    (hball_support : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        (x, y) ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support)
    (hbase_cross : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hbase_first : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        twoUserInducedCostNumerator θ x y ≠ 0 ∨ 1 ≤ β / 2)
    (hball_x_interval : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 → x ∈ Set.uIcc a b)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2)
    (hnash : SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ)
      (fun p => α * normRpowCost (SourceNorm.l2 2) β p) μ)
    (hscore_ac : ∀ i : Fin 2,
      Measure.map
        (fun q : Content 2 =>
          score (if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ) q) μ ≪
        volume) :
    False :=
  twoUser_no_l2Ball_valueSupport_of_sourceSymmetricMixedNash_of_source_nondegenerate
    hε hball_support hbase_cross hbase_first hball_x_interval
    hα hβ hsin hθ_nonneg hθ_le_half_pi hnondegenerate hnash hscore_ac

/--
Proposition `supportrestriction`, canonical equilibrium endpoint away from the
zero realized-value pair.  Unlike the lower-level form, this source-facing
version derives the induced-cost derivative-base and horizontal-interval
premises by shrinking the supplied support ball.  It retains the canonical
two-user model, raw score-law absolute continuity, and the source's explicit
angle/nondegeneracy regime.
-/
theorem paper_supportrestriction_no_l2_value_support_ball_of_source_symmetric_mixed_nash_of_center_ne_zero
    {P : ℕ} [Nonempty (Fin P)] {α β θ z1 z2 ε : ℝ}
    {μ : Measure (Content 2)} [IsProbabilityMeasure μ]
    (hε : 0 < ε)
    (hball_support : ∀ x y : ℝ,
      (x - z1) ^ 2 + (y - z2) ^ 2 < ε ^ 2 →
        (x, y) ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support)
    (hcenter : z1 ≠ 0 ∨ z2 ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2)
    (hnash : SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ)
      (fun p => α * normRpowCost (SourceNorm.l2 2) β p) μ)
    (hscore_ac : ∀ i : Fin 2,
      Measure.map
        (fun q : Content 2 =>
          score (if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ) q) μ ≪
        volume) :
    False :=
  twoUser_no_l2Ball_valueSupport_of_sourceSymmetricMixedNash_of_center_ne_zero
    hε hball_support hcenter hα hβ hsin hθ_nonneg hθ_le_half_pi
    hnondegenerate hnash hscore_ac

/--
Proposition `supportrestriction`, canonical content-support endpoint.  A
positive l2 ball in content support centered at nonzero content is transported
through the nonsingular two-user value coordinates and contradicts a tie-aware
source symmetric mixed Nash law in the stated nondegenerate regime.
-/
theorem paper_supportrestriction_no_l2_content_support_ball_of_source_symmetric_mixed_nash_of_center_nonzero
    {P : ℕ} [Nonempty (Fin P)] {α β θ ε : ℝ}
    {μ : Measure (Content 2)} {p0 : Content 2} [IsProbabilityMeasure μ]
    (hε : 0 < ε)
    (hcontent_ball : ∀ p : Content 2,
      (p 0 - p0 0) ^ 2 + (p 1 - p0 1) ^ 2 < ε ^ 2 →
      p ∈ μ.support)
    (hp0 : NonzeroContent p0)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2)
    (hnash : SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ)
      (fun p => α * normRpowCost (SourceNorm.l2 2) β p) μ)
    (hscore_ac : ∀ i : Fin 2,
      Measure.map
        (fun q : Content 2 =>
          score (if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ) q) μ ≪
        volume) :
    False :=
  twoUser_no_l2Ball_contentSupport_of_sourceSymmetricMixedNash_of_center_nonzero
    hε hcontent_ball hp0 hα hβ hsin hθ_nonneg hθ_le_half_pi
    hnondegenerate hnash hscore_ac

/--
Proposition `supportrestriction`, complete canonical two-user content-support
endpoint.  Any positive l2 ball in the content support contradicts a tie-aware
source symmetric mixed Nash law with scaled L2 cost in the source's stated
positive-sine, nondegenerate angle regime.  If its displayed center is zero,
the proof selects an explicit smaller ball with a nonzero center.
-/
theorem paper_supportrestriction_no_l2_content_support_ball_of_source_symmetric_mixed_nash
    {P : ℕ} [Nonempty (Fin P)] {α β θ ε : ℝ}
    {μ : Measure (Content 2)} {p0 : Content 2} [IsProbabilityMeasure μ]
    (hε : 0 < ε)
    (hcontent_ball : ∀ p : Content 2,
      (p 0 - p0 0) ^ 2 + (p 1 - p0 1) ^ 2 < ε ^ 2 →
      p ∈ μ.support)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2)
    (hnash : SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ)
      (fun p => α * normRpowCost (SourceNorm.l2 2) β p) μ)
    (hscore_ac : ∀ i : Fin 2,
      Measure.map
        (fun q : Content 2 =>
          score (if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ) q) μ ≪
        volume) :
    False :=
  twoUser_no_l2Ball_contentSupport_of_sourceSymmetricMixedNash
    hε hcontent_ball hα hβ hsin hθ_nonneg hθ_le_half_pi
    hnondegenerate hnash hscore_ac

/--
Proposition `supportrestriction` in the source's original two-user content
coordinates.  The nonnegative-user and at-least-two-producer assumptions are
kept at this paper-facing boundary.  The proof transports the actual score
map of the given pair, so its feasible region remains the image of the
original nonnegative content cone rather than a rotated canonical cone.
-/
theorem paper_supportrestriction_no_l2_content_support_ball_of_original_two_user_source_nash
    {P : ℕ} [Nonempty (Fin P)] {α β θ ε : ℝ}
    {u v p0 : Content 2} {μ : Measure (Content 2)}
    [IsProbabilityMeasure μ]
    (hP : 1 < P)
    (husers_nonnegative : ∀ i : Fin 2,
      NonnegativeContent (if i = 0 then u else v))
    (hε : 0 < ε)
    (hcontent_ball : ∀ p : Content 2,
      (p 0 - p0 0) ^ 2 + (p 1 - p0 1) ^ 2 < ε ^ 2 →
        p ∈ μ.support)
    (hu : score u u = 1) (hv : score v v = 1)
    (huv : score u v = Real.cos θ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsin : 0 < Real.sin θ) (hθ_nonneg : 0 ≤ θ)
    (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hnondegenerate : β ≠ 2 ∨ θ ≠ Real.pi / 2)
    (hnash : SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then u else v)
      (fun q => α * normRpowCost (SourceNorm.l2 2) β q) μ)
    (hscore_ac : ∀ i : Fin 2,
      Measure.map (fun q : Content 2 => score (if i = 0 then u else v) q) μ ≪
        volume) :
    False :=
  twoUser_no_l2Ball_contentSupport_of_sourceSymmetricMixedNash_of_source_nondegenerate
    hε hcontent_ball hu hv huv hα hβ hsin hθ_nonneg hθ_le_half_pi
    hnondegenerate hnash hscore_ac

/--
Proposition `uniqueness`, original-coordinate closed-cone step.  For every
content action in the equilibrium support, the pair of user scores lies between
the two user rays.  This is the cone geometry used by the phase-transition
argument, established directly from feasible nonnegative ray deviations
instead of by rotating the nonnegative content cone to canonical coordinates.
-/
theorem paper_uniqueness_original_score_support_closed_user_cone
    {P : ℕ} [Nonempty (Fin P)] {α β θ : ℝ}
    {u v p : Content 2} {μ : Measure (Content 2)}
    [IsProbabilityMeasure μ]
    (hP : 1 < P)
    (husers_nonnegative : ∀ i : Fin 2,
      NonnegativeContent (if i = 0 then u else v))
    (hu : score u u = 1) (hv : score v v = 1)
    (huv : score u v = Real.cos θ)
    (hα : 0 < α) (hβ : 0 < β) (hsin : 0 < Real.sin θ)
    (hnash : SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then u else v)
      (fun q => α * normRpowCost (SourceNorm.l2 2) β q) μ)
    (hscore_ac : ∀ i : Fin 2,
      Measure.map (fun q : Content 2 => score (if i = 0 then u else v) q) μ ≪
        volume)
    (hp : p ∈ μ.support) :
    Real.cos θ * score v p ≤ score u p ∧
      Real.cos θ * score u p ≤ score v p := by
  have hu_nonnegative : NonnegativeContent u := by
    simpa using husers_nonnegative 0
  have hv_nonnegative : NonnegativeContent v := by
    simpa using husers_nonnegative 1
  exact twoUserScore_closedUserCone_of_scaledNormRpowCostNash
    hu hv huv hu_nonnegative hv_nonnegative hα hβ hsin hnash hscore_ac hp

/--
Proposition `uniqueness`, original-coordinate C1 ordering step.  Under the
displayed global induced-cost differentiability and negative-cross-partial
conditions, two equilibrium-support actions cannot reverse their user-score
order.  The proof uses only meet/join deviations in the feasible closed cone
generated by the original nonnegative users.
-/
theorem paper_uniqueness_original_score_support_ordered_of_cross_partial_neg
    {P : ℕ} [Nonempty (Fin P)] {α β θ : ℝ}
    {u v p q : Content 2} {μ : Measure (Content 2)}
    [IsProbabilityMeasure μ]
    (hP : 1 < P)
    (husers_nonnegative : ∀ i : Fin 2,
      NonnegativeContent (if i = 0 then u else v))
    (hu : score u u = 1) (hv : score v v = 1)
    (huv : score u v = Real.cos θ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsin : 0 < Real.sin θ) (hcos : 0 ≤ Real.cos θ)
    (hbase : ∀ z1 z2 : ℝ,
      twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2 - 1)
    (hcross : ∀ z1 z2 : ℝ,
      twoUserInducedCostCrossPartial α β θ z1 z2 < 0)
    (hnash : SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then u else v)
      (fun r => α * normRpowCost (SourceNorm.l2 2) β r) μ)
    (hscore_ac : ∀ i : Fin 2,
      Measure.map (fun r : Content 2 => score (if i = 0 then u else v) r) μ ≪
        volume)
    (hp : p ∈ μ.support) (hq : q ∈ μ.support)
    (hpq : score u p < score u q) :
    score v p ≤ score v q := by
  have hu_nonnegative : NonnegativeContent u := by
    simpa using husers_nonnegative 0
  have hv_nonnegative : NonnegativeContent v := by
    simpa using husers_nonnegative 1
  exact twoUserScore_ordered_snd_of_scaledNormRpowCostNash
    hu hv huv hu_nonnegative hv_nonnegative hα hβ hsin hcos hbase hcross
    hnash hscore_ac hp hq hpq

/--
Proposition `uniqueness`, original-coordinate support graph step.  If every
nonzero support score lies strictly between the two user rays and the two
score-CDF rewards are differentiable there, strict negative cross partials
make each score coordinate injective on equilibrium support.  These are the
precise local hypotheses needed before the paper's no-gap/C2 argument.
-/
theorem paper_uniqueness_original_score_support_injective_of_strict_cone
    {P : ℕ} [Nonempty (Fin P)] {α β θ : ℝ}
    {u v : Content 2} {μ : Measure (Content 2)}
    [IsProbabilityMeasure μ]
    (hP : 1 < P)
    (husers_nonnegative : ∀ i : Fin 2,
      NonnegativeContent (if i = 0 then u else v))
    (hu : score u u = 1) (hv : score v v = 1)
    (huv : score u v = Real.cos θ)
    (hsin : 0 < Real.sin θ) (hcos : 0 ≤ Real.cos θ)
    (hnash : SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then u else v)
      (fun r => α * normRpowCost (SourceNorm.l2 2) β r) μ)
    (hscore_ac : ∀ i : Fin 2,
      Measure.map (fun r : Content 2 => score (if i = 0 then u else v) r) μ ≪
        volume)
    (hstrict : ∀ p : Content 2, p ∈ μ.support → p ≠ 0 →
      Real.cos θ * score v p < score u p ∧
        Real.cos θ * score u p < score v p)
    (hcross : ∀ z1 z2 : ℝ, 0 < z1 → 0 < z2 →
      twoUserInducedCostCrossPartial α β θ z1 z2 < 0)
    (hderiv1 : ∀ p : Content 2, p ∈ μ.support → p ≠ 0 →
      HasDerivAt
        (fun x => AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1)
          (Measure.map (fun r : Content 2 => score u r) μ) x)
        (deriv (fun x => AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1)
          (Measure.map (fun r : Content 2 => score u r) μ) x) (score u p))
        (score u p))
    (hderiv2 : ∀ p : Content 2, p ∈ μ.support → p ≠ 0 →
      HasDerivAt
        (fun x => AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1)
          (Measure.map (fun r : Content 2 => score v r) μ) x)
        (deriv (fun x => AppliedModelingLib.Probability.iidMaximumCdf (n := P - 1)
          (Measure.map (fun r : Content 2 => score v r) μ) x) (score v p))
        (score v p)) :
    (twoUserScoreMap u v '' μ.support).InjOn Prod.fst ∧
      (twoUserScoreMap u v '' μ.support).InjOn Prod.snd := by
  have hu_nonnegative : NonnegativeContent u := by
    simpa using husers_nonnegative 0
  have hv_nonnegative : NonnegativeContent v := by
    simpa using husers_nonnegative 1
  exact twoUserScoreSupport_injOn_projections_of_scaledNormRpowCostNash
    hu hv huv hu_nonnegative hv_nonnegative hsin hcos hnash hscore_ac hstrict
    hcross hderiv1 hderiv2

/-- Corollary `2users` / Theorem `phasetransitionformal`, critical value. -/
noncomputable abbrev paper_two_user_phase_threshold (θ : ℝ) : ℝ :=
  twoUserPhaseThreshold θ

/--
The source's threshold definition (equation (2)), specialized to two equal
populations and the nonnegative Euclidean unit ball.  It is stated using the
formal product-supremum condition, which is the source's equality of the two
displayed maxima after compactness supplies attainment.
-/
noncomputable def paper_two_user_product_beta_star
    {D K : ℕ} (users : Fin 2 → Content D) : ℝ :=
  sSup {β : ℝ | 1 ≤ β ∧
    SingleGenreProductSupCondition
      {z : Fin (2 * K) → ℝ |
        InPoweredUnitImage (twoPopulationUsers K users)
          (fun p => NonnegativeContent p ∧ (SourceNorm.l2 D).norm p ≤ 1)
          β z}}

/--
Corollary `2users`, corrected angular welfare calculation: the product of the
two normalized user scores is maximized at their angular bisector.  The source
proof's subsequent threshold endpoint is separately held for source review.
-/
theorem paper_two_user_score_product_isMaxOn_bisector
    (θstar : ℝ) :
    IsMaxOn (fun θ : ℝ => Real.cos θ * Real.cos (θstar - θ)) Set.univ
      (θstar / 2) :=
  twoUser_cos_product_isMaxOn_bisector θstar

/--
Corrected C1 polar-cost calculation for Corollary `2users`: the induced cost
of the source polar value point is `alpha * r^beta`. This records explicitly
the source Lemma `inducedcost` exponent `beta / 2`; the printed Corollary
proof's `beta` exponent would not have this radial homogeneity.
-/
theorem paper_two_user_induced_cost_polar_eq_alpha_mul_rpow
    {α β θ φ r : ℝ}
    (hr : 0 ≤ r) (hsin : 0 < Real.sin θ) :
    twoUserInducedCost α β θ
        (r * Real.cos φ) (r * Real.cos (θ - φ)) = α * r ^ β :=
  twoUserInducedCost_param_eq_alpha_mul_rpow hr hsin

/--
Valid arbitrary-dimensional replacement for the equality asserted by source
Lemma `inducedcost`: for two unit users with the stated Gram angle, the
canonical two-score cost is a lower bound on the original Euclidean
norm-power cost of every realizing content vector.  Equality needs additional
two-coordinate/cone-preserving hypotheses.
-/
theorem paper_two_user_induced_cost_le_original_l2_cost
    {D : ℕ} {u v p : Content D} {β θ : ℝ}
    (hu : score u u = 1) (hv : score v v = 1)
    (huv : score u v = Real.cos θ) (hsin : 0 < Real.sin θ)
    (hβ : 0 ≤ β) :
    twoUserInducedCost 1 β θ (score u p) (score v p) ≤
      AppliedModelingLib.FiniteDimensionalNorms.l2 p ^ β :=
  twoUserInducedCost_le_l2_rpow_of_unit_score_pair hu hv huv hsin hβ

/--
The precise squared-cost version of the valid general-dimensional reduction:
the Gram quadratic lower-bounds the source's constrained nonnegative score
fibre minimum whenever that fibre is nonempty.  It deliberately does not
assert equality.
-/
theorem paper_two_user_induced_cost_quadratic_le_nonnegative_fiber_cost
    {D : ℕ} {u v : Content D} {θ z1 z2 : ℝ}
    (hu : score u u = 1) (hv : score v v = 1)
    (huv : score u v = Real.cos θ) (hsin : Real.sin θ ≠ 0)
    (hfiber : ∃ p : Content D,
      NonnegativeContent p ∧ score u p = z1 ∧ score v p = z2) :
    twoUserInducedCostQuadratic θ z1 z2 ≤
      twoUserNonnegativeFiberNormSq u v z1 z2 :=
  twoUserInducedCostQuadratic_le_nonnegativeFiberNormSq hu hv huv hsin hfiber

/--
Exact repaired form of Lemma `inducedcost` for the canonical two-coordinate
nonnegative model: on a feasible score pair, the actual constrained fibre
minimum equals the Gram quadratic.  This is the cone-preserving statement the
phase-transition C1 calculation may use.
-/
theorem paper_canonical_two_user_induced_cost_quadratic_eq_nonnegative_fiber_cost
    {θ z1 z2 : ℝ} (hsin : 0 < Real.sin θ)
    (hfeasible : NonnegativeContent (canonicalTwoUserContentOfValues θ z1 z2)) :
    twoUserNonnegativeFiberNormSq
      canonicalTwoUserFirst (canonicalTwoUserSecond θ) z1 z2 =
      twoUserInducedCostQuadratic θ z1 z2 :=
  canonicalTwoUser_nonnegativeFiberNormSq_eq_inducedCostQuadratic hsin hfeasible

/--
The repaired induced-cost identity is unchanged by adjoining unused ambient
coordinates to the canonical pair of user rows.  This is the cone-preserving
arbitrary-dimension extension, distinct from rotating an arbitrary
nonnegative user pair into canonical coordinates.
-/
theorem paper_canonical_two_user_extended_induced_cost_quadratic_eq_nonnegative_fiber_cost
    {m : ℕ} {θ z1 z2 : ℝ} (hsin : 0 < Real.sin θ)
    (hfeasible : NonnegativeContent (canonicalTwoUserContentOfValues θ z1 z2)) :
    twoUserNonnegativeFiberNormSq
      (canonicalTwoUserExtendedFirst m) (canonicalTwoUserExtendedSecond m θ) z1 z2 =
      twoUserInducedCostQuadratic θ z1 z2 :=
  canonicalTwoUserExtended_nonnegativeFiberNormSq_eq_inducedCostQuadratic hsin hfeasible

/--
For every feasible score pair in the extended canonical model, the repaired
induced cost has an explicit nonnegative content minimizer.  This exposes the
attainment bridge needed when translating C1 value-space maximization back to
the original content game.
-/
theorem paper_canonical_two_user_extended_exists_nonnegative_fiber_cost_minimizer
    {m : ℕ} {θ z1 z2 : ℝ} (hsin : 0 < Real.sin θ)
    (hfeasible : NonnegativeContent (canonicalTwoUserContentOfValues θ z1 z2)) :
    ∃ p : Content (m + 2), NonnegativeContent p ∧
      score (canonicalTwoUserExtendedFirst m) p = z1 ∧
      score (canonicalTwoUserExtendedSecond m θ) p = z2 ∧
      score p p = twoUserNonnegativeFiberNormSq
        (canonicalTwoUserExtendedFirst m) (canonicalTwoUserExtendedSecond m θ) z1 z2 :=
  canonicalTwoUserExtended_exists_nonnegativeFiberNormSq_minimizer hsin hfeasible

/--
At every nonnegative score-fibre realization, the exact constrained fibre
minimum in the paper's `L2^beta` cost convention is a lower bound on the
realization's own cost.
-/
theorem paper_two_user_nonnegative_fiber_l2_rpow_le_l2_rpow
    {D : ℕ} {u v p : Content D} {beta : ℝ}
    (hbeta : 0 ≤ beta) (hp : NonnegativeContent p) :
    twoUserNonnegativeFiberL2Rpow beta u v (score u p) (score v p) ≤
      AppliedModelingLib.FiniteDimensionalNorms.l2 p ^ beta :=
  twoUserNonnegativeFiberL2Rpow_le_l2_rpow hbeta hp

/--
The repaired extended canonical fibre formula has an explicit nonnegative
minimizer for the paper's actual `L2^beta` content cost.
-/
theorem paper_canonical_two_user_extended_exists_nonnegative_fiber_l2_rpow_minimizer
    {m : ℕ} {beta theta z1 z2 : ℝ} (hsin : 0 < Real.sin theta)
    (hfeasible : NonnegativeContent (canonicalTwoUserContentOfValues theta z1 z2)) :
    ∃ p : Content (m + 2), NonnegativeContent p ∧
      score (canonicalTwoUserExtendedFirst m) p = z1 ∧
      score (canonicalTwoUserExtendedSecond m theta) p = z2 ∧
      AppliedModelingLib.FiniteDimensionalNorms.l2 p ^ beta =
        twoUserNonnegativeFiberL2Rpow beta
          (canonicalTwoUserExtendedFirst m) (canonicalTwoUserExtendedSecond m theta) z1 z2 :=
  canonicalTwoUserExtended_exists_nonnegativeFiberL2Rpow_minimizer hsin hfeasible

/--
Source correction for Lemma `inducedcost`: its displayed arbitrary-dimensional
nonnegative-fibre equality is false.  In a nonempty three-coordinate fibre of
two nonnegative unit users, the formula's squared cost is `25 / 34`, strictly
below every feasible content squared norm.  The named users, their unit and
Gram identities, and an explicit feasible content point are compiled in the
paper implementation.
-/
theorem paper_lemma_inducedcost_general_dimension_counterexample
    {q : Content 3} (hq : NonnegativeContent q)
    (hfirst : score threeCoordinateInducedCostFirstUser q = 4 / 5)
    (hsecond : score threeCoordinateInducedCostSecondUser q = 0) :
    twoUserInducedCostQuadratic (Real.arccos (9 / 25 : ℝ)) (4 / 5) 0 < score q q :=
  threeCoordinateInducedCost_source_quadratic_lt_nonnegative_fiber_normSq
    hq hfirst hsecond

/--
The counterexample in the source's own induced-cost language: the exact
nonnegative-fibre squared cost is one, while the displayed Gram quadratic is
strictly smaller.  Hence the arbitrary-dimensional equality cannot be used as
the C1 cost identity without a revised source assumption or a constrained
fibre-minimization proof.
-/
theorem paper_lemma_inducedcost_general_dimension_exact_counterexample :
    twoUserInducedCostQuadratic (Real.arccos (9 / 25 : ℝ)) (4 / 5) 0 <
      twoUserNonnegativeFiberNormSq
        threeCoordinateInducedCostFirstUser threeCoordinateInducedCostSecondUser (4 / 5) 0 :=
  threeCoordinateInducedCost_source_quadratic_lt_nonnegativeFiberNormSq

/--
Corrected local threshold calculation for Corollary `2users`: at or below the
displayed phase threshold, the angular-power objective has nonpositive
bisector curvature. This is a local consequence of the corrected formula,
not yet the missing global C1 maximum or the full threshold identity.
-/
theorem paper_two_user_bisector_curvature_nonpos_of_le_phase_threshold
    {β θ : ℝ}
    (hβ : 0 ≤ β) (hden : 0 < 1 - Real.cos θ)
    (hβle : β ≤ paper_two_user_phase_threshold θ)
    (hcos : 0 < Real.cos (θ / 2)) :
    2 * β *
      ((β - 1) * (Real.sin (θ / 2)) ^ 2 *
          (Real.cos (θ / 2)) ^ (β - 2) -
        (Real.cos (θ / 2)) ^ β) ≤ 0 :=
  twoUserCosPowerSum_bisector_curvature_nonpos_of_le_phaseThreshold
    hβ hden hβle hcos

theorem paper_two_user_coeff_lt_cos_of_beta_lt_phase_threshold
    {β θ : ℝ}
    (hβ : 0 < β)
    (hden : 0 < 1 - Real.cos θ)
    (hβlt : β < paper_two_user_phase_threshold θ) :
    (β - 2) / β < Real.cos θ :=
  twoUser_coeff_lt_cos_of_beta_lt_phaseThreshold hβ hden hβlt

theorem paper_two_user_cos_lt_coeff_of_phase_threshold_lt_beta
    {β θ : ℝ}
    (hβ : 0 < β)
    (hden : 0 < 1 - Real.cos θ)
    (hβgt : paper_two_user_phase_threshold θ < β) :
    Real.cos θ < (β - 2) / β :=
  twoUser_cos_lt_coeff_of_phaseThreshold_lt_beta hβ hden hβgt

/--
Above the source phase threshold, a positive user-angle cosine implies beta
is strictly above two. This connects the paper's phase regime to the checked
bracket geometry.
-/
theorem paper_two_user_two_lt_beta_of_phase_threshold_lt_beta
    {β θ : ℝ} (hden : 0 < 1 - Real.cos θ)
    (hcos : 0 < Real.cos θ) (hphase : paper_two_user_phase_threshold θ < β) :
    2 < β :=
  twoUser_two_lt_beta_of_phaseThreshold_lt_beta hden hcos hphase

/--
In the above-threshold source regime, the `secondderiv` bracket is strictly
increasing left of the angle bisector. This is bracket geometry only, not a
support-graph or finite-genre fiber conclusion.
-/
theorem paper_two_user_second_deriv_sign_bracket_strict_mono_left_of_phase_threshold_lt_beta
    {β θ : ℝ} (hden : 0 < 1 - Real.cos θ)
    (hcos : 0 < Real.cos θ) (hphase : paper_two_user_phase_threshold θ < β)
    (hθ_lt_pi : θ < Real.pi) :
    StrictMonoOn (fun φ => paper_two_user_second_deriv_sign_bracket β θ φ)
      (Set.Icc 0 (θ / 2)) :=
  twoUserSecondDerivSignBracket_strictMonoOn_left_of_phaseThreshold_lt_beta
    hden hcos hphase hθ_lt_pi

/--
In the above-threshold source regime, the `secondderiv` bracket is strictly
decreasing right of the angle bisector. It is the complementary local bracket
calculation and not the paper's unsupported global fiber classification.
-/
theorem paper_two_user_second_deriv_sign_bracket_strict_anti_right_of_phase_threshold_lt_beta
    {β θ : ℝ} (hden : 0 < 1 - Real.cos θ)
    (hcos : 0 < Real.cos θ) (hphase : paper_two_user_phase_threshold θ < β)
    (hθ_lt_pi : θ < Real.pi) :
    StrictAntiOn (fun φ => paper_two_user_second_deriv_sign_bracket β θ φ)
      (Set.Icc (θ / 2) θ) :=
  twoUserSecondDerivSignBracket_strictAntiOn_right_of_phaseThreshold_lt_beta
    hden hcos hphase hθ_lt_pi

/--
Theorem `phasetransitionformal`, finite-genre obstruction algebra: above the
critical value, the `secondderiv` bracket is positive at the midpoint angle.
-/
theorem paper_two_user_second_deriv_bracket_midpoint_pos_of_phase_threshold_lt_beta
    {β θ : ℝ}
    (hβ : 0 < β)
    (hden : 0 < 1 - Real.cos θ)
    (hβgt : paper_two_user_phase_threshold θ < β) :
    0 < paper_two_user_second_deriv_sign_bracket β θ (θ / 2) :=
  twoUserSecondDerivSignBracket_midpoint_pos_of_phaseThreshold_lt_beta
    hβ hden hβgt

/--
Complete root geometry for the `secondderiv` bracket in the acute
above-threshold regime: exactly one root lies on each side of the angle
bisector. This is not a simultaneous FOC-label fiber classification and does
not construct the support graph used in the source's next inference.
-/
theorem paper_two_user_second_deriv_bracket_exists_unique_zero_on_each_half
    {β θ : ℝ} (hθ_pos : 0 < θ) (hθ_lt_pi : θ < Real.pi)
    (hden : 0 < 1 - Real.cos θ) (hcos : 0 < Real.cos θ)
    (hphase : paper_two_user_phase_threshold θ < β) :
    (∃! φ, φ ∈ Set.Ioo 0 (θ / 2) ∧
      paper_two_user_second_deriv_sign_bracket β θ φ = 0) ∧
    (∃! φ, φ ∈ Set.Ioo (θ / 2) θ ∧
      paper_two_user_second_deriv_sign_bracket β θ φ = 0) :=
  twoUserSecondDerivSignBracket_existsUnique_zero_on_each_half_of_phaseThreshold_lt_beta
    hθ_pos hθ_lt_pi hden hcos hphase

/--
Theorem `phasetransitionformal`, uniqueness-regime sign algebra: below the
critical value, the `secondderiv` bracket is nonpositive throughout the source
angle range.
-/
theorem paper_two_user_second_deriv_bracket_nonpos_of_beta_lt_phase_threshold_and_cos_range
    {β θ φ : ℝ}
    (hβ : 0 < β)
    (hden : 0 < 1 - Real.cos θ)
    (hβlt : β < paper_two_user_phase_threshold θ)
    (hcosθ_nonneg : 0 ≤ Real.cos θ)
    (hcos_lower : Real.cos θ ≤ Real.cos (θ - 2 * φ))
    (hcos_upper : Real.cos (θ - 2 * φ) ≤ 1) :
    paper_two_user_second_deriv_sign_bracket β θ φ ≤ 0 :=
  twoUserSecondDerivSignBracket_nonpos_of_beta_lt_phaseThreshold_and_cos_range
    hβ hden hβlt hcosθ_nonneg hcos_lower hcos_upper

theorem paper_two_user_second_deriv_bracket_neg_of_beta_lt_phase_threshold_and_cos_range
    {β θ φ : ℝ}
    (hβ : 0 < β)
    (hden : 0 < 1 - Real.cos θ)
    (hβlt : β < paper_two_user_phase_threshold θ)
    (hcosθ_pos : 0 < Real.cos θ)
    (hcos_lower : Real.cos θ ≤ Real.cos (θ - 2 * φ))
    (hcos_upper : Real.cos (θ - 2 * φ) ≤ 1) :
    paper_two_user_second_deriv_sign_bracket β θ φ < 0 :=
  twoUserSecondDerivSignBracket_neg_of_beta_lt_phaseThreshold_and_cos_range
    hβ hden hβlt hcosθ_pos hcos_lower hcos_upper

theorem paper_two_user_cos_range_of_angle_mem_Icc
    {θ φ : ℝ}
    (hθ_le_pi : θ ≤ Real.pi)
    (hφ_nonneg : 0 ≤ φ)
    (hφ_leθ : φ ≤ θ) :
    Real.cos θ ≤ Real.cos (θ - 2 * φ) ∧
      Real.cos (θ - 2 * φ) ≤ 1 :=
  twoUser_cos_range_of_angle_mem_Icc hθ_le_pi hφ_nonneg hφ_leθ

/--
Theorem `phasetransitionformal`, source angle interval endpoint: below the
critical value, the `secondderiv` bracket is nonpositive for every support
angle between the two nonnegative user directions.
-/
theorem paper_two_user_second_deriv_bracket_nonpos_of_beta_lt_phase_threshold_and_angle_mem_Icc
    {β θ φ : ℝ}
    (hβ : 0 < β)
    (hden : 0 < 1 - Real.cos θ)
    (hβlt : β < paper_two_user_phase_threshold θ)
    (hθ_nonneg : 0 ≤ θ)
    (hθ_le_half_pi : θ ≤ Real.pi / 2)
    (hφ_nonneg : 0 ≤ φ)
    (hφ_leθ : φ ≤ θ) :
    paper_two_user_second_deriv_sign_bracket β θ φ ≤ 0 :=
  twoUserSecondDerivSignBracket_nonpos_of_beta_lt_phaseThreshold_and_angle_mem_Icc
    hβ hden hβlt hθ_nonneg hθ_le_half_pi hφ_nonneg hφ_leθ

/--
Theorem `phasetransitionformal`, strict uniqueness-regime sign algebra away
from the orthogonal boundary: below the critical value, the `secondderiv`
bracket is strictly negative along the source angle interval.
-/
theorem paper_two_user_second_deriv_bracket_neg_of_beta_lt_phase_threshold_and_angle_mem_Icc_lt_half_pi
    {β θ φ : ℝ}
    (hβ : 0 < β)
    (hden : 0 < 1 - Real.cos θ)
    (hβlt : β < paper_two_user_phase_threshold θ)
    (hθ_nonneg : 0 ≤ θ)
    (hθ_lt_half_pi : θ < Real.pi / 2)
    (hφ_nonneg : 0 ≤ φ)
    (hφ_leθ : φ ≤ θ) :
    paper_two_user_second_deriv_sign_bracket β θ φ < 0 :=
  twoUserSecondDerivSignBracket_neg_of_beta_lt_phaseThreshold_and_angle_mem_Icc_lt_half_pi
    hβ hden hβlt hθ_nonneg hθ_lt_half_pi hφ_nonneg hφ_leθ

/--
Proposition `uniqueness`, corrected algebraic ODE normalization. Under the
explicit product-rule representation of a nonzero support graph, the source's
graph equation is equivalent to the displayed normalized differential
equation. This does not assert the source's global uniqueness conclusion.
-/
theorem paper_two_user_normalized_graph_ode_iff
    {θ w f f' g g' : ℝ} (hw : w ≠ 0)
    (hg : g = w * f) (hg' : g' = f + w * f') :
    g' * g - g' * w * Real.cos θ = w - g * Real.cos θ ↔
      w * f' * (f - Real.cos θ) = 1 - f ^ 2 :=
  twoUser_normalizedGraphOde_iff hw hg hg'

/-- Proposition `uniqueness`, corrected final inverse-graph implication.
When a support graph and its left inverse are both proved weakly below the
diagonal on their respective domains, the graph is diagonal.  The source does
not establish these global one-sided bounds or the needed graph/inverse
package from equilibrium; those remain explicit hypotheses here. -/
theorem paper_two_user_graph_eq_idOn_of_left_inverse_of_le_self
    {I₁ I₂ : Set ℝ} {g gInv : ℝ → ℝ}
    (hmap : Set.MapsTo g I₁ I₂)
    (hleft : Set.EqOn (gInv ∘ g) id I₁)
    (hbelow : ∀ w ∈ I₁, g w ≤ w)
    (hinv_below : ∀ z ∈ I₂, gInv z ≤ z) :
    Set.EqOn g id I₁ :=
  eq_idOn_of_leftInverse_of_mapsTo_of_le_self_of_inverse_le_self
    hmap hleft hbelow hinv_below

/--
Proposition `uniqueness`, corrected local Step-2 graph-ODE bridge.  A supplied
local CDF-composition identity and derivative data yield the density transport;
with the explicit nonzero common FOC scale, they yield the source graph ODE.
This does not infer C2 transport or the graph regularity premises from
equilibrium.
-/
theorem paper_two_user_graph_ode_of_eventuallyEq_cdf_composition_and_first_partial_forms
    {H1 H2 g : ℝ → ℝ} {w h1 h2 g' scale θ : ℝ}
    (hH1 : HasDerivAt H1 h1 w)
    (hH2 : HasDerivAt H2 h2 (g w))
    (hg : HasDerivAt g g' w)
    (htransport : H1 =ᶠ[𝓝 w] fun x => H2 (g x))
    (hscale : scale ≠ 0)
    (hfirst1 : h1 = scale * (w - g w * Real.cos θ))
    (hfirst2 : h2 = scale * (g w - w * Real.cos θ)) :
    g' * g w - g' * w * Real.cos θ = w - g w * Real.cos θ :=
  twoUser_graphOde_of_eventuallyEq_cdfComposition_and_firstPartialForms
    hH1 hH2 hg htransport hscale hfirst1 hfirst2

/--
Proposition `uniqueness`, corrected global Step-3 conclusion.  A graph that
continuously reaches the C1-forced origin and solves the graph ODE at every
strictly interior point of the nonnegative cone is diagonal on its whole
compact radius interval.  The proof uses the monotonicity of
`(g(w)^2 - w^2)^2`, not the malformed printed logarithmic solution.  C1--C3
still need to supply the graph, continuity, strict-interior ODE, and endpoint
premises; none is inferred here.
-/
theorem paper_two_user_graph_eq_idOn_of_origin_of_strict_cone_ode
    {B c : ℝ} {g g' : ℝ → ℝ}
    (hc : 0 ≤ c) (hzero : g 0 = 0)
    (hcont : ContinuousOn g (Set.Icc 0 B))
    (hnonneg : ∀ w ∈ Set.Icc 0 B, 0 ≤ g w)
    (hcone : ∀ w ∈ Set.Ioo 0 B, w * c < g w)
    (hderiv : ∀ w ∈ Set.Ioo 0 B, HasDerivAt g (g' w) w)
    (hode : ∀ w ∈ Set.Ioo 0 B,
      g' w * g w - g' w * w * c = w - g w * c) :
    ∀ w ∈ Set.Icc 0 B, g w = w :=
  twoUser_graph_eq_idOn_of_origin_of_strictCone_ode
    hc hzero hcont hnonneg hcone hderiv hode

/--
Proposition `uniqueness`, corrected C1/C2 composition.  On a supplied compact
graph interval, C1's interior first-order conditions, C2's CDF transport, and
explicit pointwise derivative data imply that the graph is diagonal.  The
origin is established separately and never used as an interior FOC point.
The source's stated a.e. density regularity does not supply the pointwise
derivative hypotheses below.
-/
theorem paper_two_user_graph_eq_idOn_of_value_support_graph_of_c1c2
    {α β θ B : ℝ} {μ : Measure (Content 2)} {H1 H2 g g' : ℝ → ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hsin : 0 < Real.sin θ) (hcos : 0 ≤ Real.cos θ) (hB : 0 ≤ B)
    (hgraph_mem : ∀ w ∈ Set.Icc 0 B,
      (w, g w) ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support)
    (hcont : ContinuousOn g (Set.Icc 0 B))
    (hfeasible : ∀ z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      z ∈ canonicalTwoUserFeasibleValueSet θ)
    (hmax : ∀ z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      IsMaxOn
        (fun w : ℝ × ℝ => H1 w.1 + H2 w.2 - twoUserInducedCost α β θ w.1 w.2)
        (canonicalTwoUserFeasibleValueSet θ) z)
    (hinterior : ∀ z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      z ≠ (0, 0) → 0 < z.1 ∧ z.1 * Real.cos θ < z.2)
    (hderiv1 : ∀ z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      z ≠ (0, 0) → HasDerivAt H1 (deriv H1 z.1) z.1)
    (hderiv2 : ∀ z ∈ (Measure.map (canonicalTwoUserValueMap θ) μ).support,
      z ≠ (0, 0) → HasDerivAt H2 (deriv H2 z.2) z.2)
    (hgraph_deriv : ∀ w ∈ Set.Ioo 0 B, HasDerivAt g (g' w) w)
    (htransport : ∀ w ∈ Set.Icc 0 B, H2 (g w) = H1 w) :
    ∀ w ∈ Set.Icc 0 B, g w = w :=
  twoUser_graph_eq_idOn_of_valueSupport_graph_of_C1C2
    hα hβ hsin hcos hB hgraph_mem hcont hfeasible hmax hinterior
    hderiv1 hderiv2 hgraph_deriv htransport

/--
Proposition `uniqueness`, corrected local Step-3 first integral.  On the
explicit positive-radius, `(-1,1)` normalized-graph domain, the displayed
logarithmic expression has zero derivative under the normalized graph ODE.
This is a local separation identity, not the source's unsupported global ODE
solution or uniqueness conclusion.
-/
theorem paper_two_user_hasDerivAt_normalized_graph_first_integral_zero
    {θ w f' : ℝ} {f : ℝ → ℝ}
    (hw : 0 < w)
    (hf_lower : -1 < f w)
    (hf_upper : f w < 1)
    (hderiv : HasDerivAt f f' w)
    (hode : w * f' * (f w - Real.cos θ) = 1 - f w ^ 2) :
    HasDerivAt
      (fun x =>
        -((1 : ℝ) / 2) * Real.log (1 - f x * f x) -
          (Real.cos θ / 2) * (Real.log (1 + f x) - Real.log (1 - f x)) -
            Real.log x)
      0 w :=
  twoUser_hasDerivAt_normalizedGraphFirstIntegral_zero
    hw hf_lower hf_upper hderiv hode

/--
Proposition `uniqueness`, Step-3 counterexample to ODE-only uniqueness.  At
the orthogonal angle, `sqrt(w^2 - 1)` is a differentiable non-diagonal local
solution of the graph ODE for every `w > 1`.  Thus additional global boundary
or equilibrium conditions are mathematically necessary.
-/
theorem paper_two_user_orthogonal_sqrt_graph_satisfies_graph_ode_non_diagonal
    {w : ℝ} (hw : 1 < w) :
    let g : ℝ := Real.sqrt (w ^ 2 - 1)
    HasDerivAt (fun x => Real.sqrt (x ^ 2 - 1)) (w / g) w ∧
      (w / g) * g - (w / g) * w * Real.cos (Real.pi / 2) =
        w - g * Real.cos (Real.pi / 2) ∧ g ≠ w :=
  twoUser_orthogonal_sqrtGraph_satisfies_graphOde_nonDiagonal hw

/--
Lemma `secondderiv`, first canonical linear factor under
`z=(r cos φ, r cos(θ-φ))`.
-/
theorem paper_two_user_param_z2_sub_z1_cos
    (θ φ r : ℝ) :
    r * Real.cos (θ - φ) - (r * Real.cos φ) * Real.cos θ =
      r * Real.sin θ * Real.sin φ :=
  twoUserParam_z2_sub_z1_cos θ φ r

/--
Lemma `secondderiv`, second canonical linear factor under
`z=(r cos φ, r cos(θ-φ))`.
-/
theorem paper_two_user_param_z1_sub_z2_cos
    (θ φ r : ℝ) :
    r * Real.cos φ - (r * Real.cos (θ - φ)) * Real.cos θ =
      r * Real.sin θ * Real.sin (θ - φ) :=
  twoUserParam_z1_sub_z2_cos θ φ r

/--
Lemma `secondderiv`, source parametrization turns the induced-cost numerator
into `r^2 sin^2(θ)`.
-/
theorem paper_two_user_induced_cost_numerator_param
    (θ φ r : ℝ) :
    twoUserInducedCostNumerator θ
        (r * Real.cos φ) (r * Real.cos (θ - φ)) =
      r ^ 2 * (Real.sin θ) ^ 2 :=
  twoUserInducedCostNumerator_param θ φ r

/--
Lemma `secondderiv`, source parametrization of the cross-partial: after
substituting `z=(r cos φ, r cos(θ-φ))`, the cross-partial is a scalar multiple
of the paper's sign bracket.
-/
theorem paper_two_user_induced_cost_cross_partial_param_factor
    {α β θ φ r : ℝ}
    (hβ : β ≠ 0)
    (hNpos : 0 < r ^ 2 * (Real.sin θ) ^ 2) :
    paper_two_user_induced_cost_cross_partial α β θ
        (r * Real.cos φ) (r * Real.cos (θ - φ)) =
      β * α * (Real.sin θ) ^ (-β) *
        ((r ^ 2 * (Real.sin θ) ^ 2) ^ (β / 2 - 1) *
          ((β / 2) * paper_two_user_second_deriv_sign_bracket β θ φ)) :=
  twoUserInducedCostCrossPartial_param_factor hβ hNpos

/--
Corrected Proposition `uniqueness` Step-1 sign conclusion: below the phase
threshold, the induced-cost cross-partial is strictly negative at every
positive-radius source-parametrized point in the visible angle interval.
This is an analytic component, not a support-graph or equilibrium conclusion.
-/
theorem paper_two_user_induced_cost_cross_partial_neg_of_beta_lt_phase_threshold
    {α β θ φ r : ℝ}
    (hα : 0 < α)
    (hβ : 0 < β)
    (hsin : 0 < Real.sin θ)
    (hden : 0 < 1 - Real.cos θ)
    (hNpos : 0 < r ^ 2 * (Real.sin θ) ^ 2)
    (hβlt : β < paper_two_user_phase_threshold θ)
    (hθ_nonneg : 0 ≤ θ)
    (hθ_lt_half_pi : θ < Real.pi / 2)
    (hφ_nonneg : 0 ≤ φ)
    (hφ_leθ : φ ≤ θ) :
    paper_two_user_induced_cost_cross_partial α β θ
      (r * Real.cos φ) (r * Real.cos (θ - φ)) < 0 :=
  twoUserInducedCostCrossPartial_neg_of_beta_lt_phaseThreshold_and_angle_mem_Icc_lt_half_pi
    hα hβ hsin hden hNpos hβlt hθ_nonneg hθ_lt_half_pi hφ_nonneg hφ_leθ

/--
Lemma `regionscolor`, source sign transfer: after the source parametrization
`z=(r cos φ, r cos(θ-φ))`, the Hessian/cross-partial sign condition implies
the printed bracket sign because the scalar factor relating the two signs is
positive under the paper's cost and angle assumptions.
-/
theorem paper_regionscolor_param_bracket_nonpos_of_cross_nonpos
    {α β θ φ r slope : ℝ}
    (hα : 0 < α)
    (hβ : 0 < β)
    (hsin : 0 < Real.sin θ)
    (hNpos : 0 < r ^ 2 * (Real.sin θ) ^ 2)
    (hcross :
      slope * paper_two_user_induced_cost_cross_partial α β θ
        (r * Real.cos φ) (r * Real.cos (θ - φ)) ≤ 0) :
    slope * paper_two_user_second_deriv_sign_bracket β θ φ ≤ 0 :=
  twoUser_regionscolor_param_bracket_nonpos_of_cross_nonpos
    hα hβ hsin hNpos hcross

/--
Lemma `regionscolor`, composed paper-facing endpoint: the C1
negative-semidefinite graph-Hessian condition implies the source inequality
`g'(z_1)` times the `secondderiv` sign bracket is nonpositive.
-/
theorem paper_regionscolor_param_bracket_nonpos_of_negativeSemidefinite
    {α β θ φ r slope : ℝ}
    (hα : 0 < α)
    (hβ : 0 < β)
    (hsin : 0 < Real.sin θ)
    (hNpos : 0 < r ^ 2 * (Real.sin θ) ^ 2)
    (hneg :
      paper_negative_semidefinite_quadratic2
        (slope *
          paper_two_user_induced_cost_cross_partial α β θ
            (r * Real.cos φ) (r * Real.cos (θ - φ)))
        (-(paper_two_user_induced_cost_cross_partial α β θ
            (r * Real.cos φ) (r * Real.cos (θ - φ))))
        (slope⁻¹ *
          paper_two_user_induced_cost_cross_partial α β θ
            (r * Real.cos φ) (r * Real.cos (θ - φ)))) :
    slope * paper_two_user_second_deriv_sign_bracket β θ φ ≤ 0 :=
  twoUser_regionscolor_param_bracket_nonpos_of_negativeSemidefinite
    hα hβ hsin hNpos hneg

/--
Lemma `regionscolor`, source-shaped SOC bridge: a supplied objective
second-order condition and the two FOC derivative identities along a support
graph imply the printed slope/bracket inequality. This does not construct the
graph or derive those premises from C1--C3.
-/
theorem paper_regionscolor_param_bracket_nonpos_of_objective_soc_and_graph_foc_derivatives
    {α β θ φ r slope c11 c22 h1prime h2prime : ℝ}
    (hα : 0 < α)
    (hβ : 0 < β)
    (hsin : 0 < Real.sin θ)
    (hNpos : 0 < r ^ 2 * (Real.sin θ) ^ 2)
    (hsoc :
      paper_negative_semidefinite_quadratic2
        (h1prime - c11)
        (-(paper_two_user_induced_cost_cross_partial α β θ
          (r * Real.cos φ) (r * Real.cos (θ - φ))))
        (h2prime - c22))
    (hfirst : h1prime = c11 + slope *
      paper_two_user_induced_cost_cross_partial α β θ
        (r * Real.cos φ) (r * Real.cos (θ - φ)))
    (hsecond : h2prime = c22 + slope⁻¹ *
      paper_two_user_induced_cost_cross_partial α β θ
        (r * Real.cos φ) (r * Real.cos (θ - φ))) :
    slope * paper_two_user_second_deriv_sign_bracket β θ φ ≤ 0 :=
  twoUser_regionscolor_param_bracket_nonpos_of_objectiveSOC_and_graphFOCDerivatives
    hα hβ hsin hNpos hsoc hfirst hsecond

/--
Lemma `regionscolor`, positive-slope endpoint: the source graph-Hessian
condition implies a nonpositive `secondderiv` bracket when the support curve
has positive slope. The source-to-graph construction remains an explicit
requirement.
-/
theorem paper_regionscolor_bracket_nonpos_of_negativeSemidefinite_of_slope_pos
    {α β θ φ r slope : ℝ}
    (hα : 0 < α)
    (hβ : 0 < β)
    (hsin : 0 < Real.sin θ)
    (hNpos : 0 < r ^ 2 * (Real.sin θ) ^ 2)
    (hneg :
      paper_negative_semidefinite_quadratic2
        (slope *
          paper_two_user_induced_cost_cross_partial α β θ
            (r * Real.cos φ) (r * Real.cos (θ - φ)))
        (-(paper_two_user_induced_cost_cross_partial α β θ
            (r * Real.cos φ) (r * Real.cos (θ - φ))))
        (slope⁻¹ *
          paper_two_user_induced_cost_cross_partial α β θ
            (r * Real.cos φ) (r * Real.cos (θ - φ))))
    (hslope : 0 < slope) :
    paper_two_user_second_deriv_sign_bracket β θ φ ≤ 0 :=
  twoUser_regionscolor_bracket_nonpos_of_negativeSemidefinite_of_slope_pos
    hα hβ hsin hNpos hneg hslope

/--
Theorem `phasetransitionformal`, finite-genre obstruction sign endpoint: above
the phase threshold, the `regionscolor` condition forces the support-curve
slope at the midpoint angle to be nonpositive.
-/
theorem paper_regionscolor_midpoint_slope_nonpos_of_phase_threshold_lt_beta
    {α β θ r slope : ℝ}
    (hα : 0 < α)
    (hβ : 0 < β)
    (hsin : 0 < Real.sin θ)
    (hden : 0 < 1 - Real.cos θ)
    (hNpos : 0 < r ^ 2 * (Real.sin θ) ^ 2)
    (hβgt : paper_two_user_phase_threshold θ < β)
    (hneg :
      paper_negative_semidefinite_quadratic2
        (slope *
          paper_two_user_induced_cost_cross_partial α β θ
            (r * Real.cos (θ / 2)) (r * Real.cos (θ - θ / 2)))
        (-(paper_two_user_induced_cost_cross_partial α β θ
            (r * Real.cos (θ / 2)) (r * Real.cos (θ - θ / 2))))
        (slope⁻¹ *
          paper_two_user_induced_cost_cross_partial α β θ
            (r * Real.cos (θ / 2)) (r * Real.cos (θ - θ / 2)))) :
    slope ≤ 0 :=
  twoUser_regionscolor_midpoint_slope_nonpos_of_phaseThreshold_lt_beta
    hα hβ hsin hden hNpos hβgt hneg

/--
Theorem `phasetransitionformal`, uniqueness-regime slope endpoint: below the
phase threshold and away from the orthogonal boundary, `regionscolor` forces
the local support-curve slope to be nonnegative.
-/
theorem paper_regionscolor_slope_nonneg_of_beta_lt_phase_threshold_and_angle_mem_Icc_lt_half_pi
    {α β θ φ r slope : ℝ}
    (hα : 0 < α)
    (hβ : 0 < β)
    (hsin : 0 < Real.sin θ)
    (hden : 0 < 1 - Real.cos θ)
    (hNpos : 0 < r ^ 2 * (Real.sin θ) ^ 2)
    (hβlt : β < paper_two_user_phase_threshold θ)
    (hθ_nonneg : 0 ≤ θ)
    (hθ_lt_half_pi : θ < Real.pi / 2)
    (hφ_nonneg : 0 ≤ φ)
    (hφ_leθ : φ ≤ θ)
    (hneg :
      paper_negative_semidefinite_quadratic2
        (slope *
          paper_two_user_induced_cost_cross_partial α β θ
            (r * Real.cos φ) (r * Real.cos (θ - φ)))
        (-(paper_two_user_induced_cost_cross_partial α β θ
            (r * Real.cos φ) (r * Real.cos (θ - φ))))
        (slope⁻¹ *
          paper_two_user_induced_cost_cross_partial α β θ
            (r * Real.cos φ) (r * Real.cos (θ - φ)))) :
    0 ≤ slope :=
  twoUser_regionscolor_slope_nonneg_of_beta_lt_phaseThreshold_and_angle_mem_Icc_lt_half_pi
    hα hβ hsin hden hNpos hβlt hθ_nonneg hθ_lt_half_pi hφ_nonneg hφ_leθ hneg

/-- Lemma `standardbasismax`, source objective for the standard-basis closed forms. -/
noncomputable abbrev paper_standard_basis_objective
    (β z1 z2 : ℝ) : ℝ :=
  standardBasisObjective β z1 z2

/--
Lemma `standardbasismax`, upper bound: for `β > 2`, the source objective is
at most `1 - 2/β` for all nonnegative realized values.  The proof uses
Young's inequality after reducing the two-coordinate objective to the radial
quantity `z_1^2 + z_2^2`.
-/
theorem paper_standard_basis_objective_le
    {β z1 z2 : ℝ} (hβ : 2 < β) :
    paper_standard_basis_objective β z1 z2 ≤ 1 - 2 / β :=
  standardBasisObjective_le hβ

/--
Lemma `standardbasismax`, equality case: every point on the source radius
`z_1^2+z_2^2=(2/β)^(2/β)` attains the objective value `1 - 2/β`.
-/
theorem paper_standard_basis_objective_eq_of_radius
    {β z1 z2 : ℝ} (hβ : 2 < β)
    (hradius : z1 ^ 2 + z2 ^ 2 = (2 / β) ^ (2 / β)) :
    paper_standard_basis_objective β z1 z2 = 1 - 2 / β :=
  standardBasisObjective_eq_of_radius hβ hradius

theorem paper_standard_basis_objective_le_of_radius
    {β z1 z2 w1 w2 : ℝ} (hβ : 2 < β)
    (hradius : z1 ^ 2 + z2 ^ 2 = (2 / β) ^ (2 / β)) :
    paper_standard_basis_objective β w1 w2 ≤
      paper_standard_basis_objective β z1 z2 :=
  standardBasisObjective_le_of_radius hβ hradius

theorem paper_standard_basis_objective_le_beta_two (z1 z2 : ℝ) :
    paper_standard_basis_objective 2 z1 z2 ≤ 0 :=
  standardBasisObjective_le_beta_two z1 z2

theorem paper_standard_basis_objective_eq_beta_two_of_radius
    {z1 z2 : ℝ} (hradius : z1 ^ 2 + z2 ^ 2 = 1) :
    paper_standard_basis_objective 2 z1 z2 = 0 :=
  standardBasisObjective_eq_beta_two_of_radius hradius

theorem paper_standard_basis_objective_beta_two_le_of_radius
    {z1 z2 w1 w2 : ℝ} (hradius : z1 ^ 2 + z2 ^ 2 = 1) :
    paper_standard_basis_objective 2 w1 w2 ≤
      paper_standard_basis_objective 2 z1 z2 :=
  standardBasisObjective_beta_two_le_of_radius hradius

/--
Lemma `standardbasismax`, source theorem form: for `β ≥ 2`, any point on the
radius `z_1^2+z_2^2=(2/β)^(2/β)` maximizes the standard-basis objective.
-/
theorem paper_standard_basis_objective_le_of_radius_two_le
    {β z1 z2 w1 w2 : ℝ} (hβ : 2 ≤ β)
    (hradius : z1 ^ 2 + z2 ^ 2 = (2 / β) ^ (2 / β)) :
    paper_standard_basis_objective β w1 w2 ≤
      paper_standard_basis_objective β z1 z2 :=
  standardBasisObjective_le_of_radius_two_le hβ hradius

/--
Proposition `Ptwo`, C1 maximizer step: for `β ≥ 2`, every point on the
source's displayed quarter-circle support maximizes the reparametrized payoff
objective.
-/
theorem paper_proposition_Ptwo_standard_basis_c1_maximizer_on_source_circle
    {β θ w1 w2 : ℝ} (hβ : 2 ≤ β)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paper_standard_basis_objective β w1 w2 ≤
      paper_standard_basis_objective β
        ((2 / β) ^ (1 / β) * Real.cos θ)
        ((2 / β) ^ (1 / β) * Real.sin θ) :=
  propositionPtwo_standardBasis_c1_maximizer_on_source_circle hβ hθ

/--
Proposition `Ptwo`, density validity substep: its displayed angle density is
nonnegative on the source interval `[0, pi / 2]`.
-/
theorem paper_proposition_Ptwo_angle_density_nonnegative_on_source_interval
    {theta : ℝ} (htheta : theta ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ 2 * Real.cos theta * Real.sin theta :=
  propositionPtwo_angleDensity_nonneg_on_source_interval htheta

/--
Proposition `Ptwo`, density validity substep: its displayed angle density has
interval integral one. The construction of the corresponding angle law is
exposed separately below; this theorem does not establish C3 or equilibrium.
-/
theorem paper_proposition_Ptwo_angle_density_interval_integral_eq_one :
    ∫ theta in (0 : ℝ)..Real.pi / 2, 2 * Real.cos theta * Real.sin theta = 1 :=
  propositionPtwo_angleDensity_intervalIntegral_eq_one

/--
Proposition `Ptwo`, angle-law clause: the primitive source angle sampler has
exactly the displayed density `2 cos(theta) sin(theta)` on `[0, pi / 2]`,
extended by zero outside that interval. This is a direct measure equality, not
a C3 or equilibrium conclusion.
-/
theorem paper_proposition_Ptwo_source_angle_measure_eq_density :
    pTwoSourceAngleMeasure = pTwoSourceAngleDensityMeasure :=
  pTwoSourceAngleMeasure_eq_densityMeasure

/--
Proposition `Ptwo`, radius-angle construction: for the source regime
`beta >= 2`, the concrete quarter-circle measure is the angle-density law
pushed through `(r cos(theta), r sin(theta))`. This does not assert C3 or
equilibrium.
-/
theorem paper_proposition_Ptwo_source_circle_measure_eq_angle_density_map
    {beta : ℝ} (_hbeta : 2 ≤ beta) :
    pTwoSourceCircleMeasure beta =
      MeasureTheory.Measure.map (pTwoSourceCircleFromAngle beta) pTwoSourceAngleDensityMeasure :=
  pTwoSourceCircleMeasure_eq_densityAngleMeasure_map beta

/--
Proposition `Ptwo`, C3 source-model component: the concrete content law for
the two standard-basis users is a probability measure.
-/
theorem paper_proposition_Ptwo_source_content_measure_is_probability
    (beta : ℝ) :
    MeasureTheory.IsProbabilityMeasure (pTwoSourceContentMeasure beta) :=
  pTwoSourceContentMeasure_isProbabilityMeasure beta

/--
Proposition `Ptwo`, C3 source-domain component: in the source regime
`beta >= 2`, the concrete content law is almost everywhere nonnegative.
-/
theorem paper_proposition_Ptwo_source_content_measure_ae_nonnegative
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    ∀ᵐ p ∂pTwoSourceContentMeasure beta, NonnegativeContent p :=
  pTwoSourceContentMeasure_ae_nonnegative hbeta

/--
Proposition `Ptwo`, C3 transport component: scoring the concrete content law
against the two actual standard-basis users has exactly the constructed
coordinate law. This direct equality does not package C3 or assert equilibrium.
-/
theorem paper_proposition_Ptwo_c3_standard_basis_value_law
    {beta : ℝ} (_hbeta : 2 ≤ beta) :
    MeasureTheory.Measure.map pTwoStandardBasisValueMap (pTwoSourceContentMeasure beta) =
      pTwoSourceCircleMeasure beta :=
  pTwoStandardBasisValueMap_map_contentMeasure beta

/--
Proposition `Ptwo`, tie-null payoff premise: every fixed inferred-value level
has zero mass under the concrete source content law. This discharges the
uniform-tie caveat in the source's CDF payoff calculation; it is not a C1--C3
or equilibrium conclusion.
-/
theorem paper_proposition_Ptwo_score_level_has_zero_mass
    {beta : ℝ} (hbeta : 2 ≤ beta) (i : Fin 2) (z : ℝ) :
    pTwoSourceContentMeasure beta
      {q : Content 2 | paper_inferred_user_value (pTwoStandardBasisUsers i) q = z} = 0 :=
  pTwoSourceContentMeasure_score_level_eq_zero hbeta i z

/--
Proposition `Ptwo`, normal-form payoff calculation: for the concrete P=2
candidate, the actual uniform-tie assignment payoff against an arbitrary pure
content action is the sum of the two source marginal CDF values. The tie-null
premise is proved separately above; this theorem does not assert C1--C3 or a
mixed Nash equilibrium.
-/
theorem paper_proposition_Ptwo_expected_users_won_eq_source_marginal_cdf_sum
    {beta : ℝ} (hbeta : 2 ≤ beta) (p : Content 2) :
    ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers (0 : Fin 2) p
        (pTwoSourceContentMeasure beta) =
      pTwoSourceMarginalCdf beta
          (paper_inferred_user_value (pTwoStandardBasisUsers 0) p) +
        pTwoSourceMarginalCdf beta
          (paper_inferred_user_value (pTwoStandardBasisUsers 1) p) :=
  pTwoSourceContentMeasure_expectedUsersWon_eq_sourceMarginalCdfSum hbeta p

/--
Proposition `Ptwo`, normal-form payoff calculation at either producer index:
the actual uniform-tie assignment payoff against an arbitrary pure content
action is the source sum of marginal CDF values. The proof separately uses the
other coordinate of the product profile in each focal case.
-/
theorem paper_proposition_Ptwo_expected_users_won_at_each_focal_eq_source_marginal_cdf_sum
    {beta : ℝ} (hbeta : 2 ≤ beta) (j : Fin 2) (p : Content 2) :
    ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers j p
        (pTwoSourceContentMeasure beta) =
      pTwoSourceMarginalCdf beta
          (paper_inferred_user_value (pTwoStandardBasisUsers 0) p) +
        pTwoSourceMarginalCdf beta
          (paper_inferred_user_value (pTwoStandardBasisUsers 1) p) :=
  pTwoSourceContentMeasure_expectedUsersWonAtFocal_eq_sourceMarginalCdfSum
    hbeta j p

/--
Proposition `Ptwo`, source-domain payoff reduction: for a nonnegative content
action, the actual tie-aware mixed payoff equals the source standard-basis
objective. The nonnegative premise is part of the source action space.
-/
theorem paper_proposition_Ptwo_nonnegative_pure_payoff_eq_standard_basis_objective
    {beta : ℝ} (hbeta : 2 ≤ beta) (p : Content 2)
    (hp : NonnegativeContent p) :
    SourceMixedPurePayoff
      (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers (0 : Fin 2))
      (normRpowCost (SourceNorm.l2 2) beta) p
      (pTwoSourceContentMeasure beta) =
    paper_standard_basis_objective beta
      (paper_inferred_user_value (pTwoStandardBasisUsers 0) p)
      (paper_inferred_user_value (pTwoStandardBasisUsers 1) p) :=
  pTwoSourceContentMeasure_sourceMixedPurePayoff_eq_standardBasisObjective hbeta p hp

/--
Proposition `Ptwo`, source-domain no-deviation component: every nonnegative
pure content action has payoff at most `1 - 2 / beta` against the concrete
candidate. This does not assert a mixed Nash equilibrium.
-/
theorem paper_proposition_Ptwo_nonnegative_pure_payoff_le_equilibrium_value
    {beta : ℝ} (hbeta : 2 ≤ beta) (p : Content 2)
    (hp : NonnegativeContent p) :
    SourceMixedPurePayoff
      (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers (0 : Fin 2))
      (normRpowCost (SourceNorm.l2 2) beta) p
      (pTwoSourceContentMeasure beta) ≤
    1 - 2 / beta :=
  pTwoSourceContentMeasure_sourceMixedPurePayoff_le_equilibriumValue hbeta p hp

/--
Proposition `Ptwo`, source-domain no-deviation component at either producer:
every nonnegative pure content action has payoff at most `1 - 2 / beta`
against the concrete candidate. The action-domain premise remains visible.
-/
theorem paper_proposition_Ptwo_nonnegative_pure_payoff_at_each_focal_le_equilibrium_value
    {beta : ℝ} (hbeta : 2 ≤ beta) (j : Fin 2) (p : Content 2)
    (hp : NonnegativeContent p) :
    SourceMixedPurePayoff
      (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers j)
      (normRpowCost (SourceNorm.l2 2) beta) p
      (pTwoSourceContentMeasure beta) ≤
    1 - 2 / beta :=
  pTwoSourceContentMeasure_sourceMixedPurePayoffAtFocal_le_equilibriumValue
    hbeta j p hp

/--
Proposition `Ptwo`, source-circle payoff component: every action explicitly
encoded by a point on the literal source quarter-circle attains `1 - 2 / beta`.
This is not yet a statement about the topological support of the content law.
-/
theorem paper_proposition_Ptwo_source_circle_action_payoff_eq_equilibrium_value
    {beta : ℝ} (hbeta : 2 ≤ beta) (z : ℝ × ℝ)
    (hz : z ∈ pTwoSourceCircleSupportSet beta) :
    SourceMixedPurePayoff
      (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers (0 : Fin 2))
      (normRpowCost (SourceNorm.l2 2) beta) (pTwoContentOfCoordinates z)
      (pTwoSourceContentMeasure beta) =
    1 - 2 / beta :=
  pTwoContentOfCoordinates_sourceMixedPurePayoff_eq_equilibriumValue_on_sourceCircle
    hbeta z hz

/--
Proposition `Ptwo`, C2/C3 support consequence: the actual standard-basis value
law of the concrete content measure has exactly the literal source circle as
its topological support. This is support of the realized-value variable, not
of the content measure.
-/
theorem paper_proposition_Ptwo_realized_value_law_support_eq_source_circle
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    (MeasureTheory.Measure.map pTwoStandardBasisValueMap
      (pTwoSourceContentMeasure beta)).support =
      pTwoSourceCircleSupportSet beta :=
  pTwoStandardBasisValueMap_contentMeasure_support_eq_sourceCircle hbeta

/--
Proposition `Ptwo`, concrete sampling consequence: almost every content draw
has its standard-basis value vector on the literal source circle. This is an
a.e. law statement, not a topological support claim for content actions.
-/
theorem paper_proposition_Ptwo_source_content_measure_ae_value_on_source_circle
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    ∀ᵐ p ∂pTwoSourceContentMeasure beta,
      pTwoStandardBasisValueMap p ∈ pTwoSourceCircleSupportSet beta :=
  pTwoSourceContentMeasure_ae_standardBasisValue_on_sourceCircle hbeta

/--
Proposition `Ptwo`, mixed-payoff component: almost every pure content action
drawn from the candidate attains `1 - 2 / beta`. Combined with the separate
source-domain no-deviation inequality, this is not itself an equilibrium
claim.
-/
theorem paper_proposition_Ptwo_source_content_measure_ae_pure_payoff_eq_equilibrium_value
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    ∀ᵐ p ∂pTwoSourceContentMeasure beta,
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers (0 : Fin 2))
        (normRpowCost (SourceNorm.l2 2) beta) p
        (pTwoSourceContentMeasure beta) =
      1 - 2 / beta :=
  pTwoSourceContentMeasure_ae_sourceMixedPurePayoff_eq_equilibriumValue hbeta

/--
Corollary `2usersprofit`: the concrete P=2 equilibrium has the source
expected profit `1 - 2 / beta`.  The integral is over the focal producer's
content draw, after the other producer's draw and uniform recommendation ties
have already been integrated into `SourceMixedPurePayoff`.
-/
theorem paper_corollary_2usersprofit_pTwo_equilibrium_payoff
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    ∫ p, SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers (0 : Fin 2))
        (normRpowCost (SourceNorm.l2 2) beta) p
        (pTwoSourceContentMeasure beta) ∂pTwoSourceContentMeasure beta =
      1 - 2 / beta :=
  pTwoSourceContentMeasure_integral_sourceMixedPurePayoff_eq_equilibriumValue hbeta

/--
Proposition `Ptwo`, source-feasibility consequence: every topological-support
action of the concrete content measure is nonnegative. This is support
inclusion, not an equality description of content support.
-/
theorem paper_proposition_Ptwo_source_content_measure_support_subset_nonnegative
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    (pTwoSourceContentMeasure beta).support ⊆
      {p : Content 2 | NonnegativeContent p} :=
  pTwoSourceContentMeasure_support_subset_nonnegative hbeta

/--
Proposition `Ptwo`, support transport: every support action of the concrete
content measure has standard-basis values on the literal source circle. This
uses continuity of the score map and the exact realized-value support law.
-/
theorem paper_proposition_Ptwo_support_action_value_on_source_circle
    {beta : ℝ} (hbeta : 2 ≤ beta) {p : Content 2}
    (hp : p ∈ (pTwoSourceContentMeasure beta).support) :
    pTwoStandardBasisValueMap p ∈ pTwoSourceCircleSupportSet beta :=
  pTwoStandardBasisValueMap_mem_sourceCircle_of_mem_contentMeasure_support hbeta hp

/--
Proposition `Ptwo`, focal support-action payoff: every support action of the
candidate attains `1 - 2 / beta` against the other symmetric draw. This does
not yet assert the corresponding statement for the other focal index.
-/
theorem paper_proposition_Ptwo_support_action_pure_payoff_eq_equilibrium_value
    {beta : ℝ} (hbeta : 2 ≤ beta) (p : Content 2)
    (hp : p ∈ (pTwoSourceContentMeasure beta).support) :
    SourceMixedPurePayoff
      (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers (0 : Fin 2))
      (normRpowCost (SourceNorm.l2 2) beta) p
      (pTwoSourceContentMeasure beta) =
    1 - 2 / beta :=
  pTwoSourceContentMeasure_sourceMixedPurePayoff_eq_equilibriumValue_of_mem_support
    hbeta p hp

/--
Proposition `Ptwo`, focal support-action maximizer: every candidate support
action weakly beats every nonnegative pure deviation. The source action-domain
premise remains visible; this is not a full symmetric mixed-Nash conclusion.
-/
theorem paper_proposition_Ptwo_support_action_payoff_is_maximal
    {beta : ℝ} (hbeta : 2 ≤ beta) (p : Content 2)
    (hp : p ∈ (pTwoSourceContentMeasure beta).support) :
    ∀ q : Content 2, NonnegativeContent q →
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers (0 : Fin 2))
        (normRpowCost (SourceNorm.l2 2) beta) q
        (pTwoSourceContentMeasure beta) ≤
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers (0 : Fin 2))
        (normRpowCost (SourceNorm.l2 2) beta) p
        (pTwoSourceContentMeasure beta) :=
  pTwoSourceContentMeasure_support_action_payoff_is_maximal hbeta p hp

/--
Proposition `Ptwo`, source mixed-Nash support-action condition: for either
producer index, every candidate support action weakly beats every nonnegative
pure deviation. This is the source definition's behavioral clause stated
directly; it does not package an equilibrium conclusion.
-/
theorem paper_proposition_Ptwo_support_action_payoff_is_maximal_at_each_focal
    {beta : ℝ} (hbeta : 2 ≤ beta) (j : Fin 2) (p : Content 2)
    (hp : p ∈ (pTwoSourceContentMeasure beta).support) :
    ∀ q : Content 2, NonnegativeContent q →
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers j)
        (normRpowCost (SourceNorm.l2 2) beta) q
        (pTwoSourceContentMeasure beta) ≤
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers j)
        (normRpowCost (SourceNorm.l2 2) beta) p
        (pTwoSourceContentMeasure beta) :=
  pTwoSourceContentMeasure_support_action_payoff_is_maximal_at_each_focal
    hbeta j p hp

/--
Proposition `Ptwo`, source coordinate-density sign: the quadratic-CDF
candidate has a nonnegative density on its displayed support interval.
-/
theorem paper_proposition_Ptwo_coordinate_density_nonnegative_on_source_interval
    {beta z : ℝ} (hbeta : 2 ≤ beta)
    (hz : z ∈ Set.Icc (0 : ℝ) ((2 / beta) ^ (1 / beta))) :
    0 ≤ 2 * (2 / beta) ^ (-(2 / beta)) * z :=
  propositionPtwo_coordinateDensity_nonneg_on_source_interval hbeta hz

/--
Proposition `Ptwo`, source coordinate-density calculation: integrating the
candidate density gives the displayed quadratic CDF value in `[0, 1]` on the
source support. It does not assert a coordinate pushforward law.
-/
theorem paper_proposition_Ptwo_coordinate_density_integral_eq_candidate_cdf
    {beta z : ℝ} (hbeta : 2 ≤ beta)
    (hz : z ∈ Set.Icc (0 : ℝ) ((2 / beta) ^ (1 / beta))) :
    ∫ t in (0 : ℝ)..z, 2 * (2 / beta) ^ (-(2 / beta)) * t =
      (2 / beta) ^ (-(2 / beta)) * z ^ 2 ∧
        (2 / beta) ^ (-(2 / beta)) * z ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
  propositionPtwo_coordinateDensity_integral_eq_candidateCdf hbeta hz

/--
Proposition `Ptwo`, source coordinate-density normalization: the candidate
density has total interval integral one over the displayed support. This does
not construct the coordinate marginal measure.
-/
theorem paper_proposition_Ptwo_coordinate_density_interval_integral_eq_one
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    ∫ z in (0 : ℝ)..((2 / beta) ^ (1 / beta)),
        2 * (2 / beta) ^ (-(2 / beta)) * z = 1 :=
  propositionPtwo_coordinateDensity_intervalIntegral_eq_one hbeta

/--
Proposition `Ptwo`, interior change-of-variables calculation: the source
coordinate-density formula equals the angle density divided by the positive
coordinate Jacobian. This is not a C2 pushforward assertion.
-/
theorem paper_proposition_Ptwo_coordinate_density_jacobian_quotient_on_source_angle
    {beta theta : ℝ} (hbeta : 2 ≤ beta)
    (htheta : theta ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    2 * (2 / beta) ^ (-(2 / beta)) *
        ((2 / beta) ^ (1 / beta) * Real.sin theta) =
      (2 * Real.sin theta * Real.cos theta) /
        ((2 / beta) ^ (1 / beta) * Real.cos theta) :=
  propositionPtwo_coordinateDensity_jacobian_quotient_on_source_angle hbeta htheta

/--
Proposition `Ptwo`, construction substep: the concrete quarter-circle sampler
induces a probability measure. This does not assert equilibrium or C2/C3.
-/
theorem paper_proposition_Ptwo_source_circle_measure_is_probability
    (beta : ℝ) :
    MeasureTheory.IsProbabilityMeasure (pTwoSourceCircleMeasure beta) :=
  pTwoSourceCircleMeasure_isProbabilityMeasure beta

/--
Proposition `Ptwo`, construction substep: for `beta >= 2`, the concrete
quarter-circle measure lies almost everywhere on the literal nonnegative
source circle. The separate support theorem upgrades this a.e. fact to the
source's topological-support equality.
-/
theorem paper_proposition_Ptwo_source_circle_measure_ae_on_literal_circle
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    ∀ᵐ z ∂pTwoSourceCircleMeasure beta,
      0 ≤ z.1 ∧ 0 ≤ z.2 ∧
        z.1 ^ 2 + z.2 ^ 2 = (2 / beta) ^ (2 / beta) :=
  pTwoSourceCircleMeasure_ae_on_literal_circle hbeta

/--
Proposition `Ptwo`, C2 support substep: the concrete quarter-circle measure
has exactly the literal source circle as its topological support. This does
not establish C3 or assemble an equilibrium.
-/
theorem paper_proposition_Ptwo_source_circle_measure_support_eq_source_circle
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    (pTwoSourceCircleMeasure beta).support = pTwoSourceCircleSupportSet beta :=
  pTwoSourceCircleMeasure_support_eq_supportSet hbeta

/--
Proposition `Ptwo`, C2 marginal substep: the constructed first coordinate has
the source quadratic CDF formula on the displayed support interval. This does
not itself supply the off-support branches; the full source-CDF bridge is
exposed separately below.
-/
theorem paper_proposition_Ptwo_source_circle_measure_first_coordinate_cdf_on_source_interval
    {beta z : ℝ} (hbeta : 2 ≤ beta)
    (hz : z ∈ Set.Icc (0 : ℝ) ((2 / beta) ^ (1 / beta))) :
    pTwoSourceCircleMeasure beta {point : ℝ × ℝ | point.1 ≤ z} =
      ENNReal.ofReal ((2 / beta) ^ (-(2 / beta)) * z ^ 2) :=
  pTwoSourceCircleMeasure_first_cdf_on_source_interval hbeta hz

/--
Proposition `Ptwo`, C2 marginal substep: the constructed second coordinate
has the source quadratic CDF formula on the displayed support interval. This
does not itself supply the off-support branches; the full source-CDF bridge is
exposed separately below.
-/
theorem paper_proposition_Ptwo_source_circle_measure_second_coordinate_cdf_on_source_interval
    {beta z : ℝ} (hbeta : 2 ≤ beta)
    (hz : z ∈ Set.Icc (0 : ℝ) ((2 / beta) ^ (1 / beta))) :
    pTwoSourceCircleMeasure beta {point : ℝ × ℝ | point.2 ≤ z} =
      ENNReal.ofReal ((2 / beta) ^ (-(2 / beta)) * z ^ 2) :=
  pTwoSourceCircleMeasure_second_cdf_on_source_interval hbeta hz

/--
Proposition `Ptwo`, coordinate-measure substep: the constructed first
coordinate has its full CDF, including the zero and one branches outside the
displayed interval. Topological support equality is proved separately; this
does not establish C3.
-/
theorem paper_proposition_Ptwo_source_circle_measure_first_coordinate_full_cdf
    {beta z : ℝ} (hbeta : 2 ≤ beta) :
    pTwoSourceCircleMeasure beta {point : ℝ × ℝ | point.1 ≤ z} =
      ENNReal.ofReal (pTwoSourceCircleFullCoordinateCdf beta z) :=
  pTwoSourceCircleMeasure_first_full_cdf hbeta

/--
Proposition `Ptwo`, coordinate-measure substep: the constructed second
coordinate has its full CDF, including the zero and one branches outside the
displayed interval. Topological support equality is proved separately; this
does not establish C3.
-/
theorem paper_proposition_Ptwo_source_circle_measure_second_coordinate_full_cdf
    {beta z : ℝ} (hbeta : 2 ≤ beta) :
    pTwoSourceCircleMeasure beta {point : ℝ × ℝ | point.2 ≤ z} =
      ENNReal.ofReal (pTwoSourceCircleFullCoordinateCdf beta z) :=
  pTwoSourceCircleMeasure_second_full_cdf hbeta

/--
Proposition `Ptwo`, C2 first-coordinate clause: the constructed measure has
the literal source marginal CDF with the explicit `P = 2` exponent. This is a
direct component theorem, not a C2 package or equilibrium conclusion.
-/
theorem paper_proposition_Ptwo_c2_first_coordinate_source_cdf
    {beta z : ℝ} (hbeta : 2 ≤ beta) :
    pTwoSourceCircleMeasure beta {point : ℝ × ℝ | point.1 ≤ z} =
      ENNReal.ofReal ((pTwoSourceMarginalCdf beta z) ^ (1 / ((2 : ℝ) - 1))) :=
  pTwoSourceCircleMeasure_first_cdf_eq_sourceMarginalCdf hbeta

/--
Proposition `Ptwo`, C2 second-coordinate clause: the constructed measure has
the literal source marginal CDF with the explicit `P = 2` exponent. This is a
direct component theorem, not a C2 package or equilibrium conclusion.
-/
theorem paper_proposition_Ptwo_c2_second_coordinate_source_cdf
    {beta z : ℝ} (hbeta : 2 ≤ beta) :
    pTwoSourceCircleMeasure beta {point : ℝ × ℝ | point.2 ≤ z} =
      ENNReal.ofReal ((pTwoSourceMarginalCdf beta z) ^ (1 / ((2 : ℝ) - 1))) :=
  pTwoSourceCircleMeasure_second_cdf_eq_sourceMarginalCdf hbeta

/--
Proposition `finiteP`, corrected C1 maximizer step: for `P ≥ 2`, every point
on the source's displayed support curve maximizes the reparametrized payoff
objective at `β = 2`.
-/
theorem paper_proposition_finiteP_standard_basis_c1_maximizer_on_source_curve
    {P : ℕ} (hP : 2 ≤ P) {x w1 w2 : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    paper_standard_basis_objective 2 w1 w2 ≤
      paper_standard_basis_objective 2 x
        ((1 - x ^ (2 / ((P : ℝ) - 1))) ^ (((P : ℝ) - 1) / 2)) :=
  propositionFiniteP_standardBasis_c1_maximizer_on_source_curve hP hx

/--
Proposition `finiteP`, literal construction substep: the concrete unit-
interval sampler lies on the displayed source curve for every `P ≥ 2`. This is
not an exact support or CDF assertion.
-/
theorem paper_proposition_finiteP_source_curve_sampler_on_literal_curve
    {P : ℕ} (hP : 2 ≤ P) (u : ↑unitInterval) :
    finitePSourceCurveSample P u ∈ finitePSourceCurveSupportSet P :=
  finitePSourceCurveSample_mem_source_curve hP u

/--
Proposition `finiteP`, literal marginal-law clause: the first coordinate of
the constructed source curve has the displayed zero-extended `min` CDF. This
is a direct CDF equality, not an exact-support or equilibrium conclusion.
-/
theorem paper_proposition_finiteP_first_coordinate_source_cdf
    {P : ℕ} (hP : 2 ≤ P) (z : ℝ) :
    finitePSourceCurveMeasure P {point : ℝ × ℝ | point.1 ≤ z} =
      ENNReal.ofReal (if z < 0 then 0 else min 1 (z ^ (2 / ((P : ℝ) - 1)))) :=
  finitePSourceCurveMeasure_first_cdf_eq_sourceMarginalCdf hP z

/--
Proposition `finiteP`, symmetric coordinate-law clause: the second coordinate
has the same zero-extended source CDF. This does not claim the remaining C2
topological-support equality.
-/
theorem paper_proposition_finiteP_second_coordinate_source_cdf
    {P : ℕ} (hP : 2 ≤ P) (z : ℝ) :
    finitePSourceCurveMeasure P {point : ℝ × ℝ | point.2 ≤ z} =
      ENNReal.ofReal (if z < 0 then 0 else min 1 (z ^ (2 / ((P : ℝ) - 1)))) :=
  finitePSourceCurveMeasure_second_cdf_eq_sourceMarginalCdf hP z

/--
Proposition `finiteP`, C2 first-coordinate clause: the constructed law has
the required `(P - 1)`-root of the beta-two base CDF. This direct equality
does not package C2 or assert an equilibrium.
-/
theorem paper_proposition_finiteP_c2_first_coordinate_root_cdf
    {P : ℕ} (hP : 2 ≤ P) (z : ℝ) :
    finitePSourceCurveMeasure P {point : ℝ × ℝ | point.1 ≤ z} =
      ENNReal.ofReal ((finitePSourceBaseCdf z) ^ (1 / ((P : ℝ) - 1))) :=
  finitePSourceCurveMeasure_first_cdf_eq_sourceC2Root hP z

/--
Proposition `finiteP`, C2 second-coordinate clause: the constructed law has
the required `(P - 1)`-root of the beta-two base CDF. Exact support remains a
separate proof obligation.
-/
theorem paper_proposition_finiteP_c2_second_coordinate_root_cdf
    {P : ℕ} (hP : 2 ≤ P) (z : ℝ) :
    finitePSourceCurveMeasure P {point : ℝ × ℝ | point.2 ≤ z} =
      ENNReal.ofReal ((finitePSourceBaseCdf z) ^ (1 / ((P : ℝ) - 1))) :=
  finitePSourceCurveMeasure_second_cdf_eq_sourceC2Root hP z

/--
Proposition `finiteP`, C2 support clause: the constructed coordinate law has
exactly the literal source curve as topological support. This is support of the
realized-value variable, not of the content-action measure.
-/
theorem paper_proposition_finiteP_c2_coordinate_law_support_eq_source_curve
    {P : ℕ} (hP : 2 ≤ P) :
    (finitePSourceCurveMeasure P).support = finitePSourceCurveSupportSet P :=
  finitePSourceCurveMeasure_support_eq_source_curve hP

/--
Proposition `finiteP`, source-strategy construction substep: the concrete
content law is a probability measure for the source producer range. Its C2
facts and the C3 score-law transport are exposed as separate direct rows.
-/
theorem paper_proposition_finiteP_source_content_measure_is_probability
    {P : ℕ} (hP : 2 ≤ P) :
    MeasureTheory.IsProbabilityMeasure (finitePSourceContentMeasure P) :=
  by
    have _ : 1 < P := lt_of_lt_of_le (by norm_num) hP
    exact finitePSourceContentMeasure_isProbabilityMeasure P

/--
Proposition `finiteP`, source-feasibility substep: every support action of the
concrete content law is nonnegative. This concerns the content action space,
not C2 support of the realized-value random variable.
-/
theorem paper_proposition_finiteP_source_content_measure_support_subset_nonnegative
    {P : ℕ} (hP : 2 ≤ P) :
    (finitePSourceContentMeasure P).support ⊆
      {p : Content 2 | NonnegativeContent p} :=
  by
    have _ : 1 < P := lt_of_lt_of_le (by norm_num) hP
    exact finitePSourceContentMeasure_support_subset_nonnegative P

/--
Proposition `finiteP`, C3 transport component: scoring the concrete content
law against the two actual standard-basis users gives exactly the constructed
finiteP coordinate law. This direct equality does not package C2/C3 or assert
an equilibrium.
-/
theorem paper_proposition_finiteP_c3_standard_basis_value_law
    {P : ℕ} (hP : 2 ≤ P) :
    MeasureTheory.Measure.map pTwoStandardBasisValueMap (finitePSourceContentMeasure P) =
      finitePSourceCurveMeasure P :=
  by
    have _ : 1 < P := lt_of_lt_of_le (by norm_num) hP
    exact finitePStandardBasisValueMap_map_contentMeasure P

/--
Proposition `finiteP`, C2/C3 transport consequence: the actual standard-basis
value law of the concrete content measure has the literal source curve as its
topological support. This direct equality does not package C2/C3 or assert an
equilibrium.
-/
theorem paper_proposition_finiteP_realized_value_law_support_eq_source_curve
    {P : ℕ} (hP : 2 ≤ P) :
    (MeasureTheory.Measure.map pTwoStandardBasisValueMap
      (finitePSourceContentMeasure P)).support = finitePSourceCurveSupportSet P :=
  finitePStandardBasisValueMap_contentMeasure_support_eq_source_curve hP

/--
Lemma `necessarysuff`, tie-aware payoff reduction: under explicit measurable
score laws and zero mass at every focal score level, the actual product
integral of the paper's uniform tie rule is the sum of independent strict-score
masses. This is not a C1/C2/C3 or equilibrium conclusion.
-/
theorem paper_necessarysuff_tie_aware_expected_users_won_eq_strict_score_mass
    {D N P : ℕ} {users : Fin N → Content D} {j : Fin P}
    {μ : MeasureTheory.Measure (Content D)} [MeasureTheory.IsProbabilityMeasure μ]
    (p : Content D)
    (hmeas_score : ∀ i : Fin N, Measurable (fun q : Content D => score (users i) q))
    (hno_atom : ∀ (i : Fin N) (z : ℝ),
      μ {q : Content D | score (users i) q = z} = 0) :
    ExpectedUsersWonAgainstSymmetricMixed users j p μ =
      ∑ i : Fin N,
        (μ.real {q : Content D | score (users i) q < score (users i) p}) ^ (P - 1) :=
  expectedUsersWonAgainstSymmetricMixed_eq_sum_strictScoreMass p hmeas_score hno_atom

/--
Structural score-law prerequisite used in the source statements of
`supportrestriction` and `phasetransitionformal`: an explicitly
Lebesgue-absolutely-continuous score pushforward has zero mass at every fixed
score level. This is not a support, C1/C2/C3, or equilibrium conclusion.
-/
theorem paper_structural_score_level_has_zero_mass_of_absolutely_continuous_score_law
    {D : ℕ} {u : Content D} {μ : MeasureTheory.Measure (Content D)}
    (hmeas_score : Measurable (fun q : Content D => score u q))
    (hscore_ac : MeasureTheory.Measure.map (fun q : Content D => score u q) μ ≪
      MeasureTheory.volume)
    (z : ℝ) :
    μ {q : Content D | score u q = z} = 0 :=
  score_level_measure_eq_zero_of_score_law_absolutelyContinuous
    hmeas_score hscore_ac z

/--
Structural CDF step: the same source score-law premise makes the strict and
weak score events equal in mass. This does not infer continuity, support, or
equilibrium facts beyond the visible absolute-continuity premise.
-/
theorem paper_structural_strict_score_mass_eq_weak_score_mass_of_absolutely_continuous_score_law
    {D : ℕ} {u : Content D} {μ : MeasureTheory.Measure (Content D)}
    (hmeas_score : Measurable (fun q : Content D => score u q))
    (hscore_ac : MeasureTheory.Measure.map (fun q : Content D => score u q) μ ≪
      MeasureTheory.volume)
    (z : ℝ) :
    μ {q : Content D | score u q < z} =
      μ {q : Content D | score u q ≤ z} :=
  score_lt_measure_eq_score_le_measure_of_score_law_absolutelyContinuous
    hmeas_score hscore_ac z

/--
Structural tie-aware payoff calculation: the source's explicit absolutely
continuous score-law premise discharges the null-tie condition in the actual
uniform-tie product integral. This direct formula does not establish the
source structural propositions or infer their other hypotheses.
-/
theorem paper_structural_tie_aware_expected_users_won_eq_strict_score_mass_of_absolutely_continuous_score_laws
    {D N P : ℕ} {users : Fin N → Content D} {j : Fin P}
    {μ : MeasureTheory.Measure (Content D)} [MeasureTheory.IsProbabilityMeasure μ]
    (p : Content D)
    (hmeas_score : ∀ i : Fin N, Measurable (fun q : Content D => score (users i) q))
    (hscore_ac : ∀ i : Fin N,
      MeasureTheory.Measure.map (fun q : Content D => score (users i) q) μ ≪
        MeasureTheory.volume) :
    ExpectedUsersWonAgainstSymmetricMixed users j p μ =
      ∑ i : Fin N,
        (μ.real {q : Content D | score (users i) q < score (users i) p}) ^ (P - 1) :=
  expectedUsersWonAgainstSymmetricMixed_eq_sum_strictScoreMass_of_scoreLaw_absolutelyContinuous
    p hmeas_score hscore_ac

/--
Structural CDF-facing payoff calculation: because the visible score-law
absolute-continuity premise eliminates score-level mass, the actual uniform-tie
product integral equals the source-style sum of weak score-CDF masses. This
does not establish either structural source proposition or its other premises.
-/
theorem paper_structural_tie_aware_expected_users_won_eq_weak_score_mass_of_absolutely_continuous_score_laws
    {D N P : ℕ} {users : Fin N → Content D} {j : Fin P}
    {μ : MeasureTheory.Measure (Content D)} [MeasureTheory.IsProbabilityMeasure μ]
    (p : Content D)
    (hmeas_score : ∀ i : Fin N, Measurable (fun q : Content D => score (users i) q))
    (hscore_ac : ∀ i : Fin N,
      MeasureTheory.Measure.map (fun q : Content D => score (users i) q) μ ≪
        MeasureTheory.volume) :
    ExpectedUsersWonAgainstSymmetricMixed users j p μ =
      ∑ i : Fin N,
        (μ.real {q : Content D | score (users i) q ≤ score (users i) p}) ^ (P - 1) :=
  expectedUsersWonAgainstSymmetricMixed_eq_sum_weakScoreMass_of_scoreLaw_absolutelyContinuous
    p hmeas_score hscore_ac

/--
Proposition `finiteP`, tie-null score component: every fixed standard-basis
score level has zero mass under the constructed content law. This is the
premise that validates replacing uniform tie shares by strict-score events.
-/
theorem paper_proposition_finiteP_standard_basis_score_level_eq_zero
    {P : ℕ} (hP : 2 ≤ P) (i : Fin 2) (z : ℝ) :
    finitePSourceContentMeasure P
      {q : Content 2 | score (pTwoStandardBasisUsers i) q = z} = 0 :=
  finitePSourceContentMeasure_score_level_eq_zero hP i z

/--
Proposition `finiteP`, strict-score C2 component: each standard-basis strict
score mass is the literal `(P - 1)`-root base CDF. The null-tie argument is
internal to the checked proof; no C2 package is introduced.
-/
theorem paper_proposition_finiteP_standard_basis_strict_score_root_cdf
    {P : ℕ} (hP : 2 ≤ P) (i : Fin 2) (z : ℝ) :
    (finitePSourceContentMeasure P).real
      {q : Content 2 | score (pTwoStandardBasisUsers i) q < z} =
      (finitePSourceBaseCdf z) ^ (1 / ((P : ℝ) - 1)) :=
  finitePSourceContentMeasure_score_lt_measureReal_eq_sourceC2Root hP i z

/--
Proposition `finiteP`, normal-form payoff component: for each focal producer,
the actual full-profile uniform-tie assignment integral is exactly the sum of
the source beta-two base CDF values.
-/
theorem paper_proposition_finiteP_tie_aware_expected_users_won_eq_base_cdf_sum
    {P : ℕ} (hP : 2 ≤ P) (j : Fin P) (p : Content 2) :
    ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers j p
      (finitePSourceContentMeasure P) =
      ∑ i : Fin 2, finitePSourceBaseCdf (score (pTwoStandardBasisUsers i) p) :=
  finitePSourceContentMeasure_expectedUsersWon_eq_sourceBaseCdfSum hP j p

/--
Proposition `finiteP`, source-domain pure-payoff component: a nonnegative
action's actual tie-aware payoff agrees with the beta-two standard-basis
objective. The action-domain premise is visible because the source permits
only nonnegative content.
-/
theorem paper_proposition_finiteP_tie_aware_pure_payoff_eq_standard_basis_objective
    {P : ℕ} (hP : 2 ≤ P) (j : Fin P) (p : Content 2)
    (hp : NonnegativeContent p) :
    SourceMixedPurePayoff
      (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers j)
      (normRpowCost (SourceNorm.l2 2) 2) p
      (finitePSourceContentMeasure P) =
    paper_standard_basis_objective 2
      (score (pTwoStandardBasisUsers 0) p)
      (score (pTwoStandardBasisUsers 1) p) :=
  finitePSourceContentMeasure_sourceMixedPurePayoff_eq_standardBasisObjective hP j p hp

/--
Proposition `finiteP`, source mixed-Nash behavioral clause: at every focal
producer, a topological-support action weakly beats every nonnegative pure
deviation. This is the source definition's direct support-action condition,
not a theorem-facing equilibrium or C1/C2/C3 package.
-/
theorem paper_proposition_finiteP_support_action_payoff_is_maximal_at_each_focal
    {P : ℕ} (hP : 2 ≤ P) (j : Fin P) (p : Content 2)
    (hp : p ∈ (finitePSourceContentMeasure P).support) :
    ∀ q : Content 2, NonnegativeContent q →
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers j)
        (normRpowCost (SourceNorm.l2 2) 2) q
        (finitePSourceContentMeasure P) ≤
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers j)
        (normRpowCost (SourceNorm.l2 2) 2) p
        (finitePSourceContentMeasure P) :=
  finitePSourceContentMeasure_support_action_payoff_is_maximal_at_each_focal
    hP j p hp

/--
The literal `infinitegenreformal` hypothesis defining its user angle as an
arccosine while requiring that angle to be negative is contradictory.
-/
theorem paper_infinite_genre_false_of_arccos_angle_neg
    {x theta_star : ℝ}
    (hangle : theta_star = Real.arccos x) (hneg : theta_star < 0) :
    False :=
  infiniteGenre_false_of_arccos_angle_neg hangle hneg

/--
The literal `infinitegenreformal` weights `alpha_1 = alpha_2 = 2` contradict
the preceding finite-genre probability normalization that their sum be one.
-/
theorem paper_infinite_genre_false_of_two_weights_eq_two_and_sum_one
    {alpha1 alpha2 : ℝ}
    (halpha1 : alpha1 = 2) (halpha2 : alpha2 = 2)
    (hsum : alpha1 + alpha2 = 1) :
    False :=
  infiniteGenre_false_of_two_weights_eq_two_and_sum_one halpha1 halpha2 hsum

/--
If two normalized genre weights are equal, each equals one half; these are the
weights compatible with the square-root CDF calculation later in the source.
-/
theorem paper_infinite_genre_equal_weight_eq_half_of_sum_one
    {alpha : ℝ} (hsum : alpha + alpha = 1) : alpha = 1 / 2 :=
  infiniteGenre_equal_weight_eq_half_of_sum_one hsum

/--
Theorem `infinitegenreformal`, cosine-power identity: the first-order
`β`-power equation for the candidate genre angle implies the closed-form
cosine-power sum used in the source verification.
-/
theorem paper_infinite_genre_cos_power_sum_eq_of_beta_powers
    {β θstar θG : ℝ}
    (hsinG : Real.sin θG ≠ 0)
    (hcosG : 0 < Real.cos θG)
    (hcosO : 0 < Real.cos (θstar - θG))
    (hbetaPowers :
      Real.sin θG * (Real.cos θG) ^ (β - 1) =
        Real.sin (θstar - θG) * (Real.cos (θstar - θG)) ^ (β - 1)) :
    (Real.cos θG) ^ β + (Real.cos (θstar - θG)) ^ β =
      Real.sin θstar * (Real.cos (θstar - θG)) ^ (β - 1) / Real.sin θG :=
  infiniteGenre_cosPower_sum_eq_of_betaPowers hsinG hcosG hcosO hbetaPowers

/-- Theorem `infinitegenreformal`, objective maximized to choose `θ_G`. -/
noncomputable abbrev paper_two_user_cos_power_sum
    (β θstar θ : ℝ) : ℝ :=
  twoUserCosPowerSum β θstar θ

/--
Two-user angular-power component at exponent two: nonnegative cosine
similarity gives a global bisector maximum. This is a direct trigonometric
component, not the paper's unresolved threshold equality.
-/
theorem paper_two_user_cos_power_sum_two_le_bisector
    {θstar θ : ℝ}
    (hcosStar : 0 ≤ Real.cos θstar) :
    paper_two_user_cos_power_sum 2 θstar θ ≤
      paper_two_user_cos_power_sum 2 θstar (θstar / 2) :=
  twoUserCosPowerSum_two_le_bisector hcosStar

/--
Corrected two-user C1 angular comparison in the fully checked low-exponent
range.  For `0 ≤ beta ≤ 2`, the angular-power sum is at most its bisector
value whenever the relevant cosine scores are nonnegative.  This is a valid
subrange of the source's intended threshold calculation, not a claim of the
unrepaired full threshold identity.
-/
theorem paper_two_user_cos_power_sum_le_bisector_of_nonnegative_cosines_of_le_two
    {β θstar θ : ℝ}
    (hβ_nonnegative : 0 ≤ β) (hβ_le_two : β ≤ 2)
    (hcosStar : 0 ≤ Real.cos θstar)
    (hcos : 0 ≤ Real.cos θ)
    (hcosOther : 0 ≤ Real.cos (θstar - θ))
    (hcosBisector : 0 ≤ Real.cos (θstar / 2)) :
    paper_two_user_cos_power_sum β θstar θ ≤
      paper_two_user_cos_power_sum β θstar (θstar / 2) :=
  twoUserCosPowerSum_le_bisector_of_nonnegative_cosines_of_le_two
    hβ_nonnegative hβ_le_two hcosStar hcos hcosOther hcosBisector

/--
The same corrected C1 comparison on the source's visible angular domain:
`0 ≤ theta ≤ theta_star ≤ pi / 2`.  The interval hypotheses establish every
cosine nonnegativity premise explicitly.
-/
theorem paper_two_user_cos_power_sum_le_bisector_of_angle_mem_Icc_of_le_two
    {β θstar θ : ℝ}
    (hβ_nonnegative : 0 ≤ β) (hβ_le_two : β ≤ 2)
    (hθstar_nonnegative : 0 ≤ θstar)
    (hθstar_le_half_pi : θstar ≤ Real.pi / 2)
    (hθ_nonnegative : 0 ≤ θ) (hθ_le : θ ≤ θstar) :
    paper_two_user_cos_power_sum β θstar θ ≤
      paper_two_user_cos_power_sum β θstar (θstar / 2) :=
  twoUserCosPowerSum_le_bisector_of_angle_mem_Icc_of_le_two
    hβ_nonnegative hβ_le_two hθstar_nonnegative hθstar_le_half_pi
    hθ_nonnegative hθ_le

/--
Corrected two-user C1 angular comparison on the full intended source phase
domain.  The theorem proves the analytic bisector comparison for
`beta ≥ 1`, positive `theta_star ≤ pi / 2`, and
`beta * (1 - cos theta_star) ≤ 2`.  It does not assert the paper's unrepaired
equilibrium-threshold identity or its C1/Nash bridge.
-/
theorem paper_two_user_cos_power_sum_le_bisector_of_source_phase
    {β θstar θ : ℝ}
    (hβ_one : 1 ≤ β)
    (hphase : β * (1 - Real.cos θstar) ≤ 2)
    (hθstar_pos : 0 < θstar)
    (hθstar_le_half_pi : θstar ≤ Real.pi / 2)
    (hθ_nonnegative : 0 ≤ θ) (hθ_le : θ ≤ θstar) :
    paper_two_user_cos_power_sum β θstar θ ≤
      paper_two_user_cos_power_sum β θstar (θstar / 2) :=
  twoUserCosPowerSum_le_bisector_of_source_phase
    hβ_one hphase hθstar_pos hθstar_le_half_pi hθ_nonnegative hθ_le

/--
Corrected two-user C1 comparison on the whole primary positive-score cone in
value coordinates.  The two score cosines are nonnegative precisely on the
displayed angular interval; the source wrote only its central subinterval.
This is an analytic cone extension, not an identification of that value cone
with the full nonnegative content image for arbitrary user embeddings.
-/
theorem paper_two_user_cos_power_sum_le_bisector_of_source_phase_of_angle_mem_positive_score_cone
    {β θstar θ : ℝ}
    (hβ_one : 1 ≤ β)
    (hphase : β * (1 - Real.cos θstar) ≤ 2)
    (hθstar_pos : 0 < θstar)
    (hθstar_le_half_pi : θstar ≤ Real.pi / 2)
    (hθ_lower : θstar - Real.pi / 2 ≤ θ) (hθ_upper : θ ≤ Real.pi / 2) :
    paper_two_user_cos_power_sum β θstar θ ≤
      paper_two_user_cos_power_sum β θstar (θstar / 2) :=
  twoUserCosPowerSum_le_bisector_of_source_phase_of_angle_mem_positiveScoreCone
    hβ_one hphase hθstar_pos hθstar_le_half_pi hθ_lower hθ_upper

/--
Exact analytic threshold characterization for the corrected two-user C1
angular comparison.  It remains separate from the paper's unproved
equilibrium-threshold identification.
-/
theorem paper_two_user_cos_power_sum_bisector_max_iff_source_phase
    {β θstar : ℝ}
    (hβ_one : 1 ≤ β)
    (hθstar_pos : 0 < θstar)
    (hθstar_le_half_pi : θstar ≤ Real.pi / 2) :
    (∀ θ, 0 ≤ θ → θ ≤ θstar →
      paper_two_user_cos_power_sum β θstar θ ≤
        paper_two_user_cos_power_sum β θstar (θstar / 2)) ↔
      β * (1 - Real.cos θstar) ≤ 2 :=
  twoUserCosPowerSum_bisector_max_iff_source_phase
    hβ_one hθstar_pos hθstar_le_half_pi

/--
The corrected two-user polar powered-score row set.  It records exactly the
angular rows to which the repaired C1 calculation applies, without claiming
that the source proof has established a parametrization of the complete
nonnegative content image by those rows.
-/
noncomputable abbrev paper_two_user_angular_powered_rows
    (β θstar : ℝ) : Set (Fin 2 → ℝ) :=
  twoUserAngularPoweredRows β θstar

/--
Corrected optimization bridge for Corollary `2users`: on the explicit
positive angular domain and at or below the displayed phase inequality, the
bisector powered-score row has the same coordinate-product supremum before
and after convexification.  This composes the full angular maximum with a
two-coordinate AM--GM/convexification argument.  It is not yet the source's
beta-star equality: the source still needs a checked theorem identifying its
full powered content image with this polar angular row model.
-/
theorem paper_two_user_angular_product_sup_condition_of_source_phase
    {β θstar : ℝ}
    (hβ_one : 1 ≤ β)
    (hphase : β * (1 - Real.cos θstar) ≤ 2)
    (hθstar_pos : 0 < θstar)
    (hθstar_le_half_pi : θstar ≤ Real.pi / 2) :
    SingleGenreProductSupCondition
      (paper_two_user_angular_powered_rows β θstar) :=
  singleGenreProductSupCondition_twoUserAngularPoweredRows_of_source_phase
    hβ_one hphase hθstar_pos hθstar_le_half_pi

/--
Corrected source-image form of Corollary `2users` for two equally sized
populations.  For arbitrary nonzero nonnegative user vectors, the complete
nonnegative Euclidean unit-ball powered-score image has the one-genre
product-supremum property exactly below the displayed two-user phase
threshold.  The angle is the normalized Euclidean angle between the two user
vectors, so this theorem does not silently assume unit user embeddings.

This is the product-optimization assertion behind the source corollary; the
separate compact-source `singlegenre` theorem below turns it into the
zero-safe singleton-support equilibrium statement.
-/
theorem paper_corollary_twousers_corrected_product_sup_condition_iff_phase_threshold
    {D K : ℕ} {users : Fin 2 → Content D} {β θ : ℝ}
    (hK : 0 < K)
    (husers_nonnegative : ∀ i, NonnegativeContent (users i))
    (hfirst_nonzero : NonzeroContent (users 0))
    (hsecond_nonzero : NonzeroContent (users 1))
    (hangle : paper_inferred_user_value (users 0) (users 1) /
      (AppliedModelingLib.FiniteDimensionalNorms.l2 (users 0) *
        AppliedModelingLib.FiniteDimensionalNorms.l2 (users 1)) = Real.cos θ)
    (hβ_one : 1 ≤ β)
    (hθ_pos : 0 < θ)
    (hθ_le_half_pi : θ ≤ Real.pi / 2) :
    SingleGenreProductSupCondition
      {z : Fin (2 * K) → ℝ |
        InPoweredUnitImage (twoPopulationUsers K users)
          (fun p => NonnegativeContent p ∧ (SourceNorm.l2 D).norm p ≤ 1)
          β z} ↔
      β ≤ twoUserPhaseThreshold θ := by
  exact
    singleGenreProductSupCondition_inPoweredUnitImage_twoPopulationUsers_l2_raw_iff_le_phaseThreshold
      hK husers_nonnegative
      (AppliedModelingLib.FiniteDimensionalNorms.normL2_pos_of_exists_ne_zero hfirst_nonzero)
      (AppliedModelingLib.FiniteDimensionalNorms.normL2_pos_of_exists_ne_zero hsecond_nonzero)
      hangle hβ_one hθ_pos hθ_le_half_pi

/--
Corrected literal threshold identity for Corollary `2users`.  The supremum in
the source's definition is exactly the explicit Euclidean phase threshold.
The proof first identifies the admissible exponents with the closed interval
`[1, twoUserPhaseThreshold theta]`, and then takes its supremum.
-/
theorem paper_corollary_twousers_corrected_product_beta_star_eq_phase_threshold
    {D K : ℕ} {users : Fin 2 → Content D} {θ : ℝ}
    (hK : 0 < K)
    (husers_nonnegative : ∀ i, NonnegativeContent (users i))
    (hfirst_nonzero : NonzeroContent (users 0))
    (hsecond_nonzero : NonzeroContent (users 1))
    (hangle : paper_inferred_user_value (users 0) (users 1) /
      (AppliedModelingLib.FiniteDimensionalNorms.l2 (users 0) *
        AppliedModelingLib.FiniteDimensionalNorms.l2 (users 1)) = Real.cos θ)
    (hθ_pos : 0 < θ)
    (hθ_le_half_pi : θ ≤ Real.pi / 2) :
    paper_two_user_product_beta_star (K := K) users =
      twoUserPhaseThreshold θ := by
  have htheta_lt_pi : θ < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin_half : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have htrig : 1 - Real.cos θ = 2 * (Real.sin (θ / 2)) ^ 2 := by
    rw [Real.sin_sq_eq_half_sub]
    have hdouble : 2 * (θ / 2) = θ := by ring
    rw [hdouble]
    ring
  have hden : 0 < 1 - Real.cos θ := by
    rw [htrig]
    positivity
  have hcos_nonnegative : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], hθ_le_half_pi⟩
  have hthreshold_ge_one : 1 ≤ twoUserPhaseThreshold θ := by
    rw [twoUserPhaseThreshold]
    apply (le_div_iff₀ hden).2
    nlinarith
  unfold paper_two_user_product_beta_star
  rw [show
    {β : ℝ | 1 ≤ β ∧
      SingleGenreProductSupCondition
        {z : Fin (2 * K) → ℝ |
          InPoweredUnitImage (twoPopulationUsers K users)
            (fun p => NonnegativeContent p ∧ (SourceNorm.l2 D).norm p ≤ 1)
            β z}} = Set.Icc 1 (twoUserPhaseThreshold θ) by
      ext β
      simp only [Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · rintro ⟨hβ_one, hproduct⟩
        exact ⟨hβ_one,
          (paper_corollary_twousers_corrected_product_sup_condition_iff_phase_threshold
            hK husers_nonnegative hfirst_nonzero hsecond_nonzero hangle hβ_one
            hθ_pos hθ_le_half_pi).mp hproduct⟩
      · rintro ⟨hβ_one, hβ_le⟩
        exact ⟨hβ_one,
          (paper_corollary_twousers_corrected_product_sup_condition_iff_phase_threshold
            hK husers_nonnegative hfirst_nonzero hsecond_nonzero hangle hβ_one
            hθ_pos hθ_le_half_pi).mpr hβ_le⟩]
  exact csSup_Icc hthreshold_ge_one

theorem paper_hasDerivAt_two_user_cos_power_sum
    {β θstar θ : ℝ}
    (hcosG : Real.cos θ ≠ 0 ∨ 1 ≤ β)
    (hcosO : Real.cos (θstar - θ) ≠ 0 ∨ 1 ≤ β) :
    HasDerivAt
      (fun t : ℝ => paper_two_user_cos_power_sum β θstar t)
      (β *
        (Real.sin (θstar - θ) * (Real.cos (θstar - θ)) ^ (β - 1) -
          Real.sin θ * (Real.cos θ) ^ (β - 1))) θ :=
  hasDerivAt_twoUserCosPowerSum hcosG hcosO

theorem paper_beta_powers_of_cos_power_sum_derivative_zero
    {β θstar θ : ℝ}
    (hβ : β ≠ 0)
    (hzero :
      β *
        (Real.sin (θstar - θ) * (Real.cos (θstar - θ)) ^ (β - 1) -
          Real.sin θ * (Real.cos θ) ^ (β - 1)) = 0) :
    Real.sin θ * (Real.cos θ) ^ (β - 1) =
      Real.sin (θstar - θ) * (Real.cos (θstar - θ)) ^ (β - 1) :=
  betaPowers_of_cosPowerSum_derivative_zero hβ hzero

noncomputable abbrev paper_infinite_genre_scale
    (β θstar θG : ℝ) : ℝ :=
  infiniteGenreScale β θstar θG

theorem paper_infinite_genre_cos_power_sum_eq_inv_scale_of_beta_powers
    {β θstar θG : ℝ}
    (hsinG : Real.sin θG ≠ 0)
    (hsinStar : Real.sin θstar ≠ 0)
    (hcosG : 0 < Real.cos θG)
    (hcosO : 0 < Real.cos (θstar - θG))
    (hbetaPowers :
      Real.sin θG * (Real.cos θG) ^ (β - 1) =
        Real.sin (θstar - θG) * (Real.cos (θstar - θG)) ^ (β - 1)) :
    (Real.cos θG) ^ β + (Real.cos (θstar - θG)) ^ β =
      (paper_infinite_genre_scale β θstar θG)⁻¹ :=
  infiniteGenre_cosPower_sum_eq_inv_scale_of_betaPowers
    hsinG hsinStar hcosG hcosO hbetaPowers

/--
The source's printed trigonometric `C₁` has an additional squared-score factor
relative to the cutoff balance required by the repaired two-genre candidate.
-/
theorem paper_infinite_genre_source_C1_eq_scoreSquare_mul_balance
    {β θstar θG : ℝ}
    (hcosG : 0 < Real.cos θG)
    (hcosO : 0 < Real.cos (θstar - θG))
    (hsinO : Real.sin (θstar - θG) ≠ 0)
    (hbetaPowers :
      Real.sin θG * (Real.cos θG) ^ (β - 1) =
        Real.sin (θstar - θG) * (Real.cos (θstar - θG)) ^ (β - 1)) :
    Real.sin θstar * Real.cos θG / Real.sin (θstar - θG) =
      (Real.cos θG) ^ 2 *
        (1 + (Real.cos (θstar - θG) / Real.cos θG) ^ β) :=
  infiniteGenre_source_C1_eq_scoreSquare_mul_balance
    hcosG hcosO hsinO hbetaPowers

/--
Corrected total version of the alternating `FMax` display in
`infinitegenreformal`.  It fixes the endpoint convention by choosing the
least geometric shell.  This abbreviation is not yet a claim that the
function is a probability CDF.
-/
noncomputable abbrev paper_corrected_infinite_genre_candidate_cdf
    (a C1 C2 beta q : ℝ) : ℝ :=
  infiniteGenreCandidateCdf a C1 C2 beta q

/--
Corrected capped functional equation for the source's alternating candidate.
The cutoff relation `C₁ = a^β` is the displayed calibration in a form that is
well defined for positive parameters.  Unlike the literal source display,
this theorem includes the zero endpoint, every geometric interval, the upper
transition, and the saturated tail.
-/
theorem paper_corrected_infinite_genre_candidate_cdf_product_eq_min
    {a C1 C2 beta q : ℝ}
    (ha : 0 < a) (hC2 : 0 < C2) (hC2_one : C2 < 1) (hbeta : 0 < beta)
    (hC1 : C1 = a ^ beta) (hq : 0 ≤ q) :
    paper_corrected_infinite_genre_candidate_cdf a C1 C2 beta q *
        paper_corrected_infinite_genre_candidate_cdf a C1 C2 beta (q * C2) =
      min 1 ((infiniteGenreCdfFunctionalScale C1 C2 beta) ^ (-2 : ℝ) *
        q ^ (2 * beta)) :=
  infiniteGenreCandidateCdf_product_eq_min_functional_coefficient
    ha hC2 hC2_one hbeta hC1 hq

/--
Corrected square-root reward identity used in the source's `H_1` and `H_2`
calculation.  It follows from the repaired product equation and records the
nonnegative square-root step explicitly.
-/
theorem paper_corrected_infinite_genre_candidate_cdf_sqrt_product_eq_min_reward
    {a C1 C2 beta q : ℝ}
    (ha : 0 < a) (hC2 : 0 < C2) (hC2_one : C2 < 1) (hbeta : 0 < beta)
    (hC1 : C1 = a ^ beta) (hq : 0 ≤ q) :
    Real.sqrt
        (paper_corrected_infinite_genre_candidate_cdf a C1 C2 beta q *
          paper_corrected_infinite_genre_candidate_cdf a C1 C2 beta (q * C2)) =
      min 1 ((infiniteGenreCdfFunctionalScale C1 C2 beta)⁻¹ * q ^ beta) :=
  sqrt_infiniteGenreCandidateCdf_product_eq_min_reward
    ha hC2 hC2_one hbeta hC1 hq

/--
The repaired total candidate CDF is realized by a genuine probability law.
The proof arguments record its necessary positive cutoff and geometric-scale
regime rather than treating the source's piecewise display as a distribution by
fiat.
-/
noncomputable abbrev paper_corrected_infinite_genre_candidate_measure
    (a C1 C2 beta : ℝ)
    (ha : 0 < a) (hC2 : 0 < C2) (hC2_one : C2 < 1) (hbeta : 0 < beta)
    (hC1 : C1 = a ^ beta) : Measure ℝ :=
  infiniteGenreCandidateMeasure a C1 C2 beta ha hC2 hC2_one hbeta hC1

theorem paper_corrected_infinite_genre_candidate_is_probability_measure
    (a C1 C2 beta : ℝ)
    (ha : 0 < a) (hC2 : 0 < C2) (hC2_one : C2 < 1) (hbeta : 0 < beta)
    (hC1 : C1 = a ^ beta) :
    IsProbabilityMeasure
      (paper_corrected_infinite_genre_candidate_measure
        a C1 C2 beta ha hC2 hC2_one hbeta hC1) :=
  infiniteGenreCandidate_isProbabilityMeasure
    a C1 C2 beta ha hC2 hC2_one hbeta hC1

theorem paper_corrected_infinite_genre_candidate_measure_support_subset_cutoff
    (a C1 C2 beta : ℝ)
    (ha : 0 < a) (hC2 : 0 < C2) (hC2_one : C2 < 1) (hbeta : 0 < beta)
    (hC1 : C1 = a ^ beta) :
    (paper_corrected_infinite_genre_candidate_measure
      a C1 C2 beta ha hC2 hC2_one hbeta hC1).support ⊆ Set.Icc 0 a :=
  infiniteGenreCandidateMeasure_support_subset_cutoff
    a C1 C2 beta ha hC2 hC2_one hbeta hC1

/--
Corrected two-genre objective induced by the repaired conditional-quality law.
It uses the symmetric square-root reward corresponding to equal genre weights
`1/2`, not the incompatible weights printed in the source theorem.
-/
noncomputable abbrev paper_corrected_infinite_genre_cross_objective
    (a C1 C2 beta A B theta z1 z2 : ℝ) : ℝ :=
  infiniteGenreCandidateCrossObjective a C1 C2 beta A B theta z1 z2

/--
The corrected candidate objective is globally nonpositive over the full
nonnegative polar score cone if the selected direction has the explicitly
stated global angular-power maximum property.
-/
theorem paper_corrected_infinite_genre_cross_objective_nonpos_of_global_angle_max
    {a C1 C2 beta A B theta phi r : ℝ}
    (ha : 0 < a) (hC2 : 0 < C2) (hC2_one : C2 < 1) (hbeta : 0 < beta)
    (hC1 : C1 = a ^ beta) (hbalance : C1 = 1 + C2 ^ beta)
    (hA : 0 < A) (hB : 0 < B) (hratio : C2 = B / A)
    (hr : 0 ≤ r) (hsin : 0 < Real.sin theta)
    (hcos : 0 ≤ Real.cos phi) (hcos_other : 0 ≤ Real.cos (theta - phi))
    (hglobal : ∀ psi : ℝ, 0 ≤ Real.cos psi →
      0 ≤ Real.cos (theta - psi) →
      (Real.cos psi) ^ beta + (Real.cos (theta - psi)) ^ beta ≤
        A ^ beta + B ^ beta) :
    paper_corrected_infinite_genre_cross_objective a C1 C2 beta A B theta
      (r * Real.cos phi) (r * Real.cos (theta - phi)) ≤ 0 :=
  infiniteGenreCandidateCrossObjective_nonpos_of_global_angle_max
    ha hC2 hC2_one hbeta hC1 hbalance hA hB hratio hr hsin
    hcos hcos_other hglobal

/--
The corrected candidate has zero profit at every cutoff-bounded radius on its
first support ray; the companion main theorem covers the swapped second ray.
-/
theorem paper_corrected_infinite_genre_cross_objective_eq_zero_on_support_ray
    {a C1 C2 beta A B theta phi r : ℝ}
    (ha : 0 < a) (hC2 : 0 < C2) (hC2_one : C2 < 1) (hbeta : 0 < beta)
    (hC1 : C1 = a ^ beta) (hbalance : C1 = 1 + C2 ^ beta)
    (hA : 0 < A) (hB : 0 < B) (hratio : C2 = B / A)
    (hr : 0 ≤ r) (hra : r ≤ a) (hsin : 0 < Real.sin theta)
    (hA_angle : A = Real.cos phi)
    (hB_angle : B = Real.cos (theta - phi)) :
    paper_corrected_infinite_genre_cross_objective a C1 C2 beta A B theta
      (r * A) (r * B) = 0 :=
  infiniteGenreCandidateCrossObjective_eq_zero_on_support_ray
    ha hC2 hC2_one hbeta hC1 hbalance hA hB hratio hr hra hsin
    hA_angle hB_angle

/--
Corrected infinite-genre argmax endpoint for every actual quality in the
conditional law's support, on the first score ray.  It includes both
nonnegative-score feasibility and global objective optimality.
-/
theorem paper_corrected_infinite_genre_cross_objective_isMaxOn_first_ray_of_mem_support
    {a C1 C2 beta A B theta phi r : ℝ}
    (ha : 0 < a) (hC2 : 0 < C2) (hC2_one : C2 < 1) (hbeta : 0 < beta)
    (hC1 : C1 = a ^ beta) (hbalance : C1 = 1 + C2 ^ beta)
    (hA : 0 < A) (hB : 0 < B) (hratio : C2 = B / A)
    (hsin : 0 < Real.sin theta)
    (hA_angle : A = Real.cos phi)
    (hB_angle : B = Real.cos (theta - phi))
    (hglobal : ∀ psi : ℝ, 0 ≤ Real.cos psi →
      0 ≤ Real.cos (theta - psi) →
      (Real.cos psi) ^ beta + (Real.cos (theta - psi)) ^ beta ≤
        A ^ beta + B ^ beta)
    (hr : r ∈ (paper_corrected_infinite_genre_candidate_measure
      a C1 C2 beta ha hC2 hC2_one hbeta hC1).support) :
    (r * A, r * B) ∈ Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ) ∧
      IsMaxOn
        (fun z : ℝ × ℝ =>
          paper_corrected_infinite_genre_cross_objective
            a C1 C2 beta A B theta z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))
        (r * A, r * B) :=
  infiniteGenreCandidateCrossObjective_isMaxOn_nonnegative_scores_of_mem_support
    ha hC2 hC2_one hbeta hC1 hbalance hA hB hratio hsin hA_angle hB_angle
    hglobal hr

/-- The same corrected argmax endpoint for the second, swapped score ray. -/
theorem paper_corrected_infinite_genre_cross_objective_isMaxOn_second_ray_of_mem_support
    {a C1 C2 beta A B theta phi r : ℝ}
    (ha : 0 < a) (hC2 : 0 < C2) (hC2_one : C2 < 1) (hbeta : 0 < beta)
    (hC1 : C1 = a ^ beta) (hbalance : C1 = 1 + C2 ^ beta)
    (hA : 0 < A) (hB : 0 < B) (hratio : C2 = B / A)
    (hsin : 0 < Real.sin theta)
    (hA_angle : A = Real.cos phi)
    (hB_angle : B = Real.cos (theta - phi))
    (hglobal : ∀ psi : ℝ, 0 ≤ Real.cos psi →
      0 ≤ Real.cos (theta - psi) →
      (Real.cos psi) ^ beta + (Real.cos (theta - psi)) ^ beta ≤
        A ^ beta + B ^ beta)
    (hr : r ∈ (paper_corrected_infinite_genre_candidate_measure
      a C1 C2 beta ha hC2 hC2_one hbeta hC1).support) :
    (r * B, r * A) ∈ Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ) ∧
      IsMaxOn
        (fun z : ℝ × ℝ =>
          paper_corrected_infinite_genre_cross_objective
            a C1 C2 beta A B theta z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))
        (r * B, r * A) :=
  infiniteGenreCandidateCrossObjective_isMaxOn_nonnegative_scores_of_mem_support_swapped
    ha hC2 hC2_one hbeta hC1 hbalance hA hB hratio hsin hA_angle hB_angle
    hglobal hr

/--
Corrected score-space equilibrium object for the infinite-producer two-genre
construction. It explicitly records a probability-normalized conditional law,
equal weights, and support-wide C1 maximization on both rays.
-/
abbrev paper_corrected_infinite_two_genre_score_equilibrium :=
  CorrectedInfiniteTwoGenreScoreEquilibrium

/--
The geometric-shell law realizes the canonical two-genre score equilibrium.
-/
noncomputable abbrev paper_corrected_infinite_genre_candidate_score_equilibrium :=
  @infiniteGenreCandidate_correctedInfiniteTwoGenreScoreEquilibrium

/--
The same score equilibrium, with C1 supplied by a maximizer on the corrected
compact left-half angular domain rather than an all-real-angle premise.
-/
noncomputable abbrev paper_corrected_infinite_genre_candidate_score_equilibrium_of_left_half_angle_max :=
  @infiniteGenreCandidate_correctedInfiniteTwoGenreScoreEquilibrium_of_leftHalf_angle_max

/--
Corrected two-genre equilibrium object in the source's nonnegative content
space.  It includes the concrete unit genre directions and C1 comparisons
against every feasible content deviation.
-/
abbrev paper_corrected_infinite_two_genre_content_equilibrium :=
  CorrectedInfiniteTwoGenreContentEquilibrium

/--
The geometric-shell candidate realizes the corrected two-genre content
equilibrium in canonical two-user coordinates.
-/
noncomputable abbrev paper_corrected_infinite_genre_candidate_content_equilibrium :=
  @infiniteGenreCandidate_correctedInfiniteTwoGenreContentEquilibrium

/--
The content-space candidate equilibrium obtained from the corrected compact
left-half angular maximization condition.
-/
noncomputable abbrev paper_corrected_infinite_genre_candidate_content_equilibrium_of_left_half_angle_max :=
  @infiniteGenreCandidate_correctedInfiniteTwoGenreContentEquilibrium_of_leftHalf_angle_max

/--
Corrected infinite-producer two-genre existence theorem in the strictly acute,
strictly-above-phase-threshold regime.  It chooses the compact angular
maximizer and constructs the normalized candidate law and content equilibrium.
-/
theorem paper_exists_corrected_infinite_two_genre_content_equilibrium_of_phase_threshold_lt
    {beta theta : ℝ}
    (htheta_pos : 0 < theta) (htheta_lt_half_pi : theta < Real.pi / 2)
    (hphase : twoUserPhaseThreshold theta < beta) :
    ∃ a C1 C2 A B phi : ℝ,
      ∃ _ : CorrectedInfiniteTwoGenreContentEquilibrium
        (infiniteGenreCandidateCdf a C1 C2 beta) beta theta,
      phi ∈ Set.Icc 0 (theta / 2) ∧
      IsMaxOn (twoUserCosPowerSum beta theta) (Set.Icc 0 (theta / 2)) phi ∧
      0 < a ∧ 0 < C2 ∧ C2 < 1 ∧
      C1 = a ^ beta ∧ C1 = 1 + C2 ^ beta ∧
      A = Real.cos phi ∧ B = Real.cos (theta - phi) ∧ C2 = B / A :=
  exists_correctedInfiniteTwoGenreContentEquilibrium_of_phaseThreshold_lt
    htheta_pos htheta_lt_half_pi hphase

/-- Corrected infinite-producer two-genre equilibrium object for arbitrary
nonnegative content-space users. -/
abbrev paper_corrected_infinite_two_genre_general_content_equilibrium
    {D : ℕ} (F : ℝ → ℝ) (beta : ℝ) (u v : Content D) :=
  CorrectedInfiniteTwoGenreGeneralContentEquilibrium F beta u v

/-- Source-facing repaired infinite-genre theorem.  For two nonzero
nonnegative users with strictly acute normalized angle, the high-phase regime
constructs the geometric-shell probability law, two equal-weight genres, and
C1 best responses against every nonnegative content deviation.  The proof
normalizes users internally and then proves scale invariance of the score-ratio
payoffs before returning the equilibrium for the original users. -/
theorem paper_exists_corrected_infinite_two_genre_general_content_equilibrium_of_phase_threshold_lt
    {D : ℕ} {beta theta : ℝ} {u v : Content D}
    (hu_nonnegative : NonnegativeContent u) (hv_nonnegative : NonnegativeContent v)
    (hu_nonzero : u ≠ 0) (hv_nonzero : v ≠ 0)
    (hangle : score u v /
      (AppliedModelingLib.FiniteDimensionalNorms.l2 u *
        AppliedModelingLib.FiniteDimensionalNorms.l2 v) = Real.cos theta)
    (htheta_pos : 0 < theta) (htheta_lt_half_pi : theta < Real.pi / 2)
    (hphase : twoUserPhaseThreshold theta < beta) :
    ∃ a C1 C2 A B phi : ℝ,
      ∃ _ : CorrectedInfiniteTwoGenreGeneralContentEquilibrium
        (infiniteGenreCandidateCdf a C1 C2 beta) beta u v,
      phi ∈ Set.Icc 0 (theta / 2) ∧
      IsMaxOn (twoUserCosPowerSum beta theta) (Set.Icc 0 (theta / 2)) phi ∧
      0 < a ∧ 0 < C2 ∧ C2 < 1 ∧
      C1 = a ^ beta ∧ C1 = 1 + C2 ^ beta ∧
      A = Real.cos phi ∧ B = Real.cos (theta - phi) ∧ C2 = B / A :=
  exists_correctedInfiniteTwoGenreGeneralContentEquilibrium_of_phaseThreshold_lt_for_raw_users
    hu_nonnegative hv_nonnegative hu_nonzero hv_nonzero hangle
    htheta_pos htheta_lt_half_pi hphase

/--
Corrected infinite-producer verification objective.  This is the capped
reward expression that the source derives after its conditional-quality
calculation; it is not a definition of the source's printed, incomplete CDF.
-/
noncomputable abbrev paper_infinite_genre_capped_objective
    (c beta theta z1 z2 : ℝ) : ℝ :=
  infiniteGenreCappedObjective c beta theta z1 z2

/--
Corrected global verification step for `infinitegenreformal`: an angular
power bound makes the capped objective nonpositive at a canonical polar value.
The candidate-CDF bridge is formalized separately above; this lower-level
lemma remains available for other applications of the capped objective.
-/
theorem paper_infinite_genre_capped_objective_nonpos_of_polar_angle_bound
    {c beta theta phi r : ℝ}
    (hr : 0 ≤ r) (hc : 0 < c) (hsin : 0 < Real.sin theta)
    (hcos : 0 ≤ Real.cos phi)
    (hcos_other : 0 ≤ Real.cos (theta - phi))
    (hangle : (Real.cos phi) ^ beta +
      (Real.cos (theta - phi)) ^ beta ≤ c⁻¹) :
    paper_infinite_genre_capped_objective c beta theta
      (r * Real.cos phi) (r * Real.cos (theta - phi)) ≤ 0 :=
  infiniteGenreCappedObjective_nonpos_of_polar_angle_bound
    hr hc hsin hcos hcos_other hangle

/--
Corrected support-attainment verification for `infinitegenreformal`.  At an
angular maximizer, the capped objective is zero whenever the two reward caps
are inactive.  The repaired candidate obtains those conditions through its
explicit cutoff balance in the stronger cross-objective theorem above.
-/
theorem paper_infinite_genre_capped_objective_eq_zero_of_polar_angle_eq
    {c beta theta phi r : ℝ}
    (hr : 0 ≤ r) (hsin : 0 < Real.sin theta)
    (hcos : 0 ≤ Real.cos phi)
    (hcos_other : 0 ≤ Real.cos (theta - phi))
    (hangle : c * ((Real.cos phi) ^ beta +
      (Real.cos (theta - phi)) ^ beta) = 1)
    (hcap : c * (r * Real.cos phi) ^ beta ≤ 1)
    (hcap_other : c * (r * Real.cos (theta - phi)) ^ beta ≤ 1) :
    paper_infinite_genre_capped_objective c beta theta
      (r * Real.cos phi) (r * Real.cos (theta - phi)) = 0 :=
  infiniteGenreCappedObjective_eq_zero_of_polar_angle_eq
    hr hsin hcos hcos_other hangle hcap hcap_other

/--
Lemma `inducedcost`, canonical reconstruction: the first rotated user
`e_1` receives value `z_1` from the reconstructed content vector.
-/
theorem paper_score_canonical_two_user_first_content_of_values
    (θ z1 z2 : ℝ) :
    score canonicalTwoUserFirst
      (canonicalTwoUserContentOfValues θ z1 z2) = z1 :=
  score_canonicalTwoUserFirst_contentOfValues θ z1 z2

/--
Lemma `inducedcost`, canonical reconstruction: the second rotated user
`(cos θ, sin θ)` receives value `z_2` from the reconstructed content vector.
-/
theorem paper_score_canonical_two_user_second_content_of_values
    {θ z1 z2 : ℝ} (hsin : Real.sin θ ≠ 0) :
    score (canonicalTwoUserSecond θ)
      (canonicalTwoUserContentOfValues θ z1 z2) = z2 :=
  score_canonicalTwoUserSecond_contentOfValues hsin

/-- Proposition `atom`: source mixed strategy as a measure over content vectors. -/
abbrev paper_mixed_content_strategy (D : ℕ) :=
  MixedContentStrategy D

/-- Proposition `atom`: a candidate content vector has positive point mass. -/
abbrev paper_has_content_point_mass {D : ℕ}
    (μ : paper_mixed_content_strategy D) (p : Content D) : Prop :=
  HasContentPointMass μ p

/-- Proposition `atom`: source-facing atomless predicate for mixed strategies. -/
abbrev paper_mixed_content_strategy_atomless {D : ℕ}
    (μ : paper_mixed_content_strategy D) : Prop :=
  MixedContentStrategyAtomless μ

/--
Proposition `atom`, equilibrium-contradiction surface: no pure content vector
can earn more than the symmetric mixed equilibrium payoff.
-/
abbrev paper_symmetric_mixed_no_profitable_pure_deviation {D : ℕ}
    (payoff : Content D → paper_mixed_content_strategy D → ℝ)
    (μ : paper_mixed_content_strategy D) (equilibriumPayoff : ℝ) : Prop :=
  SymmetricMixedNoProfitablePureDeviation payoff μ equilibriumPayoff

/--
Proposition `atom`, bundled source-facing symmetric mixed equilibrium
conditions: no pure content deviation beats the equilibrium payoff, and every
atom in the mixed strategy's support earns that payoff.
-/
abbrev paper_source_symmetric_mixed_equilibrium_conditions {D : ℕ}
    (payoff : Content D → paper_mixed_content_strategy D → ℝ)
    (μ : paper_mixed_content_strategy D) : Prop :=
  SourceSymmetricMixedEquilibriumConditions payoff μ

/--
Proposition `atom`, perturbation surface: every point mass creates a profitable
pure perturbation.  The remaining source-specific work is the payoff/probability
calculation deriving this premise from the atom event and cost continuity.
-/
abbrev paper_atom_perturbation_profitable {D : ℕ}
    (payoff : Content D → paper_mixed_content_strategy D → ℝ)
    (μ : paper_mixed_content_strategy D) (equilibriumPayoff : ℝ) : Prop :=
  AtomPerturbationProfitable payoff μ equilibriumPayoff

/--
Proposition `atom`, closed contradiction core: no-profitable-deviation plus
the source atom-perturbation premise implies the mixed strategy is atomless.
-/
theorem paper_proposition_atom_atomless_of_no_profitable_deviation
    {D : ℕ} {payoff : Content D → paper_mixed_content_strategy D → ℝ}
    {μ : paper_mixed_content_strategy D} {equilibriumPayoff : ℝ}
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation payoff μ equilibriumPayoff)
    (hatom : paper_atom_perturbation_profitable payoff μ equilibriumPayoff) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_of_no_profitable_deviation hno hatom

/--
Proposition `atom`, mathlib atomlessness form: the same contradiction core
exposed as `MeasureTheory.NoAtoms` for later CDF/support arguments.
-/
theorem paper_proposition_atom_noAtoms_of_no_profitable_deviation
    {D : ℕ} {payoff : Content D → paper_mixed_content_strategy D → ℝ}
    {μ : paper_mixed_content_strategy D} {equilibriumPayoff : ℝ}
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation payoff μ equilibriumPayoff)
    (hatom : paper_atom_perturbation_profitable payoff μ equilibriumPayoff) :
    MeasureTheory.NoAtoms μ :=
  noAtoms_of_no_profitable_deviation_and_atom_perturbation hno hatom

/--
Proposition `atom`, real singleton-probability form: under the same closed
contradiction core, every content vector has zero real point mass.
-/
theorem paper_proposition_atom_real_point_mass_zero_of_no_profitable_deviation
    {D : ℕ} {payoff : Content D → paper_mixed_content_strategy D → ℝ}
    {μ : paper_mixed_content_strategy D} {equilibriumPayoff : ℝ}
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation payoff μ equilibriumPayoff)
    (hatom : paper_atom_perturbation_profitable payoff μ equilibriumPayoff)
    (p : Content D) :
    μ.real ({p} : Set (Content D)) = 0 :=
  measureReal_singleton_eq_zero_of_no_profitable_deviation hno hatom p

/--
Proposition `atom`, positive event-gain algebra: if an atom has mass `α > 0`,
then the event that all other producers draw that atom and the deviator changes
from a `1/P` tie share to a strict win has positive payoff gain before costs.
-/
theorem paper_proposition_atom_tie_event_gain_positive {P : ℕ}
    [Nontrivial (Fin P)] {α : ℝ} (hα : 0 < α) :
    0 < α ^ (P - 1) * (1 - 1 / (P : ℝ)) :=
  atomTieEventGain_positive hα

/--
Proposition `atom`, point-mass event-gain bridge: a positive point mass under a
finite mixed strategy yields the strictly positive source gain term
`μ({p})^(P-1) (1 - 1/P)`.
-/
theorem paper_proposition_atom_tie_event_gain_positive_of_point_mass
    {D P : ℕ} [Nontrivial (Fin P)]
    {μ : paper_mixed_content_strategy D} [MeasureTheory.IsFiniteMeasure μ]
    {p : Content D} (hp : paper_has_content_point_mass μ p) :
    0 < (μ.real ({p} : Set (Content D))) ^ (P - 1) *
      (1 - 1 / (P : ℝ)) :=
  atomTieEventGain_positive_of_content_point_mass hp

/--
Proposition `atom`, source tie calculation on the all-atom event: if every
producer chooses the same content vector, each producer receives tie share
`1/P` for every user.
-/
theorem paper_proposition_atom_all_at_atom_tie_share_eq_one_div
    {D P : ℕ} (u p : Content D) (j : Fin P) :
    tieShare u (fun _ : Fin P => p) j = 1 / (P : ℝ) :=
  tieShare_constantProfile_eq_one_div u p j

/--
Proposition `atom`, source tie calculation after perturbation: on the event
where all producers would otherwise choose the atom `p`, a positive perturbation
in a nonzero user direction changes the focal producer's tie share from `1/P`
to `1`.
-/
theorem paper_proposition_atom_all_at_atom_tie_share_gain
    {D P : ℕ} {u p : Content D} {j : Fin P} {ε : ℝ}
    (hu : NonnegativeContent u) (hzero : NonzeroContent u) (hε : 0 < ε) :
    tieShare u
        (deviateProfile (fun _ : Fin P => p) j (fun d => p d + ε * u d)) j -
      tieShare u (fun _ : Fin P => p) j =
        1 - 1 / (P : ℝ) :=
  tieShare_gain_constantProfile_perturb_eq_one_sub_one_div hu hzero hε

/--
Proposition `atom`, realized all-atom pure-profile gain: on the event where
all producers would otherwise choose the atom `p`, the focal perturbation gains
at least the tie-share jump `1 - 1/P` minus the cost increase.
-/
theorem paper_proposition_atom_all_at_atom_pure_profit_gain_lower_bound
    {D N P : ℕ} {users : Fin N → Content D} {cost : Content D → ℝ}
    {p : Content D} {i0 : Fin N} {j : Fin P} {ε : ℝ}
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0)) (hε : 0 < ε) :
    1 - 1 / (P : ℝ) -
        (cost (fun d => p d + ε * users i0 d) - cost p) ≤
      paper_profit_formula users cost
          (deviateProfile (fun _ : Fin P => p) j
            (fun d => p d + ε * users i0 d)) j -
        paper_profit_formula users cost (fun _ : Fin P => p) j :=
  pureProfit_gain_constantProfile_perturb_ge_one_sub_one_div_sub_cost
    husers_nonneg hzero hε

/--
Proposition `atom`, source event as a set of realized full profiles: every
producer other than the deviating producer `j` draws the atom content `p`.
-/
abbrev paper_all_other_producers_draw_content {D P : ℕ}
    (j : Fin P) (p : Content D) : Set (Fin P → Content D) :=
  AllOtherProducersDrawContent j p

/--
Proposition `atom`, event-profile normalization: if all other producers drew
`p`, then replacing producer `j` by `p` gives the constant all-`p` profile.
-/
theorem paper_proposition_atom_profile_eq_constant_on_all_others_event
    {D P : ℕ} {profile : Fin P → Content D} {j : Fin P} {p : Content D}
    (hprofile : profile ∈ paper_all_other_producers_draw_content j p) :
    deviateProfile profile j p = fun _ : Fin P => p :=
  deviateProfile_eq_constant_of_allOtherProducersDrawContent hprofile

/--
Proposition `atom`, full-profile event probability: under independent
probability draws from the symmetric mixed strategy, the event that every
producer other than `j` draws atom `p` has probability `μ({p})^(P-1)`.
-/
theorem paper_proposition_atom_all_other_producers_event_measure_eq_pow
    {D P : ℕ} {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ] (j : Fin P) (p : Content D) :
    MeasureTheory.Measure.pi (fun _ : Fin P => μ)
        (paper_all_other_producers_draw_content j p) =
      μ ({p} : Set (Content D)) ^ (P - 1) :=
  measure_allOtherProducersDrawContent_eq_pow (μ := μ) j p

/--
Proposition `atom`, real-valued full-profile event probability.
-/
theorem paper_proposition_atom_all_other_producers_event_measureReal_eq_pow
    {D P : ℕ} {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ] (j : Fin P) (p : Content D) :
    (MeasureTheory.Measure.pi (fun _ : Fin P => μ)).real
        (paper_all_other_producers_draw_content j p) =
      (μ.real ({p} : Set (Content D))) ^ (P - 1) :=
  measureReal_allOtherProducersDrawContent_eq_pow (μ := μ) j p

/--
Proposition `atom`, pointwise monotonicity: replacing `p` by `p + ε u` in a
nonnegative user direction weakly increases producer `j`'s assigned-user mass
for every realized profile.
-/
theorem paper_proposition_atom_users_won_weakly_increases_under_nonnegative_perturb
    {D N P : ℕ} {users : Fin N → Content D}
    {profile : Fin P → Content D} {p u : Content D} {j : Fin P} {ε : ℝ}
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hu : NonnegativeContent u) (hε : 0 ≤ ε) :
    usersWon users (deviateProfile profile j p) j ≤
      usersWon users (deviateProfile profile j (fun d => p d + ε * u d)) j :=
  usersWon_le_deviate_replace_by_nonnegative_perturb husers_nonneg hu hε

/--
Proposition `atom`, pointwise all-at-atom gain: on the event where every other
producer drew the atom `p`, perturbing to `p + ε u_i` raises assigned-user mass
by at least `1 - 1/P`.
-/
theorem paper_proposition_atom_users_won_gain_on_all_others_event
    {D N P : ℕ} {users : Fin N → Content D}
    {profile : Fin P → Content D} {p : Content D}
    {i0 : Fin N} {j : Fin P} {ε : ℝ}
    (hprofile : profile ∈ paper_all_other_producers_draw_content j p)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0)) (hε : 0 < ε) :
    1 - 1 / (P : ℝ) ≤
      usersWon users (deviateProfile profile j (fun d => p d + ε * users i0 d)) j -
        usersWon users (deviateProfile profile j p) j :=
  usersWon_gain_allOtherProducersDrawContent_perturb_ge_one_sub_one_div
    hprofile husers_nonneg hzero hε

/--
Proposition `atom`, point-mass event-gain bridge with the realized tie-share
gain: a genuine atom gives positive probability to the all-opponents-at-`p`
event, and the focal perturbation has strictly positive tie-share gain on that
event.
-/
theorem paper_proposition_atom_event_perturbation_gain_positive_of_point_mass
    {D P : ℕ} [Nontrivial (Fin P)]
    {μ : paper_mixed_content_strategy D} [MeasureTheory.IsFiniteMeasure μ]
    {p u : Content D} {j : Fin P} {ε : ℝ}
    (hp : paper_has_content_point_mass μ p)
    (hu : NonnegativeContent u) (hzero : NonzeroContent u) (hε : 0 < ε) :
    0 < (μ.real ({p} : Set (Content D))) ^ (P - 1) *
      (tieShare u
          (deviateProfile (fun _ : Fin P => p) j (fun d => p d + ε * u d)) j -
        tieShare u (fun _ : Fin P => p) j) :=
  atomTieEventPerturbationGain_positive_of_content_point_mass hp hu hzero hε

/--
Proposition `atom`, cost-continuity step: the strictly positive atom-event
tie-share gain leaves room for a positive perturbation whose cost increase is
smaller than that realized event gain.
-/
theorem paper_proposition_atom_exists_perturb_cost_increase_lt_event_gain
    {D P : ℕ} [Nontrivial (Fin P)]
    {μ : paper_mixed_content_strategy D} [MeasureTheory.IsFiniteMeasure μ]
    {cost : Content D → ℝ} (hcont : PerturbationCostContinuous cost)
    {p u : Content D} {j : Fin P}
    (hp : paper_has_content_point_mass μ p)
    (hu : NonnegativeContent u) (hzero : NonzeroContent u) :
    ∃ ε : ℝ, 0 < ε ∧
      cost (fun d => p d + ε * u d) - cost p <
        (μ.real ({p} : Set (Content D))) ^ (P - 1) *
          (tieShare u
              (deviateProfile (fun _ : Fin P => p) j
                (fun d => p d + ε * u d)) j -
            tieShare u (fun _ : Fin P => p) j) :=
  exists_atom_perturb_cost_increase_lt_event_gain hcont hp hu hzero

/--
Proposition `atom`, cost-continuity step for the paper's source cost family
`c(p)=ν(p)^β`.
-/
theorem paper_proposition_atom_exists_perturb_norm_rpow_cost_increase_lt_event_gain
    {D P : ℕ} [Nontrivial (Fin P)]
    {μ : paper_mixed_content_strategy D} [MeasureTheory.IsFiniteMeasure μ]
    (ν : SourceNorm D) {β : ℝ} (hβ : 0 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    {p u : Content D} {j : Fin P}
    (hp : paper_has_content_point_mass μ p)
    (hu : NonnegativeContent u) (hzero : NonzeroContent u) :
    ∃ ε : ℝ, 0 < ε ∧
      normRpowCost ν β (fun d => p d + ε * u d) - normRpowCost ν β p <
        (μ.real ({p} : Set (Content D))) ^ (P - 1) *
          (tieShare u
              (deviateProfile (fun _ : Fin P => p) j
                (fun d => p d + ε * u d)) j -
            tieShare u (fun _ : Fin P => p) j) :=
  exists_atom_perturb_normRpowCost_increase_lt_event_gain ν hβ hcont hp hu hzero

/--
Proposition `atom`, remaining payoff-semantics boundary for a single
perturbation: the expected payoff gain is at least the realized event gain
minus the production-cost increase.
-/
abbrev paper_atom_event_payoff_gain_lower_bound
    {D P : ℕ} [Nontrivial (Fin P)]
    (payoff : Content D → paper_mixed_content_strategy D → ℝ)
    (cost : Content D → ℝ) (μ : paper_mixed_content_strategy D)
    (p u : Content D) (j : Fin P) (ε : ℝ) : Prop :=
  AtomEventPayoffGainLowerBound payoff cost μ p u j ε

/--
Proposition `atom`, source mixed-payoff decomposition: pure payoff against the
symmetric mixed strategy equals expected assigned-user mass minus production
cost.
-/
noncomputable abbrev paper_source_mixed_pure_payoff
    {D : ℕ}
    (expectedUsersWon : Content D → paper_mixed_content_strategy D → ℝ)
    (cost : Content D → ℝ) (p : Content D)
    (μ : paper_mixed_content_strategy D) : ℝ :=
  SourceMixedPurePayoff expectedUsersWon cost p μ

/--
Proposition `atom`, product-integral semantics for expected assigned-user
mass: a pure content vector is evaluated against independent symmetric mixed
draws, with the focal producer's coordinate overwritten by the pure action.
-/
noncomputable abbrev paper_expected_users_won_against_symmetric_mixed
    {D N P : ℕ}
    (users : Fin N → Content D) (j : Fin P)
    (p : Content D) (μ : paper_mixed_content_strategy D) : ℝ :=
  ExpectedUsersWonAgainstSymmetricMixed users j p μ

/--
Proposition `atom`, expected-users event-gain boundary: the source all-at-atom
event raises the expected assigned-user component by at least the event
probability times the realized tie-share jump.
-/
abbrev paper_atom_event_expected_users_won_gain_lower_bound
    {D P : ℕ} [Nontrivial (Fin P)]
    (expectedUsersWon : Content D → paper_mixed_content_strategy D → ℝ)
    (μ : paper_mixed_content_strategy D)
    (p u : Content D) (j : Fin P) (ε : ℝ) : Prop :=
  AtomEventExpectedUsersWonGainLowerBound (D := D) (P := P)
    expectedUsersWon μ p u j ε

theorem paper_atom_event_expected_users_won_gain_lower_bound_of_integral_semantics
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {p : Content D} {i0 : Fin N} {j : Fin P} {ε : ℝ}
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0)) (hε : 0 < ε)
    (hint_base :
      MeasureTheory.Integrable
        (fun profile : Fin P → Content D =>
          usersWon users (deviateProfile profile j p) j)
        (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hint_perturb :
      MeasureTheory.Integrable
        (fun profile : Fin P → Content D =>
          usersWon users
            (deviateProfile profile j (fun d => p d + ε * users i0 d)) j)
        (MeasureTheory.Measure.pi (fun _ : Fin P => μ))) :
    paper_atom_event_expected_users_won_gain_lower_bound (D := D) (P := P)
      (paper_expected_users_won_against_symmetric_mixed users j)
      μ p (users i0) j ε :=
  atomEventExpectedUsersWonGainLowerBound_of_integral_semantics
    (D := D) (N := N) (P := P)
    husers_nonneg hzero hε
    (measurableSet_allOtherProducersDrawContent j p)
    hint_base hint_perturb

theorem paper_atom_event_payoff_gain_lower_bound_of_expected_users_won_gain_lower_bound
    {D P : ℕ} [Nontrivial (Fin P)]
    {expectedUsersWon : Content D → paper_mixed_content_strategy D → ℝ}
    {cost : Content D → ℝ} {μ : paper_mixed_content_strategy D}
    {p u : Content D} {j : Fin P} {ε : ℝ}
    (hgain :
      paper_atom_event_expected_users_won_gain_lower_bound
        (D := D) (P := P) expectedUsersWon μ p u j ε) :
    paper_atom_event_payoff_gain_lower_bound
      (D := D) (P := P)
      (paper_source_mixed_pure_payoff expectedUsersWon cost) cost μ p u j ε :=
  atomEventPayoffGainLowerBound_of_expectedUsersWonGainLowerBound hgain

/--
Proposition `atom`, one-atom conclusion: payoff-semantics lower bound plus
cost continuity produces a pure perturbation with payoff above the symmetric
equilibrium payoff.
-/
theorem paper_proposition_atom_exists_profitable_perturbation_of_event_gain_lower_bound
    {D P : ℕ} [Nontrivial (Fin P)]
    {payoff : Content D → paper_mixed_content_strategy D → ℝ}
    {cost : Content D → ℝ} {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsFiniteMeasure μ] {equilibriumPayoff : ℝ}
    (hcont : PerturbationCostContinuous cost)
    {p u : Content D} {j : Fin P}
    (hp : paper_has_content_point_mass μ p)
    (hu : NonnegativeContent u) (hzero : NonzeroContent u)
    (hpayoff : payoff p μ = equilibriumPayoff)
    (hlower :
      ∀ {ε : ℝ}, 0 < ε →
        paper_atom_event_payoff_gain_lower_bound payoff cost μ p u j ε) :
    ∃ p' : Content D, equilibriumPayoff < payoff p' μ :=
  exists_profitable_atom_perturbation_of_event_gain_lower_bound
    hcont hp hu hzero hpayoff hlower

/--
Proposition `atom`, all-atoms payoff-semantics boundary: every point mass has a
source user direction and focal producer for which the event-gain lower bound
applies.
-/
abbrev paper_atom_event_payoff_lower_bounds_for_atoms
    {D P : ℕ} [Nontrivial (Fin P)]
    (payoff : Content D → paper_mixed_content_strategy D → ℝ)
    (cost : Content D → ℝ) (μ : paper_mixed_content_strategy D)
    (equilibriumPayoff : ℝ) : Prop :=
  AtomEventPayoffLowerBoundsForAtoms (D := D) (P := P)
    payoff cost μ equilibriumPayoff

/--
Proposition `atom`, expected-users version of the all-atoms event-gain
boundary.  Cost subtraction is derived separately, rather than assumed in the
mixed-payoff lower bound.
-/
abbrev paper_atom_event_expected_users_won_lower_bounds_for_atoms
    {D P : ℕ} [Nontrivial (Fin P)]
    (expectedUsersWon : Content D → paper_mixed_content_strategy D → ℝ)
    (cost : Content D → ℝ) (μ : paper_mixed_content_strategy D)
    (equilibriumPayoff : ℝ) : Prop :=
  AtomEventExpectedUsersWonLowerBoundsForAtoms (D := D) (P := P)
    expectedUsersWon cost μ equilibriumPayoff

theorem paper_atom_event_expected_users_won_lower_bounds_for_atoms_of_integral_semantics
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff : ℝ} {i0 : Fin N} {j : Fin P}
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j) cost p μ =
          equilibriumPayoff)
    (hint_base :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hint_perturb :
      ∀ (p : Content D) {ε : ℝ}, paper_has_content_point_mass μ p → 0 < ε →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users
              (deviateProfile profile j (fun d => p d + ε * users i0 d)) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ))) :
    paper_atom_event_expected_users_won_lower_bounds_for_atoms (D := D) (P := P)
      (paper_expected_users_won_against_symmetric_mixed users j)
      cost μ equilibriumPayoff :=
  atomEventExpectedUsersWonLowerBoundsForAtoms_of_integral_semantics
    (D := D) (N := N) (P := P)
    husers_nonneg hzero hpayoff hint_base hint_perturb

theorem paper_atom_event_payoff_lower_bounds_for_atoms_of_expected_users_won_lower_bounds
    {D P : ℕ} [Nontrivial (Fin P)]
    {expectedUsersWon : Content D → paper_mixed_content_strategy D → ℝ}
    {cost : Content D → ℝ} {μ : paper_mixed_content_strategy D}
    {equilibriumPayoff : ℝ}
    (hlower :
      paper_atom_event_expected_users_won_lower_bounds_for_atoms (D := D) (P := P)
        expectedUsersWon cost μ equilibriumPayoff) :
    paper_atom_event_payoff_lower_bounds_for_atoms (D := D) (P := P)
      (paper_source_mixed_pure_payoff expectedUsersWon cost)
      cost μ equilibriumPayoff :=
  atomEventPayoffLowerBoundsForAtoms_of_expectedUsersWon_lower_bounds hlower

/--
Proposition `atom`, reduction of the remaining payoff-semantics boundary: if
the event-gain lower bound is available for every atom, then the abstract
atom-perturbation premise used by the contradiction core follows.
-/
theorem paper_proposition_atom_perturbation_profitable_of_event_gain_lower_bounds
    {D P : ℕ} [Nontrivial (Fin P)]
    {payoff : Content D → paper_mixed_content_strategy D → ℝ}
    {cost : Content D → ℝ} {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsFiniteMeasure μ] {equilibriumPayoff : ℝ}
    (hcont : PerturbationCostContinuous cost)
    (hlower :
      paper_atom_event_payoff_lower_bounds_for_atoms (D := D) (P := P)
        payoff cost μ equilibriumPayoff) :
    paper_atom_perturbation_profitable payoff μ equilibriumPayoff :=
  atomPerturbationProfitable_of_event_gain_lower_bounds hcont hlower

/--
Proposition `atom`, direct atomlessness theorem from no profitable pure
deviation, cost continuity, and the source payoff-semantics lower-bound
package.
-/
theorem paper_proposition_atom_atomless_of_event_gain_lower_bounds
    {D P : ℕ} [Nontrivial (Fin P)]
    {payoff : Content D → paper_mixed_content_strategy D → ℝ}
    {cost : Content D → ℝ} {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsFiniteMeasure μ] {equilibriumPayoff : ℝ}
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation payoff μ equilibriumPayoff)
    (hcont : PerturbationCostContinuous cost)
    (hlower :
      paper_atom_event_payoff_lower_bounds_for_atoms (D := D) (P := P)
        payoff cost μ equilibriumPayoff) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_of_event_gain_lower_bounds
    (P := P) hno hcont hlower

/--
Proposition `atom`, mathlib `NoAtoms` form from the explicit payoff-semantics
lower-bound package.
-/
theorem paper_proposition_atom_noAtoms_of_event_gain_lower_bounds
    {D P : ℕ} [Nontrivial (Fin P)]
    {payoff : Content D → paper_mixed_content_strategy D → ℝ}
    {cost : Content D → ℝ} {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsFiniteMeasure μ] {equilibriumPayoff : ℝ}
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation payoff μ equilibriumPayoff)
    (hcont : PerturbationCostContinuous cost)
    (hlower :
      paper_atom_event_payoff_lower_bounds_for_atoms (D := D) (P := P)
        payoff cost μ equilibriumPayoff) :
    MeasureTheory.NoAtoms μ :=
  noAtoms_of_event_gain_lower_bounds (P := P) hno hcont hlower

/--
Proposition `atom`, real singleton-probability form from the explicit
payoff-semantics lower-bound package.
-/
theorem paper_proposition_atom_real_point_mass_zero_of_event_gain_lower_bounds
    {D P : ℕ} [Nontrivial (Fin P)]
    {payoff : Content D → paper_mixed_content_strategy D → ℝ}
    {cost : Content D → ℝ} {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsFiniteMeasure μ] {equilibriumPayoff : ℝ}
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation payoff μ equilibriumPayoff)
    (hcont : PerturbationCostContinuous cost)
    (hlower :
      paper_atom_event_payoff_lower_bounds_for_atoms (D := D) (P := P)
        payoff cost μ equilibriumPayoff)
    (p : Content D) :
    μ.real ({p} : Set (Content D)) = 0 :=
  measureReal_singleton_eq_zero_of_event_gain_lower_bounds
    (P := P) hno hcont hlower p

/--
Proposition `atom`, atomlessness from the expected assigned-user event-gain
boundary, with payoff defined as expected assigned-user mass minus cost.
-/
theorem paper_proposition_atom_atomless_of_expected_users_won_event_gain_lower_bounds
    {D P : ℕ} [Nontrivial (Fin P)]
    {expectedUsersWon : Content D → paper_mixed_content_strategy D → ℝ}
    {cost : Content D → ℝ} {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsFiniteMeasure μ] {equilibriumPayoff : ℝ}
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff expectedUsersWon cost) μ equilibriumPayoff)
    (hcont : PerturbationCostContinuous cost)
    (hlower :
      paper_atom_event_expected_users_won_lower_bounds_for_atoms
        (D := D) (P := P) expectedUsersWon cost μ equilibriumPayoff) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_of_expectedUsersWon_event_gain_lower_bounds
    (P := P) hno hcont hlower

/--
Proposition `atom`, `NoAtoms` form from the expected assigned-user event-gain
boundary.
-/
theorem paper_proposition_atom_noAtoms_of_expected_users_won_event_gain_lower_bounds
    {D P : ℕ} [Nontrivial (Fin P)]
    {expectedUsersWon : Content D → paper_mixed_content_strategy D → ℝ}
    {cost : Content D → ℝ} {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsFiniteMeasure μ] {equilibriumPayoff : ℝ}
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff expectedUsersWon cost) μ equilibriumPayoff)
    (hcont : PerturbationCostContinuous cost)
    (hlower :
      paper_atom_event_expected_users_won_lower_bounds_for_atoms
        (D := D) (P := P) expectedUsersWon cost μ equilibriumPayoff) :
    MeasureTheory.NoAtoms μ :=
  noAtoms_of_expectedUsersWon_event_gain_lower_bounds
    (P := P) hno hcont hlower

/--
Proposition `atom`, real singleton-probability form from the expected
assigned-user event-gain boundary.
-/
theorem paper_proposition_atom_real_point_mass_zero_of_expected_users_won_event_gain_lower_bounds
    {D P : ℕ} [Nontrivial (Fin P)]
    {expectedUsersWon : Content D → paper_mixed_content_strategy D → ℝ}
    {cost : Content D → ℝ} {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsFiniteMeasure μ] {equilibriumPayoff : ℝ}
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff expectedUsersWon cost) μ equilibriumPayoff)
    (hcont : PerturbationCostContinuous cost)
    (hlower :
      paper_atom_event_expected_users_won_lower_bounds_for_atoms
        (D := D) (P := P) expectedUsersWon cost μ equilibriumPayoff)
    (p : Content D) :
    μ.real ({p} : Set (Content D)) = 0 :=
  measureReal_singleton_eq_zero_of_expectedUsersWon_event_gain_lower_bounds
    (P := P) hno hcont hlower p

/--
Proposition `atom`, product-integral atomlessness theorem: once the expected
assigned-user term is interpreted as the product integral over independent
symmetric draws, atomlessness follows from no profitable pure deviation,
support payoff indifference, integrability, nonnegative users, and cost
continuity.
-/
theorem paper_proposition_atom_atomless_of_integral_semantics
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff : ℝ} {i0 : Fin N} {j : Fin P}
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j) cost)
        μ equilibriumPayoff)
    (hcont : PerturbationCostContinuous cost)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j) cost p μ =
          equilibriumPayoff)
    (hint_base :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hint_perturb :
      ∀ (p : Content D) {ε : ℝ}, paper_has_content_point_mass μ p → 0 < ε →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users
              (deviateProfile profile j (fun d => p d + ε * users i0 d)) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ))) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_of_integral_semantics
    (D := D) (N := N) (P := P)
    hno hcont husers_nonneg hzero hpayoff hint_base hint_perturb

/--
Proposition `atom`, `NoAtoms` form of the product-integral atomlessness
theorem.
-/
theorem paper_proposition_atom_noAtoms_of_integral_semantics
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff : ℝ} {i0 : Fin N} {j : Fin P}
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j) cost)
        μ equilibriumPayoff)
    (hcont : PerturbationCostContinuous cost)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j) cost p μ =
          equilibriumPayoff)
    (hint_base :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hint_perturb :
      ∀ (p : Content D) {ε : ℝ}, paper_has_content_point_mass μ p → 0 < ε →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users
              (deviateProfile profile j (fun d => p d + ε * users i0 d)) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ))) :
    MeasureTheory.NoAtoms μ :=
  noAtoms_of_integral_semantics
    (D := D) (N := N) (P := P)
    hno hcont husers_nonneg hzero hpayoff hint_base hint_perturb

/--
Proposition `atom`, singleton-probability form of the product-integral
atomlessness theorem.
-/
theorem paper_proposition_atom_real_point_mass_zero_of_integral_semantics
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff : ℝ} {i0 : Fin N} {j : Fin P}
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j) cost)
        μ equilibriumPayoff)
    (hcont : PerturbationCostContinuous cost)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j) cost p μ =
          equilibriumPayoff)
    (hint_base :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hint_perturb :
      ∀ (p : Content D) {ε : ℝ}, paper_has_content_point_mass μ p → 0 < ε →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users
              (deviateProfile profile j (fun d => p d + ε * users i0 d)) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (p : Content D) :
    μ.real ({p} : Set (Content D)) = 0 :=
  measureReal_singleton_eq_zero_of_integral_semantics
    (D := D) (N := N) (P := P)
    hno hcont husers_nonneg hzero hpayoff hint_base hint_perturb p

/--
Proposition `atom`, source cost-family product-integral theorem: for
`c(p)=ν(p)^β`, `β >= 1`, atomlessness follows from the product-integral
interpretation of expected assigned users.
-/
theorem paper_proposition_atom_atomless_norm_rpow_cost_of_integral_semantics
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β))
        μ equilibriumPayoff)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β) p μ =
          equilibriumPayoff)
    (hint_base :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hint_perturb :
      ∀ (p : Content D) {ε : ℝ}, paper_has_content_point_mass μ p → 0 < ε →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users
              (deviateProfile profile j (fun d => p d + ε * users i0 d)) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ))) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_normRpowCost_of_integral_semantics
    (D := D) (N := N) (P := P)
    ν hβ hcont hno husers_nonneg hzero hpayoff hint_base hint_perturb

/--
Proposition `atom`, source cost-family product-integral `NoAtoms` form.
-/
theorem paper_proposition_atom_noAtoms_norm_rpow_cost_of_integral_semantics
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β))
        μ equilibriumPayoff)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β) p μ =
          equilibriumPayoff)
    (hint_base :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hint_perturb :
      ∀ (p : Content D) {ε : ℝ}, paper_has_content_point_mass μ p → 0 < ε →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users
              (deviateProfile profile j (fun d => p d + ε * users i0 d)) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ))) :
    MeasureTheory.NoAtoms μ :=
  noAtoms_normRpowCost_of_integral_semantics
    (D := D) (N := N) (P := P)
    ν hβ hcont hno husers_nonneg hzero hpayoff hint_base hint_perturb

/--
Proposition `atom`, source cost-family product-integral singleton-probability
form.
-/
theorem paper_proposition_atom_real_point_mass_zero_norm_rpow_cost_of_integral_semantics
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β))
        μ equilibriumPayoff)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β) p μ =
          equilibriumPayoff)
    (hint_base :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hint_perturb :
      ∀ (p : Content D) {ε : ℝ}, paper_has_content_point_mass μ p → 0 < ε →
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users
              (deviateProfile profile j (fun d => p d + ε * users i0 d)) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (p : Content D) :
    μ.real ({p} : Set (Content D)) = 0 :=
  measureReal_singleton_eq_zero_normRpowCost_of_integral_semantics
    (D := D) (N := N) (P := P)
    ν hβ hcont hno husers_nonneg hzero hpayoff hint_base hint_perturb p

/--
Proposition `atom`, source cost-family product-integral theorem with
measurability premises.  Boundedness of assigned-user mass supplies the
integrability required by the source perturbation argument.
-/
theorem paper_proposition_atom_atomless_norm_rpow_cost_of_integral_semantics_aemeasurable
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β))
        μ equilibriumPayoff)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β) p μ =
          equilibriumPayoff)
    (hmeas_base :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        MeasureTheory.AEStronglyMeasurable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hmeas_perturb :
      ∀ (p : Content D) {ε : ℝ}, paper_has_content_point_mass μ p → 0 < ε →
        MeasureTheory.AEStronglyMeasurable
          (fun profile : Fin P → Content D =>
            usersWon users
              (deviateProfile profile j (fun d => p d + ε * users i0 d)) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ))) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_normRpowCost_of_integral_semantics_aemeasurable
    (D := D) (N := N) (P := P)
    ν hβ hcont hno husers_nonneg hzero hpayoff hmeas_base hmeas_perturb

/--
Proposition `atom`, source cost-family product-integral `NoAtoms` form with
measurability premises.
-/
theorem paper_proposition_atom_noAtoms_norm_rpow_cost_of_integral_semantics_aemeasurable
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β))
        μ equilibriumPayoff)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β) p μ =
          equilibriumPayoff)
    (hmeas_base :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        MeasureTheory.AEStronglyMeasurable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hmeas_perturb :
      ∀ (p : Content D) {ε : ℝ}, paper_has_content_point_mass μ p → 0 < ε →
        MeasureTheory.AEStronglyMeasurable
          (fun profile : Fin P → Content D =>
            usersWon users
              (deviateProfile profile j (fun d => p d + ε * users i0 d)) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ))) :
    MeasureTheory.NoAtoms μ :=
  noAtoms_normRpowCost_of_integral_semantics_aemeasurable
    (D := D) (N := N) (P := P)
    ν hβ hcont hno husers_nonneg hzero hpayoff hmeas_base hmeas_perturb

/--
Proposition `atom`, source cost-family product-integral singleton-probability
form with measurability premises.
-/
theorem paper_proposition_atom_real_point_mass_zero_norm_rpow_cost_of_integral_semantics_aemeasurable
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β))
        μ equilibriumPayoff)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β) p μ =
          equilibriumPayoff)
    (hmeas_base :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        MeasureTheory.AEStronglyMeasurable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hmeas_perturb :
      ∀ (p : Content D) {ε : ℝ}, paper_has_content_point_mass μ p → 0 < ε →
        MeasureTheory.AEStronglyMeasurable
          (fun profile : Fin P → Content D =>
            usersWon users
              (deviateProfile profile j (fun d => p d + ε * users i0 d)) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (p : Content D) :
    μ.real ({p} : Set (Content D)) = 0 :=
  measureReal_singleton_eq_zero_normRpowCost_of_integral_semantics_aemeasurable
    (D := D) (N := N) (P := P)
    ν hβ hcont hno husers_nonneg hzero hpayoff hmeas_base hmeas_perturb p

/--
Proposition `atom`, source cost-family product-integral theorem with finite
tie-share measurability discharged internally.
-/
theorem paper_proposition_atom_atomless_norm_rpow_cost_of_integral_semantics_measurable
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β))
        μ equilibriumPayoff)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β) p μ =
          equilibriumPayoff) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_normRpowCost_of_integral_semantics_measurable
    (D := D) (N := N) (P := P)
    ν hβ hcont hno husers_nonneg hzero hpayoff

/--
Proposition `atom`, direct norm-power endpoint: finite tie-share measurability
is internal, and the payoff equality needed at a putative atom follows from
the explicit almost-everywhere support-payoff equality.
-/
theorem paper_proposition_atom_atomless_norm_rpow_cost_of_ae_equilibrium_payoff
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β))
        μ equilibriumPayoff)
    (hae_support_payoff :
      ∀ᵐ p ∂μ,
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β) p μ = equilibriumPayoff)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0)) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_normRpowCost_of_integral_semantics_measurable_ae_equilibrium_payoff
    (D := D) (N := N) (P := P)
    ν hβ hcont hno hae_support_payoff husers_nonneg hzero

/--
Proposition `atom`, direct norm-power endpoint: the mixed strategy's expected
pure payoff equals its equilibrium payoff, so no-profitable-deviation derives
the required almost-everywhere support-payoff equality internally.
-/
theorem paper_proposition_atom_atomless_norm_rpow_cost_of_mixed_payoff_integral_eq
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β))
        μ equilibriumPayoff)
    (hmixed_payoff_integrable :
      MeasureTheory.Integrable
        (fun p =>
          paper_source_mixed_pure_payoff
            (paper_expected_users_won_against_symmetric_mixed users j)
            (normRpowCost ν β) p μ)
        μ)
    (hmixed_payoff :
      ∫ p,
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β) p μ ∂μ = equilibriumPayoff)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0)) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_normRpowCost_of_integral_semantics_measurable_mixed_payoff_integral_eq
    (D := D) (N := N) (P := P)
    ν hβ hcont hno hmixed_payoff_integrable hmixed_payoff husers_nonneg hzero

/--
Proposition `atom`, source cost-family product-integral `NoAtoms` form with
finite tie-share measurability discharged internally.
-/
theorem paper_proposition_atom_noAtoms_norm_rpow_cost_of_integral_semantics_measurable
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β))
        μ equilibriumPayoff)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β) p μ =
          equilibriumPayoff) :
    MeasureTheory.NoAtoms μ :=
  noAtoms_normRpowCost_of_integral_semantics_measurable
    (D := D) (N := N) (P := P)
    ν hβ hcont hno husers_nonneg hzero hpayoff

/--
Proposition `atom`, source cost-family product-integral singleton-probability
form with finite tie-share measurability discharged internally.
-/
theorem paper_proposition_atom_real_point_mass_zero_norm_rpow_cost_of_integral_semantics_measurable
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β))
        μ equilibriumPayoff)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hpayoff :
      ∀ p : Content D, paper_has_content_point_mass μ p →
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β) p μ =
          equilibriumPayoff)
    (p : Content D) :
    μ.real ({p} : Set (Content D)) = 0 :=
  measureReal_singleton_eq_zero_normRpowCost_of_integral_semantics_measurable
    (D := D) (N := N) (P := P)
    ν hβ hcont hno husers_nonneg hzero hpayoff p

/--
Proposition `atom`, source cost-family theorem from the bundled source-facing
symmetric mixed equilibrium conditions.
-/
theorem paper_proposition_atom_atomless_norm_rpow_cost_of_source_symmetric_mixed_equilibrium
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (heq :
      paper_source_symmetric_mixed_equilibrium_conditions
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β)) μ)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0)) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_normRpowCost_of_source_symmetric_mixed_equilibrium
    (D := D) (N := N) (P := P)
    ν hβ hcont heq husers_nonneg hzero

/--
Proposition `atom`, source cost-family `NoAtoms` theorem from the bundled
source-facing symmetric mixed equilibrium conditions.
-/
theorem paper_proposition_atom_noAtoms_norm_rpow_cost_of_source_symmetric_mixed_equilibrium
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (heq :
      paper_source_symmetric_mixed_equilibrium_conditions
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β)) μ)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0)) :
    MeasureTheory.NoAtoms μ :=
  noAtoms_normRpowCost_of_source_symmetric_mixed_equilibrium
    (D := D) (N := N) (P := P)
    ν hβ hcont heq husers_nonneg hzero

/--
Proposition `atom`, source cost-family singleton-probability theorem from the
bundled source-facing symmetric mixed equilibrium conditions.
-/
theorem paper_proposition_atom_real_point_mass_zero_norm_rpow_cost_of_source_symmetric_mixed_equilibrium
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {β : ℝ} {i0 : Fin N} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (heq :
      paper_source_symmetric_mixed_equilibrium_conditions
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β)) μ)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (p : Content D) :
    μ.real ({p} : Set (Content D)) = 0 :=
  measureReal_singleton_eq_zero_normRpowCost_of_source_symmetric_mixed_equilibrium
    (D := D) (N := N) (P := P)
    ν hβ hcont heq husers_nonneg hzero p

/--
Proposition `atom`, source cost-family theorem with the paper's global
nonzero-user assumption: for `c(p)=ν(p)^β`, `β >= 1`, every symmetric mixed
equilibrium satisfying the bundled source equilibrium conditions is atomless.
-/
theorem paper_proposition_atom_atomless_norm_rpow_cost_of_source_symmetric_mixed_equilibrium_nonzero_users
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {β : ℝ} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (heq :
      paper_source_symmetric_mixed_equilibrium_conditions
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β)) μ)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i)) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_normRpowCost_of_source_symmetric_mixed_equilibrium_nonzero_users
    (D := D) (N := N) (P := P) (j := j)
    ν hβ hcont heq husers_nonneg husers_nonzero

/--
Proposition `atom`, `NoAtoms` source cost-family theorem with the paper's
global nonzero-user assumption.
-/
theorem paper_proposition_atom_noAtoms_norm_rpow_cost_of_source_symmetric_mixed_equilibrium_nonzero_users
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {β : ℝ} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (heq :
      paper_source_symmetric_mixed_equilibrium_conditions
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β)) μ)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i)) :
    MeasureTheory.NoAtoms μ :=
  noAtoms_normRpowCost_of_source_symmetric_mixed_equilibrium_nonzero_users
    (D := D) (N := N) (P := P) (j := j)
    ν hβ hcont heq husers_nonneg husers_nonzero

/--
Proposition `atom`, singleton-probability source cost-family theorem with the
paper's global nonzero-user assumption.
-/
theorem paper_proposition_atom_real_point_mass_zero_norm_rpow_cost_of_source_symmetric_mixed_equilibrium_nonzero_users
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {β : ℝ} {j : Fin P}
    (ν : SourceNorm D) (hβ : 1 ≤ β)
    (hcont : SourceNormPerturbationContinuous ν)
    (heq :
      paper_source_symmetric_mixed_equilibrium_conditions
        (paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j)
          (normRpowCost ν β)) μ)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (p : Content D) :
    μ.real ({p} : Set (Content D)) = 0 :=
  measureReal_singleton_eq_zero_normRpowCost_of_source_symmetric_mixed_equilibrium_nonzero_users
    (D := D) (N := N) (P := P) (j := j)
    ν hβ hcont heq husers_nonneg husers_nonzero p

/--
Proposition `atom`, source cost-family form: for `c(p)=ν(p)^β`, `β >= 1`,
the explicit event-gain lower-bound package implies atomlessness.
-/
theorem paper_proposition_atom_atomless_norm_rpow_cost_of_event_gain_lower_bounds
    {D P : ℕ} [Nontrivial (Fin P)]
    {payoff : Content D → paper_mixed_content_strategy D → ℝ}
    {μ : paper_mixed_content_strategy D} [MeasureTheory.IsFiniteMeasure μ]
    {equilibriumPayoff β : ℝ} (ν : SourceNorm D)
    (hβ : 1 ≤ β) (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation payoff μ equilibriumPayoff)
    (hlower :
      paper_atom_event_payoff_lower_bounds_for_atoms (D := D) (P := P)
        payoff (normRpowCost ν β) μ equilibriumPayoff) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_normRpowCost_of_event_gain_lower_bounds
    (P := P) ν hβ hcont hno hlower

/--
Proposition `atom`, source cost-family mathlib `NoAtoms` form.
-/
theorem paper_proposition_atom_noAtoms_norm_rpow_cost_of_event_gain_lower_bounds
    {D P : ℕ} [Nontrivial (Fin P)]
    {payoff : Content D → paper_mixed_content_strategy D → ℝ}
    {μ : paper_mixed_content_strategy D} [MeasureTheory.IsFiniteMeasure μ]
    {equilibriumPayoff β : ℝ} (ν : SourceNorm D)
    (hβ : 1 ≤ β) (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation payoff μ equilibriumPayoff)
    (hlower :
      paper_atom_event_payoff_lower_bounds_for_atoms (D := D) (P := P)
        payoff (normRpowCost ν β) μ equilibriumPayoff) :
    MeasureTheory.NoAtoms μ :=
  noAtoms_normRpowCost_of_event_gain_lower_bounds
    (P := P) ν hβ hcont hno hlower

/--
Proposition `atom`, source cost-family real singleton-probability form.
-/
theorem paper_proposition_atom_real_point_mass_zero_norm_rpow_cost_of_event_gain_lower_bounds
    {D P : ℕ} [Nontrivial (Fin P)]
    {payoff : Content D → paper_mixed_content_strategy D → ℝ}
    {μ : paper_mixed_content_strategy D} [MeasureTheory.IsFiniteMeasure μ]
    {equilibriumPayoff β : ℝ} (ν : SourceNorm D)
    (hβ : 1 ≤ β) (hcont : SourceNormPerturbationContinuous ν)
    (hno :
      paper_symmetric_mixed_no_profitable_pure_deviation payoff μ equilibriumPayoff)
    (hlower :
      paper_atom_event_payoff_lower_bounds_for_atoms (D := D) (P := P)
        payoff (normRpowCost ν β) μ equilibriumPayoff)
    (p : Content D) :
    μ.real ({p} : Set (Content D)) = 0 :=
  measureReal_singleton_eq_zero_normRpowCost_of_event_gain_lower_bounds
    (P := P) ν hβ hcont hno hlower p

/--
Proposition `atom`: event that all sampled opposing producers draw the same
content vector.
-/
abbrev paper_all_opponents_draw_content {D K : ℕ} (p : Content D) :
    Set (Fin K → Content D) :=
  AllOpponentsDrawContent (K := K) p

/--
Proposition `atom`, product-measure event probability: the probability that all
`K` opponents independently draw `p` is `μ({p})^K`.
-/
theorem paper_proposition_atom_all_opponents_draw_content_measure_eq_pow
    {D K : ℕ} {μ : paper_mixed_content_strategy D}
    [MeasureTheory.SigmaFinite μ] (p : Content D) :
    MeasureTheory.Measure.pi (fun _ : Fin K => μ)
        (paper_all_opponents_draw_content (K := K) p) =
      μ ({p} : Set (Content D)) ^ K :=
  measure_allOpponentsDrawContent_eq_pow (K := K) (μ := μ) p

/--
Proposition `atom`, real-valued product-measure event probability for finite
mixed strategies.
-/
theorem paper_proposition_atom_all_opponents_draw_content_measureReal_eq_pow
    {D K : ℕ} {μ : paper_mixed_content_strategy D}
    [MeasureTheory.IsFiniteMeasure μ] (p : Content D) :
    (MeasureTheory.Measure.pi (fun _ : Fin K => μ)).real
        (paper_all_opponents_draw_content (K := K) p) =
      (μ.real ({p} : Set (Content D))) ^ K :=
  measureReal_allOpponentsDrawContent_eq_pow (K := K) (μ := μ) p

/--
Lemma `cdf`, raw interior formula:
`(r^β / N)^(1/(P-1))`.
-/
noncomputable abbrev paper_single_genre_cdf_raw
    (N P : ℕ) (β r : ℝ) : ℝ :=
  singleGenreCdfRaw N P β r

/--
Lemma `cdf`, clipped source formula:
`F(r) = min(1, (r^β / N)^(1/(P-1)))`.
-/
noncomputable abbrev paper_single_genre_cdf
    (N P : ℕ) (β r : ℝ) : ℝ :=
  singleGenreCdf N P β r

/-- Lemma `cdf`: the closed-form CDF is nonnegative on nonnegative radii. -/
theorem paper_single_genre_cdf_nonnegative {N P : ℕ} [Nonempty (Fin N)]
    {β r : ℝ} (hr : 0 ≤ r) :
    0 ≤ paper_single_genre_cdf N P β r :=
  singleGenreCdf_nonneg hr

/-- Lemma `cdf`: the closed-form CDF is bounded above by one. -/
theorem paper_single_genre_cdf_le_one {N P : ℕ} {β r : ℝ} :
    paper_single_genre_cdf N P β r ≤ 1 :=
  singleGenreCdf_le_one

/-- Lemma `cdf`: the closed-form CDF starts at zero when `β > 0`. -/
theorem paper_single_genre_cdf_zero {N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {β : ℝ} (hβ : 0 < β) :
    paper_single_genre_cdf N P β 0 = 0 :=
  singleGenreCdf_zero hβ

/--
Lemma `cdf`, scalar support consequence: an exact lower-CDF formula on the
nonnegative radii puts zero in the topological support of that scalar law.
This deliberately does not identify an arbitrary content strategy with its
norm pushforward; that source-to-model bridge is a separate premise.
-/
theorem paper_lemma_cdf_scalar_zero_mem_support
    {N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {β : ℝ} {μ : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure μ]
    (hβ : 0 < β)
    (hcdf : ∀ r : ℝ, 0 ≤ r →
      AppliedModelingLib.Probability.lowerCDFMass μ r = paper_single_genre_cdf N P β r) :
    (0 : ℝ) ∈ μ.support :=
  zero_mem_support_of_lowerCDFMass_eq_singleGenreCdf hβ hcdf

/--
Lemma `cdf`, corrected content-support consequence: the scalar CDF applies to
the source-norm pushforward.  It yields zero content support only when the
source norm is measurable and explicitly detects every content neighborhood
of zero.  This keeps the scalar-to-content bridge visible rather than treating
the paper's CDF notation as a content-law identity.
-/
theorem paper_lemma_cdf_content_zero_mem_support_of_source_norm
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {ν : SourceNorm D} {μ : MeasureTheory.Measure (Content D)}
    [MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.map ν.norm μ)]
    {β : ℝ}
    (hmeas : Measurable ν.norm)
    (hzero_detect : SourceNormZeroReflectsNeighborhood ν)
    (hβ : 0 < β)
    (hcdf : ∀ r : ℝ, 0 ≤ r →
      AppliedModelingLib.Probability.lowerCDFMass (MeasureTheory.Measure.map ν.norm μ) r =
        paper_single_genre_cdf N P β r) :
    (0 : Content D) ∈ μ.support :=
  zero_mem_support_of_sourceNormLaw_lowerCDFMass_eq_singleGenreCdf
    hmeas hzero_detect hβ hcdf

/--
Lemma `cdf`, concrete Euclidean version: an exact CDF for the Euclidean-norm
pushforward puts zero in the content strategy's topological support.
-/
theorem paper_lemma_cdf_content_zero_mem_support_of_l2_law
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {μ : MeasureTheory.Measure (Content D)}
    [MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.map (SourceNorm.l2 D).norm μ)]
    {β : ℝ}
    (hβ : 0 < β)
    (hcdf : ∀ r : ℝ, 0 ≤ r →
      AppliedModelingLib.Probability.lowerCDFMass
        (MeasureTheory.Measure.map (SourceNorm.l2 D).norm μ) r =
        paper_single_genre_cdf N P β r) :
    (0 : Content D) ∈ μ.support :=
  zero_mem_support_of_l2Law_lowerCDFMass_eq_singleGenreCdf hβ hcdf

/--
Lemma `cdf`, finite `Lq` version: an exact CDF for a positive `Lq`-norm
pushforward puts zero in the content strategy's topological support.
-/
theorem paper_lemma_cdf_content_zero_mem_support_of_lp_law
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {q : ℝ} (hq : 0 < q) {μ : MeasureTheory.Measure (Content D)}
    [MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.map (SourceNorm.lp D hq).norm μ)]
    {β : ℝ}
    (hβ : 0 < β)
    (hcdf : ∀ r : ℝ, 0 ≤ r →
      AppliedModelingLib.Probability.lowerCDFMass
        (MeasureTheory.Measure.map (SourceNorm.lp D hq).norm μ) r =
        paper_single_genre_cdf N P β r) :
    (0 : Content D) ∈ μ.support :=
  zero_mem_support_of_lpLaw_lowerCDFMass_eq_singleGenreCdf hq hβ hcdf

/-- Lemma `cdf`: for nonnegative radii, the closed-form CDF is monotone. -/
theorem paper_single_genre_cdf_mono_on_nonnegative {N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)] {β r s : ℝ}
    (hβ : 0 ≤ β) (hr : 0 ≤ r) (hrs : r ≤ s) :
    paper_single_genre_cdf N P β r ≤ paper_single_genre_cdf N P β s :=
  singleGenreCdf_mono_on_nonnegative hβ hr hrs

/-- Lemma `cdf`: the raw formula reaches one at the source support cap. -/
theorem paper_single_genre_cdf_raw_at_support_cap {N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)] {β : ℝ}
    (hβ : 0 < β) :
    paper_single_genre_cdf_raw N P β ((N : ℝ) ^ β⁻¹) = 1 :=
  singleGenreCdfRaw_at_support_cap hβ

/-- Lemma `cdf`: the closed-form CDF reaches one at `N^(1 / β)`. -/
theorem paper_single_genre_cdf_at_support_cap {N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)] {β : ℝ}
    (hβ : 0 < β) :
    paper_single_genre_cdf N P β ((N : ℝ) ^ β⁻¹) = 1 :=
  singleGenreCdf_at_support_cap hβ

/-- Lemma `cdf`: after the source support cap `N^(1 / β)`, the CDF is one. -/
theorem paper_single_genre_cdf_eq_one_of_support_cap_le {N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)] {β r : ℝ}
    (hβ : 0 < β) (hcap : (N : ℝ) ^ β⁻¹ ≤ r) :
    paper_single_genre_cdf N P β r = 1 :=
  singleGenreCdf_eq_one_of_support_cap_le hβ hcap

/--
Lemma `cdf`: before the source support cap `N^(1 / β)`, the clipped CDF equals
the raw interior formula.
-/
theorem paper_single_genre_cdf_eq_raw_of_le_support_cap {N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)] {β r : ℝ}
    (hβ : 0 < β) (hr : 0 ≤ r) (hle : r ≤ (N : ℝ) ^ β⁻¹) :
    paper_single_genre_cdf N P β r =
      paper_single_genre_cdf_raw N P β r :=
  singleGenreCdf_eq_raw_of_le_support_cap hβ hr hle

/--
Lemma `cdf`, probability identity: below the clipping point,
`F(r)^(P-1) = r^β / N`.
-/
theorem paper_single_genre_cdf_power_eq_ratio_of_raw_le_one {N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)] {β r : ℝ}
    (hr : 0 ≤ r)
    (hraw : paper_single_genre_cdf_raw N P β r ≤ 1) :
    (paper_single_genre_cdf N P β r) ^ ((P : ℝ) - 1) =
      r ^ β / (N : ℝ) :=
  singleGenreCdf_power_eq_ratio_of_raw_le_one hr hraw

/--
Lemma `cdf`, support-interval probability identity: for
`0 <= r <= N^(1 / β)`, `F(r)^(P-1) = r^β / N`.
-/
theorem paper_single_genre_cdf_power_eq_ratio_of_le_support_cap {N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)] {β r : ℝ}
    (hβ : 0 < β) (hr : 0 ≤ r) (hle : r ≤ (N : ℝ) ^ β⁻¹) :
    (paper_single_genre_cdf N P β r) ^ ((P : ℝ) - 1) =
      r ^ β / (N : ℝ) :=
  singleGenreCdf_power_eq_ratio_of_le_support_cap hβ hr hle

/--
Lemma `cdf`, interior zero-profit identity: below the clipping point,
`N F(r)^(P-1) - r^β = 0`.
-/
theorem paper_single_genre_cdf_zero_profit_identity {N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)] {β r : ℝ}
    (hr : 0 ≤ r)
    (hraw : paper_single_genre_cdf_raw N P β r ≤ 1) :
    (N : ℝ) * (paper_single_genre_cdf N P β r) ^ ((P : ℝ) - 1) -
        r ^ β = 0 :=
  singleGenreCdf_zero_profit_identity_of_raw_le_one hr hraw

/--
Lemma `cdf`, support-interval zero-profit identity: for
`0 <= r <= N^(1 / β)`, the expected assigned-user term exactly matches cost.
-/
theorem paper_single_genre_cdf_zero_profit_identity_of_le_support_cap {N P : ℕ}
    [Nonempty (Fin N)] [Nontrivial (Fin P)] {β r : ℝ}
    (hβ : 0 < β) (hr : 0 ≤ r) (hle : r ≤ (N : ℝ) ^ β⁻¹) :
    (N : ℝ) * (paper_single_genre_cdf N P β r) ^ ((P : ℝ) - 1) -
        r ^ β = 0 :=
  singleGenreCdf_zero_profit_identity_of_le_support_cap hβ hr hle

/--
Corollary `onepopulation`, quality-CDF formula surface: for homogeneous users,
the single-genre quality distribution has source support cap `N^(1 / β)`, the
raw Lemma `cdf` power law below that cap, and value one after the cap.
-/
theorem paper_corollary_onepopulation_quality_cdf_formula_and_support_cap
    {N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)] {β : ℝ}
    (hβ : 0 < β) :
    paper_single_genre_cdf N P β ((N : ℝ) ^ β⁻¹) = 1 ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ (N : ℝ) ^ β⁻¹ →
        paper_single_genre_cdf N P β r =
          ((r ^ β) / (N : ℝ)) ^ (((P : ℝ) - 1)⁻¹)) ∧
      (∀ r : ℝ, (N : ℝ) ^ β⁻¹ ≤ r →
        paper_single_genre_cdf N P β r = 1) :=
  onePopulation_quality_cdf_formula_and_support_cap hβ

/--
Corollary `onepopulation`, concrete unit-support law: inverse-transforming
uniform unit-interval mass gives a probability measure whose CDF is exactly
the Lemma `cdf` formula for one homogeneous population on `[0,1]`.
-/
theorem paper_corollary_onepopulation_concrete_quality_law_cdf
    {P : ℕ} [Nontrivial (Fin P)] {β z : ℝ}
    (hβ : 0 < β) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    onePopulationSingleGenreQualityLaw P β (Set.Iic z) =
      ENNReal.ofReal (paper_single_genre_cdf 1 P β z) :=
  onePopulationSingleGenreQualityLaw_cdf_eq_singleGenreCdf_on_unitInterval hβ hz

/--
Lemma `cdf`, general concrete quality law: scaling the unit-interval
inverse-transform sampler gives a probability law on the paper's support cap
whose CDF is the displayed clipped source formula on that support.
-/
theorem paper_lemma_cdf_concrete_quality_law
    {N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)] {β z : ℝ}
    (hβ : 0 < β)
    (hz : z ∈ Set.Icc (0 : ℝ) ((N : ℝ) ^ β⁻¹)) :
    singleGenreQualityLaw N P β (Set.Iic z) =
      ENNReal.ofReal (paper_single_genre_cdf N P β z) :=
  singleGenreQualityLaw_cdf_eq_singleGenreCdf_on_support hβ hz

/--
Lemma `cdf`, concrete content norm form: for a measurable source norm and a
unit genre, the norm pushforward of the ray law has the source clipped CDF at
every nonnegative threshold.
-/
theorem paper_lemma_cdf_concrete_ray_norm_law
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)] {β z : ℝ}
    (ν : SourceNorm D) {genre : Content D}
    (hnorm_meas : Measurable ν.norm) (hgenre_norm : ν.norm genre = 1)
    (hβ : 0 < β) (hz : 0 ≤ z) :
    Measure.map ν.norm (singleGenreContentLaw N P β genre) (Set.Iic z) =
      ENNReal.ofReal (paper_single_genre_cdf N P β z) :=
  singleGenreContentLaw_sourceNorm_map_cdf_eq_singleGenreCdf_of_nonneg
    ν hnorm_meas hgenre_norm hβ hz

/--
Lemma `cdf`, content-level form: putting the concrete quality law on a fixed
candidate genre gives the source CDF for each user whose score on that genre
is positive.
-/
theorem paper_lemma_cdf_concrete_single_genre_content_score_law
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {β z : ℝ} {genre u : Content D}
    (hβ : 0 < β) (hscore : 0 < paper_inferred_user_value u genre)
    (hz : z ∈ Set.Icc (0 : ℝ)
      (paper_inferred_user_value u genre * ((N : ℝ) ^ β⁻¹))) :
    Measure.map (fun p : Content D => paper_inferred_user_value u p)
        (singleGenreContentLaw N P β genre) (Set.Iic z) =
      ENNReal.ofReal
        (paper_single_genre_cdf N P β
          (z / paper_inferred_user_value u genre)) :=
  singleGenreContentLaw_score_map_cdf_on_support hβ hscore hz

/--
Lemma `cdf`, tie-null score law: a positive-score user sees no atoms under the
concrete single-genre content distribution.
-/
theorem paper_lemma_cdf_concrete_single_genre_score_law_no_atoms
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {β : ℝ} {genre u : Content D}
    (hβ : 0 < β) (hscore : 0 < paper_inferred_user_value u genre) :
    MeasureTheory.NoAtoms
      (Measure.map (fun p : Content D => paper_inferred_user_value u p)
        (singleGenreContentLaw N P β genre)) :=
  singleGenreContentLaw_score_map_noAtoms hβ hscore

/--
Lemma `optsingledirection`, concrete-law payoff reduction: when all users
score the candidate genre positively, the actual uniform-tie payoff is the
sum of its weak score-CDF masses.  Equality with strict score masses is proved
from atomlessness internally.
-/
theorem paper_lemma_optsingledirection_concrete_law_weak_cdf_payoff
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {genre : Content D}
    (hβ : 0 < β)
    (hscore : ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre)
    (j : Fin P) (p : Content D) :
    ExpectedUsersWonAgainstSymmetricMixed users j
        p (singleGenreContentLaw N P β genre) =
      ∑ i : Fin N,
        ((singleGenreContentLaw N P β genre).real
          {q : Content D |
            paper_inferred_user_value (users i) q ≤
              paper_inferred_user_value (users i) p}) ^ (P - 1) :=
  expectedUsersWonAgainstSymmetricMixed_singleGenreContentLaw_eq_sum_weakScoreMass
    hβ hscore j p

/--
Lemma `optsingledirection`, explicit concrete-law payoff: for every feasible
nonnegative deviation, the actual uniform-tie assigned-user mass is the sum
of the paper's clipped CDF powers at the user-score ratios.
-/
theorem paper_lemma_optsingledirection_concrete_law_cdf_payoff
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {genre p : Content D}
    (hβ : 0 < β)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hp : NonnegativeContent p)
    (hscore : ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre)
    (j : Fin P) :
    ExpectedUsersWonAgainstSymmetricMixed users j
        p (singleGenreContentLaw N P β genre) =
      ∑ i : Fin N,
        (paper_single_genre_cdf N P β
          (paper_inferred_user_value (users i) p /
            paper_inferred_user_value (users i) genre)) ^ (P - 1) :=
  expectedUsersWonAgainstSymmetricMixed_singleGenreContentLaw_eq_cdfSum
    hβ husers hp hscore j

/--
Lemma `cdf`/`optsingledirection`, support-indifference endpoint: every
topological-support action of the concrete unit-genre ray law earns exactly
zero actual mixed payoff.
-/
theorem paper_single_genre_concrete_law_support_payoff_zero
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {genre p : Content D}
    (ν : SourceNorm D) (hβ : 0 < β)
    (hgenre_norm : ν.norm genre = 1)
    (hgenre_nonnegative : NonnegativeContent genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hscore : ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre)
    (j : Fin P) (hp : p ∈ (singleGenreContentLaw N P β genre).support) :
    paper_source_mixed_pure_payoff
      (paper_expected_users_won_against_symmetric_mixed users j)
      (normRpowCost ν β) p (singleGenreContentLaw N P β genre) = 0 :=
  singleGenreContentLaw_support_action_sourceMixedPurePayoff_eq_zero
    ν hβ hgenre_norm hgenre_nonnegative husers hscore j hp

/--
Proposition `zeroutilitysinglegenre`, concrete source-Nash law: zero quality is
an actual topological-support action of the ray law and has zero actual
uniform-tie payoff.
-/
theorem paper_proposition_zeroutilitysinglegenre_concrete_zero_support_payoff
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {genre : Content D}
    (ν : SourceNorm D) (hβ : 0 < β)
    (hgenre_norm : ν.norm genre = 1)
    (hgenre_nonnegative : NonnegativeContent genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hscore : ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre)
    (j : Fin P) :
    (0 : Content D) ∈ (singleGenreContentLaw N P β genre).support ∧
      paper_source_mixed_pure_payoff
        (paper_expected_users_won_against_symmetric_mixed users j)
        (normRpowCost ν β) (0 : Content D)
        (singleGenreContentLaw N P β genre) = 0 := by
  refine ⟨zero_mem_singleGenreContentLaw_support hβ genre, ?_⟩
  exact singleGenreContentLaw_zero_sourceMixedPurePayoff_eq_zero
    ν hβ hgenre_norm hgenre_nonnegative husers hscore j

/--
Lemma `cdf`, concrete support: the ray law's topological support is exactly
the range of its continuous inverse-transform sampler.
-/
theorem paper_lemma_cdf_concrete_ray_law_support_eq_sampler_range
    {D N P : ℕ} [Nontrivial (Fin P)] {β : ℝ} (genre : Content D)
    (hβ : 0 < β) :
    (singleGenreContentLaw N P β genre).support =
      Set.range (singleGenreContentSample N P β genre) :=
  singleGenreContentLaw_support_eq_range genre hβ

/--
Corollary `onepopulation`, concrete support component: the ray law is
supported on the nonnegative quality segment from zero to
`N^(1 / beta) * genre`.
-/
theorem paper_corollary_onepopulation_concrete_law_support_subset_segment
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)] {β : ℝ}
    (genre : Content D) (hβ : 0 < β) :
    (singleGenreContentLaw N P β genre).support ⊆
      {p : Content D | ∃ q : ℝ, q ∈ Set.Icc (0 : ℝ) ((N : ℝ) ^ β⁻¹) ∧
        p = scaleContent q genre} :=
  singleGenreContentLaw_support_subset_scaledGenre_segment genre hβ

/--
Corrected single-genre assertion for the concrete ray law: after excluding the
zero support action before normalizing, the set of support genres is exactly
the chosen unit genre. This is the source display with its necessary
zero-support correction made explicit.
-/
abbrev paper_nonzero_support_genres {D : ℕ} (ν : SourceNorm D)
    (μ : MixedContentStrategy D) : Set (Content D) :=
  SourceNonzeroSupportGenres ν μ

theorem paper_theorem_singlegenre_corrected_nonzero_support_genre_eq
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {β : ℝ} {genre : Content D}
    (ν : SourceNorm D) (hβ : 0 < β) (hgenre_norm : ν.norm genre = 1) :
    paper_nonzero_support_genres ν (singleGenreContentLaw N P β genre) =
      ({genre} : Set (Content D)) :=
  singleGenreContentLaw_nonzeroSupportGenres_eq_singleton
    ν hβ hgenre_norm

/--
Corrected singleton-genre geometry: an arbitrary law whose nonzero support
normalizes to one genre has support on that genre's nonnegative source-norm
ray. This does not assume the proposed scalar CDF.
-/
theorem paper_lemma_singlegenre_support_subset_ray
    {D : ℕ} {ν : SourceNorm D} {μ : MixedContentStrategy D}
    {genre : Content D}
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D))) :
    μ.support ⊆ {p : Content D | ∃ r : ℝ, 0 ≤ r ∧
      p = scaleContent r genre} :=
  support_subset_scaledGenre_ray_of_singleton_nonzeroSupportGenres hgenres

/--
Corrected singleton-genre normalization: a genuinely represented genre has
source norm one. The nonzero support witness prevents vacuity.
-/
theorem paper_lemma_singlegenre_genre_norm_eq_one
    {D : ℕ} {ν : SourceNorm D} {μ : MixedContentStrategy D}
    {genre : Content D}
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hexists : ∃ p : Content D, p ∈ μ.support ∧ NonzeroContent p) :
    ν.norm genre = 1 :=
  sourceNorm_genre_eq_one_of_singleton_nonzeroSupportGenres_of_exists
    hgenres hexists

/--
Corrected singleton-genre feasibility: if every support action is in the
source action space, a genuinely represented genre is nonnegative.
-/
theorem paper_lemma_singlegenre_genre_nonnegative
    {D : ℕ} {ν : SourceNorm D} {μ : MixedContentStrategy D}
    {genre : Content D}
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hexists : ∃ p : Content D, p ∈ μ.support ∧ NonzeroContent p)
    (hsupport_nonnegative : μ.support ⊆
      {p : Content D | NonnegativeContent p}) :
    NonnegativeContent genre :=
  genre_nonnegative_of_singleton_nonzeroSupportGenres_of_exists
    hgenres hexists hsupport_nonnegative

/--
Corrected singleton-genre scalar atomlessness: atomless content induces an
atomless measurable source-norm law because every norm level meets the support
in at most one ray point.
-/
theorem paper_lemma_singlegenre_norm_law_no_atoms
    {D : ℕ} {ν : SourceNorm D} {μ : MixedContentStrategy D}
    [MeasureTheory.NoAtoms μ] {genre : Content D}
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hmeas_norm : Measurable ν.norm) :
    MeasureTheory.NoAtoms (Measure.map ν.norm μ) :=
  sourceNorm_map_noAtoms_of_singleton_nonzeroSupportGenres hgenres hmeas_norm

/--
Corrected singleton-genre score-law bridge: each user's score pushforward is
the source-norm pushforward scaled by that user's score against the genre.
-/
theorem paper_lemma_singlegenre_score_map_eq_scaled_norm_map
    {D : ℕ} {ν : SourceNorm D} {μ : MixedContentStrategy D}
    {genre u : Content D}
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hmeas_norm : Measurable ν.norm) :
    Measure.map (fun p : Content D => score u p) μ =
      Measure.map (fun r : ℝ => r * score u genre) (Measure.map ν.norm μ) :=
  score_map_eq_scale_sourceNorm_map_of_singleton_nonzeroSupportGenres
    hgenres hmeas_norm

/--
At a positive genre score, the corrected singleton-genre score CDF is the
source-norm CDF at the rescaled threshold. The scalar norm CDF itself remains
an explicit hypothesis for any paper-level equilibrium characterization.
-/
theorem paper_lemma_singlegenre_score_cdf_eq_norm_cdf_rescaled
    {D : ℕ} {ν : SourceNorm D} {μ : MixedContentStrategy D}
    {genre u : Content D} {z : ℝ}
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hmeas_norm : Measurable ν.norm)
    (hscore_pos : 0 < score u genre) :
    Measure.map (fun p : Content D => score u p) μ (Set.Iic z) =
      Measure.map ν.norm μ (Set.Iic (z / score u genre)) :=
  score_map_Iic_eq_sourceNorm_map_Iic_div_of_singleton_nonzeroSupportGenres
    hgenres hmeas_norm hscore_pos

/--
Corrected singleton-genre payoff bridge: at a support action, the actual
tie-aware expected-user term is a sum of the common scalar norm lower-CDF
mass. No formula for that scalar CDF is assumed.
-/
theorem paper_lemma_singlegenre_expected_users_won_eq_norm_cdf_sum
    {D N P : ℕ} {users : Fin N → Content D} {j : Fin P}
    {ν : SourceNorm D} {μ : MixedContentStrategy D}
    {genre p : Content D}
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.NoAtoms μ]
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hmeas_norm : Measurable ν.norm)
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hp : p ∈ μ.support) :
    paper_expected_users_won_against_symmetric_mixed users j p μ =
      ∑ i : Fin N,
        ((Measure.map ν.norm μ).real (Set.Iic (ν.norm p))) ^ (P - 1) :=
  expectedUsersWonAgainstSymmetricMixed_eq_sum_sourceNormLowerCdfMass_of_mem_support_of_singleton_nonzeroSupportGenres
    hgenres hmeas_norm hgenre_score hp

/--
Lemma `optsingledirection`, radial-minimum step: after setting `t=r^β`, the
objective `sum_i min(1,t a_i)/t - 1` is weakly decreasing in `t`.
-/
noncomputable abbrev paper_single_genre_radial_min_objective {N : ℕ}
    (a : Fin N → ℝ) (t : ℝ) : ℝ :=
  singleGenreRadialMinObjective a t

theorem paper_single_genre_radial_min_objective_antitone {N : ℕ}
    (a : Fin N → ℝ) {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    paper_single_genre_radial_min_objective a s ≤
      paper_single_genre_radial_min_objective a t :=
  singleGenreRadialMinObjective_antitone a ht hts

/--
Lemma `optsingledirection`, finite small-radius step: for any finite vector of
coefficients, some positive `t=r^β` makes every `min(1,t a_i)` unclipped.
-/
theorem paper_exists_positive_unclipped_scale {N : ℕ} (a : Fin N → ℝ) :
    ∃ t : ℝ, 0 < t ∧ ∀ i : Fin N, t * a i ≤ 1 :=
  exists_positive_unclipped_scale a

/--
Equation (2): the source optimization-program ratio objective
`sum_i y'_i / y_i`.
-/
noncomputable abbrev paper_ratio_objective {N : ℕ}
    (y y' : Fin N → ℝ) : ℝ :=
  ratioObjective y y'

/--
Lemma `optsingledirection` algebra: after substituting the single-genre CDF,
the normalized deviation payoff is `sum_i y'_i / y_i / N - 1`.
-/
noncomputable abbrev paper_single_genre_normalized_deviation {N : ℕ}
    (y y' : Fin N → ℝ) : ℝ :=
  singleGenreNormalizedDeviation y y'

theorem paper_single_genre_radial_min_objective_eq_normalized_deviation_of_unclipped
    {N : ℕ} [Nonempty (Fin N)] {y y' : Fin N → ℝ} {t : ℝ}
    (ht : t ≠ 0)
    (hclip : ∀ i, t * ((y' i / y i) / (N : ℝ)) ≤ 1) :
    paper_single_genre_radial_min_objective
        (fun i => (y' i / y i) / (N : ℝ)) t =
      paper_single_genre_normalized_deviation y y' :=
  singleGenreRadialMinObjective_eq_normalizedDeviation_of_unclipped ht hclip

/--
Lemma `optsingledirection` algebra: nonpositive normalized deviation payoff is
equivalent to the ratio objective being at most `N`.
-/
theorem paper_single_genre_normalized_deviation_nonpositive_iff {N : ℕ}
    [Nonempty (Fin N)] {y y' : Fin N → ℝ} :
    paper_single_genre_normalized_deviation y y' ≤ 0 ↔
      paper_ratio_objective y y' ≤ (N : ℝ) :=
  singleGenreNormalizedDeviation_nonpos_iff_ratio_le_card

/-- Lemma `optsingledirection`: ratio-objective condition over a feasible row set. -/
abbrev paper_single_genre_direction_condition {N : ℕ}
    (R : Set (Fin N → ℝ)) (y : Fin N → ℝ) : Prop :=
  SingleGenreDirectionCondition R y

/-- Lemma `optsingledirection`: no positive normalized deviations over a row set. -/
abbrev paper_no_positive_single_genre_normalized_deviation {N : ℕ}
    (R : Set (Fin N → ℝ)) (y : Fin N → ℝ) : Prop :=
  NoPositiveSingleGenreNormalizedDeviation R y

/--
Lemma `optsingledirection`: no positive radial deviations after CDF
substitution, before taking the small-radius limit.
-/
abbrev paper_no_positive_single_genre_radial_deviations {N : ℕ}
    (R : Set (Fin N → ℝ)) (y : Fin N → ℝ) : Prop :=
  NoPositiveSingleGenreRadialDeviations R y

/--
Lemma `optsingledirection` algebra: no positive normalized deviations over a
feasible row set is equivalent to the ratio-objective condition over that set.
-/
theorem paper_no_positive_single_genre_normalized_deviation_iff_condition {N : ℕ}
    [Nonempty (Fin N)] {R : Set (Fin N → ℝ)} {y : Fin N → ℝ} :
    paper_no_positive_single_genre_normalized_deviation R y ↔
      paper_single_genre_direction_condition R y :=
  noPositiveSingleGenreNormalizedDeviation_iff_directionCondition

/--
Lemma `optsingledirection` radial form: no positive radial deviations over a
feasible row set is equivalent to the source ratio-objective condition.
-/
theorem paper_no_positive_single_genre_radial_deviations_iff_condition {N : ℕ}
    [Nonempty (Fin N)] {R : Set (Fin N → ℝ)} {y : Fin N → ℝ} :
    paper_no_positive_single_genre_radial_deviations R y ↔
      paper_single_genre_direction_condition R y :=
  noPositiveSingleGenreRadialDeviations_iff_directionCondition

/--
Lemma `optsingledirection` algebra: the source direction itself has zero
normalized deviation payoff.
-/
theorem paper_single_genre_normalized_deviation_self_eq_zero {N : ℕ}
    [Nonempty (Fin N)] {y : Fin N → ℝ}
    (hy : ∀ i, y i ≠ 0) :
    paper_single_genre_normalized_deviation y y = 0 :=
  singleGenreNormalizedDeviation_self_eq_zero hy

/--
Source sanity check for the ratio objective: evaluating it at the same positive
row gives exactly `N`.
-/
theorem paper_ratio_objective_self_of_pos {N : ℕ} {y : Fin N → ℝ}
    (hy : ∀ i, y i ≠ 0) :
    paper_ratio_objective y y = (N : ℝ) :=
  ratioObjective_self_of_pos hy

/--
Lemma `supinf`, attained-product-maximizer case: if `yStar` maximizes
`prod_i y_i` over a positive feasible set, then AM-GM gives
`sum_i yStar_i / y_i >= N` for every feasible `y`.
-/
theorem paper_lemma_supinf_argmax_lower_bound {N : ℕ} [Nonempty (Fin N)]
    {R : Set (Fin N → ℝ)} {y yStar : Fin N → ℝ}
    (hmax : IsCoordinateProductMaximizer R yStar)
    (hy_mem : y ∈ R)
    (hpos : ∀ z ∈ R, ∀ i, 0 < z i) :
    (N : ℝ) ≤ paper_ratio_objective y yStar :=
  ratioObjective_ge_card_of_coordinateProductMaximizer hmax hy_mem hpos

/--
Lemma `supinf`, attained-product-maximizer case: the product maximizer also
attains the infimum of `sum_i yStar_i / y_i`, with value exactly `N`.
-/
theorem paper_lemma_supinf_argmax_attains_inf {N : ℕ} [Nonempty (Fin N)]
    {R : Set (Fin N → ℝ)} {yStar : Fin N → ℝ}
    (hmax : IsCoordinateProductMaximizer R yStar)
    (hpos : ∀ z ∈ R, ∀ i, 0 < z i) :
    IsMinimizerOn (fun y => y ∈ R) (fun y => paper_ratio_objective y yStar)
      yStar ∧
      paper_ratio_objective yStar yStar = (N : ℝ) :=
  ⟨ratioObjective_minimizer_at_coordinateProductMaximizer hmax hpos,
    ratioObjective_value_at_coordinateProductMaximizer hmax hpos⟩

/--
Corollary `singlegenrestructure`, optimization core: the single-genre
ratio-objective condition makes the candidate row maximize `prod_i y_i`.
-/
theorem paper_corollary_singlegenrestructure_product_maximizer_of_direction_condition
    {N : ℕ} [Nonempty (Fin N)]
    {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hcond : paper_single_genre_direction_condition R y)
    (hy_mem : y ∈ R)
    (hpos : ∀ z ∈ R, ∀ i, 0 < z i) :
    IsCoordinateProductMaximizer R y :=
  coordinateProductMaximizer_of_directionCondition hcond hy_mem hpos

/--
Corrected Corollary `singlegenrestructure` product step: a positive candidate
row satisfying the ratio condition maximizes coordinate product over a
nonnegative feasible set, including the zero row of the source norm ball.
-/
theorem paper_corollary_singlegenrestructure_product_maximizer_of_direction_condition_nonnegative
    {N : ℕ} [Nonempty (Fin N)] {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hcond : paper_single_genre_direction_condition R y)
    (hy_mem : y ∈ R) (hy_positive : ∀ i, 0 < y i)
    (hnonnegative : ∀ z ∈ R, ∀ i, 0 ≤ z i) :
    IsCoordinateProductMaximizer R y :=
  coordinateProductMaximizer_of_directionCondition_nonnegative
    hcond hy_mem hy_positive hnonnegative

/--
Corollary `singlegenrestructure`, optimization core: the product-maximizing
row also maximizes the log Nash-social-welfare objective on any positive
feasible set.
-/
theorem paper_corollary_singlegenrestructure_nash_log_maximizer {N : ℕ}
    {R : Set (Fin N → ℝ)} {yStar : Fin N → ℝ}
    (hmax : IsCoordinateProductMaximizer R yStar)
    (hpos : ∀ z ∈ R, ∀ i, 0 < z i) :
    IsMaximizerOn (fun y => y ∈ R) nashLogObjective yStar :=
  nashLogObjective_maximizer_of_coordinateProductMaximizer hmax hpos

/--
Corollary `singlegenrestructure`: the single-genre ratio-objective condition
implies the source Nash-log welfare maximization property.
-/
theorem paper_corollary_singlegenrestructure_nash_log_maximizer_of_direction_condition
    {N : ℕ} [Nonempty (Fin N)]
    {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hcond : paper_single_genre_direction_condition R y)
    (hy_mem : y ∈ R)
    (hpos : ∀ z ∈ R, ∀ i, 0 < z i) :
    IsMaximizerOn (fun z => z ∈ R) nashLogObjective y :=
  nashLogObjective_maximizer_of_coordinateProductMaximizer
    (coordinateProductMaximizer_of_directionCondition hcond hy_mem hpos) hpos

/--
Corollary `singlegenrestructure`: the radial no-deviation condition from the
single-genre equilibrium proof implies Nash-log welfare maximization.
-/
theorem paper_corollary_singlegenrestructure_nash_log_maximizer_of_radial_no_deviations
    {N : ℕ} [Nonempty (Fin N)]
    {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hradial : paper_no_positive_single_genre_radial_deviations R y)
    (hy_mem : y ∈ R)
    (hpos : ∀ z ∈ R, ∀ i, 0 < z i) :
    IsMaximizerOn (fun z => z ∈ R) nashLogObjective y :=
  paper_corollary_singlegenrestructure_nash_log_maximizer_of_direction_condition
    ((paper_no_positive_single_genre_radial_deviations_iff_condition).mp hradial)
    hy_mem hpos

/--
Corollary `singlegenrestructure`: the radial no-deviation condition from the
single-genre equilibrium proof also implies coordinate-product maximization.
-/
theorem paper_corollary_singlegenrestructure_product_maximizer_of_radial_no_deviations
    {N : ℕ} [Nonempty (Fin N)]
    {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hradial : paper_no_positive_single_genre_radial_deviations R y)
    (hy_mem : y ∈ R)
    (hpos : ∀ z ∈ R, ∀ i, 0 < z i) :
    IsCoordinateProductMaximizer R y :=
  paper_corollary_singlegenrestructure_product_maximizer_of_direction_condition
    ((paper_no_positive_single_genre_radial_deviations_iff_condition).mp hradial)
    hy_mem hpos

/--
Corollary `singlegenrestructure`, optimization core: on positive feasible
rows, maximizing `prod_i y_i` is equivalent to maximizing `sum_i log y_i`.
-/
theorem paper_corollary_singlegenrestructure_product_log_argmax_iff {N : ℕ}
    {R : Set (Fin N → ℝ)} {yStar : Fin N → ℝ}
    (hpos : ∀ z ∈ R, ∀ i, 0 < z i) :
    IsMaximizerOn (fun y => y ∈ R) nashLogObjective yStar ↔
      IsCoordinateProductMaximizer R yStar :=
  nashLogObjective_maximizer_iff_coordinateProductMaximizer hpos

/--
Theorem `singlegenre`, convex first-order bridge: the source first-order
condition for the Nash-log objective rewrites to the ratio-objective condition
used by Lemma `optsingledirection`.
-/
abbrev paper_nash_log_first_order_condition {N : ℕ}
    (R : Set (Fin N → ℝ)) (y : Fin N → ℝ) : Prop :=
  NashLogFirstOrderCondition R y

noncomputable abbrev paper_nash_log_segment_objective {N : ℕ}
    (y y' : Fin N → ℝ) (t : ℝ) : ℝ :=
  nashLogSegmentObjective y y' t

theorem paper_theorem_singlegenre_segment_derivative_at_zero {N : ℕ}
    {y y' : Fin N → ℝ} (hy : ∀ i, y i ≠ 0) :
    HasDerivAt (fun t : ℝ => paper_nash_log_segment_objective y y' t)
      (∑ i : Fin N, (y' i - y i) / y i) 0 :=
  hasDerivAt_nashLogSegmentObjective_zero hy

theorem paper_theorem_singlegenre_first_order_of_segment_local_max {N : ℕ}
    {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hy : ∀ i, y i ≠ 0)
    (hseg :
      ∀ y' ∈ R, ∀ ε : ℝ, 0 < ε → ε < 1 →
        paper_nash_log_segment_objective y y' ε ≤ nashLogObjective y) :
    paper_nash_log_first_order_condition R y :=
  nashLogFirstOrderCondition_of_segment_local_max hy hseg

theorem paper_theorem_singlegenre_first_order_of_convex_nash_log_maximizer
    {N : ℕ} {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hconv : Convex ℝ R)
    (hmax : IsMaximizerOn (fun z => z ∈ R) nashLogObjective y)
    (hy : ∀ i, y i ≠ 0) :
    paper_nash_log_first_order_condition R y :=
  nashLogFirstOrderCondition_of_convex_nashLogMaximizer hconv hmax hy

theorem paper_theorem_singlegenre_direction_condition_of_convex_nash_log_maximizer
    {N : ℕ} {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hconv : Convex ℝ R)
    (hmax : IsMaximizerOn (fun z => z ∈ R) nashLogObjective y)
    (hy : ∀ i, y i ≠ 0) :
    paper_single_genre_direction_condition R y :=
  (nashLogFirstOrderCondition_iff_directionCondition hy).mp
    (nashLogFirstOrderCondition_of_convex_nashLogMaximizer hconv hmax hy)

theorem paper_theorem_singlegenre_no_positive_radial_deviations_of_convex_nash_log_maximizer
    {N : ℕ} [Nonempty (Fin N)] {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hconv : Convex ℝ R)
    (hmax : IsMaximizerOn (fun z => z ∈ R) nashLogObjective y)
    (hy : ∀ i, y i ≠ 0) :
    paper_no_positive_single_genre_radial_deviations R y :=
  noPositiveSingleGenreRadialDeviations_of_convex_nashLogMaximizer hconv hmax hy

theorem paper_theorem_singlegenre_no_positive_radial_deviations_of_convex_product_maximizer
    {N : ℕ} [Nonempty (Fin N)] {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hconv : Convex ℝ R)
    (hmax : IsCoordinateProductMaximizer R y)
    (hpos : ∀ z ∈ R, ∀ i, 0 < z i) :
    paper_no_positive_single_genre_radial_deviations R y :=
  noPositiveSingleGenreRadialDeviations_of_convex_coordinateProductMaximizer
    hconv hmax hpos

theorem paper_theorem_singlegenre_direction_condition_of_convex_product_maximizer
    {N : ℕ} [Nonempty (Fin N)] {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hconv : Convex ℝ R)
    (hmax : IsCoordinateProductMaximizer R y)
    (hpos : ∀ z ∈ R, ∀ i, 0 < z i) :
    paper_single_genre_direction_condition R y :=
  singleGenreDirectionCondition_of_convex_coordinateProductMaximizer
    hconv hmax hpos

/--
Theorem `singlegenre`, existence predicate: the powered source set contains a
candidate single-genre row satisfying the ratio-objective no-deviation
condition from Lemma `optsingledirection`.
-/
abbrev paper_exists_single_genre_direction_condition {N : ℕ}
    (S : Set (Fin N → ℝ)) : Prop :=
  ExistsSingleGenreDirectionCondition S

theorem paper_theorem_singlegenre_exists_direction_condition_of_convex_product_maximizer
    {N : ℕ} [Nonempty (Fin N)] {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hconv : Convex ℝ R)
    (hmax : IsCoordinateProductMaximizer R y)
    (hpos : ∀ z ∈ R, ∀ i, 0 < z i) :
    paper_exists_single_genre_direction_condition R :=
  existsSingleGenreDirectionCondition_of_convex_coordinateProductMaximizer
    hconv hmax hpos

/--
Theorem `singlegenre`, source max-condition direction: if the coordinate-product
maximizer over the convexified powered set is itself attainable by an original
powered row, then the original powered set contains a row satisfying the
single-genre no-deviation condition.
-/
theorem paper_theorem_singlegenre_exists_direction_condition_of_hull_product_maximizer_mem
    {N : ℕ} [Nonempty (Fin N)] {S : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hmaxHull : IsCoordinateProductMaximizer (convexHull ℝ S) y)
    (hyS : y ∈ S)
    (hposHull : ∀ z ∈ convexHull ℝ S, ∀ i, 0 < z i) :
    paper_exists_single_genre_direction_condition S :=
  existsSingleGenreDirectionCondition_of_hull_coordinateProductMaximizer_mem
    hmaxHull hyS hposHull

theorem paper_theorem_singlegenre_first_order_sum_eq_ratio_sub_card {N : ℕ}
    {y y' : Fin N → ℝ} (hy : ∀ i, y i ≠ 0) :
    (∑ i : Fin N, (y' i - y i) / y i) =
      paper_ratio_objective y y' - (N : ℝ) :=
  nashLogFirstOrder_sum_eq_ratioObjective_sub_card hy

theorem paper_theorem_singlegenre_first_order_iff_direction_condition {N : ℕ}
    {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hy : ∀ i, y i ≠ 0) :
    paper_nash_log_first_order_condition R y ↔
      paper_single_genre_direction_condition R y :=
  nashLogFirstOrderCondition_iff_directionCondition hy

theorem paper_theorem_singlegenre_direction_condition_of_first_order {N : ℕ}
    {R : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hy : ∀ i, y i ≠ 0)
    (hfirst : paper_nash_log_first_order_condition R y) :
    paper_single_genre_direction_condition R y :=
  (paper_theorem_singlegenre_first_order_iff_direction_condition hy).mp hfirst

/--
Section 2 tie-breaking sanity check: every producer's tie share is nonnegative.
-/
theorem paper_tie_share_nonnegative {D P : ℕ}
    (u : Content D) (profile : Fin P → Content D) (j : Fin P) :
    0 ≤ tieShare u profile j :=
  tieShare_nonneg u profile j

/--
Section 2 tie-breaking sanity check: a producer in the winning set receives a
strictly positive reciprocal share.
-/
theorem paper_tie_share_positive_for_winner {D P : ℕ}
    {u : Content D} {profile : Fin P → Content D} {j : Fin P}
    (h : j ∈ winningProducers u profile) :
    0 < tieShare u profile j :=
  tieShare_pos_of_mem h

/--
No-tie case: a strict score maximizer is the unique winning producer for that
user.
-/
theorem paper_strict_winner_unique {D P : ℕ}
    {u : Content D} {profile : Fin P → Content D} {j : Fin P}
    (h : StrictWinner u profile j) :
    paper_winning_producers u profile = {j} :=
  winningProducers_eq_singleton_of_strictWinner h

/--
No-tie case: a strict score maximizer receives the entire recommendation share
for that user.
-/
theorem paper_tie_share_eq_one_of_strict_winner {D P : ℕ}
    {u : Content D} {profile : Fin P → Content D} {j : Fin P}
    (h : StrictWinner u profile j) :
    tieShare u profile j = 1 :=
  tieShare_eq_one_of_strictWinner h

/--
Section 2 assignment accounting: for each realized content profile, uniform
tie-breaking assigns one unit of recommendation mass per user.
-/
theorem paper_total_assigned_users_eq_card {D N P : ℕ} [Nonempty (Fin P)]
    (users : Fin N → Content D) (profile : Fin P → Content D) :
    (∑ j : Fin P, usersWon users profile j) = (N : ℝ) :=
  sum_usersWon_eq_card users profile

/--
Section 2 assignment accounting: no individual producer can be assigned more
than the total user mass `N`.
-/
theorem paper_users_won_le_user_count {D N P : ℕ} [Nonempty (Fin P)]
    (users : Fin N → Content D) (profile : Fin P → Content D) (j : Fin P) :
    usersWon users profile j ≤ (N : ℝ) :=
  usersWon_le_card users profile j

/--
Proposition `pure`, no-tie case setup: since total assigned recommendation mass
is `N`, when there is at least one user and producer, some producer receives a
strictly positive expected number of users.
-/
theorem paper_exists_positive_user_mass_producer {D N P : ℕ}
    [Nonempty (Fin N)] [Nonempty (Fin P)]
    (users : Fin N → Content D) (profile : Fin P → Content D) :
    ∃ j : Fin P, 0 < usersWon users profile j :=
  exists_producer_usersWon_pos users profile

/--
Proposition `pure`, no-tie case bridge: positive expected user mass for a
producer comes from at least one individual user with positive tie-breaking
share.
-/
theorem paper_exists_positive_tie_share_user_of_positive_mass {D N P : ℕ}
    {users : Fin N → Content D} {profile : Fin P → Content D} {j : Fin P}
    (h : 0 < usersWon users profile j) :
    ∃ i : Fin N, 0 < tieShare (users i) profile j :=
  exists_user_tieShare_pos_of_usersWon_pos h

/--
Proposition `pure`, no-tie case bridge: under no score ties, a producer with
positive expected recommendation mass strictly wins at least one user.
-/
theorem paper_exists_strictly_won_user_of_positive_mass_no_ties {D N P : ℕ}
    {users : Fin N → Content D} {profile : Fin P → Content D} {j : Fin P}
    (hno : NoScoreTies users profile)
    (hpos : 0 < usersWon users profile j) :
    ∃ i : Fin N, StrictWinner (users i) profile j :=
  exists_user_strictWinner_of_usersWon_pos_noScoreTies hno hpos

/--
Proposition `pure`, no-tie case setup: when all scores are untied, some
producer strictly wins some user.
-/
theorem paper_exists_strict_winner_under_no_ties {D N P : ℕ}
    [Nonempty (Fin N)] [Nonempty (Fin P)]
    (users : Fin N → Content D) (profile : Fin P → Content D)
    (hno : NoScoreTies users profile) :
    ∃ (j : Fin P) (i : Fin N), StrictWinner (users i) profile j :=
  exists_producer_user_strictWinner_of_noScoreTies users profile hno

/--
Equation (2) source set `S`: rows of user values induced by feasible unit
content vectors.
-/
abbrev paper_unit_image {D N : ℕ}
    (users : Fin N → Content D) (unitFeasible : Content D → Prop)
    (y : Fin N → ℝ) : Prop :=
  InUnitImage users unitFeasible y

/--
Corollary `betaone` setup: if the source unit-feasible content region is
convex, then its user-value image `S` is convex.
-/
theorem paper_unit_image_convex_of_convex_feasible {D N : ℕ}
    {users : Fin N → Content D} {unitFeasible : Content D → Prop}
    (hconv : Convex ℝ {p : Content D | unitFeasible p}) :
    Convex ℝ {y : Fin N → ℝ | paper_unit_image users unitFeasible y} :=
  convex_inUnitImage_of_convex_unitFeasible hconv

/--
Equation (2) source set `S^β`: coordinatewise powers of rows in `S`.
-/
noncomputable abbrev paper_powered_unit_image {D N : ℕ}
    (users : Fin N → Content D) (unitFeasible : Content D → Prop)
    (β : ℝ) (y : Fin N → ℝ) : Prop :=
  InPoweredUnitImage users unitFeasible β y

/--
Corollary `betaone` algebra: for exponent `β = 1`, the powered set `S^β`
coincides with the original unit image `S`.
-/
theorem paper_powered_unit_image_one_iff {D N : ℕ}
    {users : Fin N → Content D} {unitFeasible : Content D → Prop}
    {y : Fin N → ℝ} :
    paper_powered_unit_image users unitFeasible (1 : ℝ) y ↔
      paper_unit_image users unitFeasible y :=
  inPoweredUnitImage_one_iff

/--
Corollary `betaone`: for exponent `β = 1`, `S^β` is convex whenever the
source unit-feasible content region is convex.
-/
theorem paper_powered_unit_image_one_convex_of_convex_feasible {D N : ℕ}
    {users : Fin N → Content D} {unitFeasible : Content D → Prop}
    (hconv : Convex ℝ {p : Content D | unitFeasible p}) :
    Convex ℝ
      {y : Fin N → ℝ |
        paper_powered_unit_image users unitFeasible (1 : ℝ) y} :=
  convex_inPoweredUnitImage_one_of_convex_unitFeasible hconv

/--
Corollary `betaone`: for exponent `β = 1`, the powered source set equals its
convex hull whenever the source unit-feasible content region is convex.
-/
theorem paper_powered_unit_image_one_convex_hull_eq_of_convex_feasible {D N : ℕ}
    {users : Fin N → Content D} {unitFeasible : Content D → Prop}
    (hconv : Convex ℝ {p : Content D | unitFeasible p}) :
    convexHull ℝ
        {y : Fin N → ℝ |
          paper_powered_unit_image users unitFeasible (1 : ℝ) y} =
      {y : Fin N → ℝ |
        paper_powered_unit_image users unitFeasible (1 : ℝ) y} :=
  convexHull_inPoweredUnitImage_one_eq_of_convex_unitFeasible hconv

/--
Theorem `singlegenre`, source-side maximum attainment.  Proper source-norm
sublevels make the powered nonnegative unit-ball image compact, so its
coordinate-product `max` is attained.  This is only the source-image half of
the printed max condition; compactness/attainment of the convex-hull side is
recorded as a separate finite-dimensional requirement.
-/
theorem paper_lemma_singlegenre_powered_source_image_compact
    {D N : ℕ} (users : Fin N → Content D) (ν : SourceNorm D)
    {β : ℝ} (hcompact : SourceNormCompactSublevels ν) (hβ : 0 ≤ β) :
    IsCompact {y : Fin N → ℝ |
      paper_powered_unit_image users
        (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y} :=
  isCompact_inPoweredUnitImage_of_compactSublevels users ν hcompact hβ

/--
Theorem `singlegenre`, source-side product maximum attainment under the same
properness condition.  The statement deliberately does not smuggle in the
separate convex-hull maximum needed by the source's equality display.
-/
theorem paper_lemma_singlegenre_powered_source_product_maximizer
    {D N : ℕ} (users : Fin N → Content D) (ν : SourceNorm D)
    {β : ℝ} (hcompact : SourceNormCompactSublevels ν) (hβ : 0 ≤ β) :
    ∃ y : Fin N → ℝ,
      IsCoordinateProductMaximizer
        {z : Fin N → ℝ |
          paper_powered_unit_image users
            (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β z} y :=
  exists_coordinateProductMaximizer_inPoweredUnitImage_of_compactSublevels
    users ν hcompact hβ

/--
Theorem `singlegenre`, convex special case: if the powered source set
`S^β` is convex, then the source max-condition is automatically satisfied.
-/
theorem paper_theorem_singlegenre_product_sup_condition_of_convex {N : ℕ}
    {S : Set (Fin N → ℝ)} (hconv : Convex ℝ S) :
    SingleGenreProductSupCondition S :=
  singleGenreProductSupCondition_of_convex hconv

/--
Theorem `singlegenre`, corrected attained-max bridge: if a positive
coordinate-product maximizer of the convex hull is an original powered row,
and hull rows are nonnegative, that row satisfies the source direction
condition.  The nonnegativity formulation correctly permits the zero row.
-/
theorem paper_theorem_singlegenre_direction_condition_of_positive_hull_product_maximizer
    {N : ℕ} [Nonempty (Fin N)] {S : Set (Fin N → ℝ)} {y : Fin N → ℝ}
    (hmax : IsCoordinateProductMaximizer (convexHull ℝ S) y)
    (hyS : y ∈ S) (hy_positive : ∀ i, 0 < y i)
    (hnonnegative : ∀ z ∈ convexHull ℝ S, ∀ i, 0 ≤ z i) :
    paper_exists_single_genre_direction_condition S :=
  existsSingleGenreDirectionCondition_of_hull_coordinateProductMaximizer_mem_nonnegative
    hmax hyS hy_positive hnonnegative

/--
Theorem `singlegenre`, corrected attained-max form: the displayed equality of
source and convex-hull product suprema yields a direction condition once both
maxima are attained, the source maximizer is positive, and hull rows are
nonnegative.  These are the finite-domain hypotheses needed to make the
paper's `max` notation and zero-row semantics precise.
-/
theorem paper_theorem_singlegenre_direction_condition_of_product_sup_condition
    {N : ℕ} [Nonempty (Fin N)] {S : Set (Fin N → ℝ)}
    {x y : Fin N → ℝ}
    (hproduct : SingleGenreProductSupCondition S)
    (hmax_source : IsCoordinateProductMaximizer S x)
    (hmax_hull : IsCoordinateProductMaximizer (convexHull ℝ S) y)
    (hx_positive : ∀ i, 0 < x i)
    (hnonnegative_hull : ∀ z ∈ convexHull ℝ S, ∀ i, 0 ≤ z i) :
    paper_exists_single_genre_direction_condition S :=
  existsSingleGenreDirectionCondition_of_productSupCondition_of_attained_maximizers_nonnegative
    hproduct hmax_source hmax_hull hx_positive hnonnegative_hull

/--
Theorem `singlegenre`, corrected concrete sufficient direction.  With the
displayed product-sup equality interpreted as attained maxima on the source
image and its convex hull, plus positive source maximizer and nonnegative hull
rows, Lean constructs the corresponding single-genre source symmetric mixed
Nash ray law.  This does not claim the literal generic iff or the source's
unstated noncompact minimax argument.
-/
abbrev paper_source_symmetric_mixed_nash {D N : ℕ} (P : ℕ)
    (users : Fin N → Content D) (cost : Content D → ℝ)
    (μ : MixedContentStrategy D) : Prop :=
  SourceSymmetricMixedNash (P := P) users cost μ

/-- Claim `equivalence`, checked equal-population component.  When there are
`K` copies of each of two user types (hence `N = 2K`), the paper's displayed
cost factor `2 / N` is exactly the payoff-preserving factor `1 / K`.

This result deliberately does not include the source's later coordinate
rotation to `u₁ = e₁`: that rotation need not preserve the nonnegative
content action space. -/
theorem paper_claim_equivalence_equal_populations
    {D K P : ℕ} (users : Fin 2 → Content D) {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} (hK : 0 < K) :
    paper_source_symmetric_mixed_nash P (twoPopulationUsers K users) cost μ ↔
      paper_source_symmetric_mixed_nash P users
        (fun q => (2 : ℝ) / ((2 * K : ℕ) : ℝ) * cost q) μ := by
  rw [two_div_natCast_two_mul_eq_inv K hK]
  exact sourceSymmetricMixedNash_twoPopulationUsers_iff users hK

theorem paper_theorem_singlegenre_concrete_source_symmetric_mixed_nash_of_product_sup_condition
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {x y : Fin N → ℝ}
    (ν : SourceNorm D) (hβ : 0 < β)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hproduct : SingleGenreProductSupCondition
      {z : Fin N → ℝ | paper_powered_unit_image users
        (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β z})
    (hmax_source : IsCoordinateProductMaximizer
      {z : Fin N → ℝ | paper_powered_unit_image users
        (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β z} x)
    (hmax_hull : IsCoordinateProductMaximizer
      (convexHull ℝ {z : Fin N → ℝ | paper_powered_unit_image users
        (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β z}) y)
    (hx_positive : ∀ i, 0 < x i)
    (hnonnegative_hull : ∀ z ∈ convexHull ℝ
      {z : Fin N → ℝ | paper_powered_unit_image users
        (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β z},
      ∀ i, 0 ≤ z i) :
    ∃ p : Content D, NonnegativeContent p ∧ ν.norm p ≤ 1 ∧
      (∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) ∧
      paper_source_symmetric_mixed_nash P users (normRpowCost ν β)
        (singleGenreContentLaw N P β (SourceNorm.normalizedContent ν p)) :=
  exists_singleGenreContentLaw_sourceSymmetricMixedNash_of_productSupCondition_of_attained_maximizers_nonnegative
    ν hβ husers hproduct hmax_source hmax_hull hx_positive hnonnegative_hull

/--
Corrected compact-source form of Theorem `singlegenre` for the explicit
single-genre inverse-transform ray law.  With nonnegative nonzero users and
compact source-norm sublevels, equality of the source and convex-hull
coordinate-product suprema is equivalent to existence of a positive feasible
content vector whose normalized ray law is a source symmetric mixed Nash
equilibrium.

This formalizes the source's product condition without assuming that its
convex hull is compact or that the displayed hull maximum is separately
attained.  It does not assert the literal source `Genre(mu) = {genre}`
notation, which is incompatible with the ray law's zero-support point.
-/
theorem paper_theorem_singlegenre_concrete_source_symmetric_mixed_nash_iff_product_sup_condition_of_compact_sublevels
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} (ν : SourceNorm D)
    (hβ : 0 < β) (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hcompact : SourceNormCompactSublevels ν) :
    (∃ p : Content D, NonnegativeContent p ∧ ν.norm p ≤ 1 ∧
      (∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) ∧
      paper_source_symmetric_mixed_nash P users (normRpowCost ν β)
        (singleGenreContentLaw N P β (SourceNorm.normalizedContent ν p))) ↔
      SingleGenreProductSupCondition
        {z : Fin N → ℝ | paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β z} :=
  exists_positive_ball_singleGenreContentLaw_sourceSymmetricMixedNash_iff_productSupCondition_of_compactSublevels
    ν hβ husers husers_nonzero hcompact

/--
The product-supremum condition in Theorem `singlegenre` is preserved when the
power exponent is decreased: if it holds at `beta' >= beta`, it holds at
`beta`.  The source proof's final monotonicity paragraph has a duplicated
inconsistent inequality direction; this is its intended corrected conclusion.

Compact source-norm sublevels make the source maxima available and bound the
convex-hull objectives.  No unqualified threshold or literal genre statement
is asserted here.
-/
theorem paper_theorem_singlegenre_product_sup_condition_of_le_exponent_of_compact_sublevels
    {D N : ℕ} {users : Fin N → Content D} {ν : SourceNorm D}
    {β β' : ℝ} (hβ : 0 < β) (hβ_le : β ≤ β')
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hcompact : SourceNormCompactSublevels ν)
    (hproduct : SingleGenreProductSupCondition
      {y : Fin N → ℝ | paper_powered_unit_image users
        (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β' y}) :
    SingleGenreProductSupCondition
      {y : Fin N → ℝ | paper_powered_unit_image users
        (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y} :=
  singleGenreProductSupCondition_inPoweredUnitImage_of_le_exponent_of_compactSublevels
    hβ hβ_le husers hcompact hproduct

/--
Corollary `betaone`: for exponent `β = 1`, the source max-condition holds in
supremum form because `S^1` equals its convex hull.
-/
theorem paper_betaone_product_sup_condition_of_convex_feasible {D N : ℕ}
    {users : Fin N → Content D} {unitFeasible : Content D → Prop}
    (hconv : Convex ℝ {p : Content D | unitFeasible p}) :
    SingleGenreProductSupCondition
      {y : Fin N → ℝ |
        paper_powered_unit_image users unitFeasible (1 : ℝ) y} :=
  singleGenreProductSupCondition_poweredUnitImage_one_of_convex_unitFeasible hconv

/--
Corollary `betaone`, direction-condition endpoint: when the source feasible
content region is convex and the product objective attains a positive maximizer
on `S^1`, the resulting row satisfies the single-genre no-deviation condition.
-/
theorem paper_betaone_exists_direction_condition_of_product_maximizer
    {D N : ℕ} [Nonempty (Fin N)]
    {users : Fin N → Content D} {unitFeasible : Content D → Prop}
    {y : Fin N → ℝ}
    (hconv : Convex ℝ {p : Content D | unitFeasible p})
    (hmax :
      IsCoordinateProductMaximizer
        {z : Fin N → ℝ |
          paper_powered_unit_image users unitFeasible (1 : ℝ) z} y)
    (hpos :
      ∀ z ∈ {z : Fin N → ℝ |
          paper_powered_unit_image users unitFeasible (1 : ℝ) z},
        ∀ i, 0 < z i) :
    paper_exists_single_genre_direction_condition
      {z : Fin N → ℝ |
        paper_powered_unit_image users unitFeasible (1 : ℝ) z} :=
  existsSingleGenreDirectionCondition_poweredUnitImage_one_of_product_maximizer
    hconv hmax hpos

/-! ## Profit section -/

/--
Proposition `zeroutilitysinglegenre`, formula surface: the single-genre CDF
implies zero profit at the zero-quality support point.
-/
noncomputable abbrev paper_single_genre_profit_formula
    (N P : ℕ) (β r : ℝ) : ℝ :=
  SingleGenreProfitFormula N P β r

/--
Proposition `zeroutilitysinglegenre`: under Lemma `cdf`'s single-genre CDF
formula, the zero-quality support point has profit zero.
-/
theorem paper_proposition_zeroutilitysinglegenre_profit_formula_zero
    {N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {β : ℝ} (hβ : 0 < β) :
    paper_single_genre_profit_formula N P β 0 = 0 :=
  singleGenreProfitFormula_zero_eq_zero hβ

/--
Proposition `zeroutilitysinglegenre`, payoff wrapper: if the common
equilibrium payoff equals the zero-quality support payoff, then the
equilibrium profit is zero.
-/
theorem paper_proposition_zeroutilitysinglegenre_equilibrium_payoff_zero
    {N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {β equilibriumPayoff : ℝ}
    (hβ : 0 < β)
    (hpayoff : equilibriumPayoff = paper_single_genre_profit_formula N P β 0) :
    equilibriumPayoff = 0 :=
  equilibriumPayoff_eq_zero_of_singleGenre_zero_support_payoff hβ hpayoff

/--
Proposition `utility`, geometry-gap expression from the source proof.  The
paper proves this gap is positive from the user-geometry condition and the
support-norm bound.
-/
noncomputable abbrev paper_positive_profit_geometry_gap
    (N P : ℕ) (β Q R : ℝ) : ℝ :=
  PositiveProfitGeometryGap N P β Q R

/--
Proposition `utility`, scalar support-bound step: after bounding the support
radius by `R^β <= N`, the paper's strict post-substitution geometry inequality
implies the deviation gap is positive.
-/
theorem paper_positive_profit_geometry_gap_pos_of_source_scalar_bound
    {N P : ℕ} {β Q R : ℝ}
    (hQ_nonneg : 0 ≤ Q) (hR_nonneg : 0 ≤ R)
    (hR : R ^ β ≤ (N : ℝ))
    (hQ : Q ^ β * (N : ℝ) < (1 / (N : ℝ)) ^ ((P : ℝ) - 1)) :
    0 < paper_positive_profit_geometry_gap N P β Q R :=
  positiveProfitGeometryGap_pos_of_source_scalar_bound hQ_nonneg hR_nonneg hR hQ

/--
Proposition `utility`, printed-condition algebra: the source condition
`Q < (1/N)^(P/β)` implies the strict scalar inequality used after substituting
the support-radius bound.
-/
theorem paper_source_scalar_bound_of_positive_profit_condition
    {N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {β Q : ℝ}
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β)) :
    Q ^ β * (N : ℝ) < (1 / (N : ℝ)) ^ ((P : ℝ) - 1) :=
  source_scalar_bound_of_positive_profit_condition hβ hQ_nonneg hQ

/--
Proposition `utility`, source-shaped scalar endpoint: the paper's printed
geometry condition plus the source support-radius bound imply that the
deviation gap is positive.
-/
theorem paper_positive_profit_geometry_gap_pos_of_positive_profit_condition_and_support_bound
    {N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {β Q R : ℝ}
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q) (hR_nonneg : 0 ≤ R)
    (hR : R ^ β ≤ (N : ℝ))
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β)) :
    0 < paper_positive_profit_geometry_gap N P β Q R :=
  positiveProfitGeometryGap_pos_of_positive_profit_condition_and_support_bound
    hβ hQ_nonneg hR_nonneg hR hQ

/--
Proposition `utility`, outside-option step: a nonnegative pure deviation
forces the symmetric equilibrium payoff to be nonnegative.
-/
theorem paper_equilibrium_payoff_nonneg_of_nonnegative_pure_deviation
    {D : ℕ} {equilibriumPayoff : ℝ}
    {payoff : Content D → MixedContentStrategy D → ℝ}
    {μ : MixedContentStrategy D} {p : Content D}
    (hno : SymmetricMixedNoProfitablePureDeviation payoff μ equilibriumPayoff)
    (hp : 0 ≤ payoff p μ) :
    0 ≤ equilibriumPayoff :=
  equilibriumPayoff_nonneg_of_nonnegative_pure_deviation hno hp

/--
Proposition `utility`, support-radius algebra: if the common equilibrium payoff
is nonnegative and is at most `N - R^β`, then `R^β <= N`.
-/
theorem paper_support_radius_rpow_le_card_of_nonnegative_payoff_upper_bound
    {N : ℕ} {β R equilibriumPayoff : ℝ}
    (hpayoff_nonneg : 0 ≤ equilibriumPayoff)
    (hpayoff_upper : equilibriumPayoff ≤ (N : ℝ) - R ^ β) :
    R ^ β ≤ (N : ℝ) :=
  support_radius_rpow_le_card_of_nonnegative_payoff_upper_bound
    hpayoff_nonneg hpayoff_upper

/--
Proposition `utility`, source-shaped support-radius step: a nonnegative pure
outside option plus the paper's support-action payoff upper bound imply
`R^β <= N`.
-/
theorem paper_support_radius_rpow_le_card_of_deviation_upper_bound
    {D N : ℕ} {β R equilibriumPayoff : ℝ}
    {payoff : Content D → MixedContentStrategy D → ℝ}
    {μ : MixedContentStrategy D} {outside : Content D}
    (hno : SymmetricMixedNoProfitablePureDeviation payoff μ equilibriumPayoff)
    (houtside : 0 ≤ payoff outside μ)
    (hpayoff_upper : equilibriumPayoff ≤ (N : ℝ) - R ^ β) :
    R ^ β ≤ (N : ℝ) :=
  support_radius_rpow_le_card_of_deviation_upper_bound hno houtside hpayoff_upper

/--
Proposition `utility`, zero-action outside option: under the source norm-power
cost, the zero content vector has nonnegative mixed payoff.
-/
theorem paper_source_mixed_pure_payoff_zero_nonneg_of_norm_rpow_cost
    {D N P : ℕ} {users : Fin N → Content D} {j : Fin P}
    {μ : MixedContentStrategy D} (ν : SourceNorm D) {β : ℝ}
    (hβ : 0 < β) :
    0 ≤
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β)
        (0 : Content D) μ :=
  sourceMixedPurePayoff_zero_nonneg_of_normRpowCost ν hβ

/--
Proposition `utility`, mixed payoff upper bound: any pure content vector wins
at most `N` users in expectation before subtracting the norm-power cost.
-/
theorem paper_source_mixed_pure_payoff_le_card_sub_norm_rpow_cost
    {D N P : ℕ} [Nonempty (Fin P)]
    {users : Fin N → Content D} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    (ν : SourceNorm D) {β : ℝ} {p : Content D}
    (hint :
      MeasureTheory.Integrable
        (fun profile : Fin P → Content D =>
          usersWon users (deviateProfile profile j p) j)
        (MeasureTheory.Measure.pi (fun _ : Fin P => μ))) :
    SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β)
        p μ ≤
      (N : ℝ) - normRpowCost ν β p :=
  sourceMixedPurePayoff_le_card_sub_normRpowCost ν hint

/--
Proposition `utility`, support-radius upper-bound step: if a radius-attaining
support point earns the equilibrium payoff, then that payoff is at most
`N - R^β`.
-/
theorem paper_equilibrium_payoff_le_card_sub_radius_rpow_of_support_radius_point
    {D N P : ℕ} [Nonempty (Fin P)]
    {users : Fin N → Content D} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    (ν : SourceNorm D) {β R equilibriumPayoff : ℝ} {pR : Content D}
    (hint :
      MeasureTheory.Integrable
        (fun profile : Fin P → Content D =>
          usersWon users (deviateProfile profile j pR) j)
        (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hpayoff_eq :
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β)
        pR μ = equilibriumPayoff)
    (hnorm : ν.norm pR = R) :
    equilibriumPayoff ≤ (N : ℝ) - R ^ β :=
  equilibriumPayoff_le_card_sub_radius_rpow_of_support_radius_point
    ν hint hpayoff_eq hnorm

/--
Proposition `utility`, assembled endpoint before the geometry construction:
the printed condition, the source support-action upper bound, a nonnegative
outside option, and the event-deviation lower bound imply strictly positive
equilibrium profit.
-/
theorem paper_proposition_utility_positive_equilibrium_payoff_of_source_bounds
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {β Q R equilibriumPayoff : ℝ}
    {payoff : Content D → MixedContentStrategy D → ℝ}
    {μ : MixedContentStrategy D} {outside : Content D}
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q) (hR_nonneg : 0 ≤ R)
    (hno : SymmetricMixedNoProfitablePureDeviation payoff μ equilibriumPayoff)
    (houtside : 0 ≤ payoff outside μ)
    (hpayoff_upper : equilibriumPayoff ≤ (N : ℝ) - R ^ β)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β))
    (hdev :
      ∃ p : Content D,
        paper_positive_profit_geometry_gap N P β Q R ≤ payoff p μ) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_support_upper_and_deviation
    hβ hQ_nonneg hR_nonneg hno houtside hpayoff_upper hQ hdev

/--
Proposition `utility`, clustering pigeonhole step: among `N` direction groups
whose probabilities are nonnegative and sum to one, one has mass at least
`1/N`.
-/
theorem paper_exists_group_mass_ge_one_div_card
    {N : ℕ} [Nonempty (Fin N)] {w : Fin N → ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hsum : (∑ i : Fin N, w i) = 1) :
    ∃ i : Fin N, (1 / (N : ℝ)) ≤ w i :=
  exists_group_mass_ge_one_div_card hw_nonneg hsum

/--
Proposition `utility`, event-probability step: if the selected group has mass
at least `1/N`, the independent event that the other `P-1` producers land in
that group has probability at least `(1/N)^(P-1)`.
-/
theorem paper_group_event_probability_lower_bound
    {N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {mass : ℝ} (hmass_nonneg : 0 ≤ mass)
    (hmass : (1 / (N : ℝ)) ≤ mass) :
    (1 / (N : ℝ)) ^ ((P : ℝ) - 1) ≤ mass ^ ((P : ℝ) - 1) :=
  group_event_probability_lower_bound hmass_nonneg hmass

/--
Proposition `utility`, scalar epsilon step: if `x^β` is strictly below `B`,
one can increase `x` while keeping the `β`-power below `B`.
-/
theorem paper_exists_scale_gt_with_rpow_lt
    {β x B : ℝ} (hβ : 0 < β) (hx : 0 ≤ x) (hxb : x ^ β < B) :
    ∃ a : ℝ, x < a ∧ a ^ β < B :=
  exists_scale_gt_with_rpow_lt hβ hx hxb

/--
Proposition `utility`, scaled-unit-direction epsilon step: if the threshold
cost is below the event probability, a scaled unit direction beats the score
threshold while keeping norm-power cost below the event probability.
-/
theorem paper_exists_scaled_unit_direction_score_gt_cost_lt
    {D : ℕ} (ν : SourceNorm D) {β threshold eventMass : ℝ}
    {u direction : Content D}
    (hβ : 0 < β) (hthreshold : 0 ≤ threshold)
    (hgap : threshold ^ β < eventMass)
    (hscore_unit : score u direction = 1)
    (hnorm_unit : ν.norm direction = 1) :
    ∃ p : Content D,
      threshold < score u p ∧ normRpowCost ν β p < eventMass :=
  exists_scaled_unit_direction_score_gt_cost_lt
    ν hβ hthreshold hgap hscore_unit hnorm_unit

/--
Proposition `utility`, source event: every opponent producer lies in the
selected direction group and within the support-radius bound.
-/
abbrev paper_all_other_producers_in_bounded_direction_group {D N P : ℕ}
    (j : Fin P) (group : Content D → Fin N) (i : Fin N)
    (ν : SourceNorm D) (R : ℝ) : Set (Fin P → Content D) :=
  AllOtherProducersInBoundedDirectionGroup j group i ν R

/-- Proposition `utility`, the source support-radius ball. -/
abbrev paper_source_support_ball {D : ℕ}
    (ν : SourceNorm D) (R : ℝ) : Set (Content D) :=
  SourceSupportBall ν R

/--
Proposition `utility`, one-producer selected set: a producer lies in the
selected direction group and within the support-radius bound.
-/
abbrev paper_bounded_direction_group_set {D N : ℕ}
    (group : Content D → Fin N) (i : Fin N)
    (ν : SourceNorm D) (R : ℝ) : Set (Content D) :=
  BoundedDirectionGroupSet group i ν R

/--
Proposition `utility`, overlapping source min-direction set: user `i` is one
minimum-score user for the normalized direction.
-/
abbrev paper_source_min_direction_set {D N : ℕ}
    (users : Fin N → Content D) (ν : SourceNorm D)
    (i : Fin N) : Set (Content D) :=
  SourceMinDirectionSet users ν i

/--
Proposition `utility`, bounded overlapping source min-direction set: the
content vector lies in the radius bound and user `i` is one minimum-score user.
-/
abbrev paper_bounded_source_min_direction_set {D N : ℕ}
    (users : Fin N → Content D) (ν : SourceNorm D)
    (i : Fin N) (R : ℝ) : Set (Content D) :=
  BoundedSourceMinDirectionSet users ν i R

/--
Proposition `utility`, product event for the overlapping source min-direction
cover.
-/
abbrev paper_all_other_producers_in_bounded_source_min_direction_set {D N P : ℕ}
    (j : Fin P) (users : Fin N → Content D) (i : Fin N)
    (ν : SourceNorm D) (R : ℝ) : Set (Fin P → Content D) :=
  AllOtherProducersInBoundedSourceMinDirectionSet j users i ν R

/--
Proposition `utility`, source direction map: a nonzero content vector is
normalized to the unit direction `p / ||p||`.
-/
noncomputable abbrev paper_normalized_content {D : ℕ}
    (ν : SourceNorm D) (p : Content D) : Content D :=
  SourceNorm.normalizedContent ν p

/--
Proposition `utility`, source-normalized users: each user vector is replaced by
`u_i / ||u_i||_2` for the geometry condition, while recommendation assignments
are unchanged because the rescaling is positive.
-/
noncomputable abbrev paper_l2_normalized_users {D N : ℕ}
    (users : Fin N → Content D) : Fin N → Content D :=
  l2NormalizedUsers users

/--
Proposition `utility`, source clustering rule: the selected group labels a
direction by a user attaining the minimum normalized inferred value.
-/
abbrev paper_source_direction_group_min {D N : ℕ}
    (users : Fin N → Content D) (ν : SourceNorm D)
    (group : Content D → Fin N) : Prop :=
  SourceDirectionGroupMin users ν group

/--
Proposition `utility`, source definition of `Q`: every unit direction has some
user whose inferred value is at most `Q`.
-/
abbrev paper_source_unit_direction_Q_upper_bound {D N : ℕ}
    (users : Fin N → Content D) (ν : SourceNorm D) (Q : ℝ) : Prop :=
  SourceUnitDirectionQUpperBound users ν Q

/--
Proposition `utility`, canonical finite tie-breaking for assigning each
direction to a minimum-score user.
-/
noncomputable abbrev paper_source_min_score_user {D N : ℕ}
    [Nonempty (Fin N)]
    (users : Fin N → Content D) (ν : SourceNorm D) (p : Content D) : Fin N :=
  sourceMinScoreUser users ν p

/--
Proposition `utility`, the canonical source selector chooses a user whose
normalized inferred value is minimal among all users.
-/
theorem paper_source_min_score_user_min {D N : ℕ} [Nonempty (Fin N)]
    (users : Fin N → Content D) (ν : SourceNorm D) (p : Content D)
    (k : Fin N) :
    score (users (paper_source_min_score_user users ν p))
        (paper_normalized_content ν p) ≤
      score (users k) (paper_normalized_content ν p) :=
  sourceMinScoreUser_min users ν p k

/--
Proposition `utility`, the canonical source selector satisfies the source
direction-clustering rule.
-/
theorem paper_source_direction_group_min_source_min_score_user
    {D N : ℕ} [Nonempty (Fin N)]
    (users : Fin N → Content D) (ν : SourceNorm D) :
    paper_source_direction_group_min users ν
      (paper_source_min_score_user users ν) :=
  sourceDirectionGroupMin_sourceMinScoreUser users ν

/--
Proposition `utility`, normalized nonzero content has source norm one.
-/
theorem paper_norm_normalized_content_eq_one {D : ℕ} (ν : SourceNorm D)
    {p : Content D} (hp : NonzeroContent p) :
    ν.norm (paper_normalized_content ν p) = 1 :=
  SourceNorm.norm_normalizedContent_eq_one ν hp

/--
Proposition `utility`, source linearity step: any nonzero content vector's
score is its norm times the score of its normalized direction.
-/
theorem paper_score_eq_norm_mul_score_normalized_content {D : ℕ}
    (ν : SourceNorm D) (u : Content D) {p : Content D}
    (hp : NonzeroContent p) :
    score u p = ν.norm p * score u (paper_normalized_content ν p) :=
  SourceNorm.score_eq_norm_mul_score_normalizedContent ν u hp

/--
Proposition `utility`, source geometry bridge: the source group-min rule and
the definition of `Q` imply the pointwise score bound used on each bounded
direction-group event.
-/
theorem paper_source_direction_group_bound_of_min_and_Q_upper
    {D N : ℕ} [Nonempty (Fin N)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {Q : ℝ}
    (hQ_nonneg : 0 ≤ Q)
    (hmin : paper_source_direction_group_min users ν group)
    (hQupper : paper_source_unit_direction_Q_upper_bound users ν Q) :
    ∀ (i : Fin N) (p : Content D), group p = i →
      score (users i) p ≤ Q * ν.norm p :=
  source_direction_group_bound_of_min_and_QUpper hQ_nonneg hmin hQupper

/--
Proposition `utility`, support-radius ball measurability from a measurable
source norm.
-/
theorem paper_measurable_set_source_support_ball_of_measurable_norm
    {D : ℕ} {ν : SourceNorm D} {R : ℝ}
    (hnorm_meas : Measurable ν.norm) :
    MeasurableSet (paper_source_support_ball ν R) :=
  measurableSet_sourceSupportBall_of_measurable_norm hnorm_meas

/--
Proposition `utility`, bounded direction-group measurability from a measurable
group fiber and the support-radius ball.
-/
theorem paper_measurable_set_bounded_direction_group_set_of_fiber_and_ball
    {D N : ℕ} {group : Content D → Fin N} {i : Fin N}
    {ν : SourceNorm D} {R : ℝ}
    (hfiber : MeasurableSet {v : Content D | group v = i})
    (hball : MeasurableSet (paper_source_support_ball ν R)) :
    MeasurableSet (paper_bounded_direction_group_set group i ν R) :=
  measurableSet_boundedDirectionGroupSet_of_fiber_and_ball hfiber hball

/--
Proposition `utility`, all bounded direction groups are measurable once every
group fiber and the source norm are measurable.
-/
theorem paper_measurable_set_bounded_direction_group_set_all_of_fibers_and_measurable_norm
    {D N : ℕ} {group : Content D → Fin N}
    {ν : SourceNorm D} {R : ℝ}
    (hfiber : ∀ i : Fin N, MeasurableSet {v : Content D | group v = i})
    (hnorm_meas : Measurable ν.norm) :
    ∀ i : Fin N,
      MeasurableSet (paper_bounded_direction_group_set group i ν R) :=
  measurableSet_boundedDirectionGroupSet_all_of_fibers_and_measurable_norm
    hfiber hnorm_meas

/--
Proposition `utility`, a probability measure whose draws satisfy the radius
bound almost everywhere gives full mass to the source support-radius ball.
-/
theorem paper_measure_real_source_support_ball_eq_one_of_ae_norm_le
    {D : ℕ} {μ : MeasureTheory.Measure (Content D)}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : SourceNorm D} {R : ℝ}
    (hae : ∀ᵐ p ∂μ, ν.norm p ≤ R) :
    μ.real (paper_source_support_ball ν R) = 1 :=
  measureReal_sourceSupportBall_eq_one_of_ae_norm_le hae

/--
Proposition `utility`, product event measurability: if the one-producer
selected bounded group is measurable, then so is the event that every opponent
producer lies in it.
-/
theorem paper_measurable_set_all_other_producers_in_bounded_direction_group
    {D N P : ℕ} {group : Content D → Fin N} {i : Fin N}
    {ν : SourceNorm D} {R : ℝ}
    (hgroup_meas : MeasurableSet (paper_bounded_direction_group_set group i ν R))
    (j : Fin P) :
    MeasurableSet
      (paper_all_other_producers_in_bounded_direction_group j group i ν R) :=
  measurableSet_allOtherProducersInBoundedDirectionGroup hgroup_meas j

/--
Proposition `utility`, independent product probability: the probability that
all `P-1` opponent producers lie in the selected bounded group is the
`(P-1)`-power of the one-producer mass.
-/
theorem paper_measure_real_all_other_producers_in_bounded_direction_group_eq_rpow
    {D N P : ℕ} [Nontrivial (Fin P)]
    {μ : MeasureTheory.Measure (Content D)}
    [MeasureTheory.IsProbabilityMeasure μ]
    (j : Fin P) (group : Content D → Fin N) (i : Fin N)
    (ν : SourceNorm D) (R : ℝ) :
    (MeasureTheory.Measure.pi (fun _ : Fin P => μ)).real
        (paper_all_other_producers_in_bounded_direction_group j group i ν R) =
      (μ.real (paper_bounded_direction_group_set group i ν R)) ^ ((P : ℝ) - 1) :=
  measureReal_allOtherProducersInBoundedDirectionGroup_eq_rpow j group i ν R

/--
Proposition `utility`, finite partition mass accounting: the selected bounded
direction groups partition the source support-radius ball, so their real
measures sum to the support-ball measure.
-/
theorem paper_sum_measure_real_bounded_direction_group_set_eq_source_support_ball
    {D N : ℕ} {μ : MeasureTheory.Measure (Content D)}
    [MeasureTheory.IsFiniteMeasure μ]
    (group : Content D → Fin N) (ν : SourceNorm D) (R : ℝ)
    (hmeas : ∀ i : Fin N,
      MeasurableSet (paper_bounded_direction_group_set group i ν R)) :
    (∑ i : Fin N, μ.real (paper_bounded_direction_group_set group i ν R)) =
      μ.real (paper_source_support_ball ν R) :=
  sum_measureReal_boundedDirectionGroupSet_eq_sourceSupportBall
    group ν R hmeas

/--
Proposition `utility`, pigeonhole mass accounting: if the mixed strategy is
supported in the support-radius ball, then some selected bounded direction
group has one-producer mass at least `1/N`.
-/
theorem paper_exists_bounded_direction_group_mass_ge_one_div_card
    {D N : ℕ} [Nonempty (Fin N)]
    {μ : MeasureTheory.Measure (Content D)} [MeasureTheory.IsFiniteMeasure μ]
    (group : Content D → Fin N) (ν : SourceNorm D) (R : ℝ)
    (hmeas : ∀ i : Fin N,
      MeasurableSet (paper_bounded_direction_group_set group i ν R))
    (hsupport : μ.real (paper_source_support_ball ν R) = 1) :
    ∃ i : Fin N, (1 / (N : ℝ)) ≤
      μ.real (paper_bounded_direction_group_set group i ν R) :=
  exists_bounded_direction_group_mass_ge_one_div_card
    group ν R hmeas hsupport

/--
Proposition `utility`, pointwise geometry step: on the bounded selected-group
event, a deviation whose selected-user score beats `Q R` wins that user.
-/
theorem paper_users_won_ge_one_on_bounded_direction_group_deviation
    {D N P : ℕ} {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {i : Fin N} {j : Fin P}
    {profile : Fin P → Content D} {p : Content D} {Q R : ℝ}
    (hprofile :
      profile ∈ paper_all_other_producers_in_bounded_direction_group j group i ν R)
    (hgroup :
      ∀ v : Content D, group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hQ_nonneg : 0 ≤ Q)
    (hdev_score : Q * R < score (users i) p) :
    1 ≤ usersWon users (deviateProfile profile j p) j :=
  usersWon_ge_one_on_bounded_direction_group_deviation
    hprofile hgroup hQ_nonneg hdev_score

/--
Proposition `utility`, generic event lower bound: a nonnegative integrable
random payoff that is at least `c` on event `E` has expectation at least
`c * Pr(E)`.
-/
theorem paper_integral_lower_bound_of_pointwise_event
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → ℝ} {E : Set Ω} {c : ℝ}
    (hE : MeasurableSet E)
    (hf : MeasureTheory.Integrable f μ)
    (hnonneg : 0 ≤ᵐ[μ] f)
    (hevent : ∀ᵐ ω ∂μ, ω ∈ E → c ≤ f ω)
    (hc : 0 ≤ c) :
    c * μ.real E ≤ ∫ ω, f ω ∂μ :=
  integral_lower_bound_of_pointwise_event hE hf hnonneg hevent hc

/--
Proposition `utility`, expected-users event bridge: if the deviation wins at
least `c` users on a measurable event, the expected assigned-user term is at
least `c` times that event's probability.
-/
theorem paper_expected_users_won_lower_bound_of_event
    {D N P : ℕ} {users : Fin N → Content D}
    {μ : MixedContentStrategy D} [MeasureTheory.IsFiniteMeasure μ]
    {p : Content D} {j : Fin P} {E : Set (Fin P → Content D)} {c : ℝ}
    (hE : MeasurableSet E)
    (hint :
      MeasureTheory.Integrable
        (fun profile : Fin P → Content D =>
          usersWon users (deviateProfile profile j p) j)
        (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hevent :
      ∀ᵐ profile ∂MeasureTheory.Measure.pi (fun _ : Fin P => μ),
        profile ∈ E → c ≤ usersWon users (deviateProfile profile j p) j)
    (hc : 0 ≤ c) :
    c * (MeasureTheory.Measure.pi (fun _ : Fin P => μ)).real E ≤
      ExpectedUsersWonAgainstSymmetricMixed users j p μ :=
  expectedUsersWonAgainstSymmetricMixed_lower_bound_of_event hE hint hevent hc

/--
Proposition `utility`, bounded measurable assignment rule: the assigned-user
mass after a fixed deviation is integrable under the product mixed strategy.
-/
theorem paper_integrable_users_won_deviate_profile_const
    {D N P : ℕ} [Nonempty (Fin P)]
    {μ : MeasureTheory.Measure (Content D)} [MeasureTheory.IsProbabilityMeasure μ]
    (users : Fin N → Content D) (j : Fin P) (p : Content D) :
    MeasureTheory.Integrable
      (fun profile : Fin P → Content D =>
        usersWon users (deviateProfile profile j p) j)
      (MeasureTheory.Measure.pi (fun _ : Fin P => μ)) :=
  integrable_usersWon_deviateProfile_const users j p

/--
Proposition `utility`, direct event-to-equilibrium endpoint: if a measurable
event makes the deviation win at least `c` users and the deviation cost is
below `c` times the event probability, then the symmetric equilibrium payoff is
strictly positive.
-/
theorem paper_equilibrium_payoff_pos_of_event_win_lower_bound_and_cost_lt
    {D N P : ℕ} {users : Fin N → Content D}
    {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} [MeasureTheory.IsFiniteMeasure μ]
    {equilibriumPayoff : ℝ} {p : Content D} {j : Fin P}
    {E : Set (Fin P → Content D)} {c : ℝ}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff (ExpectedUsersWonAgainstSymmetricMixed users j) cost)
        μ equilibriumPayoff)
    (hE : MeasurableSet E)
    (hint :
      MeasureTheory.Integrable
        (fun profile : Fin P → Content D =>
          usersWon users (deviateProfile profile j p) j)
        (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hevent :
      ∀ᵐ profile ∂MeasureTheory.Measure.pi (fun _ : Fin P => μ),
        profile ∈ E → c ≤ usersWon users (deviateProfile profile j p) j)
    (hc : 0 ≤ c)
    (hcost : cost p <
      c * (MeasureTheory.Measure.pi (fun _ : Fin P => μ)).real E) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_event_win_lower_bound_and_cost_lt
    hno hE hint hevent hc hcost

/--
Proposition `utility`, expected-users lower bound for the bounded selected
direction-group event.
-/
theorem paper_expected_users_won_lower_bound_of_bounded_direction_group_event
    {D N P : ℕ} {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {i : Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsFiniteMeasure μ]
    {p : Content D} {Q R : ℝ}
    (hE :
      MeasurableSet
        (paper_all_other_producers_in_bounded_direction_group j group i ν R))
    (hint :
      MeasureTheory.Integrable
        (fun profile : Fin P → Content D =>
          usersWon users (deviateProfile profile j p) j)
        (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hgroup :
      ∀ v : Content D, group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hQ_nonneg : 0 ≤ Q)
    (hdev_score : Q * R < score (users i) p) :
    (MeasureTheory.Measure.pi (fun _ : Fin P => μ)).real
        (paper_all_other_producers_in_bounded_direction_group j group i ν R) ≤
      ExpectedUsersWonAgainstSymmetricMixed users j p μ :=
  expectedUsersWonAgainstSymmetricMixed_lower_bound_of_bounded_direction_group_event
    hE hint hgroup hQ_nonneg hdev_score

/--
Proposition `utility`, bounded-group event endpoint: if the selected-group
event is measurable and the deviation cost is below the event probability, the
symmetric equilibrium payoff is strictly positive.
-/
theorem paper_equilibrium_payoff_pos_of_bounded_direction_group_event_cost_lt
    {D N P : ℕ} {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {i : Fin N} {j : Fin P}
    {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} [MeasureTheory.IsFiniteMeasure μ]
    {equilibriumPayoff : ℝ} {p : Content D} {Q R : ℝ}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff (ExpectedUsersWonAgainstSymmetricMixed users j) cost)
        μ equilibriumPayoff)
    (hE :
      MeasurableSet
        (paper_all_other_producers_in_bounded_direction_group j group i ν R))
    (hint :
      MeasureTheory.Integrable
        (fun profile : Fin P → Content D =>
          usersWon users (deviateProfile profile j p) j)
        (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hgroup :
      ∀ v : Content D, group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hQ_nonneg : 0 ≤ Q)
    (hdev_score : Q * R < score (users i) p)
    (hcost :
      cost p <
        (MeasureTheory.Measure.pi (fun _ : Fin P => μ)).real
          (paper_all_other_producers_in_bounded_direction_group j group i ν R)) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_bounded_direction_group_event_cost_lt
    hno hE hint hgroup hQ_nonneg hdev_score hcost

/--
Proposition `utility`, assembled bounded-group endpoint with explicit scaled
unit-direction deviation.  The remaining event-probability input is the strict
gap between the bounded selected-group event probability and `(Q R)^β`.
-/
theorem paper_equilibrium_payoff_pos_of_bounded_group_probability_gap_and_unit_direction
    {D N P : ℕ} {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {i : Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsFiniteMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {direction : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β))
        μ equilibriumPayoff)
    (hE :
      MeasurableSet
        (paper_all_other_producers_in_bounded_direction_group j group i ν R))
    (hint :
      ∀ p : Content D,
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hgroup :
      ∀ v : Content D, group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q) (hR_nonneg : 0 ≤ R)
    (hprob_gap :
      (Q * R) ^ β <
        (MeasureTheory.Measure.pi (fun _ : Fin P => μ)).real
          (paper_all_other_producers_in_bounded_direction_group j group i ν R))
    (hscore_unit : score (users i) direction = 1)
    (hnorm_unit : ν.norm direction = 1) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_bounded_group_probability_gap_and_unit_direction
    hno hE hint hgroup hβ hQ_nonneg hR_nonneg hprob_gap
    hscore_unit hnorm_unit

/--
Proposition `utility`, source-condition endpoint modulo the selected-group
event probability lower bound.  This is the paper's positive-profit argument
after the direction partition supplies its event probability bound.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_and_bounded_group_event
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {i : Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsFiniteMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {direction : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β))
        μ equilibriumPayoff)
    (hE :
      MeasurableSet
        (paper_all_other_producers_in_bounded_direction_group j group i ν R))
    (hint :
      ∀ p : Content D,
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hgroup :
      ∀ v : Content D, group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q) (hR_nonneg : 0 ≤ R)
    (hR : R ^ β ≤ (N : ℝ))
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β))
    (hevent_lower :
      (1 / (N : ℝ)) ^ ((P : ℝ) - 1) ≤
        (MeasureTheory.Measure.pi (fun _ : Fin P => μ)).real
          (paper_all_other_producers_in_bounded_direction_group j group i ν R))
    (hscore_unit : score (users i) direction = 1)
    (hnorm_unit : ν.norm direction = 1) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_and_bounded_group_event
    hno hE hint hgroup hβ hQ_nonneg hR_nonneg hR hQ hevent_lower
    hscore_unit hnorm_unit

/--
Proposition `utility`, selected-group mass bridge: if a selected group has mass
at least `1/N` and the independent event probability is its `(P-1)`-power, then
the event has probability at least `(1/N)^(P-1)`.
-/
theorem paper_selected_group_event_lower_bound_of_mass_power
    {N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {mass eventProb : ℝ}
    (hmass_nonneg : 0 ≤ mass)
    (hmass : (1 / (N : ℝ)) ≤ mass)
    (hevent_eq : eventProb = mass ^ ((P : ℝ) - 1)) :
    (1 / (N : ℝ)) ^ ((P : ℝ) - 1) ≤ eventProb :=
  selected_group_event_lower_bound_of_mass_power hmass_nonneg hmass hevent_eq

/--
Proposition `utility`, source-condition endpoint using a selected-group mass
certificate and the independent-event power identity.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_and_group_mass_event
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {i : Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsFiniteMeasure μ]
    {equilibriumPayoff β Q R mass : ℝ} {direction : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β))
        μ equilibriumPayoff)
    (hE :
      MeasurableSet
        (paper_all_other_producers_in_bounded_direction_group j group i ν R))
    (hint :
      ∀ p : Content D,
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hgroup :
      ∀ v : Content D, group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q) (hR_nonneg : 0 ≤ R)
    (hR : R ^ β ≤ (N : ℝ))
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β))
    (hmass_nonneg : 0 ≤ mass)
    (hmass : (1 / (N : ℝ)) ≤ mass)
    (hevent_eq :
      (MeasureTheory.Measure.pi (fun _ : Fin P => μ)).real
          (paper_all_other_producers_in_bounded_direction_group j group i ν R) =
        mass ^ ((P : ℝ) - 1))
    (hscore_unit : score (users i) direction = 1)
    (hnorm_unit : ν.norm direction = 1) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_and_group_mass_event
    hno hE hint hgroup hβ hQ_nonneg hR_nonneg hR hQ
    hmass_nonneg hmass hevent_eq hscore_unit hnorm_unit

/--
Proposition `utility`, selected-group-measure endpoint: the positive-profit
condition, support-radius bound, and a selected bounded group with mass at
least `1/N` imply strictly positive symmetric-equilibrium payoff.  The
independent product-event probability is derived from the one-producer mass.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_and_selected_group_measure
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {i : Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {direction : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β))
        μ equilibriumPayoff)
    (hgroup_meas : MeasurableSet (paper_bounded_direction_group_set group i ν R))
    (hint :
      ∀ p : Content D,
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hgroup :
      ∀ v : Content D, group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q) (hR_nonneg : 0 ≤ R)
    (hR : R ^ β ≤ (N : ℝ))
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β))
    (hmass :
      (1 / (N : ℝ)) ≤
        μ.real (paper_bounded_direction_group_set group i ν R))
    (hscore_unit : score (users i) direction = 1)
    (hnorm_unit : ν.norm direction = 1) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_and_selected_group_measure
    hno hgroup_meas hint hgroup hβ hQ_nonneg hR_nonneg hR hQ hmass
    hscore_unit hnorm_unit

/--
Proposition `utility`, support-partition endpoint: the positive-profit
condition plus support of the mixed strategy inside the source radius ball
imply strictly positive symmetric-equilibrium payoff.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_and_support_partition
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {direction : Fin N → Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β))
        μ equilibriumPayoff)
    (hmeas :
      ∀ i : Fin N,
        MeasurableSet (paper_bounded_direction_group_set group i ν R))
    (hsupport : μ.real (paper_source_support_ball ν R) = 1)
    (hint :
      ∀ p : Content D,
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hgroup :
      ∀ (i : Fin N) (v : Content D), group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q) (hR_nonneg : 0 ≤ R)
    (hR : R ^ β ≤ (N : ℝ))
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β))
    (hscore_unit : ∀ i : Fin N, score (users i) (direction i) = 1)
    (hnorm_unit : ∀ i : Fin N, ν.norm (direction i) = 1) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_and_support_partition
    hno hmeas hsupport hint hgroup hβ hQ_nonneg hR_nonneg hR hQ
    hscore_unit hnorm_unit

/--
Proposition `utility`, support-partition endpoint with the source support
radius bound derived from the equilibrium outside option and support-action
upper bound.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_support_upper_and_support_partition
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {direction : Fin N → Content D}
    {outside : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β))
        μ equilibriumPayoff)
    (houtside :
      0 ≤
        SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β)
          outside μ)
    (hpayoff_upper : equilibriumPayoff ≤ (N : ℝ) - R ^ β)
    (hmeas :
      ∀ i : Fin N,
        MeasurableSet (paper_bounded_direction_group_set group i ν R))
    (hsupport : μ.real (paper_source_support_ball ν R) = 1)
    (hint :
      ∀ p : Content D,
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hgroup :
      ∀ (i : Fin N) (v : Content D), group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q) (hR_nonneg : 0 ≤ R)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β))
    (hscore_unit : ∀ i : Fin N, score (users i) (direction i) = 1)
    (hnorm_unit : ∀ i : Fin N, ν.norm (direction i) = 1) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_support_upper_and_support_partition
    hno houtside hpayoff_upper hmeas hsupport hint hgroup hβ hQ_nonneg
    hR_nonneg hQ hscore_unit hnorm_unit

/--
Proposition `utility`, support-partition endpoint with the zero-action outside
option discharged.  The remaining support-radius input is the source upper
bound for a support-radius action.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_support_upper_and_support_partition_zero_outside
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {direction : Fin N → Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β))
        μ equilibriumPayoff)
    (hpayoff_upper : equilibriumPayoff ≤ (N : ℝ) - R ^ β)
    (hmeas :
      ∀ i : Fin N,
        MeasurableSet (paper_bounded_direction_group_set group i ν R))
    (hsupport : μ.real (paper_source_support_ball ν R) = 1)
    (hint :
      ∀ p : Content D,
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hgroup :
      ∀ (i : Fin N) (v : Content D), group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q) (hR_nonneg : 0 ≤ R)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β))
    (hscore_unit : ∀ i : Fin N, score (users i) (direction i) = 1)
    (hnorm_unit : ∀ i : Fin N, ν.norm (direction i) = 1) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_support_upper_and_support_partition_zero_outside
    hno hpayoff_upper hmeas hsupport hint hgroup hβ hQ_nonneg hR_nonneg
    hQ hscore_unit hnorm_unit

/--
Proposition `utility`, support-partition endpoint with the support-radius upper
bound derived from a concrete radius-attaining support point.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_support_point_and_support_partition
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {direction : Fin N → Content D}
    {pR : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β))
        μ equilibriumPayoff)
    (hpayoff_eq :
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β)
        pR μ = equilibriumPayoff)
    (hnorm : ν.norm pR = R)
    (hmeas :
      ∀ i : Fin N,
        MeasurableSet (paper_bounded_direction_group_set group i ν R))
    (hsupport : μ.real (paper_source_support_ball ν R) = 1)
    (hint :
      ∀ p : Content D,
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hgroup :
      ∀ (i : Fin N) (v : Content D), group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β))
    (hscore_unit : ∀ i : Fin N, score (users i) (direction i) = 1)
    (hnorm_unit : ∀ i : Fin N, ν.norm (direction i) = 1) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_support_point_and_support_partition
    hno hpayoff_eq hnorm hmeas hsupport hint hgroup hβ hQ_nonneg hQ
    hscore_unit hnorm_unit

/--
Proposition `utility`, support-point endpoint with bounded-group measurability
derived from measurable partition fibers and a measurable source norm.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_support_point_and_measurable_partition
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {direction : Fin N → Content D}
    {pR : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β))
        μ equilibriumPayoff)
    (hpayoff_eq :
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β)
        pR μ = equilibriumPayoff)
    (hnorm : ν.norm pR = R)
    (hfiber : ∀ i : Fin N, MeasurableSet {v : Content D | group v = i})
    (hnorm_meas : Measurable ν.norm)
    (hsupport : μ.real (paper_source_support_ball ν R) = 1)
    (hint :
      ∀ p : Content D,
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hgroup :
      ∀ (i : Fin N) (v : Content D), group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β))
    (hscore_unit : ∀ i : Fin N, score (users i) (direction i) = 1)
    (hnorm_unit : ∀ i : Fin N, ν.norm (direction i) = 1) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_support_point_and_measurable_partition
    hno hpayoff_eq hnorm hfiber hnorm_meas hsupport hint hgroup hβ
    hQ_nonneg hQ hscore_unit hnorm_unit

/--
Proposition `utility`, support-point endpoint with support of the mixed strategy
inside the radius ball stated as an almost-everywhere norm bound.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_support_point_and_ae_supported_partition
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {direction : Fin N → Content D}
    {pR : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β))
        μ equilibriumPayoff)
    (hpayoff_eq :
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β)
        pR μ = equilibriumPayoff)
    (hnorm : ν.norm pR = R)
    (hfiber : ∀ i : Fin N, MeasurableSet {v : Content D | group v = i})
    (hnorm_meas : Measurable ν.norm)
    (hae_support : ∀ᵐ p ∂μ, ν.norm p ≤ R)
    (hint :
      ∀ p : Content D,
        MeasureTheory.Integrable
          (fun profile : Fin P → Content D =>
            usersWon users (deviateProfile profile j p) j)
          (MeasureTheory.Measure.pi (fun _ : Fin P => μ)))
    (hgroup :
      ∀ (i : Fin N) (v : Content D), group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β))
    (hscore_unit : ∀ i : Fin N, score (users i) (direction i) = 1)
    (hnorm_unit : ∀ i : Fin N, ν.norm (direction i) = 1) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_support_point_and_ae_supported_partition
    hno hpayoff_eq hnorm hfiber hnorm_meas hae_support hint hgroup hβ
    hQ_nonneg hQ hscore_unit hnorm_unit

/--
Proposition `utility`, support-point endpoint with support and integrability
discharged from the measurable source model.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_support_point_and_ae_supported_partition_measurable
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {group : Content D → Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {direction : Fin N → Content D}
    {pR : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β))
        μ equilibriumPayoff)
    (hpayoff_eq :
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j) (normRpowCost ν β)
        pR μ = equilibriumPayoff)
    (hnorm : ν.norm pR = R)
    (hfiber : ∀ i : Fin N, MeasurableSet {v : Content D | group v = i})
    (hnorm_meas : Measurable ν.norm)
    (hae_support : ∀ᵐ p ∂μ, ν.norm p ≤ R)
    (hgroup :
      ∀ (i : Fin N) (v : Content D), group v = i →
        score (users i) v ≤ Q * ν.norm v)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β))
    (hscore_unit : ∀ i : Fin N, score (users i) (direction i) = 1)
    (hnorm_unit : ∀ i : Fin N, ν.norm (direction i) = 1) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_support_point_and_ae_supported_partition_measurable
    hno hpayoff_eq hnorm hfiber hnorm_meas hae_support hgroup hβ hQ_nonneg
    hQ hscore_unit hnorm_unit

/--
Proposition `utility`, Euclidean/unit-user specialization: in the paper's main
`||.||_2` setup, unit user vectors themselves provide the deviation directions.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_l2_unit_users_support_point
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {group : Content D → Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {pR : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j)
          (normRpowCost (SourceNorm.l2 D) β))
        μ equilibriumPayoff)
    (hpayoff_eq :
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j)
        (normRpowCost (SourceNorm.l2 D) β) pR μ = equilibriumPayoff)
    (hnorm : (SourceNorm.l2 D).norm pR = R)
    (hfiber : ∀ i : Fin N, MeasurableSet {v : Content D | group v = i})
    (hae_support : ∀ᵐ p ∂μ, (SourceNorm.l2 D).norm p ≤ R)
    (hgroup :
      ∀ (i : Fin N) (v : Content D), group v = i →
        score (users i) v ≤ Q * (SourceNorm.l2 D).norm v)
    (hunit_users : ∀ i : Fin N, (SourceNorm.l2 D).norm (users i) = 1)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β)) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_l2_unit_users_support_point
    hno hpayoff_eq hnorm hfiber hae_support hgroup hunit_users hβ hQ_nonneg hQ

/--
Proposition `utility`, source-geometry Euclidean endpoint: with unit users,
radius-bounded support, a radius-attaining support action, the source
direction-clustering rule, and the source definition of `Q`, every symmetric
mixed equilibrium has strictly positive payoff under the paper's printed
condition `Q < (1/N)^(P/β)`.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_l2_unit_users_source_geometry_support_point
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {group : Content D → Fin N} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {pR : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j)
          (normRpowCost (SourceNorm.l2 D) β))
        μ equilibriumPayoff)
    (hpayoff_eq :
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j)
        (normRpowCost (SourceNorm.l2 D) β) pR μ = equilibriumPayoff)
    (hnorm : (SourceNorm.l2 D).norm pR = R)
    (hfiber : ∀ i : Fin N, MeasurableSet {v : Content D | group v = i})
    (hae_support : ∀ᵐ p ∂μ, (SourceNorm.l2 D).norm p ≤ R)
    (hgroup_min : paper_source_direction_group_min users (SourceNorm.l2 D) group)
    (hQupper : paper_source_unit_direction_Q_upper_bound users (SourceNorm.l2 D) Q)
    (hunit_users : ∀ i : Fin N, (SourceNorm.l2 D).norm (users i) = 1)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β)) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_l2_unit_users_source_geometry_support_point
    hno hpayoff_eq hnorm hfiber hae_support hgroup_min hQupper hunit_users
    hβ hQ_nonneg hQ

/--
Proposition `utility`, canonical source-clustering Euclidean endpoint: the
finite min-score grouping is instantiated with least-index tie-breaking. Its
measurable fibers are derived from the source score functions.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_l2_unit_users_canonical_group_support_point
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {pR : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j)
          (normRpowCost (SourceNorm.l2 D) β))
        μ equilibriumPayoff)
    (hpayoff_eq :
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j)
        (normRpowCost (SourceNorm.l2 D) β) pR μ = equilibriumPayoff)
    (hnorm : (SourceNorm.l2 D).norm pR = R)
    (hae_support : ∀ᵐ p ∂μ, (SourceNorm.l2 D).norm p ≤ R)
    (hQupper : paper_source_unit_direction_Q_upper_bound users (SourceNorm.l2 D) Q)
    (hunit_users : ∀ i : Fin N, (SourceNorm.l2 D).norm (users i) = 1)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β)) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_l2_unit_users_canonical_group_support_point
    hno hpayoff_eq hnorm hae_support hQupper hunit_users
    hβ hQ_nonneg hQ

/--
Proposition `utility`, source-min cover Euclidean endpoint: with unit users,
radius-bounded support, a radius-attaining support action, and the source
definition of `Q`, the paper's printed condition `Q < (1/N)^(P/β)` implies
strictly positive symmetric mixed-equilibrium payoff. This version uses the
overlapping measurable min-direction cover instead of carrying a tie-broken
group selector.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_l2_unit_users_source_min_cover_support_point
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {pR : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j)
          (normRpowCost (SourceNorm.l2 D) β))
        μ equilibriumPayoff)
    (hpayoff_eq :
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j)
        (normRpowCost (SourceNorm.l2 D) β) pR μ = equilibriumPayoff)
    (hnorm : (SourceNorm.l2 D).norm pR = R)
    (hae_support : ∀ᵐ p ∂μ, (SourceNorm.l2 D).norm p ≤ R)
    (hQupper : paper_source_unit_direction_Q_upper_bound users (SourceNorm.l2 D) Q)
    (hunit_users : ∀ i : Fin N, (SourceNorm.l2 D).norm (users i) = 1)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β)) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_l2_unit_users_source_min_cover_support_point
    hno hpayoff_eq hnorm hae_support hQupper hunit_users hβ hQ_nonneg hQ

/--
Proposition `utility`, source-normalized Euclidean endpoint: the paper's
condition is stated using normalized users `u_i / ||u_i||_2`, while the mixed
payoff game remains the original recommendation game. Nonzero users make this
normalization positive, so each user's winning producers and expected
assignment probabilities are preserved.
-/
theorem paper_equilibrium_payoff_pos_of_positive_profit_condition_l2_normalized_users_source_min_cover_support_point
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q R : ℝ} {pR : Content D}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j)
          (normRpowCost (SourceNorm.l2 D) β))
        μ equilibriumPayoff)
    (hpayoff_eq :
      SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j)
        (normRpowCost (SourceNorm.l2 D) β) pR μ = equilibriumPayoff)
    (hnorm : (SourceNorm.l2 D).norm pR = R)
    (hae_support : ∀ᵐ p ∂μ, (SourceNorm.l2 D).norm p ≤ R)
    (hQupper :
      paper_source_unit_direction_Q_upper_bound
        (paper_l2_normalized_users users) (SourceNorm.l2 D) Q)
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β)) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_l2_normalized_users_source_min_cover_support_point
    hno hpayoff_eq hnorm hae_support hQupper husers_nonzero hβ hQ_nonneg hQ

/--
Proposition `utility`, source-normalized Euclidean endpoint under explicit
mixed-equilibrium semantics.  No pure deviation beats `equilibriumPayoff`, and
almost every action drawn from the mixed strategy earns exactly that payoff.
Those premises derive the essential support norm bound; no radius-attaining
support action is assumed.
-/
theorem paper_proposition_utility_positive_equilibrium_payoff_l2_normalized_ae_support_payoff
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff β Q : ℝ}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j)
          (normRpowCost (SourceNorm.l2 D) β))
        μ equilibriumPayoff)
    (hae_support_payoff :
      ∀ᵐ p ∂μ,
        SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j)
          (normRpowCost (SourceNorm.l2 D) β) p μ = equilibriumPayoff)
    (hQupper :
      paper_source_unit_direction_Q_upper_bound
        (paper_l2_normalized_users users) (SourceNorm.l2 D) Q)
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β)) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positive_profit_condition_l2_normalized_users_source_min_cover_ae_equilibrium_payoff
    hno hae_support_payoff hQupper husers_nonzero hβ hQ_nonneg hQ

/--
Proposition `utility`, payoff lower-bound algebra: expected assigned-user mass
at least `eventMass` and cost at most `costUpper` imply payoff at least
`eventMass - costUpper`.
-/
theorem paper_source_mixed_pure_payoff_ge_event_mass_sub_cost_upper
    {D : ℕ} {expectedUsersWon : Content D → MixedContentStrategy D → ℝ}
    {cost : Content D → ℝ} {p : Content D} {μ : MixedContentStrategy D}
    {eventMass costUpper : ℝ}
    (hexpected : eventMass ≤ expectedUsersWon p μ)
    (hcost : cost p ≤ costUpper) :
    eventMass - costUpper ≤
      SourceMixedPurePayoff expectedUsersWon cost p μ :=
  sourceMixedPurePayoff_ge_eventMass_sub_costUpper hexpected hcost

/--
Proposition `utility`, positive-deviation algebra: if expected assigned-user
mass is at least `eventMass` and cost is strictly below `eventMass`, the pure
deviation has strictly positive payoff.
-/
theorem paper_source_mixed_pure_payoff_pos_of_event_mass_lower_bound_and_cost_lt
    {D : ℕ} {expectedUsersWon : Content D → MixedContentStrategy D → ℝ}
    {cost : Content D → ℝ} {p : Content D} {μ : MixedContentStrategy D}
    {eventMass : ℝ}
    (hexpected : eventMass ≤ expectedUsersWon p μ)
    (hcost : cost p < eventMass) :
    0 < SourceMixedPurePayoff expectedUsersWon cost p μ :=
  sourceMixedPurePayoff_pos_of_eventMass_lower_bound_and_cost_lt hexpected hcost

/--
Proposition `utility`, event/cost-to-equilibrium endpoint: a pure deviation
whose expected assigned-user lower bound exceeds its cost forces positive
equilibrium profit.
-/
theorem paper_equilibrium_payoff_pos_of_event_mass_lower_bound_and_cost_lt
    {D : ℕ} {equilibriumPayoff : ℝ}
    {expectedUsersWon : Content D → MixedContentStrategy D → ℝ}
    {cost : Content D → ℝ} {p : Content D} {μ : MixedContentStrategy D}
    {eventMass : ℝ}
    (hno :
      SymmetricMixedNoProfitablePureDeviation
        (SourceMixedPurePayoff expectedUsersWon cost) μ equilibriumPayoff)
    (hexpected : eventMass ≤ expectedUsersWon p μ)
    (hcost : cost p < eventMass) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_eventMass_lower_bound_and_cost_lt hno hexpected hcost

/--
Proposition `utility`, final deviation bridge: if the source geometry
construction produces a pure deviation with payoff at least the positive gap,
then the symmetric equilibrium payoff is strictly positive.
-/
theorem paper_proposition_utility_positive_equilibrium_payoff_of_geometry_gap
    {D N P : ℕ} {β Q R equilibriumPayoff : ℝ}
    {payoff : Content D → MixedContentStrategy D → ℝ}
    {μ : MixedContentStrategy D}
    (hno : SymmetricMixedNoProfitablePureDeviation payoff μ equilibriumPayoff)
    (hgap : 0 < paper_positive_profit_geometry_gap N P β Q R)
    (hdev :
      ∃ p : Content D,
        paper_positive_profit_geometry_gap N P β Q R ≤ payoff p μ) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_positiveProfitGeometryGap_deviation hno hgap hdev

/--
Proposition `utility`, generic final step: a pure content deviation with
strictly positive payoff forces positive common equilibrium payoff.
-/
theorem paper_proposition_utility_positive_equilibrium_payoff_of_profitable_deviation
    {D : ℕ} {equilibriumPayoff : ℝ}
    {payoff : Content D → MixedContentStrategy D → ℝ}
    {μ : MixedContentStrategy D}
    (hno : SymmetricMixedNoProfitablePureDeviation payoff μ equilibriumPayoff)
    (hdev : ∃ p : Content D, 0 < payoff p μ) :
    0 < equilibriumPayoff :=
  equilibriumPayoff_pos_of_profitable_pure_deviation hno hdev

/-! ## Direct mixed-Nash conclusions for the closed-form constructions -/

/--
The iid diagonal extension of the source's uniform-tie assigned-user payoff.
This full-profile formulation is the one used to validate the diagonal
calculation in Proposition `existence`.
-/
noncomputable abbrev paper_symmetric_mixed_diagonal_expected_users_won {D N : ℕ} (P : ℕ)
    (users : Fin N → Content D) (j : Fin P)
    (μ : MixedContentStrategy D) : ℝ :=
  SymmetricMixedDiagonalExpectedUsersWon users j μ

/-- The iid diagonal mixed payoff used in the source existence proof. -/
noncomputable abbrev paper_source_symmetric_mixed_diagonal_payoff {D N : ℕ} (P : ℕ)
    (users : Fin N → Content D) (cost : Content D → ℝ) (j : Fin P)
    (μ : MixedContentStrategy D) : ℝ :=
  SourceSymmetricMixedDiagonalPayoff users cost j μ

/--
Proposition `existence`, checked diagonal user-allocation identity: under iid
symmetric mixed play and the paper's uniform tie rule, every producer receives
exactly `N / P` expected users.
-/
theorem paper_lemma_existence_diagonal_expected_users_won
    {D N P : ℕ} [Nonempty (Fin P)]
    (users : Fin N → Content D) (μ : MixedContentStrategy D)
    [MeasureTheory.IsProbabilityMeasure μ] (j : Fin P) :
    paper_symmetric_mixed_diagonal_expected_users_won P users j μ =
      (N : ℝ) / (P : ℝ) :=
  symmetricMixedDiagonalExpectedUsersWon_eq_card_div users μ j

/--
Proposition `existence`, checked diagonal-payoff formula.  Cost integrability
is explicit so that the displayed integral has its intended expected-cost
interpretation.  For the paper's Euclidean norm-power specialization on the
compact truncated action set, its weak-topology continuity is formalized
immediately below.
-/
theorem paper_lemma_existence_diagonal_payoff_formula
    {D N P : ℕ} [Nonempty (Fin P)]
    (users : Fin N → Content D) (cost : Content D → ℝ)
    (μ : MixedContentStrategy D) [MeasureTheory.IsProbabilityMeasure μ]
    (j : Fin P) (hcost : MeasureTheory.Integrable cost μ) :
    paper_source_symmetric_mixed_diagonal_payoff P users cost j μ =
      (N : ℝ) / (P : ℝ) - ∫ p, cost p ∂μ :=
  sourceSymmetricMixedDiagonalPayoff_eq_card_div_sub_integral
    users cost μ j hcost

/--
Proposition `existence`, source-faithful diagonal continuity step.  For the
finite-dimensional Euclidean norm-power model on the compact truncated action
set, the original diagonal payoff of the pushed-forward mixed strategy is
weakly continuous.  This establishes the source assertion at
`arxiv-update.tex:858-862`; it does not by itself establish better-reply
security for the discontinuous off-diagonal game.
-/
theorem paper_lemma_existence_truncated_l2_diagonal_payoff_continuous
    {D N P : ℕ} [Nonempty (Fin P)] {β R : ℝ} (hβ : 0 ≤ β)
    (users : Fin N → Content D) (j : Fin P) :
    Continuous fun μ : ProbabilityMeasure
      (sourceTruncatedActionSet (SourceNorm.l2 D) R) =>
      paper_source_symmetric_mixed_diagonal_payoff P users
        (normRpowCost (SourceNorm.l2 D) β) j
        (JGS23SupplySideRecommenderSystems.sourceTruncatedStrategyToMixedContent
          (SourceNorm.l2 D) R μ).toMeasure := by
  apply (JGS23SupplySideRecommenderSystems.continuous_sourceTruncatedDiagonalPayoff_l2_normRpowCost
    (N := N) (P := P) hβ).congr
  intro μ
  exact (sourceSymmetricMixedDiagonalPayoff_sourceTruncatedStrategy users
    (SourceNorm.l2 D) R (SourceNorm.l2_compactSublevels D)
    (normRpowCost (SourceNorm.l2 D) β) μ j).symm

/--
Proposition `existence`, finite atom-avoidance substep.  Under the source
model's individual active-user condition, a sufficiently small perturbation in
the aggregate-user direction remains nonnegative and misses every
positive-mass score level.  This proves only the countability/feasibility part
of the better-reply-security construction; the strict payoff and topology
arguments remain separate obligations.
-/
theorem paper_lemma_existence_small_atom_avoiding_aggregate_perturbation
    {D N : ℕ} {users : Fin N → Content D}
    {μ : MixedContentStrategy D} {p : Content D} {ε : ℝ}
    [MeasureTheory.IsProbabilityMeasure μ]
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hp : NonnegativeContent p) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧
      NonnegativeContent (p + t • aggregateUsersContent users) ∧
      ∀ i : Fin N,
        μ {q : Content D |
          score (users i) q = score (users i) (p + t • aggregateUsersContent users)} = 0 :=
  exists_small_score_atom_avoiding_aggregatePerturbation
    husers_nonnegative husers_nonzero hp hε

/--
Proposition `existence`, profitable atom-avoiding perturbation.  Given an
actual strict pure-payoff gap over `α`, continuity of the cost and monotonicity
of uniform-tie allocation give a positive aggregate-user perturbation that
remains feasible and strictly profitable while avoiding every user-score atom.
This closes the source's previously unstated simultaneous choice of the small
cost-continuity radius and the atom-avoidance radius; the separate
Prokhorov/topology and corrected discontinuous-game security steps remain.
-/
theorem paper_lemma_existence_profitable_atom_avoiding_aggregate_perturbation
    {D N P : ℕ} [Nonempty (Fin P)] {users : Fin N → Content D}
    {μ : MixedContentStrategy D} {p : Content D} {j : Fin P}
    {cost : Content D → ℝ} {α : ℝ}
    [MeasureTheory.IsProbabilityMeasure μ]
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hp : NonnegativeContent p) (hcont : PerturbationCostContinuous cost)
    (hprofit : α < paper_expected_users_won_against_symmetric_mixed users j p μ - cost p) :
    ∃ t : ℝ, 0 < t ∧
      NonnegativeContent (p + t • aggregateUsersContent users) ∧
      (∀ i : Fin N,
        μ {q : Content D |
          score (users i) q = score (users i) (p + t • aggregateUsersContent users)} = 0) ∧
      α < paper_expected_users_won_against_symmetric_mixed users j
        (p + t • aggregateUsersContent users) μ -
          cost (p + t • aggregateUsersContent users) :=
  _root_.JGS23SupplySideRecommenderSystems.exists_small_score_atom_avoiding_profitable_aggregatePerturbation
    husers_nonnegative husers_nonzero hp hcont hprofit

/--
Proposition `existence`, tie-aware strict-score lower bound.  Even before
eliminating all ties, the actual uniform-tie expected allocation is at least
the sum of probabilities that every opponent has strictly lower score.  Thus
the source's strict-score expression is a valid lower bound, not an
unqualified equality.
-/
theorem paper_lemma_existence_tie_aware_strict_score_lower_bound
    {D N P : ℕ} [Nonempty (Fin P)] {users : Fin N → Content D} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    (p : Content D)
    (hmeas_score : ∀ i : Fin N,
      Measurable (fun q : Content D => score (users i) q)) :
    ∑ i : Fin N,
      (μ.real {q : Content D | score (users i) q < score (users i) p}) ^ (P - 1) ≤
      paper_expected_users_won_against_symmetric_mixed users j p μ :=
  expectedUsersWonAgainstSymmetricMixed_ge_sum_strictScoreMass p hmeas_score

/--
Proposition `existence`, Prokhorov-neighborhood payoff bound.  If every
baseline strict-score event's `ε`-thickening lies in the candidate strict-score
event, the actual uniform-tie payoff against a nearby law is bounded below by
the sum of the baseline masses minus the standard Prokhorov error.  The error
is clipped at zero before exponentiation, as required for a valid natural-power
lower bound.
-/
theorem paper_lemma_existence_prokhorov_tie_aware_lower_bound
    {D N P : ℕ} [Nonempty (Fin P)] {users : Fin N → Content D} {j : Fin P}
    {μ ν : MixedContentStrategy D}
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    {ε : ENNReal} (hε : ε ≠ ⊤)
    (hdist : MeasureTheory.levyProkhorovEDist μ ν < ε)
    (p : Content D)
    (threshold : Fin N → ℝ)
    (hmeas_score : ∀ i : Fin N,
      Measurable (fun q : Content D => score (users i) q))
    (hthickening : ∀ i : Fin N,
      Metric.thickening ε.toReal {q : Content D | score (users i) q < threshold i} ⊆
        {q : Content D | score (users i) q < score (users i) p}) :
    (∑ i : Fin N,
      (max 0 (μ.real {q : Content D | score (users i) q < threshold i} - ε.toReal)) ^
        (P - 1)) ≤
      paper_expected_users_won_against_symmetric_mixed users j p ν :=
  _root_.JGS23SupplySideRecommenderSystems.expectedUsersWonAgainstSymmetricMixed_ge_sum_prokhorov_lowerBound
    hε hdist p threshold hmeas_score hthickening

/--
Proposition `existence`, literal source `L2` event geometry.  The source's
Euclidean thickening of the strict-score event with margin
`ε * ||u||₂` is contained in the candidate strict-score event.
-/
theorem paper_lemma_existence_source_l2_strict_score_thickening
    {D : ℕ} (u p : Content D) (ε : ℝ) :
    sourceL2Thickening ε
        {q : Content D |
          score u q < score u p - ε * AppliedModelingLib.FiniteDimensionalNorms.l2 u} ⊆
      {q : Content D | score u q < score u p} :=
  sourceL2Thickening_strict_score_event_subset u p ε

/--
Proposition `existence`, literal source `L2` topology step.  After representing
the action space as finite Euclidean space, a positive Lévy--Prokhorov ball is
an open weak/convergence-in-distribution neighborhood of its center.  The
explicit `sourceL2ContentHomeomorph` identifies this topology with the finite
coordinate content topology used by the executable game model.
-/
theorem paper_lemma_existence_source_l2_prokhorov_ball_weak_open
    {D : ℕ} (μ : MeasureTheory.ProbabilityMeasure (SourceL2Content D))
    (ε : ℝ) :
    IsOpen {ν : MeasureTheory.ProbabilityMeasure (SourceL2Content D) |
      dist (MeasureTheory.LevyProkhorov.ofMeasure ν)
        (MeasureTheory.LevyProkhorov.ofMeasure μ) < ε} :=
  isOpen_sourceL2_levyProkhorovBall μ ε

/--
Proposition `existence`, concrete score-margin version of the Prokhorov payoff
bound for Lean's ambient finite product metric.  A score margin of
`ε * ||u_i||₁` makes the required thickening inclusion automatic.  The source
`L2` metric and its weak-open Prokhorov ball are formalized separately above;
this theorem is the directly executable equivalent finite-product-metric route.
-/
theorem paper_lemma_existence_prokhorov_l1_score_margin_lower_bound
    {D N P : ℕ} [Nonempty (Fin P)] {users : Fin N → Content D} {j : Fin P}
    {μ ν : MixedContentStrategy D}
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    {ε : ENNReal} (hε : ε ≠ ⊤)
    (hdist : MeasureTheory.levyProkhorovEDist μ ν < ε)
    (p : Content D) :
    (∑ i : Fin N,
      (max 0 (μ.real
        {q : Content D |
          score (users i) q < score (users i) p -
            ε.toReal * AppliedModelingLib.FiniteDimensionalNorms.l1 (users i)} - ε.toReal)) ^
        (P - 1)) ≤
      paper_expected_users_won_against_symmetric_mixed users j p ν :=
  _root_.JGS23SupplySideRecommenderSystems.expectedUsersWonAgainstSymmetricMixed_ge_sum_prokhorov_l1ScoreMargin
    hε hdist p

/--
Proposition `existence`, local payoff-security conclusion for the executable
finite-product-metric route.  A strict score-margin lower bound at the
baseline law yields one positive Lévy--Prokhorov radius on which the fixed pure
action's actual uniform-tie payoff remains strictly above `α`.  This performs
the finite clipped-power continuity step in `arxiv-update.tex:884-896`, with
the necessary zero clipping already built into the bound.
-/
theorem paper_lemma_existence_prokhorov_security_of_l1_score_margin_slack
    {D N P : ℕ} [Nonempty (Fin P)] {users : Fin N → Content D} {j : Fin P}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {p : Content D} {cost : Content D → ℝ} {α margin : ℝ}
    (hmargin : 0 < margin)
    (hprofit : α <
      (∑ i : Fin N,
        (μ.real {q : Content D | score (users i) q < score (users i) p -
          margin * AppliedModelingLib.FiniteDimensionalNorms.l1 (users i)}) ^ (P - 1)) - cost p) :
    ∃ ε : ENNReal, ε ≠ ⊤ ∧ 0 < ε ∧
      ∀ ν : MixedContentStrategy D, MeasureTheory.IsProbabilityMeasure ν →
        MeasureTheory.levyProkhorovEDist μ ν < ε →
          α < paper_expected_users_won_against_symmetric_mixed users j p ν - cost p :=
  _root_.JGS23SupplySideRecommenderSystems.exists_prokhorovEDist_neighborhood_payoff_gt_of_l1ScoreMarginSlack
    hmargin hprofit

/--
Proposition `existence`, composed tie-aware security construction in the
ambient nonnegative domain.  From a strictly profitable nonnegative pure
deviation, Lean builds one atom-avoiding securing action and one positive
Lévy--Prokhorov neighborhood where that action remains strictly profitable.
The compact-action refinement appears immediately below.
-/
theorem paper_lemma_existence_l1_secure_payoff_neighborhood_of_profitable_deviation
    {D N P : ℕ} [Nonempty (Fin P)] {users : Fin N → Content D}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {p : Content D} {j : Fin P} {cost : Content D → ℝ} {α : ℝ}
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hp : NonnegativeContent p) (hcont : PerturbationCostContinuous cost)
    (hprofit : α < paper_expected_users_won_against_symmetric_mixed users j p μ - cost p) :
    ∃ psec : Content D, NonnegativeContent psec ∧
      ∃ ε : ENNReal, ε ≠ ⊤ ∧ 0 < ε ∧
        ∀ ν : MixedContentStrategy D, MeasureTheory.IsProbabilityMeasure ν →
          MeasureTheory.levyProkhorovEDist μ ν < ε →
            α < paper_expected_users_won_against_symmetric_mixed users j psec ν - cost psec :=
  _root_.JGS23SupplySideRecommenderSystems.exists_l1ScoreMargin_secure_payoff_neighborhood_of_profitable_deviation
    husers_nonnegative husers_nonzero hp hcont hprofit

/--
Proposition `existence`, compact-action better-reply-security construction.
If the profitable deviation is strictly inside the source truncated action
ball and the source norm is continuous, both source perturbations can be
chosen inside that same ball.  The returned action is therefore a valid pure
deviation of the compact game throughout its positive Lévy--Prokhorov
neighborhood.  This closes the compact-feasibility issue in
`arxiv-update.tex:859-896`; the corrected external Reny condition is separate.
-/
theorem paper_lemma_existence_l1_secure_payoff_neighborhood_within_truncated_action_set
    {D N P : ℕ} [Nonempty (Fin P)] {users : Fin N → Content D}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {p : Content D} {j : Fin P} {cost : Content D → ℝ}
    {ν : SourceNorm D} {R α : ℝ}
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hp : NonnegativeContent p) (hcont : PerturbationCostContinuous cost)
    (hνcont : Continuous ν.norm) (hpR : ν.norm p < R)
    (hprofit : α < paper_expected_users_won_against_symmetric_mixed users j p μ - cost p) :
    ∃ psec : Content D, psec ∈ sourceTruncatedActionSet ν R ∧
      ∃ ε : ENNReal, ε ≠ ⊤ ∧ 0 < ε ∧
        ∀ μ' : MixedContentStrategy D, MeasureTheory.IsProbabilityMeasure μ' →
          MeasureTheory.levyProkhorovEDist μ μ' < ε →
            α < paper_expected_users_won_against_symmetric_mixed users j psec μ' - cost psec :=
  _root_.JGS23SupplySideRecommenderSystems.exists_l1ScoreMargin_secure_payoff_neighborhood_of_profitable_deviation_within_sourceTruncatedActionSet
    husers_nonnegative husers_nonzero hp hcont hνcont hpR hprofit

/--
Proposition `existence`, quantitative truncation slack: the source inner cap
`N^(1 / beta)` is strictly inside the doubled compact cap for a nonempty user
population.
-/
theorem paper_lemma_existence_inner_cap_strictly_inside_doubled_cap
    {D N : ℕ} [Nonempty (Fin N)] {ν : SourceNorm D}
    {p : Content D} {β : ℝ}
    (hp : ν.norm p ≤ (N : ℝ) ^ β⁻¹) :
    ν.norm p < 2 * ((N : ℝ) ^ β⁻¹) :=
  _root_.JGS23SupplySideRecommenderSystems.norm_lt_double_support_cap_of_norm_le_support_cap hp

/--
Proposition `existence`, corrected diagonal payoff-security statement for pure
deviations.  Following the Ewerhart--Reny corrigendum, the secured target is
the payoff of the actual deviation `p` at the diagonal baseline, less an
arbitrary positive tolerance.  For the JGS doubled compact game, Lean proves
that target is secured on a weak neighborhood by a feasible pure action.

This is intentionally a pure-deviation result.  It is not a claim that the
mixed extension itself is quasisymmetric or that the corrected external
Reny theorem has already been applied.
-/
theorem paper_lemma_existence_corrected_pure_diagonal_payoff_security
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)]
    {users : Fin N → Content D} {j : Fin P} {ν : SourceNorm D} {β : ℝ}
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hcostcont : PerturbationCostContinuous (paper_norm_rpow_cost ν β))
    (hνcont : Continuous ν.norm) (hβ : 0 < β) :
    AppliedModelingLib.PureDiagonalPayoffSecureOn
      (sourceTruncatedActionSet ν (2 * ((N : ℝ) ^ β⁻¹)))
      (SourceMixedPurePayoffOnProbabilityMeasure users j (paper_norm_rpow_cost ν β)) :=
  _root_.JGS23SupplySideRecommenderSystems.pureDiagonalPayoffSecureOn_sourceTruncatedActionSet_normRpowCost
    husers_nonnegative husers_nonzero hcostcont hνcont hβ

/--
Proposition `existence`, full corrected diagonal payoff security of the compact
mixed extension.  This lifts the checked pure-action security result using
joint measurability and compact bounded integrability of the actual
uniform-tie payoff; it is not an unproved continuity surrogate.
-/
theorem paper_lemma_existence_corrected_mixed_diagonal_payoff_security
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)]
    {users : Fin N → Content D} {j : Fin P} {ν : SourceNorm D} {β : ℝ}
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hcompact : SourceNormCompactSublevels ν)
    (hcostcont : PerturbationCostContinuous (paper_norm_rpow_cost ν β))
    (hνcont : Continuous ν.norm) (hβ : 0 < β) :
    AppliedModelingLib.DiagonallyPayoffSecure
      (AppliedModelingLib.MixedExtensionPayoff
        (SourceTruncatedMixedPurePayoff users ν (2 * ((N : ℝ) ^ β⁻¹)) j
          (paper_norm_rpow_cost ν β))) :=
  _root_.JGS23SupplySideRecommenderSystems.diagonallyPayoffSecure_sourceTruncatedMixedExtension_normRpowCost
    husers_nonnegative husers_nonzero hcompact hcostcont hνcont hβ

/--
Proposition `existence`, diagonal quasiconcavity of the compact mixed
extension.  The operation on laws is the actual probability-measure affine
mixture, and linearity follows from the checked integrability bridge.
-/
theorem paper_lemma_existence_mixed_diagonal_quasiconcavity
    {D N P : ℕ} [Nonempty (Fin P)]
    {users : Fin N → Content D} {j : Fin P} {ν : SourceNorm D} {β : ℝ}
    (hcompact : SourceNormCompactSublevels ν)
    (hνcont : Continuous ν.norm) (hβ : 0 ≤ β) :
    AppliedModelingLib.DiagonallyProbabilityMeasureQuasiConcave
      (AppliedModelingLib.MixedExtensionPayoff
        (SourceTruncatedMixedPurePayoff users ν (2 * ((N : ℝ) ^ β⁻¹)) j
          (paper_norm_rpow_cost ν β))) :=
  _root_.JGS23SupplySideRecommenderSystems.diagonallyProbabilityMeasureQuasiConcave_sourceTruncatedMixedExtension_normRpowCost
    hcompact hνcont hβ

/-- The compactness of the mixed-law action space used by Proposition `existence`. -/
theorem paper_lemma_existence_compact_mixed_action_space
    {D : ℕ} (ν : SourceNorm D) (R : ℝ)
    (hcompact : SourceNormCompactSublevels ν) :
    IsCompact (Set.univ : Set (ProbabilityMeasure (sourceTruncatedActionSet ν R))) :=
  _root_.JGS23SupplySideRecommenderSystems.isCompact_univ_sourceTruncatedMixedActionSpace
    ν R hcompact

/--
Proposition `existence`, topological convexity input: probability-law mixing
on the compact truncated action space is weakly continuous.  This is a checked
prerequisite for the still-unformalized external fixed-point theorem, not an
assertion that that theorem has been applied.
-/
theorem paper_lemma_existence_continuous_mixed_action_mixture
    {D : ℕ} (ν : SourceNorm D) (R : ℝ) :
    Continuous (fun strategies : unitInterval ×
      (ProbabilityMeasure (sourceTruncatedActionSet ν R) ×
        ProbabilityMeasure (sourceTruncatedActionSet ν R)) =>
      AppliedModelingLib.probabilityMeasureMix strategies.1 strategies.2.1 strategies.2.2) :=
  _root_.JGS23SupplySideRecommenderSystems.continuous_probabilityMeasureMix_sourceTruncatedMixedActionSpace
    ν R

/--
Proposition `existence`, diagonal better-reply security of the compact mixed
extension, derived from the stronger corrected diagonal-payoff-security
theorem rather than assumed.
-/
theorem paper_lemma_existence_mixed_diagonal_better_reply_security
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)]
    {users : Fin N → Content D} {j : Fin P} {ν : SourceNorm D} {β : ℝ}
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hcompact : SourceNormCompactSublevels ν)
    (hcostcont : PerturbationCostContinuous (paper_norm_rpow_cost ν β))
    (hνcont : Continuous ν.norm) (hβ : 0 < β) :
    AppliedModelingLib.DiagonallyBetterReplySecure
      (AppliedModelingLib.MixedExtensionPayoff
        (SourceTruncatedMixedPurePayoff users ν (2 * ((N : ℝ) ^ β⁻¹)) j
          (paper_norm_rpow_cost ν β))) :=
  _root_.JGS23SupplySideRecommenderSystems.diagonallyBetterReplySecure_sourceTruncatedMixedExtension_normRpowCost
    husers_nonnegative husers_nonzero hcompact hcostcont hνcont hβ

/--
The pointwise no-profitable-pure-deviation consequence of a future compact
mixed-extension equilibrium.  It does not replace the separately required
support-regularity bridge.
-/
theorem paper_lemma_existence_pure_payoff_le_of_mixed_diagonal_nash
    {D N P : ℕ} [Nonempty (Fin P)]
    {users : Fin N → Content D} {j : Fin P} {ν : SourceNorm D} {β : ℝ}
    (hνcont : Continuous ν.norm) (hβ : 0 ≤ β)
    {state : ProbabilityMeasure (sourceTruncatedActionSet ν (2 * ((N : ℝ) ^ β⁻¹)))}
    (hnash : AppliedModelingLib.IsDiagonalNash
      (AppliedModelingLib.MixedExtensionPayoff
        (SourceTruncatedMixedPurePayoff users ν (2 * ((N : ℝ) ^ β⁻¹)) j
          (paper_norm_rpow_cost ν β))) state) :
    ∀ action : sourceTruncatedActionSet ν (2 * ((N : ℝ) ^ β⁻¹)),
      SourceTruncatedMixedPurePayoff users ν (2 * ((N : ℝ) ^ β⁻¹)) j
          (paper_norm_rpow_cost ν β) action state ≤
        AppliedModelingLib.MixedExtensionPayoff
          (SourceTruncatedMixedPurePayoff users ν (2 * ((N : ℝ) ^ β⁻¹)) j
            (paper_norm_rpow_cost ν β)) state state :=
  _root_.JGS23SupplySideRecommenderSystems.sourceTruncatedMixedExtension_purePayoff_le_of_diagonalNash_normRpowCost
    hνcont hβ hnash

/--
The a.e. pure-payoff equality entailed by a future compact mixed-extension
equilibrium.  A topological-support-action equality needs additional
regularity and is deliberately not asserted here.
-/
theorem paper_lemma_existence_ae_pure_payoff_eq_of_mixed_diagonal_nash
    {D N P : ℕ} [Nonempty (Fin P)]
    {users : Fin N → Content D} {j : Fin P} {ν : SourceNorm D} {β : ℝ}
    (hcompact : SourceNormCompactSublevels ν)
    (hνcont : Continuous ν.norm) (hβ : 0 ≤ β)
    {state : ProbabilityMeasure (sourceTruncatedActionSet ν (2 * ((N : ℝ) ^ β⁻¹)))}
    (hnash : AppliedModelingLib.IsDiagonalNash
      (AppliedModelingLib.MixedExtensionPayoff
        (SourceTruncatedMixedPurePayoff users ν (2 * ((N : ℝ) ^ β⁻¹)) j
          (paper_norm_rpow_cost ν β))) state) :
    ∀ᵐ action ∂state.toMeasure,
      SourceTruncatedMixedPurePayoff users ν (2 * ((N : ℝ) ^ β⁻¹)) j
          (paper_norm_rpow_cost ν β) action state =
        AppliedModelingLib.MixedExtensionPayoff
          (SourceTruncatedMixedPurePayoff users ν (2 * ((N : ℝ) ^ β⁻¹)) j
            (paper_norm_rpow_cost ν β)) state state :=
  _root_.JGS23SupplySideRecommenderSystems.ae_sourceTruncatedMixedExtension_purePayoff_eq_of_diagonalNash_normRpowCost
    hcompact hνcont hβ hnash

/--
Proposition `existence`, corrected mixed-extension symmetry condition.  In
Plan's mixed-quasi-symmetry formulation, fixing a pure deviation and a common
opponent mixed law gives the same payoff for every focal producer.  The JGS
uniform-tie semantics proves this by an explicit iid producer-label
permutation, rather than by treating symmetry as a slogan.
-/
theorem paper_lemma_existence_mixed_quasi_symmetric
    {D N P : ℕ} [Nonempty (Fin P)]
    (users : Fin N → Content D) (cost : Content D → ℝ) :
    AppliedModelingLib.MixedQuasiSymmetric
      (fun j : Fin P => SourceMixedPurePayoffOnProbabilityMeasure users j cost) :=
  _root_.JGS23SupplySideRecommenderSystems.mixedQuasiSymmetric_sourceMixedPurePayoffOnProbabilityMeasure
    users cost

/--
The same exact mixed-quasi-symmetry condition on the compact action subtype
used by the corrected mixed-extension security theorem.
-/
theorem paper_lemma_existence_truncated_mixed_quasi_symmetric
    {D N P : ℕ} [Nonempty (Fin P)]
    (users : Fin N → Content D) (ν : SourceNorm D) (R : ℝ)
    (cost : Content D → ℝ) :
    AppliedModelingLib.MixedQuasiSymmetric
      (fun j : Fin P => SourceTruncatedMixedPurePayoff users ν R j cost) :=
  _root_.JGS23SupplySideRecommenderSystems.mixedQuasiSymmetric_sourceTruncatedMixedPurePayoff
    users ν R cost

/--
Restricted-game symmetric mixed Nash condition used by Proposition `existence`:
support actions are best responses only to deviations in the displayed compact
content action set.
-/
abbrev paper_source_symmetric_mixed_nash_on_action_set {D N : ℕ} (P : ℕ)
    (actionSet : Set (Content D)) (users : Fin N → Content D)
    (cost : Content D → ℝ) (μ : MixedContentStrategy D) : Prop :=
  SourceSymmetricMixedNashOnActionSet (P := P) actionSet users cost μ

/--
Proposition `existence`, action-space transport: an equilibrium of the
nonnegative compact ball of radius `2 N^(1 / beta)` is already an equilibrium
of the original unbounded source action space.  This closes the source's
truncation step only; it does not assert the separate corrected Reny
mixed-extension existence theorem.
-/
theorem paper_proposition_existence_untruncate_norm_rpow_cost
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {β : ℝ}
    (htruncated :
      paper_source_symmetric_mixed_nash_on_action_set P
        (paper_truncated_content_action_set ν (2 * ((N : ℝ) ^ β⁻¹)))
        users (paper_norm_rpow_cost ν β) μ)
    (hβ : 0 < β) :
    paper_source_symmetric_mixed_nash P users (paper_norm_rpow_cost ν β) μ :=
  sourceSymmetricMixedNash_of_truncatedActionSet_normRpowCost htruncated hβ

/--
The source action-space no-deviation condition: only nonnegative content
actions are permitted. This is the correct bridge from the paper's symmetric
mixed-Nash definition, unlike an unrestricted ambient-content condition.
-/
noncomputable abbrev paper_source_symmetric_mixed_no_profitable_nonnegative_deviation
    {D N P : ℕ} (users : Fin N → Content D) (cost : Content D → ℝ)
    (j : Fin P) (μ : MixedContentStrategy D) (equilibriumPayoff : ℝ) : Prop :=
  SourceSymmetricMixedNoProfitableNonnegativeDeviation users cost j μ equilibriumPayoff

/--
Law-level equilibrium inequalities on the full nonnegative source action space,
together with almost-everywhere equilibrium payoff equality, force every
nonzero user's score distribution to be atomless. This is the explicit bridge
from ordinary mixed-equilibrium output to the tie-nullness needed by the
uniform-tie payoff formulas.
-/
theorem paper_lemma_score_level_measure_real_zero_of_law_equilibrium
    {D N P : ℕ} [Nontrivial (Fin P)] {users : Fin N → Content D}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {cost : Content D → ℝ} {equilibriumPayoff : ℝ} {i0 : Fin N} {j : Fin P}
    (hno : paper_source_symmetric_mixed_no_profitable_nonnegative_deviation
      users cost j μ equilibriumPayoff)
    (hae_payoff : ∀ᵐ p ∂μ,
      paper_source_mixed_pure_payoff
        (paper_expected_users_won_against_symmetric_mixed users j) cost p μ =
          equilibriumPayoff)
    (hae_nonnegative : ∀ᵐ p ∂μ, NonnegativeContent p)
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hcont : PerturbationCostContinuous cost)
    (z : ℝ) :
    μ.real {q : Content D | score (users i0) q = z} = 0 :=
  score_level_measureReal_eq_zero_of_noProfitableNonnegativeDeviation_and_ae_equilibrium_payoff
    hno hae_payoff hae_nonnegative husers_nonnegative hzero hcont z

/--
Once null score fibres are obtained, the actual uniform-tie source payoff is
continuous in a focal content action.  Therefore ordinary law-level a.e.
indifference extends to every topological-support action, provided the
equilibrium bound ranges over the full nonnegative source action space.
-/
theorem paper_lemma_source_support_payoff_eq_of_law_equilibrium
    {D N P : ℕ} {users : Fin N → Content D} {j : Fin P}
    {cost : Content D → ℝ} {μ : MixedContentStrategy D}
    [MeasureTheory.IsProbabilityMeasure μ]
    {equilibriumPayoff : ℝ} {p : Content D}
    (hsupport_nonnegative : μ.support ⊆ {q : Content D | NonnegativeContent q})
    (hno : paper_source_symmetric_mixed_no_profitable_nonnegative_deviation
      users cost j μ equilibriumPayoff)
    (hae_payoff : ∀ᵐ q ∂μ,
      paper_source_mixed_pure_payoff
        (paper_expected_users_won_against_symmetric_mixed users j) cost q μ =
          equilibriumPayoff)
    (hcost : Continuous cost)
    (hscore_null : ∀ (i : Fin N) (z : ℝ),
      μ {q : Content D | score (users i) q = z} = 0)
    (hp : p ∈ μ.support) :
    paper_source_mixed_pure_payoff
      (paper_expected_users_won_against_symmetric_mixed users j) cost p μ =
      equilibriumPayoff :=
  sourceMixedPurePayoff_eq_equilibriumPayoff_of_mem_support_of_law_equilibrium
    hsupport_nonnegative hno hae_payoff hcost hscore_null hp

/--
Source-action semantic conversion for a future law-level equilibrium theorem.
This is not an existence assertion: it states exactly the additional full
nonnegative-deviation, a.e.-indifference, score-atom, and regularity facts
that turn such a law into the source's support-action mixed Nash predicate.
-/
theorem paper_lemma_source_symmetric_mixed_nash_of_law_equilibrium_nonzero_users
    {D N P : ℕ} [Nontrivial (Fin P)] {users : Fin N → Content D}
    {cost : Content D → ℝ} {μ : MixedContentStrategy D}
    (hprobability : MeasureTheory.IsProbabilityMeasure μ)
    (hsupport_nonnegative : μ.support ⊆ {q : Content D | NonnegativeContent q})
    (hlaw_equilibrium : ∀ j : Fin P, ∃ equilibriumPayoff : ℝ,
      paper_source_symmetric_mixed_no_profitable_nonnegative_deviation
        users cost j μ equilibriumPayoff ∧
      ∀ᵐ q ∂μ,
        paper_source_mixed_pure_payoff
          (paper_expected_users_won_against_symmetric_mixed users j) cost q μ =
            equilibriumPayoff)
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hperturb_cost : PerturbationCostContinuous cost)
    (hcost : Continuous cost) :
    paper_source_symmetric_mixed_nash P users cost μ :=
  sourceSymmetricMixedNash_of_law_equilibrium_of_nonzero_users
    hprobability hsupport_nonnegative hlaw_equilibrium husers_nonnegative husers_nonzero
    hperturb_cost hcost

/--
Proposition `existence`, compact-to-full semantic transport.  Once the
corrected Reny route supplies a diagonal Nash law of the compact mixed
extension for every focal producer, its subtype push-forward is already a
source-semantic symmetric mixed Nash equilibrium on the full nonnegative
content space.  The proof includes unbounded deviations and the paper's
topological-support best-response convention.
-/
theorem paper_proposition_existence_source_nash_of_truncated_mixed_diagonal_nash_norm_rpow_cost
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D} {β : ℝ}
    {state : ProbabilityMeasure
      (paper_truncated_content_action_set ν (2 * ((N : ℝ) ^ β⁻¹)))}
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hcompact : SourceNormCompactSublevels ν)
    (hνcont : Continuous ν.norm)
    (hνperturb : SourceNormPerturbationContinuous ν)
    (hβ : 1 ≤ β)
    (hdiagonal : ∀ j : Fin P,
      AppliedModelingLib.IsDiagonalNash
        (AppliedModelingLib.MixedExtensionPayoff
          (SourceTruncatedMixedPurePayoff users ν (2 * ((N : ℝ) ^ β⁻¹)) j
            (paper_norm_rpow_cost ν β))) state) :
    paper_source_symmetric_mixed_nash P users (paper_norm_rpow_cost ν β)
      (sourceTruncatedStrategyToMixedContent ν (2 * ((N : ℝ) ^ β⁻¹)) state).toMeasure :=
  sourceSymmetricMixedNash_of_truncatedMixedExtension_diagonalNash_normRpowCost
    husers_nonnegative husers_nonzero hcompact hνcont hνperturb hβ hdiagonal

/--
Proposition `existence`, completed source-level norm-power route.  This is the
JGS-specialized KKM construction: finite barycentric affinity of the actual
mixed extension supplies the cover used by the compact KKM theorem, and the
proved source transport yields the literal support-action Nash predicate.
It does not assert the more general Reny lower/upper-envelope theorem.
-/
theorem paper_proposition_existence_norm_rpow_cost
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D} {β : ℝ}
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hcompact : SourceNormCompactSublevels ν)
    (hνcont : Continuous ν.norm)
    (hνperturb : SourceNormPerturbationContinuous ν)
    (hβ : 1 ≤ β) :
    ∃ μ : MixedContentStrategy D,
      paper_source_symmetric_mixed_nash P users (paper_norm_rpow_cost ν β) μ :=
  exists_sourceSymmetricMixedNash_normRpowCost
    husers_nonnegative husers_nonzero hcompact hνcont hνperturb hβ

/--
Every support action in a source symmetric mixed Nash law supplies the
source-action-space no-profitable-deviation bound at its own pure payoff.
-/
theorem paper_source_symmetric_mixed_nash_no_profitable_nonnegative_deviation_of_mem_support
    {D N P : ℕ} {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} {j : Fin P} {p0 : Content D}
    (hnash : paper_source_symmetric_mixed_nash P users cost μ)
    (hp0 : p0 ∈ μ.support) :
    paper_source_symmetric_mixed_no_profitable_nonnegative_deviation
      users cost j μ
      (SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j) cost p0 μ) :=
  sourceSymmetricMixedNash_noProfitableNonnegativeDeviation_of_mem_support hnash hp0

/--
Source symmetric mixed Nash makes every support action payoff almost surely
equal to that of any fixed support action. This uses the topological support's
full-measure property, not an unproved payoff-continuity claim.
-/
theorem paper_ae_source_mixed_pure_payoff_eq_of_source_symmetric_mixed_nash
    {D N P : ℕ} {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} {j : Fin P} {p0 : Content D}
    (hnash : paper_source_symmetric_mixed_nash P users cost μ)
    (hp0 : p0 ∈ μ.support) :
    ∀ᵐ p ∂μ,
      SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) cost p μ =
        SourceMixedPurePayoff
          (ExpectedUsersWonAgainstSymmetricMixed users j) cost p0 μ :=
  ae_sourceMixedPurePayoff_eq_of_sourceSymmetricMixedNash_of_mem_support hnash hp0

/--
Source mixed Nash itself forces every nonzero user's score law to be tie-null.
This is strictly stronger than content-law atomlessness: it rules out a
positive-mass score fiber even when that fiber contains no content point mass.
-/
theorem paper_source_symmetric_mixed_nash_score_level_measure_eq_zero
    {D N P : ℕ} [Nontrivial (Fin P)] {users : Fin N → Content D}
    {cost : Content D → ℝ} {μ : MixedContentStrategy D} {i0 : Fin N} {j : Fin P}
    (hnash : paper_source_symmetric_mixed_nash P users cost μ)
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0))
    (hcont : PerturbationCostContinuous cost)
    (z : ℝ) :
    μ {q : Content D | score (users i0) q = z} = 0 :=
  sourceSymmetricMixedNash_score_level_measure_eq_zero
    (j := j) hnash husers_nonnegative hzero hcont z

/--
Corrected Proposition `zeroutilitysinglegenre` payoff endpoint.  If a source
mixed-Nash law has zero in support and every user score law is tie-null, then
nonnegative users imply that every support action earns zero actual
uniform-tie payoff, provided the zero action has zero cost.  A single-genre
argument must prove those exposed support and score-law premises separately.
-/
theorem paper_proposition_zeroutilitysinglegenre_source_nash_support_payoff_zero_of_zero_support
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} {j : Fin P} {p : Content D}
    (hnash : paper_source_symmetric_mixed_nash P users cost μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hmeas_score : ∀ i : Fin N,
      Measurable (fun q : Content D => score (users i) q))
    (hno_atom : ∀ (i : Fin N) (z : ℝ),
      μ {q : Content D | score (users i) q = z} = 0)
    (hcost_zero : cost (0 : Content D) = 0)
    (hp : p ∈ μ.support) :
    paper_source_mixed_pure_payoff
      (paper_expected_users_won_against_symmetric_mixed users j) cost p μ = 0 :=
  sourceSymmetricMixedNash_supportPayoff_eq_zero_of_zero_mem_support
    hnash hzero husers hmeas_score hno_atom hcost_zero hp

/--
Corrected Proposition `zeroutilitysinglegenre` endpoint with tie-nullness
derived from source mixed Nash rather than assumed.  The additional explicit
premise is precisely that each user direction is nonzero, so the profitable
score-level perturbation is available.
-/
theorem paper_proposition_zeroutilitysinglegenre_source_nash_support_payoff_zero_of_zero_support_of_nonzero_users
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} {j : Fin P} {p : Content D}
    (hnash : paper_source_symmetric_mixed_nash P users cost μ)
    (hzero_support : (0 : Content D) ∈ μ.support)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hcont : PerturbationCostContinuous cost)
    (hcost_zero : cost (0 : Content D) = 0)
    (hp : p ∈ μ.support) :
    paper_source_mixed_pure_payoff
      (paper_expected_users_won_against_symmetric_mixed users j) cost p μ = 0 :=
  sourceSymmetricMixedNash_supportPayoff_eq_zero_of_zero_mem_support_of_nonzero_users
    hnash hzero_support husers husers_nonzero hcont hcost_zero hp

/--
Corrected single-genre support-radius equation. At every support action of an
atomless source equilibrium with zero in support, the scalar norm lower-CDF
mass exactly pays for the norm-power cost. Extending this equation over gaps
to obtain the source's closed CDF remains a separate obligation.
-/
theorem paper_proposition_singlegenre_support_norm_cdf_payoff_equation
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {p genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hmeas_norm : Measurable ν.norm)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β)
    (hp : p ∈ μ.support) :
    (∑ i : Fin N,
      ((Measure.map ν.norm μ).real (Set.Iic (ν.norm p))) ^ (P - 1)) =
        (ν.norm p) ^ β :=
  sourceSymmetricMixedNash_support_normCdf_payoff_equation_of_singleton_nonzeroSupportGenres
    (j := j) hnash hzero hno_atoms hgenres hgenre_score hmeas_norm husers hβ hp

/--
The scalar form of the corrected single-genre support-radius equation: the
common norm lower-CDF term appears once for each user. This is an equation at
support radii, not yet the source's all-radii closed CDF.
-/
theorem paper_proposition_singlegenre_support_norm_cdf_power_equation
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {p genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hmeas_norm : Measurable ν.norm)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β)
    (hp : p ∈ μ.support) :
    (N : ℝ) * ((Measure.map ν.norm μ).real (Set.Iic (ν.norm p))) ^ (P - 1) =
      (ν.norm p) ^ β :=
  sourceSymmetricMixedNash_support_normCdf_power_equation_of_singleton_nonzeroSupportGenres
    (j := j) hnash hzero hno_atoms hgenres hgenre_score hmeas_norm husers hβ hp

/--
Corrected single-genre support cap: every represented support action has norm
at most `N^(1 / beta)`. It follows from the scalar payoff equation and the
probability bound on the norm CDF, without an assumed compact-support law.
-/
theorem paper_proposition_singlegenre_support_norm_le_support_cap
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {p genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hmeas_norm : Measurable ν.norm)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β)
    (hp : p ∈ μ.support) :
    ν.norm p ≤ (N : ℝ) ^ β⁻¹ :=
  sourceSymmetricMixedNash_support_norm_le_supportCap_of_singleton_nonzeroSupportGenres
    (j := j) hnash hzero hno_atoms hgenres hgenre_score hmeas_norm husers hβ hp

/--
Concrete finite-`L2` compactness repair for the source CDF proof: the corrected
singleton-genre equilibrium support is compact once its payoff-derived radius
cap is combined with the continuity/finite-dimensional structure of `L2`.
-/
theorem paper_proposition_singlegenre_l2_support_compact
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : MixedContentStrategy D} {j : Fin P} {genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users
      (normRpowCost (SourceNorm.l2 D) β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres (SourceNorm.l2 D) μ ⊆
      ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β) :
    IsCompact μ.support :=
  sourceSymmetricMixedNash_isCompact_support_l2_of_singleton_nonzeroSupportGenres
    (j := j) hnash hzero hno_atoms hgenres hgenre_score husers hβ

/--
The continuous finite-`L2` source-radius image of the corrected singleton
genre support is compact.  This is a concrete endpoint, not an assertion for
an arbitrary merely measurable `SourceNorm`.
-/
theorem paper_proposition_singlegenre_l2_radius_image_compact
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : MixedContentStrategy D} {j : Fin P} {genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users
      (normRpowCost (SourceNorm.l2 D) β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres (SourceNorm.l2 D) μ ⊆
      ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β) :
    IsCompact ((SourceNorm.l2 D).norm '' μ.support) :=
  sourceSymmetricMixedNash_isCompact_l2Radius_support_image_of_singleton_nonzeroSupportGenres
    (j := j) hnash hzero hno_atoms hgenres hgenre_score husers hβ

/--
The concrete finite-`L2` radius image is preconnected: every radius between
two represented radii is represented.  Compactness converts the checked
strict-intermediate-radius result into this interval conclusion.
-/
theorem paper_proposition_singlegenre_l2_radius_image_preconnected
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : MixedContentStrategy D} {j : Fin P} {genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users
      (normRpowCost (SourceNorm.l2 D) β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres (SourceNorm.l2 D) μ ⊆
      ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β) :
    IsPreconnected ((SourceNorm.l2 D).norm '' μ.support) :=
  sourceSymmetricMixedNash_isPreconnected_l2Radius_support_image_of_singleton_nonzeroSupportGenres
    (j := j) hnash hzero hno_atoms hgenres hgenre_score husers hβ

/--
Concrete source-Nash CDF topology endpoint: the finite-`L2` support radii fill
the full interval `[0, N^(1 / beta)]`.  Its hypotheses are explicit; this is
not a claim for an arbitrary measurable source norm.
-/
theorem paper_proposition_singlegenre_l2_radius_image_eq_support_interval
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : MixedContentStrategy D} {j : Fin P} {genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users
      (normRpowCost (SourceNorm.l2 D) β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres (SourceNorm.l2 D) μ ⊆
      ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β) :
    (SourceNorm.l2 D).norm '' μ.support =
      Set.Icc 0 ((N : ℝ) ^ β⁻¹) :=
  sourceSymmetricMixedNash_l2Radius_support_image_eq_Icc_zero_supportCap_of_singleton_nonzeroSupportGenres
    (j := j) hnash hzero hno_atoms hgenres hgenre_score husers hβ

/--
Concrete finite-`L2` all-radii CDF repair.  At every nonnegative radius the
norm pushforward has the corrected clipped CDF from Lemma `cdf`.
-/
theorem paper_lemma_singlegenre_l2_norm_cdf
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : MixedContentStrategy D} {j : Fin P} {genre : Content D} {β r : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users
      (normRpowCost (SourceNorm.l2 D) β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres (SourceNorm.l2 D) μ ⊆
      ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β) (hr : 0 ≤ r) :
    AppliedModelingLib.Probability.lowerCDFMass
        (Measure.map (SourceNorm.l2 D).norm μ) r =
      paper_single_genre_cdf N P β r :=
  sourceSymmetricMixedNash_l2NormLaw_lowerCDFMass_eq_singleGenreCdf_of_singleton_nonzeroSupportGenres
    (j := j) hnash hzero hno_atoms hgenres hgenre_score husers hβ hr

/--
All-radii corrected CDF theorem for an explicitly continuous proper source
norm.  Compact radius sublevels are the source-visible replacement for the
unstated support-extremum step in the printed CDF proof.
-/
theorem paper_lemma_singlegenre_norm_cdf_of_compact_sublevels
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {genre : Content D} {β r : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hmeas_norm : Measurable ν.norm)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β)
    (hcompact_sublevels : SourceNormCompactSublevels ν)
    (hcontinuous : Continuous ν.norm)
    (hr : 0 ≤ r) :
    AppliedModelingLib.Probability.lowerCDFMass (Measure.map ν.norm μ) r =
      paper_single_genre_cdf N P β r :=
  sourceSymmetricMixedNash_normLaw_lowerCDFMass_eq_singleGenreCdf_of_compactSublevels_of_singleton_nonzeroSupportGenres
    (j := j) hnash hzero hno_atoms hgenres hgenre_score hmeas_norm husers hβ
    hcompact_sublevels hcontinuous hr

/--
Source-Nash repair for the omitted zero-support step in Lemma `cdf`: an
atomless corrected singleton-genre equilibrium has zero content in support
when its source norm is continuous with compact sublevels.  The proof uses the
minimum support radius and Nash comparison with the feasible zero action.
-/
theorem paper_lemma_singlegenre_zero_support_of_compact_sublevels
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hmeas_norm : Measurable ν.norm)
    (hβ : 0 < β)
    (hcompact_sublevels : SourceNormCompactSublevels ν)
    (hcontinuous : Continuous ν.norm) :
    (0 : Content D) ∈ μ.support :=
  sourceSymmetricMixedNash_zero_mem_support_of_compactSublevels_of_singleton_nonzeroSupportGenres
    (j := j) hnash hno_atoms hgenres hgenre_score hmeas_norm hβ hcompact_sublevels hcontinuous

/--
Finite-`L2` specialization of the source-Nash minimum-radius zero-support
repair.  Its continuity and compact-sublevel hypotheses are discharged by the
finite-dimensional norm library.
-/
theorem paper_lemma_singlegenre_l2_zero_support
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : MixedContentStrategy D} {j : Fin P} {genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users
      (normRpowCost (SourceNorm.l2 D) β) μ)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres (SourceNorm.l2 D) μ ⊆
      ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hβ : 0 < β) :
    (0 : Content D) ∈ μ.support :=
  paper_lemma_singlegenre_zero_support_of_compact_sublevels
    (j := j) hnash hno_atoms hgenres hgenre_score (SourceNorm.l2_measurable D) hβ
    (SourceNorm.l2_compactSublevels D) (SourceNorm.l2_continuous D)

/--
Corrected all-radii CDF theorem with the source's zero-support premise derived
from Nash rather than supplied by the caller.  Continuous compact source-norm
sublevels make the support compact; atomlessness and the corrected ray
geometry then force its minimum radius to be zero.
-/
theorem paper_lemma_singlegenre_norm_cdf_of_compact_sublevels_without_zero_support_premise
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {genre : Content D} {β r : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hmeas_norm : Measurable ν.norm)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β)
    (hcompact_sublevels : SourceNormCompactSublevels ν)
    (hcontinuous : Continuous ν.norm)
    (hr : 0 ≤ r) :
    AppliedModelingLib.Probability.lowerCDFMass (Measure.map ν.norm μ) r =
      paper_single_genre_cdf N P β r :=
  sourceSymmetricMixedNash_normLaw_lowerCDFMass_eq_singleGenreCdf_of_compactSublevels_of_singleton_nonzeroSupportGenres_without_zeroSupportPremise
    (j := j) hnash hno_atoms hgenres hgenre_score hmeas_norm husers hβ
    hcompact_sublevels hcontinuous hr

/--
Positive finite-coordinate `Lq` specialization of the all-radii corrected CDF
theorem.  Its continuity and compact-sublevel hypotheses are discharged by
the reusable finite-dimensional norm library.
-/
theorem paper_lemma_singlegenre_lp_norm_cdf
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {q : ℝ} (hq : 0 < q)
    {users : Fin N → Content D}
    {μ : MixedContentStrategy D} {j : Fin P} {genre : Content D} {β r : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users
      (normRpowCost (SourceNorm.lp D hq) β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres (SourceNorm.lp D hq) μ ⊆
      ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β) (hr : 0 ≤ r) :
    AppliedModelingLib.Probability.lowerCDFMass
        (Measure.map (SourceNorm.lp D hq).norm μ) r =
      paper_single_genre_cdf N P β r :=
  paper_lemma_singlegenre_norm_cdf_of_compact_sublevels
    (j := j) hnash hzero hno_atoms hgenres hgenre_score (SourceNorm.lp_measurable hq)
    husers hβ (SourceNorm.lp_compactSublevels hq) (SourceNorm.lp_continuous hq) hr

/--
Corrected zero-utility source-Nash endpoint for a continuous proper source
norm, with the topology and compactness assumptions stated explicitly.
-/
theorem paper_proposition_zeroutilitysinglegenre_source_nash_of_compact_sublevels
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {p genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hmeas_norm : Measurable ν.norm)
    (hzero_detect : SourceNormZeroReflectsNeighborhood ν)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β)
    (hcompact_sublevels : SourceNormCompactSublevels ν)
    (hcontinuous : Continuous ν.norm)
    (hp : p ∈ μ.support) :
    paper_source_mixed_pure_payoff
      (paper_expected_users_won_against_symmetric_mixed users j)
      (normRpowCost ν β) p μ = 0 :=
  sourceSymmetricMixedNash_supportPayoff_eq_zero_of_compactSublevels_of_singleton_nonzeroSupportGenres
    hnash hzero hno_atoms hgenres hgenre_score hmeas_norm hzero_detect husers
    hβ hcompact_sublevels hcontinuous hp

/--
Corrected zero-utility endpoint with no unproved zero-support input.  The
minimum-radius Nash argument proves zero support from the remaining explicit
source-model, atomlessness, ray-geometry, and proper-continuous-norm premises.
-/
theorem paper_proposition_zeroutilitysinglegenre_source_nash_of_compact_sublevels_without_zero_support_premise
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {p genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hmeas_norm : Measurable ν.norm)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β)
    (hcompact_sublevels : SourceNormCompactSublevels ν)
    (hcontinuous : Continuous ν.norm)
    (hp : p ∈ μ.support) :
    paper_source_mixed_pure_payoff
      (paper_expected_users_won_against_symmetric_mixed users j)
      (normRpowCost ν β) p μ = 0 :=
  sourceSymmetricMixedNash_supportPayoff_eq_zero_of_compactSublevels_of_singleton_nonzeroSupportGenres_without_zeroSupportPremise
    hnash hno_atoms hgenres hgenre_score hmeas_norm husers hβ
    hcompact_sublevels hcontinuous hp

/--
Concrete finite-`L2` corrected zero-utility endpoint: every fixed support
action has zero actual uniform-tie payoff once the visible CDF, zero-support,
and singleton nonzero-genre premises are supplied.
-/
theorem paper_proposition_zeroutilitysinglegenre_l2_source_nash
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D}
    {μ : MixedContentStrategy D} {j : Fin P} {p genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users
      (normRpowCost (SourceNorm.l2 D) β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres (SourceNorm.l2 D) μ ⊆
      ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β)
    (hp : p ∈ μ.support) :
    paper_source_mixed_pure_payoff
      (paper_expected_users_won_against_symmetric_mixed users j)
      (normRpowCost (SourceNorm.l2 D) β) p μ = 0 :=
  sourceSymmetricMixedNash_l2_supportPayoff_eq_zero_of_singleton_nonzeroSupportGenres
    hnash hzero hno_atoms hgenres hgenre_score husers hβ hp

/--
Corrected no-gap component: two distinct norm radii represented in support
must have positive scalar norm-law mass between them. This does not by itself
provide the endpoint compactness needed for the source's full CDF statement.
-/
theorem paper_proposition_singlegenre_interval_norm_mass_pos_between_support_radii
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {p q genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hmeas_norm : Measurable ν.norm)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β)
    (hp : p ∈ μ.support) (hq : q ∈ μ.support)
    (hpq : ν.norm p < ν.norm q) :
    0 < AppliedModelingLib.Probability.intervalOCMass (Measure.map ν.norm μ)
      (ν.norm p) (ν.norm q) :=
  sourceSymmetricMixedNash_intervalOCMass_normLaw_pos_between_support_radii
    (j := j) hnash hzero hno_atoms hgenres hgenre_score hmeas_norm husers hβ hp hq hpq

/--
Corrected no-gap conclusion: between any two distinct represented support
radii lies another represented support radius. This avoids treating the support
of a merely measurable norm pushforward as an unproved image of content
support.
-/
theorem paper_proposition_singlegenre_exists_support_radius_between
    {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {p q genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hzero : (0 : Content D) ∈ μ.support)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hmeas_norm : Measurable ν.norm)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hβ : 0 < β)
    (hp : p ∈ μ.support) (hq : q ∈ μ.support)
    (hpq : ν.norm p < ν.norm q) :
    ∃ r : Content D, r ∈ μ.support ∧
      ν.norm p < ν.norm r ∧ ν.norm r < ν.norm q :=
  sourceSymmetricMixedNash_exists_support_radius_between_of_singleton_nonzeroSupportGenres
    (j := j) hnash hzero hno_atoms hgenres hgenre_score hmeas_norm husers hβ hp hq hpq

/--
Corrected Proposition `zeroutilitysinglegenre` composition.  The exact norm
CDF, atomlessness, and corrected singleton nonzero-genre condition give zero
content support and tie-null score laws, so every support action has zero
actual uniform-tie payoff.  The displayed source proof does not establish
these bridge premises by itself.
-/
theorem paper_proposition_zeroutilitysinglegenre_source_nash_support_payoff_zero_of_cdf
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D} {μ : MixedContentStrategy D}
    {j : Fin P} {p genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hno_atoms : MeasureTheory.NoAtoms μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hmeas_norm : Measurable ν.norm)
    (hzero_detect : SourceNormZeroReflectsNeighborhood ν)
    (hβ : 0 < β)
    (hcdf : ∀ r : ℝ, 0 ≤ r →
      AppliedModelingLib.Probability.lowerCDFMass (MeasureTheory.Measure.map ν.norm μ) r =
        paper_single_genre_cdf N P β r)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hp : p ∈ μ.support) :
    paper_source_mixed_pure_payoff
      (paper_expected_users_won_against_symmetric_mixed users j)
      (normRpowCost ν β) p μ = 0 :=
  sourceSymmetricMixedNash_supportPayoff_eq_zero_of_singleton_nonzeroSupportGenres_and_Cdf
    hnash hno_atoms hgenres hgenre_score hmeas_norm hzero_detect hβ hcdf husers hp

/--
Corrected source-Nash realization of Proposition `zeroutilitysinglegenre`.
The paper's atom argument provides content atomlessness once a nonzero user and
norm perturbation continuity are explicit; the corrected singleton-genre and
all-radii norm-CDF bridges then yield zero actual payoff at every support
action.  This retains all source conditions that the printed three-line proof
leaves implicit.
-/
theorem paper_proposition_zeroutilitysinglegenre_source_nash_support_payoff_zero_of_cdf_and_atom
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D} {μ : MixedContentStrategy D}
    {j : Fin P} {p genre : Content D} {β : ℝ} {i0 : Fin N}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hperturb : SourceNormPerturbationContinuous ν)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hi0_nonzero : NonzeroContent (users i0))
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (hgenre_score : ∀ i : Fin N,
      0 < paper_inferred_user_value (users i) genre)
    (hmeas_norm : Measurable ν.norm)
    (hzero_detect : SourceNormZeroReflectsNeighborhood ν)
    (hβ : 0 < β)
    (hcdf : ∀ r : ℝ, 0 ≤ r →
      AppliedModelingLib.Probability.lowerCDFMass (MeasureTheory.Measure.map ν.norm μ) r =
        paper_single_genre_cdf N P β r)
    (hp : p ∈ μ.support) :
    paper_source_mixed_pure_payoff
      (paper_expected_users_won_against_symmetric_mixed users j)
      (normRpowCost ν β) p μ = 0 :=
  sourceSymmetricMixedNash_supportPayoff_eq_zero_of_singleton_nonzeroSupportGenres_Cdf_and_atom
    hnash hperturb husers hi0_nonzero hgenres hgenre_score hmeas_norm
    hzero_detect hβ hcdf hp

/--
Proposition `utility`, source-action-space final step: a profitable
nonnegative pure deviation forces strictly positive payoff at every fixed
support action of a symmetric mixed Nash law.
-/
theorem paper_source_symmetric_mixed_nash_support_payoff_pos_of_profitable_nonnegative_deviation
    {D N P : ℕ} {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} {j : Fin P} {p0 : Content D}
    (hnash : paper_source_symmetric_mixed_nash P users cost μ)
    (hp0 : p0 ∈ μ.support)
    (hdev : ∃ p : Content D, NonnegativeContent p ∧
      0 < SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j) cost p μ) :
    0 < SourceMixedPurePayoff
      (ExpectedUsersWonAgainstSymmetricMixed users j) cost p0 μ :=
  sourceSymmetricMixedNash_supportPayoff_pos_of_profitableNonnegativeDeviation
    hnash hp0 hdev

/--
Proposition `utility`, source-level normalized-Euclidean endpoint. Under the
paper's nonnegative/nonzero user model and positive-profit geometry condition,
every source-Nash support action has strictly positive payoff.  The proof keeps
the producer deviation domain nonnegative throughout.
-/
theorem paper_proposition_utility_source_symmetric_mixed_nash_support_payoff_pos
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {j : Fin P}
    {μ : MixedContentStrategy D} {p0 : Content D}
    {β Q : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users
      (normRpowCost (SourceNorm.l2 D) β) μ)
    (hp0 : p0 ∈ μ.support)
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hQupper :
      SourceUnitDirectionQUpperBound
        (l2NormalizedUsers users) (SourceNorm.l2 D) Q)
    (hβ : 0 < β) (hQ_nonneg : 0 ≤ Q)
    (hQ : Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β)) :
    0 < SourceMixedPurePayoff
      (ExpectedUsersWonAgainstSymmetricMixed users j)
      (normRpowCost (SourceNorm.l2 D) β) p0 μ :=
  sourceSymmetricMixedNash_supportPayoff_pos_of_positive_profit_condition_l2_normalized_users
    hnash hp0 husers_nonnegative husers_nonzero hQupper hβ hQ_nonneg hQ

/--
Tie-aware replacement for Lemma `necessarysuff`'s reparameterized objective:
the strict-score mass from the actual candidate law, raised to the number of
opponents, minus production cost.
-/
noncomputable abbrev paper_necessarysuff_tie_aware_objective {D N P : ℕ}
    (users : Fin N → Content D) (μ : MixedContentStrategy D)
    (cost : Content D → ℝ) (p : Content D) : ℝ :=
  strictScoreMassReparamObjective (P := P) users μ cost p

/--
The source C1 value-space objective, with an explicitly supplied induced cost.
The source's informal fibre minimum can be used here only after its existence
and minimum-cost-representative properties have been separately proved.
-/
noncomputable abbrev paper_necessarysuff_value_space_objective {N : ℕ}
    (H : Fin N → ℝ → ℝ) (inducedCost : (Fin N → ℝ) → ℝ)
    (z : Fin N → ℝ) : ℝ :=
  valueSpaceReparamObjective H inducedCost z

/--
Corrected value-space sufficient direction for Lemma `necessarysuff`.

This source-shaped C1/C2/C3 bridge is sound for the actual uniform-tie game
when score levels are null, `H` is the resulting strict-score-mass power,
every support value lies in `S`, and the supplied induced cost lower-bounds all
realizing actions while being attained at support actions.  Thus it records
the fibre-minimum facts that the source proof uses but does not state.
-/
theorem paper_necessarysuff_tie_aware_value_space_sufficient
    {D N P : ℕ} {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {H : Fin N → ℝ → ℝ} {inducedCost : (Fin N → ℝ) → ℝ}
    {S : Set (Fin N → ℝ)}
    (hsupport : μ.support ⊆ {p : Content D | NonnegativeContent p})
    (hmeas_score : ∀ i : Fin N,
      Measurable (fun q : Content D => score (users i) q))
    (hno_atom : ∀ (i : Fin N) (z : ℝ),
      μ {q : Content D | score (users i) q = z} = 0)
    (hC2 : ∀ (i : Fin N) (z : ℝ),
      H i z = (μ.real {q : Content D | score (users i) q < z}) ^ (P - 1))
    (hC3_support : ∀ p : Content D, p ∈ μ.support → userValueMap users p ∈ S)
    (hC1 : ∀ z : Fin N → ℝ, z ∈ S → ∀ q : Content D,
      NonnegativeContent q →
        paper_necessarysuff_value_space_objective H inducedCost
          (userValueMap users q) ≤
          paper_necessarysuff_value_space_objective H inducedCost z)
    (hinduced_le_cost : ∀ q : Content D, NonnegativeContent q →
      inducedCost (userValueMap users q) ≤ cost q)
    (hsupport_cost : ∀ p : Content D, p ∈ μ.support →
      inducedCost (userValueMap users p) = cost p) :
    paper_source_symmetric_mixed_nash P users cost μ :=
  sourceSymmetricMixedNash_of_valueSpaceCertificate_strictScoreMass
    hsupport hmeas_score hno_atom hC2 hC3_support hC1 hinduced_le_cost
    hsupport_cost

/--
The mapped-law specialization of the corrected value-space certificate. Its C1
premise is over the topological support of the actual score-vector pushforward;
continuity proves the C3 support transport internally.
-/
theorem paper_necessarysuff_tie_aware_mapped_value_support_sufficient
    {D N P : ℕ} {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {H : Fin N → ℝ → ℝ} {inducedCost : (Fin N → ℝ) → ℝ}
    (hsupport : μ.support ⊆ {p : Content D | NonnegativeContent p})
    (hmeas_score : ∀ i : Fin N,
      Measurable (fun q : Content D => score (users i) q))
    (hno_atom : ∀ (i : Fin N) (z : ℝ),
      μ {q : Content D | score (users i) q = z} = 0)
    (hC2 : ∀ (i : Fin N) (z : ℝ),
      H i z = (μ.real {q : Content D | score (users i) q < z}) ^ (P - 1))
    (hC1 : ∀ z : Fin N → ℝ,
      z ∈ (MeasureTheory.Measure.map (userValueMap users) μ).support →
      ∀ q : Content D, NonnegativeContent q →
        paper_necessarysuff_value_space_objective H inducedCost
          (userValueMap users q) ≤
          paper_necessarysuff_value_space_objective H inducedCost z)
    (hinduced_le_cost : ∀ q : Content D, NonnegativeContent q →
      inducedCost (userValueMap users q) ≤ cost q)
    (hsupport_cost : ∀ p : Content D, p ∈ μ.support →
      inducedCost (userValueMap users p) = cost p) :
    paper_source_symmetric_mixed_nash P users cost μ :=
  sourceSymmetricMixedNash_of_mappedValueSupportCertificate_strictScoreMass
    hsupport hmeas_score hno_atom hC2 hC1 hinduced_le_cost hsupport_cost

/--
Corrected necessary C1 direction for Lemma `necessarysuff`'s value-space
formulation.  The source's fibrewise `min` needs an actual nonnegative
minimizer for every feasible realized value, and a declared value-support
point needs a source support-action preimage.  With these conditions and
tie-null score laws, a source symmetric mixed Nash law proves C1.
-/
theorem paper_necessarysuff_tie_aware_value_space_necessary
    {D N P : ℕ} [Nonempty (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} {H : Fin N → ℝ → ℝ}
    {inducedCost : (Fin N → ℝ) → ℝ} {S : Set (Fin N → ℝ)}
    (hnash : paper_source_symmetric_mixed_nash P users cost μ)
    (hmeas_score : ∀ i : Fin N,
      Measurable (fun q : Content D => score (users i) q))
    (hno_atom : ∀ (i : Fin N) (z : ℝ),
      μ {q : Content D | score (users i) q = z} = 0)
    (hC2 : ∀ (i : Fin N) (z : ℝ),
      H i z = (μ.real {q : Content D | score (users i) q < z}) ^ (P - 1))
    (hsupport_realizes : ∀ z : Fin N → ℝ, z ∈ S →
      ∃ p : Content D, p ∈ μ.support ∧ userValueMap users p = z)
    (hinduced_attained : ∀ q : Content D, NonnegativeContent q →
      ∃ qmin : Content D, NonnegativeContent qmin ∧
        userValueMap users qmin = userValueMap users q ∧
        cost qmin = inducedCost (userValueMap users q))
    (hsupport_cost : ∀ p : Content D, p ∈ μ.support →
      inducedCost (userValueMap users p) = cost p) :
    ∀ z : Fin N → ℝ, z ∈ S → ∀ q : Content D,
      NonnegativeContent q →
        paper_necessarysuff_value_space_objective H inducedCost
          (userValueMap users q) ≤
          paper_necessarysuff_value_space_objective H inducedCost z :=
  valueSpaceC1_of_sourceSymmetricMixedNash_strictScoreMass
    hnash hmeas_score hno_atom hC2 hsupport_realizes hinduced_attained hsupport_cost

/--
Corrected value-space iff for Lemma `necessarysuff`.  It keeps the C1/C2/C3
shape while making explicit the score-level-null condition, both directions
of the value-support realization bridge, and the lower-bound/attainment
properties of the induced fibre cost.  The literal printed C1--C3 iff omits
these mathematical requirements.
-/
theorem paper_necessarysuff_tie_aware_value_space_iff
    {D N P : ℕ} [Nonempty (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    {H : Fin N → ℝ → ℝ} {inducedCost : (Fin N → ℝ) → ℝ}
    {S : Set (Fin N → ℝ)}
    (hmeas_score : ∀ i : Fin N,
      Measurable (fun q : Content D => score (users i) q))
    (hno_atom : ∀ (i : Fin N) (z : ℝ),
      μ {q : Content D | score (users i) q = z} = 0)
    (hC2 : ∀ (i : Fin N) (z : ℝ),
      H i z = (μ.real {q : Content D | score (users i) q < z}) ^ (P - 1))
    (hC3_support : ∀ p : Content D, p ∈ μ.support → userValueMap users p ∈ S)
    (hsupport_realizes : ∀ z : Fin N → ℝ, z ∈ S →
      ∃ p : Content D, p ∈ μ.support ∧ userValueMap users p = z)
    (hinduced_le_cost : ∀ q : Content D, NonnegativeContent q →
      inducedCost (userValueMap users q) ≤ cost q)
    (hinduced_attained : ∀ q : Content D, NonnegativeContent q →
      ∃ qmin : Content D, NonnegativeContent qmin ∧
        userValueMap users qmin = userValueMap users q ∧
        cost qmin = inducedCost (userValueMap users q))
    (hsupport_cost : ∀ p : Content D, p ∈ μ.support →
      inducedCost (userValueMap users p) = cost p) :
    paper_source_symmetric_mixed_nash P users cost μ ↔
      μ.support ⊆ {p : Content D | NonnegativeContent p} ∧
      (∀ z : Fin N → ℝ, z ∈ S → ∀ q : Content D,
        NonnegativeContent q →
          paper_necessarysuff_value_space_objective H inducedCost
            (userValueMap users q) ≤
            paper_necessarysuff_value_space_objective H inducedCost z) :=
  sourceSymmetricMixedNash_iff_valueSpaceCertificate_strictScoreMass
    hmeas_score hno_atom hC2 hC3_support hsupport_realizes hinduced_le_cost
    hinduced_attained hsupport_cost

/--
Corrected sufficient direction of Lemma `necessarysuff`.  The visible C1-like
support-maximizer condition is imposed on the actual strict-score objective,
and score-level nullness is explicit.  These hypotheses prove a symmetric
mixed Nash equilibrium for uniform tie-breaking; the source's printed C1--C3
statement omits the null-tie condition and is not used as though it implied
this theorem.
-/
theorem paper_necessarysuff_tie_aware_sufficient
    {D N P : ℕ} {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    (hsupport : μ.support ⊆ {p : Content D | NonnegativeContent p})
    (hmeas_score : ∀ i : Fin N,
      Measurable (fun q : Content D => score (users i) q))
    (hno_atom : ∀ (i : Fin N) (z : ℝ),
      μ {q : Content D | score (users i) q = z} = 0)
    (hC1 : ∀ p : Content D, p ∈ μ.support → ∀ q : Content D,
      NonnegativeContent q →
        paper_necessarysuff_tie_aware_objective (P := P) users μ cost q ≤
          paper_necessarysuff_tie_aware_objective (P := P) users μ cost p) :
    paper_source_symmetric_mixed_nash P users cost μ :=
  sourceSymmetricMixedNash_of_supportMaximizer_strictScoreMass
    hsupport hmeas_score hno_atom hC1

/--
Corrected content-level necessary-and-sufficient form of Lemma
`necessarysuff`.  With a nonempty producer population and score-level
nullness, the formal uniform-tie symmetric Nash definition is equivalent to
nonnegative support and the displayed strict-score objective being maximized
by every support action.  This is intentionally a content-action theorem: the
source's additional C2/C3 value-law packaging can be related to it only after
its exact score-law identities have been established.
-/
theorem paper_necessarysuff_tie_aware_iff
    {D N P : ℕ} [Nonempty (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} [MeasureTheory.IsProbabilityMeasure μ]
    (hmeas_score : ∀ i : Fin N,
      Measurable (fun q : Content D => score (users i) q))
    (hno_atom : ∀ (i : Fin N) (z : ℝ),
      μ {q : Content D | score (users i) q = z} = 0) :
    paper_source_symmetric_mixed_nash P users cost μ ↔
      μ.support ⊆ {p : Content D | NonnegativeContent p} ∧
      (∀ (j : Fin P) (p : Content D), p ∈ μ.support → ∀ q : Content D,
        NonnegativeContent q →
          paper_necessarysuff_tie_aware_objective (P := P) users μ cost q ≤
            paper_necessarysuff_tie_aware_objective (P := P) users μ cost p) :=
  sourceSymmetricMixedNash_iff_supportMaximizer_strictScoreMass
    hmeas_score hno_atom

/--
Proposition `Ptwo`: the explicit nonnegative quarter-circle content law is a
symmetric mixed Nash equilibrium for the two standard-basis users whenever
`beta >= 2`.
-/
theorem paper_proposition_Ptwo_source_symmetric_mixed_nash
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    paper_source_symmetric_mixed_nash 2 pTwoStandardBasisUsers
      (normRpowCost (SourceNorm.l2 2) beta) (pTwoSourceContentMeasure beta) :=
  pTwoSourceContentMeasure_is_sourceSymmetricMixedNash hbeta

/--
Proposition `finiteP`: for every finite producer count `P >= 2`, the literal
source-curve content law is a symmetric mixed Nash equilibrium at `beta = 2`.
The proof uses the construction's tie-aware product-integral payoff directly,
not the source's generic C1--C3 lemma.
-/
theorem paper_proposition_finiteP_source_symmetric_mixed_nash
    {P : ℕ} (hP : 2 ≤ P) :
    paper_source_symmetric_mixed_nash P pTwoStandardBasisUsers
      (normRpowCost (SourceNorm.l2 2) 2) (finitePSourceContentMeasure P) :=
  finitePSourceContentMeasure_is_sourceSymmetricMixedNash hP

/--
Corrected single-genre nonvacuity bridge.  With the paper's stated nonzero
users, source Nash excludes an all-zero support: it would put score mass one
at zero for every user, contrary to the source-Nash perturbation argument.
-/
theorem paper_lemma_singlegenre_exists_nonzero_support_of_nonzero_users
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D}
    (hnash : paper_source_symmetric_mixed_nash P users cost μ)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hcont : PerturbationCostContinuous cost) :
    ∃ p : Content D, p ∈ μ.support ∧ NonzeroContent p :=
  sourceSymmetricMixedNash_exists_nonzero_support_of_nonzero_users
    hnash husers husers_nonzero hcont

/--
Corrected replacement for the source's invalid span parenthetical in Lemma
`nonzero`: a singleton nonzero-support genre has strictly positive score for
every nonzero nonnegative user.  The proof uses score-level atom exclusion,
not any implication from linear-span membership.
-/
theorem paper_lemma_singlegenre_genre_scores_positive_of_nonzero_users
    {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} {genre : Content D}
    (hnash : paper_source_symmetric_mixed_nash P users cost μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hcont : PerturbationCostContinuous cost) :
    ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre :=
  sourceSymmetricMixedNash_genre_score_pos_of_singleton_nonzeroSupportGenres_of_nonzero_users
    hnash hgenres husers husers_nonzero hcont

/--
Corrected full form of Theorem `singlegenre`.  For the paper's nonzero-user
finite-dimensional regime, a source symmetric mixed equilibrium with one
nonzero-support genre exists exactly when the powered score image and its
convex hull have the same coordinate-product supremum.

The source's literal `Genre(mu)` expression normalizes zero even though the
ray equilibrium has zero in topological support; this theorem therefore uses
the zero-safe `paper_nonzero_support_genres`.  The compactness, continuity,
and perturbation premises make explicit the finite-norm properties required by
the source CDF and atom arguments.
-/
theorem paper_theorem_singlegenre_corrected_compact_source_iff
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} (ν : SourceNorm D) {β : ℝ}
    (hβ : 0 < β) (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hperturb : SourceNormPerturbationContinuous ν)
    (hcompact_sublevels : SourceNormCompactSublevels ν)
    (hcontinuous : Continuous ν.norm) :
    (∃ (μ : MixedContentStrategy D) (genre : Content D),
      paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ ∧
      paper_nonzero_support_genres ν μ = ({genre} : Set (Content D))) ↔
      SingleGenreProductSupCondition
        {y : Fin N → ℝ | paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y} :=
  exists_sourceSymmetricMixedNash_singleton_nonzeroSupportGenre_iff_productSupCondition_of_compactSublevels
    ν hβ husers husers_nonzero hperturb hcompact_sublevels hcontinuous

/--
Corrected equilibrium form of Corollary `2users`.  In the finite
equal-population model with at least one producer, a symmetric mixed
equilibrium supported on one nonzero genre exists exactly when the two-user
phase threshold holds.  This combines the full nonnegative Euclidean
source-ball optimization theorem with the corrected compact-source theorem
`singlegenre`.

The source's literal support notation is zero-unsafe, so the conclusion uses
`paper_nonzero_support_genres`; both nonzero user-vector premises are also
made explicit.  No unit-norm convention on user embeddings is assumed.
-/
theorem paper_corollary_twousers_corrected_single_genre_equilibrium_iff_phase_threshold
    {D K P : ℕ} [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin 2 → Content D} {β θ : ℝ}
    (hK : 0 < K)
    (husers_nonnegative : ∀ i, NonnegativeContent (users i))
    (hfirst_nonzero : NonzeroContent (users 0))
    (hsecond_nonzero : NonzeroContent (users 1))
    (hangle : paper_inferred_user_value (users 0) (users 1) /
      (AppliedModelingLib.FiniteDimensionalNorms.l2 (users 0) *
        AppliedModelingLib.FiniteDimensionalNorms.l2 (users 1)) = Real.cos θ)
    (hβ_one : 1 ≤ β)
    (hθ_pos : 0 < θ)
    (hθ_le_half_pi : θ ≤ Real.pi / 2) :
    (∃ (μ : MixedContentStrategy D) (genre : Content D),
      paper_source_symmetric_mixed_nash P (twoPopulationUsers K users)
        (normRpowCost (SourceNorm.l2 D) β) μ ∧
      paper_nonzero_support_genres (SourceNorm.l2 D) μ =
        ({genre} : Set (Content D))) ↔
      β ≤ twoUserPhaseThreshold θ := by
  letI : Nonempty (Fin (2 * K)) := ⟨⟨0, by omega⟩⟩
  have husers_nonzero : ∀ i : Fin 2, NonzeroContent (users i) := by
    intro i
    fin_cases i
    · exact hfirst_nonzero
    · exact hsecond_nonzero
  have hrepusers_nonnegative :
      ∀ i : Fin (2 * K), NonnegativeContent (twoPopulationUsers K users i) := by
    intro i
    exact husers_nonnegative (finProdFinEquiv.symm i).1
  have hrepusers_nonzero :
      ∀ i : Fin (2 * K), NonzeroContent (twoPopulationUsers K users i) := by
    intro i
    exact husers_nonzero (finProdFinEquiv.symm i).1
  calc
    (∃ (μ : MixedContentStrategy D) (genre : Content D),
      paper_source_symmetric_mixed_nash P (twoPopulationUsers K users)
        (normRpowCost (SourceNorm.l2 D) β) μ ∧
      paper_nonzero_support_genres (SourceNorm.l2 D) μ =
        ({genre} : Set (Content D))) ↔
        SingleGenreProductSupCondition
          {z : Fin (2 * K) → ℝ |
            paper_powered_unit_image (twoPopulationUsers K users)
              (fun p => NonnegativeContent p ∧ (SourceNorm.l2 D).norm p ≤ 1)
              β z} :=
      paper_theorem_singlegenre_corrected_compact_source_iff
        (SourceNorm.l2 D) (lt_of_lt_of_le zero_lt_one hβ_one)
        hrepusers_nonnegative hrepusers_nonzero
        SourceNorm.l2_perturbationContinuous
        (SourceNorm.l2_compactSublevels D) (SourceNorm.l2_continuous D)
    _ ↔ β ≤ twoUserPhaseThreshold θ :=
      paper_corollary_twousers_corrected_product_sup_condition_iff_phase_threshold
        hK husers_nonnegative hfirst_nonzero hsecond_nonzero hangle hβ_one
        hθ_pos hθ_le_half_pi

/--
The direct equilibrium construction used in Theorem `singlegenre`: a
nonnegative unit genre satisfying the source ratio condition over all
nonnegative unit-ball directions generates a symmetric mixed Nash ray law.

This theorem establishes the equilibrium conclusion under the formalized
uniform-tie payoff.  It deliberately does not assert the source's literal
`Genre(mu) = {genre}` display, whose treatment of the zero support point is a
separately recorded source-definition issue.
-/
theorem paper_theorem_singlegenre_concrete_ray_law_source_symmetric_mixed_nash
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {genre : Content D}
    (ν : SourceNorm D) (hβ : 0 < β)
    (hgenre_norm : ν.norm genre = 1)
    (hgenre_nonnegative : NonnegativeContent genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hscore : ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre)
    (hcondition :
      paper_single_genre_direction_condition
        {y' : Fin N → ℝ |
          paper_powered_unit_image users
            (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y'}
        (fun i => (paper_inferred_user_value (users i) genre) ^ β)) :
    paper_source_symmetric_mixed_nash P users (normRpowCost ν β)
      (singleGenreContentLaw N P β genre) :=
  singleGenreContentLaw_is_sourceSymmetricMixedNash_of_ball_directionCondition
    ν hβ hgenre_norm hgenre_nonnegative husers hscore hcondition

/--
Corrected Lemma `optsingledirection` iff for the explicit ray law: under the
displayed unit-genre, nonnegative-action, and positive-score hypotheses, the
ray law is a source symmetric mixed Nash equilibrium exactly when the source
ratio condition holds.  The proof uses a small unclipped radial deviation from
zero support for the Nash-to-condition direction, so it respects uniform ties.
-/
theorem paper_lemma_optsingledirection_concrete_ray_law_iff
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {genre : Content D}
    (ν : SourceNorm D) (hβ : 0 < β)
    (hgenre_norm : ν.norm genre = 1)
    (hgenre_nonnegative : NonnegativeContent genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hscore : ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre) :
    paper_source_symmetric_mixed_nash P users (normRpowCost ν β)
      (singleGenreContentLaw N P β genre) ↔
      paper_single_genre_direction_condition
        {y' : Fin N → ℝ | paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y'}
        (fun i => (paper_inferred_user_value (users i) genre) ^ β) :=
  singleGenreContentLaw_sourceSymmetricMixedNash_iff_ball_directionCondition
    ν hβ hgenre_norm hgenre_nonnegative husers hscore

/--
For the concrete ray law, a source symmetric mixed Nash equilibrium forces
equality of the coordinate-product suprema of the powered source image and
its convex hull.  This is the fully specified replacement for the product
condition used in the source's generic single-genre display.
-/
theorem paper_theorem_singlegenre_concrete_ray_law_product_sup_condition
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {genre : Content D}
    (ν : SourceNorm D) (hβ : 0 < β)
    (hgenre_norm : ν.norm genre = 1)
    (hgenre_nonnegative : NonnegativeContent genre)
    (husers : ∀ i, NonnegativeContent (users i))
    (hscore : ∀ i, 0 < paper_inferred_user_value (users i) genre)
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β)
      (singleGenreContentLaw N P β genre)) :
    SingleGenreProductSupCondition
      {y' : Fin N → ℝ | paper_powered_unit_image users
        (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y'} :=
  singleGenreContentLaw_productSupCondition_of_sourceSymmetricMixedNash
    ν hβ hgenre_norm hgenre_nonnegative husers hscore hnash

/--
Corrected Corollary `singlegenrestructure` welfare conclusion for the explicit
single-genre ray law.  If that law is a source symmetric mixed Nash equilibrium,
then its powered score row maximizes coordinate product over the nonnegative
source norm-ball image.  This is the zero-safe product formulation; the
equivalent logarithmic objective is only meaningful on its strictly positive
score subdomain.
-/
theorem paper_corollary_singlegenrestructure_concrete_ray_law_product_maximizer
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {genre : Content D}
    (ν : SourceNorm D) (hβ : 0 < β)
    (hgenre_norm : ν.norm genre = 1)
    (hgenre_nonnegative : NonnegativeContent genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hscore : ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre)
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β)
      (singleGenreContentLaw N P β genre)) :
    IsCoordinateProductMaximizer
      {y' : Fin N → ℝ | paper_powered_unit_image users
        (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y'}
      (fun i => (paper_inferred_user_value (users i) genre) ^ β) :=
  singleGenreContentLaw_coordinateProductMaximizer_of_sourceSymmetricMixedNash
    ν hβ hgenre_norm hgenre_nonnegative husers hscore hnash

/--
Corrected Corollary `singlegenrestructure` log-welfare conclusion for the
explicit ray law.  Its powered score row maximizes log Nash welfare over
nonnegative unit-sphere rows with strictly positive coordinates.  The positive
domain makes the source logarithms meaningful; no value is assigned to the
zero row of the larger norm ball.
-/
theorem paper_corollary_singlegenrestructure_concrete_ray_law_nash_log_maximizer
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {genre : Content D}
    (ν : SourceNorm D) (hβ : 0 < β)
    (hgenre_norm : ν.norm genre = 1)
    (hgenre_nonnegative : NonnegativeContent genre)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hscore : ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre)
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β)
      (singleGenreContentLaw N P β genre)) :
    IsMaximizerOn
      (fun z => z ∈ {y' : Fin N → ℝ |
        paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p = 1) β y'} ∧
        ∀ i, 0 < z i)
      nashLogObjective
      (fun i => (paper_inferred_user_value (users i) genre) ^ β) :=
  singleGenreContentLaw_nashLogMaximizerOn_unitSphere_of_sourceSymmetricMixedNash
    ν hβ hgenre_norm hgenre_nonnegative husers hscore hnash

/--
Corrected arbitrary-equilibrium form of Corollary `singlegenrestructure`.
Under the explicit compact source-norm package, a source symmetric mixed
equilibrium with one nonzero-support genre has a genre whose powered score row
maximizes log Nash welfare over the positive nonnegative unit-sphere image.
The conclusion uses the completed corrected compact single-genre
identification, and so does not assume an arbitrary equilibrium is already
the concrete ray law.  The source's literal zero-inclusive `Genre` notation
and its printed free-index AM--GM display remain excluded.
-/
theorem paper_corollary_singlegenrestructure_singleton_nonzero_support_nash_log_maximizer
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {genre : Content D} {β : ℝ}
    (hnash : paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ)
    (hgenres : paper_nonzero_support_genres ν μ ⊆ ({genre} : Set (Content D)))
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hperturb : SourceNormPerturbationContinuous ν)
    (hβ : 0 < β)
    (hcompact_sublevels : SourceNormCompactSublevels ν)
    (hcontinuous : Continuous ν.norm) :
    IsMaximizerOn
      (fun z => z ∈ {y' : Fin N → ℝ |
        paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p = 1) β y'} ∧
        ∀ i, 0 < z i)
      nashLogObjective
      (fun i => (paper_inferred_user_value (users i) genre) ^ β) :=
  sourceSymmetricMixedNash_nashLogMaximizerOn_unitSphere_of_compactSublevels_of_singleton_nonzeroSupportGenres_of_nonzero_users
    (j := j) hnash hgenres husers husers_nonzero hperturb hβ
    hcompact_sublevels hcontinuous

/--
Lemma `conditiongen`, sufficient witness form: if a positive-score content
point in the source nonnegative unit ball satisfies the ratio condition, its
normalized direction generates the concrete symmetric mixed-Nash ray law.

As with the direct ray-law theorem, this is an equilibrium conclusion under
the formalized uniform-tie model and leaves the source's zero-support-point
literal `Genre` display as a separately tracked definition issue.
-/
theorem paper_lemma_conditiongen_positive_ball_witness_source_symmetric_mixed_nash
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {p : Content D}
    (ν : SourceNorm D) (hβ : 0 < β)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hp_nonnegative : NonnegativeContent p) (hp_norm_le_one : ν.norm p ≤ 1)
    (hscore : ∀ i : Fin N, 0 < paper_inferred_user_value (users i) p)
    (hcondition :
      paper_single_genre_direction_condition
        {y' : Fin N → ℝ |
          paper_powered_unit_image users
            (fun q => NonnegativeContent q ∧ ν.norm q ≤ 1) β y'}
        (fun i => (paper_inferred_user_value (users i) p) ^ β)) :
    paper_source_symmetric_mixed_nash P users (normRpowCost ν β)
      (singleGenreContentLaw N P β (SourceNorm.normalizedContent ν p)) :=
  singleGenreContentLaw_is_sourceSymmetricMixedNash_of_positive_ball_condition
    ν hβ husers hp_nonnegative hp_norm_le_one hscore hcondition

/--
Corollary `betaone`, direct equilibrium form: an attained positive
coordinate-product maximizer on the convex nonnegative unit-ball image gives
a concrete single-genre symmetric mixed-Nash ray law at `beta = 1`.
-/
theorem paper_corollary_betaone_concrete_source_symmetric_mixed_nash_of_product_maximizer
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {y : Fin N → ℝ}
    (ν : SourceNorm D)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (hconv : Convex ℝ
      {p : Content D | NonnegativeContent p ∧ ν.norm p ≤ 1})
    (hmax : IsCoordinateProductMaximizer
      {z : Fin N → ℝ |
        paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) (1 : ℝ) z} y)
    (hpos :
      ∀ z ∈ {z : Fin N → ℝ |
        paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) (1 : ℝ) z},
        ∀ i, 0 < z i) :
    ∃ p : Content D, NonnegativeContent p ∧ ν.norm p ≤ 1 ∧
      (∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) ∧
      paper_source_symmetric_mixed_nash P users (normRpowCost ν 1)
        (singleGenreContentLaw N P 1 (SourceNorm.normalizedContent ν p)) :=
  exists_singleGenreContentLaw_sourceSymmetricMixedNash_betaOne_of_productMaximizer
    ν husers hconv hmax hpos

/--
Corrected concrete Corollary `betaone`: compact convex source-norm sublevels
and the intended every-user-nonzero model condition supply the attained
positive product maximizer internally.  No impossible global positivity
assumption is made about the unit ball, which contains the zero action.
-/
theorem paper_corollary_betaone_concrete_source_symmetric_mixed_nash_of_compact_convex_nonzero_users
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} (ν : SourceNorm D)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i))
    (hcompact : SourceNormCompactSublevels ν)
    (hconvex : SourceNormConvexSublevels ν) :
    ∃ p : Content D, NonnegativeContent p ∧ ν.norm p ≤ 1 ∧
      (∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) ∧
      paper_source_symmetric_mixed_nash P users (normRpowCost ν 1)
        (singleGenreContentLaw N P 1 (SourceNorm.normalizedContent ν p)) :=
  exists_singleGenreContentLaw_sourceSymmetricMixedNash_betaOne_of_compact_convex_nonzero_users
    ν husers husers_nonzero hcompact hconvex

/--
Legacy strong-premise form of Corollary `betap` at `beta = q`.

Its global positivity premise includes the zero row of the norm ball and is
therefore normally uninhabited.  Use
`paper_corollary_betap_concrete_source_symmetric_mixed_nash_of_positive_feasible`
for the corrected nonvacuous endpoint.
-/
theorem paper_corollary_betap_concrete_source_symmetric_mixed_nash
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {q : ℝ} {users : Fin N → Content D} {y : Fin N → ℝ}
    (hq : 1 ≤ q) (husers : ∀ i, NonnegativeContent (users i))
    (hmax : IsCoordinateProductMaximizer
      (convexHull ℝ
        {z : Fin N → ℝ |
          paper_powered_unit_image users
            (fun p => NonnegativeContent p ∧
              AppliedModelingLib.FiniteDimensionalNorms.lp q p ≤ 1) q z}) y)
    (hpos : ∀ z ∈ convexHull ℝ
        {z : Fin N → ℝ |
          paper_powered_unit_image users
            (fun p => NonnegativeContent p ∧
              AppliedModelingLib.FiniteDimensionalNorms.lp q p ≤ 1) q z},
      ∀ i, 0 < z i) :
    ∃ p : Content D, NonnegativeContent p ∧
      AppliedModelingLib.FiniteDimensionalNorms.lp q p ≤ 1 ∧
      (∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) ∧
      paper_source_symmetric_mixed_nash P users
        (normRpowCost (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) q)
        (singleGenreContentLaw N P q
          (SourceNorm.normalizedContent
            (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) p)) :=
  exists_singleGenreContentLaw_sourceSymmetricMixedNash_lp_beta_eq_q
    hq husers hmax hpos

/--
Corrected direct Corollary `betap` endpoint at `beta = q`: a feasible
nonnegative content vector with positive score for every user suffices.  The
formalization proves compact attainment internally and handles the zero row
of the feasible norm ball through nonnegativity rather than treating it as a
positive row.
-/
theorem paper_corollary_betap_concrete_source_symmetric_mixed_nash_of_positive_feasible
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {q : ℝ} {users : Fin N → Content D}
    (hq : 1 ≤ q) (husers : ∀ i, NonnegativeContent (users i))
    (hpositive : ∃ p : Content D, NonnegativeContent p ∧
      AppliedModelingLib.FiniteDimensionalNorms.lp q p ≤ 1 ∧
      ∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) :
    ∃ p : Content D, NonnegativeContent p ∧
      AppliedModelingLib.FiniteDimensionalNorms.lp q p ≤ 1 ∧
      (∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) ∧
      paper_source_symmetric_mixed_nash P users
        (normRpowCost (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) q)
        (singleGenreContentLaw N P q
          (SourceNorm.normalizedContent
            (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) p)) :=
  exists_singleGenreContentLaw_sourceSymmetricMixedNash_lp_beta_eq_q_of_positive_feasible
    hq husers hpositive

/--
Positive-feasible bridge for the single-genre construction.  Under the
source-model clarification that every user embedding is nonzero, normalizing
the aggregate embedding gives a nonnegative unit direction that every user
strictly values.
-/
theorem paper_nonnegative_nonzero_users_have_positive_unit_direction
    {D N : ℕ} [Nonempty (Fin N)] (ν : SourceNorm D)
    {users : Fin N → Content D}
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i)) :
    ∃ genre : Content D, NonnegativeContent genre ∧ ν.norm genre = 1 ∧
      ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre :=
  SourceNorm.exists_nonnegative_unit_direction_positive_score_of_nonnegative_nonzero_users
    ν husers_nonnegative husers_nonzero

/--
Corrected concrete Corollary `betap` endpoint at `beta = q`: for the intended
nondegenerate source population, the positive-feasible premise follows from
nonnegative nonzero user embeddings by taking their aggregate direction.
-/
theorem paper_corollary_betap_concrete_source_symmetric_mixed_nash_of_nonzero_users
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {q : ℝ} {users : Fin N → Content D}
    (hq : 1 ≤ q) (husers : ∀ i, NonnegativeContent (users i))
    (husers_nonzero : ∀ i, NonzeroContent (users i)) :
    ∃ p : Content D, NonnegativeContent p ∧
      AppliedModelingLib.FiniteDimensionalNorms.lp q p ≤ 1 ∧
      (∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) ∧
      paper_source_symmetric_mixed_nash P users
        (normRpowCost (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) q)
        (singleGenreContentLaw N P q
          (SourceNorm.normalizedContent
            (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) p)) := by
  apply paper_corollary_betap_concrete_source_symmetric_mixed_nash_of_positive_feasible
    hq husers
  obtain ⟨genre, hgenre_nonnegative, hgenre_norm, hgenre_score⟩ :=
    paper_nonnegative_nonzero_users_have_positive_unit_direction
      (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) husers husers_nonzero
  refine ⟨genre, hgenre_nonnegative, ?_, hgenre_score⟩
  simpa [SourceNorm.lp] using hgenre_norm.le

/--
Corrected full existence form of Corollary `betap`: for every positive
`beta ≤ q`, finite Lq cost admits a source symmetric mixed equilibrium with a
singleton nonzero-support genre under the intended nonnegative/nonzero user
model.  The proof establishes the product-supremum condition at `q` by the Lq
barycenter argument and transports it to lower exponents before applying the
corrected compact Theorem `singlegenre`.  This is the mathematical content of
the source phrase `beta^* ≥ q`, without introducing its undefined global
threshold packaging.
-/
theorem paper_corollary_betap_singleton_nonzero_support_equilibrium_of_pos_le_q
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {q β : ℝ} {users : Fin N → Content D}
    (hq : 1 ≤ q) (hβ : 0 < β) (hβ_le_q : β ≤ q)
    (husers : ∀ i : Fin N, NonnegativeContent (users i))
    (husers_nonzero : ∀ i : Fin N, NonzeroContent (users i)) :
    ∃ (μ : MixedContentStrategy D) (genre : Content D),
      paper_source_symmetric_mixed_nash P users
        (normRpowCost (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) β) μ ∧
      paper_nonzero_support_genres (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) μ =
        ({genre} : Set (Content D)) :=
  exists_sourceSymmetricMixedNash_singleton_nonzeroSupportGenre_lp_of_pos_le_exponent
    hq hβ hβ_le_q husers husers_nonzero

/--
Corrected finite optimization core of Corollary `beta`.  Assume each
dual-normalized user has an attained nonnegative unit maximizing direction
with own score one, and all nonnegative unit-ball directions have total score
at most `Z`.  At any exponent satisfying the explicit strict scalar bound,
the convex hull of powered rows contains a row with strictly larger coordinate
product than every original powered row.

This is a fixed-exponent strict-gap theorem.  It does not silently identify
the paper's boundary case `Z = N` with a real-valued threshold or invoke the
separately reviewed generic single-genre iff.
-/
theorem paper_corollary_beta_finite_strict_product_gap_of_normalized_dual_witnesses
    {D N : ℕ} [Nonempty (Fin N)] {β Z : ℝ}
    {users : Fin N → Content D} (ν : SourceNorm D)
    (hβ_nonnegative : 0 ≤ β)
    (husers_nonnegative : ∀ i, NonnegativeContent (users i))
    (haggregate_bound : ∀ p : Content D, NonnegativeContent p → ν.norm p ≤ 1 →
      (∑ i : Fin N, paper_inferred_user_value (users i) p) ≤ Z)
    (hdual_witness : ∀ i : Fin N, ∃ p : Content D,
      NonnegativeContent p ∧ ν.norm p = 1 ∧
        paper_inferred_user_value (users i) p = 1)
    (hstrict : (Z / (N : ℝ)) ^ ((N : ℝ) * β) <
      (1 / (N : ℝ)) ^ (N : ℝ)) :
    ∃ y ∈ convexHull ℝ
        {z : Fin N → ℝ |
          paper_powered_unit_image users
            (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β z},
      ∀ z ∈ {z : Fin N → ℝ |
          paper_powered_unit_image users
            (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β z},
        coordinateProduct z < coordinateProduct y :=
  exists_convexHull_poweredUnitImage_coordinateProduct_strict_gap_of_normalized_dual_witnesses
    ν hβ_nonnegative husers_nonnegative haggregate_bound hdual_witness hstrict

/--
Corrected `Z = 1` branch of Corollary `beta`: if the score-one normalized
population has total score at most one on every nonnegative unit-ball action,
then every `beta > 1` gives the finite strict convex-hull product gap.
-/
theorem paper_corollary_beta_finite_strict_product_gap_of_Z_eq_one
    {D N : ℕ} [Nontrivial (Fin N)] {β : ℝ}
    {users : Fin N → Content D} (ν : SourceNorm D)
    (husers_nonnegative : ∀ i, NonnegativeContent (users i))
    (haggregate_bound : ∀ p : Content D, NonnegativeContent p → ν.norm p ≤ 1 →
      (∑ i : Fin N, paper_inferred_user_value (users i) p) ≤ 1)
    (hdual_witness : ∀ i : Fin N, ∃ p : Content D,
      NonnegativeContent p ∧ ν.norm p = 1 ∧
        paper_inferred_user_value (users i) p = 1)
    (hβ_one_lt : 1 < β) :
    ∃ y ∈ convexHull ℝ
        {z : Fin N → ℝ |
          paper_powered_unit_image users
            (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β z},
      ∀ z ∈ {z : Fin N → ℝ |
          paper_powered_unit_image users
            (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β z},
        coordinateProduct z < coordinateProduct y :=
  exists_convexHull_poweredUnitImage_coordinateProduct_strict_gap_of_Z_eq_one
    ν husers_nonnegative haggregate_bound hdual_witness hβ_one_lt

/--
Corrected interior form of Corollary `beta`.  For `1 < Z < N`, an exponent
strictly above the displayed logarithmic ratio gives the finite convex-hull
strict product gap under explicit dual-witness and aggregate-score premises.
The source's `Z = N` discussion is not encoded as real division by zero.
-/
theorem paper_corollary_beta_finite_strict_product_gap_of_lt_log_bound
    {D N : ℕ} [Nontrivial (Fin N)] {β Z : ℝ}
    {users : Fin N → Content D} (ν : SourceNorm D)
    (husers_nonnegative : ∀ i, NonnegativeContent (users i))
    (haggregate_bound : ∀ p : Content D, NonnegativeContent p → ν.norm p ≤ 1 →
      (∑ i : Fin N, paper_inferred_user_value (users i) p) ≤ Z)
    (hdual_witness : ∀ i : Fin N, ∃ p : Content D,
      NonnegativeContent p ∧ ν.norm p = 1 ∧
        paper_inferred_user_value (users i) p = 1)
    (hZ_one_lt : 1 < Z) (hZ_lt_card : Z < (N : ℝ))
    (hβ : Real.log (N : ℝ) /
        (Real.log (N : ℝ) - Real.log Z) < β) :
    ∃ y ∈ convexHull ℝ
        {z : Fin N → ℝ |
          paper_powered_unit_image users
            (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β z},
      ∀ z ∈ {z : Fin N → ℝ |
          paper_powered_unit_image users
            (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β z},
        coordinateProduct z < coordinateProduct y :=
  exists_convexHull_poweredUnitImage_coordinateProduct_strict_gap_of_lt_general_threshold
    ν husers_nonnegative haggregate_bound hdual_witness hZ_one_lt hZ_lt_card hβ

/--
Corrected finite interior equilibrium-exclusion conclusion for Corollary
`beta`: above the displayed log threshold, the strict convex-hull improvement
rules out every fully specified positive-score single-genre ray equilibrium.
-/
theorem paper_corollary_beta_no_concrete_ray_equilibrium_of_lt_log_bound
    {D N P : ℕ} [Nontrivial (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β Z : ℝ} {users : Fin N → Content D} {genre : Content D}
    (ν : SourceNorm D)
    (husers_nonnegative : ∀ i, NonnegativeContent (users i))
    (haggregate_bound : ∀ p : Content D, NonnegativeContent p → ν.norm p ≤ 1 →
      (∑ i : Fin N, paper_inferred_user_value (users i) p) ≤ Z)
    (hdual_witness : ∀ i : Fin N, ∃ p : Content D,
      NonnegativeContent p ∧ ν.norm p = 1 ∧
        paper_inferred_user_value (users i) p = 1)
    (hZ_one_lt : 1 < Z) (hZ_lt_card : Z < (N : ℝ))
    (hβ : Real.log (N : ℝ) /
        (Real.log (N : ℝ) - Real.log Z) < β)
    (hgenre_norm : ν.norm genre = 1)
    (hgenre_nonnegative : NonnegativeContent genre)
    (hscore : ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre) :
    ¬ paper_source_symmetric_mixed_nash P users (normRpowCost ν β)
      (singleGenreContentLaw N P β genre) :=
  not_singleGenreContentLaw_sourceSymmetricMixedNash_of_lt_general_threshold
    ν husers_nonnegative haggregate_bound hdual_witness hZ_one_lt hZ_lt_card hβ
    hgenre_norm hgenre_nonnegative hscore

/--
Corrected `Z = 1` boundary conclusion for Corollary `beta`: every `beta > 1`
rules out a fully specified positive-score single-genre ray equilibrium under
the score-one dual witnesses and unit-ball aggregate bound.
-/
theorem paper_corollary_beta_no_concrete_ray_equilibrium_of_Z_eq_one
    {D N P : ℕ} [Nontrivial (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {genre : Content D}
    (ν : SourceNorm D)
    (husers_nonnegative : ∀ i, NonnegativeContent (users i))
    (haggregate_bound : ∀ p : Content D, NonnegativeContent p → ν.norm p ≤ 1 →
      (∑ i : Fin N, paper_inferred_user_value (users i) p) ≤ 1)
    (hdual_witness : ∀ i : Fin N, ∃ p : Content D,
      NonnegativeContent p ∧ ν.norm p = 1 ∧
        paper_inferred_user_value (users i) p = 1)
    (hβ_one_lt : 1 < β)
    (hgenre_norm : ν.norm genre = 1)
    (hgenre_nonnegative : NonnegativeContent genre)
    (hscore : ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre) :
    ¬ paper_source_symmetric_mixed_nash P users (normRpowCost ν β)
      (singleGenreContentLaw N P β genre) :=
  not_singleGenreContentLaw_sourceSymmetricMixedNash_of_Z_eq_one
    ν husers_nonnegative haggregate_bound hdual_witness hβ_one_lt
    hgenre_norm hgenre_nonnegative hscore

/--
Corrected interior equilibrium-exclusion form of Corollary `beta`.  Under the
explicit compact source-norm package, the finite strict product gap rules out
every source symmetric mixed equilibrium with a singleton *nonzero-support*
genre, not merely the concrete ray-law presentation.  The proof uses the
completed corrected compact Theorem `singlegenre` to identify any such law
with that ray law.  It does not encode the source's undefined `Z = N`
real-division boundary or define its unqualified `beta^*`.
-/
theorem paper_corollary_beta_no_singleton_nonzero_support_equilibrium_of_lt_log_bound
    {D N P : ℕ} [Nontrivial (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β Z : ℝ} {users : Fin N → Content D}
    (ν : SourceNorm D)
    (husers_nonnegative : ∀ i, NonnegativeContent (users i))
    (husers_nonzero : ∀ i, NonzeroContent (users i))
    (hperturb : SourceNormPerturbationContinuous ν)
    (hcompact_sublevels : SourceNormCompactSublevels ν)
    (hcontinuous : Continuous ν.norm)
    (haggregate_bound : ∀ p : Content D, NonnegativeContent p → ν.norm p ≤ 1 →
      (∑ i : Fin N, paper_inferred_user_value (users i) p) ≤ Z)
    (hdual_witness : ∀ i : Fin N, ∃ p : Content D,
      NonnegativeContent p ∧ ν.norm p = 1 ∧
        paper_inferred_user_value (users i) p = 1)
    (hZ_one_lt : 1 < Z) (hZ_lt_card : Z < (N : ℝ))
    (hβ : Real.log (N : ℝ) /
        (Real.log (N : ℝ) - Real.log Z) < β) :
    ¬ ∃ (μ : MixedContentStrategy D) (genre : Content D),
      paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ ∧
      paper_nonzero_support_genres ν μ = ({genre} : Set (Content D)) :=
  not_exists_sourceSymmetricMixedNash_singleton_nonzeroSupportGenre_of_lt_general_threshold
    ν husers_nonnegative husers_nonzero hperturb hcompact_sublevels hcontinuous
    haggregate_bound hdual_witness hZ_one_lt hZ_lt_card hβ

/--
Corrected `Z = 1` equilibrium-exclusion branch of Corollary `beta`: every
`beta > 1` rules out arbitrary compact source equilibria with a singleton
nonzero-support genre under the stated normalized dual witnesses and aggregate
bound.  The literal `Z = N`/infinity branch remains intentionally separate.
-/
theorem paper_corollary_beta_no_singleton_nonzero_support_equilibrium_of_Z_eq_one
    {D N P : ℕ} [Nontrivial (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D}
    (ν : SourceNorm D)
    (husers_nonnegative : ∀ i, NonnegativeContent (users i))
    (husers_nonzero : ∀ i, NonzeroContent (users i))
    (hperturb : SourceNormPerturbationContinuous ν)
    (hcompact_sublevels : SourceNormCompactSublevels ν)
    (hcontinuous : Continuous ν.norm)
    (haggregate_bound : ∀ p : Content D, NonnegativeContent p → ν.norm p ≤ 1 →
      (∑ i : Fin N, paper_inferred_user_value (users i) p) ≤ 1)
    (hdual_witness : ∀ i : Fin N, ∃ p : Content D,
      NonnegativeContent p ∧ ν.norm p = 1 ∧
        paper_inferred_user_value (users i) p = 1)
    (hβ_one_lt : 1 < β) :
    ¬ ∃ (μ : MixedContentStrategy D) (genre : Content D),
      paper_source_symmetric_mixed_nash P users (normRpowCost ν β) μ ∧
      paper_nonzero_support_genres ν μ = ({genre} : Set (Content D)) :=
  not_exists_sourceSymmetricMixedNash_singleton_nonzeroSupportGenre_of_Z_eq_one
    ν husers_nonnegative husers_nonzero hperturb hcompact_sublevels hcontinuous
    haggregate_bound hdual_witness hβ_one_lt

/--
Corollary `beta` dual-attainment bridge: a nonzero nonnegative user has a
positive-score nonnegative unit direction maximizing its score over the
nonnegative source-norm unit ball whenever the source norm has compact
sublevels.
-/
theorem paper_corollary_beta_dual_score_attainment_of_compact_sublevels
    {D : ℕ} (ν : SourceNorm D) {u : Content D}
    (hu_nonnegative : NonnegativeContent u) (hu_nonzero : NonzeroContent u)
    (hcompact : SourceNormCompactSublevels ν) :
    ∃ p : Content D, NonnegativeContent p ∧ ν.norm p = 1 ∧
      0 < paper_inferred_user_value u p ∧
      ∀ q : Content D, NonnegativeContent q → ν.norm q ≤ 1 →
        paper_inferred_user_value u q ≤ paper_inferred_user_value u p :=
  exists_nonnegative_unit_score_maximizer_of_compactSublevels
    ν hu_nonnegative hu_nonzero hcompact

/--
Corollary `beta` aggregate-bound bridge: compact source-norm sublevels give a
positive attained bound `Z` on the total user score of every nonnegative
unit-ball direction, for a nonzero finite population.
-/
theorem paper_corollary_beta_exists_aggregate_score_bound_of_compact_sublevels
    {D N : ℕ} [Nonempty (Fin N)] (ν : SourceNorm D)
    {users : Fin N → Content D}
    (husers_nonnegative : ∀ i, NonnegativeContent (users i))
    (husers_nonzero : ∀ i, NonzeroContent (users i))
    (hcompact : SourceNormCompactSublevels ν) :
    ∃ Z : ℝ, 0 < Z ∧
      ∀ q : Content D, NonnegativeContent q → ν.norm q ≤ 1 →
        (∑ i : Fin N, paper_inferred_user_value (users i) q) ≤ Z :=
  exists_aggregate_score_bound_of_compactSublevels
    ν husers_nonnegative husers_nonzero hcompact

/--
Corollary `beta` normalization bridge.  Under compact source-norm sublevels,
each nonzero nonnegative user's attained positive dual score can be scaled to
one.  The resulting normalized finite population has nonnegative nonzero
users, score-one unit witnesses, and a positive aggregate unit-ball bound.
-/
theorem paper_corollary_beta_exists_score_normalized_users_and_aggregate_bound
    {D N : ℕ} [Nonempty (Fin N)] (ν : SourceNorm D)
    {users : Fin N → Content D}
    (husers_nonnegative : ∀ i, NonnegativeContent (users i))
    (husers_nonzero : ∀ i, NonzeroContent (users i))
    (hcompact : SourceNormCompactSublevels ν) :
    ∃ normalizedUsers : Fin N → Content D, ∃ Z : ℝ,
      (∀ i, NonnegativeContent (normalizedUsers i)) ∧
      (∀ i, NonzeroContent (normalizedUsers i)) ∧
      (∀ i, ∃ p : Content D, NonnegativeContent p ∧ ν.norm p = 1 ∧
        paper_inferred_user_value (normalizedUsers i) p = 1 ∧
        ∀ q : Content D, NonnegativeContent q → ν.norm q ≤ 1 →
          paper_inferred_user_value (normalizedUsers i) q ≤
            paper_inferred_user_value (normalizedUsers i) p) ∧
      0 < Z ∧ 1 ≤ Z ∧ Z ≤ (N : ℝ) ∧
      (∀ q : Content D, NonnegativeContent q → ν.norm q ≤ 1 →
        (∑ i : Fin N, paper_inferred_user_value (normalizedUsers i) q) ≤ Z) :=
  exists_scoreNormalizedUsers_dualWitnesses_and_aggregateBound_of_compactSublevels
    ν husers_nonnegative husers_nonzero hcompact

/--
Corollary `onepopulation`, direct equilibrium form: if every user has the
same nonnegative embedding, a positive-score unit direction maximizing that
common user's value generates the concrete single-genre symmetric mixed-Nash
ray law.
-/
theorem paper_corollary_onepopulation_concrete_source_symmetric_mixed_nash
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {u genre : Content D}
    (ν : SourceNorm D) (hβ : 0 < β)
    (hu_nonnegative : NonnegativeContent u)
    (hgenre_nonnegative : NonnegativeContent genre)
    (hgenre_norm : ν.norm genre = 1)
    (hscore_pos : 0 < paper_inferred_user_value u genre)
    (hunit_max : ∀ d : Content D, NonnegativeContent d → ν.norm d = 1 →
      paper_inferred_user_value u d ≤ paper_inferred_user_value u genre) :
    paper_source_symmetric_mixed_nash P (fun _ : Fin N => u) (normRpowCost ν β)
      (singleGenreContentLaw N P β genre) :=
  onePopulationSingleGenreContentLaw_is_sourceSymmetricMixedNash
    ν hβ hu_nonnegative hgenre_nonnegative hgenre_norm hscore_pos hunit_max

/--
Assembled concrete Corollary `onepopulation`: under the stated nondegeneracy
and measurability hypotheses, the selected ray law is a source-semantic
symmetric mixed Nash equilibrium, has the asserted bounded ray support, and
has the exact corrected Lemma-`cdf` scalar CDF after mapping by the source
norm.  The source's literal Corollary display has a separate `N`-exponent
mismatch, recorded in the paper-local working memo.
-/
theorem paper_corollary_onepopulation_concrete_full
    {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {u genre : Content D}
    (ν : SourceNorm D) (hβ : 0 < β)
    (hu_nonnegative : NonnegativeContent u)
    (hgenre_nonnegative : NonnegativeContent genre)
    (hgenre_norm : ν.norm genre = 1)
    (hscore_pos : 0 < paper_inferred_user_value u genre)
    (hunit_max : ∀ d : Content D, NonnegativeContent d → ν.norm d = 1 →
      paper_inferred_user_value u d ≤ paper_inferred_user_value u genre)
    (hnorm_meas : Measurable ν.norm) :
    paper_source_symmetric_mixed_nash P (fun _ : Fin N => u) (normRpowCost ν β)
        (singleGenreContentLaw N P β genre) ∧
      (singleGenreContentLaw N P β genre).support ⊆
        {p : Content D | ∃ q : ℝ, q ∈ Set.Icc (0 : ℝ) ((N : ℝ) ^ β⁻¹) ∧
          p = scaleContent q genre} ∧
      ∀ z : ℝ, 0 ≤ z →
        Measure.map ν.norm (singleGenreContentLaw N P β genre) (Set.Iic z) =
          ENNReal.ofReal (paper_single_genre_cdf N P β z) :=
  onePopulationSingleGenreContentLaw_sourceNash_support_and_normCdf
    ν hβ hu_nonnegative hgenre_nonnegative hgenre_norm hscore_pos hunit_max
    hnorm_meas

/--
Check of the source-model's excluded all-zero population: when every user
embedding is zero, the Dirac mass at zero content is an atomic source symmetric
mixed Nash equilibrium for every positive norm-power exponent.
-/
theorem paper_counterexample_atom_all_zero_users_atomic_source_symmetric_mixed_nash
    {D N P : ℕ} [Nonempty (Fin P)]
    (ν : SourceNorm D) {β : ℝ} (hβ : 0 < β) :
    paper_source_symmetric_mixed_nash P (fun _ : Fin N => (0 : Content D))
        (normRpowCost ν β) (MeasureTheory.Measure.dirac (0 : Content D)) ∧
      (MeasureTheory.Measure.dirac (0 : Content D)).real
        ({(0 : Content D)} : Set (Content D)) = 1 := by
  refine ⟨zeroUsers_dirac_zero_is_sourceSymmetricMixedNash_normRpowCost ν hβ, ?_⟩
  simp [MeasureTheory.Measure.real]

/--
Proposition `atom`, source-faithful endpoint: under the source-model
clarification that one user is nonzero, and with nonnegative user embeddings,
every direct symmetric mixed Nash law is atomless.  The finite uniform-tie
model discharges the product-payoff measurability internally.
-/
theorem paper_proposition_atom_atomless_of_source_symmetric_mixed_nash
    {D N P : ℕ} [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} {i0 : Fin N}
    (hnash : paper_source_symmetric_mixed_nash P users cost μ)
    (hcont : PerturbationCostContinuous cost)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0)) :
    paper_mixed_content_strategy_atomless μ :=
  mixedContentStrategyAtomless_of_sourceSymmetricMixedNash
    hnash hcont husers_nonneg hzero

/-- The corrected atomlessness conclusion in mathlib's `NoAtoms` form. -/
theorem paper_proposition_atom_no_atoms_of_source_symmetric_mixed_nash
    {D N P : ℕ} [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} {i0 : Fin N}
    (hnash : paper_source_symmetric_mixed_nash P users cost μ)
    (hcont : PerturbationCostContinuous cost)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0)) :
    MeasureTheory.NoAtoms μ :=
  noAtoms_of_sourceSymmetricMixedNash hnash hcont husers_nonneg hzero

/-- The corrected atomlessness conclusion as a zero singleton probability. -/
theorem paper_proposition_atom_singleton_mass_zero_of_source_symmetric_mixed_nash
    {D N P : ℕ} [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} {i0 : Fin N}
    (hnash : paper_source_symmetric_mixed_nash P users cost μ)
    (hcont : PerturbationCostContinuous cost)
    (husers_nonneg : ∀ i : Fin N, NonnegativeContent (users i))
    (hzero : NonzeroContent (users i0)) (p : Content D) :
    μ.real ({p} : Set (Content D)) = 0 :=
  measureReal_singleton_eq_zero_of_sourceSymmetricMixedNash
    hnash hcont husers_nonneg hzero p

/--
Proposition `finitegenre`, the source's overlap-graph step: edgewise equality
of a label propagates to every two genres once the supplied overlap graph is
preconnected.  The theorem intentionally leaves construction and
preconnectedness of that graph as explicit hypotheses.
-/
theorem paper_finite_genre_overlap_label_eq_of_preconnected
    {V W : Type*} {G : SimpleGraph V} (hpreconnected : G.Preconnected)
    (label : V → W)
    (hlabel : ∀ ⦃i j : V⦄, G.Adj i j → label i = label j)
    (i j : V) : label i = label j :=
  finiteGenre_overlapLabel_eq_of_preconnected hpreconnected label hlabel i j

/--
Proposition `finitegenre`, support-topology substep: a finite family of
nonempty pairwise-disjoint relatively closed components cannot cover the
connected score-support interval unless it has a single component.  The
closedness, cover, and nonemptiness hypotheses remain explicit rather than
being inferred from C1--C3.
-/
theorem paper_finite_genre_closed_partition_subsingleton
    {ι : Type*} [Finite ι] {a b : ℝ} (component : ι → Set ℝ)
    (hnonempty : ∀ i, (component i ∩ Set.Icc a b).Nonempty)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (component i ∩ Set.Icc a b) (component j ∩ Set.Icc a b))
    (hclosed : ∀ i, IsClosed (component i ∩ Set.Icc a b))
    (hcover : ⋃ i, component i ∩ Set.Icc a b = Set.Icc a b) :
    Subsingleton ι :=
  finiteGenre_closedPartition_subsingleton
    component hnonempty hdisjoint hclosed hcover

/--
Proposition `finitegenre`, combined overlap conclusion: under the stated
nonempty closed cover of the score-support interval, an angle label that is
equal on each overlap edge is equal for every pair of genres.  This validates
the source's cover-to-connected-overlap-to-path-equality argument without
silently deriving its measure-theoretic premises.
-/
theorem paper_finite_genre_overlap_label_eq_of_closed_cover
    {ι W : Type*} [Fintype ι] [Nonempty ι] {a b : ℝ}
    (component : ι → Set ℝ)
    (hnonempty : ∀ i, (component i ∩ Set.Icc a b).Nonempty)
    (hclosed : ∀ i, IsClosed (component i ∩ Set.Icc a b))
    (hcover : ⋃ i, component i ∩ Set.Icc a b = Set.Icc a b)
    (label : ι → W)
    (hedge : ∀ ⦃i j : ι⦄,
      (AppliedModelingLib.setFamilyOverlapGraph (Set.Icc a b) component).Adj i j →
        label i = label j)
    (i j : ι) : label i = label j :=
  finiteGenre_overlapLabel_eq_of_closed_cover
    component hnonempty hclosed hcover label hedge i j

/--
Proposition `finitegenre`, the local FOC equality step: equal density values
with a nonzero common prefactor imply equality of the two angle-label factors.
-/
theorem paper_finite_genre_label_eq_of_shared_density
    {density pref label_i label_j : ℝ} (hpref : pref ≠ 0)
    (hi : density = pref * label_i) (hj : density = pref * label_j) :
    label_i = label_j :=
  finiteGenre_label_eq_of_shared_density hpref hi hj

/--
Proposition `finitegenre`, source-shaped global label consequence: a common
nonzero-prefactor density equation on every member of the explicit finite
closed score-support cover makes the displayed angle label constant across all
genres.  The CDF/support hypotheses that would establish this package remain
visible at the theorem boundary.
-/
theorem paper_finite_genre_label_eq_of_shared_density_closed_cover
    {ι : Type*} [Fintype ι] [Nonempty ι] {a b : ℝ}
    (component : ι → Set ℝ)
    (hnonempty : ∀ i, (component i ∩ Set.Icc a b).Nonempty)
    (hclosed : ∀ i, IsClosed (component i ∩ Set.Icc a b))
    (hcover : ⋃ i, component i ∩ Set.Icc a b = Set.Icc a b)
    (density pref : ℝ → ℝ) (label : ι → ℝ)
    (hpref : ∀ w, w ∈ Set.Icc a b → pref w ≠ 0)
    (hdensity : ∀ i w, w ∈ component i ∩ Set.Icc a b →
      density w = pref w * label i)
    (i j : ι) : label i = label j :=
  finiteGenre_label_eq_of_shared_density_closed_cover
    component hnonempty hclosed hcover density pref label hpref hdensity i j

/--
Proposition `finitegenre`, compact-source version of the overlap-cover step.
Compact joint value support covered by finitely many closed genre pieces gives
closed first-score components and their full interval cover automatically.
With the displayed common density formula, the angle label is consequently
constant.  This theorem still requires an explicit finite closed piece cover;
it does not manufacture one from C1--C3.
-/
theorem paper_finite_genre_label_eq_of_shared_density_of_compact_closed_piece_cover
    {ι : Type*} [Fintype ι] [Nonempty ι] {a b : ℝ}
    {S : Set (ℝ × ℝ)} (piece : ι → Set (ℝ × ℝ))
    (hcompact : IsCompact S) (hpiece_closed : ∀ i, IsClosed (piece i))
    (hpiece_cover : S ⊆ ⋃ i, piece i)
    (hfst_image : Prod.fst '' S = Set.Icc a b)
    (hnonempty : ∀ i,
      ((Prod.fst '' (S ∩ piece i)) ∩ Set.Icc a b).Nonempty)
    (density pref : ℝ → ℝ) (label : ι → ℝ)
    (hpref : ∀ w, w ∈ Set.Icc a b → pref w ≠ 0)
    (hdensity : ∀ i w, w ∈ (Prod.fst '' (S ∩ piece i)) ∩ Set.Icc a b →
      density w = pref w * label i)
    (i j : ι) : label i = label j :=
  finiteGenre_label_eq_of_shared_density_of_compact_closed_piece_cover
    piece hcompact hpiece_closed hpiece_cover hfst_image hnonempty
    density pref label hpref hdensity i j

/-- The closed value-space ray corresponding to one finite-genre angle. -/
abbrev paper_canonical_two_user_genre_ray (theta_star theta : ℝ) : Set (ℝ × ℝ) :=
  canonicalTwoUserGenreRay theta_star theta

/--
The paper's nonnegative-radius genre parametrization is exactly the closed
canonical value-space ray when the first-user cosine is positive.
-/
theorem paper_mem_canonical_two_user_genre_ray_iff_exists_nonneg_radius
    {theta_star theta : ℝ} {z : ℝ × ℝ} (hcos : 0 < Real.cos theta) :
    z ∈ paper_canonical_two_user_genre_ray theta_star theta ↔
      ∃ r : ℝ, 0 ≤ r ∧
        z = (r * Real.cos theta, r * Real.cos (theta_star - theta)) :=
  mem_canonicalTwoUserGenreRay_iff_exists_nonneg_radius hcos

/--
Proposition `finitegenre`, canonical-ray overlap conclusion.  A compact value
support covered by the explicit finite list of genre rays supplies the
closed-component cover needed to propagate a common density label across all
angles.  Nonempty components and the C1 density formula remain explicit.
-/
theorem paper_finite_genre_label_eq_of_shared_density_of_compact_canonical_ray_cover
    {ι : Type*} [Fintype ι] [Nonempty ι] {a b theta_star : ℝ}
    {S : Set (ℝ × ℝ)} (angle : ι → ℝ)
    (hcompact : IsCompact S)
    (hray_cover : S ⊆ ⋃ i,
      paper_canonical_two_user_genre_ray theta_star (angle i))
    (hfst_image : Prod.fst '' S = Set.Icc a b)
    (hnonempty : ∀ i,
      ((Prod.fst ''
        (S ∩ paper_canonical_two_user_genre_ray theta_star (angle i))) ∩
          Set.Icc a b).Nonempty)
    (density pref : ℝ → ℝ) (label : ι → ℝ)
    (hpref : ∀ w, w ∈ Set.Icc a b → pref w ≠ 0)
    (hdensity : ∀ i w,
      w ∈ (Prod.fst ''
        (S ∩ paper_canonical_two_user_genre_ray theta_star (angle i))) ∩
          Set.Icc a b → density w = pref w * label i)
    (i j : ι) : label i = label j :=
  finiteGenre_label_eq_of_shared_density_of_compact_canonicalRay_cover
    angle hcompact hray_cover hfst_image hnonempty density pref label
    hpref hdensity i j

/--
Proposition `finitegenre`, corrected source-genre-to-label bridge.  If the
finite list of angle directions is exactly the corrected nonzero-support genre
set, it supplies the ray cover and nonempty ray components automatically.
Under compact canonical value support, the complete first-score interval, and
the displayed nonzero-prefactor density formula, the label is constant across
all listed genres.
-/
theorem paper_finite_genre_label_eq_of_shared_density_of_compact_nonzero_support_genres_eq_range
    {ν : SourceNorm 2} {theta_star a b : ℝ} {μ : MixedContentStrategy 2}
    {ι : Type*} [Fintype ι] [Nonempty ι] (angle : ι → ℝ)
    (hsin : Real.sin theta_star ≠ 0)
    (hcos : ∀ i, 0 < Real.cos (angle i))
    (hgenres : paper_nonzero_support_genres ν μ =
      Set.range (fun i => content2 (Real.cos (angle i)) (Real.sin (angle i))))
    (hcompact : IsCompact (Measure.map (canonicalTwoUserValueMap theta_star) μ).support)
    (hfst_image : Prod.fst ''
      (Measure.map (canonicalTwoUserValueMap theta_star) μ).support = Set.Icc a b)
    (density pref : ℝ → ℝ) (label : ι → ℝ)
    (hpref : ∀ w, w ∈ Set.Icc a b → pref w ≠ 0)
    (hdensity : ∀ i w,
      w ∈ (Prod.fst ''
        ((Measure.map (canonicalTwoUserValueMap theta_star) μ).support ∩
          paper_canonical_two_user_genre_ray theta_star (angle i))) ∩
          Set.Icc a b → density w = pref w * label i)
    (i j : ι) : label i = label j :=
  finiteGenre_label_eq_of_shared_density_of_compact_nonzeroSupportGenres_eq_range
    angle hsin hcos hgenres hcompact hfst_image density pref label hpref hdensity i j

/--
Proposition `finitegenre`, corrected positive-score overlap bridge.  It avoids
the origin, where the displayed C1 density prefactor can vanish, and therefore
makes the cancellation premise mathematically usable.
-/
abbrev paper_finite_genre_label_eq_of_shared_density_of_compact_nonzero_support_genres_eq_range_on_positive_cutoff :=
  @finiteGenre_label_eq_of_shared_density_of_compact_nonzeroSupportGenres_eq_range_on_positive_cutoff

/--
Proposition `finitegenre`, finite-ray positive-cutoff construction.  Each
listed realized nonzero genre retains a support point above one common positive
first-score threshold.
-/
abbrev paper_canonical_two_user_exists_positive_cutoff_of_finite_nonzero_support_genres_eq_range :=
  @canonicalTwoUser_exists_positive_cutoff_of_finite_nonzeroSupportGenres_eq_range

/--
Proposition `finitegenre`, corrected label propagation with a cutoff supplied
from the finite nonzero-genre condition itself.
-/
abbrev paper_finite_genre_exists_positive_cutoff_and_label_eq_of_compact_nonzero_support_genres_eq_range :=
  @finiteGenre_exists_positive_cutoff_and_label_eq_of_compact_nonzeroSupportGenres_eq_range

/--
Proposition `finitegenre`, actual-Nash endpoint for the finite-ray overlap
argument.  It derives compact value support and the complete first-score
interval from the boundary-safe C1 hypotheses; its remaining displayed
premise is the source's pointwise common density formula on each genre ray.
-/
abbrev paper_finite_genre_exists_first_score_interval_and_label_eq_of_scaled_norm_rpow_cost_nash :=
  @finiteGenre_exists_firstScoreInterval_and_label_eq_of_scaledNormRpowCostNash

/--
Exact algebraic C1 bridge for the first `finitegenre` label: on a positive
canonical ray, the induced-cost first partial is the common score prefactor
times the source's first angle label.
-/
abbrev paper_two_user_induced_cost_first_partial_param_eq_score_rpow_mul_finite_genre_first_angle_label :=
  @twoUserInducedCostFirstPartial_param_eq_scoreRpow_mul_finiteGenreFirstAngleLabel

/--
Pointwise C1 first-order formula for the literal first angle label at a
positive strictly interior canonical genre-ray point.  Its differentiability
and interiority hypotheses are explicit.
-/
abbrev paper_deriv_first_reward_eq_score_rpow_mul_finite_genre_first_angle_label_of_is_max_on_of_mem_canonical_genre_ray :=
  @deriv_firstReward_eq_scoreRpow_mul_finiteGenreFirstAngleLabel_of_isMaxOn_of_mem_canonicalGenreRay

/--
Exact user-swapped C1 algebraic bridge for the second `finitegenre` label on a
positive canonical ray.
-/
abbrev paper_two_user_induced_cost_second_partial_param_eq_score_rpow_mul_finite_genre_second_angle_label :=
  @twoUserInducedCostSecondPartial_param_eq_scoreRpow_mul_finiteGenreSecondAngleLabel

/--
Pointwise C1 second-coordinate formula for the literal user-swapped angle
label at a positive strictly interior canonical genre-ray point.
-/
abbrev paper_deriv_second_reward_eq_score_rpow_mul_finite_genre_second_angle_label_of_is_max_on_of_mem_canonical_genre_ray :=
  @deriv_secondReward_eq_scoreRpow_mul_finiteGenreSecondAngleLabel_of_isMaxOn_of_mem_canonicalGenreRay

/--
Finite-genre C1 endpoint with compact value support and a known first-score
interval: it derives the common first angle label on every represented ray,
using the finite positive cutoff rather than cancelling at score zero.
-/
abbrev paper_finite_genre_exists_positive_cutoff_and_first_angle_label_eq_of_compact_scaled_norm_rpow_cost_nash :=
  @finiteGenre_exists_positive_cutoff_and_firstAngleLabel_eq_of_compact_scaledNormRpowCostNash

/--
Actual-Nash endpoint for the first literal `finitegenre` FOC condition.  The
first score interval, uniform positive cutoff, and common first angle label
are all derived from the stated C1 Nash hypotheses.  The user-swapped endpoint
is exposed separately below; neither theorem claims the global graph bridge.
-/
abbrev paper_finite_genre_exists_first_score_interval_and_first_angle_label_eq_of_scaled_norm_rpow_cost_nash :=
  @finiteGenre_exists_firstScoreInterval_and_firstAngleLabel_eq_of_scaledNormRpowCostNash

/--
The source's analogous second marginal support interval, formally obtained
from the compact continuous value graph rather than by an unstated coordinate
symmetry.
-/
abbrev paper_canonical_two_user_second_score_support_eq_Icc_of_scaled_norm_rpow_cost_nash_away_origin :=
  @canonicalTwoUser_secondScoreSupport_eq_Icc_of_scaledNormRpowCostNash_awayOrigin

/--
Finite-genre construction of one positive cutoff common to all second-score
ray components.
-/
abbrev paper_canonical_two_user_exists_positive_second_cutoff_of_finite_nonzero_support_genres_eq_range :=
  @canonicalTwoUser_exists_positive_second_cutoff_of_finite_nonzeroSupportGenres_eq_range

/--
Second-coordinate finite-genre C1 propagation from compact support and its
complete second-score interval.
-/
abbrev paper_finite_genre_exists_positive_second_cutoff_and_second_angle_label_eq_of_compact_scaled_norm_rpow_cost_nash :=
  @finiteGenre_exists_positive_second_cutoff_and_secondAngleLabel_eq_of_compact_scaledNormRpowCostNash

/--
Actual-Nash endpoint for the literal user-swapped `finitegenre` FOC condition.
It derives the second score interval, its positive cutoff, and the common
second angle label under the same explicit C1 hypotheses.
-/
abbrev paper_finite_genre_exists_second_score_interval_and_second_angle_label_eq_of_scaled_norm_rpow_cost_nash :=
  @finiteGenre_exists_secondScoreInterval_and_secondAngleLabel_eq_of_scaledNormRpowCostNash

/--
Complete Step-1 FOC propagation in Proposition `finitegenre`: both marginal
score intervals and both literal angle-label equalities follow from the actual
Nash/C1 model under explicit pointwise regularity.  The later at-most-two
graph/curvature inference is not included here.
-/
abbrev paper_finite_genre_exists_score_intervals_and_angle_label_eq_of_scaled_norm_rpow_cost_nash :=
  @finiteGenre_exists_scoreIntervals_and_angleLabel_eq_of_scaledNormRpowCostNash

/--
Strengthened finite-genre consequence of the fully explicit boundary-safe C1
Nash package: a continuous ordered value-support graph covered by finitely
many represented principal-angle rays has at most one direction. This does not
restate or validate the source's unsupported literal two-genre Step-1 claim.
-/
abbrev paper_finite_genre_card_le_one_of_scaled_norm_rpow_cost_nash :=
  @finiteGenre_card_le_one_of_scaledNormRpowCostNash

/--
Proposition `finitegenre`, first literal angle-label equality from the source
FOC display.  The common density-prefactor and closed-cover hypotheses are
spelled out, rather than inferred from the reviewed C1--C3 bridge.
-/
theorem paper_finite_genre_first_angle_label_eq_of_shared_density_closed_cover
    {ι : Type*} [Fintype ι] [Nonempty ι] {a b β theta_star : ℝ}
    (component : ι → Set ℝ) (angle : ι → ℝ)
    (hnonempty : ∀ i, (component i ∩ Set.Icc a b).Nonempty)
    (hclosed : ∀ i, IsClosed (component i ∩ Set.Icc a b))
    (hcover : ⋃ i, component i ∩ Set.Icc a b = Set.Icc a b)
    (density pref : ℝ → ℝ)
    (hpref : ∀ w, w ∈ Set.Icc a b → pref w ≠ 0)
    (hdensity : ∀ i w, w ∈ component i ∩ Set.Icc a b →
      density w = pref w * finiteGenreFirstAngleLabel β theta_star (angle i))
    (i j : ι) :
    finiteGenreFirstAngleLabel β theta_star (angle i) =
      finiteGenreFirstAngleLabel β theta_star (angle j) :=
  finiteGenre_firstAngleLabel_eq_of_shared_density_closed_cover
    component angle hnonempty hclosed hcover density pref hpref hdensity i j

/--
Proposition `finitegenre`, second literal, user-swapped angle-label equality
from the source FOC display, under the same explicit structural hypotheses.
-/
theorem paper_finite_genre_second_angle_label_eq_of_shared_density_closed_cover
    {ι : Type*} [Fintype ι] [Nonempty ι] {a b β theta_star : ℝ}
    (component : ι → Set ℝ) (angle : ι → ℝ)
    (hnonempty : ∀ i, (component i ∩ Set.Icc a b).Nonempty)
    (hclosed : ∀ i, IsClosed (component i ∩ Set.Icc a b))
    (hcover : ⋃ i, component i ∩ Set.Icc a b = Set.Icc a b)
    (density pref : ℝ → ℝ)
    (hpref : ∀ w, w ∈ Set.Icc a b → pref w ≠ 0)
    (hdensity : ∀ i w, w ∈ component i ∩ Set.Icc a b →
      density w = pref w * finiteGenreSecondAngleLabel β theta_star (angle i))
    (i j : ι) :
    finiteGenreSecondAngleLabel β theta_star (angle i) =
      finiteGenreSecondAngleLabel β theta_star (angle j) :=
  finiteGenre_secondAngleLabel_eq_of_shared_density_closed_cover
    component angle hnonempty hclosed hcover density pref hpref hdensity i j

/--
Finitegenre Step 1 calculus: on the positive-cosine domain, the first printed
FOC angle label has the displayed closed derivative. This is a direct
calculation; it does not supply the source's later global fiber count.
-/
theorem paper_has_deriv_at_finite_genre_first_angle_label
    {β theta_star theta : ℝ} (hcos : 0 < Real.cos theta) :
    HasDerivAt (fun x : ℝ => finiteGenreFirstAngleLabel β theta_star x)
      ((-Real.cos (theta_star - theta) * Real.cos theta +
        (β - 1) * Real.sin (theta_star - theta) * Real.sin theta) /
        (Real.cos theta) ^ β) theta :=
  hasDerivAt_finiteGenreFirstAngleLabel hcos

/--
Finitegenre Step 1 calculus: for a positive source exponent, the derivative
of the first angle label is the source `secondderiv` sign bracket times its
positive-cosine scale. It establishes the bracket/label connection but does
not assert that the bracket classifies all simultaneous label fibers.
-/
theorem paper_has_deriv_at_finite_genre_first_angle_label_sign_bracket
    {β theta_star theta : ℝ} (hβ : 0 < β) (hcos : 0 < Real.cos theta) :
    HasDerivAt (fun x : ℝ => finiteGenreFirstAngleLabel β theta_star x)
      ((β / 2) * paper_two_user_second_deriv_sign_bracket β theta_star theta /
        (Real.cos theta) ^ β) theta :=
  hasDerivAt_finiteGenreFirstAngleLabel_signBracket hβ hcos

/--
Finitegenre Step 1 local fiber control: on a supplied interval where the
source `secondderiv` bracket is strictly positive, the first printed FOC
angle label is strictly increasing. This does not assert a global
simultaneous-label fiber classification.
-/
theorem paper_finite_genre_first_angle_label_strict_mono_on_of_sign_bracket_pos
    {β theta_star a b : ℝ} (hβ : 0 < β)
    (hcos : ∀ theta, theta ∈ Set.Icc a b → 0 < Real.cos theta)
    (hbracket : ∀ theta, theta ∈ Set.Ioo a b →
      0 < paper_two_user_second_deriv_sign_bracket β theta_star theta) :
    StrictMonoOn (finiteGenreFirstAngleLabel β theta_star) (Set.Icc a b) :=
  finiteGenreFirstAngleLabel_strictMonoOn_of_signBracket_pos hβ hcos hbracket

/--
Finitegenre Step 1 local fiber control: on a supplied interval where the
source `secondderiv` bracket is strictly negative, the first printed FOC
angle label is strictly decreasing. This remains local calculus and does not
assert the source's global two-angle conclusion.
-/
theorem paper_finite_genre_first_angle_label_strict_anti_on_of_sign_bracket_neg
    {β theta_star a b : ℝ} (hβ : 0 < β)
    (hcos : ∀ theta, theta ∈ Set.Icc a b → 0 < Real.cos theta)
    (hbracket : ∀ theta, theta ∈ Set.Ioo a b →
      paper_two_user_second_deriv_sign_bracket β theta_star theta < 0) :
    StrictAntiOn (finiteGenreFirstAngleLabel β theta_star) (Set.Icc a b) :=
  finiteGenreFirstAngleLabel_strictAntiOn_of_signBracket_neg hβ hcos hbracket

/--
Finitegenre Step 1 calculus for the second printed FOC label: reflection
across the angle bisector reverses the `secondderiv`-bracket derivative sign.
This remains a local derivative identity, not a global fiber classification.
-/
theorem paper_has_deriv_at_finite_genre_second_angle_label_sign_bracket
    {β theta_star theta : ℝ} (hβ : 0 < β)
    (hcos : 0 < Real.cos (theta_star - theta)) :
    HasDerivAt (fun x : ℝ => finiteGenreSecondAngleLabel β theta_star x)
      (-(β / 2) * paper_two_user_second_deriv_sign_bracket β theta_star theta /
        (Real.cos (theta_star - theta)) ^ β) theta :=
  hasDerivAt_finiteGenreSecondAngleLabel_signBracket hβ hcos

/--
Finitegenre Step 1 Rolle bridge: equality of the first printed FOC label at
two distinct angles forces a zero of the source `secondderiv` bracket between
them. This does not turn bracket-root information into a simultaneous
two-label fiber classification.
-/
theorem paper_finite_genre_first_angle_label_eq_of_lt_exists_second_deriv_bracket_zero
    {β theta_star a b : ℝ} (hβ : 0 < β) (hab : a < b)
    (hcos : ∀ theta, theta ∈ Set.Icc a b → 0 < Real.cos theta)
    (hlabel : finiteGenreFirstAngleLabel β theta_star a =
      finiteGenreFirstAngleLabel β theta_star b) :
    ∃ c, c ∈ Set.Ioo a b ∧
      paper_two_user_second_deriv_sign_bracket β theta_star c = 0 :=
  finiteGenreFirstAngleLabel_eq_of_lt_exists_secondDerivSignBracket_zero
    hβ hab hcos hlabel

/--
Finitegenre Step 1 ordered fiber bound: in the acute above-threshold regime,
four strictly ordered angles cannot have one common first FOC label. This is
the source's valid pre-`regionscolor` root-count stage; it does not execute
the absent support-graph slope exclusion or assert the final two-angle claim.
-/
theorem paper_finite_genre_first_angle_label_not_eq_on_four_strictly_ordered
    {β theta_star theta1 theta2 theta3 theta4 : ℝ}
    (htheta_star_pos : 0 < theta_star) (htheta_star_lt_pi : theta_star < Real.pi)
    (hden : 0 < 1 - Real.cos theta_star) (hcosstar : 0 < Real.cos theta_star)
    (hphase : paper_two_user_phase_threshold theta_star < β)
    (htheta1_pos : 0 < theta1) (h12 : theta1 < theta2)
    (h23 : theta2 < theta3) (h34 : theta3 < theta4)
    (h4star : theta4 < theta_star)
    (hcos : ∀ theta, theta ∈ Set.Icc theta1 theta4 → 0 < Real.cos theta)
    (hlabel12 : finiteGenreFirstAngleLabel β theta_star theta1 =
      finiteGenreFirstAngleLabel β theta_star theta2)
    (hlabel23 : finiteGenreFirstAngleLabel β theta_star theta2 =
      finiteGenreFirstAngleLabel β theta_star theta3)
    (hlabel34 : finiteGenreFirstAngleLabel β theta_star theta3 =
      finiteGenreFirstAngleLabel β theta_star theta4) : False :=
  finiteGenreFirstAngleLabel_not_eq_on_four_strictly_ordered_of_phaseThreshold_lt_beta
    htheta_star_pos htheta_star_lt_pi hden hcosstar hphase htheta1_pos
    h12 h23 h34 h4star hcos hlabel12 hlabel23 hlabel34

/--
Finitegenre Step 1 conditional two-angle reduction: three strictly ordered
common first-label angles are impossible once the middle genre has the
nonpositive `secondderiv` bracket that a valid `regionscolor` support-graph
argument would provide. This theorem leaves that graph construction explicit.
-/
theorem paper_finite_genre_first_angle_label_not_eq_on_three_strictly_ordered_of_middle_bracket_nonpos
    {β theta_star theta1 theta2 theta3 : ℝ}
    (htheta_star_pos : 0 < theta_star) (htheta_star_lt_pi : theta_star < Real.pi)
    (hden : 0 < 1 - Real.cos theta_star) (hcosstar : 0 < Real.cos theta_star)
    (hphase : paper_two_user_phase_threshold theta_star < β)
    (htheta1_pos : 0 < theta1) (h12 : theta1 < theta2)
    (h23 : theta2 < theta3) (h3star : theta3 < theta_star)
    (hcos : ∀ theta, theta ∈ Set.Icc theta1 theta3 → 0 < Real.cos theta)
    (hlabel12 : finiteGenreFirstAngleLabel β theta_star theta1 =
      finiteGenreFirstAngleLabel β theta_star theta2)
    (hlabel23 : finiteGenreFirstAngleLabel β theta_star theta2 =
      finiteGenreFirstAngleLabel β theta_star theta3)
    (hbracket2 : paper_two_user_second_deriv_sign_bracket β theta_star theta2 ≤ 0) :
    False :=
  finiteGenreFirstAngleLabel_not_eq_on_three_strictly_ordered_of_phaseThreshold_lt_beta
    htheta_star_pos htheta_star_lt_pi hden hcosstar hphase htheta1_pos h12 h23
    h3star hcos hlabel12 hlabel23 hbracket2

/--
Finitegenre Step 1, composed `regionscolor` form: three strictly ordered
common first-label angles are impossible once the middle support ray has
positive slope and satisfies the source's graph-Hessian condition. The theorem
does not infer those support facts from C1--C3.
-/
theorem paper_finite_genre_first_angle_label_not_eq_on_three_strictly_ordered_of_middle_regionscolor
    {α β theta_star theta1 theta2 theta3 r slope : ℝ}
    (htheta_star_pos : 0 < theta_star) (htheta_star_lt_pi : theta_star < Real.pi)
    (hden : 0 < 1 - Real.cos theta_star) (hcosstar : 0 < Real.cos theta_star)
    (hphase : paper_two_user_phase_threshold theta_star < β)
    (htheta1_pos : 0 < theta1) (h12 : theta1 < theta2)
    (h23 : theta2 < theta3) (h3star : theta3 < theta_star)
    (hcos : ∀ theta, theta ∈ Set.Icc theta1 theta3 → 0 < Real.cos theta)
    (hlabel12 : finiteGenreFirstAngleLabel β theta_star theta1 =
      finiteGenreFirstAngleLabel β theta_star theta2)
    (hlabel23 : finiteGenreFirstAngleLabel β theta_star theta2 =
      finiteGenreFirstAngleLabel β theta_star theta3)
    (halpha : 0 < α) (hsin : 0 < Real.sin theta_star)
    (hNpos : 0 < r ^ 2 * (Real.sin theta_star) ^ 2)
    (hneg :
      paper_negative_semidefinite_quadratic2
        (slope *
          paper_two_user_induced_cost_cross_partial α β theta_star
            (r * Real.cos theta2) (r * Real.cos (theta_star - theta2)))
        (-(paper_two_user_induced_cost_cross_partial α β theta_star
            (r * Real.cos theta2) (r * Real.cos (theta_star - theta2))))
        (slope⁻¹ *
          paper_two_user_induced_cost_cross_partial α β theta_star
            (r * Real.cos theta2) (r * Real.cos (theta_star - theta2))))
    (hslope : 0 < slope) : False :=
  finiteGenreFirstAngleLabel_not_eq_on_three_strictly_ordered_of_middle_regionscolor
    htheta_star_pos htheta_star_lt_pi hden hcosstar hphase htheta1_pos h12 h23
    h3star hcos hlabel12 hlabel23 halpha hsin hNpos hneg hslope

/--
Finitegenre Step 1 without a preselected ordering: three distinct finite
angles with the common first label contradict a nonpositive bracket at every
candidate angle. The acute cosine interval is derived from the paper's angle
hypotheses.
-/
theorem paper_finite_genre_first_angle_label_not_eq_on_three_distinct_of_bracket_nonpos
    {ι : Type*} {β theta_star : ℝ} (angle : ι → ℝ)
    (hinjective : Function.Injective angle)
    (htheta_star_pos : 0 < theta_star) (htheta_star_lt_pi : theta_star < Real.pi)
    (hden : 0 < 1 - Real.cos theta_star) (hcosstar : 0 < Real.cos theta_star)
    (hphase : paper_two_user_phase_threshold theta_star < β)
    (hangle_pos : ∀ i, 0 < angle i) (hangle_lt : ∀ i, angle i < theta_star)
    (hlabel : ∀ i j,
      finiteGenreFirstAngleLabel β theta_star (angle i) =
        finiteGenreFirstAngleLabel β theta_star (angle j))
    (hbracket : ∀ i,
      paper_two_user_second_deriv_sign_bracket β theta_star (angle i) ≤ 0)
    {i1 i2 i3 : ι} (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) :
    False :=
  finiteGenreFirstAngleLabel_not_eq_on_three_distinct_of_bracket_nonpos
    angle hinjective htheta_star_pos htheta_star_lt_pi hden hcosstar hphase
    hangle_pos hangle_lt hlabel hbracket h12 h13 h23

/--
Finitegenre Step 1 finite-cardinality conclusion. A finite injective genre
indexing has at most two angles when the shared first label and raywise
nonpositive bracket condition are explicitly supplied.
-/
theorem paper_finite_genre_card_le_two_of_common_first_label_of_bracket_nonpos
    {ι : Type*} [Fintype ι] {β theta_star : ℝ} (angle : ι → ℝ)
    (hinjective : Function.Injective angle)
    (htheta_star_pos : 0 < theta_star) (htheta_star_lt_pi : theta_star < Real.pi)
    (hden : 0 < 1 - Real.cos theta_star) (hcosstar : 0 < Real.cos theta_star)
    (hphase : paper_two_user_phase_threshold theta_star < β)
    (hangle_pos : ∀ i, 0 < angle i) (hangle_lt : ∀ i, angle i < theta_star)
    (hlabel : ∀ i j,
      finiteGenreFirstAngleLabel β theta_star (angle i) =
        finiteGenreFirstAngleLabel β theta_star (angle j))
    (hbracket : ∀ i,
      paper_two_user_second_deriv_sign_bracket β theta_star (angle i) ≤ 0) :
    Fintype.card ι ≤ 2 :=
  finiteGenre_card_le_two_of_common_firstLabel_of_bracket_nonpos
    angle hinjective htheta_star_pos htheta_star_lt_pi hden hcosstar hphase
    hangle_pos hangle_lt hlabel hbracket

/--
Finitegenre Step 1 in the source's full local `regionscolor` form. The
negative-semidefinite Hessian and positive slope of every support ray yield
the raywise bracket premise, hence the at-most-two cardinality conclusion.
The paper's C1--C3-to-support-graph construction remains separate.
-/
theorem paper_finite_genre_card_le_two_of_common_first_label_of_regionscolor
    {ι : Type*} [Fintype ι] {α β theta_star : ℝ} (angle : ι → ℝ)
    (hinjective : Function.Injective angle)
    (htheta_star_pos : 0 < theta_star) (htheta_star_lt_pi : theta_star < Real.pi)
    (hden : 0 < 1 - Real.cos theta_star) (hcosstar : 0 < Real.cos theta_star)
    (hphase : paper_two_user_phase_threshold theta_star < β)
    (hangle_pos : ∀ i, 0 < angle i) (hangle_lt : ∀ i, angle i < theta_star)
    (hlabel : ∀ i j,
      finiteGenreFirstAngleLabel β theta_star (angle i) =
        finiteGenreFirstAngleLabel β theta_star (angle j))
    (halpha : 0 < α) (hsin : 0 < Real.sin theta_star)
    (hregionscolor : ∀ i, ∃ r slope : ℝ,
      0 < r ^ 2 * (Real.sin theta_star) ^ 2 ∧
      paper_negative_semidefinite_quadratic2
        (slope *
          paper_two_user_induced_cost_cross_partial α β theta_star
            (r * Real.cos (angle i)) (r * Real.cos (theta_star - angle i)))
        (-(paper_two_user_induced_cost_cross_partial α β theta_star
            (r * Real.cos (angle i)) (r * Real.cos (theta_star - angle i))))
        (slope⁻¹ *
          paper_two_user_induced_cost_cross_partial α β theta_star
            (r * Real.cos (angle i)) (r * Real.cos (theta_star - angle i))) ∧
      0 < slope) :
    Fintype.card ι ≤ 2 :=
  finiteGenre_card_le_two_of_common_firstLabel_of_regionscolor
    angle hinjective htheta_star_pos htheta_star_lt_pi hden hcosstar hphase
    hangle_pos hangle_lt hlabel halpha hsin hregionscolor

/--
Finitegenre Step 1: an injective angle indexing contained in two candidate
angle values has at most two genres. This is the cardinality consequence, not
the missing analytic classification that would provide the candidates.
-/
theorem paper_finite_genre_card_le_two_of_injective_angle_of_forall_eq_or_eq
    {ι : Type*} [Fintype ι] {angle : ι → ℝ}
    (hinjective : Function.Injective angle) (i0 i1 : ι)
    (hangle : ∀ i, angle i = angle i0 ∨ angle i = angle i1) :
    Fintype.card ι ≤ 2 :=
  finiteGenre_card_le_two_of_injective_angle_of_forall_eq_or_eq
    hinjective i0 i1 hangle

/--
Finitegenre Step 1 under an explicit analytic pair-fiber classification. The
two common FOC angle labels then force the finite genre set to have at most two
distinct angles; the source does not derive that classification from the cited
lemmas.
-/
theorem paper_finite_genre_card_le_two_of_common_label_pair_fiber
    {ι : Type*} [Fintype ι] {β theta_star : ℝ} (angle : ι → ℝ)
    (hinjective : Function.Injective angle) (i0 i1 : ι)
    (hfirst : ∀ i,
      finiteGenreFirstAngleLabel β theta_star (angle i) =
        finiteGenreFirstAngleLabel β theta_star (angle i0))
    (hsecond : ∀ i,
      finiteGenreSecondAngleLabel β theta_star (angle i) =
        finiteGenreSecondAngleLabel β theta_star (angle i0))
    (hfiber : ∀ theta,
      finiteGenreFirstAngleLabel β theta_star theta =
          finiteGenreFirstAngleLabel β theta_star (angle i0) →
        finiteGenreSecondAngleLabel β theta_star theta =
          finiteGenreSecondAngleLabel β theta_star (angle i0) →
        theta = angle i0 ∨ theta = angle i1) :
    Fintype.card ι ≤ 2 :=
  finiteGenre_card_le_two_of_common_label_pair_fiber
    angle hinjective i0 i1 hfirst hsecond hfiber

/--
Conditional `finitegenre` CDF chain rule: differentiable two-genre magnitude
CDFs give the derivative of the score-rescaled weighted mixture.  This is the
left side of the source's `density1` and `density2` displays.
-/
theorem paper_has_deriv_at_two_genre_cdf_mixture
    {F1 F2 f1 f2 : ℝ → ℝ} {α1 α2 c1 c2 z : ℝ}
    (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0)
    (hF1 : HasDerivAt F1 (f1 (z / c1)) (z / c1))
    (hF2 : HasDerivAt F2 (f2 (z / c2)) (z / c2)) :
    HasDerivAt (fun w => α1 * F1 (w / c1) + α2 * F2 (w / c2))
      (α1 / c1 * f1 (z / c1) + α2 / c2 * f2 (z / c2)) z :=
  hasDerivAt_twoGenre_cdfMixture hc1 hc2 hF1 hF2

/--
Conditional `finitegenre` density equation: a local two-genre CDF mixture
identity with a power right-hand side differentiates to the displayed density
identity at a positive score.  The source’s local identity and differentiable
CDF premises remain assumptions rather than inferred consequences of C1--C3.
-/
theorem paper_two_genre_density_eq_of_eventually_eq_rpow
    {F1 F2 f1 f2 : ℝ → ℝ} {α1 α2 c1 c2 C q z : ℝ}
    (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0) (hz : 0 < z)
    (hF1 : HasDerivAt F1 (f1 (z / c1)) (z / c1))
    (hF2 : HasDerivAt F2 (f2 (z / c2)) (z / c2))
    (heq : (fun w => α1 * F1 (w / c1) + α2 * F2 (w / c2)) =ᶠ[nhds z]
      fun w => C * w ^ q) :
    α1 / c1 * f1 (z / c1) + α2 / c2 * f2 (z / c2) =
      C * (q * z ^ (q - 1)) :=
  twoGenre_density_eq_of_eventuallyEq_rpow hc1 hc2 hz hF1 hF2 heq

/--
Proposition `finitegenre`, conditional Case 1 contradiction.  The source's
rescaled density comparison is valid once its selected positive scores,
zero-outside-support fact, density nonnegativity, and coefficient inequality
are supplied.  No theorem here derives those structural inputs from C1--C3.
-/
theorem paper_two_genre_case_one_contradiction_of_density_equations
    {α1 α2 c1 c2 d1 d2 C1 C2 q z1 z2 : ℝ} {f1 f2 : ℝ → ℝ}
    (hc1 : 0 < c1) (hd1 : 0 < d1) (hz2 : 0 < z2)
    (hzscale : z1 = z2 * (c1 / d1))
    (hdensity1 :
      α1 / c1 * f1 (z1 / c1) + α2 / c2 * f2 (z1 / c2) =
        C1 * q * z1 ^ (q - 1))
    (hsecond_zero : f2 (z1 / c2) = 0)
    (hsecond_nonneg : 0 ≤ α2 / d2 * f2 (z2 / d2))
    (hdensity2 :
      α1 / d1 * f1 (z2 / d1) + α2 / d2 * f2 (z2 / d2) =
        C2 * q * z2 ^ (q - 1))
    (hq : 0 < q) (hC1 : 0 < C1) (hC : C2 ≤ C1) (hratio : 1 < c1 / d1) :
    False :=
  twoGenre_caseOne_contradiction_of_density_equations hc1 hd1 hz2 hzscale
    hdensity1 hsecond_zero hsecond_nonneg hdensity2 hq hC1 hC hratio

/--
The angle-ordering component in finitegenre Case 1: a first genre strictly
below the two-user bisector has a first/second score-coefficient ratio greater
than one, on the source's nonnegative-angle domain.
-/
theorem paper_two_genre_first_angle_cos_ratio_gt_one
    {θ θstar : ℝ}
    (hθ_nonneg : 0 ≤ θ) (hθ_pos : 0 < θ)
    (hθ_lt : θ < θstar / 2) (hθstar_le : θstar ≤ Real.pi / 2) :
    1 < Real.cos θ / Real.cos (θstar - θ) :=
  cos_div_cos_sub_gt_one_of_lt_half hθ_nonneg hθ_pos hθ_lt hθstar_le

/--
Corrected finitegenre Case-1 selection: a strict scaled-cap comparison gives
a positive first-coordinate score in its strict interior whose second-genre
rescaling is strictly above the second cap.
-/
theorem paper_exists_two_genre_case_one_off_cap_score
    {r1 r2 c1 c2 : ℝ}
    (hr2 : 0 ≤ r2) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hcap : r2 * c2 < r1 * c1) :
    ∃ z : ℝ,
      0 < z ∧ z < r1 * c1 ∧ r2 < z / c2 ∧
        0 < z / c1 ∧ z / c1 < r1 :=
  exists_twoGenre_caseOne_offCap_score hr2 hc1 hc2 hcap

/--
Paired finitegenre Case-1 score selection.  The first selected score is inside
the first magnitude range but outside the second cap; its second rescaling is
inside the second strict magnitude range.
-/
theorem paper_exists_two_genre_case_one_score_pair
    {r1 r2 c1 c2 d1 d2 : ℝ}
    (hr2 : 0 ≤ r2) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hfirst_cap : r2 * c2 < r1 * c1)
    (hsecond_cap : r1 * d1 < r2 * d2) :
    ∃ z1 z2 : ℝ,
      0 < z1 ∧ z1 < r1 * c1 ∧ r2 < z1 / c2 ∧
        0 < z1 / c1 ∧ z1 / c1 < r1 ∧
        z2 = z1 * (d1 / c1) ∧ 0 < z2 ∧ z2 < r2 * d2 ∧
          0 < z2 / d2 ∧ z2 / d2 < r2 :=
  exists_twoGenre_caseOne_score_pair hr2 hc1 hc2 hd1 hd2 hfirst_cap hsecond_cap

/--
Proposition `finitegenre`, conditional Case 2 contradiction.  The rescaled
score selection, pointwise density values, and strict coefficient comparison
are explicit because the source proof does not derive them from the displayed
interval and C1--C3.
-/
theorem paper_two_genre_case_two_contradiction_of_density_equations
    {α1 α2 c1 c2 d1 d2 C1 C2 q z1 z2 : ℝ} {f1 f2 : ℝ → ℝ}
    (hc2 : 0 < c2) (hd2 : 0 < d2) (hz1 : 0 < z1)
    (hzscale : z2 = z1 * (d2 / c2))
    (hdensity2 :
      α1 / d1 * f1 (z2 / d1) + α2 / d2 * f2 (z2 / d2) =
        C2 * q * z2 ^ (q - 1))
    (hfirst_zero : f1 (z2 / d1) = 0)
    (hfirst_nonneg : 0 ≤ α1 / c1 * f1 (z1 / c1))
    (hdensity1 :
      α1 / c1 * f1 (z1 / c1) + α2 / c2 * f2 (z1 / c2) =
        C1 * q * z1 ^ (q - 1))
    (hq : 0 < q) (hcoeff : C1 < C2 * (d2 / c2) ^ q) :
    False :=
  twoGenre_caseTwo_contradiction_of_density_equations hc2 hd2 hz1 hzscale
    hdensity2 hfirst_zero hfirst_nonneg hdensity1 hq hcoeff

/--
The final source Case-2 coefficient comparison: its displayed trigonometric
coefficient formula gives the strict root-level inequality used by the density
contradiction, on the explicit ordered-angle domain.
-/
theorem paper_two_genre_case_two_root_coefficient_lt_of_source_formula
    {c1 c2 β p θ θstar : ℝ}
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hp : 0 < p)
    (hθ_pos : 0 < θ) (hdelta_pos : 0 < θstar - θ)
    (hdelta_lt : θstar - θ < θ) (hθ_lt_half_pi : θ < Real.pi / 2)
    (hformula : c1 / c2 =
      Real.sin (θstar - θ) / Real.sin θ *
        (Real.cos (θstar - θ)) ^ (β - 1) / (Real.cos θ) ^ (β - 1)) :
    c1 ^ (1 / p) < c2 ^ (1 / p) *
      (Real.cos (θstar - θ) / Real.cos θ) ^ (β / p) :=
  twoGenre_caseTwo_root_coefficient_lt_of_source_formula hc1 hc2 hp
    hθ_pos hdelta_pos hdelta_lt hθ_lt_half_pi hformula

/--
Corrected interval-selection bridge for finitegenre Case 2.  Besides the
source's lower/upper second-score interval, it explicitly requires the upper
bound that makes division by the score ratio land inside the first range.
-/
theorem paper_exists_two_genre_case_two_rescaled_score
    {a b m r : ℝ} (ha_nonneg : 0 ≤ a) (hr : 0 < r)
    (hab : a < b) (hamr : a < m * r) :
    ∃ z : ℝ, a < z ∧ z < b ∧ 0 < z / r ∧ z / r < m :=
  exists_twoGenre_caseTwo_rescaled_score ha_nonneg hr hab hamr

/--
Paired finitegenre Case-2 selection.  The second score is above the first
radius cap after the `d1` rescaling while its `d2` rescaling remains inside the
second range; its corresponding first score is in the first strict range.
-/
theorem paper_exists_two_genre_case_two_score_pair
    {r1 r2 c1 c2 d1 d2 : ℝ}
    (hr1 : 0 ≤ r1) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hsecond_cap : r1 * d1 < r2 * d2)
    (hfirst_interior : r1 * d1 < (r1 * c1) * (d2 / c2)) :
    ∃ z1 z2 : ℝ,
      z2 = z1 * (d2 / c2) ∧
        0 < z1 ∧ 0 < z1 / c1 ∧ z1 / c1 < r1 ∧
          0 < z2 ∧ r1 < z2 / d1 ∧ 0 < z2 / d2 ∧ z2 / d2 < r2 :=
  exists_twoGenre_caseTwo_score_pair
    hr1 hc1 hc2 hd1 hd2 hsecond_cap hfirst_interior

/--
Corrected finitegenre Case-2 selection on the ordered interior-angle domain.
It constructs a second-coordinate score whose rescaling lies in the first
score range, from the source's strict endpoint relation.
-/
theorem paper_exists_two_genre_case_two_rescaled_angle_score
    {r1 b θ1 θ2 θstar : ℝ}
    (hr1 : 0 < r1) (hθ1_pos : 0 < θ1) (hθ1_lt : θ1 < θstar / 2)
    (hθ2_lt_star : θ2 < θstar) (hhalf_lt_θ2 : θstar / 2 < θ2)
    (hθstar_le : θstar ≤ Real.pi / 2)
    (hupper : r1 * Real.cos (θstar - θ1) < b) :
    ∃ z : ℝ,
      r1 * Real.cos (θstar - θ1) < z ∧ z < b ∧
        0 < z / (Real.cos (θstar - θ2) / Real.cos θ2) ∧
        z / (Real.cos (θstar - θ2) / Real.cos θ2) < r1 * Real.cos θ1 :=
  exists_twoGenre_caseTwo_rescaled_angle_score hr1 hθ1_pos hθ1_lt
    hθ2_lt_star hhalf_lt_θ2 hθstar_le hupper

/--
Finitegenre Case 1 with its zero-density input derived from a locally constant
conditional CDF and a pointwise derivative.  These remain explicit to avoid
silently replacing a.e. density information by a pointwise statement.
-/
theorem paper_two_genre_case_one_contradiction_of_cdf_eventually_eq_const
    {F2 f1 f2 : ℝ → ℝ} {α1 α2 c1 c2 d1 d2 C1 C2 q z1 z2 tail : ℝ}
    (hc1 : 0 < c1) (hd1 : 0 < d1) (hz2 : 0 < z2)
    (hzscale : z1 = z2 * (c1 / d1))
    (hdensity1 :
      α1 / c1 * f1 (z1 / c1) + α2 / c2 * f2 (z1 / c2) =
        C1 * q * z1 ^ (q - 1))
    (hF2 : HasDerivAt F2 (f2 (z1 / c2)) (z1 / c2))
    (hF2_const : F2 =ᶠ[nhds (z1 / c2)] fun _ => tail)
    (hsecond_nonneg : 0 ≤ α2 / d2 * f2 (z2 / d2))
    (hdensity2 :
      α1 / d1 * f1 (z2 / d1) + α2 / d2 * f2 (z2 / d2) =
        C2 * q * z2 ^ (q - 1))
    (hq : 0 < q) (hC1 : 0 < C1) (hC : C2 ≤ C1) (hratio : 1 < c1 / d1) :
    False :=
  twoGenre_caseOne_contradiction_of_density_equations_of_cdf_eventuallyEq_const
    hc1 hd1 hz2 hzscale hdensity1 hF2 hF2_const hsecond_nonneg hdensity2
    hq hC1 hC hratio

/--
Finitegenre Case 1 with local CDF constancy obtained from a probability law
whose topological support lies below the displayed second-coordinate cap.  The
chosen pointwise CDF derivative remains a visible premise.
-/
theorem paper_two_genre_case_one_contradiction_of_cdf_support
    {F2 f1 f2 : ℝ → ℝ} {μ2 : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure μ2]
    {α1 α2 c1 c2 d1 d2 C1 C2 q z1 z2 r2 : ℝ}
    (hc1 : 0 < c1) (hd1 : 0 < d1) (hz2 : 0 < z2)
    (hzscale : z1 = z2 * (c1 / d1))
    (hdensity1 :
      α1 / c1 * f1 (z1 / c1) + α2 / c2 * f2 (z1 / c2) =
        C1 * q * z1 ^ (q - 1))
    (hF2 : F2 = AppliedModelingLib.Probability.lowerCDFMass μ2)
    (hsupp2 : μ2.support ⊆ Set.Iic r2)
    (houtside : r2 < z1 / c2)
    (hF2_deriv : HasDerivAt F2 (f2 (z1 / c2)) (z1 / c2))
    (hsecond_nonneg : 0 ≤ α2 / d2 * f2 (z2 / d2))
    (hdensity2 :
      α1 / d1 * f1 (z2 / d1) + α2 / d2 * f2 (z2 / d2) =
        C2 * q * z2 ^ (q - 1))
    (hq : 0 < q) (hC1 : 0 < C1) (hC : C2 ≤ C1) (hratio : 1 < c1 / d1) :
    False :=
  twoGenre_caseOne_contradiction_of_density_equations_of_cdf_support
    hc1 hd1 hz2 hzscale hdensity1 hF2 hsupp2 houtside hF2_deriv hsecond_nonneg
    hdensity2 hq hC1 hC hratio

/--
Finitegenre Case 2 with the zero first-density input obtained from a CDF whose
probability-law support lies below the displayed cap.  Its chosen pointwise
derivative remains a premise.
-/
theorem paper_two_genre_case_two_contradiction_of_cdf_support
    {F1 f1 f2 : ℝ → ℝ} {μ1 : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure μ1]
    {α1 α2 c1 c2 d1 d2 C1 C2 q z1 z2 r1 : ℝ}
    (hc2 : 0 < c2) (hd2 : 0 < d2) (hz1 : 0 < z1)
    (hzscale : z2 = z1 * (d2 / c2))
    (hdensity2 :
      α1 / d1 * f1 (z2 / d1) + α2 / d2 * f2 (z2 / d2) =
        C2 * q * z2 ^ (q - 1))
    (hF1 : F1 = AppliedModelingLib.Probability.lowerCDFMass μ1)
    (hsupp1 : μ1.support ⊆ Set.Iic r1)
    (houtside : r1 < z2 / d1)
    (hF1_deriv : HasDerivAt F1 (f1 (z2 / d1)) (z2 / d1))
    (hfirst_nonneg : 0 ≤ α1 / c1 * f1 (z1 / c1))
    (hdensity1 :
      α1 / c1 * f1 (z1 / c1) + α2 / c2 * f2 (z1 / c2) =
        C1 * q * z1 ^ (q - 1))
    (hq : 0 < q) (hcoeff : C1 < C2 * (d2 / c2) ^ q) :
    False :=
  twoGenre_caseTwo_contradiction_of_density_equations_of_cdf_support
    hc2 hd2 hz1 hzscale hdensity2 hF1 hsupp1 houtside hF1_deriv hfirst_nonneg
    hdensity1 hq hcoeff

/--
Finitegenre Case 1 using the canonical `deriv` representative of a selected
CDF.  The support cap supplies only its off-cap zero value; the density
equations and the remaining nonnegative term stay explicit.
-/
theorem paper_two_genre_case_one_contradiction_of_cdf_support_deriv
    {F2 f1 : ℝ → ℝ} {μ2 : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure μ2]
    {α1 α2 c1 c2 d1 d2 C1 C2 q z1 z2 r2 : ℝ}
    (hc1 : 0 < c1) (hd1 : 0 < d1) (hz2 : 0 < z2)
    (hzscale : z1 = z2 * (c1 / d1))
    (hdensity1 :
      α1 / c1 * f1 (z1 / c1) + α2 / c2 * deriv F2 (z1 / c2) =
        C1 * q * z1 ^ (q - 1))
    (hF2 : F2 = AppliedModelingLib.Probability.lowerCDFMass μ2)
    (hsupp2 : μ2.support ⊆ Set.Iic r2)
    (houtside : r2 < z1 / c2)
    (hsecond_nonneg : 0 ≤ α2 / d2 * deriv F2 (z2 / d2))
    (hdensity2 :
      α1 / d1 * f1 (z2 / d1) + α2 / d2 * deriv F2 (z2 / d2) =
        C2 * q * z2 ^ (q - 1))
    (hq : 0 < q) (hC1 : 0 < C1) (hC : C2 ≤ C1) (hratio : 1 < c1 / d1) :
    False :=
  twoGenre_caseOne_contradiction_of_cdf_support_deriv
    hc1 hd1 hz2 hzscale hdensity1 hF2 hsupp2 houtside hsecond_nonneg hdensity2
    hq hC1 hC hratio

/--
Finitegenre Case 2 using the canonical `deriv` representative of its selected
CDF, with the same explicit density-equation and nonnegativity premises.
-/
theorem paper_two_genre_case_two_contradiction_of_cdf_support_deriv
    {F1 f2 : ℝ → ℝ} {μ1 : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure μ1]
    {α1 α2 c1 c2 d1 d2 C1 C2 q z1 z2 r1 : ℝ}
    (hc2 : 0 < c2) (hd2 : 0 < d2) (hz1 : 0 < z1)
    (hzscale : z2 = z1 * (d2 / c2))
    (hdensity2 :
      α1 / d1 * deriv F1 (z2 / d1) + α2 / d2 * f2 (z2 / d2) =
        C2 * q * z2 ^ (q - 1))
    (hF1 : F1 = AppliedModelingLib.Probability.lowerCDFMass μ1)
    (hsupp1 : μ1.support ⊆ Set.Iic r1)
    (houtside : r1 < z2 / d1)
    (hfirst_nonneg : 0 ≤ α1 / c1 * deriv F1 (z1 / c1))
    (hdensity1 :
      α1 / c1 * deriv F1 (z1 / c1) + α2 / c2 * f2 (z1 / c2) =
        C1 * q * z1 ^ (q - 1))
    (hq : 0 < q) (hcoeff : C1 < C2 * (d2 / c2) ^ q) :
    False :=
  twoGenre_caseTwo_contradiction_of_cdf_support_deriv
    hc2 hd2 hz1 hzscale hdensity2 hF1 hsupp1 houtside hfirst_nonneg hdensity1
    hq hcoeff

/--
Finitegenre Case 1 with its remaining canonical-CDF derivative term
nonnegative by CDF monotonicity, a nonnegative genre weight, and a positive
rescaling factor.
-/
theorem paper_two_genre_case_one_contradiction_of_cdf_support_deriv_nonneg
    {F2 f1 : ℝ → ℝ} {μ2 : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure μ2]
    {α1 α2 c1 c2 d1 d2 C1 C2 q z1 z2 r2 : ℝ}
    (hc1 : 0 < c1) (hd1 : 0 < d1) (hd2 : 0 < d2) (hα2 : 0 ≤ α2)
    (hz2 : 0 < z2) (hzscale : z1 = z2 * (c1 / d1))
    (hdensity1 :
      α1 / c1 * f1 (z1 / c1) + α2 / c2 * deriv F2 (z1 / c2) =
        C1 * q * z1 ^ (q - 1))
    (hF2 : F2 = AppliedModelingLib.Probability.lowerCDFMass μ2)
    (hsupp2 : μ2.support ⊆ Set.Iic r2)
    (houtside : r2 < z1 / c2)
    (hdensity2 :
      α1 / d1 * f1 (z2 / d1) + α2 / d2 * deriv F2 (z2 / d2) =
        C2 * q * z2 ^ (q - 1))
    (hq : 0 < q) (hC1 : 0 < C1) (hC : C2 ≤ C1) (hratio : 1 < c1 / d1) :
    False :=
  twoGenre_caseOne_contradiction_of_cdf_support_deriv_nonneg
    hc1 hd1 hd2 hα2 hz2 hzscale hdensity1 hF2 hsupp2 houtside hdensity2
    hq hC1 hC hratio

/--
Finitegenre Case 2 with its remaining canonical-CDF derivative term
nonnegative by CDF monotonicity, a nonnegative genre weight, and a positive
rescaling factor.
-/
theorem paper_two_genre_case_two_contradiction_of_cdf_support_deriv_nonneg
    {F1 f2 : ℝ → ℝ} {μ1 : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure μ1]
    {α1 α2 c1 c2 d1 d2 C1 C2 q z1 z2 r1 : ℝ}
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hd2 : 0 < d2) (hα1 : 0 ≤ α1)
    (hz1 : 0 < z1) (hzscale : z2 = z1 * (d2 / c2))
    (hdensity2 :
      α1 / d1 * deriv F1 (z2 / d1) + α2 / d2 * f2 (z2 / d2) =
        C2 * q * z2 ^ (q - 1))
    (hF1 : F1 = AppliedModelingLib.Probability.lowerCDFMass μ1)
    (hsupp1 : μ1.support ⊆ Set.Iic r1)
    (houtside : r1 < z2 / d1)
    (hdensity1 :
      α1 / c1 * deriv F1 (z1 / c1) + α2 / c2 * f2 (z1 / c2) =
        C1 * q * z1 ^ (q - 1))
    (hq : 0 < q) (hcoeff : C1 < C2 * (d2 / c2) ^ q) :
    False :=
  twoGenre_caseTwo_contradiction_of_cdf_support_deriv_nonneg
    hc1 hc2 hd2 hα1 hz1 hzscale hdensity2 hF1 hsupp1 houtside hdensity1 hq
    hcoeff

/--
Finitegenre Case 1 assembled under explicit two-range density equations,
probability-CDF support, positive scales, nonnegative mixture weight, and the
two strict scaled-cap inequalities.  This is not a C1--C3 consequence.
-/
theorem paper_two_genre_case_one_contradiction_of_interior_density_equations
    {F2 f1 : ℝ → ℝ} {μ2 : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure μ2]
    {α1 α2 c1 c2 d1 d2 C1 C2 q r1 r2 : ℝ}
    (hr2 : 0 ≤ r2) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hα2 : 0 ≤ α2)
    (hfirst_cap : r2 * c2 < r1 * c1)
    (hsecond_cap : r1 * d1 < r2 * d2)
    (hdensity1 : ∀ z : ℝ, 0 < z / c1 → z / c1 < r1 →
      α1 / c1 * f1 (z / c1) + α2 / c2 * deriv F2 (z / c2) =
        C1 * q * z ^ (q - 1))
    (hF2 : F2 = AppliedModelingLib.Probability.lowerCDFMass μ2)
    (hsupp2 : μ2.support ⊆ Set.Iic r2)
    (hdensity2 : ∀ z : ℝ, 0 < z / d2 → z / d2 < r2 →
      α1 / d1 * f1 (z / d1) + α2 / d2 * deriv F2 (z / d2) =
        C2 * q * z ^ (q - 1))
    (hq : 0 < q) (hC1 : 0 < C1) (hC : C2 ≤ C1) (hratio : 1 < c1 / d1) :
    False :=
  twoGenre_caseOne_contradiction_of_interior_density_equations
    hr2 hc1 hc2 hd1 hd2 hα2 hfirst_cap hsecond_cap hdensity1 hF2 hsupp2
    hdensity2 hq hC1 hC hratio

/--
Finitegenre Case 2 assembled under explicit strict-range density equations,
probability-CDF support, positive scales, nonnegative mixture weight, and the
corrected two-score interval premises.  This is not a C1--C3 consequence.
-/
theorem paper_two_genre_case_two_contradiction_of_interior_density_equations
    {F1 f2 : ℝ → ℝ} {μ1 : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure μ1]
    {α1 α2 c1 c2 d1 d2 C1 C2 q r1 r2 : ℝ}
    (hr1 : 0 ≤ r1) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hα1 : 0 ≤ α1)
    (hsecond_cap : r1 * d1 < r2 * d2)
    (hfirst_interior : r1 * d1 < (r1 * c1) * (d2 / c2))
    (hdensity2 : ∀ z : ℝ, 0 < z / d2 → z / d2 < r2 →
      α1 / d1 * deriv F1 (z / d1) + α2 / d2 * f2 (z / d2) =
        C2 * q * z ^ (q - 1))
    (hF1 : F1 = AppliedModelingLib.Probability.lowerCDFMass μ1)
    (hsupp1 : μ1.support ⊆ Set.Iic r1)
    (hdensity1 : ∀ z : ℝ, 0 < z / c1 → z / c1 < r1 →
      α1 / c1 * deriv F1 (z / c1) + α2 / c2 * f2 (z / c2) =
        C1 * q * z ^ (q - 1))
    (hq : 0 < q) (hcoeff : C1 < C2 * (d2 / c2) ^ q) :
    False :=
  twoGenre_caseTwo_contradiction_of_interior_density_equations
    hr1 hc1 hc2 hd1 hd2 hα1 hsecond_cap hfirst_interior hdensity2 hF1 hsupp1
    hdensity1 hq hcoeff

/--
Finitegenre Case 2 on the source's ordered-angle domain.  The angle hypotheses
prove the corrected score-selection inequality; the CDF/support/density and
coefficient package stays explicit rather than being inferred from C1--C3.
-/
theorem paper_two_genre_case_two_contradiction_of_ordered_angle_density_equations
    {F1 f2 : ℝ → ℝ} {μ1 : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure μ1]
    {α1 α2 C1 C2 q r1 r2 θ1 θ2 θstar : ℝ}
    (hr1 : 0 < r1) (hθ1_pos : 0 < θ1) (hθ1_lt : θ1 < θstar / 2)
    (hθ2_lt_star : θ2 < θstar) (hhalf_lt_θ2 : θstar / 2 < θ2)
    (hθstar_le : θstar ≤ Real.pi / 2)
    (hsecond_cap : r1 * Real.cos (θstar - θ1) <
      r2 * Real.cos (θstar - θ2))
    (hα1 : 0 ≤ α1)
    (hdensity2 : ∀ z : ℝ,
      0 < z / Real.cos (θstar - θ2) → z / Real.cos (θstar - θ2) < r2 →
        α1 / Real.cos (θstar - θ1) * deriv F1 (z / Real.cos (θstar - θ1)) +
          α2 / Real.cos (θstar - θ2) * f2 (z / Real.cos (θstar - θ2)) =
            C2 * q * z ^ (q - 1))
    (hF1 : F1 = AppliedModelingLib.Probability.lowerCDFMass μ1)
    (hsupp1 : μ1.support ⊆ Set.Iic r1)
    (hdensity1 : ∀ z : ℝ,
      0 < z / Real.cos θ1 → z / Real.cos θ1 < r1 →
        α1 / Real.cos θ1 * deriv F1 (z / Real.cos θ1) +
          α2 / Real.cos θ2 * f2 (z / Real.cos θ2) =
            C1 * q * z ^ (q - 1))
    (hq : 0 < q)
    (hcoeff : C1 < C2 *
      (Real.cos (θstar - θ2) / Real.cos θ2) ^ q) :
    False :=
  twoGenre_caseTwo_contradiction_of_ordered_angle_density_equations
    hr1 hθ1_pos hθ1_lt hθ2_lt_star hhalf_lt_θ2 hθstar_le hsecond_cap hα1
    hdensity2 hF1 hsupp1 hdensity1 hq hcoeff

/--
Proposition `finitegenre`: above the two-user phase threshold, a Nash law with
the source's finite conditional radial decomposition cannot have finitely many
distinct nonzero support genres.  Strict interiority of every nonzero support
value is derived from the represented angle rays; the theorem records the
remaining pointwise C2 bridge used for the printed FOC argument.
-/
abbrev paper_no_finite_genre_conditional_norm_law_of_norm_rpow_cost_nash_above_phase :=
  @no_finiteGenreConditionalNormLaw_of_normRpowCostNash_abovePhase

/--
Proposition `finitegenre` under the source's principal nonnegative polar-angle
representation.  C1 derives the closed angle cone; finite CDF arguments rule
out acute endpoints, and C2 score-law absolute continuity rules out the
orthogonal endpoints without dividing by a zero cosine.
-/
abbrev paper_no_finite_genre_conditional_norm_law_of_norm_rpow_cost_nash_above_phase_principal_angle_chart :=
  @no_finiteGenreConditionalNormLaw_of_normRpowCostNash_abovePhase_of_principalAngleChart

/--
Proposition `finitegenre` with its C2 assumption stated directly in the
source's score-space language: each marginal score CDF is twice continuously
differentiable at every point of its own support.  The proof transports that
regularity to canonical value coordinates by continuous projection; the
finite conditional law itself supplies the exact nonzero genre set.
-/
abbrev paper_no_finite_genre_conditional_norm_law_of_norm_rpow_cost_nash_above_phase_principal_angle_chart_of_score_cdf_cont_diff_at_on_support :=
  @no_finiteGenreConditionalNormLaw_of_normRpowCostNash_abovePhase_of_principalAngleChart_of_scoreCdfContDiffAtOnSupport

/--
Proposition `finitegenre` in the source's arbitrary-dimensional model.  For
two nonnegative unit users, the proof derives the polar chart, exact
equilibrium-support cost, cone-preserving canonical Nash transport, and score
identification from the source primitives; none is retained as an additional
assumption.
-/
abbrev paper_no_finite_genre_conditional_norm_law_any_dim_of_norm_rpow_cost_nash_above_phase :=
  @no_finiteGenreConditionalNormLawAnyDim_of_normRpowCostNash_abovePhase

/--
Canonical two-dimensional form of Proposition `uniqueness`, with C2 stated on
the two marginal score supports.  Nash, the phase inequality, absolute
continuity, and C2 derive the complete boundary-safe support geometry; no
strict-cone or positive-density premise remains.
-/
abbrev paper_two_user_nonzero_support_genres_eq_singleton_of_scaled_norm_rpow_cost_nash_below_phase_of_score_cdf_cont_diff_at_on_support :=
  @canonicalTwoUser_nonzeroSupportGenres_eq_singleton_of_scaledNormRpowCostNash_belowPhase

/--
Arbitrary-dimensional unit-user form of Proposition `uniqueness`.  The proof
uses a cone-preserving canonicalization and derives the original support genre
from the canonical diagonal, rather than rotating the nonnegative action cone.
-/
abbrev paper_two_user_nonzero_support_genres_eq_singleton_of_scaled_norm_rpow_cost_nash_below_phase_any_dim :=
  @twoUser_nonzeroSupportGenres_eq_singleton_of_scaledNormRpowCostNash_belowPhase_any_dim

/--
Original-user form of Proposition `uniqueness`: the two users may have
arbitrary positive Euclidean magnitudes.  User normalization, score-law
absolute continuity, and support-local C2 regularity are all transported in
the theorem rather than assumed after normalization.
-/
abbrev paper_two_user_nonzero_support_genres_eq_singleton_of_scaled_norm_rpow_cost_nash_below_phase_raw_users :=
  @twoUser_nonzeroSupportGenres_eq_singleton_of_scaledNormRpowCostNash_belowPhase_raw_users

/--
Source-shaped equal-population form of Proposition `uniqueness`, with `K`
copies of each original user type and the unscaled `l2^β` cost.  Equal
replication is eliminated by its exact payoff identity, so this statement has
no additional population-normalization premise.
-/
abbrev paper_two_population_nonzero_support_genres_eq_singleton_of_norm_rpow_cost_nash_below_phase_raw_users :=
  @twoPopulation_nonzeroSupportGenres_eq_singleton_of_normRpowCostNash_belowPhase_raw_users

/--
Corrected generic below-threshold uniqueness with the exact additional
non-flatness hypotheses needed to rule out canonical cone-boundary support.
In particular, C2 of the raw CDF is not silently treated as positive density.
-/
abbrev paper_two_user_nonzero_support_genres_eq_singleton_below_phase_of_positive_lower_boundary_reward_deriv :=
  @canonicalTwoUser_nonzeroSupportGenres_eq_singleton_of_scaledNormRpowCostNash_of_phase_of_positiveLowerBoundaryRewardDeriv

/--
Orthogonal canonical boundary repair: strictly positive iid-maximum reward
derivatives at zero rule out either zero-score ray of a nonzero support value.
This is an explicit corrected regularity premise, not a consequence claimed
from the source's C2 condition alone.
-/
abbrev paper_canonical_two_user_strict_interior_of_orthogonal_nash_of_positive_reward_deriv_at_zero :=
  @canonicalTwoUser_strictInterior_of_scaledNormRpowCostNash_of_orthogonal_of_positiveRewardDerivAtZero

/--
Below the phase threshold, the source's finite conditional radial-law
interpretation and principal nonnegative angle chart derive strict-cone
support automatically and hence force the unique canonical nonzero genre.
-/
abbrev paper_canonical_two_user_nonzero_support_genres_eq_singleton_of_finite_genre_conditional_norm_law_below_phase :=
  @canonicalTwoUser_nonzeroSupportGenres_eq_singleton_of_finiteGenreConditionalNormLaw_belowPhase

/--
Corrected canonical two-user statement of Theorem `phasetransitionformal`.
The below-threshold branch derives its boundary-safe support geometry from the
source hypotheses.  The above-threshold branch uses the concrete finite
conditional radial-law representation behind the source's finite-genre
wording.
-/
abbrev paper_canonical_two_user_corrected_phase_transition :=
  @canonicalTwoUser_corrected_phaseTransition

end JGS23SupplySideRecommenderSystems
