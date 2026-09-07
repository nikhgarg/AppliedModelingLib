import MSVV07AdWords.AdWordsExtensions
import MSVV07AdWords.AdWordsBatch
import MSVV07AdWords.AdWordsLowerBound

/-!
# Paper-Facing Theorems: AdWords and Generalized Online Matching

This file is the public theorem interface for the Mehta-Saberi-Vazirani-Vazirani
AdWords formalization. Detailed finite assignment, Balance/MSVV choice, and
LP-duality lemmas live in `AdWords.lean`.
-/

namespace AppliedModelingLib
namespace Online

/--
The empty AdWords assignment is budget-feasible when budgets are nonnegative.
-/
theorem paper_adwords_empty_assignment_feasible
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    I.Feasible (AdWordsInstance.emptyAssignment :
      AdWordsInstance.Assignment Advertiser Query) := by
  exact AdWordsInstance.emptyAssignment_feasible I hbudget

set_option linter.unusedFintypeInType false in
/--
Finite AdWords instances have an offline optimum assignment.
-/
theorem paper_adwords_offline_optimum_exists
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    ∃ A : AdWordsInstance.Assignment Advertiser Query,
      I.IsOptimalAssignment A := by
  exact AdWordsInstance.exists_optimalAssignment I hbudget

/--
Every feasible AdWords assignment earns at most total advertiser budget.
-/
theorem paper_adwords_revenue_le_total_budget_of_feasible
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : AdWordsInstance.Assignment Advertiser Query)
    (hfeasible : I.Feasible A) :
    I.revenue A ≤ ∑ a : Advertiser, I.budget a := by
  exact AdWordsInstance.revenue_le_totalBudget_of_feasible I A hfeasible

/--
Weak duality for the standard finite AdWords LP: any nonnegative dual variables
covering each bid upper-bound the revenue of every feasible assignment.
-/
theorem paper_adwords_lp_weak_duality
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : AdWordsInstance.Assignment Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hfeasible : I.Feasible A)
    (hdual : I.DualFeasible alpha beta) :
    I.revenue A ≤ I.dualObjective alpha beta := by
  exact AdWordsInstance.revenue_le_dualObjective_of_dualFeasible
    I A alpha beta hfeasible hdual

/--
Integral AdWords assignments embed as feasible `0/1` fractional LP solutions.
-/
theorem paper_adwords_integral_assignment_fractional_feasible
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : AdWordsInstance.Assignment Advertiser Query)
    (hfeasible : I.Feasible A) :
    I.FractionalFeasible (AdWordsInstance.assignmentFraction A) := by
  exact AdWordsInstance.assignmentFraction_fractionalFeasible_of_feasible
    I A hfeasible

/--
Fractional weak duality for the standard AdWords LP.
-/
theorem paper_adwords_fractional_lp_weak_duality
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (X : AdWordsInstance.FractionalAssignment Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hfeasible : I.FractionalFeasible X)
    (hdual : I.DualFeasible alpha beta) :
    I.fractionalRevenue X ≤ I.dualObjective alpha beta := by
  exact AdWordsInstance.fractionalRevenue_le_dualObjective_of_dualFeasible
    I X alpha beta hfeasible hdual

/--
Dual-feasibility builder in the form used by the Balance/MSVV analysis: it is
enough to lower-bound every query dual `beta q` by the advertiser slack score
`bid a q * (1 - alpha a)`.
-/
theorem paper_adwords_dual_feasible_of_slack_score_bound
    {Advertiser Query : Type*}
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (halpha : ∀ a, 0 ≤ alpha a)
    (hbeta : ∀ q, 0 ≤ beta q)
    (hcover : ∀ a q, I.slackScore alpha a q ≤ beta q) :
    I.DualFeasible alpha beta := by
  exact AdWordsInstance.dualFeasible_of_slackScore_le_beta
    I alpha beta halpha hbeta hcover

/--
Finite max-slack construction of query duals: for any nonnegative advertiser
dual `alpha`, setting each `beta q` to the nonnegative maximum slack score over
advertisers gives a dual-feasible AdWords LP solution.
-/
theorem paper_adwords_dual_feasible_max_slack_beta
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ)
    (halpha : ∀ a, 0 ≤ alpha a) :
    I.DualFeasible alpha (I.maxSlackBeta alpha) := by
  exact AdWordsInstance.dualFeasible_maxSlackBeta I alpha halpha

/--
The MSVV assignment-induced advertiser duals, paired with finite max-slack
query duals, form a dual-feasible AdWords LP solution.
-/
theorem paper_adwords_dual_feasible_msvv_assignment
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : AdWordsInstance.Assignment Advertiser Query) :
    I.DualFeasible (I.msvvAlphaFromAssignment A)
      (I.maxSlackBeta (I.msvvAlphaFromAssignment A)) := by
  exact AdWordsInstance.dualFeasible_msvvAssignment I A

/--
The normalized MSVV assignment-induced advertiser duals, paired with finite
max-slack query duals, form a dual-feasible AdWords LP solution. This is the
dual-fitting normalization whose initial advertiser dual value is zero.
-/
theorem paper_adwords_dual_feasible_msvv_normalized_assignment
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (A : AdWordsInstance.Assignment Advertiser Query) :
    I.DualFeasible (I.msvvNormalizedAlphaFromAssignment A)
      (I.maxSlackBeta (I.msvvNormalizedAlphaFromAssignment A)) := by
  exact AdWordsInstance.dualFeasible_msvvNormalizedAssignment
    I hbid hbudget A

/--
If some advertiser can still accept a query, a Balance/MSVV scaled-bid maximizer
exists for that query.
-/
theorem paper_adwords_balance_choice_exists
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : AdWordsInstance.Assignment Advertiser Query) (q : Query)
    (h : ∃ a, I.CanAssign A q a) :
    ∃ a, I.IsBalanceChoice A q a := by
  exact AdWordsInstance.exists_balanceChoice_of_exists_canAssign I A q h

/--
Any feasible online choice rule preserves AdWords budget feasibility over a
finite query history.
-/
theorem paper_adwords_run_assignment_feasible
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) :
    I.Feasible (I.runAssignment rule history) := by
  exact AdWordsInstance.runAssignment_feasible I hbudget rule hrule history

/--
The canonical Balance/MSVV scaled-bid choice rule preserves budget feasibility
over a finite query history.
-/
theorem paper_adwords_balance_run_assignment_feasible
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query) :
    I.Feasible (I.runAssignment I.balanceChoiceRule history) := by
  exact AdWordsInstance.balanceRunAssignment_feasible I hbudget history

/--
The Balance/MSVV run never assigns a query identifier that does not appear in
the input history.
-/
theorem paper_adwords_balance_assignment_assigned_only_from_history
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query) {q : Query} {a : Advertiser}
    (hassigned : I.runAssignment I.balanceChoiceRule history q = some a) :
    q ∈ AdWordsInstance.historyFinset history := by
  exact AdWordsInstance.balanceRunAssignment_assigned_mem_historyFinset
    I hbudget history hassigned

/--
Spend is monotone along any feasible online AdWords run when bids are
nonnegative.
-/
theorem paper_adwords_spend_monotone_over_history
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (a : Advertiser) :
    I.spend S.assignment a ≤
      I.spend
        (I.runHistoryStateFrom rule S history).assignment a := by
  exact AdWordsInstance.spend_le_runHistoryStateFrom_spend
    I hbid rule hrule history S hS a

/--
Revenue accounting for online runs: final revenue equals the recursive sum of
per-step revenue increments from the initial state.
-/
theorem paper_adwords_run_revenue_eq_history_revenue_charge
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) :
    I.revenue (I.runAssignment rule history) =
      AdWordsInstance.historyRevenueChargeFrom I rule
        AdWordsInstance.initialHistoryState history := by
  exact AdWordsInstance.revenue_runAssignment_eq_historyRevenueChargeFrom
    I hbudget rule hrule history

/--
The recursive Balance/MSVV charge is bounded by the actual revenue earned by
the same online run.
-/
theorem paper_adwords_balance_charge_le_run_revenue
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query) :
    AdWordsInstance.historyBalanceChargeFrom I I.balanceChoiceRule
        AdWordsInstance.initialHistoryState history ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) := by
  exact AdWordsInstance.historyBalanceChargeFrom_initial_le_runAssignment_revenue
    I hbid hbudget I.balanceChoiceRule
    (AdWordsInstance.balanceChoiceRule_feasible I) history

/--
MSVV monotonicity bridge: final assignment-induced slack scores are bounded by
the earlier Balance score at any prior state in the same run.
-/
theorem paper_adwords_final_slack_score_le_initial_balance_score
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a) :
    I.slackScore
        (I.msvvAlphaFromAssignment
          (I.runHistoryStateFrom rule S history).assignment) a q ≤
      I.balanceScore S.assignment a q := by
  exact AdWordsInstance.final_slackScore_le_initial_balanceScore
    I hbid rule hrule history S hS a q hbudget

/--
Non-exhausted-query beta charge: if every advertiser can still accept query
`q`, then the final max-slack query dual is bounded by the Balance score of the
advertiser selected at that state.
-/
theorem paper_adwords_max_slack_beta_le_balance_score_of_all_can_assign
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (q : Query) (chosen : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen)
    (hall : ∀ a, I.CanAssign S.assignment q a) :
    I.maxSlackBeta
        (I.msvvAlphaFromAssignment
          (I.runHistoryStateFrom rule S history).assignment) q ≤
      I.balanceScore S.assignment chosen q := by
  exact AdWordsInstance.maxSlackBeta_runHistoryStateFrom_le_balanceScore_of_all_canAssign
    I hbid hbudget rule hrule history S hS q chosen hchoice hall

/--
Normalized non-exhausted-query beta charge: using the normalized assignment
dual, the scaled final max-slack query dual is bounded by the Balance score of
the advertiser selected at that state.
-/
theorem paper_adwords_msvv_ratio_mul_normalized_max_slack_beta_le_balance_score_of_all_can_assign
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (q : Query) (chosen : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen)
    (hall : ∀ a, I.CanAssign S.assignment q a) :
    AdWordsInstance.msvvRatio *
        I.maxSlackBeta
          (I.msvvNormalizedAlphaFromAssignment
            (I.runHistoryStateFrom rule S history).assignment) q ≤
      I.balanceScore S.assignment chosen q := by
  exact AdWordsInstance.msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_balanceScore_of_all_canAssign
    I hbid hbudget rule hrule history S hS q chosen hchoice hall

/--
Exhausted-advertiser alpha charge: if advertiser `a` cannot accept query `q`
at an earlier online state, then under `ε`-small bids the final MSVV
assignment-induced advertiser dual is at least `exp (-ε)`.
-/
theorem paper_adwords_blocked_advertiser_final_alpha_ge_exp_neg_epsilon
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hsmall : I.SmallBids ε) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a)
    (hnot : ¬ I.CanAssign S.assignment q a) :
    Real.exp (-ε) ≤
      I.msvvAlphaFromAssignment
        (I.runHistoryStateFrom rule S history).assignment a := by
  exact AdWordsInstance.final_msvvAlphaFromAssignment_ge_exp_neg_epsilon_of_not_canAssign
    I hbid rule hrule history S hS hsmall a q hbudget hnot

/--
Exhausted-advertiser slack charge: a blocked advertiser contributes at most
`bid * (1 - exp (-ε))` to the final assignment-induced slack score.
-/
theorem paper_adwords_blocked_advertiser_final_slack_score_le_error
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hsmall : I.SmallBids ε) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a)
    (hnot : ¬ I.CanAssign S.assignment q a) :
    I.slackScore
        (I.msvvAlphaFromAssignment
          (I.runHistoryStateFrom rule S history).assignment) a q ≤
      I.bid a q * (1 - Real.exp (-ε)) := by
  exact AdWordsInstance.final_slackScore_le_bid_mul_one_sub_exp_neg_epsilon_of_not_canAssign
    I hbid rule hrule history S hS hsmall a q hbudget hnot

/--
Normalized exhausted-advertiser slack charge: with normalized MSVV advertiser
duals, the scaled blocked-advertiser slack is at most the explicit
`bid * (1 - exp (-ε))` small-bids error term.
-/
theorem paper_adwords_msvv_ratio_mul_blocked_advertiser_normalized_final_slack_score_le_error
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hsmall : I.SmallBids ε) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a)
    (hnot : ¬ I.CanAssign S.assignment q a) :
    AdWordsInstance.msvvRatio *
        I.slackScore
          (I.msvvNormalizedAlphaFromAssignment
            (I.runHistoryStateFrom rule S history).assignment) a q ≤
      I.bid a q * (1 - Real.exp (-ε)) := by
  exact AdWordsInstance.msvvRatio_mul_final_normalized_slackScore_le_bid_error_of_not_canAssign
    I hbid rule hrule history S hS hsmall a q hbudget hnot

/--
Normalized mixed beta charge: with normalized assignment-induced duals, the
scaled final max-slack query dual is bounded by the chosen Balance score plus
the explicit max-bid small-bids error term.
-/
theorem paper_adwords_msvv_ratio_mul_normalized_max_slack_beta_le_balance_score_add_max_bid_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) (q : Query) (chosen : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen) :
    AdWordsInstance.msvvRatio *
        I.maxSlackBeta
          (I.msvvNormalizedAlphaFromAssignment
            (I.runHistoryStateFrom rule S history).assignment) q ≤
      I.balanceScore S.assignment chosen q +
        I.maxBidForQuery q * (1 - Real.exp (-ε)) := by
  exact AdWordsInstance.msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_balanceScore_add_maxBidError_of_choice
    I hbid hbudget rule hrule history S hS hε hsmall q chosen hchoice

/--
Mixed beta charge: for a Balance/MSVV choice at state `S`, the final max-slack
query dual is bounded by the larger of the chosen Balance score and the
small-bids exhausted-advertiser error term for that query.
-/
theorem paper_adwords_max_slack_beta_le_balance_score_or_max_bid_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) (q : Query) (chosen : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen) :
    I.maxSlackBeta
        (I.msvvAlphaFromAssignment
          (I.runHistoryStateFrom rule S history).assignment) q ≤
      max (I.balanceScore S.assignment chosen q)
        (I.maxBidForQuery q * (1 - Real.exp (-ε))) := by
  exact AdWordsInstance.maxSlackBeta_runHistoryStateFrom_le_max_balanceScore_maxBidError_of_choice
    I hbid hbudget rule hrule history S hS hε hsmall q chosen hchoice

/--
Additive mixed beta charge: the same query dual can be charged to the chosen
Balance score plus the small exhausted-advertiser error term. This is the
summation-friendly form for the finite objective-bound proof.
-/
theorem paper_adwords_max_slack_beta_le_balance_score_add_max_bid_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) (q : Query) (chosen : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen) :
    I.maxSlackBeta
        (I.msvvAlphaFromAssignment
          (I.runHistoryStateFrom rule S history).assignment) q ≤
      I.balanceScore S.assignment chosen q +
        I.maxBidForQuery q * (1 - Real.exp (-ε)) := by
  exact AdWordsInstance.maxSlackBeta_runHistoryStateFrom_le_balanceScore_add_maxBidError_of_choice
    I hbid hbudget rule hrule history S hS hε hsmall q chosen hchoice

/--
History-summed beta charge for the Balance/MSVV run: over a nodup history, the
sum of final max-slack query duals along the history is bounded by the
recursive Balance charge plus the explicit max-bid exhausted-advertiser error
sum.
-/
theorem paper_adwords_balance_history_max_slack_beta_sum_le_charge_add_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    AdWordsInstance.historyMaxSlackBetaSum I
        (I.msvvAlphaFromAssignment
          (I.runAssignment I.balanceChoiceRule history))
        history ≤
      AdWordsInstance.historyBalanceChargeFrom I I.balanceChoiceRule
        AdWordsInstance.initialHistoryState history +
        AdWordsInstance.historyMaxBidErrorSum I ε history := by
  have hnonneg : I.NonnegativeBudgets := fun a => (hbudget a).le
  have hS :
      I.StateInvariant
        (AdWordsInstance.initialHistoryState :
          AdWordsInstance.HistoryState Advertiser Query) :=
    AdWordsInstance.initialHistoryState_invariant I hnonneg
  have hfresh :
      ∀ q,
        q ∈ AdWordsInstance.historyFinset history →
          q ∉
            (AdWordsInstance.initialHistoryState :
              AdWordsInstance.HistoryState Advertiser Query).seen := by
    simp [AdWordsInstance.initialHistoryState]
  have h :=
    AdWordsInstance.historyMaxSlackBetaSum_balanceChoiceRun_le_balanceCharge_add_maxBidError
      I hbid hbudget history
      (AdWordsInstance.initialHistoryState :
        AdWordsInstance.HistoryState Advertiser Query)
      hS hfresh hnodup hε hsmall
  simpa [AdWordsInstance.runAssignment, AdWordsInstance.runHistoryState] using h

/--
Query-dual sum charge for a history that enumerates all query identifiers:
the finite LP query-dual contribution is bounded by the recursive Balance
charge plus the explicit max-bid small-bids error.
-/
theorem paper_adwords_balance_query_dual_sum_le_charge_add_error_of_history_cover
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    (∑ q : Query,
      I.maxSlackBeta
        (I.msvvAlphaFromAssignment
          (I.runAssignment I.balanceChoiceRule history)) q) ≤
      AdWordsInstance.historyBalanceChargeFrom I I.balanceChoiceRule
        AdWordsInstance.initialHistoryState history +
        AdWordsInstance.historyMaxBidErrorSum I ε history := by
  exact AdWordsInstance.sum_maxSlackBeta_balanceRun_le_balanceCharge_add_maxBidError_of_cover
    I hbid hbudget history hnodup hcover hε hsmall

/--
Normalized query-dual sum charge for a history that enumerates all query
identifiers: the scaled finite LP query-dual contribution is bounded by the
recursive Balance charge plus the explicit max-bid small-bids error.
-/
theorem paper_adwords_msvv_ratio_mul_normalized_query_dual_sum_le_charge_add_error_of_history_cover
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    AdWordsInstance.msvvRatio *
      (∑ q : Query,
        I.maxSlackBeta
          (I.msvvNormalizedAlphaFromAssignment
            (I.runAssignment I.balanceChoiceRule history)) q) ≤
      AdWordsInstance.historyBalanceChargeFrom I I.balanceChoiceRule
        AdWordsInstance.initialHistoryState history +
        AdWordsInstance.historyMaxBidErrorSum I ε history := by
  exact AdWordsInstance.msvvRatio_mul_sum_maxSlackBeta_normalized_balanceRun_le_balanceCharge_add_maxBidError_of_cover
    I hbid hbudget history hnodup hcover hε hsmall

/--
Small-bids boundary lemma: if advertiser `a` cannot accept query `q`, then
under the `ε`-small-bids condition `a` has already spent more than a
`1 - ε` fraction of her budget.
-/
theorem paper_adwords_small_bids_blocked_advertiser_spent_fraction
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : AdWordsInstance.Assignment Advertiser Query)
    (a : Advertiser) (q : Query) {ε : ℝ}
    (hbudget : 0 < I.budget a)
    (hsmall : I.SmallBids ε)
    (hnot : ¬ I.CanAssign A q a) :
    1 - ε < I.spentFraction A a := by
  exact AdWordsInstance.spentFraction_gt_one_sub_epsilon_of_not_canAssign
    I A a q hbudget hsmall hnot

/--
Section 6 effective-bid reduction: replacing bids by any effective charge
function preserves advertiser budgets, and it is an AdWords instance whenever
the effective charges satisfy the same nonnegativity and small-bids hypotheses.
-/
theorem paper_adwords_effective_bids_small_bids
    {Advertiser Query : Type*}
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ) {ε : ℝ}
    (hsmall : ∀ a q, effectiveBid a q ≤ ε * I.budget a) :
    (I.withEffectiveBids effectiveBid).SmallBids ε := by
  exact AdWordsInstance.withEffectiveBids_smallBids I effectiveBid hsmall

/--
Section 6 click-through-rate reduction: if CTRs are at most one and original
bids are nonnegative and small, then expected effective bids are small.
-/
theorem paper_adwords_click_through_rates_small_bids
    {Advertiser Query : Type*}
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) {ε : ℝ}
    (hctr_le_one : ∀ a q, ctr a q ≤ 1)
    (hbid : I.NonnegativeBids)
    (hsmall : I.SmallBids ε) :
    (I.withClickThroughRates ctr).SmallBids ε := by
  exact AdWordsInstance.withClickThroughRates_smallBids_of_ctr_le_one
    I ctr hctr_le_one hbid hsmall

/--
Section 8 weighted-bid reduction: if advertiser weights are at most one and
original bids are nonnegative and small, then weighted effective bids are small.
-/
theorem paper_adwords_weighted_bids_small_bids
    {Advertiser Query : Type*}
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ) {ε : ℝ}
    (hweight_le_one : ∀ a, weight a ≤ 1)
    (hbid : I.NonnegativeBids)
    (hsmall : I.SmallBids ε) :
    (I.withAdvertiserWeights weight).SmallBids ε := by
  exact AdWordsInstance.withAdvertiserWeights_smallBids_of_weight_le_one
    I weight hweight_le_one hbid hsmall

/--
Section 6 delayed-entry/availability reduction: inactive advertisers can be
modeled by zero effective bids without breaking the small-bids hypothesis.
-/
theorem paper_adwords_availability_small_bids
    {Advertiser Query : Type*}
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)]
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hbudget : I.PositiveBudgets)
    (hsmall : I.SmallBids ε) :
    (I.withAvailability active).SmallBids ε := by
  exact AdWordsInstance.withAvailability_smallBids
    I active hε hbudget hsmall

/--
Section 6 multiple-ads reduction: expanding each original query into a finite
family of slot queries preserves the small-bids hypothesis.
-/
theorem paper_adwords_multiple_slots_small_bids
    {Advertiser Query : Type*}
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*) {ε : ℝ}
    (hsmall : I.SmallBids ε) :
    (I.withSlots Slot).SmallBids ε := by
  exact AdWordsInstance.withSlots_smallBids I Slot hsmall

/--
Section 7 / Theorem 9 lower-bound wrapper. A finite Yao certificate for the
paper's random-permutation b-matching construction implies that no randomized
online algorithm has normalized revenue strictly above `1 - 1/e` on every
input in the certified family.
-/
theorem paper_adwords_theorem9_no_randomized_algorithm_beats_msvv_ratio_of_certificate
    {Algorithm Input : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    [Fintype Input] [DecidableEq Input] [Nonempty Input]
    (C : BMatchingYaoLowerBoundCertificate Algorithm Input)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ input,
      AdWordsInstance.msvvRatio <
        AppliedModelingLib.pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm input) := by
  exact
    bMatching_no_randomized_algorithm_beats_msvvRatio_of_certificate
      C randomizedAlgorithm

/--
Section 7 / Theorem 9 wrapper specialized to the paper's hard distribution:
the uniform distribution over bidder permutations.
-/
theorem paper_adwords_theorem9_no_randomized_algorithm_beats_msvv_ratio_of_permutation_certificate
    {N : ℕ} {Algorithm : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingPermutationLowerBoundCertificate N Algorithm)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      AdWordsInstance.msvvRatio <
        AppliedModelingLib.pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact C.no_randomized_algorithm_beats_msvvRatio randomizedAlgorithm

/--
Section 7 / Theorem 9 wrapper from the paper's explicit finite revenue-bound
expression. The certificate fields are exactly the deterministic average
revenue bound and the comparison of that finite harmonic expression with the
requested finite ratio.
-/
theorem paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_revenue_bound_certificate
    {N : ℕ} {Algorithm : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    {ratio : ℝ}
    (C : BMatchingPermutationRevenueBoundCertificate N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        AppliedModelingLib.pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact C.no_randomized_algorithm_beats_ratio randomizedAlgorithm

/--
Section 7 / Theorem 9 wrapper from the paper's expected round-allocation
inequality `E[q_ij] <= 1 / (N - i + 1)`.
-/
theorem paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_round_allocation_certificate
    {N : ℕ} {Algorithm : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    {ratio : ℝ}
    (C : BMatchingRoundAllocationRevenueCertificate N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        AppliedModelingLib.pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact C.no_randomized_algorithm_beats_ratio randomizedAlgorithm

/--
Section 7 / Theorem 9 wrapper from realized per-permutation allocations. The
finite expectation algebra from pointwise capped spend to capped expected spend
is proved in Lean; more specialized wrappers below derive the expected
round/bidder allocation bound from symmetry and observed-prefix structure.
-/
theorem paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_pointwise_allocation_certificate
    {N : ℕ} {Algorithm : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    {ratio : ℝ}
    (C : BMatchingPointwiseAllocationRevenueCertificate N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        AppliedModelingLib.pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact C.no_randomized_algorithm_beats_ratio randomizedAlgorithm

/--
Section 7 / Theorem 9 wrapper from the paper's symmetry/capacity calculation:
eligible positions have equal expected allocation under the random permutation
distribution, each round allocates at most one unit, and ineligible positions
receive zero.
-/
theorem paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_symmetric_pointwise_allocation_certificate
    {N : ℕ} {Algorithm : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    {ratio : ℝ}
    (C : BMatchingSymmetricPointwiseAllocationRevenueCertificate
      N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        AppliedModelingLib.pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact C.no_randomized_algorithm_beats_ratio randomizedAlgorithm

/--
Section 7 / Theorem 9 wrapper from pointwise input-relabeling symmetry. This
derives the equal expected allocation of eligible positions from invariance of
the uniform permutation distribution under the supplied relabeling equivalence.
-/
theorem paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_relabel_symmetric_pointwise_allocation_certificate
    {N : ℕ} {Algorithm : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    {ratio : ℝ}
    (C : BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate
      N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        AppliedModelingLib.pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact C.no_randomized_algorithm_beats_ratio randomizedAlgorithm

/--
Section 7 / Theorem 9 wrapper from the observed-prefix online-information
model. The algorithm's position allocation factors through the eligible bidder
sets visible up to the current round, so the relabeling symmetry is proved
internally.
-/
theorem paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_observed_prefix_allocation_certificate
    {N : ℕ} {Algorithm : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    {ratio : ℝ}
    (C : BMatchingObservedPrefixAllocationRevenueCertificate
      N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        AppliedModelingLib.pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact C.no_randomized_algorithm_beats_ratio randomizedAlgorithm

/--
Section 7 / Theorem 9 wrapper from a feasible actual-bidder allocation rule on
the observed prefix. Position-level capacity and ineligible-zero facts are
derived internally from feasibility over the visible actual bidder set.
-/
theorem paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_feasible_observed_prefix_allocation_certificate
    {N : ℕ} {Algorithm : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    {ratio : ℝ}
    (C : BMatchingFeasibleObservedPrefixAllocationRevenueCertificate
      N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        AppliedModelingLib.pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact C.no_randomized_algorithm_beats_ratio randomizedAlgorithm

/--
Section 7 / Theorem 9 harmonic-cap wrapper: the logarithmic tail-spend bound
implies the finite layer-count estimate used in the asymptotic lower bound.
-/
theorem paper_adwords_theorem9_harmonic_layer_count_bound_of_log_spend_cap
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hlog :
      ∀ bidder : Fin N,
        0 < N - (bidder : ℕ) - 1 →
          theorem9BidderSpendUpperBound N bidder ≤
            Real.log ((N : ℝ) / ((N - (bidder : ℕ) - 1 : ℕ) : ℝ))) :
    theorem9HarmonicLayerCountBound N M := by
  exact theorem9HarmonicLayerCountBound_of_logSpendCap hN hM hlog

/--
Section 7 / Theorem 9 harmonic-prefix wrapper: each capped bidder spend is
bounded by the logarithmic tail ratio used in the paper's layer-count argument.
-/
theorem paper_adwords_theorem9_bidder_spend_upper_bound_le_log_tail
    {N : ℕ} (bidder : Fin N)
    (htail : 0 < N - (bidder : ℕ) - 1) :
    theorem9BidderSpendUpperBound N bidder ≤
      Real.log ((N : ℝ) / ((N - (bidder : ℕ) - 1 : ℕ) : ℝ)) := by
  exact theorem9BidderSpendUpperBound_le_log_tail bidder htail

/--
Section 7 / Theorem 9 finite layer-count estimate. The logarithmic spend bound
is formalized, so the layer-count hypothesis is no longer an external field.
-/
theorem paper_adwords_theorem9_harmonic_layer_count_bound
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    theorem9HarmonicLayerCountBound N M := by
  exact theorem9HarmonicLayerCountBound_of_pos hN hM

/--
Section 7 / Theorem 9 finite harmonic comparison. Given the finite layer-count
estimate, the explicit harmonic revenue cap is at most `1 - 1/e` plus the grid
errors `1/M + 1/N`.
-/
theorem paper_adwords_theorem9_normalized_revenue_upper_bound_le_msvv_ratio_add_grid_errors
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hlayer : theorem9HarmonicLayerCountBound N M) :
    theorem9NormalizedRevenueUpperBound N ≤
      AdWordsInstance.msvvRatio + 1 / (M : ℝ) + 1 / (N : ℝ) := by
  exact theorem9NormalizedRevenueUpperBound_le_msvvRatio_add_gridErrors
    hN hM hlayer

/--
Section 7 / Theorem 9 asymptotic harmonic comparison from diagonal finite
layer-count bounds.
-/
theorem paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta_of_layer_count_bound
    (hlayer : ∀ N : ℕ, 0 < N → theorem9HarmonicLayerCountBound N N) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        theorem9NormalizedRevenueUpperBound N ≤
          AdWordsInstance.msvvRatio + δ := by
  exact theorem9_harmonic_eventually_le_msvvRatio_add_of_layerCountBound
    hlayer

/--
Section 7 / Theorem 9 harmonic-cap theorem: the explicit finite harmonic cap is
eventually within every positive additive error of `1 - 1/e`.
-/
theorem paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        theorem9NormalizedRevenueUpperBound N ≤
          AdWordsInstance.msvvRatio + δ := by
  exact theorem9_harmonic_eventually_le_msvvRatio_add

/--
Section 7 / Theorem 9 asymptotic lower-bound wrapper. Once the deterministic
round-allocation expectation inequalities are supplied for a family of market
sizes, the formalized harmonic-cap limit gives that no randomized algorithm
family beats `1 - 1/e + δ` on every sufficiently large permutation instance.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (normalizedRevenue :
      (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ)
    (expectedRoundBidderAllocation :
      (N : ℕ) → Algorithm N → Fin N → Fin N → ℝ)
    (haverage :
      ∀ N algorithm,
        AppliedModelingLib.pmfExp (uniformPermutationDistribution N)
            (fun permutation => normalizedRevenue N algorithm permutation) ≤
          (∑ bidder : Fin N,
            min 1
              (∑ round : Fin N,
                expectedRoundBidderAllocation N algorithm round bidder)) /
            (N : ℝ))
    (hexpected_le :
      ∀ N algorithm round bidder,
        expectedRoundBidderAllocation N algorithm round bidder ≤
          if (round : ℕ) ≤ (bidder : ℕ) then
            1 / ((N - (round : ℕ) : ℕ) : ℝ)
          else
            0) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm => normalizedRevenue N algorithm permutation) := by
  exact
    theorem9_eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
      normalizedRevenue expectedRoundBidderAllocation haverage hexpected_le
      theorem9_harmonic_eventually_le_msvvRatio_add

/--
Paper-level Section 7 / Theorem 9 lower-bound endpoint. The certificate
packages the paper's random-permutation construction, deterministic
round-allocation expectation inequalities; the harmonic-cap limit is proved
internally.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_family_certificate
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : BMatchingTheorem9FamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  exact C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

/--
Paper-level Section 7 / Theorem 9 lower-bound endpoint from realized
per-permutation allocation variables. This wrapper derives the finite
expected-allocation certificate internally for every market size.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_pointwise_family_certificate
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : BMatchingTheorem9PointwiseFamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  exact C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

/--
Paper-level Section 7 / Theorem 9 endpoint from the symmetry/capacity form of
the deterministic lower-bound calculation.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_symmetric_pointwise_family_certificate
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : BMatchingTheorem9SymmetricPointwiseFamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  exact C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

/--
Paper-level Section 7 / Theorem 9 endpoint from pointwise input-relabeling
symmetry. Observed-prefix wrappers below derive this relabeling field from the
paper's online-information argument.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_relabel_symmetric_pointwise_family_certificate
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : BMatchingTheorem9RelabelSymmetricPointwiseFamilyCertificate
      Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  exact C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

/--
Paper-level Section 7 / Theorem 9 endpoint from the observed-prefix
online-information model.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_observed_prefix_family_certificate
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : BMatchingTheorem9ObservedPrefixFamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  exact C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

/--
Paper-level Section 7 / Theorem 9 endpoint from feasible actual-bidder
allocation rules over the observed prefix.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_observed_prefix_family_certificate
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  exact C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

/--
Paper-level Section 7 / Theorem 9 endpoint for feasible observed-prefix
allocation rules, with payoff equal to the paper's capped normalized spend
expression.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_prefix_rule_family
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : BMatchingTheorem9FeasiblePrefixRuleFamily Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  C.normalizedRevenue N algorithm permutation) := by
  exact C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

/--
Paper-level Section 7 / Theorem 9 endpoint for finite families of integral
prefix choice algorithms.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : BMatchingTheorem9IntegralPrefixChoiceFamily Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  C.normalizedRevenue N algorithm permutation) := by
  exact C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

/--
Paper-level Section 7 / Theorem 9 endpoint for finite families of integral
prefix choice algorithms under a richer realized-revenue model.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family_of_realized_revenue
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : BMatchingTheorem9IntegralPrefixChoiceFamily Algorithm)
    (normalizedRevenue :
      (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ)
    (hrealized_le_capped :
      ∀ N algorithm permutation,
        normalizedRevenue N algorithm permutation ≤
          C.normalizedRevenue N algorithm permutation) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  normalizedRevenue N algorithm permutation) := by
  exact C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta_of_realized_revenue
    normalizedRevenue hrealized_le_capped

/--
Canonical family of finite integral-prefix algorithms for the Section 7 hard
instance: each algorithm is exactly a feasible prefix choice rule.
-/
def paper_adwords_theorem9_integral_prefix_algorithm_family :
    BMatchingTheorem9IntegralPrefixChoiceFamily
      (fun N => BMatchingIntegralPrefixAlgorithm N) :=
  { choice := fun _N algorithm => algorithm.1
    choice_feasible := fun _N algorithm => algorithm.2 }

/--
For the concrete integral-prefix algorithm family, the normalized revenue used
in the unconditional Theorem 9 endpoint is definitionally the capped normalized
prefix-spend expression.
-/
theorem paper_adwords_theorem9_integral_prefix_algorithm_family_normalized_revenue_eq_capped_spend
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (permutation : Equiv.Perm (Fin N)) :
    paper_adwords_theorem9_integral_prefix_algorithm_family.normalizedRevenue
      N algorithm permutation =
      (∑ bidder : Fin N,
        min 1
          (∑ round : Fin N,
            BMatchingIntegralPrefixAlgorithm.prefixAllocation algorithm
              (theorem9ObservedPrefix N permutation round)
              round (permutation bidder))) /
        (N : ℝ) := by
  rfl

/--
Paper-level Section 7 / Theorem 9 endpoint for finite families of concrete
integral prefix algorithms (the subtype of feasible integral rules), with the
paper's capped normalized spend as normalized revenue.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms
    :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (BMatchingIntegralPrefixAlgorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  paper_adwords_theorem9_integral_prefix_algorithm_family.normalizedRevenue
                    N algorithm permutation) := by
  exact
    paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family
      paper_adwords_theorem9_integral_prefix_algorithm_family

/--
Paper-level Section 7 / Theorem 9 endpoint for finite families of concrete
integral prefix algorithms under a richer realized-revenue model.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms_of_realized_revenue
    (normalizedRevenue :
      (N : ℕ) → BMatchingIntegralPrefixAlgorithm N → Equiv.Perm (Fin N) → ℝ)
    (hrealized_le_capped :
      ∀ N algorithm permutation,
        normalizedRevenue N algorithm permutation ≤
          paper_adwords_theorem9_integral_prefix_algorithm_family.normalizedRevenue
            N algorithm permutation) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (BMatchingIntegralPrefixAlgorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  normalizedRevenue N algorithm permutation) := by
  exact
    paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family_of_realized_revenue
      paper_adwords_theorem9_integral_prefix_algorithm_family
      normalizedRevenue hrealized_le_capped

/--
Paper-level Section 7 / Theorem 9 endpoint from round-allocation inequalities
and finite layer-count harmonic bounds.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_layer_count_family_certificate
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : BMatchingTheorem9LayerCountFamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  exact C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

/--
Paper-level Section 7 / Theorem 9 endpoint from pointwise allocations and
finite layer-count harmonic bounds.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_pointwise_layer_count_family_certificate
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : BMatchingTheorem9PointwiseLayerCountFamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  exact C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

/--
Paper-level Section 7 / Theorem 9 endpoint from symmetry/capacity allocations
and finite layer-count harmonic bounds.
-/
theorem paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_symmetric_pointwise_layer_count_family_certificate
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : BMatchingTheorem9SymmetricPointwiseLayerCountFamilyCertificate
      Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  exact C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

/--
Paper-facing primal-dual seam: a finite primal-dual certificate implies the
advertised competitive-ratio inequality against the offline optimum.

This is kept as a reusable exact-certificate interface. The concrete finite
small-bids theorem and limiting Balance/MSVV theorem below no longer require a
separate primal-dual certificate from users.
-/
theorem paper_adwords_competitive_of_primal_dual_certificate
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (A : AdWordsInstance.Assignment Advertiser Query) (ratio : ℝ)
    (hcert : I.PrimalDualCompetitiveCertificate A ratio) :
    ratio * I.offlineOptimumValue hbudget ≤ I.revenue A := by
  exact AdWordsInstance.competitive_of_primalDual I hbudget A ratio hcert

/--
MSVV paper-facing seam for the Balance run: once the primal-dual certificate is
constructed for `msvvRatio = 1 - 1/e`, the Balance assignment is competitive
against the offline optimum at that ratio. This is the exact finite
certificate form; the small-bids theorem below supplies the paper-level
limiting guarantee.
-/
theorem paper_adwords_balance_msvv_competitive_of_primal_dual_certificate
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query)
    (hcert :
      I.PrimalDualCompetitiveCertificate
        (I.runAssignment I.balanceChoiceRule history)
        AdWordsInstance.msvvRatio) :
    AdWordsInstance.msvvRatio * I.offlineOptimumValue hbudget ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) := by
  exact AdWordsInstance.competitive_of_primalDual I hbudget
    (I.runAssignment I.balanceChoiceRule history)
    AdWordsInstance.msvvRatio hcert

/--
History-accounting seam for the ideal exact proof: once the advertiser-alpha
plus Balance-charge inequality is supplied, the finite MSVV objective-bound
certificate follows automatically. The concrete small-bids accounting theorem
below proves the approximate version used by the paper-level limit theorem.
-/
theorem paper_adwords_balance_msvv_objective_bound_of_history_accounting
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (history : List Query) {ε : ℝ}
    (hcert : I.MsvvHistoryAccountingCertificate history ε) :
    I.MsvvObjectiveBoundCertificate history := by
  exact AdWordsInstance.msvvObjectiveBoundCertificate_of_historyAccounting
    I history hcert

/--
Approximate history-accounting seam: the finite small-bids accounting
certificate with explicit additive error implies the approximate objective-bound
certificate for normalized MSVV duals.
-/
theorem paper_adwords_balance_msvv_approx_objective_bound_of_history_accounting
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (history : List Query) {ε error : ℝ}
    (hcert : I.MsvvHistoryApproxAccountingCertificate history ε error) :
    I.MsvvApproxObjectiveBoundCertificate history error := by
  exact AdWordsInstance.msvvApproxObjectiveBoundCertificate_of_historyApproxAccounting
    I history hcert

/--
Explicit finite small-bids accounting for the Balance run. Under nonnegative
bids, positive budgets, a duplicate-free history covering all query identifiers,
and `ε`-small bids, the remaining additive error is exactly the sum of the
advertiser-alpha discretization error and the exhausted-advertiser query-dual
error.
-/
theorem paper_adwords_balance_msvv_history_approx_accounting_with_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    I.MsvvHistoryApproxAccountingCertificate history ε
      (I.historyMaxBidAlphaErrorSum ε history +
        I.historyMaxBidErrorSum ε history) := by
  exact AdWordsInstance.msvvHistoryApproxAccountingCertificate_balanceChoiceRun
    I hbid hbudget history hnodup hcover hε hsmall

/--
Explicit finite small-bids objective bound for the Balance run, with the
history-level additive error carried in closed form.
-/
theorem paper_adwords_balance_msvv_approx_objective_bound_with_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    I.MsvvApproxObjectiveBoundCertificate history
      (I.historyMaxBidAlphaErrorSum ε history +
        I.historyMaxBidErrorSum ε history) := by
  exact AdWordsInstance.msvvApproxObjectiveBoundCertificate_balanceChoiceRun
    I hbid hbudget history hnodup hcover hε hsmall

/--
Final finite MSVV theorem seam: the Balance run is `1 - 1/e` competitive once
the single scaled dual-objective bound for the assignment-induced MSVV duals is
proved.
-/
theorem paper_adwords_balance_msvv_competitive_of_objective_bound
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hcert : I.MsvvObjectiveBoundCertificate history) :
    AdWordsInstance.msvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) := by
  exact AdWordsInstance.balance_msvv_competitive_of_objectiveBound
    I hbid hbudget history hcert

/--
Finite small-bids theorem seam with explicit additive error: an approximate
objective-bound certificate implies the corresponding approximate competitive
guarantee against the offline optimum.
-/
theorem paper_adwords_balance_msvv_approx_competitive_of_approx_objective_bound
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query) {error : ℝ}
    (hcert : I.MsvvApproxObjectiveBoundCertificate history error) :
    AdWordsInstance.msvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) + error := by
  exact AdWordsInstance.balance_msvv_approx_competitive_of_approxObjectiveBound
    I hbid hbudget history hcert

/--
Finite small-bids MSVV theorem with explicit history error. This is the
formal finite version of the Balance/MSVV guarantee before sending the small
bids error to zero.
-/
theorem paper_adwords_balance_msvv_approx_competitive_with_explicit_history_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    AdWordsInstance.msvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) +
        (I.historyMaxBidAlphaErrorSum ε history +
          I.historyMaxBidErrorSum ε history) := by
  exact AdWordsInstance.balance_msvv_approx_competitive_with_history_error
    I hbid hbudget history hnodup hcover hε hsmall

/--
Finite small-bids MSVV theorem with the explicit history error bounded by
`ε * (e + 1)` times the sum of per-query maximum bids. This is the algebraic
form of the remaining small-bids limiting seam.
-/
theorem paper_adwords_balance_msvv_approx_competitive_with_error_bound
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hε_le_one : ε ≤ 1)
    (hsmall : I.SmallBids ε) :
    AdWordsInstance.msvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) +
        ε * (Real.exp 1 + 1) * I.historyMaxBidSum history := by
  exact AdWordsInstance.balance_msvv_approx_competitive_with_error_bound
    I hbid hbudget history hnodup hcover hε hε_le_one hsmall

/--
Finite small-bids MSVV theorem with the error bound reindexed to the finite
query type: the additive term uses `∑ q, maxBidForQuery q`.
-/
theorem paper_adwords_balance_msvv_approx_competitive_with_query_sum_error_bound
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hε_le_one : ε ≤ 1)
    (hsmall : I.SmallBids ε) :
    AdWordsInstance.msvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) +
        ε * (Real.exp 1 + 1) *
          (∑ q : Query, I.maxBidForQuery q) := by
  exact AdWordsInstance.balance_msvv_approx_competitive_with_query_sum_error_bound
    I hbid hbudget history hnodup hcover hε hε_le_one hsmall

/--
Canonical finite-query version of the small-bids MSVV theorem. When queries
are indexed by `Fin n` and the history is `List.finRange n`, the nodup and
coverage assumptions are discharged automatically.
-/
theorem paper_adwords_balance_msvv_finRange_approx_competitive_with_query_sum_error_bound
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    {n : ℕ}
    (I : AdWordsInstance Advertiser (Fin n))
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hε_le_one : ε ≤ 1)
    (hsmall : I.SmallBids ε) :
    AdWordsInstance.msvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule (List.finRange n)) +
        ε * (Real.exp 1 + 1) *
          (∑ q : Fin n, I.maxBidForQuery q) := by
  exact
    AdWordsInstance.balance_msvv_approx_competitive_finRange_with_query_sum_error_bound
      I hbid hbudget hε hε_le_one hsmall

/--
Delta-form finite small-bids MSVV theorem. Once the explicit algebraic error
bound is at most `δ`, the Balance/MSVV run is competitive up to additive `δ`.
-/
theorem paper_adwords_balance_msvv_approx_competitive_up_to_delta
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {ε δ : ℝ}
    (hε : 0 ≤ ε)
    (hε_le_one : ε ≤ 1)
    (hsmall : I.SmallBids ε)
    (herror_le_delta :
      ε * (Real.exp 1 + 1) * I.historyMaxBidSum history ≤ δ) :
    AdWordsInstance.msvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) + δ := by
  exact AdWordsInstance.balance_msvv_approx_competitive_up_to_delta
    I hbid hbudget history hnodup hcover hε hε_le_one hsmall
    herror_le_delta

/--
Canonical `Fin n` delta-form small-bids theorem. The error side condition is
stated directly with the finite query sum `∑ q, maxBidForQuery q`.
-/
theorem paper_adwords_balance_msvv_finRange_approx_competitive_up_to_delta
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    {n : ℕ}
    (I : AdWordsInstance Advertiser (Fin n))
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    {ε δ : ℝ}
    (hε : 0 ≤ ε)
    (hε_le_one : ε ≤ 1)
    (hsmall : I.SmallBids ε)
    (herror_le_delta :
      ε * (Real.exp 1 + 1) *
          (∑ q : Fin n, I.maxBidForQuery q) ≤ δ) :
    AdWordsInstance.msvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule (List.finRange n)) +
        δ := by
  exact AdWordsInstance.balance_msvv_approx_competitive_finRange_up_to_delta
    I hbid hbudget hε hε_le_one hsmall herror_le_delta

/--
Threshold form of the finite small-bids MSVV theorem. For a target additive
`δ`, it is enough to assume bids are small at the explicit threshold
`min 1 (δ / ((e + 1) * historyMaxBidSum))`.
-/
theorem paper_adwords_balance_msvv_approx_competitive_up_to_delta_of_small_bids_threshold
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hmaxBidSum_pos : 0 < I.historyMaxBidSum history)
    (hsmall :
      I.SmallBids
        (min 1
          (δ / ((Real.exp 1 + 1) * I.historyMaxBidSum history)))) :
    AdWordsInstance.msvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) + δ := by
  exact
    AdWordsInstance.balance_msvv_approx_competitive_up_to_delta_of_smallBids_threshold
      I hbid hbudget history hnodup hcover hδ hmaxBidSum_pos hsmall

/--
Canonical `Fin n` threshold form. For the history `List.finRange n`, the
small-bids threshold is expressed using the finite query sum
`∑ q, maxBidForQuery q`.
-/
theorem paper_adwords_balance_msvv_finRange_approx_competitive_up_to_delta_of_small_bids_threshold
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    {n : ℕ}
    (I : AdWordsInstance Advertiser (Fin n))
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hmaxBidSum_pos : 0 < ∑ q : Fin n, I.maxBidForQuery q)
    (hsmall :
      I.SmallBids
        (min 1
          (δ / ((Real.exp 1 + 1) *
            (∑ q : Fin n, I.maxBidForQuery q))))) :
    AdWordsInstance.msvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule (List.finRange n)) +
        δ := by
  exact
    AdWordsInstance.balance_msvv_approx_competitive_finRange_up_to_delta_of_smallBids_threshold
      I hbid hbudget hδ hmaxBidSum_pos hsmall

/--
Limit-style finite MSVV theorem. If the same finite instance satisfies the
explicit small-bids threshold for every positive additive target `δ`, then the
additive term can be removed.
-/
theorem paper_adwords_balance_msvv_competitive_of_arbitrarily_small_bids_threshold
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    (hmaxBidSum_pos : 0 < I.historyMaxBidSum history)
    (hsmall :
      ∀ δ : ℝ, 0 < δ →
        I.SmallBids
          (min 1
            (δ / ((Real.exp 1 + 1) * I.historyMaxBidSum history)))) :
    AdWordsInstance.msvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) := by
  exact
    AdWordsInstance.balance_msvv_competitive_of_arbitrarily_smallBids_threshold
      I hbid hbudget history hnodup hcover hmaxBidSum_pos hsmall

/--
Canonical `Fin n` limit-style MSVV theorem. This is the no-boilerplate version
of the finite limit-style wrapper for the standard history `List.finRange n`.
-/
theorem paper_adwords_balance_msvv_finRange_competitive_of_arbitrarily_small_bids_threshold
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    {n : ℕ}
    (I : AdWordsInstance Advertiser (Fin n))
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (hmaxBidSum_pos : 0 < ∑ q : Fin n, I.maxBidForQuery q)
    (hsmall :
      ∀ δ : ℝ, 0 < δ →
        I.SmallBids
          (min 1
            (δ / ((Real.exp 1 + 1) *
              (∑ q : Fin n, I.maxBidForQuery q))))) :
    AdWordsInstance.msvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule (List.finRange n)) := by
  exact
    AdWordsInstance.balance_msvv_finRange_competitive_of_arbitrarily_smallBids_threshold
      I hbid hbudget hmaxBidSum_pos hsmall

/--
Family-level finite-query MSVV limiting seam. For a dependent family of
finite-query instances `Fin (n k)`, if the explicit finite error is eventually
below every positive target `δ`, then the Balance/MSVV run is eventually
competitive up to additive `δ`.
-/
theorem paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → AdWordsInstance Advertiser (Fin (n k)))
    (ε : ℕ → ℝ)
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hε : ∀ k, 0 ≤ ε k)
    (hε_le_one : ∀ k, ε k ≤ 1)
    (hsmall : ∀ k, (I k).SmallBids (ε k))
    (herror_eventually :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ε k * (Real.exp 1 + 1) *
              (∑ q : Fin (n k), (I k).maxBidForQuery q) ≤ δ) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        AdWordsInstance.msvvRatio *
            (I k).offlineOptimumValue (fun a => (hbudget k a).le) ≤
          (I k).revenue
              ((I k).runAssignment (I k).balanceChoiceRule
                (List.finRange (n k))) +
            δ := by
  exact
    AdWordsInstance.balance_msvv_finRange_family_eventually_up_to_delta
      n I ε hbid hbudget hε hε_le_one hsmall herror_eventually

/--
Family-level small-bids threshold seam. If every positive additive target `δ`
eventually satisfies the explicit small-bids threshold in the family, then the
MSVV guarantee is eventually additive-`δ`.
-/
theorem paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta_of_small_bids_threshold
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → AdWordsInstance Advertiser (Fin (n k)))
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hmaxBidSum_pos :
      ∀ k, 0 < ∑ q : Fin (n k), (I k).maxBidForQuery q)
    (hsmall_eventually :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          (I k).SmallBids
            (min 1
              (δ / ((Real.exp 1 + 1) *
                (∑ q : Fin (n k), (I k).maxBidForQuery q))))) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        AdWordsInstance.msvvRatio *
            (I k).offlineOptimumValue (fun a => (hbudget k a).le) ≤
          (I k).revenue
              ((I k).runAssignment (I k).balanceChoiceRule
                (List.finRange (n k))) +
            δ := by
  exact
    AdWordsInstance.balance_msvv_finRange_family_eventually_up_to_delta_of_smallBids_threshold
      n I hbid hbudget hmaxBidSum_pos hsmall_eventually

/--
Family-level limiting theorem from explicit error control. If the scaled
offline benchmark and Balance/MSVV revenue converge, and the finite explicit
error is eventually below every positive target, the limiting scaled benchmark
is at most the limiting revenue.
-/
theorem paper_adwords_balance_msvv_finRange_family_limit_competitive_of_error_eventually
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → AdWordsInstance Advertiser (Fin (n k)))
    (ε : ℕ → ℝ)
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hε : ∀ k, 0 ≤ ε k)
    (hε_le_one : ∀ k, ε k ≤ 1)
    (hsmall : ∀ k, (I k).SmallBids (ε k))
    (herror_eventually :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ε k * (Real.exp 1 + 1) *
              (∑ q : Fin (n k), (I k).maxBidForQuery q) ≤ δ)
    {scaledOptLimit revenueLimit : ℝ}
    (hscaledOpt :
      Sequence.SeqTendsTo
        (fun k =>
          AdWordsInstance.msvvRatio *
            (I k).offlineOptimumValue (fun a => (hbudget k a).le))
        scaledOptLimit)
    (hrevenue :
      Sequence.SeqTendsTo
        (fun k =>
          (I k).revenue
            ((I k).runAssignment (I k).balanceChoiceRule
              (List.finRange (n k))))
        revenueLimit) :
    scaledOptLimit ≤ revenueLimit := by
  exact
    AdWordsInstance.balance_msvv_finRange_family_limit_competitive_of_error_eventually
      n I ε hbid hbudget hε hε_le_one hsmall herror_eventually
      hscaledOpt hrevenue

/--
Family-level limiting theorem from the explicit small-bids threshold. This is
the closest current formal seam to the paper's small-bids limiting statement:
instantiate the arrival/instance family, prove convergence of the two real
sides, and prove the threshold condition eventually.
-/
theorem paper_adwords_balance_msvv_finRange_family_limit_competitive_of_small_bids_threshold
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → AdWordsInstance Advertiser (Fin (n k)))
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hmaxBidSum_pos :
      ∀ k, 0 < ∑ q : Fin (n k), (I k).maxBidForQuery q)
    (hsmall_eventually :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          (I k).SmallBids
            (min 1
              (δ / ((Real.exp 1 + 1) *
                (∑ q : Fin (n k), (I k).maxBidForQuery q)))))
    {scaledOptLimit revenueLimit : ℝ}
    (hscaledOpt :
      Sequence.SeqTendsTo
        (fun k =>
          AdWordsInstance.msvvRatio *
            (I k).offlineOptimumValue (fun a => (hbudget k a).le))
        scaledOptLimit)
    (hrevenue :
      Sequence.SeqTendsTo
        (fun k =>
          (I k).revenue
            ((I k).runAssignment (I k).balanceChoiceRule
              (List.finRange (n k))))
        revenueLimit) :
    scaledOptLimit ≤ revenueLimit := by
  exact
    AdWordsInstance.balance_msvv_finRange_family_limit_competitive_of_smallBids_threshold
      n I hbid hbudget hmaxBidSum_pos hsmall_eventually hscaledOpt hrevenue

/--
Limit theorem from ordinary offline-optimum convergence and explicit error
control. This states the conclusion in the paper-facing form
`(1 - 1/e) * optLimit ≤ revenueLimit`.
-/
theorem paper_adwords_balance_msvv_finRange_family_limit_competitive_of_error_eventually_of_offline_opt_convergence
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → AdWordsInstance Advertiser (Fin (n k)))
    (ε : ℕ → ℝ)
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hε : ∀ k, 0 ≤ ε k)
    (hε_le_one : ∀ k, ε k ≤ 1)
    (hsmall : ∀ k, (I k).SmallBids (ε k))
    (herror_eventually :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ε k * (Real.exp 1 + 1) *
              (∑ q : Fin (n k), (I k).maxBidForQuery q) ≤ δ)
    {optLimit revenueLimit : ℝ}
    (hopt :
      Sequence.SeqTendsTo
        (fun k => (I k).offlineOptimumValue (fun a => (hbudget k a).le))
        optLimit)
    (hrevenue :
      Sequence.SeqTendsTo
        (fun k =>
          (I k).revenue
            ((I k).runAssignment (I k).balanceChoiceRule
              (List.finRange (n k))))
        revenueLimit) :
    AdWordsInstance.msvvRatio * optLimit ≤ revenueLimit := by
  exact
    AdWordsInstance.balance_msvv_finRange_family_limit_competitive_of_error_eventually_of_offlineOpt_convergence
      n I ε hbid hbudget hε hε_le_one hsmall herror_eventually hopt hrevenue

/--
Limit theorem from ordinary offline-optimum convergence and the explicit
eventual small-bids threshold. This is the current closest formal statement to
the paper's limiting AdWords guarantee.
-/
theorem paper_adwords_balance_msvv_finRange_family_limit_competitive_of_small_bids_threshold_of_offline_opt_convergence
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → AdWordsInstance Advertiser (Fin (n k)))
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hmaxBidSum_pos :
      ∀ k, 0 < ∑ q : Fin (n k), (I k).maxBidForQuery q)
    (hsmall_eventually :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          (I k).SmallBids
            (min 1
              (δ / ((Real.exp 1 + 1) *
                (∑ q : Fin (n k), (I k).maxBidForQuery q)))))
    {optLimit revenueLimit : ℝ}
    (hopt :
      Sequence.SeqTendsTo
        (fun k => (I k).offlineOptimumValue (fun a => (hbudget k a).le))
        optLimit)
    (hrevenue :
      Sequence.SeqTendsTo
        (fun k =>
          (I k).revenue
            ((I k).runAssignment (I k).balanceChoiceRule
              (List.finRange (n k))))
        revenueLimit) :
    AdWordsInstance.msvvRatio * optLimit ≤ revenueLimit := by
  exact
    AdWordsInstance.balance_msvv_finRange_family_limit_competitive_of_smallBids_threshold_of_offlineOpt_convergence
      n I hbid hbudget hmaxBidSum_pos hsmall_eventually hopt hrevenue

/--
Paper-level Balance/MSVV limiting theorem. Any finite-query small-bids family
that satisfies the explicit MSVV threshold eventually, and whose offline
optimum and Balance/MSVV revenue converge, has limiting competitive ratio
`1 - 1/e`.
-/
theorem paper_adwords_balance_msvv_competitive_of_small_bids_limit_family
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (F : AdWordsInstance.MsvvSmallBidsLimitFamily Advertiser) :
    AdWordsInstance.msvvRatio * F.optLimit ≤ F.revenueLimit := by
  exact AdWordsInstance.balance_msvv_competitive_of_smallBidsLimitFamily F

end Online
end AppliedModelingLib
