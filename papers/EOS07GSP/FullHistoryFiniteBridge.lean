import EOS07GSP.OrderedExPost
import EOS07GSP.Implementation
import EOS07GSP.FiniteLegalHistory

/-!
# EOS07 Theorem 8: full-history to finite-action bridge

The source writes a strategy as a dropout price for every public price history,
whereas the finite source-event model stores the immediately preceding dropout
price in a rank-indexed continuation record.  This module identifies the
named source formula across those two representations.  It is only the action
bridge; construction of the finite advertiser execution remains separate.
-/

namespace EOS07GSP
namespace PaperInterface

open AppliedModelingLib.Auction

noncomputable section

/-- Evaluate a full-history continuation plan at the finite source-event
continuation record for each rank. -/
def Theorem8ContinuationPlan.toRankedActionStrategy
    (plan : Theorem8ContinuationPlan) (lastDropout value : ℕ → ℝ) :
    PaperTheorem8GeneralizedEnglishStrategy ℕ :=
  fun state rank =>
    plan rank [lastDropout rank] (value (rank + 1)) ≤ state.clockPrice

/-- The named full-history plan induces exactly the finite ranked action rule
obtained from the source dropout-price formula. -/
theorem theorem8_named_continuation_plan_to_ranked_action_eq
    (clickThroughRate lastDropout value : ℕ → ℝ) :
    (theorem8NamedContinuationPlan clickThroughRate).toRankedActionStrategy
        lastDropout value =
      theorem8ContinuousSourceActionStrategy
        clickThroughRate lastDropout value := by
  funext state rank
  apply propext
  simp only [Theorem8ContinuationPlan.toRankedActionStrategy,
    theorem8NamedContinuationPlan,
    theorem8_source_price_history_last_dropout_cons,
    theorem8ContinuousSourceActionStrategy,
    Theorem8ContinuousSourceStrategy.inducedActionStrategy,
    theorem8ContinuousSourceStrategy,
    theorem8ContinuousSourceDropoutPrice,
    theorem8GeneralizedEnglishDropoutPrice]

/-- With the finite `B*` continuation records, the named full-history plan
induces the ranked `B*` threshold action used by the finite source-event game.
-/
theorem theorem8_named_continuation_plan_to_ranked_action_eq_bstar_threshold
    (value clickThroughRate : ℕ → ℝ) (remaining : ℕ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank) :
    (theorem8NamedContinuationPlan clickThroughRate).toRankedActionStrategy
        (fun k =>
          theorem7BStarBid value
            (fun j =>
              paper_theorem7_ranked_vcg_tail_payment
                value clickThroughRate j remaining)
            clickThroughRate (k + 2))
        value =
      paper_theorem8_bstar_ranked_threshold_strategy
        value clickThroughRate remaining := by
  rw [theorem8_named_continuation_plan_to_ranked_action_eq]
  exact theorem8_continuous_source_action_strategy_eq_bstar_threshold
    value clickThroughRate remaining hclick_pos

/-- The finite strict-value source game recognizes the action induced by the
named full-history plan as its unique PBE and gives it the VCG outcome.  This
is the checked finite-execution bridge for the named formula; a separate
relabeling theorem must still connect arbitrary source advertisers to the
ranked strict-value realization. -/
theorem theorem8_named_continuation_plan_unique_source_sequential_pbe_outcome_eq_vcg_of_strict_values
    (model : theorem8StrictOrderedValueCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        (theorem8StrictOrderedLocalOptimalityCertificateOfStrictValues model)
    let continuation := fun k =>
      theorem7BStarBid localModel.value
        (fun j =>
          paper_theorem7_ranked_vcg_tail_payment
            localModel.value localModel.clickThroughRate j localModel.remaining)
        localModel.clickThroughRate (k + 2)
    let G := sourceSequentialGame localModel initialState
    ∃! equilibrium : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium equilibrium ∧
        equilibrium =
          (theorem8NamedContinuationPlan localModel.clickThroughRate).toRankedActionStrategy
            continuation localModel.value ∧
          G.outcomeOf equilibrium = G.vcgOutcome := by
  dsimp
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
      (theorem8StrictOrderedLocalOptimalityCertificateOfStrictValues model)
  let continuation := fun k =>
    theorem7BStarBid localModel.value
      (fun j =>
        paper_theorem7_ranked_vcg_tail_payment
          localModel.value localModel.clickThroughRate j localModel.remaining)
      localModel.clickThroughRate (k + 2)
  let namedAction :=
    (theorem8NamedContinuationPlan localModel.clickThroughRate).toRankedActionStrategy
      continuation localModel.value
  let continuousAction :=
    theorem8ContinuousSourceActionStrategy
      localModel.clickThroughRate continuation localModel.value
  let G := sourceSequentialGame localModel initialState
  have hbridge : namedAction = continuousAction := by
    exact theorem8_named_continuation_plan_to_ranked_action_eq
      localModel.clickThroughRate continuation localModel.value
  have hbase :=
    theorem8_continuous_source_action_strategy_unique_source_sequential_pbe_outcome_eq_vcg_of_strict_values
      model initialState
  dsimp [localModel, continuation, continuousAction, G] at hbase
  rcases hbase with ⟨equilibrium, hequilibrium, hunique⟩
  refine ⟨equilibrium, ?_, ?_⟩
  · exact ⟨hequilibrium.1, hequilibrium.2.1.trans hbridge.symm,
      hequilibrium.2.2⟩
  · intro other hother
    exact hunique other
      ⟨hother.1, hother.2.1.trans hbridge, hother.2.2⟩

end

end PaperInterface
end EOS07GSP
