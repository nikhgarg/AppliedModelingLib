import EOS07GSP.OrderedExPost
import EOS07GSP.FiniteSourceExecution

/-!
# EOS07 Theorem 8: finite legal-history PBE interface

The source has a finite `N`-slot market with a zero click-through rate below
the final advertised slot.  This module states the corresponding legal-history
PBE domain explicitly: continuation comparisons contain at most `N` opponents,
and legal source actions are required only at advertised ranks.  The Bayesian
belief construction itself remains the ordinary full-history construction.
-/

namespace EOS07GSP
namespace PaperInterface

noncomputable section

universe u

variable {Bidder : Type u}

/-- Legal stopped-clock actions on the `N` advertised source ranks.  The
condition intentionally does not ask for a fictitious action below the final
zero-CTR slot. -/
def Theorem8ContinuationPlan.FiniteClockLegalOnFeasibleHistory
    (plan : Theorem8ContinuationPlan) (Bidder : Type u)
    (slotCount : ℕ) : Prop :=
  ∀ bidder rank history value,
    rank < slotCount →
    theorem8SourcePriceHistoryLastDropout history ≤ value →
      theorem8SourcePriceHistoryLastDropout history ≤
        (plan.historyStrategy Bidder).dropoutPrice bidder rank history value

/-- Ex-post sequential rationality in the finite source market.  The source
has one more bidder than slots, so every feasible continuation compares at
most `slotCount` ordered opponents. -/
def Theorem8FiniteOrderedExPostBestResponse
    (clickThroughRate : ℕ → ℝ) (slotCount : ℕ)
    (plan : Theorem8ContinuationPlan) : Prop :=
  ∀ ownValue opponents history,
    opponents.length ≤ slotCount →
    Theorem8OrderedOpponentProfileValid history opponents →
    theorem8SourcePriceHistoryLastDropout history ≤ ownValue →
    ∀ deviation : Theorem8ContinuationPlan,
      theorem8OrderedContinuationUtility clickThroughRate deviation ownValue
          opponents history ≤
        theorem8OrderedContinuationUtility clickThroughRate plan ownValue
          opponents history

/-- The finite legal-history ex-post PBE predicate for the explicitly
**symmetric continuation-plan** convention. `Theorem8ContinuationPlan` is one
common rank/history/value plan; `historyStrategy Bidder` instantiates that plan
at each bidder identity and the belief system remains bidder-indexed. Thus this
endpoint does not claim the paper's stronger uniqueness over arbitrary
bidder-indexed strategy profiles. The restriction is disclosed in the EOS
validation materials. -/
def Theorem8FiniteLegalHistoryExPostPBE
    (Bidder : Type u) (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ) (slotCount : ℕ)
    (plan : Theorem8ContinuationPlan) : Prop :=
  plan.ContinuousInValuation ∧
    plan.FiniteClockLegalOnFeasibleHistory Bidder slotCount ∧
      (∃ belief : Theorem8HistoryBeliefSystem Bidder,
        belief.BayesConsistent law (plan.historyStrategy Bidder)) ∧
      Theorem8FiniteOrderedExPostBestResponse clickThroughRate slotCount plan

/-- The named source formula is clock-legal at every advertised finite rank.
The lower CTR may be zero at the final rank; only the current advertised CTR
is required to be positive. -/
theorem theorem8_named_history_strategy_finite_clock_legal_on_feasible_history
    (clickThroughRate : ℕ → ℝ) (slotCount : ℕ)
    (hclick_pos : ∀ rank, rank < slotCount → 0 < clickThroughRate rank)
    (hclick_mono : ∀ rank, rank < slotCount →
      clickThroughRate (rank + 1) ≤ clickThroughRate rank) :
    Theorem8ContinuationPlan.FiniteClockLegalOnFeasibleHistory
      (theorem8NamedContinuationPlan clickThroughRate) Bidder slotCount := by
  intro bidder rank history value hrank hfeasible
  change theorem8SourcePriceHistoryLastDropout history ≤
    paper_theorem8_generalized_english_indifference_price
      (clickThroughRate rank) (clickThroughRate (rank + 1))
      (theorem8SourcePriceHistoryLastDropout history) value
  exact paper_theorem8_generalized_english_indifference_price_lastDropout_le
    (hclick_pos rank hrank) (hclick_mono rank hrank) hfeasible

/-- The existing canonical posterior is already a bidder-indexed Bayes
belief system for the finite source interface; the finite restriction is only
on sequential decision ranks and opponent menus. -/
theorem theorem8_named_finite_history_bayes_consistent
    (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ) :
    ∃ belief : Theorem8HistoryBeliefSystem Bidder,
      belief.BayesConsistent law
        ((theorem8NamedContinuationPlan clickThroughRate).historyStrategy
          Bidder) := by
  let strategy :=
    (theorem8NamedContinuationPlan clickThroughRate).historyStrategy Bidder
  exact ⟨theorem8CanonicalHistoryBeliefSystem law strategy,
    theorem8_canonical_history_belief_bayes_consistent law strategy⟩

/-- On a finite advertised market, no higher-slot continuation beats immediate
dropout when every remaining opponent has value at least the focal bidder's.
The final comparison permits the source's zero CTR below the last slot. -/
theorem theorem8_ordered_optimal_utility_le_drop_of_own_le_all_finite
    (clickThroughRate : ℕ → ℝ) (slotCount : ℕ) (ownValue : ℝ)
    (opponents : List ℝ) (history : Theorem8SourcePriceHistory)
    (hopponents : opponents.length ≤ slotCount)
    (hclick_pos : ∀ rank, rank < slotCount → 0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < slotCount →
      0 ≤ clickThroughRate (rank + 1))
    (hclick_mono : ∀ rank, rank < slotCount →
      clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hordered : opponents.Pairwise (· ≤ ·))
    (hcurrent_le : ∀ opponent ∈ opponents,
      theorem8SourcePriceHistoryLastDropout history ≤ opponent)
    (hown_le : ∀ opponent ∈ opponents, ownValue ≤ opponent) :
    theorem8OrderedOptimalUtility clickThroughRate ownValue opponents history ≤
      clickThroughRate opponents.length *
        (ownValue - theorem8SourcePriceHistoryLastDropout history) := by
  induction opponents generalizing history with
  | nil =>
      rfl
  | cons opponent remainingOpponents ih =>
      have hremaining_bound : remainingOpponents.length ≤ slotCount := by
        have htail_le : remainingOpponents.length ≤
            (opponent :: remainingOpponents).length := by simp
        exact htail_le.trans hopponents
      have hrank : remainingOpponents.length < slotCount := by
        have hcons_bound : remainingOpponents.length + 1 ≤ slotCount := by
          simpa using hopponents
        omega
      have hlast_le_opponent :
          theorem8SourcePriceHistoryLastDropout history ≤ opponent :=
        hcurrent_le opponent (by simp)
      have hown_le_opponent : ownValue ≤ opponent :=
        hown_le opponent (by simp)
      have hordered_tail : remainingOpponents.Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp hordered).2
      have hopponent_le_tail :
          ∀ other ∈ remainingOpponents, opponent ≤ other :=
        (List.pairwise_cons.mp hordered).1
      let rank := remainingOpponents.length
      let nextPrice := theorem8OrderedOpponentPrice clickThroughRate rank
        (theorem8SourcePriceHistoryLastDropout history) opponent
      have hnext_ge_current :
          theorem8SourcePriceHistoryLastDropout history ≤ nextPrice := by
        dsimp [nextPrice, rank]
        exact paper_theorem8_generalized_english_indifference_price_lastDropout_le
          (hclick_pos remainingOpponents.length hrank)
          (hclick_mono remainingOpponents.length hrank) hlast_le_opponent
      have hnext_le_opponent : nextPrice ≤ opponent := by
        dsimp [nextPrice, rank]
        exact paper_theorem8_generalized_english_indifference_price_le_value
          (hclick_pos remainingOpponents.length hrank)
          (hcurrent_nonneg remainingOpponents.length hrank) hlast_le_opponent
      have htail_current : ∀ other ∈ remainingOpponents,
          theorem8SourcePriceHistoryLastDropout (nextPrice :: history) ≤ other := by
        intro other hother
        simpa using hnext_le_opponent.trans (hopponent_le_tail other hother)
      have htail_own : ∀ other ∈ remainingOpponents,
          ownValue ≤ other := by
        intro other hother
        exact hown_le_opponent.trans (hopponent_le_tail other hother)
      have htail := ih (nextPrice :: history) hremaining_bound hordered_tail
        htail_current htail_own
      have hadjacent :
          clickThroughRate remainingOpponents.length *
              (ownValue - nextPrice) ≤
            clickThroughRate (remainingOpponents.length + 1) *
              (ownValue - theorem8SourcePriceHistoryLastDropout history) := by
        dsimp [nextPrice, rank]
        exact theorem8_ordered_adjacent_utility_antimono_of_own_le
          clickThroughRate remainingOpponents.length
          (theorem8SourcePriceHistoryLastDropout history)
          ownValue opponent (hclick_pos remainingOpponents.length hrank)
          (hclick_mono remainingOpponents.length hrank) hown_le_opponent
      have htail_bound :
          theorem8OrderedOptimalUtility clickThroughRate ownValue
              remainingOpponents (nextPrice :: history) ≤
            clickThroughRate (remainingOpponents.length + 1) *
              (ownValue - theorem8SourcePriceHistoryLastDropout history) :=
        htail.trans hadjacent
      simp only [theorem8OrderedOptimalUtility, List.length_cons]
      rw [show max
          (theorem8SourcePriceHistoryLastDropout history)
          (theorem8OrderedOpponentPrice clickThroughRate
            remainingOpponents.length
            (theorem8SourcePriceHistoryLastDropout history) opponent) =
          nextPrice by
        dsimp [nextPrice, rank]
        exact max_eq_right hnext_ge_current]
      exact max_le (le_refl _) htail_bound

/-- The named EOS plan realizes the ordered optimum over every finite source
opponent menu.  Its induction never asks for a positive CTR below the last
advertised slot: the final lower CTR is used only through nonnegativity. -/
theorem theorem8_ordered_named_utility_eq_optimal_finite
    (clickThroughRate : ℕ → ℝ) (slotCount : ℕ) (ownValue : ℝ)
    (opponents : List ℝ) (history : Theorem8SourcePriceHistory)
    (hopponents : opponents.length ≤ slotCount)
    (hclick_pos : ∀ rank, rank < slotCount → 0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < slotCount →
      0 ≤ clickThroughRate (rank + 1))
    (hclick_strict : ∀ rank, rank < slotCount →
      clickThroughRate (rank + 1) < clickThroughRate rank)
    (hordered : opponents.Pairwise (· ≤ ·))
    (hcurrent_le : ∀ opponent ∈ opponents,
      theorem8SourcePriceHistoryLastDropout history ≤ opponent)
    (hown_feasible :
      theorem8SourcePriceHistoryLastDropout history ≤ ownValue) :
    theorem8OrderedNamedUtility clickThroughRate ownValue opponents history =
      theorem8OrderedOptimalUtility clickThroughRate ownValue opponents history := by
  induction opponents generalizing history with
  | nil =>
      rfl
  | cons opponent remainingOpponents ih =>
      have hremaining_bound : remainingOpponents.length ≤ slotCount := by
        have htail_le : remainingOpponents.length ≤
            (opponent :: remainingOpponents).length := by simp
        exact htail_le.trans hopponents
      have hrank : remainingOpponents.length < slotCount := by
        have hcons_bound : remainingOpponents.length + 1 ≤ slotCount := by
          simpa using hopponents
        omega
      let rank := remainingOpponents.length
      let lastDropout := theorem8SourcePriceHistoryLastDropout history
      let ownPrice := theorem8OrderedOpponentPrice clickThroughRate rank
        lastDropout ownValue
      let opponentPrice := theorem8OrderedOpponentPrice clickThroughRate rank
        lastDropout opponent
      have hlast_le_opponent : lastDropout ≤ opponent :=
        hcurrent_le opponent (by simp)
      have hordered_tail : remainingOpponents.Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp hordered).2
      have hopponent_le_tail :
          ∀ other ∈ remainingOpponents, opponent ≤ other :=
        (List.pairwise_cons.mp hordered).1
      have hclick_mono : ∀ r, r < slotCount →
          clickThroughRate (r + 1) ≤ clickThroughRate r :=
        fun r hr => (hclick_strict r hr).le
      have hown_price_ge : lastDropout ≤ ownPrice := by
        dsimp [ownPrice, rank, lastDropout]
        exact paper_theorem8_generalized_english_indifference_price_lastDropout_le
          (hclick_pos remainingOpponents.length hrank)
          (hclick_mono remainingOpponents.length hrank) hown_feasible
      have hopponent_price_ge : lastDropout ≤ opponentPrice := by
        dsimp [opponentPrice, rank, lastDropout]
        exact paper_theorem8_generalized_english_indifference_price_lastDropout_le
          (hclick_pos remainingOpponents.length hrank)
          (hclick_mono remainingOpponents.length hrank) hlast_le_opponent
      have hopponent_price_le : opponentPrice ≤ opponent := by
        dsimp [opponentPrice, rank, lastDropout]
        exact paper_theorem8_generalized_english_indifference_price_le_value
          (hclick_pos remainingOpponents.length hrank)
          (hcurrent_nonneg remainingOpponents.length hrank) hlast_le_opponent
      have htail_current : ∀ other ∈ remainingOpponents,
          theorem8SourcePriceHistoryLastDropout (opponentPrice :: history) ≤
            other := by
        intro other hother
        simpa using hopponent_price_le.trans (hopponent_le_tail other hother)
      dsimp [ownPrice, opponentPrice, rank, lastDropout,
        theorem8OrderedOpponentPrice] at *
      rcases lt_trichotomy ownValue opponent with hown_lt | hown_eq | hopponent_lt
      · have hprice_lt : ownPrice < opponentPrice := by
          dsimp [ownPrice, opponentPrice, rank, lastDropout]
          exact paper_theorem8_generalized_english_indifference_price_strict_mono_value
            (hclick_pos remainingOpponents.length hrank)
            (hclick_strict remainingOpponents.length hrank) hown_lt
        have htail_own_le : ∀ other ∈ remainingOpponents,
            ownValue ≤ other := by
          intro other hother
          exact hown_lt.le.trans (hopponent_le_tail other hother)
        have htail_ceiling :=
          theorem8_ordered_optimal_utility_le_drop_of_own_le_all_finite
            clickThroughRate slotCount ownValue remainingOpponents
            (opponentPrice :: history) hremaining_bound hclick_pos
            hcurrent_nonneg hclick_mono hordered_tail htail_current htail_own_le
        have hadjacent :=
          theorem8_ordered_adjacent_utility_antimono_of_own_le
            clickThroughRate remainingOpponents.length lastDropout
            ownValue opponent (hclick_pos remainingOpponents.length hrank)
            (hclick_mono remainingOpponents.length hrank) hown_lt.le
        have htail_bound :
            theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents (opponentPrice :: history) ≤
              clickThroughRate (remainingOpponents.length + 1) *
                (ownValue - lastDropout) := by
          exact htail_ceiling.trans (by
            simpa [opponentPrice, rank] using hadjacent)
        have hprice_lt_raw :
            paper_theorem8_generalized_english_indifference_price
                (clickThroughRate remainingOpponents.length)
                (clickThroughRate (remainingOpponents.length + 1))
                (theorem8SourcePriceHistoryLastDropout history) ownValue <
              paper_theorem8_generalized_english_indifference_price
                (clickThroughRate remainingOpponents.length)
                (clickThroughRate (remainingOpponents.length + 1))
                (theorem8SourcePriceHistoryLastDropout history) opponent := by
          simpa [ownPrice, opponentPrice, rank, lastDropout,
            theorem8OrderedOpponentPrice] using hprice_lt
        simpa [theorem8OrderedNamedUtility,
          theorem8OrderedContinuationUtility,
          theorem8NamedContinuationPlan,
          theorem8OrderedOptimalUtility,
          theorem8OrderedOpponentPrice, hown_price_ge,
          hopponent_price_ge, hprice_lt_raw] using
          (max_eq_left htail_bound).symm
      · subst opponent
        have hprice_eq : ownPrice = opponentPrice := rfl
        have htail_feasible :
            theorem8SourcePriceHistoryLastDropout
                (opponentPrice :: history) ≤ ownValue := by
          simpa [opponentPrice, theorem8OrderedOpponentPrice] using
            (paper_theorem8_generalized_english_indifference_price_le_value
              (hclick_pos remainingOpponents.length hrank)
              (hcurrent_nonneg remainingOpponents.length hrank)
              hown_feasible)
        have htail_named := ih (opponentPrice :: history)
          hremaining_bound hordered_tail htail_current htail_feasible
        have htail_own_le : ∀ other ∈ remainingOpponents,
            ownValue ≤ other := hopponent_le_tail
        have htail_ceiling :=
          theorem8_ordered_optimal_utility_le_drop_of_own_le_all_finite
            clickThroughRate slotCount ownValue remainingOpponents
            (opponentPrice :: history) hremaining_bound hclick_pos
            hcurrent_nonneg hclick_mono hordered_tail htail_current htail_own_le
        have hadjacent_upper :
            clickThroughRate remainingOpponents.length *
                (ownValue - opponentPrice) ≤
              clickThroughRate (remainingOpponents.length + 1) *
                (ownValue - lastDropout) := by
          exact theorem8_ordered_adjacent_utility_antimono_of_own_le
            clickThroughRate remainingOpponents.length lastDropout
            ownValue ownValue (hclick_pos remainingOpponents.length hrank)
            (hclick_mono remainingOpponents.length hrank) (le_refl _)
        have htail_upper :
            theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents (opponentPrice :: history) ≤
              clickThroughRate (remainingOpponents.length + 1) *
                (ownValue - lastDropout) :=
          htail_ceiling.trans hadjacent_upper
        have hdrop_le_tail :
            clickThroughRate (remainingOpponents.length + 1) *
                (ownValue - lastDropout) ≤
              theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents (opponentPrice :: history) := by
          have hadjacent :=
            theorem8_ordered_adjacent_utility_mono_of_opponent_le
              clickThroughRate remainingOpponents.length lastDropout
              ownValue ownValue (hclick_pos remainingOpponents.length hrank)
              (hclick_mono remainingOpponents.length hrank) (le_refl _)
          have hadjacent' :
              clickThroughRate (remainingOpponents.length + 1) *
                  (ownValue - lastDropout) ≤
                clickThroughRate remainingOpponents.length *
                  (ownValue - opponentPrice) := by
            simpa [opponentPrice, rank, theorem8OrderedOpponentPrice] using
              hadjacent
          exact hadjacent'.trans
            (theorem8_ordered_drop_utility_le_optimal clickThroughRate
              ownValue remainingOpponents (opponentPrice :: history))
        have htail_eq :
            theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents (opponentPrice :: history) =
              clickThroughRate (remainingOpponents.length + 1) *
                (ownValue - lastDropout) :=
          le_antisymm htail_upper hdrop_le_tail
        have htail_named_raw :
            theorem8OrderedContinuationUtility clickThroughRate
                (theorem8NamedContinuationPlan clickThroughRate) ownValue
                remainingOpponents
                  (paper_theorem8_generalized_english_indifference_price
                    (clickThroughRate remainingOpponents.length)
                    (clickThroughRate (remainingOpponents.length + 1))
                    (theorem8SourcePriceHistoryLastDropout history)
                    ownValue :: history) =
              theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents
                  (paper_theorem8_generalized_english_indifference_price
                    (clickThroughRate remainingOpponents.length)
                    (clickThroughRate (remainingOpponents.length + 1))
                    (theorem8SourcePriceHistoryLastDropout history)
                    ownValue :: history) := by
          simpa [theorem8OrderedNamedUtility, opponentPrice, rank,
            lastDropout, theorem8OrderedOpponentPrice] using htail_named
        have htail_eq_raw :
            theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents
                  (paper_theorem8_generalized_english_indifference_price
                    (clickThroughRate remainingOpponents.length)
                    (clickThroughRate (remainingOpponents.length + 1))
                    (theorem8SourcePriceHistoryLastDropout history)
                    ownValue :: history) =
              clickThroughRate (remainingOpponents.length + 1) *
                (ownValue - theorem8SourcePriceHistoryLastDropout history) := by
          simpa [opponentPrice, rank, lastDropout,
            theorem8OrderedOpponentPrice] using htail_eq
        simp [theorem8OrderedNamedUtility,
          theorem8OrderedContinuationUtility,
          theorem8NamedContinuationPlan,
          theorem8OrderedOptimalUtility,
          theorem8OrderedOpponentPrice, hown_price_ge,
          htail_named_raw, htail_eq_raw]
      · have hprice_lt : opponentPrice < ownPrice := by
          dsimp [ownPrice, opponentPrice, rank, lastDropout]
          exact paper_theorem8_generalized_english_indifference_price_strict_mono_value
            (hclick_pos remainingOpponents.length hrank)
            (hclick_strict remainingOpponents.length hrank) hopponent_lt
        have htail_named := ih (opponentPrice :: history)
          hremaining_bound hordered_tail htail_current
          (hopponent_price_le.trans hopponent_lt.le)
        have hadjacent :=
          theorem8_ordered_adjacent_utility_mono_of_opponent_le
            clickThroughRate remainingOpponents.length lastDropout
            ownValue opponent (hclick_pos remainingOpponents.length hrank)
            (hclick_mono remainingOpponents.length hrank) hopponent_lt.le
        have hdrop_le_tail :
            clickThroughRate (remainingOpponents.length + 1) *
                (ownValue - lastDropout) ≤
              theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents (opponentPrice :: history) := by
          have hadjacent' :
              clickThroughRate (remainingOpponents.length + 1) *
                  (ownValue - lastDropout) ≤
                clickThroughRate remainingOpponents.length *
                  (ownValue - opponentPrice) := by
            simpa [opponentPrice, rank, theorem8OrderedOpponentPrice] using
              hadjacent
          exact hadjacent'.trans
            (theorem8_ordered_drop_utility_le_optimal clickThroughRate
              ownValue remainingOpponents (opponentPrice :: history))
        have hprice_lt_raw :
            paper_theorem8_generalized_english_indifference_price
                (clickThroughRate remainingOpponents.length)
                (clickThroughRate (remainingOpponents.length + 1))
                (theorem8SourcePriceHistoryLastDropout history) opponent <
              paper_theorem8_generalized_english_indifference_price
                (clickThroughRate remainingOpponents.length)
                (clickThroughRate (remainingOpponents.length + 1))
                (theorem8SourcePriceHistoryLastDropout history) ownValue := by
          simpa [ownPrice, opponentPrice, rank, lastDropout,
            theorem8OrderedOpponentPrice] using hprice_lt
        have hprice_not_reverse :
            ¬ paper_theorem8_generalized_english_indifference_price
                (clickThroughRate remainingOpponents.length)
                (clickThroughRate (remainingOpponents.length + 1))
                (theorem8SourcePriceHistoryLastDropout history) ownValue <
              paper_theorem8_generalized_english_indifference_price
                (clickThroughRate remainingOpponents.length)
                (clickThroughRate (remainingOpponents.length + 1))
                (theorem8SourcePriceHistoryLastDropout history) opponent :=
          not_lt_of_ge hprice_lt_raw.le
        have htail_named_raw :
            theorem8OrderedContinuationUtility clickThroughRate
                (theorem8NamedContinuationPlan clickThroughRate) ownValue
                remainingOpponents
                  (paper_theorem8_generalized_english_indifference_price
                    (clickThroughRate remainingOpponents.length)
                    (clickThroughRate (remainingOpponents.length + 1))
                    (theorem8SourcePriceHistoryLastDropout history)
                    opponent :: history) =
              theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents
                  (paper_theorem8_generalized_english_indifference_price
                    (clickThroughRate remainingOpponents.length)
                    (clickThroughRate (remainingOpponents.length + 1))
                    (theorem8SourcePriceHistoryLastDropout history)
                    opponent :: history) := by
          simpa [theorem8OrderedNamedUtility, opponentPrice, rank,
            lastDropout, theorem8OrderedOpponentPrice] using htail_named
        have hdrop_le_tail_raw :
            clickThroughRate (remainingOpponents.length + 1) *
                (ownValue - theorem8SourcePriceHistoryLastDropout history) ≤
              theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents
                  (paper_theorem8_generalized_english_indifference_price
                    (clickThroughRate remainingOpponents.length)
                    (clickThroughRate (remainingOpponents.length + 1))
                    (theorem8SourcePriceHistoryLastDropout history)
                    opponent :: history) := by
          simpa [opponentPrice, rank, lastDropout,
            theorem8OrderedOpponentPrice] using hdrop_le_tail
        simp [theorem8OrderedNamedUtility,
          theorem8OrderedContinuationUtility,
          theorem8NamedContinuationPlan,
          theorem8OrderedOptimalUtility,
          theorem8OrderedOpponentPrice, hown_price_ge,
          hopponent_price_ge, hprice_lt_raw, hprice_not_reverse,
          htail_named_raw, max_eq_right hdrop_le_tail_raw]

/-- The named plan is an ex-post best response against every complete
continuation deviation in the finite source market. -/
theorem theorem8_named_plan_finite_ordered_ex_post_best_response
    (clickThroughRate : ℕ → ℝ) (slotCount : ℕ)
    (hclick_pos : ∀ rank, rank < slotCount → 0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < slotCount →
      0 ≤ clickThroughRate (rank + 1))
    (hclick_strict : ∀ rank, rank < slotCount →
      clickThroughRate (rank + 1) < clickThroughRate rank) :
    Theorem8FiniteOrderedExPostBestResponse clickThroughRate slotCount
      (theorem8NamedContinuationPlan clickThroughRate) := by
  intro ownValue opponents history hopponents hvalid hown deviation
  calc
    theorem8OrderedContinuationUtility clickThroughRate deviation ownValue
        opponents history ≤
      theorem8OrderedOptimalUtility clickThroughRate ownValue opponents history :=
        theorem8_ordered_continuation_utility_le_optimal
          clickThroughRate deviation ownValue opponents history
    _ = theorem8OrderedNamedUtility clickThroughRate ownValue opponents history :=
      (theorem8_ordered_named_utility_eq_optimal_finite
        clickThroughRate slotCount ownValue opponents history hopponents
        hclick_pos hcurrent_nonneg hclick_strict hvalid.1 hvalid.2 hown).symm

/-- The named formula is a symmetric-continuation finite legal-history ex-post
PBE under the source's positive advertised CTRs and zero-allowed lower
boundary. -/
theorem theorem8_named_finite_legal_history_ex_post_pbe
    (Bidder : Type*) (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ) (slotCount : ℕ)
    (hclick_pos : ∀ rank, rank < slotCount → 0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < slotCount →
      0 ≤ clickThroughRate (rank + 1))
    (hclick_strict : ∀ rank, rank < slotCount →
      clickThroughRate (rank + 1) < clickThroughRate rank) :
    Theorem8FiniteLegalHistoryExPostPBE Bidder law clickThroughRate slotCount
      (theorem8NamedContinuationPlan clickThroughRate) := by
  refine ⟨theorem8_named_continuation_plan_continuous clickThroughRate,
    theorem8_named_history_strategy_finite_clock_legal_on_feasible_history
      clickThroughRate slotCount hclick_pos
      (fun rank hrank => (hclick_strict rank hrank).le),
    theorem8_named_finite_history_bayes_consistent law clickThroughRate,
    theorem8_named_plan_finite_ordered_ex_post_best_response
      clickThroughRate slotCount hclick_pos hcurrent_nonneg hclick_strict⟩

/-- In the finite source market, ex-post optimality pins down the observable
dropout action at each advertised rank.  The proof tests a candidate action
against only `rank + 1 ≤ slotCount` opponents, so it does not require a
fictional positive CTR below the source's final slot. -/
theorem theorem8_finite_ordered_ex_post_best_response_effective_price_unique
    (clickThroughRate : ℕ → ℝ) (slotCount : ℕ)
    (plan : Theorem8ContinuationPlan)
    (hclick_pos : ∀ rank, rank < slotCount → 0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < slotCount →
      0 ≤ clickThroughRate (rank + 1))
    (hclick_strict : ∀ rank, rank < slotCount →
      clickThroughRate (rank + 1) < clickThroughRate rank)
    (hbest : Theorem8FiniteOrderedExPostBestResponse clickThroughRate slotCount plan)
    (rank : ℕ) (history : Theorem8SourcePriceHistory) (ownValue : ℝ)
    (hrank : rank < slotCount)
    (hown_feasible :
      theorem8SourcePriceHistoryLastDropout history ≤ ownValue) :
    max (theorem8SourcePriceHistoryLastDropout history)
        (plan rank history ownValue) =
      paper_theorem8_generalized_english_indifference_price
        (clickThroughRate rank) (clickThroughRate (rank + 1))
        (theorem8SourcePriceHistoryLastDropout history) ownValue := by
  let lastDropout := theorem8SourcePriceHistoryLastDropout history
  let namedPrice :=
    paper_theorem8_generalized_english_indifference_price
      (clickThroughRate rank) (clickThroughRate (rank + 1))
      lastDropout ownValue
  let effectivePrice := max lastDropout (plan rank history ownValue)
  have hclick_mono : clickThroughRate (rank + 1) ≤
      clickThroughRate rank := (hclick_strict rank hrank).le
  have hnamed_ge : lastDropout ≤ namedPrice := by
    dsimp [namedPrice, lastDropout]
    exact
      paper_theorem8_generalized_english_indifference_price_lastDropout_le
        (hclick_pos rank hrank) hclick_mono hown_feasible
  rcases lt_trichotomy effectivePrice namedPrice with htoo_early | heq | htoo_late
  · let targetPrice := (effectivePrice + namedPrice) / 2
    have heffective_lt_target : effectivePrice < targetPrice := by
      dsimp [targetPrice]
      linarith
    have htarget_lt_named : targetPrice < namedPrice := by
      dsimp [targetPrice]
      linarith
    have hlast_lt_target : lastDropout < targetPrice := by
      have hlast_le_effective : lastDropout ≤ effectivePrice :=
        le_max_left _ _
      exact hlast_le_effective.trans_lt heffective_lt_target
    let opponentValue := theorem8IndifferenceValueAtPrice
      (clickThroughRate rank) (clickThroughRate (rank + 1))
      lastDropout targetPrice
    have hopponent_price :
        paper_theorem8_generalized_english_indifference_price
            (clickThroughRate rank) (clickThroughRate (rank + 1))
            lastDropout opponentValue = targetPrice := by
      dsimp [opponentValue]
      exact theorem8_indifference_price_value_at_price
        (hclick_pos rank hrank) (hclick_strict rank hrank)
    have hopponent_lt_own : opponentValue < ownValue := by
      apply theorem8_indifference_value_at_price_lt_of_lt_price
        (hclick_pos rank hrank) (hclick_strict rank hrank)
      simpa [namedPrice] using htarget_lt_named
    have hlast_lt_opponent : lastDropout < opponentValue := by
      apply theorem8_indifference_value_at_price_lt_of_price_lt
        (hclick_pos rank hrank) (hclick_strict rank hrank)
      simpa using hlast_lt_target
    let opponents := opponentValue :: List.replicate rank opponentValue
    have hopponents_bound : opponents.length ≤ slotCount := by
      simp [opponents]
      omega
    have hopponents_valid :
        Theorem8OrderedOpponentProfileValid history opponents := by
      constructor
      · simp [opponents]
      · intro opponent hopponent
        rcases List.mem_cons.mp hopponent with rfl | hreplicate
        · exact hlast_lt_opponent.le
        · have heq := (List.mem_replicate.mp hreplicate).2
          simpa [heq] using hlast_lt_opponent.le
    let dropUtility := clickThroughRate (rank + 1) *
      (ownValue - lastDropout)
    have hplan_eq_drop :
        theorem8OrderedContinuationUtility clickThroughRate plan ownValue
            opponents history = dropUtility := by
      simp [opponents, theorem8OrderedContinuationUtility, effectivePrice,
        lastDropout, opponentValue, hopponent_price,
        max_eq_right hlast_lt_target.le, heffective_lt_target, dropUtility]
    have hnamed_eq_optimal :=
      theorem8_ordered_named_utility_eq_optimal_finite clickThroughRate
        slotCount ownValue opponents history hopponents_bound hclick_pos
        hcurrent_nonneg hclick_strict hopponents_valid.1 hopponents_valid.2
        hown_feasible
    have hadjacent : dropUtility <
        clickThroughRate rank * (ownValue - targetPrice) := by
      have hstrict :=
        theorem8_ordered_adjacent_utility_strict_mono_of_opponent_lt
          clickThroughRate rank lastDropout ownValue opponentValue
          (hclick_pos rank hrank) (hclick_strict rank hrank) hopponent_lt_own
      simpa [dropUtility, theorem8OrderedOpponentPrice,
        hopponent_price] using hstrict
    have himmediate_le_tail :
        clickThroughRate rank * (ownValue - targetPrice) ≤
          theorem8OrderedOptimalUtility clickThroughRate ownValue
            (List.replicate rank opponentValue) (targetPrice :: history) := by
      simpa using theorem8_ordered_drop_utility_le_optimal
        clickThroughRate ownValue (List.replicate rank opponentValue)
        (targetPrice :: history)
    have htail_le_full :
        theorem8OrderedOptimalUtility clickThroughRate ownValue
            (List.replicate rank opponentValue) (targetPrice :: history) ≤
          theorem8OrderedOptimalUtility clickThroughRate ownValue
            opponents history := by
      have hnext_price :
          max (theorem8SourcePriceHistoryLastDropout history)
              (theorem8OrderedOpponentPrice clickThroughRate rank
                (theorem8SourcePriceHistoryLastDropout history)
                opponentValue) = targetPrice := by
        simpa [theorem8OrderedOpponentPrice, lastDropout,
          hopponent_price] using
            (max_eq_right hlast_lt_target.le :
              max (theorem8SourcePriceHistoryLastDropout history)
                targetPrice = targetPrice)
      simp only [opponents, theorem8OrderedOptimalUtility,
        List.length_replicate]
      rw [hnext_price]
      exact le_max_right _ _
    have hdrop_lt_named : dropUtility <
        theorem8OrderedNamedUtility clickThroughRate ownValue
          opponents history := by
      calc
        dropUtility < clickThroughRate rank * (ownValue - targetPrice) :=
          hadjacent
        _ ≤ theorem8OrderedOptimalUtility clickThroughRate ownValue
            (List.replicate rank opponentValue) (targetPrice :: history) :=
          himmediate_le_tail
        _ ≤ theorem8OrderedOptimalUtility clickThroughRate ownValue
            opponents history := htail_le_full
        _ = theorem8OrderedNamedUtility clickThroughRate ownValue
            opponents history := hnamed_eq_optimal.symm
    have hnamed_le_plan := hbest ownValue opponents history hopponents_bound
      hopponents_valid hown_feasible
      (theorem8NamedContinuationPlan clickThroughRate)
    have hnamed_le_drop :
        theorem8OrderedNamedUtility clickThroughRate ownValue opponents history ≤
          dropUtility := by
      simpa [theorem8OrderedNamedUtility, hplan_eq_drop] using hnamed_le_plan
    exact ((not_lt_of_ge hnamed_le_drop) hdrop_lt_named).elim
  · simpa [effectivePrice, namedPrice, lastDropout] using heq
  · let targetPrice := (namedPrice + effectivePrice) / 2
    have hnamed_lt_target : namedPrice < targetPrice := by
      dsimp [targetPrice]
      linarith
    have htarget_lt_effective : targetPrice < effectivePrice := by
      dsimp [targetPrice]
      linarith
    have hlast_lt_target : lastDropout < targetPrice :=
      hnamed_ge.trans_lt hnamed_lt_target
    let opponentValue := theorem8IndifferenceValueAtPrice
      (clickThroughRate rank) (clickThroughRate (rank + 1))
      lastDropout targetPrice
    have hopponent_price :
        paper_theorem8_generalized_english_indifference_price
            (clickThroughRate rank) (clickThroughRate (rank + 1))
            lastDropout opponentValue = targetPrice := by
      dsimp [opponentValue]
      exact theorem8_indifference_price_value_at_price
        (hclick_pos rank hrank) (hclick_strict rank hrank)
    have hown_lt_opponent : ownValue < opponentValue := by
      apply theorem8_indifference_value_at_price_lt_of_price_lt
        (hclick_pos rank hrank) (hclick_strict rank hrank)
      simpa [namedPrice] using hnamed_lt_target
    have hlast_lt_opponent : lastDropout < opponentValue := by
      apply theorem8_indifference_value_at_price_lt_of_price_lt
        (hclick_pos rank hrank) (hclick_strict rank hrank)
      simpa using hlast_lt_target
    let opponents := opponentValue :: List.replicate rank opponentValue
    have hopponents_bound : opponents.length ≤ slotCount := by
      simp [opponents]
      omega
    have hopponents_valid :
        Theorem8OrderedOpponentProfileValid history opponents := by
      constructor
      · simp [opponents]
      · intro opponent hopponent
        rcases List.mem_cons.mp hopponent with rfl | hreplicate
        · exact hlast_lt_opponent.le
        · have heq := (List.mem_replicate.mp hreplicate).2
          simpa [heq] using hlast_lt_opponent.le
    let dropUtility := clickThroughRate (rank + 1) *
      (ownValue - lastDropout)
    have hplan_eq_continue :
        theorem8OrderedContinuationUtility clickThroughRate plan ownValue
            opponents history =
          theorem8OrderedContinuationUtility clickThroughRate plan ownValue
            (List.replicate rank opponentValue) (targetPrice :: history) := by
      have hown_max :
          max (theorem8SourcePriceHistoryLastDropout history)
              (plan rank history ownValue) = effectivePrice := by
        rfl
      have hopponent_max :
          max (theorem8SourcePriceHistoryLastDropout history)
              (paper_theorem8_generalized_english_indifference_price
                (clickThroughRate rank) (clickThroughRate (rank + 1))
                (theorem8SourcePriceHistoryLastDropout history)
                opponentValue) = targetPrice := by
        simpa [lastDropout, hopponent_price] using
          (max_eq_right hlast_lt_target.le :
            max (theorem8SourcePriceHistoryLastDropout history)
              targetPrice = targetPrice)
      simp [opponents, theorem8OrderedContinuationUtility, hown_max,
        hopponent_max, htarget_lt_effective,
        not_lt_of_ge htarget_lt_effective.le]
    have hplan_tail_le_optimal :=
      theorem8_ordered_continuation_utility_le_optimal clickThroughRate plan
        ownValue (List.replicate rank opponentValue) (targetPrice :: history)
    have htail_valid :
        Theorem8OrderedOpponentProfileValid (targetPrice :: history)
          (List.replicate rank opponentValue) := by
      constructor
      · simp
      · have htarget_le_opponent : targetPrice ≤ opponentValue := by
          rw [← hopponent_price]
          exact
            paper_theorem8_generalized_english_indifference_price_le_value
              (hclick_pos rank hrank) (hcurrent_nonneg rank hrank)
              hlast_lt_opponent.le
        simp [htarget_le_opponent]
    have htail_bound : (List.replicate rank opponentValue).length ≤ slotCount := by
      simp
      exact Nat.le_of_lt hrank
    have htail_ceiling :=
      theorem8_ordered_optimal_utility_le_drop_of_own_le_all_finite
        clickThroughRate slotCount ownValue (List.replicate rank opponentValue)
        (targetPrice :: history) htail_bound hclick_pos hcurrent_nonneg
        (fun r hr => (hclick_strict r hr).le) htail_valid.1 htail_valid.2
        (by
          intro opponent hopponent
          simp only [List.mem_replicate] at hopponent
          simpa [hopponent] using hown_lt_opponent.le)
    have hadjacent :
        clickThroughRate rank * (ownValue - targetPrice) < dropUtility := by
      have hstrict :=
        theorem8_ordered_adjacent_utility_strict_antimono_of_own_lt
          clickThroughRate rank lastDropout ownValue opponentValue
          (hclick_pos rank hrank) (hclick_strict rank hrank) hown_lt_opponent
      simpa [dropUtility, theorem8OrderedOpponentPrice,
        hopponent_price] using hstrict
    have hplan_lt_drop :
        theorem8OrderedContinuationUtility clickThroughRate plan ownValue
            opponents history < dropUtility := by
      rw [hplan_eq_continue]
      have htail_ceiling' :
          theorem8OrderedOptimalUtility clickThroughRate ownValue
              (List.replicate rank opponentValue) (targetPrice :: history) ≤
            clickThroughRate rank * (ownValue - targetPrice) := by
        simpa using htail_ceiling
      exact hplan_tail_le_optimal.trans_lt
        (htail_ceiling'.trans_lt hadjacent)
    have hnamed_eq_drop :
        theorem8OrderedContinuationUtility clickThroughRate
            (theorem8NamedContinuationPlan clickThroughRate) ownValue
            opponents history = dropUtility := by
      simp [opponents, theorem8OrderedContinuationUtility,
        theorem8NamedContinuationPlan, namedPrice, lastDropout,
        opponentValue, hopponent_price, hnamed_ge,
        max_eq_right hlast_lt_target.le, hnamed_lt_target, dropUtility]
    have hnamed_le_plan := hbest ownValue opponents history hopponents_bound
      hopponents_valid hown_feasible
      (theorem8NamedContinuationPlan clickThroughRate)
    rw [hnamed_eq_drop] at hnamed_le_plan
    exact ((not_lt_of_ge hnamed_le_plan) hplan_lt_drop).elim

/-- Finite legal-history existence and uniqueness endpoint under the declared
symmetric-continuation convention. Observable actions are unique at advertised
ranks; thresholds behind the stopped clock remain behaviorally identical
immediate-drop instructions. -/
theorem theorem8_finite_legal_history_ex_post_pbe_exists_unique
    (Bidder : Type*) (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ) (slotCount : ℕ)
    (hclick_pos : ∀ rank, rank < slotCount → 0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < slotCount →
      0 ≤ clickThroughRate (rank + 1))
    (hclick_strict : ∀ rank, rank < slotCount →
      clickThroughRate (rank + 1) < clickThroughRate rank) :
    Theorem8FiniteLegalHistoryExPostPBE Bidder law clickThroughRate slotCount
        (theorem8NamedContinuationPlan clickThroughRate) ∧
      ∀ plan : Theorem8ContinuationPlan,
        Theorem8FiniteLegalHistoryExPostPBE Bidder law clickThroughRate
          slotCount plan →
          ∀ rank history ownValue,
            rank < slotCount →
            theorem8SourcePriceHistoryLastDropout history ≤ ownValue →
              max (theorem8SourcePriceHistoryLastDropout history)
                  (plan rank history ownValue) =
                paper_theorem8_generalized_english_indifference_price
                  (clickThroughRate rank) (clickThroughRate (rank + 1))
                  (theorem8SourcePriceHistoryLastDropout history)
                  ownValue := by
  refine ⟨theorem8_named_finite_legal_history_ex_post_pbe Bidder law
      clickThroughRate slotCount hclick_pos hcurrent_nonneg hclick_strict, ?_⟩
  intro plan hpbe rank history ownValue hrank hfeasible
  exact theorem8_finite_ordered_ex_post_best_response_effective_price_unique
    clickThroughRate slotCount plan hclick_pos hcurrent_nonneg hclick_strict
    hpbe.2.2.2 rank history ownValue hrank hfeasible

/-- The source's finite zero-bottom market has the named legal-history PBE,
its advertised-rank action uniqueness, and the concrete stopped-clock GSP
ledger whose rankwise total payments are VCG tails.  The outcome clauses are
kept as explicit terminal-ledger facts so no certificate or unproved
allocation/payment identity is hidden in the PBE predicate. -/
theorem theorem8_named_finite_legal_history_pbe_terminal_vcg_ledger
    [Fintype Bidder] [DecidableEq Bidder] [Nonempty Bidder]
    (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (htwo : 1 < Fintype.card Bidder)
    (hvalue_nonneg : ∀ bidder, 0 ≤ values bidder)
    (hclick_pos : ∀ rank, rank < Fintype.card Bidder - 1 →
      0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < Fintype.card Bidder - 1 →
      0 ≤ clickThroughRate (rank + 1))
    (hclick_strict : ∀ rank, rank < Fintype.card Bidder - 1 →
      clickThroughRate (rank + 1) < clickThroughRate rank)
    (hbottom_zero : clickThroughRate (Fintype.card Bidder - 1) = 0)
    (defaultBidder : Bidder) :
    let plan := theorem8NamedContinuationPlan clickThroughRate
    let strategy := theorem8ContinuousHistoryStrategy Bidder clickThroughRate
    let finalState := theorem8StoppedSourceFinalState strategy values
    let initialState := theorem8StoppedSourceInitialState Bidder
    let hremaining : initialState.remaining.Nonempty := Finset.univ_nonempty
    let rankedValue := theorem8StoppedSourceTerminalRankedValue strategy values
      initialState hremaining defaultBidder
    Theorem8FiniteLegalHistoryExPostPBE Bidder law clickThroughRate
        (Fintype.card Bidder - 1) plan ∧
      (∀ otherPlan : Theorem8ContinuationPlan,
        Theorem8FiniteLegalHistoryExPostPBE Bidder law clickThroughRate
          (Fintype.card Bidder - 1) otherPlan →
          ∀ rank history ownValue,
            rank < Fintype.card Bidder - 1 →
            theorem8SourcePriceHistoryLastDropout history ≤ ownValue →
              max (theorem8SourcePriceHistoryLastDropout history)
                  (otherPlan rank history ownValue) =
                paper_theorem8_generalized_english_indifference_price
                  (clickThroughRate rank) (clickThroughRate (rank + 1))
                  (theorem8SourcePriceHistoryLastDropout history)
                  ownValue) ∧
      plan.historyStrategy Bidder = strategy ∧
      (theorem8StoppedSourceFinalRankedBidders strategy values).toFinset =
        Finset.univ ∧
      (theorem8StoppedSourceFinalRankedBidders strategy values).Pairwise
        (fun earlier later => values later ≤ values earlier) ∧
      (∀ bidder, bidder ∈ finalState.remaining →
        finalState.terminalGSPOutcome.slotOf bidder = some 0 ∧
          finalState.terminalGSPOutcome.paymentPerClick bidder =
            finalState.history.getD 0 0) ∧
      (∀ bidder, bidder ∉ finalState.remaining →
        bidder ∈ finalState.dropped.dropLast →
          finalState.terminalGSPOutcome.slotOf bidder =
              some (finalState.dropped.idxOf bidder + 1) ∧
            finalState.terminalGSPOutcome.paymentPerClick bidder =
              finalState.history.getD (finalState.dropped.idxOf bidder + 1) 0) ∧
      (∀ bidder, bidder ∉ finalState.remaining →
        bidder ∉ finalState.dropped.dropLast →
          finalState.terminalGSPOutcome.slotOf bidder = none) ∧
      ∀ index, index < finalState.history.length →
        clickThroughRate index * finalState.history.getD index 0 =
          paper_theorem7_ranked_vcg_tail_payment rankedValue clickThroughRate
            index (finalState.dropped.length - index) := by
  dsimp
  have hpbe_unique := theorem8_finite_legal_history_ex_post_pbe_exists_unique
    Bidder law clickThroughRate (Fintype.card Bidder - 1) hclick_pos
    hcurrent_nonneg hclick_strict
  refine ⟨hpbe_unique.1, hpbe_unique.2,
      theorem8_named_plan_history_strategy_eq Bidder clickThroughRate,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact theorem8_stopped_source_final_ranked_bidders_toFinset
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate) values
  · exact theorem8_named_stopped_source_final_ranked_bidders_values_nonincreasing
      clickThroughRate values hvalue_nonneg hclick_pos hcurrent_nonneg
      hclick_strict
  · intro bidder hactive
    exact theorem8_terminal_gsp_outcome_survivor _ bidder hactive
  · intro bidder hinactive hdropped
    exact theorem8_terminal_gsp_outcome_later_dropper _ bidder hinactive hdropped
  · intro bidder hinactive hfirst
    exact theorem8_terminal_gsp_outcome_first_dropper_unassigned _ bidder
      hinactive hfirst
  · intro index hindex
    exact theorem8_named_stopped_source_final_history_total_payment_eq_vcg_tail
      clickThroughRate values htwo hvalue_nonneg hclick_pos hcurrent_nonneg
      hclick_strict hbottom_zero defaultBidder index hindex

end

end PaperInterface
end EOS07GSP
