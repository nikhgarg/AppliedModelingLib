import EOS07GSP.BayesianPBE

/-!
# EOS07 Theorem 8: arbitrary-continuation ex-post optimality

The source's existence argument is ex post.  Once the other surviving bidders
are written in increasing order of value, their named dropout prices occur in
that same order.  This file uses that ordered reduction to compare the named
plan with an *arbitrary full history-dependent continuation plan*.

Unlike the older local-payoff checker, the recursive payoff below executes the
deviating plan at every subsequent public history.  The proof is driven by the
source indifference identity: after an opponent of value `v` drops, the change
between adjacent-slot utilities has the sign of `ownValue - v`.
-/

namespace EOS07GSP
namespace PaperInterface

noncomputable section

open MeasureTheory Set

/-! ## Ordered continuation game -/

/-- A common (symmetric) complete continuation plan.  It may depend on the
remaining rank, the entire public dropout-price history, and own value, but
has no bidder-identity coordinate.  Applying `historyStrategy` below yields a
bidder-indexed profile that uses this same plan at every identity.  This is a
deliberate finite formalization scope restriction, not a representation of
arbitrary bidder-indexed source strategy profiles. -/
abbrev Theorem8ContinuationPlan :=
  ℕ → Theorem8SourcePriceHistory → ℝ → ℝ

/-- The named EOS continuation plan, before the operational current-clock
clamp. -/
def theorem8NamedContinuationPlan
    (clickThroughRate : ℕ → ℝ) : Theorem8ContinuationPlan :=
  fun rank history ownValue =>
    paper_theorem8_generalized_english_indifference_price
      (clickThroughRate rank) (clickThroughRate (rank + 1))
      (theorem8SourcePriceHistoryLastDropout history) ownValue

/-- Realized payoff against opponents listed in increasing value order.

At a nonterminal node, `opponent :: remainingOpponents` is the lowest-valued
opponent still active.  The opponent uses the named EOS threshold; the focal
bidder uses the supplied arbitrary continuation plan.  A threshold below the
stopped clock is clamped to the current price, and equality is averaged by the
source's uniform two-way tie rule. -/
def theorem8OrderedContinuationUtility
    (clickThroughRate : ℕ → ℝ)
    (plan : Theorem8ContinuationPlan) (ownValue : ℝ) :
    List ℝ → Theorem8SourcePriceHistory → ℝ
  | [], history =>
      clickThroughRate 0 *
        (ownValue - theorem8SourcePriceHistoryLastDropout history)
  | opponent :: remainingOpponents, history =>
      let rank := remainingOpponents.length
      let lastDropout := theorem8SourcePriceHistoryLastDropout history
      let ownPrice := max lastDropout (plan rank history ownValue)
      let opponentPrice := max lastDropout
        (paper_theorem8_generalized_english_indifference_price
          (clickThroughRate rank) (clickThroughRate (rank + 1))
          lastDropout opponent)
      let dropUtility := clickThroughRate (rank + 1) *
        (ownValue - lastDropout)
      let continueUtility := theorem8OrderedContinuationUtility
        clickThroughRate plan ownValue remainingOpponents
          (opponentPrice :: history)
      if ownPrice < opponentPrice then dropUtility
      else if opponentPrice < ownPrice then continueUtility
      else (dropUtility + continueUtility) / 2

/-- Utility of the named EOS plan in the ordered continuation game. -/
def theorem8OrderedNamedUtility
    (clickThroughRate : ℕ → ℝ) (ownValue : ℝ)
    (opponents : List ℝ) (history : Theorem8SourcePriceHistory) : ℝ :=
  theorem8OrderedContinuationUtility clickThroughRate
    (theorem8NamedContinuationPlan clickThroughRate)
    ownValue opponents history

/-- The next named opponent price before clamping. -/
def theorem8OrderedOpponentPrice
    (clickThroughRate : ℕ → ℝ) (rank : ℕ)
    (lastDropout opponent : ℝ) : ℝ :=
  paper_theorem8_generalized_english_indifference_price
    (clickThroughRate rank) (clickThroughRate (rank + 1))
    lastDropout opponent

/-- The best payoff available from all stopping positions against the ordered
opponents.  This is defined independently of any strategy: at each node the
bidder may take the current lower slot or allow the next opponent to drop and
choose optimally later. -/
def theorem8OrderedOptimalUtility
    (clickThroughRate : ℕ → ℝ) (ownValue : ℝ) :
    List ℝ → Theorem8SourcePriceHistory → ℝ
  | [], history =>
      clickThroughRate 0 *
        (ownValue - theorem8SourcePriceHistoryLastDropout history)
  | opponent :: remainingOpponents, history =>
      let rank := remainingOpponents.length
      let lastDropout := theorem8SourcePriceHistoryLastDropout history
      let opponentPrice := max lastDropout
        (theorem8OrderedOpponentPrice clickThroughRate rank
          lastDropout opponent)
      max
        (clickThroughRate (rank + 1) * (ownValue - lastDropout))
        (theorem8OrderedOptimalUtility clickThroughRate ownValue
          remainingOpponents (opponentPrice :: history))

/-- Whatever a full history-dependent plan does, its realized payoff is no
larger than the best payoff among the finitely many stopping positions.  This
lemma uses the plan at every recursive history and also covers randomized tie
payoffs. -/
theorem theorem8_ordered_continuation_utility_le_optimal
    (clickThroughRate : ℕ → ℝ) (plan : Theorem8ContinuationPlan)
    (ownValue : ℝ) (opponents : List ℝ)
    (history : Theorem8SourcePriceHistory) :
    theorem8OrderedContinuationUtility clickThroughRate plan ownValue
        opponents history ≤
      theorem8OrderedOptimalUtility clickThroughRate ownValue
        opponents history := by
  induction opponents generalizing history with
  | nil =>
      rfl
  | cons opponent remainingOpponents ih =>
      simp only [theorem8OrderedContinuationUtility,
        theorem8OrderedOptimalUtility]
      split
      · exact le_max_left _ _
      · split
        · exact (ih _).trans (le_max_right _ _)
        · have hdrop := le_max_left
            (clickThroughRate (remainingOpponents.length + 1) *
              (ownValue - theorem8SourcePriceHistoryLastDropout history))
            (theorem8OrderedOptimalUtility clickThroughRate ownValue
              remainingOpponents
                (max (theorem8SourcePriceHistoryLastDropout history)
                  (theorem8OrderedOpponentPrice clickThroughRate
                    remainingOpponents.length
                    (theorem8SourcePriceHistoryLastDropout history)
                    opponent) :: history))
          have hcontinue := (ih _).trans (le_max_right
            (clickThroughRate (remainingOpponents.length + 1) *
              (ownValue - theorem8SourcePriceHistoryLastDropout history))
            (theorem8OrderedOptimalUtility clickThroughRate ownValue
              remainingOpponents
                (max (theorem8SourcePriceHistoryLastDropout history)
                  (theorem8OrderedOpponentPrice clickThroughRate
                    remainingOpponents.length
                    (theorem8SourcePriceHistoryLastDropout history)
                    opponent) :: history)))
          have hcontinue' :
              theorem8OrderedContinuationUtility clickThroughRate plan ownValue
                  remainingOpponents
                    (max (theorem8SourcePriceHistoryLastDropout history)
                      (paper_theorem8_generalized_english_indifference_price
                        (clickThroughRate remainingOpponents.length)
                        (clickThroughRate (remainingOpponents.length + 1))
                        (theorem8SourcePriceHistoryLastDropout history)
                        opponent) :: history) ≤
                max
                  (clickThroughRate (remainingOpponents.length + 1) *
                    (ownValue -
                      theorem8SourcePriceHistoryLastDropout history))
                  (theorem8OrderedOptimalUtility clickThroughRate ownValue
                    remainingOpponents
                      (max (theorem8SourcePriceHistoryLastDropout history)
                        (theorem8OrderedOpponentPrice clickThroughRate
                          remainingOpponents.length
                          (theorem8SourcePriceHistoryLastDropout history)
                          opponent) :: history)) := by
            simpa [theorem8OrderedOpponentPrice] using hcontinue
          linarith

/-! ## Adjacent-slot algebra -/

/-- The payoff change from allowing one more opponent to drop is exactly the
adjacent click-rate gap times the difference in values.  This is the algebraic
engine of the paper's ex-post argument. -/
theorem theorem8_ordered_adjacent_utility_sub
    (clickThroughRate : ℕ → ℝ) (rank : ℕ)
    (lastDropout ownValue opponent : ℝ)
    (hclick_pos : 0 < clickThroughRate rank) :
    clickThroughRate rank *
          (ownValue - theorem8OrderedOpponentPrice clickThroughRate rank
            lastDropout opponent) -
        clickThroughRate (rank + 1) * (ownValue - lastDropout) =
      (clickThroughRate rank - clickThroughRate (rank + 1)) *
        (ownValue - opponent) := by
  unfold theorem8OrderedOpponentPrice
  have hindiff :=
    paper_theorem8_generalized_english_indifference_price_eq
      (alphaCurrent := clickThroughRate (rank + 1))
      (lastDropout := lastDropout) (value := opponent)
      (ne_of_gt hclick_pos)
  nlinarith

/-- Continuing past a lower-valued opponent weakly improves the adjacent-slot
payoff. -/
theorem theorem8_ordered_adjacent_utility_mono_of_opponent_le
    (clickThroughRate : ℕ → ℝ) (rank : ℕ)
    (lastDropout ownValue opponent : ℝ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hclick_mono : clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hopponent_le : opponent ≤ ownValue) :
    clickThroughRate (rank + 1) * (ownValue - lastDropout) ≤
      clickThroughRate rank *
        (ownValue - theorem8OrderedOpponentPrice clickThroughRate rank
          lastDropout opponent) := by
  have hid := theorem8_ordered_adjacent_utility_sub clickThroughRate rank
    lastDropout ownValue opponent hclick_pos
  nlinarith [mul_nonneg (sub_nonneg.mpr hclick_mono)
    (sub_nonneg.mpr hopponent_le)]

/-- Continuing past a higher-valued opponent weakly worsens the adjacent-slot
payoff. -/
theorem theorem8_ordered_adjacent_utility_antimono_of_own_le
    (clickThroughRate : ℕ → ℝ) (rank : ℕ)
    (lastDropout ownValue opponent : ℝ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hclick_mono : clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hown_le : ownValue ≤ opponent) :
    clickThroughRate rank *
        (ownValue - theorem8OrderedOpponentPrice clickThroughRate rank
          lastDropout opponent) ≤
      clickThroughRate (rank + 1) * (ownValue - lastDropout) := by
  have hid := theorem8_ordered_adjacent_utility_sub clickThroughRate rank
    lastDropout ownValue opponent hclick_pos
  nlinarith [mul_nonpos_of_nonneg_of_nonpos
    (sub_nonneg.mpr hclick_mono) (sub_nonpos.mpr hown_le)]

theorem theorem8_ordered_adjacent_utility_strict_mono_of_opponent_lt
    (clickThroughRate : ℕ → ℝ) (rank : ℕ)
    (lastDropout ownValue opponent : ℝ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hclick_strict : clickThroughRate (rank + 1) <
      clickThroughRate rank)
    (hopponent_lt : opponent < ownValue) :
    clickThroughRate (rank + 1) * (ownValue - lastDropout) <
      clickThroughRate rank *
        (ownValue - theorem8OrderedOpponentPrice clickThroughRate rank
          lastDropout opponent) := by
  have hid := theorem8_ordered_adjacent_utility_sub clickThroughRate rank
    lastDropout ownValue opponent hclick_pos
  have hproduct : 0 <
      (clickThroughRate rank - clickThroughRate (rank + 1)) *
        (ownValue - opponent) :=
    mul_pos (sub_pos.mpr hclick_strict) (sub_pos.mpr hopponent_lt)
  nlinarith

theorem theorem8_ordered_adjacent_utility_strict_antimono_of_own_lt
    (clickThroughRate : ℕ → ℝ) (rank : ℕ)
    (lastDropout ownValue opponent : ℝ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hclick_strict : clickThroughRate (rank + 1) <
      clickThroughRate rank)
    (hown_lt : ownValue < opponent) :
    clickThroughRate rank *
        (ownValue - theorem8OrderedOpponentPrice clickThroughRate rank
          lastDropout opponent) <
      clickThroughRate (rank + 1) * (ownValue - lastDropout) := by
  have hid := theorem8_ordered_adjacent_utility_sub clickThroughRate rank
    lastDropout ownValue opponent hclick_pos
  have hproduct :
      (clickThroughRate rank - clickThroughRate (rank + 1)) *
          (ownValue - opponent) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hclick_strict)
      (sub_neg.mpr hown_lt)
  nlinarith

/-- On a feasible history the named opponent price is already at or above the
stopped clock, so the operational clamp is inactive. -/
theorem theorem8_ordered_opponent_price_max_eq
    (clickThroughRate : ℕ → ℝ) (rank : ℕ)
    (lastDropout opponent : ℝ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hclick_mono : clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hlast_le : lastDropout ≤ opponent) :
    max lastDropout
        (theorem8OrderedOpponentPrice clickThroughRate rank
          lastDropout opponent) =
      theorem8OrderedOpponentPrice clickThroughRate rank
        lastDropout opponent := by
  rw [max_eq_right]
  exact paper_theorem8_generalized_english_indifference_price_lastDropout_le
    hclick_pos hclick_mono hlast_le

/-! ## The ordered menu is single-peaked in value -/

/-- If every remaining opponent has value at least the focal value, every
higher-slot continuation payoff is weakly below dropping at the current node.
The proof iterates the adjacent-slot identity through the complete ordered
tail; no equilibrium or best-response premise appears. -/
theorem theorem8_ordered_optimal_utility_le_drop_of_own_le_all
    (clickThroughRate : ℕ → ℝ) (ownValue : ℝ)
    (opponents : List ℝ) (history : Theorem8SourcePriceHistory)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hclick_mono : ∀ rank,
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
        exact
          paper_theorem8_generalized_english_indifference_price_lastDropout_le
            (hclick_pos remainingOpponents.length)
            (hclick_mono remainingOpponents.length) hlast_le_opponent
      have hnext_le_opponent : nextPrice ≤ opponent := by
        dsimp [nextPrice, rank]
        exact paper_theorem8_generalized_english_indifference_price_le_value
          (hclick_pos remainingOpponents.length)
          (le_of_lt (hclick_pos (remainingOpponents.length + 1)))
          hlast_le_opponent
      have htail_current : ∀ other ∈ remainingOpponents,
          theorem8SourcePriceHistoryLastDropout (nextPrice :: history) ≤
            other := by
        intro other hother
        simpa using hnext_le_opponent.trans (hopponent_le_tail other hother)
      have htail_own : ∀ other ∈ remainingOpponents,
          ownValue ≤ other := by
        intro other hother
        exact hown_le_opponent.trans (hopponent_le_tail other hother)
      have htail := ih (nextPrice :: history)
        hordered_tail htail_current htail_own
      have hadjacent :
          clickThroughRate remainingOpponents.length *
              (ownValue - nextPrice) ≤
            clickThroughRate (remainingOpponents.length + 1) *
              (ownValue -
                theorem8SourcePriceHistoryLastDropout history) := by
        dsimp [nextPrice, rank]
        exact theorem8_ordered_adjacent_utility_antimono_of_own_le
          clickThroughRate remainingOpponents.length
          (theorem8SourcePriceHistoryLastDropout history)
          ownValue opponent (hclick_pos remainingOpponents.length)
          (hclick_mono remainingOpponents.length) hown_le_opponent
      have htail_bound :
          theorem8OrderedOptimalUtility clickThroughRate ownValue
              remainingOpponents (nextPrice :: history) ≤
            clickThroughRate (remainingOpponents.length + 1) *
              (ownValue -
                theorem8SourcePriceHistoryLastDropout history) := by
        exact htail.trans hadjacent
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

/-- The current-slot choice is one of the options in the ordered optimal
menu. -/
theorem theorem8_ordered_drop_utility_le_optimal
    (clickThroughRate : ℕ → ℝ) (ownValue : ℝ)
    (opponents : List ℝ) (history : Theorem8SourcePriceHistory) :
    clickThroughRate opponents.length *
        (ownValue - theorem8SourcePriceHistoryLastDropout history) ≤
      theorem8OrderedOptimalUtility clickThroughRate ownValue
        opponents history := by
  cases opponents with
  | nil => rfl
  | cons opponent remainingOpponents =>
      exact le_max_left _ _

/-! ## The named plan realizes the ordered optimum -/

/-- Against opponents ordered by value, the full history-dependent EOS plan
realizes the best stopping position at every feasible history.  The proof is a
backward induction over *all* remaining opponents, including the source's
random tie branch. -/
theorem theorem8_ordered_named_utility_eq_optimal
    (clickThroughRate : ℕ → ℝ) (ownValue : ℝ)
    (opponents : List ℝ) (history : Theorem8SourcePriceHistory)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hclick_strict : ∀ rank,
      clickThroughRate (rank + 1) < clickThroughRate rank)
    (hordered : opponents.Pairwise (· ≤ ·))
    (hcurrent_le : ∀ opponent ∈ opponents,
      theorem8SourcePriceHistoryLastDropout history ≤ opponent)
    (hown_feasible :
      theorem8SourcePriceHistoryLastDropout history ≤ ownValue) :
    theorem8OrderedNamedUtility clickThroughRate ownValue opponents history =
      theorem8OrderedOptimalUtility clickThroughRate ownValue
        opponents history := by
  induction opponents generalizing history with
  | nil =>
      rfl
  | cons opponent remainingOpponents ih =>
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
      have hclick_mono : ∀ r,
          clickThroughRate (r + 1) ≤ clickThroughRate r :=
        fun r => (hclick_strict r).le
      have hown_price_ge : lastDropout ≤ ownPrice := by
        dsimp [ownPrice, rank, lastDropout]
        exact
          paper_theorem8_generalized_english_indifference_price_lastDropout_le
            (hclick_pos remainingOpponents.length)
            (hclick_mono remainingOpponents.length) hown_feasible
      have hopponent_price_ge : lastDropout ≤ opponentPrice := by
        dsimp [opponentPrice, rank, lastDropout]
        exact
          paper_theorem8_generalized_english_indifference_price_lastDropout_le
            (hclick_pos remainingOpponents.length)
            (hclick_mono remainingOpponents.length) hlast_le_opponent
      have hopponent_price_le : opponentPrice ≤ opponent := by
        dsimp [opponentPrice, rank, lastDropout]
        exact paper_theorem8_generalized_english_indifference_price_le_value
          (hclick_pos remainingOpponents.length)
          (le_of_lt (hclick_pos (remainingOpponents.length + 1)))
          hlast_le_opponent
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
          exact
            paper_theorem8_generalized_english_indifference_price_strict_mono_value
              (hclick_pos remainingOpponents.length)
              (hclick_strict remainingOpponents.length) hown_lt
        have htail_own_le : ∀ other ∈ remainingOpponents,
            ownValue ≤ other := by
          intro other hother
          exact hown_lt.le.trans (hopponent_le_tail other hother)
        have htail_ceiling :=
          theorem8_ordered_optimal_utility_le_drop_of_own_le_all
            clickThroughRate ownValue remainingOpponents
            (opponentPrice :: history) hclick_pos hclick_mono
            hordered_tail htail_current htail_own_le
        have hadjacent :=
          theorem8_ordered_adjacent_utility_antimono_of_own_le
            clickThroughRate remainingOpponents.length lastDropout
            ownValue opponent (hclick_pos remainingOpponents.length)
            (hclick_mono remainingOpponents.length) hown_lt.le
        have htail_bound :
            theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents (opponentPrice :: history) ≤
              clickThroughRate (remainingOpponents.length + 1) *
                (ownValue - lastDropout) := by
          exact htail_ceiling.trans (by simpa [opponentPrice, rank] using hadjacent)
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
          hopponent_price_ge, hprice_lt_raw,
          max_eq_left htail_bound]
      · subst opponent
        have hprice_eq : ownPrice = opponentPrice := rfl
        have htail_feasible :
            theorem8SourcePriceHistoryLastDropout
                (opponentPrice :: history) ≤ ownValue := by
          simpa [opponentPrice, theorem8OrderedOpponentPrice] using
            (paper_theorem8_generalized_english_indifference_price_le_value
              (hclick_pos remainingOpponents.length)
              (le_of_lt (hclick_pos (remainingOpponents.length + 1)))
              hown_feasible)
        have htail_named := ih (opponentPrice :: history)
          hordered_tail htail_current htail_feasible
        have htail_own_le : ∀ other ∈ remainingOpponents,
            ownValue ≤ other := hopponent_le_tail
        have htail_ceiling :=
          theorem8_ordered_optimal_utility_le_drop_of_own_le_all
            clickThroughRate ownValue remainingOpponents
            (opponentPrice :: history) hclick_pos hclick_mono
            hordered_tail htail_current htail_own_le
        have hadjacent_upper :
            clickThroughRate remainingOpponents.length *
                (ownValue - opponentPrice) ≤
              clickThroughRate (remainingOpponents.length + 1) *
                (ownValue - lastDropout) := by
          exact theorem8_ordered_adjacent_utility_antimono_of_own_le
            clickThroughRate remainingOpponents.length lastDropout
            ownValue ownValue (hclick_pos remainingOpponents.length)
            (hclick_mono remainingOpponents.length) (le_refl _)
        have htail_upper :
            theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents (opponentPrice :: history) ≤
              clickThroughRate (remainingOpponents.length + 1) *
                (ownValue - lastDropout) := by
          exact htail_ceiling.trans hadjacent_upper
        have hdrop_le_tail :
            clickThroughRate (remainingOpponents.length + 1) *
                (ownValue - lastDropout) ≤
              theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents (opponentPrice :: history) := by
          have hadjacent :=
            theorem8_ordered_adjacent_utility_mono_of_opponent_le
              clickThroughRate remainingOpponents.length lastDropout
              ownValue ownValue (hclick_pos remainingOpponents.length)
              (hclick_mono remainingOpponents.length) (le_refl _)
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
                (ownValue -
                  theorem8SourcePriceHistoryLastDropout history) := by
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
          exact
            paper_theorem8_generalized_english_indifference_price_strict_mono_value
              (hclick_pos remainingOpponents.length)
              (hclick_strict remainingOpponents.length) hopponent_lt
        have htail_named := ih (opponentPrice :: history)
          hordered_tail htail_current
          (hopponent_price_le.trans hopponent_lt.le)
        have hadjacent :=
          theorem8_ordered_adjacent_utility_mono_of_opponent_le
            clickThroughRate remainingOpponents.length lastDropout
            ownValue opponent (hclick_pos remainingOpponents.length)
            (hclick_mono remainingOpponents.length) hopponent_lt.le
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
                (ownValue -
                  theorem8SourcePriceHistoryLastDropout history) ≤
              theorem8OrderedOptimalUtility clickThroughRate ownValue
                remainingOpponents
                  (paper_theorem8_generalized_english_indifference_price
                    (clickThroughRate remainingOpponents.length)
                    (clickThroughRate (remainingOpponents.length + 1))
                    (theorem8SourcePriceHistoryLastDropout history)
                    opponent :: history) := by
          simpa [opponentPrice, rank, lastDropout,
            theorem8OrderedOpponentPrice] using hdrop_le_tail
        simpa [theorem8OrderedNamedUtility,
          theorem8OrderedContinuationUtility,
          theorem8NamedContinuationPlan,
          theorem8OrderedOptimalUtility,
          theorem8OrderedOpponentPrice, hown_price_ge,
          hopponent_price_ge, hprice_lt_raw, hprice_not_reverse,
          htail_named_raw, max_eq_right hdrop_le_tail_raw]

/-- The EOS plan is an ex-post best response to named opponents against every
arbitrary full history-dependent continuation deviation.  This is the source's
existence claim in strategy form; unlike a one-step-deviation predicate, the
left side recursively executes `deviation` at every later history. -/
theorem theorem8_ordered_named_plan_ex_post_best_response
    (clickThroughRate : ℕ → ℝ) (ownValue : ℝ)
    (opponents : List ℝ) (history : Theorem8SourcePriceHistory)
    (deviation : Theorem8ContinuationPlan)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hclick_strict : ∀ rank,
      clickThroughRate (rank + 1) < clickThroughRate rank)
    (hordered : opponents.Pairwise (· ≤ ·))
    (hcurrent_le : ∀ opponent ∈ opponents,
      theorem8SourcePriceHistoryLastDropout history ≤ opponent)
    (hown_feasible :
      theorem8SourcePriceHistoryLastDropout history ≤ ownValue) :
    theorem8OrderedContinuationUtility clickThroughRate deviation ownValue
        opponents history ≤
      theorem8OrderedNamedUtility clickThroughRate ownValue
        opponents history := by
  calc
    theorem8OrderedContinuationUtility clickThroughRate deviation ownValue
        opponents history ≤
      theorem8OrderedOptimalUtility clickThroughRate ownValue
        opponents history :=
      theorem8_ordered_continuation_utility_le_optimal
        clickThroughRate deviation ownValue opponents history
    _ = theorem8OrderedNamedUtility clickThroughRate ownValue
        opponents history :=
      (theorem8_ordered_named_utility_eq_optimal clickThroughRate ownValue
        opponents history hclick_pos hclick_strict hordered hcurrent_le
        hown_feasible).symm

/-- The validity event for a value-ordered list of surviving opponents at a
public history. -/
def Theorem8OrderedOpponentProfileValid
    (history : Theorem8SourcePriceHistory) (opponents : List ℝ) : Prop :=
  opponents.Pairwise (· ≤ ·) ∧
    ∀ opponent ∈ opponents,
      theorem8SourcePriceHistoryLastDropout history ≤ opponent

/-- Ex-post optimality lifts to expected sequential rationality under *any*
posterior supported on ordered surviving opponent profiles.  The theorem keeps
integrability explicit, just as the unbounded source type law requires. -/
theorem theorem8_ordered_named_plan_expected_best_response
    [MeasurableSpace (List ℝ)]
    (clickThroughRate : ℕ → ℝ) (ownValue : ℝ)
    (history : Theorem8SourcePriceHistory)
    (deviation : Theorem8ContinuationPlan)
    (belief : Measure (List ℝ))
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hclick_strict : ∀ rank,
      clickThroughRate (rank + 1) < clickThroughRate rank)
    (hown_feasible :
      theorem8SourcePriceHistoryLastDropout history ≤ ownValue)
    (hsupported : ∀ᵐ opponents ∂belief,
      Theorem8OrderedOpponentProfileValid history opponents)
    (hdeviation_integrable : Integrable
      (fun opponents =>
        theorem8OrderedContinuationUtility clickThroughRate deviation
          ownValue opponents history) belief)
    (hnamed_integrable : Integrable
      (fun opponents =>
        theorem8OrderedNamedUtility clickThroughRate ownValue
          opponents history) belief) :
    (∫ opponents,
      theorem8OrderedContinuationUtility clickThroughRate deviation
        ownValue opponents history ∂belief) ≤
      ∫ opponents,
        theorem8OrderedNamedUtility clickThroughRate ownValue
          opponents history ∂belief := by
  apply integral_mono_ae hdeviation_integrable hnamed_integrable
  filter_upwards [hsupported] with opponents hopponents
  exact theorem8_ordered_named_plan_ex_post_best_response
    clickThroughRate ownValue opponents history deviation
    hclick_pos hclick_strict hopponents.1 hopponents.2 hown_feasible

/-! ## Uniqueness among ex-post continuation best responses -/

/-- The value whose named indifference threshold is a prescribed future clock
price.  Strict adjacent click rates make this affine inverse well-defined. -/
def theorem8IndifferenceValueAtPrice
    (alphaAbove alphaCurrent lastDropout targetPrice : ℝ) : ℝ :=
  (alphaAbove * targetPrice - alphaCurrent * lastDropout) /
    (alphaAbove - alphaCurrent)

theorem theorem8_indifference_price_value_at_price
    {alphaAbove alphaCurrent lastDropout targetPrice : ℝ}
    (halphaAbove_pos : 0 < alphaAbove)
    (hclick_strict : alphaCurrent < alphaAbove) :
    paper_theorem8_generalized_english_indifference_price
        alphaAbove alphaCurrent lastDropout
        (theorem8IndifferenceValueAtPrice alphaAbove alphaCurrent
          lastDropout targetPrice) = targetPrice := by
  have hgap_ne : alphaAbove - alphaCurrent ≠ 0 :=
    ne_of_gt (sub_pos.mpr hclick_strict)
  unfold theorem8IndifferenceValueAtPrice
  unfold paper_theorem8_generalized_english_indifference_price
  field_simp [ne_of_gt halphaAbove_pos, hgap_ne]
  ring

@[simp]
theorem theorem8_indifference_price_at_last_dropout
    (alphaAbove alphaCurrent lastDropout : ℝ) :
    paper_theorem8_generalized_english_indifference_price
      alphaAbove alphaCurrent lastDropout lastDropout = lastDropout := by
  unfold paper_theorem8_generalized_english_indifference_price
  ring

/-- Ordering of target prices transfers back through the strict affine inverse. -/
theorem theorem8_indifference_value_at_price_lt_of_price_lt
    {alphaAbove alphaCurrent lastDropout value targetPrice : ℝ}
    (halphaAbove_pos : 0 < alphaAbove)
    (hclick_strict : alphaCurrent < alphaAbove)
    (hprice_lt :
      paper_theorem8_generalized_english_indifference_price
          alphaAbove alphaCurrent lastDropout value < targetPrice) :
    value < theorem8IndifferenceValueAtPrice alphaAbove alphaCurrent
      lastDropout targetPrice := by
  let otherValue := theorem8IndifferenceValueAtPrice alphaAbove alphaCurrent
    lastDropout targetPrice
  have hother_price :
      paper_theorem8_generalized_english_indifference_price
          alphaAbove alphaCurrent lastDropout otherValue = targetPrice := by
    exact theorem8_indifference_price_value_at_price
      halphaAbove_pos hclick_strict
  by_contra hnot
  have hother_le : otherValue ≤ value := le_of_not_gt hnot
  rcases hother_le.eq_or_lt with heq | hlt
  · rw [heq] at hother_price
    linarith
  · have hmono :=
      paper_theorem8_generalized_english_indifference_price_strict_mono_value
        (lastDropout := lastDropout)
        halphaAbove_pos hclick_strict hlt
    rw [hother_price] at hmono
    linarith

theorem theorem8_indifference_value_at_price_lt_of_lt_price
    {alphaAbove alphaCurrent lastDropout value targetPrice : ℝ}
    (halphaAbove_pos : 0 < alphaAbove)
    (hclick_strict : alphaCurrent < alphaAbove)
    (hprice_lt : targetPrice <
      paper_theorem8_generalized_english_indifference_price
        alphaAbove alphaCurrent lastDropout value) :
    theorem8IndifferenceValueAtPrice alphaAbove alphaCurrent
        lastDropout targetPrice < value := by
  let otherValue := theorem8IndifferenceValueAtPrice alphaAbove alphaCurrent
    lastDropout targetPrice
  have hother_price :
      paper_theorem8_generalized_english_indifference_price
          alphaAbove alphaCurrent lastDropout otherValue = targetPrice := by
    exact theorem8_indifference_price_value_at_price
      halphaAbove_pos hclick_strict
  by_contra hnot
  have hvalue_le : value ≤ otherValue := le_of_not_gt hnot
  rcases hvalue_le.eq_or_lt with heq | hlt
  · rw [← heq] at hother_price
    linarith
  · have hmono :=
      paper_theorem8_generalized_english_indifference_price_strict_mono_value
        (lastDropout := lastDropout)
        halphaAbove_pos hclick_strict hlt
    rw [hother_price] at hmono
    linarith

/-- A plan is an ex-post continuation best response when named opponents are
ordered by value.  The quantification includes every full continuation
deviation, every feasible public history, and every finite ordered opponent
profile. -/
def Theorem8OrderedExPostBestResponse
    (clickThroughRate : ℕ → ℝ) (plan : Theorem8ContinuationPlan) : Prop :=
  ∀ ownValue opponents history,
    Theorem8OrderedOpponentProfileValid history opponents →
    theorem8SourcePriceHistoryLastDropout history ≤ ownValue →
    ∀ deviation : Theorem8ContinuationPlan,
      theorem8OrderedContinuationUtility clickThroughRate deviation ownValue
          opponents history ≤
        theorem8OrderedContinuationUtility clickThroughRate plan ownValue
          opponents history

/-- The named plan is an ex-post continuation best response. -/
theorem theorem8_named_plan_ordered_ex_post_best_response
    (clickThroughRate : ℕ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hclick_strict : ∀ rank,
      clickThroughRate (rank + 1) < clickThroughRate rank) :
    Theorem8OrderedExPostBestResponse clickThroughRate
      (theorem8NamedContinuationPlan clickThroughRate) := by
  intro ownValue opponents history hopponents hown deviation
  exact theorem8_ordered_named_plan_ex_post_best_response
    clickThroughRate ownValue opponents history deviation
    hclick_pos hclick_strict hopponents.1 hopponents.2 hown

/-! ## Legal-history ex-post PBE -/

/-- Regard one common continuation plan as a bidder-indexed full-history
strategy profile by applying the same plan at every bidder identity. -/
def Theorem8ContinuationPlan.historyStrategy
    (plan : Theorem8ContinuationPlan) (Bidder : Type*) :
    Theorem8ContinuousHistoryStrategy Bidder where
  dropoutPrice := fun _bidder rank history value => plan rank history value

/-- Source continuity for a complete continuation plan. -/
def Theorem8ContinuationPlan.ContinuousInValuation
    (plan : Theorem8ContinuationPlan) : Prop :=
  ∀ rank history, Continuous (plan rank history)

/-- The legal-history ex-post refinement of PBE used by the source's Theorem
8 conclusion.  Beliefs obey actual conditional Bayes rule on every positive-
probability full-history survival event.  Sequential rationality is stronger
than Bayesian optimality: it compares against every complete continuation plan
for every realized ordered opponent profile, so the expected comparison under
any supported posterior follows from
`theorem8_ordered_named_plan_expected_best_response`. -/
def Theorem8LegalHistoryExPostPBE
    (Bidder : Type*) (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ) (plan : Theorem8ContinuationPlan) : Prop :=
  plan.ContinuousInValuation ∧
    (plan.historyStrategy Bidder).ClockLegalOnFeasibleHistory ∧
      (∃ belief : Theorem8HistoryBeliefSystem Bidder,
        belief.BayesConsistent law (plan.historyStrategy Bidder)) ∧
      Theorem8OrderedExPostBestResponse clickThroughRate plan

/-- The named plan induces exactly the bidder-indexed full-history strategy
used by the source formula. -/
theorem theorem8_named_plan_history_strategy_eq
    (Bidder : Type*) (clickThroughRate : ℕ → ℝ) :
    (theorem8NamedContinuationPlan clickThroughRate).historyStrategy Bidder =
      theorem8ContinuousHistoryStrategy Bidder clickThroughRate := by
  rfl

/-- The named continuation plan is continuous in own value at every full
history. -/
theorem theorem8_named_continuation_plan_continuous
    (clickThroughRate : ℕ → ℝ) :
    (theorem8NamedContinuationPlan
      clickThroughRate).ContinuousInValuation := by
  intro rank history
  simpa [theorem8NamedContinuationPlan,
    theorem8ContinuousSourceDropoutPrice,
    theorem8GeneralizedEnglishDropoutPrice] using
      theorem8_continuous_source_dropout_price_continuous_in_value
        clickThroughRate rank
          (theorem8SourcePriceHistoryLastDropout history)

/-- The named full-history formula is a legal-history ex-post PBE with actual
Bayes-consistent beliefs. -/
theorem theorem8_named_legal_history_ex_post_pbe
    (Bidder : Type*) (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hclick_strict : ∀ rank,
      clickThroughRate (rank + 1) < clickThroughRate rank) :
    Theorem8LegalHistoryExPostPBE Bidder law clickThroughRate
      (theorem8NamedContinuationPlan clickThroughRate) := by
  refine ⟨theorem8_named_continuation_plan_continuous clickThroughRate,
    ?_, ?_, theorem8_named_plan_ordered_ex_post_best_response
      clickThroughRate hclick_pos hclick_strict⟩
  · rw [theorem8_named_plan_history_strategy_eq]
    exact theorem8_named_history_strategy_clock_legal_on_feasible_history
      clickThroughRate hclick_pos (fun rank => (hclick_strict rank).le)
  · let strategy :=
      (theorem8NamedContinuationPlan clickThroughRate).historyStrategy Bidder
    exact ⟨theorem8CanonicalHistoryBeliefSystem law strategy,
      theorem8_canonical_history_belief_bayes_consistent law strategy⟩

/-- Ex-post best-response behavior uniquely pins down the operational dropout
threshold at every feasible full history.  Equality is stated after clamping
at the current clock, which is the observable action in the source mechanism;
raw thresholds below a stopped clock are behaviorally identical immediate
dropout instructions. -/
theorem theorem8_ordered_ex_post_best_response_effective_price_unique
    (clickThroughRate : ℕ → ℝ) (plan : Theorem8ContinuationPlan)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hclick_strict : ∀ rank,
      clickThroughRate (rank + 1) < clickThroughRate rank)
    (hbest : Theorem8OrderedExPostBestResponse clickThroughRate plan)
    (rank : ℕ) (history : Theorem8SourcePriceHistory) (ownValue : ℝ)
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
      clickThroughRate rank := (hclick_strict rank).le
  have hnamed_ge : lastDropout ≤ namedPrice := by
    dsimp [namedPrice, lastDropout]
    exact
      paper_theorem8_generalized_english_indifference_price_lastDropout_le
        (hclick_pos rank) hclick_mono hown_feasible
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
        (hclick_pos rank) (hclick_strict rank)
    have hopponent_lt_own : opponentValue < ownValue := by
      apply theorem8_indifference_value_at_price_lt_of_lt_price
        (hclick_pos rank) (hclick_strict rank)
      simpa [namedPrice] using htarget_lt_named
    have hlast_lt_opponent : lastDropout < opponentValue := by
      apply theorem8_indifference_value_at_price_lt_of_price_lt
        (hclick_pos rank) (hclick_strict rank)
      simpa using hlast_lt_target
    let opponents := opponentValue :: List.replicate rank opponentValue
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
      theorem8_ordered_named_utility_eq_optimal clickThroughRate ownValue
        opponents history hclick_pos hclick_strict hopponents_valid.1
        hopponents_valid.2 hown_feasible
    have hadjacent : dropUtility <
        clickThroughRate rank * (ownValue - targetPrice) := by
      have hstrict :=
        theorem8_ordered_adjacent_utility_strict_mono_of_opponent_lt
          clickThroughRate rank lastDropout ownValue opponentValue
          (hclick_pos rank) (hclick_strict rank) hopponent_lt_own
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
    have hnamed_le_plan := hbest ownValue opponents history
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
        (hclick_pos rank) (hclick_strict rank)
    have hown_lt_opponent : ownValue < opponentValue := by
      apply theorem8_indifference_value_at_price_lt_of_price_lt
        (hclick_pos rank) (hclick_strict rank)
      simpa [namedPrice] using hnamed_lt_target
    have hlast_lt_opponent : lastDropout < opponentValue := by
      apply theorem8_indifference_value_at_price_lt_of_price_lt
        (hclick_pos rank) (hclick_strict rank)
      simpa using hlast_lt_target
    let opponents := opponentValue :: List.replicate rank opponentValue
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
              (hclick_pos rank)
              (le_of_lt (hclick_pos (rank + 1)))
              hlast_lt_opponent.le
        simp [htarget_le_opponent]
    have htail_ceiling :=
      theorem8_ordered_optimal_utility_le_drop_of_own_le_all
        clickThroughRate ownValue (List.replicate rank opponentValue)
        (targetPrice :: history) hclick_pos
        (fun r => (hclick_strict r).le) htail_valid.1 htail_valid.2
        (by
          intro opponent hopponent
          simp only [List.mem_replicate] at hopponent
          simpa [hopponent] using hown_lt_opponent.le)
    have hadjacent :
        clickThroughRate rank * (ownValue - targetPrice) < dropUtility := by
      have hstrict :=
        theorem8_ordered_adjacent_utility_strict_antimono_of_own_lt
          clickThroughRate rank lastDropout ownValue opponentValue
          (hclick_pos rank) (hclick_strict rank) hown_lt_opponent
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
    have hnamed_le_plan := hbest ownValue opponents history
      hopponents_valid hown_feasible
      (theorem8NamedContinuationPlan clickThroughRate)
    rw [hnamed_eq_drop] at hnamed_le_plan
    exact ((not_lt_of_ge hnamed_le_plan) hplan_lt_drop).elim

/-- Full legal-history existence and uniqueness endpoint.  The named plan is a
Bayes-consistent ex-post PBE, and every other legal-history ex-post PBE has the
same operational dropout action at every feasible full history.  Equality is
necessarily clock-clamped: a raw threshold behind the stopped clock denotes
the same immediate-drop action. -/
theorem theorem8_legal_history_ex_post_pbe_exists_unique
    (Bidder : Type*) (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hclick_strict : ∀ rank,
      clickThroughRate (rank + 1) < clickThroughRate rank) :
    Theorem8LegalHistoryExPostPBE Bidder law clickThroughRate
        (theorem8NamedContinuationPlan clickThroughRate) ∧
      ∀ plan : Theorem8ContinuationPlan,
        Theorem8LegalHistoryExPostPBE Bidder law clickThroughRate plan →
          ∀ rank history ownValue,
            theorem8SourcePriceHistoryLastDropout history ≤ ownValue →
              max (theorem8SourcePriceHistoryLastDropout history)
                  (plan rank history ownValue) =
                paper_theorem8_generalized_english_indifference_price
                  (clickThroughRate rank) (clickThroughRate (rank + 1))
                  (theorem8SourcePriceHistoryLastDropout history)
                  ownValue := by
  refine ⟨theorem8_named_legal_history_ex_post_pbe Bidder law
      clickThroughRate hclick_pos hclick_strict, ?_⟩
  intro plan hpbe rank history ownValue hfeasible
  exact theorem8_ordered_ex_post_best_response_effective_price_unique
    clickThroughRate plan hclick_pos hclick_strict hpbe.2.2.2
    rank history ownValue hfeasible

end

end PaperInterface
end EOS07GSP
