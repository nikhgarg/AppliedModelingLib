import EOS07GSP.BayesianPBE

/-!
# EOS07 Theorem 8: finite stopped-clock source execution

The Bayesian layer already defines the source's next stopped-clock price and
its set of simultaneous droppers.  This module packages those definitions as a
finite execution step.  It deliberately records the source's sequential tie
rule by selecting one member of the minimum-price set at a time; a later
outcome bridge can therefore reason about the resulting full dropout history
without replacing it by a generic state-game clock advance.
-/

namespace EOS07GSP
namespace PaperInterface

open AppliedModelingLib.Auction

noncomputable section

universe u

variable {Bidder : Type u} [Fintype Bidder] [DecidableEq Bidder]

/-- A stopped generalized-English source state: the bidders still active and
the full public dropout-price history (newest price first). -/
structure Theorem8StoppedSourceState (Bidder : Type u) where
  remaining : Finset Bidder
  history : Theorem8SourcePriceHistory
  /-- Droppers in reverse chronological order, aligned with `history`. -/
  dropped : List Bidder

/-- The displayed clock price in a stopped source state. -/
def Theorem8StoppedSourceState.clockPrice
    (state : Theorem8StoppedSourceState Bidder) : ℝ :=
  theorem8SourcePriceHistoryLastDropout state.history

/-- The source-reachable value invariant: every bidder still active has a
value at least as large as the stopped clock. -/
def Theorem8StoppedSourceState.ValuesFeasible
    (state : Theorem8StoppedSourceState Bidder) (values : Bidder → ℝ) : Prop :=
  ∀ bidder, bidder ∈ state.remaining → state.clockPrice ≤ values bidder

/-- The bidder and price histories are aligned one-for-one. -/
def Theorem8StoppedSourceState.DropLedgerAligned
    (state : Theorem8StoppedSourceState Bidder) : Prop :=
  state.dropped.length = state.history.length

/-- No previously dropped bidder remains active, and the dropout ledger has no
duplicate identities. -/
def Theorem8StoppedSourceState.DropLedgerValid
    (state : Theorem8StoppedSourceState Bidder) : Prop :=
  state.dropped.Nodup ∧
    ∀ bidder, bidder ∈ state.dropped → bidder ∉ state.remaining

/-- Every previously recorded dropout has weakly smaller value than every
currently active bidder.  This is the source's realized value-order invariant
and makes the eventual ledger a genuine rank relabeling. -/
def Theorem8StoppedSourceState.DropLedgerValuesBelowActive
    (state : Theorem8StoppedSourceState Bidder) (values : Bidder → ℝ) : Prop :=
  ∀ dropped active,
    dropped ∈ state.dropped → active ∈ state.remaining →
      values dropped ≤ values active

/-- Reverse-chronological droppers are weakly ordered from higher to lower
realized value. -/
def Theorem8StoppedSourceState.DropLedgerValuesNonincreasing
    (state : Theorem8StoppedSourceState Bidder) (values : Bidder → ℝ) : Prop :=
  state.dropped.Pairwise fun earlier later => values later ≤ values earlier

/-- A source price ledger is matched to the finite `B*` recurrence when every
recorded price has the tail length and rank determined by its position in the
reverse-chronological source history. -/
def Theorem8StoppedSourceState.PriceLedgerMatchesBStar
    (state : Theorem8StoppedSourceState Bidder)
    (clickThroughRate rankedValue : ℕ → ℝ) : Prop :=
  ∀ index, index < state.history.length →
    state.history[index]? = some
      (paper_theorem8_bstar_threshold_bid rankedValue clickThroughRate
        (state.dropped.length - index) (state.remaining.card + index))

/-- The finite set of bidders recorded in the dropout ledger. -/
def Theorem8StoppedSourceState.droppedFinset
    (state : Theorem8StoppedSourceState Bidder) : Finset Bidder :=
  state.dropped.toFinset

/-- The source's cold start: every finite advertiser is active, the clock is
zero, and no dropout has yet been recorded. -/
def theorem8StoppedSourceInitialState (Bidder : Type u) [Fintype Bidder] :
    Theorem8StoppedSourceState Bidder where
  remaining := Finset.univ
  history := []
  dropped := []

@[simp]
theorem theorem8_stopped_source_initial_clock
    (Bidder : Type u) [Fintype Bidder] :
    (theorem8StoppedSourceInitialState Bidder).clockPrice = 0 := by
  rfl

@[simp]
theorem theorem8_stopped_source_initial_drop_ledger_aligned
    (Bidder : Type u) [Fintype Bidder] :
    (theorem8StoppedSourceInitialState Bidder).DropLedgerAligned := by
  rfl

@[simp]
theorem theorem8_stopped_source_initial_drop_ledger_valid
    (Bidder : Type u) [Fintype Bidder] [DecidableEq Bidder] :
    (theorem8StoppedSourceInitialState Bidder).DropLedgerValid := by
  constructor
  · simp [theorem8StoppedSourceInitialState]
  · intro bidder hmem
    simp [theorem8StoppedSourceInitialState] at hmem

omit [DecidableEq Bidder] in
/-- The empty cold-start ledger vacuously lies below all active values. -/
lemma theorem8_stopped_source_initial_drop_ledger_values_below_active
    (values : Bidder → ℝ) :
    (theorem8StoppedSourceInitialState Bidder).DropLedgerValuesBelowActive
      values := by
  intro dropped active hmem
  simp [theorem8StoppedSourceInitialState] at hmem

omit [DecidableEq Bidder] in
/-- The empty cold-start ledger is value ordered. -/
lemma theorem8_stopped_source_initial_drop_ledger_values_nonincreasing
    (values : Bidder → ℝ) :
    (theorem8StoppedSourceInitialState Bidder).DropLedgerValuesNonincreasing
      values := by
  simp [Theorem8StoppedSourceState.DropLedgerValuesNonincreasing,
    theorem8StoppedSourceInitialState]

omit [DecidableEq Bidder] in
/-- Nonnegative source values make the cold source state feasible. -/
lemma theorem8_stopped_source_initial_values_feasible
    (values : Bidder → ℝ) (hvalue_nonneg : ∀ bidder, 0 ≤ values bidder) :
    (theorem8StoppedSourceInitialState Bidder).ValuesFeasible values := by
  intro bidder _
  exact hvalue_nonneg bidder

/-- Choose one of the source-prescribed simultaneous droppers.  The choice is
only the deterministic representative of the source's random tie ordering;
every selected bidder has the same stopped-clock price. -/
noncomputable def theorem8ChosenStoppedDropper
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ) : Bidder :=
  (theorem8_first_dropper_set_nonempty strategy values state.remaining
    hremaining rank state.history).choose

/-- The deterministic stopped-clock successor: select one minimum-price
dropper, remove that bidder, and prepend the stopped price to the public
history. -/
noncomputable def Theorem8StoppedSourceState.next
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ) :
    Theorem8StoppedSourceState Bidder where
  remaining := state.remaining.erase
    (theorem8ChosenStoppedDropper strategy values state hremaining rank)
  history := theorem8MinimumDropoutPrice strategy values state.remaining
    hremaining rank state.history :: state.history
  dropped := theorem8ChosenStoppedDropper strategy values state hremaining rank
    :: state.dropped

/-- The selected bidder belongs to the source's minimum-price dropout set. -/
theorem theorem8_chosen_stopped_dropper_mem_first_dropper_set
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ) :
    theorem8ChosenStoppedDropper strategy values state hremaining rank ∈
      theorem8FirstDropperSet strategy values state.remaining hremaining
        rank state.history := by
  exact
    (theorem8_first_dropper_set_nonempty strategy values state.remaining
      hremaining rank state.history).choose_spec

/-- In particular, the selected bidder was active before the source step. -/
theorem theorem8_chosen_stopped_dropper_mem_remaining
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ) :
    theorem8ChosenStoppedDropper strategy values state hremaining rank ∈
      state.remaining := by
  exact Finset.mem_filter.mp
    (theorem8_chosen_stopped_dropper_mem_first_dropper_set
      strategy values state hremaining rank) |>.1

/-- Every stopped source step keeps the clock weakly increasing.  This is the
formal stopped-clock/no-backtracking invariant from source footnote 18. -/
theorem theorem8_stopped_source_next_clock_ge_clock
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ) :
    state.clockPrice ≤
      (state.next strategy values hremaining rank).clockPrice := by
  change theorem8SourcePriceHistoryLastDropout state.history ≤
    theorem8MinimumDropoutPrice strategy values state.remaining hremaining
      rank state.history
  have hchosen := theorem8_chosen_stopped_dropper_mem_first_dropper_set
    strategy values state hremaining rank
  have hprice := (Finset.mem_filter.mp hchosen).2
  calc
    theorem8SourcePriceHistoryLastDropout state.history ≤
        theorem8EffectiveDropoutPrice strategy values
          (theorem8ChosenStoppedDropper strategy values state hremaining rank)
          rank state.history := le_max_left _ _
    _ = theorem8MinimumDropoutPrice strategy values state.remaining hremaining
          rank state.history := hprice

/-- The chosen stopped-clock price is no larger than the effective dropout
price of any active bidder.  Thus a source step cannot pass a bidder who was
already ready to leave at the stopped clock. -/
theorem theorem8_stopped_source_next_clock_le_effective_price
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ)
    (bidder : Bidder) (hbidder : bidder ∈ state.remaining) :
    (state.next strategy values hremaining rank).clockPrice ≤
      theorem8EffectiveDropoutPrice strategy values bidder rank state.history := by
  change theorem8MinimumDropoutPrice strategy values state.remaining hremaining
      rank state.history ≤
    theorem8EffectiveDropoutPrice strategy values bidder rank state.history
  apply Finset.min'_le
    (state.remaining.image fun bidder =>
      theorem8EffectiveDropoutPrice strategy values bidder rank state.history)
    (theorem8EffectiveDropoutPrice strategy values bidder rank state.history)
  exact Finset.mem_image.mpr ⟨bidder, hbidder, rfl⟩

/-- A source step removes exactly one active bidder. -/
theorem theorem8_stopped_source_next_card
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ) :
    (state.next strategy values hremaining rank).remaining.card + 1 =
      state.remaining.card := by
  simp [Theorem8StoppedSourceState.next,
    theorem8_chosen_stopped_dropper_mem_remaining strategy values state
      hremaining rank]
  exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr
    (Finset.card_pos.mpr hremaining))

/-- The bidder ledger advances in lockstep with the public price history. -/
theorem theorem8_stopped_source_next_dropped_length
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ) :
    (state.next strategy values hremaining rank).dropped.length =
      state.dropped.length + 1 := by
  rfl

/-- One source step also prepends exactly one public price. -/
theorem theorem8_stopped_source_next_history_length
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ) :
    (state.next strategy values hremaining rank).history.length =
      state.history.length + 1 := by
  rfl

/-- The finite source execution preserves the correspondence between each
selected dropper and the simultaneously recorded dropout price. -/
theorem theorem8_stopped_source_next_drop_ledger_aligned
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ)
    (haligned : state.DropLedgerAligned) :
    (state.next strategy values hremaining rank).DropLedgerAligned := by
  simpa [Theorem8StoppedSourceState.DropLedgerAligned,
    theorem8_stopped_source_next_dropped_length,
    theorem8_stopped_source_next_history_length] using congrArg Nat.succ haligned

/-- The chosen active bidder is fresh for a valid dropout ledger. -/
theorem theorem8_chosen_stopped_dropper_not_mem_dropped
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ)
    (hvalid : state.DropLedgerValid) :
    theorem8ChosenStoppedDropper strategy values state hremaining rank ∉
      state.dropped := by
  intro hmem
  exact (hvalid.2 _ hmem)
    (theorem8_chosen_stopped_dropper_mem_remaining strategy values state
      hremaining rank)

/-- Removing the selected active bidder and recording it preserves ledger
validity. -/
theorem theorem8_stopped_source_next_drop_ledger_valid
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ)
    (hvalid : state.DropLedgerValid) :
    (state.next strategy values hremaining rank).DropLedgerValid := by
  constructor
  · simp [Theorem8StoppedSourceState.next,
      theorem8_chosen_stopped_dropper_not_mem_dropped strategy values state
        hremaining rank hvalid, hvalid.1]
  · intro bidder hmem
    simp only [Theorem8StoppedSourceState.next, List.mem_cons] at hmem
    rcases hmem with hchosen | hdropped
    · subst bidder
      simp [Theorem8StoppedSourceState.next]
    · intro herased
      exact hvalid.2 _ hdropped (Finset.mem_of_mem_erase herased)

/-- A source step transfers exactly one bidder from the active set to the
dropout ledger. -/
theorem theorem8_stopped_source_next_card_add_dropped_length
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ) :
    (state.next strategy values hremaining rank).remaining.card +
        (state.next strategy values hremaining rank).dropped.length =
      state.remaining.card + state.dropped.length := by
  have hcard := theorem8_stopped_source_next_card strategy values state
    hremaining rank
  have hdropped := theorem8_stopped_source_next_dropped_length strategy values
    state hremaining rank
  omega

/-- Under the source click-rate inequalities, the named displayed formula
preserves feasibility of every survivor.  Combined with the stopped minimum
rule, this is the missing one-step no-overshoot invariant for an actual finite
bidder execution: the clock never advances beyond a survivor's value. -/
theorem theorem8_named_stopped_source_next_values_feasible
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_nonneg : 0 ≤ clickThroughRate (rank + 1))
    (hcurrent_le : clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hfeasible : state.ValuesFeasible values) :
    (state.next (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values hremaining rank).ValuesFeasible values := by
  intro bidder hbidder
  have hactive : bidder ∈ state.remaining :=
    Finset.mem_of_mem_erase hbidder
  have hvalue := hfeasible bidder hactive
  have hnext_le := theorem8_stopped_source_next_clock_le_effective_price
    (theorem8ContinuousHistoryStrategy Bidder clickThroughRate) values state
    hremaining rank bidder hactive
  have hformula_lower : state.clockPrice ≤
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate).dropoutPrice
        bidder rank state.history (values bidder) := by
    exact paper_theorem8_generalized_english_indifference_price_lastDropout_le
      hclick_pos hcurrent_le hvalue
  have hformula_upper :
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate).dropoutPrice
        bidder rank state.history (values bidder) ≤ values bidder := by
    exact paper_theorem8_generalized_english_indifference_price_le_value
      hclick_pos hcurrent_nonneg hvalue
  have heffective :
      theorem8EffectiveDropoutPrice
        (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
        values bidder rank state.history =
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate).dropoutPrice
        bidder rank state.history (values bidder) := by
    exact max_eq_right hformula_lower
  rw [heffective] at hnext_le
  exact hnext_le.trans hformula_upper

/-- With strictly decreasing adjacent click-through rates, a bidder selected
by the source's stopped minimum rule has weakly the lowest realized value among
the active bidders.  Equal values are intentionally left as a tie: the source
resolves precisely that case by its sequential random ordering. -/
theorem theorem8_named_chosen_stopped_dropper_value_le
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_lt : clickThroughRate (rank + 1) < clickThroughRate rank)
    (hfeasible : state.ValuesFeasible values)
    (bidder : Bidder) (hbidder : bidder ∈ state.remaining) :
    values (theorem8ChosenStoppedDropper
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values state hremaining rank) ≤ values bidder := by
  let strategy := theorem8ContinuousHistoryStrategy Bidder clickThroughRate
  let chosen := theorem8ChosenStoppedDropper strategy values state hremaining rank
  have hchosen_active : chosen ∈ state.remaining := by
    exact theorem8_chosen_stopped_dropper_mem_remaining
      strategy values state hremaining rank
  have hchosen_value := hfeasible chosen hchosen_active
  have hbidder_value := hfeasible bidder hbidder
  have hchosen_min := (Finset.mem_filter.mp
    (theorem8_chosen_stopped_dropper_mem_first_dropper_set
      strategy values state hremaining rank)).2
  have hchosen_effective_eq :
      theorem8EffectiveDropoutPrice strategy values chosen rank state.history =
        (state.next strategy values hremaining rank).clockPrice := by
    exact hchosen_min
  have hnext_le := theorem8_stopped_source_next_clock_le_effective_price
    strategy values state hremaining rank bidder hbidder
  rw [← hchosen_effective_eq] at hnext_le
  have hchosen_formula_lower : state.clockPrice ≤
      strategy.dropoutPrice chosen rank state.history (values chosen) := by
    exact paper_theorem8_generalized_english_indifference_price_lastDropout_le
      hclick_pos hcurrent_lt.le hchosen_value
  have hbidder_formula_lower : state.clockPrice ≤
      strategy.dropoutPrice bidder rank state.history (values bidder) := by
    exact paper_theorem8_generalized_english_indifference_price_lastDropout_le
      hclick_pos hcurrent_lt.le hbidder_value
  have hchosen_effective :
      theorem8EffectiveDropoutPrice strategy values chosen rank state.history =
        strategy.dropoutPrice chosen rank state.history (values chosen) := by
    exact max_eq_right hchosen_formula_lower
  have hbidder_effective :
      theorem8EffectiveDropoutPrice strategy values bidder rank state.history =
        strategy.dropoutPrice bidder rank state.history (values bidder) := by
    exact max_eq_right hbidder_formula_lower
  rw [hchosen_effective, hbidder_effective] at hnext_le
  by_contra hnot
  have hvalue_lt : values bidder < values chosen := lt_of_not_ge hnot
  have hprice_lt :
      strategy.dropoutPrice bidder rank state.history (values bidder) <
        strategy.dropoutPrice chosen rank state.history (values chosen) := by
    exact paper_theorem8_generalized_english_indifference_price_strict_mono_value
      hclick_pos hcurrent_lt hvalue_lt
  exact (not_lt_of_ge hnext_le) hprice_lt

/-- At a feasible named-formula source step, the newly recorded clock price is
exactly the selected bidder's displayed full-history dropout price.  The
stopped-clock maximum disappears here because feasibility makes the formula a
future (not past) price. -/
theorem theorem8_named_stopped_source_next_clock_eq_dropout_price
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_le : clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hfeasible : state.ValuesFeasible values) :
    (state.next (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values hremaining rank).clockPrice =
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate).dropoutPrice
        (theorem8ChosenStoppedDropper
          (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
          values state hremaining rank)
        rank state.history
        (values
          (theorem8ChosenStoppedDropper
            (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
            values state hremaining rank)) := by
  let strategy := theorem8ContinuousHistoryStrategy Bidder clickThroughRate
  let chosen := theorem8ChosenStoppedDropper strategy values state hremaining rank
  have hchosen_min := (Finset.mem_filter.mp
    (theorem8_chosen_stopped_dropper_mem_first_dropper_set
      strategy values state hremaining rank)).2
  have hchosen_active : chosen ∈ state.remaining := by
    exact theorem8_chosen_stopped_dropper_mem_remaining
      strategy values state hremaining rank
  have hchosen_value := hfeasible chosen hchosen_active
  have hformula_lower : state.clockPrice ≤
      strategy.dropoutPrice chosen rank state.history (values chosen) := by
    exact paper_theorem8_generalized_english_indifference_price_lastDropout_le
      hclick_pos hcurrent_le hchosen_value
  have heffective :
      theorem8EffectiveDropoutPrice strategy values chosen rank state.history =
        strategy.dropoutPrice chosen rank state.history (values chosen) := by
    exact max_eq_right hformula_lower
  change (state.next strategy values hremaining rank).clockPrice =
    strategy.dropoutPrice chosen rank state.history (values chosen)
  calc
    (state.next strategy values hremaining rank).clockPrice =
        theorem8EffectiveDropoutPrice strategy values chosen rank state.history :=
      hchosen_min.symm
    _ = strategy.dropoutPrice chosen rank state.history (values chosen) :=
      heffective

/-- The first dropout in the finite `K = N + 1` source market occurs at the
lowest selected value when the click-through rate just below the last
advertised slot is zero.  This is the genuine zero-CTR base case of the
recorded-price recurrence; it is intentionally not routed through the older
all-positive infinite ranked bridge. -/
theorem theorem8_named_initial_stopped_source_first_clock_eq_selected_value
    [Nonempty Bidder]
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (htwo : 1 < Fintype.card Bidder)
    (hvalue_nonneg : ∀ bidder, 0 ≤ values bidder)
    (hclick_pos : 0 < clickThroughRate (Fintype.card Bidder - 2))
    (hbottom_zero : clickThroughRate (Fintype.card Bidder - 1) = 0) :
    let initialState := theorem8StoppedSourceInitialState Bidder
    let hremaining : initialState.remaining.Nonempty := Finset.univ_nonempty
    let rank := Fintype.card Bidder - 2
    (initialState.next
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values hremaining rank).clockPrice =
      values
        (theorem8ChosenStoppedDropper
          (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
          values initialState hremaining rank) := by
  dsimp
  let initialState := theorem8StoppedSourceInitialState Bidder
  let hremaining : initialState.remaining.Nonempty := Finset.univ_nonempty
  let rank := Fintype.card Bidder - 2
  have hrank_succ : rank + 1 = Fintype.card Bidder - 1 := by
    dsimp [rank]
    omega
  have hcurrent_le : clickThroughRate (rank + 1) ≤ clickThroughRate rank := by
    rw [hrank_succ, hbottom_zero]
    exact le_of_lt hclick_pos
  have hfeasible : initialState.ValuesFeasible values := by
    exact theorem8_stopped_source_initial_values_feasible values hvalue_nonneg
  have hclock := theorem8_named_stopped_source_next_clock_eq_dropout_price
    clickThroughRate values initialState hremaining rank hclick_pos hcurrent_le
    hfeasible
  change (initialState.next
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values hremaining rank).clockPrice = _
  rw [hclock]
  simp only [theorem8ContinuousHistoryStrategy,
    theorem8ContinuousSourceDropoutPrice,
    theorem8GeneralizedEnglishDropoutPrice,
    theorem8SourcePriceHistoryLastDropout]
  rw [hrank_succ, hbottom_zero,
    paper_theorem8_generalized_english_indifference_price_zero_current_eq]

/-- Inductive source-price step above the zero-CTR base.  Once the previous
record is the one-rank-lower finite `B*` price and the selected bidder has the
corresponding ranked value, the next actual stopped-clock record is the finite
`B*` price at the current rank. -/
theorem theorem8_named_stopped_source_next_clock_eq_bstar_of_ranked_data
    (clickThroughRate rankedValue : ℕ → ℝ) (remaining : ℕ)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hnext_click_pos : 0 < clickThroughRate (rank + 1))
    (hcurrent_le : clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hfeasible : state.ValuesFeasible values)
    (hselected_value :
      values (theorem8ChosenStoppedDropper
        (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
        values state hremaining rank) = rankedValue (rank + 1))
    (hlast : state.clockPrice =
      paper_theorem8_bstar_threshold_bid rankedValue clickThroughRate
        remaining (rank + 2)) :
    (state.next (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values hremaining rank).clockPrice =
      paper_theorem8_bstar_threshold_bid rankedValue clickThroughRate
        (remaining + 1) (rank + 1) := by
  have hclock := theorem8_named_stopped_source_next_clock_eq_dropout_price
    clickThroughRate values state hremaining rank hclick_pos hcurrent_le
    hfeasible
  let continuation : ℕ → ℝ := fun k =>
    paper_theorem8_bstar_threshold_bid rankedValue clickThroughRate
      remaining (k + 2)
  have hformula :
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate).dropoutPrice
        (theorem8ChosenStoppedDropper
          (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
          values state hremaining rank)
        rank state.history
        (values
          (theorem8ChosenStoppedDropper
            (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
            values state hremaining rank)) =
      paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate continuation rankedValue rank := by
    change
      paper_theorem8_generalized_english_indifference_price
          (clickThroughRate rank) (clickThroughRate (rank + 1))
          (theorem8SourcePriceHistoryLastDropout state.history)
          (values
            (theorem8ChosenStoppedDropper
              (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
              values state hremaining rank)) =
        paper_theorem8_generalized_english_indifference_price
          (clickThroughRate rank) (clickThroughRate (rank + 1))
          (continuation rank) (rankedValue (rank + 1))
    rw [show theorem8SourcePriceHistoryLastDropout state.history =
        continuation rank by simpa [continuation] using hlast,
      hselected_value]
  calc
    (state.next (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
        values hremaining rank).clockPrice =
      paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate continuation rankedValue rank := hclock.trans hformula
    _ = paper_theorem8_bstar_threshold_bid rankedValue clickThroughRate
        (remaining + 1) (rank + 1) := by
      simpa [continuation, paper_theorem8_bstar_threshold_bid] using
        paper_theorem8_generalized_english_ranked_dropout_price_eq_bstar_bid_of_vcg_tail
          rankedValue clickThroughRate rank remaining
          (ne_of_gt hclick_pos) (ne_of_gt hnext_click_pos)

/-- The named source step preserves the realized value order between its
dropout ledger and the remaining active bidders. -/
theorem theorem8_named_stopped_source_next_drop_ledger_values_below_active
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_lt : clickThroughRate (rank + 1) < clickThroughRate rank)
    (hfeasible : state.ValuesFeasible values)
    (hbelow : state.DropLedgerValuesBelowActive values) :
    (state.next (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values hremaining rank).DropLedgerValuesBelowActive values := by
  intro dropped active hdropped hactive
  simp only [Theorem8StoppedSourceState.next, List.mem_cons] at hdropped
  have hactive_old : active ∈ state.remaining := Finset.mem_of_mem_erase hactive
  rcases hdropped with hchosen | hold
  · subst dropped
    exact theorem8_named_chosen_stopped_dropper_value_le clickThroughRate
      values state hremaining rank hclick_pos hcurrent_lt hfeasible active
      hactive_old
  · exact hbelow dropped active hold hactive_old

/-- Prepending the newly selected dropout preserves the reverse-chronological
value order of the ledger. -/
theorem theorem8_named_stopped_source_next_drop_ledger_values_nonincreasing
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (rank : ℕ)
    (hbelow : state.DropLedgerValuesBelowActive values)
    (hnonincreasing : state.DropLedgerValuesNonincreasing values) :
    (state.next (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values hremaining rank).DropLedgerValuesNonincreasing values := by
  change (theorem8ChosenStoppedDropper
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values state hremaining rank :: state.dropped).Pairwise
        (fun earlier later => values later ≤ values earlier)
  refine List.pairwise_cons.mpr ⟨?_, hnonincreasing⟩
  intro dropped hdropped
  exact hbelow dropped
    (theorem8ChosenStoppedDropper
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values state hremaining rank)
    hdropped
    (theorem8_chosen_stopped_dropper_mem_remaining
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values state hremaining rank)

/-- Execute at most `fuel` source dropouts, stopping once a single bidder
remains.  At every nonterminal step the rank is determined by the number of
active bidders, as in the source's `k`-bidder continuation notation. -/
noncomputable def theorem8StoppedSourceRun
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) : ℕ → Theorem8StoppedSourceState Bidder →
      Theorem8StoppedSourceState Bidder
  | 0, state => state
  | fuel + 1, state =>
      if htwo : 1 < state.remaining.card then
        theorem8StoppedSourceRun strategy values fuel
          (state.next strategy values
            (Finset.card_pos.mp (by omega))
            (state.remaining.card - 2))
      else state

/-- A finite sequence of the source's stopped-clock transitions.  Unlike a
generic clock-history relation, each step carries the actual minimum-price
tie-resolved source successor. -/
inductive Theorem8StoppedSourceTrace
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) :
    Theorem8StoppedSourceState Bidder → Theorem8StoppedSourceState Bidder → Prop
  | refl (state : Theorem8StoppedSourceState Bidder) :
      Theorem8StoppedSourceTrace strategy values state state
  | step (state : Theorem8StoppedSourceState Bidder)
      (hremaining : state.remaining.Nonempty) (rank : ℕ)
      {finalState : Theorem8StoppedSourceState Bidder} :
      Theorem8StoppedSourceTrace strategy values
        (state.next strategy values hremaining rank) finalState →
      Theorem8StoppedSourceTrace strategy values state finalState

/-- The recursive finite source run produces a concrete stopped source trace. -/
theorem theorem8_stopped_source_run_trace
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (fuel : ℕ)
    (state : Theorem8StoppedSourceState Bidder) :
    Theorem8StoppedSourceTrace strategy values state
      (theorem8StoppedSourceRun strategy values fuel state) := by
  induction fuel generalizing state with
  | zero =>
      exact Theorem8StoppedSourceTrace.refl state
  | succ fuel ih =>
      by_cases htwo : 1 < state.remaining.card
      · let hremaining : state.remaining.Nonempty :=
          Finset.card_pos.mp (by omega)
        rw [theorem8StoppedSourceRun, dif_pos htwo]
        exact Theorem8StoppedSourceTrace.step state hremaining
          (state.remaining.card - 2) (ih _)
      · rw [theorem8StoppedSourceRun, dif_neg htwo]
        exact Theorem8StoppedSourceTrace.refl state

/-- The run only prepends new dropouts: every pre-existing source ledger is a
suffix of the terminal ledger of that continuation. -/
theorem theorem8_stopped_source_run_dropped_eq_append
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (fuel : ℕ)
    (state : Theorem8StoppedSourceState Bidder) :
    ∃ newDropped,
      (theorem8StoppedSourceRun strategy values fuel state).dropped =
        newDropped ++ state.dropped := by
  induction fuel generalizing state with
  | zero =>
      exact ⟨[], by rfl⟩
  | succ fuel ih =>
      by_cases htwo : 1 < state.remaining.card
      · let hremaining : state.remaining.Nonempty :=
          Finset.card_pos.mp (by omega)
        rw [theorem8StoppedSourceRun, dif_pos htwo]
        rcases ih (state.next strategy values hremaining
          (state.remaining.card - 2)) with ⟨newDropped, hnew⟩
        refine ⟨newDropped ++ [theorem8ChosenStoppedDropper
          strategy values state hremaining (state.remaining.card - 2)], ?_⟩
        rw [hnew]
        simp [Theorem8StoppedSourceState.next, List.append_assoc]
      · rw [theorem8StoppedSourceRun, dif_neg htwo]
        exact ⟨[], by simp⟩

/-- The actual finite source run preserves both stopped-clock feasibility and
the realized value order of its ledger.  The click-rate assumptions are bounded
by the finite market size, so the source's zero click-through rate below the
last slot is permitted and never used as a positive denominator. -/
theorem theorem8_named_stopped_source_run_invariants
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ) (K fuel : ℕ)
    (hclick_pos : ∀ rank, rank < K - 1 → 0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < K - 1 →
      0 ≤ clickThroughRate (rank + 1))
    (hcurrent_lt : ∀ rank, rank < K - 1 →
      clickThroughRate (rank + 1) < clickThroughRate rank)
    (state : Theorem8StoppedSourceState Bidder)
    (hcard_bound : state.remaining.card ≤ K)
    (hfeasible : state.ValuesFeasible values)
    (hbelow : state.DropLedgerValuesBelowActive values)
    (hnonincreasing : state.DropLedgerValuesNonincreasing values) :
    (theorem8StoppedSourceRun
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values fuel state).ValuesFeasible values ∧
      (theorem8StoppedSourceRun
        (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
        values fuel state).DropLedgerValuesBelowActive values ∧
        (theorem8StoppedSourceRun
          (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
          values fuel state).DropLedgerValuesNonincreasing values := by
  induction fuel generalizing state with
  | zero =>
      simpa [theorem8StoppedSourceRun] using
        And.intro hfeasible (And.intro hbelow hnonincreasing)
  | succ fuel ih =>
      by_cases htwo : 1 < state.remaining.card
      · have hrank : state.remaining.card - 2 < K - 1 := by omega
        have hremaining : state.remaining.Nonempty :=
          Finset.card_pos.mp (by omega)
        have hnext_feasible := theorem8_named_stopped_source_next_values_feasible
          clickThroughRate values state hremaining
          (state.remaining.card - 2)
          (hclick_pos _ hrank) (hcurrent_nonneg _ hrank)
          (hcurrent_lt _ hrank).le hfeasible
        have hnext_below :=
          theorem8_named_stopped_source_next_drop_ledger_values_below_active
            clickThroughRate values state hremaining
            (state.remaining.card - 2)
            (hclick_pos _ hrank) (hcurrent_lt _ hrank) hfeasible hbelow
        have hnext_nonincreasing :=
          theorem8_named_stopped_source_next_drop_ledger_values_nonincreasing
            clickThroughRate values state hremaining
            (state.remaining.card - 2) hbelow hnonincreasing
        have hnext_bound :
            (state.next
              (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
              values hremaining (state.remaining.card - 2)).remaining.card ≤ K := by
          have hcard := theorem8_stopped_source_next_card
            (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
            values state hremaining (state.remaining.card - 2)
          omega
        rw [theorem8StoppedSourceRun, dif_pos htwo]
        exact ih _ hnext_bound hnext_feasible hnext_below hnext_nonincreasing
      · rw [theorem8StoppedSourceRun, dif_neg htwo]
        exact ⟨hfeasible, hbelow, hnonincreasing⟩

/-- Starting from any nonempty finite bidder set, exactly one bidder remains
after the source has made one stopped dropout per excess bidder.  This is a
termination theorem for the source process itself, independent of any VCG
conclusion. -/
theorem theorem8_stopped_source_run_remaining_card_one
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) :
    (theorem8StoppedSourceRun strategy values (state.remaining.card - 1)
      state).remaining.card = 1 := by
  let P : ℕ → Prop := fun n =>
    ∀ state : Theorem8StoppedSourceState Bidder,
      state.remaining.card = n →
        0 < n →
          (theorem8StoppedSourceRun strategy values (state.remaining.card - 1)
            state).remaining.card = 1
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro state hcard hpositive
        by_cases hone : n = 1
        · subst n
          have hfuel : state.remaining.card - 1 = 0 := by omega
          rw [hfuel, theorem8StoppedSourceRun]
          exact hone
        · have htwo : 1 < n := by omega
          have hstate_two : 1 < state.remaining.card := by
            simpa [hcard] using htwo
          have hfuel : n - 1 = (n - 2) + 1 := by omega
          rw [hcard, hfuel, theorem8StoppedSourceRun, dif_pos hstate_two]
          let nextState := state.next strategy values
            (Finset.card_pos.mp (by omega))
            (state.remaining.card - 2)
          change
            (theorem8StoppedSourceRun strategy values (n - 2) nextState).remaining.card = 1
          have hnext_card : nextState.remaining.card = n - 1 := by
            dsimp [nextState]
            have hstep := theorem8_stopped_source_next_card strategy values
              state
              (Finset.card_pos.mp
                (by omega))
              (state.remaining.card - 2)
            omega
          have hnext_positive : 0 < n - 1 := by omega
          have hrecursive := ih (n - 1) (by omega) nextState hnext_card
            hnext_positive
          simpa [hnext_card] using hrecursive
  exact hP state.remaining.card state rfl (Finset.card_pos.mpr hremaining)

/-- The terminal state generated by the finite stopped source process.  The
source ends after the next-to-last advertiser drops, leaving one advertiser
active for the top position. -/
noncomputable def theorem8StoppedSourceFinalState
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) : Theorem8StoppedSourceState Bidder :=
  theorem8StoppedSourceRun strategy values (Fintype.card Bidder - 1)
    (theorem8StoppedSourceInitialState Bidder)

/-- A nonempty finite source market reaches its intended terminal cardinality
under the generated stopped source process. -/
theorem theorem8_stopped_source_final_state_remaining_card_one
    [Nonempty Bidder]
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) :
    (theorem8StoppedSourceFinalState strategy values).remaining.card = 1 := by
  change
    (theorem8StoppedSourceRun strategy values
      ((theorem8StoppedSourceInitialState Bidder).remaining.card - 1)
      (theorem8StoppedSourceInitialState Bidder)).remaining.card = 1
  exact theorem8_stopped_source_run_remaining_card_one strategy values
    (theorem8StoppedSourceInitialState Bidder) Finset.univ_nonempty

/-- The terminal finite source state is reached by an explicit trace of the
source's stopped-clock transitions. -/
theorem theorem8_stopped_source_final_state_trace
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) :
    Theorem8StoppedSourceTrace strategy values
      (theorem8StoppedSourceInitialState Bidder)
      (theorem8StoppedSourceFinalState strategy values) := by
  exact theorem8_stopped_source_run_trace strategy values
    (Fintype.card Bidder - 1) (theorem8StoppedSourceInitialState Bidder)

/-- Source-faithful bounded-click version of the run invariant at the terminal
finite generalized-English state. -/
theorem theorem8_named_stopped_source_final_state_invariants
    [Nonempty Bidder]
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (hvalue_nonneg : ∀ bidder, 0 ≤ values bidder)
    (hclick_pos : ∀ rank, rank < Fintype.card Bidder - 1 →
      0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < Fintype.card Bidder - 1 →
      0 ≤ clickThroughRate (rank + 1))
    (hcurrent_lt : ∀ rank, rank < Fintype.card Bidder - 1 →
      clickThroughRate (rank + 1) < clickThroughRate rank) :
    (theorem8StoppedSourceFinalState
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values).ValuesFeasible values ∧
      (theorem8StoppedSourceFinalState
        (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
        values).DropLedgerValuesBelowActive values ∧
        (theorem8StoppedSourceFinalState
          (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
          values).DropLedgerValuesNonincreasing values := by
  exact theorem8_named_stopped_source_run_invariants
    clickThroughRate values (Fintype.card Bidder) (Fintype.card Bidder - 1)
    hclick_pos hcurrent_nonneg hcurrent_lt
    (theorem8StoppedSourceInitialState Bidder) (by
      exact le_rfl)
    (theorem8_stopped_source_initial_values_feasible values hvalue_nonneg)
    (theorem8_stopped_source_initial_drop_ledger_values_below_active values)
    (theorem8_stopped_source_initial_drop_ledger_values_nonincreasing values)

/-- Every finite run keeps the source's bidder and price ledgers aligned. -/
theorem theorem8_stopped_source_run_drop_ledger_aligned
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (fuel : ℕ)
    (state : Theorem8StoppedSourceState Bidder)
    (haligned : state.DropLedgerAligned) :
    (theorem8StoppedSourceRun strategy values fuel state).DropLedgerAligned := by
  induction fuel generalizing state with
  | zero =>
      simpa [theorem8StoppedSourceRun] using haligned
  | succ fuel ih =>
      by_cases htwo : 1 < state.remaining.card
      · rw [theorem8StoppedSourceRun, dif_pos htwo]
        exact ih _
          (theorem8_stopped_source_next_drop_ledger_aligned strategy values
            state (Finset.card_pos.mp (by omega))
            (state.remaining.card - 2) haligned)
      · rw [theorem8StoppedSourceRun, dif_neg htwo]
        exact haligned

/-- Every finite run preserves the fact that each recorded dropout is distinct
from all earlier droppers and from the active set. -/
theorem theorem8_stopped_source_run_drop_ledger_valid
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (fuel : ℕ)
    (state : Theorem8StoppedSourceState Bidder)
    (hvalid : state.DropLedgerValid) :
    (theorem8StoppedSourceRun strategy values fuel state).DropLedgerValid := by
  induction fuel generalizing state with
  | zero =>
      simpa [theorem8StoppedSourceRun] using hvalid
  | succ fuel ih =>
      by_cases htwo : 1 < state.remaining.card
      · rw [theorem8StoppedSourceRun, dif_pos htwo]
        exact ih _
          (theorem8_stopped_source_next_drop_ledger_valid strategy values
            state (Finset.card_pos.mp (by omega))
            (state.remaining.card - 2) hvalid)
      · rw [theorem8StoppedSourceRun, dif_neg htwo]
        exact hvalid

/-- In particular, the terminal finite source ledger records the same number
of dropout identities and public dropout prices. -/
theorem theorem8_stopped_source_final_state_drop_ledger_aligned
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) :
    (theorem8StoppedSourceFinalState strategy values).DropLedgerAligned := by
  exact theorem8_stopped_source_run_drop_ledger_aligned strategy values
    (Fintype.card Bidder - 1) (theorem8StoppedSourceInitialState Bidder)
    (theorem8_stopped_source_initial_drop_ledger_aligned Bidder)

/-- The terminal source ledger contains distinct bidder identities and none of
them is the surviving top bidder. -/
theorem theorem8_stopped_source_final_state_drop_ledger_valid
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) :
    (theorem8StoppedSourceFinalState strategy values).DropLedgerValid := by
  exact theorem8_stopped_source_run_drop_ledger_valid strategy values
    (Fintype.card Bidder - 1) (theorem8StoppedSourceInitialState Bidder)
    (theorem8_stopped_source_initial_drop_ledger_valid Bidder)

/-- The active-bidder count plus the dropout ledger size is invariant along a
finite stopped source execution. -/
theorem theorem8_stopped_source_run_card_add_dropped_length
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (fuel : ℕ)
    (state : Theorem8StoppedSourceState Bidder) :
    (theorem8StoppedSourceRun strategy values fuel state).remaining.card +
        (theorem8StoppedSourceRun strategy values fuel state).dropped.length =
      state.remaining.card + state.dropped.length := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      by_cases htwo : 1 < state.remaining.card
      · rw [theorem8StoppedSourceRun, dif_pos htwo]
        calc
          (theorem8StoppedSourceRun strategy values fuel
              (state.next strategy values (Finset.card_pos.mp (by omega))
                (state.remaining.card - 2))).remaining.card +
              (theorem8StoppedSourceRun strategy values fuel
                (state.next strategy values (Finset.card_pos.mp (by omega))
                  (state.remaining.card - 2))).dropped.length =
            (state.next strategy values (Finset.card_pos.mp (by omega))
              (state.remaining.card - 2)).remaining.card +
              (state.next strategy values (Finset.card_pos.mp (by omega))
                (state.remaining.card - 2)).dropped.length :=
              ih _
          _ = state.remaining.card + state.dropped.length :=
            theorem8_stopped_source_next_card_add_dropped_length strategy values
              state (Finset.card_pos.mp (by omega)) (state.remaining.card - 2)
      · rw [theorem8StoppedSourceRun, dif_neg htwo]

/-- When a nonempty continuation runs to its one-bidder terminal state, the
fresh prefix of its dropout ledger has exactly one entry per excess active
bidder. -/
theorem theorem8_stopped_source_run_dropped_eq_append_of_terminal
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) :
    ∃ newDropped,
      (theorem8StoppedSourceRun strategy values (state.remaining.card - 1)
        state).dropped = newDropped ++ state.dropped ∧
        newDropped.length = state.remaining.card - 1 := by
  rcases theorem8_stopped_source_run_dropped_eq_append strategy values
    (state.remaining.card - 1) state with ⟨newDropped, happend⟩
  refine ⟨newDropped, happend, ?_⟩
  have hterminal := theorem8_stopped_source_run_remaining_card_one
    strategy values state hremaining
  have hconserved := theorem8_stopped_source_run_card_add_dropped_length
    strategy values (state.remaining.card - 1) state
  rw [happend] at hconserved
  simp only [List.length_append] at hconserved
  omega

/-- The bidder selected by the next finite source step has the exact terminal
dropout-ledger rank determined by the current active-set cardinality.  This
turns the rank data used in the price recurrence into a theorem about the
actual source execution rather than an extra premise. -/
theorem theorem8_stopped_source_run_first_chosen_dropped_getElem?
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty)
    (htwo : 1 < state.remaining.card) :
    (theorem8StoppedSourceRun strategy values (state.remaining.card - 1)
      state).dropped[state.remaining.card - 2]? =
      some (theorem8ChosenStoppedDropper strategy values state hremaining
        (state.remaining.card - 2)) := by
  let nextState := state.next strategy values hremaining
    (state.remaining.card - 2)
  have hnext_card : nextState.remaining.card = state.remaining.card - 1 := by
    dsimp [nextState]
    have hstep := theorem8_stopped_source_next_card strategy values state
      hremaining (state.remaining.card - 2)
    omega
  have hnext_positive : 0 < nextState.remaining.card := by
    rw [hnext_card]
    omega
  have hnext_remaining : nextState.remaining.Nonempty :=
    Finset.card_pos.mp hnext_positive
  rcases theorem8_stopped_source_run_dropped_eq_append_of_terminal
    strategy values nextState hnext_remaining with ⟨newDropped, happend, hlength⟩
  have hfuel : state.remaining.card - 1 =
      (state.remaining.card - 2) + 1 := by omega
  have hprefix_length : newDropped.length = state.remaining.card - 2 := by
    rw [hlength, hnext_card]
    omega
  have hnext_fuel : nextState.remaining.card - 1 =
      state.remaining.card - 2 := by
    rw [hnext_card]
    omega
  have hchosen_length :
      theorem8ChosenStoppedDropper strategy values state hremaining
          newDropped.length =
        theorem8ChosenStoppedDropper strategy values state hremaining
          (state.remaining.card - 2) := by
    rw [hprefix_length]
  rw [hfuel, theorem8StoppedSourceRun, dif_pos htwo]
  change (theorem8StoppedSourceRun strategy values
      (state.remaining.card - 2) nextState).dropped[state.remaining.card - 2]? = _
  rw [← hnext_fuel, happend, ← hlength, hchosen_length]
  simp [nextState, Theorem8StoppedSourceState.next]

/-- The value-ranked bidder list generated by completing a source continuation:
its surviving bidder comes first, followed by the complete reverse-chronological
dropout ledger.  Unlike the cold-start rank list, this definition also records
the lower-ranked bidders already present in the continuation history. -/
noncomputable def theorem8StoppedSourceTerminalRankedBidders
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) : List Bidder :=
  let terminalState := theorem8StoppedSourceRun strategy values
    (state.remaining.card - 1) state
  let hterminal : terminalState.remaining.Nonempty :=
    Finset.card_pos.mp (by
      have hcard : terminalState.remaining.card = 1 := by
        exact theorem8_stopped_source_run_remaining_card_one
          strategy values state hremaining
      rw [hcard]
      exact Nat.zero_lt_one)
  hterminal.choose :: terminalState.dropped

/-- A currently selected dropout occupies the exact one-past-active-block
rank in the completed continuation ledger. -/
theorem theorem8_stopped_source_terminal_ranked_first_chosen_getElem?
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty)
    (htwo : 1 < state.remaining.card) :
    (theorem8StoppedSourceTerminalRankedBidders strategy values state
      hremaining)[state.remaining.card - 1]? =
      some (theorem8ChosenStoppedDropper strategy values state hremaining
        (state.remaining.card - 2)) := by
  have hindex : state.remaining.card - 1 =
      (state.remaining.card - 2) + 1 := by omega
  simpa [theorem8StoppedSourceTerminalRankedBidders, hindex] using
    theorem8_stopped_source_run_first_chosen_dropped_getElem?
      strategy values state hremaining htwo

/-- The realized values attached to a completed continuation rank ledger.  The
default is unreachable at every source rank used below; it merely gives the
finite list a total `ℕ → ℝ` presentation for the existing finite VCG-tail
definitions. -/
noncomputable def theorem8StoppedSourceTerminalRankedValue
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty) (defaultBidder : Bidder) : ℕ → ℝ :=
  fun rank => values
    ((theorem8StoppedSourceTerminalRankedBidders strategy values state
      hremaining).getD rank defaultBidder)

/-- The selected source dropout has exactly the value at its source-derived
terminal rank. -/
theorem theorem8_stopped_source_terminal_first_chosen_value_eq_ranked_value
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty)
    (htwo : 1 < state.remaining.card) (defaultBidder : Bidder) :
    values (theorem8ChosenStoppedDropper strategy values state hremaining
      (state.remaining.card - 2)) =
      theorem8StoppedSourceTerminalRankedValue strategy values state hremaining
        defaultBidder (state.remaining.card - 1) := by
  unfold theorem8StoppedSourceTerminalRankedValue
  have hget := theorem8_stopped_source_terminal_ranked_first_chosen_getElem?
    strategy values state hremaining htwo
  simp [List.getD_eq_getElem?_getD, hget]

/-- Completing the source execution after one actual dropout yields the same
terminal rank ledger as completing it before that step.  This is the
continuation-consistency bridge that lets the price induction retain one fixed
realized rank function. -/
theorem theorem8_stopped_source_terminal_ranked_bidders_next_eq
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty)
    (htwo : 1 < state.remaining.card) :
    let nextState := state.next strategy values hremaining
      (state.remaining.card - 2)
    let hnext_remaining : nextState.remaining.Nonempty :=
      Finset.card_pos.mp (by
        change 0 < (state.next strategy values hremaining
          (state.remaining.card - 2)).remaining.card
        have hstep :
            (state.next strategy values hremaining
              (state.remaining.card - 2)).remaining.card + 1 =
              state.remaining.card :=
          theorem8_stopped_source_next_card strategy values state
            hremaining (state.remaining.card - 2)
        omega)
    theorem8StoppedSourceTerminalRankedBidders strategy values nextState
      hnext_remaining =
      theorem8StoppedSourceTerminalRankedBidders strategy values state
        hremaining := by
  dsimp
  let nextState := state.next strategy values hremaining
    (state.remaining.card - 2)
  have hnext_card : nextState.remaining.card = state.remaining.card - 1 := by
    dsimp [nextState]
    have hstep := theorem8_stopped_source_next_card strategy values state
      hremaining (state.remaining.card - 2)
    omega
  have hfuel : state.remaining.card - 1 =
      (state.remaining.card - 2) + 1 := by omega
  have hnext_fuel : nextState.remaining.card - 1 =
      state.remaining.card - 2 := by
    rw [hnext_card]
    omega
  have hrun : theorem8StoppedSourceRun strategy values
      (state.remaining.card - 1) state =
      theorem8StoppedSourceRun strategy values
        (nextState.remaining.card - 1) nextState := by
    rw [hfuel, theorem8StoppedSourceRun, dif_pos htwo, hnext_fuel]
  change (theorem8StoppedSourceTerminalRankedBidders strategy values nextState _)
      = theorem8StoppedSourceTerminalRankedBidders strategy values state hremaining
  simp [theorem8StoppedSourceTerminalRankedBidders, hrun]

/-- With one fixed harmless out-of-range default, terminal rank values are
unchanged by taking the next source step. -/
theorem theorem8_stopped_source_terminal_ranked_value_next_eq
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty)
    (htwo : 1 < state.remaining.card) (defaultBidder : Bidder) :
    let nextState := state.next strategy values hremaining
      (state.remaining.card - 2)
    let hnext_remaining : nextState.remaining.Nonempty :=
      Finset.card_pos.mp (by
        change 0 < (state.next strategy values hremaining
          (state.remaining.card - 2)).remaining.card
        have hstep := theorem8_stopped_source_next_card strategy values state
          hremaining (state.remaining.card - 2)
        omega)
    theorem8StoppedSourceTerminalRankedValue strategy values nextState
      hnext_remaining defaultBidder =
      theorem8StoppedSourceTerminalRankedValue strategy values state
        hremaining defaultBidder := by
  dsimp
  funext rank
  unfold theorem8StoppedSourceTerminalRankedValue
  rw [theorem8_stopped_source_terminal_ranked_bidders_next_eq
    strategy values state hremaining htwo]

/-- The finite `B*` threshold at the first unassigned rank is its realized
value when the next CTR is zero.  This is the direct finite algebra underlying
the source's bottom-slot dropout, with no all-positive extension assumption. -/
theorem paper_theorem8_bstar_threshold_one_eq_value_of_next_click_zero
    (rankedValue clickThroughRate : ℕ → ℝ) (rank : ℕ)
    (hclick_ne : clickThroughRate rank ≠ 0)
    (hnext_zero : clickThroughRate (rank + 1) = 0) :
    paper_theorem8_bstar_threshold_bid rankedValue clickThroughRate 1
      (rank + 1) = rankedValue (rank + 1) := by
  simp only [paper_theorem8_bstar_threshold_bid,
    paper_theorem7_bstar_bid, paper_theorem7_ranked_vcg_tail_payment]
  rw [hnext_zero]
  field_simp
  ring

/-- The first actual source price is the finite `B*` threshold at the bottom
rank, now expressed using the completed source-derived rank ledger. -/
theorem theorem8_named_initial_stopped_source_first_clock_eq_bstar
    [Nonempty Bidder]
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (htwo : 1 < Fintype.card Bidder)
    (hvalue_nonneg : ∀ bidder, 0 ≤ values bidder)
    (hclick_pos : 0 < clickThroughRate (Fintype.card Bidder - 2))
    (hbottom_zero : clickThroughRate (Fintype.card Bidder - 1) = 0)
    (defaultBidder : Bidder) :
    let initialState := theorem8StoppedSourceInitialState Bidder
    let hremaining : initialState.remaining.Nonempty := Finset.univ_nonempty
    let rankedValue := theorem8StoppedSourceTerminalRankedValue
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate) values
      initialState hremaining defaultBidder
    (initialState.next
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values hremaining (Fintype.card Bidder - 2)).clockPrice =
      paper_theorem8_bstar_threshold_bid rankedValue clickThroughRate 1
        (Fintype.card Bidder - 1) := by
  dsimp
  let initialState := theorem8StoppedSourceInitialState Bidder
  let hremaining : initialState.remaining.Nonempty := Finset.univ_nonempty
  let strategy := theorem8ContinuousHistoryStrategy Bidder clickThroughRate
  let rankedValue := theorem8StoppedSourceTerminalRankedValue
    strategy values initialState hremaining defaultBidder
  have hclock := theorem8_named_initial_stopped_source_first_clock_eq_selected_value
    clickThroughRate values htwo hvalue_nonneg hclick_pos hbottom_zero
  have hselected : values (theorem8ChosenStoppedDropper strategy values
      initialState hremaining (Fintype.card Bidder - 2)) =
      rankedValue (Fintype.card Bidder - 1) := by
    have hselected' :=
      theorem8_stopped_source_terminal_first_chosen_value_eq_ranked_value
        strategy values initialState hremaining htwo defaultBidder
    simpa [rankedValue] using hselected'
  have hrank : Fintype.card Bidder - 2 + 1 =
      Fintype.card Bidder - 1 := by omega
  have hbase := paper_theorem8_bstar_threshold_one_eq_value_of_next_click_zero
    rankedValue clickThroughRate (Fintype.card Bidder - 2)
    (ne_of_gt hclick_pos) (by
      rw [hrank]
      exact hbottom_zero)
  change (initialState.next strategy values hremaining
      (Fintype.card Bidder - 2)).clockPrice = _
  calc
    (initialState.next strategy values hremaining
        (Fintype.card Bidder - 2)).clockPrice =
        values (theorem8ChosenStoppedDropper strategy values initialState
          hremaining (Fintype.card Bidder - 2)) := by
          simpa [strategy, initialState, hremaining] using hclock
    _ = rankedValue (Fintype.card Bidder - 1) := hselected
    _ = paper_theorem8_bstar_threshold_bid rankedValue clickThroughRate 1
        (Fintype.card Bidder - 1) := by simpa [hrank] using hbase.symm

/-- Immediately after the bottom source dropout, the singleton price history
already satisfies the exact finite `B*` ledger indexing convention. -/
theorem theorem8_named_initial_next_price_ledger_matches_bstar
    [Nonempty Bidder]
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (htwo : 1 < Fintype.card Bidder)
    (hvalue_nonneg : ∀ bidder, 0 ≤ values bidder)
    (hclick_pos : 0 < clickThroughRate (Fintype.card Bidder - 2))
    (hbottom_zero : clickThroughRate (Fintype.card Bidder - 1) = 0)
    (defaultBidder : Bidder) :
    let initialState := theorem8StoppedSourceInitialState Bidder
    let hremaining : initialState.remaining.Nonempty := Finset.univ_nonempty
    let rankedValue := theorem8StoppedSourceTerminalRankedValue
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate) values
      initialState hremaining defaultBidder
    (initialState.next
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values hremaining (Fintype.card Bidder - 2)).PriceLedgerMatchesBStar
        clickThroughRate rankedValue := by
  dsimp
  let initialState := theorem8StoppedSourceInitialState Bidder
  let hremaining : initialState.remaining.Nonempty := Finset.univ_nonempty
  let strategy := theorem8ContinuousHistoryStrategy Bidder clickThroughRate
  let rankedValue := theorem8StoppedSourceTerminalRankedValue
    strategy values initialState hremaining defaultBidder
  have hclock := theorem8_named_initial_stopped_source_first_clock_eq_bstar
    clickThroughRate values htwo hvalue_nonneg hclick_pos hbottom_zero
    defaultBidder
  change ∀ index,
    index < (initialState.next strategy values hremaining
      (Fintype.card Bidder - 2)).history.length → _
  intro index hindex
  have hzero : index = 0 := by
    change index < 1 at hindex
    omega
  subst index
  have hnext_card := theorem8_stopped_source_next_card strategy values
    initialState hremaining (Fintype.card Bidder - 2)
  have hdropped : (initialState.next strategy values hremaining
      (Fintype.card Bidder - 2)).dropped.length = 1 := by
    rw [theorem8_stopped_source_next_dropped_length]
    simp [initialState, theorem8StoppedSourceInitialState]
  have hcard : (initialState.next strategy values hremaining
      (Fintype.card Bidder - 2)).remaining.card = Fintype.card Bidder - 1 := by
    have hnext_card' : (initialState.next strategy values hremaining
        (Fintype.card Bidder - 2)).remaining.card + 1 = Fintype.card Bidder := by
      simpa [initialState, theorem8StoppedSourceInitialState] using hnext_card
    omega
  rw [hdropped, hcard]
  simpa [Theorem8StoppedSourceState.next,
    Theorem8StoppedSourceState.clockPrice, theorem8SourcePriceHistoryLastDropout,
    strategy, initialState, hremaining, rankedValue] using congrArg some hclock

omit [Fintype Bidder] [DecidableEq Bidder] in
/-- In any nonempty aligned source ledger, the newest record is the `B*`
threshold indexed by the current active block and number of lower records. -/
theorem theorem8_stopped_source_clock_eq_bstar_of_price_ledger
    (state : Theorem8StoppedSourceState Bidder)
    (clickThroughRate rankedValue : ℕ → ℝ)
    (haligned : state.DropLedgerAligned)
    (hdropped_pos : 0 < state.dropped.length)
    (hmatches : state.PriceLedgerMatchesBStar clickThroughRate rankedValue) :
    state.clockPrice = paper_theorem8_bstar_threshold_bid
      rankedValue clickThroughRate state.dropped.length state.remaining.card := by
  have hhistory_pos : 0 < state.history.length := by
    rw [← haligned]
    exact hdropped_pos
  have hentry := hmatches 0 hhistory_pos
  simp [Theorem8StoppedSourceState.clockPrice,
    theorem8SourcePriceHistoryLastDropout, List.head?_eq_getElem?, hentry]

/-- One positive-CTR source step advances the finite `B*` recurrence using
only rank data extracted from that state's completed execution ledger. -/
theorem theorem8_named_stopped_source_next_clock_eq_bstar_of_execution_rank
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty)
    (htwo : 1 < state.remaining.card)
    (hclick_pos : 0 < clickThroughRate (state.remaining.card - 2))
    (hnext_click_pos : 0 < clickThroughRate (state.remaining.card - 1))
    (hcurrent_le : clickThroughRate (state.remaining.card - 1) ≤
      clickThroughRate (state.remaining.card - 2))
    (hfeasible : state.ValuesFeasible values)
    (defaultBidder : Bidder) (rankedValue : ℕ → ℝ)
    (hranked : rankedValue = theorem8StoppedSourceTerminalRankedValue
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate) values state
      hremaining defaultBidder)
    (hlast : state.clockPrice =
      paper_theorem8_bstar_threshold_bid rankedValue clickThroughRate
        state.dropped.length state.remaining.card) :
    (state.next (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values hremaining (state.remaining.card - 2)).clockPrice =
      paper_theorem8_bstar_threshold_bid rankedValue clickThroughRate
        (state.dropped.length + 1) (state.remaining.card - 1) := by
  have hrank_succ : state.remaining.card - 2 + 1 =
      state.remaining.card - 1 := by omega
  have hrank_two : state.remaining.card - 2 + 2 =
      state.remaining.card := by omega
  have hnext_click_pos' : 0 < clickThroughRate
      (state.remaining.card - 2 + 1) := by
    simpa [hrank_succ] using hnext_click_pos
  have hcurrent_le' : clickThroughRate (state.remaining.card - 2 + 1) ≤
      clickThroughRate (state.remaining.card - 2) := by
    simpa [hrank_succ] using hcurrent_le
  have hselected : values (theorem8ChosenStoppedDropper
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values state hremaining (state.remaining.card - 2)) =
      rankedValue (state.remaining.card - 2 + 1) := by
    rw [hranked]
    simpa [hrank_succ] using
      theorem8_stopped_source_terminal_first_chosen_value_eq_ranked_value
        (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
        values state hremaining htwo defaultBidder
  have hstep := theorem8_named_stopped_source_next_clock_eq_bstar_of_ranked_data
    clickThroughRate rankedValue state.dropped.length values state hremaining
    (state.remaining.card - 2) hclick_pos hnext_click_pos' hcurrent_le'
    hfeasible hselected (by simpa [hrank_two] using hlast)
  simpa [hrank_succ] using hstep

/-- A positive-CTR source step preserves the exact `B*` indexing of every
recorded price: it prepends the newly derived recurrence record and merely
shifts the already matched history. -/
theorem theorem8_named_stopped_source_next_price_ledger_matches_bstar
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty)
    (htwo : 1 < state.remaining.card)
    (hclick_pos : 0 < clickThroughRate (state.remaining.card - 2))
    (hnext_click_pos : 0 < clickThroughRate (state.remaining.card - 1))
    (hcurrent_le : clickThroughRate (state.remaining.card - 1) ≤
      clickThroughRate (state.remaining.card - 2))
    (hfeasible : state.ValuesFeasible values)
    (haligned : state.DropLedgerAligned)
    (hdropped_pos : 0 < state.dropped.length)
    (defaultBidder : Bidder) (rankedValue : ℕ → ℝ)
    (hranked : rankedValue = theorem8StoppedSourceTerminalRankedValue
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate) values state
      hremaining defaultBidder)
    (hmatches : state.PriceLedgerMatchesBStar clickThroughRate rankedValue) :
    (state.next (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values hremaining (state.remaining.card - 2)).PriceLedgerMatchesBStar
        clickThroughRate rankedValue := by
  let strategy := theorem8ContinuousHistoryStrategy Bidder clickThroughRate
  let chosen := theorem8ChosenStoppedDropper strategy values state hremaining
    (state.remaining.card - 2)
  have hstep_card := theorem8_stopped_source_next_card strategy values state
    hremaining (state.remaining.card - 2)
  have herase_card : (state.remaining.erase chosen).card =
      state.remaining.card - 1 := by
    change (state.next strategy values hremaining
      (state.remaining.card - 2)).remaining.card = _
    omega
  have hlast := theorem8_stopped_source_clock_eq_bstar_of_price_ledger
    state clickThroughRate rankedValue haligned hdropped_pos hmatches
  have hnew_clock :=
    theorem8_named_stopped_source_next_clock_eq_bstar_of_execution_rank
      clickThroughRate values state hremaining htwo hclick_pos hnext_click_pos
      hcurrent_le hfeasible defaultBidder rankedValue hranked hlast
  intro index hindex
  cases index with
  | zero =>
      simpa [Theorem8StoppedSourceState.next,
        Theorem8StoppedSourceState.clockPrice,
        theorem8SourcePriceHistoryLastDropout, strategy, chosen, herase_card]
        using congrArg some hnew_clock
  | succ index =>
      have hhistory_length : state.history.length + 1 =
          (state.next strategy values hremaining
            (state.remaining.card - 2)).history.length := by
        rw [theorem8_stopped_source_next_history_length]
      have hhistory_length' :
          (state.next (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
            values hremaining (state.remaining.card - 2)).history.length =
            state.history.length + 1 := by
        simpa [strategy] using hhistory_length.symm
      have hindex_old : index < state.history.length := by omega
      have hindex_le : index ≤ state.dropped.length := by
        rw [haligned]
        omega
      have htail : (state.dropped.length + 1) - (index + 1) =
          state.dropped.length - index := by omega
      have hrank : (state.remaining.card - 1) + (index + 1) =
          state.remaining.card + index := by omega
      have hold := hmatches index hindex_old
      simpa [Theorem8StoppedSourceState.next, strategy, chosen,
        herase_card, htail, hrank] using hold

/-- Starting from any already-recorded source state, the finite run preserves
the exact `B*` formula for its entire dropout-price ledger.  The induction
uses only bounded finite source CTR assumptions and the execution-derived
rank-value invariant. -/
theorem theorem8_named_stopped_source_run_price_ledger_matches_bstar
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ) (K fuel : ℕ)
    (hclick_pos : ∀ rank, rank < K - 1 → 0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < K - 1 →
      0 ≤ clickThroughRate (rank + 1))
    (hcurrent_lt : ∀ rank, rank < K - 1 →
      clickThroughRate (rank + 1) < clickThroughRate rank)
    (state : Theorem8StoppedSourceState Bidder)
    (hremaining : state.remaining.Nonempty)
    (hcard_lt : state.remaining.card < K)
    (hfeasible : state.ValuesFeasible values)
    (haligned : state.DropLedgerAligned)
    (hdropped_pos : 0 < state.dropped.length)
    (defaultBidder : Bidder) (rankedValue : ℕ → ℝ)
    (hranked : rankedValue = theorem8StoppedSourceTerminalRankedValue
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate) values state
      hremaining defaultBidder)
    (hmatches : state.PriceLedgerMatchesBStar clickThroughRate rankedValue) :
    (theorem8StoppedSourceRun
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values fuel state).PriceLedgerMatchesBStar clickThroughRate rankedValue := by
  induction fuel generalizing state with
  | zero =>
      simpa [theorem8StoppedSourceRun] using hmatches
  | succ fuel ih =>
      by_cases htwo : 1 < state.remaining.card
      · let hnext_remaining :
            (state.next
            (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
              values hremaining (state.remaining.card - 2)).remaining.Nonempty :=
            Finset.card_pos.mp (by
              have hstep := theorem8_stopped_source_next_card
                (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
                values state hremaining (state.remaining.card - 2)
              omega)
        let nextState := state.next
          (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
          values hremaining (state.remaining.card - 2)
        have hrank : state.remaining.card - 2 < K - 1 := by omega
        have hnext_rank : state.remaining.card - 1 < K - 1 := by omega
        have hnext_feasible := theorem8_named_stopped_source_next_values_feasible
          clickThroughRate values state hremaining (state.remaining.card - 2)
          (hclick_pos _ hrank) (hcurrent_nonneg _ hrank)
          (hcurrent_lt _ hrank).le hfeasible
        have hnext_aligned := theorem8_stopped_source_next_drop_ledger_aligned
          (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
          values state hremaining (state.remaining.card - 2) haligned
        have hnext_dropped_pos : 0 < nextState.dropped.length := by
          dsimp [nextState]
          rw [theorem8_stopped_source_next_dropped_length]
          omega
        have hnext_matches :=
          have hcurrent_le : clickThroughRate (state.remaining.card - 1) ≤
              clickThroughRate (state.remaining.card - 2) := by
            have hcurrent_le' : clickThroughRate
                (state.remaining.card - 2 + 1) ≤
                clickThroughRate (state.remaining.card - 2) :=
              (hcurrent_lt _ hrank).le
            have hrank_succ : state.remaining.card - 2 + 1 =
                state.remaining.card - 1 := by omega
            simpa [hrank_succ] using hcurrent_le'
          theorem8_named_stopped_source_next_price_ledger_matches_bstar
            clickThroughRate values state hremaining htwo (hclick_pos _ hrank)
            (hclick_pos _ hnext_rank) hcurrent_le hfeasible
            haligned hdropped_pos defaultBidder rankedValue hranked hmatches
        have hnext_card_lt : nextState.remaining.card < K := by
          dsimp [nextState]
          have hstep := theorem8_stopped_source_next_card
            (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
            values state hremaining (state.remaining.card - 2)
          omega
        have hnext_ranked : rankedValue =
            theorem8StoppedSourceTerminalRankedValue
              (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
              values nextState hnext_remaining defaultBidder := by
          calc
            rankedValue = theorem8StoppedSourceTerminalRankedValue
                (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
                values state hremaining defaultBidder := hranked
            _ = theorem8StoppedSourceTerminalRankedValue
                (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
                values nextState hnext_remaining defaultBidder := by
                symm
                simpa [nextState] using
                  theorem8_stopped_source_terminal_ranked_value_next_eq
                    (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
                    values state hremaining htwo defaultBidder
        rw [theorem8StoppedSourceRun, dif_pos htwo]
        exact ih nextState hnext_remaining hnext_card_lt hnext_feasible
          hnext_aligned hnext_dropped_pos hnext_ranked
          (by simpa [nextState] using hnext_matches)
      · rw [theorem8StoppedSourceRun, dif_neg htwo]
        exact hmatches

/-- The completed finite source execution has a fully indexed `B*` price
ledger.  This is the finite history-level bridge needed to identify its GSP
payments with the source's VCG-tail calculation. -/
theorem theorem8_named_stopped_source_final_price_ledger_matches_bstar
    [Nonempty Bidder]
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (htwo : 1 < Fintype.card Bidder)
    (hvalue_nonneg : ∀ bidder, 0 ≤ values bidder)
    (hclick_pos : ∀ rank, rank < Fintype.card Bidder - 1 →
      0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < Fintype.card Bidder - 1 →
      0 ≤ clickThroughRate (rank + 1))
    (hcurrent_lt : ∀ rank, rank < Fintype.card Bidder - 1 →
      clickThroughRate (rank + 1) < clickThroughRate rank)
    (hbottom_zero : clickThroughRate (Fintype.card Bidder - 1) = 0)
    (defaultBidder : Bidder) :
    let initialState := theorem8StoppedSourceInitialState Bidder
    let hremaining : initialState.remaining.Nonempty := Finset.univ_nonempty
    let strategy := theorem8ContinuousHistoryStrategy Bidder clickThroughRate
    let rankedValue := theorem8StoppedSourceTerminalRankedValue strategy values
      initialState hremaining defaultBidder
    (theorem8StoppedSourceFinalState strategy values).PriceLedgerMatchesBStar
      clickThroughRate rankedValue := by
  dsimp
  let initialState := theorem8StoppedSourceInitialState Bidder
  let hremaining : initialState.remaining.Nonempty := Finset.univ_nonempty
  let strategy := theorem8ContinuousHistoryStrategy Bidder clickThroughRate
  let firstState := initialState.next strategy values hremaining
    (Fintype.card Bidder - 2)
  let rankedValue := theorem8StoppedSourceTerminalRankedValue strategy values
    initialState hremaining defaultBidder
  have hrank : Fintype.card Bidder - 2 < Fintype.card Bidder - 1 := by omega
  have hfirst_feasible := theorem8_named_stopped_source_next_values_feasible
    clickThroughRate values initialState hremaining
    (Fintype.card Bidder - 2) (hclick_pos _ hrank)
    (hcurrent_nonneg _ hrank) (hcurrent_lt _ hrank).le
    (theorem8_stopped_source_initial_values_feasible values hvalue_nonneg)
  have hfirst_aligned := theorem8_stopped_source_next_drop_ledger_aligned
    strategy values initialState hremaining (Fintype.card Bidder - 2)
    (theorem8_stopped_source_initial_drop_ledger_aligned Bidder)
  have hfirst_dropped_pos : 0 < firstState.dropped.length := by
    dsimp [firstState]
    rw [theorem8_stopped_source_next_dropped_length]
    simp [initialState, theorem8StoppedSourceInitialState]
  have hfirst_card : firstState.remaining.card = Fintype.card Bidder - 1 := by
    have hstep := theorem8_stopped_source_next_card strategy values initialState
      hremaining (Fintype.card Bidder - 2)
    have hstep' : firstState.remaining.card + 1 = Fintype.card Bidder := by
      simpa [firstState, initialState, theorem8StoppedSourceInitialState]
        using hstep
    omega
  have hfirst_remaining : firstState.remaining.Nonempty :=
    Finset.card_pos.mp (by rw [hfirst_card]; omega)
  have hfirst_card_lt : firstState.remaining.card < Fintype.card Bidder := by
    rw [hfirst_card]
    omega
  have hfirst_ranked : rankedValue =
      theorem8StoppedSourceTerminalRankedValue strategy values firstState
        hfirst_remaining defaultBidder := by
    calc
      rankedValue = theorem8StoppedSourceTerminalRankedValue strategy values
          initialState hremaining defaultBidder := rfl
      _ = theorem8StoppedSourceTerminalRankedValue strategy values firstState
          hfirst_remaining defaultBidder := by
          symm
          simpa [strategy, firstState] using
            theorem8_stopped_source_terminal_ranked_value_next_eq
              strategy values initialState hremaining htwo defaultBidder
  have hfirst_matches := theorem8_named_initial_next_price_ledger_matches_bstar
    clickThroughRate values htwo hvalue_nonneg (hclick_pos _ hrank)
    hbottom_zero defaultBidder
  have hrun := theorem8_named_stopped_source_run_price_ledger_matches_bstar
    clickThroughRate values (Fintype.card Bidder) (Fintype.card Bidder - 2)
    hclick_pos hcurrent_nonneg hcurrent_lt firstState hfirst_remaining
    hfirst_card_lt hfirst_feasible hfirst_aligned hfirst_dropped_pos
    defaultBidder rankedValue hfirst_ranked (by
      simpa [strategy, initialState, hremaining, firstState, rankedValue]
        using hfirst_matches)
  have hfuel : Fintype.card Bidder - 1 =
      (Fintype.card Bidder - 2) + 1 := by omega
  have htwo_initial : 1 < initialState.remaining.card := by
    simpa [initialState, theorem8StoppedSourceInitialState] using htwo
  change (theorem8StoppedSourceRun strategy values
    (Fintype.card Bidder - 1) initialState).PriceLedgerMatchesBStar
      clickThroughRate rankedValue
  rw [hfuel, theorem8StoppedSourceRun, dif_pos htwo_initial]
  simpa [firstState] using hrun

omit [Fintype Bidder] [DecidableEq Bidder] in
/-- In a terminal source ledger, each recorded GSP total payment is exactly
the finite VCG tail payment at the same realized rank.  This is the payment
calculation that the source's final-allocation sentence requires. -/
theorem theorem8_stopped_source_terminal_history_total_payment_eq_vcg_tail
    (state : Theorem8StoppedSourceState Bidder)
    (clickThroughRate rankedValue : ℕ → ℝ)
    (hterminal : state.remaining.card = 1)
    (haligned : state.DropLedgerAligned)
    (hmatches : state.PriceLedgerMatchesBStar clickThroughRate rankedValue)
    (index : ℕ) (hindex : index < state.history.length)
    (hclick_ne : clickThroughRate index ≠ 0) :
    clickThroughRate index * state.history.getD index 0 =
      paper_theorem7_ranked_vcg_tail_payment rankedValue clickThroughRate
        index (state.dropped.length - index) := by
  have hentry := hmatches index hindex
  have hindex_dropped : index < state.dropped.length := by
    rw [haligned]
    exact hindex
  have hrank : state.remaining.card + index = index + 1 := by
    rw [hterminal]
    omega
  have hvcg := paper_theorem7_bstar_next_bid_payment_eq_vcg
    rankedValue
    (fun j => paper_theorem7_ranked_vcg_tail_payment
      rankedValue clickThroughRate j (state.dropped.length - index))
    clickThroughRate index hclick_ne
  rw [List.getD_eq_getElem?_getD, hentry]
  simpa [paper_theorem8_bstar_threshold_bid, hrank] using hvcg

/-- At a nonempty market's terminal source state, the ledger contains one
dropout record for every bidder except the final top-position survivor. -/
theorem theorem8_stopped_source_final_state_dropped_length
    [Nonempty Bidder]
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) :
    (theorem8StoppedSourceFinalState strategy values).dropped.length =
      Fintype.card Bidder - 1 := by
  have hconserved := theorem8_stopped_source_run_card_add_dropped_length
    strategy values (Fintype.card Bidder - 1)
    (theorem8StoppedSourceInitialState Bidder)
  have hterminal := theorem8_stopped_source_final_state_remaining_card_one
    strategy values
  have hconserved' :
      (theorem8StoppedSourceFinalState strategy values).remaining.card +
          (theorem8StoppedSourceFinalState strategy values).dropped.length =
        Fintype.card Bidder := by
    simpa [theorem8StoppedSourceFinalState,
      theorem8StoppedSourceInitialState] using hconserved
  omega

/-- Source-faithful finite version of the terminal GSP-to-VCG payment bridge:
every assigned ledger price, multiplied by its slot CTR, is its VCG tail
payment. -/
theorem theorem8_named_stopped_source_final_history_total_payment_eq_vcg_tail
    [Nonempty Bidder]
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (htwo : 1 < Fintype.card Bidder)
    (hvalue_nonneg : ∀ bidder, 0 ≤ values bidder)
    (hclick_pos : ∀ rank, rank < Fintype.card Bidder - 1 →
      0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < Fintype.card Bidder - 1 →
      0 ≤ clickThroughRate (rank + 1))
    (hcurrent_lt : ∀ rank, rank < Fintype.card Bidder - 1 →
      clickThroughRate (rank + 1) < clickThroughRate rank)
    (hbottom_zero : clickThroughRate (Fintype.card Bidder - 1) = 0)
    (defaultBidder : Bidder) (index : ℕ)
    (hindex : index <
      (theorem8StoppedSourceFinalState
        (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
        values).history.length) :
    let strategy := theorem8ContinuousHistoryStrategy Bidder clickThroughRate
    let finalState := theorem8StoppedSourceFinalState strategy values
    let initialState := theorem8StoppedSourceInitialState Bidder
    let hremaining : initialState.remaining.Nonempty := Finset.univ_nonempty
    let rankedValue := theorem8StoppedSourceTerminalRankedValue strategy values
      initialState hremaining defaultBidder
    clickThroughRate index * finalState.history.getD index 0 =
      paper_theorem7_ranked_vcg_tail_payment rankedValue clickThroughRate index
        (finalState.dropped.length - index) := by
  dsimp
  let strategy := theorem8ContinuousHistoryStrategy Bidder clickThroughRate
  let finalState := theorem8StoppedSourceFinalState strategy values
  let initialState := theorem8StoppedSourceInitialState Bidder
  let hremaining : initialState.remaining.Nonempty := Finset.univ_nonempty
  let rankedValue := theorem8StoppedSourceTerminalRankedValue strategy values
    initialState hremaining defaultBidder
  have haligned := theorem8_stopped_source_final_state_drop_ledger_aligned
    strategy values
  have hdropped_length := theorem8_stopped_source_final_state_dropped_length
    strategy values
  have hindex_rank : index < Fintype.card Bidder - 1 := by
    rw [← hdropped_length, haligned]
    exact hindex
  have hterminal := theorem8_stopped_source_final_state_remaining_card_one
    strategy values
  have hmatches := theorem8_named_stopped_source_final_price_ledger_matches_bstar
    clickThroughRate values htwo hvalue_nonneg hclick_pos hcurrent_nonneg
    hcurrent_lt hbottom_zero defaultBidder
  exact theorem8_stopped_source_terminal_history_total_payment_eq_vcg_tail
    finalState clickThroughRate rankedValue hterminal haligned
    (by simpa [strategy, finalState, initialState, hremaining, rankedValue]
      using hmatches)
    index hindex (ne_of_gt (hclick_pos index hindex_rank))

omit [Fintype Bidder] in
/-- A valid source ledger is disjoint from the still-active bidders. -/
lemma theorem8_stopped_source_drop_ledger_disjoint
    (state : Theorem8StoppedSourceState Bidder)
    (hvalid : state.DropLedgerValid) :
    Disjoint state.remaining state.droppedFinset := by
  rw [Finset.disjoint_left]
  intro bidder hremaining hdropped
  exact hvalid.2 bidder (by simpa [Theorem8StoppedSourceState.droppedFinset]
    using hdropped) hremaining

omit [Fintype Bidder] in
/-- With a duplicate-free ledger, its finite-set cardinality is its recorded
sequence length. -/
lemma theorem8_stopped_source_dropped_finset_card
    (state : Theorem8StoppedSourceState Bidder)
    (hvalid : state.DropLedgerValid) :
    state.droppedFinset.card = state.dropped.length := by
  exact List.toFinset_card_of_nodup hvalid.1

/-- At a terminal finite source state, the active survivor together with the
dropout ledger accounts for every original bidder. -/
theorem theorem8_stopped_source_final_ledger_covers_univ
    [Nonempty Bidder]
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) :
    let finalState := theorem8StoppedSourceFinalState strategy values
    finalState.remaining ∪ finalState.droppedFinset = Finset.univ := by
  dsimp
  let finalState := theorem8StoppedSourceFinalState strategy values
  have hterminal : finalState.remaining.card = 1 := by
    exact theorem8_stopped_source_final_state_remaining_card_one strategy values
  have hlength : finalState.dropped.length = Fintype.card Bidder - 1 := by
    exact theorem8_stopped_source_final_state_dropped_length strategy values
  have hvalid : finalState.DropLedgerValid := by
    exact theorem8_stopped_source_final_state_drop_ledger_valid strategy values
  have hdrop_card : finalState.droppedFinset.card =
      Fintype.card Bidder - 1 := by
    rw [theorem8_stopped_source_dropped_finset_card finalState hvalid]
    exact hlength
  have hdisjoint : Disjoint finalState.remaining finalState.droppedFinset := by
    exact theorem8_stopped_source_drop_ledger_disjoint finalState hvalid
  apply Finset.eq_of_subset_of_card_le (by simp)
  rw [Finset.card_union_of_disjoint hdisjoint, hterminal, hdrop_card,
    Finset.card_univ]
  omega

/-- The finite source's realized rank ledger: the surviving top bidder first,
followed by reverse-chronological droppers.  This is the source-faithful
relabeling object for the eventual finite-rank VCG calculation. -/
noncomputable def theorem8StoppedSourceFinalRankedBidders
    [Nonempty Bidder]
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) : List Bidder :=
  let finalState := theorem8StoppedSourceFinalState strategy values
  let hnonempty : finalState.remaining.Nonempty :=
    Finset.card_pos.mp (by
      have hcard : finalState.remaining.card = 1 := by
        simpa [finalState] using
          theorem8_stopped_source_final_state_remaining_card_one strategy values
      omega)
  hnonempty.choose :: finalState.dropped

/-- The realized source rank ledger contains each finite bidder exactly once. -/
theorem theorem8_stopped_source_final_ranked_bidders_nodup
    [Nonempty Bidder]
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) :
    (theorem8StoppedSourceFinalRankedBidders strategy values).Nodup := by
  let finalState := theorem8StoppedSourceFinalState strategy values
  let hnonempty : finalState.remaining.Nonempty :=
    Finset.card_pos.mp (by
      have hcard : finalState.remaining.card = 1 := by
        simpa [finalState] using
          theorem8_stopped_source_final_state_remaining_card_one strategy values
      omega)
  have hvalid : finalState.DropLedgerValid := by
    exact theorem8_stopped_source_final_state_drop_ledger_valid strategy values
  have hsurvivor_not_dropped : hnonempty.choose ∉ finalState.dropped := by
    intro hmem
    exact hvalid.2 _ hmem hnonempty.choose_spec
  exact List.nodup_cons.mpr ⟨hsurvivor_not_dropped, hvalid.1⟩

/-- The realized source rank ledger has the market's full cardinality. -/
theorem theorem8_stopped_source_final_ranked_bidders_length
    [Nonempty Bidder]
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) :
    (theorem8StoppedSourceFinalRankedBidders strategy values).length =
      Fintype.card Bidder := by
  unfold theorem8StoppedSourceFinalRankedBidders
  change (theorem8StoppedSourceFinalState strategy values).dropped.length + 1 =
    Fintype.card Bidder
  have hdropped := theorem8_stopped_source_final_state_dropped_length
    strategy values
  have hcard : 0 < Fintype.card Bidder := Fintype.card_pos
  omega

/-- The realized source rank ledger's finite set is the entire bidder market. -/
theorem theorem8_stopped_source_final_ranked_bidders_toFinset
    [Nonempty Bidder]
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) :
    (theorem8StoppedSourceFinalRankedBidders strategy values).toFinset =
      Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (by simp)
  rw [List.toFinset_card_of_nodup
    (theorem8_stopped_source_final_ranked_bidders_nodup strategy values),
    theorem8_stopped_source_final_ranked_bidders_length strategy values,
    Finset.card_univ]

/-- Under the source's bounded adjacent click-rate conditions, the actual
terminal rank ledger is weakly ordered by decreasing realized values.  This is
the finite-bidder relabeling theorem needed before translating the ledger's
payments into the ranked VCG recurrence. -/
theorem theorem8_named_stopped_source_final_ranked_bidders_values_nonincreasing
    [Nonempty Bidder]
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (hvalue_nonneg : ∀ bidder, 0 ≤ values bidder)
    (hclick_pos : ∀ rank, rank < Fintype.card Bidder - 1 →
      0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < Fintype.card Bidder - 1 →
      0 ≤ clickThroughRate (rank + 1))
    (hcurrent_lt : ∀ rank, rank < Fintype.card Bidder - 1 →
      clickThroughRate (rank + 1) < clickThroughRate rank) :
    (theorem8StoppedSourceFinalRankedBidders
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      values).Pairwise fun earlier later => values later ≤ values earlier := by
  let strategy := theorem8ContinuousHistoryStrategy Bidder clickThroughRate
  let finalState := theorem8StoppedSourceFinalState strategy values
  let hnonempty : finalState.remaining.Nonempty :=
    Finset.card_pos.mp (by
      have hcard : finalState.remaining.card = 1 := by
        simpa [finalState, strategy] using
          theorem8_stopped_source_final_state_remaining_card_one strategy values
      omega)
  have hinvariants := theorem8_named_stopped_source_final_state_invariants
    clickThroughRate values hvalue_nonneg hclick_pos hcurrent_nonneg hcurrent_lt
  change (hnonempty.choose :: finalState.dropped).Pairwise
    (fun earlier later => values later ≤ values earlier)
  refine List.pairwise_cons.mpr ⟨?_, hinvariants.2.2⟩
  intro dropped hdropped
  exact hinvariants.2.1 dropped hnonempty.choose hdropped hnonempty.choose_spec

/-- Read a completed source dropout ledger as the GSP allocation described in
the paper: the final survivor gets the top slot, reverse-chronological
droppers receive the lower slots in that order, and the first dropout is
unassigned.  Each assigned bidder pays the following recorded dropout price.
The definition uses natural-number slots so the later finite-slot bridge can
derive its exact `Fin N` bounds instead of assuming them. -/
noncomputable def Theorem8StoppedSourceState.terminalGSPOutcome
    (state : Theorem8StoppedSourceState Bidder) : PositionOutcome Bidder ℕ where
  slotOf bidder :=
    if bidder ∈ state.remaining then some 0
    else if bidder ∈ state.dropped.dropLast then
      some (state.dropped.idxOf bidder + 1)
    else none
  paymentPerClick bidder :=
    if bidder ∈ state.remaining then state.history.getD 0 0
    else if bidder ∈ state.dropped.dropLast then
      state.history.getD (state.dropped.idxOf bidder + 1) 0
    else 0

omit [Fintype Bidder] in
/-- The terminal ledger outcome gives its unique surviving bidder the top
slot and charges the last recorded dropout price. -/
lemma theorem8_terminal_gsp_outcome_survivor
    (state : Theorem8StoppedSourceState Bidder) (bidder : Bidder)
    (hactive : bidder ∈ state.remaining) :
    state.terminalGSPOutcome.slotOf bidder = some 0 ∧
      state.terminalGSPOutcome.paymentPerClick bidder = state.history.getD 0 0 := by
  simp [Theorem8StoppedSourceState.terminalGSPOutcome, hactive]

omit [Fintype Bidder] in
/-- A non-first dropout receives the slot one rank below its ledger index and
pays the immediately lower recorded dropout price, exactly as GSP uses the
next lower bid for a winner's per-click payment. -/
lemma theorem8_terminal_gsp_outcome_later_dropper
    (state : Theorem8StoppedSourceState Bidder) (bidder : Bidder)
    (hinactive : bidder ∉ state.remaining)
    (hdropped : bidder ∈ state.dropped.dropLast) :
    state.terminalGSPOutcome.slotOf bidder =
        some (state.dropped.idxOf bidder + 1) ∧
      state.terminalGSPOutcome.paymentPerClick bidder =
        state.history.getD (state.dropped.idxOf bidder + 1) 0 := by
  simp [Theorem8StoppedSourceState.terminalGSPOutcome, hinactive, hdropped]

omit [Fintype Bidder] in
/-- The earliest source dropout receives no advertisement position when the
market has one more advertiser than slots. -/
lemma theorem8_terminal_gsp_outcome_first_dropper_unassigned
    (state : Theorem8StoppedSourceState Bidder) (bidder : Bidder)
    (hinactive : bidder ∉ state.remaining)
    (hfirst : bidder ∉ state.dropped.dropLast) :
    state.terminalGSPOutcome.slotOf bidder = none := by
  simp [Theorem8StoppedSourceState.terminalGSPOutcome, hinactive, hfirst]

end

end PaperInterface
end EOS07GSP
