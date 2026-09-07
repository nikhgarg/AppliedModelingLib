import GHW01DigitalGoods.BoundedSupply

/-!
# Ranked bounded-supply cutoffs

Section 11 of Goldberg--Hartline--Wright assumes a strict total order on bid
values, with an arbitrary fixed order resolving equal-value ties.  A numeric
posted price alone does not carry that convention: at a price shared by many
bidders, its raw acceptance count can exceed the intended supply.  This
isolated module supplies the deterministic realization used by a repaired
Section 11 model.

For a finite eligible population, `rankedBoundedWinnerSet` retains the top
`capacity` eligible bidders in the lexicographic `(bid value, tie-breaker)`
order.  Thus it has exactly the posted-price benchmark's cardinality and is
capacity feasible without treating all equal-price bids as simultaneous
acceptances.
-/

namespace GHW01DigitalGoods

open AppliedModelingLib
open AppliedModelingLib.Auction
open AppliedModelingLib.FiniteRanking
open scoped BigOperators

noncomputable section

/-- The bidders in a designated population who accept a numeric posted price. -/
def rankedEligibleFinset
    {Agent : Type*} [DecidableEq Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ) : Finset Agent :=
  population.filter fun i => price ≤ values i

/-- A posted numeric price together with the fixed secondary key that resolves
equal-valued bids in the source's strict total order.  The key is selected
from a sample and can subsequently be evaluated against a disjoint market. -/
structure RankedStaticCutoff (Agent : Type*) where
  price : ℝ
  tieKey : ℝ ×ₗ Agent

/-- Key-aware threshold acceptance.  The numeric price remains explicit and
the lexicographic key refines its eligible population to a strict cutoff. -/
def RankedStaticCutoff.Accepts
    {Agent : Type*} [LinearOrder Agent]
    (cutoff : RankedStaticCutoff Agent) (values : Agent → ℝ) (i : Agent) : Prop :=
  cutoff.price ≤ values i ∧ cutoff.tieKey ≤ valueTieKey values i

/-- The accepting bidders in a population for a sample-derived static cutoff. -/
noncomputable def rankedStaticCutoffAcceptanceSet
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ)
    (cutoff : RankedStaticCutoff Agent) : Finset Agent := by
  classical
  exact population.filter fun i => cutoff.Accepts values i

/-- The lexicographic key at a specified eligible rank. -/
noncomputable def rankedCutoffKey
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (eligible : Finset Agent) (values : Agent → ℝ) (cut : ℕ)
    (hcut : cut < eligible.card) : ℝ ×ₗ Agent :=
  rankKeyByValue eligible values rfl ⟨cut, hcut⟩

/--
The sample-derived static cutoff at the first retained rank.  Its proof
argument records that the retained ranked tail is nonempty; zero supply and
empty samples intentionally use the empty-acceptance branch instead of
inventing a cutoff key.
-/
noncomputable def rankedStaticCutoffOfPopulation
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ)
    (hcut :
      (rankedEligibleFinset population values price).card - capacity <
        (rankedEligibleFinset population values price).card) :
    RankedStaticCutoff Agent :=
  { price := price
    tieKey := rankedCutoffKey (rankedEligibleFinset population values price)
      values ((rankedEligibleFinset population values price).card - capacity) hcut }

/-- Total version of the source cutoff constructor.  If no rank can be
retained (zero supply or no eligible bid), it returns `none`, whose acceptance
set is empty. -/
noncomputable def rankedStaticCutoffOptionOfPopulation
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ) : Option (RankedStaticCutoff Agent) := by
  classical
  if hcut :
      (rankedEligibleFinset population values price).card - capacity <
        (rankedEligibleFinset population values price).card then
    exact some (rankedStaticCutoffOfPopulation population values price capacity hcut)
  else
    exact none

/-- Apply an optional sample-derived cutoff to any population.  This is the
form that can be evaluated on the market without recomputing a cutoff there. -/
noncomputable def rankedStaticCutoffOptionAcceptanceSet
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ)
    (cutoff : Option (RankedStaticCutoff Agent)) : Finset Agent :=
  match cutoff with
  | none => ∅
  | some staticCutoff =>
      rankedStaticCutoffAcceptanceSet population values staticCutoff

/-- Extend a sample profile to bidder identifiers solely so its static cutoff
key can be compared with market bidders.  Values outside the sample are fixed
to zero; this construction has no market-report argument. -/
def sampleValuesExtension
    {Agent : Type*} [DecidableEq Agent]
    (sample : Finset Agent) (sampleValues : ↑sample → ℝ) (i : Agent) : ℝ :=
  if hi : i ∈ sample then sampleValues ⟨i, hi⟩ else 0

theorem sampleValuesExtension_apply_mem
    {Agent : Type*} [DecidableEq Agent]
    (sample : Finset Agent) (sampleValues : ↑sample → ℝ)
    {i : Agent} (hi : i ∈ sample) :
    sampleValuesExtension sample sampleValues i = sampleValues ⟨i, hi⟩ := by
  simp [sampleValuesExtension, hi]

/--
Section 11's sample-derived `opt_k` descriptor.  Its type exposes the crucial
independence boundary: it consumes only the sample subtype profile and returns
a static cutoff which may later be evaluated on a market profile.
-/
noncomputable def sampleOptimalRankedStaticCutoff
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (sample : Finset Agent) [Nonempty ↑sample]
    (sampleValues : ↑sample → ℝ) (capacity : ℕ) :
    Option (RankedStaticCutoff Agent) :=
  rankedStaticCutoffOptionOfPopulation sample
    (sampleValuesExtension sample sampleValues)
    (boundedSupplyOptimalThreshold sampleValues capacity) capacity

/-- An upper ranked tail is exactly the set of eligible elements at least the
key of its first retained rank. -/
theorem rankedCutoffKey_acceptanceSet_eq_upperRankFinset
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (eligible : Finset Agent) (values : Agent → ℝ) (cut : ℕ)
    (hcut : cut < eligible.card) :
    eligible.filter fun i =>
      rankedCutoffKey eligible values cut hcut ≤ valueTieKey values i =
        upperRankFinset eligible values rfl cut := by
  classical
  let first : Fin eligible.card := ⟨cut, hcut⟩
  let rank := rankAgentByValue eligible values rfl
  let rankKey := rankKeyByValue eligible values rfl
  let keyOrder := (valueTieKeySet eligible values).orderEmbOfFin
    (valueTieKeySet_card eligible values)
  have hfirst_key : rankedCutoffKey eligible values cut hcut = rankKey first := by
    rfl
  have hrankKey_eq (r : Fin eligible.card) :
      rankKey r = valueTieKey values (rank r) := by
    exact rankKeyByValue_eq_valueTieKey eligible values rfl r
  have hrankKey_eq_keyOrder (r : Fin eligible.card) :
      rankKey r = keyOrder r := by
    rfl
  ext i
  constructor
  · intro hi
    have hi_filter := Finset.mem_filter.mp hi
    have hi_image : i ∈ Finset.image rank Finset.univ := by
      rw [image_rankAgentByValue_univ]
      exact hi_filter.1
    rcases Finset.mem_image.mp hi_image with ⟨r, _hr_univ, hri⟩
    refine Finset.mem_image.mpr ⟨r, ?_, hri⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ r, ?_⟩
    have hkey_le : rankKey first ≤ rankKey r := by
      calc
        rankKey first = rankedCutoffKey eligible values cut hcut := hfirst_key.symm
        _ ≤ valueTieKey values i := hi_filter.2
        _ = valueTieKey values (rank r) := by rw [hri]
        _ = rankKey r := (hrankKey_eq r).symm
    have hfirst_le_r : first ≤ r := by
      apply keyOrder.le_iff_le.mp
      rw [← hrankKey_eq_keyOrder first, ← hrankKey_eq_keyOrder r]
      exact hkey_le
    exact hfirst_le_r
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨r, hr_filter, hri⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simpa [rank, hri] using rankAgentByValue_mem eligible values rfl r
    · have hfirst_le_r : first ≤ r := (Finset.mem_filter.mp hr_filter).2
      have hkey_le : rankKey first ≤ rankKey r := by
        rw [hrankKey_eq_keyOrder first, hrankKey_eq_keyOrder r]
        exact keyOrder.monotone hfirst_le_r
      calc
        rankedCutoffKey eligible values cut hcut = rankKey first := hfirst_key
        _ ≤ rankKey r := hkey_le
        _ = valueTieKey values (rank r) := hrankKey_eq r
        _ = valueTieKey values i := by
          exact congrArg (valueTieKey values) (by simpa [rank] using hri)

/--
The source-faithful realization of a bounded posted price.  Eligible bidders
are ordered lexicographically by increasing `(value, tie-breaker)`, then the
upper `capacity` ranks are retained.  Consequently larger bids always precede
smaller bids, while a fixed `LinearOrder Agent` resolves equal-value ties.
-/
noncomputable def rankedBoundedWinnerSet
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ) : Finset Agent :=
  upperRankFinset
    (rankedEligibleFinset population values price) values rfl
    ((rankedEligibleFinset population values price).card - capacity)

/--
The sample-derived descriptor realizes exactly the top ranked eligible tail.
This is the missing `opt_k` tie convention: its sample acceptance count is not
the raw numeric `>= price` count when a boundary value has ties.
-/
theorem rankedStaticCutoffOfPopulation_acceptanceSet_eq_rankedBoundedWinnerSet
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ)
    (hcut :
      (rankedEligibleFinset population values price).card - capacity <
        (rankedEligibleFinset population values price).card) :
    rankedStaticCutoffAcceptanceSet population values
      (rankedStaticCutoffOfPopulation population values price capacity hcut) =
        rankedBoundedWinnerSet population values price capacity := by
  classical
  let eligible := rankedEligibleFinset population values price
  let cut := eligible.card - capacity
  let cutoff := rankedStaticCutoffOfPopulation population values price capacity hcut
  have hcutoff_price : cutoff.price = price := by
    rfl
  have haccept :
      rankedStaticCutoffAcceptanceSet population values cutoff =
        eligible.filter fun i => cutoff.tieKey ≤ valueTieKey values i := by
    ext i
    simp only [rankedStaticCutoffAcceptanceSet, Finset.mem_filter]
    change (i ∈ population ∧
        (cutoff.price ≤ values i ∧ cutoff.tieKey ≤ valueTieKey values i)) ↔
      (i ∈ eligible ∧ cutoff.tieKey ≤ valueTieKey values i)
    simp [hcutoff_price, eligible, rankedEligibleFinset, and_assoc]
  rw [haccept]
  simpa [cutoff, eligible, cut, rankedStaticCutoffOfPopulation,
    rankedBoundedWinnerSet] using
    (rankedCutoffKey_acceptanceSet_eq_upperRankFinset
      eligible values cut hcut)

/-- Revenue collected by the ranked realization of a fixed posted price. -/
noncomputable def rankedBoundedPriceRevenue
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ) : ℝ :=
  ((rankedBoundedWinnerSet population values price capacity).card : ℝ) * price

theorem rankedBoundedWinnerSet_subset_eligible
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ) :
    rankedBoundedWinnerSet population values price capacity ⊆
      rankedEligibleFinset population values price := by
  classical
  unfold rankedBoundedWinnerSet
  exact upperRankFinset_subset _ _ rfl _

theorem rankedBoundedWinnerSet_value_ge_price
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ) {i : Agent}
    (hi : i ∈ rankedBoundedWinnerSet population values price capacity) :
    price ≤ values i := by
  have heli : i ∈ rankedEligibleFinset population values price :=
    rankedBoundedWinnerSet_subset_eligible population values price capacity hi
  exact (Finset.mem_filter.mp heli).2

theorem rankedBoundedWinnerSet_card
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ) :
    (rankedBoundedWinnerSet population values price capacity).card =
      min capacity (rankedEligibleFinset population values price).card := by
  classical
  unfold rankedBoundedWinnerSet
  rw [upperRankFinset_card]
  omega

theorem rankedBoundedWinnerSet_card_le_capacity
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ) :
    (rankedBoundedWinnerSet population values price capacity).card ≤ capacity := by
  rw [rankedBoundedWinnerSet_card]
  exact min_le_left _ _

/-- The source-faithful static cutoff has at most the declared supply on the
sample from which it was derived. -/
theorem rankedStaticCutoffOfPopulation_acceptanceSet_card_le_capacity
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ)
    (hcut :
      (rankedEligibleFinset population values price).card - capacity <
        (rankedEligibleFinset population values price).card) :
    (rankedStaticCutoffAcceptanceSet population values
      (rankedStaticCutoffOfPopulation population values price capacity hcut)).card ≤
        capacity := by
  rw [rankedStaticCutoffOfPopulation_acceptanceSet_eq_rankedBoundedWinnerSet]
  exact rankedBoundedWinnerSet_card_le_capacity population values price capacity

/-- The total optional descriptor realizes the ranked sample winner set in all
edge cases.  In particular, a missing descriptor is exactly the empty winner
set, not an untracked convention. -/
theorem rankedStaticCutoffOptionOfPopulation_acceptanceSet_eq_rankedBoundedWinnerSet
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ) :
    rankedStaticCutoffOptionAcceptanceSet population values
      (rankedStaticCutoffOptionOfPopulation population values price capacity) =
        rankedBoundedWinnerSet population values price capacity := by
  classical
  by_cases hcut :
      (rankedEligibleFinset population values price).card - capacity <
        (rankedEligibleFinset population values price).card
  · simp [rankedStaticCutoffOptionOfPopulation, hcut,
      rankedStaticCutoffOptionAcceptanceSet,
      rankedStaticCutoffOfPopulation_acceptanceSet_eq_rankedBoundedWinnerSet]
  · have hge : (rankedEligibleFinset population values price).card ≤
        (rankedEligibleFinset population values price).card - capacity :=
      Nat.le_of_not_gt hcut
    have hwinner_empty : rankedBoundedWinnerSet population values price capacity = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [rankedBoundedWinnerSet_card]
      omega
    simp [rankedStaticCutoffOptionOfPopulation, hcut,
      rankedStaticCutoffOptionAcceptanceSet, hwinner_empty]

theorem rankedStaticCutoffOptionOfPopulation_acceptanceSet_card_le_capacity
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ) :
    (rankedStaticCutoffOptionAcceptanceSet population values
      (rankedStaticCutoffOptionOfPopulation population values price capacity)).card ≤
        capacity := by
  rw [rankedStaticCutoffOptionOfPopulation_acceptanceSet_eq_rankedBoundedWinnerSet]
  exact rankedBoundedWinnerSet_card_le_capacity population values price capacity

/-- On the sample itself, the `opt_k` descriptor is definitionally the
lexicographically tie-broken ranked winner set. -/
theorem sampleOptimalRankedStaticCutoff_sample_acceptance_eq_rankedWinnerSet
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (sample : Finset Agent) [Nonempty ↑sample]
    (sampleValues : ↑sample → ℝ) (capacity : ℕ) :
    rankedStaticCutoffOptionAcceptanceSet sample
      (sampleValuesExtension sample sampleValues)
      (sampleOptimalRankedStaticCutoff sample sampleValues capacity) =
        rankedBoundedWinnerSet sample (sampleValuesExtension sample sampleValues)
          (boundedSupplyOptimalThreshold sampleValues capacity) capacity := by
  simpa [sampleOptimalRankedStaticCutoff] using
    (rankedStaticCutoffOptionOfPopulation_acceptanceSet_eq_rankedBoundedWinnerSet
      sample (sampleValuesExtension sample sampleValues)
      (boundedSupplyOptimalThreshold sampleValues capacity) capacity)

/-- The sample side of the source-faithful `opt_k` descriptor never has more
than its requested sample supply. -/
theorem sampleOptimalRankedStaticCutoff_sample_acceptance_card_le_capacity
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (sample : Finset Agent) [Nonempty ↑sample]
    (sampleValues : ↑sample → ℝ) (capacity : ℕ) :
    (rankedStaticCutoffOptionAcceptanceSet sample
      (sampleValuesExtension sample sampleValues)
      (sampleOptimalRankedStaticCutoff sample sampleValues capacity)).card ≤
        capacity := by
  exact rankedStaticCutoffOptionOfPopulation_acceptanceSet_card_le_capacity
    sample (sampleValuesExtension sample sampleValues)
    (boundedSupplyOptimalThreshold sampleValues capacity) capacity

/-- Apply a descriptor computed from a sample to a market population.  The
construction has no market profile input; a truthful auction must still apply
the existing report-independent priority cap after this eligibility stage. -/
noncomputable def sampleOptimalRankedMarketEligibleSet
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (sample : Finset Agent) [Nonempty ↑sample]
    (sampleValues : ↑sample → ℝ) (sampleCapacity : ℕ)
    (market : Finset Agent) (marketValues : Agent → ℝ) : Finset Agent :=
  rankedStaticCutoffOptionAcceptanceSet market marketValues
    (sampleOptimalRankedStaticCutoff sample sampleValues sampleCapacity)

/-!
### Sample/market accounting for a ranked static cutoff

The cutoff selected from the sample is a static lexicographic key.  The
following lemmas make the accounting fact needed by Section 11 explicit: once
that key is fixed, its accepting population splits exactly across a disjoint
sample and market.  They deliberately do not assert that a *randomly selected*
sample cutoff has a balanced full-population acceptance count; establishing
that adaptive concentration statement is a separate probabilistic obligation.
-/

/-- Applying a fixed ranked cutoff commutes with splitting a population into
two finite parts. -/
theorem rankedStaticCutoffOptionAcceptanceSet_union
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (sample market : Finset Agent) (values : Agent → ℝ)
    (cutoff : Option (RankedStaticCutoff Agent)) :
    rankedStaticCutoffOptionAcceptanceSet (sample ∪ market) values cutoff =
      rankedStaticCutoffOptionAcceptanceSet sample values cutoff ∪
        rankedStaticCutoffOptionAcceptanceSet market values cutoff := by
  classical
  cases cutoff with
  | none => simp [rankedStaticCutoffOptionAcceptanceSet]
  | some cutoff =>
    ext i
    simp only [rankedStaticCutoffOptionAcceptanceSet,
      rankedStaticCutoffAcceptanceSet, Finset.mem_filter, Finset.mem_union]
    aesop

/-- A static cutoff's acceptance set depends only on the values of bidders in
the population to which it is applied. -/
theorem rankedStaticCutoffOptionAcceptanceSet_congr_on_population
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values₁ values₂ : Agent → ℝ)
    (cutoff : Option (RankedStaticCutoff Agent))
    (hvalues : ∀ i ∈ population, values₁ i = values₂ i) :
    rankedStaticCutoffOptionAcceptanceSet population values₁ cutoff =
      rankedStaticCutoffOptionAcceptanceSet population values₂ cutoff := by
  classical
  cases cutoff with
  | none => simp [rankedStaticCutoffOptionAcceptanceSet]
  | some cutoff =>
    ext i
    by_cases hi : i ∈ population
    · simp only [rankedStaticCutoffOptionAcceptanceSet,
        rankedStaticCutoffAcceptanceSet, Finset.mem_filter]
      simp only [RankedStaticCutoff.Accepts, valueTieKey]
      rw [hvalues i hi]
    · simp [rankedStaticCutoffOptionAcceptanceSet,
        rankedStaticCutoffAcceptanceSet, hi]

/-- If the populations are disjoint, so are their acceptances under any fixed
ranked cutoff. -/
theorem rankedStaticCutoffOptionAcceptanceSet_disjoint
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    {sample market : Finset Agent} (hdisjoint : Disjoint sample market)
    (values : Agent → ℝ) (cutoff : Option (RankedStaticCutoff Agent)) :
    Disjoint
      (rankedStaticCutoffOptionAcceptanceSet sample values cutoff)
      (rankedStaticCutoffOptionAcceptanceSet market values cutoff) := by
  classical
  cases cutoff with
  | none => simp [rankedStaticCutoffOptionAcceptanceSet]
  | some cutoff =>
    apply Finset.disjoint_left.mpr
    intro i his him
    simp only [rankedStaticCutoffOptionAcceptanceSet,
      rankedStaticCutoffAcceptanceSet, Finset.mem_filter] at his him
    exact (Finset.disjoint_left.mp hdisjoint) his.1 him.1

/-- Exact cardinal accounting for a ranked cutoff over a disjoint sample and
market. -/
theorem rankedStaticCutoffOptionAcceptanceSet_card_union
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    {sample market : Finset Agent} (hdisjoint : Disjoint sample market)
    (values : Agent → ℝ) (cutoff : Option (RankedStaticCutoff Agent)) :
    (rankedStaticCutoffOptionAcceptanceSet (sample ∪ market) values cutoff).card =
      (rankedStaticCutoffOptionAcceptanceSet sample values cutoff).card +
        (rankedStaticCutoffOptionAcceptanceSet market values cutoff).card := by
  rw [rankedStaticCutoffOptionAcceptanceSet_union]
  exact Finset.card_union_of_disjoint
    (rankedStaticCutoffOptionAcceptanceSet_disjoint hdisjoint values cutoff)

/-- Deterministic Section 11 bridge: if the sample side retains at least its
allocated sample capacity and the full fixed-cutoff population has at most the
sample allocation plus `capacity + slack` acceptances, then the market cap
rejects at most `slack` acceptors.  This isolates the precise concentration
obligation that an adaptive sampled `opt_k` proof must discharge. -/
theorem rankedStaticCutoffOption_market_rejection_le_slack_of_total_bound
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    {sample market : Finset Agent} (hdisjoint : Disjoint sample market)
    (values : Agent → ℝ) (cutoff : Option (RankedStaticCutoff Agent))
    {sampleCapacity capacity slack : ℕ}
    (hsample_capacity : sampleCapacity ≤
      (rankedStaticCutoffOptionAcceptanceSet sample values cutoff).card)
    (htotal_capacity :
      (rankedStaticCutoffOptionAcceptanceSet (sample ∪ market) values cutoff).card ≤
        sampleCapacity + capacity + slack) :
    boundedRejectionCount
        (rankedStaticCutoffOptionAcceptanceSet market values cutoff).card
        capacity ≤ slack := by
  apply boundedRejectionCount_le_slack
  have hcard := rankedStaticCutoffOptionAcceptanceSet_card_union
    hdisjoint values cutoff
  omega

/-- On a sample with enough threshold-eligible bids, the source's ranked
`opt_k` descriptor retains exactly its allocated sample capacity. -/
theorem sampleOptimalRankedStaticCutoff_sample_acceptance_card_eq_capacity
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (sample : Finset Agent) [Nonempty ↑sample]
    (sampleValues : ↑sample → ℝ) (capacity : ℕ)
    (hcapacity : capacity ≤
      (rankedEligibleFinset sample
        (sampleValuesExtension sample sampleValues)
        (boundedSupplyOptimalThreshold sampleValues capacity)).card) :
    (rankedStaticCutoffOptionAcceptanceSet sample
      (sampleValuesExtension sample sampleValues)
      (sampleOptimalRankedStaticCutoff sample sampleValues capacity)).card =
        capacity := by
  rw [sampleOptimalRankedStaticCutoff_sample_acceptance_eq_rankedWinnerSet,
    rankedBoundedWinnerSet_card, min_eq_left hcapacity]

/-- Section 11's actual sample-selected ranked descriptor satisfies the
deterministic rejection bridge whenever its sample has enough eligible bids
and the resulting global cutoff population obeys the stated cardinal bound.
The latter premise is intentionally explicit: it is the uniform adaptive
concentration obligation not supplied by a fixed-set tail inequality. -/
theorem sampleOptimalRankedStaticCutoff_market_rejection_le_slack_of_total_bound
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    {sample market : Finset Agent} (hdisjoint : Disjoint sample market)
    (values : Agent → ℝ) [Nonempty ↑sample]
    (sampleValues : ↑sample → ℝ) {sampleCapacity capacity slack : ℕ}
    (hvalues : ∀ i (hi : i ∈ sample), sampleValues ⟨i, hi⟩ = values i)
    (hsample_capacity : sampleCapacity ≤
      (rankedEligibleFinset sample
        (sampleValuesExtension sample sampleValues)
        (boundedSupplyOptimalThreshold sampleValues sampleCapacity)).card)
    (htotal_capacity :
      (rankedStaticCutoffOptionAcceptanceSet (sample ∪ market) values
        (sampleOptimalRankedStaticCutoff sample sampleValues sampleCapacity)).card ≤
        sampleCapacity + capacity + slack) :
    boundedRejectionCount
        (rankedStaticCutoffOptionAcceptanceSet market values
          (sampleOptimalRankedStaticCutoff sample sampleValues sampleCapacity)).card
        capacity ≤ slack := by
  apply rankedStaticCutoffOption_market_rejection_le_slack_of_total_bound
    hdisjoint values
      (sampleOptimalRankedStaticCutoff sample sampleValues sampleCapacity)
  · have hsample_congr :
        rankedStaticCutoffOptionAcceptanceSet sample values
          (sampleOptimalRankedStaticCutoff sample sampleValues sampleCapacity) =
        rankedStaticCutoffOptionAcceptanceSet sample
          (sampleValuesExtension sample sampleValues)
          (sampleOptimalRankedStaticCutoff sample sampleValues sampleCapacity) := by
      apply rankedStaticCutoffOptionAcceptanceSet_congr_on_population
      intro i hi
      rw [sampleValuesExtension_apply_mem]
      exact (hvalues i hi).symm
    have hsample_card : sampleCapacity =
        (rankedStaticCutoffOptionAcceptanceSet sample values
          (sampleOptimalRankedStaticCutoff sample sampleValues sampleCapacity)).card := by
      calc
        sampleCapacity =
            (rankedStaticCutoffOptionAcceptanceSet sample
              (sampleValuesExtension sample sampleValues)
              (sampleOptimalRankedStaticCutoff sample sampleValues sampleCapacity)).card := by
              symm
              exact sampleOptimalRankedStaticCutoff_sample_acceptance_card_eq_capacity
                sample sampleValues sampleCapacity hsample_capacity
        _ =
            (rankedStaticCutoffOptionAcceptanceSet sample values
              (sampleOptimalRankedStaticCutoff sample sampleValues sampleCapacity)).card := by
              exact congrArg Finset.card hsample_congr.symm
    exact hsample_card.le
  · exact htotal_capacity

/-- A retained bidder weakly dominates every eligible bidder rejected at the
cutoff.  This is the semantic content of the source's strict value order. -/
theorem rankedBoundedWinnerSet_retained_value_ge_rejected
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ) {retained rejected : Agent}
    (hretained : retained ∈ rankedBoundedWinnerSet population values price capacity)
    (hrejected_eligible : rejected ∈ rankedEligibleFinset population values price)
    (hrejected : rejected ∉ rankedBoundedWinnerSet population values price capacity) :
    values rejected ≤ values retained := by
  classical
  let eligible := rankedEligibleFinset population values price
  let cut := eligible.card - capacity
  have hretained' : retained ∈ upperRankFinset eligible values rfl cut := by
    simpa [rankedBoundedWinnerSet, eligible, cut] using hretained
  have hreject_eligible' : rejected ∈ eligible := by
    simpa [eligible] using hrejected_eligible
  have hreject_notupper : rejected ∉ upperRankFinset eligible values rfl cut := by
    simpa [rankedBoundedWinnerSet, eligible, cut] using hrejected
  have hreject_lower : rejected ∈ lowerRankFinset eligible values rfl cut := by
    by_contra hnotlower
    have hinupper : rejected ∈ upperRankFinset eligible values rfl cut := by
      rw [upperRankFinset_eq_sdiff_lowerRankFinset]
      exact Finset.mem_sdiff.mpr ⟨hreject_eligible', hnotlower⟩
    exact hreject_notupper hinupper
  exact lowerRank_value_le_upperRank_value eligible values rfl cut retained
    hretained' rejected hreject_lower

theorem rankedBoundedPriceRevenue_le_selected_value_sum
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ) :
    rankedBoundedPriceRevenue population values price capacity ≤
      ∑ i ∈ rankedBoundedWinnerSet population values price capacity, values i := by
  classical
  unfold rankedBoundedPriceRevenue
  calc
    ((rankedBoundedWinnerSet population values price capacity).card : ℝ) * price =
        ∑ _i ∈ rankedBoundedWinnerSet population values price capacity, price := by
          simp
    _ ≤ ∑ i ∈ rankedBoundedWinnerSet population values price capacity, values i := by
      exact Finset.sum_le_sum fun i hi =>
        rankedBoundedWinnerSet_value_ge_price population values price capacity hi

theorem rankedEligibleFinset_univ_card_eq_saleCount
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (price : ℝ) :
    (rankedEligibleFinset (Finset.univ : Finset Agent) values price).card =
      saleCount values price := by
  rfl

/-- Viewing a finite population as a subtype preserves the eligible count.
This is the bridge needed when Section 11 computes `opt_k` on a sample rather
than by zero-masking bidders outside that sample. -/
theorem rankedEligibleFinset_card_eq_saleCount_on_subtype
    {Agent : Type*} [DecidableEq Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ) :
    (rankedEligibleFinset population values price).card =
      saleCount (fun i : ↑population => values i) price := by
  classical
  let eligibleSubtype : Finset ↑population :=
    (Finset.univ : Finset ↑population).filter fun i => price ≤ values i
  let eligiblePopulation : Finset Agent :=
    rankedEligibleFinset population values price
  have hmap : eligibleSubtype.map (Function.Embedding.subtype _) =
      eligiblePopulation := by
    ext i
    simp [eligibleSubtype, eligiblePopulation, rankedEligibleFinset, and_comm]
  change eligiblePopulation.card = eligibleSubtype.card
  rw [← hmap, Finset.card_map]

/-- The ranked realization on a finite population has exactly the ordinary
bounded posted-price revenue of that population viewed as a subtype. -/
theorem rankedBoundedPriceRevenue_eq_boundedSupplySinglePriceRevenue_on_subtype
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (population : Finset Agent) (values : Agent → ℝ) (price : ℝ)
    (capacity : ℕ) :
    rankedBoundedPriceRevenue population values price capacity =
      boundedSupplySinglePriceRevenue (fun i : ↑population => values i)
        capacity price := by
  unfold rankedBoundedPriceRevenue boundedSupplySinglePriceRevenue
  rw [rankedBoundedWinnerSet_card,
    rankedEligibleFinset_card_eq_saleCount_on_subtype]
  rw [Nat.cast_min]

theorem rankedBoundedWinnerSet_univ_card
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (price : ℝ) (capacity : ℕ) :
    (rankedBoundedWinnerSet (Finset.univ : Finset Agent) values price capacity).card =
      min capacity (saleCount values price) := by
  rw [rankedBoundedWinnerSet_card,
    rankedEligibleFinset_univ_card_eq_saleCount]

theorem rankedBoundedPriceRevenue_eq_boundedSupplySinglePriceRevenue
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (price : ℝ) (capacity : ℕ) :
    rankedBoundedPriceRevenue (Finset.univ : Finset Agent) values price capacity =
      boundedSupplySinglePriceRevenue values capacity price := by
  unfold rankedBoundedPriceRevenue boundedSupplySinglePriceRevenue
  rw [rankedBoundedWinnerSet_univ_card]
  rw [Nat.cast_min]

/-- The sample-side ranked realization of `opt_k` earns exactly the sample's
bounded fixed-price benchmark.  This is the revenue bridge for the
sample-derived static descriptor, independent of any market cap. -/
theorem sampleOptimalRankedStaticCutoff_revenue_eq_sample_benchmark
    {Agent : Type*} [DecidableEq Agent] [LinearOrder Agent]
    (sample : Finset Agent) [Nonempty ↑sample]
    (sampleValues : ↑sample → ℝ) (capacity : ℕ) :
    rankedBoundedPriceRevenue sample (sampleValuesExtension sample sampleValues)
      (boundedSupplyOptimalThreshold sampleValues capacity) capacity =
        boundedSupplyFixedPriceBenchmark sampleValues capacity := by
  calc
    rankedBoundedPriceRevenue sample (sampleValuesExtension sample sampleValues)
        (boundedSupplyOptimalThreshold sampleValues capacity) capacity =
      boundedSupplySinglePriceRevenue
        (fun i : ↑sample => sampleValuesExtension sample sampleValues i)
        capacity (boundedSupplyOptimalThreshold sampleValues capacity) :=
      rankedBoundedPriceRevenue_eq_boundedSupplySinglePriceRevenue_on_subtype
        sample (sampleValuesExtension sample sampleValues)
        (boundedSupplyOptimalThreshold sampleValues capacity) capacity
    _ = boundedSupplySinglePriceRevenue sampleValues capacity
        (boundedSupplyOptimalThreshold sampleValues capacity) := by
      congr 2
      funext i
      exact sampleValuesExtension_apply_mem sample sampleValues i.property
    _ = boundedSupplyFixedPriceBenchmark sampleValues capacity :=
      boundedSupplyOptimalThreshold_revenue_eq_benchmark sampleValues capacity

theorem rankedBoundedWinnerSet_univ_value_sum_le_topK
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (price : ℝ) (capacity : ℕ) :
    (∑ i ∈ rankedBoundedWinnerSet (Finset.univ : Finset Agent)
      values price capacity, values i) ≤ boundedSupplyTopKTotal values capacity := by
  apply AppliedModelingLib.Probability.sum_le_topKSumOn capacity values
  exact rankedBoundedWinnerSet_card_le_capacity _ values price capacity

/-- The ranked realization of `opt_k` has no more than `k` acceptances. -/
noncomputable def rankedBoundedOptimalWinnerSet
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (capacity : ℕ) : Finset Agent :=
  rankedBoundedWinnerSet (Finset.univ : Finset Agent) values
    (boundedSupplyOptimalThreshold values capacity) capacity

theorem rankedBoundedOptimalWinnerSet_card_le_capacity
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (capacity : ℕ) :
    (rankedBoundedOptimalWinnerSet values capacity).card ≤ capacity := by
  exact rankedBoundedWinnerSet_card_le_capacity _ values
    (boundedSupplyOptimalThreshold values capacity) capacity

theorem rankedBoundedOptimalWinnerSet_revenue_eq_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (capacity : ℕ) :
    rankedBoundedPriceRevenue (Finset.univ : Finset Agent) values
        (boundedSupplyOptimalThreshold values capacity) capacity =
      boundedSupplyFixedPriceBenchmark values capacity := by
  rw [rankedBoundedPriceRevenue_eq_boundedSupplySinglePriceRevenue]
  exact boundedSupplyOptimalThreshold_revenue_eq_benchmark values capacity

/-- At a positive benchmark-attaining threshold, fewer than `k` bids are
strictly above the price.  Otherwise raising the price to the least strictly
higher bid would improve the bounded fixed-price benchmark.  This is the
numeric half of the source's strict tie-breaking convention. -/
theorem boundedSupplyOptimalThreshold_strictAbove_card_lt_capacity
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ)
    (hcapacity : 0 < capacity)
    (hprice : 0 < boundedSupplyOptimalThreshold values capacity) :
    ((Finset.univ : Finset Agent).filter fun i =>
      boundedSupplyOptimalThreshold values capacity < values i).card < capacity := by
  classical
  let price := boundedSupplyOptimalThreshold values capacity
  let strictAbove : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => price < values i
  have hprice_pos : 0 < price := by
    simpa [price] using hprice
  change strictAbove.card < capacity
  by_contra hnot
  have hcapacity_le : capacity ≤ strictAbove.card := Nat.le_of_not_gt hnot
  have hstrictAbove_nonempty : strictAbove.Nonempty := by
    apply Finset.card_pos.mp
    exact lt_of_lt_of_le hcapacity hcapacity_le
  obtain ⟨i, hi, hmin⟩ :=
    Finset.exists_min_image strictAbove values hstrictAbove_nonempty
  have hip : price < values i := (Finset.mem_filter.mp hi).2
  have hi_nonneg : 0 ≤ values i := hprice_pos.le.trans hip.le
  have hstrict_subset_i : strictAbove ⊆
      (Finset.univ : Finset Agent).filter fun j => values i ≤ values j := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨by simp, hmin j hj⟩
  have hsale_i : capacity ≤ saleCount values (values i) := by
    unfold saleCount
    exact hcapacity_le.trans (Finset.card_le_card hstrict_subset_i)
  have hstrict_subset_price : strictAbove ⊆
      (Finset.univ : Finset Agent).filter fun j => price ≤ values j := by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨by simp, (Finset.mem_filter.mp hj).2.le⟩
  have hsale_price : capacity ≤ saleCount values price := by
    unfold saleCount
    exact hcapacity_le.trans (Finset.card_le_card hstrict_subset_price)
  have hsale_i_real : (capacity : ℝ) ≤ (saleCount values (values i) : ℝ) := by
    exact_mod_cast hsale_i
  have hsale_price_real : (capacity : ℝ) ≤ (saleCount values price : ℝ) := by
    exact_mod_cast hsale_price
  have hrevenue_i :
      boundedSupplySinglePriceRevenue values capacity (values i) =
        (capacity : ℝ) * values i := by
    unfold boundedSupplySinglePriceRevenue
    rw [min_eq_left hsale_i_real]
  have hrevenue_price :
      boundedSupplySinglePriceRevenue values capacity price =
        (capacity : ℝ) * price := by
    unfold boundedSupplySinglePriceRevenue
    rw [min_eq_left hsale_price_real]
  have hoptimal :
      boundedSupplySinglePriceRevenue values capacity price =
        boundedSupplyFixedPriceBenchmark values capacity := by
    simpa [price] using
      (boundedSupplyOptimalThreshold_revenue_eq_benchmark values capacity)
  have hcontr_le : (capacity : ℝ) * values i ≤ (capacity : ℝ) * price := by
    calc
      (capacity : ℝ) * values i =
          boundedSupplySinglePriceRevenue values capacity (values i) := hrevenue_i.symm
      _ ≤ boundedSupplyFixedPriceBenchmark values capacity :=
        boundedSupplySinglePriceRevenue_le_benchmark values capacity hi_nonneg
      _ = boundedSupplySinglePriceRevenue values capacity price := hoptimal.symm
      _ = (capacity : ℝ) * price := hrevenue_price
  have hcontr_lt : (capacity : ℝ) * price < (capacity : ℝ) * values i :=
    mul_lt_mul_of_pos_left hip (by exact_mod_cast hcapacity)
  exact (not_lt_of_ge hcontr_le) hcontr_lt

/-- A positive optimal threshold is an actual bid value, rather than the
zero fallback used when no nonnegative candidate is selected. -/
theorem exists_bidder_value_eq_boundedSupplyOptimalThreshold_of_pos
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ)
    (hprice : 0 < boundedSupplyOptimalThreshold values capacity) :
    ∃ i : Agent, values i = boundedSupplyOptimalThreshold values capacity := by
  classical
  let i := boundedSupplyBenchmarkBidder values capacity
  by_cases hi : 0 ≤ values i
  · refine ⟨i, ?_⟩
    simp [boundedSupplyOptimalThreshold, i, hi]
  · have hzero : boundedSupplyOptimalThreshold values capacity = 0 := by
      simp [boundedSupplyOptimalThreshold, i, hi]
    linarith

/-- When the optimal threshold is positive and supply is nonzero, the ranked
realization retains a boundary bidder at exactly that threshold value. -/
theorem exists_rankedBoundedOptimalWinnerSet_value_eq_threshold_of_pos
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (capacity : ℕ)
    (hcapacity : 0 < capacity)
    (hprice : 0 < boundedSupplyOptimalThreshold values capacity) :
    ∃ i : Agent, i ∈ rankedBoundedOptimalWinnerSet values capacity ∧
      values i = boundedSupplyOptimalThreshold values capacity := by
  classical
  let price := boundedSupplyOptimalThreshold values capacity
  let winners := rankedBoundedWinnerSet (Finset.univ : Finset Agent)
    values price capacity
  let strictAbove : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => price < values i
  obtain ⟨boundary, hboundary_value⟩ :=
    exists_bidder_value_eq_boundedSupplyOptimalThreshold_of_pos
      values capacity hprice
  have hboundary_eligible : boundary ∈
      rankedEligibleFinset (Finset.univ : Finset Agent) values price := by
    simp [rankedEligibleFinset, price, hboundary_value]
  have hstrict_lt : strictAbove.card < capacity := by
    simpa [strictAbove, price] using
      (boundedSupplyOptimalThreshold_strictAbove_card_lt_capacity
        values capacity hcapacity hprice)
  by_cases hsupply : capacity ≤ saleCount values price
  · by_contra hnone
    have hwinners_card : winners.card = capacity := by
      rw [rankedBoundedWinnerSet_univ_card]
      exact min_eq_left hsupply
    have hwinners_subset : winners ⊆ strictAbove := by
      intro j hj
      have hj_price : price ≤ values j := by
        simpa [winners] using
          (rankedBoundedWinnerSet_value_ge_price
            (Finset.univ : Finset Agent) values price capacity hj)
      have hj_ne : price ≠ values j := by
        intro hvalue
        apply hnone
        refine ⟨j, ?_, ?_⟩
        · simpa [winners] using hj
        · exact hvalue.symm
      exact Finset.mem_filter.mpr ⟨by simp, lt_of_le_of_ne hj_price hj_ne⟩
    have hcapacity_le : capacity ≤ strictAbove.card := by
      rw [← hwinners_card]
      exact Finset.card_le_card hwinners_subset
    exact (not_lt_of_ge hcapacity_le) hstrict_lt
  · have hsupply_lt : saleCount values price < capacity := Nat.lt_of_not_ge hsupply
    have hwinners_eq : winners =
        rankedEligibleFinset (Finset.univ : Finset Agent) values price := by
      apply Finset.eq_of_subset_of_card_le
      · exact rankedBoundedWinnerSet_subset_eligible
          (Finset.univ : Finset Agent) values price capacity
      · rw [rankedBoundedWinnerSet_card,
          rankedEligibleFinset_univ_card_eq_saleCount]
        exact le_of_eq (min_eq_right hsupply_lt.le).symm
    refine ⟨boundary, ?_, hboundary_value⟩
    simpa [rankedBoundedOptimalWinnerSet, winners, price, hwinners_eq] using
      hboundary_eligible

/-- A finite upper value bound also bounds the benchmark-attaining threshold.
The zero fallback is covered by the visible nonnegative upper endpoint. -/
theorem boundedSupplyOptimalThreshold_le_of_forall_le
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ) {h : ℝ}
    (hh_nonneg : 0 ≤ h) (hvalues_le : ∀ i : Agent, values i ≤ h) :
    boundedSupplyOptimalThreshold values capacity ≤ h := by
  classical
  let i := boundedSupplyBenchmarkBidder values capacity
  by_cases hi : 0 ≤ values i
  · simp [boundedSupplyOptimalThreshold, i, hi, hvalues_le i]
  · simp [boundedSupplyOptimalThreshold, i, hi, hh_nonneg]

/--
The paper's scale condition `alpha * h < F_k` forces more than `alpha`
source-faithful ranked winners at the full optimal cutoff.  This avoids the
invalid inference from the raw numeric equality class at the threshold: the
cardinality here is the lexicographically tie-broken winner set.
-/
theorem rankedBoundedOptimalWinnerSet_card_gt_of_scale
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (capacity : ℕ) {alpha h : ℝ}
    (hh_pos : 0 < h) (hvalues_le : ∀ i : Agent, values i ≤ h)
    (hscale : alpha * h < boundedSupplyFixedPriceBenchmark values capacity) :
    alpha < (rankedBoundedOptimalWinnerSet values capacity).card := by
  have hprice_le : boundedSupplyOptimalThreshold values capacity ≤ h :=
    boundedSupplyOptimalThreshold_le_of_forall_le values capacity hh_pos.le hvalues_le
  have hbenchmark :
      ((rankedBoundedOptimalWinnerSet values capacity).card : ℝ) *
          boundedSupplyOptimalThreshold values capacity =
        boundedSupplyFixedPriceBenchmark values capacity := by
    simpa [rankedBoundedPriceRevenue, rankedBoundedOptimalWinnerSet] using
      (rankedBoundedOptimalWinnerSet_revenue_eq_benchmark values capacity)
  have hbenchmark_le : boundedSupplyFixedPriceBenchmark values capacity ≤
      ((rankedBoundedOptimalWinnerSet values capacity).card : ℝ) * h := by
    rw [← hbenchmark]
    exact mul_le_mul_of_nonneg_left hprice_le (by positivity)
  have hscaled : alpha * h <
      ((rankedBoundedOptimalWinnerSet values capacity).card : ℝ) * h :=
    hscale.trans_le hbenchmark_le
  exact lt_of_mul_lt_mul_right hscaled hh_pos.le

/-- The source's fixed-price benchmark is bounded by its top-`k` multi-price
relaxation, witnessed by the same ranked allocation rather than an unbounded
numeric-price acceptance set. -/
theorem boundedSupplyFixedPriceBenchmark_le_boundedSupplyTopKTotal_ranked
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (capacity : ℕ) :
    boundedSupplyFixedPriceBenchmark values capacity ≤
      boundedSupplyTopKTotal values capacity := by
  let price := boundedSupplyOptimalThreshold values capacity
  let winners := rankedBoundedWinnerSet (Finset.univ : Finset Agent)
    values price capacity
  calc
    boundedSupplyFixedPriceBenchmark values capacity =
        rankedBoundedPriceRevenue (Finset.univ : Finset Agent) values price capacity := by
          symm
          simpa [price] using
            (rankedBoundedOptimalWinnerSet_revenue_eq_benchmark values capacity)
    _ ≤ ∑ i ∈ winners, values i := by
      simpa [winners] using
        (rankedBoundedPriceRevenue_le_selected_value_sum
          (Finset.univ : Finset Agent) values price capacity)
    _ ≤ boundedSupplyTopKTotal values capacity := by
      simpa [winners] using
        (rankedBoundedWinnerSet_univ_value_sum_le_topK values price capacity)

end

end GHW01DigitalGoods
