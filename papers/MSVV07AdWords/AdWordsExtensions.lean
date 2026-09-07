import AppliedModelingLib.Algorithms.Online.AdWords

/-!
# Paper Extensions for AdWords and Generalized Online Matching

The JACM paper explains that several realistic variants are handled by running
the same Balance/MSVV proof on suitable effective bids. This file records those
finite reductions without disturbing the core AdWords proof.
-/

namespace AppliedModelingLib
namespace Online

namespace AdWordsInstance

variable {Advertiser Query Slot : Type*}

/--
Replace bids by an externally supplied effective charge/revenue function while
keeping advertiser budgets unchanged.
-/
def withEffectiveBids
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ) :
    AdWordsInstance Advertiser Query where
  budget := I.budget
  bid := effectiveBid

@[simp]
theorem withEffectiveBids_budget
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ) :
    (I.withEffectiveBids effectiveBid).budget = I.budget :=
  rfl

@[simp]
theorem withEffectiveBids_bid
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ) (a : Advertiser) (q : Query) :
    (I.withEffectiveBids effectiveBid).bid a q = effectiveBid a q :=
  rfl

theorem withEffectiveBids_positiveBudgets
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ)
    (hbudget : I.PositiveBudgets) :
    (I.withEffectiveBids effectiveBid).PositiveBudgets :=
  hbudget

theorem withEffectiveBids_nonnegativeBids
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ)
    (hbid : ∀ a q, 0 ≤ effectiveBid a q) :
    (I.withEffectiveBids effectiveBid).NonnegativeBids :=
  hbid

theorem withEffectiveBids_smallBids
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ) {ε : ℝ}
    (hsmall : ∀ a q, effectiveBid a q ≤ ε * I.budget a) :
    (I.withEffectiveBids effectiveBid).SmallBids ε :=
  hsmall

/--
Click-through-rate variant: the expected effective bid is actual bid times CTR.
-/
def withClickThroughRates
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) :
    AdWordsInstance Advertiser Query :=
  I.withEffectiveBids fun a q => ctr a q * I.bid a q

@[simp]
theorem withClickThroughRates_budget
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) :
    (I.withClickThroughRates ctr).budget = I.budget :=
  rfl

@[simp]
theorem withClickThroughRates_bid
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) (a : Advertiser) (q : Query) :
    (I.withClickThroughRates ctr).bid a q = ctr a q * I.bid a q :=
  rfl

theorem withClickThroughRates_nonnegativeBids
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ)
    (hctr : ∀ a q, 0 ≤ ctr a q)
    (hbid : I.NonnegativeBids) :
    (I.withClickThroughRates ctr).NonnegativeBids := by
  intro a q
  exact mul_nonneg (hctr a q) (hbid a q)

theorem withClickThroughRates_positiveBudgets
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ)
    (hbudget : I.PositiveBudgets) :
    (I.withClickThroughRates ctr).PositiveBudgets :=
  hbudget

theorem withClickThroughRates_smallBids_of_ctr_le_one
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) {ε : ℝ}
    (hctr_le_one : ∀ a q, ctr a q ≤ 1)
    (hbid : I.NonnegativeBids)
    (hsmall : I.SmallBids ε) :
    (I.withClickThroughRates ctr).SmallBids ε := by
  intro a q
  have hmul : ctr a q * I.bid a q ≤ 1 * I.bid a q :=
    mul_le_mul_of_nonneg_right (hctr_le_one a q) (hbid a q)
  calc
    (I.withClickThroughRates ctr).bid a q = ctr a q * I.bid a q := rfl
    _ ≤ 1 * I.bid a q := hmul
    _ = I.bid a q := by ring
    _ ≤ ε * I.budget a := hsmall a q

/--
Section 8 weighted-bid variant: advertiser weights scale all bids from the
same advertiser.
-/
def withAdvertiserWeights
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ) :
    AdWordsInstance Advertiser Query :=
  I.withEffectiveBids fun a q => weight a * I.bid a q

@[simp]
theorem withAdvertiserWeights_budget
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ) :
    (I.withAdvertiserWeights weight).budget = I.budget :=
  rfl

@[simp]
theorem withAdvertiserWeights_bid
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ) (a : Advertiser) (q : Query) :
    (I.withAdvertiserWeights weight).bid a q = weight a * I.bid a q :=
  rfl

theorem withAdvertiserWeights_nonnegativeBids
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ)
    (hweight : ∀ a, 0 ≤ weight a)
    (hbid : I.NonnegativeBids) :
    (I.withAdvertiserWeights weight).NonnegativeBids := by
  intro a q
  exact mul_nonneg (hweight a) (hbid a q)

theorem withAdvertiserWeights_positiveBudgets
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ)
    (hbudget : I.PositiveBudgets) :
    (I.withAdvertiserWeights weight).PositiveBudgets :=
  hbudget

theorem withAdvertiserWeights_smallBids_of_weight_le_one
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ) {ε : ℝ}
    (hweight_le_one : ∀ a, weight a ≤ 1)
    (hbid : I.NonnegativeBids)
    (hsmall : I.SmallBids ε) :
    (I.withAdvertiserWeights weight).SmallBids ε := by
  intro a q
  have hmul : weight a * I.bid a q ≤ 1 * I.bid a q :=
    mul_le_mul_of_nonneg_right (hweight_le_one a) (hbid a q)
  calc
    (I.withAdvertiserWeights weight).bid a q = weight a * I.bid a q := rfl
    _ ≤ 1 * I.bid a q := hmul
    _ = I.bid a q := by ring
    _ ≤ ε * I.budget a := hsmall a q

/--
Advertiser-availability variant: inactive advertisers have effective bid zero.
This models delayed entry, scheduled eligibility, or other exogenous activity
constraints expressible at the query level.
-/
def withAvailability
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)] :
    AdWordsInstance Advertiser Query :=
  I.withEffectiveBids fun a q => if active a q then I.bid a q else 0

@[simp]
theorem withAvailability_budget
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)] :
    (I.withAvailability active).budget = I.budget :=
  rfl

@[simp]
theorem withAvailability_bid
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)]
    (a : Advertiser) (q : Query) :
    (I.withAvailability active).bid a q =
      if active a q then I.bid a q else 0 :=
  rfl

theorem withAvailability_nonnegativeBids
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)]
    (hbid : I.NonnegativeBids) :
    (I.withAvailability active).NonnegativeBids := by
  intro a q
  by_cases hactive : active a q
  · simp [withAvailability, hactive, hbid a q]
  · simp [withAvailability, hactive]

theorem withAvailability_positiveBudgets
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)]
    (hbudget : I.PositiveBudgets) :
    (I.withAvailability active).PositiveBudgets :=
  hbudget

theorem withAvailability_smallBids
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)] {ε : ℝ}
    (hε : 0 ≤ ε)
    (hbudget : I.PositiveBudgets)
    (hsmall : I.SmallBids ε) :
    (I.withAvailability active).SmallBids ε := by
  intro a q
  by_cases hactive : active a q
  · simpa [withAvailability, hactive] using hsmall a q
  · have hnonneg : 0 ≤ ε * I.budget a :=
      mul_nonneg hε (le_of_lt (hbudget a))
    simpa [withAvailability, hactive] using hnonneg

/--
Multiple-slot expansion: a query with several ad slots is represented by one
ordinary AdWords query per slot. Slot-specific click-through or position effects
can be composed with `withEffectiveBids`.
-/
def withSlots
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*) :
    AdWordsInstance Advertiser (Σ q : Query, Slot q) where
  budget := I.budget
  bid := fun a qs => I.bid a qs.1

@[simp]
theorem withSlots_budget
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*) :
    (I.withSlots Slot).budget = I.budget :=
  rfl

@[simp]
theorem withSlots_bid
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*) (a : Advertiser) (qs : Σ q : Query, Slot q) :
    (I.withSlots Slot).bid a qs = I.bid a qs.1 :=
  rfl

theorem withSlots_nonnegativeBids
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*)
    (hbid : I.NonnegativeBids) :
    (I.withSlots Slot).NonnegativeBids := by
  intro a qs
  exact hbid a qs.1

theorem withSlots_positiveBudgets
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*)
    (hbudget : I.PositiveBudgets) :
    (I.withSlots Slot).PositiveBudgets :=
  hbudget

theorem withSlots_smallBids
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*) {ε : ℝ}
    (hsmall : I.SmallBids ε) :
    (I.withSlots Slot).SmallBids ε := by
  intro a qs
  exact hsmall a qs.1

/-! ### Page-level multiple-slot Balance selector -/

/-- A finite helper: choose an element of `s` maximizing the supplied score. -/
noncomputable def topByScoreMax {α : Type*} [DecidableEq α]
    (score : α → ℝ) (s : Finset α) (hs : s.Nonempty) : α :=
  Classical.choose (Finset.exists_max_image s score hs)

theorem topByScoreMax_mem {α : Type*} [DecidableEq α]
    (score : α → ℝ) (s : Finset α) (hs : s.Nonempty) :
    topByScoreMax score s hs ∈ s :=
  (Classical.choose_spec (Finset.exists_max_image s score hs)).1

theorem score_le_topByScoreMax {α : Type*} [DecidableEq α]
    (score : α → ℝ) (s : Finset α) (hs : s.Nonempty)
    {a : α} (ha : a ∈ s) :
    score a ≤ score (topByScoreMax score s hs) :=
  (Classical.choose_spec (Finset.exists_max_image s score hs)).2 a ha

/--
The `n` highest-scoring distinct elements of a finite set, with arbitrary but
fixed tie-breaking inherited from classical choice.
-/
noncomputable def topByScore {α : Type*} [DecidableEq α]
    (score : α → ℝ) : ℕ → Finset α → Finset α
  | 0, _ => ∅
  | n + 1, s =>
      if hs : s.Nonempty then
        let a := topByScoreMax score s hs
        insert a (topByScore score n (s.erase a))
      else
        ∅

theorem topByScore_subset {α : Type*} [DecidableEq α]
    (score : α → ℝ) :
    ∀ n s, topByScore score n s ⊆ s := by
  intro n
  induction n with
  | zero =>
      intro s a ha
      simp [topByScore] at ha
  | succ n ih =>
      intro s a ha
      unfold topByScore at ha
      by_cases hs : s.Nonempty
      · simp [hs] at ha
        rcases ha with ha | ha
        · simpa [ha] using topByScoreMax_mem score s hs
        · exact Finset.erase_subset _ _ (ih (s.erase (topByScoreMax score s hs)) ha)
      · simp [hs] at ha

theorem topByScore_card_eq_min {α : Type*} [DecidableEq α]
    (score : α → ℝ) :
    ∀ n s, (topByScore score n s).card = min n s.card := by
  intro n
  induction n with
  | zero =>
      intro s
      simp [topByScore]
  | succ n ih =>
      intro s
      unfold topByScore
      by_cases hs : s.Nonempty
      · simp [hs]
        let a := topByScoreMax score s hs
        have ha : a ∈ s := topByScoreMax_mem score s hs
        have hsubset : topByScore score n (s.erase a) ⊆ s.erase a :=
          topByScore_subset score n (s.erase a)
        have hanot : a ∉ topByScore score n (s.erase a) := by
          intro hmem
          exact (Finset.mem_erase.mp (hsubset hmem)).1 rfl
        calc
          (insert a (topByScore score n (s.erase a))).card =
              (topByScore score n (s.erase a)).card + 1 := by
                simp [hanot]
          _ = min n (s.erase a).card + 1 := by
                rw [ih (s.erase a)]
          _ = min (n + 1) s.card := by
                rw [← Finset.card_erase_add_one ha]
                exact (Nat.succ_min_succ n (s.erase a).card).symm
      · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

theorem topByScore_card_le {α : Type*} [DecidableEq α]
    (score : α → ℝ) (n : ℕ) (s : Finset α) :
    (topByScore score n s).card ≤ n := by
  rw [topByScore_card_eq_min]
  exact Nat.min_le_left n s.card

theorem score_le_of_mem_not_mem_topByScore {α : Type*} [DecidableEq α]
    (score : α → ℝ) :
    ∀ n s {a b : α}, a ∈ s → a ∉ topByScore score n s →
      b ∈ topByScore score n s → score a ≤ score b := by
  intro n
  induction n with
  | zero =>
      intro s a b _ha _hanot hb
      simp [topByScore] at hb
  | succ n ih =>
      intro s a b ha hanot hb
      unfold topByScore at hanot hb
      by_cases hs : s.Nonempty
      · simp [hs] at hanot hb
        let m := topByScoreMax score s hs
        rcases hb with hb | hb
        · subst b
          exact score_le_topByScoreMax score s hs ha
        · have ha_erase : a ∈ s.erase m := by
            exact (Finset.mem_erase.mpr ⟨hanot.1, ha⟩)
          exact ih (s.erase m) ha_erase hanot.2 hb
      · simp [hs] at hb

/--
The cardinality-`≤ k` subset of `s` with maximum total score.  This
powerset-based selector is proof-oriented: it gives the global top-`k` sum
property directly, while `topByScore` above records a recursive top-score
construction.
-/
def topKCandidates {α : Type*} [DecidableEq α] (s : Finset α) (k : ℕ) :
    Finset (Finset α) :=
  s.powerset.filter fun t => t.card ≤ k

theorem empty_mem_topKCandidates {α : Type*} [DecidableEq α]
    (s : Finset α) (k : ℕ) :
    ∅ ∈ topKCandidates s k := by
  simp [topKCandidates]

noncomputable def topKBySum {α : Type*} [DecidableEq α]
    (s : Finset α) (score : α → ℝ) (k : ℕ) : Finset α :=
  Classical.choose
    (Finset.exists_max_image (topKCandidates s k)
      (fun t => ∑ a ∈ t, score a)
      ⟨∅, empty_mem_topKCandidates s k⟩)

theorem topKBySum_mem_candidates {α : Type*} [DecidableEq α]
    (s : Finset α) (score : α → ℝ) (k : ℕ) :
    topKBySum s score k ∈ topKCandidates s k :=
  (Classical.choose_spec
    (Finset.exists_max_image (topKCandidates s k)
      (fun t => ∑ a ∈ t, score a)
      ⟨∅, empty_mem_topKCandidates s k⟩)).1

theorem topKBySum_subset {α : Type*} [DecidableEq α]
    (s : Finset α) (score : α → ℝ) (k : ℕ) :
    topKBySum s score k ⊆ s := by
  have hmem := topKBySum_mem_candidates s score k
  exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hmem).1)

theorem topKBySum_card_le {α : Type*} [DecidableEq α]
    (s : Finset α) (score : α → ℝ) (k : ℕ) :
    (topKBySum s score k).card ≤ k := by
  have hmem := topKBySum_mem_candidates s score k
  exact (Finset.mem_filter.mp hmem).2

theorem sum_le_topKBySum_of_subset_card_le {α : Type*} [DecidableEq α]
    (s t : Finset α) (score : α → ℝ) (k : ℕ)
    (hts : t ⊆ s) (htcard : t.card ≤ k) :
    (∑ a ∈ t, score a) ≤ ∑ a ∈ topKBySum s score k, score a := by
  have htmem : t ∈ topKCandidates s k := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hts, htcard⟩
  exact
    (Classical.choose_spec
      (Finset.exists_max_image (topKCandidates s k)
        (fun u => ∑ a ∈ u, score a)
        ⟨∅, empty_mem_topKCandidates s k⟩)).2 t htmem

/--
Page-level multiple-slot Balance rule shape: from the current slot-expanded
assignment and an original page query, return a finite set of distinct bidders.
-/
abbrev PageTopBalanceRule
    (Advertiser Query : Type*) (Slot : Query → Type*) :=
  Assignment Advertiser (Σ q : Query, Slot q) → Query → Finset Advertiser

/-- Number of ad slots on a source page. -/
def withSlotsPageSlotCount
    (Slot : Query → Type*) (slotFintype : ∀ q, Fintype (Slot q))
    (q : Query) : ℕ :=
  @Fintype.card (Slot q) (slotFintype q)

/-- Balance/MSVV score for a bidder on an original page under a slot-expanded state. -/
noncomputable def withSlotsPageBalanceScore
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q))
    (q : Query) (a : Advertiser) : ℝ :=
  I.bid a q * balanceDiscount ((I.withSlots Slot).spentFraction A a)

theorem withSlotsPageBalanceScore_eq_slot_balanceScore
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q))
    (q : Query) (s : Slot q) (a : Advertiser) :
    withSlotsPageBalanceScore I Slot A q a =
      (I.withSlots Slot).balanceScore A a ⟨q, s⟩ := by
  rfl

/--
A bidder is page-feasible when she can accept one slot of the original page
under the current slot-expanded assignment. Because `withSlots` gives every
slot of a page the same bid, this is equivalent to feasibility for any
particular slot when a slot exists.
-/
def withSlotsPageCanAssign
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q))
    (q : Query) (a : Advertiser) : Prop :=
  ∃ s : Slot q, (I.withSlots Slot).CanAssign A ⟨q, s⟩ a

theorem withSlotsPageCanAssign_slot
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q))
    (q : Query) (a : Advertiser)
    (h : withSlotsPageCanAssign I Slot A q a) (s : Slot q) :
    (I.withSlots Slot).CanAssign A ⟨q, s⟩ a := by
  rcases h with ⟨s₀, hs₀⟩
  simpa [withSlotsPageCanAssign, CanAssign, withSlots] using hs₀

/-- The finite set of bidders that can still accept a slot on this page. -/
noncomputable def withSlotsPageFeasibleAdvertisers
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q)) (q : Query) :
    Finset Advertiser := by
  classical
  exact Finset.univ.filter fun a => withSlotsPageCanAssign I Slot A q a

@[simp]
theorem mem_withSlotsPageFeasibleAdvertisers
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q)) (q : Query)
    (a : Advertiser) :
    a ∈ withSlotsPageFeasibleAdvertisers I Slot A q ↔
      withSlotsPageCanAssign I Slot A q a := by
  classical
  simp [withSlotsPageFeasibleAdvertisers]

/--
The source-shaped Section 6 selector: choose the top `n_q` distinct feasible
bidders for the original page, where `n_q` is the number of slots on that page.
-/
noncomputable def withSlotsPageTopBalanceBidders
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    (slotFintype : ∀ q, Fintype (Slot q))
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q)) (q : Query) :
    Finset Advertiser :=
  topByScore (fun a => withSlotsPageBalanceScore I Slot A q a)
    (withSlotsPageSlotCount Slot slotFintype q)
    (withSlotsPageFeasibleAdvertisers I Slot A q)

/-- The page-level top-`n_q` Balance rule as a reusable interface. -/
noncomputable def withSlotsPageTopBalanceRule
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    (slotFintype : ∀ q, Fintype (Slot q))
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser] :
    PageTopBalanceRule Advertiser Query Slot :=
  fun A q => withSlotsPageTopBalanceBidders I Slot slotFintype A q

/-- Predicate form of the page-level top-`n_q` distinct Balance interface. -/
structure IsWithSlotsPageTopBalanceSelection
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    (slotFintype : ∀ q, Fintype (Slot q))
    [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q)) (q : Query)
    (selected : Finset Advertiser) : Prop where
  card_le_slots : selected.card ≤ withSlotsPageSlotCount Slot slotFintype q
  selected_feasible :
    ∀ {a}, a ∈ selected → withSlotsPageCanAssign I Slot A q a
  no_repeated_bidder : selected.toList.Nodup
  score_maximal :
    ∀ {a b},
      withSlotsPageCanAssign I Slot A q a →
      a ∉ selected →
      b ∈ selected →
      withSlotsPageBalanceScore I Slot A q a ≤
        withSlotsPageBalanceScore I Slot A q b

theorem withSlotsPageTopBalanceBidders_subset_feasible
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    (slotFintype : ∀ q, Fintype (Slot q))
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q)) (q : Query) :
    withSlotsPageTopBalanceBidders I Slot slotFintype A q ⊆
      withSlotsPageFeasibleAdvertisers I Slot A q :=
  topByScore_subset
    (fun a => withSlotsPageBalanceScore I Slot A q a)
    (withSlotsPageSlotCount Slot slotFintype q)
    (withSlotsPageFeasibleAdvertisers I Slot A q)

theorem withSlotsPageTopBalanceBidders_card_eq_min
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    (slotFintype : ∀ q, Fintype (Slot q))
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q)) (q : Query) :
    (withSlotsPageTopBalanceBidders I Slot slotFintype A q).card =
      min (withSlotsPageSlotCount Slot slotFintype q)
        (withSlotsPageFeasibleAdvertisers I Slot A q).card :=
  topByScore_card_eq_min
    (fun a => withSlotsPageBalanceScore I Slot A q a)
    (withSlotsPageSlotCount Slot slotFintype q)
    (withSlotsPageFeasibleAdvertisers I Slot A q)

theorem withSlotsPageTopBalanceBidders_card_le_slots
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    (slotFintype : ∀ q, Fintype (Slot q))
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q)) (q : Query) :
    (withSlotsPageTopBalanceBidders I Slot slotFintype A q).card ≤
      withSlotsPageSlotCount Slot slotFintype q :=
  topByScore_card_le
    (fun a => withSlotsPageBalanceScore I Slot A q a)
    (withSlotsPageSlotCount Slot slotFintype q)
    (withSlotsPageFeasibleAdvertisers I Slot A q)

theorem withSlotsPageTopBalanceBidders_selected_feasible
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    (slotFintype : ∀ q, Fintype (Slot q))
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q)) (q : Query)
    {a : Advertiser}
    (ha : a ∈ withSlotsPageTopBalanceBidders I Slot slotFintype A q) :
    withSlotsPageCanAssign I Slot A q a := by
  exact (mem_withSlotsPageFeasibleAdvertisers I Slot A q a).1
    (withSlotsPageTopBalanceBidders_subset_feasible I Slot slotFintype A q ha)

theorem withSlotsPageTopBalanceBidders_selected_canAssign_slot
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    (slotFintype : ∀ q, Fintype (Slot q))
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q)) (q : Query)
    {a : Advertiser}
    (ha : a ∈ withSlotsPageTopBalanceBidders I Slot slotFintype A q) (s : Slot q) :
    (I.withSlots Slot).CanAssign A ⟨q, s⟩ a :=
  withSlotsPageCanAssign_slot I Slot A q a
    (withSlotsPageTopBalanceBidders_selected_feasible I Slot slotFintype A q ha) s

theorem withSlotsPageTopBalanceBidders_no_repeated_bidder
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    (slotFintype : ∀ q, Fintype (Slot q))
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q)) (q : Query) :
    (withSlotsPageTopBalanceBidders I Slot slotFintype A q).toList.Nodup :=
  Finset.nodup_toList _

theorem withSlotsPageTopBalanceBidders_score_maximal
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    (slotFintype : ∀ q, Fintype (Slot q))
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q)) (q : Query)
    {a b : Advertiser}
    (ha_feasible : withSlotsPageCanAssign I Slot A q a)
    (ha_not_selected : a ∉ withSlotsPageTopBalanceBidders I Slot slotFintype A q)
    (hb_selected : b ∈ withSlotsPageTopBalanceBidders I Slot slotFintype A q) :
    withSlotsPageBalanceScore I Slot A q a ≤
      withSlotsPageBalanceScore I Slot A q b := by
  exact
    score_le_of_mem_not_mem_topByScore
      (fun a => withSlotsPageBalanceScore I Slot A q a)
      (withSlotsPageSlotCount Slot slotFintype q)
      (withSlotsPageFeasibleAdvertisers I Slot A q)
      ((mem_withSlotsPageFeasibleAdvertisers I Slot A q a).2 ha_feasible)
      ha_not_selected
      hb_selected

theorem withSlotsPageTopBalanceBidders_is_selection
    (I : AdWordsInstance Advertiser Query) (Slot : Query → Type*)
    (slotFintype : ∀ q, Fintype (Slot q))
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)] [DecidableEq Advertiser]
    (A : Assignment Advertiser (Σ q : Query, Slot q)) (q : Query) :
    IsWithSlotsPageTopBalanceSelection I Slot slotFintype A q
      (withSlotsPageTopBalanceBidders I Slot slotFintype A q) where
  card_le_slots := withSlotsPageTopBalanceBidders_card_le_slots I Slot slotFintype A q
  selected_feasible := by
    intro a ha
    exact withSlotsPageTopBalanceBidders_selected_feasible I Slot slotFintype A q ha
  no_repeated_bidder :=
    withSlotsPageTopBalanceBidders_no_repeated_bidder I Slot slotFintype A q
  score_maximal := by
    intro a b ha_feasible ha_not_selected hb_selected
    exact withSlotsPageTopBalanceBidders_score_maximal
      I Slot slotFintype A q ha_feasible ha_not_selected hb_selected

/-- Distinct-advertiser condition for slot-expanded queries. -/
def withSlotsPerPageDistinct
    (Slot : Query → Type*) (A : Assignment Advertiser (Σ q : Query, Slot q)) : Prop :=
  ∀ q s₁ s₂ a,
    A ⟨q, s₁⟩ = some a →
    A ⟨q, s₂⟩ = some a →
    s₁ = s₂

theorem withSlotsPerPageDistinct_empty :
    (Slot : Query → Type*) →
    withSlotsPerPageDistinct
      Slot
      (emptyAssignment : Assignment Advertiser (Σ q : Query, Slot q)) := by
  intro Slot q s₁ s₂ a h1 h2
  simp [emptyAssignment] at h1

/--
Choice rule wrapper for slot-expanded queries that forbids assigning the same
advertiser twice to different slots of the same original query.
-/
noncomputable def withSlotsDistinctChoice
    (Slot : Query → Type*) (rule : ChoiceRule Advertiser (Σ q : Query, Slot q))
    (A : Assignment Advertiser (Σ q : Query, Slot q)) :
    (Σ q : Query, Slot q) → Option Advertiser :=
  by
    classical
    intro qs
    exact
    match rule A qs with
    | none => none
    | some a =>
      if hrepeat : ∃ s : Slot qs.1, A ⟨qs.1, s⟩ = some a then
        none
      else
        some a

theorem withSlotsDistinctChoice_rejects_used_advertiser
    (Slot : Query → Type*) (rule : ChoiceRule Advertiser (Σ q : Query, Slot q))
    (A : Assignment Advertiser (Σ q : Query, Slot q))
    (qs : Σ q : Query, Slot q) (a : Advertiser)
    (hchoice : withSlotsDistinctChoice Slot rule A qs = some a) :
    ¬ ∃ s : Slot qs.1, A ⟨qs.1, s⟩ = some a := by
  classical
  unfold withSlotsDistinctChoice at hchoice
  cases h : rule A qs with
  | none =>
      simp [h] at hchoice
  | some a' =>
    by_cases hrepeat : ∃ s : Slot qs.1, A ⟨qs.1, s⟩ = some a'
    · simp [h, hrepeat] at hchoice
    · have hEq' : some a' = some a := by
        simpa [h, hrepeat] using hchoice
      have hEq : a' = a := by simpa using hEq'
      intro hUsed
      exact hrepeat <| by simpa [hEq] using hUsed

theorem withSlotsDistinctChoice_allows_if_unused
    (Slot : Query → Type*) (rule : ChoiceRule Advertiser (Σ q : Query, Slot q))
    (A : Assignment Advertiser (Σ q : Query, Slot q))
    (qs : Σ q : Query, Slot q) (a : Advertiser)
    (hfree : ¬ ∃ s : Slot qs.1, A ⟨qs.1, s⟩ = some a)
    (hrule : rule A qs = some a) :
    withSlotsDistinctChoice Slot rule A qs = some a := by
  classical
  unfold withSlotsDistinctChoice
  rw [hrule]
  have hrepeat : ¬ ∃ s : Slot qs.1, A ⟨qs.1, s⟩ = some a := hfree
  simp [hrepeat]

/--
Assigning one slot to an advertiser that is unused on the corresponding
original query preserves the per-page distinct-advertiser invariant.
-/
theorem withSlotsPerPageDistinct_assignQuery
    (Slots : Query → Type*) [DecidableEq (Σ q : Query, Slots q)]
    (A : Assignment Advertiser (Σ q : Query, Slots q))
    (qs : Σ q : Query, Slots q) (a : Advertiser)
    (hA : withSlotsPerPageDistinct Slots A)
    (hfree : ¬ ∃ s : Slots qs.1, A ⟨qs.1, s⟩ = some a) :
    withSlotsPerPageDistinct Slots (assignQuery A qs a) := by
  intro q s₁ s₂ b h₁ h₂
  by_cases hleft : (⟨q, s₁⟩ : Σ q : Query, Slots q) = qs
  · subst qs
    by_cases hright : (⟨q, s₂⟩ : Σ q : Query, Slots q) = ⟨q, s₁⟩
    · cases hright
      rfl
    · have h₁ba : b = a := by
        have hsome : some a = some b := by
          simpa [assignQuery] using h₁
        simpa using Option.some.inj hsome.symm
      have h₂A : A ⟨q, s₂⟩ = some a := by
        simpa [assignQuery, hright, h₁ba] using h₂
      exact False.elim (hfree ⟨s₂, h₂A⟩)
  · by_cases hright : (⟨q, s₂⟩ : Σ q : Query, Slots q) = qs
    · subst qs
      have h₂ba : b = a := by
        have hsome : some a = some b := by
          simpa [assignQuery] using h₂
        simpa using Option.some.inj hsome.symm
      have h₁A : A ⟨q, s₁⟩ = some a := by
        simpa [assignQuery, hleft, h₂ba] using h₁
      exact False.elim (hfree ⟨s₁, h₁A⟩)
    · have h₁A : A ⟨q, s₁⟩ = some b := by
        simpa [assignQuery, hleft] using h₁
      have h₂A : A ⟨q, s₂⟩ = some b := by
        simpa [assignQuery, hright] using h₂
      exact hA q s₁ s₂ b h₁A h₂A

/--
One online step with the distinct slot wrapper preserves the per-page
distinct-advertiser invariant.
-/
theorem withSlotsDistinctChoice_step_preserves_per_page_distinct
    (Slots : Query → Type*) [Fintype (Σ q : Query, Slots q)] [DecidableEq Advertiser]
    [DecidableEq (Σ q : Query, Slots q)]
    (I : AdWordsInstance Advertiser (Σ q : Query, Slots q))
    (rule : ChoiceRule Advertiser (Σ q : Query, Slots q))
    (S : HistoryState Advertiser (Σ q : Query, Slots q))
    (qs : Σ q : Query, Slots q)
    (hA : withSlotsPerPageDistinct Slots S.assignment) :
    withSlotsPerPageDistinct Slots
      (stepHistoryState I (withSlotsDistinctChoice Slots rule) S qs).assignment := by
  unfold stepHistoryState
  by_cases hseen : qs ∈ S.seen
  · simp [hseen, hA]
  · simp [hseen]
    cases hchoice : withSlotsDistinctChoice Slots rule S.assignment qs with
    | none =>
        simpa [hchoice] using hA
    | some a =>
        have hfree :=
          withSlotsDistinctChoice_rejects_used_advertiser
            Slots rule S.assignment qs a hchoice
        simpa [hchoice] using
          withSlotsPerPageDistinct_assignQuery Slots S.assignment qs a hA hfree

/--
Running any slot-expanded choice rule through the distinct wrapper preserves
the per-page distinct-advertiser invariant from any initial state satisfying it.
-/
theorem withSlotsDistinctChoice_runHistoryStateFrom_per_page_distinct
    (Slots : Query → Type*) [Fintype (Σ q : Query, Slots q)] [DecidableEq Advertiser]
    [DecidableEq (Σ q : Query, Slots q)]
    (I : AdWordsInstance Advertiser (Σ q : Query, Slots q))
    (rule : ChoiceRule Advertiser (Σ q : Query, Slots q))
    (S : HistoryState Advertiser (Σ q : Query, Slots q))
    (history : List (Σ q : Query, Slots q))
    (hS : withSlotsPerPageDistinct Slots S.assignment) :
    withSlotsPerPageDistinct Slots
      (runHistoryStateFrom I (withSlotsDistinctChoice Slots rule) S history).assignment := by
  induction history generalizing S with
  | nil =>
      simpa [runHistoryStateFrom] using hS
  | cons qs rest ih =>
      exact
        ih (S := stepHistoryState I (withSlotsDistinctChoice Slots rule) S qs)
          (withSlotsDistinctChoice_step_preserves_per_page_distinct
            Slots I rule S qs hS)

/--
The assignment returned by the distinct slot wrapper assigns any advertiser to
at most one slot of each original query.
-/
theorem withSlotsDistinctChoice_runAssignment_per_page_distinct
    (Slots : Query → Type*) [Fintype (Σ q : Query, Slots q)] [DecidableEq Advertiser]
    [DecidableEq (Σ q : Query, Slots q)]
    (I : AdWordsInstance Advertiser (Σ q : Query, Slots q))
    (rule : ChoiceRule Advertiser (Σ q : Query, Slots q))
    (history : List (Σ q : Query, Slots q)) :
    withSlotsPerPageDistinct Slots
      (I.runAssignment (withSlotsDistinctChoice Slots rule) history) := by
  simpa [runAssignment, runHistoryState, initialHistoryState] using
    withSlotsDistinctChoice_runHistoryStateFrom_per_page_distinct
      Slots I rule initialHistoryState history
      (withSlotsPerPageDistinct_empty Slots)

end AdWordsInstance

end Online
end AppliedModelingLib
