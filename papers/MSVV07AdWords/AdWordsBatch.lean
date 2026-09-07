import MSVV07AdWords.AdWordsExtensions

/-!
# Page-Level Multiple-Slot AdWords

This file records the source-shaped Section 6 model where one arriving page can
receive several distinct advertisers at once.  The ordinary `withSlots`
reduction in `AdWordsExtensions.lean` remains useful, but the paper's
top-`n_q` sentence is naturally a batch/page-level statement.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Online

namespace AdWordsInstance

variable {Advertiser Query : Type*}

/-- A page-level assignment maps every page query to a finite set of bidders. -/
abbrev PageAssignment (Advertiser Query : Type*) :=
  Query → Finset Advertiser

/-- The empty page-level assignment. -/
def emptyPageAssignment : PageAssignment Advertiser Query :=
  fun _ => ∅

/-- Update a page-level assignment on one page query. -/
def pageAssignQuery [DecidableEq Query]
    (A : PageAssignment Advertiser Query) (q : Query)
    (selected : Finset Advertiser) :
    PageAssignment Advertiser Query :=
  fun q' => if q' = q then selected else A q'

/-- Page-level spend charged to advertiser `a`. -/
noncomputable def pageSpend
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (a : Advertiser) : ℝ :=
  ∑ q : Query, if a ∈ A q then I.bid a q else 0

/-- Page-level revenue of an assignment. -/
noncomputable def pageRevenue
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) : ℝ :=
  ∑ q : Query, ∑ a ∈ A q, I.bid a q

/--
Page-level feasibility: advertiser budgets are respected and each page receives
at most its declared number of ad slots.
-/
def PageFeasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (A : PageAssignment Advertiser Query) : Prop :=
  (∀ a, I.pageSpend A a ≤ I.budget a) ∧
    ∀ q, (A q).card ≤ slots q

/-- A bidder can still accept one ad on page `q` under a page assignment. -/
def PageCanAssign
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  I.pageSpend A a + I.bid a q ≤ I.budget a

/-- Page-level Balance/MSVV score. -/
noncomputable def pageBalanceScore
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (a : Advertiser) (q : Query) : ℝ :=
  I.bid a q * balanceDiscount (I.pageSpend A a / I.budget a)

/-- Page-level spent fraction. -/
noncomputable def pageSpentFraction
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (a : Advertiser) : ℝ :=
  I.pageSpend A a / I.budget a

/-- Page-level normalized MSVV alpha from the final spend vector. -/
noncomputable def pageMsvvNormalizedAlphaFromAssignment
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (a : Advertiser) : ℝ :=
  msvvNormalizedDualAlpha (I.pageSpentFraction A a)

/-- Page-level normalized alpha budget mass. -/
noncomputable def pageMsvvNormalizedAlphaBudgetMass
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) : ℝ :=
  ∑ a : Advertiser, I.budget a * I.pageMsvvNormalizedAlphaFromAssignment A a

/-- Page-level weighted spend assigned to advertisers under an alpha vector. -/
noncomputable def pageAssignedWeightedSpend
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (alpha : Advertiser → ℝ) : ℝ :=
  ∑ q : Query, ∑ a ∈ A q, I.bid a q * alpha a

/-- Positive part of a query slack score. -/
noncomputable def positiveSlackScore
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (a : Advertiser) (q : Query) : ℝ :=
  max 0 (I.slackScore alpha a q)

/--
The page-level query dual: the sum of the top `slots q` positive slack values
for page `q`.
-/
noncomputable def pageTopKSlackBeta
    [Fintype Advertiser] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (alpha : Advertiser → ℝ) (q : Query) : ℝ :=
  ∑ a ∈ topKBySum (Finset.univ : Finset Advertiser)
      (fun a => I.positiveSlackScore alpha a q) (slots q),
    I.positiveSlackScore alpha a q

@[simp]
theorem pageSpend_empty
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (a : Advertiser) :
    I.pageSpend (emptyPageAssignment : PageAssignment Advertiser Query) a = 0 := by
  simp [pageSpend, emptyPageAssignment]

@[simp]
theorem pageRevenue_empty
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) :
    I.pageRevenue (emptyPageAssignment : PageAssignment Advertiser Query) = 0 := by
  simp [pageRevenue, emptyPageAssignment]

theorem emptyPageAssignment_feasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (hbudget : I.NonnegativeBudgets) :
    I.PageFeasible slots (emptyPageAssignment : PageAssignment Advertiser Query) := by
  constructor
  · intro a
    simpa using hbudget a
  · intro q
    simp [emptyPageAssignment]

theorem pageSpend_nonneg
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (A : PageAssignment Advertiser Query) (a : Advertiser) :
    0 ≤ I.pageSpend A a := by
  unfold pageSpend
  exact Finset.sum_nonneg fun q _ => by
    by_cases ha : a ∈ A q
    · simp [ha, hbid a q]
    · simp [ha]

theorem pageRevenue_nonneg
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (A : PageAssignment Advertiser Query) :
    0 ≤ I.pageRevenue A := by
  unfold pageRevenue
  exact Finset.sum_nonneg fun q _ =>
    Finset.sum_nonneg fun a _ => hbid a q

theorem positiveSlackScore_nonneg
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (a : Advertiser) (q : Query) :
    0 ≤ I.positiveSlackScore alpha a q := by
  simp [positiveSlackScore]

theorem slackScore_le_positiveSlackScore
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (a : Advertiser) (q : Query) :
    I.slackScore alpha a q ≤ I.positiveSlackScore alpha a q := by
  simp [positiveSlackScore]

theorem pageAssignedWeightedSpend_eq_sum_pageSpend_mul
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (alpha : Advertiser → ℝ) :
    I.pageAssignedWeightedSpend A alpha =
      ∑ a : Advertiser, I.pageSpend A a * alpha a := by
  classical
  calc
    I.pageAssignedWeightedSpend A alpha =
        ∑ q : Query, ∑ a : Advertiser,
          if a ∈ A q then I.bid a q * alpha a else 0 := by
          unfold pageAssignedWeightedSpend
          apply Finset.sum_congr rfl
          intro q _hq
          simp
    _ = ∑ a : Advertiser, ∑ q : Query,
          if a ∈ A q then I.bid a q * alpha a else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ a : Advertiser, I.pageSpend A a * alpha a := by
          apply Finset.sum_congr rfl
          intro a _ha
          unfold pageSpend
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro q _hq
          by_cases ha : a ∈ A q <;> simp [ha]

theorem pageAssignedWeightedSpend_le_budget_weighted_of_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (A : PageAssignment Advertiser Query)
    (alpha : Advertiser → ℝ)
    (hA : I.PageFeasible slots A) (halpha : ∀ a, 0 ≤ alpha a) :
    I.pageAssignedWeightedSpend A alpha ≤
      ∑ a : Advertiser, I.budget a * alpha a := by
  rw [pageAssignedWeightedSpend_eq_sum_pageSpend_mul]
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_right (hA.1 a) (halpha a)

theorem pageRevenue_eq_weightedSpend_add_slack
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (alpha : Advertiser → ℝ) :
    I.pageRevenue A =
      I.pageAssignedWeightedSpend A alpha +
        ∑ q : Query, ∑ a ∈ A q, I.slackScore alpha a q := by
  classical
  unfold pageRevenue pageAssignedWeightedSpend slackScore
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem pageSlackSum_le_pageTopKSlackBeta
    [Fintype Advertiser] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (alpha : Advertiser → ℝ)
    (q : Query) (t : Finset Advertiser)
    (htcard : t.card ≤ slots q) :
    (∑ a ∈ t, I.slackScore alpha a q) ≤
      I.pageTopKSlackBeta slots alpha q := by
  have hpos :
      (∑ a ∈ t, I.slackScore alpha a q) ≤
        ∑ a ∈ t, I.positiveSlackScore alpha a q := by
    exact Finset.sum_le_sum fun a _ =>
      slackScore_le_positiveSlackScore I alpha a q
  have htop :
      (∑ a ∈ t, I.positiveSlackScore alpha a q) ≤
        I.pageTopKSlackBeta slots alpha q := by
    unfold pageTopKSlackBeta
    exact
      sum_le_topKBySum_of_subset_card_le
        (Finset.univ : Finset Advertiser) t
        (fun a => I.positiveSlackScore alpha a q) (slots q)
        (by intro a _ha; simp) htcard
  exact hpos.trans htop

theorem pageRevenue_le_budget_alpha_add_topKSlackBeta_of_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (A : PageAssignment Advertiser Query)
    (alpha : Advertiser → ℝ)
    (hA : I.PageFeasible slots A) (halpha : ∀ a, 0 ≤ alpha a) :
    I.pageRevenue A ≤
      (∑ a : Advertiser, I.budget a * alpha a) +
        ∑ q : Query, I.pageTopKSlackBeta slots alpha q := by
  rw [pageRevenue_eq_weightedSpend_add_slack I A alpha]
  exact add_le_add
    (pageAssignedWeightedSpend_le_budget_weighted_of_feasible
      I slots A alpha hA halpha)
    (Finset.sum_le_sum fun q _ =>
      pageSlackSum_le_pageTopKSlackBeta I slots alpha q (A q) (hA.2 q))

/-- The finite set of feasible page-level assignments. -/
noncomputable def pageFeasibleAssignments
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ) :
    Finset (PageAssignment Advertiser Query) := by
  classical
  exact Finset.univ.filter fun A => I.PageFeasible slots A

theorem mem_pageFeasibleAssignments
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ)
    (A : PageAssignment Advertiser Query) :
    A ∈ I.pageFeasibleAssignments slots ↔ I.PageFeasible slots A := by
  classical
  simp [pageFeasibleAssignments]

theorem pageFeasibleAssignments_nonempty
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ)
    (hbudget : I.NonnegativeBudgets) :
    (I.pageFeasibleAssignments slots).Nonempty := by
  classical
  refine ⟨emptyPageAssignment, ?_⟩
  exact (mem_pageFeasibleAssignments I slots
    (emptyPageAssignment : PageAssignment Advertiser Query)).2
    (emptyPageAssignment_feasible I slots hbudget)

/-- A chosen optimal page-level assignment. -/
noncomputable def pageOfflineOptimumAssignment
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ)
    (hbudget : I.NonnegativeBudgets) :
    PageAssignment Advertiser Query := by
  classical
  exact
    Classical.choose
      (Finset.exists_max_image (I.pageFeasibleAssignments slots)
        (fun A => I.pageRevenue A)
        (pageFeasibleAssignments_nonempty I slots hbudget))

/-- The page-level offline optimum value. -/
noncomputable def pageOfflineOptimumValue
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ)
    (hbudget : I.NonnegativeBudgets) : ℝ :=
  I.pageRevenue (I.pageOfflineOptimumAssignment slots hbudget)

theorem pageOfflineOptimumAssignment_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ)
    (hbudget : I.NonnegativeBudgets) :
    I.PageFeasible slots (I.pageOfflineOptimumAssignment slots hbudget) := by
  classical
  have hmem :
      I.pageOfflineOptimumAssignment slots hbudget ∈
        I.pageFeasibleAssignments slots :=
    (Classical.choose_spec
      (Finset.exists_max_image (I.pageFeasibleAssignments slots)
        (fun A => I.pageRevenue A)
        (pageFeasibleAssignments_nonempty I slots hbudget))).1
  exact (mem_pageFeasibleAssignments I slots _).1 hmem

theorem pageOfflineOptimumValue_le_budget_alpha_add_topKSlackBeta
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (hbudget : I.NonnegativeBudgets)
    (alpha : Advertiser → ℝ) (halpha : ∀ a, 0 ≤ alpha a) :
    I.pageOfflineOptimumValue slots hbudget ≤
      (∑ a : Advertiser, I.budget a * alpha a) +
        ∑ q : Query, I.pageTopKSlackBeta slots alpha q := by
  exact
    pageRevenue_le_budget_alpha_add_topKSlackBeta_of_feasible
      I slots (I.pageOfflineOptimumAssignment slots hbudget) alpha
      (pageOfflineOptimumAssignment_feasible I slots hbudget) halpha

theorem pageSpend_pageAssignQuery_of_unassigned
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (q : Query)
    (selected : Finset Advertiser) (a : Advertiser)
    (hunassigned : A q = ∅) :
    I.pageSpend (pageAssignQuery A q selected) a =
      I.pageSpend A a + if a ∈ selected then I.bid a q else 0 := by
  classical
  unfold pageSpend pageAssignQuery
  calc
    (∑ q' : Query,
        if a ∈ (if q' = q then selected else A q') then I.bid a q' else 0) =
        ∑ q' : Query,
          ((if a ∈ A q' then I.bid a q' else 0) +
            if q' = q then
              if a ∈ selected then I.bid a q else 0
            else
              0) := by
          apply Finset.sum_congr rfl
          intro q' _hq'
          by_cases hq : q' = q
          · subst q'
            simp [hunassigned]
          · simp [hq]
    _ = (∑ q' : Query, if a ∈ A q' then I.bid a q' else 0) +
        ∑ q' : Query,
          (if q' = q then if a ∈ selected then I.bid a q else 0 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ q' : Query, if a ∈ A q' then I.bid a q' else 0) +
        (if a ∈ selected then I.bid a q else 0) := by
          rw [Finset.sum_ite_eq']
          simp

theorem pageRevenue_pageAssignQuery_of_unassigned
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (q : Query)
    (selected : Finset Advertiser)
    (hunassigned : A q = ∅) :
    I.pageRevenue (pageAssignQuery A q selected) =
      I.pageRevenue A + ∑ a ∈ selected, I.bid a q := by
  classical
  unfold pageRevenue pageAssignQuery
  calc
    (∑ q' : Query,
        ∑ a ∈ (if q' = q then selected else A q'), I.bid a q') =
        ∑ q' : Query,
          ((∑ a ∈ A q', I.bid a q') +
            if q' = q then ∑ a ∈ selected, I.bid a q else 0) := by
          apply Finset.sum_congr rfl
          intro q' _hq'
          by_cases hq : q' = q
          · subst q'
            simp [hunassigned]
          · simp [hq]
    _ = (∑ q' : Query, ∑ a ∈ A q', I.bid a q') +
        ∑ q' : Query,
          (if q' = q then ∑ a ∈ selected, I.bid a q else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ q' : Query, ∑ a ∈ A q', I.bid a q') +
        ∑ a ∈ selected, I.bid a q := by
          rw [Finset.sum_ite_eq']
          simp

theorem pageFeasible_pageAssignQuery_of_canAssign
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ)
    (A : PageAssignment Advertiser Query) (q : Query)
    (selected : Finset Advertiser)
    (hA : I.PageFeasible slots A)
    (hunassigned : A q = ∅)
    (hcard : selected.card ≤ slots q)
    (hcan : ∀ a, a ∈ selected → I.PageCanAssign A q a) :
    I.PageFeasible slots (pageAssignQuery A q selected) := by
  constructor
  · intro a
    rw [pageSpend_pageAssignQuery_of_unassigned I A q selected a hunassigned]
    by_cases ha : a ∈ selected
    · simpa [PageCanAssign, ha] using hcan a ha
    · have hspend := hA.1 a
      simpa [ha] using hspend
  · intro q'
    by_cases hq : q' = q
    · subst q'
      simp [pageAssignQuery, hcard]
    · simpa [pageAssignQuery, hq] using hA.2 q'

theorem pageSpentFraction_pageAssignQuery_selected
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (q : Query)
    (selected : Finset Advertiser) (a : Advertiser)
    (hunassigned : A q = ∅) (ha : a ∈ selected)
    (hbudget : I.budget a ≠ 0) :
    I.pageSpentFraction (pageAssignQuery A q selected) a =
      I.pageSpentFraction A a + I.bid a q / I.budget a := by
  unfold pageSpentFraction
  rw [pageSpend_pageAssignQuery_of_unassigned I A q selected a hunassigned]
  simp [ha]
  field_simp [hbudget]

theorem pageSpentFraction_pageAssignQuery_not_selected
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (q : Query)
    (selected : Finset Advertiser) (a : Advertiser)
    (hunassigned : A q = ∅) (ha : a ∉ selected) :
    I.pageSpentFraction (pageAssignQuery A q selected) a =
      I.pageSpentFraction A a := by
  unfold pageSpentFraction
  rw [pageSpend_pageAssignQuery_of_unassigned I A q selected a hunassigned]
  simp [ha]

theorem msvvRatio_mul_pageNormalizedAlpha_increment_add_balanceScore_le_bid_add_alphaError
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (A : PageAssignment Advertiser Query) (q : Query)
    (selected : Finset Advertiser) (a : Advertiser)
    (hunassigned : A q = ∅)
    (hAfeasible : I.pageSpend A a ≤ I.budget a)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε)
    (ha : a ∈ selected) :
    msvvRatio *
        (I.budget a *
          (I.pageMsvvNormalizedAlphaFromAssignment
              (pageAssignQuery A q selected) a -
            I.pageMsvvNormalizedAlphaFromAssignment A a)) +
        I.pageBalanceScore A a q ≤
      I.bid a q + I.bid a q * (Real.exp ε - 1) := by
  let s := I.pageSpentFraction A a
  let δ := I.bid a q / I.budget a
  have hBpos : 0 < I.budget a := hbudget a
  have hδ_nonneg : 0 ≤ δ := by
    exact div_nonneg (hbid a q) hBpos.le
  have hδ_le : δ ≤ ε := by
    exact (div_le_iff₀ hBpos).2 (hsmall a q)
  have hafter :
      I.pageSpentFraction (pageAssignQuery A q selected) a = s + δ := by
    simpa [s, δ] using
      pageSpentFraction_pageAssignQuery_selected
        I A q selected a hunassigned ha hBpos.ne'
  have hinc_eq :
      msvvRatio *
          (I.budget a *
            (I.pageMsvvNormalizedAlphaFromAssignment
                (pageAssignQuery A q selected) a -
              I.pageMsvvNormalizedAlphaFromAssignment A a)) =
        I.budget a * Real.exp (s - 1) * (Real.exp δ - 1) := by
    simp [pageMsvvNormalizedAlphaFromAssignment, hafter, s, δ,
      msvvRatio_mul_budget_normalizedDualAlpha_increment_eq]
  have hfactor :
      Real.exp δ - 1 ≤ δ * Real.exp ε :=
    exp_sub_one_le_mul_exp_of_mem_interval hδ_nonneg hδ_le
  have hleft_nonneg :
      0 ≤ I.budget a * Real.exp (s - 1) :=
    mul_nonneg hBpos.le (Real.exp_nonneg (s - 1))
  have hBδ : I.budget a * δ = I.bid a q := by
    change I.budget a * (I.bid a q / I.budget a) = I.bid a q
    calc
      I.budget a * (I.bid a q / I.budget a) =
          I.bid a q * I.budget a / I.budget a := by
          ring
      _ = I.bid a q := by
          exact mul_div_cancel_right₀ (I.bid a q) hBpos.ne'
  have hinc_le :
      msvvRatio *
          (I.budget a *
            (I.pageMsvvNormalizedAlphaFromAssignment
                (pageAssignQuery A q selected) a -
              I.pageMsvvNormalizedAlphaFromAssignment A a)) ≤
        I.bid a q * Real.exp (s - 1) * Real.exp ε := by
    calc
      msvvRatio *
          (I.budget a *
            (I.pageMsvvNormalizedAlphaFromAssignment
                (pageAssignQuery A q selected) a -
              I.pageMsvvNormalizedAlphaFromAssignment A a)) =
          I.budget a * Real.exp (s - 1) * (Real.exp δ - 1) := hinc_eq
      _ ≤ I.budget a * Real.exp (s - 1) * (δ * Real.exp ε) :=
          mul_le_mul_of_nonneg_left hfactor hleft_nonneg
      _ = I.bid a q * Real.exp (s - 1) * Real.exp ε := by
          rw [show I.budget a * Real.exp (s - 1) * (δ * Real.exp ε) =
              (I.budget a * δ) * Real.exp (s - 1) * Real.exp ε by ring]
          rw [hBδ]
  have hbalance :
      I.pageBalanceScore A a q =
        I.bid a q * (1 - Real.exp (s - 1)) := by
    simp [pageBalanceScore, balanceDiscount, pageSpentFraction, s]
  have hs_le_one : s ≤ 1 := by
    unfold s pageSpentFraction
    calc
      I.pageSpend A a / I.budget a ≤ I.budget a / I.budget a :=
        div_le_div_of_nonneg_right hAfeasible hBpos.le
      _ = 1 := by
        exact div_self hBpos.ne'
  have hexp_s_le_one : Real.exp (s - 1) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have herr_nonneg : 0 ≤ Real.exp ε - 1 :=
    exp_sub_one_nonneg_of_nonneg hε
  have htail :
      I.bid a q * Real.exp (s - 1) * (Real.exp ε - 1) ≤
        I.bid a q * (Real.exp ε - 1) := by
    have hcoeff_nonneg :
        0 ≤ I.bid a q * (Real.exp ε - 1) :=
      mul_nonneg (hbid a q) herr_nonneg
    calc
      I.bid a q * Real.exp (s - 1) * (Real.exp ε - 1) =
          (I.bid a q * (Real.exp ε - 1)) * Real.exp (s - 1) := by
          ring
      _ ≤ (I.bid a q * (Real.exp ε - 1)) * 1 :=
          mul_le_mul_of_nonneg_left hexp_s_le_one hcoeff_nonneg
      _ = I.bid a q * (Real.exp ε - 1) := by
          ring
  calc
    msvvRatio *
        (I.budget a *
          (I.pageMsvvNormalizedAlphaFromAssignment
              (pageAssignQuery A q selected) a -
            I.pageMsvvNormalizedAlphaFromAssignment A a)) +
        I.pageBalanceScore A a q
        ≤
      I.bid a q * Real.exp (s - 1) * Real.exp ε +
        I.bid a q * (1 - Real.exp (s - 1)) :=
          add_le_add hinc_le (le_of_eq hbalance)
    _ = I.bid a q +
        I.bid a q * Real.exp (s - 1) * (Real.exp ε - 1) := by
          ring
    _ ≤ I.bid a q + I.bid a q * (Real.exp ε - 1) := by
          linarith

theorem pageMsvvNormalizedAlphaBudgetMass_pageAssignQuery_sub_eq_sum_selected
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (q : Query)
    (selected : Finset Advertiser)
    (hunassigned : A q = ∅) :
    I.pageMsvvNormalizedAlphaBudgetMass (pageAssignQuery A q selected) -
        I.pageMsvvNormalizedAlphaBudgetMass A =
      ∑ a ∈ selected,
        I.budget a *
          (I.pageMsvvNormalizedAlphaFromAssignment
              (pageAssignQuery A q selected) a -
            I.pageMsvvNormalizedAlphaFromAssignment A a) := by
  classical
  let f : Advertiser → ℝ := fun a =>
    I.budget a *
      (I.pageMsvvNormalizedAlphaFromAssignment
          (pageAssignQuery A q selected) a -
        I.pageMsvvNormalizedAlphaFromAssignment A a)
  have hdiff :
      I.pageMsvvNormalizedAlphaBudgetMass (pageAssignQuery A q selected) -
          I.pageMsvvNormalizedAlphaBudgetMass A =
        ∑ a : Advertiser, f a := by
    unfold pageMsvvNormalizedAlphaBudgetMass f
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  have hrestrict :
      (∑ a : Advertiser, f a) = ∑ a ∈ selected, f a := by
    calc
      (∑ a : Advertiser, f a) =
          ∑ a : Advertiser, if a ∈ selected then f a else 0 := by
          apply Finset.sum_congr rfl
          intro a _ha
          by_cases ha : a ∈ selected
          · simp [ha]
          · have hfrac :
                I.pageSpentFraction (pageAssignQuery A q selected) a =
                  I.pageSpentFraction A a :=
              pageSpentFraction_pageAssignQuery_not_selected
                I A q selected a hunassigned ha
            have hzero : f a = 0 := by
              simp [f, pageMsvvNormalizedAlphaFromAssignment, hfrac]
            simp [ha, hzero]
      _ = ∑ a ∈ selected, f a := by
          simp
  simpa [f] using hdiff.trans hrestrict

theorem msvvRatio_mul_pageAlphaMass_increment_add_balanceScoreSum_le_bidSum_add_alphaError
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (A : PageAssignment Advertiser Query) (q : Query)
    (selected : Finset Advertiser)
    (hunassigned : A q = ∅)
    (hAfeasible : ∀ a, I.pageSpend A a ≤ I.budget a)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio *
        (I.pageMsvvNormalizedAlphaBudgetMass
            (pageAssignQuery A q selected) -
          I.pageMsvvNormalizedAlphaBudgetMass A) +
        (∑ a ∈ selected, I.pageBalanceScore A a q) ≤
      (∑ a ∈ selected, I.bid a q) +
        ∑ a ∈ selected, I.bid a q * (Real.exp ε - 1) := by
  rw [pageMsvvNormalizedAlphaBudgetMass_pageAssignQuery_sub_eq_sum_selected
    I A q selected hunassigned]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  have hsum :
      (∑ x ∈ selected,
          (msvvRatio *
              (I.budget x *
                (I.pageMsvvNormalizedAlphaFromAssignment
                    (pageAssignQuery A q selected) x -
                  I.pageMsvvNormalizedAlphaFromAssignment A x)) +
            I.pageBalanceScore A x q)) ≤
        ∑ x ∈ selected, (I.bid x q + I.bid x q * (Real.exp ε - 1)) := by
    exact Finset.sum_le_sum fun a ha =>
      msvvRatio_mul_pageNormalizedAlpha_increment_add_balanceScore_le_bid_add_alphaError
        I hbid hbudget A q selected a hunassigned (hAfeasible a)
        hε hsmall ha
  have hright :
      (∑ x ∈ selected, (I.bid x q + I.bid x q * (Real.exp ε - 1))) =
        (∑ a ∈ selected, I.bid a q) +
          ∑ a ∈ selected, I.bid a q * (Real.exp ε - 1) := by
    rw [Finset.sum_add_distrib]
  exact hsum.trans_eq hright

/-! ## Page-level top-`n_q` Balance rule and histories -/

/-- The finite set of advertisers that can still accept page `q`. -/
noncomputable def pageFeasibleAdvertisers
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (q : Query) :
    Finset Advertiser := by
  classical
  exact Finset.univ.filter fun a => I.PageCanAssign A q a

@[simp]
theorem mem_pageFeasibleAdvertisers
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (q : Query) (a : Advertiser) :
    a ∈ I.pageFeasibleAdvertisers A q ↔ I.PageCanAssign A q a := by
  classical
  simp [pageFeasibleAdvertisers]

/--
The source-shaped page selector: choose a distinct set of up to `slots q`
feasible advertisers maximizing the total current Balance score.
-/
noncomputable def pageTopBalanceBidders
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (A : PageAssignment Advertiser Query) (q : Query) :
    Finset Advertiser :=
  topKBySum (I.pageFeasibleAdvertisers A q)
    (fun a => I.pageBalanceScore A a q) (slots q)

/-- Page-level batch choice rules return a finite set of advertisers. -/
abbrev PageBatchRule (Advertiser Query : Type*) :=
  PageAssignment Advertiser Query → Query → Finset Advertiser

/-- Feasibility for page-level batch rules. -/
def PageBatchRuleFeasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query) : Prop :=
  ∀ A q,
    (rule A q).card ≤ slots q ∧
      ∀ a, a ∈ rule A q → I.PageCanAssign A q a

/-- The page-level top-`n_q` Balance rule. -/
noncomputable def pageTopBalanceRule
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) : PageBatchRule Advertiser Query :=
  fun A q => I.pageTopBalanceBidders slots A q

theorem pageTopBalanceBidders_subset_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (A : PageAssignment Advertiser Query) (q : Query) :
    I.pageTopBalanceBidders slots A q ⊆ I.pageFeasibleAdvertisers A q :=
  topKBySum_subset (I.pageFeasibleAdvertisers A q)
    (fun a => I.pageBalanceScore A a q) (slots q)

theorem pageTopBalanceBidders_card_le
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (A : PageAssignment Advertiser Query) (q : Query) :
    (I.pageTopBalanceBidders slots A q).card ≤ slots q :=
  topKBySum_card_le (I.pageFeasibleAdvertisers A q)
    (fun a => I.pageBalanceScore A a q) (slots q)

theorem pageTopBalanceBidders_selected_canAssign
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (A : PageAssignment Advertiser Query) (q : Query)
    {a : Advertiser}
    (ha : a ∈ I.pageTopBalanceBidders slots A q) :
    I.PageCanAssign A q a := by
  exact (mem_pageFeasibleAdvertisers I A q a).1
    (pageTopBalanceBidders_subset_feasible I slots A q ha)

theorem pageTopBalanceRule_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ) :
    I.PageBatchRuleFeasible slots (I.pageTopBalanceRule slots) := by
  intro A q
  constructor
  · exact pageTopBalanceBidders_card_le I slots A q
  · intro a ha
    exact pageTopBalanceBidders_selected_canAssign I slots A q ha

theorem pageTopBalanceBidders_sum_ge_of_subset_feasible_card_le
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (A : PageAssignment Advertiser Query) (q : Query)
    (t : Finset Advertiser)
    (htfeasible : t ⊆ I.pageFeasibleAdvertisers A q)
    (htcard : t.card ≤ slots q) :
    (∑ a ∈ t, I.pageBalanceScore A a q) ≤
      ∑ a ∈ I.pageTopBalanceBidders slots A q, I.pageBalanceScore A a q :=
  sum_le_topKBySum_of_subset_card_le
    (I.pageFeasibleAdvertisers A q) t
    (fun a => I.pageBalanceScore A a q) (slots q)
    htfeasible htcard

/-- State carried by a page-level online algorithm. -/
structure PageHistoryState (Advertiser Query : Type*) where
  assignment : PageAssignment Advertiser Query
  seen : Finset Query

/-- Initial page-level online state. -/
def initialPageHistoryState [DecidableEq Query] :
    PageHistoryState Advertiser Query where
  assignment := emptyPageAssignment
  seen := ∅

/-- Page-level state invariant. Unseen pages are still unassigned. -/
def PageStateInvariant
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (S : PageHistoryState Advertiser Query) : Prop :=
  I.PageFeasible slots S.assignment ∧ ∀ q, q ∉ S.seen → S.assignment q = ∅

theorem initialPageHistoryState_invariant
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (hbudget : I.NonnegativeBudgets) :
    I.PageStateInvariant slots
      (initialPageHistoryState : PageHistoryState Advertiser Query) := by
  constructor
  · exact emptyPageAssignment_feasible I slots hbudget
  · intro q _hq
    rfl

/-- One page-level online update. Repeated pages are not reassigned. -/
def stepPageHistoryState
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (_I : AdWordsInstance Advertiser Query)
    (_slots : Query → ℕ)
    (rule : PageBatchRule Advertiser Query)
    (S : PageHistoryState Advertiser Query) (q : Query) :
    PageHistoryState Advertiser Query :=
  if q ∈ S.seen then
    { S with seen := insert q S.seen }
  else
    { assignment := pageAssignQuery S.assignment q (rule S.assignment q)
      seen := insert q S.seen }

theorem stepPageHistoryState_invariant
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (S : PageHistoryState Advertiser Query) (q : Query)
    (hS : I.PageStateInvariant slots S) :
    I.PageStateInvariant slots (stepPageHistoryState I slots rule S q) := by
  classical
  by_cases hseen : q ∈ S.seen
  · simp [stepPageHistoryState, hseen]
    constructor
    · exact hS.1
    · intro q' hq'
      exact hS.2 q' hq'
  · simp [stepPageHistoryState, hseen]
    constructor
    · exact pageFeasible_pageAssignQuery_of_canAssign I slots S.assignment q
        (rule S.assignment q) hS.1 (hS.2 q hseen)
        (hrule S.assignment q).1 (hrule S.assignment q).2
    · intro q' hq'
      by_cases hqeq : q' = q
      · subst q'
        exact False.elim (hq' (by simp))
      · have hnotseen : q' ∉ S.seen := by
          intro hin
          exact hq' (by simp [hin])
        simpa [pageAssignQuery, hqeq] using hS.2 q' hnotseen

/-- Run a page-level rule from an arbitrary state. -/
def runPageHistoryStateFrom
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query) :
    PageHistoryState Advertiser Query → List Query → PageHistoryState Advertiser Query
  | S, [] => S
  | S, q :: qs =>
      runPageHistoryStateFrom I slots rule
        (stepPageHistoryState I slots rule S q) qs

/-- Run a page-level rule from the empty state. -/
def runPageHistoryState
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (history : List Query) :
    PageHistoryState Advertiser Query :=
  runPageHistoryStateFrom I slots rule initialPageHistoryState history

/-- The final page assignment returned by a page-level rule. -/
def runPageAssignment
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (history : List Query) :
    PageAssignment Advertiser Query :=
  (runPageHistoryState I slots rule history).assignment

theorem runPageHistoryStateFrom_invariant
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (history : List Query) (S : PageHistoryState Advertiser Query)
    (hS : I.PageStateInvariant slots S) :
    I.PageStateInvariant slots
      (runPageHistoryStateFrom I slots rule S history) := by
  induction history generalizing S with
  | nil =>
      exact hS
  | cons q qs ih =>
      exact ih (stepPageHistoryState I slots rule S q)
        (stepPageHistoryState_invariant I slots rule hrule S q hS)

theorem runPageAssignment_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (history : List Query) (hbudget : I.NonnegativeBudgets) :
    I.PageFeasible slots (I.runPageAssignment slots rule history) := by
  exact
    (runPageHistoryStateFrom_invariant I slots rule hrule history
      (initialPageHistoryState : PageHistoryState Advertiser Query)
      (initialPageHistoryState_invariant I slots hbudget)).1

theorem pageRevenue_stepPageHistoryState_eq_add
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (S : PageHistoryState Advertiser Query) (q : Query)
    (hS : I.PageStateInvariant slots S) :
    I.pageRevenue (stepPageHistoryState I slots rule S q).assignment =
      I.pageRevenue S.assignment +
        if q ∈ S.seen then
          0
        else
          ∑ a ∈ rule S.assignment q, I.bid a q := by
  classical
  by_cases hseen : q ∈ S.seen
  · simp [stepPageHistoryState, hseen]
  · simp [stepPageHistoryState, hseen]
    exact pageRevenue_pageAssignQuery_of_unassigned
      I S.assignment q (rule S.assignment q) (hS.2 q hseen)

/-! ## Page-level history accounting -/

@[simp]
theorem pageMsvvNormalizedAlphaBudgetMass_emptyPageAssignment
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) :
    I.pageMsvvNormalizedAlphaBudgetMass
        (emptyPageAssignment : PageAssignment Advertiser Query) = 0 := by
  classical
  unfold pageMsvvNormalizedAlphaBudgetMass pageMsvvNormalizedAlphaFromAssignment
    pageSpentFraction msvvNormalizedDualAlpha
  simp [pageSpend_empty]

/-- Revenue increment generated by one page-level online step. -/
noncomputable def pageStepRevenueCharge
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (_I : AdWordsInstance Advertiser Query)
    (rule : PageBatchRule Advertiser Query)
    (S : PageHistoryState Advertiser Query) (q : Query) : ℝ :=
  if q ∈ S.seen then
    0
  else
    ∑ a ∈ rule S.assignment q, _I.bid a q

/-- The list-sum of page-level Balance charges generated by an online run. -/
noncomputable def pageHistoryBalanceChargeFrom
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query) :
    PageHistoryState Advertiser Query → List Query → ℝ
  | _S, [] => 0
  | S, q :: qs =>
      let stepCharge :=
        if q ∈ S.seen then
          0
        else
          ∑ a ∈ rule S.assignment q, I.pageBalanceScore S.assignment a q
      stepCharge +
        pageHistoryBalanceChargeFrom I slots rule
          (stepPageHistoryState I slots rule S q) qs

/-- Sum of online page-level revenue increments over a history list. -/
noncomputable def pageHistoryRevenueChargeFrom
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query) :
    PageHistoryState Advertiser Query → List Query → ℝ
  | _S, [] => 0
  | S, q :: qs =>
      I.pageStepRevenueCharge rule S q +
        pageHistoryRevenueChargeFrom I slots rule
          (stepPageHistoryState I slots rule S q) qs

/-- Slot-weighted alpha discretization error for one page. -/
noncomputable def pageMaxBidAlphaError
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ)
    (ε : ℝ) (q : Query) : ℝ :=
  (slots q : ℝ) * I.maxBidForQuery q * (Real.exp ε - 1)

/-- Slot-weighted exhausted-advertiser query-dual error for one page. -/
noncomputable def pageMaxBidError
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ)
    (ε : ℝ) (q : Query) : ℝ :=
  (slots q : ℝ) * I.maxBidForQuery q * (1 - Real.exp (-ε))

/-- Sum of slot-weighted alpha discretization errors over a page history. -/
noncomputable def pageHistoryMaxBidAlphaErrorSum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ)
    (ε : ℝ) : List Query → ℝ
  | [] => 0
  | q :: qs =>
      I.pageMaxBidAlphaError slots ε q +
        pageHistoryMaxBidAlphaErrorSum I slots ε qs

/-- Sum of slot-weighted exhausted-advertiser query-dual errors over a page history. -/
noncomputable def pageHistoryMaxBidErrorSum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ)
    (ε : ℝ) : List Query → ℝ
  | [] => 0
  | q :: qs =>
      I.pageMaxBidError slots ε q +
        pageHistoryMaxBidErrorSum I slots ε qs

/-- Sum of slot-weighted maximum bids over a page history. -/
noncomputable def pageHistoryMaxBidSum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ) :
    List Query → ℝ
  | [] => 0
  | q :: qs =>
      (slots q : ℝ) * I.maxBidForQuery q +
        pageHistoryMaxBidSum I slots qs

/-- Combined explicit finite small-bids error for the page-level MSVV proof. -/
noncomputable def pageHistoryMsvvSmallBidsErrorSum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ)
    (ε : ℝ) (history : List Query) : ℝ :=
  I.pageHistoryMaxBidAlphaErrorSum slots ε history +
    I.pageHistoryMaxBidErrorSum slots ε history

theorem pageSelectedBidAlphaError_le_pageMaxBidAlphaError
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (selected : Finset Advertiser) (q : Query)
    (hcard : selected.card ≤ slots q) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (∑ a ∈ selected, I.bid a q * (Real.exp ε - 1)) ≤
      I.pageMaxBidAlphaError slots ε q := by
  classical
  have herr_nonneg : 0 ≤ Real.exp ε - 1 :=
    exp_sub_one_nonneg_of_nonneg hε
  have hterm :
      (∑ a ∈ selected, I.bid a q * (Real.exp ε - 1)) ≤
        ∑ a ∈ selected, I.maxBidForQuery q * (Real.exp ε - 1) :=
    Finset.sum_le_sum fun a _ha =>
      mul_le_mul_of_nonneg_right (bid_le_maxBidForQuery I a q) herr_nonneg
  have hsum_const :
      (∑ a ∈ selected, I.maxBidForQuery q * (Real.exp ε - 1)) =
        (selected.card : ℝ) * (I.maxBidForQuery q * (Real.exp ε - 1)) := by
    simp
  have hcard_real : (selected.card : ℝ) ≤ slots q := by
    exact_mod_cast hcard
  have hfactor_nonneg :
      0 ≤ I.maxBidForQuery q * (Real.exp ε - 1) :=
    mul_nonneg (maxBidForQuery_nonneg I q) herr_nonneg
  have hcard_mul :
      (selected.card : ℝ) * (I.maxBidForQuery q * (Real.exp ε - 1)) ≤
        (slots q : ℝ) * (I.maxBidForQuery q * (Real.exp ε - 1)) :=
    mul_le_mul_of_nonneg_right hcard_real hfactor_nonneg
  calc
    (∑ a ∈ selected, I.bid a q * (Real.exp ε - 1)) ≤
        ∑ a ∈ selected, I.maxBidForQuery q * (Real.exp ε - 1) := hterm
    _ = (selected.card : ℝ) * (I.maxBidForQuery q * (Real.exp ε - 1)) :=
        hsum_const
    _ ≤ (slots q : ℝ) * (I.maxBidForQuery q * (Real.exp ε - 1)) :=
        hcard_mul
    _ = I.pageMaxBidAlphaError slots ε q := by
        simp [pageMaxBidAlphaError, mul_assoc]

theorem msvvRatio_mul_pageAlphaMass_step_increment_add_balanceCharge_le_stepRevenueCharge_add_alphaError
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (S : PageHistoryState Advertiser Query) (q : Query)
    (hS : I.PageStateInvariant slots S)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio *
        (I.pageMsvvNormalizedAlphaBudgetMass
            (stepPageHistoryState I slots rule S q).assignment -
          I.pageMsvvNormalizedAlphaBudgetMass S.assignment) +
        (if q ∈ S.seen then
          0
        else
          ∑ a ∈ rule S.assignment q, I.pageBalanceScore S.assignment a q) ≤
      I.pageStepRevenueCharge rule S q +
        I.pageMaxBidAlphaError slots ε q := by
  classical
  have herr_nonneg : 0 ≤ Real.exp ε - 1 :=
    exp_sub_one_nonneg_of_nonneg hε
  have hmaxerr_nonneg :
      0 ≤ I.pageMaxBidAlphaError slots ε q := by
    unfold pageMaxBidAlphaError
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg (slots q)) (maxBidForQuery_nonneg I q))
      herr_nonneg
  by_cases hseen : q ∈ S.seen
  · simpa [stepPageHistoryState, pageStepRevenueCharge, hseen] using hmaxerr_nonneg
  · let selected := rule S.assignment q
    have hunassigned : S.assignment q = ∅ := hS.2 q hseen
    have hlocal :=
      msvvRatio_mul_pageAlphaMass_increment_add_balanceScoreSum_le_bidSum_add_alphaError
        I hbid hbudget S.assignment q selected hunassigned hS.1.1 hε hsmall
    have hbiderr_le :
        (∑ a ∈ selected, I.bid a q * (Real.exp ε - 1)) ≤
          I.pageMaxBidAlphaError slots ε q :=
      pageSelectedBidAlphaError_le_pageMaxBidAlphaError
        I slots selected q (hrule S.assignment q).1 hε
    have hlocal' :
        msvvRatio *
            (I.pageMsvvNormalizedAlphaBudgetMass
                (pageAssignQuery S.assignment q selected) -
              I.pageMsvvNormalizedAlphaBudgetMass S.assignment) +
            (∑ a ∈ selected, I.pageBalanceScore S.assignment a q) ≤
          (∑ a ∈ selected, I.bid a q) +
            I.pageMaxBidAlphaError slots ε q := by
      linarith
    simpa [stepPageHistoryState, pageStepRevenueCharge, hseen, selected]
      using hlocal'

theorem pageRevenue_runPageHistoryStateFrom_eq_revenue_add_pageHistoryRevenueChargeFrom
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (history : List Query) (S : PageHistoryState Advertiser Query)
    (hS : I.PageStateInvariant slots S) :
    I.pageRevenue (runPageHistoryStateFrom I slots rule S history).assignment =
      I.pageRevenue S.assignment +
        I.pageHistoryRevenueChargeFrom slots rule S history := by
  induction history generalizing S with
  | nil =>
      simp [runPageHistoryStateFrom, pageHistoryRevenueChargeFrom]
  | cons q qs ih =>
      let S' := stepPageHistoryState I slots rule S q
      have hS' : I.PageStateInvariant slots S' :=
        stepPageHistoryState_invariant I slots rule hrule S q hS
      have hstep :
          I.pageRevenue S'.assignment =
            I.pageRevenue S.assignment + I.pageStepRevenueCharge rule S q := by
        simpa [S'] using
          pageRevenue_stepPageHistoryState_eq_add I slots rule S q hS
      have htail := ih S' hS'
      calc
        I.pageRevenue (runPageHistoryStateFrom I slots rule S (q :: qs)).assignment =
            I.pageRevenue (runPageHistoryStateFrom I slots rule S' qs).assignment := by
          simp [runPageHistoryStateFrom, S']
        _ = I.pageRevenue S'.assignment +
              I.pageHistoryRevenueChargeFrom slots rule S' qs := htail
        _ = I.pageRevenue S.assignment +
              I.pageHistoryRevenueChargeFrom slots rule S (q :: qs) := by
          simp [pageHistoryRevenueChargeFrom, S', hstep]
          ring

theorem msvvRatio_mul_pageAlphaMass_increment_runPageHistoryStateFrom_add_pageHistoryBalanceCharge_le_pageHistoryRevenueCharge_add_pageHistoryMaxBidAlphaErrorSum
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (history : List Query) (S : PageHistoryState Advertiser Query)
    (hS : I.PageStateInvariant slots S)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio *
        (I.pageMsvvNormalizedAlphaBudgetMass
            (runPageHistoryStateFrom I slots rule S history).assignment -
          I.pageMsvvNormalizedAlphaBudgetMass S.assignment) +
        I.pageHistoryBalanceChargeFrom slots rule S history ≤
      I.pageHistoryRevenueChargeFrom slots rule S history +
        I.pageHistoryMaxBidAlphaErrorSum slots ε history := by
  induction history generalizing S with
  | nil =>
      simp [runPageHistoryStateFrom, pageHistoryBalanceChargeFrom,
        pageHistoryRevenueChargeFrom, pageHistoryMaxBidAlphaErrorSum]
  | cons q qs ih =>
      let S' := stepPageHistoryState I slots rule S q
      have hS' : I.PageStateInvariant slots S' :=
        stepPageHistoryState_invariant I slots rule hrule S q hS
      have hhead :=
        msvvRatio_mul_pageAlphaMass_step_increment_add_balanceCharge_le_stepRevenueCharge_add_alphaError
          I hbid hbudget slots rule hrule S q hS hε hsmall
      have htail := ih S' hS'
      calc
        msvvRatio *
            (I.pageMsvvNormalizedAlphaBudgetMass
                (runPageHistoryStateFrom I slots rule S (q :: qs)).assignment -
              I.pageMsvvNormalizedAlphaBudgetMass S.assignment) +
            I.pageHistoryBalanceChargeFrom slots rule S (q :: qs)
            =
          (msvvRatio *
              (I.pageMsvvNormalizedAlphaBudgetMass S'.assignment -
                I.pageMsvvNormalizedAlphaBudgetMass S.assignment) +
              (if q ∈ S.seen then
                0
              else
                ∑ a ∈ rule S.assignment q,
                  I.pageBalanceScore S.assignment a q)) +
            (msvvRatio *
                (I.pageMsvvNormalizedAlphaBudgetMass
                    (runPageHistoryStateFrom I slots rule S' qs).assignment -
                  I.pageMsvvNormalizedAlphaBudgetMass S'.assignment) +
                I.pageHistoryBalanceChargeFrom slots rule S' qs) := by
                simp [runPageHistoryStateFrom, pageHistoryBalanceChargeFrom, S']
                ring
        _ ≤
          (I.pageStepRevenueCharge rule S q +
              I.pageMaxBidAlphaError slots ε q) +
            (I.pageHistoryRevenueChargeFrom slots rule S' qs +
              I.pageHistoryMaxBidAlphaErrorSum slots ε qs) :=
                add_le_add hhead htail
        _ =
          I.pageHistoryRevenueChargeFrom slots rule S (q :: qs) +
            I.pageHistoryMaxBidAlphaErrorSum slots ε (q :: qs) := by
              simp [pageHistoryRevenueChargeFrom,
                pageHistoryMaxBidAlphaErrorSum, S']
              ring

theorem msvvRatio_mul_pageAlphaMass_balanceRun_add_pageHistoryBalanceCharge_le_revenue_add_pageHistoryMaxBidAlphaErrorSum
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ) (history : List Query)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio *
        I.pageMsvvNormalizedAlphaBudgetMass
          (I.runPageAssignment slots (I.pageTopBalanceRule slots) history) +
        I.pageHistoryBalanceChargeFrom slots (I.pageTopBalanceRule slots)
          initialPageHistoryState history ≤
      I.pageRevenue
          (I.runPageAssignment slots (I.pageTopBalanceRule slots) history) +
        I.pageHistoryMaxBidAlphaErrorSum slots ε history := by
  have hnonneg : I.NonnegativeBudgets := fun a => (hbudget a).le
  have hS :
      I.PageStateInvariant slots
        (initialPageHistoryState : PageHistoryState Advertiser Query) :=
    initialPageHistoryState_invariant I slots hnonneg
  have hhist :=
    msvvRatio_mul_pageAlphaMass_increment_runPageHistoryStateFrom_add_pageHistoryBalanceCharge_le_pageHistoryRevenueCharge_add_pageHistoryMaxBidAlphaErrorSum
      I hbid hbudget slots (I.pageTopBalanceRule slots)
      (pageTopBalanceRule_feasible I slots) history
      (initialPageHistoryState : PageHistoryState Advertiser Query)
      hS hε hsmall
  have hhist' :
      msvvRatio *
          (I.pageMsvvNormalizedAlphaBudgetMass
              (I.runPageAssignment slots (I.pageTopBalanceRule slots) history) -
            I.pageMsvvNormalizedAlphaBudgetMass
              (emptyPageAssignment : PageAssignment Advertiser Query)) +
          I.pageHistoryBalanceChargeFrom slots (I.pageTopBalanceRule slots)
            initialPageHistoryState history ≤
        I.pageHistoryRevenueChargeFrom slots (I.pageTopBalanceRule slots)
            initialPageHistoryState history +
          I.pageHistoryMaxBidAlphaErrorSum slots ε history := by
    simpa [runPageAssignment, runPageHistoryState, initialPageHistoryState]
      using hhist
  rw [pageMsvvNormalizedAlphaBudgetMass_emptyPageAssignment I] at hhist'
  have hrev :
      I.pageRevenue
          (I.runPageAssignment slots (I.pageTopBalanceRule slots) history) =
        I.pageHistoryRevenueChargeFrom slots (I.pageTopBalanceRule slots)
          initialPageHistoryState history := by
    have h :=
      pageRevenue_runPageHistoryStateFrom_eq_revenue_add_pageHistoryRevenueChargeFrom
        I slots (I.pageTopBalanceRule slots)
        (pageTopBalanceRule_feasible I slots) history
        (initialPageHistoryState : PageHistoryState Advertiser Query) hS
    simpa [runPageAssignment, runPageHistoryState, initialPageHistoryState,
      pageRevenue_empty] using h
  rw [hrev]
  simpa using hhist'

/-! ## Page-level beta accounting -/

theorem pageSpentFraction_nonneg
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (A : PageAssignment Advertiser Query) (a : Advertiser)
    (hbudget : 0 < I.budget a) :
    0 ≤ I.pageSpentFraction A a := by
  unfold pageSpentFraction
  exact div_nonneg (pageSpend_nonneg I hbid A a) hbudget.le

theorem pageSpentFraction_le_one_of_feasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (A : PageAssignment Advertiser Query)
    (a : Advertiser)
    (hbudget : 0 < I.budget a)
    (hfeasible : I.PageFeasible slots A) :
    I.pageSpentFraction A a ≤ 1 := by
  unfold pageSpentFraction
  calc
    I.pageSpend A a / I.budget a ≤ I.budget a / I.budget a :=
      div_le_div_of_nonneg_right (hfeasible.1 a) hbudget.le
    _ = 1 := by
      exact div_self hbudget.ne'

theorem pageMsvvNormalizedAlphaFromAssignment_nonneg
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (A : PageAssignment Advertiser Query) :
    ∀ a, 0 ≤ I.pageMsvvNormalizedAlphaFromAssignment A a := by
  intro a
  exact msvvNormalizedDualAlpha_nonneg_of_nonneg
    (pageSpentFraction_nonneg I hbid A a (hbudget a))

theorem pageBalanceScore_nonneg_of_feasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ)
    (A : PageAssignment Advertiser Query) (a : Advertiser) (q : Query)
    (hfeasible : I.PageFeasible slots A) :
    0 ≤ I.pageBalanceScore A a q := by
  unfold pageBalanceScore
  exact mul_nonneg (hbid a q)
    (balanceDiscount_nonneg_of_le_one
      (pageSpentFraction_le_one_of_feasible
        I slots A a (hbudget a) hfeasible))

theorem msvvRatio_mul_slackScore_pageMsvvNormalizedAlphaFromAssignment_eq_pageBalanceScore
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (a : Advertiser) (q : Query) :
    msvvRatio *
        I.slackScore (I.pageMsvvNormalizedAlphaFromAssignment A) a q =
      I.pageBalanceScore A a q := by
  unfold msvvRatio slackScore pageBalanceScore balanceDiscount
    pageMsvvNormalizedAlphaFromAssignment msvvNormalizedDualAlpha pageSpentFraction
  have hE : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  have hden : Real.exp 1 - 1 ≠ 0 := ne_of_gt exp_one_sub_one_pos
  rw [show Real.exp (I.pageSpend A a / I.budget a - 1) =
      Real.exp (I.pageSpend A a / I.budget a) / Real.exp 1 by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg]
    ring]
  field_simp [hE, hden]
  ring

theorem pageSpend_le_pageSpend_pageAssignQuery_of_unassigned
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (A : PageAssignment Advertiser Query) (q : Query)
    (selected : Finset Advertiser) (a : Advertiser)
    (hunassigned : A q = ∅) :
    I.pageSpend A a ≤ I.pageSpend (pageAssignQuery A q selected) a := by
  rw [pageSpend_pageAssignQuery_of_unassigned I A q selected a hunassigned]
  by_cases ha : a ∈ selected
  · simp [ha, hbid a q]
  · simp [ha]

theorem pageSpend_le_stepPageHistoryState_pageSpend
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (S : PageHistoryState Advertiser Query) (q : Query)
    (hS : I.PageStateInvariant slots S) (a : Advertiser) :
    I.pageSpend S.assignment a ≤
      I.pageSpend (stepPageHistoryState I slots rule S q).assignment a := by
  classical
  by_cases hseen : q ∈ S.seen
  · simp [stepPageHistoryState, hseen]
  · simp [stepPageHistoryState, hseen]
    exact pageSpend_le_pageSpend_pageAssignQuery_of_unassigned
      I hbid S.assignment q (rule S.assignment q) a (hS.2 q hseen)

theorem pageSpend_le_runPageHistoryStateFrom_pageSpend
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (history : List Query) (S : PageHistoryState Advertiser Query)
    (hS : I.PageStateInvariant slots S) (a : Advertiser) :
    I.pageSpend S.assignment a ≤
      I.pageSpend
        (runPageHistoryStateFrom I slots rule S history).assignment a := by
  induction history generalizing S with
  | nil =>
      simp [runPageHistoryStateFrom]
  | cons q qs ih =>
      let S' := stepPageHistoryState I slots rule S q
      have hstep :
          I.pageSpend S.assignment a ≤ I.pageSpend S'.assignment a :=
        pageSpend_le_stepPageHistoryState_pageSpend I hbid slots rule S q hS a
      have hS' : I.PageStateInvariant slots S' :=
        stepPageHistoryState_invariant I slots rule hrule S q hS
      have htail :
          I.pageSpend S'.assignment a ≤
            I.pageSpend
              (runPageHistoryStateFrom I slots rule S' qs).assignment a :=
        ih S' hS'
      exact hstep.trans (by simpa [runPageHistoryStateFrom, S'] using htail)

theorem pageSpentFraction_le_runPageHistoryStateFrom_pageSpentFraction
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (history : List Query) (S : PageHistoryState Advertiser Query)
    (hS : I.PageStateInvariant slots S) (a : Advertiser) :
    I.pageSpentFraction S.assignment a ≤
      I.pageSpentFraction
        (runPageHistoryStateFrom I slots rule S history).assignment a := by
  unfold pageSpentFraction
  exact div_le_div_of_nonneg_right
    (pageSpend_le_runPageHistoryStateFrom_pageSpend
      I hbid slots rule hrule history S hS a)
    (hbudget a).le

theorem pageMsvvNormalizedAlphaFromAssignment_le_runPageHistoryStateFrom
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (history : List Query) (S : PageHistoryState Advertiser Query)
    (hS : I.PageStateInvariant slots S) (a : Advertiser) :
    I.pageMsvvNormalizedAlphaFromAssignment S.assignment a ≤
      I.pageMsvvNormalizedAlphaFromAssignment
        (runPageHistoryStateFrom I slots rule S history).assignment a := by
  unfold pageMsvvNormalizedAlphaFromAssignment
  exact msvvNormalizedDualAlpha_mono
    (pageSpentFraction_le_runPageHistoryStateFrom_pageSpentFraction
      I hbid hbudget slots rule hrule history S hS a)

theorem msvvRatio_mul_page_final_normalized_slackScore_le_initial_balanceScore
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (history : List Query) (S : PageHistoryState Advertiser Query)
    (hS : I.PageStateInvariant slots S) (a : Advertiser) (q : Query) :
    msvvRatio *
        I.slackScore
          (I.pageMsvvNormalizedAlphaFromAssignment
            (runPageHistoryStateFrom I slots rule S history).assignment) a q ≤
      I.pageBalanceScore S.assignment a q := by
  have halpha :=
    pageMsvvNormalizedAlphaFromAssignment_le_runPageHistoryStateFrom
      I hbid hbudget slots rule hrule history S hS a
  have hslack :
      I.slackScore
          (I.pageMsvvNormalizedAlphaFromAssignment
            (runPageHistoryStateFrom I slots rule S history).assignment) a q ≤
        I.slackScore (I.pageMsvvNormalizedAlphaFromAssignment S.assignment) a q := by
    unfold slackScore
    have hfactor :
        1 -
            I.pageMsvvNormalizedAlphaFromAssignment
              (runPageHistoryStateFrom I slots rule S history).assignment a ≤
          1 - I.pageMsvvNormalizedAlphaFromAssignment S.assignment a := by
      linarith
    exact mul_le_mul_of_nonneg_left hfactor (hbid a q)
  have hscaled :=
    mul_le_mul_of_nonneg_left hslack msvvRatio_nonneg
  exact hscaled.trans
    (le_of_eq
      (msvvRatio_mul_slackScore_pageMsvvNormalizedAlphaFromAssignment_eq_pageBalanceScore
        I S.assignment a q))

theorem msvvRatio_mul_page_final_normalized_positiveSlackScore_le_initial_balanceScore
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (history : List Query) (S : PageHistoryState Advertiser Query)
    (hS : I.PageStateInvariant slots S) (a : Advertiser) (q : Query) :
    msvvRatio *
        I.positiveSlackScore
          (I.pageMsvvNormalizedAlphaFromAssignment
            (runPageHistoryStateFrom I slots rule S history).assignment) a q ≤
      I.pageBalanceScore S.assignment a q := by
  by_cases hslack :
      0 ≤
        I.slackScore
          (I.pageMsvvNormalizedAlphaFromAssignment
            (runPageHistoryStateFrom I slots rule S history).assignment) a q
  · simpa [positiveSlackScore, hslack] using
      msvvRatio_mul_page_final_normalized_slackScore_le_initial_balanceScore
        I hbid hbudget slots rule hrule history S hS a q
  · have hbal_nonneg :
        0 ≤ I.pageBalanceScore S.assignment a q :=
      pageBalanceScore_nonneg_of_feasible
        I hbid hbudget slots S.assignment a q hS.1
    have hpos :
        I.positiveSlackScore
          (I.pageMsvvNormalizedAlphaFromAssignment
            (runPageHistoryStateFrom I slots rule S history).assignment) a q = 0 := by
      simp [positiveSlackScore, le_of_not_ge hslack]
    simp [hpos, hbal_nonneg]

theorem pageSpentFraction_gt_one_sub_epsilon_of_not_pageCanAssign
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : PageAssignment Advertiser Query) (a : Advertiser) (q : Query)
    {ε : ℝ}
    (hbudget : 0 < I.budget a)
    (hsmall : I.SmallBids ε)
    (hnot : ¬ I.PageCanAssign A q a) :
    1 - ε < I.pageSpentFraction A a := by
  unfold PageCanAssign at hnot
  have hlt : I.budget a < I.pageSpend A a + I.bid a q :=
    lt_of_not_ge hnot
  have hbidle : I.bid a q ≤ ε * I.budget a := hsmall a q
  have hlt' : I.budget a < I.pageSpend A a + ε * I.budget a :=
    lt_of_lt_of_le hlt (add_le_add_right hbidle (I.pageSpend A a))
  have hmul : (1 - ε) * I.budget a < I.pageSpend A a := by
    nlinarith
  have hdiv :=
    div_lt_div_of_pos_right hmul hbudget
  have hleft :
      ((1 - ε) * I.budget a) / I.budget a = 1 - ε := by
    exact mul_div_cancel_right₀ _ hbudget.ne'
  simpa [pageSpentFraction, hleft] using hdiv

theorem final_pageMsvvNormalizedAlphaFromAssignment_ge_one_sub_epsilon_of_not_pageCanAssign
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (history : List Query) (S : PageHistoryState Advertiser Query)
    (hS : I.PageStateInvariant slots S) {ε : ℝ}
    (hsmall : I.SmallBids ε) (a : Advertiser) (q : Query)
    (hnot : ¬ I.PageCanAssign S.assignment q a) :
    msvvNormalizedDualAlpha (1 - ε) ≤
      I.pageMsvvNormalizedAlphaFromAssignment
        (runPageHistoryStateFrom I slots rule S history).assignment a := by
  have hblocked :
      1 - ε < I.pageSpentFraction S.assignment a :=
    pageSpentFraction_gt_one_sub_epsilon_of_not_pageCanAssign
      I S.assignment a q (hbudget a) hsmall hnot
  have hrun :
      I.pageSpentFraction S.assignment a ≤
        I.pageSpentFraction
          (runPageHistoryStateFrom I slots rule S history).assignment a :=
    pageSpentFraction_le_runPageHistoryStateFrom_pageSpentFraction
      I hbid hbudget slots rule hrule history S hS a
  have hfrac :
      1 - ε ≤
        I.pageSpentFraction
          (runPageHistoryStateFrom I slots rule S history).assignment a :=
    (le_of_lt hblocked).trans hrun
  unfold pageMsvvNormalizedAlphaFromAssignment
  exact msvvNormalizedDualAlpha_mono hfrac

theorem msvvRatio_mul_page_final_normalized_positiveSlackScore_le_bid_error_of_not_pageCanAssign
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (history : List Query) (S : PageHistoryState Advertiser Query)
    (hS : I.PageStateInvariant slots S) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) (a : Advertiser) (q : Query)
    (hnot : ¬ I.PageCanAssign S.assignment q a) :
    msvvRatio *
        I.positiveSlackScore
          (I.pageMsvvNormalizedAlphaFromAssignment
            (runPageHistoryStateFrom I slots rule S history).assignment) a q ≤
      I.bid a q * (1 - Real.exp (-ε)) := by
  have herr_nonneg :
      0 ≤ I.bid a q * (1 - Real.exp (-ε)) :=
    mul_nonneg (hbid a q) (one_sub_exp_neg_nonneg hε)
  by_cases hslack :
      0 ≤
        I.slackScore
          (I.pageMsvvNormalizedAlphaFromAssignment
            (runPageHistoryStateFrom I slots rule S history).assignment) a q
  · have halpha :=
      final_pageMsvvNormalizedAlphaFromAssignment_ge_one_sub_epsilon_of_not_pageCanAssign
        I hbid hbudget slots rule hrule history S hS hsmall a q hnot
    have hfactor :
        1 -
            I.pageMsvvNormalizedAlphaFromAssignment
              (runPageHistoryStateFrom I slots rule S history).assignment a ≤
          1 - msvvNormalizedDualAlpha (1 - ε) := by
      linarith
    have hslack_le :
        I.slackScore
            (I.pageMsvvNormalizedAlphaFromAssignment
              (runPageHistoryStateFrom I slots rule S history).assignment) a q ≤
          I.bid a q * (1 - msvvNormalizedDualAlpha (1 - ε)) := by
      unfold slackScore
      exact mul_le_mul_of_nonneg_left hfactor (hbid a q)
    have hscaled :=
      mul_le_mul_of_nonneg_left hslack_le msvvRatio_nonneg
    calc
      msvvRatio *
          I.positiveSlackScore
            (I.pageMsvvNormalizedAlphaFromAssignment
              (runPageHistoryStateFrom I slots rule S history).assignment) a q =
        msvvRatio *
          I.slackScore
            (I.pageMsvvNormalizedAlphaFromAssignment
              (runPageHistoryStateFrom I slots rule S history).assignment) a q := by
            simp [positiveSlackScore, hslack]
      _ ≤ msvvRatio * (I.bid a q * (1 - msvvNormalizedDualAlpha (1 - ε))) :=
          hscaled
      _ = I.bid a q * (1 - Real.exp (-ε)) := by
        rw [show msvvRatio *
              (I.bid a q * (1 - msvvNormalizedDualAlpha (1 - ε))) =
            I.bid a q *
              (msvvRatio * (1 - msvvNormalizedDualAlpha (1 - ε))) by ring]
        rw [msvvRatio_mul_one_sub_msvvNormalizedDualAlpha_one_sub]
  · have hpos :
        I.positiveSlackScore
          (I.pageMsvvNormalizedAlphaFromAssignment
            (runPageHistoryStateFrom I slots rule S history).assignment) a q = 0 := by
      simp [positiveSlackScore, le_of_not_ge hslack]
    simp [hpos, herr_nonneg]

theorem pageSelectedBidError_le_pageMaxBidError
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (selected : Finset Advertiser) (q : Query)
    (hcard : selected.card ≤ slots q) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (∑ a ∈ selected, I.bid a q * (1 - Real.exp (-ε))) ≤
      I.pageMaxBidError slots ε q := by
  classical
  have herr_nonneg : 0 ≤ 1 - Real.exp (-ε) :=
    one_sub_exp_neg_nonneg hε
  have hterm :
      (∑ a ∈ selected, I.bid a q * (1 - Real.exp (-ε))) ≤
        ∑ a ∈ selected, I.maxBidForQuery q * (1 - Real.exp (-ε)) :=
    Finset.sum_le_sum fun a _ha =>
      mul_le_mul_of_nonneg_right (bid_le_maxBidForQuery I a q) herr_nonneg
  have hsum_const :
      (∑ a ∈ selected, I.maxBidForQuery q * (1 - Real.exp (-ε))) =
        (selected.card : ℝ) * (I.maxBidForQuery q * (1 - Real.exp (-ε))) := by
    simp
  have hcard_real : (selected.card : ℝ) ≤ slots q := by
    exact_mod_cast hcard
  have hfactor_nonneg :
      0 ≤ I.maxBidForQuery q * (1 - Real.exp (-ε)) :=
    mul_nonneg (maxBidForQuery_nonneg I q) herr_nonneg
  have hcard_mul :
      (selected.card : ℝ) * (I.maxBidForQuery q * (1 - Real.exp (-ε))) ≤
        (slots q : ℝ) * (I.maxBidForQuery q * (1 - Real.exp (-ε))) :=
    mul_le_mul_of_nonneg_right hcard_real hfactor_nonneg
  calc
    (∑ a ∈ selected, I.bid a q * (1 - Real.exp (-ε))) ≤
        ∑ a ∈ selected, I.maxBidForQuery q * (1 - Real.exp (-ε)) := hterm
    _ = (selected.card : ℝ) * (I.maxBidForQuery q * (1 - Real.exp (-ε))) :=
        hsum_const
    _ ≤ (slots q : ℝ) * (I.maxBidForQuery q * (1 - Real.exp (-ε)) ) :=
        hcard_mul
    _ = I.pageMaxBidError slots ε q := by
        simp [pageMaxBidError, mul_assoc]

theorem msvvRatio_mul_pageTopKSlackBeta_normalized_runPageHistoryStateFrom_le_topBalanceScore_add_pageMaxBidError
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ)
    (rule : PageBatchRule Advertiser Query)
    (hrule : I.PageBatchRuleFeasible slots rule)
    (history : List Query)
    (S : PageHistoryState Advertiser Query)
    (hS : I.PageStateInvariant slots S)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε)
    (q : Query) :
    msvvRatio *
        I.pageTopKSlackBeta slots
          (I.pageMsvvNormalizedAlphaFromAssignment
            (runPageHistoryStateFrom I slots rule S history).assignment) q ≤
      (∑ a ∈ I.pageTopBalanceBidders slots S.assignment q,
        I.pageBalanceScore S.assignment a q) +
      I.pageMaxBidError slots ε q := by
  classical
  let alphaF : Advertiser → ℝ :=
    I.pageMsvvNormalizedAlphaFromAssignment
      (runPageHistoryStateFrom I slots rule S history).assignment
  let T : Finset Advertiser :=
    topKBySum (Finset.univ : Finset Advertiser)
      (fun a => I.positiveSlackScore alphaF a q) (slots q)
  let feasibleT : Finset Advertiser :=
    T.filter fun a => I.PageCanAssign S.assignment q a
  let blockedT : Finset Advertiser :=
    T.filter fun a => ¬ I.PageCanAssign S.assignment q a
  have hTcard : T.card ≤ slots q := by
    exact topKBySum_card_le (Finset.univ : Finset Advertiser)
      (fun a => I.positiveSlackScore alphaF a q) (slots q)
  have hfeasibleT_card : feasibleT.card ≤ slots q :=
    (Finset.card_filter_le _ _).trans hTcard
  have hblockedT_card : blockedT.card ≤ slots q :=
    (Finset.card_filter_le _ _).trans hTcard
  have hfeasibleT_subset :
      feasibleT ⊆ I.pageFeasibleAdvertisers S.assignment q := by
    intro a ha
    exact (mem_pageFeasibleAdvertisers I S.assignment q a).2
      ((Finset.mem_filter.mp ha).2)
  have hfeasible_sum_to_balance :
      (∑ a ∈ feasibleT,
          msvvRatio * I.positiveSlackScore alphaF a q) ≤
        ∑ a ∈ feasibleT, I.pageBalanceScore S.assignment a q := by
    exact Finset.sum_le_sum fun a _ha =>
      msvvRatio_mul_page_final_normalized_positiveSlackScore_le_initial_balanceScore
        I hbid hbudget slots rule hrule history S hS a q
  have hfeasible_top :
      (∑ a ∈ feasibleT, I.pageBalanceScore S.assignment a q) ≤
        ∑ a ∈ I.pageTopBalanceBidders slots S.assignment q,
          I.pageBalanceScore S.assignment a q :=
    pageTopBalanceBidders_sum_ge_of_subset_feasible_card_le
      I slots S.assignment q feasibleT hfeasibleT_subset hfeasibleT_card
  have hfeasible_bound :
      (∑ a ∈ feasibleT,
          msvvRatio * I.positiveSlackScore alphaF a q) ≤
        ∑ a ∈ I.pageTopBalanceBidders slots S.assignment q,
          I.pageBalanceScore S.assignment a q :=
    hfeasible_sum_to_balance.trans hfeasible_top
  have hblocked_to_bid_error :
      (∑ a ∈ blockedT,
          msvvRatio * I.positiveSlackScore alphaF a q) ≤
        ∑ a ∈ blockedT, I.bid a q * (1 - Real.exp (-ε)) := by
    exact Finset.sum_le_sum fun a ha =>
      msvvRatio_mul_page_final_normalized_positiveSlackScore_le_bid_error_of_not_pageCanAssign
        I hbid hbudget slots rule hrule history S hS hε hsmall a q
        ((Finset.mem_filter.mp ha).2)
  have hblocked_bound :
      (∑ a ∈ blockedT,
          msvvRatio * I.positiveSlackScore alphaF a q) ≤
        I.pageMaxBidError slots ε q :=
    hblocked_to_bid_error.trans
      (pageSelectedBidError_le_pageMaxBidError
        I slots blockedT q hblockedT_card hε)
  have hsplit :
      (∑ a ∈ T, msvvRatio * I.positiveSlackScore alphaF a q) =
        (∑ a ∈ feasibleT, msvvRatio * I.positiveSlackScore alphaF a q) +
          ∑ a ∈ blockedT, msvvRatio * I.positiveSlackScore alphaF a q := by
    simpa [feasibleT, blockedT] using
      (Finset.sum_filter_add_sum_filter_not
        (s := T)
        (p := fun a => I.PageCanAssign S.assignment q a)
        (f := fun a => msvvRatio * I.positiveSlackScore alphaF a q)).symm
  calc
    msvvRatio *
        I.pageTopKSlackBeta slots
          (I.pageMsvvNormalizedAlphaFromAssignment
            (runPageHistoryStateFrom I slots rule S history).assignment) q =
      ∑ a ∈ T, msvvRatio * I.positiveSlackScore alphaF a q := by
        unfold pageTopKSlackBeta
        change msvvRatio *
            (∑ a ∈ T, I.positiveSlackScore alphaF a q) =
          ∑ a ∈ T, msvvRatio * I.positiveSlackScore alphaF a q
        rw [Finset.mul_sum]
    _ =
        (∑ a ∈ feasibleT, msvvRatio * I.positiveSlackScore alphaF a q) +
          ∑ a ∈ blockedT, msvvRatio * I.positiveSlackScore alphaF a q :=
        hsplit
    _ ≤
        (∑ a ∈ I.pageTopBalanceBidders slots S.assignment q,
          I.pageBalanceScore S.assignment a q) +
          I.pageMaxBidError slots ε q :=
        add_le_add hfeasible_bound hblocked_bound

/-- Sum of page-level top-`k` query duals over a concrete history list. -/
noncomputable def pageHistoryTopKSlackBetaSum
    [Fintype Advertiser] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (slots : Query → ℕ)
    (alpha : Advertiser → ℝ) : List Query → ℝ
  | [] => 0
  | q :: qs =>
      I.pageTopKSlackBeta slots alpha q +
        pageHistoryTopKSlackBetaSum I slots alpha qs

theorem pageHistoryTopKSlackBetaSum_eq_list_sum
    [Fintype Advertiser] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (alpha : Advertiser → ℝ)
    (history : List Query) :
    pageHistoryTopKSlackBetaSum I slots alpha history =
      (history.map fun q => I.pageTopKSlackBeta slots alpha q).sum := by
  induction history with
  | nil =>
      simp [pageHistoryTopKSlackBetaSum]
  | cons q qs ih =>
      simp [pageHistoryTopKSlackBetaSum, ih]

theorem sum_univ_pageTopKSlackBeta_eq_pageHistoryTopKSlackBetaSum_of_cover
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (alpha : Advertiser → ℝ)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ) :
    (∑ q : Query, I.pageTopKSlackBeta slots alpha q) =
      pageHistoryTopKSlackBetaSum I slots alpha history := by
  rw [sum_univ_eq_list_sum_of_historyFinset_eq_univ history hnodup hcover]
  rw [pageHistoryTopKSlackBetaSum_eq_list_sum]

theorem stepPageHistoryState_seen
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (rule : PageBatchRule Advertiser Query)
    (S : PageHistoryState Advertiser Query) (q : Query) :
    (stepPageHistoryState I slots rule S q).seen = insert q S.seen := by
  classical
  unfold stepPageHistoryState
  by_cases hseen : q ∈ S.seen
  · simp [hseen]
  · simp [hseen]

theorem msvvRatio_mul_pageHistoryTopKSlackBetaSum_normalized_topBalanceRun_le_pageHistoryBalanceCharge_add_pageHistoryMaxBidError
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ)
    (history : List Query) (S : PageHistoryState Advertiser Query)
    (hS : I.PageStateInvariant slots S)
    (hfresh : ∀ q, q ∈ historyFinset history → q ∉ S.seen)
    (hnodup : history.Nodup) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio *
        pageHistoryTopKSlackBetaSum I slots
          (I.pageMsvvNormalizedAlphaFromAssignment
            (runPageHistoryStateFrom I slots (I.pageTopBalanceRule slots)
              S history).assignment)
          history ≤
      I.pageHistoryBalanceChargeFrom slots (I.pageTopBalanceRule slots)
        S history +
        I.pageHistoryMaxBidErrorSum slots ε history := by
  induction history generalizing S with
  | nil =>
      simp [pageHistoryTopKSlackBetaSum, pageHistoryBalanceChargeFrom,
        pageHistoryMaxBidErrorSum]
  | cons q qs ih =>
      have hnodupParts := List.nodup_cons.mp hnodup
      have hqNotMemQs : q ∉ qs := hnodupParts.1
      have hnodupQs : qs.Nodup := hnodupParts.2
      have hqFresh : q ∉ S.seen := by
        exact hfresh q (by simp [historyFinset])
      let S' := stepPageHistoryState I slots (I.pageTopBalanceRule slots) S q
      have hS' : I.PageStateInvariant slots S' :=
        stepPageHistoryState_invariant I slots (I.pageTopBalanceRule slots)
          (pageTopBalanceRule_feasible I slots) S q hS
      have hqNotTail : q ∉ historyFinset qs := by
        intro hmem
        exact hqNotMemQs ((mem_historyFinset (history := qs) (q := q)).1 hmem)
      have htailFresh :
          ∀ r, r ∈ historyFinset qs → r ∉ S'.seen := by
        intro r hr hseen
        have hseen_eq :
            S'.seen = insert q S.seen := by
          simpa [S'] using
            (stepPageHistoryState_seen I slots (I.pageTopBalanceRule slots) S q)
        rw [hseen_eq] at hseen
        rcases Finset.mem_insert.mp hseen with hqr | hseenOld
        · subst r
          exact hqNotTail hr
        · exact hfresh r (by simp [historyFinset, hr]) hseenOld
      have htail :=
        ih S' hS' htailFresh hnodupQs
      have hhead :
          msvvRatio *
              I.pageTopKSlackBeta slots
                (I.pageMsvvNormalizedAlphaFromAssignment
                  (runPageHistoryStateFrom I slots (I.pageTopBalanceRule slots)
                    S (q :: qs)).assignment) q ≤
            (∑ a ∈ I.pageTopBalanceBidders slots S.assignment q,
              I.pageBalanceScore S.assignment a q) +
              I.pageMaxBidError slots ε q :=
        msvvRatio_mul_pageTopKSlackBeta_normalized_runPageHistoryStateFrom_le_topBalanceScore_add_pageMaxBidError
          I hbid hbudget slots (I.pageTopBalanceRule slots)
          (pageTopBalanceRule_feasible I slots) (q :: qs) S hS
          hε hsmall q
      have hhead' :
          msvvRatio *
              I.pageTopKSlackBeta slots
                (I.pageMsvvNormalizedAlphaFromAssignment
                  (runPageHistoryStateFrom I slots (I.pageTopBalanceRule slots)
                    S' qs).assignment) q ≤
            (∑ a ∈ I.pageTopBalanceBidders slots S.assignment q,
              I.pageBalanceScore S.assignment a q) +
              I.pageMaxBidError slots ε q := by
        simpa [S', runPageHistoryStateFrom] using hhead
      calc
        msvvRatio *
            pageHistoryTopKSlackBetaSum I slots
              (I.pageMsvvNormalizedAlphaFromAssignment
                (runPageHistoryStateFrom I slots (I.pageTopBalanceRule slots)
                  S (q :: qs)).assignment)
              (q :: qs)
            =
          msvvRatio *
              I.pageTopKSlackBeta slots
                (I.pageMsvvNormalizedAlphaFromAssignment
                  (runPageHistoryStateFrom I slots (I.pageTopBalanceRule slots)
                    S' qs).assignment) q +
            msvvRatio *
              pageHistoryTopKSlackBetaSum I slots
                (I.pageMsvvNormalizedAlphaFromAssignment
                  (runPageHistoryStateFrom I slots (I.pageTopBalanceRule slots)
                    S' qs).assignment)
                qs := by
                  simp [pageHistoryTopKSlackBetaSum, runPageHistoryStateFrom,
                    S', mul_add]
        _ ≤
          ((∑ a ∈ I.pageTopBalanceBidders slots S.assignment q,
              I.pageBalanceScore S.assignment a q) +
              I.pageMaxBidError slots ε q) +
            (I.pageHistoryBalanceChargeFrom slots (I.pageTopBalanceRule slots)
                S' qs +
              I.pageHistoryMaxBidErrorSum slots ε qs) :=
                add_le_add hhead' htail
        _ =
          I.pageHistoryBalanceChargeFrom slots (I.pageTopBalanceRule slots)
            S (q :: qs) +
            I.pageHistoryMaxBidErrorSum slots ε (q :: qs) := by
              simp [pageHistoryBalanceChargeFrom, pageHistoryMaxBidErrorSum,
                pageTopBalanceRule, hqFresh, S']
              ring

theorem msvvRatio_mul_sum_pageTopKSlackBeta_normalized_topBalanceRun_le_pageHistoryBalanceCharge_add_pageHistoryMaxBidError_of_cover
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio *
      (∑ q : Query,
        I.pageTopKSlackBeta slots
          (I.pageMsvvNormalizedAlphaFromAssignment
            (I.runPageAssignment slots (I.pageTopBalanceRule slots) history)) q) ≤
      I.pageHistoryBalanceChargeFrom slots (I.pageTopBalanceRule slots)
        initialPageHistoryState history +
        I.pageHistoryMaxBidErrorSum slots ε history := by
  have hnonneg : I.NonnegativeBudgets := fun a => (hbudget a).le
  have hS :
      I.PageStateInvariant slots
        (initialPageHistoryState : PageHistoryState Advertiser Query) :=
    initialPageHistoryState_invariant I slots hnonneg
  have hfresh :
      ∀ q,
        q ∈ historyFinset history →
          q ∉
            (initialPageHistoryState : PageHistoryState Advertiser Query).seen := by
    simp [initialPageHistoryState]
  have hhist :=
    msvvRatio_mul_pageHistoryTopKSlackBetaSum_normalized_topBalanceRun_le_pageHistoryBalanceCharge_add_pageHistoryMaxBidError
      I hbid hbudget slots history
      (initialPageHistoryState : PageHistoryState Advertiser Query)
      hS hfresh hnodup hε hsmall
  have hhist' :
      msvvRatio *
        pageHistoryTopKSlackBetaSum I slots
          (I.pageMsvvNormalizedAlphaFromAssignment
            (I.runPageAssignment slots (I.pageTopBalanceRule slots) history))
          history ≤
        I.pageHistoryBalanceChargeFrom slots (I.pageTopBalanceRule slots)
          initialPageHistoryState history +
          I.pageHistoryMaxBidErrorSum slots ε history := by
    simpa [runPageAssignment, runPageHistoryState] using hhist
  rw [sum_univ_pageTopKSlackBeta_eq_pageHistoryTopKSlackBetaSum_of_cover
    I slots
      (I.pageMsvvNormalizedAlphaFromAssignment
        (I.runPageAssignment slots (I.pageTopBalanceRule slots) history))
    history hnodup hcover]
  exact hhist'

theorem pageHistoryMsvvSmallBidsErrorSum_le_epsilon_mul_exp_one_add_one_mul_pageHistoryMaxBidSum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (slots : Query → ℕ) (history : List Query) {ε : ℝ}
    (hε : 0 ≤ ε) (hε_le_one : ε ≤ 1) :
    I.pageHistoryMsvvSmallBidsErrorSum slots ε history ≤
      ε * (Real.exp 1 + 1) * I.pageHistoryMaxBidSum slots history := by
  induction history with
  | nil =>
      simp [pageHistoryMsvvSmallBidsErrorSum,
        pageHistoryMaxBidAlphaErrorSum, pageHistoryMaxBidErrorSum,
        pageHistoryMaxBidSum]
  | cons q qs ih =>
      have hfactor :
          (Real.exp ε - 1) + (1 - Real.exp (-ε)) ≤
            ε * (Real.exp 1 + 1) :=
        msvvSmallBidsErrorFactor_le_epsilon_mul_exp_one_add_one
          hε hε_le_one
      have hweight_nonneg :
          0 ≤ (slots q : ℝ) * I.maxBidForQuery q :=
        mul_nonneg (Nat.cast_nonneg (slots q)) (maxBidForQuery_nonneg I q)
      have hhead :
          I.pageMaxBidAlphaError slots ε q +
              I.pageMaxBidError slots ε q ≤
            ε * (Real.exp 1 + 1) *
              ((slots q : ℝ) * I.maxBidForQuery q) := by
        calc
          I.pageMaxBidAlphaError slots ε q +
              I.pageMaxBidError slots ε q =
            ((slots q : ℝ) * I.maxBidForQuery q) *
              ((Real.exp ε - 1) + (1 - Real.exp (-ε))) := by
                simp [pageMaxBidAlphaError, pageMaxBidError]
                ring
          _ ≤
            ((slots q : ℝ) * I.maxBidForQuery q) *
              (ε * (Real.exp 1 + 1)) :=
                mul_le_mul_of_nonneg_left hfactor hweight_nonneg
          _ =
            ε * (Real.exp 1 + 1) *
              ((slots q : ℝ) * I.maxBidForQuery q) := by
                ring
      calc
        I.pageHistoryMsvvSmallBidsErrorSum slots ε (q :: qs) =
            (I.pageMaxBidAlphaError slots ε q +
              I.pageMaxBidError slots ε q) +
              I.pageHistoryMsvvSmallBidsErrorSum slots ε qs := by
                simp [pageHistoryMsvvSmallBidsErrorSum,
                  pageHistoryMaxBidAlphaErrorSum, pageHistoryMaxBidErrorSum]
                ring
        _ ≤
            ε * (Real.exp 1 + 1) *
                ((slots q : ℝ) * I.maxBidForQuery q) +
              ε * (Real.exp 1 + 1) * I.pageHistoryMaxBidSum slots qs :=
                add_le_add hhead ih
        _ =
            ε * (Real.exp 1 + 1) *
              I.pageHistoryMaxBidSum slots (q :: qs) := by
                simp [pageHistoryMaxBidSum]
                ring

theorem page_top_balance_msvv_approx_competitive_with_history_error
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio * I.pageOfflineOptimumValue slots (fun a => (hbudget a).le) ≤
      I.pageRevenue
          (I.runPageAssignment slots (I.pageTopBalanceRule slots) history) +
        I.pageHistoryMsvvSmallBidsErrorSum slots ε history := by
  let A :=
    I.runPageAssignment slots (I.pageTopBalanceRule slots) history
  let alpha : Advertiser → ℝ := I.pageMsvvNormalizedAlphaFromAssignment A
  let alphaMass : ℝ := ∑ a : Advertiser, I.budget a * alpha a
  let betaSum : ℝ :=
    ∑ q : Query, I.pageTopKSlackBeta slots alpha q
  let balanceCharge : ℝ :=
    I.pageHistoryBalanceChargeFrom slots (I.pageTopBalanceRule slots)
      initialPageHistoryState history
  let alphaError : ℝ := I.pageHistoryMaxBidAlphaErrorSum slots ε history
  let betaError : ℝ := I.pageHistoryMaxBidErrorSum slots ε history
  have hdualUpper :
      I.pageOfflineOptimumValue slots (fun a => (hbudget a).le) ≤
        alphaMass + betaSum := by
    simpa [alphaMass, betaSum, alpha] using
      pageOfflineOptimumValue_le_budget_alpha_add_topKSlackBeta
        I slots (fun a => (hbudget a).le) alpha
        (pageMsvvNormalizedAlphaFromAssignment_nonneg I hbid hbudget A)
  have hscaled :
      msvvRatio *
          I.pageOfflineOptimumValue slots (fun a => (hbudget a).le) ≤
        msvvRatio * (alphaMass + betaSum) :=
    mul_le_mul_of_nonneg_left hdualUpper msvvRatio_nonneg
  have halpha :
      msvvRatio * alphaMass + balanceCharge ≤
        I.pageRevenue A + alphaError := by
    simpa [A, alphaMass, alpha, balanceCharge, alphaError,
      pageMsvvNormalizedAlphaBudgetMass] using
      msvvRatio_mul_pageAlphaMass_balanceRun_add_pageHistoryBalanceCharge_le_revenue_add_pageHistoryMaxBidAlphaErrorSum
        I hbid hbudget slots history hε hsmall
  have hbeta :
      msvvRatio * betaSum ≤ balanceCharge + betaError := by
    simpa [A, alpha, betaSum, balanceCharge, betaError] using
      msvvRatio_mul_sum_pageTopKSlackBeta_normalized_topBalanceRun_le_pageHistoryBalanceCharge_add_pageHistoryMaxBidError_of_cover
        I hbid hbudget slots history hnodup hcover hε hsmall
  have hcombine :
      msvvRatio * (alphaMass + betaSum) ≤
        I.pageRevenue A + (alphaError + betaError) := by
    have hsplit :
        msvvRatio * (alphaMass + betaSum) =
          msvvRatio * alphaMass + msvvRatio * betaSum := by
      ring
    rw [hsplit]
    linarith
  exact hscaled.trans (by
    simpa [pageHistoryMsvvSmallBidsErrorSum, alphaError, betaError, A]
      using hcombine)

theorem page_top_balance_msvv_approx_competitive_with_error_bound
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (slots : Query → ℕ)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hε_le_one : ε ≤ 1)
    (hsmall : I.SmallBids ε) :
    msvvRatio * I.pageOfflineOptimumValue slots (fun a => (hbudget a).le) ≤
      I.pageRevenue
          (I.runPageAssignment slots (I.pageTopBalanceRule slots) history) +
        ε * (Real.exp 1 + 1) * I.pageHistoryMaxBidSum slots history := by
  have hbase :=
    page_top_balance_msvv_approx_competitive_with_history_error
      I hbid hbudget slots history hnodup hcover hε hsmall
  have herror :=
    pageHistoryMsvvSmallBidsErrorSum_le_epsilon_mul_exp_one_add_one_mul_pageHistoryMaxBidSum
      I slots history hε hε_le_one
  have hbound :
      I.pageRevenue
          (I.runPageAssignment slots (I.pageTopBalanceRule slots) history) +
          I.pageHistoryMsvvSmallBidsErrorSum slots ε history ≤
        I.pageRevenue
          (I.runPageAssignment slots (I.pageTopBalanceRule slots) history) +
          ε * (Real.exp 1 + 1) * I.pageHistoryMaxBidSum slots history := by
    linarith
  exact hbase.trans hbound

end AdWordsInstance

end Online
end AppliedModelingLib
