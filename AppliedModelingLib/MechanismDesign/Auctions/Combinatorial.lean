import AppliedModelingLib.Algorithms.Complexity.Classes
import AppliedModelingLib.SocialChoice.FairDivision.IndivisibleGoods
import AppliedModelingLib.Foundations.Math.FiniteSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace AppliedModelingLib
namespace Auction

/-- Bundles in combinatorial auctions reuse the fair-division bundle model. -/
abbrev Bundle (Item : Type*) := FairDivision.Bundle Item

/-- Bundle allocations reuse the fair-division allocation model. -/
abbrev BundleAllocation (Bidder Item : Type*) :=
  FairDivision.Allocation Bidder Item

/-- A direct combinatorial-auction report is a value for every bundle. -/
abbrev CombinatorialReport (Bidder Item : Type*) :=
  Bidder → Bundle Item → ℝ

/--
A direct-revelation combinatorial auction over indivisible goods.

The allocation is intentionally allowed to leave goods unallocated; feasibility
is a separate predicate because approximation algorithms often reason about
partial allocations.
-/
structure CombinatorialAuction (Bidder Item : Type*) where
  allocation : CombinatorialReport Bidder Item → BundleAllocation Bidder Item
  payment : CombinatorialReport Bidder Item → Bidder → ℝ

namespace CombinatorialAuction

variable {Bidder Item : Type*}

/-- Quasilinear utility for a combinatorial-auction bidder. -/
def utility (M : CombinatorialAuction Bidder Item)
    (values reports : CombinatorialReport Bidder Item) (i : Bidder) : ℝ :=
  values i (M.allocation reports i) - M.payment reports i

/-- Dominant-strategy truthfulness for direct bundle-value reports. -/
def TruthfulDominantStrategy [DecidableEq Bidder]
    (M : CombinatorialAuction Bidder Item) : Prop :=
  ∀ (values : CombinatorialReport Bidder Item)
      (i : Bidder) (report : Bundle Item → ℝ),
    M.utility values (Function.update values i report) i ≤
      M.utility values values i

/-- Truthfulness restricted to an admissible class of valuation profiles. -/
def TruthfulDominantStrategyOn [DecidableEq Bidder]
    (M : CombinatorialAuction Bidder Item)
    (admissible : CombinatorialReport Bidder Item → Prop) : Prop :=
  ∀ (values : CombinatorialReport Bidder Item),
    admissible values →
      ∀ (i : Bidder) (report : Bundle Item → ℝ),
        M.utility values (Function.update values i report) i ≤
          M.utility values values i

/-- Bundle valuations normalized to give the empty bundle value zero. -/
def Normalized (values : CombinatorialReport Bidder Item) : Prop :=
  ∀ i, values i ∅ = 0

/-- Bundle valuations that are everywhere nonnegative, matching the source type `ℝ₊^(2^G)`. -/
def NonnegativeValues (values : CombinatorialReport Bidder Item) : Prop :=
  ∀ i S, 0 ≤ values i S

/-- Truthful utility is always nonnegative. -/
def IndividuallyRational (M : CombinatorialAuction Bidder Item) : Prop :=
  ∀ (values : CombinatorialReport Bidder Item) (i : Bidder),
    0 ≤ M.utility values values i

/-- The mechanism never pays money to bidders. -/
def NoPositiveTransfers (M : CombinatorialAuction Bidder Item) : Prop :=
  ∀ (reports : CombinatorialReport Bidder Item) (i : Bidder),
    0 ≤ M.payment reports i

/-- Total payments collected by the auction. -/
noncomputable def revenue [Fintype Bidder]
    (M : CombinatorialAuction Bidder Item)
    (reports : CombinatorialReport Bidder Item) : ℝ :=
  ∑ i : Bidder, M.payment reports i

end CombinatorialAuction

variable {Bidder Item : Type*}

/--
Feasible partial allocation of a finite good set: every allocated good belongs
to `goods`, and no good is assigned to two different bidders.
-/
def IsFeasibleBundleAllocation [DecidableEq Item]
    (A : BundleAllocation Bidder Item) (goods : Finset Item) : Prop :=
  (∀ i g, g ∈ A i → g ∈ goods) ∧
    ∀ ⦃i j : Bidder⦄ ⦃g : Item⦄,
      i ≠ j → g ∈ A i → g ∈ A j → False

theorem feasible_emptyAllocation [DecidableEq Item] (goods : Finset Item) :
    IsFeasibleBundleAllocation
      (FairDivision.emptyAllocation Bidder Item) goods := by
  constructor
  · intro i g hmem
    simp [FairDivision.emptyAllocation] at hmem
  · intro i j g hij hgi hgj
    simp [FairDivision.emptyAllocation] at hgi

theorem feasible_of_isAllocationOf [DecidableEq Item]
    (A : BundleAllocation Bidder Item) (goods : Finset Item)
    (halloc : FairDivision.IsAllocationOf A goods) :
    IsFeasibleBundleAllocation A goods := by
  constructor
  · exact halloc.1
  · intro i j g hij hgi hgj
    obtain ⟨owner, howner, huniq⟩ := halloc.2 g (halloc.1 i g hgi)
    have hi : i = owner := huniq i hgi
    have hj : j = owner := huniq j hgj
    exact hij (hi.trans hj.symm)

/-- Social welfare of an allocation under reported bundle values. -/
noncomputable def allocationValue [Fintype Bidder]
    (values : CombinatorialReport Bidder Item)
    (A : BundleAllocation Bidder Item) : ℝ :=
  ∑ i : Bidder, values i (A i)

/-- Social welfare excluding one bidder. -/
noncomputable def allocationValueExcept [Fintype Bidder] [DecidableEq Bidder]
    (values : CombinatorialReport Bidder Item)
    (A : BundleAllocation Bidder Item) (i : Bidder) : ℝ :=
  (Finset.univ.erase i).sum fun j => values j (A j)

theorem allocationValue_nonneg [Fintype Bidder]
    (values : CombinatorialReport Bidder Item)
    (A : BundleAllocation Bidder Item)
    (hvalue : ∀ i, 0 ≤ values i (A i)) :
    0 ≤ allocationValue values A := by
  classical
  exact Finset.sum_nonneg fun i _ => hvalue i

/-- Total welfare splits into bidder `i`'s value plus everyone else's welfare. -/
theorem allocationValue_eq_self_add_except
    [Fintype Bidder] [DecidableEq Bidder]
    (values : CombinatorialReport Bidder Item)
    (A : BundleAllocation Bidder Item) (i : Bidder) :
    allocationValue values A =
      values i (A i) + allocationValueExcept values A i := by
  classical
  unfold allocationValue allocationValueExcept
  simpa [add_comm] using
    (Finset.sum_erase_add (s := Finset.univ)
      (f := fun j : Bidder => values j (A j)) (Finset.mem_univ i)).symm

/-- Reports with bidder `i` replaced by the zero valuation. -/
def reportsWithoutBidder [DecidableEq Bidder]
    (reports : CombinatorialReport Bidder Item) (i : Bidder) :
    CombinatorialReport Bidder Item :=
  Function.update reports i fun _ => 0

theorem reportsWithoutBidder_update_self [DecidableEq Bidder]
    (values : CombinatorialReport Bidder Item) (i : Bidder)
    (report : Bundle Item → ℝ) :
    reportsWithoutBidder (Function.update values i report) i =
      reportsWithoutBidder values i := by
  funext j S
  by_cases hji : j = i
  · subst j
    simp [reportsWithoutBidder]
  · simp [reportsWithoutBidder, Function.update, hji]

theorem allocationValueExcept_update_self
    [Fintype Bidder] [DecidableEq Bidder]
    (values : CombinatorialReport Bidder Item)
    (report : Bundle Item → ℝ)
    (A : BundleAllocation Bidder Item) (i : Bidder) :
    allocationValueExcept (Function.update values i report) A i =
      allocationValueExcept values A i := by
  classical
  unfold allocationValueExcept
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [Function.update, hji]

/--
An allocation rule is GVA-efficient when, for every declaration profile, it
maximizes total declared welfare over all candidate allocations.
-/
def WelfareMaximizingAllocationRule [Fintype Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item) :
    Prop :=
  ∀ reports A, allocationValue reports A ≤ allocationValue reports (alloc reports)

/--
Generalized Vickrey auction generated by a supplied allocation rule.
The payment is the Clarke pivot price: everyone else's welfare in the auction
without bidder `i`, minus everyone else's welfare under the chosen allocation.
-/
noncomputable def generalizedVickreyAuction
    [Fintype Bidder] [DecidableEq Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item) :
    CombinatorialAuction Bidder Item where
  allocation reports := alloc reports
  payment reports i :=
    allocationValueExcept reports (alloc (reportsWithoutBidder reports i)) i -
      allocationValueExcept reports (alloc reports) i

theorem generalizedVickreyAuction_utility_update_eq
    [Fintype Bidder] [DecidableEq Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item)
    (values : CombinatorialReport Bidder Item) (i : Bidder)
    (report : Bundle Item → ℝ) :
    (generalizedVickreyAuction alloc).utility values
        (Function.update values i report) i =
      allocationValue values (alloc (Function.update values i report)) -
        allocationValueExcept values
          (alloc (reportsWithoutBidder values i)) i := by
  classical
  have hsplit :=
    allocationValue_eq_self_add_except values
      (alloc (Function.update values i report)) i
  simp [CombinatorialAuction.utility, generalizedVickreyAuction,
    reportsWithoutBidder_update_self, allocationValueExcept_update_self]
  rw [hsplit]
  ring

theorem generalizedVickreyAuction_utility_truth_eq
    [Fintype Bidder] [DecidableEq Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item)
    (values : CombinatorialReport Bidder Item) (i : Bidder) :
    (generalizedVickreyAuction alloc).utility values values i =
      allocationValue values (alloc values) -
        allocationValueExcept values
          (alloc (reportsWithoutBidder values i)) i := by
  classical
  have hsplit :=
    allocationValue_eq_self_add_except values (alloc values) i
  simp [CombinatorialAuction.utility, generalizedVickreyAuction]
  rw [hsplit]
  ring

/-- a welfare-maximizing GVA is truthful. -/
theorem generalizedVickreyAuction_truthful
    [Fintype Bidder] [DecidableEq Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item)
    (hmax : WelfareMaximizingAllocationRule alloc) :
    (generalizedVickreyAuction alloc).TruthfulDominantStrategy := by
  intro values i report
  rw [generalizedVickreyAuction_utility_update_eq,
    generalizedVickreyAuction_utility_truth_eq]
  have halloc :
      allocationValue values (alloc (Function.update values i report)) ≤
        allocationValue values (alloc values) :=
    hmax values (alloc (Function.update values i report))
  linarith

/--
under nonnegative bundle values, a truthful bidder's GVA
utility is nonnegative.
-/
theorem generalizedVickreyAuction_truthful_utility_nonneg
    [Fintype Bidder] [DecidableEq Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item)
    (hmax : WelfareMaximizingAllocationRule alloc)
    (values : CombinatorialReport Bidder Item)
    (hvalues : CombinatorialAuction.NonnegativeValues values) (i : Bidder) :
    0 ≤ (generalizedVickreyAuction alloc).utility values values i := by
  rw [generalizedVickreyAuction_utility_truth_eq]
  have halloc :
      allocationValue values (alloc (reportsWithoutBidder values i)) ≤
        allocationValue values (alloc values) :=
    hmax values (alloc (reportsWithoutBidder values i))
  have hsplit :=
    allocationValue_eq_self_add_except values
      (alloc (reportsWithoutBidder values i)) i
  have hi_nonneg :
      0 ≤ values i ((alloc (reportsWithoutBidder values i)) i) :=
    hvalues i ((alloc (reportsWithoutBidder values i)) i)
  linarith

/--
Reject-all combinatorial auction. It is a useful baseline and a sanity check for
the direct-revelation interface: reports cannot affect anyone's allocation or
payment.
-/
def rejectAllAuction : CombinatorialAuction Bidder Item where
  allocation _ := FairDivision.emptyAllocation Bidder Item
  payment _ _ := 0

theorem rejectAllAuction_truthful [DecidableEq Bidder] :
    (rejectAllAuction : CombinatorialAuction Bidder Item).TruthfulDominantStrategy := by
  intro values i report
  simp [CombinatorialAuction.utility, rejectAllAuction]

theorem rejectAllAuction_noPositiveTransfers :
    (rejectAllAuction : CombinatorialAuction Bidder Item).NoPositiveTransfers := by
  intro reports i
  simp [rejectAllAuction]

/-! ## Critical-price target-bundle mechanisms -/

/--
A bundle price rule is own-report independent when changing bidder `i`'s report
does not change the price offered to bidder `i`.
-/
def BundlePriceOwnReportIndependent [DecidableEq Bidder]
    (price : CombinatorialReport Bidder Item → Bidder → ℝ) : Prop :=
  ∀ (reports : CombinatorialReport Bidder Item)
      (i : Bidder) (report : Bundle Item → ℝ),
    price (Function.update reports i report) i = price reports i

/--
Target-bundle threshold auction: bidder `i` either receives `target i` at the
offered price, or receives the empty bundle and pays zero.
-/
noncomputable def targetBundleThresholdAuction
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ) :
    CombinatorialAuction Bidder Item where
  allocation reports i :=
    if price reports i ≤ reports i (target i) then target i else ∅
  payment reports i :=
    if price reports i ≤ reports i (target i) then price reports i else 0

theorem targetBundleThresholdAuction_utility_eq
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (values reports : CombinatorialReport Bidder Item) (i : Bidder) :
    (targetBundleThresholdAuction target price).utility values reports i =
      if price reports i ≤ reports i (target i) then
        values i (target i) - price reports i
      else
        values i ∅ := by
  by_cases h : price reports i ≤ reports i (target i) <;>
    simp [CombinatorialAuction.utility, targetBundleThresholdAuction, h]

/--
Critical-price truthfulness for target-bundle mechanisms on normalized
valuations. This is the reusable theorem shape for single-minded combinatorial
auction critical-value payments.
-/
theorem targetBundleThresholdAuction_truthfulOn_normalized [DecidableEq Bidder]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind : BundlePriceOwnReportIndependent price) :
    (targetBundleThresholdAuction target price).TruthfulDominantStrategyOn
      CombinatorialAuction.Normalized := by
  intro values hnorm i report
  have htruthUtility :
      (targetBundleThresholdAuction target price).utility values values i =
        if price values i ≤ values i (target i) then
          values i (target i) - price values i
        else 0 := by
    rw [targetBundleThresholdAuction_utility_eq]
    simp [hnorm i]
  have hreportUtility :
      (targetBundleThresholdAuction target price).utility values
          (Function.update values i report) i =
        if price values i ≤ report (target i) then
          values i (target i) - price values i
        else 0 := by
    rw [targetBundleThresholdAuction_utility_eq]
    simp [Function.update, hind values i report, hnorm i]
  rw [htruthUtility, hreportUtility]
  by_cases htruth : price values i ≤ values i (target i)
  · by_cases hreport : price values i ≤ report (target i)
    · simp [htruth, hreport]
    · simp [htruth, hreport]
  · by_cases hreport : price values i ≤ report (target i)
    · simpa only [htruth, hreport, ↓reduceIte, ge_iff_le]
        using sub_nonpos.mpr (le_of_lt (lt_of_not_ge htruth))
    · simp [htruth, hreport]

/--
Single-minded bundle value: the bidder has value `value` exactly when the
allocated bundle contains the desired bundle.
-/
structure SingleMindedBid (Item : Type*) where
  desired : Bundle Item
  value : ℝ

namespace SingleMindedBid

variable [DecidableEq Item]

/-- Bundle valuation induced by a single-minded bid. -/
def valuation (b : SingleMindedBid Item) : Bundle Item → ℝ :=
  fun S => if b.desired ⊆ S then b.value else 0

theorem valuation_of_contains (b : SingleMindedBid Item) {S : Bundle Item}
    (h : b.desired ⊆ S) :
    b.valuation S = b.value := by
  simp [valuation, h]

theorem valuation_of_not_contains (b : SingleMindedBid Item) {S : Bundle Item}
    (h : ¬ b.desired ⊆ S) :
    b.valuation S = 0 := by
  simp [valuation, h]

theorem valuation_empty_eq_zero_of_nonempty
    (b : SingleMindedBid Item) (hb : b.desired.Nonempty) :
    b.valuation ∅ = 0 := by
  have hnot : ¬ b.desired ⊆ (∅ : Bundle Item) := by
    intro hsub
    rcases hb with ⟨g, hg⟩
    have hempty : g ∈ (∅ : Bundle Item) := hsub hg
    simp at hempty
  exact valuation_of_not_contains b hnot

end SingleMindedBid

/-- Profile of bundle valuations induced by single-minded bids. -/
def singleMindedValuationProfile [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) :
    CombinatorialReport Bidder Item :=
  fun i => (bids i).valuation

theorem singleMindedValuationProfile_empty_eq_zero_of_nonempty
    [DecidableEq Item] (bids : Bidder → SingleMindedBid Item)
    (hb : ∀ i, (bids i).desired.Nonempty) (i : Bidder) :
    singleMindedValuationProfile bids i ∅ = 0 := by
  exact SingleMindedBid.valuation_empty_eq_zero_of_nonempty (bids i) (hb i)

theorem singleMindedValuationProfile_normalized_of_nonempty
    [DecidableEq Item] (bids : Bidder → SingleMindedBid Item)
    (hb : ∀ i, (bids i).desired.Nonempty) :
    CombinatorialAuction.Normalized
      (singleMindedValuationProfile bids) := by
  intro i
  exact singleMindedValuationProfile_empty_eq_zero_of_nonempty bids hb i

/--
Single-minded valuation profiles with nonempty desired bundles form an
admissible class for normalized-profile critical-price truthfulness.
-/
def IsNonemptySingleMindedProfile [DecidableEq Item]
    (values : CombinatorialReport Bidder Item) : Prop :=
  ∃ bids : Bidder → SingleMindedBid Item,
    (∀ i, (bids i).desired.Nonempty) ∧
      values = singleMindedValuationProfile bids

theorem targetBundleThresholdAuction_truthfulOn_singleMindedProfiles
    [DecidableEq Bidder] [DecidableEq Item]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind : BundlePriceOwnReportIndependent price) :
    (targetBundleThresholdAuction target price).TruthfulDominantStrategyOn
      IsNonemptySingleMindedProfile := by
  intro values hvalues i report
  rcases hvalues with ⟨bids, hb, rfl⟩
  exact targetBundleThresholdAuction_truthfulOn_normalized target price hind
    (singleMindedValuationProfile bids)
    (singleMindedValuationProfile_normalized_of_nonempty bids hb)
    i report

/-! ## Feasible allocations for accepted single-minded bidders -/

/-- Accepted single-minded bidders receive their desired bundles; others receive nothing. -/
def singleMindedAllocation [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) (accepted : Finset Bidder) :
    BundleAllocation Bidder Item :=
  fun i => if i ∈ accepted then (bids i).desired else ∅

/-- Accepted desired bundles are pairwise disjoint. -/
def PairwiseDisjointDesired [DecidableEq Bidder]
    [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (accepted : Finset Bidder) : Prop :=
  ∀ ⦃i j : Bidder⦄,
    i ∈ accepted → j ∈ accepted → i ≠ j →
      Disjoint (bids i).desired (bids j).desired

/-- Feasible set-packing selections are pairwise disjoint requested sets. -/
def SetPackingFeasible [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (selected : Finset Bidder) : Prop :=
  ∀ ⦃i j : Bidder⦄,
    i ∈ selected → j ∈ selected → i ≠ j →
      Disjoint (sets i) (sets j)

/-- Encode a weighted set-packing instance as single-minded bids. -/
def setPackingSingleMindedBids
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ) :
    Bidder → SingleMindedBid Item :=
  fun i => { desired := sets i, value := weights i }

/--
Feasibility in weighted set packing is exactly feasibility of the corresponding
single-minded accepted set.
-/
theorem pairwiseDisjointDesired_setPackingSingleMindedBids_iff
    [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (selected : Finset Bidder) :
    PairwiseDisjointDesired
        (setPackingSingleMindedBids sets weights) selected ↔
      SetPackingFeasible sets selected := by
  constructor
  · intro h i j hi hj hij
    exact h hi hj hij
  · intro h i j hi hj hij
    exact h hi hj hij

theorem singleMindedAllocation_feasible [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (goods : Finset Item)
    (hgoods : ∀ i, i ∈ accepted → (bids i).desired ⊆ goods)
    (hdisjoint : PairwiseDisjointDesired bids accepted) :
    IsFeasibleBundleAllocation
      (singleMindedAllocation bids accepted) goods := by
  constructor
  · intro i g hg
    by_cases hi : i ∈ accepted
    · have hgdesired : g ∈ (bids i).desired := by
        simpa [singleMindedAllocation, hi] using hg
      exact hgoods i hi hgdesired
    · simp [singleMindedAllocation, hi] at hg
  · intro i j g hij hgi hgj
    by_cases hi : i ∈ accepted
    · by_cases hj : j ∈ accepted
      · have hgiDesired : g ∈ (bids i).desired := by
          simpa [singleMindedAllocation, hi] using hgi
        have hgjDesired : g ∈ (bids j).desired := by
          simpa [singleMindedAllocation, hj] using hgj
        exact (Finset.disjoint_left.mp (hdisjoint hi hj hij))
          hgiDesired hgjDesired
      · simp [singleMindedAllocation, hj] at hgj
    · simp [singleMindedAllocation, hi] at hgi

/-! ## Feasibility of target-bundle threshold outcomes -/

/-- Winners of a target-bundle threshold auction under a report profile. -/
noncomputable def targetBundleWinners [Fintype Bidder]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (reports : CombinatorialReport Bidder Item) : Finset Bidder :=
  (Finset.univ : Finset Bidder).filter fun i =>
    price reports i ≤ reports i (target i)

/--
View a target-bundle threshold report profile as a single-minded bid profile
whose desired bundle is the mechanism target and whose value is the reported
value for that target.
-/
def targetAsSingleMindedBids
    (target : Bidder → Bundle Item)
    (reports : CombinatorialReport Bidder Item) :
    Bidder → SingleMindedBid Item :=
  fun i => { desired := target i, value := reports i (target i) }

theorem targetBundleThresholdAuction_allocation_eq_singleMindedAllocation
    [Fintype Bidder] [DecidableEq Bidder]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (reports : CombinatorialReport Bidder Item) :
    (targetBundleThresholdAuction target price).allocation reports =
      singleMindedAllocation
        (targetAsSingleMindedBids target reports)
        (targetBundleWinners target price reports) := by
  funext i
  by_cases hwin : price reports i ≤ reports i (target i)
  · simp [targetBundleThresholdAuction, singleMindedAllocation,
      targetBundleWinners, targetAsSingleMindedBids, hwin]
  · simp [targetBundleThresholdAuction, singleMindedAllocation,
      targetBundleWinners, hwin]

theorem targetBundleThresholdAuction_feasible_of_pairwiseDisjoint
    [Fintype Bidder] [DecidableEq Bidder] [DecidableEq Item]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (reports : CombinatorialReport Bidder Item)
    (goods : Finset Item)
    (hgoods : ∀ i,
      i ∈ targetBundleWinners target price reports → target i ⊆ goods)
    (hdisjoint :
      PairwiseDisjointDesired
        (targetAsSingleMindedBids target reports)
        (targetBundleWinners target price reports)) :
    IsFeasibleBundleAllocation
      ((targetBundleThresholdAuction target price).allocation reports)
      goods := by
  rw [targetBundleThresholdAuction_allocation_eq_singleMindedAllocation]
  exact singleMindedAllocation_feasible
    (targetAsSingleMindedBids target reports)
    (targetBundleWinners target price reports)
    goods
    (by
      intro i hi
      exact hgoods i hi)
    hdisjoint

/-! ## Source-shaped single-minded mechanism axioms -/

/--
A direct mechanism for single-minded bid profiles, represented by the accepted
set and payments. Exactness is built in: accepted bidders receive exactly their
declared desired bundle, and denied bidders receive nothing.
-/
structure SingleMindedAcceptedMechanism (Bidder Item : Type*) where
  accepted : (Bidder → SingleMindedBid Item) → Finset Bidder
  payment : (Bidder → SingleMindedBid Item) → Bidder → ℝ

namespace SingleMindedAcceptedMechanism

variable {Bidder Item : Type*}

/-- The exact allocation induced by an accepted-set mechanism. -/
def allocation [DecidableEq Bidder]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (reports : Bidder → SingleMindedBid Item) :
    BundleAllocation Bidder Item :=
  singleMindedAllocation reports (M.accepted reports)

/-- Quasilinear utility for a true single-minded type under reported bids. -/
noncomputable def utility [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (values reports : Bidder → SingleMindedBid Item) (i : Bidder) : ℝ :=
  (values i).valuation (M.allocation reports i) - M.payment reports i

/-- Nonempty, nonnegative single-minded bid profiles. -/
def NonnegativeNonemptyProfile [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) : Prop :=
  ∀ i, (bids i).desired.Nonempty ∧ 0 ≤ (bids i).value

/-- Truthfulness for single-minded bids, with deviations restricted to an admissible domain. -/
def TruthfulOn [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (admissible : (Bidder → SingleMindedBid Item) → Prop) : Prop :=
  ∀ values,
    admissible values →
      ∀ i report,
        admissible (Function.update values i report) →
          M.utility values (Function.update values i report) i ≤
            M.utility values values i

/-- Participation: denied bidders pay zero. -/
def Participation (M : SingleMindedAcceptedMechanism Bidder Item) : Prop :=
  ∀ reports i, i ∉ M.accepted reports → M.payment reports i = 0

/--
Under Participation, a denied bidder with a nonempty true desired bundle has
zero utility: the accepted-set allocation gives nothing and the payment is zero.
-/
theorem utility_eq_zero_of_denied_participation
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hpart : M.Participation)
    (values reports : Bidder → SingleMindedBid Item) {i : Bidder}
    (hvalue_nonempty : (values i).desired.Nonempty)
    (hdeny : i ∉ M.accepted reports) :
    M.utility values reports i = 0 := by
  have hpay := hpart reports i hdeny
  have hval :
      (values i).valuation (M.allocation reports i) = 0 := by
    have hempty :=
      SingleMindedBid.valuation_empty_eq_zero_of_nonempty
        (values i) hvalue_nonempty
    simpa [allocation, singleMindedAllocation, hdeny] using hempty
  simp [utility, hval, hpay]

/--
Monotonicity: a granted bid remains granted after asking for a subset and
weakly increasing the declared value.
-/
def Monotonicity [DecidableEq Bidder]
    (M : SingleMindedAcceptedMechanism Bidder Item) : Prop :=
  ∀ reports i s' v',
    i ∈ M.accepted reports →
      s' ⊆ (reports i).desired →
        (reports i).value ≤ v' →
          i ∈ M.accepted
            (Function.update reports i { desired := s', value := v' })

/--
Domain-restricted monotonicity for nonempty, nonnegative single-minded type
spaces: the strengthened report must remain inside the admissible domain.
-/
def MonotonicityOn [DecidableEq Bidder]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (admissible : (Bidder → SingleMindedBid Item) → Prop) : Prop :=
  ∀ reports,
    admissible reports →
      ∀ i s' v',
        i ∈ M.accepted reports →
          admissible (Function.update reports i { desired := s', value := v' }) →
            s' ⊆ (reports i).desired →
              (reports i).value ≤ v' →
                i ∈ M.accepted
                  (Function.update reports i { desired := s', value := v' })

theorem monotonicityOn_of_monotonicity [DecidableEq Bidder]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (admissible : (Bidder → SingleMindedBid Item) → Prop)
    (hmono : M.Monotonicity) :
    M.MonotonicityOn admissible := by
  intro reports _hreports i s v hacc _hupdated hsub hle
  exact hmono reports i s v hacc hsub hle

/--
Critical-value data. The threshold may depend on other reports and the
candidate desired bundle, but not on the bidder's declared value for that bundle.
-/
structure CriticalValueCertificate [DecidableEq Bidder]
    (M : SingleMindedAcceptedMechanism Bidder Item) where
  threshold : (Bidder → SingleMindedBid Item) → Bidder → Bundle Item → ℝ
  threshold_nonneg : ∀ reports i s, 0 ≤ threshold reports i s
  threshold_own_value_independent :
    ∀ reports i s v,
      threshold (Function.update reports i { desired := s, value := v }) i s =
        threshold reports i s
  below_denied :
    ∀ reports i s v,
      v < threshold reports i s →
        i ∉ M.accepted
          (Function.update reports i { desired := s, value := v })
  above_granted :
    ∀ reports i s v,
      threshold reports i s < v →
        i ∈ M.accepted
          (Function.update reports i { desired := s, value := v })
  payment_eq_of_accepted :
    ∀ reports i,
      i ∈ M.accepted reports →
        M.payment reports i = threshold reports i (reports i).desired

namespace CriticalValueCertificate

variable [DecidableEq Bidder] {M : SingleMindedAcceptedMechanism Bidder Item}

theorem threshold_mono_of_monotone
    (C : CriticalValueCertificate M) (hmono : M.Monotonicity)
    (reports : Bidder → SingleMindedBid Item) (i : Bidder)
    {sSmall sLarge : Bundle Item}
    (hsub : sSmall ⊆ sLarge) :
    C.threshold reports i sSmall ≤ C.threshold reports i sLarge := by
  by_contra hnot
  have hlt :
      C.threshold reports i sLarge < C.threshold reports i sSmall :=
    lt_of_not_ge hnot
  let x : ℝ :=
    (C.threshold reports i sLarge + C.threshold reports i sSmall) / 2
  have hlarge_x : C.threshold reports i sLarge < x := by
    dsimp [x]
    linarith
  have hx_small : x < C.threshold reports i sSmall := by
    dsimp [x]
    linarith
  have hlarge_acc :
      i ∈ M.accepted
        (Function.update reports i { desired := sLarge, value := x }) :=
    C.above_granted reports i sLarge x hlarge_x
  have hsmall_acc_update :
      i ∈ M.accepted
        (Function.update
          (Function.update reports i { desired := sLarge, value := x })
          i { desired := sSmall, value := x }) := by
    exact hmono
      (Function.update reports i { desired := sLarge, value := x })
      i sSmall x hlarge_acc
      (by simpa [Function.update] using hsub)
      (by simp [Function.update])
  have hsmall_acc :
      i ∈ M.accepted
        (Function.update reports i { desired := sSmall, value := x }) := by
    simpa [Function.update] using hsmall_acc_update
  exact (C.below_denied reports i sSmall x hx_small) hsmall_acc

theorem threshold_le_value_of_accepted
    (C : CriticalValueCertificate M)
    (reports : Bidder → SingleMindedBid Item) {i : Bidder}
    (hacc : i ∈ M.accepted reports) :
    C.threshold reports i (reports i).desired ≤ (reports i).value := by
  by_contra hnot
  have hlt : (reports i).value < C.threshold reports i (reports i).desired :=
    lt_of_not_ge hnot
  have hdeny :=
    C.below_denied reports i (reports i).desired (reports i).value hlt
  have hsame :
      Function.update reports i
        { desired := (reports i).desired, value := (reports i).value } =
        reports := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [Function.update]
    · simp [Function.update, hk]
  exact hdeny (by simpa [hsame] using hacc)

theorem value_le_threshold_of_denied
    (C : CriticalValueCertificate M)
    (reports : Bidder → SingleMindedBid Item) {i : Bidder}
    (hdeny : i ∉ M.accepted reports) :
    (reports i).value ≤ C.threshold reports i (reports i).desired := by
  by_contra hnot
  have hlt : C.threshold reports i (reports i).desired < (reports i).value :=
    lt_of_not_ge hnot
  have hacc :=
    C.above_granted reports i (reports i).desired (reports i).value hlt
  have hsame :
      Function.update reports i
        { desired := (reports i).desired, value := (reports i).value } =
        reports := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [Function.update]
    · simp [Function.update, hk]
  exact hdeny (by simpa [hsame] using hacc)

end CriticalValueCertificate

theorem utility_nonneg_truthful
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hpart : M.Participation)
    (C : CriticalValueCertificate M)
    (values : Bidder → SingleMindedBid Item)
    (hvalues : NonnegativeNonemptyProfile values) (i : Bidder) :
    0 ≤ M.utility values values i := by
  by_cases hacc : i ∈ M.accepted values
  · have hpay := C.payment_eq_of_accepted values i hacc
    have hthreshold_le :=
      C.threshold_le_value_of_accepted values hacc
    have hval :
        (values i).valuation (M.allocation values i) = (values i).value := by
      simp [allocation, singleMindedAllocation, hacc,
        SingleMindedBid.valuation_of_contains]
    simp [utility, hval, hpay]
    linarith
  · have hpay := hpart values i hacc
    have hval :
        (values i).valuation (M.allocation values i) = 0 := by
      have hempty :=
        SingleMindedBid.valuation_empty_eq_zero_of_nonempty
          (values i) (hvalues i).1
      simpa [allocation, singleMindedAllocation, hacc] using hempty
    simp [utility, hval, hpay]

/--
Source-shaped truthfulness criterion for accepted-set mechanisms over
single-minded bid profiles. Exactness is represented by the accepted-set
allocation model; Monotonicity, Participation, and Critical imply truthful
single-minded declarations on nonempty, nonnegative types.
-/
theorem truthfulOn_of_monotonicity_participation_critical
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hmono : M.Monotonicity)
    (hpart : M.Participation)
    (C : CriticalValueCertificate M) :
    M.TruthfulOn NonnegativeNonemptyProfile := by
  intro values hvalues i report _hreport
  let reports' := Function.update values i report
  have htruth_nonneg :
      0 ≤ M.utility values values i :=
    utility_nonneg_truthful M hpart C values hvalues i
  by_cases hmis : i ∈ M.accepted reports'
  · have hpay_mis :
        M.payment reports' i =
          C.threshold values i report.desired := by
      have hpay := C.payment_eq_of_accepted reports' i hmis
      have hind :=
        C.threshold_own_value_independent values i report.desired report.value
      simpa [reports', Function.update, hind] using hpay
    by_cases hsub : (values i).desired ⊆ report.desired
    · have hval_mis :
          (values i).valuation (M.allocation reports' i) =
            (values i).value := by
        have hreports_i : reports' i = report := by
          simp [reports']
        rw [allocation, singleMindedAllocation, if_pos hmis, hreports_i]
        exact SingleMindedBid.valuation_of_contains (values i) hsub
      have hthreshold_bundle :
          C.threshold values i (values i).desired ≤
            C.threshold values i report.desired :=
        C.threshold_mono_of_monotone hmono values i hsub
      by_cases htruth : i ∈ M.accepted values
      · have hpay_truth := C.payment_eq_of_accepted values i htruth
        have hval_truth :
            (values i).valuation (M.allocation values i) =
              (values i).value := by
          simp [allocation, singleMindedAllocation, htruth,
            SingleMindedBid.valuation_of_contains]
        simp [utility, hval_truth, hpay_truth]
        linarith
      · have hvalue_le_threshold :=
          C.value_le_threshold_of_denied values htruth
        have hpay_truth := hpart values i htruth
        have hval_truth :
            (values i).valuation (M.allocation values i) = 0 := by
          have hempty :=
            SingleMindedBid.valuation_empty_eq_zero_of_nonempty
              (values i) (hvalues i).1
          simpa [allocation, singleMindedAllocation, htruth] using hempty
        simp [utility, hval_truth, hpay_truth]
        linarith
    · have hval_mis :
          (values i).valuation (M.allocation reports' i) = 0 := by
        have hreports_i : reports' i = report := by
          simp [reports']
        rw [allocation, singleMindedAllocation, if_pos hmis, hreports_i]
        exact SingleMindedBid.valuation_of_not_contains (values i) hsub
      have hpay_nonneg :
          0 ≤ M.payment reports' i := by
        rw [hpay_mis]
        exact C.threshold_nonneg values i report.desired
      have hmis_nonpos :
          M.utility values reports' i ≤ 0 := by
        simp [utility, hval_mis]
        linarith
      exact hmis_nonpos.trans htruth_nonneg
  · have hpay_mis := hpart reports' i hmis
    have hval_mis :
        (values i).valuation (M.allocation reports' i) = 0 := by
      have hempty :=
        SingleMindedBid.valuation_empty_eq_zero_of_nonempty
          (values i) (hvalues i).1
      simpa [allocation, singleMindedAllocation, hmis] using hempty
    have hmis_zero :
        M.utility values reports' i = 0 := by
      simp [utility, hval_mis, hpay_mis]
    rw [hmis_zero]
    exact htruth_nonneg

/--
Critical-value data with an explicit infinite case. A finite threshold
`some p` behaves as the usual critical price; `none` means the bidder is never
accepted for that desired bundle at any declared value.
-/
structure CriticalValueWithInfinityCertificate [DecidableEq Bidder]
    (M : SingleMindedAcceptedMechanism Bidder Item) where
  threshold : (Bidder → SingleMindedBid Item) → Bidder → Bundle Item → Option ℝ
  threshold_nonneg : ∀ reports i s p, threshold reports i s = some p → 0 ≤ p
  threshold_own_value_independent :
    ∀ reports i s v,
      threshold (Function.update reports i { desired := s, value := v }) i s =
        threshold reports i s
  below_denied :
    ∀ reports i s v p,
      threshold reports i s = some p →
        v < p →
          i ∉ M.accepted
            (Function.update reports i { desired := s, value := v })
  above_granted :
    ∀ reports i s v p,
      threshold reports i s = some p →
        p < v →
          i ∈ M.accepted
            (Function.update reports i { desired := s, value := v })
  infinite_denied :
    ∀ reports i s v,
      threshold reports i s = none →
        i ∉ M.accepted
          (Function.update reports i { desired := s, value := v })
  payment_eq_of_accepted :
    ∀ reports i,
      i ∈ M.accepted reports →
        ∃ p,
          threshold reports i (reports i).desired = some p ∧
            M.payment reports i = p

namespace CriticalValueWithInfinityCertificate

variable [DecidableEq Bidder] {M : SingleMindedAcceptedMechanism Bidder Item}

/--
Finite thresholds are monotone in the source bundle order even when smaller
bundles may a priori have infinite critical value.
-/
theorem finite_threshold_mono_of_monotone
    (C : CriticalValueWithInfinityCertificate M) (hmono : M.Monotonicity)
    (reports : Bidder → SingleMindedBid Item) (i : Bidder)
    {sSmall sLarge : Bundle Item} {pLarge : ℝ}
    (hsub : sSmall ⊆ sLarge)
    (hLarge : C.threshold reports i sLarge = some pLarge) :
    ∃ pSmall,
      C.threshold reports i sSmall = some pSmall ∧ pSmall ≤ pLarge := by
  cases hSmall : C.threshold reports i sSmall with
  | none =>
      let x : ℝ := pLarge + 1
      have hlarge_x : pLarge < x := by
        dsimp [x]
        linarith
      have hlarge_acc :
          i ∈ M.accepted
            (Function.update reports i { desired := sLarge, value := x }) :=
        C.above_granted reports i sLarge x pLarge hLarge hlarge_x
      have hsmall_acc_update :
          i ∈ M.accepted
            (Function.update
              (Function.update reports i { desired := sLarge, value := x })
              i { desired := sSmall, value := x }) := by
        exact hmono
          (Function.update reports i { desired := sLarge, value := x })
          i sSmall x hlarge_acc
          (by simpa [Function.update] using hsub)
          (by simp [Function.update])
      have hsmall_acc :
          i ∈ M.accepted
            (Function.update reports i { desired := sSmall, value := x }) := by
        simpa [Function.update] using hsmall_acc_update
      exact False.elim
        ((C.infinite_denied reports i sSmall x hSmall) hsmall_acc)
  | some pSmall =>
      refine ⟨pSmall, rfl, ?_⟩
      by_contra hnot
      have hlt : pLarge < pSmall := lt_of_not_ge hnot
      let x : ℝ := (pLarge + pSmall) / 2
      have hlarge_x : pLarge < x := by
        dsimp [x]
        linarith
      have hx_small : x < pSmall := by
        dsimp [x]
        linarith
      have hlarge_acc :
          i ∈ M.accepted
            (Function.update reports i { desired := sLarge, value := x }) :=
        C.above_granted reports i sLarge x pLarge hLarge hlarge_x
      have hsmall_acc_update :
          i ∈ M.accepted
            (Function.update
              (Function.update reports i { desired := sLarge, value := x })
              i { desired := sSmall, value := x }) := by
        exact hmono
          (Function.update reports i { desired := sLarge, value := x })
          i sSmall x hlarge_acc
          (by simpa [Function.update] using hsub)
          (by simp [Function.update])
      have hsmall_acc :
          i ∈ M.accepted
            (Function.update reports i { desired := sSmall, value := x }) := by
        simpa [Function.update] using hsmall_acc_update
      exact (C.below_denied reports i sSmall x pSmall hSmall hx_small)
        hsmall_acc

theorem threshold_le_value_of_accepted
    (C : CriticalValueWithInfinityCertificate M)
    (reports : Bidder → SingleMindedBid Item) {i : Bidder} {p : ℝ}
    (hthreshold : C.threshold reports i (reports i).desired = some p)
    (hacc : i ∈ M.accepted reports) :
    p ≤ (reports i).value := by
  by_contra hnot
  have hlt : (reports i).value < p := lt_of_not_ge hnot
  have hdeny :=
    C.below_denied reports i (reports i).desired (reports i).value p
      hthreshold hlt
  have hsame :
      Function.update reports i
        { desired := (reports i).desired, value := (reports i).value } =
        reports := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [Function.update]
    · simp [Function.update, hk]
  exact hdeny (by simpa [hsame] using hacc)

theorem value_le_threshold_of_denied
    (C : CriticalValueWithInfinityCertificate M)
    (reports : Bidder → SingleMindedBid Item) {i : Bidder} {p : ℝ}
    (hthreshold : C.threshold reports i (reports i).desired = some p)
    (hdeny : i ∉ M.accepted reports) :
    (reports i).value ≤ p := by
  by_contra hnot
  have hlt : p < (reports i).value := lt_of_not_ge hnot
  have hacc :=
    C.above_granted reports i (reports i).desired (reports i).value p
      hthreshold hlt
  have hsame :
      Function.update reports i
        { desired := (reports i).desired, value := (reports i).value } =
        reports := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [Function.update]
    · simp [Function.update, hk]
  exact hdeny (by simpa [hsame] using hacc)

end CriticalValueWithInfinityCertificate

theorem utility_nonneg_truthful_of_infinity_certificate
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hpart : M.Participation)
    (C : CriticalValueWithInfinityCertificate M)
    (values : Bidder → SingleMindedBid Item)
    (hvalues : NonnegativeNonemptyProfile values) (i : Bidder) :
    0 ≤ M.utility values values i := by
  by_cases hacc : i ∈ M.accepted values
  · rcases C.payment_eq_of_accepted values i hacc with
      ⟨p, hp, hpay⟩
    have hthreshold_le :
        p ≤ (values i).value :=
      C.threshold_le_value_of_accepted values hp hacc
    have hval :
        (values i).valuation (M.allocation values i) = (values i).value := by
      simp [allocation, singleMindedAllocation, hacc,
        SingleMindedBid.valuation_of_contains]
    simp [utility, hval, hpay]
    linarith
  · have hpay := hpart values i hacc
    have hval :
        (values i).valuation (M.allocation values i) = 0 := by
      have hempty :=
        SingleMindedBid.valuation_empty_eq_zero_of_nonempty
          (values i) (hvalues i).1
      simpa [allocation, singleMindedAllocation, hacc] using hempty
    simp [utility, hval, hpay]

/--
Truthfulness criterion with an infinite critical-value branch represented by
`none`. Exactness is represented by the accepted-set allocation model.
-/
theorem truthfulOn_of_monotonicity_participation_infinity_critical
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hmono : M.Monotonicity)
    (hpart : M.Participation)
    (C : CriticalValueWithInfinityCertificate M) :
    M.TruthfulOn NonnegativeNonemptyProfile := by
  intro values hvalues i report _hreport
  let reports' := Function.update values i report
  have htruth_nonneg :
      0 ≤ M.utility values values i :=
    utility_nonneg_truthful_of_infinity_certificate M hpart C values hvalues i
  by_cases hmis : i ∈ M.accepted reports'
  · rcases C.payment_eq_of_accepted reports' i hmis with
      ⟨p, hp_report, hpay_mis⟩
    have hp_values :
        C.threshold values i report.desired = some p := by
      have hind :=
        C.threshold_own_value_independent values i report.desired report.value
      simpa [reports', Function.update, hind] using hp_report
    by_cases hsub : (values i).desired ⊆ report.desired
    · rcases C.finite_threshold_mono_of_monotone hmono values i hsub
          hp_values with
        ⟨q, hq_values, hq_le_p⟩
      have hval_mis :
          (values i).valuation (M.allocation reports' i) =
            (values i).value := by
        have hreports_i : reports' i = report := by
          simp [reports']
        rw [allocation, singleMindedAllocation, if_pos hmis, hreports_i]
        exact SingleMindedBid.valuation_of_contains (values i) hsub
      by_cases htruth : i ∈ M.accepted values
      · rcases C.payment_eq_of_accepted values i htruth with
          ⟨qpay, hqpay_values, hpay_truth⟩
        have hqpay_eq : qpay = q := by
          rw [hq_values] at hqpay_values
          injection hqpay_values with hqeq
          exact hqeq.symm
        have hpay_truth_q : M.payment values i = q := by
          simpa [hqpay_eq] using hpay_truth
        have hval_truth :
            (values i).valuation (M.allocation values i) =
              (values i).value := by
          simp [allocation, singleMindedAllocation, htruth,
            SingleMindedBid.valuation_of_contains]
        simp [utility, hval_truth, hpay_truth_q]
        linarith
      · have hvalue_le_q :
            (values i).value ≤ q :=
          C.value_le_threshold_of_denied values hq_values htruth
        have hpay_truth := hpart values i htruth
        have hval_truth :
            (values i).valuation (M.allocation values i) = 0 := by
          have hempty :=
            SingleMindedBid.valuation_empty_eq_zero_of_nonempty
              (values i) (hvalues i).1
          simpa [allocation, singleMindedAllocation, htruth] using hempty
        simp [utility, hval_truth, hpay_truth]
        linarith
    · have hval_mis :
          (values i).valuation (M.allocation reports' i) = 0 := by
        have hreports_i : reports' i = report := by
          simp [reports']
        rw [allocation, singleMindedAllocation, if_pos hmis, hreports_i]
        exact SingleMindedBid.valuation_of_not_contains (values i) hsub
      have hpay_nonneg :
          0 ≤ M.payment reports' i := by
        rw [hpay_mis]
        exact C.threshold_nonneg values i report.desired p hp_values
      have hmis_nonpos :
          M.utility values reports' i ≤ 0 := by
        simp [utility, hval_mis]
        linarith
      exact hmis_nonpos.trans htruth_nonneg
  · have hpay_mis := hpart reports' i hmis
    have hval_mis :
        (values i).valuation (M.allocation reports' i) = 0 := by
      have hempty :=
        SingleMindedBid.valuation_empty_eq_zero_of_nonempty
          (values i) (hvalues i).1
      simpa [allocation, singleMindedAllocation, hmis] using hempty
    have hmis_zero :
        M.utility values reports' i = 0 := by
      simp [utility, hval_mis, hpay_mis]
    rw [hmis_zero]
    exact htruth_nonneg

/-- Updating one bidder to a nonempty, nonnegative single-minded report preserves
the nonempty/nonnegative profile domain. -/
theorem nonnegativeNonemptyProfile_update
    [DecidableEq Bidder] [DecidableEq Item]
    (reports : Bidder → SingleMindedBid Item)
    (hreports : NonnegativeNonemptyProfile reports)
    (i : Bidder) {s : Bundle Item} {v : ℝ}
    (hs : s.Nonempty) (hv : 0 ≤ v) :
    NonnegativeNonemptyProfile
      (Function.update reports i { desired := s, value := v }) := by
  intro k
  by_cases hk : k = i
  · subst k
    simp [Function.update, hs, hv]
  · simpa [Function.update, hk] using hreports k

/--
Threshold existence on the source domain. For a fixed nonempty
desired bundle, monotonicity implies either a finite nonnegative critical value
with strict below/above behavior, or an infinite branch where no nonnegative
declared value wins.

This constructs the acceptance threshold only; payment equality to that
threshold is the separate Critical axiom used in the single-minded truthfulness criterion.
-/
theorem exists_nonnegative_critical_value_of_monotonicityOn
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hmono : M.MonotonicityOn NonnegativeNonemptyProfile)
    (reports : Bidder → SingleMindedBid Item)
    (hreports : NonnegativeNonemptyProfile reports)
    (i : Bidder) (s : Bundle Item) (hs : s.Nonempty) :
    (∃ c : ℝ,
      0 ≤ c ∧
        (∀ v, 0 ≤ v → v < c →
          i ∉ M.accepted
            (Function.update reports i { desired := s, value := v })) ∧
        (∀ v, 0 ≤ v → c < v →
          i ∈ M.accepted
            (Function.update reports i { desired := s, value := v }))) ∨
      (∀ v, 0 ≤ v →
        i ∉ M.accepted
          (Function.update reports i { desired := s, value := v })) := by
  let acceptedValues : Set ℝ :=
    {v | 0 ≤ v ∧
      i ∈ M.accepted
        (Function.update reports i { desired := s, value := v })}
  by_cases hnonempty : acceptedValues.Nonempty
  · have hbdd : BddBelow acceptedValues :=
      ⟨0, by
        intro v hv
        exact hv.1⟩
    let c : ℝ := sInf acceptedValues
    have hc_nonneg : 0 ≤ c := by
      exact le_csInf hnonempty (by intro v hv; exact hv.1)
    left
    refine ⟨c, hc_nonneg, ?_, ?_⟩
    · intro v hv_nonneg hvc hacc
      have hv_mem : v ∈ acceptedValues := ⟨hv_nonneg, hacc⟩
      have hcv : c ≤ v := csInf_le hbdd hv_mem
      linarith
    · intro v hv_nonneg hcv
      rcases (csInf_lt_iff hbdd hnonempty).1 hcv with
        ⟨u, hu_mem, huv⟩
      have hu_nonneg : 0 ≤ u := hu_mem.1
      have hu_acc :
          i ∈ M.accepted
            (Function.update reports i { desired := s, value := u }) :=
        hu_mem.2
      have hu_profile :
          NonnegativeNonemptyProfile
            (Function.update reports i { desired := s, value := u }) :=
        nonnegativeNonemptyProfile_update reports hreports i hs hu_nonneg
      have hv_profile_update :
          NonnegativeNonemptyProfile
            (Function.update
              (Function.update reports i { desired := s, value := u })
              i { desired := s, value := v }) :=
        nonnegativeNonemptyProfile_update
          (Function.update reports i { desired := s, value := u })
          hu_profile i hs hv_nonneg
      have hv_acc_update :
          i ∈ M.accepted
            (Function.update
              (Function.update reports i { desired := s, value := u })
              i { desired := s, value := v }) := by
        exact hmono
          (Function.update reports i { desired := s, value := u })
          hu_profile i s v hu_acc hv_profile_update
          (by simp [Function.update])
          (by simpa [Function.update] using le_of_lt huv)
      simpa [Function.update] using hv_acc_update
  · right
    intro v hv_nonneg hacc
    exact hnonempty ⟨v, hv_nonneg, hacc⟩

/--
Critical-value data for the nonnegative single-minded report domain. The
finite and infinite threshold clauses only need to govern admissible
nonnegative reports, matching the type-space restriction and avoiding
forcing negative-value behavior that is irrelevant for truthfulness on this
domain.
-/
structure NonnegativeCriticalValueWithInfinityCertificate
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item) where
  threshold : (Bidder → SingleMindedBid Item) → Bidder → Bundle Item → Option ℝ
  threshold_nonneg :
    ∀ reports,
      NonnegativeNonemptyProfile reports →
        ∀ i s p, s.Nonempty → threshold reports i s = some p → 0 ≤ p
  threshold_own_value_independent :
    ∀ reports,
      NonnegativeNonemptyProfile reports →
        ∀ i s v,
          s.Nonempty →
            0 ≤ v →
              threshold
                  (Function.update reports i { desired := s, value := v }) i s =
                threshold reports i s
  below_denied :
    ∀ reports,
      NonnegativeNonemptyProfile reports →
        ∀ i s v p,
          s.Nonempty →
            0 ≤ v →
              threshold reports i s = some p →
                v < p →
                  i ∉ M.accepted
                    (Function.update reports i { desired := s, value := v })
  above_granted :
    ∀ reports,
      NonnegativeNonemptyProfile reports →
        ∀ i s v p,
          s.Nonempty →
            0 ≤ v →
              threshold reports i s = some p →
                p < v →
                  i ∈ M.accepted
                    (Function.update reports i { desired := s, value := v })
  infinite_denied :
    ∀ reports,
      NonnegativeNonemptyProfile reports →
        ∀ i s v,
          s.Nonempty →
            0 ≤ v →
              threshold reports i s = none →
                i ∉ M.accepted
                  (Function.update reports i { desired := s, value := v })
  payment_eq_of_accepted :
    ∀ reports,
      NonnegativeNonemptyProfile reports →
        ∀ i,
          i ∈ M.accepted reports →
            ∃ p,
              threshold reports i (reports i).desired = some p ∧
                M.payment reports i = p

namespace NonnegativeCriticalValueWithInfinityCertificate

variable [DecidableEq Bidder] [DecidableEq Item]
    {M : SingleMindedAcceptedMechanism Bidder Item}

/--
Finite thresholds remain monotone in the bundle order on the nonnegative domain,
even when smaller bundles may have infinite critical value a priori.
-/
theorem finite_threshold_mono_of_monotone
    (C : NonnegativeCriticalValueWithInfinityCertificate M)
    (hmono : M.MonotonicityOn NonnegativeNonemptyProfile)
    (reports : Bidder → SingleMindedBid Item)
    (hreports : NonnegativeNonemptyProfile reports) (i : Bidder)
    {sSmall sLarge : Bundle Item} {pLarge : ℝ}
    (hsSmall : sSmall.Nonempty) (hsLarge : sLarge.Nonempty)
    (hsub : sSmall ⊆ sLarge)
    (hLarge : C.threshold reports i sLarge = some pLarge) :
    ∃ pSmall,
      C.threshold reports i sSmall = some pSmall ∧ pSmall ≤ pLarge := by
  have hpLarge_nonneg : 0 ≤ pLarge :=
    C.threshold_nonneg reports hreports i sLarge pLarge hsLarge hLarge
  cases hSmall : C.threshold reports i sSmall with
  | none =>
      let x : ℝ := pLarge + 1
      have hx_nonneg : 0 ≤ x := by
        dsimp [x]
        linarith
      have hlarge_x : pLarge < x := by
        dsimp [x]
        linarith
      have hlarge_acc :
          i ∈ M.accepted
            (Function.update reports i { desired := sLarge, value := x }) :=
        C.above_granted reports hreports i sLarge x pLarge
          hsLarge hx_nonneg hLarge hlarge_x
      have hlarge_profile :
          NonnegativeNonemptyProfile
            (Function.update reports i { desired := sLarge, value := x }) :=
        nonnegativeNonemptyProfile_update reports hreports i hsLarge hx_nonneg
      have hsmall_profile_update :
          NonnegativeNonemptyProfile
            (Function.update
              (Function.update reports i { desired := sLarge, value := x })
              i { desired := sSmall, value := x }) :=
        nonnegativeNonemptyProfile_update
          (Function.update reports i { desired := sLarge, value := x })
          hlarge_profile i hsSmall hx_nonneg
      have hsmall_acc_update :
          i ∈ M.accepted
            (Function.update
              (Function.update reports i { desired := sLarge, value := x })
              i { desired := sSmall, value := x }) := by
        exact hmono
          (Function.update reports i { desired := sLarge, value := x })
          hlarge_profile i sSmall x hlarge_acc hsmall_profile_update
          (by simpa [Function.update] using hsub)
          (by simp [Function.update])
      have hsmall_acc :
          i ∈ M.accepted
            (Function.update reports i { desired := sSmall, value := x }) := by
        simpa [Function.update] using hsmall_acc_update
      exact False.elim
        ((C.infinite_denied reports hreports i sSmall x hsSmall hx_nonneg hSmall)
          hsmall_acc)
  | some pSmall =>
      have hpSmall_nonneg : 0 ≤ pSmall :=
        C.threshold_nonneg reports hreports i sSmall pSmall hsSmall hSmall
      refine ⟨pSmall, rfl, ?_⟩
      by_contra hnot
      have hlt : pLarge < pSmall := lt_of_not_ge hnot
      let x : ℝ := (pLarge + pSmall) / 2
      have hx_nonneg : 0 ≤ x := by
        dsimp [x]
        linarith
      have hlarge_x : pLarge < x := by
        dsimp [x]
        linarith
      have hx_small : x < pSmall := by
        dsimp [x]
        linarith
      have hlarge_acc :
          i ∈ M.accepted
            (Function.update reports i { desired := sLarge, value := x }) :=
        C.above_granted reports hreports i sLarge x pLarge
          hsLarge hx_nonneg hLarge hlarge_x
      have hlarge_profile :
          NonnegativeNonemptyProfile
            (Function.update reports i { desired := sLarge, value := x }) :=
        nonnegativeNonemptyProfile_update reports hreports i hsLarge hx_nonneg
      have hsmall_profile_update :
          NonnegativeNonemptyProfile
            (Function.update
              (Function.update reports i { desired := sLarge, value := x })
              i { desired := sSmall, value := x }) :=
        nonnegativeNonemptyProfile_update
          (Function.update reports i { desired := sLarge, value := x })
          hlarge_profile i hsSmall hx_nonneg
      have hsmall_acc_update :
          i ∈ M.accepted
            (Function.update
              (Function.update reports i { desired := sLarge, value := x })
              i { desired := sSmall, value := x }) := by
        exact hmono
          (Function.update reports i { desired := sLarge, value := x })
          hlarge_profile i sSmall x hlarge_acc hsmall_profile_update
          (by simpa [Function.update] using hsub)
          (by simp [Function.update])
      have hsmall_acc :
          i ∈ M.accepted
            (Function.update reports i { desired := sSmall, value := x }) := by
        simpa [Function.update] using hsmall_acc_update
      exact
        (C.below_denied reports hreports i sSmall x pSmall
          hsSmall hx_nonneg hSmall hx_small) hsmall_acc

theorem threshold_le_value_of_accepted
    (C : NonnegativeCriticalValueWithInfinityCertificate M)
    (reports : Bidder → SingleMindedBid Item)
    (hreports : NonnegativeNonemptyProfile reports) {i : Bidder} {p : ℝ}
    (hthreshold : C.threshold reports i (reports i).desired = some p)
    (hacc : i ∈ M.accepted reports) :
    p ≤ (reports i).value := by
  by_contra hnot
  have hlt : (reports i).value < p := lt_of_not_ge hnot
  have hdeny :=
    C.below_denied reports hreports i (reports i).desired (reports i).value p
      (hreports i).1 (hreports i).2 hthreshold hlt
  have hsame :
      Function.update reports i
        { desired := (reports i).desired, value := (reports i).value } =
        reports := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [Function.update]
    · simp [Function.update, hk]
  exact hdeny (by simpa [hsame] using hacc)

theorem value_le_threshold_of_denied
    (C : NonnegativeCriticalValueWithInfinityCertificate M)
    (reports : Bidder → SingleMindedBid Item)
    (hreports : NonnegativeNonemptyProfile reports) {i : Bidder} {p : ℝ}
    (hthreshold : C.threshold reports i (reports i).desired = some p)
    (hdeny : i ∉ M.accepted reports) :
    (reports i).value ≤ p := by
  by_contra hnot
  have hlt : p < (reports i).value := lt_of_not_ge hnot
  have hacc :=
    C.above_granted reports hreports i (reports i).desired (reports i).value p
      (hreports i).1 (hreports i).2 hthreshold hlt
  have hsame :
      Function.update reports i
        { desired := (reports i).desired, value := (reports i).value } =
        reports := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [Function.update]
    · simp [Function.update, hk]
  exact hdeny (by simpa [hsame] using hacc)

end NonnegativeCriticalValueWithInfinityCertificate

theorem utility_nonneg_truthful_of_nonnegative_infinity_certificate
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hpart : M.Participation)
    (C : NonnegativeCriticalValueWithInfinityCertificate M)
    (values : Bidder → SingleMindedBid Item)
    (hvalues : NonnegativeNonemptyProfile values) (i : Bidder) :
    0 ≤ M.utility values values i := by
  by_cases hacc : i ∈ M.accepted values
  · rcases C.payment_eq_of_accepted values hvalues i hacc with
      ⟨p, hp, hpay⟩
    have hthreshold_le :
        p ≤ (values i).value :=
      C.threshold_le_value_of_accepted values hvalues hp hacc
    have hval :
        (values i).valuation (M.allocation values i) = (values i).value := by
      simp [allocation, singleMindedAllocation, hacc,
        SingleMindedBid.valuation_of_contains]
    simp [utility, hval, hpay]
    linarith
  · have hpay := hpart values i hacc
    have hval :
        (values i).valuation (M.allocation values i) = 0 := by
      have hempty :=
        SingleMindedBid.valuation_empty_eq_zero_of_nonempty
          (values i) (hvalues i).1
      simpa [allocation, singleMindedAllocation, hacc] using hempty
    simp [utility, hval, hpay]

/--
Domain-aware truthfulness criterion. Critical-value clauses are only required
on the nonempty, nonnegative single-minded report domain, while exactness is
still represented by the accepted-set allocation model.
-/
theorem truthfulOn_of_monotonicityOn_participation_nonnegative_infinity_critical
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hmono : M.MonotonicityOn NonnegativeNonemptyProfile)
    (hpart : M.Participation)
    (C : NonnegativeCriticalValueWithInfinityCertificate M) :
    M.TruthfulOn NonnegativeNonemptyProfile := by
  intro values hvalues i report hreport
  let reports' := Function.update values i report
  have htruth_nonneg :
      0 ≤ M.utility values values i :=
    utility_nonneg_truthful_of_nonnegative_infinity_certificate
      M hpart C values hvalues i
  by_cases hmis : i ∈ M.accepted reports'
  · rcases C.payment_eq_of_accepted reports' hreport i hmis with
      ⟨p, hp_report, hpay_mis⟩
    have hp_values :
        C.threshold values i report.desired = some p := by
      have hreport_nonempty : report.desired.Nonempty := by
        simpa [reports', Function.update] using (hreport i).1
      have hreport_nonneg : 0 ≤ report.value := by
        simpa [reports', Function.update] using (hreport i).2
      have hind :=
        C.threshold_own_value_independent values hvalues i report.desired
          report.value hreport_nonempty hreport_nonneg
      simpa [reports', Function.update, hind] using hp_report
    by_cases hsub : (values i).desired ⊆ report.desired
    · have hreport_nonempty : report.desired.Nonempty := by
        simpa [reports', Function.update] using (hreport i).1
      rcases C.finite_threshold_mono_of_monotone hmono values hvalues i
          (hvalues i).1 hreport_nonempty hsub hp_values with
        ⟨q, hq_values, hq_le_p⟩
      have hval_mis :
          (values i).valuation (M.allocation reports' i) =
            (values i).value := by
        have hreports_i : reports' i = report := by
          simp [reports']
        rw [allocation, singleMindedAllocation, if_pos hmis, hreports_i]
        exact SingleMindedBid.valuation_of_contains (values i) hsub
      by_cases htruth : i ∈ M.accepted values
      · rcases C.payment_eq_of_accepted values hvalues i htruth with
          ⟨qpay, hqpay_values, hpay_truth⟩
        have hqpay_eq : qpay = q := by
          rw [hq_values] at hqpay_values
          injection hqpay_values with hqeq
          exact hqeq.symm
        have hpay_truth_q : M.payment values i = q := by
          simpa [hqpay_eq] using hpay_truth
        have hval_truth :
            (values i).valuation (M.allocation values i) =
              (values i).value := by
          simp [allocation, singleMindedAllocation, htruth,
            SingleMindedBid.valuation_of_contains]
        simp [utility, hval_truth, hpay_truth_q]
        linarith
      · have hvalue_le_q :
            (values i).value ≤ q :=
          C.value_le_threshold_of_denied values hvalues hq_values htruth
        have hpay_truth := hpart values i htruth
        have hval_truth :
            (values i).valuation (M.allocation values i) = 0 := by
          have hempty :=
            SingleMindedBid.valuation_empty_eq_zero_of_nonempty
              (values i) (hvalues i).1
          simpa [allocation, singleMindedAllocation, htruth] using hempty
        simp [utility, hval_truth, hpay_truth]
        linarith
    · have hval_mis :
          (values i).valuation (M.allocation reports' i) = 0 := by
        have hreports_i : reports' i = report := by
          simp [reports']
        rw [allocation, singleMindedAllocation, if_pos hmis, hreports_i]
        exact SingleMindedBid.valuation_of_not_contains (values i) hsub
      have hpay_nonneg :
          0 ≤ M.payment reports' i := by
        rw [hpay_mis]
        have hreport_nonempty : report.desired.Nonempty := by
          simpa [reports', Function.update] using (hreport i).1
        exact C.threshold_nonneg values hvalues i report.desired p
          hreport_nonempty hp_values
      have hmis_nonpos :
          M.utility values reports' i ≤ 0 := by
        simp [utility, hval_mis]
        linarith
      exact hmis_nonpos.trans htruth_nonneg
  · have hpay_mis := hpart reports' i hmis
    have hval_mis :
        (values i).valuation (M.allocation reports' i) = 0 := by
      have hempty :=
        SingleMindedBid.valuation_empty_eq_zero_of_nonempty
          (values i) (hvalues i).1
      simpa [allocation, singleMindedAllocation, hmis] using hempty
    have hmis_zero :
        M.utility values reports' i = 0 := by
      simp [utility, hval_mis, hpay_mis]
    rw [hmis_zero]
    exact htruth_nonneg

theorem truthfulOn_of_monotonicity_participation_nonnegative_infinity_critical
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hmono : M.Monotonicity)
    (hpart : M.Participation)
    (C : NonnegativeCriticalValueWithInfinityCertificate M) :
    M.TruthfulOn NonnegativeNonemptyProfile := by
  exact
    truthfulOn_of_monotonicityOn_participation_nonnegative_infinity_critical
      M (monotonicityOn_of_monotonicity M NonnegativeNonemptyProfile hmono)
      hpart C

end SingleMindedAcceptedMechanism

/-! ## Greedy single-minded auction approximation support -/

namespace SingleMindedBid

variable [DecidableEq Item]

/-- The size of a single-minded desired bundle, as a real number. -/
def bundleSize (b : SingleMindedBid Item) : ℝ :=
  (b.desired.card : ℝ)

/-- Average amount per good, `a / |s|`. -/
noncomputable def averageAmountPerGood (b : SingleMindedBid Item) : ℝ :=
  b.value / b.bundleSize

/-- The square-root bid norm `a / sqrt(|s|)`. -/
noncomputable def sqrtAmountNorm (b : SingleMindedBid Item) : ℝ :=
  b.value / Real.sqrt b.bundleSize

theorem bundleSize_pos_of_nonempty (b : SingleMindedBid Item)
    (hb : b.desired.Nonempty) :
    0 < b.bundleSize := by
  dsimp [bundleSize]
  exact_mod_cast Finset.card_pos.mpr hb

theorem averageAmountPerGood_lt_of_value_lt_bundleSize_mul
    (b n : SingleMindedBid Item) (hb : b.desired.Nonempty)
    (hlt : b.value < b.bundleSize * n.averageAmountPerGood) :
    b.averageAmountPerGood < n.averageAmountPerGood := by
  have hsize_pos : 0 < b.bundleSize := b.bundleSize_pos_of_nonempty hb
  rw [averageAmountPerGood, div_lt_iff₀ hsize_pos]
  simpa [mul_comm] using hlt

theorem averageAmountPerGood_lt_of_bundleSize_mul_lt_value
    (b n : SingleMindedBid Item) (hb : b.desired.Nonempty)
    (hlt : b.bundleSize * n.averageAmountPerGood < b.value) :
    n.averageAmountPerGood < b.averageAmountPerGood := by
  have hsize_pos : 0 < b.bundleSize := b.bundleSize_pos_of_nonempty hb
  change n.averageAmountPerGood < b.value / b.bundleSize
  rw [lt_div_iff₀ hsize_pos]
  simpa [mul_comm] using hlt

/--
On the nonnegative domain, shrinking a nonempty desired bundle while weakly
increasing value weakly increases the average amount per good.
-/
theorem averageAmountPerGood_le_of_subset_value_le
    (b : SingleMindedBid Item) {s : Bundle Item} {v : ℝ}
    (hb_nonempty : b.desired.Nonempty) (hs : s.Nonempty)
    (hsub : s ⊆ b.desired)
    (hb_nonneg : 0 ≤ b.value) (hle : b.value ≤ v) :
    b.averageAmountPerGood ≤
      ({ desired := s, value := v } : SingleMindedBid Item).averageAmountPerGood := by
  let b' : SingleMindedBid Item := { desired := s, value := v }
  have hb_size_pos : 0 < b.bundleSize :=
    b.bundleSize_pos_of_nonempty hb_nonempty
  have hb'_size_pos : 0 < b'.bundleSize :=
    b'.bundleSize_pos_of_nonempty hs
  have hsize_le : b'.bundleSize ≤ b.bundleSize := by
    dsimp [b', bundleSize]
    exact_mod_cast Finset.card_le_card hsub
  have hv_nonneg : 0 ≤ v := le_trans hb_nonneg hle
  have hmain : b.value * b'.bundleSize ≤ v * b.bundleSize := by
    have hvalue_part : b.value * b'.bundleSize ≤ v * b'.bundleSize :=
      mul_le_mul_of_nonneg_right hle hb'_size_pos.le
    have hsize_part : v * b'.bundleSize ≤ v * b.bundleSize :=
      mul_le_mul_of_nonneg_left hsize_le hv_nonneg
    exact hvalue_part.trans hsize_part
  dsimp [averageAmountPerGood]
  rw [div_le_div_iff₀ hb_size_pos hb'_size_pos]
  simpa [b', mul_comm, mul_left_comm, mul_assoc] using hmain

theorem sqrtAmountNorm_sq_eq_value_sq_div_bundleSize
    (b : SingleMindedBid Item) (hb : b.desired.Nonempty) :
    b.sqrtAmountNorm ^ 2 = b.value ^ 2 / b.bundleSize := by
  have hsize_nonneg : 0 ≤ b.bundleSize :=
    (b.bundleSize_pos_of_nonempty hb).le
  simp [sqrtAmountNorm, div_pow, Real.sq_sqrt hsize_nonneg]

end SingleMindedBid

/-- Total declared value of a finite set of single-minded bids. -/
noncomputable def singleMindedTotalValue [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) (selected : Finset Bidder) : ℝ :=
  ∑ i ∈ selected, (bids i).value

/-- Objective value of a weighted set-packing selection. -/
noncomputable def weightedSetPackingValue [DecidableEq Bidder]
    (weights : Bidder → ℝ) (selected : Finset Bidder) : ℝ :=
  ∑ i ∈ selected, weights i

/-- The set-packing encoding preserves the objective value exactly. -/
theorem singleMindedTotalValue_setPackingSingleMindedBids
    [DecidableEq Bidder]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (selected : Finset Bidder) :
    singleMindedTotalValue
        (setPackingSingleMindedBids sets weights) selected =
      weightedSetPackingValue weights selected := by
  simp [singleMindedTotalValue, weightedSetPackingValue,
    setPackingSingleMindedBids]

/-- Optimal selections for weighted set packing. -/
def WeightedSetPackingOptimal [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (selected : Finset Bidder) : Prop :=
  SetPackingFeasible sets selected ∧
    ∀ other, SetPackingFeasible sets other →
      weightedSetPackingValue weights other ≤ weightedSetPackingValue weights selected

/-- Optimal accepted sets for the single-minded welfare-maximization problem. -/
def SingleMindedOptimalAcceptedSet [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (selected : Finset Bidder) : Prop :=
  PairwiseDisjointDesired bids selected ∧
    ∀ other, PairwiseDisjointDesired bids other →
      singleMindedTotalValue bids other ≤ singleMindedTotalValue bids selected

/-- A weighted set-packing selection with value at least `factor` times optimum. -/
def WeightedSetPackingApproximationAtLeast
    [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (factor : ℝ) (selected : Finset Bidder) : Prop :=
  SetPackingFeasible sets selected ∧
    ∀ optimal, WeightedSetPackingOptimal sets weights optimal →
      factor * weightedSetPackingValue weights optimal ≤
        weightedSetPackingValue weights selected

/--
A single-minded accepted set with value at least `factor` times the optimal
feasible single-minded welfare.
-/
def SingleMindedApproximationAtLeast
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (factor : ℝ) (selected : Finset Bidder) : Prop :=
  PairwiseDisjointDesired bids selected ∧
    ∀ optimal, SingleMindedOptimalAcceptedSet bids optimal →
      factor * singleMindedTotalValue bids optimal ≤
        singleMindedTotalValue bids selected

/--
Weighted set-packing optimality is exactly single-minded welfare optimality
under the set-to-bid encoding.
-/
theorem weightedSetPackingOptimal_iff_singleMindedOptimalAcceptedSet
    [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (selected : Finset Bidder) :
    WeightedSetPackingOptimal sets weights selected ↔
      SingleMindedOptimalAcceptedSet
        (setPackingSingleMindedBids sets weights) selected := by
  constructor
  · intro h
    constructor
    · exact
        (pairwiseDisjointDesired_setPackingSingleMindedBids_iff
          sets weights selected).2 h.1
    · intro other hother
      have hother_pack :
          SetPackingFeasible sets other :=
        (pairwiseDisjointDesired_setPackingSingleMindedBids_iff
          sets weights other).1 hother
      simpa [singleMindedTotalValue_setPackingSingleMindedBids] using
        h.2 other hother_pack
  · intro h
    constructor
    · exact
        (pairwiseDisjointDesired_setPackingSingleMindedBids_iff
          sets weights selected).1 h.1
    · intro other hother
      have hother_sm :
          PairwiseDisjointDesired
            (setPackingSingleMindedBids sets weights) other :=
        (pairwiseDisjointDesired_setPackingSingleMindedBids_iff
          sets weights other).2 hother
      simpa [singleMindedTotalValue_setPackingSingleMindedBids] using
        h.2 other hother_sm

/--
The set-to-bid encoding preserves any multiplicative approximation
guarantee, not only exact optimality.
-/
theorem weightedSetPackingApproximationAtLeast_iff_singleMindedApproximationAtLeast
    [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (factor : ℝ) (selected : Finset Bidder) :
    WeightedSetPackingApproximationAtLeast sets weights factor selected ↔
      SingleMindedApproximationAtLeast
        (setPackingSingleMindedBids sets weights) factor selected := by
  constructor
  · intro h
    constructor
    · exact
        (pairwiseDisjointDesired_setPackingSingleMindedBids_iff
          sets weights selected).2 h.1
    · intro optimal hoptimal
      have hoptimal_pack :
          WeightedSetPackingOptimal sets weights optimal :=
        (weightedSetPackingOptimal_iff_singleMindedOptimalAcceptedSet
          sets weights optimal).2 hoptimal
      simpa [singleMindedTotalValue_setPackingSingleMindedBids] using
        h.2 optimal hoptimal_pack
  · intro h
    constructor
    · exact
        (pairwiseDisjointDesired_setPackingSingleMindedBids_iff
          sets weights selected).1 h.1
    · intro optimal hoptimal
      have hoptimal_sm :
          SingleMindedOptimalAcceptedSet
            (setPackingSingleMindedBids sets weights) optimal :=
        (weightedSetPackingOptimal_iff_singleMindedOptimalAcceptedSet
          sets weights optimal).1 hoptimal
      simpa [singleMindedTotalValue_setPackingSingleMindedBids] using
        h.2 optimal hoptimal_sm

/-! ### Decision-problem form of the set-packing reduction -/

/-- Threshold decision instances for weighted set packing. -/
structure WeightedSetPackingDecisionInstance (Bidder Item : Type*) where
  sets : Bidder → Finset Item
  weights : Bidder → ℝ
  threshold : ℝ

/-- Threshold decision instances for single-minded welfare maximization. -/
structure SingleMindedWelfareDecisionInstance (Bidder Item : Type*) where
  bids : Bidder → SingleMindedBid Item
  threshold : ℝ

/--
Weighted set-packing decision problem: is there a feasible finite selection
whose weight is at least the threshold?
-/
noncomputable def WeightedSetPackingDecisionProblem
    [DecidableEq Bidder] [DecidableEq Item] :
    AppliedModelingLib.Complexity.DecisionProblem
      (WeightedSetPackingDecisionInstance Bidder Item) :=
  fun problem =>
    ∃ selected,
      SetPackingFeasible problem.sets selected ∧
        problem.threshold ≤ weightedSetPackingValue problem.weights selected

/--
Single-minded welfare decision problem: is there a feasible accepted set whose
declared welfare is at least the threshold?
-/
noncomputable def SingleMindedWelfareDecisionProblem
    [DecidableEq Bidder] [DecidableEq Item] :
    AppliedModelingLib.Complexity.DecisionProblem
      (SingleMindedWelfareDecisionInstance Bidder Item) :=
  fun problem =>
    ∃ selected,
      PairwiseDisjointDesired problem.bids selected ∧
        problem.threshold ≤ singleMindedTotalValue problem.bids selected

/-- The set-to-bid encoding as a map of threshold decision instances. -/
def setPackingDecisionToSingleMindedWelfareDecision
    (problem : WeightedSetPackingDecisionInstance Bidder Item) :
    SingleMindedWelfareDecisionInstance Bidder Item where
  bids := setPackingSingleMindedBids problem.sets problem.weights
  threshold := problem.threshold

/--
The set-to-bid encoding preserves the threshold decision question exactly.
-/
theorem weightedSetPackingDecisionProblem_iff_singleMindedWelfareDecisionProblem
    [DecidableEq Bidder] [DecidableEq Item]
    (problem : WeightedSetPackingDecisionInstance Bidder Item) :
    WeightedSetPackingDecisionProblem problem ↔
      SingleMindedWelfareDecisionProblem
        (setPackingDecisionToSingleMindedWelfareDecision problem) := by
  constructor
  · rintro ⟨selected, hfeasible, hvalue⟩
    refine ⟨selected, ?_, ?_⟩
    · exact
        (pairwiseDisjointDesired_setPackingSingleMindedBids_iff
          problem.sets problem.weights selected).2 hfeasible
    · simpa [setPackingDecisionToSingleMindedWelfareDecision,
        singleMindedTotalValue_setPackingSingleMindedBids] using hvalue
  · rintro ⟨selected, hfeasible, hvalue⟩
    refine ⟨selected, ?_, ?_⟩
    · exact
        (pairwiseDisjointDesired_setPackingSingleMindedBids_iff
          problem.sets problem.weights selected).1 hfeasible
    · simpa [setPackingDecisionToSingleMindedWelfareDecision,
        singleMindedTotalValue_setPackingSingleMindedBids] using hvalue

/--
The set-to-bid encoding as an abstract many-one reduction from weighted
set packing to single-minded welfare.
-/
noncomputable def weightedSetPackingDecisionProblem_manyOneReduction_singleMindedWelfareDecisionProblem
    [DecidableEq Bidder] [DecidableEq Item] :
    AppliedModelingLib.Complexity.ManyOneReduction
      (WeightedSetPackingDecisionProblem (Bidder := Bidder) (Item := Item))
      (SingleMindedWelfareDecisionProblem (Bidder := Bidder) (Item := Item)) where
  map := setPackingDecisionToSingleMindedWelfareDecision
  correct :=
    weightedSetPackingDecisionProblem_iff_singleMindedWelfareDecisionProblem

/--
If an external complexity model certifies the set-to-bid encoding as
polynomial-time, then the compiled many-one reduction upgrades to an abstract
polynomial-time reduction.
-/
noncomputable def weightedSetPackingDecisionProblem_polynomialTimeReduction_singleMindedWelfareDecisionProblem
    [DecidableEq Bidder] [DecidableEq Item]
    (PolynomialTime :
      (WeightedSetPackingDecisionInstance Bidder Item →
        SingleMindedWelfareDecisionInstance Bidder Item) → Prop)
    (hpoly :
      PolynomialTime setPackingDecisionToSingleMindedWelfareDecision) :
    AppliedModelingLib.Complexity.PolynomialTimeReduction
      (WeightedSetPackingDecisionProblem (Bidder := Bidder) (Item := Item))
      (SingleMindedWelfareDecisionProblem (Bidder := Bidder) (Item := Item)) where
  reduction :=
    weightedSetPackingDecisionProblem_manyOneReduction_singleMindedWelfareDecisionProblem
  PolynomialTime := PolynomialTime
  polynomialTime := hpoly

/-- A solver that returns an optimal weighted set-packing selection. -/
def WeightedSetPackingOptimalSolver
    [DecidableEq Bidder] [DecidableEq Item]
    (solver :
      (Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) : Prop :=
  ∀ sets weights, WeightedSetPackingOptimal sets weights (solver sets weights)

/-- A solver that returns an optimal single-minded accepted set. -/
def SingleMindedOptimalSolver
    [DecidableEq Bidder] [DecidableEq Item]
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder) : Prop :=
  ∀ bids, SingleMindedOptimalAcceptedSet bids (solver bids)

/-- Convert any single-minded welfare solver into a weighted set-packing solver. -/
def setPackingSolverOfSingleMindedSolver
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder)
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ) : Finset Bidder :=
  solver (setPackingSingleMindedBids sets weights)

/--
Any exact solver for single-minded welfare maximization induces an exact solver
for weighted set packing via the source encoding.
-/
theorem weightedSetPackingOptimalSolver_of_singleMindedOptimalSolver
    [DecidableEq Bidder] [DecidableEq Item]
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder)
    (hsolver : SingleMindedOptimalSolver solver) :
    WeightedSetPackingOptimalSolver
      (setPackingSolverOfSingleMindedSolver solver) := by
  intro sets weights
  exact
    (weightedSetPackingOptimal_iff_singleMindedOptimalAcceptedSet
      sets weights
      (setPackingSolverOfSingleMindedSolver solver sets weights)).2
      (hsolver (setPackingSingleMindedBids sets weights))

/-- A weighted set-packing solver with a uniform multiplicative guarantee. -/
def WeightedSetPackingApproximationSolverAtLeast
    [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (solver :
      (Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) : Prop :=
  ∀ sets weights,
    WeightedSetPackingApproximationAtLeast sets weights factor
      (solver sets weights)

/-- A single-minded welfare solver with a uniform multiplicative guarantee. -/
def SingleMindedApproximationSolverAtLeast
    [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder) : Prop :=
  ∀ bids, SingleMindedApproximationAtLeast bids factor (solver bids)

/--
Any approximation solver for single-minded welfare maximization induces a
weighted set-packing approximation solver with the same factor.
-/
theorem weightedSetPackingApproximationSolverAtLeast_of_singleMindedApproximationSolverAtLeast
    [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder)
    (hsolver : SingleMindedApproximationSolverAtLeast factor solver) :
    WeightedSetPackingApproximationSolverAtLeast factor
      (setPackingSolverOfSingleMindedSolver solver) := by
  intro sets weights
  exact
    (weightedSetPackingApproximationAtLeast_iff_singleMindedApproximationAtLeast
      sets weights factor
      (setPackingSolverOfSingleMindedSolver solver sets weights)).2
      (hsolver (setPackingSingleMindedBids sets weights))

/-! ### Graph-incidence reduction for set packing -/

variable {Vertex : Type*}

/-- A finite selected set of graph vertices is independent. -/
def GraphIndependentSelection
    (G : SimpleGraph Vertex) (selected : Finset Vertex) : Prop :=
  ∀ ⦃u v : Vertex⦄,
    u ∈ selected → v ∈ selected → u ≠ v → ¬ G.Adj u v

/-- Maximum independent sets, stated by cardinality. -/
def MaximumIndependentSelection
    (G : SimpleGraph Vertex) (selected : Finset Vertex) : Prop :=
  GraphIndependentSelection G selected ∧
    ∀ other, GraphIndependentSelection G other → other.card ≤ selected.card

/-- A finite selected set of graph vertices is a clique. -/
def GraphCliqueSelection
    (G : SimpleGraph Vertex) (selected : Finset Vertex) : Prop :=
  ∀ ⦃u v : Vertex⦄,
    u ∈ selected → v ∈ selected → u ≠ v → G.Adj u v

/-- Maximum cliques, stated by cardinality. -/
def MaximumCliqueSelection
    (G : SimpleGraph Vertex) (selected : Finset Vertex) : Prop :=
  GraphCliqueSelection G selected ∧
    ∀ other, GraphCliqueSelection G other → other.card ≤ selected.card

/--
The set-packing instance whose goods are graph edges and whose requested set for
a vertex is the set of edges incident to that vertex.
-/
noncomputable def graphIncidentSets
    [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj] :
    Vertex → Finset (Sym2 Vertex) :=
  fun v => G.incidenceFinset v

/-- Unit weights for graph vertices, used to encode maximum independent set. -/
def graphUnitWeights (Vertex : Type*) : Vertex → ℝ :=
  fun _ => 1

/--
Cliques in a graph are exactly independent sets in its complement.
-/
theorem graphCliqueSelection_iff_graphIndependentSelection_compl
    (G : SimpleGraph Vertex) (selected : Finset Vertex) :
    GraphCliqueSelection G selected ↔
      GraphIndependentSelection Gᶜ selected := by
  constructor
  · intro hclique u v hu hv hne hadj_compl
    have hnot_adj : ¬ G.Adj u v :=
      ((SimpleGraph.compl_adj G u v).1 hadj_compl).2
    exact hnot_adj (hclique hu hv hne)
  · intro hind u v hu hv hne
    classical
    by_contra hnot_adj
    have hadj_compl : Gᶜ.Adj u v :=
      (SimpleGraph.compl_adj G u v).2 ⟨hne, hnot_adj⟩
    exact hind hu hv hne hadj_compl

/--
Maximum cliques in a graph are exactly maximum independent sets in its
complement.
-/
theorem maximumCliqueSelection_iff_maximumIndependentSelection_compl
    (G : SimpleGraph Vertex) (selected : Finset Vertex) :
    MaximumCliqueSelection G selected ↔
      MaximumIndependentSelection Gᶜ selected := by
  constructor
  · intro h
    constructor
    · exact
        (graphCliqueSelection_iff_graphIndependentSelection_compl
          G selected).1 h.1
    · intro other hother
      exact h.2 other
        ((graphCliqueSelection_iff_graphIndependentSelection_compl
          G other).2 hother)
  · intro h
    constructor
    · exact
        (graphCliqueSelection_iff_graphIndependentSelection_compl
          G selected).2 h.1
    · intro other hother
      exact h.2 other
        ((graphCliqueSelection_iff_graphIndependentSelection_compl
          G other).1 hother)

/--
Graph independent sets are exactly feasible set-packing selections under the
graph-incidence encoding.
-/
theorem setPackingFeasible_graphIncidentSets_iff_graphIndependentSelection
    [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    SetPackingFeasible (graphIncidentSets G) selected ↔
      GraphIndependentSelection G selected := by
  constructor
  · intro hfeas u v hu hv hne hadj
    have hdisj : Disjoint (graphIncidentSets G u) (graphIncidentSets G v) :=
      hfeas hu hv hne
    have hleft : s(u, v) ∈ graphIncidentSets G u := by
      simp [graphIncidentSets, hadj]
    have hright : s(u, v) ∈ graphIncidentSets G v := by
      simp [graphIncidentSets, SimpleGraph.mk'_mem_incidenceSet_right_iff, hadj]
    exact (Finset.disjoint_left.mp hdisj) hleft hright
  · intro hind u v hu hv hne
    refine Finset.disjoint_left.mpr ?_
    intro e he_u he_v
    have he_u_set : e ∈ G.incidenceSet u := by
      simpa [graphIncidentSets] using he_u
    have he_v_set : e ∈ G.incidenceSet v := by
      simpa [graphIncidentSets] using he_v
    have heq : e = s(u, v) :=
      G.incidenceSet_inter_incidenceSet_subset hne ⟨he_u_set, he_v_set⟩
    have hedge : s(u, v) ∈ G.edgeSet := by
      simpa [heq] using he_u_set.1
    have hadj : G.Adj u v := by
      simpa using (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).1 hedge
    exact hind hu hv hne hadj

/-- Unit-weight graph set-packing value is selected-set cardinality. -/
theorem weightedSetPackingValue_graphUnitWeights
    [DecidableEq Vertex] (selected : Finset Vertex) :
    weightedSetPackingValue (graphUnitWeights Vertex) selected =
      (selected.card : ℝ) := by
  simp [weightedSetPackingValue, graphUnitWeights]

/-! ### Graph decision-problem reductions -/

/-- Threshold decision instances for graph independent set. -/
structure GraphIndependentSetDecisionInstance (Vertex : Type*) where
  graph : SimpleGraph Vertex
  threshold : ℝ

/-- Threshold decision instances for graph clique. -/
structure GraphCliqueDecisionInstance (Vertex : Type*) where
  graph : SimpleGraph Vertex
  threshold : ℝ

/-- Graph independent-set threshold decision problem. -/
def GraphIndependentSetDecisionProblem :
    AppliedModelingLib.Complexity.DecisionProblem
      (GraphIndependentSetDecisionInstance Vertex) :=
  fun problem =>
    ∃ selected,
      GraphIndependentSelection problem.graph selected ∧
        problem.threshold ≤ (selected.card : ℝ)

/-- Graph clique threshold decision problem. -/
def GraphCliqueDecisionProblem :
    AppliedModelingLib.Complexity.DecisionProblem
      (GraphCliqueDecisionInstance Vertex) :=
  fun problem =>
    ∃ selected,
      GraphCliqueSelection problem.graph selected ∧
        problem.threshold ≤ (selected.card : ℝ)

/-- Reduce clique to independent set by taking the graph complement. -/
def graphCliqueDecisionToIndependentSetComplementDecision
    (problem : GraphCliqueDecisionInstance Vertex) :
    GraphIndependentSetDecisionInstance Vertex where
  graph := problem.graphᶜ
  threshold := problem.threshold

/-- Encode graph independent set as edge-incidence weighted set packing. -/
noncomputable def graphIndependentSetDecisionToWeightedSetPackingDecision
    [Fintype Vertex] [DecidableEq Vertex]
    (problem : GraphIndependentSetDecisionInstance Vertex) :
    WeightedSetPackingDecisionInstance Vertex (Sym2 Vertex) := by
  classical
  exact {
    sets := graphIncidentSets problem.graph
    weights := graphUnitWeights Vertex
    threshold := problem.threshold }

/-- Encode graph clique as edge-incidence weighted set packing on the complement graph. -/
noncomputable def graphCliqueDecisionToWeightedSetPackingDecision
    [Fintype Vertex] [DecidableEq Vertex]
    (problem : GraphCliqueDecisionInstance Vertex) :
    WeightedSetPackingDecisionInstance Vertex (Sym2 Vertex) :=
  graphIndependentSetDecisionToWeightedSetPackingDecision
    (graphCliqueDecisionToIndependentSetComplementDecision problem)

/-- Encode graph clique as single-minded welfare on complement-edge goods. -/
noncomputable def graphCliqueDecisionToSingleMindedWelfareDecision
    [Fintype Vertex] [DecidableEq Vertex]
    (problem : GraphCliqueDecisionInstance Vertex) :
    SingleMindedWelfareDecisionInstance Vertex (Sym2 Vertex) :=
  setPackingDecisionToSingleMindedWelfareDecision
    (graphCliqueDecisionToWeightedSetPackingDecision problem)

/-- Clique threshold decision is independent-set threshold decision on the complement graph. -/
theorem graphCliqueDecisionProblem_iff_graphIndependentSetDecisionProblem_compl
    (problem : GraphCliqueDecisionInstance Vertex) :
    GraphCliqueDecisionProblem problem ↔
      GraphIndependentSetDecisionProblem
        (graphCliqueDecisionToIndependentSetComplementDecision problem) := by
  constructor
  · rintro ⟨selected, hclique, hcard⟩
    exact ⟨selected,
      (graphCliqueSelection_iff_graphIndependentSelection_compl
        problem.graph selected).1 hclique, hcard⟩
  · rintro ⟨selected, hind, hcard⟩
    exact ⟨selected,
      (graphCliqueSelection_iff_graphIndependentSelection_compl
        problem.graph selected).2 hind, hcard⟩

/--
Independent-set threshold decision is the unit-weight edge-incidence set-packing
threshold decision.
-/
theorem graphIndependentSetDecisionProblem_iff_weightedSetPackingDecisionProblem_graphIncident
    [Fintype Vertex] [DecidableEq Vertex]
    (problem : GraphIndependentSetDecisionInstance Vertex) :
    GraphIndependentSetDecisionProblem problem ↔
      WeightedSetPackingDecisionProblem
        (graphIndependentSetDecisionToWeightedSetPackingDecision problem) := by
  classical
  constructor
  · rintro ⟨selected, hind, hcard⟩
    refine ⟨selected, ?_, ?_⟩
    · exact
        (setPackingFeasible_graphIncidentSets_iff_graphIndependentSelection
          problem.graph selected).2 hind
    · simpa [graphIndependentSetDecisionToWeightedSetPackingDecision,
        weightedSetPackingValue_graphUnitWeights] using hcard
  · rintro ⟨selected, hpack, hvalue⟩
    refine ⟨selected, ?_, ?_⟩
    · exact
        (setPackingFeasible_graphIncidentSets_iff_graphIndependentSelection
          problem.graph selected).1 hpack
    · simpa [graphIndependentSetDecisionToWeightedSetPackingDecision,
        weightedSetPackingValue_graphUnitWeights] using hvalue

/-- Clique threshold decision reduces to unit-weight set packing on complement-edge goods. -/
theorem graphCliqueDecisionProblem_iff_weightedSetPackingDecisionProblem_complGraphIncident
    [Fintype Vertex] [DecidableEq Vertex]
    (problem : GraphCliqueDecisionInstance Vertex) :
    GraphCliqueDecisionProblem problem ↔
      WeightedSetPackingDecisionProblem
        (graphCliqueDecisionToWeightedSetPackingDecision problem) := by
  rw [graphCliqueDecisionProblem_iff_graphIndependentSetDecisionProblem_compl]
  exact
    graphIndependentSetDecisionProblem_iff_weightedSetPackingDecisionProblem_graphIncident
      (graphCliqueDecisionToIndependentSetComplementDecision problem)

/-- Clique threshold decision reduces to single-minded welfare on complement-edge goods. -/
theorem graphCliqueDecisionProblem_iff_singleMindedWelfareDecisionProblem_complGraphIncident
    [Fintype Vertex] [DecidableEq Vertex]
    (problem : GraphCliqueDecisionInstance Vertex) :
    GraphCliqueDecisionProblem problem ↔
      SingleMindedWelfareDecisionProblem
        (graphCliqueDecisionToSingleMindedWelfareDecision problem) := by
  rw [graphCliqueDecisionProblem_iff_weightedSetPackingDecisionProblem_complGraphIncident]
  exact
    weightedSetPackingDecisionProblem_iff_singleMindedWelfareDecisionProblem
      (graphCliqueDecisionToWeightedSetPackingDecision problem)

/-- Clique-to-independent-set complement as an abstract many-one reduction. -/
noncomputable def graphCliqueDecisionProblem_manyOneReduction_graphIndependentSetDecisionProblem_compl :
    AppliedModelingLib.Complexity.ManyOneReduction
      (GraphCliqueDecisionProblem (Vertex := Vertex))
      (GraphIndependentSetDecisionProblem (Vertex := Vertex)) where
  map := graphCliqueDecisionToIndependentSetComplementDecision
  correct := graphCliqueDecisionProblem_iff_graphIndependentSetDecisionProblem_compl

/-- Independent-set-to-set-packing edge-incidence as an abstract many-one reduction. -/
noncomputable def graphIndependentSetDecisionProblem_manyOneReduction_weightedSetPackingDecisionProblem_graphIncident
    [Fintype Vertex] [DecidableEq Vertex] :
    AppliedModelingLib.Complexity.ManyOneReduction
      (GraphIndependentSetDecisionProblem (Vertex := Vertex))
      (WeightedSetPackingDecisionProblem
        (Bidder := Vertex) (Item := Sym2 Vertex)) where
  map := graphIndependentSetDecisionToWeightedSetPackingDecision
  correct :=
    graphIndependentSetDecisionProblem_iff_weightedSetPackingDecisionProblem_graphIncident

/-- Clique-to-set-packing complement-edge incidence as an abstract many-one reduction. -/
noncomputable def graphCliqueDecisionProblem_manyOneReduction_weightedSetPackingDecisionProblem_complGraphIncident
    [Fintype Vertex] [DecidableEq Vertex] :
    AppliedModelingLib.Complexity.ManyOneReduction
      (GraphCliqueDecisionProblem (Vertex := Vertex))
      (WeightedSetPackingDecisionProblem
        (Bidder := Vertex) (Item := Sym2 Vertex)) where
  map := graphCliqueDecisionToWeightedSetPackingDecision
  correct :=
    graphCliqueDecisionProblem_iff_weightedSetPackingDecisionProblem_complGraphIncident

/-- Clique-to-single-minded welfare complement-edge incidence as an abstract many-one reduction. -/
noncomputable def graphCliqueDecisionProblem_manyOneReduction_singleMindedWelfareDecisionProblem_complGraphIncident
    [Fintype Vertex] [DecidableEq Vertex] :
    AppliedModelingLib.Complexity.ManyOneReduction
      (GraphCliqueDecisionProblem (Vertex := Vertex))
      (SingleMindedWelfareDecisionProblem
        (Bidder := Vertex) (Item := Sym2 Vertex)) where
  map := graphCliqueDecisionToSingleMindedWelfareDecision
  correct :=
    graphCliqueDecisionProblem_iff_singleMindedWelfareDecisionProblem_complGraphIncident

/-- Clique-to-independent-set complement as a conditional abstract polynomial-time reduction. -/
noncomputable def graphCliqueDecisionProblem_polynomialTimeReduction_graphIndependentSetDecisionProblem_compl
    (PolynomialTime :
      (GraphCliqueDecisionInstance Vertex →
        GraphIndependentSetDecisionInstance Vertex) → Prop)
    (hpoly :
      PolynomialTime graphCliqueDecisionToIndependentSetComplementDecision) :
    AppliedModelingLib.Complexity.PolynomialTimeReduction
      (GraphCliqueDecisionProblem (Vertex := Vertex))
      (GraphIndependentSetDecisionProblem (Vertex := Vertex)) where
  reduction :=
    graphCliqueDecisionProblem_manyOneReduction_graphIndependentSetDecisionProblem_compl
  PolynomialTime := PolynomialTime
  polynomialTime := hpoly

/-- Independent-set-to-set-packing edge-incidence as a conditional polynomial-time reduction. -/
noncomputable def graphIndependentSetDecisionProblem_polynomialTimeReduction_weightedSetPackingDecisionProblem_graphIncident
    [Fintype Vertex] [DecidableEq Vertex]
    (PolynomialTime :
      (GraphIndependentSetDecisionInstance Vertex →
        WeightedSetPackingDecisionInstance Vertex (Sym2 Vertex)) → Prop)
    (hpoly :
      PolynomialTime
        graphIndependentSetDecisionToWeightedSetPackingDecision) :
    AppliedModelingLib.Complexity.PolynomialTimeReduction
      (GraphIndependentSetDecisionProblem (Vertex := Vertex))
      (WeightedSetPackingDecisionProblem
        (Bidder := Vertex) (Item := Sym2 Vertex)) where
  reduction :=
    graphIndependentSetDecisionProblem_manyOneReduction_weightedSetPackingDecisionProblem_graphIncident
  PolynomialTime := PolynomialTime
  polynomialTime := hpoly

/-- Clique-to-set-packing complement-edge incidence as a conditional polynomial-time reduction. -/
noncomputable def graphCliqueDecisionProblem_polynomialTimeReduction_weightedSetPackingDecisionProblem_complGraphIncident
    [Fintype Vertex] [DecidableEq Vertex]
    (PolynomialTime :
      (GraphCliqueDecisionInstance Vertex →
        WeightedSetPackingDecisionInstance Vertex (Sym2 Vertex)) → Prop)
    (hpoly :
      PolynomialTime graphCliqueDecisionToWeightedSetPackingDecision) :
    AppliedModelingLib.Complexity.PolynomialTimeReduction
      (GraphCliqueDecisionProblem (Vertex := Vertex))
      (WeightedSetPackingDecisionProblem
        (Bidder := Vertex) (Item := Sym2 Vertex)) where
  reduction :=
    graphCliqueDecisionProblem_manyOneReduction_weightedSetPackingDecisionProblem_complGraphIncident
  PolynomialTime := PolynomialTime
  polynomialTime := hpoly

/-- Clique-to-single-minded welfare as a conditional polynomial-time reduction. -/
noncomputable def graphCliqueDecisionProblem_polynomialTimeReduction_singleMindedWelfareDecisionProblem_complGraphIncident
    [Fintype Vertex] [DecidableEq Vertex]
    (PolynomialTime :
      (GraphCliqueDecisionInstance Vertex →
        SingleMindedWelfareDecisionInstance Vertex (Sym2 Vertex)) → Prop)
    (hpoly :
      PolynomialTime graphCliqueDecisionToSingleMindedWelfareDecision) :
    AppliedModelingLib.Complexity.PolynomialTimeReduction
      (GraphCliqueDecisionProblem (Vertex := Vertex))
      (SingleMindedWelfareDecisionProblem
        (Bidder := Vertex) (Item := Sym2 Vertex)) where
  reduction :=
    graphCliqueDecisionProblem_manyOneReduction_singleMindedWelfareDecisionProblem_complGraphIncident
  PolynomialTime := PolynomialTime
  polynomialTime := hpoly

/--
Maximum independent set is exactly unit-weight weighted set-packing optimality
for the graph-incidence encoding.
-/
theorem maximumIndependentSelection_iff_weightedSetPackingOptimal_graphIncidentSets
    [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    MaximumIndependentSelection G selected ↔
      WeightedSetPackingOptimal
        (graphIncidentSets G) (graphUnitWeights Vertex) selected := by
  constructor
  · intro h
    constructor
    · exact
        (setPackingFeasible_graphIncidentSets_iff_graphIndependentSelection
          G selected).2 h.1
    · intro other hother
      have hother_ind :
          GraphIndependentSelection G other :=
        (setPackingFeasible_graphIncidentSets_iff_graphIndependentSelection
          G other).1 hother
      have hcard : other.card ≤ selected.card := h.2 other hother_ind
      have hcast : (other.card : ℝ) ≤ (selected.card : ℝ) := by
        exact_mod_cast hcard
      simpa [weightedSetPackingValue_graphUnitWeights] using hcast
  · intro h
    constructor
    · exact
        (setPackingFeasible_graphIncidentSets_iff_graphIndependentSelection
          G selected).1 h.1
    · intro other hother
      have hother_pack :
          SetPackingFeasible (graphIncidentSets G) other :=
        (setPackingFeasible_graphIncidentSets_iff_graphIndependentSelection
          G other).2 hother
      have hvalue := h.2 other hother_pack
      rw [weightedSetPackingValue_graphUnitWeights,
        weightedSetPackingValue_graphUnitWeights] at hvalue
      exact_mod_cast hvalue

/--
Maximum independent set is exactly single-minded welfare optimality after
encoding graph edges as goods and vertices as unit-value single-minded bids.
-/
theorem maximumIndependentSelection_iff_singleMindedOptimalAcceptedSet_graphIncident
    [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    MaximumIndependentSelection G selected ↔
      SingleMindedOptimalAcceptedSet
        (setPackingSingleMindedBids
          (graphIncidentSets G) (graphUnitWeights Vertex)) selected := by
  rw [maximumIndependentSelection_iff_weightedSetPackingOptimal_graphIncidentSets]
  exact weightedSetPackingOptimal_iff_singleMindedOptimalAcceptedSet
    (graphIncidentSets G) (graphUnitWeights Vertex) selected

/--
Maximum clique reduces to unit-weight set packing by first taking the graph
complement and then using the edge-incidence independent-set encoding.
-/
theorem maximumCliqueSelection_iff_weightedSetPackingOptimal_complGraphIncidentSets
    [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    MaximumCliqueSelection G selected ↔
      WeightedSetPackingOptimal
        (graphIncidentSets Gᶜ) (graphUnitWeights Vertex) selected := by
  rw [maximumCliqueSelection_iff_maximumIndependentSelection_compl]
  exact
    maximumIndependentSelection_iff_weightedSetPackingOptimal_graphIncidentSets
      Gᶜ selected

/--
Maximum clique reduces to single-minded welfare maximization by first taking
the graph complement and then encoding complement edges as goods.
-/
theorem maximumCliqueSelection_iff_singleMindedOptimalAcceptedSet_complGraphIncident
    [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    MaximumCliqueSelection G selected ↔
      SingleMindedOptimalAcceptedSet
        (setPackingSingleMindedBids
          (graphIncidentSets Gᶜ) (graphUnitWeights Vertex)) selected := by
  rw [maximumCliqueSelection_iff_maximumIndependentSelection_compl]
  exact
    maximumIndependentSelection_iff_singleMindedOptimalAcceptedSet_graphIncident
      Gᶜ selected

/-- Total requested bundle size of a finite set of single-minded bids. -/
noncomputable def singleMindedTotalBundleSize [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) (selected : Finset Bidder) : ℝ :=
  ∑ i ∈ selected, (bids i).bundleSize

/--
Sum of squared source square-root norms, written without square roots:
`(a / sqrt(|s|))^2 = a^2 / |s|`.
-/
noncomputable def singleMindedSqrtNormSqSum [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) (selected : Finset Bidder) : ℝ :=
  ∑ i ∈ selected, (bids i).value ^ 2 / (bids i).bundleSize

theorem singleMindedTotalBundleSize_le_goods_card_of_pairwiseDisjoint
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (selected : Finset Bidder) (goods : Finset Item)
    (hgoods : ∀ i, i ∈ selected → (bids i).desired ⊆ goods)
    (hdisjoint : PairwiseDisjointDesired bids selected) :
    singleMindedTotalBundleSize bids selected ≤ (goods.card : ℝ) := by
  classical
  have hpair :
      (selected : Set Bidder).PairwiseDisjoint fun i =>
        (bids i).desired := by
    intro i hi j hj hij
    exact hdisjoint (by simpa using hi) (by simpa using hj) hij
  have hcard_union :
      (((selected.biUnion fun i => (bids i).desired).card : ℕ) : ℝ) =
        ∑ i ∈ selected, ((bids i).desired.card : ℝ) := by
    have hnat :
        (selected.biUnion fun i => (bids i).desired).card =
          ∑ i ∈ selected, (bids i).desired.card := by
      exact Finset.card_biUnion hpair
    exact_mod_cast hnat
  have hsubset :
      (selected.biUnion fun i => (bids i).desired) ⊆ goods := by
    intro g hg
    rcases Finset.mem_biUnion.mp hg with ⟨i, hi, hg_i⟩
    exact hgoods i hi hg_i
  have hcard_le :
      (((selected.biUnion fun i => (bids i).desired).card : ℕ) : ℝ) ≤
        (goods.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  rw [hcard_union] at hcard_le
  simpa [singleMindedTotalBundleSize, SingleMindedBid.bundleSize] using hcard_le

theorem singleMindedTotalValue_nonneg [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) (selected : Finset Bidder)
    (hvalue_nonneg : ∀ i, i ∈ selected → 0 ≤ (bids i).value) :
    0 ≤ singleMindedTotalValue bids selected := by
  unfold singleMindedTotalValue
  exact Finset.sum_nonneg fun i hi => hvalue_nonneg i hi

/--
Common-bid removal algebra. If the approximation inequality is known after
deleting bids common to `optimal` and `greedy`, then it lifts back to the
original sets for any approximation factor at least one.
-/
theorem singleMindedTotalValue_common_bid_removal_bridge [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (factor : ℝ)
    (hfactor : 1 ≤ factor)
    (hcommon_nonneg : ∀ i, i ∈ optimal ∩ greedy → 0 ≤ (bids i).value)
    (hreduced :
      singleMindedTotalValue bids (optimal \ greedy) ≤
        factor * singleMindedTotalValue bids (greedy \ optimal)) :
    singleMindedTotalValue bids optimal ≤
      factor * singleMindedTotalValue bids greedy := by
  classical
  have hopt_split :
      singleMindedTotalValue bids optimal =
        singleMindedTotalValue bids (optimal \ greedy) +
          singleMindedTotalValue bids (optimal ∩ greedy) := by
    unfold singleMindedTotalValue
    calc
      (∑ i ∈ optimal, (bids i).value) =
          ∑ i ∈ (optimal \ greedy) ∪ (optimal ∩ greedy), (bids i).value := by
            rw [Finset.sdiff_union_inter]
      _ = (∑ i ∈ optimal \ greedy, (bids i).value) +
          ∑ i ∈ optimal ∩ greedy, (bids i).value := by
            rw [Finset.sum_union (Finset.disjoint_sdiff_inter optimal greedy)]
  have hgreedy_split :
      singleMindedTotalValue bids greedy =
        singleMindedTotalValue bids (greedy \ optimal) +
          singleMindedTotalValue bids (optimal ∩ greedy) := by
    unfold singleMindedTotalValue
    calc
      (∑ i ∈ greedy, (bids i).value) =
          ∑ i ∈ (greedy \ optimal) ∪ (greedy ∩ optimal), (bids i).value := by
            rw [Finset.sdiff_union_inter]
      _ = (∑ i ∈ greedy \ optimal, (bids i).value) +
          ∑ i ∈ greedy ∩ optimal, (bids i).value := by
            rw [Finset.sum_union (Finset.disjoint_sdiff_inter greedy optimal)]
      _ = (∑ i ∈ greedy \ optimal, (bids i).value) +
          ∑ i ∈ optimal ∩ greedy, (bids i).value := by
            rw [Finset.inter_comm]
  have hcommon_nonneg_sum :
      0 ≤ singleMindedTotalValue bids (optimal ∩ greedy) :=
    singleMindedTotalValue_nonneg bids (optimal ∩ greedy) hcommon_nonneg
  rw [hopt_split, hgreedy_split]
  nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) hcommon_nonneg_sum]

theorem singleMindedSqrtNormSqSum_nonneg [DecidableEq Bidder]
    [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (selected : Finset Bidder)
    (hnonempty : ∀ i, i ∈ selected → (bids i).desired.Nonempty) :
    0 ≤ singleMindedSqrtNormSqSum bids selected := by
  classical
  unfold singleMindedSqrtNormSqSum
  refine Finset.sum_nonneg ?_
  intro i hi
  exact div_nonneg (sq_nonneg _) ((bids i).bundleSize_pos_of_nonempty (hnonempty i hi)).le

/--
If the source square-root norm of `i` is no larger than that of `j`, then the
squared norm used in the algebraic proof is also no larger.
-/
theorem singleMinded_normSq_le_of_sqrtAmountNorm_le [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) {i j : Bidder}
    (hi_nonempty : (bids i).desired.Nonempty)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hi_value_nonneg : 0 ≤ (bids i).value)
    (hnorm : (bids i).sqrtAmountNorm ≤ (bids j).sqrtAmountNorm) :
    (bids i).value ^ 2 / (bids i).bundleSize ≤
      (bids j).value ^ 2 / (bids j).bundleSize := by
  have hi_norm_nonneg : 0 ≤ (bids i).sqrtAmountNorm := by
    exact div_nonneg hi_value_nonneg (Real.sqrt_nonneg _)
  have hsq :
      (bids i).sqrtAmountNorm ^ 2 ≤
        (bids j).sqrtAmountNorm ^ 2 := by
    nlinarith
  simpa [
    SingleMindedBid.sqrtAmountNorm_sq_eq_value_sq_div_bundleSize
      (bids i) hi_nonempty,
    SingleMindedBid.sqrtAmountNorm_sq_eq_value_sq_div_bundleSize
      (bids j) hj_nonempty] using hsq

/-- Two single-minded bids conflict when their desired bundles intersect. -/
def SingleMindedBidsConflict [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (i j : Bidder) : Prop :=
  ((bids i).desired ∩ (bids j).desired).Nonempty

theorem SingleMindedBidsConflict.symm [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {i j : Bidder}
    (h : SingleMindedBidsConflict bids i j) :
    SingleMindedBidsConflict bids j i := by
  simpa [SingleMindedBidsConflict, Finset.inter_comm] using h

/--
Update only a single bidder's declared value, preserving every desired bundle.
This is the value-only perturbation used in critical-price arguments.
-/
def singleMindedValueUpdate [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) (value : ℝ) :
    Bidder → SingleMindedBid Item :=
  Function.update bids j { desired := (bids j).desired, value := value }

@[simp] theorem singleMindedValueUpdate_self [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) (value : ℝ) :
    singleMindedValueUpdate bids j value j =
      { desired := (bids j).desired, value := value } := by
  simp [singleMindedValueUpdate]

@[simp] theorem singleMindedValueUpdate_same_of_ne [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) {j k : Bidder} (value : ℝ)
    (hk : k ≠ j) :
    singleMindedValueUpdate bids j value k = bids k := by
  simp [singleMindedValueUpdate, hk]

@[simp] theorem singleMindedValueUpdate_desired [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) (value : ℝ)
    (k : Bidder) :
    (singleMindedValueUpdate bids j value k).desired = (bids k).desired := by
  by_cases hk : k = j
  · subst k
    simp [singleMindedValueUpdate]
  · simp [singleMindedValueUpdate, hk]

theorem singleMindedValueUpdate_update_desired_value [DecidableEq Bidder]
    (reports : Bidder → SingleMindedBid Item) (i : Bidder)
    (s : Bundle Item) (baseValue value : ℝ) :
    singleMindedValueUpdate
      (Function.update reports i { desired := s, value := baseValue }) i value =
        Function.update reports i { desired := s, value := value } := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [singleMindedValueUpdate]
  · simp [singleMindedValueUpdate, hk]

theorem singleMindedUpdate_update_desired_value [DecidableEq Bidder]
    (reports : Bidder → SingleMindedBid Item) (i : Bidder)
    (s : Bundle Item) (baseValue value : ℝ) :
    Function.update
      (Function.update reports i { desired := s, value := baseValue })
      i { desired := s, value := value } =
        Function.update reports i { desired := s, value := value } := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [Function.update]
  · simp [Function.update, hk]

theorem singleMindedUpdate_self_desired_value [DecidableEq Bidder]
    (reports : Bidder → SingleMindedBid Item) (i : Bidder) :
    Function.update reports i
      { desired := (reports i).desired, value := (reports i).value } =
        reports := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [Function.update]
  · simp [Function.update, hk]

theorem singleMindedValueUpdate_conflict_iff [DecidableEq Bidder]
    [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) (value : ℝ)
    (i k : Bidder) :
    SingleMindedBidsConflict (singleMindedValueUpdate bids j value) i k ↔
      SingleMindedBidsConflict bids i k := by
  simp [SingleMindedBidsConflict]

/-- Bid `i` is compatible with all currently accepted single-minded bids. -/
def SingleMindedCompatibleWithAccepted [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (i : Bidder) : Prop :=
  ∀ j, j ∈ accepted → Disjoint (bids i).desired (bids j).desired

/-- Accepted bids that conflict with the next candidate bid. -/
def singleMindedGreedyConflictingAccepted [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (i : Bidder) : Finset Bidder :=
  accepted.filter fun j => ((bids i).desired ∩ (bids j).desired).Nonempty

/--
One step of the source greedy allocation: accept the next bid iff it does not
conflict with any already accepted bid.
-/
def singleMindedGreedyStep [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (i : Bidder) : Finset Bidder :=
  if (singleMindedGreedyConflictingAccepted bids accepted i).Nonempty then
    accepted
  else
    insert i accepted

/-- Run the source greedy allocation from an arbitrary accepted-set state. -/
def singleMindedGreedyAcceptedFromState [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (order : List Bidder) :
    Finset Bidder :=
  order.foldl (singleMindedGreedyStep bids) accepted

/-- The source greedy accepted set from an explicit bid order. -/
def singleMindedGreedyAcceptedFromOrder [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) :
    Finset Bidder :=
  singleMindedGreedyAcceptedFromState bids ∅ order

theorem singleMindedGreedyConflictingAccepted_congr
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bids' : Bidder → SingleMindedBid Item}
    {accepted : Finset Bidder} {i : Bidder}
    (hi : bids' i = bids i)
    (haccepted : ∀ j, j ∈ accepted → bids' j = bids j) :
    singleMindedGreedyConflictingAccepted bids' accepted i =
      singleMindedGreedyConflictingAccepted bids accepted i := by
  apply Finset.ext
  intro j
  by_cases hj : j ∈ accepted
  · simp [singleMindedGreedyConflictingAccepted, hj, hi, haccepted j hj]
  · simp [singleMindedGreedyConflictingAccepted, hj]

theorem singleMindedGreedyConflictingAccepted_erase
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (j i : Bidder) :
    singleMindedGreedyConflictingAccepted bids (accepted.erase j) i =
      (singleMindedGreedyConflictingAccepted bids accepted i).erase j := by
  apply Finset.ext
  intro k
  by_cases hkj : k = j
  · subst k
    simp [singleMindedGreedyConflictingAccepted]
  · simp [singleMindedGreedyConflictingAccepted, hkj]

theorem singleMindedGreedyConflictingAccepted_erase_of_same_nonblocker
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → SingleMindedBid Item}
    {acceptedWithJ : Finset Bidder} {j i : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hi : i ≠ j) :
    singleMindedGreedyConflictingAccepted bidsLow (acceptedWithJ.erase j) i =
      (singleMindedGreedyConflictingAccepted bids acceptedWithJ i).erase j := by
  rw [singleMindedGreedyConflictingAccepted_congr
    (bids := bids) (bids' := bidsLow)
    (accepted := acceptedWithJ.erase j) (i := i) (hsame i hi)
    (fun k hk => hsame k (Finset.mem_erase.mp hk).1)]
  exact singleMindedGreedyConflictingAccepted_erase bids acceptedWithJ j i

theorem singleMindedGreedyStep_congr
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bids' : Bidder → SingleMindedBid Item}
    {accepted : Finset Bidder} {i : Bidder}
    (hi : bids' i = bids i)
    (haccepted : ∀ j, j ∈ accepted → bids' j = bids j) :
    singleMindedGreedyStep bids' accepted i =
      singleMindedGreedyStep bids accepted i := by
  simp [singleMindedGreedyStep,
    singleMindedGreedyConflictingAccepted_congr
      (bids := bids) (bids' := bids') (accepted := accepted)
      (i := i) hi haccepted]

theorem singleMindedGreedyStep_subset_insert [DecidableEq Bidder]
    [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (i : Bidder) :
    singleMindedGreedyStep bids accepted i ⊆ insert i accepted := by
  intro x hx
  by_cases hconflict :
      (singleMindedGreedyConflictingAccepted bids accepted i).Nonempty
  · exact Finset.mem_insert.mpr (Or.inr (by
      simpa [singleMindedGreedyStep, hconflict] using hx))
  · simpa [singleMindedGreedyStep, hconflict] using hx

theorem singleMindedGreedyStep_contains_accepted [DecidableEq Bidder]
    [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (i : Bidder) :
    accepted ⊆ singleMindedGreedyStep bids accepted i := by
  intro x hx
  by_cases hconflict :
      (singleMindedGreedyConflictingAccepted bids accepted i).Nonempty
  · simpa [singleMindedGreedyStep, hconflict] using hx
  · simpa [singleMindedGreedyStep, hconflict] using
      (Finset.mem_insert.mpr (Or.inr hx) : x ∈ insert i accepted)

theorem singleMindedGreedyStep_eq_self_of_conflicting_accepted
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (i : Bidder)
    (hconflict : ∃ j, j ∈ accepted ∧ SingleMindedBidsConflict bids i j) :
    singleMindedGreedyStep bids accepted i = accepted := by
  have hnonempty :
      (singleMindedGreedyConflictingAccepted bids accepted i).Nonempty := by
    rcases hconflict with ⟨j, hj, hji⟩
    exact ⟨j, by
      simp [singleMindedGreedyConflictingAccepted, hj, SingleMindedBidsConflict] at hji ⊢
      exact hji⟩
  simp [singleMindedGreedyStep, hnonempty]

theorem singleMindedGreedyStep_not_mem_of_conflicting_accepted
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) {i : Bidder}
    (hi : i ∉ accepted)
    (hconflict : ∃ j, j ∈ accepted ∧ SingleMindedBidsConflict bids i j) :
    i ∉ singleMindedGreedyStep bids accepted i := by
  simpa [singleMindedGreedyStep_eq_self_of_conflicting_accepted
    bids accepted i hconflict] using hi

theorem singleMindedGreedyAcceptedFromState_contains_initial
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (order : List Bidder) :
    accepted ⊆ singleMindedGreedyAcceptedFromState bids accepted order := by
  induction order generalizing accepted with
  | nil =>
      intro x hx
      simpa [singleMindedGreedyAcceptedFromState] using hx
  | cons i rest ih =>
      exact subset_trans
        (singleMindedGreedyStep_contains_accepted bids accepted i)
        (by
          simpa [singleMindedGreedyAcceptedFromState] using
            ih (accepted := singleMindedGreedyStep bids accepted i))

theorem singleMindedGreedyAcceptedFromState_append
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (pre suffix : List Bidder) :
    singleMindedGreedyAcceptedFromState bids accepted (pre ++ suffix) =
      singleMindedGreedyAcceptedFromState bids
        (singleMindedGreedyAcceptedFromState bids accepted pre) suffix := by
  simp [singleMindedGreedyAcceptedFromState, List.foldl_append]

theorem singleMindedGreedyAcceptedFromState_subset_initial_union_order
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (order : List Bidder) :
    singleMindedGreedyAcceptedFromState bids accepted order ⊆
      accepted ∪ order.toFinset := by
  induction order generalizing accepted with
  | nil =>
      intro x hx
      simp [singleMindedGreedyAcceptedFromState] at hx ⊢
      exact hx
  | cons i rest ih =>
      intro x hx
      have hx' :
          x ∈ singleMindedGreedyAcceptedFromState bids
            (singleMindedGreedyStep bids accepted i) rest := by
        simpa [singleMindedGreedyAcceptedFromState] using hx
      have hmem := ih
        (accepted := singleMindedGreedyStep bids accepted i) hx'
      rw [Finset.mem_union] at hmem ⊢
      rcases hmem with hstep | hrest
      · have hstep' :=
          singleMindedGreedyStep_subset_insert bids accepted i hstep
        rw [Finset.mem_insert] at hstep'
        rcases hstep' with rfl | hacc
        · right
          simp
        · left
          exact hacc
      · right
        simp [hrest]

theorem singleMindedGreedyAcceptedFromState_congr
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bids' : Bidder → SingleMindedBid Item}
    (accepted : Finset Bidder) (order : List Bidder)
    (haccepted : ∀ i, i ∈ accepted → bids' i = bids i)
    (horder : ∀ i, i ∈ order → bids' i = bids i) :
    singleMindedGreedyAcceptedFromState bids' accepted order =
      singleMindedGreedyAcceptedFromState bids accepted order := by
  induction order generalizing accepted with
  | nil =>
      simp [singleMindedGreedyAcceptedFromState]
  | cons head rest ih =>
      have hstep :
          singleMindedGreedyStep bids' accepted head =
            singleMindedGreedyStep bids accepted head := by
        exact singleMindedGreedyStep_congr
          (bids := bids) (bids' := bids') (accepted := accepted)
          (i := head) (horder head (by simp)) haccepted
      simp [singleMindedGreedyAcceptedFromState, hstep]
      apply ih
      · intro k hk
        have hj' :
            k ∈ insert head accepted :=
          singleMindedGreedyStep_subset_insert bids accepted head hk
        rw [Finset.mem_insert] at hj'
        rcases hj' with rfl | hjacc
        · exact horder k (by simp)
        · exact haccepted k hjacc
      · intro k hk
        exact horder k (by simp [hk])

theorem singleMindedGreedyAcceptedFromState_congr_of_forall
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bids' : Bidder → SingleMindedBid Item}
    (accepted : Finset Bidder) (order : List Bidder)
    (hsame : ∀ i, bids' i = bids i) :
    singleMindedGreedyAcceptedFromState bids' accepted order =
      singleMindedGreedyAcceptedFromState bids accepted order := by
  exact singleMindedGreedyAcceptedFromState_congr
    (bids := bids) (bids' := bids') accepted order
    (fun i _ => hsame i) (fun i _ => hsame i)

theorem singleMindedGreedyAcceptedFromState_congr_of_not_mem
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bids' : Bidder → SingleMindedBid Item}
    (accepted : Finset Bidder) (order : List Bidder) (j : Bidder)
    (hjaccepted : j ∉ accepted) (hjorder : j ∉ order)
    (hsame : ∀ i, i ≠ j → bids' i = bids i) :
    singleMindedGreedyAcceptedFromState bids' accepted order =
      singleMindedGreedyAcceptedFromState bids accepted order := by
  exact singleMindedGreedyAcceptedFromState_congr
    (bids := bids) (bids' := bids') accepted order
    (fun i hi => hsame i (by
      intro hij
      subst hij
      exact hjaccepted hi))
    (fun i hi => hsame i (by
      intro hij
      subst hij
      exact hjorder hi))

theorem singleMindedGreedyAcceptedFromState_not_mem_of_not_mem_initial_order
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (order : List Bidder) {j : Bidder}
    (hjaccepted : j ∉ accepted) (hjorder : j ∉ order) :
    j ∉ singleMindedGreedyAcceptedFromState bids accepted order := by
  intro hjfinal
  have hmem :=
    singleMindedGreedyAcceptedFromState_subset_initial_union_order
      bids accepted order hjfinal
  rw [Finset.mem_union] at hmem
  rcases hmem with hjacc | hjord
  · exact hjaccepted hjacc
  · exact hjorder (by simpa using hjord)

theorem singleMindedGreedyAcceptedFromState_erase_append_singleton_of_mem_valueUpdate
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (before : List Bidder) {j : Bidder} (value : ℝ)
    (hjbefore : j ∉ before)
    (hjaccepted :
      j ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])) :
    (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])).erase j =
      singleMindedGreedyAcceptedFromState
        (singleMindedValueUpdate bids j value) ∅ before := by
  let beforeState : Finset Bidder :=
    singleMindedGreedyAcceptedFromState bids ∅ before
  have hj_beforeState : j ∉ beforeState := by
    exact
      singleMindedGreedyAcceptedFromState_not_mem_of_not_mem_initial_order
        bids ∅ before (by simp) hjbefore
  have hfull :
      singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j]) =
        singleMindedGreedyStep bids beforeState j := by
    rw [singleMindedGreedyAcceptedFromState_append]
    simp [beforeState, singleMindedGreedyAcceptedFromState]
  have hj_step : j ∈ singleMindedGreedyStep bids beforeState j := by
    simpa [hfull] using hjaccepted
  have hno :
      ¬ (singleMindedGreedyConflictingAccepted bids beforeState j).Nonempty := by
    intro hconf
    have hstep_eq :
        singleMindedGreedyStep bids beforeState j = beforeState := by
      simp [singleMindedGreedyStep, hconf]
    exact hj_beforeState (by simpa [hstep_eq] using hj_step)
  have hstep_insert :
      singleMindedGreedyStep bids beforeState j = insert j beforeState := by
    simp [singleMindedGreedyStep, hno]
  have hprefix :
      singleMindedGreedyAcceptedFromState
          (singleMindedValueUpdate bids j value) ∅ before =
        beforeState := by
    simpa [beforeState] using
      singleMindedGreedyAcceptedFromState_congr_of_not_mem
        (bids := bids)
        (bids' := singleMindedValueUpdate bids j value)
        ∅ before j (by simp) hjbefore
        (fun k hk => singleMindedValueUpdate_same_of_ne bids value hk)
  calc
    (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])).erase j
        = (singleMindedGreedyStep bids beforeState j).erase j := by rw [hfull]
    _ = (insert j beforeState).erase j := by rw [hstep_insert]
    _ = beforeState := by simp [hj_beforeState]
    _ =
        singleMindedGreedyAcceptedFromState
          (singleMindedValueUpdate bids j value) ∅ before := hprefix.symm

theorem singleMindedGreedyAcceptedFromState_accepts_head_of_safe_initial
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (tail : List Bidder) {j : Bidder}
    (hsafe :
      ∀ k, k ∈ accepted → ¬ SingleMindedBidsConflict bids j k) :
    j ∈ singleMindedGreedyAcceptedFromState bids accepted (j :: tail) := by
  have hno :
      ¬ (singleMindedGreedyConflictingAccepted bids accepted j).Nonempty := by
    intro hnonempty
    rcases hnonempty with ⟨k, hk⟩
    have hkprops :
        k ∈ accepted ∧ SingleMindedBidsConflict bids j k := by
      simpa [singleMindedGreedyConflictingAccepted,
        SingleMindedBidsConflict] using hk
    exact hsafe k hkprops.1 hkprops.2
  have hjstep : j ∈ singleMindedGreedyStep bids accepted j := by
    simp [singleMindedGreedyStep, hno]
  simp [singleMindedGreedyAcceptedFromState]
  exact singleMindedGreedyAcceptedFromState_contains_initial
    bids (singleMindedGreedyStep bids accepted j) tail hjstep

theorem singleMindedGreedyAcceptedFromState_accepts_after_safe_prefix
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (pref tail : List Bidder) {j : Bidder}
    (hsafe :
      ∀ k,
        k ∈ singleMindedGreedyAcceptedFromState bids accepted pref →
          ¬ SingleMindedBidsConflict bids j k) :
    j ∈ singleMindedGreedyAcceptedFromState bids accepted (pref ++ j :: tail) := by
  rw [singleMindedGreedyAcceptedFromState_append]
  exact
    singleMindedGreedyAcceptedFromState_accepts_head_of_safe_initial
      bids (singleMindedGreedyAcceptedFromState bids accepted pref) tail hsafe

theorem list_orderedInsert_append_right_of_forall_not_rel
    {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (j : α) :
    ∀ before base : List α,
      (∀ x, x ∈ before → ¬ r j x) →
        (before ++ base).orderedInsert r j =
          before ++ base.orderedInsert r j
  | [], base, _ => by simp
  | a :: before, base, h => by
      have ha : ¬ r j a := h a (by simp)
      have hbefore : ∀ x, x ∈ before → ¬ r j x := by
        intro x hx
        exact h x (by simp [hx])
      simp [List.orderedInsert_cons, ha,
        list_orderedInsert_append_right_of_forall_not_rel r j before base
          hbefore]

theorem list_orderedInsert_eq_cons_of_forall_rel
    {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (j : α) :
    ∀ base : List α,
      (∀ x, x ∈ base → r j x) →
        base.orderedInsert r j = j :: base
  | [], _ => by simp
  | a :: base, h => by
      have ha : r j a := h a (by simp)
      simp [List.orderedInsert_cons, ha]

/--
If `j` relates to every element of the suffix `base`, then inserting `j` into
`before ++ base` either happens inside `before` or exactly at the boundary
before `base`.
-/
theorem list_orderedInsert_split_before_of_forall_base_rel
    {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (j : α) :
    ∀ before base : List α,
      (∀ x, x ∈ base → r j x) →
        ∃ pref rest tail,
          before = pref ++ rest ∧
            (before ++ base).orderedInsert r j =
              pref ++ j :: tail
  | [], base, hbase => by
      refine ⟨[], [], base, by simp, ?_⟩
      exact list_orderedInsert_eq_cons_of_forall_rel r j base hbase
  | a :: before, base, hbase => by
      by_cases hja : r j a
      · refine ⟨[], a :: before, (a :: before) ++ base, by simp, ?_⟩
        simp [List.orderedInsert_cons, hja]
      · rcases
          list_orderedInsert_split_before_of_forall_base_rel
            r j before base hbase with
          ⟨pref, rest, tail, hbefore, hinsert⟩
        refine ⟨a :: pref, rest, tail, ?_, ?_⟩
        · simp [hbefore]
        · simp [List.orderedInsert_cons, hja, hinsert]

theorem list_forall_rel_suffix_of_pairwise_append_of_exists_prefix_rel
    {α : Type*} {r : α → α → Prop} [IsTrans α r]
    {before base : List α} {j : α}
    (hpair : (before ++ base).Pairwise r)
    (hexists : ∃ x, x ∈ before ∧ r j x) :
    ∀ y, y ∈ base → r j y := by
  induction before with
  | nil =>
      rcases hexists with ⟨x, hx, _⟩
      simp at hx
  | cons a before ih =>
      have htail : (before ++ base).Pairwise r :=
        List.Pairwise.of_cons hpair
      rcases hexists with ⟨x, hx, hjx⟩
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · intro y hy
        have hay : r x y :=
          (List.pairwise_cons.mp hpair).1 y (by simp [hy])
        exact _root_.trans hjx hay
      · exact ih htail ⟨x, hx, hjx⟩

theorem list_orderedInsert_exists_prefix_of_exists_rel
    {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (j : α) :
    ∀ before base : List α,
      (∃ x, x ∈ before ∧ r j x) →
        ∃ pref rest,
          before = pref ++ rest ∧
            (before ++ base).orderedInsert r j =
              pref ++ j :: (rest ++ base)
  | [], _base, hexists => by
      rcases hexists with ⟨x, hx, _⟩
      simp at hx
  | a :: before, base, hexists => by
      by_cases hja : r j a
      · refine ⟨[], a :: before, by simp, ?_⟩
        simp [List.orderedInsert_cons, hja]
      · have hexists_tail : ∃ x, x ∈ before ∧ r j x := by
          rcases hexists with ⟨x, hx, hjx⟩
          rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact False.elim (hja hjx)
          · exact ⟨x, hx, hjx⟩
        rcases
          list_orderedInsert_exists_prefix_of_exists_rel r j before base
            hexists_tail with
          ⟨pref, rest, hbefore, hinsert⟩
        refine ⟨a :: pref, rest, ?_, ?_⟩
        · simp [hbefore]
        · simp [List.orderedInsert_cons, hja, hinsert]

theorem singleMindedGreedyAcceptedFromState_orderedInsert_suffix_window_iff
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (r : Bidder → Bidder → Prop) [DecidableRel r] [IsTrans Bidder r]
    (before base : List Bidder) (j : Bidder)
    (hpair : (before ++ base).Pairwise r)
    (hsafe :
      ∀ k,
        k ∈ singleMindedGreedyAcceptedFromState bids ∅ before →
          ¬ SingleMindedBidsConflict bids j k) :
    j ∈ singleMindedGreedyAcceptedFromState bids ∅
        ((before ++ base).orderedInsert r j) ↔
      j ∈ singleMindedGreedyAcceptedFromState bids
        (singleMindedGreedyAcceptedFromState bids ∅ before)
        (base.orderedInsert r j) := by
  classical
  by_cases hexists : ∃ x, x ∈ before ∧ r j x
  · have hbase_rel :
        ∀ y, y ∈ base → r j y :=
      list_forall_rel_suffix_of_pairwise_append_of_exists_prefix_rel
        hpair hexists
    have hlocal_order : base.orderedInsert r j = j :: base :=
      list_orderedInsert_eq_cons_of_forall_rel r j base hbase_rel
    have hlocal_accept :
        j ∈ singleMindedGreedyAcceptedFromState bids
          (singleMindedGreedyAcceptedFromState bids ∅ before)
          (base.orderedInsert r j) := by
      rw [hlocal_order]
      exact
        singleMindedGreedyAcceptedFromState_accepts_head_of_safe_initial
          bids (singleMindedGreedyAcceptedFromState bids ∅ before) base hsafe
    rcases
      list_orderedInsert_exists_prefix_of_exists_rel r j before base hexists with
      ⟨pref, rest, hbefore, hfull_order⟩
    have hprefix_subset :
        singleMindedGreedyAcceptedFromState bids ∅ pref ⊆
          singleMindedGreedyAcceptedFromState bids ∅ before := by
      intro k hk
      rw [hbefore, singleMindedGreedyAcceptedFromState_append]
      exact singleMindedGreedyAcceptedFromState_contains_initial
        bids (singleMindedGreedyAcceptedFromState bids ∅ pref) rest hk
    have hfull_accept :
        j ∈ singleMindedGreedyAcceptedFromState bids ∅
          ((before ++ base).orderedInsert r j) := by
      rw [hfull_order]
      exact
        singleMindedGreedyAcceptedFromState_accepts_after_safe_prefix
          bids ∅ pref (rest ++ base)
          (fun k hk => hsafe k (hprefix_subset hk))
    constructor
    · intro _h
      exact hlocal_accept
    · intro _h
      exact hfull_accept
  · have hnot : ∀ x, x ∈ before → ¬ r j x := by
      intro x hx hr
      exact hexists ⟨x, hx, hr⟩
    have hfull_order :
        (before ++ base).orderedInsert r j =
          before ++ base.orderedInsert r j :=
      list_orderedInsert_append_right_of_forall_not_rel r j before base hnot
    rw [hfull_order, singleMindedGreedyAcceptedFromState_append]

theorem singleMindedGreedyAcceptedFromState_rejects_of_prior_conflict
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBefore : Finset Bidder) (tail : List Bidder)
    {j n : Bidder}
    (hn : n ∈ acceptedBefore)
    (hj : j ∉ acceptedBefore)
    (hconflict : SingleMindedBidsConflict bids j n)
    (hjtail : j ∉ tail) :
    j ∉ singleMindedGreedyAcceptedFromState bids acceptedBefore (j :: tail) := by
  have hstep :
      singleMindedGreedyStep bids acceptedBefore j = acceptedBefore := by
    exact singleMindedGreedyStep_eq_self_of_conflicting_accepted
      bids acceptedBefore j ⟨n, hn, hconflict⟩
  simp [singleMindedGreedyAcceptedFromState, hstep]
  exact singleMindedGreedyAcceptedFromState_not_mem_of_not_mem_initial_order
    bids acceptedBefore tail hj hjtail

theorem singleMindedGreedyAcceptedFromState_rejects_after_prefix_conflict
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBefore : Finset Bidder) (pref tail : List Bidder)
    {j n : Bidder}
    (hn :
      n ∈ singleMindedGreedyAcceptedFromState bids acceptedBefore pref)
    (hjaccepted : j ∉ acceptedBefore)
    (hjpref : j ∉ pref)
    (hjtail : j ∉ tail)
    (hconflict : SingleMindedBidsConflict bids j n) :
    j ∉ singleMindedGreedyAcceptedFromState bids acceptedBefore
      (pref ++ j :: tail) := by
  have hjbefore :
      j ∉ singleMindedGreedyAcceptedFromState bids acceptedBefore pref :=
    singleMindedGreedyAcceptedFromState_not_mem_of_not_mem_initial_order
      bids acceptedBefore pref hjaccepted hjpref
  rw [singleMindedGreedyAcceptedFromState_append]
  exact singleMindedGreedyAcceptedFromState_rejects_of_prior_conflict
    bids
    (singleMindedGreedyAcceptedFromState bids acceptedBefore pref)
    tail hn hjbefore hconflict hjtail

theorem singleMindedGreedyAcceptedFromOrder_subset_order_toFinset
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) :
    singleMindedGreedyAcceptedFromOrder bids order ⊆ order.toFinset := by
  intro i hi
  have hsubset :=
    singleMindedGreedyAcceptedFromState_subset_initial_union_order
      bids (∅ : Finset Bidder) order hi
  simpa [singleMindedGreedyAcceptedFromOrder] using hsubset

/-- The allocation induced by the source greedy accepted set. -/
def singleMindedGreedyAllocationFromOrder [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) :
    BundleAllocation Bidder Item :=
  singleMindedAllocation bids (singleMindedGreedyAcceptedFromOrder bids order)

theorem pairwiseDisjointDesired_empty [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) :
    PairwiseDisjointDesired bids (∅ : Finset Bidder) := by
  intro i _j hi
  simp at hi

theorem PairwiseDisjointDesired.insert_of_compatible [DecidableEq Bidder]
    [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {accepted : Finset Bidder} {i : Bidder}
    (haccepted : PairwiseDisjointDesired bids accepted)
    (hcompatible : SingleMindedCompatibleWithAccepted bids accepted i) :
    PairwiseDisjointDesired bids (insert i accepted) := by
  intro x y hx hy hxy
  rw [Finset.mem_insert] at hx hy
  rcases hx with rfl | hx'
  · rcases hy with rfl | hy'
    · exact (hxy rfl).elim
    · exact hcompatible y hy'
  · rcases hy with rfl | hy'
    · exact (hcompatible x hx').symm
    · exact haccepted hx' hy' hxy

theorem singleMindedGreedyStep_pairwiseDisjoint [DecidableEq Bidder]
    [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (i : Bidder)
    (haccepted : PairwiseDisjointDesired bids accepted) :
    PairwiseDisjointDesired bids
      (singleMindedGreedyStep bids accepted i) := by
  classical
  by_cases hconflict :
      (singleMindedGreedyConflictingAccepted bids accepted i).Nonempty
  · simpa [singleMindedGreedyStep, hconflict] using haccepted
  · have hcompatible : SingleMindedCompatibleWithAccepted bids accepted i := by
      intro j hj
      rw [Finset.disjoint_left]
      intro g hgi hgj
      exact hconflict
        ⟨j, by
          simp [singleMindedGreedyConflictingAccepted, hj]
          exact ⟨g, Finset.mem_inter.mpr ⟨hgi, hgj⟩⟩⟩
    simpa [singleMindedGreedyStep, hconflict] using
      haccepted.insert_of_compatible hcompatible

theorem singleMindedGreedyAcceptedFromState_pairwiseDisjoint
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (order : List Bidder)
    (haccepted : PairwiseDisjointDesired bids accepted) :
    PairwiseDisjointDesired bids
      (singleMindedGreedyAcceptedFromState bids accepted order) := by
  classical
  unfold singleMindedGreedyAcceptedFromState
  refine List.foldlRecOn (l := order) (op := singleMindedGreedyStep bids)
    (motive := fun accepted => PairwiseDisjointDesired bids accepted)
    (b := accepted) ?base ?step
  · exact haccepted
  · intro acceptedBefore hacceptedBefore i _hi
    exact singleMindedGreedyStep_pairwiseDisjoint
      bids acceptedBefore i hacceptedBefore

theorem singleMindedGreedyAccepted_pairwiseDisjoint [DecidableEq Bidder]
    [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) :
    PairwiseDisjointDesired bids
      (singleMindedGreedyAcceptedFromOrder bids order) := by
  exact singleMindedGreedyAcceptedFromState_pairwiseDisjoint
    bids ∅ order (pairwiseDisjointDesired_empty bids)

/--
If `fixed` is a subset of a pairwise-disjoint accepted set, any accepted bid
whose desired bundle intersects the union of `fixed` desired bundles must itself
belong to `fixed`.
-/
theorem singleMindedAccepted_mem_fixed_of_not_disjoint_fixedGoods
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {accepted fixed : Finset Bidder}
    (hfixed_subset : fixed ⊆ accepted)
    (haccepted_pairwise : PairwiseDisjointDesired bids accepted)
    {i : Bidder} (hi : i ∈ accepted)
    (hnot :
      ¬ Disjoint (bids i).desired
        (fixed.biUnion fun j => (bids j).desired)) :
    i ∈ fixed := by
  classical
  by_contra hifixed
  have hdisjoint :
      Disjoint (bids i).desired
        (fixed.biUnion fun j => (bids j).desired) := by
    rw [Finset.disjoint_left]
    intro g hgi hgoods
    rcases Finset.mem_biUnion.mp hgoods with ⟨j, hjfixed, hgj⟩
    have hjaccepted : j ∈ accepted := hfixed_subset hjfixed
    have hij : i ≠ j := by
      intro hij
      exact hifixed (by simpa [hij] using hjfixed)
    exact (Finset.disjoint_left.mp
      (haccepted_pairwise hi hjaccepted hij)) hgi hgj
  exact hnot hdisjoint

theorem singleMindedGreedyStep_filter_eq_of_not_disjoint_fixedGoods
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted fixed : Finset Bidder) (i : Bidder)
    (hi :
      ¬ Disjoint (bids i).desired
        (fixed.biUnion fun j => (bids j).desired)) :
    (singleMindedGreedyStep bids accepted i).filter
        (fun j =>
          Disjoint (bids j).desired
            (fixed.biUnion fun k => (bids k).desired)) =
      accepted.filter
        (fun j =>
          Disjoint (bids j).desired
            (fixed.biUnion fun k => (bids k).desired)) := by
  classical
  by_cases hconf :
      (singleMindedGreedyConflictingAccepted bids accepted i).Nonempty
  · simp [singleMindedGreedyStep, hconf]
  · ext j
    by_cases hji : j = i
    · subst j
      simp [singleMindedGreedyStep, hconf, hi]
    · simp [singleMindedGreedyStep, hconf, hji]

theorem singleMindedGreedyStep_filter_eq_of_disjoint_fixedGoods
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted fixed : Finset Bidder) (i : Bidder)
    (haccepted_nonDisjoint_fixed :
      ∀ j,
        j ∈ accepted →
          ¬ Disjoint (bids j).desired
            (fixed.biUnion fun k => (bids k).desired) →
            j ∈ fixed)
    (hi :
      Disjoint (bids i).desired
        (fixed.biUnion fun j => (bids j).desired)) :
    singleMindedGreedyStep bids
        (accepted.filter
          (fun j =>
            Disjoint (bids j).desired
              (fixed.biUnion fun k => (bids k).desired))) i =
      (singleMindedGreedyStep bids accepted i).filter
        (fun j =>
          Disjoint (bids j).desired
            (fixed.biUnion fun k => (bids k).desired)) := by
  classical
  let fixedGoods : Finset Item := fixed.biUnion fun k => (bids k).desired
  let P : Bidder → Prop := fun j => Disjoint (bids j).desired fixedGoods
  have hfixed_goods :
      ∀ j, j ∈ fixed → (bids j).desired ⊆ fixedGoods := by
    intro j hj g hg
    exact Finset.mem_biUnion.mpr ⟨j, hj, hg⟩
  have hconf_iff :
      (singleMindedGreedyConflictingAccepted bids
          (accepted.filter P) i).Nonempty ↔
        (singleMindedGreedyConflictingAccepted bids accepted i).Nonempty := by
    constructor
    · intro hconf
      rcases hconf with ⟨j, hj⟩
      have hjprops :
          j ∈ accepted.filter P ∧ SingleMindedBidsConflict bids i j := by
        simpa [singleMindedGreedyConflictingAccepted,
          SingleMindedBidsConflict] using hj
      refine ⟨j, ?_⟩
      simpa [singleMindedGreedyConflictingAccepted,
        SingleMindedBidsConflict] using
        ⟨(Finset.mem_filter.mp hjprops.1).1, hjprops.2⟩
    · intro hconf
      rcases hconf with ⟨j, hj⟩
      have hjprops :
          j ∈ accepted ∧ SingleMindedBidsConflict bids i j := by
        simpa [singleMindedGreedyConflictingAccepted,
          SingleMindedBidsConflict] using hj
      have hjP : P j := by
        by_contra hjnot
        have hjfixed : j ∈ fixed :=
          haccepted_nonDisjoint_fixed j hjprops.1 (by
            simpa [P, fixedGoods] using hjnot)
        rcases hjprops.2 with ⟨g, hg⟩
        have hgi : g ∈ (bids i).desired := (Finset.mem_inter.mp hg).1
        have hgj : g ∈ (bids j).desired := (Finset.mem_inter.mp hg).2
        have hggoods : g ∈ fixedGoods := hfixed_goods j hjfixed hgj
        exact (Finset.disjoint_left.mp hi) hgi (by
          simpa [fixedGoods] using hggoods)
      refine ⟨j, ?_⟩
      simpa [singleMindedGreedyConflictingAccepted,
        SingleMindedBidsConflict, P] using
        ⟨⟨hjprops.1, hjP⟩, hjprops.2⟩
  by_cases hconf :
      (singleMindedGreedyConflictingAccepted bids accepted i).Nonempty
  · have hconf_filter :
        (singleMindedGreedyConflictingAccepted bids
          (accepted.filter P) i).Nonempty := hconf_iff.mpr hconf
    simp [singleMindedGreedyStep, hconf, hconf_filter, P, fixedGoods]
  · have hconf_filter :
        ¬ (singleMindedGreedyConflictingAccepted bids
          (accepted.filter P) i).Nonempty := fun h => hconf (hconf_iff.mp h)
    ext j
    by_cases hji : j = i
    · subst j
      simp [singleMindedGreedyStep, hconf, hconf_filter, P, fixedGoods, hi]
    · simp [singleMindedGreedyStep, hconf, hconf_filter, P, fixedGoods, hji]

/--
Filter a greedy order by bids disjoint from a fixed set of accepted goods. If
the fixed bids are contained in the final greedy set, the filtered greedy run
returns exactly the final greedy set filtered by the same disjointness
predicate.
-/
theorem singleMindedGreedyAcceptedFromState_filter_disjoint_fixedGoods
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (fixed : Finset Bidder) :
    ∀ accepted order,
      fixed ⊆ singleMindedGreedyAcceptedFromState bids accepted order →
        PairwiseDisjointDesired bids
          (singleMindedGreedyAcceptedFromState bids accepted order) →
        singleMindedGreedyAcceptedFromState bids
            (accepted.filter fun i =>
              Disjoint (bids i).desired
                (fixed.biUnion fun j => (bids j).desired))
            (order.filter fun i =>
              Disjoint (bids i).desired
                (fixed.biUnion fun j => (bids j).desired)) =
          (singleMindedGreedyAcceptedFromState bids accepted order).filter
            (fun i =>
              Disjoint (bids i).desired
                (fixed.biUnion fun j => (bids j).desired))
  | accepted, [], _hfixed, _hpairwise => by
      simp [singleMindedGreedyAcceptedFromState]
  | accepted, i :: order, hfixed, hpairwise => by
      classical
      let fixedGoods : Finset Item := fixed.biUnion fun j => (bids j).desired
      let P : Bidder → Prop := fun i => Disjoint (bids i).desired fixedGoods
      let acceptedStep := singleMindedGreedyStep bids accepted i
      have hfixed_tail :
          fixed ⊆ singleMindedGreedyAcceptedFromState bids acceptedStep order := by
        simpa [singleMindedGreedyAcceptedFromState, acceptedStep] using hfixed
      have hpairwise_tail :
          PairwiseDisjointDesired bids
            (singleMindedGreedyAcceptedFromState bids acceptedStep order) := by
        simpa [singleMindedGreedyAcceptedFromState, acceptedStep] using hpairwise
      have hih :=
        singleMindedGreedyAcceptedFromState_filter_disjoint_fixedGoods
          bids fixed acceptedStep order hfixed_tail hpairwise_tail
      have haccepted_nonDisjoint_fixed :
          ∀ j, j ∈ accepted → ¬ P j → j ∈ fixed := by
        intro j hj hjnot
        have hjfinal :
            j ∈ singleMindedGreedyAcceptedFromState bids accepted (i :: order) :=
          singleMindedGreedyAcceptedFromState_contains_initial
            bids accepted (i :: order) hj
        exact
          singleMindedAccepted_mem_fixed_of_not_disjoint_fixedGoods
            (bids := bids) (accepted :=
              singleMindedGreedyAcceptedFromState bids accepted (i :: order))
            (fixed := fixed) hfixed hpairwise hjfinal
            (by simpa [P, fixedGoods] using hjnot)
      by_cases hi : P i
      · have hstep :
            singleMindedGreedyStep bids (accepted.filter P) i =
              acceptedStep.filter P := by
          simpa [P, fixedGoods, acceptedStep] using
            singleMindedGreedyStep_filter_eq_of_disjoint_fixedGoods
              bids accepted fixed i haccepted_nonDisjoint_fixed
              (by simpa [P, fixedGoods] using hi)
        simp [singleMindedGreedyAcceptedFromState, P, fixedGoods, hi,
          acceptedStep] at hih ⊢
        rw [hstep]
        exact hih
      · have hstep :
            acceptedStep.filter P = accepted.filter P := by
          simpa [P, fixedGoods, acceptedStep] using
            singleMindedGreedyStep_filter_eq_of_not_disjoint_fixedGoods
              bids accepted fixed i (by simpa [P, fixedGoods] using hi)
        simp [singleMindedGreedyAcceptedFromState, P, fixedGoods, hi,
          acceptedStep] at hih ⊢
        rw [← hstep]
        exact hih

/--
The source common-bid removal step for the greedy run. If `common` is a set of
nonempty bids accepted by the original greedy run, then filtering the order to
bids disjoint from the goods requested by `common` makes the greedy accepted set
exactly the original greedy set with `common` removed.
-/
theorem singleMindedGreedyAcceptedFromOrder_filter_disjoint_commonGoods
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder)
    (common : Finset Bidder)
    (hcommon_subset :
      common ⊆ singleMindedGreedyAcceptedFromOrder bids order)
    (hcommon_nonempty :
      ∀ i, i ∈ common → (bids i).desired.Nonempty) :
    let greedy := singleMindedGreedyAcceptedFromOrder bids order
    let commonGoods := common.biUnion fun i => (bids i).desired
    singleMindedGreedyAcceptedFromOrder bids
        (order.filter fun i => Disjoint (bids i).desired commonGoods) =
      greedy \ common := by
  classical
  let greedy := singleMindedGreedyAcceptedFromOrder bids order
  let commonGoods := common.biUnion fun i => (bids i).desired
  let P : Bidder → Prop := fun i => Disjoint (bids i).desired commonGoods
  have hpairwise : PairwiseDisjointDesired bids greedy := by
    simpa [greedy] using singleMindedGreedyAccepted_pairwiseDisjoint bids order
  have hfiltered :
      singleMindedGreedyAcceptedFromOrder bids (order.filter P) =
        greedy.filter P := by
    simpa [singleMindedGreedyAcceptedFromOrder, greedy, commonGoods, P] using
      singleMindedGreedyAcceptedFromState_filter_disjoint_fixedGoods
        bids common (∅ : Finset Bidder) order
        (by simpa [singleMindedGreedyAcceptedFromOrder, greedy] using
          hcommon_subset)
        (by simpa [singleMindedGreedyAcceptedFromOrder, greedy] using
          hpairwise)
  change singleMindedGreedyAcceptedFromOrder bids (order.filter P) =
    greedy \ common
  rw [hfiltered]
  ext i
  constructor
  · intro hi
    have higreedy : i ∈ greedy := (Finset.mem_filter.mp hi).1
    have hiP : P i := (Finset.mem_filter.mp hi).2
    have hinot : i ∉ common := by
      intro hicommon
      rcases hcommon_nonempty i hicommon with ⟨g, hg⟩
      have hggoods : g ∈ commonGoods :=
        Finset.mem_biUnion.mpr ⟨i, hicommon, hg⟩
      exact (Finset.disjoint_left.mp hiP) hg hggoods
    exact Finset.mem_sdiff.mpr ⟨higreedy, hinot⟩
  · intro hi
    rcases Finset.mem_sdiff.mp hi with ⟨higreedy, hinot⟩
    refine Finset.mem_filter.mpr ⟨higreedy, ?_⟩
    change Disjoint (bids i).desired commonGoods
    rw [Finset.disjoint_left]
    intro g hgi hggoods
    rcases Finset.mem_biUnion.mp hggoods with ⟨j, hjcommon, hgj⟩
    have hjgreedy : j ∈ greedy := hcommon_subset hjcommon
    have hij : i ≠ j := by
      intro hij
      subst i
      exact hinot hjcommon
    exact (Finset.disjoint_left.mp (hpairwise higreedy hjgreedy hij)) hgi hgj

theorem singleMindedGreedyAllocation_feasible [DecidableEq Bidder]
    [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder)
    (goods : Finset Item)
    (hgoods : ∀ i,
      i ∈ singleMindedGreedyAcceptedFromOrder bids order →
        (bids i).desired ⊆ goods) :
    IsFeasibleBundleAllocation
      (singleMindedGreedyAllocationFromOrder bids order) goods := by
  exact singleMindedAllocation_feasible bids
    (singleMindedGreedyAcceptedFromOrder bids order) goods
    hgoods (singleMindedGreedyAccepted_pairwiseDisjoint bids order)

/--
Greedy critical-price payment formula parameterized by the `n(j)` function:
the first later bid denied because of granted bid `j`.
-/
noncomputable def singleMindedGreedyPaymentFromNextDenied
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder)
    (nextDenied : Bidder → Option Bidder) (j : Bidder) : ℝ :=
  if j ∈ accepted then
    match nextDenied j with
    | none => 0
    | some n => (bids j).bundleSize * (bids n).averageAmountPerGood
  else
    0

theorem singleMindedGreedyPaymentFromNextDenied_eq_zero_of_denied
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder)
    (nextDenied : Bidder → Option Bidder) {j : Bidder}
    (hj : j ∉ accepted) :
    singleMindedGreedyPaymentFromNextDenied bids accepted nextDenied j = 0 := by
  simp [singleMindedGreedyPaymentFromNextDenied, hj]

theorem singleMindedGreedyPaymentFromNextDenied_eq_zero_of_no_next
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder)
    (nextDenied : Bidder → Option Bidder) {j : Bidder}
    (hj : j ∈ accepted) (hnext : nextDenied j = none) :
    singleMindedGreedyPaymentFromNextDenied bids accepted nextDenied j = 0 := by
  simp [singleMindedGreedyPaymentFromNextDenied, hj, hnext]

theorem singleMindedGreedyPaymentFromNextDenied_eq_of_next
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder)
    (nextDenied : Bidder → Option Bidder) {j n : Bidder}
    (hj : j ∈ accepted) (hnext : nextDenied j = some n) :
    singleMindedGreedyPaymentFromNextDenied bids accepted nextDenied j =
      (bids j).bundleSize * (bids n).averageAmountPerGood := by
  simp [singleMindedGreedyPaymentFromNextDenied, hj, hnext]

/--
Boolean test for the greedy payment condition that bid `i` is denied because
of granted bid `j` in a final accepted set.
-/
def singleMindedGreedyDeniedBecauseOfBool [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (j i : Bidder) : Bool :=
  decide (j ∈ accepted) &&
    decide (i ∉ accepted) &&
      decide (((bids i).desired ∩ (bids j).desired).Nonempty) &&
        decide ((singleMindedGreedyConflictingAccepted bids (accepted.erase j) i) = ∅)

/--
Bid `i` is denied because of granted bid `j` in a final accepted set when `i`
is denied, `j` is accepted and conflicts with `i`, and no accepted bid other
than `j` conflicts with `i`.
-/
def SingleMindedGreedyDeniedBecauseOf [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (j i : Bidder) : Prop :=
  singleMindedGreedyDeniedBecauseOfBool bids accepted j i = true

theorem SingleMindedGreedyDeniedBecauseOf.accepted_blocker
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {accepted : Finset Bidder} {j i : Bidder}
    (h : SingleMindedGreedyDeniedBecauseOf bids accepted j i) :
    j ∈ accepted := by
  have hprops := h
  simp [SingleMindedGreedyDeniedBecauseOf,
    singleMindedGreedyDeniedBecauseOfBool] at hprops
  exact hprops.1.1.1

theorem SingleMindedGreedyDeniedBecauseOf.denied_bid
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {accepted : Finset Bidder} {j i : Bidder}
    (h : SingleMindedGreedyDeniedBecauseOf bids accepted j i) :
    i ∉ accepted := by
  have hprops := h
  simp [SingleMindedGreedyDeniedBecauseOf,
    singleMindedGreedyDeniedBecauseOfBool] at hprops
  exact hprops.1.1.2

theorem SingleMindedGreedyDeniedBecauseOf.conflict
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {accepted : Finset Bidder} {j i : Bidder}
    (h : SingleMindedGreedyDeniedBecauseOf bids accepted j i) :
    SingleMindedBidsConflict bids i j := by
  have hprops := h
  simp [SingleMindedGreedyDeniedBecauseOf,
    singleMindedGreedyDeniedBecauseOfBool] at hprops
  simpa [SingleMindedBidsConflict] using hprops.1.2

theorem SingleMindedGreedyDeniedBecauseOf.no_other_conflict
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {accepted : Finset Bidder} {j i : Bidder}
    (h : SingleMindedGreedyDeniedBecauseOf bids accepted j i) :
    singleMindedGreedyConflictingAccepted bids (accepted.erase j) i = ∅ := by
  have hprops := h
  simp [SingleMindedGreedyDeniedBecauseOf,
    singleMindedGreedyDeniedBecauseOfBool] at hprops
  exact hprops.2

/--
The greedy payment `n(j)` candidate search inside a suffix known to follow
`j` in the greedy order.
-/
def singleMindedGreedyFirstDeniedBecauseOfInSuffix
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (suffix : List Bidder) (j : Bidder) :
    Option Bidder :=
  suffix.find? fun i =>
    singleMindedGreedyDeniedBecauseOfBool bids accepted j i

theorem list_find?_some_mem {α : Type*} {p : α → Bool}
    {xs : List α} {x : α} (h : xs.find? p = some x) :
    x ∈ xs := by
  induction xs with
  | nil =>
      simp at h
  | cons y ys ih =>
      by_cases hy : p y = true
      · simp [List.find?, hy] at h
        subst h
        simp
      · simp [List.find?, hy] at h
        exact List.mem_cons_of_mem y (ih h)

theorem singleMindedGreedyFirstDeniedBecauseOfInSuffix_some_spec
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (suffix : List Bidder) (j n : Bidder)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfInSuffix
        bids accepted suffix j = some n) :
    n ∈ suffix ∧ SingleMindedGreedyDeniedBecauseOf bids accepted j n := by
  constructor
  · exact list_find?_some_mem hnext
  · exact List.find?_some hnext

theorem singleMindedGreedyFirstDeniedBecauseOfInSuffix_none_no_candidate
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (suffix : List Bidder) (j : Bidder)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfInSuffix
        bids accepted suffix j = none) :
    ∀ i, i ∈ suffix →
      ¬ SingleMindedGreedyDeniedBecauseOf bids accepted j i := by
  intro i hi hcandidate
  have hnone :=
    (List.find?_eq_none.mp hnext) i hi
  exact hnone hcandidate

/--
Boolean prefix-state version of the greedy payment condition. Bid `i` is
denied because of accepted bid `j` at the moment `i` is considered when `j`
is accepted, `i` conflicts with `j`, and removing `j` leaves no accepted
conflict.
-/
def singleMindedGreedyDeniedBecauseOfAtStateBool
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBefore : Finset Bidder) (j i : Bidder) : Bool :=
  decide (j ∈ acceptedBefore) &&
    decide (i ∉ acceptedBefore) &&
      decide (((bids i).desired ∩ (bids j).desired).Nonempty) &&
        decide
          ((singleMindedGreedyConflictingAccepted
              bids (acceptedBefore.erase j) i) = ∅)

/--
Prefix-state version of the greedy payment condition that bid `i` is denied
because of accepted bid `j`.
-/
def SingleMindedGreedyDeniedBecauseOfAtState
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBefore : Finset Bidder) (j i : Bidder) : Prop :=
  singleMindedGreedyDeniedBecauseOfAtStateBool
    bids acceptedBefore j i = true

theorem SingleMindedGreedyDeniedBecauseOfAtState.accepted_blocker
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {acceptedBefore : Finset Bidder} {j i : Bidder}
    (h : SingleMindedGreedyDeniedBecauseOfAtState bids acceptedBefore j i) :
    j ∈ acceptedBefore := by
  have hprops := h
  simp [SingleMindedGreedyDeniedBecauseOfAtState,
    singleMindedGreedyDeniedBecauseOfAtStateBool] at hprops
  exact hprops.1.1.1

theorem SingleMindedGreedyDeniedBecauseOfAtState.denied_bid
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {acceptedBefore : Finset Bidder} {j i : Bidder}
    (h : SingleMindedGreedyDeniedBecauseOfAtState bids acceptedBefore j i) :
    i ∉ acceptedBefore := by
  have hprops := h
  simp [SingleMindedGreedyDeniedBecauseOfAtState,
    singleMindedGreedyDeniedBecauseOfAtStateBool] at hprops
  exact hprops.1.1.2

theorem SingleMindedGreedyDeniedBecauseOfAtState.conflict
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {acceptedBefore : Finset Bidder} {j i : Bidder}
    (h : SingleMindedGreedyDeniedBecauseOfAtState bids acceptedBefore j i) :
    SingleMindedBidsConflict bids i j := by
  have hprops := h
  simp [SingleMindedGreedyDeniedBecauseOfAtState,
    singleMindedGreedyDeniedBecauseOfAtStateBool] at hprops
  simpa [SingleMindedBidsConflict] using hprops.1.2

theorem SingleMindedGreedyDeniedBecauseOfAtState.no_other_conflict
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {acceptedBefore : Finset Bidder} {j i : Bidder}
    (h : SingleMindedGreedyDeniedBecauseOfAtState bids acceptedBefore j i) :
    singleMindedGreedyConflictingAccepted
      bids (acceptedBefore.erase j) i = ∅ := by
  have hprops := h
  simp [SingleMindedGreedyDeniedBecauseOfAtState,
    singleMindedGreedyDeniedBecauseOfAtStateBool] at hprops
  exact hprops.2

theorem singleMindedGreedyStep_erase_of_no_deniedBecauseOfAtState
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → SingleMindedBid Item}
    {acceptedWithJ : Finset Bidder} {j i : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hi : i ≠ j)
    (hno :
      ¬ SingleMindedGreedyDeniedBecauseOfAtState bids acceptedWithJ j i) :
    singleMindedGreedyStep bidsLow (acceptedWithJ.erase j) i =
      (singleMindedGreedyStep bids acceptedWithJ i).erase j := by
  classical
  have hconf_eq :
      singleMindedGreedyConflictingAccepted
          bidsLow (acceptedWithJ.erase j) i =
        (singleMindedGreedyConflictingAccepted
          bids acceptedWithJ i).erase j :=
    singleMindedGreedyConflictingAccepted_erase_of_same_nonblocker
      (bids := bids) (bidsLow := bidsLow)
      (acceptedWithJ := acceptedWithJ) (j := j) (i := i) hsame hi
  by_cases hhigh :
      (singleMindedGreedyConflictingAccepted
        bids acceptedWithJ i).Nonempty
  · by_cases hlow :
      (singleMindedGreedyConflictingAccepted
        bidsLow (acceptedWithJ.erase j) i).Nonempty
    · simp [singleMindedGreedyStep, hhigh, hlow]
    · have hlow_empty :
          singleMindedGreedyConflictingAccepted
            bidsLow (acceptedWithJ.erase j) i = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hlow
      have herase_empty :
          (singleMindedGreedyConflictingAccepted
            bids acceptedWithJ i).erase j = ∅ := by
        simpa [hconf_eq] using hlow_empty
      by_cases hiacc : i ∈ acceptedWithJ
      · have hiacc_erase : i ∈ acceptedWithJ.erase j :=
          Finset.mem_erase.mpr ⟨hi, hiacc⟩
        simp [singleMindedGreedyStep, hhigh, hlow, hiacc_erase]
      · rcases hhigh with ⟨k, hkconflict⟩
        have hk_eq : k = j := by
          by_contra hkj
          have hk_erase :
              k ∈ (singleMindedGreedyConflictingAccepted
                bids acceptedWithJ i).erase j :=
            Finset.mem_erase.mpr ⟨hkj, hkconflict⟩
          simpa [herase_empty] using hk_erase
        subst k
        have hjprops :
            j ∈ acceptedWithJ ∧
              ((bids i).desired ∩ (bids j).desired).Nonempty := by
          simpa [singleMindedGreedyConflictingAccepted] using hkconflict
        have hjacc : j ∈ acceptedWithJ := hjprops.1
        have hconflict :
            ((bids i).desired ∩ (bids j).desired).Nonempty := hjprops.2
        have hno_other :
            singleMindedGreedyConflictingAccepted
              bids (acceptedWithJ.erase j) i = ∅ := by
          simpa [singleMindedGreedyConflictingAccepted_erase bids acceptedWithJ j i]
            using herase_empty
        have hdenied :
            SingleMindedGreedyDeniedBecauseOfAtState bids acceptedWithJ j i := by
          simp [SingleMindedGreedyDeniedBecauseOfAtState,
            singleMindedGreedyDeniedBecauseOfAtStateBool,
            hjacc, hiacc, hconflict, hno_other]
        exact False.elim (hno hdenied)
  · have hhigh_empty :
        singleMindedGreedyConflictingAccepted bids acceptedWithJ i = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hhigh
    have hlow_empty :
        singleMindedGreedyConflictingAccepted
          bidsLow (acceptedWithJ.erase j) i = ∅ := by
      simp [hconf_eq, hhigh_empty]
    have hlow :
        ¬ (singleMindedGreedyConflictingAccepted
          bidsLow (acceptedWithJ.erase j) i).Nonempty := by
      simpa [hlow_empty] using
        (Finset.not_nonempty_empty : ¬ (∅ : Finset Bidder).Nonempty)
    have herase_insert :
        insert i (acceptedWithJ.erase j) = (insert i acceptedWithJ).erase j := by
      ext x
      by_cases hxj : x = j
      · subst x
        have hji : j ≠ i := fun h => hi h.symm
        simp [hji]
      · by_cases hxi : x = i
        · subst x
          simp [hi]
        · simp [hxj, hxi]
    simpa [singleMindedGreedyStep, hhigh, hlow] using herase_insert

/--
Scan a suffix after bid `j`, updating the greedy accepted state, and return the
first later bid that is denied because of `j` in the prefix-local sense of
greedy payment.
-/
def singleMindedGreedyFirstDeniedBecauseOfFromState
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (suffix : List Bidder) (j : Bidder) : Option Bidder :=
  match suffix with
  | [] => none
  | i :: rest =>
      match singleMindedGreedyDeniedBecauseOfAtStateBool
          bids acceptedBeforeSuffix j i with
      | true => some i
      | false =>
          singleMindedGreedyFirstDeniedBecauseOfFromState bids
            (singleMindedGreedyStep bids acceptedBeforeSuffix i) rest j

/--
Bid `i` is a greedy payment denied-because-of candidate somewhere in a suffix,
where the accepted state is the greedy state obtained from the supplied initial
state and the preceding part of the suffix.
-/
def SingleMindedGreedyDeniedBecauseOfInSuffixFromState
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (suffix : List Bidder) (j i : Bidder) : Prop :=
  ∃ pre post,
    suffix = pre ++ (i :: post) ∧
      SingleMindedGreedyDeniedBecauseOfAtState bids
        (singleMindedGreedyAcceptedFromState
          bids acceptedBeforeSuffix pre) j i

theorem SingleMindedGreedyDeniedBecauseOfInSuffixFromState.mem_suffix
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {acceptedBeforeSuffix : Finset Bidder}
    {suffix : List Bidder} {j i : Bidder}
    (h :
      SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids acceptedBeforeSuffix suffix j i) :
    i ∈ suffix := by
  rcases h with ⟨pre, post, hsuffix, _hdenied⟩
  rw [hsuffix]
  simp

theorem SingleMindedGreedyDeniedBecauseOfAtState.inSuffixFromState_cons
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {acceptedBeforeSuffix : Finset Bidder}
    {suffix : List Bidder} {j i : Bidder}
    (h :
      SingleMindedGreedyDeniedBecauseOfAtState
        bids acceptedBeforeSuffix j i) :
    SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
      acceptedBeforeSuffix (i :: suffix) j i := by
  refine ⟨[], suffix, ?_, ?_⟩
  · simp
  · simpa [singleMindedGreedyAcceptedFromState] using h

theorem SingleMindedGreedyDeniedBecauseOfInSuffixFromState.cons_step
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {acceptedBeforeSuffix : Finset Bidder}
    {suffix : List Bidder} {a j i : Bidder}
    (h :
      SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
        (singleMindedGreedyStep bids acceptedBeforeSuffix a) suffix j i) :
    SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
      acceptedBeforeSuffix (a :: suffix) j i := by
  rcases h with ⟨pre, post, hsuffix, hstate⟩
  refine ⟨a :: pre, post, ?_, ?_⟩
  · simp [hsuffix]
  · simpa [singleMindedGreedyAcceptedFromState] using hstate

theorem SingleMindedGreedyDeniedBecauseOfInSuffixFromState.append_right
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {acceptedBeforeSuffix : Finset Bidder}
    {suffix : List Bidder} {j i : Bidder}
    (h :
      SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
        acceptedBeforeSuffix suffix j i)
    (tail : List Bidder) :
    SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
      acceptedBeforeSuffix (suffix ++ tail) j i := by
  rcases h with ⟨pre, post, hsuffix, hstate⟩
  refine ⟨pre, post ++ tail, ?_, hstate⟩
  rw [hsuffix]
  simp [List.append_assoc]

theorem singleMindedGreedyAcceptedFromState_erase_prefix_of_no_earlier_candidate
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder) (pref : List Bidder) {j : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hjpref : j ∉ pref)
    (hno :
      ∀ i, i ∈ pref →
        ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState
          bids acceptedWithJ pref j i) :
    singleMindedGreedyAcceptedFromState bidsLow
        (acceptedWithJ.erase j) pref =
      (singleMindedGreedyAcceptedFromState bids acceptedWithJ pref).erase j := by
  induction pref generalizing acceptedWithJ with
  | nil =>
      simp [singleMindedGreedyAcceptedFromState]
  | cons a rest ih =>
      have ha_ne_j : a ≠ j := by
        intro haj
        exact hjpref (by simp [haj])
      have hrest_not : j ∉ rest := by
        intro hjrest
        exact hjpref (by simp [hjrest])
      have hno_head :
          ¬ SingleMindedGreedyDeniedBecauseOfAtState
            bids acceptedWithJ j a := by
        intro hdenied
        exact hno a (by simp)
          (hdenied.inSuffixFromState_cons (suffix := rest))
      have hstep :
          singleMindedGreedyStep bidsLow (acceptedWithJ.erase j) a =
            (singleMindedGreedyStep bids acceptedWithJ a).erase j :=
        singleMindedGreedyStep_erase_of_no_deniedBecauseOfAtState
          (bids := bids) (bidsLow := bidsLow)
          (acceptedWithJ := acceptedWithJ) (j := j) (i := a)
          hsame ha_ne_j hno_head
      have hno_tail :
          ∀ i, i ∈ rest →
            ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState
              bids (singleMindedGreedyStep bids acceptedWithJ a) rest j i := by
        intro i hi hdenied
        exact hno i (by simp [hi]) hdenied.cons_step
      have htail :=
        ih
          (acceptedWithJ := singleMindedGreedyStep bids acceptedWithJ a)
          hrest_not hno_tail
      simpa [singleMindedGreedyAcceptedFromState, hstep] using htail

theorem singleMindedGreedyFirstDeniedBecauseOfFromState_some_spec
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (suffix : List Bidder) (j n : Bidder)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedBeforeSuffix suffix j = some n) :
    n ∈ suffix ∧
      SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids acceptedBeforeSuffix suffix j n := by
  induction suffix generalizing acceptedBeforeSuffix with
  | nil =>
      simp [singleMindedGreedyFirstDeniedBecauseOfFromState] at hnext
  | cons i rest ih =>
      unfold singleMindedGreedyFirstDeniedBecauseOfFromState at hnext
      cases hcandidate :
          singleMindedGreedyDeniedBecauseOfAtStateBool
            bids acceptedBeforeSuffix j i
      · simp [hcandidate] at hnext
        have hspec := ih
          (acceptedBeforeSuffix :=
            singleMindedGreedyStep bids acceptedBeforeSuffix i) hnext
        constructor
        · exact List.mem_cons_of_mem i hspec.1
        · rcases hspec.2 with ⟨pre, post, hsuffix, hdenied⟩
          refine ⟨i :: pre, post, ?_, ?_⟩
          · simp [hsuffix]
          · simpa [singleMindedGreedyAcceptedFromState] using hdenied
      · simp [hcandidate] at hnext
        subst hnext
        constructor
        · simp
        · refine ⟨[], rest, ?_, ?_⟩
          · simp
          · simpa [SingleMindedGreedyDeniedBecauseOfAtState,
              singleMindedGreedyAcceptedFromState] using hcandidate

/--
If the stateful greedy payment search returns `n`, then no earlier bid in a
deduplicated suffix is a denied-because-of candidate.
-/
theorem singleMindedGreedyFirstDeniedBecauseOfFromState_some_no_earlier_candidate
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (pre post : List Bidder) (j n m : Bidder)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedBeforeSuffix (pre ++ n :: post) j = some n)
    (hm : m ∈ pre) :
    ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids acceptedBeforeSuffix (pre ++ n :: post) j m := by
  induction pre generalizing acceptedBeforeSuffix with
  | nil =>
      simp at hm
  | cons a preTail ih =>
      intro hdenied
      have hnodup_tail : (preTail ++ n :: post).Nodup := by
        exact (List.nodup_cons.mp hnodup).2
      unfold singleMindedGreedyFirstDeniedBecauseOfFromState at hnext
      cases hhead :
          singleMindedGreedyDeniedBecauseOfAtStateBool
            bids acceptedBeforeSuffix j a
      · simp [hhead] at hnext
        have hm_cases : m = a ∨ m ∈ preTail := by
          simpa using hm
        rcases hm_cases with rfl | hm_tail
        · rcases hdenied with ⟨preBefore, postAfter, hsuffix, hstate⟩
          cases preBefore with
          | nil =>
              simp [SingleMindedGreedyDeniedBecauseOfAtState,
                singleMindedGreedyAcceptedFromState, hhead] at hstate
          | cons first preBeforeTail =>
              injection hsuffix with hfirst htail
              subst first
              have hm_tail : m ∈ preTail ++ n :: post := by
                change m ∈ preTail.append (n :: post)
                rw [htail]
                simp
              exact (List.nodup_cons.mp hnodup).1 hm_tail
        · have hdenied_tail :
              SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
                (singleMindedGreedyStep bids acceptedBeforeSuffix a)
                (preTail ++ n :: post) j m := by
            rcases hdenied with ⟨preBefore, postAfter, hsuffix, hstate⟩
            cases preBefore with
            | nil =>
                injection hsuffix with ham _htail
                subst m
                exact False.elim
                  ((List.nodup_cons.mp hnodup).1 (by simp [hm_tail]))
            | cons first preBeforeTail =>
                injection hsuffix with hfirst htail
                subst first
                refine ⟨preBeforeTail, postAfter, htail, ?_⟩
                simpa [singleMindedGreedyAcceptedFromState] using hstate
          exact
            (ih
              (acceptedBeforeSuffix :=
                singleMindedGreedyStep bids acceptedBeforeSuffix a)
              hnodup_tail hnext hm_tail) hdenied_tail
      · simp [hhead] at hnext
        subst n
        exact (List.nodup_cons.mp hnodup).1 (by simp)

theorem singleMindedGreedyFirstDeniedBecauseOfFromState_some_at_split
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (pre post : List Bidder) (j n : Bidder)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedBeforeSuffix (pre ++ n :: post) j = some n) :
    SingleMindedGreedyDeniedBecauseOfAtState bids
      (singleMindedGreedyAcceptedFromState bids acceptedBeforeSuffix pre) j n := by
  induction pre generalizing acceptedBeforeSuffix with
  | nil =>
      unfold singleMindedGreedyFirstDeniedBecauseOfFromState at hnext
      cases hcandidate :
          singleMindedGreedyDeniedBecauseOfAtStateBool
            bids acceptedBeforeSuffix j n
      · simp [hcandidate] at hnext
        have hn_post :
            n ∈ post :=
          (singleMindedGreedyFirstDeniedBecauseOfFromState_some_spec
            bids
            (singleMindedGreedyStep bids acceptedBeforeSuffix n)
            post j n hnext).1
        exact False.elim ((List.nodup_cons.mp hnodup).1 hn_post)
      · simpa [SingleMindedGreedyDeniedBecauseOfAtState,
          singleMindedGreedyAcceptedFromState] using hcandidate
  | cons a rest ih =>
      have hnodup_tail : (rest ++ n :: post).Nodup := by
        simpa using (List.nodup_cons.mp hnodup).2
      unfold singleMindedGreedyFirstDeniedBecauseOfFromState at hnext
      cases hcandidate :
          singleMindedGreedyDeniedBecauseOfAtStateBool
            bids acceptedBeforeSuffix j a
      · simp [hcandidate] at hnext
        have htail :=
          ih
            (acceptedBeforeSuffix :=
              singleMindedGreedyStep bids acceptedBeforeSuffix a)
            hnodup_tail hnext
        simpa [singleMindedGreedyAcceptedFromState] using htail
      · simp [hcandidate] at hnext
        have han : a = n := by
          simpa using hnext
        subst a
        exact False.elim ((List.nodup_cons.mp hnodup).1 (by simp))

theorem singleMindedGreedyAcceptedFromState_erase_prefix_before_nextDenied
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder) (pre post : List Bidder) {j n : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hjpre : j ∉ pre)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: post) j = some n) :
    singleMindedGreedyAcceptedFromState bidsLow
        (acceptedWithJ.erase j) pre =
      (singleMindedGreedyAcceptedFromState bids acceptedWithJ pre).erase j := by
  apply
    singleMindedGreedyAcceptedFromState_erase_prefix_of_no_earlier_candidate
      (bids := bids) (bidsLow := bidsLow)
      acceptedWithJ pre hsame hjpre
  intro m hm hdenied
  have hdenied_whole :
      SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
        acceptedWithJ (pre ++ n :: post) j m := by
    simpa using hdenied.append_right (n :: post)
  exact
    (singleMindedGreedyFirstDeniedBecauseOfFromState_some_no_earlier_candidate
      bids acceptedWithJ pre post j n m hnodup hnext hm) hdenied_whole

theorem singleMindedGreedyAcceptedFromState_mem_nextDenied_after_erasing_blocker_at_split
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder) (pre post : List Bidder) {j n : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hjpre : j ∉ pre)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: post) j = some n) :
    n ∈ singleMindedGreedyAcceptedFromState bidsLow
      (acceptedWithJ.erase j) (pre ++ [n]) := by
  let highBefore : Finset Bidder :=
    singleMindedGreedyAcceptedFromState bids acceptedWithJ pre
  let lowBefore : Finset Bidder :=
    singleMindedGreedyAcceptedFromState bidsLow (acceptedWithJ.erase j) pre
  have hsplit :
      SingleMindedGreedyDeniedBecauseOfAtState bids highBefore j n := by
    simpa [highBefore] using
      singleMindedGreedyFirstDeniedBecauseOfFromState_some_at_split
        bids acceptedWithJ pre post j n hnodup hnext
  have hn_ne_j : n ≠ j := by
    intro hnj
    subst n
    exact hsplit.denied_bid hsplit.accepted_blocker
  have hprefix :
      lowBefore = highBefore.erase j := by
    simpa [highBefore, lowBefore] using
      singleMindedGreedyAcceptedFromState_erase_prefix_before_nextDenied
        (bids := bids) (bidsLow := bidsLow)
        acceptedWithJ pre post hsame hjpre hnodup hnext
  have hconf_low_empty :
      singleMindedGreedyConflictingAccepted bidsLow lowBefore n = ∅ := by
    have hconf_congr :
        singleMindedGreedyConflictingAccepted bidsLow (highBefore.erase j) n =
          singleMindedGreedyConflictingAccepted bids (highBefore.erase j) n :=
      singleMindedGreedyConflictingAccepted_congr
        (bids := bids) (bids' := bidsLow)
        (accepted := highBefore.erase j) (i := n)
        (hsame n hn_ne_j)
        (fun k hk => hsame k (Finset.mem_erase.mp hk).1)
    rw [hprefix, hconf_congr]
    exact hsplit.no_other_conflict
  have hconf_low :
      ¬ (singleMindedGreedyConflictingAccepted bidsLow lowBefore n).Nonempty := by
    simpa [hconf_low_empty] using
      (Finset.not_nonempty_empty : ¬ (∅ : Finset Bidder).Nonempty)
  have hn_step : n ∈ singleMindedGreedyStep bidsLow lowBefore n := by
    simp [singleMindedGreedyStep, hconf_low]
  rw [singleMindedGreedyAcceptedFromState_append]
  simp [singleMindedGreedyAcceptedFromState]
  exact hn_step

theorem singleMindedGreedyAcceptedFromState_mem_nextDenied_after_erasing_blocker
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder) (pre post : List Bidder) {j n : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hjpre : j ∉ pre)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: post) j = some n) :
    n ∈ singleMindedGreedyAcceptedFromState bidsLow
      (acceptedWithJ.erase j) (pre ++ n :: post) := by
  let highBefore : Finset Bidder :=
    singleMindedGreedyAcceptedFromState bids acceptedWithJ pre
  let lowBefore : Finset Bidder :=
    singleMindedGreedyAcceptedFromState bidsLow (acceptedWithJ.erase j) pre
  have hsplit :
      SingleMindedGreedyDeniedBecauseOfAtState bids highBefore j n := by
    simpa [highBefore] using
      singleMindedGreedyFirstDeniedBecauseOfFromState_some_at_split
        bids acceptedWithJ pre post j n hnodup hnext
  have hn_ne_j : n ≠ j := by
    intro hnj
    subst n
    exact hsplit.denied_bid hsplit.accepted_blocker
  have hprefix :
      lowBefore = highBefore.erase j := by
    simpa [highBefore, lowBefore] using
      singleMindedGreedyAcceptedFromState_erase_prefix_before_nextDenied
        (bids := bids) (bidsLow := bidsLow)
        acceptedWithJ pre post hsame hjpre hnodup hnext
  have hconf_low_empty :
      singleMindedGreedyConflictingAccepted bidsLow lowBefore n = ∅ := by
    have hconf_congr :
        singleMindedGreedyConflictingAccepted bidsLow (highBefore.erase j) n =
          singleMindedGreedyConflictingAccepted bids (highBefore.erase j) n :=
      singleMindedGreedyConflictingAccepted_congr
        (bids := bids) (bids' := bidsLow)
        (accepted := highBefore.erase j) (i := n)
        (hsame n hn_ne_j)
        (fun k hk => hsame k (Finset.mem_erase.mp hk).1)
    rw [hprefix, hconf_congr]
    exact hsplit.no_other_conflict
  have hconf_low :
      ¬ (singleMindedGreedyConflictingAccepted bidsLow lowBefore n).Nonempty := by
    simpa [hconf_low_empty] using
      (Finset.not_nonempty_empty : ¬ (∅ : Finset Bidder).Nonempty)
  have hn_step : n ∈ singleMindedGreedyStep bidsLow lowBefore n := by
    simp [singleMindedGreedyStep, hconf_low]
  rw [singleMindedGreedyAcceptedFromState_append]
  simp [singleMindedGreedyAcceptedFromState]
  exact
    singleMindedGreedyAcceptedFromState_contains_initial bidsLow
      (singleMindedGreedyStep bidsLow lowBefore n) post hn_step

theorem singleMindedGreedyAcceptedFromState_rejects_nextDenied_after_erasing_blocker
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder)
    (pre nextPost between tail : List Bidder) {j n : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hjpre : j ∉ pre)
    (hjbetween : j ∉ between)
    (hjtail : j ∉ tail)
    (hnodup : (pre ++ n :: nextPost).Nodup)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n)
    (hconflict : SingleMindedBidsConflict bidsLow j n) :
    j ∉ singleMindedGreedyAcceptedFromState bidsLow (acceptedWithJ.erase j)
      (((pre ++ [n]) ++ between) ++ j :: tail) := by
  have hsplit :
      SingleMindedGreedyDeniedBecauseOfAtState bids
        (singleMindedGreedyAcceptedFromState bids acceptedWithJ pre) j n :=
    singleMindedGreedyFirstDeniedBecauseOfFromState_some_at_split
      bids acceptedWithJ pre nextPost j n hnodup hnext
  have hn_ne_j : n ≠ j := by
    intro hnj
    subst n
    exact hsplit.denied_bid hsplit.accepted_blocker
  have hn_split :
      n ∈ singleMindedGreedyAcceptedFromState bidsLow
        (acceptedWithJ.erase j) (pre ++ [n]) :=
    singleMindedGreedyAcceptedFromState_mem_nextDenied_after_erasing_blocker_at_split
      acceptedWithJ pre nextPost hsame hjpre hnodup hnext
  have hn_pref :
      n ∈ singleMindedGreedyAcceptedFromState bidsLow
        (acceptedWithJ.erase j) ((pre ++ [n]) ++ between) := by
    rw [singleMindedGreedyAcceptedFromState_append]
    exact singleMindedGreedyAcceptedFromState_contains_initial bidsLow
      (singleMindedGreedyAcceptedFromState bidsLow
        (acceptedWithJ.erase j) (pre ++ [n]))
      between hn_split
  have hjpref : j ∉ (pre ++ [n]) ++ between := by
    intro hjmem
    rw [List.mem_append] at hjmem
    rcases hjmem with hpre_n | hbetween
    · rw [List.mem_append] at hpre_n
      rcases hpre_n with hpre | hnlist
      · exact hjpre hpre
      · have hjn : j = n := by simpa using hnlist
        exact hn_ne_j hjn.symm
    · exact hjbetween hbetween
  exact
    singleMindedGreedyAcceptedFromState_rejects_after_prefix_conflict
      bidsLow (acceptedWithJ.erase j) ((pre ++ [n]) ++ between) tail
      hn_pref (by simp) hjpref hjtail hconflict

theorem singleMindedGreedyAcceptedFromState_accepts_after_erasing_blocker_of_no_candidate_prefix
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsHigh : Bidder → SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder) (pref tail : List Bidder) {j : Bidder}
    (hsame : ∀ k, k ≠ j → bidsHigh k = bids k)
    (hjdesired : (bidsHigh j).desired = (bids j).desired)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hjpref : j ∉ pref)
    (hno :
      ∀ i, i ∈ pref →
        ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState
          bids acceptedWithJ pref j i) :
    j ∈ singleMindedGreedyAcceptedFromState bidsHigh
      (acceptedWithJ.erase j) (pref ++ j :: tail) := by
  let highBefore : Finset Bidder :=
    singleMindedGreedyAcceptedFromState bids acceptedWithJ pref
  let lowBefore : Finset Bidder :=
    singleMindedGreedyAcceptedFromState bidsHigh (acceptedWithJ.erase j) pref
  have hprefix :
      lowBefore = highBefore.erase j := by
    simpa [highBefore, lowBefore] using
      singleMindedGreedyAcceptedFromState_erase_prefix_of_no_earlier_candidate
        (bids := bids) (bidsLow := bidsHigh)
        acceptedWithJ pref hsame hjpref hno
  have hj_high : j ∈ highBefore := by
    exact singleMindedGreedyAcceptedFromState_contains_initial
      bids acceptedWithJ pref hjaccepted
  have hpairwise_high : PairwiseDisjointDesired bids highBefore := by
    exact singleMindedGreedyAcceptedFromState_pairwiseDisjoint
      bids acceptedWithJ pref hpairwise
  have hno_conf :
      ¬ (singleMindedGreedyConflictingAccepted bidsHigh lowBefore j).Nonempty := by
    intro hnonempty
    rcases hnonempty with ⟨k, hkfilter⟩
    have hkprops :
        k ∈ lowBefore ∧
          ((bidsHigh j).desired ∩ (bidsHigh k).desired).Nonempty := by
      simpa [singleMindedGreedyConflictingAccepted] using hkfilter
    have hk_erase : k ∈ highBefore.erase j := by
      simpa [hprefix] using hkprops.1
    have hk_ne_j : k ≠ j := (Finset.mem_erase.mp hk_erase).1
    have hk_high : k ∈ highBefore := (Finset.mem_erase.mp hk_erase).2
    have hconflict :
        ((bids j).desired ∩ (bids k).desired).Nonempty := by
      simpa [hjdesired, hsame k hk_ne_j] using hkprops.2
    rcases hconflict with ⟨g, hg⟩
    have hg_left : g ∈ (bids j).desired := (Finset.mem_inter.mp hg).1
    have hg_right : g ∈ (bids k).desired := (Finset.mem_inter.mp hg).2
    have hdisjoint := hpairwise_high hj_high hk_high (fun hjk => hk_ne_j hjk.symm)
    rw [Finset.disjoint_left] at hdisjoint
    exact hdisjoint hg_left hg_right
  have hj_step : j ∈ singleMindedGreedyStep bidsHigh lowBefore j := by
    simp [singleMindedGreedyStep, hno_conf]
  rw [singleMindedGreedyAcceptedFromState_append]
  simp [singleMindedGreedyAcceptedFromState]
  exact singleMindedGreedyAcceptedFromState_contains_initial bidsHigh
    (singleMindedGreedyStep bidsHigh lowBefore j) tail hj_step

theorem singleMindedGreedyAcceptedFromState_rejects_nextDenied_after_value_update
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost between tail : List Bidder) {j n : Bidder} (value : ℝ)
    (hjpre : j ∉ pre)
    (hjbetween : j ∉ between)
    (hjtail : j ∉ tail)
    (hnodup : (pre ++ n :: nextPost).Nodup)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n) :
    j ∉ singleMindedGreedyAcceptedFromState
      (singleMindedValueUpdate bids j value) (acceptedWithJ.erase j)
      (((pre ++ [n]) ++ between) ++ j :: tail) := by
  have hsame :
      ∀ k, k ≠ j → singleMindedValueUpdate bids j value k = bids k := by
    intro k hk
    exact singleMindedValueUpdate_same_of_ne bids value hk
  have hsplit :
      SingleMindedGreedyDeniedBecauseOfAtState bids
        (singleMindedGreedyAcceptedFromState bids acceptedWithJ pre) j n :=
    singleMindedGreedyFirstDeniedBecauseOfFromState_some_at_split
      bids acceptedWithJ pre nextPost j n hnodup hnext
  have hconflict_original : SingleMindedBidsConflict bids j n :=
    hsplit.conflict.symm
  have hconflict_updated :
      SingleMindedBidsConflict (singleMindedValueUpdate bids j value) j n :=
    (singleMindedValueUpdate_conflict_iff bids j value j n).2
      hconflict_original
  exact
    singleMindedGreedyAcceptedFromState_rejects_nextDenied_after_erasing_blocker
      acceptedWithJ pre nextPost between tail hsame hjpre hjbetween hjtail
      hnodup hnext hconflict_updated

theorem singleMindedGreedyAcceptedFromState_accepts_after_value_update_of_no_candidate_prefix
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder) (pref tail : List Bidder) {j : Bidder}
    (value : ℝ)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hjpref : j ∉ pref)
    (hno :
      ∀ i, i ∈ pref →
        ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState
          bids acceptedWithJ pref j i) :
    j ∈ singleMindedGreedyAcceptedFromState
      (singleMindedValueUpdate bids j value) (acceptedWithJ.erase j)
      (pref ++ j :: tail) := by
  have hsame :
      ∀ k, k ≠ j → singleMindedValueUpdate bids j value k = bids k := by
    intro k hk
    exact singleMindedValueUpdate_same_of_ne bids value hk
  have hjdesired :
      (singleMindedValueUpdate bids j value j).desired = (bids j).desired := by
    simp
  exact
    singleMindedGreedyAcceptedFromState_accepts_after_erasing_blocker_of_no_candidate_prefix
      acceptedWithJ pref tail hsame hjdesired hjaccepted hpairwise hjpref hno

theorem singleMindedGreedyAcceptedFromState_accepts_after_shrink_of_no_prefix_conflict
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsStrong : Bidder → SingleMindedBid Item}
    (acceptedBefore : Finset Bidder) (pref tail : List Bidder) {j : Bidder}
    (hsame : ∀ k, k ≠ j → bidsStrong k = bids k)
    (hjdesired_subset : (bidsStrong j).desired ⊆ (bids j).desired)
    (hjaccepted : j ∉ acceptedBefore)
    (hjpref : j ∉ pref)
    (hno :
      ¬ (singleMindedGreedyConflictingAccepted
        bids (singleMindedGreedyAcceptedFromState bids acceptedBefore pref) j).Nonempty) :
    j ∈ singleMindedGreedyAcceptedFromState bidsStrong acceptedBefore
      (pref ++ j :: tail) := by
  let oldBefore : Finset Bidder :=
    singleMindedGreedyAcceptedFromState bids acceptedBefore pref
  let strongBefore : Finset Bidder :=
    singleMindedGreedyAcceptedFromState bidsStrong acceptedBefore pref
  have hprefix :
      strongBefore = oldBefore := by
    simpa [oldBefore, strongBefore] using
      singleMindedGreedyAcceptedFromState_congr_of_not_mem
        (bids := bids) (bids' := bidsStrong)
        acceptedBefore pref j hjaccepted hjpref hsame
  have hj_old_before : j ∉ oldBefore :=
    singleMindedGreedyAcceptedFromState_not_mem_of_not_mem_initial_order
      bids acceptedBefore pref hjaccepted hjpref
  have hno_strong :
      ¬ (singleMindedGreedyConflictingAccepted
        bidsStrong strongBefore j).Nonempty := by
    intro hnonempty
    rcases hnonempty with ⟨k, hk⟩
    have hkprops :
        k ∈ strongBefore ∧
          ((bidsStrong j).desired ∩ (bidsStrong k).desired).Nonempty := by
      simpa [singleMindedGreedyConflictingAccepted] using hk
    have hk_old : k ∈ oldBefore := by
      simpa [hprefix] using hkprops.1
    have hkj : k ≠ j := by
      intro h
      subst k
      exact hj_old_before hk_old
    have hconflict_old :
        ((bids j).desired ∩ (bids k).desired).Nonempty := by
      rcases hkprops.2 with ⟨g, hg⟩
      have hg_left : g ∈ (bidsStrong j).desired :=
        (Finset.mem_inter.mp hg).1
      have hg_right : g ∈ (bidsStrong k).desired :=
        (Finset.mem_inter.mp hg).2
      refine ⟨g, ?_⟩
      exact Finset.mem_inter.mpr
        ⟨hjdesired_subset hg_left, by simpa [hsame k hkj] using hg_right⟩
    exact hno ⟨k, by
      simp [singleMindedGreedyConflictingAccepted, oldBefore, hk_old,
        hconflict_old]⟩
  have hj_step : j ∈ singleMindedGreedyStep bidsStrong strongBefore j := by
    simp [singleMindedGreedyStep, hno_strong]
  rw [singleMindedGreedyAcceptedFromState_append]
  simp [singleMindedGreedyAcceptedFromState]
  exact singleMindedGreedyAcceptedFromState_contains_initial bidsStrong
    (singleMindedGreedyStep bidsStrong strongBefore j) tail hj_step

theorem singleMindedGreedyAcceptedFromState_accepts_after_shrink_of_original_accepts_before_move
    [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsStrong : Bidder → SingleMindedBid Item}
    (acceptedBefore : Finset Bidder)
    (pref rest suffix tail : List Bidder) {j : Bidder}
    (hsame : ∀ k, k ≠ j → bidsStrong k = bids k)
    (hjdesired_subset : (bidsStrong j).desired ⊆ (bids j).desired)
    (hjaccepted : j ∉ acceptedBefore)
    (hjpref : j ∉ pref)
    (hjrest : j ∉ rest)
    (hjsuffix : j ∉ suffix)
    (hacc :
      j ∈ singleMindedGreedyAcceptedFromState bids acceptedBefore
        ((pref ++ rest) ++ j :: suffix)) :
    j ∈ singleMindedGreedyAcceptedFromState bidsStrong acceptedBefore
      (pref ++ j :: tail) := by
  have hjpref_rest : j ∉ pref ++ rest := by
    intro hjmem
    rw [List.mem_append] at hjmem
    exact hjmem.elim hjpref hjrest
  have hno :
      ¬ (singleMindedGreedyConflictingAccepted
        bids (singleMindedGreedyAcceptedFromState bids acceptedBefore pref)
        j).Nonempty := by
    intro hconf
    rcases hconf with ⟨n, hnfilter⟩
    have hnprops :
        n ∈ singleMindedGreedyAcceptedFromState bids acceptedBefore pref ∧
          SingleMindedBidsConflict bids j n := by
      simpa [singleMindedGreedyConflictingAccepted,
        SingleMindedBidsConflict] using hnfilter
    have hn_full :
        n ∈ singleMindedGreedyAcceptedFromState bids acceptedBefore
          (pref ++ rest) := by
      rw [singleMindedGreedyAcceptedFromState_append]
      exact singleMindedGreedyAcceptedFromState_contains_initial bids
        (singleMindedGreedyAcceptedFromState bids acceptedBefore pref)
        rest hnprops.1
    have hreject :
        j ∉ singleMindedGreedyAcceptedFromState bids acceptedBefore
          ((pref ++ rest) ++ j :: suffix) :=
      singleMindedGreedyAcceptedFromState_rejects_after_prefix_conflict
        bids acceptedBefore (pref ++ rest) suffix hn_full hjaccepted
        hjpref_rest hjsuffix hnprops.2
    exact hreject hacc
  exact
    singleMindedGreedyAcceptedFromState_accepts_after_shrink_of_no_prefix_conflict
      acceptedBefore pref tail hsame hjdesired_subset hjaccepted hjpref hno

theorem singleMindedGreedyValueUpdate_local_critical_window
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost lowOrder highOrder : List Bidder) {j n : Bidder}
    (lowValue highValue : ℝ)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hjpre : j ∉ pre)
    (hnodup : (pre ++ n :: nextPost).Nodup)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n)
    (hlow_reposition :
      lowValue < (bids j).bundleSize * (bids n).averageAmountPerGood →
        ∃ between tail,
          lowOrder = (((pre ++ [n]) ++ between) ++ j :: tail) ∧
            j ∉ between ∧ j ∉ tail)
    (hhigh_reposition :
      (bids j).bundleSize * (bids n).averageAmountPerGood < highValue →
        ∃ pref rest tail,
          pre = pref ++ rest ∧ highOrder = pref ++ j :: tail) :
    (lowValue < (bids j).bundleSize * (bids n).averageAmountPerGood →
      j ∉ singleMindedGreedyAcceptedFromState
        (singleMindedValueUpdate bids j lowValue) (acceptedWithJ.erase j)
        lowOrder) ∧
    ((bids j).bundleSize * (bids n).averageAmountPerGood < highValue →
      j ∈ singleMindedGreedyAcceptedFromState
        (singleMindedValueUpdate bids j highValue) (acceptedWithJ.erase j)
        highOrder) := by
  constructor
  · intro hlt
    rcases hlow_reposition hlt with
      ⟨between, tail, hlow_order, hjbetween, hjtail⟩
    rw [hlow_order]
    exact
      singleMindedGreedyAcceptedFromState_rejects_nextDenied_after_value_update
        bids acceptedWithJ pre nextPost between tail lowValue hjpre hjbetween
        hjtail hnodup hnext
  · intro hlt
    rcases hhigh_reposition hlt with
      ⟨pref, rest, tail, hpre_eq, hhigh_order⟩
    subst pre
    have hjpref : j ∉ pref := by
      intro hjmem
      exact hjpre (by simp [hjmem])
    have hno :
        ∀ i, i ∈ pref →
          ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState
            bids acceptedWithJ pref j i := by
      intro i hi hdenied
      have hi_pre : i ∈ pref ++ rest := by
        exact List.mem_append.mpr (Or.inl hi)
      have hdenied_whole :
          SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
            acceptedWithJ ((pref ++ rest) ++ n :: nextPost) j i := by
        simpa [List.append_assoc] using
          hdenied.append_right (rest ++ n :: nextPost)
      exact
        (singleMindedGreedyFirstDeniedBecauseOfFromState_some_no_earlier_candidate
          bids acceptedWithJ (pref ++ rest) nextPost j n i hnodup hnext
          hi_pre) hdenied_whole
    rw [hhigh_order]
    exact
      singleMindedGreedyAcceptedFromState_accepts_after_value_update_of_no_candidate_prefix
        bids acceptedWithJ pref tail highValue hjaccepted hpairwise hjpref hno

theorem singleMindedGreedyFirstDeniedBecauseOfFromState_none_no_candidate
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (suffix : List Bidder) (j : Bidder)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedBeforeSuffix suffix j = none) :
    ∀ n, n ∈ suffix →
      ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids acceptedBeforeSuffix suffix j n := by
  induction suffix generalizing acceptedBeforeSuffix with
  | nil =>
      intro n hn
      simp at hn
  | cons i rest ih =>
      unfold singleMindedGreedyFirstDeniedBecauseOfFromState at hnext
      cases hcandidate :
          singleMindedGreedyDeniedBecauseOfAtStateBool
            bids acceptedBeforeSuffix j i
      · simp [hcandidate] at hnext
        intro n _hn hdenied
        rcases hdenied with ⟨pre, post, hsuffix, hstate⟩
        cases pre with
        | nil =>
            simp at hsuffix
            cases hsuffix
            subst n
            simp [SingleMindedGreedyDeniedBecauseOfAtState,
              singleMindedGreedyAcceptedFromState, hcandidate] at hstate
        | cons first preTail =>
            simp at hsuffix
            cases hsuffix
            subst first
            subst rest
            have hn_rest : n ∈ preTail ++ n :: post := by
              simp
            have hdenied_rest :
                SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
                  (singleMindedGreedyStep bids acceptedBeforeSuffix i)
                  (preTail ++ n :: post) j n := by
              refine ⟨preTail, post, rfl, ?_⟩
              simpa [singleMindedGreedyAcceptedFromState] using hstate
            exact
              (ih
                (acceptedBeforeSuffix :=
                  singleMindedGreedyStep bids acceptedBeforeSuffix i)
                hnext n hn_rest) hdenied_rest
      · simp [hcandidate] at hnext

/--
greedy payment `n(j)` from an explicit split of the sorted order into bids
before `j`, bid `j`, and the suffix after `j`.
-/
def singleMindedGreedyNextDeniedFromSplit
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j : Bidder) : Option Bidder :=
  singleMindedGreedyFirstDeniedBecauseOfFromState bids
    (singleMindedGreedyAcceptedFromState bids ∅ (pre ++ [j])) suffix j

theorem singleMindedGreedyNextDeniedFromSplit_some_spec
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j n : Bidder)
    (hnext :
      singleMindedGreedyNextDeniedFromSplit bids pre suffix j = some n) :
    n ∈ suffix ∧
      SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
        (singleMindedGreedyAcceptedFromState bids ∅ (pre ++ [j]))
        suffix j n := by
  exact
    singleMindedGreedyFirstDeniedBecauseOfFromState_some_spec
      bids
      (singleMindedGreedyAcceptedFromState bids ∅ (pre ++ [j]))
      suffix j n hnext

theorem singleMindedGreedyNextDeniedFromSplit_none_no_candidate
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j : Bidder)
    (hnext :
      singleMindedGreedyNextDeniedFromSplit bids pre suffix j = none) :
    ∀ n, n ∈ suffix →
      ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
        (singleMindedGreedyAcceptedFromState bids ∅ (pre ++ [j]))
        suffix j n := by
  exact
    singleMindedGreedyFirstDeniedBecauseOfFromState_none_no_candidate
      bids
      (singleMindedGreedyAcceptedFromState bids ∅ (pre ++ [j]))
      suffix j hnext

/--
greedy payment `n(j)` search over a full sorted order, carrying the greedy
accepted state until the first occurrence of `j` and then scanning the suffix
after `j`.
-/
def singleMindedGreedyNextDeniedFromStateInOrder
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeOrder : Finset Bidder)
    (order : List Bidder) (j : Bidder) : Option Bidder :=
  match order with
  | [] => none
  | i :: rest =>
      if i = j then
        singleMindedGreedyFirstDeniedBecauseOfFromState bids
          (singleMindedGreedyStep bids acceptedBeforeOrder i) rest j
      else
        singleMindedGreedyNextDeniedFromStateInOrder bids
          (singleMindedGreedyStep bids acceptedBeforeOrder i) rest j

/-- greedy payment `n(j)` from the full sorted greedy order. -/
def singleMindedGreedyNextDeniedFromOrder
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (j : Bidder) : Option Bidder :=
  singleMindedGreedyNextDeniedFromStateInOrder bids ∅ order j

/--
Full-order version of the greedy payment denied-because-of relation. It
packages the first occurrence split of `j` inside the supplied order.
-/
def SingleMindedGreedyDeniedBecauseOfAfterInOrderFromState
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeOrder : Finset Bidder)
    (order : List Bidder) (j i : Bidder) : Prop :=
  ∃ pre suffix,
    order = pre ++ (j :: suffix) ∧
      j ∉ pre ∧
        SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
          (singleMindedGreedyAcceptedFromState
            bids acceptedBeforeOrder (pre ++ [j]))
          suffix j i

theorem singleMindedGreedyNextDeniedFromStateInOrder_some_spec
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeOrder : Finset Bidder)
    (order : List Bidder) (j n : Bidder)
    (hnext :
      singleMindedGreedyNextDeniedFromStateInOrder
        bids acceptedBeforeOrder order j = some n) :
    SingleMindedGreedyDeniedBecauseOfAfterInOrderFromState
      bids acceptedBeforeOrder order j n := by
  induction order generalizing acceptedBeforeOrder with
  | nil =>
      simp [singleMindedGreedyNextDeniedFromStateInOrder] at hnext
  | cons i rest ih =>
      unfold singleMindedGreedyNextDeniedFromStateInOrder at hnext
      by_cases hij : i = j
      · simp [hij] at hnext
        subst i
        have hspec :=
          singleMindedGreedyFirstDeniedBecauseOfFromState_some_spec
            bids (singleMindedGreedyStep bids acceptedBeforeOrder j)
            rest j n hnext
        refine ⟨[], rest, ?_, ?_, ?_⟩
        · simp
        · simp
        · simpa [singleMindedGreedyAcceptedFromState] using hspec.2
      · simp [hij] at hnext
        rcases ih
          (acceptedBeforeOrder :=
            singleMindedGreedyStep bids acceptedBeforeOrder i)
          hnext with ⟨pre, suffix, horder, hpre, hdenied⟩
        refine ⟨i :: pre, suffix, ?_, ?_, ?_⟩
        · simp [horder]
        · intro hjmem
          rw [List.mem_cons] at hjmem
          rcases hjmem with hji | hjpre
          · exact hij hji.symm
          · exact hpre hjpre
        · simpa [singleMindedGreedyAcceptedFromState] using hdenied

theorem singleMindedGreedyNextDeniedFromOrder_some_spec
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (j n : Bidder)
    (hnext :
      singleMindedGreedyNextDeniedFromOrder bids order j = some n) :
    SingleMindedGreedyDeniedBecauseOfAfterInOrderFromState
      bids ∅ order j n := by
  exact
    singleMindedGreedyNextDeniedFromStateInOrder_some_spec
      bids ∅ order j n hnext

theorem singleMindedGreedyNextDeniedFromStateInOrder_none_no_candidate
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeOrder : Finset Bidder)
    (order : List Bidder) (j : Bidder)
    (hnext :
      singleMindedGreedyNextDeniedFromStateInOrder
        bids acceptedBeforeOrder order j = none) :
    ∀ n,
      ¬ SingleMindedGreedyDeniedBecauseOfAfterInOrderFromState
        bids acceptedBeforeOrder order j n := by
  induction order generalizing acceptedBeforeOrder with
  | nil =>
      intro n hcandidate
      rcases hcandidate with ⟨pre, suffix, horder, _hpre, _hdenied⟩
      cases pre <;> simp at horder
  | cons i rest ih =>
      unfold singleMindedGreedyNextDeniedFromStateInOrder at hnext
      by_cases hij : i = j
      · simp [hij] at hnext
        subst i
        intro n hcandidate
        rcases hcandidate with ⟨pre, suffix, horder, hpre, hdenied⟩
        cases pre with
        | nil =>
            simp at horder
            cases horder
            exact
              (singleMindedGreedyFirstDeniedBecauseOfFromState_none_no_candidate
                bids (singleMindedGreedyStep bids acceptedBeforeOrder j)
                rest j hnext n hdenied.mem_suffix) hdenied
        | cons first preTail =>
            simp at horder
            rcases horder with ⟨hfirst, _hrest⟩
            subst first
            exact hpre (by simp)
      · simp [hij] at hnext
        intro n hcandidate
        rcases hcandidate with ⟨pre, suffix, horder, hpre, hdenied⟩
        cases pre with
        | nil =>
            simp at horder
            exact hij horder.1
        | cons first preTail =>
            simp at horder
            rcases horder with ⟨hfirst, hrest⟩
            subst first
            have hpreTail : j ∉ preTail := by
              intro hjmem
              exact hpre (by simp [hjmem])
            have hdeniedRest :
                SingleMindedGreedyDeniedBecauseOfAfterInOrderFromState bids
                  (singleMindedGreedyStep bids acceptedBeforeOrder i)
                  rest j n := by
              refine ⟨preTail, suffix, hrest, hpreTail, ?_⟩
              simpa [singleMindedGreedyAcceptedFromState] using hdenied
            exact
              (ih
                (acceptedBeforeOrder :=
                  singleMindedGreedyStep bids acceptedBeforeOrder i)
                hnext n) hdeniedRest

theorem singleMindedGreedyNextDeniedFromOrder_none_no_candidate
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (j : Bidder)
    (hnext :
      singleMindedGreedyNextDeniedFromOrder bids order j = none) :
    ∀ n,
      ¬ SingleMindedGreedyDeniedBecauseOfAfterInOrderFromState
        bids ∅ order j n := by
  exact
    singleMindedGreedyNextDeniedFromStateInOrder_none_no_candidate
      bids ∅ order j hnext

theorem singleMindedGreedyNextDeniedFromStateInOrder_eq_split
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeOrder : Finset Bidder)
    (pre suffix : List Bidder) (j : Bidder)
    (hpre : j ∉ pre) :
    singleMindedGreedyNextDeniedFromStateInOrder bids acceptedBeforeOrder
      (pre ++ j :: suffix) j =
      singleMindedGreedyFirstDeniedBecauseOfFromState bids
        (singleMindedGreedyAcceptedFromState
          bids acceptedBeforeOrder (pre ++ [j]))
        suffix j := by
  induction pre generalizing acceptedBeforeOrder with
  | nil =>
      simp [singleMindedGreedyNextDeniedFromStateInOrder,
        singleMindedGreedyAcceptedFromState]
  | cons i preTail ih =>
      have hij : i ≠ j := by
        intro hij
        exact hpre (by simp [hij])
      have htail : j ∉ preTail := by
        intro hmem
        exact hpre (by simp [hmem])
      simp [singleMindedGreedyNextDeniedFromStateInOrder, hij]
      simpa [singleMindedGreedyAcceptedFromState] using
        ih
          (acceptedBeforeOrder :=
            singleMindedGreedyStep bids acceptedBeforeOrder i)
          htail

theorem singleMindedGreedyNextDeniedFromOrder_eq_split
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j : Bidder)
    (hpre : j ∉ pre) :
    singleMindedGreedyNextDeniedFromOrder bids (pre ++ j :: suffix) j =
      singleMindedGreedyNextDeniedFromSplit bids pre suffix j := by
  simp [singleMindedGreedyNextDeniedFromOrder,
    singleMindedGreedyNextDeniedFromSplit,
    singleMindedGreedyNextDeniedFromStateInOrder_eq_split bids ∅ pre suffix j hpre]

theorem singleMindedGreedyNextDeniedFromOrder_eq_split_of_nodup
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    {order pre suffix : List Bidder} {j : Bidder}
    (horder : order = pre ++ j :: suffix)
    (hnodup : order.Nodup) :
    singleMindedGreedyNextDeniedFromOrder bids order j =
      singleMindedGreedyNextDeniedFromSplit bids pre suffix j := by
  subst order
  have hpre : j ∉ pre := by
    intro hjpre
    have hnodup_append := (List.nodup_append.mp hnodup).2.2
    exact hnodup_append j hjpre j (by simp) rfl
  exact singleMindedGreedyNextDeniedFromOrder_eq_split
    bids pre suffix j hpre

theorem singleMindedGreedyNextDeniedFromOrder_some_spec_of_split
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j n : Bidder)
    (hpre : j ∉ pre)
    (hnext :
      singleMindedGreedyNextDeniedFromOrder
        bids (pre ++ j :: suffix) j = some n) :
    n ∈ suffix ∧
      SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
        (singleMindedGreedyAcceptedFromState bids ∅ (pre ++ [j]))
        suffix j n := by
  have hsplit :
      singleMindedGreedyNextDeniedFromSplit bids pre suffix j = some n := by
    simpa [singleMindedGreedyNextDeniedFromOrder_eq_split
      bids pre suffix j hpre] using hnext
  exact singleMindedGreedyNextDeniedFromSplit_some_spec
    bids pre suffix j n hsplit

theorem singleMindedGreedyNextDeniedFromOrder_none_no_candidate_of_split
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j : Bidder)
    (hpre : j ∉ pre)
    (hnext :
      singleMindedGreedyNextDeniedFromOrder
        bids (pre ++ j :: suffix) j = none) :
    ∀ n, n ∈ suffix →
      ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
        (singleMindedGreedyAcceptedFromState bids ∅ (pre ++ [j]))
        suffix j n := by
  have hsplit :
      singleMindedGreedyNextDeniedFromSplit bids pre suffix j = none := by
    simpa [singleMindedGreedyNextDeniedFromOrder_eq_split
      bids pre suffix j hpre] using hnext
  exact singleMindedGreedyNextDeniedFromSplit_none_no_candidate
    bids pre suffix j hsplit

/--
greedy payment rule computed directly from the full sorted greedy
order.
-/
noncomputable def singleMindedGreedyPaymentFromOrder
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (j : Bidder) : ℝ :=
  singleMindedGreedyPaymentFromNextDenied bids
    (singleMindedGreedyAcceptedFromOrder bids order)
    (singleMindedGreedyNextDeniedFromOrder bids order) j

theorem singleMindedGreedyPaymentFromOrder_eq_zero_of_denied
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) {j : Bidder}
    (hj : j ∉ singleMindedGreedyAcceptedFromOrder bids order) :
    singleMindedGreedyPaymentFromOrder bids order j = 0 := by
  exact
    singleMindedGreedyPaymentFromNextDenied_eq_zero_of_denied
      bids (singleMindedGreedyAcceptedFromOrder bids order)
      (singleMindedGreedyNextDeniedFromOrder bids order) hj

theorem singleMindedGreedyPaymentFromOrder_eq_zero_of_no_next
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) {j : Bidder}
    (hj : j ∈ singleMindedGreedyAcceptedFromOrder bids order)
    (hnext : singleMindedGreedyNextDeniedFromOrder bids order j = none) :
    singleMindedGreedyPaymentFromOrder bids order j = 0 := by
  exact
    singleMindedGreedyPaymentFromNextDenied_eq_zero_of_no_next
      bids (singleMindedGreedyAcceptedFromOrder bids order)
      (singleMindedGreedyNextDeniedFromOrder bids order) hj hnext

theorem singleMindedGreedyPaymentFromOrder_eq_of_next
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) {j n : Bidder}
    (hj : j ∈ singleMindedGreedyAcceptedFromOrder bids order)
    (hnext : singleMindedGreedyNextDeniedFromOrder bids order j = some n) :
    singleMindedGreedyPaymentFromOrder bids order j =
      (bids j).bundleSize * (bids n).averageAmountPerGood := by
  exact
    singleMindedGreedyPaymentFromNextDenied_eq_of_next
      bids (singleMindedGreedyAcceptedFromOrder bids order)
      (singleMindedGreedyNextDeniedFromOrder bids order) hj hnext

theorem singleMindedGreedyPaymentFromOrder_nonneg_of_nonnegative
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (j : Bidder)
    (hbids :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile bids) :
    0 ≤ singleMindedGreedyPaymentFromOrder bids order j := by
  by_cases hj : j ∈ singleMindedGreedyAcceptedFromOrder bids order
  · cases hnext :
        singleMindedGreedyNextDeniedFromOrder bids order j with
    | none =>
        have hpay :
            singleMindedGreedyPaymentFromOrder bids order j = 0 :=
          singleMindedGreedyPaymentFromOrder_eq_zero_of_no_next
            bids order hj hnext
        simpa [hpay]
    | some n =>
        have hpay :
            singleMindedGreedyPaymentFromOrder bids order j =
              (bids j).bundleSize * (bids n).averageAmountPerGood :=
          singleMindedGreedyPaymentFromOrder_eq_of_next
            bids order hj hnext
        have hj_size_nonneg : 0 ≤ (bids j).bundleSize :=
          ((bids j).bundleSize_pos_of_nonempty (hbids j).1).le
        have hn_average_nonneg : 0 ≤ (bids n).averageAmountPerGood := by
          have hn_value_nonneg : 0 ≤ (bids n).value := (hbids n).2
          have hn_size_nonneg : 0 ≤ (bids n).bundleSize :=
            ((bids n).bundleSize_pos_of_nonempty (hbids n).1).le
          exact div_nonneg hn_value_nonneg hn_size_nonneg
        simpa [hpay] using mul_nonneg hj_size_nonneg hn_average_nonneg
  · have hpay :
        singleMindedGreedyPaymentFromOrder bids order j = 0 :=
      singleMindedGreedyPaymentFromOrder_eq_zero_of_denied bids order hj
    simpa [hpay]

/--
The source greedy accepted-set mechanism induced by an order rule. The order rule
is kept explicit so theorem statements can talk about a caller-provided order
without committing to a particular sorting implementation.
-/
noncomputable def singleMindedGreedyAcceptedMechanismFromOrderOf
    [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder) :
    SingleMindedAcceptedMechanism Bidder Item where
  accepted bids := singleMindedGreedyAcceptedFromOrder bids (orderOf bids)
  payment bids j := singleMindedGreedyPaymentFromOrder bids (orderOf bids) j

/-- Denied bidders pay zero in the source greedy accepted-set mechanism. -/
theorem singleMindedGreedyAcceptedMechanismFromOrderOf_participation
    [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder) :
    (singleMindedGreedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf).Participation := by
  intro bids j hj
  exact singleMindedGreedyPaymentFromOrder_eq_zero_of_denied
    bids (orderOf bids) hj

theorem singleMindedGreedyAcceptedMechanismFromOrderOf_monotonicity_of_order_moves_earlier
    [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (hmove :
      ∀ bids j s v,
        j ∈ singleMindedGreedyAcceptedFromOrder bids (orderOf bids) →
          s ⊆ (bids j).desired →
            (bids j).value ≤ v →
              ∃ pref rest suffix tail,
                orderOf bids = (pref ++ rest) ++ j :: suffix ∧
                  orderOf (Function.update bids j { desired := s, value := v }) =
                    pref ++ j :: tail ∧
                  j ∉ pref ∧ j ∉ rest ∧ j ∉ suffix) :
    (singleMindedGreedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf).Monotonicity := by
  intro bids j s v hacc hdesired_subset hvalue_le
  rcases hmove bids j s v hacc hdesired_subset hvalue_le with
    ⟨pref, rest, suffix, tail, horder_old, horder_new,
      hjpref, hjrest, hjsuffix⟩
  let bidsStrong : Bidder → SingleMindedBid Item :=
    Function.update bids j { desired := s, value := v }
  have hsame : ∀ k, k ≠ j → bidsStrong k = bids k := by
    intro k hk
    simp [bidsStrong, hk]
  have hjdesired_subset :
      (bidsStrong j).desired ⊆ (bids j).desired := by
    simpa [bidsStrong, Function.update] using hdesired_subset
  have hacc_old :
      j ∈ singleMindedGreedyAcceptedFromState bids (∅ : Finset Bidder)
        ((pref ++ rest) ++ j :: suffix) := by
    simpa [singleMindedGreedyAcceptedMechanismFromOrderOf,
      singleMindedGreedyAcceptedFromOrder, horder_old, List.append_assoc]
      using hacc
  have hacc_new :
      j ∈ singleMindedGreedyAcceptedFromState bidsStrong (∅ : Finset Bidder)
        (pref ++ j :: tail) :=
    singleMindedGreedyAcceptedFromState_accepts_after_shrink_of_original_accepts_before_move
      (bids := bids) (bidsStrong := bidsStrong)
      (∅ : Finset Bidder) pref rest suffix tail hsame hjdesired_subset
      (by simp) hjpref hjrest hjsuffix hacc_old
  simpa [singleMindedGreedyAcceptedMechanismFromOrderOf,
    singleMindedGreedyAcceptedFromOrder, bidsStrong, horder_new] using hacc_new

theorem singleMindedGreedyAcceptedMechanismFromOrderOf_monotonicityOn_of_order_moves_earlier
    [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (admissible : (Bidder → SingleMindedBid Item) → Prop)
    (hmove :
      ∀ bids,
        admissible bids →
          ∀ j s v,
            j ∈ singleMindedGreedyAcceptedFromOrder bids (orderOf bids) →
              admissible (Function.update bids j { desired := s, value := v }) →
                s ⊆ (bids j).desired →
                  (bids j).value ≤ v →
                    ∃ pref rest suffix tail,
                      orderOf bids = (pref ++ rest) ++ j :: suffix ∧
                        orderOf (Function.update bids j
                          { desired := s, value := v }) =
                          pref ++ j :: tail ∧
                        j ∉ pref ∧ j ∉ rest ∧ j ∉ suffix) :
    (singleMindedGreedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf).MonotonicityOn admissible := by
  intro bids hbids j s v hacc hupdated hdesired_subset hvalue_le
  rcases hmove bids hbids j s v hacc hupdated hdesired_subset hvalue_le with
    ⟨pref, rest, suffix, tail, horder_old, horder_new,
      hjpref, hjrest, hjsuffix⟩
  let bidsStrong : Bidder → SingleMindedBid Item :=
    Function.update bids j { desired := s, value := v }
  have hsame : ∀ k, k ≠ j → bidsStrong k = bids k := by
    intro k hk
    simp [bidsStrong, hk]
  have hjdesired_subset :
      (bidsStrong j).desired ⊆ (bids j).desired := by
    simpa [bidsStrong, Function.update] using hdesired_subset
  have hacc_old :
      j ∈ singleMindedGreedyAcceptedFromState bids (∅ : Finset Bidder)
        ((pref ++ rest) ++ j :: suffix) := by
    simpa [singleMindedGreedyAcceptedMechanismFromOrderOf,
      singleMindedGreedyAcceptedFromOrder, horder_old, List.append_assoc]
      using hacc
  have hacc_new :
      j ∈ singleMindedGreedyAcceptedFromState bidsStrong (∅ : Finset Bidder)
        (pref ++ j :: tail) :=
    singleMindedGreedyAcceptedFromState_accepts_after_shrink_of_original_accepts_before_move
      (bids := bids) (bidsStrong := bidsStrong)
      (∅ : Finset Bidder) pref rest suffix tail hsame hjdesired_subset
      (by simp) hjpref hjrest hjsuffix hacc_old
  simpa [singleMindedGreedyAcceptedMechanismFromOrderOf,
    singleMindedGreedyAcceptedFromOrder, bidsStrong, horder_new] using hacc_new

/-- Source-order predicate: `earlier` appears before `later` in a bid order. -/
def SingleMindedPrecedes [DecidableEq Bidder]
    (order : List Bidder) (earlier later : Bidder) : Prop :=
  ∃ left mid right,
    order = left ++ (earlier :: (mid ++ (later :: right)))

/-- The source square-root norm is weakly descending along the explicit order. -/
def SingleMindedSqrtNormDescending [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) : Prop :=
  order.Pairwise fun earlier later =>
    (bids later).sqrtAmountNorm ≤ (bids earlier).sqrtAmountNorm

/-- The source section 10 average amount per good is weakly descending along an order. -/
def SingleMindedAverageAmountDescending [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) : Prop :=
  order.Pairwise fun earlier later =>
    (bids later).averageAmountPerGood ≤ (bids earlier).averageAmountPerGood

/--
Deterministic key for the concrete source average-density order. The primary
coordinate is dualized so increasing lexicographic sort lists larger averages
first; the bidder order is only a tie-breaker.
-/
noncomputable def singleMindedAverageTieKey
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (i : Bidder) :
    (ℝᵒᵈ ×ₗ Bidder) :=
  toLex (OrderDual.toDual (bids i).averageAmountPerGood, i)

theorem singleMindedAverageTieKey_injective
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    Function.Injective (singleMindedAverageTieKey bids) := by
  intro i j hkey
  have hpair :
      (OrderDual.toDual (bids i).averageAmountPerGood, i) =
        (OrderDual.toDual (bids j).averageAmountPerGood, j) := by
    simpa [singleMindedAverageTieKey] using
      congrArg (fun x => (ofLex x : ℝᵒᵈ × Bidder)) hkey
  exact congrArg Prod.snd hpair

/-- Concrete total relation used to sort single-minded bidders by average density. -/
noncomputable def singleMindedAverageTieRel
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) : Bidder → Bidder → Prop :=
  Order.Preimage (singleMindedAverageTieKey bids) (· ≤ ·)

noncomputable instance singleMindedAverageTieRelDecidable
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    DecidableRel (singleMindedAverageTieRel bids) := by
  dsimp [singleMindedAverageTieRel]
  infer_instance

instance singleMindedAverageTieRelTrans
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    IsTrans Bidder (singleMindedAverageTieRel bids) := by
  dsimp [singleMindedAverageTieRel]
  infer_instance

instance singleMindedAverageTieRelTotal
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    Std.Total (singleMindedAverageTieRel bids) := by
  dsimp [singleMindedAverageTieRel]
  infer_instance

instance singleMindedAverageTieRelAntisymm
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    Std.Antisymm (singleMindedAverageTieRel bids) := by
  dsimp [singleMindedAverageTieRel]
  exact Order.Preimage.antisymm (singleMindedAverageTieKey_injective bids)

/-- The concrete greedy order: bidders sorted by decreasing average amount per good. -/
noncomputable def singleMindedAverageOrderOf
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) : List Bidder :=
  (Finset.univ : Finset Bidder).sort (singleMindedAverageTieRel bids)

theorem singleMindedAverageOrderOf_nodup
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    (singleMindedAverageOrderOf bids).Nodup := by
  simp [singleMindedAverageOrderOf]

theorem singleMindedAverageOrderOf_mem
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (i : Bidder) :
    i ∈ singleMindedAverageOrderOf bids := by
  simp [singleMindedAverageOrderOf]

theorem singleMindedAverageOrderOf_average_descending
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    SingleMindedAverageAmountDescending bids
      (singleMindedAverageOrderOf bids) := by
  dsimp [SingleMindedAverageAmountDescending, singleMindedAverageOrderOf]
  refine
    (Finset.pairwise_sort
      (s := (Finset.univ : Finset Bidder))
      (r := singleMindedAverageTieRel bids)).imp ?_
  intro earlier later hrel
  dsimp [singleMindedAverageTieRel, singleMindedAverageTieKey] at hrel
  rw [Prod.Lex.toLex_le_toLex] at hrel
  rcases hrel with hlt | heqle
  · exact le_of_lt (by simpa using hlt)
  · exact le_of_eq (by
      simpa using (congrArg OrderDual.ofDual heqle.1).symm)

/--
Changing only bidder `j`'s declared value does not change the concrete
average-order comparison between two other bidders.
-/
theorem singleMindedAverageTieRel_valueUpdate_iff_of_ne
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) (value : ℝ)
    {i k : Bidder} (hi : i ≠ j) (hk : k ≠ j) :
    singleMindedAverageTieRel (singleMindedValueUpdate bids j value) i k ↔
      singleMindedAverageTieRel bids i k := by
  dsimp [singleMindedAverageTieRel, singleMindedAverageTieKey]
  simp [singleMindedValueUpdate, hi, hk]

theorem singleMindedAverageTieRel_update_iff_of_ne
    [DecidableEq Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder)
    (bid : SingleMindedBid Item)
    {i k : Bidder} (hi : i ≠ j) (hk : k ≠ j) :
    singleMindedAverageTieRel (Function.update bids j bid) i k ↔
      singleMindedAverageTieRel bids i k := by
  dsimp [singleMindedAverageTieRel, singleMindedAverageTieKey]
  simp [Function.update, hi, hk]

theorem singleMindedAverageTieRel_of_average_lt
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) {i k : Bidder}
    (hlt : (bids k).averageAmountPerGood < (bids i).averageAmountPerGood) :
    singleMindedAverageTieRel bids i k := by
  dsimp [singleMindedAverageTieRel, singleMindedAverageTieKey]
  rw [Prod.Lex.toLex_le_toLex]
  exact Or.inl (by simpa using hlt)

theorem singleMindedAverageTieRel_mono_left_average
    [DecidableEq Item] [LinearOrder Bidder]
    (bids updated : Bidder → SingleMindedBid Item) {j k : Bidder}
    (hrel : singleMindedAverageTieRel bids j k)
    (hk_avg :
      (updated k).averageAmountPerGood = (bids k).averageAmountPerGood)
    (havg :
      (bids j).averageAmountPerGood ≤ (updated j).averageAmountPerGood) :
    singleMindedAverageTieRel updated j k := by
  classical
  dsimp [singleMindedAverageTieRel, singleMindedAverageTieKey] at hrel ⊢
  rw [Prod.Lex.toLex_le_toLex] at hrel ⊢
  rcases hrel with hlt | heqle
  · exact Or.inl (by
      have hlt_real :
          (bids k).averageAmountPerGood < (bids j).averageAmountPerGood := by
        simpa using hlt
      have hlt_updated :
          (updated k).averageAmountPerGood <
            (updated j).averageAmountPerGood := by
        rw [hk_avg]
        exact hlt_real.trans_le havg
      simpa using hlt_updated)
  · rcases lt_or_eq_of_le havg with hlt_avg | heq_avg
    · exact Or.inl (by
        have heq_real :
            (bids k).averageAmountPerGood =
              (bids j).averageAmountPerGood := by
          simpa using (congrArg OrderDual.ofDual heqle.1).symm
        have hlt_updated :
            (updated k).averageAmountPerGood <
              (updated j).averageAmountPerGood := by
          rw [hk_avg, heq_real]
          exact hlt_avg
        simpa using hlt_updated)
    · exact Or.inr ⟨by
        have heq_real :
            (bids k).averageAmountPerGood =
              (bids j).averageAmountPerGood := by
          simpa using (congrArg OrderDual.ofDual heqle.1).symm
        exact congrArg OrderDual.toDual (by
          rw [hk_avg, ← heq_avg]
          exact heq_real.symm), heqle.2⟩

/--
The concrete source average order is stable off the bidder whose value changes:
erasing the changed bidder from the old and updated orders gives the same list.
-/
theorem singleMindedAverageOrderOf_erase_valueUpdate
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) (value : ℝ) :
    (singleMindedAverageOrderOf
        (singleMindedValueUpdate bids j value)).erase j =
      (singleMindedAverageOrderOf bids).erase j := by
  classical
  let updated := singleMindedValueUpdate bids j value
  let oldOrder := singleMindedAverageOrderOf bids
  let updatedOrder := singleMindedAverageOrderOf updated
  have hperm_updated :
      List.Perm updatedOrder (Finset.univ : Finset Bidder).toList := by
    simpa [updatedOrder, singleMindedAverageOrderOf] using
      (Finset.sort_perm_toList
        (s := (Finset.univ : Finset Bidder))
        (r := singleMindedAverageTieRel updated))
  have hperm_old :
      List.Perm oldOrder (Finset.univ : Finset Bidder).toList := by
    simpa [oldOrder, singleMindedAverageOrderOf] using
      (Finset.sort_perm_toList
        (s := (Finset.univ : Finset Bidder))
        (r := singleMindedAverageTieRel bids))
  have hperm :
      List.Perm (updatedOrder.erase j) (oldOrder.erase j) :=
    (hperm_updated.erase j).trans (hperm_old.erase j).symm
  have hpair_old_full :
      oldOrder.Pairwise (singleMindedAverageTieRel bids) := by
    simpa [oldOrder, singleMindedAverageOrderOf] using
      (Finset.pairwise_sort
        (s := (Finset.univ : Finset Bidder))
        (r := singleMindedAverageTieRel bids))
  have hpair_old :
      (oldOrder.erase j).Pairwise (singleMindedAverageTieRel bids) :=
    List.Pairwise.sublist List.erase_sublist hpair_old_full
  have hpair_updated_full :
      updatedOrder.Pairwise (singleMindedAverageTieRel updated) := by
    simpa [updatedOrder, singleMindedAverageOrderOf] using
      (Finset.pairwise_sort
        (s := (Finset.univ : Finset Bidder))
        (r := singleMindedAverageTieRel updated))
  have hpair_updated_erase :
      (updatedOrder.erase j).Pairwise (singleMindedAverageTieRel updated) :=
    List.Pairwise.sublist List.erase_sublist hpair_updated_full
  have hnodup_updated : updatedOrder.Nodup := by
    simpa [updatedOrder] using singleMindedAverageOrderOf_nodup updated
  have hpair_updated :
      (updatedOrder.erase j).Pairwise (singleMindedAverageTieRel bids) := by
    rw [List.pairwise_iff_get]
    intro a b hab
    have hrel :=
      (List.pairwise_iff_get.mp hpair_updated_erase) a b hab
    have ha_mem :
        (updatedOrder.erase j).get a ∈ updatedOrder.erase j :=
      List.get_mem (updatedOrder.erase j) a
    have hb_mem :
        (updatedOrder.erase j).get b ∈ updatedOrder.erase j :=
      List.get_mem (updatedOrder.erase j) b
    have ha_ne :
        (updatedOrder.erase j).get a ≠ j :=
      ((List.Nodup.mem_erase_iff (d := hnodup_updated)).mp ha_mem).1
    have hb_ne :
        (updatedOrder.erase j).get b ≠ j :=
      ((List.Nodup.mem_erase_iff (d := hnodup_updated)).mp hb_mem).1
    exact
      (singleMindedAverageTieRel_valueUpdate_iff_of_ne
        bids j value ha_ne hb_ne).1 hrel
  have heq :
      updatedOrder.erase j = oldOrder.erase j :=
    List.Perm.eq_of_pairwise' hpair_updated hpair_old hperm
  simpa [updated, oldOrder, updatedOrder]
    using heq

/--
Split form of `singleMindedAverageOrderOf_erase_valueUpdate`: if the original
concrete average order is displayed as a prefix, `j`, and a suffix, then the
updated concrete order with `j` erased is exactly that prefix followed by the
same suffix.
-/
theorem singleMindedAverageOrderOf_erase_valueUpdate_of_split
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base) :
    (singleMindedAverageOrderOf
        (singleMindedValueUpdate bids j value)).erase j =
      before ++ base := by
  have hnodup_split : (before ++ j :: base).Nodup := by
    simpa [horder] using singleMindedAverageOrderOf_nodup bids
  have hj_before : j ∉ before := by
    intro hjbefore
    have hdisjoint := (List.nodup_append.mp hnodup_split).2.2
    exact hdisjoint j hjbefore j (by simp) rfl
  have hold_erase :
      (singleMindedAverageOrderOf bids).erase j = before ++ base := by
    rw [horder]
    rw [List.erase_append_right (j :: base) hj_before]
    simp
  rw [singleMindedAverageOrderOf_erase_valueUpdate, hold_erase]

/--
Global concrete-order facts for a value update around a displayed split of the
original order. The local source-window bridge still has to remove the prefix,
but sortedness, duplicate-freeness, membership, and global erase-stability are
all discharged here.
-/
theorem singleMindedAverageOrderOf_valueUpdate_global_facts_of_split
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base) :
    let updated := singleMindedValueUpdate bids j value
    let updatedOrder := singleMindedAverageOrderOf updated
    SingleMindedAverageAmountDescending updated updatedOrder ∧
      updatedOrder.Nodup ∧
      j ∈ updatedOrder ∧
      updatedOrder.erase j = before ++ base := by
  dsimp
  exact
    ⟨singleMindedAverageOrderOf_average_descending
        (singleMindedValueUpdate bids j value),
      singleMindedAverageOrderOf_nodup
        (singleMindedValueUpdate bids j value),
      singleMindedAverageOrderOf_mem
        (singleMindedValueUpdate bids j value) j,
      singleMindedAverageOrderOf_erase_valueUpdate_of_split
        bids value horder⟩

theorem singleMindedAverageOrderOf_valueUpdate_eq_orderedInsert_erase_of_split
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base) :
    singleMindedAverageOrderOf (singleMindedValueUpdate bids j value) =
      (before ++ base).orderedInsert
        (singleMindedAverageTieRel (singleMindedValueUpdate bids j value))
        j := by
  let updated := singleMindedValueUpdate bids j value
  let rel := singleMindedAverageTieRel updated
  let updatedOrder := singleMindedAverageOrderOf updated
  have hpair_updated :
      updatedOrder.Pairwise rel := by
    simpa [updatedOrder, rel, singleMindedAverageOrderOf] using
      (Finset.pairwise_sort
        (s := (Finset.univ : Finset Bidder))
        (r := rel))
  have hmem : j ∈ updatedOrder := by
    simpa [updatedOrder] using singleMindedAverageOrderOf_mem updated j
  have herase :
      updatedOrder.erase j = before ++ base := by
    simpa [updatedOrder, updated] using
      singleMindedAverageOrderOf_erase_valueUpdate_of_split
        bids value horder
  have hinsert :
      (updatedOrder.erase j).orderedInsert rel j = updatedOrder :=
    List.orderedInsert_erase
      (r := rel) j updatedOrder hmem hpair_updated
  calc
    singleMindedAverageOrderOf (singleMindedValueUpdate bids j value)
        = updatedOrder := rfl
    _ = (updatedOrder.erase j).orderedInsert rel j := hinsert.symm
    _ =
        (before ++ base).orderedInsert
          (singleMindedAverageTieRel
            (singleMindedValueUpdate bids j value)) j := by
      simp [herase, rel, updated]

/--
The concrete average order is stable off an arbitrary replacement of bidder
`j`'s own report: after erasing `j`, the sorted bidder list is unchanged.
-/
theorem singleMindedAverageOrderOf_erase_update
    [Fintype Bidder] [DecidableEq Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder)
    (bid : SingleMindedBid Item) :
    (singleMindedAverageOrderOf
        (Function.update bids j bid)).erase j =
      (singleMindedAverageOrderOf bids).erase j := by
  classical
  let updated := Function.update bids j bid
  let oldOrder := singleMindedAverageOrderOf bids
  let updatedOrder := singleMindedAverageOrderOf updated
  have hperm_updated :
      List.Perm updatedOrder (Finset.univ : Finset Bidder).toList := by
    simpa [updatedOrder, singleMindedAverageOrderOf] using
      (Finset.sort_perm_toList
        (s := (Finset.univ : Finset Bidder))
        (r := singleMindedAverageTieRel updated))
  have hperm_old :
      List.Perm oldOrder (Finset.univ : Finset Bidder).toList := by
    simpa [oldOrder, singleMindedAverageOrderOf] using
      (Finset.sort_perm_toList
        (s := (Finset.univ : Finset Bidder))
        (r := singleMindedAverageTieRel bids))
  have hperm :
      List.Perm (updatedOrder.erase j) (oldOrder.erase j) :=
    (hperm_updated.erase j).trans (hperm_old.erase j).symm
  have hpair_old_full :
      oldOrder.Pairwise (singleMindedAverageTieRel bids) := by
    simpa [oldOrder, singleMindedAverageOrderOf] using
      (Finset.pairwise_sort
        (s := (Finset.univ : Finset Bidder))
        (r := singleMindedAverageTieRel bids))
  have hpair_old :
      (oldOrder.erase j).Pairwise (singleMindedAverageTieRel bids) :=
    List.Pairwise.sublist List.erase_sublist hpair_old_full
  have hpair_updated_full :
      updatedOrder.Pairwise (singleMindedAverageTieRel updated) := by
    simpa [updatedOrder, singleMindedAverageOrderOf] using
      (Finset.pairwise_sort
        (s := (Finset.univ : Finset Bidder))
        (r := singleMindedAverageTieRel updated))
  have hpair_updated_erase :
      (updatedOrder.erase j).Pairwise (singleMindedAverageTieRel updated) :=
    List.Pairwise.sublist List.erase_sublist hpair_updated_full
  have hnodup_updated : updatedOrder.Nodup := by
    simpa [updatedOrder] using singleMindedAverageOrderOf_nodup updated
  have hpair_updated :
      (updatedOrder.erase j).Pairwise (singleMindedAverageTieRel bids) := by
    rw [List.pairwise_iff_get]
    intro a b hab
    have hrel :=
      (List.pairwise_iff_get.mp hpair_updated_erase) a b hab
    have ha_mem :
        (updatedOrder.erase j).get a ∈ updatedOrder.erase j :=
      List.get_mem (updatedOrder.erase j) a
    have hb_mem :
        (updatedOrder.erase j).get b ∈ updatedOrder.erase j :=
      List.get_mem (updatedOrder.erase j) b
    have ha_ne :
        (updatedOrder.erase j).get a ≠ j :=
      ((List.Nodup.mem_erase_iff (d := hnodup_updated)).mp ha_mem).1
    have hb_ne :
        (updatedOrder.erase j).get b ≠ j :=
      ((List.Nodup.mem_erase_iff (d := hnodup_updated)).mp hb_mem).1
    exact
      (singleMindedAverageTieRel_update_iff_of_ne
        bids j bid ha_ne hb_ne).1 hrel
  have heq :
      updatedOrder.erase j = oldOrder.erase j :=
    List.Perm.eq_of_pairwise' hpair_updated hpair_old hperm
  simpa [updated, oldOrder, updatedOrder]
    using heq

/--
Split form of `singleMindedAverageOrderOf_erase_update`: if the original
average order is `before`, then `j`, then `base`, replacing `j`'s own report
leaves `before ++ base` after erasing `j`.
-/
theorem singleMindedAverageOrderOf_erase_update_of_split
    [Fintype Bidder] [DecidableEq Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder}
    (bid : SingleMindedBid Item)
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base) :
    (singleMindedAverageOrderOf
        (Function.update bids j bid)).erase j =
      before ++ base := by
  have hnodup_split : (before ++ j :: base).Nodup := by
    simpa [horder] using singleMindedAverageOrderOf_nodup bids
  have hj_before : j ∉ before := by
    intro hjbefore
    have hdisjoint := (List.nodup_append.mp hnodup_split).2.2
    exact hdisjoint j hjbefore j (by simp) rfl
  have hold_erase :
      (singleMindedAverageOrderOf bids).erase j = before ++ base := by
    rw [horder]
    rw [List.erase_append_right (j :: base) hj_before]
    simp
  rw [singleMindedAverageOrderOf_erase_update, hold_erase]

/--
After replacing bidder `j`'s own report, the new concrete average order is
obtained by inserting `j` into the old order with `j` erased, using the updated
average-order relation.
-/
theorem singleMindedAverageOrderOf_update_eq_orderedInsert_erase_of_split
    [Fintype Bidder] [DecidableEq Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder}
    (bid : SingleMindedBid Item)
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base) :
    singleMindedAverageOrderOf (Function.update bids j bid) =
      (before ++ base).orderedInsert
        (singleMindedAverageTieRel (Function.update bids j bid)) j := by
  let updated := Function.update bids j bid
  let rel := singleMindedAverageTieRel updated
  let updatedOrder := singleMindedAverageOrderOf updated
  have hpair_updated :
      updatedOrder.Pairwise rel := by
    simpa [updatedOrder, rel, singleMindedAverageOrderOf] using
      (Finset.pairwise_sort
        (s := (Finset.univ : Finset Bidder))
        (r := rel))
  have hmem : j ∈ updatedOrder := by
    simpa [updatedOrder] using singleMindedAverageOrderOf_mem updated j
  have herase :
      updatedOrder.erase j = before ++ base := by
    simpa [updatedOrder, updated] using
      singleMindedAverageOrderOf_erase_update_of_split
        bids bid horder
  have hinsert :
      (updatedOrder.erase j).orderedInsert rel j = updatedOrder :=
    List.orderedInsert_erase
      (r := rel) j updatedOrder hmem hpair_updated
  calc
    singleMindedAverageOrderOf (Function.update bids j bid)
        = updatedOrder := rfl
    _ = (updatedOrder.erase j).orderedInsert rel j := hinsert.symm
    _ =
        (before ++ base).orderedInsert
          (singleMindedAverageTieRel (Function.update bids j bid)) j := by
      simp [herase, rel, updated]

/--
On the nonnegative single-minded domain, replacing an accepted bidder's report
by a nonempty subset bundle with weakly larger value can only move that bidder
earlier in the concrete average-density order, in the source-window sense used
by the greedy monotonicity theorem.
-/
theorem singleMindedAverageOrderOf_nonnegative_update_moves_earlier
    [Fintype Bidder] [DecidableEq Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    (hbids :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile bids)
    {j : Bidder} {s : Bundle Item} {v : ℝ}
    (hupdated :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile
        (Function.update bids j { desired := s, value := v }))
    (hsub : s ⊆ (bids j).desired)
    (hle : (bids j).value ≤ v) :
    ∃ pref rest suffix tail,
      singleMindedAverageOrderOf bids = (pref ++ rest) ++ j :: suffix ∧
        singleMindedAverageOrderOf
            (Function.update bids j { desired := s, value := v }) =
          pref ++ j :: tail ∧
        j ∉ pref ∧ j ∉ rest ∧ j ∉ suffix := by
  classical
  let bid : SingleMindedBid Item := { desired := s, value := v }
  let updated := Function.update bids j bid
  rcases
    List.mem_iff_append.mp (singleMindedAverageOrderOf_mem bids j) with
    ⟨before, base, horder⟩
  have hnodup_split : (before ++ j :: base).Nodup := by
    simpa [horder] using singleMindedAverageOrderOf_nodup bids
  have hjbefore : j ∉ before := by
    intro hj
    have hdisjoint := (List.nodup_append.mp hnodup_split).2.2
    exact hdisjoint j hj j (by simp) rfl
  have hjbase : j ∉ base := by
    have htail_nodup : (j :: base).Nodup :=
      (List.nodup_append.mp hnodup_split).2.1
    exact (List.nodup_cons.mp htail_nodup).1
  have hupdated_order :
      singleMindedAverageOrderOf updated =
        (before ++ base).orderedInsert (singleMindedAverageTieRel updated) j := by
    simpa [updated, bid] using
      singleMindedAverageOrderOf_update_eq_orderedInsert_erase_of_split
        bids bid horder
  have hs : s.Nonempty := by
    simpa [updated, bid, Function.update] using (hupdated j).1
  have havg :
      (bids j).averageAmountPerGood ≤
        (updated j).averageAmountPerGood := by
    have hcore :
        (bids j).averageAmountPerGood ≤
          ({ desired := s, value := v } :
            SingleMindedBid Item).averageAmountPerGood :=
      SingleMindedBid.averageAmountPerGood_le_of_subset_value_le
        (bids j) (hbids j).1 hs hsub (hbids j).2 hle
    simpa [updated, bid, Function.update] using hcore
  have hpair_order :
      (singleMindedAverageOrderOf bids).Pairwise
        (singleMindedAverageTieRel bids) := by
    simpa [singleMindedAverageOrderOf] using
      (Finset.pairwise_sort
        (s := (Finset.univ : Finset Bidder))
        (r := singleMindedAverageTieRel bids))
  have hpair_split :
      (before ++ j :: base).Pairwise
        (singleMindedAverageTieRel bids) := by
    simpa [horder] using hpair_order
  have htail_pair :
      (j :: base).Pairwise (singleMindedAverageTieRel bids) := by
    have hsuffix : j :: base <:+ before ++ j :: base := by
      simpa using (List.suffix_append before (j :: base))
    exact List.Pairwise.sublist hsuffix.sublist hpair_split
  have hbase_rel :
      ∀ k, k ∈ base → singleMindedAverageTieRel updated j k := by
    intro k hk
    have hold_rel : singleMindedAverageTieRel bids j k := by
      exact (List.pairwise_cons.mp htail_pair).1 k hk
    have hk_ne : k ≠ j := by
      intro hkj
      exact hjbase (by simpa [hkj] using hk)
    have hk_avg :
        (updated k).averageAmountPerGood =
          (bids k).averageAmountPerGood := by
      simp [updated, bid, hk_ne]
    exact
      singleMindedAverageTieRel_mono_left_average
        bids updated hold_rel hk_avg havg
  rcases
    list_orderedInsert_split_before_of_forall_base_rel
      (singleMindedAverageTieRel updated) j before base hbase_rel with
    ⟨pref, rest, tail, hbefore, hinsert⟩
  have hjpref : j ∉ pref := by
    intro hj
    exact hjbefore (by
      rw [hbefore]
      exact List.mem_append.mpr (Or.inl hj))
  have hjrest : j ∉ rest := by
    intro hj
    exact hjbefore (by
      rw [hbefore]
      exact List.mem_append.mpr (Or.inr hj))
  refine ⟨pref, rest, base, tail, ?_, ?_, hjpref, hjrest, hjbase⟩
  · rw [horder, hbefore]
  · rw [hupdated_order, hinsert]

theorem singleMindedAverageValueUpdate_prefix_state_erase_of_split
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base)
    (hjaccepted :
      j ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])) :
    (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])).erase j =
      singleMindedGreedyAcceptedFromState
        (singleMindedValueUpdate bids j value) ∅ before := by
  have hnodup_split : (before ++ j :: base).Nodup := by
    simpa [horder] using singleMindedAverageOrderOf_nodup bids
  have hjbefore : j ∉ before := by
    have hdisjoint := (List.nodup_append.mp hnodup_split).2.2
    intro hj
    exact hdisjoint j hj j (by simp) rfl
  exact
    singleMindedGreedyAcceptedFromState_erase_append_singleton_of_mem_valueUpdate
      bids before value hjbefore hjaccepted

/--
The ordered-insertion suffix window used by the concrete source average order
after changing only bidder `j`'s value.
-/
noncomputable def singleMindedAverageValueUpdateWindow
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder)
    (base : List Bidder) (value : ℝ) : List Bidder :=
  base.orderedInsert
    (singleMindedAverageTieRel (singleMindedValueUpdate bids j value)) j

theorem SingleMindedAverageAmountDescending.of_pairwise_averageTieRel
    [DecidableEq Item] [LinearOrder Bidder]
    {bids : Bidder → SingleMindedBid Item} {order : List Bidder}
    (hpair : order.Pairwise (singleMindedAverageTieRel bids)) :
    SingleMindedAverageAmountDescending bids order := by
  dsimp [SingleMindedAverageAmountDescending]
  refine hpair.imp ?_
  intro earlier later hrel
  dsimp [singleMindedAverageTieRel, singleMindedAverageTieKey] at hrel
  rw [Prod.Lex.toLex_le_toLex] at hrel
  rcases hrel with hlt | heqle
  · exact le_of_lt (by simpa using hlt)
  · exact le_of_eq (by
      simpa using (congrArg OrderDual.ofDual heqle.1).symm)

theorem singleMindedAverageValueUpdateWindow_pairwise_of_split
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base) :
    (singleMindedAverageValueUpdateWindow bids j base value).Pairwise
      (singleMindedAverageTieRel
        (singleMindedValueUpdate bids j value)) := by
  let updated := singleMindedValueUpdate bids j value
  have hpair_order :
      (singleMindedAverageOrderOf bids).Pairwise
        (singleMindedAverageTieRel bids) := by
    simpa [singleMindedAverageOrderOf] using
      (Finset.pairwise_sort
        (s := (Finset.univ : Finset Bidder))
        (r := singleMindedAverageTieRel bids))
  have hpair_split :
      (before ++ j :: base).Pairwise
        (singleMindedAverageTieRel bids) := by
    simpa [horder] using hpair_order
  have hbase_old :
      base.Pairwise (singleMindedAverageTieRel bids) := by
    have hsuffix : base <:+ before ++ j :: base := by
      simpa [List.append_assoc] using
        (List.suffix_append (before ++ [j]) base)
    exact List.Pairwise.sublist hsuffix.sublist hpair_split
  have hnodup_split : (before ++ j :: base).Nodup := by
    simpa [horder] using singleMindedAverageOrderOf_nodup bids
  have hjbase : j ∉ base := by
    have htail_nodup : (j :: base).Nodup :=
      (List.nodup_append.mp hnodup_split).2.1
    exact (List.nodup_cons.mp htail_nodup).1
  have hbase_updated :
      base.Pairwise (singleMindedAverageTieRel updated) := by
    rw [List.pairwise_iff_get]
    intro a b hab
    have hrel_old :=
      (List.pairwise_iff_get.mp hbase_old) a b hab
    have ha_ne :
        base.get a ≠ j := by
      intro ha
      exact hjbase (by
        rw [← ha]
        exact List.get_mem base a)
    have hb_ne :
        base.get b ≠ j := by
      intro hb
      exact hjbase (by
        rw [← hb]
        exact List.get_mem base b)
    exact
      (singleMindedAverageTieRel_valueUpdate_iff_of_ne
        bids j value ha_ne hb_ne).2 hrel_old
  exact
    hbase_updated.orderedInsert j base

theorem singleMindedAverageValueUpdateWindow_average_descending_of_split
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base) :
    SingleMindedAverageAmountDescending
      (singleMindedValueUpdate bids j value)
      (singleMindedAverageValueUpdateWindow bids j base value) :=
  SingleMindedAverageAmountDescending.of_pairwise_averageTieRel
    (singleMindedAverageValueUpdateWindow_pairwise_of_split
      bids value horder)

theorem singleMindedAverageValueUpdateWindow_erase_eq_of_split
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base) :
    (singleMindedAverageValueUpdateWindow bids j base value).erase j = base := by
  have hnodup_split : (before ++ j :: base).Nodup := by
    simpa [horder] using singleMindedAverageOrderOf_nodup bids
  have hjbase : j ∉ base := by
    have htail_nodup : (j :: base).Nodup :=
      (List.nodup_append.mp hnodup_split).2.1
    exact (List.nodup_cons.mp htail_nodup).1
  simpa [singleMindedAverageValueUpdateWindow] using
    (List.erase_orderedInsert_of_notMem
      (r := singleMindedAverageTieRel
        (singleMindedValueUpdate bids j value))
      (x := j) (xs := base) hjbase)

theorem singleMindedAverageValueUpdateWindow_mem_j
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    (base : List Bidder) (j : Bidder) (value : ℝ) :
    j ∈ singleMindedAverageValueUpdateWindow bids j base value := by
  simp [singleMindedAverageValueUpdateWindow, List.mem_orderedInsert]

theorem singleMindedAverageValueUpdateWindow_nodup_of_split
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base) :
    (singleMindedAverageValueUpdateWindow bids j base value).Nodup := by
  have hnodup_split : (before ++ j :: base).Nodup := by
    simpa [horder] using singleMindedAverageOrderOf_nodup bids
  have htail_nodup : (j :: base).Nodup :=
    (List.nodup_append.mp hnodup_split).2.1
  have hbase_nodup : base.Nodup :=
    (List.nodup_cons.mp htail_nodup).2
  have hjbase : j ∉ base :=
    (List.nodup_cons.mp htail_nodup).1
  have hperm :
      (singleMindedAverageValueUpdateWindow bids j base value).Perm
        (j :: base) := by
    simpa [singleMindedAverageValueUpdateWindow] using
      (List.perm_orderedInsert
        (singleMindedAverageTieRel
          (singleMindedValueUpdate bids j value)) j base)
  exact hperm.symm.nodup (List.Nodup.cons hjbase hbase_nodup)

theorem singleMindedAverageValueUpdateWindow_facts_of_split
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base) :
    let window := singleMindedAverageValueUpdateWindow bids j base value
    SingleMindedAverageAmountDescending
      (singleMindedValueUpdate bids j value) window ∧
      window.Nodup ∧
      window.erase j = base ∧
      j ∈ window := by
  dsimp
  exact
    ⟨singleMindedAverageValueUpdateWindow_average_descending_of_split
        bids value horder,
      singleMindedAverageValueUpdateWindow_nodup_of_split bids value horder,
      singleMindedAverageValueUpdateWindow_erase_eq_of_split bids value horder,
      singleMindedAverageValueUpdateWindow_mem_j bids base j value⟩

theorem singleMindedAverageValueUpdateWindow_membership_iff_mechanism_of_split
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base)
    (hjaccepted :
      j ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])) :
    j ∈ singleMindedGreedyAcceptedFromOrder
        (singleMindedValueUpdate bids j value)
        (singleMindedAverageOrderOf
          (singleMindedValueUpdate bids j value)) ↔
      j ∈ singleMindedGreedyAcceptedFromState
        (singleMindedValueUpdate bids j value)
        ((singleMindedGreedyAcceptedFromState bids ∅
          (before ++ [j])).erase j)
        (singleMindedAverageValueUpdateWindow bids j base value) := by
  classical
  let updated := singleMindedValueUpdate bids j value
  let rel := singleMindedAverageTieRel updated
  let updatedOrder := singleMindedAverageOrderOf updated
  have hupdated_order :
      updatedOrder = (before ++ base).orderedInsert rel j := by
    simpa [updatedOrder, updated, rel] using
      singleMindedAverageOrderOf_valueUpdate_eq_orderedInsert_erase_of_split
        bids value horder
  have hprefix_state :
      (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])).erase j =
        singleMindedGreedyAcceptedFromState updated ∅ before := by
    simpa [updated] using
      singleMindedAverageValueUpdate_prefix_state_erase_of_split
        bids value horder hjaccepted
  have hpair_updated :
      updatedOrder.Pairwise rel := by
    simpa [updatedOrder, rel, singleMindedAverageOrderOf] using
      (Finset.pairwise_sort
        (s := (Finset.univ : Finset Bidder))
        (r := rel))
  have herase :
      updatedOrder.erase j = before ++ base := by
    simpa [updatedOrder, updated] using
      singleMindedAverageOrderOf_erase_valueUpdate_of_split
        bids value horder
  have hpair_base :
      (before ++ base).Pairwise rel := by
    have hsub :
        (updatedOrder.erase j).Pairwise rel :=
      List.Pairwise.sublist List.erase_sublist hpair_updated
    simpa [herase] using hsub
  have hpairwise_old :
      PairwiseDisjointDesired bids
        (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])) :=
    singleMindedGreedyAcceptedFromState_pairwiseDisjoint
      bids ∅ (before ++ [j]) (pairwiseDisjointDesired_empty bids)
  have hsafe :
      ∀ k,
        k ∈ singleMindedGreedyAcceptedFromState updated ∅ before →
          ¬ SingleMindedBidsConflict updated j k := by
    intro k hk hconf
    have hk_old_erase :
        k ∈
          (singleMindedGreedyAcceptedFromState bids ∅
            (before ++ [j])).erase j := by
      simpa [hprefix_state] using hk
    have hk_ne_j : k ≠ j := (Finset.mem_erase.mp hk_old_erase).1
    have hk_old :
        k ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j]) :=
      (Finset.mem_erase.mp hk_old_erase).2
    have hconf_old : SingleMindedBidsConflict bids j k := by
      simpa [updated] using
        (singleMindedValueUpdate_conflict_iff bids j value j k).1 hconf
    have hdisjoint :
        Disjoint (bids j).desired (bids k).desired :=
      hpairwise_old hjaccepted hk_old (fun hjk => hk_ne_j hjk.symm)
    rw [Finset.disjoint_left] at hdisjoint
    rcases hconf_old with ⟨g, hg⟩
    exact hdisjoint (Finset.mem_inter.mp hg).1 (Finset.mem_inter.mp hg).2
  have hiff :=
    singleMindedGreedyAcceptedFromState_orderedInsert_suffix_window_iff
      updated rel before base j hpair_base hsafe
  change
    j ∈ singleMindedGreedyAcceptedFromState updated ∅ updatedOrder ↔
      j ∈ singleMindedGreedyAcceptedFromState updated
        ((singleMindedGreedyAcceptedFromState bids ∅
          (before ++ [j])).erase j)
        (singleMindedAverageValueUpdateWindow bids j base value)
  rw [hupdated_order, hprefix_state]
  simpa [singleMindedAverageValueUpdateWindow, updated, rel] using hiff

theorem singleMindedPrecedes_append_cons_of_mem_prefix [DecidableEq Bidder]
    {order pre suffix : List Bidder} {earlier later : Bidder}
    (horder : order = pre ++ later :: suffix)
    (hearlier : earlier ∈ pre) :
    SingleMindedPrecedes order earlier later := by
  rcases List.mem_iff_append.mp hearlier with ⟨left, mid, hpre⟩
  refine ⟨left, mid, suffix, ?_⟩
  rw [horder, hpre]
  simp [List.append_assoc]

/--
The split-order greedy payment search only returns bids that occur after `j`
in the supplied order split.
-/
theorem singleMindedGreedyNextDeniedFromSplit_precedes
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j n : Bidder)
    (hnext :
      singleMindedGreedyNextDeniedFromSplit bids pre suffix j = some n) :
    SingleMindedPrecedes (pre ++ j :: suffix) j n := by
  have hn :
      n ∈ suffix :=
    (singleMindedGreedyNextDeniedFromSplit_some_spec
      bids pre suffix j n hnext).1
  rcases List.mem_iff_append.mp hn with ⟨left, right, hsuffix⟩
  refine ⟨pre, left, right, ?_⟩
  simpa [hsuffix, List.append_assoc]

/--
The full-order greedy payment search only returns bids after the first
occurrence split of `j`.
-/
theorem singleMindedGreedyNextDeniedFromOrder_precedes_of_split
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j n : Bidder)
    (hpre : j ∉ pre)
    (hnext :
      singleMindedGreedyNextDeniedFromOrder
        bids (pre ++ j :: suffix) j = some n) :
    SingleMindedPrecedes (pre ++ j :: suffix) j n := by
  have hsplit :
      singleMindedGreedyNextDeniedFromSplit bids pre suffix j = some n := by
    simpa [singleMindedGreedyNextDeniedFromOrder_eq_split
      bids pre suffix j hpre] using hnext
  exact singleMindedGreedyNextDeniedFromSplit_precedes
    bids pre suffix j n hsplit

theorem SingleMindedSqrtNormDescending.norm_le_of_precedes
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {order : List Bidder}
    {earlier later : Bidder}
    (hsorted : SingleMindedSqrtNormDescending bids order)
    (hprecedes : SingleMindedPrecedes order earlier later) :
    (bids later).sqrtAmountNorm ≤ (bids earlier).sqrtAmountNorm := by
  rcases hprecedes with ⟨left, mid, right, horder⟩
  dsimp [SingleMindedSqrtNormDescending] at hsorted
  rw [horder, List.pairwise_append] at hsorted
  rcases hsorted with ⟨_hleft, htail, _hcross⟩
  rw [List.pairwise_cons] at htail
  have hlater_mem : later ∈ mid ++ later :: right := by
    exact List.mem_append.mpr
      (Or.inr (by simp : later ∈ later :: right))
  exact htail.1 later hlater_mem

theorem SingleMindedAverageAmountDescending.average_le_of_precedes
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {order : List Bidder}
    {earlier later : Bidder}
    (hsorted : SingleMindedAverageAmountDescending bids order)
    (hprecedes : SingleMindedPrecedes order earlier later) :
    (bids later).averageAmountPerGood ≤
      (bids earlier).averageAmountPerGood := by
  rcases hprecedes with ⟨left, mid, right, horder⟩
  dsimp [SingleMindedAverageAmountDescending] at hsorted
  rw [horder, List.pairwise_append] at hsorted
  rcases hsorted with ⟨_hleft, htail, _hcross⟩
  rw [List.pairwise_cons] at htail
  have hlater_mem : later ∈ mid ++ later :: right := by
    exact List.mem_append.mpr
      (Or.inr (by simp : later ∈ later :: right))
  exact htail.1 later hlater_mem

theorem SingleMindedAverageAmountDescending.not_precedes_of_average_lt
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {order : List Bidder}
    {earlier later : Bidder}
    (hsorted : SingleMindedAverageAmountDescending bids order)
    (hlt :
      (bids earlier).averageAmountPerGood <
        (bids later).averageAmountPerGood) :
    ¬ SingleMindedPrecedes order earlier later := by
  intro hprecedes
  have hle := hsorted.average_le_of_precedes hprecedes
  linarith

theorem singleMindedPrecedes_or_precedes_of_mem
    [DecidableEq Bidder]
    {order : List Bidder} {i j : Bidder}
    (hi : i ∈ order) (hj : j ∈ order) (hij : i ≠ j) :
    SingleMindedPrecedes order i j ∨ SingleMindedPrecedes order j i := by
  rcases List.mem_iff_append.mp hi with ⟨left, right, horder⟩
  have hj_mem : j ∈ left ++ i :: right := by
    simpa [horder] using hj
  rw [List.mem_append] at hj_mem
  rcases hj_mem with hjleft | hjtail
  · right
    exact singleMindedPrecedes_append_cons_of_mem_prefix horder hjleft
  · have hji_ne : j ≠ i := fun hji => hij hji.symm
    have hjright : j ∈ right := by
      simpa [hji_ne] using hjtail
    left
    rcases List.mem_iff_append.mp hjright with ⟨mid, tail, hright⟩
    refine ⟨left, mid, tail, ?_⟩
    rw [horder, hright]

theorem SingleMindedAverageAmountDescending.precedes_of_average_lt
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {order : List Bidder}
    {higher lower : Bidder}
    (hsorted : SingleMindedAverageAmountDescending bids order)
    (hhigher : higher ∈ order) (hlower : lower ∈ order)
    (hne : higher ≠ lower)
    (hlt :
      (bids lower).averageAmountPerGood <
        (bids higher).averageAmountPerGood) :
    SingleMindedPrecedes order higher lower := by
  rcases singleMindedPrecedes_or_precedes_of_mem hhigher hlower hne with
    hhighlow | hlowhigh
  · exact hhighlow
  · exact False.elim (hsorted.not_precedes_of_average_lt hlt hlowhigh)

theorem SingleMindedAverageAmountDescending.exists_split_of_average_lt
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {order : List Bidder}
    {higher lower : Bidder}
    (hsorted : SingleMindedAverageAmountDescending bids order)
    (hhigher : higher ∈ order) (hlower : lower ∈ order)
    (hne : higher ≠ lower)
    (hlt :
      (bids lower).averageAmountPerGood <
        (bids higher).averageAmountPerGood) :
    ∃ pre between tail,
      order = ((pre ++ [higher]) ++ between) ++ lower :: tail := by
  rcases hsorted.precedes_of_average_lt hhigher hlower hne hlt with
    ⟨pre, between, tail, horder⟩
  refine ⟨pre, between, tail, ?_⟩
  rw [horder]
  simp [List.append_assoc]

theorem SingleMindedAverageAmountDescending.exists_split_nodup_of_average_lt
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {order : List Bidder}
    {higher lower : Bidder}
    (hsorted : SingleMindedAverageAmountDescending bids order)
    (hnodup : order.Nodup)
    (hhigher : higher ∈ order) (hlower : lower ∈ order)
    (hlt :
      (bids lower).averageAmountPerGood <
        (bids higher).averageAmountPerGood) :
    ∃ pre between tail,
      order = ((pre ++ [higher]) ++ between) ++ lower :: tail ∧
        lower ∉ pre ∧ lower ∉ between ∧ lower ∉ tail := by
  have hne : higher ≠ lower := by
    intro h
    subst higher
    exact (lt_irrefl _ hlt).elim
  rcases hsorted.exists_split_of_average_lt hhigher hlower hne hlt with
    ⟨pre, between, tail, horder⟩
  have hnodup_split :
      (((pre ++ [higher]) ++ between) ++ lower :: tail).Nodup := by
    simpa [horder] using hnodup
  have hnot_pref :
      lower ∉ (pre ++ [higher]) ++ between := by
    intro hmem
    have hdisjoint := (List.nodup_append.mp hnodup_split).2.2
    exact hdisjoint lower hmem lower (by simp) rfl
  have hnot_pre : lower ∉ pre := by
    intro hlower_pre
    exact hnot_pref (by simp [hlower_pre])
  have hnot_between : lower ∉ between := by
    intro hlower_between
    exact hnot_pref (by simp [hlower_between])
  have hnot_tail : lower ∉ tail := by
    have htail_nodup : (lower :: tail).Nodup :=
      (List.nodup_append.mp hnodup_split).2.1
    exact (List.nodup_cons.mp htail_nodup).1
  exact ⟨pre, between, tail, horder, hnot_pre, hnot_between, hnot_tail⟩

theorem SingleMindedAverageAmountDescending.precedes_of_value_lt_bundleSize_mul_average
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {order : List Bidder}
    {j n : Bidder}
    (hsorted : SingleMindedAverageAmountDescending bids order)
    (hj : j ∈ order) (hn : n ∈ order) (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).value <
        (bids j).bundleSize * (bids n).averageAmountPerGood) :
    SingleMindedPrecedes order n j := by
  have havg :
      (bids j).averageAmountPerGood <
        (bids n).averageAmountPerGood :=
    (bids j).averageAmountPerGood_lt_of_value_lt_bundleSize_mul
      (bids n) hj_nonempty hlt
  exact hsorted.precedes_of_average_lt hn hj hjn.symm havg

theorem SingleMindedAverageAmountDescending.exists_split_of_value_lt_bundleSize_mul_average
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {order : List Bidder}
    {j n : Bidder}
    (hsorted : SingleMindedAverageAmountDescending bids order)
    (hj : j ∈ order) (hn : n ∈ order) (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).value <
        (bids j).bundleSize * (bids n).averageAmountPerGood) :
    ∃ pre between tail,
      order = ((pre ++ [n]) ++ between) ++ j :: tail := by
  have hprecedes :
      SingleMindedPrecedes order n j :=
    hsorted.precedes_of_value_lt_bundleSize_mul_average
      hj hn hjn hj_nonempty hlt
  rcases hprecedes with ⟨pre, between, tail, horder⟩
  refine ⟨pre, between, tail, ?_⟩
  rw [horder]
  simp [List.append_assoc]

theorem SingleMindedAverageAmountDescending.precedes_of_bundleSize_mul_average_lt_value
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {order : List Bidder}
    {j n : Bidder}
    (hsorted : SingleMindedAverageAmountDescending bids order)
    (hj : j ∈ order) (hn : n ∈ order) (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).bundleSize * (bids n).averageAmountPerGood <
        (bids j).value) :
    SingleMindedPrecedes order j n := by
  have havg :
      (bids n).averageAmountPerGood <
        (bids j).averageAmountPerGood :=
    (bids j).averageAmountPerGood_lt_of_bundleSize_mul_lt_value
      (bids n) hj_nonempty hlt
  exact hsorted.precedes_of_average_lt hj hn hjn havg

theorem SingleMindedAverageAmountDescending.exists_split_of_bundleSize_mul_average_lt_value
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {order : List Bidder}
    {j n : Bidder}
    (hsorted : SingleMindedAverageAmountDescending bids order)
    (hj : j ∈ order) (hn : n ∈ order) (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).bundleSize * (bids n).averageAmountPerGood <
        (bids j).value) :
    ∃ pre between tail,
      order = ((pre ++ [j]) ++ between) ++ n :: tail := by
  have hprecedes :
      SingleMindedPrecedes order j n :=
    hsorted.precedes_of_bundleSize_mul_average_lt_value
      hj hn hjn hj_nonempty hlt
  rcases hprecedes with ⟨pre, between, tail, horder⟩
  refine ⟨pre, between, tail, ?_⟩
  rw [horder]
  simp [List.append_assoc]

theorem SingleMindedAverageAmountDescending.exists_split_nodup_of_value_update_lt_payment
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {orderUpdated : List Bidder}
    {j n : Bidder} (value : ℝ)
    (hsorted :
      SingleMindedAverageAmountDescending
        (singleMindedValueUpdate bids j value) orderUpdated)
    (hnodup : orderUpdated.Nodup)
    (hj : j ∈ orderUpdated) (hn : n ∈ orderUpdated)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      value < (bids j).bundleSize * (bids n).averageAmountPerGood) :
    ∃ pre between tail,
      orderUpdated = ((pre ++ [n]) ++ between) ++ j :: tail ∧
        j ∉ pre ∧ j ∉ between ∧ j ∉ tail := by
  let updated := singleMindedValueUpdate bids j value
  have hj_nonempty_updated : (updated j).desired.Nonempty := by
    simpa [updated] using hj_nonempty
  have hlt_updated :
      (updated j).value <
        (updated j).bundleSize * (updated n).averageAmountPerGood := by
    simpa [updated, singleMindedValueUpdate, hjn.symm] using hlt
  have havg :
      (updated j).averageAmountPerGood <
        (updated n).averageAmountPerGood :=
    (updated j).averageAmountPerGood_lt_of_value_lt_bundleSize_mul
      (updated n) hj_nonempty_updated hlt_updated
  exact
    hsorted.exists_split_nodup_of_average_lt hnodup hn hj havg

theorem SingleMindedAverageAmountDescending.exists_split_nodup_of_payment_lt_value_update
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item} {orderUpdated : List Bidder}
    {j n : Bidder} (value : ℝ)
    (hsorted :
      SingleMindedAverageAmountDescending
        (singleMindedValueUpdate bids j value) orderUpdated)
    (hnodup : orderUpdated.Nodup)
    (hj : j ∈ orderUpdated) (hn : n ∈ orderUpdated)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).bundleSize * (bids n).averageAmountPerGood < value) :
    ∃ pre between tail,
      orderUpdated = ((pre ++ [j]) ++ between) ++ n :: tail ∧
        n ∉ pre ∧ n ∉ between ∧ n ∉ tail := by
  let updated := singleMindedValueUpdate bids j value
  have hj_nonempty_updated : (updated j).desired.Nonempty := by
    simpa [updated] using hj_nonempty
  have hlt_updated :
      (updated j).bundleSize * (updated n).averageAmountPerGood <
        (updated j).value := by
    simpa [updated, singleMindedValueUpdate, hjn.symm] using hlt
  have havg :
      (updated n).averageAmountPerGood <
        (updated j).averageAmountPerGood :=
    (updated j).averageAmountPerGood_lt_of_bundleSize_mul_lt_value
      (updated n) hj_nonempty_updated hlt_updated
  exact
    hsorted.exists_split_nodup_of_average_lt hnodup hj hn havg

theorem SingleMindedAverageAmountDescending.exists_reposition_of_value_update_lt_payment_and_erase
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {orderUpdated pre nextPost : List Bidder} {j n : Bidder} (value : ℝ)
    (hsorted :
      SingleMindedAverageAmountDescending
        (singleMindedValueUpdate bids j value) orderUpdated)
    (hnodup : orderUpdated.Nodup)
    (hj : j ∈ orderUpdated) (hn : n ∈ orderUpdated)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      value < (bids j).bundleSize * (bids n).averageAmountPerGood)
    (herase : orderUpdated.erase j = pre ++ n :: nextPost) :
    ∃ between tail,
      orderUpdated = (((pre ++ [n]) ++ between) ++ j :: tail) ∧
        j ∉ between ∧ j ∉ tail := by
  rcases hsorted.exists_split_nodup_of_value_update_lt_payment
      value hnodup hj hn hjn hj_nonempty hlt with
    ⟨preUpdated, between, tail, horder, hj_not_preUpdated,
      hj_not_between, hj_not_tail⟩
  have hnodup_split :
      (((preUpdated ++ [n]) ++ between) ++ j :: tail).Nodup := by
    simpa [horder] using hnodup
  have hnodup_at_n :
      (preUpdated ++ n :: (between ++ j :: tail)).Nodup := by
    simpa [List.append_assoc] using hnodup_split
  have hn_not_preUpdated : n ∉ preUpdated := by
    have hdisjoint := (List.nodup_append.mp hnodup_at_n).2.2
    intro hnmem
    exact hdisjoint n hnmem n (by simp) rfl
  have hn_not_after : n ∉ between ++ j :: tail := by
    have htail_nodup := (List.nodup_append.mp hnodup_at_n).2.1
    exact (List.nodup_cons.mp htail_nodup).1
  have hn_not_between_tail : n ∉ between ++ tail := by
    intro hnmem
    rw [List.mem_append] at hnmem
    rcases hnmem with hn_between | hn_tail
    · exact hn_not_after (List.mem_append.mpr (Or.inl hn_between))
    · exact hn_not_after
        (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem j hn_tail)))
  have herase_split :
      orderUpdated.erase j =
        ((preUpdated ++ [n]) ++ between) ++ tail := by
    rw [horder]
    have hj_not_left : j ∉ (preUpdated ++ [n]) ++ between := by
      intro hjmem
      rw [List.mem_append] at hjmem
      rcases hjmem with hjmem_left | hjmem_between
      · rw [List.mem_append] at hjmem_left
        rcases hjmem_left with hjmem_pre | hjmem_n
        · exact hj_not_preUpdated hjmem_pre
        · exact hjn (by simpa using hjmem_n)
      · exact hj_not_between hjmem_between
    rw [List.erase_append_right (j :: tail) hj_not_left]
    simp
  have hwithout_j :
      preUpdated ++ n :: (between ++ tail) = pre ++ n :: nextPost := by
    simpa [List.append_assoc] using herase_split.symm.trans herase
  have hparts :=
    (List.append_cons_inj_of_notMem hn_not_preUpdated
      hn_not_between_tail).mp hwithout_j
  have hpre : preUpdated = pre := hparts.1
  refine ⟨between, tail, ?_, hj_not_between, hj_not_tail⟩
  simpa [hpre] using horder

theorem SingleMindedAverageAmountDescending.exists_reposition_of_payment_lt_value_update_and_erase
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {orderUpdated pre nextPost : List Bidder} {j n : Bidder} (value : ℝ)
    (hsorted :
      SingleMindedAverageAmountDescending
        (singleMindedValueUpdate bids j value) orderUpdated)
    (hnodup : orderUpdated.Nodup)
    (hj : j ∈ orderUpdated) (hn : n ∈ orderUpdated)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).bundleSize * (bids n).averageAmountPerGood < value)
    (herase : orderUpdated.erase j = pre ++ n :: nextPost) :
    ∃ pref rest tail,
      pre = pref ++ rest ∧ orderUpdated = pref ++ j :: tail := by
  rcases hsorted.exists_split_nodup_of_payment_lt_value_update
      value hnodup hj hn hjn hj_nonempty hlt with
    ⟨pref, between, tailAfterN, horder, hn_not_pref,
      hn_not_between, hn_not_tailAfterN⟩
  have hnodup_split :
      (((pref ++ [j]) ++ between) ++ n :: tailAfterN).Nodup := by
    simpa [horder] using hnodup
  have hnodup_at_j :
      (pref ++ j :: (between ++ n :: tailAfterN)).Nodup := by
    simpa [List.append_assoc] using hnodup_split
  have hj_not_pref : j ∉ pref := by
    have hdisjoint := (List.nodup_append.mp hnodup_at_j).2.2
    intro hjmem
    exact hdisjoint j hjmem j (by simp) rfl
  have hj_not_after : j ∉ between ++ n :: tailAfterN := by
    have htail_nodup := (List.nodup_append.mp hnodup_at_j).2.1
    exact (List.nodup_cons.mp htail_nodup).1
  have hj_not_between : j ∉ between := by
    intro hjmem
    exact hj_not_after (by simp [hjmem])
  have hj_not_tailAfterN : j ∉ tailAfterN := by
    intro hjmem
    exact hj_not_after (by simp [hjn, hjmem])
  have hn_not_pref_between : n ∉ pref ++ between := by
    intro hnmem
    rw [List.mem_append] at hnmem
    rcases hnmem with hn_pref | hn_between
    · exact hn_not_pref hn_pref
    · exact hn_not_between hn_between
  have herase_split :
      orderUpdated.erase j = (pref ++ between) ++ n :: tailAfterN := by
    rw [horder]
    have herase_pref :
        (pref ++ j :: (between ++ n :: tailAfterN)).erase j =
          pref ++ (between ++ n :: tailAfterN) := by
      rw [List.erase_append_right (j :: (between ++ n :: tailAfterN)) hj_not_pref]
      simp
    simpa [List.append_assoc] using herase_pref
  have hwithout_j :
      (pref ++ between) ++ n :: tailAfterN = pre ++ n :: nextPost := by
    exact herase_split.symm.trans herase
  have hparts :=
    (List.append_cons_inj_of_notMem hn_not_pref_between
      hn_not_tailAfterN).mp hwithout_j
  have hpre : pref ++ between = pre := hparts.1
  refine ⟨pref, between, between ++ n :: tailAfterN, ?_, ?_⟩
  · exact hpre.symm
  · simpa [List.append_assoc] using horder

theorem singleMindedGreedyValueUpdate_local_critical_window_of_sorted_erase
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost lowOrder highOrder : List Bidder) {j n : Bidder}
    (lowValue highValue : ℝ)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hjpre : j ∉ pre)
    (hnodup_original : (pre ++ n :: nextPost).Nodup)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n)
    (hlow_sorted :
      SingleMindedAverageAmountDescending
        (singleMindedValueUpdate bids j lowValue) lowOrder)
    (hhigh_sorted :
      SingleMindedAverageAmountDescending
        (singleMindedValueUpdate bids j highValue) highOrder)
    (hlow_nodup : lowOrder.Nodup)
    (hhigh_nodup : highOrder.Nodup)
    (hlow_erase : lowOrder.erase j = pre ++ n :: nextPost)
    (hhigh_erase : highOrder.erase j = pre ++ n :: nextPost)
    (hj_low : j ∈ lowOrder) (hj_high : j ∈ highOrder)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty) :
    (lowValue < (bids j).bundleSize * (bids n).averageAmountPerGood →
      j ∉ singleMindedGreedyAcceptedFromState
        (singleMindedValueUpdate bids j lowValue) (acceptedWithJ.erase j)
        lowOrder) ∧
    ((bids j).bundleSize * (bids n).averageAmountPerGood < highValue →
      j ∈ singleMindedGreedyAcceptedFromState
        (singleMindedValueUpdate bids j highValue) (acceptedWithJ.erase j)
        highOrder) := by
  have hn_low : n ∈ lowOrder := by
    exact List.mem_of_mem_erase (by rw [hlow_erase]; simp)
  have hn_high : n ∈ highOrder := by
    exact List.mem_of_mem_erase (by rw [hhigh_erase]; simp)
  exact
    singleMindedGreedyValueUpdate_local_critical_window
      bids acceptedWithJ pre nextPost lowOrder highOrder lowValue highValue
      hjaccepted hpairwise hjpre hnodup_original hnext
      (fun hlt =>
        hlow_sorted.exists_reposition_of_value_update_lt_payment_and_erase
          lowValue hlow_nodup hj_low hn_low hjn hj_nonempty hlt
          hlow_erase)
      (fun hlt =>
        hhigh_sorted.exists_reposition_of_payment_lt_value_update_and_erase
          highValue hhigh_nodup hj_high hn_high hjn hj_nonempty hlt
          hhigh_erase)

theorem singleMindedGreedyAcceptedFromState_accepts_after_value_update_of_no_nextDenied
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (base windowOrder : List Bidder) {j : Bidder} (value : ℝ)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hnodup : windowOrder.Nodup)
    (herase : windowOrder.erase j = base)
    (hjmem : j ∈ windowOrder)
    (hnext :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ base j = none) :
    j ∈ singleMindedGreedyAcceptedFromState
      (singleMindedValueUpdate bids j value) (acceptedWithJ.erase j)
      windowOrder := by
  rcases List.mem_iff_append.mp hjmem with ⟨pref, tail, horder⟩
  have hnodup_split : (pref ++ j :: tail).Nodup := by
    simpa [horder] using hnodup
  have hjpref : j ∉ pref := by
    intro hjpref
    have hdisjoint := (List.nodup_append.mp hnodup_split).2.2
    exact hdisjoint j hjpref j (by simp) rfl
  have herase_split : windowOrder.erase j = pref ++ tail := by
    rw [horder]
    rw [List.erase_append_right (j :: tail) hjpref]
    simp
  have hbase : base = pref ++ tail := by
    exact herase.symm.trans herase_split
  have hno :
      ∀ i, i ∈ pref →
        ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState
          bids acceptedWithJ pref j i := by
    intro i hi hdenied
    have hi_base : i ∈ base := by
      rw [hbase]
      exact List.mem_append.mpr (Or.inl hi)
    have hdenied_base :
        SingleMindedGreedyDeniedBecauseOfInSuffixFromState
          bids acceptedWithJ base j i := by
      simpa [hbase] using hdenied.append_right tail
    exact
      (singleMindedGreedyFirstDeniedBecauseOfFromState_none_no_candidate
        bids acceptedWithJ base j hnext i hi_base) hdenied_base
  rw [horder]
  exact
    singleMindedGreedyAcceptedFromState_accepts_after_value_update_of_no_candidate_prefix
      bids acceptedWithJ pref tail value hjaccepted hpairwise hjpref hno

/--
Local order-window package for the finite `n(j) = n` branch of the source
greedy payment. It records the sorted window used for value-only perturbations
and the bridge from that local rerun back to the full greedy mechanism.
-/
structure SingleMindedSortedEraseCriticalWindow [DecidableEq Bidder]
    [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder) (j : Bidder)
    (base : List Bidder) (windowOrder : ℝ → List Bidder) : Prop where
  sorted : ∀ v,
    SingleMindedAverageAmountDescending
      (singleMindedValueUpdate bids j v) (windowOrder v)
  nodup : ∀ v, (windowOrder v).Nodup
  erase_eq : ∀ v, (windowOrder v).erase j = base
  mem_j : ∀ v, j ∈ windowOrder v
  reject_window_to_mechanism : ∀ v,
    j ∉ singleMindedGreedyAcceptedFromState
        (singleMindedValueUpdate bids j v) (acceptedWithJ.erase j)
        (windowOrder v) →
      j ∉ singleMindedGreedyAcceptedFromOrder
        (singleMindedValueUpdate bids j v)
        (orderOf (singleMindedValueUpdate bids j v))
  accept_window_to_mechanism : ∀ v,
    j ∈ singleMindedGreedyAcceptedFromState
        (singleMindedValueUpdate bids j v) (acceptedWithJ.erase j)
        (windowOrder v) →
      j ∈ singleMindedGreedyAcceptedFromOrder
        (singleMindedValueUpdate bids j v)
        (orderOf (singleMindedValueUpdate bids j v))

/--
Full-order package for the source Section 10 critical-window argument. It
connects the displayed split of the original sorted order around accepted `j`
to the local erase-stable windows used by the finite and zero critical-branch
theorems.
-/
structure SingleMindedFullOrderSortedEraseCriticalWindow [DecidableEq Bidder]
    [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder) (j : Bidder)
    (base : List Bidder) (windowOrder : ℝ → List Bidder) where
  before : List Bidder
  order_eq : orderOf bids = before ++ j :: base
  acceptedWithJ_eq :
    acceptedWithJ =
      singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])
  hjaccepted : j ∈ acceptedWithJ
  order_nodup : (orderOf bids).Nodup
  window :
    SingleMindedSortedEraseCriticalWindow orderOf bids acceptedWithJ j
      base windowOrder

theorem singleMindedAverageValueUpdateWindow_sortedEraseCriticalWindow_of_split
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    {before base : List Bidder} {j : Bidder}
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base)
    (hreject : ∀ v,
      j ∉ singleMindedGreedyAcceptedFromState
          (singleMindedValueUpdate bids j v) (acceptedWithJ.erase j)
          (singleMindedAverageValueUpdateWindow bids j base v) →
        j ∉ singleMindedGreedyAcceptedFromOrder
          (singleMindedValueUpdate bids j v)
          (singleMindedAverageOrderOf
            (singleMindedValueUpdate bids j v)))
    (haccept : ∀ v,
      j ∈ singleMindedGreedyAcceptedFromState
          (singleMindedValueUpdate bids j v) (acceptedWithJ.erase j)
          (singleMindedAverageValueUpdateWindow bids j base v) →
        j ∈ singleMindedGreedyAcceptedFromOrder
          (singleMindedValueUpdate bids j v)
          (singleMindedAverageOrderOf
            (singleMindedValueUpdate bids j v))) :
    SingleMindedSortedEraseCriticalWindow
      (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))
      bids acceptedWithJ j base
      (singleMindedAverageValueUpdateWindow bids j base) := by
  refine
    { sorted := ?_,
      nodup := ?_,
      erase_eq := ?_,
      mem_j := ?_,
      reject_window_to_mechanism := hreject,
      accept_window_to_mechanism := haccept }
  · intro v
    exact
      singleMindedAverageValueUpdateWindow_average_descending_of_split
        bids v horder
  · intro v
    exact
      singleMindedAverageValueUpdateWindow_nodup_of_split bids v horder
  · intro v
    exact
      singleMindedAverageValueUpdateWindow_erase_eq_of_split bids v horder
  · intro v
    exact singleMindedAverageValueUpdateWindow_mem_j bids base j v

def singleMindedAverageValueUpdateWindow_fullOrderSortedEraseCriticalWindow_of_split
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder}
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base)
    (hjaccepted :
      j ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j]))
    (hreject : ∀ v,
      j ∉ singleMindedGreedyAcceptedFromState
          (singleMindedValueUpdate bids j v)
          ((singleMindedGreedyAcceptedFromState bids ∅
            (before ++ [j])).erase j)
          (singleMindedAverageValueUpdateWindow bids j base v) →
        j ∉ singleMindedGreedyAcceptedFromOrder
          (singleMindedValueUpdate bids j v)
          (singleMindedAverageOrderOf
            (singleMindedValueUpdate bids j v)))
    (haccept : ∀ v,
      j ∈ singleMindedGreedyAcceptedFromState
          (singleMindedValueUpdate bids j v)
          ((singleMindedGreedyAcceptedFromState bids ∅
            (before ++ [j])).erase j)
          (singleMindedAverageValueUpdateWindow bids j base v) →
        j ∈ singleMindedGreedyAcceptedFromOrder
          (singleMindedValueUpdate bids j v)
          (singleMindedAverageOrderOf
            (singleMindedValueUpdate bids j v))) :
    SingleMindedFullOrderSortedEraseCriticalWindow
      (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))
      bids (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j]))
      j base (singleMindedAverageValueUpdateWindow bids j base) := by
  refine
    { before := before,
      order_eq := horder,
      acceptedWithJ_eq := rfl,
      hjaccepted := hjaccepted,
      order_nodup := ?_,
      window := ?_ }
  · exact singleMindedAverageOrderOf_nodup bids
  · exact
      singleMindedAverageValueUpdateWindow_sortedEraseCriticalWindow_of_split
        bids (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j]))
        horder hreject haccept

theorem singleMindedAverageValueUpdateWindow_sortedEraseCriticalWindow_of_split_data
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder}
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base)
    (hjaccepted :
      j ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])) :
    SingleMindedSortedEraseCriticalWindow
      (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))
      bids (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j]))
      j base (singleMindedAverageValueUpdateWindow bids j base) := by
  exact
    singleMindedAverageValueUpdateWindow_sortedEraseCriticalWindow_of_split
      bids (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j]))
      horder
      (fun v hlocal hglobal =>
        hlocal
          ((singleMindedAverageValueUpdateWindow_membership_iff_mechanism_of_split
            bids v horder hjaccepted).1 hglobal))
      (fun v hlocal =>
        (singleMindedAverageValueUpdateWindow_membership_iff_mechanism_of_split
          bids v horder hjaccepted).2 hlocal)

def singleMindedAverageValueUpdateWindow_fullOrderSortedEraseCriticalWindow_of_split_data
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder}
    (horder :
      singleMindedAverageOrderOf bids = before ++ j :: base)
    (hjaccepted :
      j ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])) :
    SingleMindedFullOrderSortedEraseCriticalWindow
      (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))
      bids (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j]))
      j base (singleMindedAverageValueUpdateWindow bids j base) := by
  refine
    { before := before,
      order_eq := horder,
      acceptedWithJ_eq := rfl,
      hjaccepted := hjaccepted,
      order_nodup := ?_,
      window := ?_ }
  · exact singleMindedAverageOrderOf_nodup bids
  · exact
      singleMindedAverageValueUpdateWindow_sortedEraseCriticalWindow_of_split_data
        bids horder hjaccepted

theorem singleMindedGreedyAcceptedMechanism_finite_branch_of_nextDenied_some
    [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost : List Bidder) {j n : Bidder}
    (windowOrder : ℝ → List Bidder)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hjpre : j ∉ pre)
    (hnodup_original : (pre ++ n :: nextPost).Nodup)
    (hnext_state :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n)
    (hwindow :
      SingleMindedSortedEraseCriticalWindow orderOf bids acceptedWithJ j
        (pre ++ n :: nextPost) windowOrder)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hj_final :
      j ∈ singleMindedGreedyAcceptedFromOrder bids (orderOf bids))
    (hnext_order :
      singleMindedGreedyNextDeniedFromOrder bids (orderOf bids) j = some n) :
    let M := singleMindedGreedyAcceptedMechanismFromOrderOf orderOf
    let p := (bids j).bundleSize * (bids n).averageAmountPerGood
    (∀ v, v < p →
      j ∉ M.accepted (singleMindedValueUpdate bids j v)) ∧
    (∀ v, p < v →
      j ∈ M.accepted (singleMindedValueUpdate bids j v)) ∧
    M.payment bids j = p := by
  classical
  dsimp
  constructor
  · intro v hv
    have hlocal :=
      singleMindedGreedyValueUpdate_local_critical_window_of_sorted_erase
        bids acceptedWithJ pre nextPost (windowOrder v) (windowOrder v) v v
        hjaccepted hpairwise hjpre hnodup_original hnext_state
        (hwindow.sorted v) (hwindow.sorted v)
        (hwindow.nodup v) (hwindow.nodup v)
        (hwindow.erase_eq v) (hwindow.erase_eq v)
        (hwindow.mem_j v) (hwindow.mem_j v) hjn hj_nonempty
    exact hwindow.reject_window_to_mechanism v (hlocal.1 hv)
  · constructor
    · intro v hv
      have hlocal :=
        singleMindedGreedyValueUpdate_local_critical_window_of_sorted_erase
          bids acceptedWithJ pre nextPost (windowOrder v) (windowOrder v) v v
          hjaccepted hpairwise hjpre hnodup_original hnext_state
          (hwindow.sorted v) (hwindow.sorted v)
          (hwindow.nodup v) (hwindow.nodup v)
          (hwindow.erase_eq v) (hwindow.erase_eq v)
          (hwindow.mem_j v) (hwindow.mem_j v) hjn hj_nonempty
      exact hwindow.accept_window_to_mechanism v (hlocal.2 hv)
    · have hpay :
          singleMindedGreedyPaymentFromOrder bids (orderOf bids) j =
            (bids j).bundleSize * (bids n).averageAmountPerGood :=
        singleMindedGreedyPaymentFromOrder_eq_of_next
          bids (orderOf bids) hj_final hnext_order
      simpa [singleMindedGreedyAcceptedMechanismFromOrderOf] using hpay

theorem singleMindedGreedyAcceptedMechanism_zero_branch_of_nextDenied_none
    [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (base : List Bidder) {j : Bidder}
    (windowOrder : ℝ → List Bidder)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hnext_state :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ base j = none)
    (hwindow :
      SingleMindedSortedEraseCriticalWindow orderOf bids acceptedWithJ j
        base windowOrder)
    (hj_final :
      j ∈ singleMindedGreedyAcceptedFromOrder bids (orderOf bids))
    (hnext_order :
      singleMindedGreedyNextDeniedFromOrder bids (orderOf bids) j = none) :
    let M := singleMindedGreedyAcceptedMechanismFromOrderOf orderOf
    (∀ v, 0 ≤ v → v < 0 →
      j ∉ M.accepted (singleMindedValueUpdate bids j v)) ∧
    (∀ v, 0 < v →
      j ∈ M.accepted (singleMindedValueUpdate bids j v)) ∧
    M.payment bids j = 0 := by
  classical
  dsimp
  constructor
  · intro v hv_nonneg hv_lt
    exact False.elim (not_lt_of_ge hv_nonneg hv_lt)
  · constructor
    · intro v _hv_pos
      have hlocal :
          j ∈ singleMindedGreedyAcceptedFromState
            (singleMindedValueUpdate bids j v) (acceptedWithJ.erase j)
            (windowOrder v) :=
        singleMindedGreedyAcceptedFromState_accepts_after_value_update_of_no_nextDenied
          bids acceptedWithJ base (windowOrder v) v hjaccepted hpairwise
          (hwindow.nodup v) (hwindow.erase_eq v) (hwindow.mem_j v)
          hnext_state
      exact hwindow.accept_window_to_mechanism v hlocal
    · have hpay :
          singleMindedGreedyPaymentFromOrder bids (orderOf bids) j = 0 :=
        singleMindedGreedyPaymentFromOrder_eq_zero_of_no_next
          bids (orderOf bids) hj_final hnext_order
      simpa [singleMindedGreedyAcceptedMechanismFromOrderOf] using hpay

theorem singleMindedGreedyAcceptedMechanism_finite_branch_of_sorted_window
    [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost : List Bidder) {j n : Bidder}
    (windowOrder : ℝ → List Bidder)
    (hsource :
      SingleMindedFullOrderSortedEraseCriticalWindow orderOf bids acceptedWithJ j
        (pre ++ n :: nextPost) windowOrder)
    (hnext_order :
      singleMindedGreedyNextDeniedFromOrder bids (orderOf bids) j = some n)
    (hj_nonempty : (bids j).desired.Nonempty) :
    let M := singleMindedGreedyAcceptedMechanismFromOrderOf orderOf
    let p := (bids j).bundleSize * (bids n).averageAmountPerGood
    (∀ v, v < p →
      j ∉ M.accepted (singleMindedValueUpdate bids j v)) ∧
    (∀ v, p < v →
      j ∈ M.accepted (singleMindedValueUpdate bids j v)) ∧
    M.payment bids j = p := by
  classical
  have hnodup_order :
      (hsource.before ++ j :: (pre ++ n :: nextPost)).Nodup := by
    simpa [hsource.order_eq] using hsource.order_nodup
  have htail_nodup : (j :: (pre ++ n :: nextPost)).Nodup :=
    (List.nodup_append.mp hnodup_order).2.1
  have hjbase : j ∉ pre ++ n :: nextPost :=
    (List.nodup_cons.mp htail_nodup).1
  have hnodup_original : (pre ++ n :: nextPost).Nodup :=
    (List.nodup_cons.mp htail_nodup).2
  have hjpre : j ∉ pre := by
    intro hjpre
    exact hjbase (List.mem_append.mpr (Or.inl hjpre))
  have hjn : j ≠ n := by
    intro h
    subst n
    exact hjbase (by simp)
  have hbefore : j ∉ hsource.before := by
    have hdisjoint := (List.nodup_append.mp hnodup_order).2.2
    intro hjbefore
    exact hdisjoint j hjbefore j (by simp) rfl
  have hnext_split :
      singleMindedGreedyNextDeniedFromSplit bids hsource.before
        (pre ++ n :: nextPost) j = some n := by
    have hnext_display :
        singleMindedGreedyNextDeniedFromOrder bids
          (hsource.before ++ j :: (pre ++ n :: nextPost)) j = some n := by
      simpa [hsource.order_eq] using hnext_order
    simpa [
      singleMindedGreedyNextDeniedFromOrder_eq_split
        bids hsource.before (pre ++ n :: nextPost) j hbefore] using
      hnext_display
  have hnext_state :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n := by
    simpa [singleMindedGreedyNextDeniedFromSplit,
      hsource.acceptedWithJ_eq] using hnext_split
  have hpairwise : PairwiseDisjointDesired bids acceptedWithJ := by
    have hstate_pairwise :
        PairwiseDisjointDesired bids
          (singleMindedGreedyAcceptedFromState bids ∅ (hsource.before ++ [j])) :=
      singleMindedGreedyAcceptedFromState_pairwiseDisjoint
        bids ∅ (hsource.before ++ [j]) (pairwiseDisjointDesired_empty bids)
    simpa [hsource.acceptedWithJ_eq] using hstate_pairwise
  have hj_final :
      j ∈ singleMindedGreedyAcceptedFromOrder bids (orderOf bids) := by
    have hj_state :
        j ∈ singleMindedGreedyAcceptedFromState bids acceptedWithJ
          (pre ++ n :: nextPost) :=
      singleMindedGreedyAcceptedFromState_contains_initial
        bids acceptedWithJ (pre ++ n :: nextPost) hsource.hjaccepted
    have hdecomp :
        hsource.before ++ j :: (pre ++ n :: nextPost) =
          (hsource.before ++ [j]) ++ (pre ++ n :: nextPost) := by
      simp [List.append_assoc]
    change j ∈ singleMindedGreedyAcceptedFromState bids ∅ (orderOf bids)
    rw [hsource.order_eq, hdecomp]
    rw [singleMindedGreedyAcceptedFromState_append]
    rw [← hsource.acceptedWithJ_eq]
    exact hj_state
  exact
    singleMindedGreedyAcceptedMechanism_finite_branch_of_nextDenied_some
      orderOf bids acceptedWithJ pre nextPost windowOrder hsource.hjaccepted
      hpairwise hjpre hnodup_original hnext_state hsource.window hjn
      hj_nonempty hj_final hnext_order

theorem singleMindedGreedyAcceptedMechanism_zero_branch_of_sorted_window
    [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (base : List Bidder) {j : Bidder}
    (windowOrder : ℝ → List Bidder)
    (hsource :
      SingleMindedFullOrderSortedEraseCriticalWindow orderOf bids acceptedWithJ j
        base windowOrder)
    (hnext_order :
      singleMindedGreedyNextDeniedFromOrder bids (orderOf bids) j = none) :
    let M := singleMindedGreedyAcceptedMechanismFromOrderOf orderOf
    (∀ v, 0 ≤ v → v < 0 →
      j ∉ M.accepted (singleMindedValueUpdate bids j v)) ∧
    (∀ v, 0 < v →
      j ∈ M.accepted (singleMindedValueUpdate bids j v)) ∧
    M.payment bids j = 0 := by
  classical
  have hnodup_order :
      (hsource.before ++ j :: base).Nodup := by
    simpa [hsource.order_eq] using hsource.order_nodup
  have hbefore : j ∉ hsource.before := by
    have hdisjoint := (List.nodup_append.mp hnodup_order).2.2
    intro hjbefore
    exact hdisjoint j hjbefore j (by simp) rfl
  have hnext_split :
      singleMindedGreedyNextDeniedFromSplit bids hsource.before base j =
        none := by
    have hnext_display :
        singleMindedGreedyNextDeniedFromOrder bids
          (hsource.before ++ j :: base) j = none := by
      simpa [hsource.order_eq] using hnext_order
    simpa [
      singleMindedGreedyNextDeniedFromOrder_eq_split
        bids hsource.before base j hbefore] using hnext_display
  have hnext_state :
      singleMindedGreedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ base j = none := by
    simpa [singleMindedGreedyNextDeniedFromSplit,
      hsource.acceptedWithJ_eq] using hnext_split
  have hpairwise : PairwiseDisjointDesired bids acceptedWithJ := by
    have hstate_pairwise :
        PairwiseDisjointDesired bids
          (singleMindedGreedyAcceptedFromState bids ∅ (hsource.before ++ [j])) :=
      singleMindedGreedyAcceptedFromState_pairwiseDisjoint
        bids ∅ (hsource.before ++ [j]) (pairwiseDisjointDesired_empty bids)
    simpa [hsource.acceptedWithJ_eq] using hstate_pairwise
  have hj_final :
      j ∈ singleMindedGreedyAcceptedFromOrder bids (orderOf bids) := by
    have hj_state :
        j ∈ singleMindedGreedyAcceptedFromState bids acceptedWithJ base :=
      singleMindedGreedyAcceptedFromState_contains_initial
        bids acceptedWithJ base hsource.hjaccepted
    have hdecomp :
        hsource.before ++ j :: base =
          (hsource.before ++ [j]) ++ base := by
      simp [List.append_assoc]
    change j ∈ singleMindedGreedyAcceptedFromState bids ∅ (orderOf bids)
    rw [hsource.order_eq, hdecomp]
    rw [singleMindedGreedyAcceptedFromState_append]
    rw [← hsource.acceptedWithJ_eq]
    exact hj_state
  exact
    singleMindedGreedyAcceptedMechanism_zero_branch_of_nextDenied_none
      orderOf bids acceptedWithJ base windowOrder hsource.hjaccepted
      hpairwise hnext_state hsource.window hj_final hnext_order

/--
Source-window data for the accepted-bid critical branch of the greedy payment
formula. It provides the full-order sorted-window package for whichever case
the `n(j)` search returns: a finite next-denied bid or no next-denied bid.
-/
structure SingleMindedCriticalBranchWindows [DecidableEq Bidder]
    [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) where
  finite :
    ∀ n,
      singleMindedGreedyNextDeniedFromOrder bids (orderOf bids) j = some n →
        Σ acceptedWithJ : Finset Bidder,
          Σ pre : List Bidder,
            Σ nextPost : List Bidder,
              Σ windowOrder : ℝ → List Bidder,
                SingleMindedFullOrderSortedEraseCriticalWindow orderOf bids
                  acceptedWithJ j (pre ++ n :: nextPost) windowOrder
  none :
    singleMindedGreedyNextDeniedFromOrder bids (orderOf bids) j = none →
      Σ acceptedWithJ : Finset Bidder,
        Σ base : List Bidder,
        Σ windowOrder : ℝ → List Bidder,
          SingleMindedFullOrderSortedEraseCriticalWindow orderOf bids
            acceptedWithJ j base windowOrder

noncomputable def singleMindedAverageCriticalBranchWindows_of_accepted
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) {j : Bidder}
    (hjacc :
      j ∈ singleMindedGreedyAcceptedFromOrder bids
        (singleMindedAverageOrderOf bids)) :
    SingleMindedCriticalBranchWindows
      (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))
      bids j := by
  classical
  have hsplit :
      ∃ before base,
        singleMindedAverageOrderOf bids = before ++ j :: base :=
    List.mem_iff_append.mp (singleMindedAverageOrderOf_mem bids j)
  let before : List Bidder := Classical.choose hsplit
  have hsplit_before :
      ∃ base,
        singleMindedAverageOrderOf bids = before ++ j :: base :=
    Classical.choose_spec hsplit
  let base : List Bidder := Classical.choose hsplit_before
  have horder :
      singleMindedAverageOrderOf bids = before ++ j :: base :=
    Classical.choose_spec hsplit_before
  have hnodup_split : (before ++ j :: base).Nodup := by
    simpa [horder] using singleMindedAverageOrderOf_nodup bids
  have hjbefore : j ∉ before := by
    have hdisjoint := (List.nodup_append.mp hnodup_split).2.2
    intro hj
    exact hdisjoint j hj j (by simp) rfl
  have hjbase : j ∉ base := by
    have htail : (j :: base).Nodup :=
      (List.nodup_append.mp hnodup_split).2.1
    exact (List.nodup_cons.mp htail).1
  let acceptedWithJ :=
    singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])
  have hjaccepted : j ∈ acceptedWithJ := by
    have hj_full :
        j ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ j :: base) := by
      simpa [singleMindedGreedyAcceptedFromOrder, horder] using hjacc
    have hdecomp :
        before ++ j :: base = (before ++ [j]) ++ base := by
      simp [List.append_assoc]
    have hj_full_decomp :
        j ∈ singleMindedGreedyAcceptedFromState bids ∅
          ((before ++ [j]) ++ base) := by
      simpa [← hdecomp] using hj_full
    have hj_tail :
        j ∈ singleMindedGreedyAcceptedFromState bids acceptedWithJ base := by
      rw [singleMindedGreedyAcceptedFromState_append] at hj_full_decomp
      simpa [acceptedWithJ] using hj_full_decomp
    have hsubset :=
      singleMindedGreedyAcceptedFromState_subset_initial_union_order
        bids acceptedWithJ base hj_tail
    rw [Finset.mem_union] at hsubset
    rcases hsubset with hjinitial | hjbase_finset
    · exact hjinitial
    · exact False.elim (hjbase (by simpa using hjbase_finset))
  refine
    { finite := ?_,
      none := ?_ }
  · intro n hnext
    have hnext_display :
        singleMindedGreedyNextDeniedFromOrder bids
          (before ++ j :: base) j = some n := by
      simpa [horder] using hnext
    have hnext_split :
        singleMindedGreedyFirstDeniedBecauseOfFromState
          bids acceptedWithJ base j = some n := by
      simpa [acceptedWithJ,
        singleMindedGreedyNextDeniedFromOrder_eq_split
          bids before base j hjbefore] using hnext_display
    have hnbase : n ∈ base :=
      (singleMindedGreedyFirstDeniedBecauseOfFromState_some_spec
        bids acceptedWithJ base j n hnext_split).1
    have hn_split : ∃ pre nextPost, base = pre ++ n :: nextPost :=
      List.mem_iff_append.mp hnbase
    let pre : List Bidder := Classical.choose hn_split
    have hn_split_pre : ∃ nextPost, base = pre ++ n :: nextPost :=
      Classical.choose_spec hn_split
    let nextPost : List Bidder := Classical.choose hn_split_pre
    have hbase : base = pre ++ n :: nextPost :=
      Classical.choose_spec hn_split_pre
    refine
      ⟨acceptedWithJ, pre, nextPost,
        singleMindedAverageValueUpdateWindow bids j (pre ++ n :: nextPost),
        ?_⟩
    have horder' :
        singleMindedAverageOrderOf bids =
          before ++ j :: (pre ++ n :: nextPost) := by
      rw [horder, hbase]
    exact
      singleMindedAverageValueUpdateWindow_fullOrderSortedEraseCriticalWindow_of_split_data
        bids horder' hjaccepted
  · intro _hnext
    exact
      ⟨acceptedWithJ, base, singleMindedAverageValueUpdateWindow bids j base,
        singleMindedAverageValueUpdateWindow_fullOrderSortedEraseCriticalWindow_of_split_data
          bids horder hjaccepted⟩

/--
Witness data showing that a finite threshold is represented by some source
critical branch after fixing bidder `i`'s desired bundle and varying only its
declared value.
-/
structure SingleMindedSomeThresholdBranch [DecidableEq Bidder]
    [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (reports : Bidder → SingleMindedBid Item)
    (i : Bidder) (s : Bundle Item) (p : ℝ) where
  branchBids : Bidder → SingleMindedBid Item
  value_update_eq :
    ∀ v,
      singleMindedValueUpdate branchBids i v =
        Function.update reports i { desired := s, value := v }
  branch_nonempty : (branchBids i).desired.Nonempty
  windows : SingleMindedCriticalBranchWindows orderOf branchBids i
  payment_eq :
    (singleMindedGreedyAcceptedMechanismFromOrderOf orderOf).payment
      branchBids i = p
  threshold_nonneg : 0 ≤ p

noncomputable def singleMindedSomeThresholdBranch_of_branch_windows
    [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (reports branchBids : Bidder → SingleMindedBid Item)
    (i : Bidder) (s : Bundle Item)
    (hbranch_profile :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile branchBids)
    (hvalue_update_eq :
      ∀ v,
        singleMindedValueUpdate branchBids i v =
          Function.update reports i { desired := s, value := v })
    (hwindows :
      SingleMindedCriticalBranchWindows orderOf branchBids i) :
    SingleMindedSomeThresholdBranch orderOf reports i s
      ((singleMindedGreedyAcceptedMechanismFromOrderOf orderOf).payment
        branchBids i) := by
  refine
    { branchBids := branchBids
      value_update_eq := hvalue_update_eq
      branch_nonempty := (hbranch_profile i).1
      windows := hwindows
      payment_eq := rfl
      threshold_nonneg := ?_ }
  simpa [singleMindedGreedyAcceptedMechanismFromOrderOf] using
    singleMindedGreedyPaymentFromOrder_nonneg_of_nonnegative
      branchBids (orderOf branchBids) i hbranch_profile

noncomputable def singleMindedAverageSomeThresholdBranch_of_accepted_update
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (reports : Bidder → SingleMindedBid Item)
    (hreports :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile reports)
    (i : Bidder) {s : Bundle Item} {branchValue : ℝ}
    (hs : s.Nonempty) (hbranchValue_nonneg : 0 ≤ branchValue)
    (hacc :
      i ∈ singleMindedGreedyAcceptedFromOrder
        (Function.update reports i { desired := s, value := branchValue })
        (singleMindedAverageOrderOf
          (Function.update reports i { desired := s, value := branchValue }))) :
    SingleMindedSomeThresholdBranch
      (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))
      reports i s
      ((singleMindedGreedyAcceptedMechanismFromOrderOf
        (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))).payment
          (Function.update reports i { desired := s, value := branchValue })
          i) := by
  classical
  let branchBids :=
    Function.update reports i { desired := s, value := branchValue }
  have hbranch_profile :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile branchBids := by
    simpa [branchBids] using
      SingleMindedAcceptedMechanism.nonnegativeNonemptyProfile_update
        reports hreports i hs hbranchValue_nonneg
  have hvalue_update_eq :
      ∀ v,
        singleMindedValueUpdate branchBids i v =
          Function.update reports i { desired := s, value := v } := by
    intro v
    simpa [branchBids] using
      singleMindedValueUpdate_update_desired_value
        reports i s branchValue v
  have hwindows :
      SingleMindedCriticalBranchWindows
        (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))
        branchBids i :=
    singleMindedAverageCriticalBranchWindows_of_accepted
      branchBids (by simpa [branchBids] using hacc)
  simpa [branchBids] using
    singleMindedSomeThresholdBranch_of_branch_windows
      (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))
      reports branchBids i s hbranch_profile hvalue_update_eq hwindows

noncomputable abbrev singleMindedAverageGreedyAcceptedMechanism
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder] :
    SingleMindedAcceptedMechanism Bidder Item :=
  singleMindedGreedyAcceptedMechanismFromOrderOf
    (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))

/--
The concrete average-density greedy accepted-set rule is monotone on the
nonempty nonnegative single-minded domain.
-/
theorem singleMindedAverageGreedyAcceptedMechanism_nonnegative_monotonicity
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder] :
    (singleMindedAverageGreedyAcceptedMechanism
      (Bidder := Bidder) (Item := Item)).MonotonicityOn
        SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  classical
  exact
    singleMindedGreedyAcceptedMechanismFromOrderOf_monotonicityOn_of_order_moves_earlier
      (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile
      (by
        intro bids hbids j s v _hacc hupdated hsub hle
        exact
          singleMindedAverageOrderOf_nonnegative_update_moves_earlier
            bids hbids hupdated hsub hle)

noncomputable def singleMindedAverageGreedyCriticalThreshold
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (reports : Bidder → SingleMindedBid Item) (i : Bidder)
    (s : Bundle Item) : Option ℝ := by
  classical
  let M := singleMindedAverageGreedyAcceptedMechanism
    (Bidder := Bidder) (Item := Item)
  exact
    if h :
        ∃ v, 0 ≤ v ∧
          i ∈ M.accepted
            (Function.update reports i { desired := s, value := v }) then
      some
        (M.payment
          (Function.update reports i
            { desired := s, value := Classical.choose h }) i)
    else
      none

theorem singleMindedAverageGreedyCriticalThreshold_none_denied
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (reports : Bidder → SingleMindedBid Item)
    (i : Bidder) (s : Bundle Item)
    (hthreshold :
      singleMindedAverageGreedyCriticalThreshold reports i s = none) :
    ∀ v, 0 ≤ v →
      i ∉ (singleMindedAverageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item)).accepted
          (Function.update reports i { desired := s, value := v }) := by
  intro v hv hacc
  have hex :
      ∃ v, 0 ≤ v ∧
        i ∈ (singleMindedAverageGreedyAcceptedMechanism
          (Bidder := Bidder) (Item := Item)).accepted
            (Function.update reports i { desired := s, value := v }) :=
    ⟨v, hv, hacc⟩
  have hsome :
      singleMindedAverageGreedyCriticalThreshold reports i s =
        some
          ((singleMindedAverageGreedyAcceptedMechanism
            (Bidder := Bidder) (Item := Item)).payment
              (Function.update reports i
                { desired := s, value := Classical.choose hex }) i) := by
    simp [singleMindedAverageGreedyCriticalThreshold, hex]
  rw [hthreshold] at hsome
  simp at hsome

noncomputable def singleMindedAverageGreedyCriticalThreshold_some_branch
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (reports : Bidder → SingleMindedBid Item)
    (hreports :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile reports)
    (i : Bidder) (s : Bundle Item) (p : ℝ)
    (hs : s.Nonempty)
    (hthreshold :
      singleMindedAverageGreedyCriticalThreshold reports i s = some p) :
    SingleMindedSomeThresholdBranch
      (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))
      reports i s p := by
  classical
  by_cases hex :
      ∃ v, 0 ≤ v ∧
        i ∈ (singleMindedAverageGreedyAcceptedMechanism
          (Bidder := Bidder) (Item := Item)).accepted
            (Function.update reports i { desired := s, value := v })
  · let branchValue : ℝ := Classical.choose hex
    have hbranchValue_nonneg : 0 ≤ branchValue :=
      (Classical.choose_spec hex).1
    have hacc :
        i ∈ (singleMindedAverageGreedyAcceptedMechanism
          (Bidder := Bidder) (Item := Item)).accepted
            (Function.update reports i
              { desired := s, value := branchValue }) :=
      (Classical.choose_spec hex).2
    have hthreshold_some :
        some
          ((singleMindedAverageGreedyAcceptedMechanism
            (Bidder := Bidder) (Item := Item)).payment
              (Function.update reports i
                { desired := s, value := branchValue }) i) =
            some p := by
      simpa [singleMindedAverageGreedyCriticalThreshold, hex, branchValue]
        using hthreshold
    have hp :
        (singleMindedAverageGreedyAcceptedMechanism
          (Bidder := Bidder) (Item := Item)).payment
            (Function.update reports i
              { desired := s, value := branchValue }) i = p := by
      exact Option.some.inj hthreshold_some
    have hbranch :=
      singleMindedAverageSomeThresholdBranch_of_accepted_update
        reports hreports i hs hbranchValue_nonneg (by
          simpa [singleMindedAverageGreedyAcceptedMechanism] using hacc)
    simpa [singleMindedAverageGreedyAcceptedMechanism, hp] using hbranch
  · have hnone :
        singleMindedAverageGreedyCriticalThreshold reports i s = none := by
      simp [singleMindedAverageGreedyCriticalThreshold, hex]
    rw [hnone] at hthreshold
    cases hthreshold

/--
Source-branch data sufficient to build the domain-aware critical-value
certificate for the source greedy accepted-set mechanism. This keeps the
concrete sorted-order construction outside the generic certificate proof.
-/
structure SingleMindedNonnegativeCriticalBranchData
    [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder) where
  threshold :
    (Bidder → SingleMindedBid Item) → Bidder → Bundle Item → Option ℝ
  threshold_own_value_independent :
    ∀ reports,
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile reports →
        ∀ i s v,
          s.Nonempty →
            0 ≤ v →
              threshold
                  (Function.update reports i { desired := s, value := v }) i s =
                threshold reports i s
  some_branch :
    ∀ reports,
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile reports →
        ∀ i s p,
          s.Nonempty →
            threshold reports i s = some p →
              SingleMindedSomeThresholdBranch orderOf reports i s p
  none_denied :
    ∀ reports,
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile reports →
        ∀ i s,
          s.Nonempty →
            threshold reports i s = none →
              ∀ v, 0 ≤ v →
                i ∉ (singleMindedGreedyAcceptedMechanismFromOrderOf orderOf).accepted
                  (Function.update reports i { desired := s, value := v })
  accepted_threshold :
    ∀ reports,
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile reports →
        ∀ i,
          i ∈ (singleMindedGreedyAcceptedMechanismFromOrderOf orderOf).accepted
            reports →
            threshold reports i (reports i).desired =
              match
                  singleMindedGreedyNextDeniedFromOrder
                    reports (orderOf reports) i with
              | none => some 0
              | some n =>
                  some
                    ((reports i).bundleSize *
                      (reports n).averageAmountPerGood)

/--
Accepted-bid criticality for the full greedy mechanism. Given source sorted
windows for the finite and no-next cases, the actual greedy payment is
the critical threshold for changing only the accepted bidder's value on the
nonnegative report domain.
-/
theorem singleMindedGreedyAcceptedMechanism_payment_critical_of_branch_windows
    [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item) {j : Bidder}
    (hwindows :
      SingleMindedCriticalBranchWindows orderOf bids j)
    (hj_nonempty : (bids j).desired.Nonempty) :
    let M := singleMindedGreedyAcceptedMechanismFromOrderOf orderOf
    (∀ v, 0 ≤ v → v < M.payment bids j →
      j ∉ M.accepted (singleMindedValueUpdate bids j v)) ∧
    (∀ v, M.payment bids j < v →
      j ∈ M.accepted (singleMindedValueUpdate bids j v)) := by
  classical
  let M := singleMindedGreedyAcceptedMechanismFromOrderOf orderOf
  constructor
  · intro v hv_nonneg hv_lt
    cases hnext :
        singleMindedGreedyNextDeniedFromOrder bids (orderOf bids) j with
    | none =>
        rcases hwindows.none hnext with
          ⟨acceptedWithJ, base, windowOrder, hsource⟩
        have hbranch :=
          singleMindedGreedyAcceptedMechanism_zero_branch_of_sorted_window
            orderOf bids acceptedWithJ base windowOrder hsource hnext
        have hpay : M.payment bids j = 0 := by
          simpa [M] using hbranch.2.2
        exact hbranch.1 v hv_nonneg (by simpa [M, hpay] using hv_lt)
    | some n =>
        rcases hwindows.finite n hnext with
          ⟨acceptedWithJ, pre, nextPost, windowOrder, hsource⟩
        have hbranch :=
          singleMindedGreedyAcceptedMechanism_finite_branch_of_sorted_window
            orderOf bids acceptedWithJ pre nextPost windowOrder hsource hnext
            hj_nonempty
        have hpay :
            M.payment bids j =
              (bids j).bundleSize * (bids n).averageAmountPerGood := by
          simpa [M] using hbranch.2.2
        exact hbranch.1 v (by simpa [M, hpay] using hv_lt)
  · intro v hv_gt
    cases hnext :
        singleMindedGreedyNextDeniedFromOrder bids (orderOf bids) j with
    | none =>
        rcases hwindows.none hnext with
          ⟨acceptedWithJ, base, windowOrder, hsource⟩
        have hbranch :=
          singleMindedGreedyAcceptedMechanism_zero_branch_of_sorted_window
            orderOf bids acceptedWithJ base windowOrder hsource hnext
        have hpay : M.payment bids j = 0 := by
          simpa [M] using hbranch.2.2
        exact hbranch.2.1 v (by simpa [M, hpay] using hv_gt)
    | some n =>
        rcases hwindows.finite n hnext with
          ⟨acceptedWithJ, pre, nextPost, windowOrder, hsource⟩
        have hbranch :=
          singleMindedGreedyAcceptedMechanism_finite_branch_of_sorted_window
            orderOf bids acceptedWithJ pre nextPost windowOrder hsource hnext
            hj_nonempty
        have hpay :
            M.payment bids j =
              (bids j).bundleSize * (bids n).averageAmountPerGood := by
          simpa [M] using hbranch.2.2
        exact hbranch.2.1 v (by simpa [M, hpay] using hv_gt)

theorem singleMindedAverageGreedyAcceptedMechanism_payment_critical_of_accepted
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) {j : Bidder}
    (hjacc :
      j ∈ singleMindedGreedyAcceptedFromOrder bids
        (singleMindedAverageOrderOf bids))
    (hj_nonempty : (bids j).desired.Nonempty) :
    let M := singleMindedAverageGreedyAcceptedMechanism
      (Bidder := Bidder) (Item := Item)
    (∀ v, 0 ≤ v → v < M.payment bids j →
      j ∉ M.accepted (singleMindedValueUpdate bids j v)) ∧
    (∀ v, M.payment bids j < v →
      j ∈ M.accepted (singleMindedValueUpdate bids j v)) := by
  exact
    singleMindedGreedyAcceptedMechanism_payment_critical_of_branch_windows
      (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))
      bids
      (singleMindedAverageCriticalBranchWindows_of_accepted bids hjacc)
      hj_nonempty

theorem singleMindedAverageGreedyPayment_eq_of_accepted_updates
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (reports : Bidder → SingleMindedBid Item)
    (hreports :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile reports)
    (i : Bidder) {s : Bundle Item} (hs : s.Nonempty)
    {v1 v2 : ℝ} (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2)
    (hacc1 :
      i ∈ (singleMindedAverageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item)).accepted
          (Function.update reports i { desired := s, value := v1 }))
    (hacc2 :
      i ∈ (singleMindedAverageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item)).accepted
          (Function.update reports i { desired := s, value := v2 })) :
    (singleMindedAverageGreedyAcceptedMechanism
      (Bidder := Bidder) (Item := Item)).payment
        (Function.update reports i { desired := s, value := v1 }) i =
      (singleMindedAverageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item)).payment
          (Function.update reports i { desired := s, value := v2 }) i := by
  classical
  let M := singleMindedAverageGreedyAcceptedMechanism
    (Bidder := Bidder) (Item := Item)
  let branch1 : Bidder → SingleMindedBid Item :=
    Function.update reports i { desired := s, value := v1 }
  let branch2 : Bidder → SingleMindedBid Item :=
    Function.update reports i { desired := s, value := v2 }
  have hprofile1 :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile branch1 := by
    simpa [branch1] using
      SingleMindedAcceptedMechanism.nonnegativeNonemptyProfile_update
        reports hreports i hs hv1
  have hprofile2 :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile branch2 := by
    simpa [branch2] using
      SingleMindedAcceptedMechanism.nonnegativeNonemptyProfile_update
        reports hreports i hs hv2
  have hacc1_order :
      i ∈ singleMindedGreedyAcceptedFromOrder branch1
        (singleMindedAverageOrderOf branch1) := by
    simpa [M, branch1, singleMindedAverageGreedyAcceptedMechanism,
      singleMindedGreedyAcceptedMechanismFromOrderOf] using hacc1
  have hacc2_order :
      i ∈ singleMindedGreedyAcceptedFromOrder branch2
        (singleMindedAverageOrderOf branch2) := by
    simpa [M, branch2, singleMindedAverageGreedyAcceptedMechanism,
      singleMindedGreedyAcceptedMechanismFromOrderOf] using hacc2
  have hcrit1 :=
    singleMindedAverageGreedyAcceptedMechanism_payment_critical_of_accepted
      branch1 hacc1_order (by simpa [branch1, Function.update] using hs)
  have hcrit2 :=
    singleMindedAverageGreedyAcceptedMechanism_payment_critical_of_accepted
      branch2 hacc2_order (by simpa [branch2, Function.update] using hs)
  let p1 : ℝ := M.payment branch1 i
  let p2 : ℝ := M.payment branch2 i
  have hp1_nonneg : 0 ≤ p1 := by
    simpa [p1, M, singleMindedAverageGreedyAcceptedMechanism,
      singleMindedGreedyAcceptedMechanismFromOrderOf] using
      singleMindedGreedyPaymentFromOrder_nonneg_of_nonnegative
        branch1 (singleMindedAverageOrderOf branch1) i hprofile1
  have hp2_nonneg : 0 ≤ p2 := by
    simpa [p2, M, singleMindedAverageGreedyAcceptedMechanism,
      singleMindedGreedyAcceptedMechanismFromOrderOf] using
      singleMindedGreedyPaymentFromOrder_nonneg_of_nonnegative
        branch2 (singleMindedAverageOrderOf branch2) i hprofile2
  have hvalue_update1 :
      ∀ x,
        singleMindedValueUpdate branch1 i x =
          Function.update reports i { desired := s, value := x } := by
    intro x
    simpa [branch1] using
      singleMindedValueUpdate_update_desired_value reports i s v1 x
  have hvalue_update2 :
      ∀ x,
        singleMindedValueUpdate branch2 i x =
          Function.update reports i { desired := s, value := x } := by
    intro x
    simpa [branch2] using
      singleMindedValueUpdate_update_desired_value reports i s v2 x
  by_contra hne
  rcases lt_or_gt_of_ne hne with hp1_lt_p2_raw | hp2_lt_p1_raw
  · have hp1_lt_p2 : p1 < p2 := by
      simpa [p1, p2, M, branch1, branch2] using hp1_lt_p2_raw
    let x : ℝ := (p1 + p2) / 2
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      nlinarith [hp1_nonneg, hp1_lt_p2]
    have hp1_lt_x : p1 < x := by
      dsimp [x]
      nlinarith [hp1_lt_p2]
    have hx_lt_p2 : x < p2 := by
      dsimp [x]
      nlinarith [hp1_lt_p2]
    have hacc_x :
        i ∈ M.accepted (singleMindedValueUpdate branch1 i x) :=
      hcrit1.2 x hp1_lt_x
    have hdeny_x :
        i ∉ M.accepted (singleMindedValueUpdate branch2 i x) :=
      hcrit2.1 x hx_nonneg hx_lt_p2
    exact hdeny_x (by
      simpa [hvalue_update1 x, hvalue_update2 x] using hacc_x)
  · have hp2_lt_p1 : p2 < p1 := by
      simpa [p1, p2, M, branch1, branch2] using hp2_lt_p1_raw
    let x : ℝ := (p1 + p2) / 2
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      nlinarith [hp2_nonneg, hp2_lt_p1]
    have hp2_lt_x : p2 < x := by
      dsimp [x]
      nlinarith [hp2_lt_p1]
    have hx_lt_p1 : x < p1 := by
      dsimp [x]
      nlinarith [hp2_lt_p1]
    have hacc_x :
        i ∈ M.accepted (singleMindedValueUpdate branch2 i x) :=
      hcrit2.2 x hp2_lt_x
    have hdeny_x :
        i ∉ M.accepted (singleMindedValueUpdate branch1 i x) :=
      hcrit1.1 x hx_nonneg hx_lt_p1
    exact hdeny_x (by
      simpa [hvalue_update1 x, hvalue_update2 x] using hacc_x)

theorem singleMindedAverageGreedyCriticalThreshold_own_value_independent
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (reports : Bidder → SingleMindedBid Item)
    (_hreports :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile reports)
    (i : Bidder) {s : Bundle Item} (_hs : s.Nonempty)
    {v : ℝ} (_hv : 0 ≤ v) :
    singleMindedAverageGreedyCriticalThreshold
        (Function.update reports i { desired := s, value := v }) i s =
      singleMindedAverageGreedyCriticalThreshold reports i s := by
  classical
  let M := singleMindedAverageGreedyAcceptedMechanism
    (Bidder := Bidder) (Item := Item)
  let Pleft : Prop :=
    ∃ w, 0 ≤ w ∧
      i ∈ M.accepted
        (Function.update
          (Function.update reports i { desired := s, value := v })
          i { desired := s, value := w })
  let Pright : Prop :=
    ∃ w, 0 ≤ w ∧
      i ∈ M.accepted
        (Function.update reports i { desired := s, value := w })
  have hiff : Pleft ↔ Pright := by
    constructor
    · rintro ⟨w, hw_nonneg, hwacc⟩
      refine ⟨w, hw_nonneg, ?_⟩
      simpa [Pleft, Pright, M,
        singleMindedUpdate_update_desired_value reports i s v w]
        using hwacc
    · rintro ⟨w, hw_nonneg, hwacc⟩
      refine ⟨w, hw_nonneg, ?_⟩
      simpa [Pleft, Pright, M,
        singleMindedUpdate_update_desired_value reports i s v w]
        using hwacc
  change
    (if h : Pleft then
      some
        (M.payment
          (Function.update
            (Function.update reports i { desired := s, value := v })
            i { desired := s, value := Classical.choose h }) i)
    else
      none) =
      if h : Pright then
        some
          (M.payment
            (Function.update reports i
              { desired := s, value := Classical.choose h }) i)
      else
        none
  by_cases hright : Pright
  · have hleft : Pleft := hiff.mpr hright
    simp [hleft, hright]
  · have hleft : ¬ Pleft := fun h => hright (hiff.mp h)
    simp [hleft, hright]

theorem singleMindedAverageGreedyCriticalThreshold_eq_payment_of_accepted
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (reports : Bidder → SingleMindedBid Item)
    (hreports :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile reports)
    {i : Bidder}
    (hacc :
      i ∈ (singleMindedAverageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item)).accepted reports) :
    singleMindedAverageGreedyCriticalThreshold reports i
        (reports i).desired =
      some
        ((singleMindedAverageGreedyAcceptedMechanism
          (Bidder := Bidder) (Item := Item)).payment reports i) := by
  classical
  let M := singleMindedAverageGreedyAcceptedMechanism
    (Bidder := Bidder) (Item := Item)
  let P : Prop :=
    ∃ v, 0 ≤ v ∧
      i ∈ M.accepted
        (Function.update reports i
          { desired := (reports i).desired, value := v })
  have hreports_self :
      Function.update reports i
        { desired := (reports i).desired, value := (reports i).value } =
          reports :=
    singleMindedUpdate_self_desired_value reports i
  have hP : P := by
    refine ⟨(reports i).value, (hreports i).2, ?_⟩
    simpa [P, M, hreports_self] using hacc
  have hchoose_nonneg : 0 ≤ Classical.choose hP :=
    (Classical.choose_spec hP).1
  have hchoose_acc :
      i ∈ M.accepted
        (Function.update reports i
          { desired := (reports i).desired, value := Classical.choose hP }) :=
    (Classical.choose_spec hP).2
  have hpay_eq :
      M.payment
          (Function.update reports i
            { desired := (reports i).desired, value := Classical.choose hP }) i =
        M.payment reports i := by
    simpa [hreports_self] using
      singleMindedAverageGreedyPayment_eq_of_accepted_updates
        reports hreports i (hreports i).1 hchoose_nonneg (hreports i).2
        (by simpa [M] using hchoose_acc)
        (by simpa [M, hreports_self] using hacc)
  change
    (if h : P then
      some
        (M.payment
          (Function.update reports i
            { desired := (reports i).desired, value := Classical.choose h }) i)
    else
      none) =
      some (M.payment reports i)
  simp [hP, hpay_eq]

theorem singleMindedAverageGreedyCriticalThreshold_accepted_threshold
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder]
    (reports : Bidder → SingleMindedBid Item)
    (hreports :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile reports)
    {i : Bidder}
    (hacc :
      i ∈ (singleMindedAverageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item)).accepted reports) :
    singleMindedAverageGreedyCriticalThreshold reports i
        (reports i).desired =
      match
        singleMindedGreedyNextDeniedFromOrder
          reports (singleMindedAverageOrderOf reports) i with
      | none => some 0
      | some n =>
          some
            ((reports i).bundleSize *
              (reports n).averageAmountPerGood) := by
  classical
  let M := singleMindedAverageGreedyAcceptedMechanism
    (Bidder := Bidder) (Item := Item)
  have hthreshold :
      singleMindedAverageGreedyCriticalThreshold reports i
          (reports i).desired =
        some (M.payment reports i) :=
    singleMindedAverageGreedyCriticalThreshold_eq_payment_of_accepted
      reports hreports hacc
  have hacc_order :
      i ∈ singleMindedGreedyAcceptedFromOrder reports
        (singleMindedAverageOrderOf reports) := by
    simpa [M, singleMindedAverageGreedyAcceptedMechanism,
      singleMindedGreedyAcceptedMechanismFromOrderOf] using hacc
  cases hnext :
      singleMindedGreedyNextDeniedFromOrder
        reports (singleMindedAverageOrderOf reports) i with
  | none =>
      have hpay :
          M.payment reports i = 0 := by
        simpa [M, singleMindedAverageGreedyAcceptedMechanism,
          singleMindedGreedyAcceptedMechanismFromOrderOf] using
          singleMindedGreedyPaymentFromOrder_eq_zero_of_no_next
            reports (singleMindedAverageOrderOf reports) hacc_order hnext
      simpa [hnext, hpay] using hthreshold
  | some n =>
      have hpay :
          M.payment reports i =
            (reports i).bundleSize * (reports n).averageAmountPerGood := by
        simpa [M, singleMindedAverageGreedyAcceptedMechanism,
          singleMindedGreedyAcceptedMechanismFromOrderOf] using
          singleMindedGreedyPaymentFromOrder_eq_of_next
            reports (singleMindedAverageOrderOf reports) hacc_order hnext
      simpa [hnext, hpay] using hthreshold

noncomputable def singleMindedAverageGreedyNonnegativeCriticalBranchData
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder] :
    SingleMindedNonnegativeCriticalBranchData
      (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item)) where
  threshold := singleMindedAverageGreedyCriticalThreshold
  threshold_own_value_independent := by
    intro reports hreports i s v hs hv
    exact
      singleMindedAverageGreedyCriticalThreshold_own_value_independent
        reports hreports i hs hv
  some_branch := by
    intro reports hreports i s p hs hthreshold
    exact
      singleMindedAverageGreedyCriticalThreshold_some_branch
        reports hreports i s p hs hthreshold
  none_denied := by
    intro reports _hreports i s _hs hthreshold v hv
    exact
      singleMindedAverageGreedyCriticalThreshold_none_denied
        reports i s hthreshold v hv
  accepted_threshold := by
    intro reports hreports i hacc
    exact
      singleMindedAverageGreedyCriticalThreshold_accepted_threshold
        reports hreports (by
          simpa [singleMindedAverageGreedyAcceptedMechanism] using hacc)

/--
Build the domain-aware critical-value certificate for the greedy
accepted-set mechanism from source branch data. Finite thresholds are discharged
by the accepted-bid payment-criticality theorem, while true infinite thresholds
are supplied explicitly by `none_denied`.
-/
noncomputable def singleMindedGreedyAcceptedMechanism_nonnegativeCriticalValueWithInfinityCertificate_of_branch_data
    [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (data :
      SingleMindedNonnegativeCriticalBranchData orderOf) :
    (singleMindedGreedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item)
      orderOf).NonnegativeCriticalValueWithInfinityCertificate := by
  classical
  let M := singleMindedGreedyAcceptedMechanismFromOrderOf orderOf
  refine
    { threshold := data.threshold
      threshold_nonneg := ?_
      threshold_own_value_independent := data.threshold_own_value_independent
      below_denied := ?_
      above_granted := ?_
      infinite_denied := ?_
      payment_eq_of_accepted := ?_ }
  · intro reports hreports i s p hs hthreshold
    exact
      (data.some_branch reports hreports i s p hs hthreshold).threshold_nonneg
  · intro reports hreports i s v p hs hv_nonneg hthreshold hv_lt
    let branch := data.some_branch reports hreports i s p hs hthreshold
    have hcritical :=
      singleMindedGreedyAcceptedMechanism_payment_critical_of_branch_windows
        orderOf branch.branchBids branch.windows branch.branch_nonempty
    have hdeny :
        i ∉ M.accepted (singleMindedValueUpdate branch.branchBids i v) :=
      hcritical.1 v hv_nonneg (by
        simpa [M, branch.payment_eq] using hv_lt)
    simpa [M, branch.value_update_eq v] using hdeny
  · intro reports hreports i s v p hs hv_nonneg hthreshold hp_lt
    let branch := data.some_branch reports hreports i s p hs hthreshold
    have hcritical :=
      singleMindedGreedyAcceptedMechanism_payment_critical_of_branch_windows
        orderOf branch.branchBids branch.windows branch.branch_nonempty
    have hacc :
        i ∈ M.accepted (singleMindedValueUpdate branch.branchBids i v) :=
      hcritical.2 v (by
        simpa [M, branch.payment_eq] using hp_lt)
    simpa [M, branch.value_update_eq v] using hacc
  · intro reports hreports i s v hs hv_nonneg hthreshold
    exact data.none_denied reports hreports i s hs hthreshold v hv_nonneg
  · intro reports hreports i hacc
    have haccepted_threshold :=
      data.accepted_threshold reports hreports i hacc
    have hacc_order :
        i ∈ singleMindedGreedyAcceptedFromOrder reports (orderOf reports) := by
      simpa [singleMindedGreedyAcceptedMechanismFromOrderOf] using hacc
    cases hnext :
        singleMindedGreedyNextDeniedFromOrder reports (orderOf reports) i with
    | none =>
        refine ⟨0, ?_, ?_⟩
        · simpa [hnext] using haccepted_threshold
        · have hpay :
              singleMindedGreedyPaymentFromOrder reports (orderOf reports) i =
                0 :=
            singleMindedGreedyPaymentFromOrder_eq_zero_of_no_next
              reports (orderOf reports) hacc_order hnext
          simpa [M, singleMindedGreedyAcceptedMechanismFromOrderOf] using hpay
    | some n =>
        refine
          ⟨(reports i).bundleSize * (reports n).averageAmountPerGood,
            ?_, ?_⟩
        · simpa [hnext] using haccepted_threshold
        · have hpay :
              singleMindedGreedyPaymentFromOrder reports (orderOf reports) i =
                (reports i).bundleSize *
                  (reports n).averageAmountPerGood :=
            singleMindedGreedyPaymentFromOrder_eq_of_next
              reports (orderOf reports) hacc_order hnext
          simpa [M, singleMindedGreedyAcceptedMechanismFromOrderOf] using hpay

/--
Truthfulness for the concrete average-density greedy accepted-set/payment
mechanism on the nonempty nonnegative single-minded domain.
-/
theorem singleMindedAverageGreedyAcceptedMechanism_truthfulOn_nonnegative
    [Fintype Bidder] [DecidableEq Item] [LinearOrder Bidder] :
    (singleMindedAverageGreedyAcceptedMechanism
      (Bidder := Bidder) (Item := Item)).TruthfulOn
        SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  classical
  exact
    SingleMindedAcceptedMechanism.truthfulOn_of_monotonicityOn_participation_nonnegative_infinity_critical
      (singleMindedAverageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item))
      (singleMindedAverageGreedyAcceptedMechanism_nonnegative_monotonicity
        (Bidder := Bidder) (Item := Item))
      (singleMindedGreedyAcceptedMechanismFromOrderOf_participation
        (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item)))
      (singleMindedGreedyAcceptedMechanism_nonnegativeCriticalValueWithInfinityCertificate_of_branch_data
        (singleMindedAverageOrderOf (Bidder := Bidder) (Item := Item))
        (singleMindedAverageGreedyNonnegativeCriticalBranchData
          (Bidder := Bidder) (Item := Item)))

theorem singleMindedGreedyAcceptedFromState_rejects_of_average_threshold_and_prefix_accept
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    (acceptedBefore : Finset Bidder) (order : List Bidder) {j n : Bidder}
    (hsorted : SingleMindedAverageAmountDescending bids order)
    (hnodup : order.Nodup)
    (hjorder : j ∈ order) (hnorder : n ∈ order)
    (hjn : j ≠ n)
    (hjaccepted : j ∉ acceptedBefore)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).value <
        (bids j).bundleSize * (bids n).averageAmountPerGood)
    (hprefix_accept :
      ∀ pre between tail,
        order = ((pre ++ [n]) ++ between) ++ j :: tail →
          n ∈ singleMindedGreedyAcceptedFromState bids acceptedBefore
            ((pre ++ [n]) ++ between))
    (hconflict : SingleMindedBidsConflict bids j n) :
    j ∉ singleMindedGreedyAcceptedFromState bids acceptedBefore order := by
  rcases hsorted.exists_split_of_value_lt_bundleSize_mul_average
      hjorder hnorder hjn hj_nonempty hlt with
    ⟨pre, between, tail, horder⟩
  have hnodup_split :
      (((pre ++ [n]) ++ between) ++ j :: tail).Nodup := by
    simpa [horder] using hnodup
  have hjpref : j ∉ (pre ++ [n]) ++ between := by
    intro hjmem
    have hdisjoint := (List.nodup_append.mp hnodup_split).2.2
    exact hdisjoint j hjmem j (by simp) rfl
  have hjtail : j ∉ tail := by
    have hright_nodup : (j :: tail).Nodup :=
      (List.nodup_append.mp hnodup_split).2.1
    exact (List.nodup_cons.mp hright_nodup).1
  rw [horder]
  exact
    singleMindedGreedyAcceptedFromState_rejects_after_prefix_conflict
      bids acceptedBefore ((pre ++ [n]) ++ between) tail
      (hprefix_accept pre between tail horder) hjaccepted hjpref hjtail
      hconflict

theorem singleMindedGreedyRejectedAtPosition_conflictingAccepted_nonempty
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (i : Bidder)
    (hnot_final :
      i ∉ singleMindedGreedyAcceptedFromOrder bids (pre ++ i :: suffix)) :
    (singleMindedGreedyConflictingAccepted bids
      (singleMindedGreedyAcceptedFromState bids ∅ pre) i).Nonempty := by
  classical
  let before : Finset Bidder :=
    singleMindedGreedyAcceptedFromState bids ∅ pre
  let afterStep : Finset Bidder := singleMindedGreedyStep bids before i
  have hfinal_eq :
      singleMindedGreedyAcceptedFromOrder bids (pre ++ i :: suffix) =
        singleMindedGreedyAcceptedFromState bids afterStep suffix := by
    simp [singleMindedGreedyAcceptedFromOrder,
      singleMindedGreedyAcceptedFromState, before, afterStep]
  by_contra hconflict
  have hi_step : i ∈ afterStep := by
    simpa [afterStep, singleMindedGreedyStep, before, hconflict] using
      (Finset.mem_insert_self i before)
  have hi_final : i ∈ singleMindedGreedyAcceptedFromState bids afterStep suffix :=
    singleMindedGreedyAcceptedFromState_contains_initial bids
      afterStep suffix hi_step
  exact hnot_final (by simpa [hfinal_eq] using hi_final)

/--
A bid that appears at a given position and is absent from the final greedy
accepted set has a conflicting bid from the already accepted prefix. That
prefix blocker remains accepted at the end and precedes the rejected bid.
-/
theorem singleMindedGreedyRejectedAtPosition_exists_final_preceding_blocker
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order pre suffix : List Bidder) (i : Bidder)
    (horder : order = pre ++ i :: suffix)
    (hnot_final : i ∉ singleMindedGreedyAcceptedFromOrder bids order) :
    ∃ j,
      j ∈ singleMindedGreedyAcceptedFromOrder bids order ∧
        SingleMindedPrecedes order j i ∧
          SingleMindedBidsConflict bids i j := by
  classical
  let before : Finset Bidder :=
    singleMindedGreedyAcceptedFromState bids ∅ pre
  have hnot_final' :
      i ∉ singleMindedGreedyAcceptedFromOrder bids (pre ++ i :: suffix) := by
    simpa [horder] using hnot_final
  have hconflict :=
    singleMindedGreedyRejectedAtPosition_conflictingAccepted_nonempty
      bids pre suffix i hnot_final'
  rcases hconflict with ⟨j, hjfilter⟩
  have hjbefore : j ∈ before := by
    have hjfilter' :
        j ∈ (singleMindedGreedyAcceptedFromState bids ∅ pre).filter
          (fun j => ((bids i).desired ∩ (bids j).desired).Nonempty) := by
      simpa [singleMindedGreedyConflictingAccepted] using hjfilter
    simpa [before] using (Finset.mem_filter.mp hjfilter').1
  have hjconflict : SingleMindedBidsConflict bids i j := by
    exact (Finset.mem_filter.mp (by
      simpa [before, singleMindedGreedyConflictingAccepted] using hjfilter)).2
  have hjfinal : j ∈ singleMindedGreedyAcceptedFromOrder bids order := by
    let afterStep : Finset Bidder := singleMindedGreedyStep bids before i
    have hfinal_eq :
        singleMindedGreedyAcceptedFromOrder bids order =
          singleMindedGreedyAcceptedFromState bids afterStep suffix := by
      simp [horder, singleMindedGreedyAcceptedFromOrder,
        singleMindedGreedyAcceptedFromState, before, afterStep]
    have hjstep : j ∈ afterStep :=
      singleMindedGreedyStep_contains_accepted bids before i hjbefore
    have hjend :
        j ∈ singleMindedGreedyAcceptedFromState bids afterStep suffix :=
      singleMindedGreedyAcceptedFromState_contains_initial bids
        afterStep suffix hjstep
    simpa [hfinal_eq] using hjend
  have hjpre : j ∈ pre := by
    have hjpre_finset :
        j ∈ pre.toFinset := by
      have hsubset :=
        singleMindedGreedyAcceptedFromState_subset_initial_union_order
          bids (∅ : Finset Bidder) pre hjbefore
      simpa [before] using hsubset
    simpa using (List.mem_toFinset.mp hjpre_finset)
  exact ⟨j, hjfinal,
    singleMindedPrecedes_append_cons_of_mem_prefix horder hjpre,
    hjconflict⟩

theorem singleMindedGreedyRejectedBid_exists_final_preceding_blocker
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (i : Bidder)
    (hi_order : i ∈ order)
    (hnot_final : i ∉ singleMindedGreedyAcceptedFromOrder bids order) :
    ∃ j,
      j ∈ singleMindedGreedyAcceptedFromOrder bids order ∧
        SingleMindedPrecedes order j i ∧
          SingleMindedBidsConflict bids i j := by
  rcases List.mem_iff_append.mp hi_order with ⟨pre, suffix, horder⟩
  exact singleMindedGreedyRejectedAtPosition_exists_final_preceding_blocker
    bids order pre suffix i horder hnot_final

theorem singleMindedGreedyRejectedBid_exists_order_blocker
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (i : Bidder)
    (hsorted : SingleMindedSqrtNormDescending bids order)
    (hi_order : i ∈ order)
    (hnot_final : i ∉ singleMindedGreedyAcceptedFromOrder bids order) :
    ∃ j, ∃ g,
      j ∈ singleMindedGreedyAcceptedFromOrder bids order ∧
        SingleMindedPrecedes order j i ∧
          g ∈ (bids i).desired ∧
            g ∈ (bids j).desired ∧
              (bids i).sqrtAmountNorm ≤ (bids j).sqrtAmountNorm := by
  rcases singleMindedGreedyRejectedBid_exists_final_preceding_blocker
      bids order i hi_order hnot_final with
    ⟨j, hjfinal, hprecedes, hconflict⟩
  rcases hconflict with ⟨g, hg⟩
  exact ⟨j, g, hjfinal, hprecedes,
    (Finset.mem_inter.mp hg).1,
    (Finset.mem_inter.mp hg).2,
    hsorted.norm_le_of_precedes hprecedes⟩

theorem singleMindedGreedyOptimalDisjoint_exists_order_blockers
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal : Finset Bidder) (order : List Bidder)
    (hsorted : SingleMindedSqrtNormDescending bids order)
    (hoptimal_order : ∀ i, i ∈ optimal → i ∈ order)
    (hoptimal_greedy_disjoint :
      Disjoint optimal (singleMindedGreedyAcceptedFromOrder bids order)) :
    ∀ i, i ∈ optimal →
      ∃ j, ∃ g,
        j ∈ singleMindedGreedyAcceptedFromOrder bids order ∧
          SingleMindedPrecedes order j i ∧
            g ∈ (bids i).desired ∧
              g ∈ (bids j).desired ∧
                (bids i).sqrtAmountNorm ≤ (bids j).sqrtAmountNorm := by
  intro i hi
  have hnot_final : i ∉ singleMindedGreedyAcceptedFromOrder bids order :=
    (Finset.disjoint_left.mp hoptimal_greedy_disjoint) hi
  exact singleMindedGreedyRejectedBid_exists_order_blocker
    bids order i hsorted (hoptimal_order i hi) hnot_final

/--
Blocking certificate for square-root greedy approximation. Each optimal bid is
assigned to a greedy bid that blocks it on a shared good and has at least as
large a squared square-root norm.
-/
structure SingleMindedGreedyBlockingCertificate [DecidableEq Bidder]
    [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder) where
  blocker : Bidder → Bidder
  blockedGood : Bidder → Item
  blocker_mem : ∀ i, i ∈ optimal → blocker i ∈ greedy
  good_mem_opt : ∀ i, i ∈ optimal → blockedGood i ∈ (bids i).desired
  good_mem_blocker :
    ∀ i, i ∈ optimal → blockedGood i ∈ (bids (blocker i)).desired
  normSq_le :
    ∀ i, i ∈ optimal →
      (bids i).value ^ 2 / (bids i).bundleSize ≤
        (bids (blocker i)).value ^ 2 / (bids (blocker i)).bundleSize

/--
Order-level blocking certificate. This keeps the proof obligation that the
blocking greedy bid appears earlier in the sorted list and has weakly larger
square-root norm.
-/
structure SingleMindedGreedyOrderBlockingCertificate [DecidableEq Bidder]
    [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (order : List Bidder) where
  blocker : Bidder → Bidder
  blockedGood : Bidder → Item
  blocker_mem : ∀ i, i ∈ optimal → blocker i ∈ greedy
  blocker_precedes :
    ∀ i, i ∈ optimal → SingleMindedPrecedes order (blocker i) i
  good_mem_opt : ∀ i, i ∈ optimal → blockedGood i ∈ (bids i).desired
  good_mem_blocker :
    ∀ i, i ∈ optimal → blockedGood i ∈ (bids (blocker i)).desired
  sqrtNorm_le :
    ∀ i, i ∈ optimal →
      (bids i).sqrtAmountNorm ≤ (bids (blocker i)).sqrtAmountNorm

noncomputable def singleMindedGreedyOrderBlockingCertificateOfDisjoint
    [DecidableEq Bidder] [DecidableEq Item]
    [Inhabited Bidder] [Inhabited Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal : Finset Bidder) (order : List Bidder)
    (hsorted : SingleMindedSqrtNormDescending bids order)
    (hoptimal_order : ∀ i, i ∈ optimal → i ∈ order)
    (hoptimal_greedy_disjoint :
      Disjoint optimal (singleMindedGreedyAcceptedFromOrder bids order)) :
    SingleMindedGreedyOrderBlockingCertificate bids optimal
      (singleMindedGreedyAcceptedFromOrder bids order) order := by
  classical
  let H :=
    singleMindedGreedyOptimalDisjoint_exists_order_blockers
      bids optimal order hsorted hoptimal_order hoptimal_greedy_disjoint
  let blocker : Bidder → Bidder := fun i =>
    if hi : i ∈ optimal then Classical.choose (H i hi) else default
  let blockedGood : Bidder → Item := fun i =>
    if hi : i ∈ optimal then
      Classical.choose (Classical.choose_spec (H i hi))
    else default
  refine
    { blocker := blocker
      blockedGood := blockedGood
      blocker_mem := ?_
      blocker_precedes := ?_
      good_mem_opt := ?_
      good_mem_blocker := ?_
      sqrtNorm_le := ?_ }
  · intro i hi
    have hspec := Classical.choose_spec (Classical.choose_spec (H i hi))
    simpa [blocker, hi] using hspec.1
  · intro i hi
    have hspec := Classical.choose_spec (Classical.choose_spec (H i hi))
    simpa [blocker, hi] using hspec.2.1
  · intro i hi
    have hspec := Classical.choose_spec (Classical.choose_spec (H i hi))
    simpa [blockedGood, hi] using hspec.2.2.1
  · intro i hi
    have hspec := Classical.choose_spec (Classical.choose_spec (H i hi))
    simpa [blocker, blockedGood, hi] using hspec.2.2.2.1
  · intro i hi
    have hspec := Classical.choose_spec (Classical.choose_spec (H i hi))
    simpa [blocker, hi] using hspec.2.2.2.2

/-- Convert the source-order blocking certificate to the algebraic form. -/
def SingleMindedGreedyOrderBlockingCertificate.toBlockingCertificate
    [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {optimal greedy : Finset Bidder} {order : List Bidder}
    (C : SingleMindedGreedyOrderBlockingCertificate bids optimal greedy order)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty : ∀ j, j ∈ greedy → (bids j).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value) :
    SingleMindedGreedyBlockingCertificate bids optimal greedy where
  blocker := C.blocker
  blockedGood := C.blockedGood
  blocker_mem := C.blocker_mem
  good_mem_opt := C.good_mem_opt
  good_mem_blocker := C.good_mem_blocker
  normSq_le := by
    intro i hi
    exact singleMinded_normSq_le_of_sqrtAmountNorm_le bids
      (hoptimal_nonempty i hi)
      (hgreedy_nonempty (C.blocker i) (C.blocker_mem i hi))
      (hoptimal_value_nonneg i hi)
      (C.sqrtNorm_le i hi)

/--
The blocking association implies the greedy blocking inequality. The proof
injects optimal bids into `(greedy bid, blocked good)` pairs. Pairwise
disjointness of the optimal bundles makes the map injective, while the nonempty
greedy bundles collapse the per-good charge for each greedy bid back to its
declared value squared.
-/
theorem singleMindedSqrtNormSqSum_le_sum_sq_of_blocking_certificate
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hgreedy_nonempty : ∀ j, j ∈ greedy → (bids j).desired.Nonempty)
    (C : SingleMindedGreedyBlockingCertificate bids optimal greedy) :
    singleMindedSqrtNormSqSum bids optimal ≤
      ∑ j ∈ greedy, (bids j).value ^ 2 := by
  classical
  let target : Finset ((j : Bidder) × Item) :=
    greedy.sigma fun j => (bids j).desired
  let φ : Bidder → ((j : Bidder) × Item) :=
    fun i => ⟨C.blocker i, C.blockedGood i⟩
  have htoTarget : ∀ i ∈ optimal, φ i ∈ target := by
    intro i hi
    simp [target, φ, C.blocker_mem i hi, C.good_mem_blocker i hi]
  have hinj : Set.InjOn φ (↑optimal : Set Bidder) := by
    intro i hi i' hi' hsame
    by_contra hne
    have hgood_eq : C.blockedGood i = C.blockedGood i' := by
      exact (by
        simpa [φ] using hsame :
          C.blocker i = C.blocker i' ∧
            C.blockedGood i = C.blockedGood i').2
    have hgood_i' : C.blockedGood i ∈ (bids i').desired := by
      simpa [hgood_eq] using C.good_mem_opt i' hi'
    exact (Finset.disjoint_left.mp (hoptimal_disjoint hi hi' hne))
      (C.good_mem_opt i hi) hgood_i'
  have htoSigma :
      singleMindedSqrtNormSqSum bids optimal ≤
        ∑ p ∈ target,
          (bids p.1).value ^ 2 / (bids p.1).bundleSize := by
    unfold singleMindedSqrtNormSqSum
    exact
      AppliedModelingLib.FiniteSum.finset_sum_le_sum_of_injOn_nonneg
        optimal target φ
        (fun i => (bids i).value ^ 2 / (bids i).bundleSize)
        (fun p => (bids p.1).value ^ 2 / (bids p.1).bundleSize)
        htoTarget hinj
        (by
          intro i hi
          exact C.normSq_le i hi)
        (by
          intro p hp
          have hp' : p.2 ∈ (bids p.1).desired := by
            exact (by simpa [target] using hp : p.1 ∈ greedy ∧
              p.2 ∈ (bids p.1).desired).2
          exact div_nonneg (sq_nonneg _)
            ((bids p.1).bundleSize_pos_of_nonempty ⟨p.2, hp'⟩).le)
  have hsigma :
      (∑ p ∈ target,
          (bids p.1).value ^ 2 / (bids p.1).bundleSize) =
        ∑ j ∈ greedy,
          ∑ _g ∈ (bids j).desired,
            (bids j).value ^ 2 / (bids j).bundleSize := by
    change
      (∑ p ∈ greedy.sigma (fun j => (bids j).desired),
          (bids p.1).value ^ 2 / (bids p.1).bundleSize) =
        ∑ j ∈ greedy,
          ∑ _g ∈ (bids j).desired,
            (bids j).value ^ 2 / (bids j).bundleSize
    rw [Finset.sum_sigma]
  have hcollapse :
      (∑ j ∈ greedy,
          ∑ _g ∈ (bids j).desired,
            (bids j).value ^ 2 / (bids j).bundleSize) ≤
        ∑ j ∈ greedy, (bids j).value ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hsize_pos : 0 < (bids j).bundleSize :=
      (bids j).bundleSize_pos_of_nonempty (hgreedy_nonempty j hj)
    calc
      ∑ _g ∈ (bids j).desired,
          (bids j).value ^ 2 / (bids j).bundleSize
          = (bids j).bundleSize *
              ((bids j).value ^ 2 / (bids j).bundleSize) := by
            simp [SingleMindedBid.bundleSize]
      _ = (bids j).value ^ 2 := by
            exact mul_div_cancel₀ ((bids j).value ^ 2) (ne_of_gt hsize_pos)
      _ ≤ (bids j).value ^ 2 := by
            rfl
  exact le_trans htoSigma (by simpa [hsigma] using hcollapse)

/--
Square-root greedy approximation, algebraic core in squared form. If the greedy
analysis gives the blocking inequality

`sum_{i in OP} a_i^2 / |s_i| <= sum_{j in GR} a_j^2`,

then the optimal value is at most `sqrt(k)` times the greedy value, equivalently
`OP^2 <= k * GR^2`. The theorem keeps the blocking step as an explicit
certificate field, so later work can focus just on the greedy ordering argument.
-/
theorem singleMinded_sqrt_greedy_approx_sq_of_blocking_bound
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (goods : Finset Item)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg : ∀ i, i ∈ greedy → 0 ≤ (bids i).value)
    (hblocking :
      singleMindedSqrtNormSqSum bids optimal ≤
        ∑ j ∈ greedy, (bids j).value ^ 2) :
    (singleMindedTotalValue bids optimal) ^ 2 ≤
      (goods.card : ℝ) * (singleMindedTotalValue bids greedy) ^ 2 := by
  classical
  by_cases hopt_empty : optimal = ∅
  · have hrhs_nonneg :
        0 ≤ (goods.card : ℝ) * (singleMindedTotalValue bids greedy) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    simpa [singleMindedTotalValue, hopt_empty] using hrhs_nonneg
  have hsize_pos :
      0 < singleMindedTotalBundleSize bids optimal := by
    have hnonempty_finset : optimal.Nonempty := by
      exact Finset.nonempty_iff_ne_empty.mpr hopt_empty
    unfold singleMindedTotalBundleSize
    refine Finset.sum_pos ?_ hnonempty_finset
    intro i hi
    exact (bids i).bundleSize_pos_of_nonempty (hoptimal_nonempty i hi)
  have hcs_div :
      (singleMindedTotalValue bids optimal) ^ 2 /
          singleMindedTotalBundleSize bids optimal ≤
        singleMindedSqrtNormSqSum bids optimal := by
    simpa [singleMindedTotalValue, singleMindedTotalBundleSize,
      singleMindedSqrtNormSqSum, SingleMindedBid.bundleSize] using
      (Finset.sq_sum_div_le_sum_sq_div
        (s := optimal) (f := fun i => (bids i).value)
        (g := fun i => ((bids i).desired.card : ℝ))
        (by
          intro i hi
          exact (bids i).bundleSize_pos_of_nonempty
            (hoptimal_nonempty i hi)))
  have hvalue_sq_le_norm_size :
      (singleMindedTotalValue bids optimal) ^ 2 ≤
        singleMindedSqrtNormSqSum bids optimal *
          singleMindedTotalBundleSize bids optimal := by
    exact (div_le_iff₀ hsize_pos).mp hcs_div
  have hsize_le :
      singleMindedTotalBundleSize bids optimal ≤ (goods.card : ℝ) :=
    singleMindedTotalBundleSize_le_goods_card_of_pairwiseDisjoint
      bids optimal goods hoptimal_goods hoptimal_disjoint
  have hsize_nonneg :
      0 ≤ singleMindedTotalBundleSize bids optimal :=
    le_of_lt hsize_pos
  have hgreedy_sq_nonneg :
      0 ≤ ∑ j ∈ greedy, (bids j).value ^ 2 := by
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hnorm_size_le :
      singleMindedSqrtNormSqSum bids optimal *
          singleMindedTotalBundleSize bids optimal ≤
        (∑ j ∈ greedy, (bids j).value ^ 2) * (goods.card : ℝ) := by
    exact mul_le_mul hblocking hsize_le hsize_nonneg hgreedy_sq_nonneg
  have hsum_sq_le :
      (∑ j ∈ greedy, (bids j).value ^ 2) ≤
        (singleMindedTotalValue bids greedy) ^ 2 := by
    simpa [singleMindedTotalValue] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := greedy) (f := fun j => (bids j).value)
        (fun j hj => hgreedy_value_nonneg j hj))
  have hgoods_nonneg : 0 ≤ (goods.card : ℝ) := by positivity
  have hgreedy_part :
      (∑ j ∈ greedy, (bids j).value ^ 2) * (goods.card : ℝ) ≤
        (singleMindedTotalValue bids greedy) ^ 2 * (goods.card : ℝ) :=
    mul_le_mul_of_nonneg_right hsum_sq_le hgoods_nonneg
  have hchain :
      (singleMindedTotalValue bids optimal) ^ 2 ≤
        (singleMindedTotalValue bids greedy) ^ 2 * (goods.card : ℝ) :=
    le_trans hvalue_sq_le_norm_size (le_trans hnorm_size_le hgreedy_part)
  nlinarith

/--
Square-root approximation form derived from the same blocking certificate.
-/
theorem singleMinded_sqrt_greedy_approx_of_blocking_bound
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (goods : Finset Item)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg : ∀ i, i ∈ greedy → 0 ≤ (bids i).value)
    (hblocking :
      singleMindedSqrtNormSqSum bids optimal ≤
        ∑ j ∈ greedy, (bids j).value ^ 2) :
    singleMindedTotalValue bids optimal ≤
      Real.sqrt (goods.card : ℝ) * singleMindedTotalValue bids greedy := by
  classical
  have hsq :=
    singleMinded_sqrt_greedy_approx_sq_of_blocking_bound
      bids optimal greedy goods hoptimal_goods hoptimal_disjoint
      hoptimal_nonempty hoptimal_value_nonneg hgreedy_value_nonneg hblocking
  have htarget_sq :
      (singleMindedTotalValue bids optimal) ^ 2 ≤
        (Real.sqrt (goods.card : ℝ) * singleMindedTotalValue bids greedy) ^ 2 := by
    have hgoods_nonneg : 0 ≤ (goods.card : ℝ) := by positivity
    rw [mul_pow, Real.sq_sqrt hgoods_nonneg]
    nlinarith
  exact le_of_sq_le_sq htarget_sq
    (mul_nonneg (Real.sqrt_nonneg _)
      (singleMindedTotalValue_nonneg bids greedy hgreedy_value_nonneg))

/--
Square-root approximation in certificate form. The remaining greedy-order proof
can focus on constructing `SingleMindedGreedyBlockingCertificate` from an
actual sorted greedy execution.
-/
theorem singleMinded_sqrt_greedy_approx_of_blocking_certificate
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (goods : Finset Item)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty : ∀ i, i ∈ greedy → (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg : ∀ i, i ∈ greedy → 0 ≤ (bids i).value)
    (C : SingleMindedGreedyBlockingCertificate bids optimal greedy) :
    singleMindedTotalValue bids optimal ≤
      Real.sqrt (goods.card : ℝ) * singleMindedTotalValue bids greedy := by
  exact singleMinded_sqrt_greedy_approx_of_blocking_bound
    bids optimal greedy goods hoptimal_goods hoptimal_disjoint
    hoptimal_nonempty hoptimal_value_nonneg hgreedy_value_nonneg
    (singleMindedSqrtNormSqSum_le_sum_sq_of_blocking_certificate
      bids optimal greedy hoptimal_disjoint hgreedy_nonempty C)

/--
Square-root approximation from an order-level blocking certificate: every
optimal bid has an earlier conflicting greedy blocker with weakly larger
square-root norm.
-/
theorem singleMinded_sqrt_greedy_approx_of_order_blocking_certificate
    [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (goods : Finset Item) (order : List Bidder)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty : ∀ i, i ∈ greedy → (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg : ∀ i, i ∈ greedy → 0 ≤ (bids i).value)
    (C :
      SingleMindedGreedyOrderBlockingCertificate
        bids optimal greedy order) :
    singleMindedTotalValue bids optimal ≤
      Real.sqrt (goods.card : ℝ) * singleMindedTotalValue bids greedy := by
  exact singleMinded_sqrt_greedy_approx_of_blocking_certificate
    bids optimal greedy goods hoptimal_goods hoptimal_disjoint
    hoptimal_nonempty hgreedy_nonempty hoptimal_value_nonneg
    hgreedy_value_nonneg
    (C.toBlockingCertificate hoptimal_nonempty hgreedy_nonempty
      hoptimal_value_nonneg)

/--
Disjoint-case square-root approximation for the explicit sorted greedy run,
after removing bids common to the greedy and optimal allocations.
-/
theorem singleMinded_sqrt_greedy_approx_of_sorted_order_disjoint
    [DecidableEq Bidder] [DecidableEq Item]
    [Inhabited Bidder] [Inhabited Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal : Finset Bidder) (goods : Finset Item) (order : List Bidder)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty :
      ∀ i, i ∈ singleMindedGreedyAcceptedFromOrder bids order →
        (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg :
      ∀ i, i ∈ singleMindedGreedyAcceptedFromOrder bids order →
        0 ≤ (bids i).value)
    (hsorted : SingleMindedSqrtNormDescending bids order)
    (hoptimal_order : ∀ i, i ∈ optimal → i ∈ order)
    (hoptimal_greedy_disjoint :
      Disjoint optimal (singleMindedGreedyAcceptedFromOrder bids order)) :
    singleMindedTotalValue bids optimal ≤
      Real.sqrt (goods.card : ℝ) *
        singleMindedTotalValue bids
          (singleMindedGreedyAcceptedFromOrder bids order) := by
  exact singleMinded_sqrt_greedy_approx_of_order_blocking_certificate
    bids optimal (singleMindedGreedyAcceptedFromOrder bids order)
    goods order hoptimal_goods hoptimal_disjoint hoptimal_nonempty
    hgreedy_nonempty hoptimal_value_nonneg hgreedy_value_nonneg
    (singleMindedGreedyOrderBlockingCertificateOfDisjoint
      bids optimal order hsorted hoptimal_order hoptimal_greedy_disjoint)

/--
Square-root approximation for the explicit sorted greedy run. This theorem
formalizes the common-bid removal step by filtering the order to bids disjoint
from the goods used by bids common to the optimal and greedy accepted sets,
applies the disjoint reduced theorem, and lifts the bound back to the original
sets.
-/
theorem singleMinded_sqrt_greedy_approx_of_sorted_order
    [DecidableEq Bidder] [DecidableEq Item]
    [Inhabited Bidder] [Inhabited Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal : Finset Bidder) (goods : Finset Item) (order : List Bidder)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty :
      ∀ i, i ∈ singleMindedGreedyAcceptedFromOrder bids order →
        (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg :
      ∀ i, i ∈ singleMindedGreedyAcceptedFromOrder bids order →
        0 ≤ (bids i).value)
    (hsorted : SingleMindedSqrtNormDescending bids order)
    (hoptimal_order : ∀ i, i ∈ optimal → i ∈ order) :
    singleMindedTotalValue bids optimal ≤
      Real.sqrt (goods.card : ℝ) *
        singleMindedTotalValue bids
          (singleMindedGreedyAcceptedFromOrder bids order) := by
  classical
  by_cases hgoods_zero : goods.card = 0
  · have hgoods_empty : goods = ∅ := Finset.card_eq_zero.mp hgoods_zero
    have hoptimal_empty : optimal = ∅ := by
      ext i
      constructor
      · intro hi
        rcases hoptimal_nonempty i hi with ⟨g, hg_desired⟩
        have hg_goods : g ∈ goods := hoptimal_goods i hi hg_desired
        simpa [hgoods_empty] using hg_goods
      · intro hi
        simpa using hi
    have hrhs_nonneg :
        0 ≤ Real.sqrt (goods.card : ℝ) *
          singleMindedTotalValue bids
            (singleMindedGreedyAcceptedFromOrder bids order) := by
      exact mul_nonneg (Real.sqrt_nonneg _)
        (singleMindedTotalValue_nonneg bids
          (singleMindedGreedyAcceptedFromOrder bids order)
          hgreedy_value_nonneg)
    simpa [singleMindedTotalValue, hoptimal_empty] using hrhs_nonneg
  have hfactor : 1 ≤ Real.sqrt (goods.card : ℝ) := by
    have hgoods_pos : 0 < goods.card := Nat.pos_of_ne_zero hgoods_zero
    have hone_le_goods : 1 ≤ goods.card := Nat.succ_le_of_lt hgoods_pos
    have hone_le_goods_real : (1 : ℝ) ≤ (goods.card : ℝ) := by
      exact_mod_cast hone_le_goods
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hone_le_goods_real
  let greedy := singleMindedGreedyAcceptedFromOrder bids order
  let common := optimal ∩ greedy
  let commonGoods := common.biUnion fun i => (bids i).desired
  let reducedOrder :=
    order.filter fun i => Disjoint (bids i).desired commonGoods
  have hcommon_subset : common ⊆ greedy := by
    intro i hi
    exact (Finset.mem_inter.mp hi).2
  have hcommon_nonempty :
      ∀ i, i ∈ common → (bids i).desired.Nonempty := by
    intro i hi
    exact hoptimal_nonempty i (Finset.mem_inter.mp hi).1
  have hreduced_common :
      singleMindedGreedyAcceptedFromOrder bids reducedOrder =
        greedy \ common := by
    simpa [reducedOrder, commonGoods, greedy, common] using
      singleMindedGreedyAcceptedFromOrder_filter_disjoint_commonGoods
        bids order common hcommon_subset hcommon_nonempty
  have hreduced_greedy :
      singleMindedGreedyAcceptedFromOrder bids reducedOrder =
        greedy \ optimal := by
    rw [hreduced_common]
    ext i
    constructor
    · intro hi
      rcases Finset.mem_sdiff.mp hi with ⟨higreedy, hincommon⟩
      exact Finset.mem_sdiff.mpr
        ⟨higreedy, fun hiopt =>
          hincommon (Finset.mem_inter.mpr ⟨hiopt, higreedy⟩)⟩
    · intro hi
      rcases Finset.mem_sdiff.mp hi with ⟨higreedy, hinopt⟩
      exact Finset.mem_sdiff.mpr
        ⟨higreedy, fun hicommon =>
          hinopt (Finset.mem_inter.mp hicommon).1⟩
  have hsorted_reduced :
      SingleMindedSqrtNormDescending bids reducedOrder := by
    dsimp [SingleMindedSqrtNormDescending, reducedOrder]
    exact
      List.Pairwise.sublist List.filter_sublist
        (by simpa [SingleMindedSqrtNormDescending] using hsorted)
  have hoptimal_order_reduced :
      ∀ i, i ∈ optimal \ greedy → i ∈ reducedOrder := by
    intro i hi
    rcases Finset.mem_sdiff.mp hi with ⟨hiopt, higreedy_not⟩
    have hiP : Disjoint (bids i).desired commonGoods := by
      rw [Finset.disjoint_left]
      intro g hgi hggoods
      rcases Finset.mem_biUnion.mp hggoods with ⟨j, hjcommon, hgj⟩
      have hjopt : j ∈ optimal := (Finset.mem_inter.mp hjcommon).1
      have hjgreedy : j ∈ greedy := (Finset.mem_inter.mp hjcommon).2
      have hij : i ≠ j := by
        intro hij
        subst i
        exact higreedy_not hjgreedy
      exact (Finset.disjoint_left.mp
        (hoptimal_disjoint hiopt hjopt hij)) hgi hgj
    exact List.mem_filter.mpr ⟨hoptimal_order i hiopt, by simpa [hiP]⟩
  have hoptimal_disjoint_reduced :
      PairwiseDisjointDesired bids (optimal \ greedy) := by
    intro i j hi hj hij
    exact hoptimal_disjoint
      (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij
  have hoptimal_nonempty_reduced :
      ∀ i, i ∈ optimal \ greedy → (bids i).desired.Nonempty := by
    intro i hi
    exact hoptimal_nonempty i (Finset.mem_sdiff.mp hi).1
  have hoptimal_value_nonneg_reduced :
      ∀ i, i ∈ optimal \ greedy → 0 ≤ (bids i).value := by
    intro i hi
    exact hoptimal_value_nonneg i (Finset.mem_sdiff.mp hi).1
  have hgreedy_nonempty_reduced :
      ∀ i, i ∈ singleMindedGreedyAcceptedFromOrder bids reducedOrder →
        (bids i).desired.Nonempty := by
    intro i hi
    have higreedy_sdiff : i ∈ greedy \ optimal := by
      simpa [hreduced_greedy] using hi
    exact hgreedy_nonempty i (Finset.mem_sdiff.mp higreedy_sdiff).1
  have hgreedy_value_nonneg_reduced :
      ∀ i, i ∈ singleMindedGreedyAcceptedFromOrder bids reducedOrder →
        0 ≤ (bids i).value := by
    intro i hi
    have higreedy_sdiff : i ∈ greedy \ optimal := by
      simpa [hreduced_greedy] using hi
    exact hgreedy_value_nonneg i (Finset.mem_sdiff.mp higreedy_sdiff).1
  have hoptimal_greedy_disjoint_reduced :
      Disjoint (optimal \ greedy)
        (singleMindedGreedyAcceptedFromOrder bids reducedOrder) := by
    rw [hreduced_greedy]
    rw [Finset.disjoint_left]
    intro i hiopt higr
    exact (Finset.mem_sdiff.mp hiopt).2 (Finset.mem_sdiff.mp higr).1
  have hreduced_bound :
      singleMindedTotalValue bids (optimal \ greedy) ≤
        Real.sqrt (goods.card : ℝ) *
          singleMindedTotalValue bids (greedy \ optimal) := by
    have hbound :=
      singleMinded_sqrt_greedy_approx_of_sorted_order_disjoint
        bids (optimal \ greedy) goods reducedOrder
        (fun i hi => hoptimal_goods i (Finset.mem_sdiff.mp hi).1)
        hoptimal_disjoint_reduced hoptimal_nonempty_reduced
        hgreedy_nonempty_reduced hoptimal_value_nonneg_reduced
        hgreedy_value_nonneg_reduced hsorted_reduced hoptimal_order_reduced
        hoptimal_greedy_disjoint_reduced
    simpa [hreduced_greedy] using hbound
  have hcommon_nonneg :
      ∀ i, i ∈ optimal ∩ greedy → 0 ≤ (bids i).value := by
    intro i hi
    exact hoptimal_value_nonneg i (Finset.mem_inter.mp hi).1
  exact
    singleMindedTotalValue_common_bid_removal_bridge
      bids optimal greedy (Real.sqrt (goods.card : ℝ))
      hfactor hcommon_nonneg hreduced_bound

end Auction
end AppliedModelingLib
