import AppliedModelingLib.SocialChoice.FairDivision.IndivisibleGoods
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

/-!
# Chore Allocation

Reusable definitions for finite allocations of indivisible chores with additive
costs. The allocation and feasibility representations are shared with the
indivisible-goods layer; fairness and efficiency inequalities are stated in the
cost direction.

The separation of a raw allocation from its feasibility predicate follows the
indivisible-allocation design in GameTheoryInLean's AppliedModelingLib,
`SocialChoice.FairDivision.Indivisible.Basic` (commit `cef01c7`).
The instance wrapper below adapts its
`SocialChoice.FairDivision.Indivisible.Instance` module at the same commit;
the fairness and efficiency predicates use the chore-specific cost direction.
-/

namespace AppliedModelingLib
namespace FairDivision

variable {Agent Item : Type*}

/-- Per-agent costs of individual chores. -/
abbrev ChoreCost (Agent Item : Type*) := Agent → Item → ℝ

/-- Multiply every individual chore cost by one common scalar.  Positive
rescaling preserves every additive EFX comparison and is the normalization
bridge from positive bi-valued costs `{p,q}` to `{1,q/p}`. -/
def rescaleChoreCost (scale : ℝ) (cost : ChoreCost Agent Item) : ChoreCost Agent Item :=
  fun agent item => scale * cost agent item

/-- Reindex a chore-cost profile along an equivalence of agent labels. -/
def relabelChoreCost {Agent' : Type*} (labels : Agent' ≃ Agent) (cost : ChoreCost Agent Item) :
    ChoreCost Agent' Item :=
  fun agent item => cost (labels agent) item

/-- Reindex an allocation along an equivalence of agent labels. -/
def relabelAllocation {Agent' : Type*} (labels : Agent' ≃ Agent) (allocation : Allocation Agent Item) :
    Allocation Agent' Item :=
  fun agent => allocation (labels agent)

/-- Reindex an agent-indexed cardinality quota along an equivalence of labels. -/
def relabelQuota {Agent' : Type*} (labels : Agent' ≃ Agent) (quota : Agent → ℕ) :
    Agent' → ℕ :=
  fun agent => quota (labels agent)

/-- Feasibility is invariant under a bijective relabelling of agents. -/
theorem IsAllocationOf.relabel [DecidableEq Item]
    {Agent' : Type*} (labels : Agent' ≃ Agent) (allocation : Allocation Agent Item)
    (goods : Finset Item)
    (halloc : IsAllocationOf allocation goods) :
    IsAllocationOf (relabelAllocation labels allocation) goods := by
  constructor
  · intro agent item hitem
    exact halloc.1 (labels agent) item hitem
  · intro item hitem
    obtain ⟨owner, howner, hunique⟩ := halloc.2 item hitem
    refine ⟨labels.symm owner, ?_, ?_⟩
    · simpa [relabelAllocation] using howner
    · intro agent hagent
      apply labels.injective
      simpa only [relabelAllocation, labels.apply_symm_apply] using
        hunique (labels agent) hagent

/-- The additive cost of a finite bundle of chores. -/
noncomputable def additiveChoreCost (cost : ChoreCost Agent Item)
    (agent : Agent) (bundle : Bundle Item) : ℝ :=
  bundle.sum fun item => cost agent item

/-- The additive cost of the empty chore bundle is zero. -/
theorem additiveChoreCost_empty (cost : ChoreCost Agent Item) (agent : Agent) :
    additiveChoreCost cost agent ∅ = 0 := by
  simp [additiveChoreCost]

/-- Additive costs commute with a common scalar rescaling. -/
theorem additiveChoreCost_rescale (scale : ℝ) (cost : ChoreCost Agent Item)
  (agent : Agent) (bundle : Bundle Item) :
    additiveChoreCost (rescaleChoreCost scale cost) agent bundle =
      scale * additiveChoreCost cost agent bundle := by
  simp [additiveChoreCost, rescaleChoreCost, ← Finset.mul_sum]

/-- Removing a chore from a bundle subtracts its individual additive cost. -/
theorem additiveChoreCost_erase [DecidableEq Item]
    (cost : ChoreCost Agent Item) (agent : Agent) (bundle : Bundle Item)
    (item : Item) (hitem : item ∈ bundle) :
    additiveChoreCost cost agent (bundle \ {item}) =
      additiveChoreCost cost agent bundle - cost agent item := by
  unfold additiveChoreCost
  simp only [Finset.sdiff_singleton_eq_erase]
  exact Finset.sum_erase_eq_sub hitem

/-- Additive chore costs are nonnegative when every individual chore cost is
nonnegative. -/
theorem additiveChoreCost_nonneg (cost : ChoreCost Agent Item)
    (hcost : ∀ agent item, 0 ≤ cost agent item) (agent : Agent)
    (bundle : Bundle Item) :
    0 ≤ additiveChoreCost cost agent bundle := by
  unfold additiveChoreCost
  exact Finset.sum_nonneg fun item _ => hcost agent item

/-- Additive chore cost is the sum of costs over disjoint bundles. -/
theorem additiveChoreCost_union [DecidableEq Item]
    (cost : ChoreCost Agent Item) (agent : Agent) (left right : Bundle Item)
    (hdisjoint : Disjoint left right) :
    additiveChoreCost cost agent (left ∪ right) =
      additiveChoreCost cost agent left + additiveChoreCost cost agent right := by
  unfold additiveChoreCost
  exact Finset.sum_union hdisjoint

/-- If every chore in a bundle has the same cost, its additive cost is the
cardinality of the bundle times that common cost. -/
theorem additiveChoreCost_eq_card_nsmul_of_constant
    (cost : ChoreCost Agent Item) (agent : Agent) (bundle : Bundle Item) (value : ℝ)
    (hconstant : ∀ item ∈ bundle, cost agent item = value) :
    additiveChoreCost cost agent bundle = bundle.card • value := by
  unfold additiveChoreCost
  calc
    ∑ item ∈ bundle, cost agent item = ∑ _item ∈ bundle, value :=
      Finset.sum_congr rfl hconstant
    _ = bundle.card • value := Finset.sum_const value

/-- If every chore in an owned bundle has the same cost, deleting any owned
chore leaves exactly one fewer copy of that cost. -/
theorem additiveChoreCost_erase_eq_card_sub_one_nsmul_of_constant [DecidableEq Item]
    (cost : ChoreCost Agent Item) (agent : Agent) (bundle : Bundle Item)
    (item : Item) (value : ℝ) (hitem : item ∈ bundle)
    (hconstant : ∀ chore ∈ bundle, cost agent chore = value) :
    additiveChoreCost cost agent (bundle \ {item}) = (bundle.card - 1) • value := by
  rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent (bundle \ {item}) value]
  · rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem]
  · intro chore hchore
    exact hconstant chore (Finset.sdiff_subset hchore)

/-- A pointwise lower bound on individual costs gives a cardinality lower bound
on additive chore cost. -/
theorem card_nsmul_le_additiveChoreCost_of_le
    (cost : ChoreCost Agent Item) (agent : Agent) (bundle : Bundle Item) (lower : ℝ)
    (hlower : ∀ item ∈ bundle, lower ≤ cost agent item) :
    bundle.card • lower ≤ additiveChoreCost cost agent bundle := by
  unfold additiveChoreCost
  calc
    bundle.card • lower = ∑ _item ∈ bundle, lower := (Finset.sum_const lower).symm
    _ ≤ ∑ item ∈ bundle, cost agent item := Finset.sum_le_sum hlower

/-- A pointwise upper bound on individual costs gives a cardinality upper bound
on additive chore cost. -/
theorem additiveChoreCost_le_card_nsmul_of_le
    (cost : ChoreCost Agent Item) (agent : Agent) (bundle : Bundle Item) (upper : ℝ)
    (hupper : ∀ item ∈ bundle, cost agent item ≤ upper) :
    additiveChoreCost cost agent bundle ≤ bundle.card • upper := by
  unfold additiveChoreCost
  calc
    ∑ item ∈ bundle, cost agent item ≤ ∑ _item ∈ bundle, upper :=
      Finset.sum_le_sum hupper
    _ = bundle.card • upper := Finset.sum_const upper

/-- Restricting a feasible allocation to a subpool remains feasible for the
intersection of the original pool with that subpool. -/
theorem IsAllocationOf.inter_right [DecidableEq Item]
    (allocation : Allocation Agent Item) (goods items : Finset Item)
    (halloc : IsAllocationOf allocation goods) :
    IsAllocationOf (fun agent => allocation agent ∩ items) (goods ∩ items) := by
  constructor
  · intro agent item hitem
    exact Finset.mem_inter.mpr
      ⟨halloc.1 agent item (Finset.mem_inter.mp hitem).1,
        (Finset.mem_inter.mp hitem).2⟩
  · intro item hitem
    obtain ⟨owner, howner, hunique⟩ := halloc.2 item (Finset.mem_inter.mp hitem).1
    refine ⟨owner, Finset.mem_inter.mpr ⟨howner, (Finset.mem_inter.mp hitem).2⟩, ?_⟩
    intro other hother
    exact hunique other (Finset.mem_inter.mp hother).1

/-- Distinct owners' bundles are disjoint in every feasible allocation.  This
is the direct finite-set form of the uniqueness clause in `IsAllocationOf`. -/
theorem IsAllocationOf.disjoint_of_ne [DecidableEq Item]
    (allocation : Allocation Agent Item) (goods : Finset Item)
    (halloc : IsAllocationOf allocation goods) {first second : Agent}
    (hne : first ≠ second) :
    Disjoint (allocation first) (allocation second) := by
  rw [Finset.disjoint_left]
  intro item hfirst hsecond
  exact hne (isAllocationOf_owner_unique halloc (halloc.1 first item hfirst) hfirst hsecond)

/-- In a feasible allocation, the restricted bundle cardinalities sum to the
cardinality of any designated subpool. -/
theorem sum_card_inter_allocation_eq_card_inter [Fintype Agent] [DecidableEq Item]
    (allocation : Allocation Agent Item) (goods items : Finset Item)
    (halloc : IsAllocationOf allocation goods) :
    Finset.univ.sum (fun agent => (allocation agent ∩ items).card) = (goods ∩ items).card := by
  exact sum_card_allocation_eq_card_of_isAllocation
    (fun agent => allocation agent ∩ items) (goods ∩ items)
    (IsAllocationOf.inter_right allocation goods items halloc)

/-- For any observer, her additive costs of the bundles in a feasible
allocation sum to her additive cost of the entire chore pool. -/
theorem sum_additiveChoreCost_allocation_eq_additiveChoreCost [Fintype Agent]
    [DecidableEq Item] (cost : ChoreCost Agent Item) (observer : Agent)
    (allocation : Allocation Agent Item) (goods : Finset Item)
    (halloc : IsAllocationOf allocation goods) :
    Finset.univ.sum (fun owner => additiveChoreCost cost observer (allocation owner)) =
      additiveChoreCost cost observer goods := by
  have hdisjoint : ((Finset.univ : Finset Agent) : Set Agent).PairwiseDisjoint allocation := by
    intro first _ second _ hne
    change Disjoint (allocation first) (allocation second)
    rw [Finset.disjoint_left]
    intro item hfirst hsecond
    apply hne
    exact isAllocationOf_owner_unique halloc
      (isAllocationOf_mem_goods halloc hfirst) hfirst hsecond
  have hunion : (Finset.univ : Finset Agent).biUnion allocation = goods := by
    ext item
    constructor
    · intro hitem
      obtain ⟨owner, _, howner⟩ := Finset.mem_biUnion.mp hitem
      exact isAllocationOf_mem_goods halloc howner
    · intro hitem
      obtain ⟨owner, howner⟩ := isAllocationOf_exists_owner halloc hitem
      exact Finset.mem_biUnion.mpr ⟨owner, Finset.mem_univ _, howner⟩
  unfold additiveChoreCost
  calc
    ∑ owner ∈ (Finset.univ : Finset Agent), ∑ item ∈ allocation owner, cost observer item =
        ∑ item ∈ (Finset.univ : Finset Agent).biUnion allocation, cost observer item :=
      (Finset.sum_biUnion hdisjoint).symm
    _ = ∑ item ∈ goods, cost observer item := by rw [hunion]

/-- The cost remaining after removing a cheapest item from a bundle, with value
zero for the empty bundle. -/
noncomputable def efxThreshold [DecidableEq Item]
    (cost : ChoreCost Agent Item) (agent : Agent) (bundle : Bundle Item) : ℝ := by
  classical
  by_cases h : bundle = ∅
  · exact 0
  · exact additiveChoreCost cost agent bundle - (bundle.image (cost agent)).min'
      (Finset.image_nonempty.mpr (Finset.nonempty_iff_ne_empty.mpr h))

/-- An allocation is envy-free for chores when each agent's own cost is no
greater than their cost for any other agent's bundle. -/
def EnvyFreeForChores (cost : Agent → Bundle Item → ℝ)
    (allocation : Allocation Agent Item) : Prop :=
  ∀ i j, cost i (allocation i) ≤ cost i (allocation j)

/-- Envy-freeness up to any item for chores: after removing any item from an
agent's own bundle, that agent incurs no more cost than for another bundle. -/
def EFXForChores [DecidableEq Item] (cost : Agent → Bundle Item → ℝ)
    (allocation : Allocation Agent Item) : Prop :=
  ∀ i j, allocation i = ∅ ∨
    ∀ item ∈ allocation i, cost i (allocation i \ {item}) ≤ cost i (allocation j)

/-- Positive rescaling preserves chore EFX. -/
theorem EFXForChores.rescale_of_pos [DecidableEq Item]
    (scale : ℝ) (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item)
    (hscale : 0 < scale)
    (hefx : EFXForChores (additiveChoreCost cost) allocation) :
    EFXForChores (additiveChoreCost (rescaleChoreCost scale cost)) allocation := by
  intro first second
  rcases hefx first second with hempty | hitems
  · exact Or.inl hempty
  · right
    intro item hitem
    rw [additiveChoreCost_rescale, additiveChoreCost_rescale]
    exact mul_le_mul_of_nonneg_left (hitems item hitem) hscale.le

/-- Chore EFX is equivalent before and after a positive common rescaling. -/
theorem efxForChores_rescale_iff_of_pos [DecidableEq Item]
    (scale : ℝ) (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item)
    (hscale : 0 < scale) :
    EFXForChores (additiveChoreCost (rescaleChoreCost scale cost)) allocation ↔
      EFXForChores (additiveChoreCost cost) allocation := by
  constructor
  · intro hefx first second
    rcases hefx first second with hempty | hitems
    · exact Or.inl hempty
    · right
      intro item hitem
      have hcomparison := hitems item hitem
      rw [additiveChoreCost_rescale, additiveChoreCost_rescale] at hcomparison
      exact le_of_mul_le_mul_left hcomparison hscale
  · exact EFXForChores.rescale_of_pos scale cost allocation hscale

/-- Chore EFX is invariant under a bijective relabelling of agents. -/
theorem EFXForChores.relabel [DecidableEq Item]
    {Agent' : Type*} (labels : Agent' ≃ Agent) (cost : ChoreCost Agent Item)
    (allocation : Allocation Agent Item)
    (hefx : EFXForChores (additiveChoreCost cost) allocation) :
    EFXForChores (additiveChoreCost (relabelChoreCost labels cost))
      (relabelAllocation labels allocation) := by
  intro i j
  rcases hefx (labels i) (labels j) with hempty | hitems
  · exact Or.inl hempty
  · right
    intro item hitem
    exact hitems item hitem

/-- In an additive chore allocation, the EFX comparison obtained by removing
a chore of cost one is exactly the unit-slack certificate used in bi-valued
arguments. -/
theorem EFXForChores.additive_sub_one_le_of_small [DecidableEq Item]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (first second : Agent) (item : Item) (hitem : item ∈ allocation first)
    (hsmall : cost first item = 1) :
    additiveChoreCost cost first (allocation first) - 1 ≤
      additiveChoreCost cost first (allocation second) := by
  rcases hefx first second with hempty | hitems
  · rw [hempty] at hitem
    simp at hitem
  · have hcomparison := hitems item hitem
    rw [additiveChoreCost_erase cost first (allocation first) item hitem, hsmall] at hcomparison
    exact hcomparison

/-- An EFX allocation for a relabelled instance transports back to an EFX
allocation for the original instance. -/
theorem exists_efx_relabel_back [DecidableEq Item]
    {Agent' : Type*} (labels : Agent' ≃ Agent) (cost : ChoreCost Agent Item)
    (goods : Finset Item)
    (h : ∃ allocation : Allocation Agent' Item,
      IsAllocationOf allocation goods ∧
        EFXForChores (additiveChoreCost (relabelChoreCost labels cost)) allocation) :
    ∃ allocation : Allocation Agent Item,
      IsAllocationOf allocation goods ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨allocation, halloc, hefx⟩ := h
  refine ⟨relabelAllocation labels.symm allocation, halloc.relabel labels.symm, ?_⟩
  have hefx' := hefx.relabel labels.symm
  have hcostEq : relabelChoreCost labels.symm (relabelChoreCost labels cost) = cost := by
    funext agent item
    simp [relabelChoreCost]
  rw [hcostEq] at hefx'
  exact hefx'

/-- Agent `i` does not strongly envy agent `j` when the chore-EFX condition
holds for this ordered pair. -/
def DoesNotStronglyEnvyForChores [DecidableEq Item]
    (cost : Agent → Bundle Item → ℝ) (allocation : Allocation Agent Item)
    (i j : Agent) : Prop :=
  allocation i = ∅ ∨
    ∀ item ∈ allocation i, cost i (allocation i \ {item}) ≤ cost i (allocation j)

/-- Chore EFX is the absence of strong envy in every ordered pair. -/
theorem efxForChores_iff_forall_doesNotStronglyEnvy [DecidableEq Item]
    (cost : Agent → Bundle Item → ℝ) (allocation : Allocation Agent Item) :
    EFXForChores cost allocation ↔
      ∀ i j, DoesNotStronglyEnvyForChores cost allocation i j :=
  Iff.rfl

/-- With nonnegative individual chore costs, no agent strongly envies her own
bundle: deleting one chore can only weakly reduce its cost. -/
theorem doesNotStronglyEnvyForChores_self_of_nonneg [DecidableEq Item]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item) (agent : Agent)
    (hnonneg : ∀ item, 0 ≤ cost agent item) :
    DoesNotStronglyEnvyForChores (additiveChoreCost cost) allocation agent agent := by
  by_cases hempty : allocation agent = ∅
  · exact Or.inl hempty
  · right
    intro item hitem
    rw [additiveChoreCost_erase cost agent (allocation agent) item hitem]
    linarith [hnonneg item]

/-- For nonnegative additive chore costs, the item-removal definition of EFX
is equivalent to the threshold formulation used by He and Tao. -/
theorem efxForChores_iff_threshold_le [DecidableEq Item]
    (cost : ChoreCost Agent Item) (hcost : ∀ agent item, 0 ≤ cost agent item)
    (allocation : Allocation Agent Item) :
    EFXForChores (additiveChoreCost cost) allocation ↔
      ∀ i j, efxThreshold cost i (allocation i) ≤
        additiveChoreCost cost i (allocation j) := by
  constructor
  · intro hefx i j
    by_cases hi : allocation i = ∅
    · simp only [efxThreshold, hi]
      exact additiveChoreCost_nonneg cost hcost i (allocation j)
    · have hitems := (hefx i j).resolve_left hi
      let costs := (allocation i).image (cost i)
      have hcosts : costs.Nonempty :=
        Finset.image_nonempty.mpr (Finset.nonempty_iff_ne_empty.mpr hi)
      obtain ⟨item, hitem, hmin⟩ := Finset.mem_image.mp (Finset.min'_mem costs hcosts)
      simp only [efxThreshold, dif_neg hi]
      rw [← hmin, ← additiveChoreCost_erase cost i (allocation i) item hitem]
      exact hitems item hitem
  · intro h i j
    by_cases hi : allocation i = ∅
    · exact Or.inl hi
    · right
      intro item hitem
      have hthreshold := h i j
      have hmin : ((allocation i).image (cost i)).min'
          (Finset.image_nonempty.mpr (Finset.nonempty_iff_ne_empty.mpr hi)) ≤
          cost i item := by
        apply Finset.min'_le
        exact Finset.mem_image.mpr ⟨item, hitem, rfl⟩
      simp only [efxThreshold, dif_neg hi] at hthreshold
      rw [additiveChoreCost_erase cost i (allocation i) item hitem]
      linarith

/-- In a nonempty EFX bundle, the observer's excess cost over any comparison
bundle is bounded by the cost of a cheapest owned chore.  This is the
cost-gap form of the EFX threshold characterization. -/
theorem EFXForChores.additive_sub_le_min_cost [DecidableEq Item]
    (cost : ChoreCost Agent Item) (hcost : ∀ agent item, 0 ≤ cost agent item)
    (allocation : Allocation Agent Item)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (own comparison : Agent) (hnonempty : (allocation own).Nonempty) :
    additiveChoreCost cost own (allocation own) -
        additiveChoreCost cost own (allocation comparison) ≤
      ((allocation own).image (cost own)).min'
        (Finset.image_nonempty.mpr hnonempty) := by
  have hthreshold := (efxForChores_iff_threshold_le cost hcost allocation).mp hefx
    own comparison
  have hne : allocation own ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hnonempty
  simp only [efxThreshold, dif_neg hne] at hthreshold
  linarith

/-- The source composition inequality ensures that an agent does not strongly
envy a comparison bundle after two disjoint partial allocations are united. -/
theorem doesNotStronglyEnvyForChores_union_of_cost_gap [DecidableEq Item]
    (cost : ChoreCost Agent Item) (leftAllocation rightAllocation : Allocation Agent Item)
    (hdisjoint : ∀ agent, Disjoint (leftAllocation agent) (rightAllocation agent))
    (i j : Agent)
    (hnonempty : (leftAllocation i ∪ rightAllocation i).Nonempty)
    (hgap :
      additiveChoreCost cost i (leftAllocation i) - additiveChoreCost cost i (leftAllocation j) ≤
        additiveChoreCost cost i (rightAllocation j) -
          additiveChoreCost cost i (rightAllocation i) +
          ((leftAllocation i ∪ rightAllocation i).image (cost i)).min'
            (Finset.image_nonempty.mpr hnonempty)) :
    DoesNotStronglyEnvyForChores (additiveChoreCost cost)
      (fun agent => leftAllocation agent ∪ rightAllocation agent) i j := by
  right
  intro item hitem
  have hmin : ((leftAllocation i ∪ rightAllocation i).image (cost i)).min'
      (Finset.image_nonempty.mpr hnonempty) ≤ cost i item := by
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨item, hitem, rfl⟩
  rw [additiveChoreCost_erase cost i (leftAllocation i ∪ rightAllocation i) item hitem]
  rw [additiveChoreCost_union cost i (leftAllocation i) (rightAllocation i) (hdisjoint i)]
  rw [additiveChoreCost_union cost i (leftAllocation j) (rightAllocation j) (hdisjoint j)]
  linarith

/-- The source composition inequality ensures chore EFX for the union of two
partial allocations. Empty own bundles satisfy EFX automatically. -/
theorem efxForChores_union_of_cost_gap [DecidableEq Item]
    (cost : ChoreCost Agent Item) (leftAllocation rightAllocation : Allocation Agent Item)
    (hdisjoint : ∀ agent, Disjoint (leftAllocation agent) (rightAllocation agent))
    (hgap : ∀ i j (hnonempty : (leftAllocation i ∪ rightAllocation i).Nonempty),
      additiveChoreCost cost i (leftAllocation i) - additiveChoreCost cost i (leftAllocation j) ≤
        additiveChoreCost cost i (rightAllocation j) -
          additiveChoreCost cost i (rightAllocation i) +
          ((leftAllocation i ∪ rightAllocation i).image (cost i)).min'
            (Finset.image_nonempty.mpr hnonempty)) :
    EFXForChores (additiveChoreCost cost)
      (fun agent => leftAllocation agent ∪ rightAllocation agent) := by
  rw [efxForChores_iff_forall_doesNotStronglyEnvy]
  intro i j
  by_cases hnonempty : (leftAllocation i ∪ rightAllocation i).Nonempty
  · exact doesNotStronglyEnvyForChores_union_of_cost_gap cost leftAllocation rightAllocation
      hdisjoint i j
      hnonempty (hgap i j hnonempty)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hnonempty)

/-- The first composition criterion from He and Tao: an envy-free prefix and
a suffix with one unit of EFX slack combine to an EFX allocation when every
chore costs at least one. -/
theorem efxForChores_union_of_envyFree_of_unit_slack [DecidableEq Item]
    (cost : ChoreCost Agent Item) (leftAllocation rightAllocation : Allocation Agent Item)
    (hdisjoint : ∀ agent, Disjoint (leftAllocation agent) (rightAllocation agent))
    (hcostLower : ∀ agent item, 1 ≤ cost agent item)
    (hleft : EnvyFreeForChores (additiveChoreCost cost) leftAllocation)
    (hright : ∀ i j,
      additiveChoreCost cost i (rightAllocation i) - 1 ≤
        additiveChoreCost cost i (rightAllocation j)) :
    EFXForChores (additiveChoreCost cost)
      (fun agent => leftAllocation agent ∪ rightAllocation agent) := by
  apply efxForChores_union_of_cost_gap cost leftAllocation rightAllocation hdisjoint
  intro i j hnonempty
  have hminimum : 1 ≤ ((leftAllocation i ∪ rightAllocation i).image (cost i)).min'
      (Finset.image_nonempty.mpr hnonempty) := by
    apply Finset.le_min'
    intro value hvalue
    obtain ⟨item, _, hitem⟩ := Finset.mem_image.mp hvalue
    rw [← hitem]
    exact hcostLower i item
  linarith [hleft i j, hright i j]

/-- A variant of the unit-slack composition criterion with one distinguished
agent.  That agent may have one unit of left-hand slack rather than an
envy-free left bundle, provided their right-hand bundle is no more costly than
any comparison bundle.  This is the residual-favorite branch of the
gap-filling composition used for bi-valued chores. -/
theorem efxForChores_union_of_special_unit_slack_and_favorite [DecidableEq Item]
    (cost : ChoreCost Agent Item) (leftAllocation rightAllocation : Allocation Agent Item)
    (special : Agent)
    (hdisjoint : ∀ agent, Disjoint (leftAllocation agent) (rightAllocation agent))
    (hcostLower : ∀ agent item, 1 ≤ cost agent item)
    (hleftSpecial : ∀ other,
      additiveChoreCost cost special (leftAllocation special) - 1 ≤
        additiveChoreCost cost special (leftAllocation other))
    (hleftOther : ∀ agent, agent ≠ special → ∀ other,
      additiveChoreCost cost agent (leftAllocation agent) ≤
        additiveChoreCost cost agent (leftAllocation other))
    (hrightUnit : ∀ agent other,
      additiveChoreCost cost agent (rightAllocation agent) - 1 ≤
        additiveChoreCost cost agent (rightAllocation other))
    (hrightFavorite : ∀ other,
      additiveChoreCost cost special (rightAllocation special) ≤
        additiveChoreCost cost special (rightAllocation other)) :
    EFXForChores (additiveChoreCost cost)
      (fun agent => leftAllocation agent ∪ rightAllocation agent) := by
  apply efxForChores_union_of_cost_gap cost leftAllocation rightAllocation hdisjoint
  intro agent other hnonempty
  have hminimum : 1 ≤ ((leftAllocation agent ∪ rightAllocation agent).image (cost agent)).min'
      (Finset.image_nonempty.mpr hnonempty) := by
    apply Finset.le_min'
    intro value hvalue
    obtain ⟨item, _, hitem⟩ := Finset.mem_image.mp hvalue
    rw [← hitem]
    exact hcostLower agent item
  by_cases hspecial : agent = special
  · subst agent
    linarith [hleftSpecial other, hrightFavorite other]
  · linarith [hleftOther agent hspecial other, hrightUnit agent other]

/-- A complementary composition criterion for a distinguished short bundle.
The left allocation is envy-free from the short agent's perspective and among
the other agents; each other left bundle may exceed the short bundle by one.
If the right allocation has unit EFX slack and the short right bundle is no
more costly than any other right bundle for every non-short observer, the
union is chore EFX. -/
theorem efxForChores_union_of_short_unit_slack_and_right_dominance [DecidableEq Item]
    (cost : ChoreCost Agent Item) (leftAllocation rightAllocation : Allocation Agent Item)
    (short : Agent)
    (hdisjoint : ∀ agent, Disjoint (leftAllocation agent) (rightAllocation agent))
    (hcostLower : ∀ agent item, 1 ≤ cost agent item)
    (hleftShort : ∀ other,
      additiveChoreCost cost short (leftAllocation short) ≤
        additiveChoreCost cost short (leftAllocation other))
    (hleftOther : ∀ agent, agent ≠ short → ∀ other, other ≠ short →
      additiveChoreCost cost agent (leftAllocation agent) ≤
        additiveChoreCost cost agent (leftAllocation other))
    (hleftToShort : ∀ agent, agent ≠ short →
      additiveChoreCost cost agent (leftAllocation agent) ≤
        additiveChoreCost cost agent (leftAllocation short) + 1)
    (hrightUnit : ∀ agent other,
      additiveChoreCost cost agent (rightAllocation agent) - 1 ≤
        additiveChoreCost cost agent (rightAllocation other))
    (hrightShortDominates : ∀ agent, agent ≠ short →
      additiveChoreCost cost agent (rightAllocation agent) ≤
        additiveChoreCost cost agent (rightAllocation short)) :
    EFXForChores (additiveChoreCost cost)
      (fun agent => leftAllocation agent ∪ rightAllocation agent) := by
  apply efxForChores_union_of_cost_gap cost leftAllocation rightAllocation hdisjoint
  intro agent other hnonempty
  have hminimum : 1 ≤ ((leftAllocation agent ∪ rightAllocation agent).image (cost agent)).min'
      (Finset.image_nonempty.mpr hnonempty) := by
    apply Finset.le_min'
    intro value hvalue
    obtain ⟨item, _, hvalueEq⟩ := Finset.mem_image.mp hvalue
    rw [← hvalueEq]
    exact hcostLower agent item
  by_cases hagent : agent = short
  · subst agent
    linarith [hleftShort other, hrightUnit short other]
  · by_cases hother : other = short
    · subst other
      linarith [hleftToShort agent hagent, hrightShortDominates agent hagent]
    · linarith [hleftOther agent hagent other hother, hrightUnit agent other]

/-- A short-bundle variant of the preceding composition criterion.  The left
short bundle may itself use one-unit EFX slack, provided the same short agent
is a favorite in the right allocation.  This is the exact concatenation
pattern after the two-item gap fill in He--Tao Case B.4.2(a). -/
theorem efxForChores_union_of_short_unit_slack_and_right_favorite [DecidableEq Item]
    (cost : ChoreCost Agent Item) (leftAllocation rightAllocation : Allocation Agent Item)
    (short : Agent)
    (hdisjoint : ∀ agent, Disjoint (leftAllocation agent) (rightAllocation agent))
    (hcostLower : ∀ agent item, 1 ≤ cost agent item)
    (hleftShort : ∀ other,
      additiveChoreCost cost short (leftAllocation short) - 1 ≤
        additiveChoreCost cost short (leftAllocation other))
    (hleftOther : ∀ agent, agent ≠ short → ∀ other, other ≠ short →
      additiveChoreCost cost agent (leftAllocation agent) ≤
        additiveChoreCost cost agent (leftAllocation other))
    (hleftToShort : ∀ agent, agent ≠ short →
      additiveChoreCost cost agent (leftAllocation agent) ≤
        additiveChoreCost cost agent (leftAllocation short))
    (hrightUnit : ∀ agent other,
      additiveChoreCost cost agent (rightAllocation agent) - 1 ≤
        additiveChoreCost cost agent (rightAllocation other))
    (hrightFavorite : ∀ other,
      additiveChoreCost cost short (rightAllocation short) ≤
        additiveChoreCost cost short (rightAllocation other)) :
    EFXForChores (additiveChoreCost cost)
      (fun agent => leftAllocation agent ∪ rightAllocation agent) := by
  apply efxForChores_union_of_cost_gap cost leftAllocation rightAllocation hdisjoint
  intro agent other hnonempty
  have hminimum : 1 ≤ ((leftAllocation agent ∪ rightAllocation agent).image (cost agent)).min'
      (Finset.image_nonempty.mpr hnonempty) := by
    apply Finset.le_min'
    intro value hvalue
    obtain ⟨item, _, hvalueEq⟩ := Finset.mem_image.mp hvalue
    rw [← hvalueEq]
    exact hcostLower agent item
  by_cases hagent : agent = short
  · subst agent
    linarith [hleftShort other, hrightFavorite other]
  · by_cases hother : other = short
    · subst other
      linarith [hleftToShort agent hagent, hrightUnit agent short]
    · linarith [hleftOther agent hagent other hother, hrightUnit agent other]

/-- The direct-sink branch of He--Tao's `M₃₄` insertion argument. If a chore
is small for an agent whose bundle is cheapest from that agent's perspective,
adding it to that agent preserves chore EFX. -/
theorem efxForChores_addItem_of_envyFree_owner [DecidableEq Agent] [DecidableEq Item]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item)
    (owner : Agent) (item : Item)
    (hcost : ∀ agent chore, 1 ≤ cost agent chore)
    (hitem : item ∉ allocation owner)
    (hsmall : cost owner item = 1)
    (howner : ∀ agent,
      additiveChoreCost cost owner (allocation owner) ≤
        additiveChoreCost cost owner (allocation agent))
    (hefx : EFXForChores (additiveChoreCost cost) allocation) :
    EFXForChores (additiveChoreCost cost) (addItem allocation owner item) := by
  intro agent comparison
  by_cases hagent : agent = owner
  · subst agent
    right
    intro removed hremoved
    by_cases hcomparison : comparison = owner
    · subst comparison
      simp only [addItem, ↓reduceIte] at hremoved ⊢
      rw [additiveChoreCost_erase cost owner (insert item (allocation owner))
        removed hremoved]
      linarith [hcost owner removed]
    · simp only [addItem, ↓reduceIte, if_neg hcomparison]
      by_cases hremovedItem : removed = item
      · subst removed
        simpa [Finset.sdiff_singleton_eq_erase, Finset.erase_insert hitem] using
          howner comparison
      · have hremovedOld : removed ∈ allocation owner := by
          have hremovedInserted : removed ∈ insert item (allocation owner) := by
            simpa [addItem] using hremoved
          rcases Finset.mem_insert.mp hremovedInserted with hremoved' | hremoved'
          · exact (hremovedItem hremoved').elim
          · exact hremoved'
        rw [Finset.sdiff_singleton_eq_erase,
          Finset.erase_insert_of_ne (Ne.symm hremovedItem)]
        have hdisjoint : Disjoint ({item} : Finset Item) ((allocation owner).erase removed) := by
          rw [Finset.disjoint_left]
          intro chore hchore hmem
          have : chore = item := Finset.mem_singleton.mp hchore
          subst chore
          exact hitem (Finset.mem_of_mem_erase hmem)
        rw [← Finset.singleton_union, additiveChoreCost_union cost owner {item}
          ((allocation owner).erase removed) hdisjoint]
        have hsingleton : additiveChoreCost cost owner ({item} : Finset Item) =
            cost owner item := by
          simp [additiveChoreCost]
        rw [hsingleton]
        have herase := additiveChoreCost_erase cost owner (allocation owner)
          removed hremovedOld
        simp only [Finset.sdiff_singleton_eq_erase] at herase
        rw [herase]
        linarith [hsmall, hcost owner removed, howner comparison]
  · by_cases hempty : allocation agent = ∅
    · left
      simp [addItem, hagent, hempty]
    · right
      intro removed hremoved
      have hremovedOld : removed ∈ allocation agent := by
        simpa [addItem, hagent] using hremoved
      have hold := (hefx agent comparison).resolve_left hempty removed hremovedOld
      by_cases hcomparison : comparison = owner
      · subst comparison
        have hle : additiveChoreCost cost agent (allocation owner) ≤
            additiveChoreCost cost agent (insert item (allocation owner)) := by
          rw [← Finset.singleton_union, additiveChoreCost_union cost agent {item}
            (allocation owner)]
          · simp only [additiveChoreCost, Finset.sum_singleton]
            linarith [hcost agent item]
          · rw [Finset.disjoint_left]
            intro chore hchore hmem
            have : chore = item := Finset.mem_singleton.mp hchore
            subst chore
            exact hitem hmem
        simpa [addItem, hagent] using hold.trans hle
      · simpa [addItem, hagent, hcomparison] using hold

/-- Adding a chore preserves EFX when the augmented owner's bundle is already
cheapest from that owner's perspective. -/
theorem efxForChores_addItem_of_new_owner_minimal [DecidableEq Agent] [DecidableEq Item]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item)
    (owner : Agent) (item : Item)
    (hcost : ∀ agent chore, 0 ≤ cost agent chore)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hminimum : ∀ comparison,
      additiveChoreCost cost owner (addItem allocation owner item owner) ≤
        additiveChoreCost cost owner (addItem allocation owner item comparison)) :
    EFXForChores (additiveChoreCost cost) (addItem allocation owner item) := by
  intro agent comparison
  by_cases hagent : agent = owner
  · subst agent
    by_cases hempty : addItem allocation owner item owner = ∅
    · left
      exact hempty
    · right
      intro removed hremoved
      rw [additiveChoreCost_erase cost owner (addItem allocation owner item owner)
        removed hremoved]
      exact le_trans (by linarith [hcost owner removed]) (hminimum comparison)
  · by_cases hempty : allocation agent = ∅
    · left
      simp [addItem, hagent, hempty]
    · right
      intro removed hremoved
      have hremovedOld : removed ∈ allocation agent := by
        simpa [addItem, hagent] using hremoved
      by_cases hcomparison : comparison = owner
      · subst comparison
        have hold := (hefx agent owner).resolve_left hempty removed hremovedOld
        have hle : additiveChoreCost cost agent (allocation owner) ≤
            additiveChoreCost cost agent (insert item (allocation owner)) := by
          by_cases hitem : item ∈ allocation owner
          · rw [Finset.insert_eq_of_mem hitem]
          · rw [← Finset.singleton_union, additiveChoreCost_union cost agent {item}
              (allocation owner)]
            · simp only [additiveChoreCost, Finset.sum_singleton]
              linarith [hcost agent item]
            · rw [Finset.disjoint_left]
              intro chore hchore hmem
              have : chore = item := Finset.mem_singleton.mp hchore
              subst chore
              exact hitem hmem
        simpa [addItem, hagent] using hold.trans hle
      · simpa [addItem, hagent, hcomparison] using
          (hefx agent comparison).resolve_left hempty removed hremovedOld

/-- Rotating bundles along any partial permutation of cheapest-bundle choices
preserves chore EFX. This is the local cycle-elimination step in He--Tao's
`M₃₄` insertion proof. -/
theorem efxForChores_rotate_of_minimal_successors [DecidableEq Item]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item)
    (next : Agent → Agent)
    (hcost : ∀ agent chore, 0 ≤ cost agent chore)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hminimal : ∀ agent, next agent ≠ agent → ∀ comparison,
      additiveChoreCost cost agent (allocation (next agent)) ≤
        additiveChoreCost cost agent (allocation comparison)) :
    EFXForChores (additiveChoreCost cost) (rotateBundles allocation next) := by
  intro agent comparison
  by_cases hfixed : next agent = agent
  · simpa [rotateBundles, hfixed] using hefx agent (next comparison)
  · by_cases hempty : allocation (next agent) = ∅
    · left
      simp [rotateBundles, hempty]
    · right
      intro removed hremoved
      simp only [rotateBundles] at hremoved ⊢
      rw [additiveChoreCost_erase cost agent (allocation (next agent)) removed hremoved]
      linarith [hcost agent removed, hminimal agent hfixed (next comparison)]

/-! ## Finite cheapest-bundle reductions -/

/-- The finite search space of allocations whose bundles use only `chores`. -/
noncomputable def allocationCandidates [Fintype Agent] [DecidableEq Agent] [DecidableEq Item]
    (chores : Finset Item) : Finset (Allocation Agent Item) :=
  (Finset.univ.pi fun _ : Agent => chores.powerset).image
    fun assignment agent => assignment agent (Finset.mem_univ agent)

theorem mem_allocationCandidates_iff [Fintype Agent] [DecidableEq Agent] [DecidableEq Item]
    (chores : Finset Item) (allocation : Allocation Agent Item) :
    allocation ∈ allocationCandidates (Agent := Agent) chores ↔
      ∀ agent, allocation agent ⊆ chores := by
  classical
  constructor
  · intro hcandidate
    rw [allocationCandidates] at hcandidate
    rcases Finset.mem_image.mp hcandidate with ⟨assignment, hassignment, rfl⟩
    intro agent
    exact Finset.mem_powerset.mp
      (Finset.mem_pi.mp hassignment agent (Finset.mem_univ agent))
  · intro hsubset
    let assignment : (agent : Agent) → agent ∈ (Finset.univ : Finset Agent) → Finset Item :=
      fun agent _ => allocation agent
    refine Finset.mem_image.mpr ⟨assignment, ?_, ?_⟩
    · refine Finset.mem_pi.mpr ?_
      intro agent hagent
      exact Finset.mem_powerset.mpr (hsubset agent)
    · rfl

/-- An edge from `agent` to `comparison` in the cost-side most-envy graph. -/
def StrictMostEnvyEdgeForChores [DecidableEq Item]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item)
    (agent comparison : Agent) : Prop :=
  additiveChoreCost cost agent (allocation comparison) <
      additiveChoreCost cost agent (allocation agent) ∧
    ∀ other,
      additiveChoreCost cost agent (allocation comparison) ≤
        additiveChoreCost cost agent (allocation other)

noncomputable def selfChoreCost [Fintype Agent]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item) : ℝ :=
  ∑ agent, additiveChoreCost cost agent (allocation agent)

theorem efxForChores_rotate_of_strictMostEnvyCycle [DecidableEq Agent] [DecidableEq Item]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item)
    (hcost : ∀ agent chore, 0 ≤ cost agent chore)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (cycle : List Agent)
    (hcycle : ∀ agent, agent ∈ cycle →
      StrictMostEnvyEdgeForChores cost allocation agent (cycle.formPerm agent)) :
    EFXForChores (additiveChoreCost cost) (rotateBundles allocation cycle.formPerm) := by
  apply efxForChores_rotate_of_minimal_successors cost allocation cycle.formPerm hcost hefx
  intro agent hchanged
  exact (hcycle agent (List.mem_of_formPerm_apply_ne hchanged)).2

theorem selfChoreCost_rotate_lt_of_strictMostEnvyCycle
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Item]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item)
    (cycle : List Agent) (hlen : 2 ≤ cycle.length)
    (hcycle : ∀ agent, agent ∈ cycle →
      StrictMostEnvyEdgeForChores cost allocation agent (cycle.formPerm agent)) :
    selfChoreCost cost (rotateBundles allocation cycle.formPerm) <
      selfChoreCost cost allocation := by
  unfold selfChoreCost
  apply Finset.sum_lt_sum
  · intro agent _
    by_cases hmem : agent ∈ cycle
    · exact (hcycle agent hmem).1.le
    · change additiveChoreCost cost agent (allocation (cycle.formPerm agent)) ≤
        additiveChoreCost cost agent (allocation agent)
      rw [List.formPerm_apply_of_notMem hmem]
  · obtain ⟨agent, hmem⟩ := List.exists_mem_of_ne_nil cycle
      (List.ne_nil_of_length_pos (by omega))
    exact ⟨agent, Finset.mem_univ _, (hcycle agent hmem).1⟩

theorem no_strictMostEnvyEdge_implies_envyFreeForChores
    [Fintype Agent] [Nonempty Agent] [DecidableEq Item]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item) (agent : Agent)
    (hno : ∀ comparison,
      ¬ StrictMostEnvyEdgeForChores cost allocation agent comparison) :
    ∀ comparison,
      additiveChoreCost cost agent (allocation agent) ≤
        additiveChoreCost cost agent (allocation comparison) := by
  by_contra hnot
  push Not at hnot
  obtain ⟨cheapest, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset Agent)
    (fun comparison => additiveChoreCost cost agent (allocation comparison)) Finset.univ_nonempty
  apply hno cheapest
  constructor
  · exact lt_of_le_of_lt (hmin (hnot.choose) (Finset.mem_univ _)) hnot.choose_spec
  · intro comparison
    exact hmin comparison (Finset.mem_univ _)

/-- A self-cost-minimal feasible EFX allocation has no directed cycle in its
cost-side most-envy graph. -/
theorem no_strictMostEnvyCycle_of_selfChoreCost_minimal
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Item]
    (cost : ChoreCost Agent Item) (chores : Finset Item)
    (hcost : ∀ agent chore, 0 ≤ cost agent chore)
    (allocation : Allocation Agent Item)
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hminimal : ∀ candidate : Allocation Agent Item,
      IsAllocationOf candidate chores →
      EFXForChores (additiveChoreCost cost) candidate →
      selfChoreCost cost allocation ≤ selfChoreCost cost candidate) :
    ∀ agent, ¬ Relation.TransGen (StrictMostEnvyEdgeForChores cost allocation) agent agent := by
  intro agent hclosed
  obtain ⟨steps, hstepsPos, hsteps⟩ :=
    AppliedModelingLib.Foundations.Graph.exists_relatesInSteps_pos_of_transGen hclosed
  obtain ⟨cycle, hnodup, hlength, hcycle⟩ :=
    AppliedModelingLib.Foundations.Graph.exists_simple_cycle_list_of_stepCycle
      (r := StrictMostEnvyEdgeForChores cost allocation)
      (by
        intro vertex hedge
        exact (lt_irrefl (additiveChoreCost cost vertex (allocation vertex))) hedge.1)
      ⟨agent, steps, hstepsPos, hsteps⟩
  let rotated := rotateBundles allocation cycle.formPerm
  have hrotatedAlloc : IsAllocationOf rotated chores := by
    exact isAllocationOf_rotate_of_bijective allocation chores cycle.formPerm halloc
      cycle.formPerm.bijective
  have hrotatedEFX : EFXForChores (additiveChoreCost cost) rotated := by
    exact efxForChores_rotate_of_strictMostEnvyCycle cost allocation hcost hefx cycle hcycle
  have hle := hminimal rotated hrotatedAlloc hrotatedEFX
  have hlt := selfChoreCost_rotate_lt_of_strictMostEnvyCycle cost allocation cycle hlength hcycle
  exact (not_lt_of_ge hle) hlt

/-- Every finite EFX chore allocation can be reduced, without changing the
allocated chore pool, to one with a cost-side most-envy sink. -/
theorem exists_efx_allocation_with_cost_sink
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent] [DecidableEq Item]
    (cost : ChoreCost Agent Item) (chores : Finset Item)
    (hcost : ∀ agent chore, 0 ≤ cost agent chore)
    (allocation : Allocation Agent Item)
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation) :
    ∃ reduced : Allocation Agent Item, IsAllocationOf reduced chores ∧
      EFXForChores (additiveChoreCost cost) reduced ∧
      ∃ sink, ∀ comparison,
        additiveChoreCost cost sink (reduced sink) ≤
          additiveChoreCost cost sink (reduced comparison) := by
  classical
  let eligible := (allocationCandidates (Agent := Agent) chores).filter fun candidate =>
    IsAllocationOf candidate chores ∧ EFXForChores (additiveChoreCost cost) candidate
  have hmember : allocation ∈ eligible := by
    refine Finset.mem_filter.mpr ⟨?_, halloc, hefx⟩
    rw [mem_allocationCandidates_iff]
    exact fun agent item hitem => halloc.1 agent item hitem
  obtain ⟨reduced, hmemberReduced, hminimal⟩ :=
    Finset.exists_min_image eligible (selfChoreCost cost) ⟨allocation, hmember⟩
  have hreduced := Finset.mem_filter.mp hmemberReduced
  refine ⟨reduced, hreduced.2.1, hreduced.2.2, ?_⟩
  by_contra hnoSink
  push Not at hnoSink
  obtain ⟨cycle, hnodup, hlen, hcycle⟩ :=
    AppliedModelingLib.Foundations.Graph.exists_simple_cycle_list_of_forall_exists_edge
      (r := StrictMostEnvyEdgeForChores cost reduced)
      (by
        intro agent hedge
        exact (lt_irrefl (additiveChoreCost cost agent (reduced agent))) hedge.1)
      (by
        intro agent
        obtain ⟨comparison, hcomparison⟩ := hnoSink agent
        obtain ⟨cheapest, _, hminimum⟩ :=
          Finset.exists_min_image (Finset.univ : Finset Agent)
            (fun other => additiveChoreCost cost agent (reduced other)) Finset.univ_nonempty
        refine ⟨cheapest, ?_, fun other => hminimum other (Finset.mem_univ _)⟩
        exact lt_of_le_of_lt (hminimum comparison (Finset.mem_univ _)) hcomparison)
  let rotated := rotateBundles reduced cycle.formPerm
  have hrotatedAlloc : IsAllocationOf rotated chores := by
    exact isAllocationOf_rotate_of_bijective reduced chores cycle.formPerm hreduced.2.1
      cycle.formPerm.bijective
  have hrotatedEFX : EFXForChores (additiveChoreCost cost) rotated := by
    exact efxForChores_rotate_of_strictMostEnvyCycle cost reduced hcost hreduced.2.2 cycle hcycle
  have hrotatedMember : rotated ∈ eligible := by
    refine Finset.mem_filter.mpr ⟨?_, hrotatedAlloc, hrotatedEFX⟩
    rw [mem_allocationCandidates_iff]
    exact fun agent item hitem => hrotatedAlloc.1 agent item hitem
  have hle := hminimal rotated hrotatedMember
  have hlt := selfChoreCost_rotate_lt_of_strictMostEnvyCycle cost reduced cycle hlen hcycle
  exact (not_lt_of_ge hle) hlt

/-- A finite EFX allocation can be reduced to a self-cost-minimal EFX
allocation whose cost-side most-envy graph is acyclic and has a sink. -/
theorem exists_reduced_efx_allocation_with_cost_sink_and_no_mostEnvyCycle
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent] [DecidableEq Item]
    (cost : ChoreCost Agent Item) (chores : Finset Item)
    (hcost : ∀ agent chore, 0 ≤ cost agent chore)
    (allocation : Allocation Agent Item)
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation) :
    ∃ reduced : Allocation Agent Item, IsAllocationOf reduced chores ∧
      EFXForChores (additiveChoreCost cost) reduced ∧
      (∀ agent, ¬ Relation.TransGen (StrictMostEnvyEdgeForChores cost reduced) agent agent) ∧
      ∃ sink, ∀ comparison,
        additiveChoreCost cost sink (reduced sink) ≤
          additiveChoreCost cost sink (reduced comparison) := by
  classical
  let eligible := (allocationCandidates (Agent := Agent) chores).filter fun candidate =>
    IsAllocationOf candidate chores ∧ EFXForChores (additiveChoreCost cost) candidate
  have hmember : allocation ∈ eligible := by
    refine Finset.mem_filter.mpr ⟨?_, halloc, hefx⟩
    rw [mem_allocationCandidates_iff]
    exact fun agent item hitem => halloc.1 agent item hitem
  obtain ⟨reduced, hmemberReduced, hminimal⟩ :=
    Finset.exists_min_image eligible (selfChoreCost cost) ⟨allocation, hmember⟩
  have hreduced := Finset.mem_filter.mp hmemberReduced
  have hminimal' : ∀ candidate : Allocation Agent Item,
      IsAllocationOf candidate chores →
      EFXForChores (additiveChoreCost cost) candidate →
      selfChoreCost cost reduced ≤ selfChoreCost cost candidate := by
    intro candidate hcandidateAlloc hcandidateEFX
    apply hminimal candidate
    refine Finset.mem_filter.mpr ⟨?_, ⟨hcandidateAlloc, hcandidateEFX⟩⟩
    rw [mem_allocationCandidates_iff]
    exact fun agent item hitem => hcandidateAlloc.1 agent item hitem
  have hnoCycle := no_strictMostEnvyCycle_of_selfChoreCost_minimal cost chores hcost
    reduced hreduced.2.1 hreduced.2.2 hminimal'
  refine ⟨reduced, hreduced.2.1, hreduced.2.2, hnoCycle, ?_⟩
  by_contra hnoSink
  push Not at hnoSink
  have hstep : ∀ agent, ∃ comparison,
      StrictMostEnvyEdgeForChores cost reduced agent comparison := by
    intro agent
    obtain ⟨comparison, hcomparison⟩ := hnoSink agent
    obtain ⟨cheapest, _, hminimum⟩ :=
      Finset.exists_min_image (Finset.univ : Finset Agent)
        (fun other => additiveChoreCost cost agent (reduced other)) Finset.univ_nonempty
    refine ⟨cheapest, ?_, fun other => hminimum other (Finset.mem_univ _)⟩
    exact lt_of_le_of_lt (hminimum comparison (Finset.mem_univ _)) hcomparison
  have hnotwf : ¬ WellFounded (Function.swap (StrictMostEnvyEdgeForChores cost reduced)) := by
    intro hwf
    obtain ⟨agent, _, hminimum⟩ := hwf.has_min Set.univ Set.univ_nonempty
    obtain ⟨comparison, hcomparison⟩ := hstep agent
    exact hminimum comparison (by simp) hcomparison
  obtain ⟨agent, hclosed⟩ :=
    AppliedModelingLib.Foundations.Graph.exists_transGen_self_of_not_wellFounded hnotwf
  apply hnoCycle agent
  simpa only [Function.swap] using hclosed.swap

/-- The final rotation-and-insertion step in the hard branch of He--Tao's
`M₃₄` insertion proof. -/
theorem efxForChores_addItem_after_rotation_of_minimal_path
    [DecidableEq Agent] [DecidableEq Item]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item)
    (next : Agent → Agent) (owner sink : Agent) (item : Item)
    (hownerNe : owner ≠ sink) (hnextOwner : next owner = sink)
    (hcost : ∀ agent chore, 1 ≤ cost agent chore)
    (hitem : item ∉ allocation sink)
    (hownerSmall : cost owner item = 1)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hownerMin : ∀ comparison,
      additiveChoreCost cost owner (allocation sink) ≤
        additiveChoreCost cost owner (allocation comparison))
    (hpathMin : ∀ agent, agent ≠ sink → agent ≠ owner → next agent ≠ agent →
      ∀ comparison,
        additiveChoreCost cost agent (allocation (next agent)) ≤
          additiveChoreCost cost agent (allocation comparison))
    (hsinkMin : ∀ comparison,
      additiveChoreCost cost sink (allocation (next sink)) ≤
        additiveChoreCost cost sink
          (addItem (rotateBundles allocation next) owner item comparison)) :
    EFXForChores (additiveChoreCost cost)
      (addItem (rotateBundles allocation next) owner item) := by
  intro agent comparison
  by_cases hagentSink : agent = sink
  · subst agent
    right
    intro removed hremoved
    have hsinkBundle : addItem (rotateBundles allocation next) owner item sink =
        allocation (next sink) := by
      simp [addItem, rotateBundles, hownerNe.symm]
    have hremovedOld : removed ∈ allocation (next sink) := by
      simpa [hsinkBundle] using hremoved
    rw [hsinkBundle]
    rw [additiveChoreCost_erase cost sink (allocation (next sink)) removed hremovedOld]
    linarith [hcost sink removed, hsinkMin comparison]
  · by_cases hagentOwner : agent = owner
    · subst agent
      right
      intro removed hremoved
      by_cases hcomparisonOwner : comparison = owner
      · subst comparison
        have hownerBundle : addItem (rotateBundles allocation next) owner item owner =
            insert item (allocation sink) := by
          simp [addItem, rotateBundles, hnextOwner]
        have hremovedInserted : removed ∈ insert item (allocation sink) := by
          simpa [hownerBundle] using hremoved
        rw [hownerBundle]
        rw [additiveChoreCost_erase cost owner (insert item (allocation sink))
          removed hremovedInserted]
        linarith [hcost owner removed]
      · have hownerBundle : addItem (rotateBundles allocation next) owner item owner =
            insert item (allocation sink) := by
          simp [addItem, rotateBundles, hnextOwner]
        have hcomparisonBundle : addItem (rotateBundles allocation next) owner item comparison =
            allocation (next comparison) := by
          simp [addItem, rotateBundles, hcomparisonOwner]
        have hremovedInserted : removed ∈ insert item (allocation sink) := by
          simpa [hownerBundle] using hremoved
        rw [hownerBundle, hcomparisonBundle]
        by_cases hremovedItem : removed = item
        · subst removed
          simp only [Finset.sdiff_singleton_eq_erase, Finset.erase_insert hitem]
          exact hownerMin (next comparison)
        · have hremovedInserted : removed ∈ insert item (allocation sink) := by
            exact hremovedInserted
          have hremovedOld : removed ∈ allocation sink := by
            rcases Finset.mem_insert.mp hremovedInserted with hremoved' | hremoved'
            · exact (hremovedItem hremoved').elim
            · exact hremoved'
          simp only [Finset.sdiff_singleton_eq_erase]
          rw [Finset.erase_insert_of_ne (Ne.symm hremovedItem)]
          have hdisjoint : Disjoint ({item} : Finset Item) ((allocation sink).erase removed) := by
            rw [Finset.disjoint_left]
            intro chore hchore hmem
            have : chore = item := Finset.mem_singleton.mp hchore
            subst chore
            exact hitem (Finset.mem_of_mem_erase hmem)
          rw [← Finset.singleton_union, additiveChoreCost_union cost owner {item}
            ((allocation sink).erase removed) hdisjoint]
          have hsingleton : additiveChoreCost cost owner ({item} : Finset Item) =
              cost owner item := by
            simp [additiveChoreCost]
          rw [hsingleton]
          have herase := additiveChoreCost_erase cost owner (allocation sink) removed hremovedOld
          simp only [Finset.sdiff_singleton_eq_erase] at herase
          rw [herase]
          linarith [hownerSmall, hcost owner removed, hownerMin (next comparison)]
    · by_cases hfixed : next agent = agent
      · by_cases hempty : allocation agent = ∅
        · left
          simp [addItem, rotateBundles, hagentOwner, hfixed, hempty]
        · right
          intro removed hremoved
          have hremovedOld : removed ∈ allocation agent := by
            simpa [addItem, rotateBundles, hagentOwner, hfixed] using hremoved
          by_cases hcomparisonOwner : comparison = owner
          · subst comparison
            have hold := (hefx agent sink).resolve_left hempty removed hremovedOld
            have hle : additiveChoreCost cost agent (allocation sink) ≤
                additiveChoreCost cost agent (insert item (allocation sink)) := by
              rw [← Finset.singleton_union, additiveChoreCost_union cost agent {item}
                (allocation sink)]
              · simp only [additiveChoreCost, Finset.sum_singleton]
                linarith [hcost agent item]
              · rw [Finset.disjoint_left]
                intro chore hchore hmem
                have : chore = item := Finset.mem_singleton.mp hchore
                subst chore
                exact hitem hmem
            simpa [addItem, rotateBundles, hagentOwner, hfixed, hnextOwner] using hold.trans hle
          · simpa [addItem, rotateBundles, hagentOwner, hfixed, hcomparisonOwner] using
              (hefx agent (next comparison)).resolve_left hempty removed hremovedOld
      · right
        intro removed hremoved
        have hremovedOld : removed ∈ allocation (next agent) := by
          simpa [addItem, rotateBundles, hagentOwner] using hremoved
        have hself : additiveChoreCost cost agent
            (allocation (next agent) \ {removed}) ≤
            additiveChoreCost cost agent (allocation (next agent)) := by
          rw [additiveChoreCost_erase cost agent (allocation (next agent)) removed hremovedOld]
          linarith [hcost agent removed]
        by_cases hcomparisonOwner : comparison = owner
        · subst comparison
          have hcomp : additiveChoreCost cost agent (allocation (next agent)) ≤
              additiveChoreCost cost agent (allocation sink) :=
            hpathMin agent hagentSink hagentOwner hfixed sink
          have hle : additiveChoreCost cost agent (allocation sink) ≤
              additiveChoreCost cost agent (insert item (allocation sink)) := by
            rw [← Finset.singleton_union, additiveChoreCost_union cost agent {item}
              (allocation sink)]
            · simp only [additiveChoreCost, Finset.sum_singleton]
              linarith [hcost agent item]
            · rw [Finset.disjoint_left]
              intro chore hchore hmem
              have : chore = item := Finset.mem_singleton.mp hchore
              subst chore
              exact hitem hmem
          simpa [addItem, rotateBundles, hagentOwner, hnextOwner] using
            hself.trans (hcomp.trans hle)
        · have hcomp : additiveChoreCost cost agent (allocation (next agent)) ≤
              additiveChoreCost cost agent (allocation (next comparison)) :=
            hpathMin agent hagentSink hagentOwner hfixed (next comparison)
          simpa [addItem, rotateBundles, hagentOwner, hcomparisonOwner] using hself.trans hcomp

/-- The direct-sink branch of the M₃₄ insertion lemma, packaged with
the resulting feasible extended allocation. -/
theorem exists_efx_allocation_addItem_of_small_cost_sink
    {Item : Type*} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (item : Item)
    (hcost : ∀ agent chore, 1 ≤ cost agent chore)
    (hitem : item ∉ chores)
    (allocation : Allocation (Fin 4) Item)
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (sink : Fin 4) (hsmall : cost sink item = 1)
    (hminimum : ∀ comparison,
      additiveChoreCost cost sink (allocation sink) ≤
        additiveChoreCost cost sink (allocation comparison)) :
    ∃ extended : Allocation (Fin 4) Item,
      IsAllocationOf extended (insert item chores) ∧
        EFXForChores (additiveChoreCost cost) extended := by
  refine ⟨addItem allocation sink item, ?_, ?_⟩
  · exact isAllocationOf_addItem_insert allocation chores sink item halloc hitem
  · apply efxForChores_addItem_of_envyFree_owner cost allocation sink item hcost
      (by
        intro hmem
        exact hitem (halloc.1 sink item hmem))
      hsmall hminimum hefx

/-- Allocation `improvement` Pareto-dominates `allocation` for chores when it
weakly decreases every cost and strictly decreases one cost. -/
def ParetoDominatesForChores (cost : Agent → Bundle Item → ℝ)
    (allocation improvement : Allocation Agent Item) : Prop :=
  (∀ i, cost i (improvement i) ≤ cost i (allocation i)) ∧
    ∃ i, cost i (improvement i) < cost i (allocation i)

/-- A complete chore allocation is Pareto-optimal if no other complete
allocation Pareto-dominates it in the cost direction. -/
def ParetoOptimalForChores [DecidableEq Item] (cost : Agent → Bundle Item → ℝ)
    (chores : Finset Item) (allocation : Allocation Agent Item) : Prop :=
  IsAllocationOf allocation chores ∧
    ¬ ∃ improvement : Allocation Agent Item,
      IsAllocationOf improvement chores ∧
        ParetoDominatesForChores cost allocation improvement

/-- An additive indivisible-chore instance: a finite chore set with nonnegative
per-agent item costs. -/
structure AdditiveChoreInstance (Agent Item : Type*) where
  /-- The chores that must be allocated. -/
  chores : Finset Item
  /-- The cost of each individual chore for each agent. -/
  cost : ChoreCost Agent Item
  /-- Source-model nonnegativity of individual chore costs. -/
  nonneg : ∀ agent item, 0 ≤ cost agent item

namespace AdditiveChoreInstance

/-- A feasible allocation partitions the instance's entire chore set. -/
def IsFeasible {Agent Item : Type*} [DecidableEq Item]
    (choreInstance : AdditiveChoreInstance Agent Item)
    (allocation : Allocation Agent Item) : Prop :=
  IsAllocationOf allocation choreInstance.chores

/-- EFX for a chore instance, expressed using its additive cost function. -/
def IsEFX {Agent Item : Type*} [DecidableEq Item]
    (choreInstance : AdditiveChoreInstance Agent Item)
    (allocation : Allocation Agent Item) : Prop :=
  EFXForChores (additiveChoreCost choreInstance.cost) allocation

/-- Pareto-optimality for a chore instance among allocations of all its chores. -/
def IsParetoOptimal {Agent Item : Type*} [DecidableEq Item]
    (choreInstance : AdditiveChoreInstance Agent Item)
    (allocation : Allocation Agent Item) : Prop :=
  ParetoOptimalForChores (additiveChoreCost choreInstance.cost) choreInstance.chores allocation

/-- The threshold characterization of EFX, specialized to an additive
chore instance. -/
theorem isEFX_iff_threshold_le {Agent Item : Type*} [DecidableEq Item]
    (choreInstance : AdditiveChoreInstance Agent Item)
    (allocation : Allocation Agent Item) :
    choreInstance.IsEFX allocation ↔
      ∀ i j, efxThreshold choreInstance.cost i (allocation i) ≤
        additiveChoreCost choreInstance.cost i (allocation j) :=
  efxForChores_iff_threshold_le choreInstance.cost choreInstance.nonneg allocation

end AdditiveChoreInstance

/-- Every item cost is one of three nonnegative values. -/
def IsTriValuedChoreCost (cost : ChoreCost Agent Item) : Prop :=
  ∃ p q r : ℝ, 0 ≤ p ∧ 0 ≤ q ∧ 0 ≤ r ∧
    ∀ agent item, cost agent item = p ∨ cost agent item = q ∨ cost agent item = r

/-- Every item cost is one of two nonnegative values. -/
def IsBiValuedChoreCost (cost : ChoreCost Agent Item) : Prop :=
  ∃ p q : ℝ, 0 ≤ p ∧ 0 ≤ q ∧
    ∀ agent item, cost agent item = p ∨ cost agent item = q

/-- In a `(1, r)` bi-valued instance, an item is large for an agent precisely
when its individual cost is `r`. -/
def IsLargeChore (cost : ChoreCost Agent Item) (r : ℝ)
    (agent : Agent) (item : Item) : Prop :=
  cost agent item = r

/-- In a `(1, r)` bi-valued instance, an item is small for an agent precisely
when its individual cost is `1`. -/
def IsSmallChore (cost : ChoreCost Agent Item)
    (agent : Agent) (item : Item) : Prop :=
  cost agent item = 1

/-- A normalized bi-valued chore cost takes only the values `1` and `r`. -/
def IsOneOrRChoreCost (cost : ChoreCost Agent Item) (r : ℝ) : Prop :=
  ∀ agent item, cost agent item = 1 ∨ cost agent item = r

/-- A strictly positive ordered bi-valued cost normalizes to a `(1,r)` cost
with `r > 1`.  The converse EFX transfer is supplied by
`efxForChores_rescale_iff_of_pos`. -/
theorem normalize_positive_biValuedChoreCost
    (cost : ChoreCost Agent Item) (p q : ℝ)
    (hp : 0 < p) (hpq : p < q)
    (hvalues : ∀ agent item, cost agent item = p ∨ cost agent item = q) :
    IsOneOrRChoreCost (rescaleChoreCost p⁻¹ cost) (q / p) ∧ 1 < q / p := by
  constructor
  · intro agent item
    rcases hvalues agent item with hsmall | hlarge
    · left
      change p⁻¹ * cost agent item = 1
      rw [hsmall]
      exact inv_mul_cancel₀ hp.ne'
    · right
      change p⁻¹ * cost agent item = q / p
      rw [hlarge]
      simp [div_eq_mul_inv, mul_comm]
  · rw [lt_div_iff₀ hp]
    linarith

/-- The normalized bi-valued condition is preserved by relabelling agents. -/
theorem IsOneOrRChoreCost.relabel {Agent' : Type*}
    (labels : Agent' ≃ Agent) (cost : ChoreCost Agent Item) (r : ℝ)
    (hcost : IsOneOrRChoreCost cost r) :
    IsOneOrRChoreCost (relabelChoreCost labels cost) r := by
  intro agent item
  exact hcost (labels agent) item

/-- If a bundle contains no chore small for its observer, every chore in it
is large for that observer in a normalized bi-valued instance.  This is the
all-large branch used by direct chore-EFX schedules. -/
theorem IsOneOrRChoreCost.all_large_of_no_small
    (cost : ChoreCost Agent Item) (r : ℝ) (hcost : IsOneOrRChoreCost cost r)
    (agent : Agent) (bundle : Finset Item)
    (hnoSmall : ¬ ∃ item ∈ bundle, IsSmallChore cost agent item) :
    ∀ item ∈ bundle, IsLargeChore cost r agent item := by
  intro item hitem
  rcases hcost agent item with hsmall | hlarge
  · exact (hnoSmall ⟨item, hitem, by simpa [IsSmallChore] using hsmall⟩).elim
  · simpa [IsLargeChore] using hlarge

/-- A normalized `(1,r)` cost is nonnegative when `r` is nonnegative. -/
theorem IsOneOrRChoreCost.nonneg (cost : ChoreCost Agent Item) (r : ℝ)
    (hcost : IsOneOrRChoreCost cost r)
    (hr : 0 ≤ r) (agent : Agent) (item : Item) :
    0 ≤ cost agent item := by
  rcases hcost agent item with hsmall | hlarge
  · rw [hsmall]
    norm_num
  · rw [hlarge]
    exact hr

/-- Every normalized `(1,r)` cost is at least one when `r ≥ 1`. -/
theorem IsOneOrRChoreCost.one_le (cost : ChoreCost Agent Item) (r : ℝ)
    (hcost : IsOneOrRChoreCost cost r)
    (hr : 1 ≤ r) (agent : Agent) (item : Item) :
    1 ≤ cost agent item := by
  rcases hcost agent item with hsmall | hlarge
  · rw [hsmall]
  · rw [hlarge]
    exact hr

/-- Every normalized `(1,r)` cost is at most `r` when `r ≥ 1`. -/
theorem IsOneOrRChoreCost.le_r (cost : ChoreCost Agent Item) (r : ℝ)
    (hcost : IsOneOrRChoreCost cost r)
    (hr : 1 ≤ r) (agent : Agent) (item : Item) :
    cost agent item ≤ r := by
  rcases hcost agent item with hsmall | hlarge
  · rw [hsmall]
    exact hr
  · rw [hlarge]

/-- In a normalized bi-valued EFX allocation, an owner's whole bundle costs
at most `r` more than any comparison bundle.  This is the direct consequence
of deleting one owned chore and bounding its cost by `r`. -/
theorem EFXForChores.additive_le_additive_add_r [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (allocation : Allocation Agent Item)
    (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (own comparison : Agent) :
    additiveChoreCost cost own (allocation own) ≤
      additiveChoreCost cost own (allocation comparison) + r := by
  by_cases hempty : allocation own = ∅
  · rw [hempty]
    have hnonneg : 0 ≤ additiveChoreCost cost own (allocation comparison) :=
      additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) own _
    change 0 ≤ additiveChoreCost cost own (allocation comparison) + r
    linarith
  · rcases hefx own comparison with hcontradiction | hitems
    · exact (hempty hcontradiction).elim
    obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hcomparison := hitems item hitem
    rw [additiveChoreCost_erase cost own (allocation own) item hitem] at hcomparison
    have hitemLe : cost own item ≤ r :=
      IsOneOrRChoreCost.le_r cost r hcost hr own item
    linarith

/-- In a normalized bi-valued bundle, additive cost is its cardinality plus
`r - 1` for each large chore.  This cardinal accounting identity is useful
when a construction controls the number of large chores in each bundle rather
than their particular identities. -/
noncomputable def largeChoreSet [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (agent : Agent) (bundle : Bundle Item) :
    Finset Item := by
  classical
  exact bundle.filter fun item => IsLargeChore cost r agent item

/-- Relabelling agents commutes with selecting the large chores in a fixed
bundle. -/
theorem largeChoreSet_relabel [DecidableEq Item]
    {Agent' : Type*} (labels : Agent' ≃ Agent) (cost : ChoreCost Agent Item)
    (r : ℝ) (agent : Agent') (bundle : Bundle Item) :
    largeChoreSet (relabelChoreCost labels cost) r agent bundle =
      largeChoreSet cost r (labels agent) bundle := by
  classical
  ext item
  simp [largeChoreSet, relabelChoreCost, IsLargeChore]

/-- Large chores selected from a bundle remain a subbundle of it. -/
theorem largeChoreSet_subset_bundle [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (agent : Agent) (bundle : Bundle Item) :
    largeChoreSet cost r agent bundle ⊆ bundle := by
  intro item hitem
  exact (by simpa [largeChoreSet] using hitem :
    item ∈ bundle ∧ IsLargeChore cost r agent item).1

/-- If the left component is entirely small and the right component entirely
large for one evaluator, the large subbundle of their union is exactly the
right component. -/
theorem largeChoreSet_union_eq_right_of_left_small_right_large [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (agent : Agent)
    (left right : Bundle Item) (hr : 1 < r)
    (hleft : ∀ item ∈ left, IsSmallChore cost agent item)
    (hright : ∀ item ∈ right, IsLargeChore cost r agent item) :
    largeChoreSet cost r agent (left ∪ right) = right := by
  classical
  ext item
  constructor
  · intro hitem
    have hitem' : item ∈ left ∪ right ∧ IsLargeChore cost r agent item := by
      simpa [largeChoreSet] using hitem
    rcases Finset.mem_union.mp hitem'.1 with hleftMem | hrightMem
    · have hsmall := hleft item hleftMem
      exfalso
      have hsmallCost : cost agent item = 1 := hsmall
      have hlarge : cost agent item = r := hitem'.2
      linarith
    · exact hrightMem
  · intro hitem
    have hlarge := hright item hitem
    simp [largeChoreSet, hitem, hlarge]

/-- The symmetric large-subset calculation: if the left component is entirely
large and the right component entirely small, precisely the left component is
large in their union. -/
theorem largeChoreSet_union_eq_left_of_left_large_right_small [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (agent : Agent)
    (left right : Bundle Item) (hr : 1 < r)
    (hleft : ∀ item ∈ left, IsLargeChore cost r agent item)
    (hright : ∀ item ∈ right, IsSmallChore cost agent item) :
    largeChoreSet cost r agent (left ∪ right) = left := by
  simpa only [Finset.union_comm] using
    largeChoreSet_union_eq_right_of_left_small_right_large cost r agent right left hr hright hleft

theorem additiveChoreCost_eq_card_add_largeCard [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (agent : Agent) (bundle : Bundle Item)
    (hcost : IsOneOrRChoreCost cost r) :
    additiveChoreCost cost agent bundle =
      (bundle.card : ℝ) + (r - 1) *
        ((largeChoreSet cost r agent bundle).card : ℝ) := by
  classical
  unfold additiveChoreCost
  calc
    ∑ item ∈ bundle, cost agent item =
        ∑ item ∈ bundle, (1 + if IsLargeChore cost r agent item then r - 1 else 0) := by
      apply Finset.sum_congr rfl
      intro item hitem
      by_cases hlarge : IsLargeChore cost r agent item
      · change cost agent item = r at hlarge
        calc
          cost agent item = r := hlarge
          _ = 1 + (r - 1) := by ring
          _ = 1 + if IsLargeChore cost r agent item then r - 1 else 0 := by
            simp [IsLargeChore, hlarge]
      · rcases hcost agent item with hsmall | hlarge'
        · have hnotLarge : ¬ cost agent item = r := by
            simpa [IsLargeChore] using hlarge
          calc
            cost agent item = 1 := hsmall
            _ = 1 + 0 := by norm_num
            _ = 1 + if IsLargeChore cost r agent item then r - 1 else 0 := by
              simp [IsLargeChore, hnotLarge]
        · exact (hlarge (by simpa [IsLargeChore] using hlarge')).elim
    _ = (∑ _item ∈ bundle, (1 : ℝ)) +
        ∑ item ∈ bundle, (if IsLargeChore cost r agent item then r - 1 else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (bundle.card : ℝ) +
        (r - 1) * ((largeChoreSet cost r agent bundle).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [largeChoreSet, nsmul_eq_mul]; ring

/-- Equal bundle cardinalities and no more large chores in the owner's bundle
than in any comparison bundle imply chore envy-freeness.  This is the
large-item-count form of the additive `{1,r}` calculation used when a
partial allocation has been gap-filled to equal size. -/
theorem envyFreeForChores_of_equalCard_and_largeCard_le [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (allocation : Allocation Agent Item)
    (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hcard : ∀ own comparison, (allocation own).card = (allocation comparison).card)
    (hlarge : ∀ own comparison,
      (largeChoreSet cost r own (allocation own)).card ≤
        (largeChoreSet cost r own (allocation comparison)).card) :
    EnvyFreeForChores (additiveChoreCost cost) allocation := by
  intro own comparison
  rw [additiveChoreCost_eq_card_add_largeCard cost r own (allocation own) hcost,
    additiveChoreCost_eq_card_add_largeCard cost r own (allocation comparison) hcost]
  have hcardReal : ((allocation own).card : ℝ) = (allocation comparison).card := by
    exact_mod_cast hcard own comparison
  have hlargeReal : ((largeChoreSet cost r own (allocation own)).card : ℝ) ≤
      (largeChoreSet cost r own (allocation comparison)).card := by
    exact_mod_cast hlarge own comparison
  have hfactor : 0 ≤ r - 1 := by linarith
  linarith [mul_le_mul_of_nonneg_left hlargeReal hfactor]

/-- Removing a chore commutes with taking the large-chore subbundle. -/
theorem largeChoreSet_erase [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (agent : Agent) (bundle : Bundle Item)
    (item : Item) :
    largeChoreSet cost r agent (bundle \ {item}) =
      (largeChoreSet cost r agent bundle).erase item := by
  classical
  ext chore
  simp [largeChoreSet, and_assoc, and_comm]

/-- The large-item count after deleting an owned chore falls by one exactly
when that chore was large for the evaluating agent. -/
theorem largeChoreSet_erase_card_of_large [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (agent : Agent) (bundle : Bundle Item)
    (item : Item) (hitem : item ∈ bundle) :
    IsLargeChore cost r agent item →
    (largeChoreSet cost r agent (bundle \ {item})).card =
      (largeChoreSet cost r agent bundle).card - 1 := by
  classical
  intro hlarge
  rw [largeChoreSet_erase]
  have hmem : item ∈ largeChoreSet cost r agent bundle := by
    simp [largeChoreSet, hitem, hlarge]
  rw [Finset.card_erase_of_mem hmem]

/-- If the removed chore is small, the evaluating agent's large-item count is
unchanged. -/
theorem largeChoreSet_erase_card_of_not_large [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (agent : Agent) (bundle : Bundle Item)
    (item : Item) (hlarge : ¬ IsLargeChore cost r agent item) :
    (largeChoreSet cost r agent (bundle \ {item})).card =
      (largeChoreSet cost r agent bundle).card := by
  classical
  rw [largeChoreSet_erase]
  have hnotmem : item ∉ largeChoreSet cost r agent bundle := by
    simp [largeChoreSet, hlarge]
  rw [Finset.erase_eq_of_notMem hnotmem]

/--
An allocation is EFX when every owner receives only chores that cost her one
and every bundle has size at least the owner's size minus one. This is the
fairness verification used for the all-small orientation branch of the M₂
multigraph construction.
-/
theorem efxForChores_of_all_owners_small_and_balanced_card [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (allocation : Allocation Agent Item)
    (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hsmall : ∀ agent item, item ∈ allocation agent → IsSmallChore cost agent item)
    (hcard : ∀ i j, (allocation i).card ≤ (allocation j).card + 1) :
    EFXForChores (additiveChoreCost cost) allocation := by
  intro i j
  by_cases hi : allocation i = ∅
  · exact Or.inl hi
  · right
    intro item hitem
    have hcardErase : (allocation i \ {item}).card ≤ (allocation j).card := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem]
      exact Nat.sub_le_iff_le_add.mpr (hcard i j)
    have hcardEraseReal : ((allocation i \ {item}).card : ℝ) ≤ (allocation j).card := by
      exact_mod_cast hcardErase
    have hremovedConst : ∀ chore ∈ allocation i \ {item}, cost i chore = 1 := by
      intro chore hchore
      exact hsmall i chore (Finset.sdiff_subset hchore)
    have hleft : additiveChoreCost cost i (allocation i \ {item}) =
        (allocation i \ {item}).card • (1 : ℝ) :=
      additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation i \ {item}) 1
        hremovedConst
    have hright : (allocation j).card • (1 : ℝ) ≤
        additiveChoreCost cost i (allocation j) :=
      card_nsmul_le_additiveChoreCost_of_le cost i (allocation j) 1
        (fun chore hchore => IsOneOrRChoreCost.one_le cost r hcost hr i chore)
    rw [hleft]
    norm_num [nsmul_eq_mul]
    norm_num [nsmul_eq_mul] at hright
    linarith

/-- A single owner satisfies every chore-EFX comparison when all of her own
chores are small and her bundle has cardinality at most one above the
comparison bundle. -/
theorem doesNotStronglyEnvyForChores_of_ownSmall_and_card [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (allocation : Allocation Agent Item)
    (i j : Agent) (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hsmall : ∀ item ∈ allocation i, IsSmallChore cost i item)
    (hcard : (allocation i).card ≤ (allocation j).card + 1) :
    DoesNotStronglyEnvyForChores (additiveChoreCost cost) allocation i j := by
  by_cases hi : allocation i = ∅
  · exact Or.inl hi
  · right
    intro item hitem
    have hcardErase : (allocation i \ {item}).card ≤ (allocation j).card := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem]
      exact Nat.sub_le_iff_le_add.mpr hcard
    have hcardEraseReal : ((allocation i \ {item}).card : ℝ) ≤ (allocation j).card := by
      exact_mod_cast hcardErase
    have hremovedConst : ∀ chore ∈ allocation i \ {item}, cost i chore = 1 := by
      intro chore hchore
      exact hsmall chore (Finset.sdiff_subset hchore)
    have hleft : additiveChoreCost cost i (allocation i \ {item}) =
        (allocation i \ {item}).card • (1 : ℝ) :=
      additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation i \ {item}) 1
        hremovedConst
    have hright : (allocation j).card • (1 : ℝ) ≤
        additiveChoreCost cost i (allocation j) :=
      card_nsmul_le_additiveChoreCost_of_le cost i (allocation j) 1
        (fun chore hchore => IsOneOrRChoreCost.one_le cost r hcost hr i chore)
    rw [hleft]
    norm_num [nsmul_eq_mul]
    norm_num [nsmul_eq_mul] at hright
    linarith

/-- If every owner finds every chore in her bundle small and bundle sizes are
balanced within one, then the allocation is EFX for `(1,r)`-valued chores. -/
theorem efxForChores_of_ownSmall_balanced [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (allocation : Allocation Agent Item)
    (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hsmall : ∀ agent item, item ∈ allocation agent → IsSmallChore cost agent item)
    (hbalanced : ∀ i j, (allocation i).card ≤ (allocation j).card + 1) :
    EFXForChores (additiveChoreCost cost) allocation := by
  rw [efxForChores_iff_forall_doesNotStronglyEnvy]
  intro i j
  exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation i j hcost hr
    (fun item hitem => hsmall i item hitem) (hbalanced i j)

/-- A version of the own-small EFX certificate for comparison bundles whose
cost lower bound is known directly, rather than through their cardinality. -/
theorem doesNotStronglyEnvyForChores_of_ownSmall_and_costLower [DecidableEq Item]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item)
    (i j : Agent) (hsmall : ∀ item ∈ allocation i, IsSmallChore cost i item)
    (hbound : (((allocation i).card - 1 : ℕ) : ℝ) ≤
      additiveChoreCost cost i (allocation j)) :
    DoesNotStronglyEnvyForChores (additiveChoreCost cost) allocation i j := by
  by_cases hi : allocation i = ∅
  · exact Or.inl hi
  · right
    intro item hitem
    have hcardErase : (allocation i \ {item}).card = (allocation i).card - 1 := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem]
    have hleft : additiveChoreCost cost i (allocation i \ {item}) =
        (allocation i \ {item}).card • (1 : ℝ) :=
      additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation i \ {item}) 1
        (fun chore hchore => hsmall chore (Finset.sdiff_subset hchore))
    rw [hleft, hcardErase]
    norm_num [nsmul_eq_mul]
    exact hbound

/-- A two-valued cost comparison from the large-chore counts in the two
bundles. This is the direct algebraic core of the Case 3.1 comparisons
between the two deficient-pair agents. -/
theorem additiveChoreCost_erase_le_of_largeCard
    [DecidableEq Item] (cost : ChoreCost Agent Item) (r : ℝ)
    (allocation : Allocation Agent Item) (first second : Agent)
    (bundleCard firstLarge secondLarge : ℕ)
    (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hfirstCard : (allocation first).card = bundleCard)
    (hsecondCard : (allocation second).card = bundleCard)
    (hfirstLarge : (largeChoreSet cost r first (allocation first)).card = firstLarge)
    (hsecondLarge : (largeChoreSet cost r first (allocation second)).card = secondLarge)
    (hlargeLe : firstLarge ≤ secondLarge) :
    ∀ item ∈ allocation first,
      additiveChoreCost cost first (allocation first \ {item}) ≤
        additiveChoreCost cost first (allocation second) := by
  intro item hitem
  rw [additiveChoreCost_eq_card_add_largeCard cost r first (allocation first \ {item}) hcost,
    additiveChoreCost_eq_card_add_largeCard cost r first (allocation second) hcost]
  have hcardErase : (allocation first \ {item}).card = bundleCard - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem, hfirstCard]
  have hlargeLeReal : (firstLarge : ℝ) ≤ secondLarge := by
    exact_mod_cast hlargeLe
  have hfactor : 0 ≤ r - 1 := by linarith
  have hdiff : 0 ≤ (secondLarge : ℝ) - firstLarge := by linarith
  have hproduct : 0 ≤ (r - 1) * ((secondLarge : ℝ) - firstLarge) :=
    mul_nonneg hfactor hdiff
  have hbundleCardOne : 1 ≤ bundleCard := by
    have hpositive : 0 < (allocation first).card := Finset.card_pos.mpr ⟨item, hitem⟩
    omega
  by_cases hlarge : IsLargeChore cost r first item
  · rw [largeChoreSet_erase_card_of_large cost r first (allocation first) item hitem hlarge,
      hcardErase, hfirstLarge, hsecondCard, hsecondLarge]
    have hlargeMem : item ∈ largeChoreSet cost r first (allocation first) := by
      simp [largeChoreSet, hitem, hlarge]
    have hfirstLargeOne : 1 ≤ firstLarge := by
      have hpositive : 0 < (largeChoreSet cost r first (allocation first)).card :=
        Finset.card_pos.mpr ⟨item, hlargeMem⟩
      omega
    rw [Nat.cast_sub hbundleCardOne, Nat.cast_sub hfirstLargeOne]
    nlinarith
  · rw [largeChoreSet_erase_card_of_not_large cost r first (allocation first) item hlarge,
      hcardErase, hfirstLarge, hsecondCard, hsecondLarge]
    rw [Nat.cast_sub hbundleCardOne]
    nlinarith

/-- A cardinal/large-count EFX comparison with arbitrary (rather than equal)
bundle sizes.  The displayed real inequality is an upper bound on the source
bundle after one deletion, retaining all of its large chores; it is useful
when the source allocation has deliberately unbalanced cardinalities. -/
theorem additiveChoreCost_erase_le_of_card_largeCard_upper
    [DecidableEq Item] (cost : ChoreCost Agent Item) (r : ℝ)
    (allocation : Allocation Agent Item) (first second : Agent)
    (firstCard secondCard firstLarge secondLarge : ℕ)
    (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hfirstCard : (allocation first).card = firstCard)
    (hsecondCard : (allocation second).card = secondCard)
    (hfirstLarge : (largeChoreSet cost r first (allocation first)).card = firstLarge)
    (hsecondLarge : (largeChoreSet cost r first (allocation second)).card = secondLarge)
    (hbound : (((firstCard - 1 : ℕ) : ℝ) + (r - 1) * firstLarge) ≤
      (secondCard : ℝ) + (r - 1) * secondLarge) :
    ∀ item ∈ allocation first,
      additiveChoreCost cost first (allocation first \ {item}) ≤
        additiveChoreCost cost first (allocation second) := by
  intro item hitem
  rw [additiveChoreCost_eq_card_add_largeCard cost r first (allocation first \ {item}) hcost,
    additiveChoreCost_eq_card_add_largeCard cost r first (allocation second) hcost]
  have hcardErase : (allocation first \ {item}).card = firstCard - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem, hfirstCard]
  have hlargeErase :
      (largeChoreSet cost r first (allocation first \ {item})).card ≤ firstLarge := by
    rw [largeChoreSet_erase, ← hfirstLarge]
    exact Finset.card_le_card (Finset.erase_subset _ _)
  have hlargeEraseReal :
      ((largeChoreSet cost r first (allocation first \ {item})).card : ℝ) ≤ firstLarge := by
    exact_mod_cast hlargeErase
  have hfactor : 0 ≤ r - 1 := by linarith
  rw [hcardErase, hsecondCard, hsecondLarge]
  nlinarith

/-- When all chores of the source bundle are large for the evaluating agent,
deleting any one leaves precisely `card - 1` copies of `r`.  This provides a
sharp comparison against an arbitrary two-valued target bundle. -/
theorem additiveChoreCost_erase_le_of_allLarge_first
    [DecidableEq Item] (cost : ChoreCost Agent Item) (r : ℝ)
    (allocation : Allocation Agent Item) (first second : Agent)
    (firstCard secondCard secondLarge : ℕ)
    (hcost : IsOneOrRChoreCost cost r)
    (hfirstCard : (allocation first).card = firstCard)
    (hsecondCard : (allocation second).card = secondCard)
    (hfirstAllLarge : ∀ item ∈ allocation first, IsLargeChore cost r first item)
    (hsecondLarge : (largeChoreSet cost r first (allocation second)).card = secondLarge)
    (hbound : (((firstCard - 1 : ℕ) : ℝ) * r) ≤
      (secondCard : ℝ) + (r - 1) * secondLarge) :
    ∀ item ∈ allocation first,
      additiveChoreCost cost first (allocation first \ {item}) ≤
        additiveChoreCost cost first (allocation second) := by
  intro item hitem
  rw [additiveChoreCost_erase_eq_card_sub_one_nsmul_of_constant cost first
    (allocation first) item r hitem (fun chore hchore => hfirstAllLarge chore hchore),
    additiveChoreCost_eq_card_add_largeCard cost r first (allocation second) hcost,
    hfirstCard, hsecondCard, hsecondLarge]
  norm_num [nsmul_eq_mul]
  exact hbound

/-- A bundle whose every chore is large for the evaluating agent is expensive
enough to certify EFX against a same-cardinality source bundle after any one
chore is removed, provided its cardinality is at least one less.  This is the
other Case 3.1 comparison, from a deficient-pair agent to either complementary
agent. -/
theorem additiveChoreCost_erase_le_of_allLarge_comparison
    [DecidableEq Item] (cost : ChoreCost Agent Item) (r : ℝ)
    (allocation : Allocation Agent Item) (first second : Agent)
    (bundleCard firstLarge : ℕ)
    (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hfirstCard : (allocation first).card = bundleCard)
    (hfirstLarge : (largeChoreSet cost r first (allocation first)).card = firstLarge)
    (hsecondAllLarge : ∀ item ∈ allocation second, IsLargeChore cost r first item)
    (hsecondCard : bundleCard - 1 ≤ (allocation second).card) :
    ∀ item ∈ allocation first,
      additiveChoreCost cost first (allocation first \ {item}) ≤
        additiveChoreCost cost first (allocation second) := by
  intro item hitem
  have hright : additiveChoreCost cost first (allocation second) =
      (allocation second).card • r :=
    additiveChoreCost_eq_card_nsmul_of_constant cost first (allocation second) r
      hsecondAllLarge
  rw [additiveChoreCost_eq_card_add_largeCard cost r first (allocation first \ {item}) hcost,
    hright]
  have hcardErase : (allocation first \ {item}).card = bundleCard - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem, hfirstCard]
  have hbundleCardOne : 1 ≤ bundleCard := by
    have hpositive : 0 < (allocation first).card := Finset.card_pos.mpr ⟨item, hitem⟩
    omega
  have hsecondCardReal : ((bundleCard - 1 : ℕ) : ℝ) ≤ (allocation second).card := by
    exact_mod_cast hsecondCard
  have hfactor : 0 ≤ r - 1 := by linarith
  have hrnonneg : 0 ≤ r := by linarith
  have hrightScale : ((bundleCard - 1 : ℕ) : ℝ) * r ≤
      (allocation second).card * r :=
    mul_le_mul_of_nonneg_right hsecondCardReal hrnonneg
  rw [Nat.cast_sub hbundleCardOne] at hrightScale
  have hidentity : (bundleCard : ℝ) - 1 +
      (r - 1) * ((bundleCard : ℝ) - 1) = ((bundleCard : ℝ) - 1) * r := by
    ring
  have hlargeCardLe : firstLarge ≤ bundleCard := by
    rw [← hfirstLarge]
    calc
      (largeChoreSet cost r first (allocation first)).card ≤ (allocation first).card :=
        Finset.card_le_card (largeChoreSet_subset_bundle cost r first (allocation first))
      _ = bundleCard := hfirstCard
  by_cases hlarge : IsLargeChore cost r first item
  · rw [largeChoreSet_erase_card_of_large cost r first (allocation first) item hitem hlarge,
      hcardErase, hfirstLarge]
    have hlargeMem : item ∈ largeChoreSet cost r first (allocation first) := by
      simp [largeChoreSet, hitem, hlarge]
    have hfirstLargeOne : 1 ≤ firstLarge := by
      have hpositive : 0 < (largeChoreSet cost r first (allocation first)).card :=
        Finset.card_pos.mpr ⟨item, hlargeMem⟩
      omega
    have hlargeSub : firstLarge - 1 ≤ bundleCard - 1 :=
      Nat.sub_le_sub_right hlargeCardLe 1
    have hlargeSubReal : ((firstLarge - 1 : ℕ) : ℝ) ≤ ((bundleCard - 1 : ℕ) : ℝ) := by
      exact_mod_cast hlargeSub
    have hlargeScale : (r - 1) * ((firstLarge - 1 : ℕ) : ℝ) ≤
        (r - 1) * ((bundleCard - 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hlargeSubReal hfactor
    rw [Nat.cast_sub hbundleCardOne, Nat.cast_sub hfirstLargeOne] at hlargeScale
    rw [Nat.cast_sub hbundleCardOne, Nat.cast_sub hfirstLargeOne]
    norm_num [nsmul_eq_mul]
    calc
      (bundleCard : ℝ) - 1 + (r - 1) * ((firstLarge : ℝ) - 1) ≤
          (bundleCard : ℝ) - 1 + (r - 1) * ((bundleCard : ℝ) - 1) :=
        by simpa using add_le_add_left hlargeScale ((bundleCard : ℝ) - 1)
      _ = ((bundleCard : ℝ) - 1) * r := hidentity
      _ ≤ (allocation second).card * r := by simpa using hrightScale
  · rw [largeChoreSet_erase_card_of_not_large cost r first (allocation first) item hlarge,
      hcardErase, hfirstLarge]
    have hlargeEraseLe : (largeChoreSet cost r first (allocation first \ {item})).card ≤
        (allocation first \ {item}).card :=
      Finset.card_le_card (largeChoreSet_subset_bundle cost r first
        (allocation first \ {item}))
    rw [largeChoreSet_erase_card_of_not_large cost r first (allocation first) item hlarge,
      hfirstLarge, hcardErase] at hlargeEraseLe
    have hlargeEraseLeReal : (firstLarge : ℝ) ≤ ((bundleCard - 1 : ℕ) : ℝ) := by
      exact_mod_cast hlargeEraseLe
    have hlargeScale : (r - 1) * (firstLarge : ℝ) ≤
        (r - 1) * ((bundleCard - 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hlargeEraseLeReal hfactor
    rw [Nat.cast_sub hbundleCardOne] at hlargeScale
    rw [Nat.cast_sub hbundleCardOne]
    norm_num [nsmul_eq_mul]
    calc
      (bundleCard : ℝ) - 1 + (r - 1) * (firstLarge : ℝ) ≤
          (bundleCard : ℝ) - 1 + (r - 1) * ((bundleCard : ℝ) - 1) :=
        by simpa using add_le_add_left hlargeScale ((bundleCard : ℝ) - 1)
      _ = ((bundleCard : ℝ) - 1) * r := hidentity
      _ ≤ (allocation second).card * r := by simpa using hrightScale

/-- The allocation induced by an item-owner map on a finite chore pool. -/
noncomputable def allocationOfOwner [DecidableEq Item]
    (chores : Finset Item) (owner : Item → Option Agent) : Allocation Agent Item := by
  classical
  exact fun agent => chores.filter fun item => owner item = some agent

/-- A total owner map induces a feasible allocation of precisely the chore pool. -/
theorem isAllocationOf_allocationOfOwner [DecidableEq Item]
    (chores : Finset Item) (owner : Item → Option Agent)
    (howner : ∀ item ∈ chores, ∃ agent, owner item = some agent) :
    IsAllocationOf (allocationOfOwner chores owner) chores := by
  constructor
  · intro agent item hitem
    have hfilter : item ∈ chores ∧ owner item = some agent := by
      simpa [allocationOfOwner] using hitem
    exact hfilter.1
  · intro item hitem
    obtain ⟨agent, hagent⟩ := howner item hitem
    refine ⟨agent, ?_, ?_⟩
    · simpa [allocationOfOwner, hagent]
    · intro other hother
      have hotherEq : owner item = some other := by
        have hfilter : item ∈ chores ∧ owner item = some other := by
          simpa [allocationOfOwner] using hother
        exact hfilter.2
      exact Option.some.inj (hotherEq.symm.trans hagent)

/-- Turn a partial owner map into a total owner map by giving every unassigned
item to a designated fallback agent. -/
def ownerWithFallback (fallback : Agent) (partialOwner : Item → Option Agent) : Item → Option Agent :=
  fun item => some (partialOwner item |>.getD fallback)

/-- Fallback completion always yields a feasible allocation of the supplied
finite chore pool. -/
theorem isAllocationOf_allocationOfOwnerWithFallback [DecidableEq Item]
    (chores : Finset Item) (fallback : Agent) (partialOwner : Item → Option Agent) :
    IsAllocationOf (allocationOfOwner chores (ownerWithFallback fallback partialOwner)) chores := by
  apply isAllocationOf_allocationOfOwner
  intro item _
  exact ⟨partialOwner item |>.getD fallback, rfl⟩

/-- Away from the fallback agent, a completed owner map has exactly the fibers
of the original partial owner map. -/
theorem allocationOfOwnerWithFallback_eq_partialFiber [DecidableEq Agent] [DecidableEq Item]
    (chores : Finset Item) (fallback agent : Agent) (partialOwner : Item → Option Agent)
    (hagent : agent ≠ fallback) :
    allocationOfOwner chores (ownerWithFallback fallback partialOwner) agent =
      chores.filter fun item => partialOwner item = some agent := by
  ext item
  simp only [allocationOfOwner, Finset.mem_filter]
  constructor
  · rintro ⟨hitem, howner⟩
    refine ⟨hitem, ?_⟩
    simp only [ownerWithFallback, Option.some.injEq] at howner
    cases hpartial : partialOwner item with
    | none =>
      have hfallback : fallback = agent := by simpa [hpartial] using howner
      exact (hagent hfallback.symm).elim
    | some owner => simpa [hpartial] using howner
  · rintro ⟨hitem, howner⟩
    refine ⟨hitem, ?_⟩
    simp only [ownerWithFallback, Option.some.injEq]
    cases hpartial : partialOwner item with
    | none => simp [hpartial] at howner
    | some owner => simpa [hpartial] using howner

/--
An owner-map allocation is EFX when each owner finds every assigned chore
small and the induced bundle sizes differ by at most one.
-/
theorem efxForChores_allocationOfOwner_of_small_balanced [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (chores : Finset Item)
    (owner : Item → Option Agent) (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hsmall : ∀ agent item, item ∈ chores → owner item = some agent →
      IsSmallChore cost agent item)
    (hcard : ∀ i j, (allocationOfOwner chores owner i).card ≤
      (allocationOfOwner chores owner j).card + 1) :
    EFXForChores (additiveChoreCost cost) (allocationOfOwner chores owner) := by
  apply efxForChores_of_all_owners_small_and_balanced_card cost r
    (allocationOfOwner chores owner) hcost hr ?_ hcard
  intro agent item hitem
  have hfilter : item ∈ chores ∧ owner item = some agent := by
    simpa [allocationOfOwner] using hitem
  exact hsmall agent item hfilter.1 hfilter.2

/-- If every agent assigns one constant nonnegative cost to every chore, then
any allocation whose bundle sizes differ by at most one is EFX.  This is useful
for homogeneous edge-type residues, where different agents may have different
constants but no agent distinguishes items within the residue. -/
theorem efxForChores_of_balanced_card_and_agentwise_constant [DecidableEq Item]
    (cost : ChoreCost Agent Item) (allocation : Allocation Agent Item) (value : Agent → ℝ)
    (hnonneg : ∀ agent, 0 ≤ value agent)
    (hconstant : ∀ agent owner item, item ∈ allocation owner → cost agent item = value agent)
    (hcard : ∀ first second, (allocation first).card ≤ (allocation second).card + 1) :
    EFXForChores (additiveChoreCost cost) allocation := by
  intro first second
  by_cases hempty : allocation first = ∅
  · exact Or.inl hempty
  · right
    intro item hitem
    rw [additiveChoreCost_erase cost first (allocation first) item hitem]
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost first (allocation first)
      (value first) (fun other hother => hconstant first first other hother)]
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost first (allocation second)
      (value first) (fun other hother => hconstant first second other hother)]
    rw [hconstant first first item hitem]
    simp only [nsmul_eq_mul]
    have hcard' : (allocation first).card ≤ (allocation second).card + 1 := hcard first second
    have hcardReal : ((allocation first).card : ℝ) ≤ (allocation second).card + 1 := by
      exact_mod_cast hcard'
    have hmul := mul_le_mul_of_nonneg_right hcardReal (hnonneg first)
    nlinarith

/-- A distinguished bundle of size `q` and other bundles of sizes `q` or
`q + 1` form an EFX allocation when every nondistinguished owner receives only
small chores, and every nondistinguished bundle is large for the distinguished
agent. This is the fairness calculation used in the singleton-deficiency M₂
construction. -/
theorem efxForChores_of_single_special_balanced_shape [DecidableEq Agent] [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (allocation : Allocation Agent Item)
    (special : Agent) (q : ℕ) (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hspecialCard : (allocation special).card = q)
    (hcardLower : ∀ agent, q ≤ (allocation agent).card)
    (hcardOtherUpper : ∀ agent, agent ≠ special → (allocation agent).card ≤ q + 1)
    (hotherSmall : ∀ agent item, agent ≠ special → item ∈ allocation agent →
      IsSmallChore cost agent item)
    (hotherLargeForSpecial : ∀ agent item, agent ≠ special → item ∈ allocation agent →
      IsLargeChore cost r special item) :
    EFXForChores (additiveChoreCost cost) allocation := by
  intro agent comparison
  by_cases hspecial : agent = special
  · subst agent
    by_cases hcomparison : comparison = special
    · subst comparison
      by_cases hempty : allocation special = ∅
      · exact Or.inl hempty
      · right
        intro item hitem
        rw [additiveChoreCost_erase cost special (allocation special) item hitem]
        have hnonneg := IsOneOrRChoreCost.nonneg cost r hcost (by linarith) special item
        linarith
    · by_cases hempty : allocation special = ∅
      · exact Or.inl hempty
      · right
        intro item hitem
        have hupper : additiveChoreCost cost special (allocation special \ {item}) ≤
            (allocation special \ {item}).card • r :=
          additiveChoreCost_le_card_nsmul_of_le cost special (allocation special \ {item}) r
            (fun other _ => IsOneOrRChoreCost.le_r cost r hcost hr special other)
        have heraseCard : (allocation special \ {item}).card = q - 1 := by
          rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem, hspecialCard]
        have hcomparisonConst : additiveChoreCost cost special (allocation comparison) =
            (allocation comparison).card • r :=
          additiveChoreCost_eq_card_nsmul_of_constant cost special (allocation comparison) r
            (fun other hother => hotherLargeForSpecial comparison other hcomparison hother)
        rw [hcomparisonConst]
        rw [heraseCard] at hupper
        have hqCard := hcardLower comparison
        have hqReal : (q : ℝ) ≤ (allocation comparison).card := by exact_mod_cast hqCard
        simp only [nsmul_eq_mul] at hupper ⊢
        have hrnonneg : 0 ≤ r := by linarith
        have hmult := mul_le_mul_of_nonneg_right hqReal hrnonneg
        have hqminusNat : q - 1 ≤ q := Nat.sub_le q 1
        have hqminus : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqminusNat
        nlinarith
  · right
    intro item hitem
    have hupper : additiveChoreCost cost agent (allocation agent \ {item}) ≤
        (allocation agent \ {item}).card • 1 :=
      additiveChoreCost_le_card_nsmul_of_le cost agent (allocation agent \ {item}) 1
        (fun other hother => by
          have hother' : other ∈ allocation agent ∧ other ≠ item := by simpa using hother
          have hsmall := hotherSmall agent other hspecial hother'.1
          simpa [IsSmallChore] using hsmall.le)
    have heraseCard : (allocation agent \ {item}).card = (allocation agent).card - 1 := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem]
    have hcardUpper := hcardOtherUpper agent hspecial
    have hcardEraseLe : (allocation agent \ {item}).card ≤ q := by
      rw [heraseCard]
      omega
    have hcomparisonLower : q • (1 : ℝ) ≤ additiveChoreCost cost agent (allocation comparison) := by
      calc
        q • (1 : ℝ) ≤ (allocation comparison).card • 1 := by
          exact nsmul_le_nsmul_left (by norm_num) (hcardLower comparison)
        _ ≤ additiveChoreCost cost agent (allocation comparison) :=
          card_nsmul_le_additiveChoreCost_of_le cost agent (allocation comparison) 1
            (fun other _ => IsOneOrRChoreCost.one_le cost r hcost hr agent other)
    calc
      additiveChoreCost cost agent (allocation agent \ {item}) ≤
          (allocation agent \ {item}).card • 1 := hupper
      _ ≤ q • 1 := nsmul_le_nsmul_left (by norm_num) hcardEraseLe
      _ ≤ additiveChoreCost cost agent (allocation comparison) := hcomparisonLower

/-- In the singleton-deficiency shape, if the distinguished agent receives
only large chores, her bundle is envy-free: each other bundle has at least as
many chores and all of them are large to her. -/
theorem envyFreeForChores_single_special_of_all_large [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (allocation : Allocation Agent Item)
    (special : Agent) (q : ℕ) (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hspecialCard : (allocation special).card = q)
    (hcardLower : ∀ agent, q ≤ (allocation agent).card)
    (hotherLargeForSpecial : ∀ agent item, agent ≠ special → item ∈ allocation agent →
      IsLargeChore cost r special item)
    (hspecialLarge : ∀ item ∈ allocation special, IsLargeChore cost r special item) :
    ∀ comparison, additiveChoreCost cost special (allocation special) ≤
      additiveChoreCost cost special (allocation comparison) := by
  intro comparison
  by_cases hcomparison : comparison = special
  · subst comparison
    exact le_rfl
  · have hspecialCost : additiveChoreCost cost special (allocation special) = q • r := by
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost special (allocation special) r
        hspecialLarge, hspecialCard]
    have hcomparisonCost : additiveChoreCost cost special (allocation comparison) =
        (allocation comparison).card • r := by
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost special (allocation comparison) r
        (fun item hitem => hotherLargeForSpecial comparison item hcomparison hitem)]
    rw [hspecialCost, hcomparisonCost]
    simp only [nsmul_eq_mul]
    have hcardReal : (q : ℝ) ≤ (allocation comparison).card := by
      exact_mod_cast hcardLower comparison
    exact mul_le_mul_of_nonneg_right hcardReal (by linarith)

/--
A total small-owner map with balanced induced bundle sizes yields a feasible
EFX allocation. This packages the all-small branch of an endpoint orientation.
-/
theorem exists_efx_allocation_of_total_small_owner_balanced [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (chores : Finset Item)
    (owner : Item → Option Agent) (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (howner : ∀ item ∈ chores, ∃ agent, owner item = some agent)
    (hsmall : ∀ agent item, item ∈ chores → owner item = some agent →
      IsSmallChore cost agent item)
    (hcard : ∀ i j, (allocationOfOwner chores owner i).card ≤
      (allocationOfOwner chores owner j).card + 1) :
    ∃ allocation : Allocation Agent Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  refine ⟨allocationOfOwner chores owner,
    isAllocationOf_allocationOfOwner chores owner howner, ?_⟩
  exact efxForChores_allocationOfOwner_of_small_balanced cost r chores owner hcost hr hsmall hcard

/-- The finite set of agents for whom a chore is small. -/
noncomputable def smallAgentSet [Fintype Agent] [DecidableEq Agent]
    (cost : ChoreCost Agent Item) (item : Item) : Finset Agent := by
  classical
  exact Finset.univ.filter fun agent => IsSmallChore cost agent item

/-- Relabelling agents maps the set of agents finding a chore small along the
inverse label equivalence. -/
theorem smallAgentSet_relabel [Fintype Agent] [DecidableEq Agent]
    {Agent' : Type*} [Fintype Agent'] [DecidableEq Agent']
    (labels : Agent' ≃ Agent) (cost : ChoreCost Agent Item) (item : Item) :
    smallAgentSet (relabelChoreCost labels cost) item =
      (smallAgentSet cost item).map labels.symm.toEmbedding := by
  ext agent
  simp [smallAgentSet, relabelChoreCost, IsSmallChore]

/-- A chore is small for at most one agent. -/
def IsSmallForAtMostOne [Fintype Agent] [DecidableEq Agent]
    (cost : ChoreCost Agent Item) (item : Item) : Prop :=
  (smallAgentSet cost item).card ≤ 1

/-- A chore is small for exactly two agents. -/
def IsSmallForExactlyTwo [Fintype Agent] [DecidableEq Agent]
    (cost : ChoreCost Agent Item) (item : Item) : Prop :=
  (smallAgentSet cost item).card = 2

/-- The at-most-one-small-agent condition is invariant under a bijective
relabelling of agents. -/
theorem IsSmallForAtMostOne.relabel [Fintype Agent] [DecidableEq Agent]
    {Agent' : Type*} [Fintype Agent'] [DecidableEq Agent']
    (labels : Agent' ≃ Agent) (cost : ChoreCost Agent Item) (item : Item)
    (hsmall : IsSmallForAtMostOne cost item) :
    IsSmallForAtMostOne (relabelChoreCost labels cost) item := by
  rw [IsSmallForAtMostOne, smallAgentSet_relabel]
  simpa [IsSmallForAtMostOne] using hsmall

/-- The exact-two-small-agents condition is invariant under a bijective
relabelling of agents. -/
theorem IsSmallForExactlyTwo.relabel [Fintype Agent] [DecidableEq Agent]
    {Agent' : Type*} [Fintype Agent'] [DecidableEq Agent']
    (labels : Agent' ≃ Agent) (cost : ChoreCost Agent Item) (item : Item)
    (hsmall : IsSmallForExactlyTwo cost item) :
    IsSmallForExactlyTwo (relabelChoreCost labels cost) item := by
  rw [IsSmallForExactlyTwo, smallAgentSet_relabel]
  simpa [IsSmallForExactlyTwo] using hsmall

/-- A chore is small for at least three agents. -/
def IsSmallForAtLeastThree [Fintype Agent] [DecidableEq Agent]
    (cost : ChoreCost Agent Item) (item : Item) : Prop :=
  3 ≤ (smallAgentSet cost item).card

/-- In the four-agent setting, a chore that is small for at least three agents
is small for every agent other than any fixed agent who finds it non-small. -/
theorem small_for_all_other_agents_of_atLeastThree
    {Item : Type*} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item) (item : Item)
    (hthree : IsSmallForAtLeastThree cost item) (agent : Fin 4)
    (hnotSmall : ¬ IsSmallChore cost agent item) :
    ∀ other : Fin 4, other ≠ agent → IsSmallChore cost other item := by
  intro other hother
  by_contra hnotOther
  have hsubset : smallAgentSet cost item ⊆
      ((Finset.univ : Finset (Fin 4)).erase agent).erase other := by
    intro candidate hcandidate
    simp only [smallAgentSet, Finset.mem_filter, Finset.mem_univ, true_and] at hcandidate
    simp only [Finset.mem_erase, Finset.mem_univ]
    constructor
    · intro hcandidateEq
      subst candidate
      exact hnotOther hcandidate
    · constructor
      · intro hcandidateEq
        subst candidate
        exact hnotSmall hcandidate
      · simp
  have hcard := Finset.card_le_card hsubset
  have hupper : (((Finset.univ : Finset (Fin 4)).erase agent).erase other).card = 2 := by
    have hotherMem : other ∈ (Finset.univ : Finset (Fin 4)).erase agent := by
      simp [hother]
    rw [Finset.card_erase_of_mem hotherMem]
    rw [Finset.card_erase_of_mem (Finset.mem_univ agent)]
    norm_num
  rw [hupper] at hcard
  change 3 ≤ (smallAgentSet cost item).card at hthree
  omega

/-- The chores from a finite set that are small for one fixed agent. -/
noncomputable def ownSmallChoreSet (cost : ChoreCost Agent Item)
    (chores : Finset Item) (agent : Agent) : Finset Item := by
  classical
  exact chores.filter fun item => IsSmallChore cost agent item

/-- A quota allocation is canonical when every agent receives exactly her quota
and as many own-small chores as that quota permits. This is the reusable core
of the canonical `M₀₁` allocation definition. -/
noncomputable def IsCanonicalSmallChoreAllocation [DecidableEq Item]
    (cost : ChoreCost Agent Item) (chores : Finset Item) (quota : Agent → ℕ)
    (allocation : Allocation Agent Item) : Prop :=
  IsAllocationOf allocation chores ∧
    ∀ agent,
      (allocation agent).card = quota agent ∧
        (ownSmallChoreSet cost (allocation agent) agent).card =
          min (quota agent) (ownSmallChoreSet cost chores agent).card

/-- A canonical chore allocation is super-canonical relative to specified
short and long agents when every short agent values her own bundle at least
`r` below every long-agent bundle.  The definition is deliberately generic:
the paper interface supplies the source's cardinality-based short/long sets. -/
noncomputable def IsSuperCanonicalSmallChoreAllocation [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost Agent Item) (chores : Finset Item)
    (shortAgents longAgents : Finset Agent) (quota : Agent → ℕ)
    (allocation : Allocation Agent Item) : Prop :=
  IsCanonicalSmallChoreAllocation cost chores quota allocation ∧
    ∀ shortAgent ∈ shortAgents, ∀ longAgent ∈ longAgents,
      additiveChoreCost cost shortAgent (allocation shortAgent) ≤
        additiveChoreCost cost shortAgent (allocation longAgent) - r

/-- Canonical small-chore allocations are invariant under a bijective
relabelling of agents, with the quota vector reindexed in the same way. -/
theorem IsCanonicalSmallChoreAllocation.relabel [DecidableEq Item]
    {Agent' : Type*} (labels : Agent' ≃ Agent) (cost : ChoreCost Agent Item)
    (chores : Finset Item) (quota : Agent → ℕ) (allocation : Allocation Agent Item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost chores quota allocation) :
    IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost) chores
      (relabelQuota labels quota) (relabelAllocation labels allocation) := by
  constructor
  · exact hcanonical.1.relabel labels
  · intro agent
    rcases hcanonical.2 (labels agent) with ⟨hcard, hsmall⟩
    constructor
    · simpa [relabelAllocation, relabelQuota] using hcard
    · have hset :
        ownSmallChoreSet (relabelChoreCost labels cost)
            (relabelAllocation labels allocation agent) agent =
          ownSmallChoreSet cost (allocation (labels agent)) (labels agent) := by
        ext item
        simp [ownSmallChoreSet, relabelAllocation, relabelChoreCost, IsSmallChore]
      have hwhole :
          ownSmallChoreSet (relabelChoreCost labels cost) chores agent =
            ownSmallChoreSet cost chores (labels agent) := by
        ext item
        simp [ownSmallChoreSet, relabelChoreCost, IsSmallChore]
      rw [hset, hwhole]
      simpa [relabelQuota] using hsmall

/-- Own-small chore sets are monotone in the ambient chore set. -/
theorem ownSmallChoreSet_subset (cost : ChoreCost Agent Item)
    (agent : Agent) {left right : Finset Item} (hsubset : left ⊆ right) :
    ownSmallChoreSet cost left agent ⊆ ownSmallChoreSet cost right agent := by
  intro item hitem
  simp only [ownSmallChoreSet, Finset.mem_filter] at hitem ⊢
  exact ⟨hsubset hitem.1, hitem.2⟩

/-- Equal cardinality upgrades inclusion of own-small chore sets to equality. -/
theorem ownSmallChoreSet_eq_of_subset_and_card (cost : ChoreCost Agent Item)
    (agent : Agent) {left right : Finset Item} (hsubset : left ⊆ right)
    (hcard : (ownSmallChoreSet cost left agent).card =
      (ownSmallChoreSet cost right agent).card) :
    ownSmallChoreSet cost left agent = ownSmallChoreSet cost right agent := by
  apply Finset.eq_of_subset_of_card_le (ownSmallChoreSet_subset cost agent hsubset)
  simp [hcard]

/-- The feasibility component of a canonical quota allocation. -/
theorem IsCanonicalSmallChoreAllocation.isAllocationOf [DecidableEq Item]
    {cost : ChoreCost Agent Item} {chores : Finset Item} {quota : Agent → ℕ}
    {allocation : Allocation Agent Item}
    (hcanonical : IsCanonicalSmallChoreAllocation cost chores quota allocation) :
    IsAllocationOf allocation chores :=
  hcanonical.1

/-- Pairwise-disjoint bundles whose union is a finite chore pool form a
feasible allocation of that pool. -/
theorem isAllocationOf_of_pairwiseDisjoint_biUnion [Fintype Agent] [DecidableEq Item]
    (allocation : Allocation Agent Item) (chores : Finset Item)
    (hdisjoint : ((Finset.univ : Finset Agent) : Set Agent).PairwiseDisjoint allocation)
    (hunion : (Finset.univ : Finset Agent).biUnion allocation = chores) :
    IsAllocationOf allocation chores := by
  constructor
  · intro agent item hitem
    rw [← hunion]
    exact Finset.mem_biUnion.mpr ⟨agent, Finset.mem_univ _, hitem⟩
  · intro item hitem
    rw [← hunion] at hitem
    obtain ⟨agent, _, hagent⟩ := Finset.mem_biUnion.mp hitem
    refine ⟨agent, hagent, ?_⟩
    intro other hother
    by_cases hEq : other = agent
    · exact hEq
    · exact False.elim ((Finset.disjoint_left.mp
        (hdisjoint (Finset.mem_univ other) (Finset.mem_univ agent) hEq)) hother hagent)

/-- A canonical quota allocation is EFX when normalized costs are `1` or `r`
and quotas differ by at most one. This is the reusable core of the canonical
allocation argument for normalized bi-valued chore instances. -/
theorem IsCanonicalSmallChoreAllocation.efxForChores [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (chores : Finset Item)
    (quota : Agent → ℕ) (allocation : Allocation Agent Item)
    (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hquota : ∀ i j, quota i ≤ quota j + 1)
    (hcanonical : IsCanonicalSmallChoreAllocation cost chores quota allocation) :
    EFXForChores (additiveChoreCost cost) allocation := by
  intro i j
  by_cases hi : allocation i = ∅
  · exact Or.inl hi
  · right
    intro item hitem
    by_cases hij : i = j
    · subst j
      rw [additiveChoreCost_erase cost i (allocation i) item hitem]
      have hnonneg : 0 ≤ cost i item :=
        IsOneOrRChoreCost.nonneg cost r hcost (by linarith) i item
      linarith
    · rcases hcanonical.2 i with ⟨hcardI, hsmallI⟩
      rcases hcanonical.2 j with ⟨hcardJ, hsmallJ⟩
      have hquotaReal : (quota i : ℝ) - 1 ≤ quota j := by
        have hquotaCast : (quota i : ℝ) ≤ (quota j : ℝ) + 1 := by
          exact_mod_cast hquota i j
        linarith
      have hcardErase : (allocation i \ {item}).card = quota i - 1 := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem, hcardI]
      have hcardLe : (allocation i \ {item}).card ≤ (allocation j).card := by
        calc
          (allocation i \ {item}).card = quota i - 1 := hcardErase
          _ ≤ quota j := Nat.sub_le_iff_le_add.mpr (hquota i j)
          _ = (allocation j).card := hcardJ.symm
      have hcardLeReal : ((allocation i \ {item}).card : ℝ) ≤ (allocation j).card := by
        exact_mod_cast hcardLe
      by_cases hsmallEnough : quota i ≤ (ownSmallChoreSet cost chores i).card
      · have hsmallCard : (ownSmallChoreSet cost (allocation i) i).card = quota i := by
          rw [hsmallI, Nat.min_eq_left hsmallEnough]
        have hsmallSubset : ownSmallChoreSet cost (allocation i) i ⊆ allocation i := by
          intro x hx
          have hx' : x ∈ allocation i ∧ IsSmallChore cost i x := by
            simpa only [ownSmallChoreSet, Finset.mem_filter] using hx
          exact hx'.1
        have hsmallEq : ownSmallChoreSet cost (allocation i) i = allocation i := by
          apply Finset.eq_of_subset_of_card_le hsmallSubset
          rw [hsmallCard, hcardI]
        have hownSmall : ∀ x ∈ allocation i, cost i x = 1 := by
          intro x hx
          have hxsmall : x ∈ ownSmallChoreSet cost (allocation i) i := by
            rw [hsmallEq]
            exact hx
          have hxsmall' : x ∈ allocation i ∧ IsSmallChore cost i x := by
            simpa only [ownSmallChoreSet, Finset.mem_filter] using hxsmall
          exact hxsmall'.2
        have hremovedConst : ∀ x ∈ allocation i \ {item}, cost i x = 1 := by
          intro x hx
          exact hownSmall x (Finset.sdiff_subset hx)
        have hleft :
            additiveChoreCost cost i (allocation i \ {item}) =
              (allocation i \ {item}).card • (1 : ℝ) :=
          additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation i \ {item}) 1
            hremovedConst
        have hright : (allocation j).card • (1 : ℝ) ≤
            additiveChoreCost cost i (allocation j) :=
          card_nsmul_le_additiveChoreCost_of_le cost i (allocation j) 1
            (fun x hx => IsOneOrRChoreCost.one_le cost r hcost hr i x)
        rw [hleft]
        norm_num [nsmul_eq_mul]
        norm_num [nsmul_eq_mul] at hright
        linarith
      · have hsmallLess : (ownSmallChoreSet cost chores i).card < quota i :=
          Nat.lt_of_not_ge hsmallEnough
        have hsmallCard :
            (ownSmallChoreSet cost (allocation i) i).card =
              (ownSmallChoreSet cost chores i).card := by
          rw [hsmallI, Nat.min_eq_right hsmallLess.le]
        have hallocationI : allocation i ⊆ chores := by
          intro x hx
          exact hcanonical.1.1 i x hx
        have hsmallEq :
            ownSmallChoreSet cost (allocation i) i =
              ownSmallChoreSet cost chores i :=
          ownSmallChoreSet_eq_of_subset_and_card cost i hallocationI hsmallCard
        have hotherLarge : ∀ x ∈ allocation j, cost i x = r := by
          intro x hx
          rcases hcost i x with hsmall | hlarge
          · exfalso
            have hxchore : x ∈ chores := hcanonical.1.1 j x hx
            have hxsmallChores : x ∈ ownSmallChoreSet cost chores i := by
              have hx' : x ∈ chores ∧ IsSmallChore cost i x := ⟨hxchore, hsmall⟩
              simpa only [ownSmallChoreSet, Finset.mem_filter] using hx'
            have hxsmallI : x ∈ ownSmallChoreSet cost (allocation i) i := by
              rw [hsmallEq]
              exact hxsmallChores
            have hxallocationI : x ∈ allocation i := by
              have hxsmallI' : x ∈ allocation i ∧ IsSmallChore cost i x := by
                simpa only [ownSmallChoreSet, Finset.mem_filter] using hxsmallI
              exact hxsmallI'.1
            exact hij (isAllocationOf_owner_unique hcanonical.1 hxchore hxallocationI hx)
          · exact hlarge
        have hright : additiveChoreCost cost i (allocation j) =
            (allocation j).card • r :=
          additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation j) r hotherLarge
        by_cases hsmallZero : (ownSmallChoreSet cost chores i).card = 0
        · have hsmallEmpty : ownSmallChoreSet cost chores i = ∅ :=
            Finset.card_eq_zero.mp hsmallZero
          have hownLarge : ∀ x ∈ allocation i, cost i x = r := by
            intro x hx
            rcases hcost i x with hsmall | hlarge
            · exfalso
              have hxchore : x ∈ chores := hcanonical.1.1 i x hx
              have hxsmall : x ∈ ownSmallChoreSet cost chores i := by
                have hx' : x ∈ chores ∧ IsSmallChore cost i x := ⟨hxchore, hsmall⟩
                simpa only [ownSmallChoreSet, Finset.mem_filter] using hx'
              rw [hsmallEmpty] at hxsmall
              have hnotmem : x ∉ (∅ : Finset Item) := by simp
              exact hnotmem hxsmall
            · exact hlarge
          have hremovedLarge : ∀ x ∈ allocation i \ {item}, cost i x = r := by
            intro x hx
            exact hownLarge x (Finset.sdiff_subset hx)
          have hleft : additiveChoreCost cost i (allocation i \ {item}) =
              (allocation i \ {item}).card • r :=
            additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation i \ {item}) r
              hremovedLarge
          rw [hleft, hright]
          simpa only [nsmul_eq_mul] using
            mul_le_mul_of_nonneg_right hcardLeReal (by linarith)
        · have hsmallPiPos : 0 < (ownSmallChoreSet cost (allocation i) i).card := by
            rw [hsmallEq]
            exact Nat.pos_of_ne_zero hsmallZero
          rcases Finset.card_pos.mp hsmallPiPos with ⟨smallItem, hsmallItem⟩
          have hsmallCost : cost i smallItem = 1 := by
            have hsmallItem' : smallItem ∈ allocation i ∧ IsSmallChore cost i smallItem := by
              simpa only [ownSmallChoreSet, Finset.mem_filter] using hsmallItem
            exact hsmallItem'.2
          have hsmallAllocation : smallItem ∈ allocation i := by
            have hsmallItem' : smallItem ∈ allocation i ∧ IsSmallChore cost i smallItem := by
              simpa only [ownSmallChoreSet, Finset.mem_filter] using hsmallItem
            exact hsmallItem'.1
          have hremoveItem : additiveChoreCost cost i (allocation i \ {item}) =
              additiveChoreCost cost i (allocation i) - cost i item :=
            additiveChoreCost_erase cost i (allocation i) item hitem
          have hremoveSmall : additiveChoreCost cost i (allocation i \ {smallItem}) =
              additiveChoreCost cost i (allocation i) - 1 := by
            rw [additiveChoreCost_erase cost i (allocation i) smallItem hsmallAllocation]
            rw [hsmallCost]
          have hitemOne : 1 ≤ cost i item :=
            IsOneOrRChoreCost.one_le cost r hcost hr i item
          have hleftLe : additiveChoreCost cost i (allocation i \ {item}) ≤
              additiveChoreCost cost i (allocation i \ {smallItem}) := by
            rw [hremoveItem, hremoveSmall]
            linarith
          have hsmallUpper : additiveChoreCost cost i (allocation i \ {smallItem}) ≤
              (allocation i \ {smallItem}).card • r :=
            additiveChoreCost_le_card_nsmul_of_le cost i (allocation i \ {smallItem}) r
              (fun x hx => IsOneOrRChoreCost.le_r cost r hcost hr i x)
          have hsmallEraseCard : (allocation i \ {smallItem}).card = quota i - 1 := by
            rw [Finset.sdiff_singleton_eq_erase,
              Finset.card_erase_of_mem hsmallAllocation, hcardI]
          have hquotaSub : quota i - 1 ≤ quota j :=
            Nat.sub_le_iff_le_add.mpr (hquota i j)
          have hquotaSubReal : ((quota i - 1 : ℕ) : ℝ) ≤ quota j := by
            exact_mod_cast hquotaSub
          have hrnonneg : (0 : ℝ) ≤ r := by linarith
          calc
            additiveChoreCost cost i (allocation i \ {item}) ≤
                additiveChoreCost cost i (allocation i \ {smallItem}) := hleftLe
            _ ≤ (allocation i \ {smallItem}).card • r := hsmallUpper
            _ = (quota i - 1) • r := by rw [hsmallEraseCard]
            _ ≤ quota j • r := by
              simpa only [nsmul_eq_mul] using
                mul_le_mul_of_nonneg_right hquotaSubReal hrnonneg
            _ = (allocation j).card • r := by rw [hcardJ]
            _ = additiveChoreCost cost i (allocation j) := hright.symm

/-- If all canonical quotas are equal, the same allocation is envy-free. -/
theorem IsCanonicalSmallChoreAllocation.envyFreeForChores [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (chores : Finset Item)
    (quota : Agent → ℕ) (allocation : Allocation Agent Item) (commonQuota : ℕ)
    (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hquota : ∀ agent, quota agent = commonQuota)
    (hcanonical : IsCanonicalSmallChoreAllocation cost chores quota allocation) :
    EnvyFreeForChores (additiveChoreCost cost) allocation := by
  intro i j
  by_cases hij : i = j
  · subst j
    exact le_rfl
  · rcases hcanonical.2 i with ⟨hcardI, hsmallI⟩
    rcases hcanonical.2 j with ⟨hcardJ, hsmallJ⟩
    have hcardEq : (allocation i).card = (allocation j).card := by
      rw [hcardI, hcardJ, hquota i, hquota j]
    by_cases hsmallEnough : quota i ≤ (ownSmallChoreSet cost chores i).card
    · have hsmallCard : (ownSmallChoreSet cost (allocation i) i).card = quota i := by
        rw [hsmallI, Nat.min_eq_left hsmallEnough]
      have hsmallSubset : ownSmallChoreSet cost (allocation i) i ⊆ allocation i := by
        intro x hx
        have hx' : x ∈ allocation i ∧ IsSmallChore cost i x := by
          simpa only [ownSmallChoreSet, Finset.mem_filter] using hx
        exact hx'.1
      have hsmallEq : ownSmallChoreSet cost (allocation i) i = allocation i := by
        apply Finset.eq_of_subset_of_card_le hsmallSubset
        rw [hsmallCard, hcardI]
      have hownSmall : ∀ x ∈ allocation i, cost i x = 1 := by
        intro x hx
        have hxsmall : x ∈ ownSmallChoreSet cost (allocation i) i := by
          rw [hsmallEq]
          exact hx
        have hxsmall' : x ∈ allocation i ∧ IsSmallChore cost i x := by
          simpa only [ownSmallChoreSet, Finset.mem_filter] using hxsmall
        exact hxsmall'.2
      have hleft : additiveChoreCost cost i (allocation i) =
          (allocation i).card • (1 : ℝ) :=
        additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation i) 1 hownSmall
      have hright : (allocation j).card • (1 : ℝ) ≤
          additiveChoreCost cost i (allocation j) :=
        card_nsmul_le_additiveChoreCost_of_le cost i (allocation j) 1
          (fun x hx => IsOneOrRChoreCost.one_le cost r hcost hr i x)
      rw [hleft]
      norm_num [nsmul_eq_mul]
      norm_num [nsmul_eq_mul] at hright
      have hcardEqReal : ((allocation i).card : ℝ) = (allocation j).card := by
        exact_mod_cast hcardEq
      linarith
    · have hsmallLess : (ownSmallChoreSet cost chores i).card < quota i :=
        Nat.lt_of_not_ge hsmallEnough
      have hsmallCard :
          (ownSmallChoreSet cost (allocation i) i).card =
            (ownSmallChoreSet cost chores i).card := by
        rw [hsmallI, Nat.min_eq_right hsmallLess.le]
      have hallocationI : allocation i ⊆ chores := by
        intro x hx
        exact hcanonical.1.1 i x hx
      have hsmallEq :
          ownSmallChoreSet cost (allocation i) i =
            ownSmallChoreSet cost chores i :=
        ownSmallChoreSet_eq_of_subset_and_card cost i hallocationI hsmallCard
      have hotherLarge : ∀ x ∈ allocation j, cost i x = r := by
        intro x hx
        rcases hcost i x with hsmall | hlarge
        · exfalso
          have hxchore : x ∈ chores := hcanonical.1.1 j x hx
          have hxsmallChores : x ∈ ownSmallChoreSet cost chores i := by
            have hx' : x ∈ chores ∧ IsSmallChore cost i x := ⟨hxchore, hsmall⟩
            simpa only [ownSmallChoreSet, Finset.mem_filter] using hx'
          have hxsmallI : x ∈ ownSmallChoreSet cost (allocation i) i := by
            rw [hsmallEq]
            exact hxsmallChores
          have hxallocationI : x ∈ allocation i := by
            have hxsmallI' : x ∈ allocation i ∧ IsSmallChore cost i x := by
              simpa only [ownSmallChoreSet, Finset.mem_filter] using hxsmallI
            exact hxsmallI'.1
          exact hij (isAllocationOf_owner_unique hcanonical.1 hxchore hxallocationI hx)
        · exact hlarge
      have hleft : additiveChoreCost cost i (allocation i) ≤ (allocation i).card • r :=
        additiveChoreCost_le_card_nsmul_of_le cost i (allocation i) r
          (fun x hx => IsOneOrRChoreCost.le_r cost r hcost hr i x)
      have hright : additiveChoreCost cost i (allocation j) =
          (allocation j).card • r :=
        additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation j) r hotherLarge
      rw [hright]
      rw [← hcardEq]
      exact hleft

/-- Two canonical bundles with the same quota are envy-free in the cost
direction.  This pairwise form is useful when a later gap filling changes the
other bundles while leaving equal-quota prefix comparisons unchanged. -/
theorem IsCanonicalSmallChoreAllocation.envyFreeForChores_of_quota_eq [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (chores : Finset Item)
    (quota : Agent → ℕ) (allocation : Allocation Agent Item)
    (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hcanonical : IsCanonicalSmallChoreAllocation cost chores quota allocation)
    (i j : Agent) (hquotaEq : quota i = quota j) :
    additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j) := by
  by_cases hij : i = j
  · subst j
    exact le_rfl
  · rcases hcanonical.2 i with ⟨hcardI, hsmallI⟩
    rcases hcanonical.2 j with ⟨hcardJ, _hsmallJ⟩
    have hcardEq : (allocation i).card = (allocation j).card := by
      rw [hcardI, hcardJ, hquotaEq]
    by_cases hsmallEnough : quota i ≤ (ownSmallChoreSet cost chores i).card
    · have hsmallCard : (ownSmallChoreSet cost (allocation i) i).card = quota i := by
        rw [hsmallI, Nat.min_eq_left hsmallEnough]
      have hsmallSubset : ownSmallChoreSet cost (allocation i) i ⊆ allocation i := by
        intro x hx
        exact (by simpa [ownSmallChoreSet] using hx :
          x ∈ allocation i ∧ IsSmallChore cost i x).1
      have hsmallEq : ownSmallChoreSet cost (allocation i) i = allocation i := by
        apply Finset.eq_of_subset_of_card_le hsmallSubset
        rw [hsmallCard, hcardI]
      have hownSmall : ∀ x ∈ allocation i, cost i x = 1 := by
        intro x hx
        have hxsmall : x ∈ ownSmallChoreSet cost (allocation i) i := by
          rw [hsmallEq]
          exact hx
        exact (by simpa [ownSmallChoreSet] using hxsmall :
          x ∈ allocation i ∧ IsSmallChore cost i x).2
      have hleft : additiveChoreCost cost i (allocation i) =
          (allocation i).card • (1 : ℝ) :=
        additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation i) 1 hownSmall
      have hright : (allocation j).card • (1 : ℝ) ≤
          additiveChoreCost cost i (allocation j) :=
        card_nsmul_le_additiveChoreCost_of_le cost i (allocation j) 1
          (fun x hx => IsOneOrRChoreCost.one_le cost r hcost hr i x)
      rw [hleft]
      norm_num [nsmul_eq_mul]
      norm_num [nsmul_eq_mul] at hright
      have hcardEqReal : ((allocation i).card : ℝ) = (allocation j).card := by
        exact_mod_cast hcardEq
      linarith
    · have hsmallLess : (ownSmallChoreSet cost chores i).card < quota i :=
        Nat.lt_of_not_ge hsmallEnough
      have hsmallCard :
          (ownSmallChoreSet cost (allocation i) i).card =
            (ownSmallChoreSet cost chores i).card := by
        rw [hsmallI, Nat.min_eq_right hsmallLess.le]
      have hallocationI : allocation i ⊆ chores := by
        intro x hx
        exact hcanonical.1.1 i x hx
      have hsmallEq : ownSmallChoreSet cost (allocation i) i =
          ownSmallChoreSet cost chores i :=
        ownSmallChoreSet_eq_of_subset_and_card cost i hallocationI hsmallCard
      have hotherLarge : ∀ x ∈ allocation j, cost i x = r := by
        intro x hx
        rcases hcost i x with hsmall | hlarge
        · exfalso
          have hxchore : x ∈ chores := hcanonical.1.1 j x hx
          have hxsmallChores : x ∈ ownSmallChoreSet cost chores i := by
            simpa [ownSmallChoreSet] using ⟨hxchore, hsmall⟩
          have hxsmallI : x ∈ ownSmallChoreSet cost (allocation i) i := by
            rw [hsmallEq]
            exact hxsmallChores
          have hxallocationI : x ∈ allocation i :=
            (by simpa [ownSmallChoreSet] using hxsmallI :
              x ∈ allocation i ∧ IsSmallChore cost i x).1
          exact hij (isAllocationOf_owner_unique hcanonical.1 hxchore hxallocationI hx)
        · exact hlarge
      have hleft : additiveChoreCost cost i (allocation i) ≤ (allocation i).card • r :=
        additiveChoreCost_le_card_nsmul_of_le cost i (allocation i) r
          (fun x hx => IsOneOrRChoreCost.le_r cost r hcost hr i x)
      have hright : additiveChoreCost cost i (allocation j) =
          (allocation j).card • r :=
        additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation j) r hotherLarge
      rw [hright, ← hcardEq]
      exact hleft

/-- A canonical bundle with one fewer chore remains no more costly after one
additional small chore than a canonical bundle with the successor quota.  This
is the one-small-item balance used when gap filling is assigned to a short
canonical agent. -/
theorem IsCanonicalSmallChoreAllocation.additive_add_one_le_of_quota_succ
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (chores : Finset Item)
    (quota : Agent → ℕ) (allocation : Allocation Agent Item)
    (hcost : IsOneOrRChoreCost cost r) (hr : 1 ≤ r)
    (hcanonical : IsCanonicalSmallChoreAllocation cost chores quota allocation)
    (i j : Agent) (hquota : quota j = quota i + 1) :
    additiveChoreCost cost i (allocation i) + 1 ≤
      additiveChoreCost cost i (allocation j) := by
  classical
  rcases hcanonical.2 i with ⟨hcardI, hsmallI⟩
  rcases hcanonical.2 j with ⟨hcardJ, _hsmallJ⟩
  have hij : i ≠ j := by
    intro heq
    subst j
    omega
  have hcardSucc : (allocation j).card = (allocation i).card + 1 := by
    rw [hcardI, hcardJ, hquota]
  by_cases hsmallEnough : quota i ≤ (ownSmallChoreSet cost chores i).card
  · have hsmallCard : (ownSmallChoreSet cost (allocation i) i).card = quota i := by
      rw [hsmallI, Nat.min_eq_left hsmallEnough]
    have hsmallSubset : ownSmallChoreSet cost (allocation i) i ⊆ allocation i := by
      intro item hitem
      exact (Finset.mem_filter.mp hitem).1
    have hsmallEq : ownSmallChoreSet cost (allocation i) i = allocation i := by
      apply Finset.eq_of_subset_of_card_le hsmallSubset
      rw [hsmallCard, hcardI]
    have hownSmall : ∀ item ∈ allocation i, cost i item = 1 := by
      intro item hitem
      have hmem : item ∈ ownSmallChoreSet cost (allocation i) i := by
        rw [hsmallEq]
        exact hitem
      exact (by simpa [ownSmallChoreSet] using hmem :
        item ∈ allocation i ∧ IsSmallChore cost i item).2
    have hleft : additiveChoreCost cost i (allocation i) =
        (allocation i).card • (1 : ℝ) :=
      additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation i) 1 hownSmall
    have hright : (allocation j).card • (1 : ℝ) ≤
        additiveChoreCost cost i (allocation j) :=
      card_nsmul_le_additiveChoreCost_of_le cost i (allocation j) 1
        (fun item hitem => IsOneOrRChoreCost.one_le cost r hcost hr i item)
    rw [hleft]
    norm_num [nsmul_eq_mul]
    norm_num [nsmul_eq_mul] at hright
    have hcardSuccReal : ((allocation j).card : ℝ) = (allocation i).card + 1 := by
      exact_mod_cast hcardSucc
    linarith
  · have hsmallLess : (ownSmallChoreSet cost chores i).card < quota i :=
      Nat.lt_of_not_ge hsmallEnough
    have hsmallCard :
        (ownSmallChoreSet cost (allocation i) i).card =
          (ownSmallChoreSet cost chores i).card := by
      rw [hsmallI, Nat.min_eq_right hsmallLess.le]
    have hallocationI : allocation i ⊆ chores := by
      intro item hitem
      exact hcanonical.1.1 i item hitem
    have hsmallEq : ownSmallChoreSet cost (allocation i) i =
        ownSmallChoreSet cost chores i :=
      ownSmallChoreSet_eq_of_subset_and_card cost i hallocationI hsmallCard
    have hotherLarge : ∀ item ∈ allocation j, cost i item = r := by
      intro item hitem
      rcases hcost i item with hsmall | hlarge
      · exfalso
        have hchore : item ∈ chores := hcanonical.1.1 j item hitem
        have hsmallChores : item ∈ ownSmallChoreSet cost chores i := by
          simpa [ownSmallChoreSet] using ⟨hchore, hsmall⟩
        have hsmallI : item ∈ ownSmallChoreSet cost (allocation i) i := by
          rw [hsmallEq]
          exact hsmallChores
        have hallocationI : item ∈ allocation i :=
          (by simpa [ownSmallChoreSet] using hsmallI :
            item ∈ allocation i ∧ IsSmallChore cost i item).1
        exact hij (isAllocationOf_owner_unique hcanonical.1 hchore hallocationI hitem)
      · exact hlarge
    have hleft : additiveChoreCost cost i (allocation i) ≤ (allocation i).card • r :=
      additiveChoreCost_le_card_nsmul_of_le cost i (allocation i) r
        (fun item hitem => IsOneOrRChoreCost.le_r cost r hcost hr i item)
    have hright : additiveChoreCost cost i (allocation j) = (allocation j).card • r :=
      additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation j) r hotherLarge
    rw [hright]
    simp only [nsmul_eq_mul]
    have hcardSuccReal : ((allocation j).card : ℝ) = (allocation i).card + 1 := by
      exact_mod_cast hcardSucc
    have hrnonneg : 0 ≤ r := by linarith
    have hcardnonneg : 0 ≤ ((allocation i).card : ℝ) := by positivity
    rw [nsmul_eq_mul] at hleft
    nlinarith

/-- Equal-quota canonical bundles enjoy an `r - 1` cross-cost advantage when
both owners receive an own-small chore.  This is the quantitative canonical
invariant used when a later allocation has to replace a unit EFX removal by a
large-chore removal. -/
theorem IsCanonicalSmallChoreAllocation.cross_cost_advantage_of_ownSmall
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Item]
    (cost : ChoreCost Agent Item) (r : ℝ) (chores : Finset Item)
    (quota : Agent → ℕ) (allocation : Allocation Agent Item)
    (hcost : IsOneOrRChoreCost cost r) (hr : 1 < r)
    (hatMostOne : ∀ item ∈ chores, IsSmallForAtMostOne cost item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost chores quota allocation)
    (i j : Agent) (hij : i ≠ j) (hquota : quota i = quota j)
    (hiSmall : ∃ item ∈ allocation i, IsSmallChore cost i item)
    (hjSmall : ∃ item ∈ allocation j, IsSmallChore cost j item) :
    additiveChoreCost cost i (allocation i) + (r - 1) ≤
      additiveChoreCost cost i (allocation j) := by
  classical
  rcases hcanonical.2 i with ⟨hcardI, hsmallI⟩
  rcases hcanonical.2 j with ⟨hcardJ, hsmallJ⟩
  have hcardEq : (allocation i).card = (allocation j).card := by
    rw [hcardI, hcardJ, hquota]
  have hcardEqReal : ((allocation i).card : ℝ) = (allocation j).card := by
    exact_mod_cast hcardEq
  by_cases hsmallEnough : quota i ≤ (ownSmallChoreSet cost chores i).card
  · have hsmallCard : (ownSmallChoreSet cost (allocation i) i).card = quota i := by
      rw [hsmallI, Nat.min_eq_left hsmallEnough]
    have hsmallSubset : ownSmallChoreSet cost (allocation i) i ⊆ allocation i := by
      intro item hitem
      exact (Finset.mem_filter.mp hitem).1
    have hsmallEq : ownSmallChoreSet cost (allocation i) i = allocation i := by
      apply Finset.eq_of_subset_of_card_le hsmallSubset
      rw [hsmallCard, hcardI]
    have hownSmall : ∀ item ∈ allocation i, cost i item = 1 := by
      intro item hitem
      have hmem : item ∈ ownSmallChoreSet cost (allocation i) i := by
        rw [hsmallEq]
        exact hitem
      exact (Finset.mem_filter.mp hmem).2
    have hleft : additiveChoreCost cost i (allocation i) =
        (allocation i).card • (1 : ℝ) :=
      additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation i) 1 hownSmall
    obtain ⟨smallItem, hsmallItem, hsmallForJ⟩ := hjSmall
    have hnotSmallForI : ¬ IsSmallChore cost i smallItem := by
      intro hsmallForI
      have hsubset : ({i, j} : Finset Agent) ⊆ smallAgentSet cost smallItem := by
        intro agent hagent
        simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
        rcases hagent with rfl | rfl
        · simpa [smallAgentSet] using hsmallForI
        · simpa [smallAgentSet] using hsmallForJ
      have hcard := Finset.card_le_card hsubset
      have hsmallCard := hatMostOne smallItem (hcanonical.1.1 j smallItem hsmallItem)
      change (smallAgentSet cost smallItem).card ≤ 1 at hsmallCard
      have hpairCard : ({i, j} : Finset Agent).card = 2 := by simp [hij]
      omega
    have hlargeForI : IsLargeChore cost r i smallItem := by
      rcases hcost i smallItem with hsmall | hlarge
      · exact (hnotSmallForI (by simpa [IsSmallChore] using hsmall)).elim
      · simpa [IsLargeChore] using hlarge
    have hlargeMem : smallItem ∈ largeChoreSet cost r i (allocation j) := by
      simpa [largeChoreSet] using And.intro hsmallItem hlargeForI
    have hlargePos : 0 < (largeChoreSet cost r i (allocation j)).card :=
      Finset.card_pos.mpr ⟨smallItem, hlargeMem⟩
    have hlargeReal : (1 : ℝ) ≤ (largeChoreSet cost r i (allocation j)).card := by
      exact_mod_cast hlargePos
    have hright : ((allocation i).card : ℝ) + (r - 1) ≤
        additiveChoreCost cost i (allocation j) := by
      rw [additiveChoreCost_eq_card_add_largeCard cost r i (allocation j) hcost]
      nlinarith [mul_le_mul_of_nonneg_left hlargeReal (by linarith : 0 ≤ r - 1)]
    rw [hleft]
    norm_num [nsmul_eq_mul]
    linarith
  · have hsmallLess : (ownSmallChoreSet cost chores i).card < quota i :=
      Nat.lt_of_not_ge hsmallEnough
    have hsmallCard :
        (ownSmallChoreSet cost (allocation i) i).card =
          (ownSmallChoreSet cost chores i).card := by
      rw [hsmallI, Nat.min_eq_right hsmallLess.le]
    have hallocationI : allocation i ⊆ chores := by
      intro item hitem
      exact hcanonical.1.1 i item hitem
    have hsmallEq :
        ownSmallChoreSet cost (allocation i) i = ownSmallChoreSet cost chores i :=
      ownSmallChoreSet_eq_of_subset_and_card cost i hallocationI hsmallCard
    have hotherLarge : ∀ item ∈ allocation j, cost i item = r := by
      intro item hitem
      rcases hcost i item with hsmall | hlarge
      · exfalso
        have hitemChores : item ∈ chores := hcanonical.1.1 j item hitem
        have hsmallChores : item ∈ ownSmallChoreSet cost chores i := by
          simpa [ownSmallChoreSet, IsSmallChore] using And.intro hitemChores hsmall
        have hsmallI : item ∈ ownSmallChoreSet cost (allocation i) i := by
          rw [hsmallEq]
          exact hsmallChores
        have hitemI : item ∈ allocation i :=
          (Finset.mem_filter.mp hsmallI).1
        exact hij (isAllocationOf_owner_unique hcanonical.1 hitemChores hitemI hitem)
      · exact hlarge
    obtain ⟨smallItem, hsmallItem, hsmallForI⟩ := hiSmall
    have hremove : additiveChoreCost cost i (allocation i \ {smallItem}) =
        additiveChoreCost cost i (allocation i) - 1 := by
      rw [additiveChoreCost_erase cost i (allocation i) smallItem hsmallItem, hsmallForI]
    have heraseUpper : additiveChoreCost cost i (allocation i \ {smallItem}) ≤
        (allocation i \ {smallItem}).card • r :=
      additiveChoreCost_le_card_nsmul_of_le cost i (allocation i \ {smallItem}) r
        (fun item hitem => IsOneOrRChoreCost.le_r cost r hcost hr.le i item)
    have hright : additiveChoreCost cost i (allocation j) =
        (allocation j).card • r :=
      additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation j) r hotherLarge
    have hcardPos : 0 < (allocation i).card := Finset.card_pos.mpr ⟨smallItem, hsmallItem⟩
    have hcardErase : (allocation i \ {smallItem}).card = (allocation i).card - 1 := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hsmallItem]
    have hsubAdd : (allocation i).card - 1 + 1 = (allocation i).card := by omega
    have hsubAddReal : (((allocation i).card - 1 : ℕ) : ℝ) + 1 = (allocation i).card := by
      exact_mod_cast hsubAdd
    rw [hright]
    norm_num [nsmul_eq_mul] at heraseUpper ⊢
    calc
      additiveChoreCost cost i (allocation i) + (r - 1) =
          additiveChoreCost cost i (allocation i \ {smallItem}) + r := by
            rw [hremove]
            ring
      _ ≤ ((allocation i \ {smallItem}).card : ℝ) * r + r :=
        by linarith [heraseUpper]
      _ = ((allocation i).card : ℝ) * r := by
        rw [hcardErase]
        nlinarith
      _ = ((allocation j).card : ℝ) * r := by rw [hcardEqReal]

end FairDivision
end AppliedModelingLib
