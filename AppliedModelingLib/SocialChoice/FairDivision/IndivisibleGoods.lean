import AppliedModelingLib.Foundations.Graph.Cycle
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Perm.List
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace AppliedModelingLib
namespace FairDivision

/-- A bundle of indivisible goods. -/
abbrev Bundle (Item : Type*) := Finset Item

/-- An allocation assigns each agent a bundle. -/
abbrev Allocation (Agent Item : Type*) := Agent → Bundle Item

/-- The allocation assigning every agent the empty bundle. -/
def emptyAllocation (Agent Item : Type*) : Allocation Agent Item :=
  fun _ => ∅

/-- The allocation that gives a whole finite item pool to one designated
agent and leaves every other bundle empty. -/
def allocateAllTo (Agent Item : Type*) [DecidableEq Agent]
    (owner : Agent) (items : Finset Item) :
    Allocation Agent Item :=
  fun agent => if agent = owner then items else ∅

/--
A valuation profile for indivisible goods.

The first fair-division target only needs monotone set valuations; additivity
and normalization should be separate assumptions for later papers.
-/
structure Valuation (Agent Item : Type*) where
  value : Agent → Bundle Item → ℝ
  monotone : ∀ agent {S T : Bundle Item}, S ⊆ T → value agent S ≤ value agent T

variable {Agent Item : Type*}

/-- Additive finite-good value from item weights. -/
noncomputable def additiveValue (w : Agent → Item → ℝ)
    (agent : Agent) (S : Bundle Item) : ℝ :=
  S.sum fun g => w agent g

/-- Additive valuations with nonnegative item weights are monotone. -/
noncomputable def additiveValuation [DecidableEq Item]
    (w : Agent → Item → ℝ) (hnonneg : ∀ agent g, 0 ≤ w agent g) :
    Valuation Agent Item where
  value := additiveValue w
  monotone := by
    intro agent S T hsub
    unfold additiveValue
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (by intro g _ _; exact hnonneg agent g)

theorem additiveValuation_value [DecidableEq Item]
    (w : Agent → Item → ℝ) (hnonneg : ∀ agent g, 0 ≤ w agent g)
    (agent : Agent) (S : Bundle Item) :
    (additiveValuation w hnonneg).value agent S = additiveValue w agent S := by
  rfl

/-- Envy of `i` for `j` under allocation `A`. -/
def envy (v : Valuation Agent Item) (A : Allocation Agent Item) (i j : Agent) : ℝ :=
  max 0 (v.value i (A j) - v.value i (A i))

/-- No agent strictly prefers another agent's bundle to her own. -/
def EnvyFree (v : Valuation Agent Item) (A : Allocation Agent Item) : Prop :=
  ∀ i j, v.value i (A j) ≤ v.value i (A i)

/-- Every pairwise envy is bounded by `α`. -/
def EnvyBoundedBy (v : Valuation Agent Item) (A : Allocation Agent Item) (α : ℝ) : Prop :=
  ∀ i j, envy v A i j ≤ α

/-- `A` allocates exactly the goods in `goods`, with no duplicates and no outsiders. -/
def IsAllocationOf [DecidableEq Item] (A : Allocation Agent Item) (goods : Finset Item) : Prop :=
  (∀ i g, g ∈ A i → g ∈ goods) ∧
    ∀ g, g ∈ goods → ∃! i, g ∈ A i

theorem isAllocationOf_mem_goods [DecidableEq Item]
    {A : Allocation Agent Item} {goods : Finset Item}
    (halloc : IsAllocationOf A goods) {i : Agent} {g : Item}
    (hmem : g ∈ A i) :
    g ∈ goods :=
  halloc.1 i g hmem

theorem isAllocationOf_exists_owner [DecidableEq Item]
    {A : Allocation Agent Item} {goods : Finset Item}
    (halloc : IsAllocationOf A goods) {g : Item}
    (hgoods : g ∈ goods) :
    ∃ i : Agent, g ∈ A i :=
  (halloc.2 g hgoods).exists

theorem isAllocationOf_owner_unique [DecidableEq Item]
    {A : Allocation Agent Item} {goods : Finset Item}
    (halloc : IsAllocationOf A goods) {g : Item}
    (hgoods : g ∈ goods) {i j : Agent}
    (hi : g ∈ A i) (hj : g ∈ A j) :
    i = j :=
  (halloc.2 g hgoods).unique hi hj

theorem isAllocationOf_not_mem_of_mem_ne [DecidableEq Item]
    {A : Allocation Agent Item} {goods : Finset Item}
    (halloc : IsAllocationOf A goods) {g : Item}
    (hgoods : g ∈ goods) {i j : Agent}
    (hi : g ∈ A i) (hne : j ≠ i) :
    g ∉ A j := by
  intro hj
  exact hne (isAllocationOf_owner_unique halloc hgoods hj hi)

/-- Feasible allocations on disjoint finite pools combine by taking the union
of each agent's two bundles. -/
theorem isAllocationOf_union [DecidableEq Item]
    (first second : Allocation Agent Item) (firstGoods secondGoods : Finset Item)
    (hdisjoint : Disjoint firstGoods secondGoods)
    (hfirst : IsAllocationOf first firstGoods) (hsecond : IsAllocationOf second secondGoods) :
    IsAllocationOf (fun agent => first agent ∪ second agent) (firstGoods ∪ secondGoods) := by
  constructor
  · intro agent item hitem
    rcases Finset.mem_union.mp hitem with hfirstItem | hsecondItem
    · exact Finset.mem_union_left _ (hfirst.1 agent item hfirstItem)
    · exact Finset.mem_union_right _ (hsecond.1 agent item hsecondItem)
  · intro item hitem
    rcases Finset.mem_union.mp hitem with hfirstGoods | hsecondGoods
    · obtain ⟨owner, howner, hunique⟩ := hfirst.2 item hfirstGoods
      refine ⟨owner, Finset.mem_union_left _ howner, ?_⟩
      intro other hother
      rcases Finset.mem_union.mp hother with hfirstOther | hsecondOther
      · exact hunique other hfirstOther
      · have hsecondMem : item ∈ secondGoods := hsecond.1 other item hsecondOther
        exact (Finset.disjoint_left.mp hdisjoint hfirstGoods hsecondMem).elim
    · obtain ⟨owner, howner, hunique⟩ := hsecond.2 item hsecondGoods
      refine ⟨owner, Finset.mem_union_right _ howner, ?_⟩
      intro other hother
      rcases Finset.mem_union.mp hother with hfirstOther | hsecondOther
      · have hfirstMem : item ∈ firstGoods := hfirst.1 other item hfirstOther
        exact (Finset.disjoint_left.mp hdisjoint hfirstMem hsecondGoods).elim
      · exact hunique other hsecondOther

/-- In a feasible finite allocation, the sum of bundle cardinalities is the
cardinality of the allocated item set. -/
theorem sum_card_allocation_eq_card_of_isAllocation [Fintype Agent] [DecidableEq Item]
    (allocation : Allocation Agent Item) (goods : Finset Item)
    (halloc : IsAllocationOf allocation goods) :
    Finset.univ.sum (fun agent => (allocation agent).card) = goods.card := by
  have hdisjoint : ((Finset.univ : Finset Agent) : Set Agent).PairwiseDisjoint allocation := by
    intro first _ second _ hne
    change Disjoint (allocation first) (allocation second)
    rw [Finset.disjoint_left]
    intro item hfirst hsecond
    apply hne
    exact isAllocationOf_owner_unique halloc (isAllocationOf_mem_goods halloc hfirst) hfirst hsecond
  have hunion : (Finset.univ : Finset Agent).biUnion allocation = goods := by
    ext item
    constructor
    · intro hitem
      obtain ⟨agent, _, hagent⟩ := Finset.mem_biUnion.mp hitem
      exact isAllocationOf_mem_goods halloc hagent
    · intro hitem
      obtain ⟨agent, hagent⟩ := isAllocationOf_exists_owner halloc hitem
      exact Finset.mem_biUnion.mpr ⟨agent, Finset.mem_univ _, hagent⟩
  calc
    Finset.univ.sum (fun agent => (allocation agent).card) =
        ((Finset.univ : Finset Agent).biUnion allocation).card :=
      (Finset.card_biUnion hdisjoint).symm
    _ = goods.card := congrArg Finset.card hunion

theorem isAllocationOf_empty [DecidableEq Item] :
    IsAllocationOf (emptyAllocation Agent Item) (∅ : Finset Item) := by
  constructor
  · intro i g hmem
    simp [emptyAllocation] at hmem
  · intro g hmem
    simp at hmem

/-- Giving an entire finite pool to one agent is feasible. -/
theorem isAllocationOf_allocateAllTo [DecidableEq Agent] [DecidableEq Item]
    (owner : Agent) (items : Finset Item) :
    IsAllocationOf (allocateAllTo Agent Item owner items) items := by
  constructor
  · intro agent item hitem
    by_cases howner : agent = owner
    · simpa [allocateAllTo, howner] using hitem
    · simp [allocateAllTo, howner] at hitem
  · intro item hitem
    refine ⟨owner, ?_, ?_⟩
    · simp [allocateAllTo, hitem]
    · intro agent hagent
      by_cases howner : agent = owner
      · exact howner
      · simp [allocateAllTo, howner] at hagent

theorem envy_nonneg (v : Valuation Agent Item) (A : Allocation Agent Item)
    (i j : Agent) :
    0 ≤ envy v A i j := by
  exact le_max_left 0 (v.value i (A j) - v.value i (A i))

theorem envy_eq_zero_iff (v : Valuation Agent Item) (A : Allocation Agent Item)
    (i j : Agent) :
    envy v A i j = 0 ↔ v.value i (A j) ≤ v.value i (A i) := by
  constructor
  · intro h
    have hgap : v.value i (A j) - v.value i (A i) ≤ 0 := by
      have hright : v.value i (A j) - v.value i (A i) ≤
          envy v A i j := by
        exact le_max_right 0 (v.value i (A j) - v.value i (A i))
      simpa [h] using hright
    linarith
  · intro h
    have hgap : v.value i (A j) - v.value i (A i) ≤ 0 := by
      linarith
    exact max_eq_left hgap

theorem envyBoundedBy_zero_iff_envyFree
    (v : Valuation Agent Item) (A : Allocation Agent Item) :
    EnvyBoundedBy v A 0 ↔ EnvyFree v A := by
  constructor
  · intro h i j
    have hzero : envy v A i j = 0 :=
      le_antisymm (h i j) (envy_nonneg v A i j)
    exact (envy_eq_zero_iff v A i j).mp hzero
  · intro h i j
    have hzero : envy v A i j = 0 :=
      (envy_eq_zero_iff v A i j).mpr (h i j)
    simp [hzero]

/-- Maximum-marginal-utility upper bound. -/
def MarginalBound [DecidableEq Item] (v : Valuation Agent Item) (α : ℝ) : Prop :=
  ∀ agent (S : Bundle Item) (g : Item),
    v.value agent (insert g S) - v.value agent S ≤ α

/-- If every item weight is at most `α`, the additive valuation has marginal bound `α`. -/
theorem additiveValuation_marginalBound [DecidableEq Item]
    (w : Agent → Item → ℝ) (hnonneg : ∀ agent g, 0 ≤ w agent g)
    {α : ℝ} (hweight : ∀ agent g, w agent g ≤ α) :
    MarginalBound (additiveValuation w hnonneg) α := by
  intro agent S g
  by_cases hg : g ∈ S
  · have halpha : 0 ≤ α := le_trans (hnonneg agent g) (hweight agent g)
    simp [additiveValuation, additiveValue, Finset.insert_eq_of_mem hg, halpha]
  · simp [additiveValuation, additiveValue, hg, hweight agent g]

/--
Maximum one-good marginal value over all finite agents, bundles, and goods.
This supplies the canonical finite-universe marginal-bound constant.
-/
noncomputable def maxMarginal
    [Fintype Agent] [Fintype Item] [DecidableEq Item]
    [Nonempty Agent] [Nonempty Item]
    (v : Valuation Agent Item) : ℝ :=
  ((Finset.univ : Finset Agent).product
      (((Finset.univ : Finset Item).powerset).product
        (Finset.univ : Finset Item))).sup'
    (by
      obtain ⟨agent⟩ := (inferInstance : Nonempty Agent)
      obtain ⟨g⟩ := (inferInstance : Nonempty Item)
      exact ⟨(agent, (∅, g)), by simp⟩)
    (fun x => v.value x.1 (insert x.2.2 x.2.1) - v.value x.1 x.2.1)

/-- The maximum marginal value bounds every one-good marginal. -/
theorem marginalBound_maxMarginal
    [Fintype Agent] [Fintype Item] [DecidableEq Item]
    [Nonempty Agent] [Nonempty Item]
    (v : Valuation Agent Item) :
    MarginalBound v (maxMarginal v) := by
  intro agent S g
  unfold maxMarginal
  exact Finset.le_sup'
    (f := fun x : Agent × (Bundle Item × Item) =>
      v.value x.1 (insert x.2.2 x.2.1) - v.value x.1 x.2.1)
    (b := (agent, (S, g))) (by simp)

/-- Monotonicity makes the maximum marginal value nonnegative. -/
theorem maxMarginal_nonneg
    [Fintype Agent] [Fintype Item] [DecidableEq Item]
    [Nonempty Agent] [Nonempty Item]
    (v : Valuation Agent Item) :
    0 ≤ maxMarginal v := by
  obtain ⟨agent⟩ := (inferInstance : Nonempty Agent)
  obtain ⟨g⟩ := (inferInstance : Nonempty Item)
  have hmono :
      v.value agent (∅ : Bundle Item) ≤
        v.value agent (insert g (∅ : Bundle Item)) := by
    exact v.monotone agent (by intro x hx; simp at hx)
  have hdelta :
      0 ≤ v.value agent (insert g (∅ : Bundle Item)) -
        v.value agent (∅ : Bundle Item) := by
    linarith
  have hbound :=
    marginalBound_maxMarginal (v := v) agent (∅ : Bundle Item) g
  linarith

/-- Nobody envies the bundle currently held by `owner`. -/
def NoOneEnvies (v : Valuation Agent Item) (A : Allocation Agent Item)
    (owner : Agent) : Prop :=
  ∀ i, v.value i (A owner) ≤ v.value i (A i)

/-- Directed envy edge: `i` strictly prefers `j`'s bundle to her own. -/
def EnvyEdge (v : Valuation Agent Item) (A : Allocation Agent Item)
    (i j : Agent) : Prop :=
  v.value i (A i) < v.value i (A j)

/--
The directed envy graph is acyclic when the incoming-edge relation is
well-founded. This is the exact graph-theoretic condition needed to produce a
source/unenvied agent.
-/
def AcyclicEnvyGraph (v : Valuation Agent Item) (A : Allocation Agent Item) :
    Prop :=
  WellFounded fun i j => EnvyEdge v A i j

/--
Every finite acyclic envy graph has a source.  Here the finite/no-cycle work is
packaged as `AcyclicEnvyGraph`; the lemma extracts an unenvied agent.
-/
theorem exists_noOneEnvies_of_acyclicEnvyGraph [Nonempty Agent]
    (v : Valuation Agent Item) (A : Allocation Agent Item)
    (hacyclic : AcyclicEnvyGraph v A) :
    ∃ owner : Agent, NoOneEnvies v A owner := by
  classical
  obtain ⟨owner, _, hmin⟩ := hacyclic.has_min Set.univ Set.univ_nonempty
  refine ⟨owner, ?_⟩
  intro i
  by_contra hnot
  exact hmin i trivial (lt_of_not_ge hnot)

/-- Rotate bundles according to `next`. Cycle elimination is a special case. -/
def rotateBundles (A : Allocation Agent Item) (next : Agent → Agent) :
    Allocation Agent Item :=
  fun i => A (next i)

/-- Give one additional good to `owner`. -/
def addItem [DecidableEq Agent] [DecidableEq Item]
    (A : Allocation Agent Item) (owner : Agent) (g : Item) :
    Allocation Agent Item :=
  fun i => if i = owner then insert g (A i) else A i

theorem isAllocationOf_addItem_insert [DecidableEq Agent] [DecidableEq Item]
    (A : Allocation Agent Item) (goods : Finset Item) (owner : Agent) (g : Item)
    (halloc : IsAllocationOf A goods)
    (hg : g ∉ goods) :
    IsAllocationOf (addItem A owner g) (insert g goods) := by
  constructor
  · intro i x hx
    by_cases hi : i = owner
    · have hx' : x ∈ insert g (A owner) := by
        simpa [addItem, hi] using hx
      rcases Finset.mem_insert.mp hx' with hxg | hxold
      · exact Finset.mem_insert.mpr (Or.inl hxg)
      · exact Finset.mem_insert.mpr (Or.inr (halloc.1 owner x hxold))
    · have hxold : x ∈ A i := by
        simpa [addItem, hi] using hx
      exact Finset.mem_insert.mpr (Or.inr (halloc.1 i x hxold))
  · intro x hx
    rcases Finset.mem_insert.mp hx with hxg | hxgoods
    · refine ⟨owner, ?_, ?_⟩
      · simp [addItem, hxg]
      · intro j hj
        by_cases hjowner : j = owner
        · exact hjowner
        · have hjold : g ∈ A j := by
            simpa [addItem, hjowner, hxg] using hj
          exact (False.elim (hg (halloc.1 j g hjold)))
    · obtain ⟨oldOwner, holdmem, holduniq⟩ := halloc.2 x hxgoods
      refine ⟨oldOwner, ?_, ?_⟩
      · by_cases hold : oldOwner = owner
        · have hmemOwner : x ∈ insert g (A owner) :=
            Finset.mem_insert.mpr (Or.inr (by simpa [hold] using holdmem))
          simpa [addItem, hold] using hmemOwner
        · simp [addItem, hold, holdmem]
      · intro j hj
        have hjold : x ∈ A j := by
          by_cases hjowner : j = owner
          · have hxinsert : x ∈ insert g (A owner) := by
              simpa [addItem, hjowner] using hj
            rcases Finset.mem_insert.mp hxinsert with hxg | hxold
            · exact False.elim (hg (by simpa [hxg] using hxgoods))
            · simpa [hjowner] using hxold
          · simpa [addItem, hjowner] using hj
        exact holduniq j hjold

theorem envy_le_of_gap_le (v : Valuation Agent Item) (A : Allocation Agent Item)
    (i j : Agent) {α : ℝ}
    (hα : 0 ≤ α)
    (hgap : v.value i (A j) - v.value i (A i) ≤ α) :
    envy v A i j ≤ α := by
  exact max_le hα hgap

theorem max_zero_sub_le_max_zero_sub {a b c : ℝ} (h : a ≤ b) :
    max 0 (c - b) ≤ max 0 (c - a) := by
  by_cases hnonneg : 0 ≤ c - b
  · have hsub : c - b ≤ c - a := by linarith
    exact max_le (le_max_left 0 (c - a)) (le_trans hsub (le_max_right 0 (c - a)))
  · have hleft : max 0 (c - b) = 0 := by
      exact max_eq_left (le_of_not_ge hnonneg)
    rw [hleft]
    exact le_max_left 0 (c - a)

/--
If rotation gives agent `i` a weakly better own bundle, then `i`'s envy after
rotation is bounded by evaluating the new comparison bundle against the old
self-bundle. This is the local inequality used in envy-cycle elimination.
-/
theorem envy_rotate_le_old_baseline
    (v : Valuation Agent Item) (A : Allocation Agent Item) (next : Agent → Agent)
    (i j : Agent)
    (hself : v.value i (A i) ≤ v.value i (A (next i))) :
    envy v (rotateBundles A next) i j ≤
      max 0 (v.value i (A (next j)) - v.value i (A i)) := by
  exact max_zero_sub_le_max_zero_sub (a := v.value i (A i))
    (b := v.value i (A (next i))) (c := v.value i (A (next j))) hself

/--
Any bundle rotation that weakly improves every agent's own bundle preserves an
existing global envy bound. Cycle elimination uses this with `next` equal to the
successor map around an envy cycle and identity off the cycle.
-/
theorem envyBoundedBy_rotate_of_self_improves
    (v : Valuation Agent Item) (A : Allocation Agent Item) (next : Agent → Agent)
    {α : ℝ}
    (hbound : EnvyBoundedBy v A α)
    (hself : ∀ i, v.value i (A i) ≤ v.value i (A (next i))) :
    EnvyBoundedBy v (rotateBundles A next) α := by
  intro i j
  calc
    envy v (rotateBundles A next) i j
        ≤ max 0 (v.value i (A (next j)) - v.value i (A i)) :=
          envy_rotate_le_old_baseline v A next i j (hself i)
    _ = envy v A i (next j) := rfl
    _ ≤ α := hbound i (next j)

theorem isAllocationOf_rotate_of_bijective [DecidableEq Item]
    (A : Allocation Agent Item) (goods : Finset Item) (next : Agent → Agent)
    (halloc : IsAllocationOf A goods)
    (hnext : Function.Bijective next) :
    IsAllocationOf (rotateBundles A next) goods := by
  constructor
  · intro i g hg
    exact halloc.1 (next i) g (by simpa [rotateBundles] using hg)
  · intro g hg
    obtain ⟨oldOwner, holdmem, holduniq⟩ := halloc.2 g hg
    obtain ⟨owner, howner⟩ := hnext.2 oldOwner
    refine ⟨owner, ?_, ?_⟩
    · simpa [rotateBundles, howner] using holdmem
    · intro j hj
      have hjold : g ∈ A (next j) := by
        simpa [rotateBundles] using hj
      have hnextj : next j = oldOwner := holduniq (next j) hjold
      exact hnext.1 (hnextj.trans howner.symm)

/-- The self-value potential used to prove termination of cycle elimination. -/
noncomputable def selfValueSum [Fintype Agent]
    (v : Valuation Agent Item) (A : Allocation Agent Item) : ℝ :=
  ∑ i : Agent, v.value i (A i)

theorem selfValueSum_rotate_eq [Fintype Agent]
    (v : Valuation Agent Item) (A : Allocation Agent Item) (next : Agent → Agent) :
    selfValueSum v (rotateBundles A next) =
      ∑ i : Agent, v.value i (A (next i)) := by
  simp [selfValueSum, rotateBundles]

theorem selfValueSum_le_rotate_of_self_improves [Fintype Agent]
    (v : Valuation Agent Item) (A : Allocation Agent Item) (next : Agent → Agent)
    (hself : ∀ i, v.value i (A i) ≤ v.value i (A (next i))) :
    selfValueSum v A ≤ selfValueSum v (rotateBundles A next) := by
  rw [selfValueSum_rotate_eq]
  exact Finset.sum_le_sum (by intro i _; exact hself i)

theorem selfValueSum_lt_rotate_of_self_improves_and_exists_strict [Fintype Agent]
    (v : Valuation Agent Item) (A : Allocation Agent Item) (next : Agent → Agent)
    (hself : ∀ i, v.value i (A i) ≤ v.value i (A (next i)))
    (hstrict : ∃ i, v.value i (A i) < v.value i (A (next i))) :
    selfValueSum v A < selfValueSum v (rotateBundles A next) := by
  rw [selfValueSum_rotate_eq]
  refine Finset.sum_lt_sum (by intro i _; exact hself i) ?_
  obtain ⟨i, hi⟩ := hstrict
  exact ⟨i, by simp, hi⟩

theorem self_improves_of_fixed_or_envyEdge
    (v : Valuation Agent Item) (A : Allocation Agent Item) (next : Agent → Agent)
    (hstep : ∀ i, next i = i ∨ EnvyEdge v A i (next i)) :
    ∀ i, v.value i (A i) ≤ v.value i (A (next i)) := by
  intro i
  rcases hstep i with hfixed | hedge
  · simp [hfixed]
  · exact le_of_lt hedge

theorem exists_strict_self_improves_of_exists_envyEdge_next
    (v : Valuation Agent Item) (A : Allocation Agent Item) (next : Agent → Agent)
    (hedge : ∃ i, EnvyEdge v A i (next i)) :
    ∃ i, v.value i (A i) < v.value i (A (next i)) := by
  simpa [EnvyEdge] using hedge

/--
A closed envy walk, represented as a transitive-closure cycle.  This is weaker
than an explicit simple cycle permutation, but it is fully extracted from finite
non-acyclicity below.
-/
def HasTransitiveEnvyCycle
    (v : Valuation Agent Item) (A : Allocation Agent Item) : Prop :=
  ∃ i, Relation.TransGen (fun p q => EnvyEdge v A p q) i i

/--
A positive-length closed envy walk, represented with CSLib's step-indexed
relation path API.  This is the next bridge toward shortest-walk extraction of
a simple nodup envy cycle.
-/
def HasStepEnvyCycle
    (v : Valuation Agent Item) (A : Allocation Agent Item) : Prop :=
  ∃ i n, 0 < n ∧
    Relation.RelatesInSteps (fun p q => EnvyEdge v A p q) i i n

theorem hasStepEnvyCycle_of_transitiveEnvyCycle
    {v : Valuation Agent Item} {A : Allocation Agent Item}
    (hcycle : HasTransitiveEnvyCycle v A) :
    HasStepEnvyCycle v A := by
  obtain ⟨i, hi⟩ := hcycle
  obtain ⟨n, hnpos, hn⟩ :=
    AppliedModelingLib.Foundations.Graph.exists_relatesInSteps_pos_of_transGen hi
  exact ⟨i, n, hnpos, hn⟩

theorem hasTransitiveEnvyCycle_of_not_acyclic
    [Finite Agent]
    (v : Valuation Agent Item) (A : Allocation Agent Item)
    (hnot : ¬ AcyclicEnvyGraph v A) :
    HasTransitiveEnvyCycle v A := by
  exact AppliedModelingLib.Foundations.Graph.exists_transGen_self_of_not_wellFounded (α := Agent)
    (r := fun p q => EnvyEdge v A p q) hnot

/--
The finite graph theorem now proved in this file: non-acyclic envy graphs yield
closed envy walks in the transitive closure.
-/
def HasTransitiveEnvyCycleExtraction
    (v : Valuation Agent Item) : Prop :=
  ∀ A : Allocation Agent Item,
    ¬ AcyclicEnvyGraph v A → HasTransitiveEnvyCycle v A

def HasStepEnvyCycleExtraction
    (v : Valuation Agent Item) : Prop :=
  ∀ A : Allocation Agent Item,
    ¬ AcyclicEnvyGraph v A → HasStepEnvyCycle v A

theorem hasTransitiveEnvyCycleExtraction_of_finite
    [Finite Agent] (v : Valuation Agent Item) :
    HasTransitiveEnvyCycleExtraction v := by
  intro A hnot
  exact hasTransitiveEnvyCycle_of_not_acyclic v A hnot

theorem hasStepEnvyCycleExtraction_of_finite
    [Finite Agent] (v : Valuation Agent Item) :
    HasStepEnvyCycleExtraction v := by
  intro A hnot
  exact hasStepEnvyCycle_of_transitiveEnvyCycle
    (hasTransitiveEnvyCycle_of_not_acyclic v A hnot)

/--
A simple envy cycle as a nodup list.  `cycle.formPerm` maps every listed agent to
the next listed agent, wrapping the last agent to the first.
-/
structure EnvyCycleList [DecidableEq Agent]
    (v : Valuation Agent Item) (A : Allocation Agent Item) where
  cycle : List Agent
  nodup : cycle.Nodup
  length_two : 2 ≤ cycle.length
  edge_formPerm : ∀ i, i ∈ cycle → EnvyEdge v A i (cycle.formPerm i)

namespace EnvyCycleList

def ofTwoCycle [DecidableEq Agent]
    {v : Valuation Agent Item} {A : Allocation Agent Item}
    {i j : Agent}
    (hij : EnvyEdge v A i j)
    (hji : EnvyEdge v A j i) :
    EnvyCycleList v A where
  cycle := [i, j]
  nodup := by
    have hne : i ≠ j := by
      intro h
      subst j
      exact (lt_irrefl (v.value i (A i))) hij
    simp [hne]
  length_two := by simp
  edge_formPerm := by
    intro x hx
    have hne : i ≠ j := by
      intro h
      subst j
      exact (lt_irrefl (v.value i (A i))) hij
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simpa [List.formPerm_pair, hne] using hij
    · simpa [List.formPerm_pair, hne, hne.symm] using hji

end EnvyCycleList

/--
An envy-cycle permutation: outside the cycle `next` may fix agents, while on
the cycle each moved agent points to a bundle she strictly envies.
-/
structure EnvyCyclePermutation
    (v : Valuation Agent Item) (A : Allocation Agent Item) where
  next : Agent → Agent
  bijective : Function.Bijective next
  fixed_or_envy : ∀ i, next i = i ∨ EnvyEdge v A i (next i)
  some_envy : ∃ i, EnvyEdge v A i (next i)

namespace EnvyCyclePermutation

def ofEnvyCycleList [DecidableEq Agent]
    {v : Valuation Agent Item} {A : Allocation Agent Item}
    (cycle : EnvyCycleList v A) :
    EnvyCyclePermutation v A where
  next := cycle.cycle.formPerm
  bijective := Equiv.bijective cycle.cycle.formPerm
  fixed_or_envy := by
    intro i
    by_cases hi : i ∈ cycle.cycle
    · exact Or.inr (cycle.edge_formPerm i hi)
    · exact Or.inl (List.formPerm_apply_of_notMem hi)
  some_envy := by
    have hpos : 0 < cycle.cycle.length :=
      lt_of_lt_of_le (by decide : 0 < 2) cycle.length_two
    obtain ⟨i, hi⟩ := List.length_pos_iff_exists_mem.mp hpos
    exact ⟨i, cycle.edge_formPerm i hi⟩

end EnvyCyclePermutation

/--
Certificate for the local rotation produced by an envy cycle: the successor map
is a permutation, every agent weakly improves her own bundle, and at least one
agent strictly improves.
-/
structure ImprovingBundleRotation
    (v : Valuation Agent Item) (A : Allocation Agent Item) where
  next : Agent → Agent
  bijective : Function.Bijective next
  self_improves : ∀ i, v.value i (A i) ≤ v.value i (A (next i))
  some_strict : ∃ i, v.value i (A i) < v.value i (A (next i))

namespace ImprovingBundleRotation

def ofEnvyCyclePermutation
    {v : Valuation Agent Item} {A : Allocation Agent Item}
    (cycle : EnvyCyclePermutation v A) :
    ImprovingBundleRotation v A where
  next := cycle.next
  bijective := cycle.bijective
  self_improves :=
    self_improves_of_fixed_or_envyEdge v A cycle.next cycle.fixed_or_envy
  some_strict :=
    exists_strict_self_improves_of_exists_envyEdge_next v A cycle.next
      cycle.some_envy

def ofFixedOrEnvyEdge
    (v : Valuation Agent Item) (A : Allocation Agent Item) (next : Agent → Agent)
    (hbij : Function.Bijective next)
    (hstep : ∀ i, next i = i ∨ EnvyEdge v A i (next i))
    (hedge : ∃ i, EnvyEdge v A i (next i)) :
    ImprovingBundleRotation v A where
  next := next
  bijective := hbij
  self_improves := self_improves_of_fixed_or_envyEdge v A next hstep
  some_strict := exists_strict_self_improves_of_exists_envyEdge_next v A next hedge

theorem isAllocationOf_rotate [DecidableEq Item]
    {v : Valuation Agent Item} {A : Allocation Agent Item} {goods : Finset Item}
    (rot : ImprovingBundleRotation v A)
    (halloc : IsAllocationOf A goods) :
    IsAllocationOf (rotateBundles A rot.next) goods :=
  isAllocationOf_rotate_of_bijective A goods rot.next halloc rot.bijective

theorem envyBoundedBy_rotate
    {v : Valuation Agent Item} {A : Allocation Agent Item} {α : ℝ}
    (rot : ImprovingBundleRotation v A)
    (hbound : EnvyBoundedBy v A α) :
    EnvyBoundedBy v (rotateBundles A rot.next) α :=
  envyBoundedBy_rotate_of_self_improves v A rot.next hbound rot.self_improves

theorem selfValueSum_lt_rotate [Fintype Agent]
    {v : Valuation Agent Item} {A : Allocation Agent Item}
    (rot : ImprovingBundleRotation v A) :
    selfValueSum v A < selfValueSum v (rotateBundles A rot.next) :=
  selfValueSum_lt_rotate_of_self_improves_and_exists_strict
    v A rot.next rot.self_improves rot.some_strict

end ImprovingBundleRotation

/--
A feasible allocation is potential-maximal when no other bounded allocation of
the same goods has larger self-value sum.
-/
def PotentialMaximal [Fintype Agent] [DecidableEq Item]
    (v : Valuation Agent Item) (goods : Finset Item)
    (A : Allocation Agent Item) (α : ℝ) : Prop :=
  IsAllocationOf A goods ∧ EnvyBoundedBy v A α ∧
    ∀ B : Allocation Agent Item,
      IsAllocationOf B goods → EnvyBoundedBy v B α →
        selfValueSum v B ≤ selfValueSum v A

/--
A potential-maximal bounded allocation admits no improving bundle rotation.
This is the contradiction step behind finite envy-cycle elimination.
-/
theorem PotentialMaximal.not_improvingBundleRotation
    [Fintype Agent] [DecidableEq Item]
    {v : Valuation Agent Item} {goods : Finset Item}
    {A : Allocation Agent Item} {α : ℝ}
    (hmax : PotentialMaximal v goods A α)
    (rot : ImprovingBundleRotation v A) :
    False := by
  have halloc' : IsAllocationOf (rotateBundles A rot.next) goods :=
    rot.isAllocationOf_rotate hmax.1
  have hbound' : EnvyBoundedBy v (rotateBundles A rot.next) α :=
    rot.envyBoundedBy_rotate hmax.2.1
  have hle : selfValueSum v (rotateBundles A rot.next) ≤ selfValueSum v A :=
    hmax.2.2 (rotateBundles A rot.next) halloc' hbound'
  exact (not_lt_of_ge hle) rot.selfValueSum_lt_rotate

/--
Among finitely many exact allocations of finitely many goods, any nonempty
bounded feasible set has a self-value-potential maximizer.
-/
theorem exists_potentialMaximal
    [Fintype Agent] [Finite Item] [DecidableEq Item]
    (v : Valuation Agent Item) {goods : Finset Item}
    {A : Allocation Agent Item} {α : ℝ}
    (halloc : IsAllocationOf A goods)
    (hbound : EnvyBoundedBy v A α) :
    ∃ B : Allocation Agent Item, PotentialMaximal v goods B α := by
  classical
  letI := Fintype.ofFinite Item
  let Feasible :=
    {B : Allocation Agent Item // IsAllocationOf B goods ∧ EnvyBoundedBy v B α}
  have hnonempty : (Finset.univ : Finset Feasible).Nonempty :=
    ⟨⟨A, halloc, hbound⟩, by simp⟩
  obtain ⟨B, _, hmax⟩ :=
    Finset.exists_max_image
      (s := (Finset.univ : Finset Feasible))
      (f := fun B : Feasible => selfValueSum v B.1)
      hnonempty
  refine ⟨B.1, B.2.1, B.2.2, ?_⟩
  intro C hCalloc hCbound
  exact hmax ⟨C, hCalloc, hCbound⟩ (by simp)

/--
The remaining graph-theoretic seam for finite cycle elimination: every
non-acyclic envy graph yields a potential-improving permutation of bundles.
-/
def HasImprovingRotationExtraction
    (v : Valuation Agent Item) : Prop :=
  ∀ A : Allocation Agent Item,
    ¬ AcyclicEnvyGraph v A → Nonempty (ImprovingBundleRotation v A)

/--
Equivalent graph-facing seam: a non-acyclic envy graph provides an explicit
cycle permutation.  This is the natural finite graph lemma to prove next.
-/
def HasEnvyCyclePermutationExtraction
    (v : Valuation Agent Item) : Prop :=
  ∀ A : Allocation Agent Item,
    ¬ AcyclicEnvyGraph v A → Nonempty (EnvyCyclePermutation v A)

/--
List-facing version of the remaining simple-cycle extraction seam.  This is
often easier to prove from a concrete directed cycle than constructing the
permutation directly.
-/
def HasEnvyCycleListExtraction [DecidableEq Agent]
    (v : Valuation Agent Item) : Prop :=
  ∀ A : Allocation Agent Item,
    ¬ AcyclicEnvyGraph v A → Nonempty (EnvyCycleList v A)

/--
Finite non-acyclic envy graphs contain an explicit simple envy cycle.  This
closes the graph-theoretic cycle-extraction step used by bounded-envy proofs.
-/
theorem hasEnvyCycleListExtraction_of_finite
    [Finite Agent] [DecidableEq Agent] (v : Valuation Agent Item) :
    HasEnvyCycleListExtraction v := by
  intro A hnot
  obtain ⟨i, n, hnpos, hsteps⟩ := hasStepEnvyCycleExtraction_of_finite v A hnot
  obtain ⟨cycle, hnodup, hlen, hedge⟩ :=
    AppliedModelingLib.Foundations.Graph.exists_simple_cycle_list_of_stepCycle
      (r := fun p q => EnvyEdge v A p q)
      (by
        intro a ha
        exact (lt_irrefl (v.value a (A a))) ha)
      ⟨i, n, hnpos, hsteps⟩
  exact ⟨{ cycle := cycle
           nodup := hnodup
           length_two := hlen
           edge_formPerm := hedge }⟩

theorem hasEnvyCyclePermutationExtraction_of_envyCycleListExtraction
    [DecidableEq Agent]
    {v : Valuation Agent Item}
    (hextract : HasEnvyCycleListExtraction v) :
    HasEnvyCyclePermutationExtraction v := by
  intro A hnot
  obtain ⟨cycle⟩ := hextract A hnot
  exact ⟨EnvyCyclePermutation.ofEnvyCycleList cycle⟩

theorem hasImprovingRotationExtraction_of_envyCyclePermutationExtraction
    {v : Valuation Agent Item}
    (hextract : HasEnvyCyclePermutationExtraction v) :
    HasImprovingRotationExtraction v := by
  intro A hnot
  obtain ⟨cycle⟩ := hextract A hnot
  exact ⟨ImprovingBundleRotation.ofEnvyCyclePermutation cycle⟩

theorem PotentialMaximal.acyclic_of_improvingRotationExtraction
    [Fintype Agent] [DecidableEq Item]
    {v : Valuation Agent Item} {goods : Finset Item}
    {A : Allocation Agent Item} {α : ℝ}
    (hmax : PotentialMaximal v goods A α)
    (hextract : HasImprovingRotationExtraction v) :
    AcyclicEnvyGraph v A := by
  by_contra hnot
  obtain ⟨rot⟩ := hextract A hnot
  exact hmax.not_improvingBundleRotation rot

/--
If nobody envies `owner`, adding one good to `owner` creates envy toward
`owner` of at most the marginal bound. This is the key local step in the
bounded-envy algorithm.
-/
theorem envy_addItem_owner_le_marginalBound [DecidableEq Agent] [DecidableEq Item]
    (v : Valuation Agent Item) (A : Allocation Agent Item)
    (owner q : Agent) (g : Item) {α : ℝ}
    (hαnonneg : 0 ≤ α)
    (hmargin : MarginalBound v α)
    (hunenvied : NoOneEnvies v A owner) :
    envy v (addItem A owner g) q owner ≤ α := by
  by_cases hq : q = owner
  · subst q
    simp [envy, addItem, hαnonneg]
  · have hno : v.value q (A owner) ≤ v.value q (A q) := hunenvied q
    have hmarg : v.value q (insert g (A owner)) - v.value q (A owner) ≤ α :=
      hmargin q (A owner) g
    have hgap : v.value q (insert g (A owner)) - v.value q (A q) ≤ α := by
      linarith
    calc
      envy v (addItem A owner g) q owner
          = max 0 (v.value q (insert g (A owner)) - v.value q (A q)) := by
            simp [envy, addItem, hq]
      _ ≤ α := max_le hαnonneg hgap

theorem envyBoundedBy_addItem_of_unenvied [DecidableEq Agent] [DecidableEq Item]
    (v : Valuation Agent Item) (A : Allocation Agent Item)
    (owner : Agent) (g : Item) {α : ℝ}
    (hαnonneg : 0 ≤ α)
    (hbound : EnvyBoundedBy v A α)
    (hmargin : MarginalBound v α)
    (hunenvied : NoOneEnvies v A owner) :
    EnvyBoundedBy v (addItem A owner g) α := by
  intro i j
  by_cases hj : j = owner
  · subst j
    exact envy_addItem_owner_le_marginalBound v A owner i g
      hαnonneg hmargin hunenvied
  · by_cases hi : i = owner
    · have hmono : v.value i (A i) ≤ v.value i (insert g (A i)) := by
        exact v.monotone i (by intro x hx; exact Finset.mem_insert.mpr (Or.inr hx))
      calc
        envy v (addItem A owner g) i j
            = max 0 (v.value i (A j) - v.value i (insert g (A i))) := by
              simp [envy, addItem, hi, hj]
        _ ≤ max 0 (v.value i (A j) - v.value i (A i)) :=
              max_zero_sub_le_max_zero_sub hmono
        _ = envy v A i j := rfl
        _ ≤ α := hbound i j
    · calc
        envy v (addItem A owner g) i j = envy v A i j := by
          simp [envy, addItem, hi, hj]
        _ ≤ α := hbound i j

/--
Cycle-elimination step packaged as the exact property needed by the main
induction: every bounded partial allocation can be transformed into a bounded
allocation of the same goods with an unenvied owner.
-/
def HasUnenviedReduction [DecidableEq Item]
    (v : Valuation Agent Item) (α : ℝ) : Prop :=
  ∀ goods (A : Allocation Agent Item),
    IsAllocationOf A goods →
    EnvyBoundedBy v A α →
    ∃ B owner, IsAllocationOf B goods ∧ EnvyBoundedBy v B α ∧ NoOneEnvies v B owner

/--
Cycle-elimination target: every bounded partial allocation can be transformed
into one with an acyclic envy graph while preserving the allocated goods and the
envy bound.
-/
def HasAcyclicReduction [DecidableEq Item]
    (v : Valuation Agent Item) (α : ℝ) : Prop :=
  ∀ goods (A : Allocation Agent Item),
    IsAllocationOf A goods →
    EnvyBoundedBy v A α →
    ∃ B, IsAllocationOf B goods ∧ EnvyBoundedBy v B α ∧ AcyclicEnvyGraph v B

/--
Finite potential maximization reduces cycle elimination to the pure graph step
`HasImprovingRotationExtraction`.
-/
theorem hasAcyclicReduction_of_improvingRotationExtraction
    [Finite Agent] [Finite Item] [DecidableEq Item]
    (v : Valuation Agent Item) {α : ℝ}
    (hextract : HasImprovingRotationExtraction v) :
    HasAcyclicReduction v α := by
  classical
  letI := Fintype.ofFinite Agent
  intro goods A halloc hbound
  obtain ⟨B, hmax⟩ := exists_potentialMaximal v halloc hbound
  exact ⟨B, hmax.1, hmax.2.1,
    hmax.acyclic_of_improvingRotationExtraction hextract⟩

/--
Version of finite cycle elimination stated with the explicit envy-cycle
permutation seam.
-/
theorem hasAcyclicReduction_of_envyCyclePermutationExtraction
    [Finite Agent] [Finite Item] [DecidableEq Item]
    (v : Valuation Agent Item) {α : ℝ}
    (hextract : HasEnvyCyclePermutationExtraction v) :
    HasAcyclicReduction v α := by
  exact hasAcyclicReduction_of_improvingRotationExtraction v
    (hasImprovingRotationExtraction_of_envyCyclePermutationExtraction hextract)

/--
Finite cycle elimination stated with a simple-cycle list extractor.
-/
theorem hasAcyclicReduction_of_envyCycleListExtraction
    [Finite Agent] [Finite Item] [DecidableEq Agent] [DecidableEq Item]
    (v : Valuation Agent Item) {α : ℝ}
    (hextract : HasEnvyCycleListExtraction v) :
    HasAcyclicReduction v α := by
  exact hasAcyclicReduction_of_envyCyclePermutationExtraction v
    (hasEnvyCyclePermutationExtraction_of_envyCycleListExtraction hextract)

theorem hasUnenviedReduction_of_acyclicReduction
    [DecidableEq Item] [Nonempty Agent]
    (v : Valuation Agent Item) {α : ℝ}
    (hreduce : HasAcyclicReduction v α) :
    HasUnenviedReduction v α := by
  intro goods A halloc hbound
  obtain ⟨B, hBalloc, hBbound, hBacyclic⟩ :=
    hreduce goods A halloc hbound
  obtain ⟨owner, hunenvied⟩ :=
    exists_noOneEnvies_of_acyclicEnvyGraph v B hBacyclic
  exact ⟨B, owner, hBalloc, hBbound, hunenvied⟩

/--
Main bounded-envy existence theorem for indivisible goods, assuming the
cycle-elimination/unenvied-reduction lemma. Algorithmic complexity claims are
intentionally outside this reusable existence statement.
-/
theorem exists_envyBounded_allocation_of_unenviedReduction
    [DecidableEq Item]
    (v : Valuation Agent Item) {α : ℝ}
    (hαnonneg : 0 ≤ α)
    (hmargin : MarginalBound v α)
    (hreduce : HasUnenviedReduction v α) :
    ∀ goods : Finset Item,
      ∃ A : Allocation Agent Item, IsAllocationOf A goods ∧ EnvyBoundedBy v A α := by
  classical
  intro goods
  refine Finset.induction_on goods ?empty ?insert
  · refine ⟨emptyAllocation Agent Item, isAllocationOf_empty, ?_⟩
    intro i j
    simp [emptyAllocation, envy, hαnonneg]
  · intro g goods hg ih
    obtain ⟨A, halloc, hbound⟩ := ih
    obtain ⟨B, owner, hBalloc, hBbound, hunenvied⟩ :=
      hreduce goods A halloc hbound
    refine ⟨addItem B owner g, ?_, ?_⟩
    · exact isAllocationOf_addItem_insert B goods owner g hBalloc hg
    · exact envyBoundedBy_addItem_of_unenvied v B owner g
        hαnonneg hBbound hmargin hunenvied

/--
Paper-level bounded-envy theorem phrased with the concrete envy-graph seam:
cycle elimination only has to produce an acyclic envy graph, and this theorem
extracts the unenvied source at every induction step.
-/
theorem exists_envyBounded_allocation_of_acyclicReduction
    [DecidableEq Item] [Nonempty Agent]
    (v : Valuation Agent Item) {α : ℝ}
    (hαnonneg : 0 ≤ α)
    (hmargin : MarginalBound v α)
    (hreduce : HasAcyclicReduction v α) :
    ∀ goods : Finset Item,
      ∃ A : Allocation Agent Item, IsAllocationOf A goods ∧ EnvyBoundedBy v A α := by
  exact exists_envyBounded_allocation_of_unenviedReduction v hαnonneg hmargin
    (hasUnenviedReduction_of_acyclicReduction v hreduce)

/--
Finite paper-level bounded-envy theorem with only the pure directed-cycle
extraction step left as an assumption.
-/
theorem exists_envyBounded_allocation_of_improvingRotationExtraction
    [Finite Agent] [Finite Item] [DecidableEq Item] [Nonempty Agent]
    (v : Valuation Agent Item) {α : ℝ}
    (hαnonneg : 0 ≤ α)
    (hmargin : MarginalBound v α)
    (hextract : HasImprovingRotationExtraction v) :
    ∀ goods : Finset Item,
      ∃ A : Allocation Agent Item, IsAllocationOf A goods ∧ EnvyBoundedBy v A α := by
  exact exists_envyBounded_allocation_of_acyclicReduction v hαnonneg hmargin
    (hasAcyclicReduction_of_improvingRotationExtraction v hextract)

/--
Paper-level bounded-envy theorem with the finite graph work isolated as an
explicit envy-cycle permutation extractor.
-/
theorem exists_envyBounded_allocation_of_envyCyclePermutationExtraction
    [Finite Agent] [Finite Item] [DecidableEq Item] [Nonempty Agent]
    (v : Valuation Agent Item) {α : ℝ}
    (hαnonneg : 0 ≤ α)
    (hmargin : MarginalBound v α)
    (hextract : HasEnvyCyclePermutationExtraction v) :
    ∀ goods : Finset Item,
      ∃ A : Allocation Agent Item, IsAllocationOf A goods ∧ EnvyBoundedBy v A α := by
  exact exists_envyBounded_allocation_of_acyclicReduction v hαnonneg hmargin
    (hasAcyclicReduction_of_envyCyclePermutationExtraction v hextract)

/--
Paper-level bounded-envy theorem with the finite graph work isolated as a
simple-cycle list extractor.
-/
theorem exists_envyBounded_allocation_of_envyCycleListExtraction
    [Finite Agent] [Finite Item] [DecidableEq Agent] [DecidableEq Item] [Nonempty Agent]
    (v : Valuation Agent Item) {α : ℝ}
    (hαnonneg : 0 ≤ α)
    (hmargin : MarginalBound v α)
    (hextract : HasEnvyCycleListExtraction v) :
    ∀ goods : Finset Item,
      ∃ A : Allocation Agent Item, IsAllocationOf A goods ∧ EnvyBoundedBy v A α := by
  exact exists_envyBounded_allocation_of_acyclicReduction v hαnonneg hmargin
    (hasAcyclicReduction_of_envyCycleListExtraction v hextract)

/--
Finite version of a bounded-envy theorem.
For finite agents and finite goods, every set of goods admits an allocation in
which every pairwise envy is bounded by the maximum marginal value `α`.
-/
theorem exists_envyBounded_allocation_of_finite
    [Finite Agent] [Finite Item] [DecidableEq Item] [Nonempty Agent]
    (v : Valuation Agent Item) {α : ℝ}
    (hαnonneg : 0 ≤ α)
    (hmargin : MarginalBound v α) :
    ∀ goods : Finset Item,
      ∃ A : Allocation Agent Item, IsAllocationOf A goods ∧ EnvyBoundedBy v A α := by
  classical
  exact exists_envyBounded_allocation_of_envyCycleListExtraction v hαnonneg hmargin
    (hasEnvyCycleListExtraction_of_finite v)

/--
Paper-facing finite statement of a bounded-envy theorem:
under a maximum marginal bound `α`, every finite set of indivisible goods has an
allocation whose pairwise envy is bounded by `α`.
-/
theorem lmms_theorem_2_1_finite
    [Finite Agent] [Finite Item] [DecidableEq Item] [Nonempty Agent]
    (v : Valuation Agent Item) {α : ℝ}
    (hαnonneg : 0 ≤ α)
    (hmargin : MarginalBound v α) :
    ∀ goods : Finset Item,
      ∃ A : Allocation Agent Item, IsAllocationOf A goods ∧ EnvyBoundedBy v A α := by
  exact exists_envyBounded_allocation_of_finite v hαnonneg hmargin

/--
Finite bounded-envy theorem with `α` instantiated as the maximum one-good
marginal value over the finite economy.
-/
theorem lmms_theorem_2_1_finite_maxMarginal
    [Fintype Agent] [Fintype Item] [DecidableEq Item]
    [Nonempty Agent] [Nonempty Item]
    (v : Valuation Agent Item) :
    ∀ goods : Finset Item,
      ∃ A : Allocation Agent Item, IsAllocationOf A goods ∧
        EnvyBoundedBy v A (maxMarginal v) := by
  exact lmms_theorem_2_1_finite v
    (maxMarginal_nonneg v) (marginalBound_maxMarginal v)

end FairDivision
end AppliedModelingLib
