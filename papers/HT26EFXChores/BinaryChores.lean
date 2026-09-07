import AppliedModelingLib.SocialChoice.FairDivision.Chores

/-!
# Binary additive chores

The main He--Tao manuscript deliberately sets aside the degenerate
`{0,q}` branch (source lines 294--296), citing the binary-chore result of
Tao--Wu--Yu--Zhou instead.  This module develops that source-compatible
branch from first principles.  The first phase of their algorithm assigns
every non-universal chore to an agent who incurs zero cost.  Later lemmas will
formalize the balancing/reallocation phase for the universally costly chores.

Reference for the algorithmic route: Tao, Wu, Yu, and Zhou, *On the Existence
of EFX (and Pareto-Optimal) Allocations for Binary Chores*, Algorithm 1 and
Lemma 3.3 (arXiv:2308.12177).
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- A binary additive chore-cost profile has only the individual costs zero
and one.  The positive `{0,q}` branch is reduced to this profile by positive
rescaling. -/
def IsZeroOrOneChoreCost {Agent Item : Type*} (cost : ChoreCost Agent Item) : Prop :=
  ∀ agent item, cost agent item = 0 ∨ cost agent item = 1

/-- Chores with at least one zero-cost owner.  This is `M⁰` in the binary
algorithm. -/
noncomputable def zeroableChorePool {Agent Item : Type*} [DecidableEq Item]
    (cost : ChoreCost Agent Item) (chores : Finset Item) : Finset Item :=
  @Finset.filter _ (fun item => ∃ agent, cost agent item = 0) (Classical.decPred _) chores

/-- Chores that cost one to every agent.  This is `M⁺` in the binary
algorithm. -/
noncomputable def universalChorePool {Agent Item : Type*} [DecidableEq Item]
    (cost : ChoreCost Agent Item) (chores : Finset Item) : Finset Item :=
  @Finset.filter _ (fun item => ∀ agent, cost agent item = 1) (Classical.decPred _) chores

/-- Binary costs are nonnegative. -/
theorem IsZeroOrOneChoreCost.nonneg {Agent Item : Type*}
    (cost : ChoreCost Agent Item) (hbinary : IsZeroOrOneChoreCost cost) :
    ∀ agent item, 0 ≤ cost agent item := by
  intro agent item
  rcases hbinary agent item with hzero | hone
  · linarith
  · linarith

/-- Membership in the zeroable pool exposes its source-pool and zero-owner
conditions without exposing the noncomputable filter's decidability witness. -/
theorem mem_zeroableChorePool_iff
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (item : Item) :
    item ∈ zeroableChorePool cost chores ↔
      item ∈ chores ∧ ∃ agent, cost agent item = 0 := by
  letI : DecidablePred (fun chore : Item => ∃ agent : Fin 4, cost agent chore = 0) :=
    Classical.decPred _
  simp only [zeroableChorePool, Finset.mem_filter]

/-- Membership in the universally costly pool exposes its source-pool and
all-agents-one conditions without exposing the filter implementation. -/
theorem mem_universalChorePool_iff
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (item : Item) :
    item ∈ universalChorePool cost chores ↔
      item ∈ chores ∧ ∀ agent, cost agent item = 1 := by
  letI : DecidablePred (fun chore : Item => ∀ agent : Fin 4, cost agent chore = 1) :=
    Classical.decPred _
  simp only [universalChorePool, Finset.mem_filter]

/-- The zeroable and universal pools partition a binary chore pool. -/
theorem zeroableChorePool_union_universalChorePool_eq
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hbinary : IsZeroOrOneChoreCost cost) :
    zeroableChorePool cost chores ∪ universalChorePool cost chores = chores := by
  ext item
  constructor
  · intro hmem
    rcases Finset.mem_union.mp hmem with hzeroable | huniversal
    · exact (mem_zeroableChorePool_iff Item cost chores item).mp hzeroable |>.1
    · exact (mem_universalChorePool_iff Item cost chores item).mp huniversal |>.1
  · intro hmem
    by_cases hzero : ∃ agent, cost agent item = 0
    · apply Finset.mem_union_left
      exact (mem_zeroableChorePool_iff Item cost chores item).mpr ⟨hmem, hzero⟩
    · apply Finset.mem_union_right
      refine (mem_universalChorePool_iff Item cost chores item).mpr ⟨hmem, ?_⟩
      intro agent
      rcases hbinary agent item with hagentZero | hagentOne
      · exact (hzero ⟨agent, hagentZero⟩).elim
      · exact hagentOne

/-- The two binary pools are disjoint. -/
theorem zeroableChorePool_disjoint_universalChorePool
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) :
    Disjoint (zeroableChorePool cost chores) (universalChorePool cost chores) := by
  rw [Finset.disjoint_left]
  intro item hzeroable huniversal
  have hzeroableData := (mem_zeroableChorePool_iff Item cost chores item).mp hzeroable
  obtain ⟨zeroAgent, hzero⟩ := hzeroableData.2
  have huniversalData := (mem_universalChorePool_iff Item cost chores item).mp huniversal
  have hone := huniversalData.2 zeroAgent
  linarith

/-- Deterministically select a zero-cost owner whenever one exists. -/
noncomputable def binaryZeroOwner (Item : Type) (cost : ChoreCost (Fin 4) Item) :
    Item → Option (Fin 4) := by
  classical
  exact fun item => if h : ∃ agent, cost agent item = 0 then some h.choose else none

/-- Every zeroable chore has a selected owner who finds it free. -/
theorem exists_binaryZeroOwner_of_mem_zeroableChorePool
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) {item : Item}
    (hitem : item ∈ zeroableChorePool cost chores) :
    ∃ agent, binaryZeroOwner Item cost item = some agent ∧ cost agent item = 0 := by
  classical
  have hzero : ∃ agent, cost agent item = 0 :=
    (mem_zeroableChorePool_iff Item cost chores item).mp hitem |>.2
  refine ⟨hzero.choose, ?_, hzero.choose_spec⟩
  simp [binaryZeroOwner, hzero]

/-- Phase 1 of the binary-chore algorithm: allocate every zeroable chore to
the selected zero-cost owner, leaving universal chores unallocated. -/
noncomputable def binaryZeroAllocation (Item : Type) [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) : Allocation (Fin 4) Item :=
  allocationOfOwner (zeroableChorePool cost chores) (binaryZeroOwner Item cost)

/-- The phase-1 binary allocation is feasible for the zeroable pool. -/
theorem binaryZeroAllocation_isAllocationOf
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) :
    IsAllocationOf (binaryZeroAllocation Item cost chores) (zeroableChorePool cost chores) := by
  apply isAllocationOf_allocationOfOwner
  intro item hitem
  obtain ⟨agent, howner, _⟩ :=
    exists_binaryZeroOwner_of_mem_zeroableChorePool Item cost chores hitem
  exact ⟨agent, howner⟩

/-- Every phase-1 owner incurs zero cost for every chore in her own bundle. -/
theorem binaryZeroAllocation_owner_cost_zero
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (agent : Fin 4) {item : Item}
    (hitem : item ∈ binaryZeroAllocation Item cost chores agent) :
    cost agent item = 0 := by
  have hfilter : item ∈ zeroableChorePool cost chores ∧
      binaryZeroOwner Item cost item = some agent := by
    simpa [binaryZeroAllocation, allocationOfOwner] using hitem
  obtain ⟨zeroOwner, howner, hzero⟩ :=
    exists_binaryZeroOwner_of_mem_zeroableChorePool Item cost chores hfilter.1
  have hownersEq : zeroOwner = agent :=
    Option.some.inj (howner.symm.trans hfilter.2)
  simpa [hownersEq] using hzero

/-- Phase 1 is already EFX: every agent's own bundle has zero cost. -/
theorem binaryZeroAllocation_efx
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hbinary : IsZeroOrOneChoreCost cost) :
    EFXForChores (additiveChoreCost cost) (binaryZeroAllocation Item cost chores) := by
  intro agent comparison
  by_cases hempty : binaryZeroAllocation Item cost chores agent = ∅
  · exact Or.inl hempty
  · right
    intro item hitem
    have hself : additiveChoreCost cost agent
        (binaryZeroAllocation Item cost chores agent) = 0 := by
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent
        (binaryZeroAllocation Item cost chores agent) 0]
      · simp
      · intro owned howned
        exact binaryZeroAllocation_owner_cost_zero Item cost chores agent howned
    have hremoved := additiveChoreCost_erase cost agent
      (binaryZeroAllocation Item cost chores agent) item hitem
    have hcomparisonNonneg := additiveChoreCost_nonneg cost hbinary.nonneg agent
      (binaryZeroAllocation Item cost chores comparison)
    have hitemZero := binaryZeroAllocation_owner_cost_zero Item cost chores agent hitem
    rw [hself, hitemZero] at hremoved
    linarith

/-- The number of universally costly chores currently held by an agent.  In a
binary-stage allocation this is exactly that agent's own additive cost. -/
def universalLoad {Item : Type} [DecidableEq Item]
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item) (agent : Fin 4) : ℕ :=
  (allocation agent ∩ universal).card

/-- The invariant maintained while Algorithm 1 distributes universal chores.
Every non-universal owned item remains free for its owner, universal loads
remain within one, and the partial allocation is EFX. -/
def BinaryUniversalInvariant {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (universal : Finset Item)
    (allocation : Allocation (Fin 4) Item) : Prop :=
  (∀ agent item, item ∈ allocation agent → item ∉ universal → cost agent item = 0) ∧
  (∀ first second,
    universalLoad universal allocation first ≤ universalLoad universal allocation second + 1) ∧
  EFXForChores (additiveChoreCost cost) allocation

/-- In the phase-1 allocation no universal chore has yet been allocated. -/
theorem universalLoad_binaryZeroAllocation_eq_zero
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (agent : Fin 4) :
    universalLoad (universalChorePool cost chores) (binaryZeroAllocation Item cost chores) agent = 0 := by
  have hdisjoint : Disjoint (binaryZeroAllocation Item cost chores agent)
      (universalChorePool cost chores) := by
    rw [Finset.disjoint_left]
    intro item howned huniversal
    have hzeroable : item ∈ zeroableChorePool cost chores :=
      (binaryZeroAllocation_isAllocationOf Item cost chores).1 agent item howned
    exact (Finset.disjoint_left.mp
      (zeroableChorePool_disjoint_universalChorePool Item cost chores) hzeroable huniversal).elim
  unfold universalLoad
  rw [Finset.disjoint_iff_inter_eq_empty.mp hdisjoint]
  rfl

/-- Phase 1 establishes the full binary universal-chore invariant. -/
theorem binaryZeroAllocation_invariant
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hbinary : IsZeroOrOneChoreCost cost) :
    BinaryUniversalInvariant cost (universalChorePool cost chores)
      (binaryZeroAllocation Item cost chores) := by
  refine ⟨?_, ?_, binaryZeroAllocation_efx Item cost chores hbinary⟩
  · intro agent item howned _
    exact binaryZeroAllocation_owner_cost_zero Item cost chores agent howned
  · intro first second
    rw [universalLoad_binaryZeroAllocation_eq_zero,
      universalLoad_binaryZeroAllocation_eq_zero]
    omega

/-- Under the binary-stage ownership invariant, an agent's own cost is the
number of universal chores in her bundle. -/
theorem additiveChoreCost_eq_universalLoad_of_binary_owner_invariant
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (huniversal : ∀ item ∈ universal, ∀ agent, cost agent item = 1)
    (hzeroOutside : ∀ agent item, item ∈ allocation agent → item ∉ universal →
      cost agent item = 0) (agent : Fin 4) :
    additiveChoreCost cost agent (allocation agent) =
      (universalLoad universal allocation agent : ℝ) := by
  have hsplit : allocation agent =
      (allocation agent ∩ universal) ∪ (allocation agent \ universal) := by
    rw [Finset.union_comm, Finset.sdiff_union_inter]
  rw [hsplit, additiveChoreCost_union cost agent (allocation agent ∩ universal)
    (allocation agent \ universal) (Finset.disjoint_sdiff_inter _ _).symm]
  rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent
      (allocation agent ∩ universal) 1,
    additiveChoreCost_eq_card_nsmul_of_constant cost agent
      (allocation agent \ universal) 0]
  · simp [universalLoad]
  · intro item hitem
    exact hzeroOutside agent item (Finset.mem_sdiff.mp hitem).1
      (Finset.mem_sdiff.mp hitem).2
  · intro item hitem
    exact huniversal item (Finset.mem_inter.mp hitem).2 agent

/-- A least-loaded agent for a finite binary stage.  Ties are immaterial. -/
noncomputable def binaryMinLoadAgent (Item : Type) [DecidableEq Item]
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item) : Fin 4 :=
  Classical.choose (Finset.exists_min_image (Finset.univ : Finset (Fin 4))
    (universalLoad universal allocation) Finset.univ_nonempty)

/-- The selected binary-stage agent has weakly minimum universal load. -/
theorem binaryMinLoadAgent_le
    (Item : Type) [DecidableEq Item] (universal : Finset Item)
    (allocation : Allocation (Fin 4) Item) (agent : Fin 4) :
    universalLoad universal allocation (binaryMinLoadAgent Item universal allocation) ≤
      universalLoad universal allocation agent := by
  exact (Classical.choose_spec (Finset.exists_min_image (Finset.univ : Finset (Fin 4))
    (universalLoad universal allocation) Finset.univ_nonempty)).2 agent (Finset.mem_univ _)

/-- Adding a fresh universal chore increases only its owner's universal load. -/
theorem universalLoad_addItem_self
    (Item : Type) [DecidableEq Item] (universal : Finset Item)
    (allocation : Allocation (Fin 4) Item) (owner : Fin 4) (item : Item)
    (huniversal : item ∈ universal) (hfresh : item ∉ allocation owner) :
    universalLoad universal (addItem allocation owner item) owner =
      universalLoad universal allocation owner + 1 := by
  unfold universalLoad
  simp only [addItem, ↓reduceIte]
  rw [Finset.insert_inter_of_mem huniversal, Finset.card_insert_of_notMem]
  intro hmem
  exact hfresh (Finset.mem_inter.mp hmem).1

/-- Adding a chore leaves each other agent's universal load unchanged. -/
theorem universalLoad_addItem_of_ne
    (Item : Type) [DecidableEq Item] (universal : Finset Item)
    (allocation : Allocation (Fin 4) Item) (owner other : Fin 4) (item : Item)
    (hne : other ≠ owner) :
    universalLoad universal (addItem allocation owner item) other =
      universalLoad universal allocation other := by
  unfold universalLoad
  simp [addItem, hne]

/-- The direct branch of the binary algorithm preserves its invariant whenever
the selected least-loaded owner can receive the universal chore without
breaking EFX. -/
theorem BinaryUniversalInvariant.addItem_of_efx
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (owner : Fin 4) (item : Item)
    (hinvariant : BinaryUniversalInvariant cost universal allocation)
    (hminimum : ∀ agent,
      universalLoad universal allocation owner ≤ universalLoad universal allocation agent)
    (huniversal : item ∈ universal) (hfresh : ∀ agent, item ∉ allocation agent)
    (hefx : EFXForChores (additiveChoreCost cost) (addItem allocation owner item)) :
    BinaryUniversalInvariant cost universal (addItem allocation owner item) := by
  refine ⟨?_, ?_, hefx⟩
  · intro agent chore howned houtside
    by_cases hagent : agent = owner
    · subst agent
      simp only [addItem, ↓reduceIte] at howned
      rcases Finset.mem_insert.mp howned with hchore | hchore
      · subst chore
        exact (houtside huniversal).elim
      · exact hinvariant.1 owner chore hchore houtside
    · have hownedOld : chore ∈ allocation agent := by
        simpa [addItem, hagent] using howned
      exact hinvariant.1 agent chore hownedOld houtside
  · intro first second
    by_cases hfirst : first = owner
    · subst first
      by_cases hsecond : second = owner
      · subst second
        exact Nat.le_succ _
      · rw [universalLoad_addItem_self Item universal allocation owner item huniversal
            (hfresh owner),
          universalLoad_addItem_of_ne Item universal allocation owner second item hsecond]
        exact Nat.succ_le_succ (hminimum second)
    · by_cases hsecond : second = owner
      · subst second
        rw [universalLoad_addItem_of_ne Item universal allocation owner first item hfirst,
          universalLoad_addItem_self Item universal allocation owner item huniversal
            (hfresh owner)]
        exact Nat.le_trans (hinvariant.2.1 first owner) (by omega)
      · rw [universalLoad_addItem_of_ne Item universal allocation owner first item hfirst,
          universalLoad_addItem_of_ne Item universal allocation owner second item hsecond]
        exact hinvariant.2.1 first second

/-- Every observer assigns at least the universal load as much cost to a
bundle.  This is the lower-bound half of the binary repair argument. -/
theorem universalLoad_le_additiveChoreCost
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (hbinary : IsZeroOrOneChoreCost cost)
    (huniversal : ∀ item ∈ universal, ∀ agent, cost agent item = 1)
    (observer owner : Fin 4) :
    (universalLoad universal allocation owner : ℝ) ≤
      additiveChoreCost cost observer (allocation owner) := by
  have hsplit : allocation owner =
      (allocation owner ∩ universal) ∪ (allocation owner \ universal) := by
    rw [Finset.union_comm, Finset.sdiff_union_inter]
  rw [hsplit, additiveChoreCost_union cost observer (allocation owner ∩ universal)
    (allocation owner \ universal) (Finset.disjoint_sdiff_inter _ _).symm]
  rw [additiveChoreCost_eq_card_nsmul_of_constant cost observer
    (allocation owner ∩ universal) 1]
  · simp only [nsmul_eq_mul]
    have hnonnegative := additiveChoreCost_nonneg cost hbinary.nonneg observer
      (allocation owner \ universal)
    change ((allocation owner ∩ universal).card : ℝ) ≤
      ((allocation owner ∩ universal).card : ℝ) * 1 +
        additiveChoreCost cost observer (allocation owner \ universal)
    norm_num
    linarith
  · intro chore hchore
    exact huniversal chore (Finset.mem_inter.mp hchore).2 observer

/-- A bundle's cost is at least the number of universal chores it contains. -/
theorem universalCard_le_additiveChoreCost
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal bundle : Finset Item) (observer : Fin 4)
    (hbinary : IsZeroOrOneChoreCost cost)
    (huniversal : ∀ item ∈ universal, ∀ agent, cost agent item = 1) :
    ((bundle ∩ universal).card : ℝ) ≤ additiveChoreCost cost observer bundle := by
  have hsplit : bundle = (bundle ∩ universal) ∪ (bundle \ universal) := by
    rw [Finset.union_comm, Finset.sdiff_union_inter]
  calc
    ((bundle ∩ universal).card : ℝ) ≤
        additiveChoreCost cost observer ((bundle ∩ universal) ∪ (bundle \ universal)) := by
      rw [additiveChoreCost_union cost observer (bundle ∩ universal)
        (bundle \ universal) (Finset.disjoint_sdiff_inter _ _).symm]
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost observer (bundle ∩ universal) 1]
      · simp only [nsmul_eq_mul]
        have hnonnegative := additiveChoreCost_nonneg cost hbinary.nonneg observer (bundle \ universal)
        norm_num
        linarith
      · intro chore hchore
        exact huniversal chore (Finset.mem_inter.mp hchore).2 observer
    _ = additiveChoreCost cost observer bundle := by rw [← hsplit]

/-- A one-cost non-universal chore raises an observer's bundle cost by at
least one beyond its universal-cardinality lower bound. -/
theorem universalCard_add_one_le_additiveChoreCost_of_one_outside
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal bundle : Finset Item) (observer : Fin 4) (item : Item)
    (hbinary : IsZeroOrOneChoreCost cost)
    (huniversal : ∀ chore ∈ universal, ∀ agent, cost agent chore = 1)
    (hitem : item ∈ bundle) (houtside : item ∉ universal) (hone : cost observer item = 1) :
    ((bundle ∩ universal).card + 1 : ℕ) ≤ additiveChoreCost cost observer bundle := by
  have hset : (bundle \ {item}) ∩ universal = bundle ∩ universal := by
    ext chore
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hbundle, hne⟩, huniversalMem⟩
      exact ⟨hbundle, huniversalMem⟩
    · rintro ⟨hbundle, huniversalMem⟩
      refine ⟨⟨hbundle, ?_⟩, huniversalMem⟩
      intro heq
      subst chore
      exact houtside huniversalMem
  have hcard : ((bundle \ {item}) ∩ universal).card = (bundle ∩ universal).card :=
    congrArg Finset.card hset
  have hlower := universalCard_le_additiveChoreCost Item cost universal (bundle \ {item}) observer
    hbinary huniversal
  rw [hcard] at hlower
  have herase := additiveChoreCost_erase cost observer bundle item hitem
  rw [hone] at herase
  exact_mod_cast (show ((bundle ∩ universal).card : ℝ) + 1 ≤
    additiveChoreCost cost observer bundle by linarith)

/-- Adding a fresh chore has the expected additive-cost increment for every
observer. -/
theorem additiveChoreCost_addItem_owner_of_fresh
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item) (owner observer : Fin 4) (item : Item)
    (hfresh : item ∉ allocation owner) :
    additiveChoreCost cost observer (addItem allocation owner item owner) =
      additiveChoreCost cost observer (allocation owner) + cost observer item := by
  rw [show addItem allocation owner item owner = insert item (allocation owner) by simp [addItem]]
  rw [← Finset.singleton_union, additiveChoreCost_union cost observer {item} (allocation owner)]
  · simp [additiveChoreCost, add_comm]
  · rw [Finset.disjoint_left]
    intro chore hchore hmem
    have heq : chore = item := Finset.mem_singleton.mp hchore
    subst chore
    exact hfresh hmem

/-- A failed direct assignment has exactly the structure used by Algorithm
1's repair branch.  The failed owner and comparison have equal universal
loads; the witness removed from the owner is a zero-cost old chore; and every
one-cost item in the comparison bundle is universal. -/
theorem binaryDirectFailure_structure
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (owner comparison : Fin 4) (item : Item)
    (hbinary : IsZeroOrOneChoreCost cost)
    (huniversal : ∀ chore ∈ universal, ∀ agent, cost agent chore = 1)
    (hinvariant : BinaryUniversalInvariant cost universal allocation)
    (hminimum : ∀ agent,
      universalLoad universal allocation owner ≤ universalLoad universal allocation agent)
    (hfresh : ∀ agent, item ∉ allocation agent) (hitemUniversal : item ∈ universal)
    (hfailure : ∃ removed ∈ addItem allocation owner item owner,
      additiveChoreCost cost owner (addItem allocation owner item owner \ {removed}) >
        additiveChoreCost cost owner (addItem allocation owner item comparison)) :
    comparison ≠ owner ∧
      universalLoad universal allocation owner = universalLoad universal allocation comparison ∧
      (∀ chore ∈ allocation comparison, cost owner chore = 1 → chore ∈ universal) ∧
      ∃ zeroChore ∈ allocation owner, cost owner zeroChore = 0 := by
  rcases hfailure with ⟨removed, hremoved, hstrict⟩
  have hnonnegative : ∀ agent chore, 0 ≤ cost agent chore :=
    IsZeroOrOneChoreCost.nonneg cost hbinary
  have hownerCost := additiveChoreCost_eq_universalLoad_of_binary_owner_invariant Item cost
    universal allocation huniversal hinvariant.1 owner
  have haugCost : additiveChoreCost cost owner (addItem allocation owner item owner) =
      (universalLoad universal allocation owner : ℝ) + 1 := by
    rw [additiveChoreCost_addItem_owner_of_fresh Item cost allocation owner owner item
      (hfresh owner), hownerCost, huniversal item hitemUniversal owner]
  have hcomparisonNe : comparison ≠ owner := by
    intro heq
    subst comparison
    have herase := additiveChoreCost_erase cost owner
      (addItem allocation owner item owner) removed hremoved
    linarith [hnonnegative owner removed]
  have hstrict' : additiveChoreCost cost owner
      (addItem allocation owner item owner \ {removed}) >
        additiveChoreCost cost owner (allocation comparison) := by
    simpa [addItem, hcomparisonNe] using hstrict
  have herase := additiveChoreCost_erase cost owner
    (addItem allocation owner item owner) removed hremoved
  have htargetLt : additiveChoreCost cost owner (allocation comparison) <
      (universalLoad universal allocation owner : ℝ) + 1 := by
    rw [haugCost] at herase
    linarith [hnonnegative owner removed]
  have hcomparisonLower := universalLoad_le_additiveChoreCost Item cost universal allocation
    hbinary huniversal owner comparison
  have hcomparisonLoadLt : universalLoad universal allocation comparison <
      universalLoad universal allocation owner + 1 := by
    have hcomparisonLoadLtReal : (universalLoad universal allocation comparison : ℝ) <
        (universalLoad universal allocation owner : ℝ) + 1 :=
      lt_of_le_of_lt hcomparisonLower htargetLt
    exact_mod_cast hcomparisonLoadLtReal
  have hloadEq : universalLoad universal allocation owner =
      universalLoad universal allocation comparison := by
    have hloadLower := hminimum comparison
    omega
  have htargetLower : (universalLoad universal allocation owner : ℝ) ≤
      additiveChoreCost cost owner (allocation comparison) := by
    calc
      (universalLoad universal allocation owner : ℝ) ≤
          (universalLoad universal allocation comparison : ℝ) := by
            exact_mod_cast hminimum comparison
      _ ≤ additiveChoreCost cost owner (allocation comparison) := hcomparisonLower
  have hremovedZero : cost owner removed = 0 := by
    rw [additiveChoreCost_erase cost owner (addItem allocation owner item owner) removed hremoved,
      haugCost] at hstrict'
    rcases hbinary owner removed with hzero | hone
    · exact hzero
    · linarith
  have hremovedOld : removed ∈ allocation owner := by
    have hremovedInsert : removed ∈ insert item (allocation owner) := by
      simpa [addItem] using hremoved
    rcases Finset.mem_insert.mp hremovedInsert with hnew | hold
    · subst removed
      have hone := huniversal item hitemUniversal owner
      linarith
    · exact hold
  refine ⟨hcomparisonNe, hloadEq, ?_, ⟨removed, hremovedOld, hremovedZero⟩⟩
  intro chore hchore hone
  by_contra hnotUniversal
  have htargetLarge := universalCard_add_one_le_additiveChoreCost_of_one_outside Item cost
    universal (allocation comparison) owner chore hbinary huniversal hchore hnotUniversal hone
  change ((universalLoad universal allocation comparison + 1 : ℕ) : ℝ) ≤
    additiveChoreCost cost owner (allocation comparison) at htargetLarge
  rw [← hloadEq] at htargetLarge
  push_cast at htargetLarge
  linarith

/-- After adding one fresh chore, all EFX comparisons not originating at the
new owner are inherited automatically.  Thus Algorithm 1 only needs to test
the new owner before choosing its direct versus repair branch. -/
theorem efxForChores_addItem_of_owner_efx
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item) (owner : Fin 4) (item : Item)
    (hbinary : IsZeroOrOneChoreCost cost)
    (hfresh : item ∉ allocation owner)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (howner : ∀ comparison,
      DoesNotStronglyEnvyForChores (additiveChoreCost cost)
        (addItem allocation owner item) owner comparison) :
    EFXForChores (additiveChoreCost cost) (addItem allocation owner item) := by
  intro agent comparison
  by_cases hagent : agent = owner
  · subst agent
    exact howner comparison
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
        have htarget : additiveChoreCost cost agent (allocation owner) ≤
            additiveChoreCost cost agent (insert item (allocation owner)) := by
          rw [← Finset.singleton_union, additiveChoreCost_union cost agent {item}
            (allocation owner)]
          · simp only [additiveChoreCost, Finset.sum_singleton]
            linarith [IsZeroOrOneChoreCost.nonneg cost hbinary agent item]
          · rw [Finset.disjoint_left]
            intro chore hchore hmem
            have hitem : chore = item := Finset.mem_singleton.mp hchore
            subst chore
            exact hfresh hmem
        simpa [addItem, hagent] using hold.trans htarget
      · simpa [addItem, hagent, hcomparison] using hold

/-- The part of a bundle that costs zero to a designated observer.  This is
the transfer set in the repair branch of Algorithm 1. -/
noncomputable def zeroCostSubbundle {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (observer : Fin 4) (bundle : Finset Item) : Finset Item :=
  @Finset.filter _ (fun item => cost observer item = 0) (Classical.decPred _) bundle

/-- The part of a binary bundle that costs one to a designated observer. -/
noncomputable def oneCostSubbundle {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (observer : Fin 4) (bundle : Finset Item) : Finset Item :=
  @Finset.filter _ (fun item => cost observer item = 1) (Classical.decPred _) bundle

/-- Membership in a zero-cost transfer set. -/
theorem mem_zeroCostSubbundle_iff
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (observer : Fin 4) (bundle : Finset Item) (item : Item) :
    item ∈ zeroCostSubbundle cost observer bundle ↔
      item ∈ bundle ∧ cost observer item = 0 := by
  letI : DecidablePred (fun chore : Item => cost observer chore = 0) := Classical.decPred _
  simp only [zeroCostSubbundle, Finset.mem_filter]

/-- Membership in a one-cost residual set. -/
theorem mem_oneCostSubbundle_iff
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (observer : Fin 4) (bundle : Finset Item) (item : Item) :
    item ∈ oneCostSubbundle cost observer bundle ↔
      item ∈ bundle ∧ cost observer item = 1 := by
  letI : DecidablePred (fun chore : Item => cost observer chore = 1) := Classical.decPred _
  simp only [oneCostSubbundle, Finset.mem_filter]

/-- In a binary profile, the zero and one parts partition every bundle. -/
theorem zeroCostSubbundle_union_oneCostSubbundle_eq
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (observer : Fin 4) (bundle : Finset Item) (hbinary : IsZeroOrOneChoreCost cost) :
    zeroCostSubbundle cost observer bundle ∪ oneCostSubbundle cost observer bundle = bundle := by
  ext item
  constructor
  · intro hitem
    rcases Finset.mem_union.mp hitem with hzero | hone
    · exact (mem_zeroCostSubbundle_iff Item cost observer bundle item).mp hzero |>.1
    · exact (mem_oneCostSubbundle_iff Item cost observer bundle item).mp hone |>.1
  · intro hitem
    rcases hbinary observer item with hzero | hone
    · exact Finset.mem_union_left _
        ((mem_zeroCostSubbundle_iff Item cost observer bundle item).mpr ⟨hitem, hzero⟩)
    · exact Finset.mem_union_right _
        ((mem_oneCostSubbundle_iff Item cost observer bundle item).mpr ⟨hitem, hone⟩)

/-- The two repair pieces are disjoint. -/
theorem zeroCostSubbundle_disjoint_oneCostSubbundle
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (observer : Fin 4) (bundle : Finset Item) :
    Disjoint (zeroCostSubbundle cost observer bundle) (oneCostSubbundle cost observer bundle) := by
  rw [Finset.disjoint_left]
  intro item hzero hone
  have hzero' := (mem_zeroCostSubbundle_iff Item cost observer bundle item).mp hzero
  have hone' := (mem_oneCostSubbundle_iff Item cost observer bundle item).mp hone
  linarith

/-- The repair branch of Algorithm 1.  A failed least-loaded owner keeps her
old bundle, takes every chore in the comparison bundle that is free for her,
and gives the new universal chore plus the residual one-cost part to that
comparison agent. -/
noncomputable def binaryRepairAllocation (Item : Type) [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (allocation : Allocation (Fin 4) Item)
    (owner comparison : Fin 4) (item : Item) : Allocation (Fin 4) Item :=
  fun agent =>
    if agent = owner then allocation owner ∪ zeroCostSubbundle cost owner (allocation comparison)
    else if agent = comparison then insert item (oneCostSubbundle cost owner (allocation comparison))
    else allocation agent

theorem binaryRepairAllocation_owner
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item) (owner comparison : Fin 4) (item : Item) :
    binaryRepairAllocation Item cost allocation owner comparison item owner =
      allocation owner ∪ zeroCostSubbundle cost owner (allocation comparison) := by
  simp [binaryRepairAllocation]

theorem binaryRepairAllocation_comparison
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item) (owner comparison : Fin 4) (item : Item)
    (hne : comparison ≠ owner) :
    binaryRepairAllocation Item cost allocation owner comparison item comparison =
      insert item (oneCostSubbundle cost owner (allocation comparison)) := by
  simp [binaryRepairAllocation, hne]

theorem binaryRepairAllocation_other
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item) (owner comparison other : Fin 4) (item : Item)
    (howner : other ≠ owner) (hcomparison : other ≠ comparison) :
    binaryRepairAllocation Item cost allocation owner comparison item other = allocation other := by
  simp [binaryRepairAllocation, howner, hcomparison]

theorem zeroCostSubbundle_subset
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (observer : Fin 4) (bundle : Finset Item) :
    zeroCostSubbundle cost observer bundle ⊆ bundle := by
  intro item hitem
  exact (mem_zeroCostSubbundle_iff Item cost observer bundle item).mp hitem |>.1

theorem oneCostSubbundle_subset
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (observer : Fin 4) (bundle : Finset Item) :
    oneCostSubbundle cost observer bundle ⊆ bundle := by
  intro item hitem
  exact (mem_oneCostSubbundle_iff Item cost observer bundle item).mp hitem |>.1

/-- Every bundle in a repaired allocation stays inside the original pool plus
the newly assigned universal chore. -/
theorem binaryRepairAllocation_mem_insert_goods
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item) (goods : Finset Item)
    (owner comparison : Fin 4) (item : Item) (hne : owner ≠ comparison)
    (halloc : IsAllocationOf allocation goods) :
    ∀ agent chore, chore ∈ binaryRepairAllocation Item cost allocation owner comparison item agent →
      chore ∈ insert item goods := by
  intro agent chore hchore
  by_cases hagentOwner : agent = owner
  · subst agent
    rw [binaryRepairAllocation_owner] at hchore
    rcases Finset.mem_union.mp hchore with hown | htransfer
    · exact Finset.mem_insert.mpr (Or.inr (halloc.1 owner chore hown))
    · exact Finset.mem_insert.mpr (Or.inr
        (halloc.1 comparison chore (zeroCostSubbundle_subset Item cost owner
          (allocation comparison) htransfer)))
  · by_cases hagentComparison : agent = comparison
    · subst agent
      rw [binaryRepairAllocation_comparison Item cost allocation owner comparison item hne.symm] at hchore
      rcases Finset.mem_insert.mp hchore with hnew | hresidual
      · exact Finset.mem_insert.mpr (Or.inl hnew)
      · exact Finset.mem_insert.mpr (Or.inr
          (halloc.1 comparison chore (oneCostSubbundle_subset Item cost owner
            (allocation comparison) hresidual)))
    · rw [binaryRepairAllocation_other Item cost allocation owner comparison agent item hagentOwner
        hagentComparison] at hchore
      exact Finset.mem_insert.mpr (Or.inr (halloc.1 agent chore hchore))

/-- The repair operation preserves a disjoint complete allocation while adding
exactly the new chore.  This is the finite-partition component of Algorithm
1's repair branch. -/
theorem binaryRepairAllocation_isAllocationOf
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item) (goods : Finset Item)
    (owner comparison : Fin 4) (item : Item) (hne : owner ≠ comparison)
    (hitem : item ∉ goods) (hbinary : IsZeroOrOneChoreCost cost)
    (halloc : IsAllocationOf allocation goods) :
    IsAllocationOf (binaryRepairAllocation Item cost allocation owner comparison item)
      (insert item goods) := by
  constructor
  · exact binaryRepairAllocation_mem_insert_goods Item cost allocation goods owner comparison item hne halloc
  · intro chore hchore
    rcases Finset.mem_insert.mp hchore with hnew | hold
    · refine ⟨comparison, ?_, ?_⟩
      · change chore ∈ binaryRepairAllocation Item cost allocation owner comparison item comparison
        rw [binaryRepairAllocation_comparison Item cost allocation owner comparison item hne.symm]
        exact Finset.mem_insert.mpr (Or.inl hnew)
      · intro agent hagent
        by_cases hagentComparison : agent = comparison
        · exact hagentComparison
        · by_cases hagentOwner : agent = owner
          · subst agent
            rw [binaryRepairAllocation_owner] at hagent
            rcases Finset.mem_union.mp hagent with howner | htransfer
            · exact (hitem (halloc.1 owner item (by simpa [hnew] using howner))).elim
            · exact (hitem (halloc.1 comparison item (by
                simpa [hnew] using zeroCostSubbundle_subset Item cost owner
                  (allocation comparison) htransfer))).elim
          · rw [binaryRepairAllocation_other Item cost allocation owner comparison agent item hagentOwner
              hagentComparison] at hagent
            exact (hitem (halloc.1 agent item (by simpa [hnew] using hagent))).elim
    · obtain ⟨oldOwner, howned, hunique⟩ := halloc.2 chore hold
      by_cases holdOwner : oldOwner = owner
      · subst oldOwner
        refine ⟨owner, ?_, ?_⟩
        · change chore ∈ binaryRepairAllocation Item cost allocation owner comparison item owner
          rw [binaryRepairAllocation_owner]
          exact Finset.mem_union_left _ howned
        · intro agent hagent
          by_cases hagentOwner : agent = owner
          · exact hagentOwner
          · by_cases hagentComparison : agent = comparison
            · subst agent
              rw [binaryRepairAllocation_comparison Item cost allocation owner comparison item hne.symm]
                at hagent
              have hneItem : chore ≠ item := by
                intro heq
                subst chore
                exact hitem hold
              have hresidual : chore ∈ oneCostSubbundle cost owner (allocation comparison) := by
                rcases Finset.mem_insert.mp hagent with hnew | hresidual
                · exact (hneItem hnew).elim
                · exact hresidual
              have hcomparisonOwned : chore ∈ allocation comparison :=
                oneCostSubbundle_subset Item cost owner (allocation comparison) hresidual
              exact (hne (hunique comparison hcomparisonOwned).symm).elim
            · rw [binaryRepairAllocation_other Item cost allocation owner comparison agent item hagentOwner
                hagentComparison] at hagent
              exact hunique agent hagent
      · by_cases holdComparison : oldOwner = comparison
        · subst oldOwner
          rcases hbinary owner chore with hzero | hone
          · refine ⟨owner, ?_, ?_⟩
            · change chore ∈ binaryRepairAllocation Item cost allocation owner comparison item owner
              rw [binaryRepairAllocation_owner]
              apply Finset.mem_union_right
              exact (mem_zeroCostSubbundle_iff Item cost owner (allocation comparison) chore).mpr
                ⟨howned, hzero⟩
            · intro agent hagent
              by_cases hagentOwner : agent = owner
              · exact hagentOwner
              · by_cases hagentComparison : agent = comparison
                · subst agent
                  rw [binaryRepairAllocation_comparison Item cost allocation owner comparison item hne.symm]
                    at hagent
                  have hneItem : chore ≠ item := by
                    intro heq
                    subst chore
                    exact hitem hold
                  have hresidual : chore ∈ oneCostSubbundle cost owner (allocation comparison) := by
                    rcases Finset.mem_insert.mp hagent with hnew | hresidual
                    · exact (hneItem hnew).elim
                    · exact hresidual
                  have hone' := (mem_oneCostSubbundle_iff Item cost owner
                    (allocation comparison) chore).mp hresidual |>.2
                  exact (by linarith : False).elim
                · rw [binaryRepairAllocation_other Item cost allocation owner comparison agent item hagentOwner
                    hagentComparison] at hagent
                  exact (hagentComparison (hunique agent hagent)).elim
          · refine ⟨comparison, ?_, ?_⟩
            · change chore ∈ binaryRepairAllocation Item cost allocation owner comparison item comparison
              rw [binaryRepairAllocation_comparison Item cost allocation owner comparison item hne.symm]
              apply Finset.mem_insert.mpr
              right
              exact (mem_oneCostSubbundle_iff Item cost owner (allocation comparison) chore).mpr
                ⟨howned, hone⟩
            · intro agent hagent
              by_cases hagentComparison : agent = comparison
              · exact hagentComparison
              · by_cases hagentOwner : agent = owner
                · subst agent
                  rw [binaryRepairAllocation_owner] at hagent
                  rcases Finset.mem_union.mp hagent with howner | htransfer
                  · exact (hne (hunique owner howner)).elim
                  · have hzero' := (mem_zeroCostSubbundle_iff Item cost owner
                      (allocation comparison) chore).mp htransfer |>.2
                    exact (by linarith : False).elim
                · rw [binaryRepairAllocation_other Item cost allocation owner comparison agent item hagentOwner
                    hagentComparison] at hagent
                  exact (hagentComparison (hunique agent hagent)).elim
        · refine ⟨oldOwner, ?_, ?_⟩
          · change chore ∈ binaryRepairAllocation Item cost allocation owner comparison item oldOwner
            rw [binaryRepairAllocation_other Item cost allocation owner comparison oldOwner item
              (fun heq => holdOwner heq) (fun heq => holdComparison heq)]
            exact howned
          · intro agent hagent
            by_cases hagentOld : agent = oldOwner
            · exact hagentOld
            · by_cases hagentOwner : agent = owner
              · subst agent
                rw [binaryRepairAllocation_owner] at hagent
                rcases Finset.mem_union.mp hagent with howner | htransfer
                · exact (holdOwner (hunique owner howner).symm).elim
                · have hcomparisonOwned : chore ∈ allocation comparison :=
                    zeroCostSubbundle_subset Item cost owner (allocation comparison) htransfer
                  exact (holdComparison (hunique comparison hcomparisonOwned).symm).elim
              · by_cases hagentComparison : agent = comparison
                · subst agent
                  rw [binaryRepairAllocation_comparison Item cost allocation owner comparison item hne.symm]
                    at hagent
                  have hneItem : chore ≠ item := by
                    intro heq
                    subst chore
                    exact hitem hold
                  have hresidual : chore ∈ oneCostSubbundle cost owner (allocation comparison) := by
                    rcases Finset.mem_insert.mp hagent with hnew | hresidual
                    · exact (hneItem hnew).elim
                    · exact hresidual
                  have hcomparisonOwned : chore ∈ allocation comparison :=
                    oneCostSubbundle_subset Item cost owner (allocation comparison) hresidual
                  exact (holdComparison (hunique comparison hcomparisonOwned).symm).elim
                · rw [binaryRepairAllocation_other Item cost allocation owner comparison agent item hagentOwner
                    hagentComparison] at hagent
                  exact hunique agent hagent

/-- A transferred zero-cost subbundle contains no universally costly chore. -/
theorem zeroCostSubbundle_disjoint_universal
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (observer : Fin 4) (bundle universal : Finset Item)
    (huniversal : ∀ item ∈ universal, ∀ agent, cost agent item = 1) :
    Disjoint (zeroCostSubbundle cost observer bundle) universal := by
  rw [Finset.disjoint_left]
  intro chore hzero hunivMem
  have hzero' := (mem_zeroCostSubbundle_iff Item cost observer bundle chore).mp hzero |>.2
  have hone := huniversal chore hunivMem observer
  linarith

/-- If every one-cost item in a residual bundle is universal, its one-cost
part is precisely the universal portion of that bundle. -/
theorem oneCostSubbundle_eq_inter_universal
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (observer : Fin 4) (bundle universal : Finset Item)
    (huniversal : ∀ item ∈ universal, ∀ agent, cost agent item = 1)
    (hresidual : ∀ item ∈ bundle, cost observer item = 1 → item ∈ universal) :
    oneCostSubbundle cost observer bundle = bundle ∩ universal := by
  ext item
  constructor
  · intro hitem
    have hdata := (mem_oneCostSubbundle_iff Item cost observer bundle item).mp hitem
    exact Finset.mem_inter.mpr ⟨hdata.1, hresidual item hdata.1 hdata.2⟩
  · intro hitem
    have hdata := Finset.mem_inter.mp hitem
    exact (mem_oneCostSubbundle_iff Item cost observer bundle item).mpr
      ⟨hdata.1, huniversal item hdata.2 observer⟩

/-- The repair does not change the failed owner's universal load: the only
transferred chores are free for her and hence cannot be universal. -/
theorem universalLoad_binaryRepair_owner
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (owner comparison : Fin 4) (item : Item)
    (huniversal : ∀ item ∈ universal, ∀ agent, cost agent item = 1) :
    universalLoad universal (binaryRepairAllocation Item cost allocation owner comparison item) owner =
      universalLoad universal allocation owner := by
  unfold universalLoad
  rw [binaryRepairAllocation_owner]
  have hdisjoint := zeroCostSubbundle_disjoint_universal Item cost owner
    (allocation comparison) universal huniversal
  have hset : ((allocation owner ∪ zeroCostSubbundle cost owner (allocation comparison)) ∩ universal) =
      allocation owner ∩ universal := by
    ext chore
    constructor
    · intro hmem
      rcases Finset.mem_inter.mp hmem with ⟨hunion, huniv⟩
      rcases Finset.mem_union.mp hunion with howner | hzero
      · exact Finset.mem_inter.mpr ⟨howner, huniv⟩
      · exact (Finset.disjoint_left.mp hdisjoint hzero huniv).elim
    · intro hmem
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hmem).1,
        (Finset.mem_inter.mp hmem).2⟩
  rw [hset]

/-- Once the residual one-cost part is exactly universal, repair increases the
comparison agent's universal load by one. -/
theorem universalLoad_binaryRepair_comparison
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (owner comparison : Fin 4) (item : Item) (hne : owner ≠ comparison)
    (huniversal : ∀ chore ∈ universal, ∀ agent, cost agent chore = 1)
    (hresidual : ∀ chore ∈ allocation comparison, cost owner chore = 1 → chore ∈ universal)
    (hfresh : item ∉ allocation comparison) (hitemUniversal : item ∈ universal) :
    universalLoad universal (binaryRepairAllocation Item cost allocation owner comparison item) comparison =
      universalLoad universal allocation comparison + 1 := by
  unfold universalLoad
  rw [binaryRepairAllocation_comparison Item cost allocation owner comparison item hne.symm,
    oneCostSubbundle_eq_inter_universal Item cost owner (allocation comparison) universal
      huniversal hresidual]
  rw [Finset.insert_inter_of_mem hitemUniversal, Finset.card_insert_of_notMem]
  · simp [Finset.inter_assoc]
  · intro hmem
    exact hfresh ((Finset.mem_inter.mp (Finset.mem_inter.mp hmem).1).1)

/-- Repair leaves all uninvolved agents' universal loads unchanged. -/
theorem universalLoad_binaryRepair_other
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (owner comparison other : Fin 4) (item : Item)
    (howner : other ≠ owner) (hcomparison : other ≠ comparison) :
    universalLoad universal (binaryRepairAllocation Item cost allocation owner comparison item) other =
      universalLoad universal allocation other := by
  unfold universalLoad
  rw [binaryRepairAllocation_other Item cost allocation owner comparison other item howner hcomparison]

/-- Repair preserves the invariant that every non-universal owned chore is
free for its owner. -/
theorem binaryRepairAllocation_owner_zero_outside_universal
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (owner comparison : Fin 4) (item : Item) (hne : owner ≠ comparison)
    (hzeroOutside : ∀ agent chore, chore ∈ allocation agent → chore ∉ universal →
      cost agent chore = 0)
    (hresidual : ∀ chore ∈ allocation comparison, cost owner chore = 1 → chore ∈ universal)
    (hitemUniversal : item ∈ universal) :
    ∀ agent chore, chore ∈ binaryRepairAllocation Item cost allocation owner comparison item agent →
      chore ∉ universal → cost agent chore = 0 := by
  intro agent chore howned houtside
  by_cases hagentOwner : agent = owner
  · subst agent
    rw [binaryRepairAllocation_owner] at howned
    rcases Finset.mem_union.mp howned with howned | htransfer
    · exact hzeroOutside owner chore howned houtside
    · exact (mem_zeroCostSubbundle_iff Item cost owner (allocation comparison) chore).mp htransfer |>.2
  · by_cases hagentComparison : agent = comparison
    · subst agent
      rw [binaryRepairAllocation_comparison Item cost allocation owner comparison item hne.symm] at howned
      rcases Finset.mem_insert.mp howned with hnew | hresidualMem
      · subst chore
        exact (houtside hitemUniversal).elim
      · have hdata := (mem_oneCostSubbundle_iff Item cost owner
          (allocation comparison) chore).mp hresidualMem
        exact (houtside (hresidual chore hdata.1 hdata.2)).elim
    · rw [binaryRepairAllocation_other Item cost allocation owner comparison agent item hagentOwner
        hagentComparison] at howned
      exact hzeroOutside agent chore howned houtside

/-- Under the equal-load failure structure, repair preserves the one-unit
universal-load balance. -/
theorem binaryRepairAllocation_balanced_universalLoads
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (owner comparison : Fin 4) (item : Item) (hne : owner ≠ comparison)
    (hbalance : ∀ first second,
      universalLoad universal allocation first ≤ universalLoad universal allocation second + 1)
    (hminimum : ∀ agent,
      universalLoad universal allocation owner ≤ universalLoad universal allocation agent)
    (hloadEq : universalLoad universal allocation owner = universalLoad universal allocation comparison)
    (huniversal : ∀ chore ∈ universal, ∀ agent, cost agent chore = 1)
    (hresidual : ∀ chore ∈ allocation comparison, cost owner chore = 1 → chore ∈ universal)
    (hfresh : ∀ agent, item ∉ allocation agent) (hitemUniversal : item ∈ universal) :
    ∀ first second,
      universalLoad universal (binaryRepairAllocation Item cost allocation owner comparison item) first ≤
        universalLoad universal (binaryRepairAllocation Item cost allocation owner comparison item) second + 1 := by
  intro first second
  by_cases hfirstOwner : first = owner
  · subst first
    by_cases hsecondOwner : second = owner
    · subst second
      exact Nat.le_succ _
    · by_cases hsecondComparison : second = comparison
      · subst second
        rw [universalLoad_binaryRepair_owner Item cost universal allocation owner comparison item huniversal,
          universalLoad_binaryRepair_comparison Item cost universal allocation owner comparison item hne
            huniversal hresidual (hfresh comparison) hitemUniversal, ← hloadEq]
        omega
      · rw [universalLoad_binaryRepair_owner Item cost universal allocation owner comparison item huniversal,
          universalLoad_binaryRepair_other Item cost universal allocation owner comparison second item
            hsecondOwner hsecondComparison]
        exact le_trans (hminimum second) (Nat.le_succ _)
  · by_cases hfirstComparison : first = comparison
    · subst first
      by_cases hsecondOwner : second = owner
      · subst second
        rw [universalLoad_binaryRepair_comparison Item cost universal allocation owner comparison item hne
            huniversal hresidual (hfresh comparison) hitemUniversal,
          universalLoad_binaryRepair_owner Item cost universal allocation owner comparison item huniversal,
          ← hloadEq]
      · by_cases hsecondComparison : second = comparison
        · subst second
          exact Nat.le_succ _
        · rw [universalLoad_binaryRepair_comparison Item cost universal allocation owner comparison item hne
            huniversal hresidual (hfresh comparison) hitemUniversal,
          universalLoad_binaryRepair_other Item cost universal allocation owner comparison second item
            hsecondOwner hsecondComparison, ← hloadEq]
          exact Nat.succ_le_succ (hminimum second)
    · by_cases hsecondOwner : second = owner
      · subst second
        rw [universalLoad_binaryRepair_other Item cost universal allocation owner comparison first item
            hfirstOwner hfirstComparison,
          universalLoad_binaryRepair_owner Item cost universal allocation owner comparison item huniversal]
        exact hbalance first owner
      · by_cases hsecondComparison : second = comparison
        · subst second
          rw [universalLoad_binaryRepair_other Item cost universal allocation owner comparison first item
              hfirstOwner hfirstComparison,
            universalLoad_binaryRepair_comparison Item cost universal allocation owner comparison item hne
              huniversal hresidual (hfresh comparison) hitemUniversal, ← hloadEq]
          have hbound := hbalance first owner
          omega
        · rw [universalLoad_binaryRepair_other Item cost universal allocation owner comparison first item
              hfirstOwner hfirstComparison,
            universalLoad_binaryRepair_other Item cost universal allocation owner comparison second item
              hsecondOwner hsecondComparison]
          exact hbalance first second

/-- In the repair branch, the comparison agent's final bundle consists only
of universal chores: the new item plus the retained one-cost residual. -/
theorem binaryRepairAllocation_comparison_all_universal
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (owner comparison : Fin 4) (item : Item) (hne : owner ≠ comparison)
    (huniversal : ∀ chore ∈ universal, ∀ agent, cost agent chore = 1)
    (hresidual : ∀ chore ∈ allocation comparison, cost owner chore = 1 → chore ∈ universal)
    (hitemUniversal : item ∈ universal) :
    ∀ observer chore,
      chore ∈ binaryRepairAllocation Item cost allocation owner comparison item comparison →
      cost observer chore = 1 := by
  intro observer chore hchore
  rw [binaryRepairAllocation_comparison Item cost allocation owner comparison item hne.symm] at hchore
  rcases Finset.mem_insert.mp hchore with hnew | hresidualMem
  · subst chore
    exact huniversal item hitemUniversal observer
  · have hdata := (mem_oneCostSubbundle_iff Item cost owner
      (allocation comparison) chore).mp hresidualMem
    exact huniversal chore (hresidual chore hdata.1 hdata.2) observer

/-- The comparison bundle produced by repair is a subset of the universal
pool. -/
theorem binaryRepairAllocation_comparison_subset_universal
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (owner comparison : Fin 4) (item : Item) (hne : owner ≠ comparison)
    (hresidual : ∀ chore ∈ allocation comparison, cost owner chore = 1 → chore ∈ universal)
    (hitemUniversal : item ∈ universal) :
    binaryRepairAllocation Item cost allocation owner comparison item comparison ⊆ universal := by
  intro chore hchore
  rw [binaryRepairAllocation_comparison Item cost allocation owner comparison item hne.symm] at hchore
  rcases Finset.mem_insert.mp hchore with hnew | hresidualMem
  · simpa [hnew] using hitemUniversal
  · have hdata := (mem_oneCostSubbundle_iff Item cost owner
      (allocation comparison) chore).mp hresidualMem
    exact hresidual chore hdata.1 hdata.2

/-- Adding a disjoint nonnegative-cost bundle cannot make a comparison bundle
cheaper for an observer. -/
theorem additiveChoreCost_le_union_of_nonneg
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (observer : Fin 4) (left right : Finset Item) (hdisjoint : Disjoint left right)
    (hnonnegative : ∀ chore ∈ right, 0 ≤ cost observer chore) :
    additiveChoreCost cost observer left ≤ additiveChoreCost cost observer (left ∪ right) := by
  rw [additiveChoreCost_union cost observer left right hdisjoint]
  apply le_add_of_nonneg_right
  unfold additiveChoreCost
  exact Finset.sum_nonneg fun chore hchore => hnonnegative chore hchore

/-- The repair branch preserves EFX.  This is the inductive calculation in
Lemma 3.3 of the binary-chore algorithm: the repaired owner has the minimum
universal load, the comparison bundle becomes universally costly, and all
other EFX comparisons are inherited or improve. -/
theorem binaryRepairAllocation_efx
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (owner comparison : Fin 4) (item : Item) (hne : owner ≠ comparison)
    (hbinary : IsZeroOrOneChoreCost cost)
    (huniversal : ∀ chore ∈ universal, ∀ agent, cost agent chore = 1)
    (goods : Finset Item) (halloc : IsAllocationOf allocation goods)
    (hinvariant : BinaryUniversalInvariant cost universal allocation)
    (hminimum : ∀ agent,
      universalLoad universal allocation owner ≤ universalLoad universal allocation agent)
    (hloadEq : universalLoad universal allocation owner = universalLoad universal allocation comparison)
    (hresidual : ∀ chore ∈ allocation comparison, cost owner chore = 1 → chore ∈ universal)
    (hfresh : ∀ agent, item ∉ allocation agent) (hitemUniversal : item ∈ universal) :
    EFXForChores (additiveChoreCost cost)
      (binaryRepairAllocation Item cost allocation owner comparison item) := by
  let repaired := binaryRepairAllocation Item cost allocation owner comparison item
  change EFXForChores (additiveChoreCost cost) repaired
  have hnonnegative : ∀ agent chore, 0 ≤ cost agent chore :=
    IsZeroOrOneChoreCost.nonneg cost hbinary
  have hzeroOutside := binaryRepairAllocation_owner_zero_outside_universal Item cost universal
    allocation owner comparison item hne hinvariant.1 hresidual hitemUniversal
  have hownerCost := additiveChoreCost_eq_universalLoad_of_binary_owner_invariant Item cost
    universal repaired huniversal hzeroOutside owner
  have hcomparisonSubset := binaryRepairAllocation_comparison_subset_universal Item cost universal
    allocation owner comparison item hne hresidual hitemUniversal
  have hcomparisonAll := binaryRepairAllocation_comparison_all_universal Item cost universal
    allocation owner comparison item hne huniversal hresidual hitemUniversal
  have hcomparisonCard : (repaired comparison).card = universalLoad universal repaired comparison := by
    unfold universalLoad
    exact congrArg Finset.card (Finset.inter_eq_left.mpr hcomparisonSubset).symm
  have hcomparisonCost (observer : Fin 4) : additiveChoreCost cost observer (repaired comparison) =
      (universalLoad universal allocation owner : ℝ) + 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost observer (repaired comparison) 1
      (hcomparisonAll observer), hcomparisonCard,
      universalLoad_binaryRepair_comparison Item cost universal allocation owner comparison item hne
        huniversal hresidual (hfresh comparison) hitemUniversal, ← hloadEq]
    norm_num [nsmul_eq_mul]
  have hloadLower (agent : Fin 4) : universalLoad universal allocation owner ≤
      universalLoad universal repaired agent := by
    by_cases hagentOwner : agent = owner
    · subst agent
      rw [universalLoad_binaryRepair_owner Item cost universal allocation owner comparison item huniversal]
    · by_cases hagentComparison : agent = comparison
      · subst agent
        rw [universalLoad_binaryRepair_comparison Item cost universal allocation owner comparison item hne
          huniversal hresidual (hfresh comparison) hitemUniversal, ← hloadEq]
        omega
      · rw [universalLoad_binaryRepair_other Item cost universal allocation owner comparison agent item
          hagentOwner hagentComparison]
        exact hminimum agent
  have htransferDisjoint : Disjoint (allocation owner)
      (zeroCostSubbundle cost owner (allocation comparison)) := by
    rw [Finset.disjoint_left]
    intro chore howner htransfer
    have hcomparison : chore ∈ allocation comparison :=
      zeroCostSubbundle_subset Item cost owner (allocation comparison) htransfer
    exact (Finset.disjoint_left.mp (halloc.disjoint_of_ne allocation goods hne)
      howner hcomparison).elim
  have hownerMonotone (observer : Fin 4) : additiveChoreCost cost observer (allocation owner) ≤
      additiveChoreCost cost observer (repaired owner) := by
    rw [show repaired owner = allocation owner ∪
      zeroCostSubbundle cost owner (allocation comparison) by
      simp [repaired, binaryRepairAllocation]]
    exact additiveChoreCost_le_union_of_nonneg Item cost observer (allocation owner)
      (zeroCostSubbundle cost owner (allocation comparison)) htransferDisjoint
      (fun chore _ => hnonnegative observer chore)
  intro agent target
  by_cases hagentOwner : agent = owner
  · subst agent
    right
    intro removed hremoved
    have htargetLower := universalLoad_le_additiveChoreCost Item cost universal repaired
      hbinary huniversal owner target
    calc
      additiveChoreCost cost owner (repaired owner \ {removed}) =
          additiveChoreCost cost owner (repaired owner) - cost owner removed :=
        additiveChoreCost_erase cost owner (repaired owner) removed hremoved
      _ ≤ (universalLoad universal allocation owner : ℝ) := by
        rw [hownerCost, universalLoad_binaryRepair_owner Item cost universal allocation owner comparison
          item huniversal]
        linarith [hnonnegative owner removed]
      _ ≤ (universalLoad universal repaired target : ℝ) := by
        exact_mod_cast hloadLower target
      _ ≤ additiveChoreCost cost owner (repaired target) := htargetLower
  · by_cases hagentComparison : agent = comparison
    · subst agent
      right
      intro removed hremoved
      have htargetLower := universalLoad_le_additiveChoreCost Item cost universal repaired
        hbinary huniversal comparison target
      calc
        additiveChoreCost cost comparison (repaired comparison \ {removed}) =
            additiveChoreCost cost comparison (repaired comparison) - cost comparison removed :=
          additiveChoreCost_erase cost comparison (repaired comparison) removed hremoved
        _ = (universalLoad universal allocation owner : ℝ) := by
          rw [hcomparisonCost comparison, hcomparisonAll comparison removed hremoved]
          norm_num
        _ ≤ (universalLoad universal repaired target : ℝ) := by
          exact_mod_cast hloadLower target
        _ ≤ additiveChoreCost cost comparison (repaired target) := htargetLower
    · by_cases hempty : allocation agent = ∅
      · left
        simp [repaired, binaryRepairAllocation, hagentOwner, hagentComparison, hempty]
      · right
        intro removed hremoved
        have hremovedOld : removed ∈ allocation agent := by
          simpa [repaired, binaryRepairAllocation, hagentOwner, hagentComparison] using hremoved
        by_cases htargetOwner : target = owner
        · subst target
          have hold := (hinvariant.2.2 agent owner).resolve_left hempty removed hremovedOld
          simpa [repaired, binaryRepairAllocation, hagentOwner, hagentComparison] using
            hold.trans (hownerMonotone agent)
        · by_cases htargetComparison : target = comparison
          · subst target
            rw [show repaired agent = allocation agent by
              simp [repaired, binaryRepairAllocation, hagentOwner, hagentComparison],
              additiveChoreCost_erase cost agent (allocation agent) removed hremovedOld,
              additiveChoreCost_eq_universalLoad_of_binary_owner_invariant Item cost universal
                allocation huniversal hinvariant.1 agent,
              hcomparisonCost agent]
            have hupper := hinvariant.2.1 agent owner
            have hupperReal : (universalLoad universal allocation agent : ℝ) ≤
                (universalLoad universal allocation owner : ℝ) + 1 := by
              exact_mod_cast hupper
            have hremNonneg := hnonnegative agent removed
            linarith
          · have hold := (hinvariant.2.2 agent target).resolve_left hempty removed hremovedOld
            simpa [repaired, binaryRepairAllocation, hagentOwner, hagentComparison,
              htargetOwner, htargetComparison] using hold

/-- The repair branch establishes the full binary universal-chore invariant. -/
theorem BinaryUniversalInvariant.repair
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal : Finset Item) (allocation : Allocation (Fin 4) Item)
    (goods : Finset Item) (owner comparison : Fin 4) (item : Item)
    (hbinary : IsZeroOrOneChoreCost cost)
    (huniversal : ∀ chore ∈ universal, ∀ agent, cost agent chore = 1)
    (halloc : IsAllocationOf allocation goods)
    (hinvariant : BinaryUniversalInvariant cost universal allocation)
    (hminimum : ∀ agent,
      universalLoad universal allocation owner ≤ universalLoad universal allocation agent)
    (hfresh : ∀ agent, item ∉ allocation agent) (hitemUniversal : item ∈ universal)
    (hfailure : ∃ removed ∈ addItem allocation owner item owner,
      additiveChoreCost cost owner (addItem allocation owner item owner \ {removed}) >
        additiveChoreCost cost owner (addItem allocation owner item comparison)) :
    BinaryUniversalInvariant cost universal
      (binaryRepairAllocation Item cost allocation owner comparison item) := by
  obtain ⟨hne, hloadEq, hresidual, _⟩ := binaryDirectFailure_structure Item cost universal allocation
    owner comparison item hbinary huniversal hinvariant hminimum hfresh hitemUniversal hfailure
  refine ⟨?_, ?_, ?_⟩
  · exact binaryRepairAllocation_owner_zero_outside_universal Item cost universal allocation owner
      comparison item hne.symm hinvariant.1 hresidual hitemUniversal
  · exact binaryRepairAllocation_balanced_universalLoads Item cost universal allocation owner comparison
      item hne.symm hinvariant.2.1 hminimum hloadEq huniversal hresidual hfresh hitemUniversal
  · exact binaryRepairAllocation_efx Item cost universal allocation owner comparison item hne.symm hbinary
      huniversal goods halloc hinvariant hminimum hloadEq hresidual hfresh hitemUniversal

/-- One iteration of the binary universal-chore phase.  The direct branch
adds the chore to a least-loaded owner; the alternative invokes the verified
repair branch. -/
theorem exists_binaryUniversal_step
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal goods : Finset Item) (allocation : Allocation (Fin 4) Item)
    (item : Item) (hbinary : IsZeroOrOneChoreCost cost)
    (huniversal : ∀ chore ∈ universal, ∀ agent, cost agent chore = 1)
    (hitemUniversal : item ∈ universal) (hitemFresh : item ∉ goods)
    (halloc : IsAllocationOf allocation goods)
    (hinvariant : BinaryUniversalInvariant cost universal allocation) :
    ∃ next : Allocation (Fin 4) Item,
      IsAllocationOf next (insert item goods) ∧ BinaryUniversalInvariant cost universal next := by
  let owner := binaryMinLoadAgent Item universal allocation
  have hminimum : ∀ agent,
      universalLoad universal allocation owner ≤ universalLoad universal allocation agent := by
    intro agent
    exact binaryMinLoadAgent_le Item universal allocation agent
  have hfresh : ∀ agent, item ∉ allocation agent := by
    intro agent hmem
    exact hitemFresh (halloc.1 agent item hmem)
  by_cases hdirect : ∀ comparison,
      DoesNotStronglyEnvyForChores (additiveChoreCost cost)
        (addItem allocation owner item) owner comparison
  · have hefx := efxForChores_addItem_of_owner_efx Item cost allocation owner item hbinary
      (hfresh owner) hinvariant.2.2 hdirect
    refine ⟨addItem allocation owner item,
      isAllocationOf_addItem_insert allocation goods owner item halloc hitemFresh, ?_⟩
    exact BinaryUniversalInvariant.addItem_of_efx Item cost universal allocation owner item hinvariant
      hminimum hitemUniversal hfresh hefx
  · simp only [DoesNotStronglyEnvyForChores] at hdirect
    push Not at hdirect
    obtain ⟨comparison, _, removed, hremoved, hstrict⟩ := hdirect
    have hfailure : ∃ removed ∈ addItem allocation owner item owner,
        additiveChoreCost cost owner (addItem allocation owner item owner \ {removed}) >
          additiveChoreCost cost owner (addItem allocation owner item comparison) :=
      ⟨removed, hremoved, hstrict⟩
    refine ⟨binaryRepairAllocation Item cost allocation owner comparison item,
      binaryRepairAllocation_isAllocationOf Item cost allocation goods owner comparison item
        (by
          obtain ⟨hne, _, _, _⟩ := binaryDirectFailure_structure Item cost universal allocation owner
            comparison item hbinary huniversal hinvariant hminimum hfresh hitemUniversal hfailure
          exact hne.symm)
        hitemFresh hbinary halloc, ?_⟩
    exact BinaryUniversalInvariant.repair Item cost universal allocation goods owner comparison item
      hbinary huniversal halloc hinvariant hminimum hfresh hitemUniversal hfailure

/-- Iterating the verified binary universal-chore step over a finite residual
pool preserves feasibility and the binary EFX invariant. -/
theorem exists_binaryUniversal_extension
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (universal remaining goods : Finset Item) (allocation : Allocation (Fin 4) Item)
    (hbinary : IsZeroOrOneChoreCost cost)
    (huniversal : ∀ chore ∈ universal, ∀ agent, cost agent chore = 1)
    (hremaining : ∀ chore ∈ remaining, chore ∈ universal)
    (hdisjoint : Disjoint remaining goods)
    (halloc : IsAllocationOf allocation goods)
    (hinvariant : BinaryUniversalInvariant cost universal allocation) :
    ∃ final : Allocation (Fin 4) Item,
      IsAllocationOf final (remaining ∪ goods) ∧ BinaryUniversalInvariant cost universal final := by
  induction remaining using Finset.induction_on generalizing goods allocation with
  | empty =>
      exact ⟨allocation, by simpa using halloc, hinvariant⟩
  | @insert item rest hitemNotMem ih =>
      have hitemUniversal : item ∈ universal := hremaining item (by simp)
      have hitemFresh : item ∉ goods := by
        intro hitemGoods
        exact (Finset.disjoint_left.mp hdisjoint (by simp) hitemGoods).elim
      obtain ⟨next, hnextAlloc, hnextInvariant⟩ :=
        exists_binaryUniversal_step Item cost universal goods allocation item hbinary huniversal
          hitemUniversal hitemFresh halloc hinvariant
      have hrestUniversal : ∀ chore ∈ rest, chore ∈ universal := by
        intro chore hchore
        exact hremaining chore (Finset.mem_insert_of_mem hchore)
      have hrestDisjoint : Disjoint rest (insert item goods) := by
        rw [Finset.disjoint_left]
        intro chore hrest hnewGoods
        rcases Finset.mem_insert.mp hnewGoods with hnew | hgoods
        · exact hitemNotMem (hnew ▸ hrest)
        · exact (Finset.disjoint_left.mp hdisjoint
            (Finset.mem_insert_of_mem hrest) hgoods).elim
      obtain ⟨final, hfinalAlloc, hfinalInvariant⟩ :=
        ih (goods := insert item goods) (allocation := next) hrestUniversal hrestDisjoint
          hnextAlloc hnextInvariant
      refine ⟨final, ?_, hfinalInvariant⟩
      simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hfinalAlloc

/-- Additive binary chore instances admit an EFX allocation.  This is the
self-contained `{0,1}` degeneracy branch deferred by He--Tao to the binary
chores literature. -/
theorem existsEfxOfZeroOrOneChoreCost
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hbinary : IsZeroOrOneChoreCost cost) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  let zeroable := zeroableChorePool cost chores
  let universal := universalChorePool cost chores
  have huniversal : ∀ chore ∈ universal, ∀ agent, cost agent chore = 1 := by
    intro chore hchore agent
    exact (mem_universalChorePool_iff Item cost chores chore).mp hchore |>.2 agent
  have hdisjoint : Disjoint universal zeroable := by
    simpa [universal, zeroable] using
      (zeroableChorePool_disjoint_universalChorePool Item cost chores).symm
  have hbaseAlloc : IsAllocationOf (binaryZeroAllocation Item cost chores) zeroable := by
    simpa [zeroable] using binaryZeroAllocation_isAllocationOf Item cost chores
  have hbaseInvariant : BinaryUniversalInvariant cost universal (binaryZeroAllocation Item cost chores) := by
    simpa [universal] using binaryZeroAllocation_invariant Item cost chores hbinary
  obtain ⟨allocation, halloc, hinvariant⟩ := exists_binaryUniversal_extension Item cost universal
    universal zeroable (binaryZeroAllocation Item cost chores) hbinary huniversal
    (fun chore hchore => hchore) hdisjoint hbaseAlloc hbaseInvariant
  refine ⟨allocation, ?_, hinvariant.2.2⟩
  have hpartition := zeroableChorePool_union_universalChorePool_eq Item cost chores hbinary
  have hpool : universal ∪ zeroable = chores := by
    simpa [universal, zeroable, Finset.union_comm] using hpartition
  rw [hpool] at halloc
  exact halloc

/-- Positive rescaling transfers the binary `{0,1}` theorem to every
positive `{0,q}` chore profile. -/
theorem existsEfxOfZeroOrQChoreCost
    (Item : Type) [DecidableEq Item] (q : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hq : 0 < q)
    (hvalues : ∀ agent item, cost agent item = 0 ∨ cost agent item = q) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  let scaled := rescaleChoreCost q⁻¹ cost
  have hscaled : IsZeroOrOneChoreCost scaled := by
    intro agent item
    rcases hvalues agent item with hzero | hqcost
    · left
      simp [scaled, rescaleChoreCost, hzero]
    · right
      simp [scaled, rescaleChoreCost, hqcost, hq.ne']
  obtain ⟨allocation, halloc, hefx⟩ := existsEfxOfZeroOrOneChoreCost Item scaled chores hscaled
  have hrestored := hefx.rescale_of_pos q scaled allocation hq
  have hscale : rescaleChoreCost q scaled = cost := by
    funext agent item
    simp [scaled, rescaleChoreCost, hq.ne']
  rw [hscale] at hrestored
  exact ⟨allocation, halloc, hrestored⟩

end HT26EFXChores
