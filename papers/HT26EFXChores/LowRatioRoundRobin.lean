import AppliedModelingLib.SocialChoice.FairDivision.Chores
import Mathlib.Tactic

/-!
# Low-ratio round-robin bridge

For the normalized `1 ≤ r ≤ 2` branch of He--Tao Theorem 3, agents choose a
minimum-cost remaining chore in round-robin order.  Equivalently, they choose a
maximum-weight good for the complementary weight `r - cᵢ(g)`.  This file
records the algebraic bridge from the standard goods-EF1 certificate for that
round-robin procedure to chore EFX in a full (equal-cardinality) round.

The round-robin choice and EF1 argument follow the finite-choice construction
in GTIL AppliedModelingLib's `Indivisible/RoundRobin.lean` (commit `cef01c7`), adapted
to the chore namespace.  The conversion below is specific to the He--Tao
`{1,r}` regime and is proved directly.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

variable {Item : Type}

/-- Complementary goods weights used to implement a minimum-cost chore pick.
For a normalized chore cost this takes values `r - 1` and `0`. -/
def lowRatioRoundRobinWeight {Item : Type}
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) : ChoreCost (Fin 4) Item :=
  fun agent item => r - cost agent item

/-- Complementary weights are nonnegative in the normalized regime.  This is
the nonnegativity premise of the GTIL goods round-robin EF1 proof. -/
theorem lowRatioRoundRobinWeight_nonneg
    (Item : Type) (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (hcost : IsOneOrRChoreCost cost r) (hrone : 1 ≤ r) :
    ∀ agent item, 0 ≤ lowRatioRoundRobinWeight r cost agent item := by
  intro agent item
  rcases hcost agent item with hone | hr
  · simp only [lowRatioRoundRobinWeight, hone]
    linarith
  · simp only [lowRatioRoundRobinWeight, hr, sub_self]
    norm_num

/-- Additive complementary weight is cardinality times `r`, less the original
additive chore cost. -/
theorem additive_lowRatioRoundRobinWeight
    (Item : Type) (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (agent : Fin 4) (bundle : Finset Item) :
    additiveChoreCost (lowRatioRoundRobinWeight r cost) agent bundle =
      (bundle.card : ℝ) * r - additiveChoreCost cost agent bundle := by
  unfold additiveChoreCost lowRatioRoundRobinWeight
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp only [nsmul_eq_mul]

/-- The EF1 consequence supplied by the standard maximum-weight round-robin
proof, expressed only in the additive notation needed by the chore bridge.
The witness belongs to the comparison bundle, as in goods EF1. -/
def ComplementaryEF1 {Item : Type} [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item) : Prop :=
  ∀ own comparison, own ≠ comparison → (allocation comparison).Nonempty →
    ∃ witness ∈ allocation comparison,
      additiveChoreCost (lowRatioRoundRobinWeight r cost) own
        (allocation comparison \ {witness}) ≤
      additiveChoreCost (lowRatioRoundRobinWeight r cost) own (allocation own)

/-- In a full round-robin allocation, the usual goods-EF1 certificate for
complementary weights strengthens to chore EFX when `r ≤ 2`.  The numerical
step is exactly the source argument: an EF1 comparison can lose at most `r`,
whereas deleting *any* owned chore recovers at least `1`, and the EF1 witness
itself costs at least `1` to the evaluating agent. -/
theorem efxForChores_of_equalCard_complementaryEF1
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item)
    (hcost : IsOneOrRChoreCost cost r) (hrone : 1 ≤ r) (hrtwo : r ≤ 2)
    (hcard : ∀ own comparison, (allocation own).card = (allocation comparison).card)
    (hef1 : ComplementaryEF1 r cost allocation) :
    EFXForChores (additiveChoreCost cost) allocation := by
  intro own comparison
  by_cases hempty : allocation own = ∅
  · exact Or.inl hempty
  · right
    intro removed hremoved
    by_cases hsame : own = comparison
    · subst comparison
      rw [additiveChoreCost_erase cost own (allocation own) removed hremoved]
      have hnonneg : 0 ≤ cost own removed :=
        IsOneOrRChoreCost.nonneg cost r hcost (by linarith) own removed
      linarith
    · have hownPos : 0 < (allocation own).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
      have hcomparisonPos : 0 < (allocation comparison).card := by
        rw [← hcard own comparison]
        exact hownPos
      have hcomparisonNonempty : (allocation comparison).Nonempty :=
        Finset.card_pos.mp hcomparisonPos
      obtain ⟨witness, hwitness, hweight⟩ := hef1 own comparison hsame hcomparisonNonempty
      have hremovedOne : 1 ≤ cost own removed :=
        IsOneOrRChoreCost.one_le cost r hcost hrone own removed
      have hwitnessOne : 1 ≤ cost own witness :=
        IsOneOrRChoreCost.one_le cost r hcost hrone own witness
      have hweight' :
          (((allocation comparison \ {witness}).card : ℝ) * r -
              additiveChoreCost cost own (allocation comparison \ {witness})) ≤
            ((allocation own).card : ℝ) * r -
              additiveChoreCost cost own (allocation own) := by
        simpa only [additive_lowRatioRoundRobinWeight] using hweight
      have hcomparisonCard :
          (allocation comparison \ {witness}).card = (allocation comparison).card - 1 := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hwitness]
      have hcostBound :
          additiveChoreCost cost own (allocation own) ≤
            additiveChoreCost cost own (allocation comparison \ {witness}) + r := by
        rw [hcomparisonCard, ← hcard own comparison] at hweight'
        have hownCardReal : ((allocation own).card : ℝ) =
            (((allocation own).card - 1 : ℕ) : ℝ) + 1 := by
          exact_mod_cast (Nat.sub_add_cancel (Nat.succ_le_iff.mpr hownPos)).symm
        rw [hownCardReal] at hweight'
        nlinarith
      have hcomparisonSplit :
          additiveChoreCost cost own (allocation comparison) =
            additiveChoreCost cost own (allocation comparison \ {witness}) + cost own witness := by
        rw [additiveChoreCost_erase cost own (allocation comparison) witness hwitness]
        linarith
      rw [additiveChoreCost_erase cost own (allocation own) removed hremoved]
      rw [hcomparisonSplit]
      have hslack : r - cost own removed ≤ cost own witness := by
        linarith
      linarith

/-! ### The GTIL round-robin schedule, specialized to four chore agents -/

/-- Choose a remaining chore with maximum complementary weight, equivalently a
minimum-cost remaining chore for the picking agent.  This is the chore-side
specialization of GTIL AppliedModelingLib's `rawBestGood`. -/
noncomputable def lowRatioBestChore
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (agent : Fin 4)
    (remaining : Finset Item) (hremaining : remaining.Nonempty) : Item :=
  Classical.choose (Finset.exists_max_image remaining
    (lowRatioRoundRobinWeight r cost agent) hremaining)

/-- The selected round-robin chore belongs to the remaining pool. -/
theorem lowRatioBestChore_mem
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (agent : Fin 4)
    (remaining : Finset Item) (hremaining : remaining.Nonempty) :
    lowRatioBestChore r cost agent remaining hremaining ∈ remaining :=
  (Classical.choose_spec (Finset.exists_max_image remaining
    (lowRatioRoundRobinWeight r cost agent) hremaining)).1

/-- A picker weakly prefers the complementary weight of her selected chore to
that of every other remaining chore. -/
theorem lowRatioBestChore_le
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (agent : Fin 4)
    (remaining : Finset Item) (hremaining : remaining.Nonempty) {item : Item}
    (hitem : item ∈ remaining) :
    lowRatioRoundRobinWeight r cost agent item ≤
      lowRatioRoundRobinWeight r cost agent
        (lowRatioBestChore r cost agent remaining hremaining) :=
  (Classical.choose_spec (Finset.exists_max_image remaining
    (lowRatioRoundRobinWeight r cost agent) hremaining)).2 item hitem

/-- Re-express complementary-weight maximality as the minimum-cost property
used in the He--Tao round-robin description. -/
theorem lowRatioBestChore_cost_le
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (agent : Fin 4)
    (remaining : Finset Item) (hremaining : remaining.Nonempty) {item : Item}
    (hitem : item ∈ remaining) :
    cost agent (lowRatioBestChore r cost agent remaining hremaining) ≤ cost agent item := by
  have hweight := lowRatioBestChore_le r cost agent remaining hremaining hitem
  unfold lowRatioRoundRobinWeight at hweight
  linarith

/-- If a minimum-cost pick has the large value `r`, then every later residual
chore from the same choice pool has value `r` for that picker.  This is the
local dichotomy used for each special chore in the source's reverse prefix. -/
theorem lowRatioBestChore_large_forces_large_on_subset
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (agent : Fin 4)
    (remaining residual : Finset Item) (hremaining : remaining.Nonempty)
    (hcost : IsOneOrRChoreCost cost r) (hrone : 1 ≤ r)
    (hsubset : residual ⊆ remaining)
    (hlarge : cost agent (lowRatioBestChore r cost agent remaining hremaining) = r) :
    ∀ item ∈ residual, cost agent item = r := by
  intro item hitem
  have hminimum := lowRatioBestChore_cost_le r cost agent remaining hremaining
    (hsubset hitem)
  rcases hcost agent item with hsmall | hlargeItem
  · linarith
  · exact hlargeItem

/-- Advance one position in the fixed four-agent cyclic order. -/
def nextLowRatioRoundRobinAgent (agent : Fin 4) : Fin 4 :=
  ⟨(agent.val + 1) % 4, by omega⟩

/-- Recursive core of full-round minimum-cost chore round robin.  The
accumulator contains already allocated chores and `remaining` is consumed one
chore at a time. -/
noncomputable def lowRatioRoundRobinAux [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (turn : Fin 4)
    (remaining : Finset Item) (allocation : Allocation (Fin 4) Item) :
    Allocation (Fin 4) Item :=
  if hremaining : remaining.Nonempty then
    let item := lowRatioBestChore r cost turn remaining hremaining
    lowRatioRoundRobinAux r cost (nextLowRatioRoundRobinAgent turn)
      (remaining.erase item) (addItem allocation turn item)
  else allocation
termination_by remaining.card
decreasing_by
  exact Finset.card_erase_lt_of_mem
    (lowRatioBestChore_mem r cost turn remaining hremaining)

/-- The round-robin allocation starts with agent zero and no allocated chores. -/
noncomputable def lowRatioRoundRobinAllocation [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) :
    Allocation (Fin 4) Item :=
  lowRatioRoundRobinAux r cost 0 chores (emptyAllocation (Fin 4) Item)

/-- Unfold one nonempty round-robin choice. -/
theorem lowRatioRoundRobinAux_step [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (turn : Fin 4)
    (remaining : Finset Item) (allocation : Allocation (Fin 4) Item)
    (hremaining : remaining.Nonempty) :
    lowRatioRoundRobinAux r cost turn remaining allocation =
      lowRatioRoundRobinAux r cost (nextLowRatioRoundRobinAgent turn)
        (remaining.erase (lowRatioBestChore r cost turn remaining hremaining))
        (addItem allocation turn
          (lowRatioBestChore r cost turn remaining hremaining)) := by
  rw [lowRatioRoundRobinAux.eq_1]
  exact dif_pos hremaining

/-- With no chores left, the recursive round-robin core returns its
accumulator unchanged. -/
@[simp]
theorem lowRatioRoundRobinAux_empty [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (turn : Fin 4)
    (allocation : Allocation (Fin 4) Item) :
    lowRatioRoundRobinAux r cost turn ∅ allocation = allocation := by
  rw [lowRatioRoundRobinAux.eq_1]
  simp

/-- The round-robin core preserves a feasible accumulator and allocates every
remaining chore exactly once.  This is the allocation invariant in the GTIL
round-robin proof, stated with this campaign's `IsAllocationOf` interface. -/
theorem lowRatioRoundRobinAux_isAllocationOf [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (turn : Fin 4)
    (allocated remaining : Finset Item) (allocation : Allocation (Fin 4) Item)
    (halloc : IsAllocationOf allocation allocated)
    (hdisjoint : Disjoint allocated remaining) :
    IsAllocationOf (lowRatioRoundRobinAux r cost turn remaining allocation)
      (allocated ∪ remaining) := by
  induction remaining using Finset.strongInductionOn generalizing turn allocated allocation
  rename_i chores inductionHypothesis
  by_cases hremaining : chores.Nonempty
  · let item : Item := lowRatioBestChore r cost turn chores hremaining
    have hitem : item ∈ chores := by
      exact lowRatioBestChore_mem r cost turn chores hremaining
    have hnotAllocated : item ∉ allocated := by
      intro hitemAllocated
      exact Finset.disjoint_left.mp hdisjoint hitemAllocated hitem
    have halloc' : IsAllocationOf (addItem allocation turn item) (insert item allocated) :=
      isAllocationOf_addItem_insert allocation allocated turn item halloc hnotAllocated
    have hdisjoint' : Disjoint (insert item allocated) (chores.erase item) := by
      rw [Finset.disjoint_left]
      intro other hotherAllocated hotherRemaining
      rcases Finset.mem_insert.mp hotherAllocated with rfl | hotherAllocated
      · exact (Finset.mem_erase.mp hotherRemaining).1 rfl
      · exact Finset.disjoint_left.mp hdisjoint hotherAllocated
          (Finset.erase_subset item chores hotherRemaining)
    rw [lowRatioRoundRobinAux_step r cost turn chores allocation hremaining]
    have hinduction := inductionHypothesis (chores.erase item)
      (Finset.erase_ssubset hitem) (nextLowRatioRoundRobinAgent turn)
      (insert item allocated) (addItem allocation turn item) halloc' hdisjoint'
    have hunion : (insert item allocated) ∪ chores.erase item = allocated ∪ chores := by
      calc
        (insert item allocated) ∪ chores.erase item =
            insert item (allocated ∪ chores.erase item) :=
          Finset.insert_union item allocated (chores.erase item)
        _ = allocated ∪ insert item (chores.erase item) :=
          (Finset.union_insert item allocated (chores.erase item)).symm
        _ = allocated ∪ chores := by rw [Finset.insert_erase hitem]
    rwa [hunion] at hinduction
  · rw [Finset.not_nonempty_iff_eq_empty.mp hremaining,
      lowRatioRoundRobinAux_empty]
    simpa using halloc

/-- The complete full-round minimum-cost round-robin allocation is feasible. -/
theorem lowRatioRoundRobinAllocation_isAllocationOf [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) :
    IsAllocationOf (lowRatioRoundRobinAllocation r cost chores) chores := by
  unfold lowRatioRoundRobinAllocation
  simpa using lowRatioRoundRobinAux_isAllocationOf r cost 0 ∅ chores
    (emptyAllocation (Fin 4) Item) isAllocationOf_empty (Finset.disjoint_empty_left chores)

/-- An earlier picker has at least as much complementary weight as any later
picker.  This is GTIL's round-by-round no-envy invariant, transplanted to the
minimum-cost chore schedule. -/
theorem lowRatioRoundRobin_noEnvy_of_earlier [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (hnonneg : ∀ agent item, 0 ≤ lowRatioRoundRobinWeight r cost agent item)
    (first second : Fin 4) (hfirstSecond : first.val < second.val) :
    additiveChoreCost (lowRatioRoundRobinWeight r cost) first
        (lowRatioRoundRobinAllocation r cost chores second) ≤
      additiveChoreCost (lowRatioRoundRobinWeight r cost) first
        (lowRatioRoundRobinAllocation r cost chores first) := by
  suffices inductionClaim : ∀ (turn : Fin 4) (remaining : Finset Item)
      (allocation : Allocation (Fin 4) Item),
      (∀ left right : Fin 4, left ≠ right → Disjoint (allocation left) (allocation right)) →
      (∀ item ∈ remaining, ∀ agent : Fin 4, item ∉ allocation agent) →
      additiveChoreCost (lowRatioRoundRobinWeight r cost) first (allocation second) ≤
        additiveChoreCost (lowRatioRoundRobinWeight r cost) first (allocation first) →
      (first.val < turn.val ∧ turn.val ≤ second.val → ∀ item ∈ remaining,
        additiveChoreCost (lowRatioRoundRobinWeight r cost) first (allocation second) +
          lowRatioRoundRobinWeight r cost first item ≤
            additiveChoreCost (lowRatioRoundRobinWeight r cost) first (allocation first)) →
      additiveChoreCost (lowRatioRoundRobinWeight r cost) first
          (lowRatioRoundRobinAux r cost turn remaining allocation second) ≤
        additiveChoreCost (lowRatioRoundRobinWeight r cost) first
          (lowRatioRoundRobinAux r cost turn remaining allocation first) by
    unfold lowRatioRoundRobinAllocation
    apply inductionClaim 0 chores (emptyAllocation (Fin 4) Item)
    · intro left right _
      exact Finset.disjoint_empty_left _
    · intro item _ agent hitem
      exact Finset.notMem_empty item hitem
    · simp [emptyAllocation, additiveChoreCost]
    · rintro ⟨hfirst, _⟩
      exact (Nat.not_lt_zero first.val hfirst).elim
  intro turn remaining
  induction remaining using Finset.strongInductionOn generalizing turn
  rename_i current inductionHypothesis
  intro allocation hdisjoint hremainingDistinct hinv hheadroom
  by_cases hnonempty : current.Nonempty
  · rw [lowRatioRoundRobinAux_step r cost turn current allocation hnonempty]
    let item : Item := lowRatioBestChore r cost turn current hnonempty
    have hitem : item ∈ current := by
      exact lowRatioBestChore_mem r cost turn current hnonempty
    have hitemNotOwned : ∀ agent : Fin 4, item ∉ allocation agent :=
      hremainingDistinct item hitem
    have hfirstNeSecond : first ≠ second :=
      Fin.ne_of_val_ne (Nat.ne_of_lt hfirstSecond)
    apply inductionHypothesis (current.erase item) (Finset.erase_ssubset hitem)
      (nextLowRatioRoundRobinAgent turn) (addItem allocation turn item)
    · intro left right hleftRight
      simp only [addItem]
      by_cases hleft : left = turn <;> by_cases hright : right = turn
      · exact (hleftRight (hleft.trans hright.symm)).elim
      · subst left
        rw [if_pos rfl, if_neg hright, Finset.disjoint_left]
        intro other hotherLeft hotherRight
        rcases Finset.mem_insert.mp hotherLeft with rfl | hotherLeft
        · exact hitemNotOwned right hotherRight
        · exact Finset.disjoint_left.mp (hdisjoint turn right hleftRight)
            hotherLeft hotherRight
      · subst right
        rw [if_neg hleft, if_pos rfl, Finset.disjoint_left]
        intro other hotherLeft hotherRight
        rcases Finset.mem_insert.mp hotherRight with rfl | hotherRight
        · exact hitemNotOwned left hotherLeft
        · exact Finset.disjoint_left.mp (hdisjoint left turn hleftRight)
            hotherLeft hotherRight
      · rw [if_neg hleft, if_neg hright]
        exact hdisjoint left right hleftRight
    · intro other hother agent
      simp only [addItem]
      by_cases hagent : agent = turn
      · rw [if_pos hagent]
        simp only [Finset.mem_insert]
        rintro (rfl | hotherOwned)
        · exact (Finset.mem_erase.mp hother).1 rfl
        · exact hremainingDistinct other (Finset.erase_subset item current hother) turn
            (hagent ▸ hotherOwned)
      · rw [if_neg hagent]
        exact hremainingDistinct other (Finset.erase_subset item current hother) agent
    · by_cases hfirstTurn : first = turn <;> by_cases hsecondTurn : second = turn
      · exact (hfirstNeSecond (hfirstTurn.trans hsecondTurn.symm)).elim
      · have hsecondBundle : addItem allocation turn item second = allocation second := by
          simp [addItem, hsecondTurn]
        have hfirstBundle : addItem allocation turn item first = insert item (allocation first) := by
          simp [addItem, hfirstTurn]
        rw [hsecondBundle, hfirstBundle]
        simp only [additiveChoreCost]
        rw [Finset.sum_insert (hitemNotOwned first)]
        exact le_trans hinv (le_add_of_nonneg_left (hnonneg first item))
      · have hsecondBundle : addItem allocation turn item second = insert item (allocation second) := by
          simp [addItem, hsecondTurn]
        have hfirstBundle : addItem allocation turn item first = allocation first := by
          simp [addItem, hfirstTurn]
        rw [hsecondBundle, hfirstBundle]
        simp only [additiveChoreCost]
        rw [Finset.sum_insert (hitemNotOwned second)]
        have hstep := hheadroom ⟨by simpa [← hsecondTurn] using hfirstSecond,
          by simp [← hsecondTurn]⟩ item hitem
        rw [add_comm]
        exact hstep
      · simp only [addItem, hfirstTurn, hsecondTurn]
        exact hinv
    · rintro ⟨hfirstTurn', hturnSecond'⟩ other hother
      by_cases hfirstTurn : first = turn <;> by_cases hsecondTurn : second = turn
      · exact (hfirstNeSecond (hfirstTurn.trans hsecondTurn.symm)).elim
      · have hsecondBundle : addItem allocation turn item second = allocation second := by
          simp [addItem, hsecondTurn]
        have hfirstBundle : addItem allocation turn item first = insert item (allocation first) := by
          simp [addItem, hfirstTurn]
        rw [hsecondBundle, hfirstBundle]
        simp only [additiveChoreCost]
        rw [Finset.sum_insert (hitemNotOwned first)]
        have hbest : lowRatioRoundRobinWeight r cost first other ≤
            lowRatioRoundRobinWeight r cost first item := by
          rw [hfirstTurn]
          exact lowRatioBestChore_le r cost turn current hnonempty
            (Finset.erase_subset item current hother)
        have hcombined := add_le_add hinv hbest
        simp only [additiveChoreCost] at hcombined
        linarith
      · exfalso
        have hturnEq : turn.val = second.val := congrArg Fin.val hsecondTurn.symm
        dsimp [nextLowRatioRoundRobinAgent] at hfirstTurn' hturnSecond'
        omega
      · have hsecondBundle : addItem allocation turn item second = allocation second := by
          simp [addItem, hsecondTurn]
        have hfirstBundle : addItem allocation turn item first = allocation first := by
          simp [addItem, hfirstTurn]
        rw [hsecondBundle, hfirstBundle]
        have hturnBound : turn.val + 1 ≤ 4 := Nat.succ_le_of_lt turn.isLt
        have hpreviousGuard : first.val < turn.val ∧ turn.val ≤ second.val := by
          dsimp [nextLowRatioRoundRobinAgent] at hfirstTurn' hturnSecond'
          rcases Nat.eq_or_lt_of_le hturnBound with hturnLast | hturnNotLast
          · rw [hturnLast, Nat.mod_self] at hfirstTurn' hturnSecond'
            omega
          · rw [Nat.mod_eq_of_lt hturnNotLast] at hfirstTurn' hturnSecond'
            rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hfirstTurn') with hturnEq | hfirstLess
            · exact (hfirstTurn (Fin.ext_iff.mpr hturnEq)).elim
            · exact ⟨hfirstLess, by omega⟩
        exact hheadroom hpreviousGuard other (Finset.erase_subset item current hother)
  · have hempty : current = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty, lowRatioRoundRobinAux_empty]
    exact hinv

/-- A later picker has a standard goods-EF1 witness in an earlier picker's
bundle.  This is the two-phase invariant from GTIL's round-robin proof: before
the earlier picker takes her first chore, and after that distinguished chore
has become the persistent witness. -/
theorem lowRatioRoundRobin_ef1_of_later [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (hnonneg : ∀ agent item, 0 ≤ lowRatioRoundRobinWeight r cost agent item)
    (first second : Fin 4) (hsecondFirst : second.val < first.val)
    (hnonempty : (lowRatioRoundRobinAllocation r cost chores second).Nonempty) :
    ∃ witness ∈ lowRatioRoundRobinAllocation r cost chores second,
      additiveChoreCost (lowRatioRoundRobinWeight r cost) first
          (lowRatioRoundRobinAllocation r cost chores second \ {witness}) ≤
        additiveChoreCost (lowRatioRoundRobinWeight r cost) first
          (lowRatioRoundRobinAllocation r cost chores first) := by
  suffices inductionClaim : ∀ (turn : Fin 4) (remaining : Finset Item)
      (allocation : Allocation (Fin 4) Item),
      (∀ left right : Fin 4, left ≠ right → Disjoint (allocation left) (allocation right)) →
      (∀ item ∈ remaining, ∀ agent : Fin 4, item ∉ allocation agent) →
      ((allocation second = ∅ ∧ turn.val ≤ second.val) ∨
        (∃ witness ∈ allocation second,
          additiveChoreCost (lowRatioRoundRobinWeight r cost) first
              (allocation second \ {witness}) ≤
            additiveChoreCost (lowRatioRoundRobinWeight r cost) first (allocation first) ∧
          (first.val < turn.val ∨ turn.val ≤ second.val → ∀ item ∈ remaining,
            additiveChoreCost (lowRatioRoundRobinWeight r cost) first
                (allocation second \ {witness}) +
              lowRatioRoundRobinWeight r cost first item ≤
                additiveChoreCost (lowRatioRoundRobinWeight r cost) first (allocation first)))) →
      (∃ witness ∈ lowRatioRoundRobinAux r cost turn remaining allocation second,
        additiveChoreCost (lowRatioRoundRobinWeight r cost) first
            (lowRatioRoundRobinAux r cost turn remaining allocation second \ {witness}) ≤
          additiveChoreCost (lowRatioRoundRobinWeight r cost) first
            (lowRatioRoundRobinAux r cost turn remaining allocation first)) ∨
        lowRatioRoundRobinAux r cost turn remaining allocation second = ∅ by
    unfold lowRatioRoundRobinAllocation
    rcases inductionClaim 0 chores (emptyAllocation (Fin 4) Item)
        (fun left right _ => Finset.disjoint_empty_left _)
        (fun item _ agent hitem => Finset.notMem_empty item hitem)
        (Or.inl ⟨rfl, Nat.zero_le _⟩) with hexists | hempty
    · exact hexists
    · exact (Finset.Nonempty.ne_empty hnonempty hempty).elim
  intro turn remaining
  induction remaining using Finset.strongInductionOn generalizing turn
  rename_i current inductionHypothesis
  intro allocation hdisjoint hremainingDistinct hphase
  by_cases hnonemptyCurrent : current.Nonempty
  · rw [lowRatioRoundRobinAux_step r cost turn current allocation hnonemptyCurrent]
    let item : Item := lowRatioBestChore r cost turn current hnonemptyCurrent
    have hitem : item ∈ current :=
      lowRatioBestChore_mem r cost turn current hnonemptyCurrent
    have hitemNotOwned : ∀ agent : Fin 4, item ∉ allocation agent :=
      hremainingDistinct item hitem
    have hsecondNeFirst : second ≠ first :=
      Fin.ne_of_val_ne (Nat.ne_of_lt hsecondFirst)
    have hturnBound : turn.val + 1 ≤ 4 := Nat.succ_le_of_lt turn.isLt
    apply inductionHypothesis (current.erase item) (Finset.erase_ssubset hitem)
      (nextLowRatioRoundRobinAgent turn) (addItem allocation turn item)
    · intro left right hleftRight
      simp only [addItem]
      by_cases hleft : left = turn <;> by_cases hright : right = turn
      · exact (hleftRight (hleft.trans hright.symm)).elim
      · subst left
        rw [if_pos rfl, if_neg hright, Finset.disjoint_left]
        intro other hotherLeft hotherRight
        rcases Finset.mem_insert.mp hotherLeft with rfl | hotherLeft
        · exact hitemNotOwned right hotherRight
        · exact Finset.disjoint_left.mp (hdisjoint turn right hleftRight)
            hotherLeft hotherRight
      · subst right
        rw [if_neg hleft, if_pos rfl, Finset.disjoint_left]
        intro other hotherLeft hotherRight
        rcases Finset.mem_insert.mp hotherRight with rfl | hotherRight
        · exact hitemNotOwned left hotherLeft
        · exact Finset.disjoint_left.mp (hdisjoint left turn hleftRight)
            hotherLeft hotherRight
      · rw [if_neg hleft, if_neg hright]
        exact hdisjoint left right hleftRight
    · intro other hother agent
      simp only [addItem]
      by_cases hagent : agent = turn
      · rw [if_pos hagent]
        simp only [Finset.mem_insert]
        rintro (rfl | hotherOwned)
        · exact (Finset.mem_erase.mp hother).1 rfl
        · exact hremainingDistinct other (Finset.erase_subset item current hother) turn
            (hagent ▸ hotherOwned)
      · rw [if_neg hagent]
        exact hremainingDistinct other (Finset.erase_subset item current hother) agent
    · rcases hphase with ⟨hsecondEmpty, hturnSecond⟩ |
        ⟨witness, hwitness, hef1, hheadroom⟩
      · by_cases hsecondTurn : second = turn
        · have hsecondBundle : addItem allocation turn item second = insert item (allocation second) := by
            simp [addItem, hsecondTurn]
          have hfirstNotTurn : first ≠ turn := by
            intro hfirstTurn
            exact hsecondNeFirst (hsecondTurn.trans hfirstTurn.symm)
          have hfirstBundle : addItem allocation turn item first = allocation first := by
            simp [addItem, hfirstNotTurn]
          right
          refine ⟨item, ?_, ?_, ?_⟩
          · rw [hsecondBundle]
            exact Finset.mem_insert_self item (allocation second)
          · rw [hsecondBundle, hfirstBundle, Finset.sdiff_singleton_eq_erase,
              Finset.erase_insert (hitemNotOwned second), hsecondEmpty]
            simp only [additiveChoreCost, Finset.sum_empty]
            exact Finset.sum_nonneg fun x _ => hnonneg first x
          · intro hguard
            exfalso
            subst turn
            dsimp [nextLowRatioRoundRobinAgent] at hguard
            rcases hguard with hguard | hguard <;> omega
        · have hfirstTurn : first ≠ turn := by
            intro hfirstTurn
            rw [hfirstTurn] at hsecondFirst
            exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hsecondFirst hturnSecond)
          left
          constructor
          · simp [addItem, hsecondTurn, hsecondEmpty]
          · have hturnStrict : turn.val < second.val := by
              exact Nat.lt_of_le_of_ne hturnSecond
                (fun h => hsecondTurn (Fin.ext_iff.mpr h.symm))
            dsimp [nextLowRatioRoundRobinAgent]
            rcases Nat.eq_or_lt_of_le hturnBound with hlast | hnotLast
            · rw [hlast, Nat.mod_self]
              exact Nat.zero_le _
            · rw [Nat.mod_eq_of_lt hnotLast]
              omega
      · by_cases hfirstTurn : first = turn <;> by_cases hsecondTurn : second = turn
        · exact (hsecondNeFirst (hsecondTurn.trans hfirstTurn.symm)).elim
        · have hsecondBundle : addItem allocation turn item second = allocation second := by
            simp [addItem, hsecondTurn]
          have hfirstBundle : addItem allocation turn item first = insert item (allocation first) := by
            simp [addItem, hfirstTurn]
          right
          refine ⟨witness, ?_, ?_, ?_⟩
          · rw [hsecondBundle]
            exact hwitness
          · rw [hsecondBundle, hfirstBundle]
            simp only [additiveChoreCost]
            rw [Finset.sum_insert (hitemNotOwned first)]
            exact le_trans hef1 (le_add_of_nonneg_left (hnonneg first item))
          · intro _ other hother
            rw [hsecondBundle, hfirstBundle]
            simp only [additiveChoreCost]
            rw [Finset.sum_insert (hitemNotOwned first)]
            have hbest : lowRatioRoundRobinWeight r cost first other ≤
                lowRatioRoundRobinWeight r cost first item := by
              rw [hfirstTurn]
              exact lowRatioBestChore_le r cost turn current hnonemptyCurrent
                (Finset.erase_subset item current hother)
            have hcombined := add_le_add hef1 hbest
            simp only [additiveChoreCost] at hcombined
            linarith
        · have hsecondBundle : addItem allocation turn item second = insert item (allocation second) := by
            simp [addItem, hsecondTurn]
          have hfirstBundle : addItem allocation turn item first = allocation first := by
            simp [addItem, hfirstTurn]
          have hguard : first.val < turn.val ∨ turn.val ≤ second.val :=
            Or.inr (le_of_eq (congrArg Fin.val hsecondTurn.symm))
          right
          refine ⟨witness, ?_, ?_, ?_⟩
          · rw [hsecondBundle]
            exact Finset.mem_insert_of_mem hwitness
          · have hitemNeWitness : item ≠ witness := by
              intro hitemWitness
              exact hitemNotOwned second (hitemWitness ▸ hwitness)
            rw [hsecondBundle, hfirstBundle]
            have hsDiff : insert item (allocation second) \ {witness} =
                insert item (allocation second \ {witness}) := by
              ext other
              simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨hother | hother, hotherNe⟩
                · exact Or.inl hother
                · exact Or.inr ⟨hother, hotherNe⟩
              · rintro (rfl | ⟨hother, hotherNe⟩)
                · exact ⟨Or.inl rfl, hitemNeWitness⟩
                · exact ⟨Or.inr hother, hotherNe⟩
            rw [hsDiff]
            simp only [additiveChoreCost]
            have hitemNotInDifference : item ∉ allocation second \ {witness} := by
              intro hitemDifference
              exact hitemNotOwned second (Finset.mem_sdiff.mp hitemDifference).1
            rw [Finset.sum_insert hitemNotInDifference]
            have hstep := hheadroom hguard item hitem
            simp only [additiveChoreCost] at hstep
            linarith
          · intro hnextGuard
            exfalso
            subst turn
            dsimp [nextLowRatioRoundRobinAgent] at hnextGuard
            rcases hnextGuard with hnextGuard | hnextGuard <;> omega
        · have hsecondBundle : addItem allocation turn item second = allocation second := by
            simp [addItem, hsecondTurn]
          have hfirstBundle : addItem allocation turn item first = allocation first := by
            simp [addItem, hfirstTurn]
          right
          refine ⟨witness, ?_, ?_, ?_⟩
          · rw [hsecondBundle]
            exact hwitness
          · rw [hsecondBundle, hfirstBundle]
            exact hef1
          · intro hnextGuard other hother
            rw [hsecondBundle, hfirstBundle]
            have hpreviousGuard : first.val < turn.val ∨ turn.val ≤ second.val := by
              dsimp [nextLowRatioRoundRobinAgent] at hnextGuard
              rcases Nat.eq_or_lt_of_le hturnBound with hlast | hnotLast
              · rw [hlast, Nat.mod_self] at hnextGuard
                rcases hnextGuard with hnextGuard | hnextGuard
                · omega
                · left
                  omega
              · rw [Nat.mod_eq_of_lt hnotLast] at hnextGuard
                rcases hnextGuard with hnextGuard | hnextGuard
                · left
                  omega
                · right
                  omega
            exact hheadroom hpreviousGuard other (Finset.erase_subset item current hother)
  · have hempty : current = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonemptyCurrent
    rw [hempty, lowRatioRoundRobinAux_empty]
    rcases hphase with ⟨hsecondEmpty, _⟩ | ⟨witness, hwitness, hef1, _⟩
    · exact Or.inr hsecondEmpty
    · exact Or.inl ⟨witness, hwitness, hef1⟩

/-- The full minimum-cost round-robin schedule has the complementary goods-EF1
certificate needed for the He--Tao low-ratio argument. -/
theorem lowRatioRoundRobin_complementaryEF1 [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (hnonneg : ∀ agent item, 0 ≤ lowRatioRoundRobinWeight r cost agent item) :
    ComplementaryEF1 r cost (lowRatioRoundRobinAllocation r cost chores) := by
  intro own comparison hownComparison hcomparisonNonempty
  have hvalueNe : own.val ≠ comparison.val := by
    intro hvalueEq
    exact hownComparison (Fin.ext hvalueEq)
  rcases lt_or_gt_of_ne hvalueNe with hownEarlier | hcomparisonEarlier
  · obtain ⟨witness, hwitness⟩ := hcomparisonNonempty
    refine ⟨witness, hwitness, ?_⟩
    have hmono : additiveChoreCost (lowRatioRoundRobinWeight r cost) own
        (lowRatioRoundRobinAllocation r cost chores comparison \ {witness}) ≤
        additiveChoreCost (lowRatioRoundRobinWeight r cost) own
          (lowRatioRoundRobinAllocation r cost chores comparison) := by
      unfold additiveChoreCost
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun item _ _ => hnonneg own item)
    exact hmono.trans (lowRatioRoundRobin_noEnvy_of_earlier r cost chores hnonneg
      own comparison hownEarlier)
  · exact lowRatioRoundRobin_ef1_of_later r cost chores hnonneg own comparison
      hcomparisonEarlier hcomparisonNonempty

/-- Processing a multiple of four chores from the start of a round preserves
equal bundle cardinalities.  This is independent of values: one complete
round adds exactly one fresh chore to each of the four agents. -/
theorem lowRatioRoundRobinAux_equalCard_of_card_mul_four [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (rounds : ℕ)
    (remaining : Finset Item) (allocation : Allocation (Fin 4) Item)
    (hcard : remaining.card = 4 * rounds)
    (hequal : ∀ first second, (allocation first).card = (allocation second).card)
    (hremainingFresh : ∀ item ∈ remaining, ∀ agent, item ∉ allocation agent) :
    ∀ first second,
      (lowRatioRoundRobinAux r cost 0 remaining allocation first).card =
        (lowRatioRoundRobinAux r cost 0 remaining allocation second).card := by
  induction rounds generalizing remaining allocation with
  | zero =>
      have hremainingEmpty : remaining = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa using hcard
      rw [hremainingEmpty, lowRatioRoundRobinAux_empty]
      exact hequal
  | succ rounds inductionHypothesis =>
      have hfourLe : 4 ≤ remaining.card := by
        rw [hcard]
        omega
      have hnonempty0 : remaining.Nonempty := Finset.card_pos.mp (by omega)
      let item0 : Item := lowRatioBestChore r cost 0 remaining hnonempty0
      let remaining1 : Finset Item := remaining.erase item0
      let allocation1 : Allocation (Fin 4) Item := addItem allocation 0 item0
      have hitem0 : item0 ∈ remaining := by
        exact lowRatioBestChore_mem r cost 0 remaining hnonempty0
      have hcard1 : remaining1.card = remaining.card - 1 := by
        dsimp [remaining1]
        rw [Finset.card_erase_of_mem hitem0]
      have hnonempty1 : remaining1.Nonempty := Finset.card_pos.mp (by
        rw [hcard1]
        omega)
      let item1 : Item := lowRatioBestChore r cost 1 remaining1 hnonempty1
      let remaining2 : Finset Item := remaining1.erase item1
      let allocation2 : Allocation (Fin 4) Item := addItem allocation1 1 item1
      have hitem1 : item1 ∈ remaining1 := by
        exact lowRatioBestChore_mem r cost 1 remaining1 hnonempty1
      have hcard2 : remaining2.card = remaining1.card - 1 := by
        dsimp [remaining2]
        rw [Finset.card_erase_of_mem hitem1]
      have hnonempty2 : remaining2.Nonempty := Finset.card_pos.mp (by
        rw [hcard2, hcard1]
        omega)
      let item2 : Item := lowRatioBestChore r cost 2 remaining2 hnonempty2
      let remaining3 : Finset Item := remaining2.erase item2
      let allocation3 : Allocation (Fin 4) Item := addItem allocation2 2 item2
      have hitem2 : item2 ∈ remaining2 := by
        exact lowRatioBestChore_mem r cost 2 remaining2 hnonempty2
      have hcard3 : remaining3.card = remaining2.card - 1 := by
        dsimp [remaining3]
        rw [Finset.card_erase_of_mem hitem2]
      have hnonempty3 : remaining3.Nonempty := Finset.card_pos.mp (by
        rw [hcard3, hcard2, hcard1]
        omega)
      let item3 : Item := lowRatioBestChore r cost 3 remaining3 hnonempty3
      let remaining4 : Finset Item := remaining3.erase item3
      let allocation4 : Allocation (Fin 4) Item := addItem allocation3 3 item3
      have hitem3 : item3 ∈ remaining3 := by
        exact lowRatioBestChore_mem r cost 3 remaining3 hnonempty3
      have hcard4 : remaining4.card = 4 * rounds := by
        have hcard4' : remaining4.card = remaining3.card - 1 := by
          dsimp [remaining4]
          rw [Finset.card_erase_of_mem hitem3]
        rw [hcard4', hcard3, hcard2, hcard1, hcard]
        omega
      have hitem0NotOwned : item0 ∉ allocation 0 := hremainingFresh item0 hitem0 0
      have hitem1NotOwned : item1 ∉ allocation 1 :=
        hremainingFresh item1 (Finset.erase_subset item0 remaining hitem1) 1
      have hitem2NotOwned : item2 ∉ allocation 2 :=
        hremainingFresh item2
          (Finset.erase_subset item0 remaining
            (Finset.erase_subset item1 remaining1 hitem2)) 2
      have hitem3NotOwned : item3 ∉ allocation 3 :=
        hremainingFresh item3
          (Finset.erase_subset item0 remaining
            (Finset.erase_subset item1 remaining1
              (Finset.erase_subset item2 remaining2 hitem3))) 3
      have hallocation4Card : ∀ agent,
          (allocation4 agent).card = (allocation agent).card + 1 := by
        intro agent
        fin_cases agent <;>
          simp [allocation4, allocation3, allocation2, allocation1, addItem,
            Finset.card_insert_of_notMem, hitem0NotOwned, hitem1NotOwned,
            hitem2NotOwned, hitem3NotOwned]
      have hequal4 : ∀ first second,
          (allocation4 first).card = (allocation4 second).card := by
        intro first second
        rw [hallocation4Card first, hallocation4Card second, hequal first second]
      have hremaining4Fresh : ∀ item ∈ remaining4, ∀ agent, item ∉ allocation4 agent := by
        intro other hother agent
        have hotherNe3 : other ≠ item3 := (Finset.mem_erase.mp hother).1
        have hotherIn3 : other ∈ remaining3 := (Finset.mem_erase.mp hother).2
        have hotherNe2 : other ≠ item2 := (Finset.mem_erase.mp hotherIn3).1
        have hotherIn2 : other ∈ remaining2 := (Finset.mem_erase.mp hotherIn3).2
        have hotherNe1 : other ≠ item1 := (Finset.mem_erase.mp hotherIn2).1
        have hotherIn1 : other ∈ remaining1 := (Finset.mem_erase.mp hotherIn2).2
        have hotherNe0 : other ≠ item0 := (Finset.mem_erase.mp hotherIn1).1
        have hotherIn0 : other ∈ remaining := (Finset.mem_erase.mp hotherIn1).2
        fin_cases agent
        · simpa [allocation4, allocation3, allocation2, allocation1, addItem,
            hotherNe0, hotherNe1, hotherNe2, hotherNe3] using
            hremainingFresh other hotherIn0 0
        · simpa [allocation4, allocation3, allocation2, allocation1, addItem,
            hotherNe0, hotherNe1, hotherNe2, hotherNe3] using
            hremainingFresh other hotherIn0 1
        · simpa [allocation4, allocation3, allocation2, allocation1, addItem,
            hotherNe0, hotherNe1, hotherNe2, hotherNe3] using
            hremainingFresh other hotherIn0 2
        · simpa [allocation4, allocation3, allocation2, allocation1, addItem,
            hotherNe0, hotherNe1, hotherNe2, hotherNe3] using
            hremainingFresh other hotherIn0 3
      have hinduction := inductionHypothesis remaining4 allocation4 hcard4 hequal4 hremaining4Fresh
      rw [lowRatioRoundRobinAux_step r cost 0 remaining allocation hnonempty0]
      change ∀ first second,
        (lowRatioRoundRobinAux r cost 1 remaining1 allocation1 first).card =
          (lowRatioRoundRobinAux r cost 1 remaining1 allocation1 second).card
      rw [lowRatioRoundRobinAux_step r cost 1 remaining1 allocation1 hnonempty1]
      change ∀ first second,
        (lowRatioRoundRobinAux r cost 2 remaining2 allocation2 first).card =
          (lowRatioRoundRobinAux r cost 2 remaining2 allocation2 second).card
      rw [lowRatioRoundRobinAux_step r cost 2 remaining2 allocation2 hnonempty2]
      change ∀ first second,
        (lowRatioRoundRobinAux r cost 3 remaining3 allocation3 first).card =
          (lowRatioRoundRobinAux r cost 3 remaining3 allocation3 second).card
      rw [lowRatioRoundRobinAux_step r cost 3 remaining3 allocation3 hnonempty3]
      change ∀ first second,
        (lowRatioRoundRobinAux r cost 0 remaining4 allocation4 first).card =
          (lowRatioRoundRobinAux r cost 0 remaining4 allocation4 second).card
      exact hinduction

/-- A complete full-round round-robin allocation has equal bundle sizes when
the number of chores is divisible by four. -/
theorem lowRatioRoundRobinAllocation_equalCard_of_card_mul_four [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (rounds : ℕ)
    (hcard : chores.card = 4 * rounds) :
    ∀ first second,
      (lowRatioRoundRobinAllocation r cost chores first).card =
        (lowRatioRoundRobinAllocation r cost chores second).card := by
  unfold lowRatioRoundRobinAllocation
  apply lowRatioRoundRobinAux_equalCard_of_card_mul_four r cost rounds chores
    (emptyAllocation (Fin 4) Item) hcard
  · intro first second
    simp [emptyAllocation]
  · intro item _ agent hitem
    exact Finset.notMem_empty item hitem

/-- The source's standard round-robin construction proves EFX for a normalized
`{1,r}` chore pool of size divisible by four when `1 ≤ r ≤ 2`. -/
theorem existsEfxOfOneOrR_lowRatio_b0
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (rounds : ℕ)
    (hrone : 1 ≤ r) (hrtwo : r ≤ 2) (hcost : IsOneOrRChoreCost cost r)
    (hcard : chores.card = 4 * rounds) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  let allocation : Allocation (Fin 4) Item := lowRatioRoundRobinAllocation r cost chores
  refine ⟨allocation, ?_, ?_⟩
  · exact lowRatioRoundRobinAllocation_isAllocationOf r cost chores
  · apply efxForChores_of_equalCard_complementaryEF1 Item r cost allocation hcost hrone hrtwo
    · exact lowRatioRoundRobinAllocation_equalCard_of_card_mul_four r cost chores rounds hcard
    · exact lowRatioRoundRobin_complementaryEF1 r cost chores
        (lowRatioRoundRobinWeight_nonneg Item r cost hcost hrone)

/-- In an equal-cardinality full round, an earlier standard-round picker has
no chore envy, not merely complementary-weight no-envy. -/
theorem lowRatioRoundRobin_chore_noEnvy_of_earlier [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (hnonneg : ∀ agent item, 0 ≤ lowRatioRoundRobinWeight r cost agent item)
    (hcard : ∀ first second,
      (lowRatioRoundRobinAllocation r cost chores first).card =
        (lowRatioRoundRobinAllocation r cost chores second).card)
    (first second : Fin 4) (hfirstSecond : first.val < second.val) :
    additiveChoreCost cost first (lowRatioRoundRobinAllocation r cost chores first) ≤
      additiveChoreCost cost first (lowRatioRoundRobinAllocation r cost chores second) := by
  have hweight := lowRatioRoundRobin_noEnvy_of_earlier r cost chores hnonneg
    first second hfirstSecond
  rw [additive_lowRatioRoundRobinWeight, additive_lowRatioRoundRobinWeight,
    hcard first second] at hweight
  linarith

/-- In an equal-cardinality full round, a later standard-round picker's chore
cost exceeds an earlier picker's by at most one when `r ≤ 2`. -/
theorem lowRatioRoundRobin_chore_later_le_add_one [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (hnonneg : ∀ agent item, 0 ≤ lowRatioRoundRobinWeight r cost agent item)
    (hcost : IsOneOrRChoreCost cost r) (hrone : 1 ≤ r) (hrtwo : r ≤ 2)
    (hcard : ∀ first second,
      (lowRatioRoundRobinAllocation r cost chores first).card =
        (lowRatioRoundRobinAllocation r cost chores second).card)
    (later earlier : Fin 4) (hearlierLater : earlier.val < later.val)
    (hearlierNonempty : (lowRatioRoundRobinAllocation r cost chores earlier).Nonempty) :
    additiveChoreCost cost later (lowRatioRoundRobinAllocation r cost chores later) ≤
      additiveChoreCost cost later (lowRatioRoundRobinAllocation r cost chores earlier) + 1 := by
  obtain ⟨witness, hwitness, hweight⟩ :=
    lowRatioRoundRobin_ef1_of_later r cost chores hnonneg later earlier
      hearlierLater hearlierNonempty
  have hweight' :
      (((lowRatioRoundRobinAllocation r cost chores earlier \ {witness}).card : ℝ) * r -
          additiveChoreCost cost later
            (lowRatioRoundRobinAllocation r cost chores earlier \ {witness})) ≤
        ((lowRatioRoundRobinAllocation r cost chores later).card : ℝ) * r -
          additiveChoreCost cost later (lowRatioRoundRobinAllocation r cost chores later) := by
    simpa only [additive_lowRatioRoundRobinWeight] using hweight
  have heraseCard :
      (lowRatioRoundRobinAllocation r cost chores earlier \ {witness}).card =
        (lowRatioRoundRobinAllocation r cost chores earlier).card - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hwitness]
  have hbound : additiveChoreCost cost later (lowRatioRoundRobinAllocation r cost chores later) ≤
      additiveChoreCost cost later
        (lowRatioRoundRobinAllocation r cost chores earlier \ {witness}) + r := by
    rw [heraseCard, ← hcard later earlier] at hweight'
    have hlaterPositive : 0 < (lowRatioRoundRobinAllocation r cost chores later).card := by
      rw [hcard later earlier]
      exact Finset.card_pos.mpr hearlierNonempty
    have hcardReal : ((lowRatioRoundRobinAllocation r cost chores later).card : ℝ) =
        (((lowRatioRoundRobinAllocation r cost chores later).card - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlaterPositive)).symm
    rw [hcardReal] at hweight'
    nlinarith
  have hsplit : additiveChoreCost cost later (lowRatioRoundRobinAllocation r cost chores earlier) =
      additiveChoreCost cost later
        (lowRatioRoundRobinAllocation r cost chores earlier \ {witness}) + cost later witness := by
    rw [additiveChoreCost_erase cost later
      (lowRatioRoundRobinAllocation r cost chores earlier) witness hwitness]
    linarith
  have hwitnessOne : 1 ≤ cost later witness :=
    IsOneOrRChoreCost.one_le cost r hcost hrone later witness
  rw [hsplit]
  linarith

/-- The `b = 1` initial reverse round of the He--Tao construction, followed by
`a` full minimum-cost rounds, is EFX for `1 ≤ r ≤ 2`. -/
theorem existsEfxOfOneOrR_lowRatio_b1
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (rounds : ℕ)
    (hrone : 1 ≤ r) (hrtwo : r ≤ 2) (hcost : IsOneOrRChoreCost cost r)
    (hcard : chores.card = 4 * rounds + 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  classical
  have hchoresNonempty : chores.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  let special : Item := lowRatioBestChore r cost 0 chores hchoresNonempty
  let residualChores : Finset Item := chores.erase special
  let residual : Allocation (Fin 4) Item :=
    lowRatioRoundRobinAllocation r cost residualChores
  let allocation : Allocation (Fin 4) Item := addItem residual 0 special
  have hspecial : special ∈ chores := by
    exact lowRatioBestChore_mem r cost 0 chores hchoresNonempty
  have hspecialNotResidual : special ∉ residualChores := by
    simp [residualChores]
  have hresidualCard : residualChores.card = 4 * rounds := by
    dsimp [residualChores]
    rw [Finset.card_erase_of_mem hspecial, hcard]
    omega
  have hresidualAllocation : IsAllocationOf residual residualChores := by
    exact lowRatioRoundRobinAllocation_isAllocationOf r cost residualChores
  have hresidualEqualCard : ∀ first second,
      (residual first).card = (residual second).card := by
    exact lowRatioRoundRobinAllocation_equalCard_of_card_mul_four r cost residualChores
      rounds hresidualCard
  have hweightNonneg : ∀ agent item,
      0 ≤ lowRatioRoundRobinWeight r cost agent item :=
    lowRatioRoundRobinWeight_nonneg Item r cost hcost hrone
  have hresidualComplementary : ComplementaryEF1 r cost residual := by
    exact lowRatioRoundRobin_complementaryEF1 r cost residualChores hweightNonneg
  have hresidualEfx : EFXForChores (additiveChoreCost cost) residual := by
    exact efxForChores_of_equalCard_complementaryEF1 Item r cost residual hcost hrone hrtwo
      hresidualEqualCard hresidualComplementary
  have hspecialNotOwned : ∀ agent, special ∉ residual agent := by
    intro agent howned
    exact hspecialNotResidual (hresidualAllocation.1 agent special howned)
  refine ⟨allocation, ?_, ?_⟩
  · have halloc := isAllocationOf_addItem_insert residual residualChores 0 special
        hresidualAllocation hspecialNotResidual
    simpa [allocation, residualChores, Finset.insert_erase hspecial] using halloc
  · intro own comparison
    by_cases hownZero : own = 0
    · subst own
      by_cases hcomparisonZero : comparison = 0
      · subst comparison
        by_cases hempty : allocation 0 = ∅
        · exact Or.inl hempty
        · right
          intro removed hremoved
          rw [additiveChoreCost_erase cost 0 (allocation 0) removed hremoved]
          have hnonneg : 0 ≤ cost 0 removed :=
            IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 0 removed
          linarith
      · right
        intro removed hremoved
        have hzeroEarlier : (0 : Fin 4).val < comparison.val := by
          omega
        have hnoEnvy : additiveChoreCost cost 0 (residual 0) ≤
            additiveChoreCost cost 0 (residual comparison) :=
          lowRatioRoundRobin_chore_noEnvy_of_earlier r cost residualChores
            hweightNonneg hresidualEqualCard 0 comparison hzeroEarlier
        have hcomparisonBundle : allocation comparison = residual comparison := by
          simp [allocation, addItem, hcomparisonZero]
        have hownCost : additiveChoreCost cost 0 (allocation 0) =
            cost 0 special + additiveChoreCost cost 0 (residual 0) := by
          rw [show allocation 0 = insert special (residual 0) by simp [allocation, addItem]]
          unfold additiveChoreCost
          rw [Finset.sum_insert (hspecialNotOwned 0)]
        rw [additiveChoreCost_erase cost 0 (allocation 0) removed hremoved,
          hcomparisonBundle, hownCost]
        by_cases hremovedSpecial : removed = special
        · rw [hremovedSpecial]
          linarith
        · have hremovedResidual : removed ∈ residual 0 := by
            have hremovedInsert : removed ∈ insert special (residual 0) := by
              simpa [allocation, addItem] using hremoved
            rcases Finset.mem_insert.mp hremovedInsert with hremovedSpecial' | hremovedResidual
            · exact (hremovedSpecial hremovedSpecial').elim
            · exact hremovedResidual
          have hremovedOne : 1 ≤ cost 0 removed :=
            IsOneOrRChoreCost.one_le cost r hcost hrone 0 removed
          rcases hcost 0 special with hspecialSmall | hspecialLarge
          · rw [hspecialSmall]
            linarith
          · have hremovedInPool : removed ∈ residualChores :=
              hresidualAllocation.1 0 removed hremovedResidual
            have hminimum : cost 0 special ≤ cost 0 removed := by
              dsimp [special]
              exact lowRatioBestChore_cost_le r cost 0 chores hchoresNonempty
                (Finset.erase_subset special chores hremovedInPool)
            have hremovedLarge : cost 0 removed = r := by
              rcases hcost 0 removed with hremovedSmall | hremovedLarge
              · linarith
              · exact hremovedLarge
            rw [hspecialLarge, hremovedLarge]
            linarith
    · have hownBundle : allocation own = residual own := by
        simp [allocation, addItem, hownZero]
      rcases hresidualEfx own comparison with hresidualEmpty | hresidualComparison
      · exact Or.inl (by simpa [hownBundle] using hresidualEmpty)
      · right
        intro removed hremoved
        have hremovedResidual : removed ∈ residual own := by
          simpa [hownBundle] using hremoved
        have hresidualInequality := hresidualComparison removed hremovedResidual
        have hcomparisonLower : additiveChoreCost cost own (residual comparison) ≤
            additiveChoreCost cost own (allocation comparison) := by
          by_cases hcomparisonZero : comparison = 0
          · subst comparison
            rw [show allocation 0 = insert special (residual 0) by simp [allocation, addItem]]
            unfold additiveChoreCost
            rw [Finset.sum_insert (hspecialNotOwned 0)]
            exact le_add_of_nonneg_left
              (IsOneOrRChoreCost.nonneg cost r hcost (by linarith) own special)
          · simp [allocation, addItem, hcomparisonZero]
        rw [hownBundle]
        exact hresidualInequality.trans hcomparisonLower

/-- The source's reverse-prefix comparison argument.  An initial segment of
agents receives one special chore each; a complete equal-cardinality round
robin allocation handles the residual pool.  The only special-item condition
needed is that a large chosen special chore forces every residual chore of its
owner to be large as well. -/
theorem efxForChores_of_lowRatioInitialPrefix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (b : ℕ) (initial residual : Allocation (Fin 4) Item)
    (hcost : IsOneOrRChoreCost cost r) (hrone : 1 ≤ r)
    (hresidualEfx : EFXForChores (additiveChoreCost cost) residual)
    (hnoEnvy : ∀ own comparison, own.val < comparison.val →
      additiveChoreCost cost own (residual own) ≤
        additiveChoreCost cost own (residual comparison))
    (hlater : ∀ own comparison, comparison.val < own.val →
      additiveChoreCost cost own (residual own) ≤
        additiveChoreCost cost own (residual comparison) + 1)
    (hprefixShape : ∀ agent,
      (agent.val < b → ∃ special, initial agent = {special}) ∧
      (b ≤ agent.val → initial agent = ∅))
    (hdisjoint : ∀ agent, Disjoint (initial agent) (residual agent))
    (hspecial : ∀ agent special, initial agent = {special} →
      cost agent special = 1 ∨
        (cost agent special = r ∧ ∀ item ∈ residual agent, cost agent item = r)) :
    EFXForChores (additiveChoreCost cost) (fun agent => initial agent ∪ residual agent) := by
  intro own comparison
  by_cases hownLong : own.val < b
  · obtain ⟨special, hprefixOwn⟩ := (hprefixShape own).1 hownLong
    have hspecialNotResidual : special ∉ residual own := by
      intro hspecialResidual
      exact Finset.disjoint_left.mp (hdisjoint own) (by simp [hprefixOwn]) hspecialResidual
    have hownBundle : initial own ∪ residual own = insert special (residual own) := by
      simp [hprefixOwn]
    have hownCost : additiveChoreCost cost own (initial own ∪ residual own) =
        cost own special + additiveChoreCost cost own (residual own) := by
      rw [hownBundle]
      unfold additiveChoreCost
      rw [Finset.sum_insert hspecialNotResidual]
    by_cases hsame : own = comparison
    · subst comparison
      by_cases hempty : initial own ∪ residual own = ∅
      · exact Or.inl hempty
      · right
        intro removed hremoved
        rw [additiveChoreCost_erase cost own (initial own ∪ residual own) removed hremoved]
        have hnonneg : 0 ≤ cost own removed :=
          IsOneOrRChoreCost.nonneg cost r hcost (by linarith) own removed
        linarith
    · have horder : own.val < comparison.val ∨ comparison.val < own.val := by
        have hne : own.val ≠ comparison.val := by
          intro hvalue
          exact hsame (Fin.ext hvalue)
        exact lt_or_gt_of_ne hne
      right
      intro removed hremoved
      rw [additiveChoreCost_erase cost own (initial own ∪ residual own) removed hremoved,
        hownCost]
      have hremovedUnion : removed ∈ insert special (residual own) := by
        simpa [← hownBundle] using hremoved
      rcases Finset.mem_insert.mp hremovedUnion with hremovedSpecial | hremovedResidual
      · subst removed
        rcases horder with hownEarlier | hcomparisonEarlier
        · have hresidualNoEnvy := hnoEnvy own comparison hownEarlier
          have hcomparisonLower : additiveChoreCost cost own (residual comparison) ≤
              additiveChoreCost cost own (initial comparison ∪ residual comparison) := by
            rw [additiveChoreCost_union cost own (initial comparison) (residual comparison)
              (hdisjoint comparison)]
            exact le_add_of_nonneg_left (additiveChoreCost_nonneg cost
              (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) own (initial comparison))
          linarith
        · have hcomparisonLong : comparison.val < b := lt_trans hcomparisonEarlier hownLong
          obtain ⟨comparisonSpecial, hprefixComparison⟩ :=
            (hprefixShape comparison).1 hcomparisonLong
          have hcomparisonNotResidual : comparisonSpecial ∉ residual comparison := by
            intro hcomparisonResidual
            exact Finset.disjoint_left.mp (hdisjoint comparison)
              (by simp [hprefixComparison]) hcomparisonResidual
          have hcomparisonCost :
              additiveChoreCost cost own (initial comparison ∪ residual comparison) =
                cost own comparisonSpecial + additiveChoreCost cost own (residual comparison) := by
            rw [show initial comparison ∪ residual comparison =
              insert comparisonSpecial (residual comparison) by simp [hprefixComparison]]
            unfold additiveChoreCost
            rw [Finset.sum_insert hcomparisonNotResidual]
          have hcomparisonOne : 1 ≤ cost own comparisonSpecial :=
            IsOneOrRChoreCost.one_le cost r hcost hrone own comparisonSpecial
          have hlaterBound := hlater own comparison hcomparisonEarlier
          rw [hcomparisonCost]
          linarith
      · rcases horder with hownEarlier | hcomparisonEarlier
        · have hresidualNoEnvy := hnoEnvy own comparison hownEarlier
          have hcomparisonLower : additiveChoreCost cost own (residual comparison) ≤
              additiveChoreCost cost own (initial comparison ∪ residual comparison) := by
            rw [additiveChoreCost_union cost own (initial comparison) (residual comparison)
              (hdisjoint comparison)]
            exact le_add_of_nonneg_left (additiveChoreCost_nonneg cost
              (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) own (initial comparison))
          have hremovedOne : 1 ≤ cost own removed :=
            IsOneOrRChoreCost.one_le cost r hcost hrone own removed
          rcases hspecial own special hprefixOwn with hspecialSmall | ⟨hspecialLarge, hresidualLarge⟩
          · rw [hspecialSmall]
            linarith
          · have hremovedLarge := hresidualLarge removed hremovedResidual
            rw [hspecialLarge, hremovedLarge]
            linarith
        · have hcomparisonLong : comparison.val < b := lt_trans hcomparisonEarlier hownLong
          obtain ⟨comparisonSpecial, hprefixComparison⟩ :=
            (hprefixShape comparison).1 hcomparisonLong
          have hcomparisonNotResidual : comparisonSpecial ∉ residual comparison := by
            intro hcomparisonResidual
            exact Finset.disjoint_left.mp (hdisjoint comparison)
              (by simp [hprefixComparison]) hcomparisonResidual
          have hcomparisonCost :
              additiveChoreCost cost own (initial comparison ∪ residual comparison) =
                cost own comparisonSpecial + additiveChoreCost cost own (residual comparison) := by
            rw [show initial comparison ∪ residual comparison =
              insert comparisonSpecial (residual comparison) by simp [hprefixComparison]]
            unfold additiveChoreCost
            rw [Finset.sum_insert hcomparisonNotResidual]
          have hcomparisonOne : 1 ≤ cost own comparisonSpecial :=
            IsOneOrRChoreCost.one_le cost r hcost hrone own comparisonSpecial
          have hlaterBound := hlater own comparison hcomparisonEarlier
          rcases hspecial own special hprefixOwn with hspecialSmall | ⟨hspecialLarge, hresidualLarge⟩
          · rcases hresidualEfx own comparison with hresidualEmpty | hresidualComparison
            · have hresidualNonempty : (residual own).Nonempty := ⟨removed, hremovedResidual⟩
              exact (hresidualNonempty.ne_empty hresidualEmpty).elim
            · have hresidualBound := hresidualComparison removed hremovedResidual
              rw [additiveChoreCost_erase cost own (residual own) removed hremovedResidual]
                at hresidualBound
              rw [hspecialSmall, hcomparisonCost]
              linarith
          · have hremovedLarge := hresidualLarge removed hremovedResidual
            rw [hspecialLarge, hremovedLarge, hcomparisonCost]
            linarith
  · have hprefixOwn : initial own = ∅ :=
      (hprefixShape own).2 (Nat.le_of_not_gt hownLong)
    rcases hresidualEfx own comparison with hresidualEmpty | hresidualComparison
    · exact Or.inl (by simp [hprefixOwn, hresidualEmpty])
    · right
      intro removed hremoved
      have hremovedResidual : removed ∈ residual own := by
        simpa [hprefixOwn] using hremoved
      have hresidualBound := hresidualComparison removed hremovedResidual
      have hcomparisonLower : additiveChoreCost cost own (residual comparison) ≤
          additiveChoreCost cost own (initial comparison ∪ residual comparison) := by
        rw [additiveChoreCost_union cost own (initial comparison) (residual comparison)
          (hdisjoint comparison)]
        exact le_add_of_nonneg_left (additiveChoreCost_nonneg cost
          (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) own (initial comparison))
      simpa [hprefixOwn] using hresidualBound.trans hcomparisonLower

/-- The `b = 2` initial reverse round of the He--Tao construction, followed
by `a` full minimum-cost rounds, is EFX for `1 ≤ r ≤ 2`. -/
theorem existsEfxOfOneOrR_lowRatio_b2
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (rounds : ℕ)
    (hrone : 1 ≤ r) (hrtwo : r ≤ 2) (hcost : IsOneOrRChoreCost cost r)
    (hcard : chores.card = 4 * rounds + 2) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  classical
  have hchoresNonempty : chores.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  let special1 : Item := lowRatioBestChore r cost 1 chores hchoresNonempty
  let remaining1 : Finset Item := chores.erase special1
  have hspecial1 : special1 ∈ chores := by
    exact lowRatioBestChore_mem r cost 1 chores hchoresNonempty
  have hremaining1Card : remaining1.card = 4 * rounds + 1 := by
    dsimp [remaining1]
    rw [Finset.card_erase_of_mem hspecial1, hcard]
    omega
  have hremaining1Nonempty : remaining1.Nonempty := Finset.card_pos.mp (by
    rw [hremaining1Card]
    omega)
  let special0 : Item := lowRatioBestChore r cost 0 remaining1 hremaining1Nonempty
  let residualChores : Finset Item := remaining1.erase special0
  let residual : Allocation (Fin 4) Item :=
    lowRatioRoundRobinAllocation r cost residualChores
  let initial : Allocation (Fin 4) Item := fun agent =>
    if agent = 0 then {special0} else if agent = 1 then {special1} else ∅
  let allocation : Allocation (Fin 4) Item := fun agent => initial agent ∪ residual agent
  have hspecial0 : special0 ∈ remaining1 := by
    exact lowRatioBestChore_mem r cost 0 remaining1 hremaining1Nonempty
  have hspecial0NeSpecial1 : special0 ≠ special1 := by
    dsimp [remaining1] at hspecial0
    exact (Finset.mem_erase.mp hspecial0).1
  have hspecial0NotResidual : special0 ∉ residualChores := by
    simp [residualChores]
  have hspecial1NotResidual : special1 ∉ residualChores := by
    intro hitem
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hitem).2).1 rfl
  have hresidualCard : residualChores.card = 4 * rounds := by
    dsimp [residualChores]
    rw [Finset.card_erase_of_mem hspecial0, hremaining1Card]
    omega
  have hresidualAllocation : IsAllocationOf residual residualChores := by
    exact lowRatioRoundRobinAllocation_isAllocationOf r cost residualChores
  have hresidualEqualCard : ∀ first second,
      (residual first).card = (residual second).card := by
    exact lowRatioRoundRobinAllocation_equalCard_of_card_mul_four r cost residualChores
      rounds hresidualCard
  have hweightNonneg : ∀ agent item,
      0 ≤ lowRatioRoundRobinWeight r cost agent item :=
    lowRatioRoundRobinWeight_nonneg Item r cost hcost hrone
  have hresidualEfx : EFXForChores (additiveChoreCost cost) residual := by
    exact efxForChores_of_equalCard_complementaryEF1 Item r cost residual hcost hrone hrtwo
      hresidualEqualCard (lowRatioRoundRobin_complementaryEF1 r cost residualChores
        hweightNonneg)
  have hspecial0NotOwned : special0 ∉ residual 0 := by
    intro hitem
    exact hspecial0NotResidual (hresidualAllocation.1 0 special0 hitem)
  have hspecial1NotOwned : special1 ∉ residual 1 := by
    intro hitem
    exact hspecial1NotResidual (hresidualAllocation.1 1 special1 hitem)
  have hwithOne : IsAllocationOf (addItem residual 1 special1)
      (insert special1 residualChores) :=
    isAllocationOf_addItem_insert residual residualChores 1 special1 hresidualAllocation
      hspecial1NotResidual
  have hspecial0NotWithOnePool : special0 ∉ insert special1 residualChores := by
    simp [hspecial0NeSpecial1, hspecial0NotResidual]
  have hwithZero : IsAllocationOf (addItem (addItem residual 1 special1) 0 special0)
      (insert special0 (insert special1 residualChores)) :=
    isAllocationOf_addItem_insert (addItem residual 1 special1)
      (insert special1 residualChores) 0 special0 hwithOne hspecial0NotWithOnePool
  have hpool : insert special0 (insert special1 residualChores) = chores := by
    calc
      insert special0 (insert special1 residualChores) =
          insert special1 (insert special0 residualChores) :=
        Finset.insert_comm _ _ _
      _ = insert special1 remaining1 := by
        rw [show insert special0 residualChores = remaining1 by
          dsimp [residualChores]
          exact Finset.insert_erase hspecial0]
      _ = chores := Finset.insert_erase hspecial1
  have hallocationEq : allocation = addItem (addItem residual 1 special1) 0 special0 := by
    funext agent
    fin_cases agent <;> simp [allocation, initial, addItem]
  refine ⟨allocation, ?_, ?_⟩
  · rw [hallocationEq]
    simpa only [hpool] using hwithZero
  · have hnoEnvy : ∀ own comparison, own.val < comparison.val →
        additiveChoreCost cost own (residual own) ≤
          additiveChoreCost cost own (residual comparison) := by
      intro own comparison hlt
      exact lowRatioRoundRobin_chore_noEnvy_of_earlier r cost residualChores
        hweightNonneg hresidualEqualCard own comparison hlt
    have hlater : ∀ own comparison, comparison.val < own.val →
        additiveChoreCost cost own (residual own) ≤
          additiveChoreCost cost own (residual comparison) + 1 := by
      intro own comparison hlt
      by_cases hempty : residual comparison = ∅
      · have hownEmpty : residual own = ∅ := by
          apply Finset.card_eq_zero.mp
          have hequal := hresidualEqualCard own comparison
          rw [hempty] at hequal
          simpa using hequal
        norm_num [hownEmpty, hempty, additiveChoreCost]
      · exact lowRatioRoundRobin_chore_later_le_add_one r cost residualChores
          hweightNonneg hcost hrone hrtwo hresidualEqualCard own comparison hlt
          (Finset.nonempty_iff_ne_empty.mpr hempty)
    have hprefixShape : ∀ agent,
        (agent.val < 2 → ∃ special, initial agent = {special}) ∧
        (2 ≤ agent.val → initial agent = ∅) := by
      intro agent
      fin_cases agent
      · constructor
        · intro _
          exact ⟨special0, by simp [initial]⟩
        · intro h
          norm_num at h
      · constructor
        · intro _
          exact ⟨special1, by simp [initial]⟩
        · intro h
          norm_num at h
      · constructor
        · intro h
          norm_num at h
        · intro _
          simp [initial]
      · constructor
        · intro h
          norm_num at h
        · intro _
          simp [initial]
    have hdisjoint : ∀ agent, Disjoint (initial agent) (residual agent) := by
      intro agent
      fin_cases agent
      · rw [Finset.disjoint_left]
        intro item hinitial hresidual
        have hitem : item = special0 := by simpa [initial] using hinitial
        subst item
        exact hspecial0NotOwned hresidual
      · rw [Finset.disjoint_left]
        intro item hinitial hresidual
        have hitem : item = special1 := by simpa [initial] using hinitial
        subst item
        exact hspecial1NotOwned hresidual
      · simp [initial]
      · simp [initial]
    have hspecial : ∀ agent special, initial agent = {special} →
        cost agent special = 1 ∨
          (cost agent special = r ∧ ∀ item ∈ residual agent, cost agent item = r) := by
      intro agent special hinitial
      fin_cases agent
      · have hspecialEq : special0 = special := by simpa [initial] using hinitial
        subst special
        rcases hcost 0 special0 with hsmall | hlarge
        · exact Or.inl hsmall
        · right
          refine ⟨hlarge, ?_⟩
          intro item hitem
          exact lowRatioBestChore_large_forces_large_on_subset r cost 0 remaining1
            residualChores hremaining1Nonempty hcost hrone
            (Finset.erase_subset special0 remaining1) hlarge item
            (hresidualAllocation.1 0 item hitem)
      · have hspecialEq : special1 = special := by simpa [initial] using hinitial
        subst special
        rcases hcost 1 special1 with hsmall | hlarge
        · exact Or.inl hsmall
        · right
          refine ⟨hlarge, ?_⟩
          intro item hitem
          exact lowRatioBestChore_large_forces_large_on_subset r cost 1 chores
            residualChores hchoresNonempty hcost hrone
            (fun item hitem => Finset.erase_subset special1 chores
              (Finset.erase_subset special0 remaining1 hitem)) hlarge item
            (hresidualAllocation.1 1 item hitem)
      · simp [initial] at hinitial
      · simp [initial] at hinitial
    exact efxForChores_of_lowRatioInitialPrefix Item r cost 2 initial residual hcost hrone
      hresidualEfx hnoEnvy hlater hprefixShape hdisjoint hspecial

/-- The `b = 3` initial reverse round of the He--Tao construction, followed
by `a` full minimum-cost rounds, is EFX for `1 ≤ r ≤ 2`. -/
theorem existsEfxOfOneOrR_lowRatio_b3
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (rounds : ℕ)
    (hrone : 1 ≤ r) (hrtwo : r ≤ 2) (hcost : IsOneOrRChoreCost cost r)
    (hcard : chores.card = 4 * rounds + 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  classical
  have hchoresNonempty : chores.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  let special2 : Item := lowRatioBestChore r cost 2 chores hchoresNonempty
  let remaining2 : Finset Item := chores.erase special2
  have hspecial2 : special2 ∈ chores := by
    exact lowRatioBestChore_mem r cost 2 chores hchoresNonempty
  have hremaining2Card : remaining2.card = 4 * rounds + 2 := by
    dsimp [remaining2]
    rw [Finset.card_erase_of_mem hspecial2, hcard]
    omega
  have hremaining2Nonempty : remaining2.Nonempty := Finset.card_pos.mp (by
    rw [hremaining2Card]
    omega)
  let special1 : Item := lowRatioBestChore r cost 1 remaining2 hremaining2Nonempty
  let remaining1 : Finset Item := remaining2.erase special1
  have hspecial1 : special1 ∈ remaining2 := by
    exact lowRatioBestChore_mem r cost 1 remaining2 hremaining2Nonempty
  have hremaining1Card : remaining1.card = 4 * rounds + 1 := by
    dsimp [remaining1]
    rw [Finset.card_erase_of_mem hspecial1, hremaining2Card]
    omega
  have hremaining1Nonempty : remaining1.Nonempty := Finset.card_pos.mp (by
    rw [hremaining1Card]
    omega)
  let special0 : Item := lowRatioBestChore r cost 0 remaining1 hremaining1Nonempty
  let residualChores : Finset Item := remaining1.erase special0
  let residual : Allocation (Fin 4) Item :=
    lowRatioRoundRobinAllocation r cost residualChores
  let initial : Allocation (Fin 4) Item := fun agent =>
    if agent = 0 then {special0}
    else if agent = 1 then {special1}
    else if agent = 2 then {special2} else ∅
  let allocation : Allocation (Fin 4) Item := fun agent => initial agent ∪ residual agent
  have hspecial0 : special0 ∈ remaining1 := by
    exact lowRatioBestChore_mem r cost 0 remaining1 hremaining1Nonempty
  have hspecial1NeSpecial2 : special1 ≠ special2 := by
    exact (Finset.mem_erase.mp hspecial1).1
  have hspecial0NeSpecial1 : special0 ≠ special1 := by
    exact (Finset.mem_erase.mp hspecial0).1
  have hspecial0InRemaining2 : special0 ∈ remaining2 :=
    (Finset.mem_erase.mp hspecial0).2
  have hspecial0NeSpecial2 : special0 ≠ special2 := by
    exact (Finset.mem_erase.mp hspecial0InRemaining2).1
  have hspecial0NotResidual : special0 ∉ residualChores := by
    simp [residualChores]
  have hspecial1NotResidual : special1 ∉ residualChores := by
    intro hitem
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hitem).2).1 rfl
  have hspecial2NotResidual : special2 ∉ residualChores := by
    intro hitem
    exact (Finset.mem_erase.mp
      (Finset.mem_erase.mp (Finset.mem_erase.mp hitem).2).2).1 rfl
  have hresidualCard : residualChores.card = 4 * rounds := by
    dsimp [residualChores]
    rw [Finset.card_erase_of_mem hspecial0, hremaining1Card]
    omega
  have hresidualAllocation : IsAllocationOf residual residualChores := by
    exact lowRatioRoundRobinAllocation_isAllocationOf r cost residualChores
  have hresidualEqualCard : ∀ first second,
      (residual first).card = (residual second).card := by
    exact lowRatioRoundRobinAllocation_equalCard_of_card_mul_four r cost residualChores
      rounds hresidualCard
  have hweightNonneg : ∀ agent item,
      0 ≤ lowRatioRoundRobinWeight r cost agent item :=
    lowRatioRoundRobinWeight_nonneg Item r cost hcost hrone
  have hresidualEfx : EFXForChores (additiveChoreCost cost) residual := by
    exact efxForChores_of_equalCard_complementaryEF1 Item r cost residual hcost hrone hrtwo
      hresidualEqualCard (lowRatioRoundRobin_complementaryEF1 r cost residualChores
        hweightNonneg)
  have hspecial0NotOwned : special0 ∉ residual 0 := by
    intro hitem
    exact hspecial0NotResidual (hresidualAllocation.1 0 special0 hitem)
  have hspecial1NotOwned : special1 ∉ residual 1 := by
    intro hitem
    exact hspecial1NotResidual (hresidualAllocation.1 1 special1 hitem)
  have hspecial2NotOwned : special2 ∉ residual 2 := by
    intro hitem
    exact hspecial2NotResidual (hresidualAllocation.1 2 special2 hitem)
  have hwithTwo : IsAllocationOf (addItem residual 2 special2)
      (insert special2 residualChores) :=
    isAllocationOf_addItem_insert residual residualChores 2 special2 hresidualAllocation
      hspecial2NotResidual
  have hspecial1NotWithTwoPool : special1 ∉ insert special2 residualChores := by
    simp [hspecial1NeSpecial2, hspecial1NotResidual]
  have hwithOne : IsAllocationOf (addItem (addItem residual 2 special2) 1 special1)
      (insert special1 (insert special2 residualChores)) :=
    isAllocationOf_addItem_insert (addItem residual 2 special2)
      (insert special2 residualChores) 1 special1 hwithTwo hspecial1NotWithTwoPool
  have hspecial0NotWithOnePool : special0 ∉ insert special1 (insert special2 residualChores) := by
    simp [hspecial0NeSpecial1, hspecial0NeSpecial2, hspecial0NotResidual]
  have hwithZero : IsAllocationOf
      (addItem (addItem (addItem residual 2 special2) 1 special1) 0 special0)
      (insert special0 (insert special1 (insert special2 residualChores))) :=
    isAllocationOf_addItem_insert (addItem (addItem residual 2 special2) 1 special1)
      (insert special1 (insert special2 residualChores)) 0 special0 hwithOne hspecial0NotWithOnePool
  have hpool : insert special0 (insert special1 (insert special2 residualChores)) = chores := by
    calc
      insert special0 (insert special1 (insert special2 residualChores)) =
          insert special1 (insert special2 (insert special0 residualChores)) := by
        rw [Finset.insert_comm special0 special1, Finset.insert_comm special0 special2]
      _ = insert special1 (insert special2 remaining1) := by
        rw [show insert special0 residualChores = remaining1 by
          dsimp [residualChores]
          exact Finset.insert_erase hspecial0]
      _ = insert special2 (insert special1 remaining1) :=
        Finset.insert_comm _ _ _
      _ = insert special2 remaining2 := by
        rw [show insert special1 remaining1 = remaining2 by
          dsimp [remaining1]
          exact Finset.insert_erase hspecial1]
      _ = chores := Finset.insert_erase hspecial2
  have hallocationEq : allocation =
      addItem (addItem (addItem residual 2 special2) 1 special1) 0 special0 := by
    funext agent
    fin_cases agent <;> simp [allocation, initial, addItem]
  refine ⟨allocation, ?_, ?_⟩
  · rw [hallocationEq]
    simpa only [hpool] using hwithZero
  · have hnoEnvy : ∀ own comparison, own.val < comparison.val →
        additiveChoreCost cost own (residual own) ≤
          additiveChoreCost cost own (residual comparison) := by
      intro own comparison hlt
      exact lowRatioRoundRobin_chore_noEnvy_of_earlier r cost residualChores
        hweightNonneg hresidualEqualCard own comparison hlt
    have hlater : ∀ own comparison, comparison.val < own.val →
        additiveChoreCost cost own (residual own) ≤
          additiveChoreCost cost own (residual comparison) + 1 := by
      intro own comparison hlt
      by_cases hempty : residual comparison = ∅
      · have hownEmpty : residual own = ∅ := by
          apply Finset.card_eq_zero.mp
          have hequal := hresidualEqualCard own comparison
          rw [hempty] at hequal
          simpa using hequal
        norm_num [hownEmpty, hempty, additiveChoreCost]
      · exact lowRatioRoundRobin_chore_later_le_add_one r cost residualChores
          hweightNonneg hcost hrone hrtwo hresidualEqualCard own comparison hlt
          (Finset.nonempty_iff_ne_empty.mpr hempty)
    have hprefixShape : ∀ agent,
        (agent.val < 3 → ∃ special, initial agent = {special}) ∧
        (3 ≤ agent.val → initial agent = ∅) := by
      intro agent
      fin_cases agent
      · constructor
        · intro _
          exact ⟨special0, by simp [initial]⟩
        · intro h
          norm_num at h
      · constructor
        · intro _
          exact ⟨special1, by simp [initial]⟩
        · intro h
          norm_num at h
      · constructor
        · intro _
          exact ⟨special2, by simp [initial]⟩
        · intro h
          norm_num at h
      · constructor
        · intro h
          norm_num at h
        · intro _
          simp [initial]
    have hdisjoint : ∀ agent, Disjoint (initial agent) (residual agent) := by
      intro agent
      fin_cases agent
      · rw [Finset.disjoint_left]
        intro item hinitial hresidual
        have hitem : item = special0 := by simpa [initial] using hinitial
        subst item
        exact hspecial0NotOwned hresidual
      · rw [Finset.disjoint_left]
        intro item hinitial hresidual
        have hitem : item = special1 := by simpa [initial] using hinitial
        subst item
        exact hspecial1NotOwned hresidual
      · rw [Finset.disjoint_left]
        intro item hinitial hresidual
        have hitem : item = special2 := by simpa [initial] using hinitial
        subst item
        exact hspecial2NotOwned hresidual
      · simp [initial]
    have hspecial : ∀ agent special, initial agent = {special} →
        cost agent special = 1 ∨
          (cost agent special = r ∧ ∀ item ∈ residual agent, cost agent item = r) := by
      intro agent special hinitial
      fin_cases agent
      · have hspecialEq : special0 = special := by simpa [initial] using hinitial
        subst special
        rcases hcost 0 special0 with hsmall | hlarge
        · exact Or.inl hsmall
        · right
          refine ⟨hlarge, ?_⟩
          intro item hitem
          exact lowRatioBestChore_large_forces_large_on_subset r cost 0 remaining1
            residualChores hremaining1Nonempty hcost hrone
            (Finset.erase_subset special0 remaining1) hlarge item
            (hresidualAllocation.1 0 item hitem)
      · have hspecialEq : special1 = special := by simpa [initial] using hinitial
        subst special
        rcases hcost 1 special1 with hsmall | hlarge
        · exact Or.inl hsmall
        · right
          refine ⟨hlarge, ?_⟩
          intro item hitem
          exact lowRatioBestChore_large_forces_large_on_subset r cost 1 remaining2
            residualChores hremaining2Nonempty hcost hrone
            (fun item hitem => Finset.erase_subset special1 remaining2
              (Finset.erase_subset special0 remaining1 hitem)) hlarge item
            (hresidualAllocation.1 1 item hitem)
      · have hspecialEq : special2 = special := by simpa [initial] using hinitial
        subst special
        rcases hcost 2 special2 with hsmall | hlarge
        · exact Or.inl hsmall
        · right
          refine ⟨hlarge, ?_⟩
          intro item hitem
          exact lowRatioBestChore_large_forces_large_on_subset r cost 2 chores
            residualChores hchoresNonempty hcost hrone
            (fun item hitem => Finset.erase_subset special2 chores
              (Finset.erase_subset special1 remaining2
                (Finset.erase_subset special0 remaining1 hitem))) hlarge item
            (hresidualAllocation.1 2 item hitem)
      · simp [initial] at hinitial
    exact efxForChores_of_lowRatioInitialPrefix Item r cost 3 initial residual hcost hrone
      hresidualEfx hnoEnvy hlater hprefixShape hdisjoint hspecial

/-- The complete normalized low-ratio branch of Theorem 3.  Dividing the
number of chores by four selects one of the source's four reverse-prefix
orders, including the ordinary full-round case when the remainder is zero. -/
theorem existsEfxOfOneOrR_lowRatio
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hrone : 1 ≤ r) (hrtwo : r ≤ 2)
    (hcost : IsOneOrRChoreCost cost r) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  let rounds := chores.card / 4
  let b := chores.card % 4
  have hdecomposition : chores.card = 4 * rounds + b := by
    dsimp [rounds, b]
    omega
  have hb : b < 4 := by
    dsimp [b]
    exact Nat.mod_lt _ (by omega)
  interval_cases b
  · exact existsEfxOfOneOrR_lowRatio_b0 Item r cost chores rounds hrone hrtwo hcost
      (by omega)
  · exact existsEfxOfOneOrR_lowRatio_b1 Item r cost chores rounds hrone hrtwo hcost
      (by omega)
  · exact existsEfxOfOneOrR_lowRatio_b2 Item r cost chores rounds hrone hrtwo hcost
      (by omega)
  · exact existsEfxOfOneOrR_lowRatio_b3 Item r cost chores rounds hrone hrtwo hcost
      (by omega)

end HT26EFXChores
