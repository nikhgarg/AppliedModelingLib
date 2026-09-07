import HT26EFXChores.Canonical

/-!
# Canonical-prefix orientation for source Case B.2.1(b)

The disjoint-edge case needs a canonical prefix whose short endpoint on the
`(2,3)` edge has an `r` advantage over its long endpoint.  This file records
the dichotomy that makes the source's move-and-swap construction possible.

Source: `EFXadditivechores.tex`, lines 2411--2419.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- The source's B.2.1(b) transfer: remove one chore from the presently long
agent `2` and give it to agent `3`.  The subsequent label swap is handled
separately, so this allocation keeps the original labels. -/
def b1DisjointTransferredAllocation {Item : Type} [DecidableEq Item]
    (allocation : Allocation (Fin 4) Item) (item : Item) : Allocation (Fin 4) Item :=
  fun agent =>
    if agent = 2 then allocation 2 \ {item}
    else if agent = 3 then allocation 3 ∪ {item}
    else allocation agent

/-- Moving an item between the two distinguished bundles preserves
feasibility when the item was originally owned by agent `2`. -/
theorem isAllocationOf_b1DisjointTransferredAllocation
    (Item : Type) [DecidableEq Item] (chores : Finset Item)
    (allocation : Allocation (Fin 4) Item) (item : Item)
    (hallocation : IsAllocationOf allocation chores) (hitem : item ∈ allocation 2) :
    IsAllocationOf (b1DisjointTransferredAllocation allocation item) chores := by
  classical
  constructor
  · intro agent chore hchore
    fin_cases agent
    · exact hallocation.1 0 chore (by
        simpa [b1DisjointTransferredAllocation] using hchore)
    · exact hallocation.1 1 chore (by
        simpa [b1DisjointTransferredAllocation] using hchore)
    · have hmem : chore ∈ allocation 2 \ {item} := by
        simpa [b1DisjointTransferredAllocation] using hchore
      exact hallocation.1 2 chore (Finset.mem_sdiff.mp hmem |>.1)
    · have hmem : chore = item ∨ chore ∈ allocation 3 := by
        simpa [b1DisjointTransferredAllocation] using hchore
      rcases hmem with hchoreEq | hmem
      · subst chore
        exact hallocation.1 2 item hitem
      · exact hallocation.1 3 chore hmem
  · intro chore hchore
    obtain ⟨owner, howner, hunique⟩ := hallocation.2 chore hchore
    by_cases hownerTwo : owner = 2
    · subst owner
      by_cases hchoreItem : chore = item
      · subst chore
        refine ⟨3, by simp [b1DisjointTransferredAllocation], ?_⟩
        intro other hother
        fin_cases other
        · have hotherOld : item ∈ allocation 0 := by
            simpa [b1DisjointTransferredAllocation] using hother
          exact False.elim ((by decide : (0 : Fin 4) ≠ 2) (hunique 0 hotherOld))
        · have hotherOld : item ∈ allocation 1 := by
            simpa [b1DisjointTransferredAllocation] using hother
          exact False.elim ((by decide : (1 : Fin 4) ≠ 2) (hunique 1 hotherOld))
        · have hnot : item ∉ allocation 2 \ {item} := by simp
          exact (hnot (by simpa [b1DisjointTransferredAllocation] using hother)).elim
        · rfl
      · refine ⟨2, ?_, ?_⟩
        · simpa [b1DisjointTransferredAllocation, hchoreItem] using howner
        · intro other hother
          fin_cases other
          · exact hunique 0 (by simpa [b1DisjointTransferredAllocation] using hother)
          · exact hunique 1 (by simpa [b1DisjointTransferredAllocation] using hother)
          · rfl
          · have hmem : chore = item ∨ chore ∈ allocation 3 := by
              simpa [b1DisjointTransferredAllocation] using hother
            rcases hmem with hitemEq | hmem
            · exact (hchoreItem hitemEq).elim
            · exact hunique 3 hmem
    · refine ⟨owner, ?_, ?_⟩
      · by_cases hownerThree : owner = 3
        · subst owner
          simp [b1DisjointTransferredAllocation, howner]
        · simpa [b1DisjointTransferredAllocation, hownerTwo, hownerThree] using howner
      · intro other hother
        by_cases hotherTwo : other = 2
        · subst other
          have hmem : chore ∈ allocation 2 \ {item} := by
            simpa [b1DisjointTransferredAllocation] using hother
          exact hunique 2 (Finset.mem_sdiff.mp hmem |>.1)
        by_cases hotherThree : other = 3
        · subst other
          have hmem : chore = item ∨ chore ∈ allocation 3 := by
            simpa [b1DisjointTransferredAllocation] using hother
          rcases hmem with hitemEq | hmem
          · subst chore
            exact (hownerTwo (hunique 2 hitem).symm).elim
          · exact hunique 3 hmem
        · exact hunique other (by
            simpa [b1DisjointTransferredAllocation, hotherTwo, hotherThree] using hother)

/-- In the move branch of source Case B.2.1(b), the transferred item is small
for agent `3` and hence large for agent `2`.  Moving it transfers the unique
long quota from `2` to `3` while preserving canonicity. -/
theorem canonical_b1DisjointTransferredAllocation
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (allocation : Allocation (Fin 4) Item) (item : Item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost chores quota allocation)
    (hitemAtMostOne : IsSmallForAtMostOne cost item)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hitem : item ∈ allocation 2) (hitemSmallThree : IsSmallChore cost 3 item) :
    IsCanonicalSmallChoreAllocation cost chores (canonicalQuota a {3})
      (b1DisjointTransferredAllocation allocation item) := by
  classical
  have hitemChores : item ∈ chores := hcanonical.1.1 2 item hitem
  have hitemNotThree : item ∉ allocation 3 := by
    intro hitemThree
    exact (by decide : (2 : Fin 4) ≠ 3)
      (isAllocationOf_owner_unique hcanonical.1 hitemChores hitem hitemThree)
  have hitemNotSmallTwo : ¬ IsSmallChore cost 2 item := by
    intro hitemSmallTwo
    have hsmallTwo : 2 ∈ smallAgentSet cost item := by
      simpa [smallAgentSet, IsSmallChore] using hitemSmallTwo
    have hsmallThree : 3 ∈ smallAgentSet cost item := by
      simpa [smallAgentSet, IsSmallChore] using hitemSmallThree
    have hsubset : ({2, 3} : Finset (Fin 4)) ⊆ smallAgentSet cost item := by
      intro agent hagent
      simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
      rcases hagent with rfl | rfl
      · exact hsmallTwo
      · exact hsmallThree
    have hcard := Finset.card_le_card hsubset
    have hsmallCard := hitemAtMostOne
    change (smallAgentSet cost item).card ≤ 1 at hsmallCard
    have hpairCard : ({2, 3} : Finset (Fin 4)).card = 2 := by decide
    omega
  constructor
  · exact isAllocationOf_b1DisjointTransferredAllocation Item chores allocation item
      hcanonical.1 hitem
  · intro agent
    fin_cases agent
    · constructor
      · change (allocation 0).card = canonicalQuota a {3} 0
        rw [hcanonical.2 0 |>.1, hquota0]
        simp [canonicalQuota]
      · change (ownSmallChoreSet cost (allocation 0) 0).card =
          min (canonicalQuota a {3} 0) (ownSmallChoreSet cost chores 0).card
        rw [hcanonical.2 0 |>.2, hquota0]
        simp [canonicalQuota]
    · constructor
      · change (allocation 1).card = canonicalQuota a {3} 1
        rw [hcanonical.2 1 |>.1, hquota1]
        simp [canonicalQuota]
      · change (ownSmallChoreSet cost (allocation 1) 1).card =
          min (canonicalQuota a {3} 1) (ownSmallChoreSet cost chores 1).card
        rw [hcanonical.2 1 |>.2, hquota1]
        simp [canonicalQuota]
    · have hsmallTwoSubset : ownSmallChoreSet cost (allocation 2) 2 ⊆
        allocation 2 \ {item} := by
        intro chore hchore
        rcases Finset.mem_filter.mp hchore with ⟨hmem, hsmall⟩
        refine Finset.mem_sdiff.mpr ⟨hmem, ?_⟩
        simp only [Finset.mem_singleton]
        intro hchoreItem
        subst chore
        exact hitemNotSmallTwo hsmall
      have hsmallTwoCardLe : (ownSmallChoreSet cost (allocation 2) 2).card ≤ a := by
        calc
          (ownSmallChoreSet cost (allocation 2) 2).card ≤ (allocation 2 \ {item}).card :=
            Finset.card_le_card hsmallTwoSubset
          _ = a := by
            rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem,
              hcanonical.2 2 |>.1, hquota2]
            omega
      have hwholeSmallTwo : (ownSmallChoreSet cost chores 2).card ≤ a := by
        by_contra hnot
        have hge : a + 1 ≤ (ownSmallChoreSet cost chores 2).card := by omega
        have hcanonicalTwo := hcanonical.2 2 |>.2
        rw [hquota2, Nat.min_eq_left hge] at hcanonicalTwo
        omega
      have hwholeSmallTwoSucc : (ownSmallChoreSet cost chores 2).card ≤ a + 1 := by
        omega
      have htransferredSmallTwo : ownSmallChoreSet cost (allocation 2 \ {item}) 2 =
          ownSmallChoreSet cost (allocation 2) 2 := by
        ext chore
        simp only [ownSmallChoreSet, Finset.mem_filter, Finset.mem_sdiff,
          Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hmem, _⟩, hsmall⟩
          exact ⟨hmem, hsmall⟩
        · rintro ⟨hmem, hsmall⟩
          refine ⟨⟨hmem, ?_⟩, hsmall⟩
          intro hchoreItem
          subst chore
          exact hitemNotSmallTwo hsmall
      constructor
      · change (allocation 2 \ {item}).card = canonicalQuota a {3} 2
        rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem,
          hcanonical.2 2 |>.1, hquota2]
        simp [canonicalQuota]
      · change (ownSmallChoreSet cost (allocation 2 \ {item}) 2).card =
          min (canonicalQuota a {3} 2) (ownSmallChoreSet cost chores 2).card
        rw [htransferredSmallTwo, hcanonical.2 2 |>.2, hquota2,
          Nat.min_eq_right hwholeSmallTwoSucc]
        simp [canonicalQuota, Nat.min_eq_right hwholeSmallTwo]
    · have hwholeSmallThree : a + 1 ≤ (ownSmallChoreSet cost chores 3).card := by
        by_contra hnot
        have hle : (ownSmallChoreSet cost chores 3).card ≤ a := by omega
        have hcanonicalThree : (ownSmallChoreSet cost (allocation 3) 3).card =
            (ownSmallChoreSet cost chores 3).card := by
          rw [hcanonical.2 3 |>.2, hquota3, Nat.min_eq_right hle]
        have hallocationThreeSubset : allocation 3 ⊆ chores := by
          intro chore hchore
          exact hcanonical.1.1 3 chore hchore
        have hsmallThreeEq : ownSmallChoreSet cost (allocation 3) 3 =
            ownSmallChoreSet cost chores 3 :=
          ownSmallChoreSet_eq_of_subset_and_card cost 3 hallocationThreeSubset hcanonicalThree
        have hitemWholeSmall : item ∈ ownSmallChoreSet cost chores 3 := by
          exact Finset.mem_filter.mpr ⟨hitemChores, hitemSmallThree⟩
        have hitemAllocationSmall : item ∈ ownSmallChoreSet cost (allocation 3) 3 := by
          rw [hsmallThreeEq]
          exact hitemWholeSmall
        exact hitemNotThree (Finset.mem_filter.mp hitemAllocationSmall |>.1)
      have htransferredSmallThree : ownSmallChoreSet cost (allocation 3 ∪ {item}) 3 =
          ownSmallChoreSet cost (allocation 3) 3 ∪ {item} := by
        ext chore
        simp only [ownSmallChoreSet, Finset.mem_filter, Finset.mem_union,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hmem | hchoreItem, hsmall⟩
          · exact Or.inl ⟨hmem, hsmall⟩
          · subst chore
            exact Or.inr rfl
        · rintro (⟨hmem, hsmall⟩ | hchoreItem)
          · exact ⟨Or.inl hmem, hsmall⟩
          · subst chore
            exact ⟨Or.inr rfl, hitemSmallThree⟩
      have hitemNotSmallThree : item ∉ ownSmallChoreSet cost (allocation 3) 3 := by
        intro hitemSmall
        exact hitemNotThree (Finset.mem_filter.mp hitemSmall |>.1)
      constructor
      · change (allocation 3 ∪ {item}).card = canonicalQuota a {3} 3
        rw [Finset.card_union_of_disjoint]
        · rw [hcanonical.2 3 |>.1, hquota3]
          simp [canonicalQuota]
        · rw [Finset.disjoint_singleton_right]
          exact hitemNotThree
      · change (ownSmallChoreSet cost (allocation 3 ∪ {item}) 3).card =
          min (canonicalQuota a {3} 3) (ownSmallChoreSet cost chores 3).card
        rw [htransferredSmallThree, Finset.card_union_of_disjoint]
        · rw [hcanonical.2 3 |>.2, hquota3,
            Nat.min_eq_left (Nat.le_of_succ_le hwholeSmallThree)]
          simp [canonicalQuota, Nat.min_eq_left hwholeSmallThree]
        · rw [Finset.disjoint_singleton_right]
          exact hitemNotSmallThree

/-- A chore that is small for agent `3` is large for agent `2` under the M01
condition and the normalized `1`/`r` cost alphabet. -/
theorem b1Disjoint_smallThree_largeTwo
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (item : Item) (hcost : IsOneOrRChoreCost cost r)
    (hitemAtMostOne : IsSmallForAtMostOne cost item)
    (hitemSmallThree : IsSmallChore cost 3 item) :
    IsLargeChore cost r 2 item := by
  rcases hcost 2 item with hitemSmallTwo | hitemLargeTwo
  · exfalso
    have hsmallTwo : 2 ∈ smallAgentSet cost item := by
      simpa [smallAgentSet, IsSmallChore] using hitemSmallTwo
    have hsmallThree : 3 ∈ smallAgentSet cost item := by
      simpa [smallAgentSet, IsSmallChore] using hitemSmallThree
    have hsubset : ({2, 3} : Finset (Fin 4)) ⊆ smallAgentSet cost item := by
      intro agent hagent
      simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
      rcases hagent with rfl | rfl
      · exact hsmallTwo
      · exact hsmallThree
    have hcard := Finset.card_le_card hsubset
    have hsmallCard := hitemAtMostOne
    change (smallAgentSet cost item).card ≤ 1 at hsmallCard
    have hpairCard : ({2, 3} : Finset (Fin 4)).card = 2 := by decide
    omega
  · exact hitemLargeTwo

/-- For a canonical prefix with agent `2` long and agent `3` short, either
agent `3` already has the required `r` advantage, or every item in the long
bundle is small for agent `3`.  The latter is exactly the source's trigger for
moving one long-bundle item and swapping the two endpoint labels. -/
theorem canonical_b1_disjoint_advantage_or_long_all_small
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (allocation : Allocation (Fin 4) Item)
    (hr : 1 ≤ r) (hcost : IsOneOrRChoreCost cost r)
    (hcanonical : IsCanonicalSmallChoreAllocation cost chores quota allocation)
    (hquotaShort : quota 3 = a) (hquotaLong : quota 2 = a + 1) :
    additiveChoreCost cost 3 (allocation 3) ≤
        additiveChoreCost cost 3 (allocation 2) - r ∨
      ∀ item ∈ allocation 2, IsSmallChore cost 3 item := by
  classical
  have hcardShort : (allocation 3).card = a := by
    rw [hcanonical.2 3 |>.1, hquotaShort]
  have hcardLong : (allocation 2).card = a + 1 := by
    rw [hcanonical.2 2 |>.1, hquotaLong]
  by_cases hsmallEnough : a ≤ (ownSmallChoreSet cost chores 3).card
  · have hcanonicalOwn : (ownSmallChoreSet cost (allocation 3) 3).card = a := by
      rw [hcanonical.2 3 |>.2, hquotaShort, Nat.min_eq_left hsmallEnough]
    have hownShortEq : ownSmallChoreSet cost (allocation 3) 3 = allocation 3 := by
      apply Finset.eq_of_subset_of_card_le
      · intro item hitem
        exact (Finset.mem_filter.mp hitem).1
      · rw [hcanonicalOwn, hcardShort]
    have hownShort : ∀ item ∈ allocation 3, IsSmallChore cost 3 item := by
      intro item hitem
      have hitemOwn : item ∈ ownSmallChoreSet cost (allocation 3) 3 := by
        rw [hownShortEq]
        exact hitem
      exact (Finset.mem_filter.mp hitemOwn).2
    by_cases hlargeExists : ∃ item ∈ allocation 2, IsLargeChore cost r 3 item
    · left
      obtain ⟨largeItem, hlargeItem, hlarge⟩ := hlargeExists
      have hshortCost : additiveChoreCost cost 3 (allocation 3) = a := by
        rw [additiveChoreCost_eq_card_nsmul_of_constant cost 3 (allocation 3) 1
          hownShort, hcardShort]
        norm_num [nsmul_eq_mul]
      have heraseCard : (allocation 2 \ {largeItem}).card = a := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hlargeItem, hcardLong]
        omega
      have heraseLower : (a : ℝ) ≤ additiveChoreCost cost 3 (allocation 2 \ {largeItem}) := by
        calc
          (a : ℝ) = (allocation 2 \ {largeItem}).card • (1 : ℝ) := by
            rw [heraseCard]
            norm_num [nsmul_eq_mul]
          _ ≤ additiveChoreCost cost 3 (allocation 2 \ {largeItem}) :=
            card_nsmul_le_additiveChoreCost_of_le cost 3 (allocation 2 \ {largeItem}) 1
              (fun item hitem => IsOneOrRChoreCost.one_le cost r hcost hr 3 item)
      have heraseCost : additiveChoreCost cost 3 (allocation 2 \ {largeItem}) =
          additiveChoreCost cost 3 (allocation 2) - r := by
        rw [additiveChoreCost_erase cost 3 (allocation 2) largeItem hlargeItem]
        simpa [IsLargeChore] using hlarge
      rw [hshortCost]
      linarith
    · right
      intro item hitem
      rcases hcost 3 item with hsmall | hlarge
      · exact hsmall
      · exact (hlargeExists ⟨item, hitem, hlarge⟩).elim
  · left
    have hsmallLess : (ownSmallChoreSet cost chores 3).card < a :=
      Nat.lt_of_not_ge hsmallEnough
    have hcanonicalOwn : (ownSmallChoreSet cost (allocation 3) 3).card =
        (ownSmallChoreSet cost chores 3).card := by
      rw [hcanonical.2 3 |>.2, hquotaShort, Nat.min_eq_right hsmallLess.le]
    have hallocationShort : allocation 3 ⊆ chores := by
      intro item hitem
      exact hcanonical.1.1 3 item hitem
    have hsmallEq : ownSmallChoreSet cost (allocation 3) 3 =
        ownSmallChoreSet cost chores 3 :=
      ownSmallChoreSet_eq_of_subset_and_card cost 3 hallocationShort hcanonicalOwn
    have hlongLarge : ∀ item ∈ allocation 2, IsLargeChore cost r 3 item := by
      intro item hitem
      rcases hcost 3 item with hsmall | hlarge
      · exfalso
        have hitemChores : item ∈ chores := hcanonical.1.1 2 item hitem
        have hitemOwn : item ∈ ownSmallChoreSet cost chores 3 := by
          exact Finset.mem_filter.mpr ⟨hitemChores, hsmall⟩
        have hitemShort : item ∈ allocation 3 := by
          have hitemOwnShort : item ∈ ownSmallChoreSet cost (allocation 3) 3 := by
            rw [hsmallEq]
            exact hitemOwn
          exact (Finset.mem_filter.mp hitemOwnShort).1
        exact (by decide : (2 : Fin 4) ≠ 3)
          (isAllocationOf_owner_unique hcanonical.1 hitemChores hitem hitemShort)
      · exact hlarge
    have hshortUpper : additiveChoreCost cost 3 (allocation 3) ≤ (a : ℝ) * r := by
      calc
        additiveChoreCost cost 3 (allocation 3) ≤ (allocation 3).card • r :=
          additiveChoreCost_le_card_nsmul_of_le cost 3 (allocation 3) r
            (fun item hitem => IsOneOrRChoreCost.le_r cost r hcost hr 3 item)
        _ = (a : ℝ) * r := by rw [hcardShort]; simp [nsmul_eq_mul]
    have hlongCost : additiveChoreCost cost 3 (allocation 2) = (a + 1 : ℕ) • r := by
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost 3 (allocation 2) r
        (fun item hitem => by simpa [IsLargeChore] using hlongLarge item hitem), hcardLong]
    calc
      additiveChoreCost cost 3 (allocation 3) ≤ (a : ℝ) * r := hshortUpper
      _ = (a + 1 : ℕ) • r - r := by
        ring
      _ = additiveChoreCost cost 3 (allocation 2) - r := by rw [hlongCost]

/-- Source Case B.2.1(b)'s canonical-prefix orientation.  A canonical prefix
with agent `2` initially long either has the required short-agent advantage,
or one item is moved from `2` to `3` and labels `2,3` are swapped.  In both
branches the returned labels retain agents `0,1` and put the long quota at
new label `2`, exactly as required by the disjoint-edge gap fill. -/
theorem existsCanonicalB1DisjointPrefix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores : Finset Item) (a : ℕ)
    (hr : 1 ≤ r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item) :
    ∃ labels : Fin 4 ≃ Fin 4, ∃ quota : Fin 4 → ℕ,
      ∃ prefixAllocation : Allocation (Fin 4) Item,
        (labels = Equiv.refl (Fin 4) ∨ labels = Equiv.swap 2 3) ∧
        IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost) prefixChores quota
          prefixAllocation ∧
        quota 0 = a ∧ quota 1 = a ∧ quota 2 = a + 1 ∧ quota 3 = a ∧
        additiveChoreCost (relabelChoreCost labels cost) 3 (prefixAllocation 3) ≤
          additiveChoreCost (relabelChoreCost labels cost) 3 (prefixAllocation 2) - r := by
  classical
  let initialQuota : Fin 4 → ℕ := canonicalQuota a {2}
  have hinitialQuotaSum : Finset.univ.sum initialQuota = prefixChores.card := by
    calc
      Finset.univ.sum initialQuota = 4 * a + ({2} : Finset (Fin 4)).card := by
        simpa [initialQuota] using canonicalQuota_sum a ({2} : Finset (Fin 4))
      _ = 4 * a + 1 := by simp
      _ = prefixChores.card := hprefixCard.symm
  obtain ⟨initialAllocation, hinitialCanonical⟩ :=
    existsCanonicalSmallChoreAllocation Item cost prefixChores initialQuota hinitialQuotaSum
      hprefixSmall
  have hinitialQuota0 : initialQuota 0 = a := by simp [initialQuota, canonicalQuota]
  have hinitialQuota1 : initialQuota 1 = a := by simp [initialQuota, canonicalQuota]
  have hinitialQuota2 : initialQuota 2 = a + 1 := by simp [initialQuota, canonicalQuota]
  have hinitialQuota3 : initialQuota 3 = a := by simp [initialQuota, canonicalQuota]
  rcases canonical_b1_disjoint_advantage_or_long_all_small Item r cost prefixChores a
      initialQuota initialAllocation hr hcost hinitialCanonical hinitialQuota3 hinitialQuota2 with
    hgap | hallSmall
  · refine ⟨Equiv.refl (Fin 4), initialQuota, initialAllocation, Or.inl rfl, ?_,
      hinitialQuota0, hinitialQuota1, hinitialQuota2, hinitialQuota3, ?_⟩
    · simpa [relabelChoreCost, relabelQuota, relabelAllocation] using hinitialCanonical
    · simpa [relabelChoreCost, relabelAllocation] using hgap
  · have hlongCard : (initialAllocation 2).card = a + 1 := by
      rw [hinitialCanonical.2 2 |>.1, hinitialQuota2]
    have hlongPos : 0 < (initialAllocation 2).card := by omega
    obtain ⟨item, hitem⟩ := Finset.card_pos.mp hlongPos
    have hitemPrefix : item ∈ prefixChores := hinitialCanonical.1.1 2 item hitem
    have hitemSmallThree : IsSmallChore cost 3 item := hallSmall item hitem
    have hitemAtMostOne : IsSmallForAtMostOne cost item := hprefixSmall item hitemPrefix
    have hmovedCanonical := canonical_b1DisjointTransferredAllocation Item cost prefixChores a
      initialQuota initialAllocation item hinitialCanonical hitemAtMostOne hinitialQuota0
      hinitialQuota1 hinitialQuota2 hinitialQuota3 hitem hitemSmallThree
    have hprefixEfx : EFXForChores (additiveChoreCost cost) initialAllocation :=
      hinitialCanonical.efxForChores cost r prefixChores initialQuota initialAllocation hcost hr
        (by
          intro first second
          fin_cases first <;> fin_cases second <;>
            simp [initialQuota, canonicalQuota] <;> omega)
    have hremove : additiveChoreCost cost 2 (initialAllocation 2 \ {item}) ≤
        additiveChoreCost cost 2 (initialAllocation 3) := by
      rcases hprefixEfx 2 3 with hempty | hremove
      · rw [hempty] at hitem
        simp at hitem
      · exact hremove item hitem
    have hitemLargeTwo : IsLargeChore cost r 2 item :=
      b1Disjoint_smallThree_largeTwo Item r cost item hcost hitemAtMostOne hitemSmallThree
    have hitemNotThree : item ∉ initialAllocation 3 := by
      intro hitemThree
      exact (by decide : (2 : Fin 4) ≠ 3)
        (isAllocationOf_owner_unique hinitialCanonical.1 hitemPrefix hitem hitemThree)
    have hrightCost : additiveChoreCost cost 2 (initialAllocation 3 ∪ {item}) =
        additiveChoreCost cost 2 (initialAllocation 3) + r := by
      have hitemCostTwo : cost 2 item = r := by
        simpa [IsLargeChore] using hitemLargeTwo
      rw [additiveChoreCost_union cost 2 (initialAllocation 3) {item}]
      · simp [additiveChoreCost, hitemCostTwo]
      · rw [Finset.disjoint_singleton_right]
        exact hitemNotThree
    have hmovedGap : additiveChoreCost cost 2 (initialAllocation 2 \ {item}) ≤
        additiveChoreCost cost 2 (initialAllocation 3 ∪ {item}) - r := by
      rw [hrightCost]
      linarith
    let labels : Fin 4 ≃ Fin 4 := Equiv.swap 2 3
    let movedQuota : Fin 4 → ℕ := canonicalQuota a {3}
    let movedAllocation : Allocation (Fin 4) Item :=
      b1DisjointTransferredAllocation initialAllocation item
    refine ⟨labels, relabelQuota labels movedQuota, relabelAllocation labels movedAllocation,
      Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [labels, movedQuota, movedAllocation] using
        hmovedCanonical.relabel labels cost prefixChores movedQuota movedAllocation
    · simp [labels, movedQuota, relabelQuota, canonicalQuota, Equiv.swap_apply_def]
    · simp [labels, movedQuota, relabelQuota, canonicalQuota, Equiv.swap_apply_def]
    · simp [labels, movedQuota, relabelQuota, canonicalQuota]
    · simp [labels, movedQuota, relabelQuota, canonicalQuota]
    · simpa [labels, movedAllocation, b1DisjointTransferredAllocation,
        relabelChoreCost, relabelAllocation, Equiv.swap_apply_def] using hmovedGap

end HT26EFXChores
