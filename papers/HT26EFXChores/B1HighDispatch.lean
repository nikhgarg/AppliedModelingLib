import HT26EFXChores.B1DisjointDispatch
import HT26EFXChores.B1Dispatch
import HT26EFXChores.M34Extension

/-!
# M34-level bridges for high-multiplicity source Case B.2.1

The two fixed-label graph leaves are closed before this module.  Here their
base EFX allocations are lifted through the final M34 insertion stage.

Source: EFXadditivechores.tex, lines 2241--2470.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- The complete fixed-label B.2.1(a) intersecting branch extended across
the M34 pool. -/
theorem existsEfxOfM01M2M34_b1IntersectingMaximum
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ)
    (first second third : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixM34 : Disjoint prefixChores m34Chores)
    (hm2M34 : Disjoint m2Chores m34Chores)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hm34Small : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨baseAllocation, hbaseAllocation, hbaseEFX⟩ :=
    existsEfxOfB1IntersectingMaximum_dispatch Item r cost prefixChores m2Chores a
      first second third hr hcost hprefixCard hprefixSmall hprefixM2 hfirst hsecond hthird
      hfirstNeSecond hm2Small hmaximum
  have hbaseM34 : Disjoint (prefixChores ∪ m2Chores) m34Chores := by
    rw [Finset.disjoint_left]
    intro item hbase hm34
    rcases Finset.mem_union.mp hbase with hprefix | hm2
    · exact (Finset.disjoint_left.mp hprefixM34 hprefix hm34).elim
    · exact (Finset.disjoint_left.mp hm2M34 hm2 hm34).elim
  exact extendEfxByM34 Item r cost (prefixChores ∪ m2Chores) m34Chores hr hcost
    hbaseM34 hm34Small baseAllocation hbaseAllocation hbaseEFX

/-- The B.2.1(a) branch transported across a relabelling that keeps the
maximum type displayed as (0,1) and sends the chosen intersecting type to
(1,2). -/
theorem existsEfxOfM01M2M34_b1IntersectingMaximum_of_relabelled_types
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores m34Chores : Finset Item)
    (a : ℕ) (first second third : Item)
    (intersectingType : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixM34 : Disjoint prefixChores m34Chores)
    (hm2M34 : Disjoint m2Chores m34Chores)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hm34Small : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores intersectingType)
    (hfirstNeSecond : first ≠ second)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hlabels01 : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = {0, 1})
    (hlabels12 : ({1, 2} : Finset (Fin 4)).map labels.toEmbedding = intersectingType) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost ((prefixChores ∪ m2Chores) ∪ m34Chores)
  apply existsEfxOfM01M2M34_b1IntersectingMaximum Item r (relabelChoreCost labels cost)
    prefixChores m2Chores m34Chores a first second third
  · exact hr
  · exact IsOneOrRChoreCost.relabel labels cost r hcost
  · exact hprefixM2
  · exact hprefixM34
  · exact hm2M34
  · exact hprefixCard
  · intro item hitem
    exact IsSmallForAtMostOne.relabel labels cost item (hprefixSmall item hitem)
  · intro item hitem
    exact IsSmallForExactlyTwo.relabel labels cost item (hm2Small item hitem)
  · intro item hitem
    rw [IsSmallForAtLeastThree, smallAgentSet_relabel]
    simpa [IsSmallForAtLeastThree] using hm34Small item hitem
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hlabels01]
    exact hfirst
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hlabels01]
    exact hsecond
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({1, 2} : Finset (Fin 4)), hlabels12]
    exact hthird
  · exact hfirstNeSecond
  · intro edgeType
    rw [m2TypeChorePool_relabel labels cost m2Chores edgeType,
      m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)),
      hlabels01]
    exact hmaximum (edgeType.map labels.toEmbedding)

/-- Complete high-multiplicity b=1 dispatch after the maximum M2 type has
been displayed as (0,1).  A nonempty intersecting fibre is sent to (1,2) by
a finite relabelling; if all four intersecting fibres are empty, every M2
chore is in the complementary (2,3) fibre and the disjoint dispatcher applies. -/
theorem existsEfxOfM01M2M34_b1HighMaximum
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixM34 : Disjoint prefixChores m34Chores)
    (hm2M34 : Disjoint m2Chores m34Chores)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hm34Small : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hmaximumCard : 3 ≤
      (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let maximumPool := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  obtain ⟨gap, hgapSub, hgapCard⟩ := maximumPool.exists_subset_card_eq
    (by simpa [maximumPool] using hmaximumCard)
  obtain ⟨first, second, third, hfirstNeSecond, hfirstNeThird, hsecondNeThird,
      hgapEq⟩ := Finset.card_eq_three.mp hgapCard
  have hfirst : first ∈ maximumPool := hgapSub (by rw [hgapEq]; simp)
  have hsecond : second ∈ maximumPool := hgapSub (by rw [hgapEq]; simp)
  have hthird : third ∈ maximumPool := hgapSub (by rw [hgapEq]; simp)
  have hfirst' : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) := by
    simpa [maximumPool] using hfirst
  have hsecond' : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) := by
    simpa [maximumPool] using hsecond
  have hthird' : third ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) := by
    simpa [maximumPool] using hthird
  by_cases h12 : (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).Nonempty
  · obtain ⟨cross, hcross⟩ := h12
    exact existsEfxOfM01M2M34_b1IntersectingMaximum_of_relabelled_types Item r cost
      (Equiv.refl (Fin 4)) prefixChores m2Chores m34Chores a first second cross
      ({1, 2} : Finset (Fin 4)) hr hcost hprefixM2 hprefixM34 hm2M34 hprefixCard
      hprefixSmall hm2Small hm34Small hfirst' hsecond' hcross hfirstNeSecond hmaximum
      (by decide) (by decide)
  · by_cases h02 : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).Nonempty
    · obtain ⟨cross, hcross⟩ := h02
      let labels : Fin 4 ≃ Fin 4 := Equiv.swap 0 1
      exact existsEfxOfM01M2M34_b1IntersectingMaximum_of_relabelled_types Item r cost
        labels prefixChores m2Chores m34Chores a first second cross
        ({0, 2} : Finset (Fin 4)) hr hcost hprefixM2 hprefixM34 hm2M34 hprefixCard
        hprefixSmall hm2Small hm34Small hfirst' hsecond' hcross hfirstNeSecond hmaximum
        (by decide) (by decide)
    · by_cases h13 : (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).Nonempty
      · obtain ⟨cross, hcross⟩ := h13
        let labels : Fin 4 ≃ Fin 4 := Equiv.swap 2 3
        exact existsEfxOfM01M2M34_b1IntersectingMaximum_of_relabelled_types Item r cost
          labels prefixChores m2Chores m34Chores a first second cross
          ({1, 3} : Finset (Fin 4)) hr hcost hprefixM2 hprefixM34 hm2M34 hprefixCard
          hprefixSmall hm2Small hm34Small hfirst' hsecond' hcross hfirstNeSecond hmaximum
          (by decide) (by decide)
      · by_cases h03 : (m2TypeChorePool cost m2Chores
          ({0, 3} : Finset (Fin 4))).Nonempty
        · obtain ⟨cross, hcross⟩ := h03
          let labels : Fin 4 ≃ Fin 4 := (Equiv.swap 0 1).trans (Equiv.swap 2 3)
          exact existsEfxOfM01M2M34_b1IntersectingMaximum_of_relabelled_types Item r cost
            labels prefixChores m2Chores m34Chores a first second cross
            ({0, 3} : Finset (Fin 4)) hr hcost hprefixM2 hprefixM34 hm2M34 hprefixCard
            hprefixSmall hm2Small hm34Small hfirst' hsecond' hcross hfirstNeSecond hmaximum
            (by decide) (by decide)
        · have hcover : m2Chores =
            m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
              m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) := by
            apply Finset.Subset.antisymm
            · intro item hitem
              rcases finset_fin4_card_two_eq_one_of_six (smallAgentSet cost item)
                  (hm2Small item hitem) with h01 | h02' | h03' | h12' | h13' | h23
              · exact Finset.mem_union_left _
                  ((mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mpr
                    ⟨hitem, h01⟩)
              · exact (h02 ⟨item,
                  (mem_m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) item).mpr
                    ⟨hitem, h02'⟩⟩).elim
              · exact (h03 ⟨item,
                  (mem_m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)) item).mpr
                    ⟨hitem, h03'⟩⟩).elim
              · exact (h12 ⟨item,
                  (mem_m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) item).mpr
                    ⟨hitem, h12'⟩⟩).elim
              · exact (h13 ⟨item,
                  (mem_m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) item).mpr
                    ⟨hitem, h13'⟩⟩).elim
              · exact Finset.mem_union_right _
                  ((mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mpr
                    ⟨hitem, h23⟩)
            · intro item hitem
              rcases Finset.mem_union.mp hitem with h01 | h23
              · exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp
                  h01 |>.1
              · exact (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mp
                  h23 |>.1
          exact existsEfxOfM01M2M34_b1DisjointMaximum Item r cost prefixChores m2Chores
            m34Chores a first second third hr hcost hprefixM2 hprefixM34 hm2M34 hprefixCard
            hprefixSmall hm2Small hm34Small hcover
            (hmaximum ({2, 3} : Finset (Fin 4))) hfirst' hsecond' hthird' hfirstNeSecond
            hfirstNeThird hsecondNeThird

/-- The complete high-multiplicity b=1 dispatcher transported across a
relabelling that sends the displayed type (0,1) to the selected maximum
source fibre. -/
theorem existsEfxOfM01M2M34_b1HighMaximum_of_relabelled_maximum
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores m34Chores : Finset Item)
    (a : ℕ) (maximumType : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixM34 : Disjoint prefixChores m34Chores)
    (hm2M34 : Disjoint m2Chores m34Chores)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hm34Small : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores maximumType).card)
    (hmaximumCard : 3 ≤ (m2TypeChorePool cost m2Chores maximumType).card)
    (hlabels : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = maximumType) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost ((prefixChores ∪ m2Chores) ∪ m34Chores)
  apply existsEfxOfM01M2M34_b1HighMaximum Item r (relabelChoreCost labels cost)
    prefixChores m2Chores m34Chores a
  · exact hr
  · exact IsOneOrRChoreCost.relabel labels cost r hcost
  · exact hprefixM2
  · exact hprefixM34
  · exact hm2M34
  · exact hprefixCard
  · intro item hitem
    exact IsSmallForAtMostOne.relabel labels cost item (hprefixSmall item hitem)
  · intro item hitem
    exact IsSmallForExactlyTwo.relabel labels cost item (hm2Small item hitem)
  · intro item hitem
    rw [IsSmallForAtLeastThree, smallAgentSet_relabel]
    simpa [IsSmallForAtLeastThree] using hm34Small item hitem
  · intro edgeType
    rw [m2TypeChorePool_relabel labels cost m2Chores edgeType,
      m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hlabels]
    exact hmaximum (edgeType.map labels.toEmbedding)
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hlabels]
    exact hmaximumCard

/-- Every two-element fibre can be displayed as the source's maximum
type (0,1) by a finite relabelling. -/
theorem exists_b1_type_relabelling
    (edgeType : Finset (Fin 4)) (hcard : edgeType.card = 2) :
    ∃ labels : Fin 4 ≃ Fin 4,
      ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = edgeType := by
  rcases finset_fin4_card_two_eq_one_of_six edgeType hcard with h01 | h02 | h03 | h12 | h13 | h23
  · subst edgeType
    exact ⟨Equiv.refl (Fin 4), by decide⟩
  · subst edgeType
    exact ⟨Equiv.swap 1 2, by decide⟩
  · subst edgeType
    exact ⟨Equiv.swap 1 3, by decide⟩
  · subst edgeType
    exact ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1), by decide⟩
  · subst edgeType
    exact ⟨(Equiv.swap 1 3).trans (Equiv.swap 0 1), by decide⟩
  · subst edgeType
    exact ⟨(Equiv.swap 0 2).trans (Equiv.swap 1 3), by decide⟩

/-- Complete normalized b=1 source case.  A maximum M2 fibre of multiplicity
at most two uses the low-multiplicity dispatcher; otherwise it is relabelled
to (0,1) and the high-multiplicity graph dispatcher applies. -/
theorem existsEfxOfM01M2M34_b1
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixM34 : Disjoint prefixChores m34Chores)
    (hm2M34 : Disjoint m2Chores m34Chores)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hm34Small : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let edgeTypes : Finset (Finset (Fin 4)) :=
    (Finset.univ : Finset (Finset (Fin 4))).filter fun edgeType => edgeType.card = 2
  have hedgeTypesNonempty : edgeTypes.Nonempty := by
    refine ⟨({0, 1} : Finset (Fin 4)), ?_⟩
    simp [edgeTypes]
  obtain ⟨maximumType, hmaximumMem, hmaximum⟩ := Finset.exists_max_image edgeTypes
    (fun edgeType => (m2TypeChorePool cost m2Chores edgeType).card) hedgeTypesNonempty
  have hmaximumTypeCard : maximumType.card = 2 := by
    simpa [edgeTypes] using hmaximumMem
  have hnonPairEmpty : ∀ edgeType : Finset (Fin 4), edgeType.card ≠ 2 →
      m2TypeChorePool cost m2Chores edgeType = ∅ := by
    intro edgeType hcard
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    obtain ⟨item, hitem⟩ := hnonempty
    obtain ⟨hm2, htype⟩ := (mem_m2TypeChorePool cost m2Chores edgeType item).mp hitem
    have hsmall : (smallAgentSet cost item).card = 2 := hm2Small item hm2
    exact hcard (by rw [← htype]; exact hsmall)
  have hmaximumAll : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores maximumType).card := by
    intro edgeType
    by_cases hcard : edgeType.card = 2
    · exact hmaximum edgeType (by simpa [edgeTypes] using hcard)
    · rw [hnonPairEmpty edgeType hcard]
      exact Nat.zero_le _
  by_cases hmaximumSmall :
      (m2TypeChorePool cost m2Chores maximumType).card ≤ 2
  · apply existsEfxOfM01M2M34_b1Low Item r cost prefixChores m2Chores m34Chores a
      hr hcost hprefixM2 hprefixM34 hm2M34 hprefixCard hprefixSmall hm2Small hm34Small
    intro edgeType
    exact (hmaximumAll edgeType).trans hmaximumSmall
  · have hmaximumCard : 3 ≤ (m2TypeChorePool cost m2Chores maximumType).card := by
      omega
    obtain ⟨labels, hlabels⟩ := exists_b1_type_relabelling maximumType hmaximumTypeCard
    exact existsEfxOfM01M2M34_b1HighMaximum_of_relabelled_maximum Item r cost labels
      prefixChores m2Chores m34Chores a maximumType hr hcost hprefixM2 hprefixM34 hm2M34
      hprefixCard hprefixSmall hm2Small hm34Small hmaximumAll hmaximumCard hlabels

/-- Every normalized instance whose M01 pool has remainder one admits an EFX
allocation.  This joins the complete low- and high-multiplicity b=1
dispatches and restores the M34 pool. -/
theorem existsEfxOfOneOrR_b1
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcard : (m01ChorePool cost chores).card = 4 * a + 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨allocation, hallocation, hefx⟩ :=
    existsEfxOfM01M2M34_b1 Item r cost (m01ChorePool cost chores)
      (m2ChorePool cost chores) (m34ChorePool cost chores) a hr hcost
      (m01ChorePool_disjoint_m2ChorePool cost chores)
      (m01ChorePool_disjoint_m34ChorePool cost chores)
      (m2ChorePool_disjoint_m34ChorePool cost chores) hcard
      (m01ChorePool_small cost chores) (m2ChorePool_small cost chores)
      (m34ChorePool_small cost chores)
  refine ⟨allocation, ?_, hefx⟩
  simpa only [← Finset.union_assoc, m01_m2_m34_union_eq] using hallocation

end HT26EFXChores
