import HT26EFXChores.B1FourCycleAllocation
import HT26EFXChores.FourEdgeProfile

/-!
# Four-edge type-pool dispatch for source Case B.2.2(b)

This file turns the numerical four-vertex multigraph classification into the
finite M₂ type-pool covers required by the two direct EFX schedules.

Source: `EFXadditivechores.tex`, lines 2526--2542.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- The six unordered two-agent fibres partition an M₂ pool when every chore
is small for exactly two agents. -/
theorem m2_eq_union_of_six_type_pools_of_smallExactlyTwo
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item)
    (hsmall : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item) :
    m2Chores = (((((m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
      m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))) ∪
      m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))) ∪
      m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))) ∪
      m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))) ∪
      m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))) := by
  classical
  apply Finset.Subset.antisymm
  · intro item hitem
    have hitemCard : (smallAgentSet cost item).card = 2 := by
      simpa [IsSmallForExactlyTwo] using hsmall item hitem
    obtain ⟨first, second, hdistinct, htype⟩ := Finset.card_eq_two.mp hitemCard
    fin_cases first <;> fin_cases second <;>
      simp_all [m2TypeChorePool] <;> decide
  · intro item hitem
    rcases Finset.mem_union.mp hitem with h01234 | h23
    · rcases Finset.mem_union.mp h01234 with h0123 | h13
      · rcases Finset.mem_union.mp h0123 with h012 | h12
        · rcases Finset.mem_union.mp h012 with h01 | h03
          · rcases Finset.mem_union.mp h01 with h01 | h02
            · exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp h01 |>.1
            · exact (mem_m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) item).mp h02 |>.1
          · exact (mem_m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)) item).mp h03 |>.1
        · exact (mem_m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) item).mp h12 |>.1
      · exact (mem_m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) item).mp h13 |>.1
    · exact (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mp h23 |>.1

/-- The six M₂ type-fibre cardinalities sum to the M₂-pool cardinality. -/
theorem m2_type_card_sum_of_smallExactlyTwo
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item)
    (hsmall : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item) :
    (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = m2Chores.card := by
  classical
  have hcover := m2_eq_union_of_six_type_pools_of_smallExactlyTwo Item cost m2Chores hsmall
  have h01_02 : Disjoint (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
      (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))) :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide)
  have h012_03 : Disjoint
      (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)))
      (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))) := by
    rw [Finset.disjoint_union_left]
    exact ⟨m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide),
      m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide)⟩
  have h0123_12 : Disjoint
      ((m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))) ∪
        m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)))
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
    exact ⟨⟨m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide),
      m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide)⟩,
      m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide)⟩
  have h01234_13 : Disjoint
      (((m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))) ∪
        m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))) ∪
        m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left, Finset.disjoint_union_left]
    exact ⟨⟨⟨m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide),
      m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide)⟩,
      m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide)⟩,
      m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide)⟩
  have h012345_23 : Disjoint
      ((((m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))) ∪
        m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))) ∪
        m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))) ∪
        m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)))
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left, Finset.disjoint_union_left,
      Finset.disjoint_union_left]
    exact ⟨⟨⟨⟨m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide),
      m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide)⟩,
      m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide)⟩,
      m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide)⟩,
      m2TypeChorePool_disjoint_of_ne cost m2Chores _ _ (by decide)⟩
  have hunionCard :
      (((((m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))) ∪
        m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))) ∪
        m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))) ∪
        m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))) ∪
        m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card =
      (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card := by
    rw [Finset.card_union_of_disjoint h012345_23,
      Finset.card_union_of_disjoint h01234_13,
      Finset.card_union_of_disjoint h0123_12,
      Finset.card_union_of_disjoint h012_03,
      Finset.card_union_of_disjoint h01_02]
  exact hunionCard.symm.trans (congrArg Finset.card hcover).symm

/-- Three pairwise distinct edge fibres whose endpoints exclude `agent` are
all large for that agent.  Their combined cardinality is therefore bounded by
the number of M₂ chores large for that agent. -/
theorem m2_nonincident_type_card_le_large_card
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (agent : Fin 4)
    (type1 type2 type3 : Finset (Fin 4))
    (h12 : type1 ≠ type2) (h13 : type1 ≠ type3) (h23 : type2 ≠ type3)
    (h1 : agent ∉ type1) (h2 : agent ∉ type2) (h3 : agent ∉ type3)
    (hcost : IsOneOrRChoreCost cost r) :
    (m2TypeChorePool cost m2Chores type1).card +
      (m2TypeChorePool cost m2Chores type2).card +
      (m2TypeChorePool cost m2Chores type3).card ≤
      (largeChoreSet cost r agent m2Chores).card := by
  classical
  let pool1 := m2TypeChorePool cost m2Chores type1
  let pool2 := m2TypeChorePool cost m2Chores type2
  let pool3 := m2TypeChorePool cost m2Chores type3
  let large := largeChoreSet cost r agent m2Chores
  have h12Disjoint : Disjoint pool1 pool2 :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores type1 type2 h12
  have h123Disjoint : Disjoint (pool1 ∪ pool2) pool3 := by
    rw [Finset.disjoint_union_left]
    exact ⟨m2TypeChorePool_disjoint_of_ne cost m2Chores type1 type3 h13,
      m2TypeChorePool_disjoint_of_ne cost m2Chores type2 type3 h23⟩
  have hsubset : (pool1 ∪ pool2) ∪ pool3 ⊆ large := by
    intro item hitem
    change item ∈ largeChoreSet cost r agent m2Chores
    simp only [largeChoreSet, Finset.mem_filter]
    rcases Finset.mem_union.mp hitem with h12mem | h3mem
    · rcases Finset.mem_union.mp h12mem with h1mem | h2mem
      · exact ⟨(mem_m2TypeChorePool cost m2Chores type1 item).mp h1mem |>.1,
          m2TypeChorePool_large_for_nonendpoint r cost m2Chores type1 item agent hcost h1mem h1⟩
      · exact ⟨(mem_m2TypeChorePool cost m2Chores type2 item).mp h2mem |>.1,
          m2TypeChorePool_large_for_nonendpoint r cost m2Chores type2 item agent hcost h2mem h2⟩
    · exact ⟨(mem_m2TypeChorePool cost m2Chores type3 item).mp h3mem |>.1,
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores type3 item agent hcost h3mem h3⟩
  have hcardLe := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint h123Disjoint,
    Finset.card_union_of_disjoint h12Disjoint] at hcardLe
  simpa [pool1, pool2, pool3, large, Nat.add_assoc] using hcardLe

/-- If each agent finds at most two M₂ chores large, then the M₂ pool has at
most four chores.  Each chore is counted twice across the four complementary
three-fibre bounds, once for each of its two large agents. -/
theorem m2_card_le_four_of_no_three_large
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (hcost : IsOneOrRChoreCost cost r)
    (hsmall : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hlarge : ∀ agent : Fin 4, (largeChoreSet cost r agent m2Chores).card ≤ 2) :
    m2Chores.card ≤ 4 := by
  have hsum := m2_type_card_sum_of_smallExactlyTwo Item cost m2Chores hsmall
  have hlarge0 :
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card ≤ 2 := by
    calc
      _ ≤ (largeChoreSet cost r 0 m2Chores).card :=
        m2_nonincident_type_card_le_large_card Item r cost m2Chores 0
          ({1, 2} : Finset (Fin 4)) ({1, 3} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4))
          (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) hcost
      _ ≤ 2 := hlarge 0
  have hlarge1 :
      (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card ≤ 2 := by
    calc
      _ ≤ (largeChoreSet cost r 1 m2Chores).card :=
        m2_nonincident_type_card_le_large_card Item r cost m2Chores 1
          ({0, 2} : Finset (Fin 4)) ({0, 3} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4))
          (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) hcost
      _ ≤ 2 := hlarge 1
  have hlarge2 :
      (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card ≤ 2 := by
    calc
      _ ≤ (largeChoreSet cost r 2 m2Chores).card :=
        m2_nonincident_type_card_le_large_card Item r cost m2Chores 2
          ({0, 1} : Finset (Fin 4)) ({0, 3} : Finset (Fin 4)) ({1, 3} : Finset (Fin 4))
          (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) hcost
      _ ≤ 2 := hlarge 2
  have hlarge3 :
      (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card ≤ 2 := by
    calc
      _ ≤ (largeChoreSet cost r 3 m2Chores).card :=
        m2_nonincident_type_card_le_large_card Item r cost m2Chores 3
          ({0, 1} : Finset (Fin 4)) ({0, 2} : Finset (Fin 4)) ({1, 2} : Finset (Fin 4))
          (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) hcost
      _ ≤ 2 := hlarge 3
  omega

/-- In the source's four-chore subcase, every agent has at most two M₂ chores
that are large for her.  Since every M₂ chore has exactly two small endpoints,
the six edge multiplicities are consequently two-regular. -/
theorem m2_four_edge_degrees_of_no_three_large
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (hcost : IsOneOrRChoreCost cost r)
    (hm2Card : m2Chores.card = 4)
    (hsmall : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hlarge : ∀ agent : Fin 4, (largeChoreSet cost r agent m2Chores).card ≤ 2) :
    ((m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card = 2) ∧
    ((m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card = 2) ∧
    ((m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 2) ∧
    ((m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 2) := by
  have hsum := m2_type_card_sum_of_smallExactlyTwo Item cost m2Chores hsmall
  rw [hm2Card] at hsum
  have hlarge0 :
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card ≤ 2 := by
    calc
      _ ≤ (largeChoreSet cost r 0 m2Chores).card :=
        m2_nonincident_type_card_le_large_card Item r cost m2Chores 0
          ({1, 2} : Finset (Fin 4)) ({1, 3} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4))
          (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) hcost
      _ ≤ 2 := hlarge 0
  have hlarge1 :
      (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card ≤ 2 := by
    calc
      _ ≤ (largeChoreSet cost r 1 m2Chores).card :=
        m2_nonincident_type_card_le_large_card Item r cost m2Chores 1
          ({0, 2} : Finset (Fin 4)) ({0, 3} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4))
          (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) hcost
      _ ≤ 2 := hlarge 1
  have hlarge2 :
      (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card ≤ 2 := by
    calc
      _ ≤ (largeChoreSet cost r 2 m2Chores).card :=
        m2_nonincident_type_card_le_large_card Item r cost m2Chores 2
          ({0, 1} : Finset (Fin 4)) ({0, 3} : Finset (Fin 4)) ({1, 3} : Finset (Fin 4))
          (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) hcost
      _ ≤ 2 := hlarge 2
  have hlarge3 :
      (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card +
        (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card ≤ 2 := by
    calc
      _ ≤ (largeChoreSet cost r 3 m2Chores).card :=
        m2_nonincident_type_card_le_large_card Item r cost m2Chores 3
          ({0, 1} : Finset (Fin 4)) ({0, 2} : Finset (Fin 4)) ({1, 2} : Finset (Fin 4))
          (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) hcost
      _ ≤ 2 := hlarge 3
  constructor <;> omega

/-- Two distinct M₂ edge fibres of cardinality two cover a four-chore M₂
pool.  This is the type-pool bridge for a doubled disjoint-edge profile. -/
theorem m2_eq_union_of_two_type_pools_of_card_two
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (firstType secondType : Finset (Fin 4))
    (hfirstSecond : firstType ≠ secondType)
    (hm2Card : m2Chores.card = 4)
    (hfirstCard : (m2TypeChorePool cost m2Chores firstType).card = 2)
    (hsecondCard : (m2TypeChorePool cost m2Chores secondType).card = 2) :
    m2Chores = m2TypeChorePool cost m2Chores firstType ∪
      m2TypeChorePool cost m2Chores secondType := by
  classical
  let firstPool := m2TypeChorePool cost m2Chores firstType
  let secondPool := m2TypeChorePool cost m2Chores secondType
  have hsubset : firstPool ∪ secondPool ⊆ m2Chores := by
    intro item hitem
    rcases Finset.mem_union.mp hitem with hfirst | hsecond
    · exact (mem_m2TypeChorePool cost m2Chores firstType item).mp hfirst |>.1
    · exact (mem_m2TypeChorePool cost m2Chores secondType item).mp hsecond |>.1
  have hdisjoint : Disjoint firstPool secondPool :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores firstType secondType hfirstSecond
  have hunionCard : (firstPool ∪ secondPool).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisjoint]
    simp only [firstPool, secondPool]
    omega
  exact (Finset.eq_of_subset_of_card_le hsubset (by rw [hm2Card, hunionCard])).symm

/-- Four pairwise distinct M₂ edge fibres of cardinality one cover a
four-chore M₂ pool.  This is the type-pool bridge for a four-cycle profile. -/
theorem m2_eq_union_of_four_type_pools_of_card_one
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (type1 type2 type3 type4 : Finset (Fin 4))
    (h12 : type1 ≠ type2) (h13 : type1 ≠ type3) (h14 : type1 ≠ type4)
    (h23 : type2 ≠ type3) (h24 : type2 ≠ type4) (h34 : type3 ≠ type4)
    (hm2Card : m2Chores.card = 4)
    (h1Card : (m2TypeChorePool cost m2Chores type1).card = 1)
    (h2Card : (m2TypeChorePool cost m2Chores type2).card = 1)
    (h3Card : (m2TypeChorePool cost m2Chores type3).card = 1)
    (h4Card : (m2TypeChorePool cost m2Chores type4).card = 1) :
    m2Chores = ((m2TypeChorePool cost m2Chores type1 ∪
      m2TypeChorePool cost m2Chores type2) ∪
      m2TypeChorePool cost m2Chores type3) ∪
      m2TypeChorePool cost m2Chores type4 := by
  classical
  let pool1 := m2TypeChorePool cost m2Chores type1
  let pool2 := m2TypeChorePool cost m2Chores type2
  let pool3 := m2TypeChorePool cost m2Chores type3
  let pool4 := m2TypeChorePool cost m2Chores type4
  have hsubset : ((pool1 ∪ pool2) ∪ pool3) ∪ pool4 ⊆ m2Chores := by
    intro item hitem
    rcases Finset.mem_union.mp hitem with h123 | h4
    · rcases Finset.mem_union.mp h123 with h12' | h3'
      · rcases Finset.mem_union.mp h12' with h1' | h2'
        · exact (mem_m2TypeChorePool cost m2Chores type1 item).mp h1' |>.1
        · exact (mem_m2TypeChorePool cost m2Chores type2 item).mp h2' |>.1
      · exact (mem_m2TypeChorePool cost m2Chores type3 item).mp h3' |>.1
    · exact (mem_m2TypeChorePool cost m2Chores type4 item).mp h4 |>.1
  have h12Disjoint : Disjoint pool1 pool2 :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores type1 type2 h12
  have h123Disjoint : Disjoint (pool1 ∪ pool2) pool3 := by
    rw [Finset.disjoint_union_left]
    exact ⟨m2TypeChorePool_disjoint_of_ne cost m2Chores type1 type3 h13,
      m2TypeChorePool_disjoint_of_ne cost m2Chores type2 type3 h23⟩
  have h1234Disjoint : Disjoint ((pool1 ∪ pool2) ∪ pool3) pool4 := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
    exact ⟨⟨m2TypeChorePool_disjoint_of_ne cost m2Chores type1 type4 h14,
      m2TypeChorePool_disjoint_of_ne cost m2Chores type2 type4 h24⟩,
      m2TypeChorePool_disjoint_of_ne cost m2Chores type3 type4 h34⟩
  have hunionCard : (((pool1 ∪ pool2) ∪ pool3) ∪ pool4).card = 4 := by
    rw [Finset.card_union_of_disjoint h1234Disjoint,
      Finset.card_union_of_disjoint h123Disjoint,
      Finset.card_union_of_disjoint h12Disjoint]
    simp only [pool1, pool2, pool3, pool4]
    omega
  exact (Finset.eq_of_subset_of_card_le hsubset (by rw [hm2Card, hunionCard])).symm

/-- The four labelled source degrees translate directly to the six edge-fibre
multiplicities.  The resulting disjunction is the exact doubled-matching or
four-cycle classification, before a label symmetry chooses the displayed
source configuration. -/
theorem m2_four_edge_type_profile_classification
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item)
    (h0 : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card = 2)
    (h1 : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card = 2)
    (h2 : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 2)
    (h3 : (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card +
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 2) :
    ((m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card = 2 ∧
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 2) ∨
    ((m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card = 2 ∧
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card = 2) ∨
    ((m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card = 2 ∧
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card = 2) ∨
    ((m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card = 1 ∧
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card = 1 ∧
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 1 ∧
      (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card = 1) ∨
    ((m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card = 1 ∧
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card = 1 ∧
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 1 ∧
      (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card = 1) ∨
    ((m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).card = 1 ∧
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card = 1 ∧
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card = 1 ∧
      (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card = 1) := by
  exact four_edge_profile_classification _ _ _ _ _ _ h0 h1 h2 h3

/-- The doubled-edge B.2.2(b) schedule follows directly from the two
nonempty type-pool cardinalities; no separate cover certificate is needed. -/
theorem existsEfxOfB1LowMultiplicity_doubleDisjoint_longZero_of_typePoolCards
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 0) - r)
    (hm2Card : m2Chores.card = 4)
    (h01Card : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card = 2)
    (h23Card : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 2) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let u := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let w := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  have hcover : m2Chores = u ∪ w := by
    exact m2_eq_union_of_two_type_pools_of_card_two Item cost m2Chores
      ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)
      hm2Card h01Card h23Card
  have hwNonempty : w.Nonempty := by
    apply Finset.card_pos.mp
    rw [show w = m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) by rfl, h23Card]
    norm_num
  obtain ⟨head, hhead⟩ := hwNonempty
  apply existsEfxOfB1LowMultiplicity_doubleDisjoint_longZero_of_typePools Item r cost
    prefixChores m2Chores u w head a quota prefixAllocation hr hcost hprefixM2 hcanonical
    hquota0 hquota1 hquota2 hquota3 hsuper hcover
  · simpa [u] using h01Card
  · simpa [w] using h23Card
  · exact hhead
  · intro item hitem
    simpa [u] using hitem
  · intro item hitem
    simpa [w] using hitem

/-- The four-cycle B.2.2(b) schedule follows directly from one chore in each
of its four type pools.  The cover is derived by the finite card count. -/
theorem existsEfxOfB1LowMultiplicity_fourCycle_longZero_of_typePoolCards
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 0) - r)
    (hm2Card : m2Chores.card = 4)
    (h01Card : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card = 1)
    (h12Card : (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).card = 1)
    (h23Card : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 1)
    (h03Card : (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card = 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  obtain ⟨item01, h01Eq⟩ := Finset.card_eq_one.mp h01Card
  obtain ⟨item12, h12Eq⟩ := Finset.card_eq_one.mp h12Card
  obtain ⟨item23, h23Eq⟩ := Finset.card_eq_one.mp h23Card
  obtain ⟨item03, h03Eq⟩ := Finset.card_eq_one.mp h03Card
  have h01 : item01 ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) := by
    rw [h01Eq]
    simp
  have h12 : item12 ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) := by
    rw [h12Eq]
    simp
  have h23 : item23 ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) := by
    rw [h23Eq]
    simp
  have h03 : item03 ∈ m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)) := by
    rw [h03Eq]
    simp
  have htypeCover := m2_eq_union_of_four_type_pools_of_card_one Item cost m2Chores
    ({0, 1} : Finset (Fin 4)) ({1, 2} : Finset (Fin 4))
    ({2, 3} : Finset (Fin 4)) ({0, 3} : Finset (Fin 4))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hm2Card h01Card h12Card h23Card h03Card
  have hcover : m2Chores = ({item01, item12} ∪ {item23}) ∪ {item03} := by
    simpa [h01Eq, h12Eq, h23Eq, h03Eq] using htypeCover
  exact existsEfxOfB1LowMultiplicity_fourCycle_longZero Item r cost
    prefixChores m2Chores item01 item12 item23 item03 a quota prefixAllocation
    hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3 hsuper
    h01 h12 h23 h03 hcover

/-- The doubled-edge cardinality dispatch is invariant under agent labels. -/
theorem existsEfxOfB1LowMultiplicity_doubleDisjoint_of_relabelled_typePoolCards
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a + 1) (hquota1 : quota (labels 1) = a)
    (hquota2 : quota (labels 2) = a) (hquota3 : quota (labels 3) = a)
    (hsuper : ∀ short : Fin 4, short ≠ labels 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation (labels 0)) - r)
    (hm2Card : m2Chores.card = 4)
    (h01Card : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4))).card = 2)
    (h23Card : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({2, 3} : Finset (Fin 4))).card = 2) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB1LowMultiplicity_doubleDisjoint_longZero_of_typePoolCards Item r
    (relabelChoreCost labels cost) prefixChores m2Chores a
    (relabelQuota labels quota) (relabelAllocation labels prefixAllocation)
  · exact hr
  · exact IsOneOrRChoreCost.relabel labels cost r hcost
  · exact hprefixM2
  · exact hcanonical.relabel labels cost prefixChores quota prefixAllocation
  · simpa [relabelQuota] using hquota0
  · simpa [relabelQuota] using hquota1
  · simpa [relabelQuota] using hquota2
  · simpa [relabelQuota] using hquota3
  · intro short hshort
    have hshortOriginal : labels short ≠ labels 0 := by
      intro hEq
      apply hshort
      exact labels.injective hEq
    simpa [relabelChoreCost, relabelAllocation, additiveChoreCost] using
      hsuper (labels short) hshortOriginal
  · exact hm2Card
  · exact h01Card
  · exact h23Card

/-- The four-cycle cardinality dispatch is invariant under agent labels. -/
theorem existsEfxOfB1LowMultiplicity_fourCycle_of_relabelled_typePoolCards
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a + 1) (hquota1 : quota (labels 1) = a)
    (hquota2 : quota (labels 2) = a) (hquota3 : quota (labels 3) = a)
    (hsuper : ∀ short : Fin 4, short ≠ labels 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation (labels 0)) - r)
    (hm2Card : m2Chores.card = 4)
    (h01Card : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4))).card = 1)
    (h12Card : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({1, 2} : Finset (Fin 4))).card = 1)
    (h23Card : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({2, 3} : Finset (Fin 4))).card = 1)
    (h03Card : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 3} : Finset (Fin 4))).card = 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB1LowMultiplicity_fourCycle_longZero_of_typePoolCards Item r
    (relabelChoreCost labels cost) prefixChores m2Chores a
    (relabelQuota labels quota) (relabelAllocation labels prefixAllocation)
  · exact hr
  · exact IsOneOrRChoreCost.relabel labels cost r hcost
  · exact hprefixM2
  · exact hcanonical.relabel labels cost prefixChores quota prefixAllocation
  · simpa [relabelQuota] using hquota0
  · simpa [relabelQuota] using hquota1
  · simpa [relabelQuota] using hquota2
  · simpa [relabelQuota] using hquota3
  · intro short hshort
    have hshortOriginal : labels short ≠ labels 0 := by
      intro hEq
      apply hshort
      exact labels.injective hEq
    simpa [relabelChoreCost, relabelAllocation, additiveChoreCost] using
      hsuper (labels short) hshortOriginal
  · exact hm2Card
  · exact h01Card
  · exact h12Card
  · exact h23Card
  · exact h03Card

/-- The complete four-chore branch of source Case B.2.2(b).  If no agent has
three M₂ chores that are large for her, the edge-fibre multigraph is
two-regular.  The finite classification leaves either two doubled disjoint
edges or a four-cycle; the relabelled direct schedules above cover all six
labelled profiles. -/
theorem existsEfxOfB1LowMultiplicity_m2_card_four_of_no_three_large
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 0) - r)
    (hm2Card : m2Chores.card = 4)
    (hsmall : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hlarge : ∀ agent : Fin 4, (largeChoreSet cost r agent m2Chores).card ≤ 2) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨hdeg0, hdeg1, hdeg2, hdeg3⟩ :=
    m2_four_edge_degrees_of_no_three_large Item r cost m2Chores hcost hm2Card hsmall hlarge
  rcases m2_four_edge_type_profile_classification Item cost m2Chores
    hdeg0 hdeg1 hdeg2 hdeg3 with hdouble01 | hprofiles
  · exact existsEfxOfB1LowMultiplicity_doubleDisjoint_of_relabelled_typePoolCards
      Item r cost (Equiv.refl (Fin 4)) prefixChores m2Chores a quota prefixAllocation
      hr hcost hprefixM2 hcanonical (by simpa using hquota0) (by simpa using hquota1)
      (by simpa using hquota2) (by simpa using hquota3) (by simpa using hsuper)
      hm2Card (by simpa [m2TypeChorePool_relabel] using hdouble01.1)
      (by simpa [m2TypeChorePool_relabel] using hdouble01.2)
  rcases hprofiles with hdouble02 | hprofiles
  · let labels : Fin 4 ≃ Fin 4 := Equiv.swap 1 2
    apply existsEfxOfB1LowMultiplicity_doubleDisjoint_of_relabelled_typePoolCards
      Item r cost labels prefixChores m2Chores a quota prefixAllocation
    · exact hr
    · exact hcost
    · exact hprefixM2
    · exact hcanonical
    · simpa [labels] using hquota0
    · simpa [labels] using hquota2
    · simpa [labels] using hquota1
    · simpa [labels] using hquota3
    · simpa [labels] using hsuper
    · exact hm2Card
    · rw [m2TypeChorePool_relabel]
      simpa [labels] using hdouble02.1
    · rw [m2TypeChorePool_relabel]
      simpa [labels] using hdouble02.2
  rcases hprofiles with hdouble03 | hprofiles
  · let labels : Fin 4 ≃ Fin 4 := (Equiv.swap 1 3).trans (Equiv.swap 1 2)
    apply existsEfxOfB1LowMultiplicity_doubleDisjoint_of_relabelled_typePoolCards
      Item r cost labels prefixChores m2Chores a quota prefixAllocation
    · exact hr
    · exact hcost
    · exact hprefixM2
    · exact hcanonical
    · simpa [labels] using hquota0
    · simpa [labels] using hquota3
    · simpa [labels] using hquota1
    · simpa [labels] using hquota2
    · simpa [labels] using hsuper
    · exact hm2Card
    · rw [m2TypeChorePool_relabel]
      simpa [labels] using hdouble03.1
    · rw [m2TypeChorePool_relabel]
      simpa [labels] using hdouble03.2
  rcases hprofiles with hcycle01 | hprofiles
  · rcases hcycle01 with ⟨h01, h12, h23, h03⟩
    exact existsEfxOfB1LowMultiplicity_fourCycle_of_relabelled_typePoolCards
      Item r cost (Equiv.refl (Fin 4)) prefixChores m2Chores a quota prefixAllocation
      hr hcost hprefixM2 hcanonical (by simpa using hquota0) (by simpa using hquota1)
      (by simpa using hquota2) (by simpa using hquota3) (by simpa using hsuper)
      hm2Card (by simpa [m2TypeChorePool_relabel] using h01)
      (by simpa [m2TypeChorePool_relabel] using h12)
      (by simpa [m2TypeChorePool_relabel] using h23)
      (by simpa [m2TypeChorePool_relabel] using h03)
  rcases hprofiles with hcycle013 | hcycle023
  · rcases hcycle013 with ⟨h01, h13, h23, h02⟩
    let labels : Fin 4 ≃ Fin 4 := Equiv.swap 2 3
    apply existsEfxOfB1LowMultiplicity_fourCycle_of_relabelled_typePoolCards
      Item r cost labels prefixChores m2Chores a quota prefixAllocation
    · exact hr
    · exact hcost
    · exact hprefixM2
    · exact hcanonical
    · simpa [labels] using hquota0
    · simpa [labels] using hquota1
    · simpa [labels] using hquota3
    · simpa [labels] using hquota2
    · simpa [labels] using hsuper
    · exact hm2Card
    · rw [m2TypeChorePool_relabel]
      simpa [labels] using h01
    · rw [m2TypeChorePool_relabel]
      simpa [labels] using h13
    · rw [m2TypeChorePool_relabel]
      have hmap : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = {2, 3} := by
        decide
      rw [hmap]
      exact h23
    · rw [m2TypeChorePool_relabel]
      simpa [labels] using h02
  · rcases hcycle023 with ⟨h02, h12, h13, h03⟩
    let labels : Fin 4 ≃ Fin 4 := Equiv.swap 1 2
    apply existsEfxOfB1LowMultiplicity_fourCycle_of_relabelled_typePoolCards
      Item r cost labels prefixChores m2Chores a quota prefixAllocation
    · exact hr
    · exact hcost
    · exact hprefixM2
    · exact hcanonical
    · simpa [labels] using hquota0
    · simpa [labels] using hquota2
    · simpa [labels] using hquota1
    · simpa [labels] using hquota3
    · simpa [labels] using hsuper
    · exact hm2Card
    · rw [m2TypeChorePool_relabel]
      simpa [labels] using h02
    · rw [m2TypeChorePool_relabel]
      have hmap : ({1, 2} : Finset (Fin 4)).map labels.toEmbedding = {1, 2} := by
        decide
      rw [hmap]
      exact h12
    · rw [m2TypeChorePool_relabel]
      simpa [labels] using h13
    · rw [m2TypeChorePool_relabel]
      simpa [labels] using h03

end HT26EFXChores
