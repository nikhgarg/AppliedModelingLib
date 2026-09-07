import HT26EFXChores.B1DisjointResidualClassification
import HT26EFXChores.M34Extension

/-!
# Complete B.2.1(b) dispatcher in oriented labels

This is the source case after the canonical-prefix orientation has selected
the identity or the swap of agents 2 and 3.

Source: EFXadditivechores.tex, lines 2411--2443.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- Complete source Case B.2.1(b), once the prefix has been oriented in the
working labels.  The two small fibre profiles use their explicit schedules;
every other instance uses the three-chore gap fill and the residual
classification. -/
theorem existsEfxOfB1DisjointMaximum_of_relabelled_prefix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (first second third : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost)
      prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hshortAdvantage : additiveChoreCost (relabelChoreCost labels cost) 3
      (prefixAllocation 3) ≤
        additiveChoreCost (relabelChoreCost labels cost) 3 (prefixAllocation 2) - r)
    (hcover : m2Chores =
      m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({2, 3} : Finset (Fin 4)))
    (hsecondCardLe : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({2, 3} : Finset (Fin 4))).card ≤
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({0, 1} : Finset (Fin 4))).card)
    (hfirst : first ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second) (hfirstNeThird : first ≠ third)
    (hsecondNeThird : second ≠ third)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  by_cases hsmallProfile :
      ((m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({0, 1} : Finset (Fin 4))).card = 3 ∨
        (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
          ({0, 1} : Finset (Fin 4))).card = 4) ∧
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({2, 3} : Finset (Fin 4))).card = 3
  · exact existsEfxOfB1DisjointExceptionalDirect_of_relabelled_typePools Item r cost labels
      prefixChores m2Chores a quota prefixAllocation hr hcost hprefixM2 hcanonical hquota0
      hquota1 hquota2 hquota3 hshortAdvantage hcover hsmallProfile.1 hsmallProfile.2
  · by_cases hnotExceptional : ¬ IsM2Exceptional (relabelChoreCost labels cost)
      (m2Chores \ {first, second, third})
    · exact existsEfxOfB1DisjointResidual_of_relabelled_prefix Item r cost labels
        prefixChores m2Chores a quota prefixAllocation first second third hr hcost hprefixM2
        hcanonical hquota0 hquota1 hquota2 hquota3 hshortAdvantage hfirst hsecond hthird
        hfirstNeSecond hfirstNeThird hsecondNeThird hm2Small (Or.inl hnotExceptional)
    · have hexceptional : IsM2Exceptional (relabelChoreCost labels cost)
          (m2Chores \ {first, second, third}) :=
        not_not.mp hnotExceptional
      rcases b1_disjoint_exceptional_endpoints_or_small_profiles Item
          (relabelChoreCost labels cost) m2Chores first second third hfirst hsecond hthird
          hfirstNeSecond hfirstNeThird hsecondNeThird hcover hsecondCardLe hexceptional with
        hendpoint | hsmallThree | hsmallFour
      · exact existsEfxOfB1DisjointResidual_of_relabelled_prefix Item r cost labels
          prefixChores m2Chores a quota prefixAllocation first second third hr hcost hprefixM2
          hcanonical hquota0 hquota1 hquota2 hquota3 hshortAdvantage hfirst hsecond hthird
          hfirstNeSecond hfirstNeThird hsecondNeThird hm2Small (Or.inr hendpoint)
      · exact False.elim (hsmallProfile ⟨Or.inl hsmallThree.1, hsmallThree.2⟩)
      · exact False.elim (hsmallProfile ⟨Or.inr hsmallFour.1, hsmallFour.2⟩)

/-- Complete fixed-label source Case B.2.1(b).  The canonical-prefix
orientation supplies either the original labels or the swap of 2 and 3; both
displayed M2 endpoint fibres are invariant under that swap. -/
theorem existsEfxOfB1DisjointMaximum_dispatch
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (first second third : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcover : m2Chores =
      m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hsecondCardLe : (m2TypeChorePool cost m2Chores
      ({2, 3} : Finset (Fin 4))).card ≤
      (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second) (hfirstNeThird : first ≠ third)
    (hsecondNeThird : second ≠ third)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨labels, quota, prefixAllocation, hlabels, hcanonical, hquota0, hquota1,
      hquota2, hquota3, hshortAdvantage⟩ :=
    existsCanonicalB1DisjointPrefix Item r cost prefixChores a (by linarith) hcost
      hprefixCard hprefixSmall
  have hmap01 : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = {0, 1} := by
    rcases hlabels with rfl | rfl <;> decide
  have hmap23 : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = {2, 3} := by
    rcases hlabels with rfl | rfl <;> decide
  apply existsEfxOfB1DisjointMaximum_of_relabelled_prefix Item r cost labels
    prefixChores m2Chores a quota prefixAllocation first second third hr hcost hprefixM2
    hcanonical hquota0 hquota1 hquota2 hquota3 hshortAdvantage
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)),
      m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)),
      hmap01, hmap23]
    exact hcover
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)),
      m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)),
      hmap01, hmap23]
    exact hsecondCardLe
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmap01]
    exact hfirst
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmap01]
    exact hsecond
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmap01]
    exact hthird
  · exact hfirstNeSecond
  · exact hfirstNeThird
  · exact hsecondNeThird
  · exact hm2Small

/-- The complete fixed-label B.2.1(b) branch extended across the M34 pool by
the source's iterative insertion lemma. -/
theorem existsEfxOfM01M2M34_b1DisjointMaximum
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
    (hcover : m2Chores =
      m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hsecondCardLe : (m2TypeChorePool cost m2Chores
      ({2, 3} : Finset (Fin 4))).card ≤
      (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second) (hfirstNeThird : first ≠ third)
    (hsecondNeThird : second ≠ third) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨baseAllocation, hbaseAllocation, hbaseEFX⟩ :=
    existsEfxOfB1DisjointMaximum_dispatch Item r cost prefixChores m2Chores a first second
      third hr hcost hprefixCard hprefixSmall hprefixM2 hcover hsecondCardLe hfirst hsecond
      hthird hfirstNeSecond hfirstNeThird hsecondNeThird hm2Small
  have hbaseM34 : Disjoint (prefixChores ∪ m2Chores) m34Chores := by
    rw [Finset.disjoint_left]
    intro item hbase hm34
    rcases Finset.mem_union.mp hbase with hprefix | hm2
    · exact (Finset.disjoint_left.mp hprefixM34 hprefix hm34).elim
    · exact (Finset.disjoint_left.mp hm2M34 hm2 hm34).elim
  exact extendEfxByM34 Item r cost (prefixChores ∪ m2Chores) m34Chores hr hcost
    hbaseM34 hm34Small baseAllocation hbaseAllocation hbaseEFX

end HT26EFXChores
