import HT26EFXChores.ExceptionalCombination
import HT26EFXChores.M34Extension
import HT26EFXChores.PoolPartition

/-!
# The divisible M₀₁--M₂ concatenation branch

This module closes the `b = 0` branch of the source's final concatenation
argument.  Here the M₀₁ pool has a multiple of four chores, so its canonical
allocation is envy-free without gap filling.  A nonexceptional M₂ allocation
combines by unit slack.  For an exceptional residue, the controlled-residue
construction combines either through an all-large prefix bundle or through
the canonical `r - 1` cross-cost advantage.

Source: `EFXadditivechores.tex`, lines 1732--1740 (case `b=0`).
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- The `b = 0` source case: a multiple-of-four M₀₁ prefix and an M₂ pool
admit a joint EFX allocation.  This theorem deliberately concerns only the
M₀₁--M₂ reduction; M₃₄ chores are inserted later by the paper's insertion
lemma. -/
theorem existsEfxOfM01M2_divisible
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hdisjoint : Disjoint prefixChores m2Chores)
    (hprefixCard : prefixChores.card = 4 * a)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let quota : Fin 4 → ℕ := fun _ => a
  have hquotaSum : Finset.univ.sum quota = prefixChores.card := by
    simp [quota, hprefixCard]
  obtain ⟨prefixAllocation, hcanonical⟩ :=
    existsCanonicalSmallChoreAllocation Item cost prefixChores quota hquotaSum hprefixSmall
  have hprefixEnvyFree : EnvyFreeForChores (additiveChoreCost cost) prefixAllocation :=
    IsCanonicalSmallChoreAllocation.envyFreeForChores cost r prefixChores quota
      prefixAllocation a hcost (by linarith) (by intro agent; simp [quota]) hcanonical
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  have hbundleDisjoint (right : Allocation (Fin 4) Item)
      (hright : IsAllocationOf right m2Chores) :
      ∀ agent, Disjoint (prefixAllocation agent) (right agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro item hprefix hrightItem
    exact (Finset.disjoint_left.mp hdisjoint
      (hcanonical.isAllocationOf.1 agent item hprefix)
      (hright.1 agent item hrightItem)).elim
  have hcombinedAllocation (right : Allocation (Fin 4) Item)
      (hright : IsAllocationOf right m2Chores) :
      IsAllocationOf (fun agent => prefixAllocation agent ∪ right agent)
        (prefixChores ∪ m2Chores) :=
    isAllocationOf_union prefixAllocation right prefixChores m2Chores hdisjoint
      hcanonical.isAllocationOf hright
  obtain ⟨right, hright, _hefx, hcertificates⟩ :=
    existsEfxOfM2_with_conditionalCertificates Item r cost m2Chores hr hcost hm2Small
  by_cases hexceptional : IsM2Exceptional cost m2Chores
  · rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary,
      htypesDisjoint, hshape⟩
    obtain ⟨special, companion, hne, hauxEq⟩ := Finset.card_eq_two.mp hauxiliary
    have hspecial : special ∈ auxiliary := by simp [hauxEq]
    have hcompanion : companion ∈ auxiliary := by simp [hauxEq]
    have hfinish (chosen other : Fin 4)
        (hchosen : chosen ∈ auxiliary) (hother : other ∈ auxiliary)
        (hchosenNe : chosen ≠ other)
        (hprefixCondition :
          (∀ item ∈ prefixAllocation chosen, IsLargeChore cost r chosen item) ∨
          additiveChoreCost cost chosen (prefixAllocation chosen) + (r - 1) ≤
            additiveChoreCost cost chosen (prefixAllocation other)) :
        ∃ allocation : Allocation (Fin 4) Item,
          IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
            EFXForChores (additiveChoreCost cost) allocation := by
      obtain ⟨controlled, hcontrolled, hunit, hlarge, haway, hcomparison⟩ :=
        existsExceptionalM2Allocation_controlled Item r cost m2Chores dominant auxiliary q
          (by linarith) hcost hdominant hauxiliary htypesDisjoint hshape chosen other
          hchosen hother hchosenNe
      refine ⟨fun agent => prefixAllocation agent ∪ controlled agent,
        hcombinedAllocation controlled hcontrolled, ?_⟩
      exact efx_union_of_controlled_exceptional Item r cost prefixAllocation controlled
        chosen other (hbundleDisjoint controlled hcontrolled) hcostLower hprefixEnvyFree hunit
        hlarge haway hcomparison hprefixCondition
    by_cases hsmallSpecial : ∃ item ∈ prefixAllocation special,
        IsSmallChore cost special item
    · by_cases hsmallCompanion : ∃ item ∈ prefixAllocation companion,
          IsSmallChore cost companion item
      · have hadvantage : additiveChoreCost cost special (prefixAllocation special) + (r - 1) ≤
            additiveChoreCost cost special (prefixAllocation companion) :=
          hcanonical.cross_cost_advantage_of_ownSmall cost r prefixChores quota prefixAllocation
            hcost (by linarith) hprefixSmall special companion hne (by simp [quota])
            hsmallSpecial hsmallCompanion
        exact hfinish special companion hspecial hcompanion hne (Or.inr hadvantage)
      · have hleftLarge : ∀ item ∈ prefixAllocation companion,
            IsLargeChore cost r companion item := by
          intro item hitem
          rcases hcost companion item with hsmall | hlarge
          · exact (hsmallCompanion ⟨item, hitem, by simpa [IsSmallChore] using hsmall⟩).elim
          · simpa [IsLargeChore] using hlarge
        exact hfinish companion special hcompanion hspecial hne.symm (Or.inl hleftLarge)
    · have hleftLarge : ∀ item ∈ prefixAllocation special,
          IsLargeChore cost r special item := by
        intro item hitem
        rcases hcost special item with hsmall | hlarge
        · exact (hsmallSpecial ⟨item, hitem, by simpa [IsSmallChore] using hsmall⟩).elim
        · simpa [IsLargeChore] using hlarge
      exact hfinish special companion hspecial hcompanion hne (Or.inl hleftLarge)
  · have hcertificate := hcertificates hexceptional
    have hunit : ∀ agent other,
        additiveChoreCost cost agent (right agent) - 1 ≤
          additiveChoreCost cost agent (right other) := by
      intro agent other
      by_cases hsmall : ∃ item ∈ right agent, IsSmallChore cost agent item
      · exact hcertificate.1 agent hsmall other
      · have hlarge : ∀ item ∈ right agent, IsLargeChore cost r agent item := by
          intro item hitem
          rcases hcost agent item with hsmallItem | hlargeItem
          · exact (hsmall ⟨item, hitem, by simpa [IsSmallChore] using hsmallItem⟩).elim
          · simpa [IsLargeChore] using hlargeItem
        have henvyFree := hcertificate.2 agent hlarge other
        linarith
    refine ⟨fun agent => prefixAllocation agent ∪ right agent,
      hcombinedAllocation right hright, ?_⟩
    exact efxForChores_union_of_envyFree_of_unit_slack cost prefixAllocation right
      (hbundleDisjoint right hright) hcostLower hprefixEnvyFree hunit

/-- The complete `b = 0` branch after restoring the M₃₄ chores.  It first
uses `existsEfxOfM01M2_divisible` for the reduced pool and then applies the
paper's iterated insertion argument. -/
theorem existsEfxOfM01M2M34_divisible
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixM34 : Disjoint prefixChores m34Chores)
    (hm2M34 : Disjoint m2Chores m34Chores)
    (hprefixCard : prefixChores.card = 4 * a)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hm34Small : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨baseAllocation, hbaseAllocation, hbaseEFX⟩ :=
    existsEfxOfM01M2_divisible Item r cost prefixChores m2Chores a hr hcost hprefixM2
      hprefixCard hprefixSmall hm2Small
  have hbaseM34 : Disjoint (prefixChores ∪ m2Chores) m34Chores := by
    rw [Finset.disjoint_left]
    intro item hbase hm34
    rcases Finset.mem_union.mp hbase with hprefix | hm2
    · exact (Finset.disjoint_left.mp hprefixM34 hprefix hm34).elim
    · exact (Finset.disjoint_left.mp hm2M34 hm2 hm34).elim
  exact extendEfxByM34 Item r cost (prefixChores ∪ m2Chores) m34Chores hr hcost
    hbaseM34 hm34Small baseAllocation hbaseAllocation hbaseEFX

/-- The normalized four-agent theorem is complete whenever the automatically
defined M₀₁ pool has cardinality divisible by four. -/
theorem existsEfxOfOneOrR_b0
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcard : (m01ChorePool cost chores).card = 4 * a) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨allocation, hallocation, hefx⟩ :=
    existsEfxOfM01M2M34_divisible Item r cost (m01ChorePool cost chores)
      (m2ChorePool cost chores) (m34ChorePool cost chores) a hr hcost
      (m01ChorePool_disjoint_m2ChorePool cost chores)
      (m01ChorePool_disjoint_m34ChorePool cost chores)
      (m2ChorePool_disjoint_m34ChorePool cost chores) hcard
      (m01ChorePool_small cost chores) (m2ChorePool_small cost chores)
      (m34ChorePool_small cost chores)
  refine ⟨allocation, ?_, hefx⟩
  simpa only [← Finset.union_assoc, m01_m2_m34_union_eq] using hallocation

end HT26EFXChores
