import HT26EFXChores.B1DirectAllocation
import HT26EFXChores.B1DisjointPrefix
import HT26EFXChores.B1DisjointSpecialAllocation
import HT26EFXChores.HighRatioGapFilling

/-!
# Source-to-model bridges for high-multiplicity Case B.2.1

This module begins the outer dispatch for the `b = 1` branch in which a
maximum M₂ edge type has multiplicity at least three.

Source: `EFXadditivechores.tex`, lines 2241--2470.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- The B.2.1(b) gap-fill/residual schedules transport back across the only
prefix relabelling used in that case.  The source's canonical-prefix
orientation chooses either the identity or the swap of agents `2,3`; this
bridge keeps the residual classification in those working labels and returns
an EFX allocation for the original instance. -/
theorem existsEfxOfB1DisjointResidual_of_relabelled_prefix
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
    (hfirst : first ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second) (hfirstNeThird : first ≠ third)
    (hsecondNeThird : second ≠ third)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hresidual :
      ¬ IsM2Exceptional (relabelChoreCost labels cost) (m2Chores \ {first, second, third}) ∨
      IsM2ExceptionalWithEndpoints (relabelChoreCost labels cost)
        (m2Chores \ {first, second, third}) 2 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  rcases hresidual with hnonexceptional | hexceptional
  · exact existsEfxOfM01M2_b1_disjoint_nonexceptional Item r (relabelChoreCost labels cost)
      prefixChores m2Chores a quota prefixAllocation first second third hr
      (IsOneOrRChoreCost.relabel labels cost r hcost) hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hshortAdvantage hfirst hsecond hthird
      hfirstNeSecond hfirstNeThird hsecondNeThird
      (fun item hitem => IsSmallForExactlyTwo.relabel labels cost item (hm2Small item hitem))
      hnonexceptional
  · exact existsEfxOfM01M2_b1_disjoint_exceptional Item r (relabelChoreCost labels cost)
      prefixChores m2Chores a quota prefixAllocation first second third hr
      (IsOneOrRChoreCost.relabel labels cost r hcost) hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hshortAdvantage hfirst hsecond hthird
      hfirstNeSecond hfirstNeThird hsecondNeThird hexceptional

/-- After the intersecting-edge gap fill in B.2.1(a), an exceptional residue
has auxiliary endpoints either at the maximum type `(0,1)` or at its
complement `(2,3)`.  A surviving maximum-type chore rules out every other
exceptional pair. -/
theorem b1_intersecting_exceptional_auxiliary_pair
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (first second third : Item)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hexceptional : IsM2Exceptional cost (m2Chores \ {first, second, third})) :
    IsM2ExceptionalWithEndpoints cost (m2Chores \ {first, second, third}) 0 1 ∨
      IsM2ExceptionalWithEndpoints cost (m2Chores \ {first, second, third}) 2 3 := by
  let residue := m2Chores \ {first, second, third}
  let firstType := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  have hdominantLarge : ∀ dominant auxiliary : Finset (Fin 4), ∀ q : ℕ,
      dominant.card = 2 → auxiliary.card = 2 → Disjoint dominant auxiliary →
      (((∀ item ∈ residue, smallAgentSet cost item = dominant) ∧
          residue.card = 4 * q + 3) ∨
        (∃ exceptionalItem ∈ residue, smallAgentSet cost exceptionalItem = auxiliary ∧
          (∀ item ∈ residue.erase exceptionalItem, smallAgentSet cost item = dominant) ∧
          (residue.erase exceptionalItem).card = 4 * q + 3)) →
      3 ≤ (m2TypeChorePool cost m2Chores dominant).card := by
    intro dominant auxiliary q _hdominant _hauxiliary _hdisjoint hshape
    rcases hshape with hfixed | hsingle
    · have hsubset : residue ⊆ m2TypeChorePool cost m2Chores dominant := by
        intro item hitem
        exact (mem_m2TypeChorePool cost m2Chores dominant item).mpr
          ⟨Finset.sdiff_subset hitem, hfixed.1 item hitem⟩
      have hcard := Finset.card_le_card hsubset
      rw [hfixed.2] at hcard
      omega
    · obtain ⟨exceptionalItem, _hexceptionalItem, _hitemType, houtsideType,
          houtsideCard⟩ := hsingle
      have hsubset : residue.erase exceptionalItem ⊆
          m2TypeChorePool cost m2Chores dominant := by
        intro item hitem
        exact (mem_m2TypeChorePool cost m2Chores dominant item).mpr
          ⟨Finset.sdiff_subset (Finset.erase_subset exceptionalItem residue hitem),
            houtsideType item hitem⟩
      have hcard := Finset.card_le_card hsubset
      rw [houtsideCard] at hcard
      omega
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary,
      hdisjoint, hshape⟩
  have hdominantPoolLarge : 3 ≤ (m2TypeChorePool cost m2Chores dominant).card :=
    hdominantLarge dominant auxiliary q hdominant hauxiliary hdisjoint (by
      simpa [residue] using hshape)
  have hfirstTypeCard : 3 ≤ firstType.card := by
    exact hdominantPoolLarge.trans (by simpa [firstType] using hmaximum dominant)
  have hsurviving : ∃ item ∈ firstType, item ∉ ({first, second} : Finset Item) := by
    by_contra hnone
    have hsubset : firstType ⊆ ({first, second} : Finset Item) := by
      intro item hitem
      by_contra hnot
      exact hnone ⟨item, hitem, hnot⟩
    have hcard : firstType.card ≤ 2 := by
      calc
        firstType.card ≤ ({first, second} : Finset Item).card := Finset.card_le_card hsubset
        _ = 2 := by simp [hfirstNeSecond]
    omega
  obtain ⟨surviving, hsurvivingType, hsurvivingNotFirstSecond⟩ := hsurviving
  have hsurvivingSmall : smallAgentSet cost surviving = ({0, 1} : Finset (Fin 4)) :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) surviving).mp
      (by simpa [firstType] using hsurvivingType) |>.2
  have hsurvivingNeThird : surviving ≠ third := by
    intro hEq
    subst third
    have hthirdSmall : smallAgentSet cost surviving = ({1, 2} : Finset (Fin 4)) :=
      (mem_m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) surviving).mp hthird |>.2
    exact (by decide : ({0, 1} : Finset (Fin 4)) ≠ {1, 2})
      (hsurvivingSmall.symm.trans hthirdSmall)
  have hsurvivingNotGap : surviving ∉ ({first, second, third} : Finset Item) := by
    simpa [Finset.mem_insert, Finset.mem_singleton, hsurvivingNeThird] using
      hsurvivingNotFirstSecond
  have hsurvivingResidue : surviving ∈ residue := by
    refine Finset.mem_sdiff.mpr ⟨?_, hsurvivingNotGap⟩
    exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) surviving).mp
      (by simpa [firstType] using hsurvivingType) |>.1
  have hauxiliary_eq_23 (hdominantEq : dominant = ({0, 1} : Finset (Fin 4))) :
      auxiliary = ({2, 3} : Finset (Fin 4)) := by
    have hsubset : auxiliary ⊆ ({0, 1} : Finset (Fin 4))ᶜ := by
      intro agent hagent
      simp only [Finset.mem_compl]
      intro hfirstPair
      apply Finset.disjoint_left.mp hdisjoint
      · rw [hdominantEq]
        exact hfirstPair
      · exact hagent
    have hauxiliaryCompl : auxiliary = ({0, 1} : Finset (Fin 4))ᶜ := by
      apply Finset.eq_of_subset_of_card_le hsubset
      have hcomplementCard : (({0, 1} : Finset (Fin 4))ᶜ).card = 2 := by
        decide
      rw [hcomplementCard, hauxiliary]
    calc
      auxiliary = ({0, 1} : Finset (Fin 4))ᶜ := hauxiliaryCompl
      _ = ({2, 3} : Finset (Fin 4)) := by decide
  rcases hshape with hfixed | hsingle
  · have hdominantEq : dominant = ({0, 1} : Finset (Fin 4)) :=
      (hfixed.1 surviving hsurvivingResidue).symm.trans hsurvivingSmall
    have hauxiliaryEq := hauxiliary_eq_23 hdominantEq
    right
    refine ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint, ?_, ?_, Or.inl hfixed⟩
    · simpa [hauxiliaryEq]
    · simpa [hauxiliaryEq]
  · obtain ⟨exceptionalItem, hexceptionalItem, hitemType, houtsideType,
      houtsideCard⟩ := hsingle
    by_cases hsurvivingExceptional : surviving = exceptionalItem
    · subst surviving
      have hauxiliaryEq : auxiliary = ({0, 1} : Finset (Fin 4)) :=
        hitemType.symm.trans hsurvivingSmall
      left
      refine ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint, ?_, ?_,
        Or.inr ⟨exceptionalItem, hexceptionalItem, hitemType, houtsideType, houtsideCard⟩⟩
      · simpa [hauxiliaryEq]
      · simpa [hauxiliaryEq]
    · have hsurvivingErase : surviving ∈ residue.erase exceptionalItem :=
        Finset.mem_erase.mpr ⟨hsurvivingExceptional, hsurvivingResidue⟩
      have hdominantEq : dominant = ({0, 1} : Finset (Fin 4)) :=
        (houtsideType surviving hsurvivingErase).symm.trans hsurvivingSmall
      have hauxiliaryEq := hauxiliary_eq_23 hdominantEq
      right
      refine ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint, ?_, ?_,
        Or.inr ⟨exceptionalItem, hexceptionalItem, hitemType, houtsideType, houtsideCard⟩⟩
      · simpa [hauxiliaryEq]
      · simpa [hauxiliaryEq]

/-- If the exceptional endpoints after the intersecting B.2.1(a) gap fill
are the maximum pair itself, the residual has the source's tight `3,1,3`
form: one surviving maximum-type chore and a `4q+3` complementary fibre.
The fixed-fibre exceptional alternative is impossible because a maximum-type
chore remains after removing only two such chores. -/
theorem b1_intersecting_exceptional_shortPair_tight_data
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (first second third : Item)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hexceptional : IsM2ExceptionalWithEndpoints cost
      (m2Chores \ {first, second, third}) 0 1) :
    ∃ surviving q, surviving ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∧
      m2Chores \ {first, second, third} = {surviving} ∪
        m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) ∧
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 4 * q + 3 := by
  let residue := m2Chores \ {first, second, third}
  let firstType := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let secondType := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary,
      hdisjoint, hzero, hone, hshape⟩
  have hauxiliaryEq : auxiliary = ({0, 1} : Finset (Fin 4)) := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro agent hagent
      simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
      rcases hagent with rfl | rfl
      · exact hzero
      · exact hone
    · rw [hauxiliary]
      decide
  have hdominantEq : dominant = ({2, 3} : Finset (Fin 4)) := by
    have hsubset : dominant ⊆ ({0, 1} : Finset (Fin 4))ᶜ := by
      intro agent hagent
      simp only [Finset.mem_compl]
      intro hpair
      apply Finset.disjoint_left.mp hdisjoint hagent
      rw [hauxiliaryEq]
      exact hpair
    have hdominantCompl : dominant = ({0, 1} : Finset (Fin 4))ᶜ := by
      apply Finset.eq_of_subset_of_card_le hsubset
      have hcomplementCard : (({0, 1} : Finset (Fin 4))ᶜ).card = 2 := by
        decide
      rw [hcomplementCard, hdominant]
    calc
      dominant = ({0, 1} : Finset (Fin 4))ᶜ := hdominantCompl
      _ = ({2, 3} : Finset (Fin 4)) := by decide
  rcases hshape with hfixed | hsingle
  · have hresidueSubset : residue ⊆ secondType := by
      intro item hitem
      apply (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mpr
      refine ⟨Finset.sdiff_subset hitem, ?_⟩
      simpa [residue, hdominantEq] using hfixed.1 item (by simpa [residue] using hitem)
    have hresidueCardLarge : 3 ≤ residue.card := by
      rw [show residue.card = 4 * q + 3 by simpa [residue] using hfixed.2]
      omega
    have hsecondTypeCard : 3 ≤ secondType.card :=
      hresidueCardLarge.trans (Finset.card_le_card hresidueSubset)
    have hfirstTypeCard : 3 ≤ firstType.card :=
      hsecondTypeCard.trans (by simpa [firstType, secondType] using hmaximum ({2, 3}))
    have hsurviving : ∃ item ∈ firstType, item ∉ ({first, second} : Finset Item) := by
      by_contra hnone
      have hsubset : firstType ⊆ ({first, second} : Finset Item) := by
        intro item hitem
        by_contra hnot
        exact hnone ⟨item, hitem, hnot⟩
      have hcard : firstType.card ≤ 2 := by
        calc
          firstType.card ≤ ({first, second} : Finset Item).card := Finset.card_le_card hsubset
          _ = 2 := by simp [hfirstNeSecond]
      omega
    obtain ⟨surviving, hsurvivingType, hsurvivingNotFirstSecond⟩ := hsurviving
    have hsurvivingSmall : smallAgentSet cost surviving = ({0, 1} : Finset (Fin 4)) :=
      (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) surviving).mp
        (by simpa [firstType] using hsurvivingType) |>.2
    have hsurvivingNeThird : surviving ≠ third := by
      intro hEq
      subst third
      have hthirdSmall : smallAgentSet cost surviving = ({1, 2} : Finset (Fin 4)) :=
        (mem_m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) surviving).mp hthird |>.2
      exact (by decide : ({0, 1} : Finset (Fin 4)) ≠ {1, 2})
        (hsurvivingSmall.symm.trans hthirdSmall)
    have hsurvivingNotGap : surviving ∉ ({first, second, third} : Finset Item) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, hsurvivingNeThird] using
        hsurvivingNotFirstSecond
    have hsurvivingResidue : surviving ∈ residue := by
      refine Finset.mem_sdiff.mpr ⟨?_, hsurvivingNotGap⟩
      exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) surviving).mp
        (by simpa [firstType] using hsurvivingType) |>.1
    have hcontradiction : ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by
      have hsurvivingDominant : smallAgentSet cost surviving = ({2, 3} : Finset (Fin 4)) := by
        simpa [hdominantEq] using hfixed.1 surviving (by simpa [residue] using hsurvivingResidue)
      exact hsurvivingDominant.symm.trans hsurvivingSmall
    exact False.elim ((by decide : ({2, 3} : Finset (Fin 4)) ≠ ({0, 1} : Finset (Fin 4)))
      hcontradiction)
  · obtain ⟨surviving, hsurvivingResidue, hsurvivingType, houtsideType,
      houtsideCard⟩ := hsingle
    change surviving ∈ m2Chores \ ({first, second, third} : Finset Item) at hsurvivingResidue
    have hsurvivingM2 : surviving ∈ m2Chores :=
      (Finset.mem_sdiff.mp hsurvivingResidue).1
    have hsurvivingFirstType : surviving ∈ firstType := by
      apply (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) surviving).mpr
      refine ⟨hsurvivingM2, ?_⟩
      simpa [hauxiliaryEq] using hsurvivingType
    have hsurvivingNotSecondType : surviving ∉ secondType := by
      intro hsecondType
      have hsecondSmall :=
        (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) surviving).mp
          (by simpa [secondType] using hsecondType) |>.2
      have hcontradiction : ({0, 1} : Finset (Fin 4)) = ({2, 3} : Finset (Fin 4)) := by
        calc
          ({0, 1} : Finset (Fin 4)) = auxiliary := (by simpa [hauxiliaryEq])
          _ = smallAgentSet cost surviving := hsurvivingType.symm
          _ = ({2, 3} : Finset (Fin 4)) := hsecondSmall
      exact (by decide : ({0, 1} : Finset (Fin 4)) ≠ ({2, 3} : Finset (Fin 4)))
        hcontradiction
    have heraseEq : residue.erase surviving = secondType := by
      apply Finset.Subset.antisymm
      · intro item hitem
        apply (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mpr
        refine ⟨Finset.sdiff_subset (Finset.erase_subset surviving residue hitem), ?_⟩
        simpa [residue, hdominantEq] using houtsideType item
          (by simpa [residue] using hitem)
      · intro item hitem
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · intro hEq
          subst item
          exact hsurvivingNotSecondType hitem
        · refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · exact (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mp
              (by simpa [secondType] using hitem) |>.1
          · simp only [Finset.mem_insert, Finset.mem_singleton]
            intro hEq
            rcases hEq with rfl | rfl | rfl
            · exact (Finset.disjoint_left.mp
                (m2TypeChorePool_disjoint_of_ne cost m2Chores
                  ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide))
                hfirst hitem).elim
            · exact (Finset.disjoint_left.mp
                (m2TypeChorePool_disjoint_of_ne cost m2Chores
                  ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide))
                hsecond hitem).elim
            · exact (Finset.disjoint_left.mp
                (m2TypeChorePool_disjoint_of_ne cost m2Chores
                  ({1, 2} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide))
                hthird hitem).elim
    refine ⟨surviving, q, (by simpa [firstType] using hsurvivingFirstType), ?_, ?_⟩
    · change residue = {surviving} ∪ secondType
      calc
        residue = insert surviving (residue.erase surviving) :=
          (Finset.insert_erase (show surviving ∈ residue from hsurvivingResidue)).symm
        _ = {surviving} ∪ secondType := by rw [heraseEq]; simp
    · change secondType.card = 4 * q + 3
      rw [← heraseEq]
      simpa [residue] using houtsideCard

/-- The `3,1,3` direct allocation from source Case B.2.1(a), with the long
agent left explicit.  The endpoint-long schedule covers agents `0` and `3`;
the internal-long schedule covers agents `1` and `2`, with reversal of the
three-edge chain covering the right-hand positions. -/
theorem existsEfxOfB1IntersectingExceptionalDirect_of_longAgent
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores u v w : Finset Item) (head : Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (long : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquotaLong : quota long = a + 1)
    (hquotaShort : ∀ short : Fin 4, short ≠ long → quota short = a)
    (hsuper : ∀ short : Fin 4, short ≠ long →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hcover : m2Chores = u ∪ v ∪ w)
    (huv : Disjoint u v) (huw : Disjoint u w) (hvw : Disjoint v w)
    (hucard : u.card = 3) (hvcard : v.card = 1) (hwcard : w.card = 3)
    (hhead : head ∈ w)
    (hu : ∀ item ∈ u,
      item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hv : ∀ item ∈ v,
      item ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hw : ∀ item ∈ w,
      item ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  fin_cases long
  · apply existsEfxOfB1IntersectingExceptionalDirect_longZero_of_typePools Item r cost
      prefixChores m2Chores u v w head a quota prefixAllocation hr hcost hprefixM2 hcanonical
    · simpa using hquotaLong
    · exact hquotaShort 1 (by decide)
    · exact hquotaShort 2 (by decide)
    · exact hquotaShort 3 (by decide)
    · intro short hshort
      exact hsuper short hshort
    · exact hcover
    · exact huv
    · exact huw
    · exact hvw
    · exact hucard
    · exact hvcard
    · exact hwcard
    · exact hhead
    · exact hu
    · exact hv
    · exact hw
  · apply existsEfxOfB1IntersectingExceptionalDirect_longOne_of_typePools Item r cost
      prefixChores m2Chores u v w head a quota prefixAllocation hr hcost hprefixM2 hcanonical
    · exact hquotaShort 0 (by decide)
    · simpa using hquotaLong
    · exact hquotaShort 2 (by decide)
    · exact hquotaShort 3 (by decide)
    · intro short hshort
      exact hsuper short hshort
    · exact hcover
    · exact huv
    · exact huw
    · exact hvw
    · exact hucard
    · exact hvcard
    · exact hwcard
    · exact hhead
    · exact hu
    · exact hv
    · exact hw
  · let labels : Fin 4 ≃ Fin 4 := (Equiv.swap 0 3).trans (Equiv.swap 1 2)
    have hmap01 : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = {2, 3} := by decide
    have hmap12 : ({1, 2} : Finset (Fin 4)).map labels.toEmbedding = {1, 2} := by decide
    have hmap23 : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = {0, 1} := by decide
    obtain ⟨headU, hheadU⟩ : u.Nonempty := Finset.card_pos.mp (by omega)
    apply existsEfxOfB1IntersectingExceptionalDirect_longOne_of_relabelled_typePools Item r
      cost labels prefixChores m2Chores w v u headU a quota prefixAllocation hr hcost hprefixM2
      hcanonical
    · simpa [labels, Equiv.swap_apply_def] using hquotaShort 3 (by decide)
    · simpa [labels, Equiv.swap_apply_def] using hquotaLong
    · simpa [labels, Equiv.swap_apply_def] using hquotaShort 1 (by decide)
    · simpa [labels, Equiv.swap_apply_def] using hquotaShort 0 (by decide)
    · intro short hshort
      apply hsuper short
      simpa [labels, Equiv.swap_apply_def] using hshort
    · rw [hcover]
      ac_rfl
    · exact hvw.symm
    · exact huw.symm
    · exact huv.symm
    · exact hwcard
    · exact hvcard
    · exact hucard
    · exact hheadU
    · intro item hitem
      rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmap01]
      exact hw item hitem
    · intro item hitem
      rw [m2TypeChorePool_relabel labels cost m2Chores ({1, 2} : Finset (Fin 4)), hmap12]
      exact hv item hitem
    · intro item hitem
      rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmap23]
      exact hu item hitem
  · let labels : Fin 4 ≃ Fin 4 := (Equiv.swap 0 3).trans (Equiv.swap 1 2)
    have hmap01 : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = {2, 3} := by decide
    have hmap12 : ({1, 2} : Finset (Fin 4)).map labels.toEmbedding = {1, 2} := by decide
    have hmap23 : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = {0, 1} := by decide
    obtain ⟨headU, hheadU⟩ : u.Nonempty := Finset.card_pos.mp (by omega)
    apply existsEfxOfB1IntersectingExceptionalDirect_of_relabelled_typePools Item r cost labels
      prefixChores m2Chores w v u headU a quota prefixAllocation hr hcost hprefixM2 hcanonical
    · simpa [labels, Equiv.swap_apply_def] using hquotaLong
    · simpa [labels, Equiv.swap_apply_def] using hquotaShort 2 (by decide)
    · simpa [labels, Equiv.swap_apply_def] using hquotaShort 1 (by decide)
    · simpa [labels, Equiv.swap_apply_def] using hquotaShort 0 (by decide)
    · intro short hshort
      apply hsuper short
      simpa [labels, Equiv.swap_apply_def] using hshort
    · rw [hcover]
      ac_rfl
    · exact hvw.symm
    · exact huw.symm
    · exact huv.symm
    · exact hwcard
    · exact hvcard
    · exact hucard
    · exact hheadU
    · intro item hitem
      rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmap01]
      exact hw item hitem
    · intro item hitem
      rw [m2TypeChorePool_relabel labels cost m2Chores ({1, 2} : Finset (Fin 4)), hmap12]
      exact hv item hitem
    · intro item hitem
      rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmap23]
      exact hu item hitem

/-- A super-canonical quota vector of total size `4a+1` has exactly one long
agent.  This version exposes that agent directly, rather than choosing a
relabelling, for the source's four direct-schedule cases. -/
theorem exists_b1_long_agent
    (a : ℕ) (quota : Fin 4 → ℕ)
    (hquota : ∀ agent, quota agent = a ∨ quota agent = a + 1)
    (hsum : Finset.univ.sum quota = 4 * a + 1) :
    ∃ long : Fin 4, quota long = a + 1 ∧
      ∀ short : Fin 4, short ≠ long → quota short = a := by
  have hsumFour : quota 0 + quota 1 + quota 2 + quota 3 = 4 * a + 1 := by
    simpa [Fin.sum_univ_four, Nat.add_assoc] using hsum
  rcases hquota 0 with h0 | h0
  · rcases hquota 1 with h1 | h1
    · rcases hquota 2 with h2 | h2
      · rcases hquota 3 with h3 | h3
        · omega
        · refine ⟨3, h3, ?_⟩
          intro short hshort
          fin_cases short
          · exact h0
          · exact h1
          · exact h2
          · exact (hshort rfl).elim
      · rcases hquota 3 with h3 | h3
        · refine ⟨2, h2, ?_⟩
          intro short hshort
          fin_cases short
          · exact h0
          · exact h1
          · exact (hshort rfl).elim
          · exact h3
        · omega
    · rcases hquota 2 with h2 | h2
      · rcases hquota 3 with h3 | h3
        · refine ⟨1, h1, ?_⟩
          intro short hshort
          fin_cases short
          · exact h0
          · exact (hshort rfl).elim
          · exact h2
          · exact h3
        · omega
      · rcases hquota 3 with h3 | h3 <;> omega
  · rcases hquota 1 with h1 | h1
    · rcases hquota 2 with h2 | h2
      · rcases hquota 3 with h3 | h3
        · refine ⟨0, h0, ?_⟩
          intro short hshort
          fin_cases short
          · exact (hshort rfl).elim
          · exact h1
          · exact h2
          · exact h3
        · omega
      · rcases hquota 3 with h3 | h3 <;> omega
    · rcases hquota 2 with h2 | h2
      · rcases hquota 3 with h3 | h3 <;> omega
      · rcases hquota 3 with h3 | h3 <;> omega

/-- The tight short-pair leaf of source Case B.2.1(a).  The exceptional
residue forces the complete M₂ pool to have the `3,1,3` chain profile; a
super-canonical prefix then has one long agent, and the preceding four-way
direct dispatch selects its displayed schedule. -/
theorem existsEfxOfB1IntersectingMaximum_tight_dispatch
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ)
    (first second third surviving : Item) (q : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hsurviving : surviving ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hresidue : m2Chores \ {first, second, third} = {surviving} ∪
      m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hresidueCard : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card =
      4 * q + 3)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  obtain ⟨quota, prefixAllocation, hquota, hcanonical, hsuper⟩ :=
    existsSuperCanonicalSmallChoreAllocation Item r cost prefixChores a 1 (by linarith)
      hcost (by omega) (by omega) hprefixCard hprefixSmall
  have hquotaSum : Finset.univ.sum quota = 4 * a + 1 := by
    calc
      Finset.univ.sum quota =
          Finset.univ.sum (fun agent => (prefixAllocation agent).card) := by
            apply Finset.sum_congr rfl
            intro agent _
            symm
            exact (hcanonical.2 agent).1
      _ = prefixChores.card :=
        sum_card_allocation_eq_card_of_isAllocation prefixAllocation prefixChores hcanonical.1
      _ = 4 * a + 1 := hprefixCard
  obtain ⟨long, hquotaLong, hquotaShort⟩ :=
    exists_b1_long_agent a quota hquota hquotaSum
  let u := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let v := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))
  let w := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  have huSub : u ⊆ m2Chores := by
    intro item hitem
    exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp
      (by simpa [u] using hitem) |>.1
  have hvSub : v ⊆ m2Chores := by
    intro item hitem
    exact (mem_m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) item).mp
      (by simpa [v] using hitem) |>.1
  have hwSub : w ⊆ m2Chores := by
    intro item hitem
    exact (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mp
      (by simpa [w] using hitem) |>.1
  have huv : Disjoint u v := by
    simpa [u, v] using m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({0, 1} : Finset (Fin 4)) ({1, 2} : Finset (Fin 4)) (by decide)
  have huw : Disjoint u w := by
    simpa [u, w] using m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)
  have hvw : Disjoint v w := by
    simpa [v, w] using m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({1, 2} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)
  obtain ⟨hcover, hucard, hvcard, hwcard⟩ :=
    b1_intersecting_exceptional_forces_313 Item m2Chores u v w first second third surviving q
      huSub hvSub hwSub huv huw hvw (by simpa [u] using hfirst) (by simpa [u] using hsecond)
      (by simpa [v] using hthird) (by simpa [u] using hsurviving) hfirstNeSecond
      (by simpa [u, w] using hresidue) (by simpa [w] using hresidueCard)
      (by simpa [u, w] using hmaximum ({2, 3} : Finset (Fin 4)))
  obtain ⟨head, hhead⟩ : w.Nonempty := Finset.card_pos.mp (by omega)
  apply existsEfxOfB1IntersectingExceptionalDirect_of_longAgent Item r cost
    prefixChores m2Chores u v w head a quota prefixAllocation long hr hcost hprefixM2 hcanonical
    hquotaLong hquotaShort
  · intro short hshort
    exact hsuper short long (hquotaShort short hshort) hquotaLong
  · exact hcover
  · exact huv
  · exact huw
  · exact hvw
  · exact hucard
  · exact hvcard
  · exact hwcard
  · exact hhead
  · intro item hitem
    simpa [u] using hitem
  · intro item hitem
    simpa [v] using hitem
  · intro item hitem
    simpa [w] using hitem

/-- The ordinary B.2.1(a) intersecting-edge dispatch.  Once the short-pair
exceptional leaf has been excluded, the residual is either nonexceptional or
has the complementary endpoints `(2,3)`, both covered by the source's
gap-filling schedules. -/
theorem existsEfxOfB1IntersectingMaximum_regular
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second third : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a + 1)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hnotShortPair : ¬ IsM2ExceptionalWithEndpoints cost
      (m2Chores \ {first, second, third}) 0 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  by_cases hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {first, second, third})
  · exact existsEfxOfM01M2_b1_intersecting_nonexceptional Item r cost prefixChores m2Chores
      a quota prefixAllocation first second third hr hcost hprefixM2 hcanonical hquota0 hquota1
      hquota2 hquota3 hfirst hsecond hfirstNeSecond hthird hm2Small hnotExceptional
  have hexceptional : IsM2Exceptional cost (m2Chores \ {first, second, third}) :=
    not_not.mp hnotExceptional
  rcases b1_intersecting_exceptional_auxiliary_pair Item cost m2Chores first second third
    hfirst hsecond hthird hfirstNeSecond hmaximum hexceptional with hshortPair | hlongPair
  · exact (hnotShortPair hshortPair).elim
  · exact existsEfxOfM01M2_b1_intersecting_exceptional_unaffectedEdge Item r cost
      prefixChores m2Chores a quota prefixAllocation first second third hr hcost hprefixM2
      hcanonical hquota0 hquota1 hquota2 hquota3 hfirst hsecond hfirstNeSecond hthird (by
        rcases hlongPair with ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint,
          htwo, hthree, hshape⟩
        exact ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint, hthree, htwo, hshape⟩)

/-- The ordinary B.2.1(a) branch with the paper's displayed canonical
prefix: agents `0,1,2` are short and agent `3` is long. -/
theorem existsEfxOfB1IntersectingMaximum_regular_dispatch
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (first second third : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hnotShortPair : ¬ IsM2ExceptionalWithEndpoints cost
      (m2Chores \ {first, second, third}) 0 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let quota : Fin 4 → ℕ := canonicalQuota a {3}
  have hquotaSum : Finset.univ.sum quota = prefixChores.card := by
    calc
      Finset.univ.sum quota = 4 * a + ({3} : Finset (Fin 4)).card := by
        simpa [quota] using canonicalQuota_sum a ({3} : Finset (Fin 4))
      _ = 4 * a + 1 := by simp
      _ = prefixChores.card := hprefixCard.symm
  obtain ⟨prefixAllocation, hcanonical⟩ :=
    existsCanonicalSmallChoreAllocation Item cost prefixChores quota hquotaSum hprefixSmall
  exact existsEfxOfB1IntersectingMaximum_regular Item r cost prefixChores m2Chores a quota
    prefixAllocation first second third hr hcost hprefixM2 hcanonical
    (by simp [quota, canonicalQuota]) (by simp [quota, canonicalQuota])
    (by simp [quota, canonicalQuota]) (by simp [quota, canonicalQuota]) hfirst hsecond hthird
    hfirstNeSecond hm2Small hmaximum hnotShortPair

/-- Complete fixed-label B.2.1(a) dispatch.  If the residual exceptional
endpoints are the short pair `(0,1)`, the source's tight direct allocation
is used; otherwise the ordinary gap-fill/residual schedule applies. -/
theorem existsEfxOfB1IntersectingMaximum_dispatch
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (first second third : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  by_cases hshortPair : IsM2ExceptionalWithEndpoints cost
      (m2Chores \ {first, second, third}) 0 1
  · obtain ⟨surviving, q, hsurviving, hresidue, hresidueCard⟩ :=
      b1_intersecting_exceptional_shortPair_tight_data Item cost m2Chores first second third
        hfirst hsecond hthird hfirstNeSecond hmaximum hshortPair
    exact existsEfxOfB1IntersectingMaximum_tight_dispatch Item r cost prefixChores m2Chores a
      first second third surviving q hr hcost hprefixCard hprefixSmall hprefixM2 hfirst hsecond
      hthird hsurviving hfirstNeSecond hresidue hresidueCard hmaximum
  · exact existsEfxOfB1IntersectingMaximum_regular_dispatch Item r cost prefixChores m2Chores a
      first second third hr hcost hprefixCard hprefixSmall hprefixM2 hfirst hsecond hthird
      hfirstNeSecond hm2Small hmaximum hshortPair

end HT26EFXChores
