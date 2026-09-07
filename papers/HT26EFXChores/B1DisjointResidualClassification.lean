import HT26EFXChores.B1HighMultiplicityDispatch

/-!
# Residual classification for source Case B.2.1(b)

The disjoint two-fibre case deletes three chores from the dominant (0,1)
fibre.  This module identifies exactly when the exceptional M2 residue is not
already covered by the ordinary gap-fill schedules.

Source: EFXadditivechores.tex, lines 2420--2443.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- In source Case B.2.1(b), deleting three chores from the dominant
(0,1)-type fibre leaves an exceptional residue with auxiliary endpoints
(2,3), unless the original two fibre cardinalities are exactly (3,3) or
(4,3).  Those two small profiles are the direct-allocation leaves. -/
theorem b1_disjoint_exceptional_endpoints_or_small_profiles
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (first second third : Item)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second) (hfirstNeThird : first ≠ third)
    (hsecondNeThird : second ≠ third)
    (hcover : m2Chores =
      m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hsecondCardLe : (m2TypeChorePool cost m2Chores
      ({2, 3} : Finset (Fin 4))).card ≤
      (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hexceptional : IsM2Exceptional cost (m2Chores \ {first, second, third})) :
    IsM2ExceptionalWithEndpoints cost (m2Chores \ {first, second, third}) 2 3 ∨
      ((m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card = 3 ∧
        (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 3) ∨
      ((m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card = 4 ∧
        (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 3) := by
  classical
  let u := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let w := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  let gap : Finset Item := {first, second, third}
  let residue : Finset Item := m2Chores \ gap
  have hresidueDirect : residue = m2Chores \ {first, second, third} := by rfl
  have hfirstU : first ∈ u := by simpa [u] using hfirst
  have hsecondU : second ∈ u := by simpa [u] using hsecond
  have hthirdU : third ∈ u := by simpa [u] using hthird
  have hgapCard : gap.card = 3 := by
    simp [gap, hfirstNeSecond, hfirstNeThird, hsecondNeThird]
  have hgapSubsetU : gap ⊆ u := by
    intro item hitem
    simp only [gap, Finset.mem_insert, Finset.mem_singleton] at hitem
    rcases hitem with rfl | rfl | rfl
    · exact hfirstU
    · exact hsecondU
    · exact hthirdU
  have huSub : u ⊆ m2Chores := by
    intro item hitem
    exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp
      (by simpa [u] using hitem) |>.1
  have hcoverUW : m2Chores = u ∪ w := by simpa [u, w] using hcover
  have hwCardLe : w.card ≤ u.card := by simpa [u, w] using hsecondCardLe
  have huw : Disjoint u w := by
    simpa [u, w] using m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)
  have hresidueEq : residue = (u \ gap) ∪ w := by
    apply Finset.Subset.antisymm
    · intro item hitem
      obtain ⟨hitemM2, hitemNotGap⟩ := Finset.mem_sdiff.mp hitem
      rw [hcoverUW] at hitemM2
      rcases Finset.mem_union.mp hitemM2 with hitemU | hitemW
      · exact Finset.mem_union_left w (Finset.mem_sdiff.mpr ⟨hitemU, hitemNotGap⟩)
      · exact Finset.mem_union_right _ hitemW
    · intro item hitem
      rcases Finset.mem_union.mp hitem with hitemU | hitemW
      · exact Finset.mem_sdiff.mpr
          ⟨by rw [hcoverUW]; exact Finset.mem_union_left w (Finset.mem_sdiff.mp hitemU).1,
            (Finset.mem_sdiff.mp hitemU).2⟩
      · refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · rw [hcoverUW]
          exact Finset.mem_union_right u hitemW
        · intro hitemGap
          exact (Finset.disjoint_left.mp huw (hgapSubsetU hitemGap) hitemW).elim
  have hresidueUW : Disjoint (u \ gap) w :=
    Disjoint.mono Finset.sdiff_subset (by rfl) huw
  have hresidueCard : residue.card = u.card - 3 + w.card := by
    rw [hresidueEq, Finset.card_union_of_disjoint hresidueUW,
      Finset.card_sdiff_of_subset hgapSubsetU, hgapCard]
  have huCardGeThree : 3 ≤ u.card := by
    have hcard := Finset.card_le_card hgapSubsetU
    rw [hgapCard] at hcard
    exact hcard
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary,
      hdisjoint, hshape⟩
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
  by_cases huLarge : 5 ≤ u.card
  · rcases hshape with hfixed | hsingle
    · have hsurviving : ∃ item ∈ u, item ∉ gap := by
        by_contra hnone
        have hsubset : u ⊆ gap := by
          intro item hitem
          by_contra hnot
          exact hnone ⟨item, hitem, hnot⟩
        have hcard := Finset.card_le_card hsubset
        rw [hgapCard] at hcard
        omega
      obtain ⟨surviving, hsurvivingU, hsurvivingNotGap⟩ := hsurviving
      have hsurvivingResidue : surviving ∈ residue :=
        Finset.mem_sdiff.mpr ⟨huSub hsurvivingU, hsurvivingNotGap⟩
      have hsurvivingType : smallAgentSet cost surviving = ({0, 1} : Finset (Fin 4)) :=
        (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) surviving).mp
          (by simpa [u] using hsurvivingU) |>.2
      have hdominantEq : dominant = ({0, 1} : Finset (Fin 4)) :=
        (hfixed.1 surviving (by rw [← hresidueDirect]; exact hsurvivingResidue)).symm.trans
          hsurvivingType
      have hauxiliaryEq := hauxiliary_eq_23 hdominantEq
      left
      refine ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint, ?_, ?_,
        Or.inl hfixed⟩
      · simpa [hauxiliaryEq]
      · simpa [hauxiliaryEq]
    · obtain ⟨exceptionalItem, hexceptionalItem, hitemType, houtsideType,
          houtsideCard⟩ := hsingle
      have hlargeSetCard : (gap ∪ {exceptionalItem}).card ≤ 4 := by
        calc
          (gap ∪ {exceptionalItem}).card ≤ gap.card + ({exceptionalItem} : Finset Item).card :=
            Finset.card_union_le _ _
          _ = 4 := by rw [hgapCard]; simp
      have hsurviving : ∃ item ∈ u, item ∉ gap ∧ item ≠ exceptionalItem := by
        by_contra hnone
        have hsubset : u ⊆ gap ∪ {exceptionalItem} := by
          intro item hitem
          by_cases hitemGap : item ∈ gap
          · exact Finset.mem_union_left _ hitemGap
          · by_cases hitemExceptional : item = exceptionalItem
            · exact Finset.mem_union_right _ (by simp [hitemExceptional])
            · exact False.elim (hnone ⟨item, hitem, hitemGap, hitemExceptional⟩)
        have hcard := Finset.card_le_card hsubset
        omega
      obtain ⟨surviving, hsurvivingU, hsurvivingNotGap,
        hsurvivingNeExceptional⟩ := hsurviving
      have hsurvivingResidue : surviving ∈ residue :=
        Finset.mem_sdiff.mpr ⟨huSub hsurvivingU, hsurvivingNotGap⟩
      have hsurvivingErase : surviving ∈ residue.erase exceptionalItem :=
        Finset.mem_erase.mpr ⟨hsurvivingNeExceptional, hsurvivingResidue⟩
      have hsurvivingType : smallAgentSet cost surviving = ({0, 1} : Finset (Fin 4)) :=
        (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) surviving).mp
          (by simpa [u] using hsurvivingU) |>.2
      have hdominantEq : dominant = ({0, 1} : Finset (Fin 4)) :=
        (houtsideType surviving (by rw [← hresidueDirect]; exact hsurvivingErase)).symm.trans
          hsurvivingType
      have hauxiliaryEq := hauxiliary_eq_23 hdominantEq
      left
      refine ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint, ?_, ?_,
        Or.inr ⟨exceptionalItem, hexceptionalItem, hitemType, houtsideType, houtsideCard⟩⟩
      · simpa [hauxiliaryEq]
      · simpa [hauxiliaryEq]
  · have huCardLeFour : u.card ≤ 4 := by omega
    have huGapCard : (u \ gap).card = u.card - 3 := by
      rw [Finset.card_sdiff_of_subset hgapSubsetU, hgapCard]
    have hdominant_is_second :
        ∀ core : Finset Item, core ⊆ residue →
          (∀ item ∈ core, smallAgentSet cost item = dominant) →
          core.card = 4 * q + 3 →
          dominant = ({2, 3} : Finset (Fin 4)) ∧ 3 ≤ w.card := by
      intro core hcoreSub hcoreType hcoreCard
      have hcorePos : 0 < core.card := by rw [hcoreCard]; omega
      obtain ⟨item, hitem⟩ := Finset.card_pos.mp hcorePos
      have hitemResidue : item ∈ residue := hcoreSub hitem
      have hitemM2 : item ∈ m2Chores := Finset.sdiff_subset hitemResidue
      rw [hcoverUW] at hitemM2
      rcases Finset.mem_union.mp hitemM2 with hitemU | hitemW
      · have hdominantEq : dominant = ({0, 1} : Finset (Fin 4)) :=
          (hcoreType item hitem).symm.trans
            ((mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp
              (by simpa [u] using hitemU) |>.2)
        have hcoreSubU : core ⊆ u \ gap := by
          intro chore hchore
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · apply (mem_m2TypeChorePool cost m2Chores
              ({0, 1} : Finset (Fin 4)) chore).mpr
            refine ⟨Finset.sdiff_subset (hcoreSub hchore), ?_⟩
            calc
              smallAgentSet cost chore = dominant := hcoreType chore hchore
              _ = ({0, 1} : Finset (Fin 4)) := hdominantEq
          · exact (Finset.mem_sdiff.mp (hcoreSub hchore)).2
        have hcard := Finset.card_le_card hcoreSubU
        rw [hcoreCard, huGapCard] at hcard
        omega
      · have hdominantEq : dominant = ({2, 3} : Finset (Fin 4)) :=
          (hcoreType item hitem).symm.trans
            ((mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mp
              (by simpa [w] using hitemW) |>.2)
        have hcoreSubW : core ⊆ w := by
          intro chore hchore
          apply (mem_m2TypeChorePool cost m2Chores
            ({2, 3} : Finset (Fin 4)) chore).mpr
          refine ⟨Finset.sdiff_subset (hcoreSub hchore), ?_⟩
          calc
            smallAgentSet cost chore = dominant := hcoreType chore hchore
            _ = ({2, 3} : Finset (Fin 4)) := hdominantEq
        refine ⟨hdominantEq, ?_⟩
        have hcard := Finset.card_le_card hcoreSubW
        rw [hcoreCard] at hcard
        omega
    rcases hshape with hfixed | hsingle
    · obtain ⟨_hdominantEq, hwCardGeThree⟩ :=
        hdominant_is_second residue (by rfl) hfixed.1 hfixed.2
      have hresidueBound : residue.card ≤ 5 := by
        rw [hresidueCard]
        omega
      have hresidueCardThree : residue.card = 3 := by
        rw [hfixed.2] at hresidueBound ⊢
        omega
      rw [hresidueCard] at hresidueCardThree
      have huCardThree : u.card = 3 := by omega
      have hwCardThree : w.card = 3 := by omega
      right
      left
      exact ⟨by simpa [u] using huCardThree, by simpa [w] using hwCardThree⟩
    · obtain ⟨exceptionalItem, hexceptionalItem, hitemType, houtsideType,
          houtsideCard⟩ := hsingle
      obtain ⟨_hdominantEq, hwCardGeThree⟩ :=
        hdominant_is_second (residue.erase exceptionalItem)
          (Finset.erase_subset exceptionalItem residue) houtsideType houtsideCard
      have hresidueBound : residue.card ≤ 5 := by
        rw [hresidueCard]
        omega
      have heraseCard : (residue.erase exceptionalItem).card + 1 = residue.card :=
        Finset.card_erase_add_one hexceptionalItem
      have hqZero : q = 0 := by
        rw [← heraseCard, houtsideCard] at hresidueBound
        omega
      have hresidueCardFour : residue.card = 4 := by
        calc
          residue.card = (residue.erase exceptionalItem).card + 1 := heraseCard.symm
          _ = 4 * q + 3 + 1 := by rw [houtsideCard]
          _ = 4 := by rw [hqZero]
      rw [hresidueCard] at hresidueCardFour
      have huCardFour : u.card = 4 := by omega
      have hwCardThree : w.card = 3 := by omega
      right
      right
      exact ⟨by simpa [u] using huCardFour, by simpa [w] using hwCardThree⟩

end HT26EFXChores
