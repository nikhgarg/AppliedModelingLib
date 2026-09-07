import HT26EFXChores.B2SimpleGraphAllocation
import HT26EFXChores.B2ZeroCornerAllocation

/-!
# Source-to-model dispatch for the maximum-multiplicity b = 2 branch

This module begins the remaining Case B.3.1 bridge.  After removing two
chores from a maximum type `(0,1)`, an exceptional residual can have auxiliary
endpoints only `(0,1)` or `(2,3)`.  This is the finite type argument used by
the source before selecting its long-pair or tight direct schedule.

Source: `EFXadditivechores.tex`, lines 2615--2640.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- In the parallel-edge branch, an exceptional residual has auxiliary
endpoints either at the gap-filled short pair or at the complementary long
pair.  The maximum-multiplicity hypothesis is used to retain a surviving
type-`(0,1)` chore in the residue. -/
theorem b2_parallel_exceptional_auxiliary_pair
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (first second : Item)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hexceptional : IsM2Exceptional cost (m2Chores \ {first, second})) :
    IsM2ExceptionalWithEndpoints cost (m2Chores \ {first, second}) 0 1 ∨
      IsM2ExceptionalWithEndpoints cost (m2Chores \ {first, second}) 2 3 := by
  let residue := m2Chores \ {first, second}
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
  obtain ⟨surviving, hsurvivingType, hsurvivingNotGap⟩ := hsurviving
  have hsurvivingResidue : surviving ∈ residue := by
    refine Finset.mem_sdiff.mpr ⟨?_, hsurvivingNotGap⟩
    exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) surviving).mp
      (by simpa [firstType] using hsurvivingType) |>.1
  have hsurvivingSmall : smallAgentSet cost surviving = ({0, 1} : Finset (Fin 4)) :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) surviving).mp
      (by simpa [firstType] using hsurvivingType) |>.2
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

/-- When the exceptional endpoints are the original parallel type, the
fixed-fibre exceptional shape would leave at least three complementary chores
while the maximum type has only the two removed chores.  Thus the residual is
the source's tight configuration: one surviving parallel chore and a
three-modulo-four complementary fibre. -/
theorem b2_parallel_exceptional_shortPair_tight_data
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (first second : Item)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hexceptional : IsM2ExceptionalWithEndpoints cost (m2Chores \ {first, second}) 0 1) :
    ∃ surviving q, surviving ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∧
      m2Chores \ {first, second} = {surviving} ∪
        m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) ∧
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 4 * q + 3 := by
  let residue := m2Chores \ {first, second}
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
    obtain ⟨surviving, hsurvivingType, hsurvivingNotGap⟩ := hsurviving
    have hsurvivingResidue : surviving ∈ residue := by
      refine Finset.mem_sdiff.mpr ⟨?_, hsurvivingNotGap⟩
      exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) surviving).mp
        (by simpa [firstType] using hsurvivingType) |>.1
    have hsurvivingSmall : smallAgentSet cost surviving = ({0, 1} : Finset (Fin 4)) :=
      (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) surviving).mp
        (by simpa [firstType] using hsurvivingType) |>.2
    have hcontradiction : ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by
      have hsurvivingDominant : smallAgentSet cost surviving = ({2, 3} : Finset (Fin 4)) := by
        simpa [hdominantEq] using hfixed.1 surviving (by simpa [residue] using hsurvivingResidue)
      exact hsurvivingDominant.symm.trans hsurvivingSmall
    exact False.elim ((by decide : ({2, 3} : Finset (Fin 4)) ≠ ({0, 1} : Finset (Fin 4)))
      hcontradiction)
  · obtain ⟨surviving, hsurvivingResidue, hsurvivingType, houtsideType,
      houtsideCard⟩ := hsingle
    change surviving ∈ m2Chores \ ({first, second} : Finset Item) at hsurvivingResidue
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
            rcases hEq with rfl | rfl
            · exact (Finset.disjoint_left.mp
                (m2TypeChorePool_disjoint_of_ne cost m2Chores
                  ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide))
                (by simpa [firstType] using hfirst) hitem).elim
            · exact (Finset.disjoint_left.mp
                (m2TypeChorePool_disjoint_of_ne cost m2Chores
                  ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide))
                (by simpa [firstType] using hsecond) hitem).elim
    refine ⟨surviving, q, (by simpa [firstType] using hsurvivingFirstType), ?_, ?_⟩
    · change residue = {surviving} ∪ secondType
      calc
        residue = insert surviving (residue.erase surviving) :=
          (Finset.insert_erase (show surviving ∈ residue from hsurvivingResidue)).symm
        _ = {surviving} ∪ secondType := by rw [heraseEq]; simp
    · change secondType.card = 4 * q + 3
      rw [← heraseEq]
      simpa [residue] using houtsideCard

/-- The positive-`a` maximum-multiplicity branch of source Case B.3.1.
The ordinary gap-fill route handles nonexceptional and long-pair residues.
For the short-pair exceptional residue, the preceding bridge gives the tight
two-fibre instance; source Lemma `canonical`(c) supplies one short agent in
each fibre, and a pair-preserving relabelling invokes the direct schedule. -/
theorem existsEfxOfB2MaximumMultiplicity_positive
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (ha : 0 < a) (hprefixCard : prefixChores.card = 4 * a + 2)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let standardQuota : Fin 4 → ℕ := canonicalQuota a ({2, 3} : Finset (Fin 4))
  have hstandardQuotaSum : Finset.univ.sum standardQuota = prefixChores.card := by
    rw [show standardQuota = canonicalQuota a ({2, 3} : Finset (Fin 4)) by rfl,
      canonicalQuota_sum, hprefixCard]
    congr 1
  obtain ⟨standardAllocation, hstandardCanonical⟩ :=
    existsCanonicalSmallChoreAllocation Item cost prefixChores standardQuota
      hstandardQuotaSum hprefixSmall
  have hstandardQuota0 : standardQuota 0 = a := by simp [standardQuota, canonicalQuota]
  have hstandardQuota1 : standardQuota 1 = a := by simp [standardQuota, canonicalQuota]
  have hstandardQuota2 : standardQuota 2 = a + 1 := by simp [standardQuota, canonicalQuota]
  have hstandardQuota3 : standardQuota 3 = a + 1 := by simp [standardQuota, canonicalQuota]
  by_cases hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {first, second})
  · exact existsEfxOfB2_parallelShortEndpoints_nonexceptional Item r cost prefixChores
      m2Chores a standardQuota standardAllocation first second hr hcost hprefixM2
      hstandardCanonical hstandardQuota0 hstandardQuota1 hstandardQuota2 hstandardQuota3
      hfirst hsecond hfirstNeSecond hm2Small hnotExceptional
  have hexceptional : IsM2Exceptional cost (m2Chores \ {first, second}) := by
    exact not_not.mp hnotExceptional
  rcases b2_parallel_exceptional_auxiliary_pair Item cost m2Chores first second hfirst hsecond
    hfirstNeSecond hmaximum hexceptional with hshortPair | hlongPair
  · obtain ⟨surviving, q, hsurviving, hresidue, hsecondCardFormula⟩ :=
      b2_parallel_exceptional_shortPair_tight_data Item cost m2Chores first second hfirst hsecond
        hfirstNeSecond hmaximum hshortPair
    let firstType := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
    let secondType := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
    have hfirstSubset : firstType ⊆ m2Chores := by
      intro item hitem
      exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp
        (by simpa [firstType] using hitem) |>.1
    have hsecondSubset : secondType ⊆ m2Chores := by
      intro item hitem
      exact (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mp
        (by simpa [secondType] using hitem) |>.1
    have htypesDisjoint : Disjoint firstType secondType := by
      simpa [firstType, secondType] using m2TypeChorePool_disjoint_of_ne cost m2Chores
        ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)
    obtain ⟨hcover, hfirstCard, hsecondCard⟩ :=
      b2_parallel_exceptional_forces_33 Item m2Chores firstType secondType first second surviving q
        hfirstSubset hsecondSubset htypesDisjoint (by simpa [firstType] using hfirst)
        (by simpa [firstType] using hsecond) (by simpa [firstType] using hsurviving)
        hfirstNeSecond (by simpa [firstType, secondType] using hresidue)
        (by simpa [secondType] using hsecondCardFormula)
        (by simpa [firstType, secondType] using hmaximum ({2, 3}))
    obtain ⟨i, hi, j, hj, quota, prefixAllocation, hquota, hcanonical, hsuper, hquotaI,
      hquotaJ⟩ := existsSuperCanonicalOneShortEachSide Item r cost prefixChores a ha
        (by linarith) hcost hprefixCard hprefixSmall ({0, 1} : Finset (Fin 4))
        ({2, 3} : Finset (Fin 4)) (by decide) (by decide) (by decide) (by decide)
    have hquotaSum : Finset.univ.sum quota = 4 * a + 2 := by
      calc
        Finset.univ.sum quota = Finset.univ.sum (fun agent => (prefixAllocation agent).card) := by
          apply Finset.sum_congr rfl
          intro agent _
          symm
          exact (hcanonical.2 agent).1
        _ = prefixChores.card :=
          sum_card_allocation_eq_card_of_isAllocation prefixAllocation prefixChores hcanonical.1
        _ = 4 * a + 2 := hprefixCard
    have hTight : ∀ labels : Fin 4 ≃ Fin 4,
        ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = ({0, 1} : Finset (Fin 4)) →
        ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = ({2, 3} : Finset (Fin 4)) →
        quota (labels 0) = a + 1 → quota (labels 1) = a →
        quota (labels 2) = a + 1 → quota (labels 3) = a →
        ∃ allocation : Allocation (Fin 4) Item,
          IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
            EFXForChores (additiveChoreCost cost) allocation := by
      intro labels hlabels01 hlabels23 hquota0 hquota1 hquota2 hquota3
      apply existsEfxOfB2TightExceptionalDirect_of_relabelled_typePools Item r cost labels
        prefixChores m2Chores a quota prefixAllocation hr hcost hprefixM2 hcanonical
      · exact hquota0
      · exact hquota1
      · exact hquota2
      · exact hquota3
      · exact hsuper
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)),
          m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)),
          hlabels01, hlabels23]
        simpa [firstType, secondType] using hcover
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hlabels01]
        simpa [firstType] using hfirstCard
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hlabels23]
        simpa [secondType] using hsecondCard
    rcases (by simpa using hi : i = 0 ∨ i = 1) with rfl | rfl
    · rcases (by simpa using hj : j = 2 ∨ j = 3) with rfl | rfl
      · let labels : Fin 4 ≃ Fin 4 := (Equiv.swap 0 1).trans (Equiv.swap 2 3)
        obtain ⟨hquotaOne, hquotaThree⟩ :=
          b2_remaining_quotas_are_long a quota hquota hquotaSum hquotaI hquotaJ
        apply hTight labels (by decide) (by decide)
        · simpa [labels] using hquotaOne
        · simpa [labels] using hquotaI
        · simpa [labels] using hquotaThree
        · simpa [labels] using hquotaJ
      · let labels : Fin 4 ≃ Fin 4 := Equiv.swap 0 1
        let bookkeeping : Fin 4 ≃ Fin 4 := Equiv.swap 2 3
        have hbookkeepingSum : Finset.univ.sum (relabelQuota bookkeeping quota) = 4 * a + 2 := by
          simpa [bookkeeping, relabelQuota, Fin.sum_univ_four, Equiv.swap_apply_def,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hquotaSum
        obtain ⟨hquotaOne, hquotaTwo⟩ :=
          b2_remaining_quotas_are_long a (relabelQuota bookkeeping quota)
            (fun agent => by simpa [relabelQuota] using hquota (bookkeeping agent))
            hbookkeepingSum (by simpa [bookkeeping, relabelQuota] using hquotaI)
            (by simpa [bookkeeping, relabelQuota] using hquotaJ)
        apply hTight labels (by decide) (by decide)
        · simpa [labels] using hquotaOne
        · simpa [labels] using hquotaI
        · simpa [labels, bookkeeping, relabelQuota] using hquotaTwo
        · simpa [labels] using hquotaJ
    · rcases (by simpa using hj : j = 2 ∨ j = 3) with rfl | rfl
      · let labels : Fin 4 ≃ Fin 4 := Equiv.swap 2 3
        let bookkeeping : Fin 4 ≃ Fin 4 := Equiv.swap 0 1
        have hbookkeepingSum : Finset.univ.sum (relabelQuota bookkeeping quota) = 4 * a + 2 := by
          simpa [bookkeeping, relabelQuota, Fin.sum_univ_four, Equiv.swap_apply_def,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hquotaSum
        obtain ⟨hquotaZero, hquotaThree⟩ :=
          b2_remaining_quotas_are_long a (relabelQuota bookkeeping quota)
            (fun agent => by simpa [relabelQuota] using hquota (bookkeeping agent))
            hbookkeepingSum (by simpa [bookkeeping, relabelQuota] using hquotaI)
            (by simpa [bookkeeping, relabelQuota] using hquotaJ)
        apply hTight labels (by decide) (by decide)
        · simpa [labels, bookkeeping, relabelQuota] using hquotaZero
        · simpa [labels] using hquotaI
        · simpa [labels] using hquotaThree
        · simpa [labels] using hquotaJ
      · let bookkeeping : Fin 4 ≃ Fin 4 := (Equiv.swap 0 1).trans (Equiv.swap 2 3)
        have hbookkeepingSum : Finset.univ.sum (relabelQuota bookkeeping quota) = 4 * a + 2 := by
          simpa [bookkeeping, relabelQuota, Fin.sum_univ_four, Equiv.swap_apply_def,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hquotaSum
        obtain ⟨hquotaZero, hquotaTwo⟩ :=
          b2_remaining_quotas_are_long a (relabelQuota bookkeeping quota)
            (fun agent => by simpa [relabelQuota] using hquota (bookkeeping agent))
            hbookkeepingSum (by simpa [bookkeeping, relabelQuota] using hquotaI)
            (by simpa [bookkeeping, relabelQuota] using hquotaJ)
        apply hTight (Equiv.refl (Fin 4)) (by decide) (by decide)
        · simpa [bookkeeping, relabelQuota] using hquotaZero
        · exact hquotaI
        · simpa [bookkeeping, relabelQuota] using hquotaTwo
        · exact hquotaJ
  · exact existsEfxOfB2_parallelShortEndpoints_exceptional_longPair Item r cost prefixChores
      m2Chores a standardQuota standardAllocation first second hr hcost hprefixM2 hprefixSmall
      hstandardCanonical hstandardQuota0 hstandardQuota1 hstandardQuota2 hstandardQuota3
      hfirst hsecond hfirstNeSecond hlongPair

/-- The literal hard corner of source Case B.3.1 for `a = 0`, derived from
the two M01 chores' small-agent sets.  The prefix chores are respectively
small only for the two endpoints of one tight M₂ fibre; assigning them to
those endpoints instantiates the compiled `2:1` suffix schedule. -/
theorem existsEfxOfB2MaximumMultiplicity_zeroCorner_of_smallAgentSets
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (firstPrefix secondPrefix : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefix : prefixChores = {firstPrefix, secondPrefix})
    (hprefixNe : firstPrefix ≠ secondPrefix)
    (hfirstSmall : smallAgentSet cost firstPrefix = ({0} : Finset (Fin 4)))
    (hsecondSmall : smallAgentSet cost secondPrefix = ({1} : Finset (Fin 4)))
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcover : m2Chores =
      m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hfirstCard : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card = 3)
    (hsecondCard : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let firstAllocation : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 {firstPrefix}
  let secondAllocation : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 1 {secondPrefix}
  let prefixAllocation : Allocation (Fin 4) Item := fun agent =>
    firstAllocation agent ∪ secondAllocation agent
  have hpairsDisjoint : Disjoint ({firstPrefix} : Finset Item) {secondPrefix} := by
    rw [Finset.disjoint_singleton_left]
    simpa [eq_comm] using hprefixNe
  have hprefixAllocation : IsAllocationOf prefixAllocation prefixChores := by
    rw [hprefix]
    simpa [prefixAllocation] using isAllocationOf_union firstAllocation secondAllocation
      {firstPrefix} {secondPrefix} hpairsDisjoint
      (isAllocationOf_allocateAllTo 0 {firstPrefix})
      (isAllocationOf_allocateAllTo 1 {secondPrefix})
  have hprefixZero : prefixAllocation 0 = {firstPrefix} := by
    simp [prefixAllocation, firstAllocation, secondAllocation, allocateAllTo]
  have hprefixOne : prefixAllocation 1 = {secondPrefix} := by
    simp [prefixAllocation, firstAllocation, secondAllocation, allocateAllTo]
  have hprefixTwo : prefixAllocation 2 = ∅ := by
    simp [prefixAllocation, firstAllocation, secondAllocation, allocateAllTo]
  have hprefixThree : prefixAllocation 3 = ∅ := by
    simp [prefixAllocation, firstAllocation, secondAllocation, allocateAllTo]
  have hsmallCost (item : Item) (agent : Fin 4) (hmem : agent ∈ smallAgentSet cost item) :
      cost agent item = 1 := by
    simpa [smallAgentSet, IsSmallChore] using hmem
  have hlargeCost (item : Item) (agent : Fin 4) (hnot : agent ∉ smallAgentSet cost item) :
      cost agent item = r := by
    rcases hcost agent item with hsmall | hlarge
    · exact (hnot (by simpa [smallAgentSet, IsSmallChore] using hsmall)).elim
    · exact hlarge
  have hfirstCosts : cost 0 firstPrefix = 1 ∧ cost 1 firstPrefix = r ∧
      cost 2 firstPrefix = r ∧ cost 3 firstPrefix = r := by
    refine ⟨hsmallCost firstPrefix 0 (by rw [hfirstSmall]; simp),
      hlargeCost firstPrefix 1 (by rw [hfirstSmall]; simp),
      hlargeCost firstPrefix 2 (by rw [hfirstSmall]; simp),
      hlargeCost firstPrefix 3 (by rw [hfirstSmall]; simp)⟩
  have hsecondCosts : cost 0 secondPrefix = r ∧ cost 1 secondPrefix = 1 ∧
      cost 2 secondPrefix = r ∧ cost 3 secondPrefix = r := by
    refine ⟨hlargeCost secondPrefix 0 (by rw [hsecondSmall]; simp),
      hsmallCost secondPrefix 1 (by rw [hsecondSmall]; simp),
      hlargeCost secondPrefix 2 (by rw [hsecondSmall]; simp),
      hlargeCost secondPrefix 3 (by rw [hsecondSmall]; simp)⟩
  apply existsEfxOfB2ZeroCornerDirect Item r cost prefixChores m2Chores
    (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    firstPrefix secondPrefix prefixAllocation hr hcost hprefixM2 hprefixAllocation hprefixZero
    hprefixOne hprefixTwo hprefixThree hfirstCosts hsecondCosts hcover
  · exact m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)
  · exact hfirstCard
  · exact hsecondCard
  · intro item hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({0, 1} : Finset (Fin 4)) item 0 hitem (by decide)
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({0, 1} : Finset (Fin 4)) item 1 hitem (by decide)
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({0, 1} : Finset (Fin 4)) item 2 hcost hitem (by decide)
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({0, 1} : Finset (Fin 4)) item 3 hcost hitem (by decide)
  · intro item hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 0 hcost hitem (by decide)
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 1 hcost hitem (by decide)
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 2 hitem (by decide)
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 3 hitem (by decide)

/-- For two M01 chores, either one can select a short agent from each
complementary M₂ pair that finds both chores large, or the two uniquely-small
agents exhaust one of those pairs.  The latter alternatives are exactly the
two source zero-prefix corners (up to swapping the two prefix chores). -/
theorem b2_zero_prefix_cross_or_samePair
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (firstPrefix secondPrefix : Item)
    (hfirst : IsSmallForAtMostOne cost firstPrefix)
    (hsecond : IsSmallForAtMostOne cost secondPrefix) :
    (∃ firstShort ∈ ({0, 1} : Finset (Fin 4)),
      ∃ secondShort ∈ ({2, 3} : Finset (Fin 4)),
        firstShort ∉ smallAgentSet cost firstPrefix ∧
          secondShort ∉ smallAgentSet cost firstPrefix ∧
          firstShort ∉ smallAgentSet cost secondPrefix ∧
          secondShort ∉ smallAgentSet cost secondPrefix) ∨
      (smallAgentSet cost firstPrefix = ({0} : Finset (Fin 4)) ∧
        smallAgentSet cost secondPrefix = ({1} : Finset (Fin 4))) ∨
      (smallAgentSet cost firstPrefix = ({1} : Finset (Fin 4)) ∧
        smallAgentSet cost secondPrefix = ({0} : Finset (Fin 4))) ∨
      (smallAgentSet cost firstPrefix = ({2} : Finset (Fin 4)) ∧
        smallAgentSet cost secondPrefix = ({3} : Finset (Fin 4))) ∨
      (smallAgentSet cost firstPrefix = ({3} : Finset (Fin 4)) ∧
        smallAgentSet cost secondPrefix = ({2} : Finset (Fin 4))) := by
  classical
  have hshape : ∀ smallAgents : Finset (Fin 4), smallAgents.card ≤ 1 →
      smallAgents = ∅ ∨ ∃ agent, smallAgents = {agent} := by
    intro smallAgents hcard
    by_cases hempty : smallAgents = ∅
    · exact Or.inl hempty
    · right
      have hpositive : 0 < smallAgents.card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
      have hcardOne : smallAgents.card = 1 := by omega
      exact Finset.card_eq_one.mp hcardOne
  rcases hshape (smallAgentSet cost firstPrefix) hfirst with hfirstEmpty | ⟨firstAgent, hfirstEq⟩
  · rcases hshape (smallAgentSet cost secondPrefix) hsecond with hsecondEmpty | ⟨secondAgent, hsecondEq⟩
    · left
      exact ⟨0, by simp, 2, by simp, by simp [hfirstEmpty], by simp [hfirstEmpty],
        by simp [hsecondEmpty], by simp [hsecondEmpty]⟩
    · left
      fin_cases secondAgent
      · exact ⟨1, by simp, 2, by simp, by simp [hfirstEmpty], by simp [hfirstEmpty],
          by simp [hsecondEq], by simp [hsecondEq]⟩
      · exact ⟨0, by simp, 2, by simp, by simp [hfirstEmpty], by simp [hfirstEmpty],
          by simp [hsecondEq], by simp [hsecondEq]⟩
      · exact ⟨0, by simp, 3, by simp, by simp [hfirstEmpty], by simp [hfirstEmpty],
          by simp [hsecondEq], by simp [hsecondEq]⟩
      · exact ⟨0, by simp, 2, by simp, by simp [hfirstEmpty], by simp [hfirstEmpty],
          by simp [hsecondEq], by simp [hsecondEq]⟩
  · rcases hshape (smallAgentSet cost secondPrefix) hsecond with hsecondEmpty | ⟨secondAgent, hsecondEq⟩
    · left
      fin_cases firstAgent
      · exact ⟨1, by simp, 2, by simp, by simp [hfirstEq], by simp [hfirstEq],
          by simp [hsecondEmpty], by simp [hsecondEmpty]⟩
      · exact ⟨0, by simp, 2, by simp, by simp [hfirstEq], by simp [hfirstEq],
          by simp [hsecondEmpty], by simp [hsecondEmpty]⟩
      · exact ⟨0, by simp, 3, by simp, by simp [hfirstEq], by simp [hfirstEq],
          by simp [hsecondEmpty], by simp [hsecondEmpty]⟩
      · exact ⟨0, by simp, 2, by simp, by simp [hfirstEq], by simp [hfirstEq],
          by simp [hsecondEmpty], by simp [hsecondEmpty]⟩
    · fin_cases firstAgent <;> fin_cases secondAgent <;>
        simp [hfirstEq, hsecondEq]

/-- The cross-pair alternative of `b2_zero_prefix_cross_or_samePair` supplies
the super-canonical prefix used by the source before the hard zero corner.
Both selected short agents have no own-small prefix chore, so the general
short-light construction applies with `a = 0`. -/
theorem existsSuperCanonicalB2ZeroPrefix_cross
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores : Finset Item) (firstPrefix secondPrefix : Item)
    (firstShort secondShort : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefix : prefixChores = {firstPrefix, secondPrefix})
    (hprefixNe : firstPrefix ≠ secondPrefix)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hfirstShort : firstShort ∈ ({0, 1} : Finset (Fin 4)))
    (hsecondShort : secondShort ∈ ({2, 3} : Finset (Fin 4)))
    (hcross : firstShort ∉ smallAgentSet cost firstPrefix ∧
      secondShort ∉ smallAgentSet cost firstPrefix ∧
      firstShort ∉ smallAgentSet cost secondPrefix ∧
      secondShort ∉ smallAgentSet cost secondPrefix) :
    ∃ allocation,
      IsCanonicalSmallChoreAllocation cost prefixChores
        (canonicalQuota 0 (Finset.univ \ {firstShort, secondShort})) allocation ∧
      ∀ short long,
        canonicalQuota 0 (Finset.univ \ {firstShort, secondShort}) short = 0 →
        canonicalQuota 0 (Finset.univ \ {firstShort, secondShort}) long = 0 + 1 →
        additiveChoreCost cost short (allocation short) ≤
          additiveChoreCost cost short (allocation long) - r := by
  classical
  have hshortDistinct : firstShort ≠ secondShort := by
    intro hEq
    subst secondShort
    exact (Finset.disjoint_left.mp (by decide :
      Disjoint ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4))) hfirstShort hsecondShort).elim
  have hprefixCard : prefixChores.card = 4 * 0 + 2 := by
    rw [hprefix]
    simp [hprefixNe]
  have hshortCard : ({firstShort, secondShort} : Finset (Fin 4)).card = 4 - 2 := by
    simp [hshortDistinct]
  have hshortLight : ∀ agent ∈ ({firstShort, secondShort} : Finset (Fin 4)),
      (ownSmallChoreSet cost prefixChores agent).card ≤ 2 * 0 := by
    intro agent hagent
    have hempty : ownSmallChoreSet cost prefixChores agent = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨item, hitem⟩
      obtain ⟨hitemPrefix, hitemSmall⟩ := Finset.mem_filter.mp hitem
      have hagentCases : agent = firstShort ∨ agent = secondShort := by
        simpa using hagent
      have hitemCases : item = firstPrefix ∨ item = secondPrefix := by
        rw [hprefix] at hitemPrefix
        simpa using hitemPrefix
      rcases hagentCases with rfl | rfl <;> rcases hitemCases with rfl | rfl
      · exact hcross.1 (by simpa [smallAgentSet, IsSmallChore] using hitemSmall)
      · exact hcross.2.2.1 (by simpa [smallAgentSet, IsSmallChore] using hitemSmall)
      · exact hcross.2.1 (by simpa [smallAgentSet, IsSmallChore] using hitemSmall)
      · exact hcross.2.2.2 (by simpa [smallAgentSet, IsSmallChore] using hitemSmall)
    rw [hempty]
    norm_num
  exact existsSuperCanonicalOfShortLight Item r cost prefixChores
    ({firstShort, secondShort} : Finset (Fin 4))
    (Finset.univ \ {firstShort, secondShort}) 0 2 (by linarith) hcost (by omega)
    hprefixSmall hprefixCard rfl hshortCard hshortLight

/-- In the cross-pair zero-prefix alternative, the super-canonical prefix and
the tight two-fibre suffix combine through the same pair-preserving relabelling
used in the positive-`a` branch. -/
theorem existsEfxOfB2TightExceptional_zero_cross
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (firstPrefix secondPrefix : Item)
    (firstShort secondShort : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefix : prefixChores = {firstPrefix, secondPrefix})
    (hprefixNe : firstPrefix ≠ secondPrefix)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hfirstShort : firstShort ∈ ({0, 1} : Finset (Fin 4)))
    (hsecondShort : secondShort ∈ ({2, 3} : Finset (Fin 4)))
    (hcross : firstShort ∉ smallAgentSet cost firstPrefix ∧
      secondShort ∉ smallAgentSet cost firstPrefix ∧
      firstShort ∉ smallAgentSet cost secondPrefix ∧
      secondShort ∉ smallAgentSet cost secondPrefix)
    (hcover : m2Chores =
      m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hfirstCard : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card = 3)
    (hsecondCard : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨prefixAllocation, hcanonical, hsuper⟩ :=
    existsSuperCanonicalB2ZeroPrefix_cross Item r cost prefixChores firstPrefix secondPrefix
      firstShort secondShort hr hcost hprefix hprefixNe hprefixSmall hfirstShort hsecondShort hcross
  rcases (by simpa using hfirstShort : firstShort = 0 ∨ firstShort = 1) with rfl | rfl
  · rcases (by simpa using hsecondShort : secondShort = 2 ∨ secondShort = 3) with rfl | rfl
    · let labels : Fin 4 ≃ Fin 4 := (Equiv.swap 0 1).trans (Equiv.swap 2 3)
      have hmap01 : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = {0, 1} := by decide
      have hmap23 : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = {2, 3} := by decide
      apply existsEfxOfB2TightExceptionalDirect_of_relabelled_typePools Item r cost labels
        prefixChores m2Chores 0 (canonicalQuota 0 (Finset.univ \ ({0, 2} : Finset (Fin 4))))
        prefixAllocation hr hcost hprefixM2 hcanonical
      · simp [labels, canonicalQuota, Equiv.swap_apply_def]
      · simp [labels, canonicalQuota, Equiv.swap_apply_def]
      · simp [labels, canonicalQuota, Equiv.swap_apply_def]
      · simp [labels, canonicalQuota, Equiv.swap_apply_def]
      · exact hsuper
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)),
          m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmap01, hmap23]
        exact hcover
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4))]
        rw [hmap01]
        exact hfirstCard
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4))]
        rw [hmap23]
        exact hsecondCard
    · let labels : Fin 4 ≃ Fin 4 := Equiv.swap 0 1
      have hmap01 : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = {0, 1} := by decide
      have hmap23 : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = {2, 3} := by decide
      apply existsEfxOfB2TightExceptionalDirect_of_relabelled_typePools Item r cost labels
        prefixChores m2Chores 0 (canonicalQuota 0 (Finset.univ \ ({0, 3} : Finset (Fin 4))))
        prefixAllocation hr hcost hprefixM2 hcanonical
      · simp [labels, canonicalQuota, Equiv.swap_apply_def]
      · simp [labels, canonicalQuota, Equiv.swap_apply_def]
      · simp [labels, canonicalQuota, Equiv.swap_apply_def]
      · simp [labels, canonicalQuota, Equiv.swap_apply_def]
      · exact hsuper
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)),
          m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmap01, hmap23]
        exact hcover
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4))]
        rw [hmap01]
        exact hfirstCard
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4))]
        simpa [labels, Equiv.swap_apply_def, Finset.insert_comm] using hsecondCard
  · rcases (by simpa using hsecondShort : secondShort = 2 ∨ secondShort = 3) with rfl | rfl
    · let labels : Fin 4 ≃ Fin 4 := Equiv.swap 2 3
      have hmap01 : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = {0, 1} := by decide
      have hmap23 : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = {2, 3} := by decide
      apply existsEfxOfB2TightExceptionalDirect_of_relabelled_typePools Item r cost labels
        prefixChores m2Chores 0 (canonicalQuota 0 (Finset.univ \ ({1, 2} : Finset (Fin 4))))
        prefixAllocation hr hcost hprefixM2 hcanonical
      · simp [labels, canonicalQuota, Equiv.swap_apply_def]
      · simp [labels, canonicalQuota, Equiv.swap_apply_def]
      · simp [labels, canonicalQuota, Equiv.swap_apply_def]
      · simp [labels, canonicalQuota, Equiv.swap_apply_def]
      · exact hsuper
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)),
          m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmap01, hmap23]
        exact hcover
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4))]
        simpa [labels, Equiv.swap_apply_def, Finset.insert_comm] using hfirstCard
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4))]
        rw [hmap23]
        exact hsecondCard
    · apply existsEfxOfB2TightExceptionalDirect_of_relabelled_typePools Item r cost
        (Equiv.refl (Fin 4)) prefixChores m2Chores 0
        (canonicalQuota 0 (Finset.univ \ ({1, 3} : Finset (Fin 4)))) prefixAllocation
        hr hcost hprefixM2 hcanonical
      · simp [canonicalQuota]
      · simp [canonicalQuota]
      · simp [canonicalQuota]
      · simp [canonicalQuota]
      · exact hsuper
      · simpa using hcover
      · simpa using hfirstCard
      · simpa using hsecondCard

/-- Complete zero-prefix dispatch for the tight maximum-multiplicity residue.
The finite two-chore classification either gives the cross super-canonical
prefix or one of the two same-pair corners; swapping complementary endpoint
pairs transports the latter direct schedule to the symmetric corners. -/
theorem existsEfxOfB2TightExceptional_zero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (firstPrefix secondPrefix : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefix : prefixChores = {firstPrefix, secondPrefix})
    (hprefixNe : firstPrefix ≠ secondPrefix)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcover : m2Chores =
      m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hfirstCard : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card = 3)
    (hsecondCard : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  have hfirstM01 : IsSmallForAtMostOne cost firstPrefix := by
    apply hprefixSmall firstPrefix
    rw [hprefix]
    simp
  have hsecondM01 : IsSmallForAtMostOne cost secondPrefix := by
    apply hprefixSmall secondPrefix
    rw [hprefix]
    simp
  rcases b2_zero_prefix_cross_or_samePair Item cost firstPrefix secondPrefix hfirstM01 hsecondM01
    with hcross | h01 | h10 | h23 | h32
  · obtain ⟨firstShort, hfirstShort, secondShort, hsecondShort, hcross⟩ := hcross
    exact existsEfxOfB2TightExceptional_zero_cross Item r cost prefixChores m2Chores
      firstPrefix secondPrefix firstShort secondShort hr hcost hprefix hprefixNe hprefixSmall
      hprefixM2 hfirstShort hsecondShort hcross hcover hfirstCard hsecondCard
  · exact existsEfxOfB2MaximumMultiplicity_zeroCorner_of_smallAgentSets Item r cost
      prefixChores m2Chores firstPrefix secondPrefix hr hcost hprefix hprefixNe h01.1 h01.2
      hprefixM2 hcover hfirstCard hsecondCard
  · apply existsEfxOfB2MaximumMultiplicity_zeroCorner_of_smallAgentSets Item r cost
      prefixChores m2Chores secondPrefix firstPrefix hr hcost
    · simpa [Finset.pair_comm] using hprefix
    · exact hprefixNe.symm
    · exact h10.2
    · exact h10.1
    · exact hprefixM2
    · exact hcover
    · exact hfirstCard
    · exact hsecondCard
  · let labels : Fin 4 ≃ Fin 4 := (Equiv.swap 0 2).trans (Equiv.swap 1 3)
    have hmap01 : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = {2, 3} := by decide
    have hmap23 : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = {0, 1} := by decide
    apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
    apply existsEfxOfB2MaximumMultiplicity_zeroCorner_of_smallAgentSets Item r
      (relabelChoreCost labels cost) prefixChores m2Chores firstPrefix secondPrefix
    · exact hr
    · exact IsOneOrRChoreCost.relabel labels cost r hcost
    · exact hprefix
    · exact hprefixNe
    · rw [smallAgentSet_relabel]
      rw [h23.1]
      decide
    · rw [smallAgentSet_relabel]
      rw [h23.2]
      decide
    · exact hprefixM2
    · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)),
        m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmap01, hmap23]
      simpa [Finset.union_comm] using hcover
    · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4))]
      rw [hmap01]
      exact hsecondCard
    · rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4))]
      rw [hmap23]
      exact hfirstCard
  · let labels : Fin 4 ≃ Fin 4 := (Equiv.swap 0 2).trans (Equiv.swap 1 3)
    have hmap01 : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = {2, 3} := by decide
    have hmap23 : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = {0, 1} := by decide
    apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
    apply existsEfxOfB2MaximumMultiplicity_zeroCorner_of_smallAgentSets Item r
      (relabelChoreCost labels cost) prefixChores m2Chores secondPrefix firstPrefix
    · exact hr
    · exact IsOneOrRChoreCost.relabel labels cost r hcost
    · simpa [Finset.pair_comm] using hprefix
    · exact hprefixNe.symm
    · rw [smallAgentSet_relabel]
      rw [h32.2]
      decide
    · rw [smallAgentSet_relabel]
      rw [h32.1]
      decide
    · exact hprefixM2
    · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)),
        m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmap01, hmap23]
      simpa [Finset.union_comm] using hcover
    · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4))]
      rw [hmap01]
      exact hsecondCard
    · rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4))]
      rw [hmap23]
      exact hfirstCard

/-- The `a = 0` maximum-multiplicity branch of source Case B.3.1.
Outside the tight short-pair residue, the ordinary canonical gap fill is
already sufficient.  In that residue, the endpoint and multiplicity bridge
reduces the suffix to the exact `3+3` instance handled by the zero-prefix
tight dispatcher. -/
theorem existsEfxOfB2MaximumMultiplicity_zero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 2)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨firstPrefix, secondPrefix, hprefixNe, hprefix⟩ :=
    Finset.card_eq_two.mp hprefixCard
  let standardQuota : Fin 4 → ℕ := canonicalQuota 0 ({2, 3} : Finset (Fin 4))
  have hstandardQuotaSum : Finset.univ.sum standardQuota = prefixChores.card := by
    rw [show standardQuota = canonicalQuota 0 ({2, 3} : Finset (Fin 4)) by rfl,
      canonicalQuota_sum, hprefixCard]
    decide
  obtain ⟨standardAllocation, hstandardCanonical⟩ :=
    existsCanonicalSmallChoreAllocation Item cost prefixChores standardQuota
      hstandardQuotaSum hprefixSmall
  have hstandardQuota0 : standardQuota 0 = 0 := by simp [standardQuota, canonicalQuota]
  have hstandardQuota1 : standardQuota 1 = 0 := by simp [standardQuota, canonicalQuota]
  have hstandardQuota2 : standardQuota 2 = 0 + 1 := by simp [standardQuota, canonicalQuota]
  have hstandardQuota3 : standardQuota 3 = 0 + 1 := by simp [standardQuota, canonicalQuota]
  by_cases hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {first, second})
  · exact existsEfxOfB2_parallelShortEndpoints_nonexceptional Item r cost prefixChores
      m2Chores 0 standardQuota standardAllocation first second hr hcost hprefixM2
      hstandardCanonical hstandardQuota0 hstandardQuota1 hstandardQuota2 hstandardQuota3
      hfirst hsecond hfirstNeSecond hm2Small hnotExceptional
  have hexceptional : IsM2Exceptional cost (m2Chores \ {first, second}) := by
    exact not_not.mp hnotExceptional
  rcases b2_parallel_exceptional_auxiliary_pair Item cost m2Chores first second hfirst hsecond
    hfirstNeSecond hmaximum hexceptional with hshortPair | hlongPair
  · obtain ⟨surviving, q, hsurviving, hresidue, hsecondCardFormula⟩ :=
      b2_parallel_exceptional_shortPair_tight_data Item cost m2Chores first second hfirst hsecond
        hfirstNeSecond hmaximum hshortPair
    let firstType := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
    let secondType := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
    have hfirstSubset : firstType ⊆ m2Chores := by
      intro item hitem
      exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp
        (by simpa [firstType] using hitem) |>.1
    have hsecondSubset : secondType ⊆ m2Chores := by
      intro item hitem
      exact (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mp
        (by simpa [secondType] using hitem) |>.1
    have htypesDisjoint : Disjoint firstType secondType := by
      simpa [firstType, secondType] using m2TypeChorePool_disjoint_of_ne cost m2Chores
        ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)
    obtain ⟨hcover, hfirstCard, hsecondCard⟩ :=
      b2_parallel_exceptional_forces_33 Item m2Chores firstType secondType first second surviving q
        hfirstSubset hsecondSubset htypesDisjoint (by simpa [firstType] using hfirst)
        (by simpa [firstType] using hsecond) (by simpa [firstType] using hsurviving)
        hfirstNeSecond (by simpa [firstType, secondType] using hresidue)
        (by simpa [secondType] using hsecondCardFormula)
        (by simpa [firstType, secondType] using hmaximum ({2, 3}))
    exact existsEfxOfB2TightExceptional_zero Item r cost prefixChores m2Chores
      firstPrefix secondPrefix hr hcost hprefix hprefixNe hprefixSmall hprefixM2
      (by simpa [firstType, secondType] using hcover)
      (by simpa [firstType] using hfirstCard) (by simpa [secondType] using hsecondCard)
  · exact existsEfxOfB2_parallelShortEndpoints_exceptional_longPair Item r cost prefixChores
      m2Chores 0 standardQuota standardAllocation first second hr hcost hprefixM2 hprefixSmall
      hstandardCanonical hstandardQuota0 hstandardQuota1 hstandardQuota2 hstandardQuota3
      hfirst hsecond hfirstNeSecond hlongPair

/-- Complete dispatch for source Case B.3.1 after the maximum M₂ type has
been relabelled to `(0,1)`.  A maximum fibre with at least two chores supplies
the gap pair; the positive and zero-prefix regimes are then the two compiled
source cases above. -/
theorem existsEfxOfB2MaximumMultiplicity
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 2)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hfirstTypeCard : 2 ≤
      (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨first, hfirst, second, hsecond, hfirstNeSecond⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
  by_cases ha : 0 < a
  · exact existsEfxOfB2MaximumMultiplicity_positive Item r cost prefixChores m2Chores a
      first second hr hcost ha hprefixCard hprefixSmall hm2Small hprefixM2 hfirst hsecond
      hfirstNeSecond hmaximum
  · have haZero : a = 0 := by omega
    apply existsEfxOfB2MaximumMultiplicity_zero Item r cost prefixChores m2Chores first second
      hr hcost
    · omega
    · exact hprefixSmall
    · exact hm2Small
    · exact hprefixM2
    · exact hfirst
    · exact hsecond
    · exact hfirstNeSecond
    · exact hmaximum

/-- The maximum-multiplicity B.3.1 dispatcher is invariant under a relabelling
that sends its displayed type `(0,1)` to the selected maximum M₂ fibre. -/
theorem existsEfxOfB2MaximumMultiplicity_of_relabelled_maximum
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item) (a : ℕ)
    (maximumType : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 2)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores maximumType).card)
    (hmaximumCard : 2 ≤ (m2TypeChorePool cost m2Chores maximumType).card)
    (hlabels : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = maximumType) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB2MaximumMultiplicity Item r (relabelChoreCost labels cost)
    prefixChores m2Chores a
  · exact hr
  · exact IsOneOrRChoreCost.relabel labels cost r hcost
  · exact hprefixCard
  · intro item hitem
    exact IsSmallForAtMostOne.relabel labels cost item (hprefixSmall item hitem)
  · intro item hitem
    exact IsSmallForExactlyTwo.relabel labels cost item (hm2Small item hitem)
  · exact hprefixM2
  · intro edgeType
    rw [m2TypeChorePool_relabel labels cost m2Chores edgeType,
      m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hlabels]
    exact hmaximum (edgeType.map labels.toEmbedding)
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hlabels]
    exact hmaximumCard

end HT26EFXChores
