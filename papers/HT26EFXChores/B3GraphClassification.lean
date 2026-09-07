import HT26EFXChores.PoolPartition
import Mathlib.Data.Fin.VecNotation

/-!
# The finite M₂ graph split for source Case B.4

The `b = 3` source proof first classifies the nonempty edge types of the
four-vertex M₂ multigraph.  If two types intersect, it enters B.4.1;
otherwise every pair of distinct types is disjoint, so the support is either
a matching of two types or one fixed type.

Source: `EFXadditivechores.tex`, lines 3006--3009 and 3200--3201.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- The edge-type support of an M₂ pool has exactly the three graph forms
used in the source's `b = 3` analysis.  The fixed-type alternative also
covers an empty M₂ pool vacuously; the later source dispatch can then use the
already compiled M₀₁-only branch. -/
theorem m2_graph_intersecting_or_matching_or_fixed
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item) :
    (∃ firstType secondType : Finset (Fin 4),
      firstType.card = 2 ∧ secondType.card = 2 ∧ firstType ≠ secondType ∧
      ¬ Disjoint firstType secondType ∧
      (m2TypeChorePool cost m2Chores firstType).Nonempty ∧
      (m2TypeChorePool cost m2Chores secondType).Nonempty) ∨
    (∃ firstType secondType : Finset (Fin 4),
      firstType.card = 2 ∧ secondType.card = 2 ∧ Disjoint firstType secondType ∧
      (m2TypeChorePool cost m2Chores firstType).Nonempty ∧
      (m2TypeChorePool cost m2Chores secondType).Nonempty ∧
      ∀ item ∈ m2Chores,
        smallAgentSet cost item = firstType ∨ smallAgentSet cost item = secondType) ∨
    (∃ edgeType : Finset (Fin 4), edgeType.card = 2 ∧
      ∀ item ∈ m2Chores, smallAgentSet cost item = edgeType) := by
  classical
  let support : Finset (Finset (Fin 4)) :=
    (Finset.univ : Finset (Finset (Fin 4))).filter fun edgeType =>
      edgeType.card = 2 ∧ (m2TypeChorePool cost m2Chores edgeType).Nonempty
  have hsupportMem (edgeType : Finset (Fin 4)) (hedgeType : edgeType ∈ support) :
      edgeType.card = 2 ∧ (m2TypeChorePool cost m2Chores edgeType).Nonempty := by
    simpa [support] using Finset.mem_filter.mp hedgeType
  have htypeInSupport (item : Item) (hitem : item ∈ m2Chores) :
      smallAgentSet cost item ∈ support := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hm2Small item hitem, ?_⟩
    refine ⟨item, ?_⟩
    exact (mem_m2TypeChorePool cost m2Chores (smallAgentSet cost item) item).mpr
      ⟨hitem, rfl⟩
  by_cases hintersecting : ∃ firstType ∈ support, ∃ secondType ∈ support,
      firstType ≠ secondType ∧ ¬ Disjoint firstType secondType
  · rcases hintersecting with ⟨firstType, hfirstType, secondType, hsecondType,
      hne, hnotDisjoint⟩
    exact Or.inl ⟨firstType, secondType, (hsupportMem firstType hfirstType).1,
      (hsupportMem secondType hsecondType).1, hne, hnotDisjoint,
      (hsupportMem firstType hfirstType).2, (hsupportMem secondType hsecondType).2⟩
  have hdisjointDistinct : ∀ firstType ∈ support, ∀ secondType ∈ support,
      firstType ≠ secondType → Disjoint firstType secondType := by
    intro firstType hfirstType secondType hsecondType hne
    by_contra hnotDisjoint
    exact hintersecting ⟨firstType, hfirstType, secondType, hsecondType, hne, hnotDisjoint⟩
  by_cases hsupportEmpty : support = ∅
  · right
    right
    refine ⟨({0, 1} : Finset (Fin 4)), by decide, ?_⟩
    intro item hitem
    have hitemSupport := htypeInSupport item hitem
    rw [hsupportEmpty] at hitemSupport
    simp at hitemSupport
  obtain ⟨firstType, hfirstType⟩ := Finset.nonempty_iff_ne_empty.mpr hsupportEmpty
  have hsupportSubset : support ⊆ {firstType, firstTypeᶜ} := by
    intro secondType hsecondType
    by_cases heq : secondType = firstType
    · simp [heq]
    · have hdisjoint := hdisjointDistinct firstType hfirstType secondType hsecondType (Ne.symm heq)
      have hsubset : secondType ⊆ firstTypeᶜ := by
        intro agent hagent
        simp only [Finset.mem_compl]
        intro hfirstAgent
        exact (Finset.disjoint_left.mp hdisjoint hfirstAgent hagent).elim
      have hfirstCard : firstType.card = 2 := (hsupportMem firstType hfirstType).1
      have hsecondCard : secondType.card = 2 := (hsupportMem secondType hsecondType).1
      have hcomplementCard : firstTypeᶜ.card = 2 := by
        rw [Finset.card_compl, hfirstCard]
        norm_num
      have hsecondEq : secondType = firstTypeᶜ := by
        apply Finset.eq_of_subset_of_card_le hsubset
        rw [hcomplementCard, hsecondCard]
      simp [hsecondEq]
  have hsupportCard : support.card ≤ 2 := by
    calc
      support.card ≤ ({firstType, firstTypeᶜ} : Finset (Finset (Fin 4))).card :=
        Finset.card_le_card hsupportSubset
      _ ≤ 2 := Finset.card_insert_le _ _
  have hsupportPos : 0 < support.card := Finset.card_pos.mpr ⟨firstType, hfirstType⟩
  by_cases hcardOne : support.card = 1
  · have hsupportEq : support = {firstType} := by
      apply Finset.eq_of_subset_of_card_le
      · intro edgeType hedgeType
        by_cases heq : edgeType = firstType
        · simp [heq]
        · have hdisjoint := hdisjointDistinct firstType hfirstType edgeType hedgeType (Ne.symm heq)
          have hsubset : edgeType ⊆ firstTypeᶜ := by
            intro agent hagent
            simp only [Finset.mem_compl]
            intro hfirstAgent
            exact (Finset.disjoint_left.mp hdisjoint hfirstAgent hagent).elim
          have hedgeCard : edgeType.card = 2 := (hsupportMem edgeType hedgeType).1
          have hfirstCard : firstType.card = 2 := (hsupportMem firstType hfirstType).1
          have hcomplementCard : firstTypeᶜ.card = 2 := by
            rw [Finset.card_compl, hfirstCard]
            norm_num
          have heqComplement : edgeType = firstTypeᶜ := by
            apply Finset.eq_of_subset_of_card_le hsubset
            rw [hcomplementCard, hedgeCard]
          have hneMem : edgeType ∈ support := hedgeType
          have hfirstOnly : support.card = 1 := hcardOne
          have hfirstMem' : firstType ∈ support := hfirstType
          have htwoMembers : ({firstType, edgeType} : Finset (Finset (Fin 4))).card = 2 := by
            rw [Finset.card_pair (Ne.symm heq)]
          have hsubsetTwo : ({firstType, edgeType} : Finset (Finset (Fin 4))) ⊆ support := by
            intro type htype
            simp only [Finset.mem_insert, Finset.mem_singleton] at htype
            rcases htype with rfl | rfl
            · exact hfirstMem'
            · exact hneMem
          have hle := Finset.card_le_card hsubsetTwo
          omega
      · rw [hcardOne]
        simp
    right
    right
    refine ⟨firstType, (hsupportMem firstType hfirstType).1, ?_⟩
    intro item hitem
    have hitemSupport := htypeInSupport item hitem
    rw [hsupportEq] at hitemSupport
    simpa using hitemSupport
  · have hcardTwo : support.card = 2 := by omega
    obtain ⟨secondType, thirdType, hne, hsupportEq⟩ := Finset.card_eq_two.mp hcardTwo
    have hsecondType : secondType ∈ support := by simp [hsupportEq]
    have hthirdType : thirdType ∈ support := by simp [hsupportEq]
    right
    left
    refine ⟨secondType, thirdType, (hsupportMem secondType hsecondType).1,
      (hsupportMem thirdType hthirdType).1,
      hdisjointDistinct secondType hsecondType thirdType hthirdType hne,
      (hsupportMem secondType hsecondType).2, (hsupportMem thirdType hthirdType).2, ?_⟩
    intro item hitem
    have hitemSupport := htypeInSupport item hitem
    rw [hsupportEq] at hitemSupport
    simpa using hitemSupport

/-- Any two disjoint two-agent types on four agents can be relabelled to the
displayed matching `(0,1),(2,3)`.  This is the finite WLOG bridge used by the
outer B.4 matching dispatcher. -/
theorem exists_matching_type_relabelling
    (firstType secondType : Finset (Fin 4))
    (hfirstCard : firstType.card = 2) (hsecondCard : secondType.card = 2)
    (hdisjoint : Disjoint firstType secondType) :
    ∃ labels : Fin 4 ≃ Fin 4,
      ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = firstType ∧
      ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = secondType := by
  have second_eq_complement (hfirst : firstType.card = 2) :
      secondType = firstTypeᶜ := by
    have hsubset : secondType ⊆ firstTypeᶜ := by
      intro agent hsecond
      simp only [Finset.mem_compl]
      intro hfirstMember
      exact Finset.disjoint_left.mp hdisjoint hfirstMember hsecond
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [Finset.card_compl, hfirst, hsecondCard]
    norm_num
  rcases finset_fin4_card_two_eq_one_of_six firstType hfirstCard with h01 | h02 | h03 | h12 | h13 | h23
  · subst firstType
    have hsecond : secondType = ({2, 3} : Finset (Fin 4)) := by
      calc
        secondType = ({0, 1} : Finset (Fin 4))ᶜ := second_eq_complement (by decide)
        _ = {2, 3} := by decide
    subst secondType
    exact ⟨Equiv.refl (Fin 4), by decide, by decide⟩
  · subst firstType
    have hsecond : secondType = ({1, 3} : Finset (Fin 4)) := by
      calc
        secondType = ({0, 2} : Finset (Fin 4))ᶜ := second_eq_complement (by decide)
        _ = {1, 3} := by decide
    subst secondType
    exact ⟨Equiv.swap 1 2, by decide, by decide⟩
  · subst firstType
    have hsecond : secondType = ({1, 2} : Finset (Fin 4)) := by
      calc
        secondType = ({0, 3} : Finset (Fin 4))ᶜ := second_eq_complement (by decide)
        _ = {1, 2} := by decide
    subst secondType
    exact ⟨Equiv.swap 1 3, by decide, by decide⟩
  · subst firstType
    have hsecond : secondType = ({0, 3} : Finset (Fin 4)) := by
      calc
        secondType = ({1, 2} : Finset (Fin 4))ᶜ := second_eq_complement (by decide)
        _ = {0, 3} := by decide
    subst secondType
    exact ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1), by decide, by decide⟩
  · subst firstType
    have hsecond : secondType = ({0, 2} : Finset (Fin 4)) := by
      calc
        secondType = ({1, 3} : Finset (Fin 4))ᶜ := second_eq_complement (by decide)
        _ = {0, 2} := by decide
    subst secondType
    exact ⟨((Equiv.swap 0 1).trans (Equiv.swap 0 3)).trans (Equiv.swap 0 2), by decide, by decide⟩
  · subst firstType
    have hsecond : secondType = ({0, 1} : Finset (Fin 4)) := by
      calc
        secondType = ({2, 3} : Finset (Fin 4))ᶜ := second_eq_complement (by decide)
        _ = {0, 1} := by decide
    subst secondType
    exact ⟨(Equiv.swap 0 2).trans (Equiv.swap 1 3), by decide, by decide⟩

/-- Any two distinct intersecting two-agent types can be relabelled to the
displayed source pair `(0,1),(0,2)`.  The proof is the finite six-edge table;
each listed bijection sends working labels `0,1,2,3` to the common endpoint,
the first-only endpoint, the second-only endpoint, and the remaining agent. -/
theorem exists_intersecting_type_relabelling
    (firstType secondType : Finset (Fin 4))
    (hfirstCard : firstType.card = 2) (hsecondCard : secondType.card = 2)
    (hne : firstType ≠ secondType) (hnotDisjoint : ¬ Disjoint firstType secondType) :
    ∃ labels : Fin 4 ≃ Fin 4,
      ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = firstType ∧
      ({0, 2} : Finset (Fin 4)).map labels.toEmbedding = secondType := by
  classical
  rcases finset_fin4_card_two_eq_one_of_six firstType hfirstCard with
      h01 | h02 | h03 | h12 | h13 | h23
  · subst firstType
    rcases finset_fin4_card_two_eq_one_of_six secondType hsecondCard with
        h01 | h02 | h03 | h12 | h13 | h23
    · subst secondType
      exact (hne rfl).elim
    · subst secondType
      refine ⟨Equiv.ofBijective (![0, 1, 2, 3] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      refine ⟨Equiv.ofBijective (![0, 1, 3, 2] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      refine ⟨Equiv.ofBijective (![1, 0, 2, 3] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      refine ⟨Equiv.ofBijective (![1, 0, 3, 2] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      exact (hnotDisjoint (by decide)).elim
  · subst firstType
    rcases finset_fin4_card_two_eq_one_of_six secondType hsecondCard with
        h01 | h02 | h03 | h12 | h13 | h23
    · subst secondType
      refine ⟨Equiv.ofBijective (![0, 2, 1, 3] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      exact (hne rfl).elim
    · subst secondType
      refine ⟨Equiv.ofBijective (![0, 2, 3, 1] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      refine ⟨Equiv.ofBijective (![2, 0, 1, 3] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      exact (hnotDisjoint (by decide)).elim
    · subst secondType
      refine ⟨Equiv.ofBijective (![2, 0, 3, 1] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
  · subst firstType
    rcases finset_fin4_card_two_eq_one_of_six secondType hsecondCard with
        h01 | h02 | h03 | h12 | h13 | h23
    · subst secondType
      refine ⟨Equiv.ofBijective (![0, 3, 1, 2] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      refine ⟨Equiv.ofBijective (![0, 3, 2, 1] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      exact (hne rfl).elim
    · subst secondType
      exact (hnotDisjoint (by decide)).elim
    · subst secondType
      refine ⟨Equiv.ofBijective (![3, 0, 1, 2] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      refine ⟨Equiv.ofBijective (![3, 0, 2, 1] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
  · subst firstType
    rcases finset_fin4_card_two_eq_one_of_six secondType hsecondCard with
        h01 | h02 | h03 | h12 | h13 | h23
    · subst secondType
      refine ⟨Equiv.ofBijective (![1, 2, 0, 3] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      refine ⟨Equiv.ofBijective (![2, 1, 0, 3] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      exact (hnotDisjoint (by decide)).elim
    · subst secondType
      exact (hne rfl).elim
    · subst secondType
      refine ⟨Equiv.ofBijective (![1, 2, 3, 0] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      refine ⟨Equiv.ofBijective (![2, 1, 3, 0] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
  · subst firstType
    rcases finset_fin4_card_two_eq_one_of_six secondType hsecondCard with
        h01 | h02 | h03 | h12 | h13 | h23
    · subst secondType
      refine ⟨Equiv.ofBijective (![1, 3, 0, 2] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      exact (hnotDisjoint (by decide)).elim
    · subst secondType
      refine ⟨Equiv.ofBijective (![3, 1, 0, 2] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      refine ⟨Equiv.ofBijective (![1, 3, 2, 0] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      exact (hne rfl).elim
    · subst secondType
      refine ⟨Equiv.ofBijective (![3, 1, 2, 0] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
  · subst firstType
    rcases finset_fin4_card_two_eq_one_of_six secondType hsecondCard with
        h01 | h02 | h03 | h12 | h13 | h23
    · subst secondType
      exact (hnotDisjoint (by decide)).elim
    · subst secondType
      refine ⟨Equiv.ofBijective (![2, 3, 0, 1] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      refine ⟨Equiv.ofBijective (![3, 2, 0, 1] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      refine ⟨Equiv.ofBijective (![2, 3, 1, 0] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      refine ⟨Equiv.ofBijective (![3, 2, 1, 0] : Fin 4 → Fin 4) (by decide), ?_, ?_⟩ <;> decide
    · subst secondType
      exact (hne rfl).elim

/-- In an intersecting-support M₂ graph, a maximum edge type has an
intersecting support neighbor.  Otherwise both members of one intersecting
pair would be the unique complementary edge to that maximum type. -/
theorem exists_intersecting_neighbor_of_maximum
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (maximumType firstType secondType : Finset (Fin 4))
    (hmaximumCard : maximumType.card = 2)
    (hfirstCard : firstType.card = 2) (hsecondCard : secondType.card = 2)
    (hfirstNeSecond : firstType ≠ secondType)
    (hfirstNonempty : (m2TypeChorePool cost m2Chores firstType).Nonempty)
    (hsecondNonempty : (m2TypeChorePool cost m2Chores secondType).Nonempty) :
    ∃ neighborType : Finset (Fin 4), neighborType.card = 2 ∧
      ¬ Disjoint maximumType neighborType ∧
      (m2TypeChorePool cost m2Chores neighborType).Nonempty := by
  classical
  by_cases hinterFirst : ¬ Disjoint maximumType firstType
  · exact ⟨firstType, hfirstCard, hinterFirst, hfirstNonempty⟩
  by_cases hinterSecond : ¬ Disjoint maximumType secondType
  · exact ⟨secondType, hsecondCard, hinterSecond, hsecondNonempty⟩
  have hdisjointFirst : Disjoint maximumType firstType := not_not.mp hinterFirst
  have hdisjointSecond : Disjoint maximumType secondType := not_not.mp hinterSecond
  have first_eq_complement : firstType = maximumTypeᶜ := by
    have hsubset : firstType ⊆ maximumTypeᶜ := by
      intro agent hfirst
      simp only [Finset.mem_compl]
      intro hmaximum
      exact (Finset.disjoint_left.mp hdisjointFirst hmaximum hfirst).elim
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [Finset.card_compl, hmaximumCard, hfirstCard]
    norm_num
  have second_eq_complement : secondType = maximumTypeᶜ := by
    have hsubset : secondType ⊆ maximumTypeᶜ := by
      intro agent hsecond
      simp only [Finset.mem_compl]
      intro hmaximum
      exact (Finset.disjoint_left.mp hdisjointSecond hmaximum hsecond).elim
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [Finset.card_compl, hmaximumCard, hsecondCard]
    norm_num
  exact False.elim (hfirstNeSecond (first_eq_complement.trans second_eq_complement.symm))

end HT26EFXChores
