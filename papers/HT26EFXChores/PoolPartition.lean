import AppliedModelingLib.SocialChoice.FairDivision.Chores
import Mathlib.Tactic.FinCases

/-!
# The M₀₁--M₂--M₃₄ chore-pool partition

The final section of He--Tao partitions every normalized chore pool by the
number of agents for whom each chore is small.  Keeping the finite-set
partition explicit prevents later concatenation theorems from silently
assuming that their three input pools cover the instance.

Source: `EFXadditivechores.tex`, lines 548--560.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- Chores small for at most one of the four agents. -/
noncomputable def m01ChorePool {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) : Finset Item := by
  classical
  exact chores.filter fun item => (smallAgentSet cost item).card ≤ 1

/-- Chores small for exactly two of the four agents. -/
noncomputable def m2ChorePool {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) : Finset Item := by
  classical
  exact chores.filter fun item => (smallAgentSet cost item).card = 2

/-- The source's multigraph edge fibre: the M₂ chores that are small for
exactly the prescribed pair of agents.  Keeping edge types explicit is useful
for the high-ratio gap-filling cases. -/
noncomputable def m2TypeChorePool {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (smallAgents : Finset (Fin 4)) : Finset Item := by
  classical
  exact chores.filter fun item => smallAgentSet cost item = smallAgents

/-- Chores small for at least three of the four agents. -/
noncomputable def m34ChorePool {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) : Finset Item := by
  classical
  exact chores.filter fun item => 3 ≤ (smallAgentSet cost item).card

theorem mem_m01ChorePool {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (item : Item) :
    item ∈ m01ChorePool cost chores ↔ item ∈ chores ∧ IsSmallForAtMostOne cost item := by
  simp [m01ChorePool, IsSmallForAtMostOne]

theorem mem_m2ChorePool {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (item : Item) :
    item ∈ m2ChorePool cost chores ↔ item ∈ chores ∧ IsSmallForExactlyTwo cost item := by
  simp [m2ChorePool, IsSmallForExactlyTwo]

/-- Membership in an M₂ edge fibre records both source-pool membership and
the exact two-agent small set. -/
theorem mem_m2TypeChorePool {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (smallAgents : Finset (Fin 4)) (item : Item) :
    item ∈ m2TypeChorePool cost chores smallAgents ↔
      item ∈ chores ∧ smallAgentSet cost item = smallAgents := by
  simp [m2TypeChorePool]

/-- Relabelling agents carries an M₂ edge fibre to the fibre whose endpoint
set is the corresponding image under the label equivalence. -/
theorem m2TypeChorePool_relabel {Item : Type} [DecidableEq Item]
    (labels : Fin 4 ≃ Fin 4) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (smallAgents : Finset (Fin 4)) :
    m2TypeChorePool (relabelChoreCost labels cost) chores smallAgents =
      m2TypeChorePool cost chores (smallAgents.map labels.toEmbedding) := by
  classical
  ext item
  constructor
  · intro hitem
    obtain ⟨hchore, hsmall⟩ :=
      (mem_m2TypeChorePool (relabelChoreCost labels cost) chores smallAgents item).mp hitem
    refine (mem_m2TypeChorePool cost chores (smallAgents.map labels.toEmbedding) item).mpr
      ⟨hchore, ?_⟩
    rw [smallAgentSet_relabel] at hsmall
    have hmap : labels.symm.toEmbedding.trans labels.toEmbedding =
        (Function.Embedding.refl (Fin 4)) := by
      ext agent
      simp
    simpa [Finset.map_map, hmap] using
      congrArg (Finset.map labels.toEmbedding) hsmall
  · intro hitem
    obtain ⟨hchore, hsmall⟩ :=
      (mem_m2TypeChorePool cost chores (smallAgents.map labels.toEmbedding) item).mp hitem
    refine (mem_m2TypeChorePool (relabelChoreCost labels cost) chores smallAgents item).mpr
      ⟨hchore, ?_⟩
    rw [smallAgentSet_relabel]
    have hmap : labels.toEmbedding.trans labels.symm.toEmbedding =
        (Function.Embedding.refl (Fin 4)) := by
      ext agent
      simp
    simpa [Finset.map_map, hmap] using
      congrArg (Finset.map labels.symm.toEmbedding) hsmall

/-- An endpoint of an M₂ edge fibre regards each chore in that fibre as
small. -/
theorem m2TypeChorePool_small_for_endpoint {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (smallAgents : Finset (Fin 4)) (item : Item) (agent : Fin 4)
    (hitem : item ∈ m2TypeChorePool cost chores smallAgents)
    (hagent : agent ∈ smallAgents) :
    IsSmallChore cost agent item := by
  have htype := (mem_m2TypeChorePool cost chores smallAgents item).mp hitem |>.2
  have hsmallSet : agent ∈ smallAgentSet cost item := by simpa [htype] using hagent
  simpa [smallAgentSet] using hsmallSet

/-- A nonendpoint of an M₂ edge fibre regards each chore in that fibre as
large in a normalized bi-valued instance. -/
theorem m2TypeChorePool_large_for_nonendpoint {Item : Type} [DecidableEq Item]
    (r : ℝ) (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (smallAgents : Finset (Fin 4)) (item : Item) (agent : Fin 4)
    (hcost : IsOneOrRChoreCost cost r)
    (hitem : item ∈ m2TypeChorePool cost chores smallAgents)
    (hagent : agent ∉ smallAgents) :
    IsLargeChore cost r agent item := by
  rcases hcost agent item with hsmall | hlarge
  · exfalso
    apply hagent
    have hsmallSet : agent ∈ smallAgentSet cost item := by
      simpa [smallAgentSet, IsSmallChore] using hsmall
    simpa [(mem_m2TypeChorePool cost chores smallAgents item).mp hitem |>.2] using hsmallSet
  · simpa [IsLargeChore] using hlarge

/-- Distinct M₂ edge fibres are disjoint. -/
theorem m2TypeChorePool_disjoint_of_ne {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (firstType secondType : Finset (Fin 4)) (hne : firstType ≠ secondType) :
    Disjoint (m2TypeChorePool cost chores firstType)
      (m2TypeChorePool cost chores secondType) := by
  rw [Finset.disjoint_left]
  intro item hfirst hsecond
  have hfirstType := (mem_m2TypeChorePool cost chores firstType item).mp hfirst |>.2
  have hsecondType := (mem_m2TypeChorePool cost chores secondType item).mp hsecond |>.2
  exact hne (hfirstType.symm.trans hsecondType)

/-- Restricting the ambient M₂ pool can only remove chores from any fixed
edge fibre. -/
theorem m2TypeChorePool_mono {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) {left right : Finset Item}
    (smallAgents : Finset (Fin 4)) (hsubset : left ⊆ right) :
    m2TypeChorePool cost left smallAgents ⊆
      m2TypeChorePool cost right smallAgents := by
  intro item hitem
  obtain ⟨hleft, htype⟩ :=
    (mem_m2TypeChorePool cost left smallAgents item).mp hitem
  exact (mem_m2TypeChorePool cost right smallAgents item).mpr ⟨hsubset hleft, htype⟩

theorem mem_m34ChorePool {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (item : Item) :
    item ∈ m34ChorePool cost chores ↔ item ∈ chores ∧ IsSmallForAtLeastThree cost item := by
  simp [m34ChorePool, IsSmallForAtLeastThree]

/-- The three source pools are pairwise disjoint. -/
theorem m01ChorePool_disjoint_m2ChorePool {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) :
    Disjoint (m01ChorePool cost chores) (m2ChorePool cost chores) := by
  classical
  rw [Finset.disjoint_left]
  intro item hm01 hm2
  obtain ⟨_, hm01'⟩ := (mem_m01ChorePool cost chores item).mp hm01
  obtain ⟨_, hm2'⟩ := (mem_m2ChorePool cost chores item).mp hm2
  change (smallAgentSet cost item).card ≤ 1 at hm01'
  change (smallAgentSet cost item).card = 2 at hm2'
  omega

theorem m01ChorePool_disjoint_m34ChorePool {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) :
    Disjoint (m01ChorePool cost chores) (m34ChorePool cost chores) := by
  classical
  rw [Finset.disjoint_left]
  intro item hm01 hm34
  obtain ⟨_, hm01'⟩ := (mem_m01ChorePool cost chores item).mp hm01
  obtain ⟨_, hm34'⟩ := (mem_m34ChorePool cost chores item).mp hm34
  change (smallAgentSet cost item).card ≤ 1 at hm01'
  change 3 ≤ (smallAgentSet cost item).card at hm34'
  omega

theorem m2ChorePool_disjoint_m34ChorePool {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) :
    Disjoint (m2ChorePool cost chores) (m34ChorePool cost chores) := by
  classical
  rw [Finset.disjoint_left]
  intro item hm2 hm34
  obtain ⟨_, hm2'⟩ := (mem_m2ChorePool cost chores item).mp hm2
  obtain ⟨_, hm34'⟩ := (mem_m34ChorePool cost chores item).mp hm34
  change (smallAgentSet cost item).card = 2 at hm2'
  change 3 ≤ (smallAgentSet cost item).card at hm34'
  omega

/-- The M₀₁, M₂, and M₃₄ pools cover every chore. -/
theorem m01_m2_m34_union_eq {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) :
    (m01ChorePool cost chores ∪ m2ChorePool cost chores) ∪ m34ChorePool cost chores = chores := by
  classical
  apply Finset.Subset.antisymm
  · intro item hitem
    rcases Finset.mem_union.mp hitem with hleft | hm34
    · rcases Finset.mem_union.mp hleft with hm01 | hm2
      · exact ((mem_m01ChorePool cost chores item).mp hm01).1
      · exact ((mem_m2ChorePool cost chores item).mp hm2).1
    · exact ((mem_m34ChorePool cost chores item).mp hm34).1
  · intro item hitem
    by_cases hm01 : IsSmallForAtMostOne cost item
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        ((mem_m01ChorePool cost chores item).mpr ⟨hitem, hm01⟩))
    · have htwoOrThree : 2 ≤ (smallAgentSet cost item).card := by
        change ¬ (smallAgentSet cost item).card ≤ 1 at hm01
        omega
      by_cases hm2 : IsSmallForExactlyTwo cost item
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          ((mem_m2ChorePool cost chores item).mpr ⟨hitem, hm2⟩))
      · have hm34 : IsSmallForAtLeastThree cost item := by
          change 3 ≤ (smallAgentSet cost item).card
          change (smallAgentSet cost item).card ≠ 2 at hm2
          omega
        exact Finset.mem_union_right _ ((mem_m34ChorePool cost chores item).mpr ⟨hitem, hm34⟩)

theorem m01ChorePool_small {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) :
    ∀ item ∈ m01ChorePool cost chores, IsSmallForAtMostOne cost item := by
  intro item hitem
  exact ((mem_m01ChorePool cost chores item).mp hitem).2

theorem m2ChorePool_small {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) :
    ∀ item ∈ m2ChorePool cost chores, IsSmallForExactlyTwo cost item := by
  intro item hitem
  exact ((mem_m2ChorePool cost chores item).mp hitem).2

/-- The six two-element subsets of four labelled agents are exactly the six
edge types used by the source's M₂ multigraph. -/
theorem finset_fin4_card_two_eq_one_of_six (smallAgents : Finset (Fin 4))
    (hcard : smallAgents.card = 2) :
    smallAgents = ({0, 1} : Finset (Fin 4)) ∨
    smallAgents = ({0, 2} : Finset (Fin 4)) ∨
    smallAgents = ({0, 3} : Finset (Fin 4)) ∨
    smallAgents = ({1, 2} : Finset (Fin 4)) ∨
    smallAgents = ({1, 3} : Finset (Fin 4)) ∨
    smallAgents = ({2, 3} : Finset (Fin 4)) := by
  obtain ⟨first, second, hne, hsmallAgents⟩ := Finset.card_eq_two.mp hcard
  rw [hsmallAgents]
  fin_cases first <;> fin_cases second <;> simp_all [Finset.ext_iff] <;> aesop

/-- The literal M₂ pool is the union of its six labelled edge fibres.  This
is the source-to-model bridge used to turn a finite simple-graph schedule into
an allocation of every M₂ chore. -/
theorem m2ChorePool_eq_union_six_typeChorePools {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) :
    m2ChorePool cost chores =
      m2TypeChorePool cost chores ({0, 1} : Finset (Fin 4)) ∪
      m2TypeChorePool cost chores ({0, 2} : Finset (Fin 4)) ∪
      m2TypeChorePool cost chores ({0, 3} : Finset (Fin 4)) ∪
      m2TypeChorePool cost chores ({1, 2} : Finset (Fin 4)) ∪
      m2TypeChorePool cost chores ({1, 3} : Finset (Fin 4)) ∪
      m2TypeChorePool cost chores ({2, 3} : Finset (Fin 4)) := by
  classical
  ext item
  constructor
  · intro hitem
    obtain ⟨hchore, hsmall⟩ := (mem_m2ChorePool cost chores item).mp hitem
    obtain h01 | h02 | h03 | h12 | h13 | h23 :=
      finset_fin4_card_two_eq_one_of_six (smallAgentSet cost item) hsmall
    · simp only [Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        ((mem_m2TypeChorePool cost chores ({0, 1} : Finset (Fin 4)) item).mpr
          ⟨hchore, h01⟩)))))
    · simp only [Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
        ((mem_m2TypeChorePool cost chores ({0, 2} : Finset (Fin 4)) item).mpr
          ⟨hchore, h02⟩)))))
    · simp only [Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr
        ((mem_m2TypeChorePool cost chores ({0, 3} : Finset (Fin 4)) item).mpr
          ⟨hchore, h03⟩))))
    · simp only [Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr
        ((mem_m2TypeChorePool cost chores ({1, 2} : Finset (Fin 4)) item).mpr
          ⟨hchore, h12⟩)))
    · simp only [Finset.mem_union]
      exact Or.inl (Or.inr
        ((mem_m2TypeChorePool cost chores ({1, 3} : Finset (Fin 4)) item).mpr
          ⟨hchore, h13⟩))
    · simp only [Finset.mem_union]
      exact Or.inr
        ((mem_m2TypeChorePool cost chores ({2, 3} : Finset (Fin 4)) item).mpr
          ⟨hchore, h23⟩)
  · intro hitem
    have htypePoolSubsetM2 (smallAgents : Finset (Fin 4))
        (hsmallAgents : smallAgents.card = 2) :
        m2TypeChorePool cost chores smallAgents ⊆ m2ChorePool cost chores := by
      intro chore hchore
      obtain ⟨hchore', htype⟩ :=
        (mem_m2TypeChorePool cost chores smallAgents chore).mp hchore
      exact (mem_m2ChorePool cost chores chore).mpr ⟨hchore', by
        change (smallAgentSet cost chore).card = 2
        rw [htype]
        exact hsmallAgents⟩
    rcases Finset.mem_union.mp hitem with hleft | h23
    · rcases Finset.mem_union.mp hleft with hleft | h13
      · rcases Finset.mem_union.mp hleft with hleft | h12
        · rcases Finset.mem_union.mp hleft with hleft | h03
          · rcases Finset.mem_union.mp hleft with h01 | h02
            · exact htypePoolSubsetM2 ({0, 1} : Finset (Fin 4)) (by decide) h01
            · exact htypePoolSubsetM2 ({0, 2} : Finset (Fin 4)) (by decide) h02
          · exact htypePoolSubsetM2 ({0, 3} : Finset (Fin 4)) (by decide) h03
        · exact htypePoolSubsetM2 ({1, 2} : Finset (Fin 4)) (by decide) h12
      · exact htypePoolSubsetM2 ({1, 3} : Finset (Fin 4)) (by decide) h13
    · exact htypePoolSubsetM2 ({2, 3} : Finset (Fin 4)) (by decide) h23

/-- When all four short--long edge fibres are absent, every M₂ chore has one
of the two same-side types.  This is the source-to-model bridge for Case
B.3.2(d). -/
theorem m2ChorePool_eq_sameSide_typeChorePools_of_cross_empty
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item)
    (h02 : m2TypeChorePool cost chores ({0, 2} : Finset (Fin 4)) = ∅)
    (h03 : m2TypeChorePool cost chores ({0, 3} : Finset (Fin 4)) = ∅)
    (h12 : m2TypeChorePool cost chores ({1, 2} : Finset (Fin 4)) = ∅)
    (h13 : m2TypeChorePool cost chores ({1, 3} : Finset (Fin 4)) = ∅) :
    m2ChorePool cost chores =
      m2TypeChorePool cost chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost chores ({2, 3} : Finset (Fin 4)) := by
  rw [m2ChorePool_eq_union_six_typeChorePools cost chores, h02, h03, h12, h13]
  simp only [Finset.union_empty]

theorem m34ChorePool_small {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) :
    ∀ item ∈ m34ChorePool cost chores, IsSmallForAtLeastThree cost item := by
  intro item hitem
  exact ((mem_m34ChorePool cost chores item).mp hitem).2

end HT26EFXChores
