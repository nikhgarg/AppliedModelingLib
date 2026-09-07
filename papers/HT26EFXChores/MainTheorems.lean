import AppliedModelingLib.Foundations.Graph.Cycle
import AppliedModelingLib.SocialChoice.FairDivision.Chores
import Mathlib
import HT26EFXChores.BalancedOrientation
import HT26EFXChores.M2Orientation

/-!
# Paper-Facing Theorems: EFX for Additive Chores: Nonexistence, Pareto Incompatibility, and Bi-Valued Existence

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

During the statement-first phase, each exact paper-facing proposition lives in a
transparent `<name>Spec : Prop` declaration in `PaperInterface.lean`; the paired
theorem/lemma has exactly that type and a temporary `by sorry` body. Add proof
implementations here only after those specifications pass v10 semantic statement
review and recursive premise provenance audit. Before full closeout, the v11
realization audit independently binds pinned source atoms to the elaborated Spec
and accounts for the complete Lean closure; a proof hole or a declaration name
is never evidence for that correspondence.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/--
Source-faithful implementation of He--Tao's M34 insertion lemma.

The reduction potential removes cycles in the strict most-envy graph.  When
direct insertion at its sink is unavailable, a path from the cheapest updated
bundle to that sink is rotated and the chore is inserted at the predecessor.
The reusable allocation and graph lemmas are implemented in the core library;
this theorem composes them in the paper's four-agent setting.

Source: `EFXadditivechores.tex`, Lemma (M34 insertion), lines 577--580.
-/
theorem m34InsertionOfAllOtherSmallProof
    (Agent Item : Type) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [DecidableEq Item] (r : ℝ) (cost : ChoreCost Agent Item)
    (chores : Finset Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r) (hitem : item ∉ chores)
    (hsmallOther : ∀ sink, cost sink item ≠ 1 →
      ∀ agent, agent ≠ sink → cost agent item = 1)
    (allocation : Allocation Agent Item)
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation) :
    ∃ extended : Allocation Agent Item,
      IsAllocationOf extended (insert item chores) ∧
        EFXForChores (additiveChoreCost cost) extended := by
  have hnonneg : ∀ agent chore, 0 ≤ cost agent chore :=
    IsOneOrRChoreCost.nonneg cost r hcost (by linarith)
  have hlower : ∀ agent chore, 1 ≤ cost agent chore :=
    IsOneOrRChoreCost.one_le cost r hcost (by linarith)
  obtain ⟨reduced, hReducedAlloc, hReducedEFX, hNoCycle, sink, hSinkMin⟩ :=
    exists_reduced_efx_allocation_with_cost_sink_and_no_mostEnvyCycle
      cost chores hnonneg allocation halloc hefx
  by_cases hhasSmallSink : ∃ agent : Agent,
      (∀ comparison, additiveChoreCost cost agent (reduced agent) ≤
        additiveChoreCost cost agent (reduced comparison)) ∧ IsSmallChore cost agent item
  · obtain ⟨agent, hminimum, hsmall⟩ := hhasSmallSink
    refine ⟨addItem reduced agent item,
      isAllocationOf_addItem_insert reduced chores agent item hReducedAlloc hitem, ?_⟩
    exact efxForChores_addItem_of_envyFree_owner cost reduced agent item hlower
      (by
        intro hmem
        exact hitem (hReducedAlloc.1 agent item hmem))
      (by simpa [IsSmallChore] using hsmall) hminimum hReducedEFX
  · have hsmallSink : ¬ IsSmallChore cost sink item := by
      intro hsmall
      exact hhasSmallSink ⟨sink, hSinkMin, hsmall⟩
    have hsmallOtherSink := hsmallOther sink (by
      simpa [IsSmallChore] using hsmallSink)
    have hunique : ∀ agent,
        (∀ comparison,
          ¬ StrictMostEnvyEdgeForChores cost reduced agent comparison) → agent = sink := by
      intro agent hno
      have hminimum := no_strictMostEnvyEdge_implies_envyFreeForChores cost reduced agent hno
      by_contra hne
      exact hhasSmallSink ⟨agent, hminimum, by
        simpa [IsSmallChore] using hsmallOtherSink agent hne⟩
    let tentative := addItem reduced sink item
    obtain ⟨cheapest, _, hcheapest⟩ := Finset.exists_min_image (Finset.univ : Finset Agent)
      (fun agent => additiveChoreCost cost sink (tentative agent)) Finset.univ_nonempty
    by_cases hcheapestSink : cheapest = sink
    · refine ⟨tentative,
        isAllocationOf_addItem_insert reduced chores sink item hReducedAlloc hitem, ?_⟩
      apply efxForChores_addItem_of_new_owner_minimal cost reduced sink item hnonneg hReducedEFX
      intro comparison
      simpa [tentative, hcheapestSink] using hcheapest comparison (Finset.mem_univ _)
    · have hpath : Relation.ReflTransGen (StrictMostEnvyEdgeForChores cost reduced)
          cheapest sink :=
        AppliedModelingLib.Foundations.Graph.reaches_unique_sink_of_no_cycle hNoCycle sink hunique cheapest
      have hpathTrans : Relation.TransGen (StrictMostEnvyEdgeForChores cost reduced)
          cheapest sink := by
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp hpath with hEq | hTrans
        · exact (hcheapestSink hEq.symm).elim
        · exact hTrans
      obtain ⟨path, hpathNodup, hpathLength, hpathHead, hpathLast, hpathChain⟩ :=
        AppliedModelingLib.Foundations.Graph.exists_nodup_chain_list_of_transGen_of_no_cycle hNoCycle
          hpathTrans
      have hpathNe : path ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hlast : path.getLast hpathNe = sink := by
        simpa [List.getLast?_eq_getLast_of_ne_nil hpathNe] using hpathLast
      let owner := path[path.length - 2]
      let next : Agent → Agent := path.formPerm
      have hnextOwner : next owner = sink := by
        dsimp [next, owner]
        rw [AppliedModelingLib.Foundations.Graph.formPerm_penultimate_eq_getLast path hpathNodup hpathLength]
        exact hlast
      have hownerNe : owner ≠ sink := by
        intro hEq
        apply AppliedModelingLib.Foundations.Graph.penultimate_ne_getLast_of_nodup path hpathNodup
          hpathLength
        simpa [owner, hlast] using hEq
      have hownerSmall : cost owner item = 1 := hsmallOtherSink owner hownerNe
      have hownerMin : ∀ comparison,
          additiveChoreCost cost owner (reduced sink) ≤
            additiveChoreCost cost owner (reduced comparison) := by
        have hedge := AppliedModelingLib.Foundations.Graph.isChain_edge_formPerm_of_ne_getLast
          hpathNodup hpathChain hpathNe
          (vertex := owner)
          (by
            dsimp [owner]
            exact List.getElem_mem (by omega))
          (by
            simpa [owner, hlast] using hownerNe)
        simpa [next, hnextOwner] using hedge.2
      have hpathMin : ∀ agent, agent ≠ sink → agent ≠ owner → next agent ≠ agent →
          ∀ comparison,
            additiveChoreCost cost agent (reduced (next agent)) ≤
              additiveChoreCost cost agent (reduced comparison) := by
        intro agent hagentSink _ hchanged
        have hmem : agent ∈ path := by
          exact List.mem_of_formPerm_apply_ne (by simpa [next] using hchanged)
        have hnotLast : agent ≠ path.getLast hpathNe := by simpa [hlast] using hagentSink
        exact (AppliedModelingLib.Foundations.Graph.isChain_edge_formPerm_of_ne_getLast
          hpathNodup hpathChain hpathNe hmem hnotLast).2
      have hnextSink : next sink = cheapest := by
        dsimp [next]
        rw [← hlast]
        exact AppliedModelingLib.Foundations.Graph.formPerm_getLast_eq_head_of_head?_eq
          path hpathNe hpathHead
      have hnextInjective : Function.Injective next := by
        exact path.formPerm.injective
      have hmap : ∀ comparison,
          addItem (rotateBundles reduced next) owner item comparison =
            tentative (next comparison) := by
        intro comparison
        by_cases hcomparison : comparison = owner
        · subst comparison
          simp [tentative, addItem, rotateBundles, hnextOwner]
        · have hnextNe : next comparison ≠ sink := by
            intro hEq
            apply hcomparison
            apply hnextInjective
            exact hEq.trans hnextOwner.symm
          simp [tentative, addItem, rotateBundles, hcomparison, hnextNe]
      have hsinkMin : ∀ comparison,
          additiveChoreCost cost sink (reduced (next sink)) ≤
            additiveChoreCost cost sink
              (addItem (rotateBundles reduced next) owner item comparison) := by
        intro comparison
        rw [hmap comparison]
        have htcheap : tentative cheapest = reduced cheapest := by
          simp [tentative, addItem, hcheapestSink]
        calc
          additiveChoreCost cost sink (reduced (next sink)) =
              additiveChoreCost cost sink (tentative (next sink)) := by
            rw [hnextSink]
            exact congrArg (additiveChoreCost cost sink) htcheap.symm
          _ ≤ additiveChoreCost cost sink (tentative (next comparison)) :=
            by simpa [hnextSink] using hcheapest (next comparison) (Finset.mem_univ _)
      refine ⟨addItem (rotateBundles reduced next) owner item, ?_, ?_⟩
      · apply isAllocationOf_addItem_insert
        · exact isAllocationOf_rotate_of_bijective reduced chores next hReducedAlloc
            path.formPerm.bijective
        · exact hitem
      · exact efxForChores_addItem_after_rotation_of_minimal_path cost reduced next owner sink item
          hownerNe hnextOwner hlower
          (by
            intro hmem
            exact hitem (hReducedAlloc.1 sink item hmem))
          hownerSmall hReducedEFX hownerMin hpathMin hsinkMin

/-- Remark 3's arbitrary-agent insertion statement.  The source condition is
that at most one agent values the inserted chore at the large cost `r`; the
paper's one-or-`r` model therefore makes it small for every other agent. -/
theorem m34InsertionGeneralAgentsProof
    (Agent Item : Type) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [DecidableEq Item] (r : ℝ) (cost : ChoreCost Agent Item)
    (chores : Finset Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r) (hitem : item ∉ chores)
    (hlargeAtMostOne : ∀ first second,
      cost first item = r → cost second item = r → first = second)
    (allocation : Allocation Agent Item)
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation) :
    ∃ extended : Allocation Agent Item,
      IsAllocationOf extended (insert item chores) ∧
        EFXForChores (additiveChoreCost cost) extended := by
  refine m34InsertionOfAllOtherSmallProof Agent Item r cost chores item hr hcost hitem ?_
    allocation halloc hefx
  intro sink hsink agent hne
  have hsinkLarge : cost sink item = r := (hcost sink item).resolve_left hsink
  rcases hcost agent item with hsmall | hlarge
  · exact hsmall
  · exact (hne (hlargeAtMostOne agent sink hlarge hsinkLarge)).elim

/-- Iterating the arbitrary-agent insertion step allocates every remaining
item that is large for at most one agent, exactly as stated in Remark 3. -/
theorem m34InsertAllRemainingGeneralAgentsProof
    (Agent Item : Type) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [DecidableEq Item] (r : ℝ) (cost : ChoreCost Agent Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r) :
    ∀ (remaining chores : Finset Item),
      Disjoint remaining chores →
        (∀ item ∈ remaining, ∀ first second,
          cost first item = r → cost second item = r → first = second) →
          ∀ allocation : Allocation Agent Item,
            IsAllocationOf allocation chores →
              EFXForChores (additiveChoreCost cost) allocation →
                ∃ extended : Allocation Agent Item,
                  IsAllocationOf extended (chores ∪ remaining) ∧
                    EFXForChores (additiveChoreCost cost) extended := by
  intro remaining
  induction remaining using Finset.induction_on with
  | empty =>
      intro chores _hdisjoint _hlarge allocation halloc hefx
      exact ⟨allocation, by simpa using halloc, hefx⟩
  | @insert item remaining hitem ih =>
      intro chores hdisjoint hlarge allocation halloc hefx
      have hitemNotChores : item ∉ chores := by
        intro hmem
        exact Finset.disjoint_left.mp hdisjoint (Finset.mem_insert_self item remaining) hmem
      have hitemLarge : ∀ first second,
          cost first item = r → cost second item = r → first = second :=
        hlarge item (Finset.mem_insert_self item remaining)
      obtain ⟨withItem, hwithItemAlloc, hwithItemEfx⟩ :=
        m34InsertionGeneralAgentsProof Agent Item r cost chores item hr hcost
          hitemNotChores hitemLarge allocation halloc hefx
      have hremainingDisjoint : Disjoint remaining (insert item chores) := by
        rw [Finset.disjoint_left]
        intro candidate hcandidate hinsert
        rcases Finset.mem_insert.mp hinsert with hcandidateItem | hcandidateChores
        · exact hitem (hcandidateItem ▸ hcandidate)
        · exact Finset.disjoint_left.mp hdisjoint
            (Finset.mem_insert_of_mem hcandidate) hcandidateChores
      have hremainingLarge : ∀ candidate ∈ remaining, ∀ first second,
          cost first candidate = r → cost second candidate = r → first = second := by
        intro candidate hcandidate
        exact hlarge candidate (Finset.mem_insert_of_mem hcandidate)
      obtain ⟨extended, hextendedAlloc, hextendedEfx⟩ :=
        ih (insert item chores) hremainingDisjoint hremainingLarge withItem
          hwithItemAlloc hwithItemEfx
      refine ⟨extended, ?_, hextendedEfx⟩
      simpa [Finset.union_insert, Finset.insert_union] using hextendedAlloc

/-- Source-faithful four-agent specialization of the paper's named M34
insertion lemma. -/
theorem m34InsertionProof
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r) (hitem : item ∉ chores)
    (hsmallThree : IsSmallForAtLeastThree cost item)
    (allocation : Allocation (Fin 4) Item)
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation) :
    ∃ extended : Allocation (Fin 4) Item,
      IsAllocationOf extended (insert item chores) ∧
        EFXForChores (additiveChoreCost cost) extended := by
  refine m34InsertionOfAllOtherSmallProof (Fin 4) Item r cost chores item hr hcost hitem ?_
    allocation halloc hefx
  intro sink hsink agent hne
  have hnotSmall : ¬ IsSmallChore cost sink item := by
    simpa [IsSmallChore] using hsink
  simpa [IsSmallChore] using
    small_for_all_other_agents_of_atLeastThree cost item hsmallThree sink hnotSmall agent hne

/-- Source-faithful implementation of the paper's balanced-orientation lemma. -/
theorem balancedOrientationProof
    (Vertex Edge : Type) [Fintype Vertex] [DecidableEq Vertex] [DecidableEq Edge]
    (edges : Finset Edge) (endpoints : Edge → Finset Vertex) (quota : Vertex → ℕ)
    (hends : ∀ edge ∈ edges, (endpoints edge).card = 2) :
    (Finset.univ.sum quota = edges.card →
      ((∃ owner : Edge → Option Vertex,
        (∀ edge ∈ edges, ∃ vertex, owner edge = some vertex ∧ vertex ∈ endpoints edge) ∧
          ∀ vertex, (edges.filter fun edge => owner edge = some vertex).card = quota vertex) ↔
        ∀ vertices : Finset Vertex,
          vertices.sum quota ≤
            (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty).card)) ∧
      (Finset.univ.sum quota ≤ edges.card →
        (∀ vertices : Finset Vertex,
          vertices.sum quota ≤
            (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty).card) →
          ∃ owner : Edge → Option Vertex,
            (∀ edge ∈ edges, ∀ vertex, owner edge = some vertex → vertex ∈ endpoints edge) ∧
              ∀ vertex, (edges.filter fun edge => owner edge = some vertex).card = quota vertex) := by
  constructor
  · intro hsum
    exact balancedOrientationIff Vertex Edge edges endpoints quota hends hsum
  · intro _ hcondition
    exact partialBalancedOrientation Vertex Edge edges endpoints quota hcondition

/-- Source-faithful proof of the paper's M2 allocation lemma.  The case split
and its finite incidence arithmetic are established in `M2Orientation.lean`. -/
theorem m2EfxAllocationProof
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation :=
  existsEfxOfM2 Item r cost chores hr hcost hsmall

end HT26EFXChores
