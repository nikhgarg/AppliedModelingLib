import AppliedModelingLib.Foundations.Graph.BipartitePruning

/-!
# Witnesses for finite bipartite short-cycle packings

The pruning/BFS trace records its choices inductively.  This module turns that
trace into a finite, edge-disjoint family of actual simple cycles and proves
that the original edges outside that family are bounded by the trace's
discard budget.  It is the graph object used by the bipartite cycle-packing
lemma before the remaining Eulerian orientation bridge.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Graph

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite, edge-disjoint family of actual simple cycles in a graph. -/
structure PartialSimpleCyclePacking (G : SimpleGraph V) (maxLength : Nat) where
  Cycle : Type
  instFintypeCycle : Fintype Cycle
  instDecidableEqCycle : DecidableEq Cycle
  walk : (cycle : Cycle) → Σ start : V, G.Walk start start
  isCycle : ∀ cycle, (walk cycle).2.IsCycle
  length_le : ∀ cycle, (walk cycle).2.length ≤ maxLength
  pairwiseDisjoint : Set.PairwiseDisjoint Set.univ
    (fun cycle => (walk cycle).2.edges.toFinset)

attribute [instance] PartialSimpleCyclePacking.instFintypeCycle
  PartialSimpleCyclePacking.instDecidableEqCycle

namespace PartialSimpleCyclePacking

variable {G : SimpleGraph V} {maxLength : Nat} (P : PartialSimpleCyclePacking G maxLength)

/-- The original graph edges covered by the cycle family. -/
noncomputable def usedEdges : Finset (Sym2 V) :=
  Finset.univ.biUnion (fun cycle => (P.walk cycle).2.edges.toFinset)

noncomputable def empty (G : SimpleGraph V) (maxLength : Nat) :
    PartialSimpleCyclePacking G maxLength where
  Cycle := Empty
  instFintypeCycle := inferInstance
  instDecidableEqCycle := inferInstance
  walk := fun cycle => nomatch cycle
  isCycle := fun cycle => nomatch cycle
  length_le := fun cycle => nomatch cycle
  pairwiseDisjoint := by
    intro first _
    exact nomatch first

omit [Fintype V] in
@[simp] theorem usedEdges_empty (G : SimpleGraph V) (maxLength : Nat) :
    (empty G maxLength).usedEdges = ∅ := by
  simp [usedEdges, empty]

theorem usedEdges_subset_edgeFinset [DecidableRel G.Adj] :
    P.usedEdges ⊆ G.edgeFinset := by
  intro edge hedge
  rcases Finset.mem_biUnion.mp hedge with ⟨cycle, hcycle, hedgeCycle⟩
  rw [SimpleGraph.mem_edgeFinset]
  exact (P.walk cycle).2.edges_subset_edgeSet (by simpa using hedgeCycle)

omit [Fintype V] in
theorem cycleEdges_subset_usedEdges (cycle : P.Cycle) :
    (P.walk cycle).2.edges.toFinset ⊆ P.usedEdges := by
  intro edge hedge
  apply Finset.mem_biUnion.mpr
  exact ⟨cycle, Finset.mem_univ _, hedge⟩

/-- Regard a cycle family in a subgraph as a family in a supergraph. -/
noncomputable def lift {H : SimpleGraph V} (hHG : H ≤ G)
    (P : PartialSimpleCyclePacking H maxLength) :
    PartialSimpleCyclePacking G maxLength where
  Cycle := P.Cycle
  instFintypeCycle := P.instFintypeCycle
  instDecidableEqCycle := P.instDecidableEqCycle
  walk := fun cycle =>
    let walk := P.walk cycle
    ⟨walk.1, walk.2.mapLe hHG⟩
  isCycle := fun cycle => (P.isCycle cycle).mapLe hHG
  length_le := fun cycle => by
    change ((P.walk cycle).2.map (.ofLE hHG)).length ≤ maxLength
    rw [SimpleGraph.Walk.length_map]
    exact P.length_le cycle
  pairwiseDisjoint := by
    intro first _ second _ hne
    simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using
      P.pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) hne

omit [Fintype V] in
theorem usedEdges_lift {H : SimpleGraph V} (hHG : H ≤ G)
    (P : PartialSimpleCyclePacking H maxLength) :
    (P.lift hHG).usedEdges = P.usedEdges := by
  ext edge
  simp [usedEdges, lift, SimpleGraph.Walk.edges_mapLe_eq_edges]

/-- Lifting a packed cycle along a graph inclusion does not change its
length. -/
theorem length_lift {H : SimpleGraph V} (hHG : H ≤ G)
    (P : PartialSimpleCyclePacking H maxLength) (cycle : P.Cycle) :
    ((P.lift hHG).walk cycle).2.length = (P.walk cycle).2.length := by
  change ((P.walk cycle).2.map (.ofLE hHG)).length = (P.walk cycle).2.length
  rw [SimpleGraph.Walk.length_map]

/-- Add one simple cycle that is edge-disjoint from an existing family. -/
noncomputable def cons {start : V} (walk : G.Walk start start)
    (hcycle : walk.IsCycle) (hlength : walk.length ≤ maxLength)
    (P : PartialSimpleCyclePacking G maxLength)
    (hdisjoint : Disjoint walk.edges.toFinset P.usedEdges) :
    PartialSimpleCyclePacking G maxLength where
  Cycle := Option P.Cycle
  instFintypeCycle := inferInstance
  instDecidableEqCycle := inferInstance
  walk := fun cycle =>
    match cycle with
    | none => ⟨start, walk⟩
    | some cycle => P.walk cycle
  isCycle := fun cycle => by
    cases cycle with
    | none => exact hcycle
    | some cycle => exact P.isCycle cycle
  length_le := fun cycle => by
    cases cycle with
    | none => exact hlength
    | some cycle => exact P.length_le cycle
  pairwiseDisjoint := by
    intro first _ second _ hne
    cases first with
    | none =>
      cases second with
      | none => exact False.elim (hne rfl)
      | some second =>
        apply Finset.disjoint_left.2
        intro edge hedgeWalk hedgeSecond
        exact (Finset.disjoint_left.mp hdisjoint hedgeWalk)
          (P.cycleEdges_subset_usedEdges second hedgeSecond)
    | some first =>
      cases second with
      | none =>
        apply Finset.disjoint_left.2
        intro edge hedgeFirst hedgeWalk
        exact (Finset.disjoint_left.mp hdisjoint hedgeWalk)
          (P.cycleEdges_subset_usedEdges first hedgeFirst)
      | some second =>
        apply P.pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _)
        intro hEq
        apply hne
        simp [hEq]

omit [Fintype V] in
theorem usedEdges_cons {start : V} (walk : G.Walk start start)
    (hcycle : walk.IsCycle) (hlength : walk.length ≤ maxLength)
    (P : PartialSimpleCyclePacking G maxLength)
    (hdisjoint : Disjoint walk.edges.toFinset P.usedEdges) :
    (cons walk hcycle hlength P hdisjoint).usedEdges = walk.edges.toFinset ∪ P.usedEdges := by
  ext edge
  simp only [usedEdges, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨(_ | cycle), hedge⟩
    · exact Or.inl hedge
    · exact Or.inr ⟨cycle, hedge⟩
  · rintro (hedge | ⟨cycle, hedge⟩)
    · exact ⟨none, hedge⟩
    · exact ⟨some cycle, hedge⟩

/-- Preserve the same cycle family while increasing its stated length cap. -/
noncomputable def relaxLength {newMaxLength : Nat}
    (hbound : maxLength ≤ newMaxLength) :
    PartialSimpleCyclePacking G newMaxLength where
  Cycle := P.Cycle
  instFintypeCycle := P.instFintypeCycle
  instDecidableEqCycle := P.instDecidableEqCycle
  walk := P.walk
  isCycle := P.isCycle
  length_le := fun cycle => (P.length_le cycle).trans hbound
  pairwiseDisjoint := P.pairwiseDisjoint

omit [Fintype V] in
theorem usedEdges_relaxLength {newMaxLength : Nat}
    (hbound : maxLength ≤ newMaxLength) :
    (P.relaxLength hbound).usedEdges = P.usedEdges := by
  rfl

/-- The pruning/BFS trace yields a genuine partial cycle decomposition: all
selected cycles are simple, pairwise edge-disjoint, and logarithmically
bounded, while at most the trace budget of original edges remains uncovered. -/
theorem BipartiteCyclePacking.exists_partialSimpleCyclePacking
    {G : SimpleGraph V} {left right : Set V} {k : Nat}
    (packing : BipartiteCyclePacking G left right k) :
    ∃ P : PartialSimpleCyclePacking G (4 * Nat.log 2 left.ncard),
      edgeCount G - P.usedEdges.card ≤ k := by
  induction packing with
  | done G left right hzero =>
    refine ⟨empty G (4 * Nat.log 2 left.ncard), ?_⟩
    rw [usedEdges_empty]
    simp [hzero]
  | discardLeft G left right vertex k hleft hpositive hsmall packing ih =>
    classical
    letI : DecidableRel G.Adj := Classical.decRel _
    obtain ⟨P, hbudget⟩ := ih
    have hcard : (left \ {vertex}).ncard ≤ left.ncard :=
      Set.ncard_mono Set.diff_subset
    have hlength : 4 * Nat.log 2 (left \ {vertex}).ncard ≤
        4 * Nat.log 2 left.ncard := by
      exact Nat.mul_le_mul_left _ (Nat.log_mono_right hcard)
    refine ⟨(P.lift (SimpleGraph.deleteIncidenceSet_le G vertex)).relaxLength hlength, ?_⟩
    rw [usedEdges_relaxLength, usedEdges_lift]
    have hdelete : edgeCount (G.deleteIncidenceSet vertex) =
        edgeCount G - degreeCount G vertex := by
      rw [edgeCount_eq_edgeFinset_card, edgeCount_eq_edgeFinset_card, degreeCount_eq_degree]
      exact SimpleGraph.card_edgeFinset_deleteIncidenceSet G vertex
    omega
  | discardRight G left right vertex k hright hpositive hsmall packing ih =>
    classical
    letI : DecidableRel G.Adj := Classical.decRel _
    obtain ⟨P, hbudget⟩ := ih
    refine ⟨P.lift (SimpleGraph.deleteIncidenceSet_le G vertex), ?_⟩
    rw [usedEdges_lift]
    have hdelete : edgeCount (G.deleteIncidenceSet vertex) =
        edgeCount G - degreeCount G vertex := by
      rw [edgeCount_eq_edgeFinset_card, edgeCount_eq_edgeFinset_card, degreeCount_eq_degree]
      exact SimpleGraph.card_edgeFinset_deleteIncidenceSet G vertex
    omega
  | cycle G left right start walk k hcycle hlength packing ih =>
    classical
    letI : DecidableRel G.Adj := Classical.decRel _
    have hresidualLe : cycleResidual walk ≤ G := by
      unfold cycleResidual
      exact sdiff_le
    obtain ⟨P, hbudget⟩ := ih
    have husedResidual : P.usedEdges ⊆ (cycleResidual walk).edgeFinset :=
      P.usedEdges_subset_edgeFinset
    have hdisjoint : Disjoint walk.edges.toFinset
        (P.lift hresidualLe).usedEdges := by
      rw [usedEdges_lift]
      apply Finset.disjoint_left.2
      intro edge hedgeWalk hedgePacked
      have hedgeResidual := husedResidual hedgePacked
      rw [edgeFinset_cycleResidual] at hedgeResidual
      exact (Finset.mem_sdiff.mp hedgeResidual).2 hedgeWalk
    refine ⟨cons walk hcycle hlength (P.lift hresidualLe) hdisjoint, ?_⟩
    rw [usedEdges_cons, usedEdges_lift]
    have hcycleSubset : walk.edges.toFinset ⊆ G.edgeFinset := by
      intro edge hedge
      rw [SimpleGraph.mem_edgeFinset]
      exact walk.edges_subset_edgeSet (by simpa using hedge)
    have husedSubset : P.usedEdges ⊆ G.edgeFinset :=
      husedResidual.trans (SimpleGraph.edgeFinset_mono hresidualLe)
    have hunionSubset : walk.edges.toFinset ∪ P.usedEdges ⊆ G.edgeFinset :=
      Finset.union_subset hcycleSubset husedSubset
    have hremaining : G.edgeFinset \ (walk.edges.toFinset ∪ P.usedEdges) =
        (cycleResidual walk).edgeFinset \ P.usedEdges := by
      rw [edgeFinset_cycleResidual]
      ext edge
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    calc
      edgeCount G - (walk.edges.toFinset ∪ P.usedEdges).card =
          (G.edgeFinset \ (walk.edges.toFinset ∪ P.usedEdges)).card := by
        rw [edgeCount_eq_edgeFinset_card]
        exact (Finset.card_sdiff_of_subset hunionSubset).symm
      _ = ((cycleResidual walk).edgeFinset \ P.usedEdges).card := by rw [hremaining]
      _ = edgeCount (cycleResidual walk) - P.usedEdges.card := by
        rw [edgeCount_eq_edgeFinset_card]
        exact Finset.card_sdiff_of_subset husedResidual
      _ ≤ k := hbudget

end PartialSimpleCyclePacking

/-- The pruning/BFS trace yields a genuine partial cycle decomposition: all
selected cycles are simple, pairwise edge-disjoint, and logarithmically
bounded, while at most the trace budget of original edges remains uncovered. -/
theorem BipartiteCyclePacking.exists_partialSimpleCyclePacking
    {G : SimpleGraph V} {left right : Set V} {k : Nat}
    (packing : BipartiteCyclePacking G left right k) :
    ∃ P : PartialSimpleCyclePacking G (4 * Nat.log 2 left.ncard),
      edgeCount G - P.usedEdges.card ≤ k :=
  PartialSimpleCyclePacking.BipartiteCyclePacking.exists_partialSimpleCyclePacking packing

end Graph
end Foundations
end AppliedModelingLib
