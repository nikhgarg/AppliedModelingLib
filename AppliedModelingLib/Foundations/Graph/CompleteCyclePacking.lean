import AppliedModelingLib.Foundations.Graph.BipartitePacking

/-!
# Complete finite simple-cycle packings

A `HasBoundedSimpleCyclePeeling` records successive cycle removals.  This
module turns that recursive trace into one finite, edge-disjoint family of
actual simple cycles that covers every graph edge.  It is the graph-level
partition interface needed when a paper's statistical construction indexes
the positions of all cycles at once.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Graph

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace PartialSimpleCyclePacking

variable {G : SimpleGraph V} {maxLength : Nat}

/-- A partial simple-cycle packing is complete when its selected cycles cover
the entire edge set of its ambient graph. -/
def IsComplete (P : PartialSimpleCyclePacking G maxLength) : Prop :=
  (↑P.usedEdges : Set (Sym2 V)) = G.edgeSet

/-- The graph left after deleting every edge selected by a partial
simple-cycle packing.  This is the residual graph used to append the
Eulerian long-cycle phase to a source-capped short-cycle packing. -/
noncomputable def residual [DecidableRel G.Adj]
    (P : PartialSimpleCyclePacking G maxLength) :
    SimpleGraph V :=
  G \ SimpleGraph.fromEdgeSet (↑P.usedEdges : Set (Sym2 V))

noncomputable instance residual_decidableRel [DecidableRel G.Adj]
    (P : PartialSimpleCyclePacking G maxLength) : DecidableRel P.residual.Adj :=
  by
    classical
    unfold residual
    infer_instance

noncomputable instance usedEdgesGraph_decidableRel
    (P : PartialSimpleCyclePacking G maxLength) :
    DecidableRel (SimpleGraph.fromEdgeSet (↑P.usedEdges : Set (Sym2 V))).Adj :=
  Classical.decRel _

/-- The packing residual's edge set is exactly the ambient edge set with the
selected packing edges removed. -/
theorem edgeSet_residual [DecidableRel G.Adj]
    (P : PartialSimpleCyclePacking G maxLength) :
    P.residual.edgeSet = G.edgeSet \ (↑P.usedEdges : Set (Sym2 V)) := by
  classical
  unfold residual
  rw [SimpleGraph.edgeSet_sdiff, SimpleGraph.edgeSet_fromEdgeSet]
  ext edge
  simp only [Set.mem_diff]
  constructor
  · rintro ⟨hedgeG, hedgeNotUsed⟩
    refine ⟨hedgeG, ?_⟩
    intro hedgeUsed
    apply hedgeNotUsed
    exact ⟨hedgeUsed, G.edgeSet_subset_compl_diagSet hedgeG⟩
  · rintro ⟨hedgeG, hedgeNotUsed⟩
    refine ⟨hedgeG, ?_⟩
    rintro ⟨hedgeUsed, _⟩
    exact hedgeNotUsed hedgeUsed

/-- On a finite graph, the residual edge finset is the ambient edge finset
with precisely the selected packing edges removed. -/
theorem edgeFinset_residual [DecidableRel G.Adj]
    (P : PartialSimpleCyclePacking G maxLength) :
    P.residual.edgeFinset = G.edgeFinset \ P.usedEdges := by
  ext edge
  simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
  rw [P.edgeSet_residual]
  simp

/-- The number of residual edges is the ambient edge count minus the number
of selected packing edges. -/
theorem card_edgeFinset_residual [DecidableRel G.Adj]
    (P : PartialSimpleCyclePacking G maxLength) :
    P.residual.edgeFinset.card = G.edgeFinset.card - P.usedEdges.card := by
  rw [P.edgeFinset_residual, Finset.card_sdiff_of_subset P.usedEdges_subset_edgeFinset]

/-- Deleting any selected subgraph whose local degrees are even preserves
Eulerian parity.  The next packing-specific lemma constructs the required
even-degree fact from the individual edge-disjoint simple cycles. -/
theorem even_degree_sdiff_usedEdges_of_even_degree [DecidableRel G.Adj]
    (P : PartialSimpleCyclePacking G maxLength)
    (hdegree : ∀ vertex : V, Even (G.degree vertex))
    (hselected : ∀ vertex : V,
      Even ((SimpleGraph.fromEdgeSet (↑P.usedEdges : Set (Sym2 V))).degree vertex)) :
    ∀ vertex : V, Even ((G \ SimpleGraph.fromEdgeSet
      (↑P.usedEdges : Set (Sym2 V))).degree vertex) := by
  have hselectedLe :
      SimpleGraph.fromEdgeSet (↑P.usedEdges : Set (Sym2 V)) ≤ G := by
    rw [SimpleGraph.fromEdgeSet_le]
    intro edge hedge
    have hedgeFinite := P.usedEdges_subset_edgeFinset hedge.1
    rwa [SimpleGraph.mem_edgeFinset] at hedgeFinite
  intro vertex
  have hsum := degree_sdiff_add_degree_of_le hselectedLe vertex
  have htotal := hdegree vertex
  rw [← hsum] at htotal
  exact (Nat.even_add.mp htotal).mpr (hselected vertex)

/-- At a vertex, edge-disjoint graph summands have additive degree count.
Using `degreeCount` keeps this finite identity independent of a particular
decidable-relation implementation for the union graph. -/
theorem degreeCount_sup_eq_add_of_disjoint
    {H₁ H₂ : SimpleGraph V} (hdisjoint : Disjoint H₁ H₂) (vertex : V) :
    degreeCount (H₁ ⊔ H₂) vertex = degreeCount H₁ vertex + degreeCount H₂ vertex := by
  classical
  letI : DecidableRel H₁.Adj := Classical.decRel _
  letI : DecidableRel H₂.Adj := Classical.decRel _
  letI : DecidableRel (H₁ ⊔ H₂).Adj := Classical.decRel _
  have hneighbor : (H₁ ⊔ H₂).neighborFinset vertex =
      H₁.neighborFinset vertex ∪ H₂.neighborFinset vertex := by
    ext neighbor
    simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj]
  have hneighborDisjoint : Disjoint (H₁.neighborFinset vertex) (H₂.neighborFinset vertex) := by
    apply Finset.disjoint_left.mpr
    intro neighbor hfirst hsecond
    have hedgeDisjoint : Disjoint H₁.edgeSet H₂.edgeSet :=
      SimpleGraph.disjoint_edgeSet.mpr hdisjoint
    exact Set.disjoint_left.mp hedgeDisjoint
      (H₁.mem_edgeSet.mpr
        ((SimpleGraph.mem_neighborFinset H₁ vertex neighbor).mp hfirst))
      (H₂.mem_edgeSet.mpr
        ((SimpleGraph.mem_neighborFinset H₂ vertex neighbor).mp hsecond))
  rw [degreeCount_eq_degree, degreeCount_eq_degree, degreeCount_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree, hneighbor,
    Finset.card_union_of_disjoint hneighborDisjoint]

/-- A disjoint union of finite even-degree graphs is again even-degree. -/
theorem even_degreeCount_sup_of_disjoint
    {H₁ H₂ : SimpleGraph V} (hdisjoint : Disjoint H₁ H₂)
    (hfirst : ∀ vertex : V, Even (degreeCount H₁ vertex))
    (hsecond : ∀ vertex : V, Even (degreeCount H₂ vertex)) :
    ∀ vertex : V, Even (degreeCount (H₁ ⊔ H₂) vertex) := by
  intro vertex
  rw [degreeCount_sup_eq_add_of_disjoint hdisjoint]
  exact (hfirst vertex).add (hsecond vertex)

/-- A finite edge-disjoint union of even-degree graphs is even-degree.
This is the finite aggregation step needed to turn an actual family of
edge-disjoint simple cycles into an Eulerian selected-edge graph. -/
theorem even_degreeCount_finsetSup_of_pairwiseDisjoint
    {ι : Type*} [DecidableEq ι] (indices : Finset ι) (graphs : ι → SimpleGraph V)
    (hdisjoint : Set.PairwiseDisjoint (↑indices : Set ι) graphs)
    (heven : ∀ index ∈ indices, ∀ vertex : V, Even (degreeCount (graphs index) vertex)) :
    ∀ vertex : V, Even (degreeCount (indices.sup graphs) vertex) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    intro vertex
    simp [degreeCount]
  | @insert first rest hfirst ih =>
    intro vertex
    rw [Finset.sup_insert]
    apply even_degreeCount_sup_of_disjoint
    · rw [Finset.disjoint_sup_right]
      intro other hother
      apply hdisjoint (by simp) (by simp [hother])
      intro hEq
      subst other
      exact hfirst hother
    · exact heven first (by simp)
    · apply ih
      · intro second hsecond third hthird hne
        exact hdisjoint (by simp [hsecond]) (by simp [hthird]) hne
      · intro index hindex
        exact heven index (by simp [hindex])

/-- The edge set of a finite supremum of graphs is the finite union of the
edge sets of its summands.  The finite-edge presentation is convenient when
the same union is also recorded by a cycle packing. -/
theorem edgeSet_finsetSup_eq_coe_biUnion
    {ι : Type*} [DecidableEq ι] (indices : Finset ι) (graphs : ι → SimpleGraph V)
    (edges : ι → Finset (Sym2 V))
    (hedges : ∀ index, (graphs index).edgeSet = (↑(edges index) : Set (Sym2 V))) :
    (indices.sup graphs).edgeSet = (↑(indices.biUnion edges) : Set (Sym2 V)) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | insert first rest hfirst ih =>
    rw [Finset.sup_insert, SimpleGraph.edgeSet_sup, ih,
      Finset.biUnion_insert, hedges]
    ext edge
    simp

/-- The spanning graph of one selected packing cycle. -/
noncomputable def cycleGraph (P : PartialSimpleCyclePacking G maxLength)
    (cycle : P.Cycle) : SimpleGraph V :=
  (P.walk cycle).2.toSubgraph.spanningCoe

/-- The graph consisting of exactly the union of all selected packing cycles. -/
noncomputable def selectedGraph (P : PartialSimpleCyclePacking G maxLength) : SimpleGraph V :=
  Finset.univ.sup P.cycleGraph

/-- A selected cycle graph carries exactly the edges traversed by that cycle. -/
theorem edgeSet_cycleGraph (P : PartialSimpleCyclePacking G maxLength) (cycle : P.Cycle) :
    (P.cycleGraph cycle).edgeSet = (↑((P.walk cycle).2.edges.toFinset) : Set (Sym2 V)) := by
  unfold cycleGraph
  rw [SimpleGraph.Subgraph.edgeSet_spanningCoe, (P.walk cycle).2.edgeSet_toSubgraph]
  ext edge
  simp

/-- The cycle graphs of a packing are pairwise edge-disjoint. -/
theorem pairwiseDisjoint_cycleGraph (P : PartialSimpleCyclePacking G maxLength) :
    Set.PairwiseDisjoint Set.univ P.cycleGraph := by
  intro first _ second _ hne
  apply SimpleGraph.disjoint_edgeSet.mp
  rw [P.edgeSet_cycleGraph, P.edgeSet_cycleGraph]
  exact Finset.disjoint_coe.mpr
    (P.pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) hne)

/-- Each selected simple cycle graph has even degree at every vertex. -/
theorem even_degreeCount_cycleGraph (P : PartialSimpleCyclePacking G maxLength)
    [DecidableRel G.Adj] (cycle : P.Cycle) :
    ∀ vertex : V, Even (degreeCount (P.cycleGraph cycle) vertex) := by
  classical
  letI : DecidableRel (P.cycleGraph cycle).Adj := Classical.decRel _
  intro vertex
  rw [degreeCount_eq_degree]
  simpa [cycleGraph] using
    (even_degree_spanningCoe_of_simpleCycle (P.isCycle cycle) vertex)

/-- The selected graph has exactly the packing's finite union of used edges. -/
theorem edgeSet_selectedGraph (P : PartialSimpleCyclePacking G maxLength) :
    P.selectedGraph.edgeSet = (↑P.usedEdges : Set (Sym2 V)) := by
  change (Finset.univ.sup P.cycleGraph).edgeSet =
    (↑(Finset.univ.biUnion fun cycle => (P.walk cycle).2.edges.toFinset) : Set (Sym2 V))
  exact edgeSet_finsetSup_eq_coe_biUnion Finset.univ P.cycleGraph
    (fun cycle => (P.walk cycle).2.edges.toFinset) P.edgeSet_cycleGraph

/-- The selected graph agrees with the graph made directly from the packing's
used-edge set.  All packed edges are ambient graph edges, hence non-loops. -/
theorem selectedGraph_eq_usedEdgesGraph [DecidableRel G.Adj]
    (P : PartialSimpleCyclePacking G maxLength) :
    P.selectedGraph = SimpleGraph.fromEdgeSet (↑P.usedEdges : Set (Sym2 V)) := by
  apply SimpleGraph.edgeSet_injective
  rw [P.edgeSet_selectedGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext edge
  simp only [Set.mem_diff]
  constructor
  · intro hedge
    refine ⟨hedge, ?_⟩
    have hedgeAmbient := P.usedEdges_subset_edgeFinset hedge
    rw [SimpleGraph.mem_edgeFinset] at hedgeAmbient
    exact G.edgeSet_subset_compl_diagSet hedgeAmbient
  · exact fun hedge => hedge.1

/-- The graph formed by all selected packing edges is Eulerian. -/
theorem even_degreeCount_selectedGraph [DecidableRel G.Adj]
    (P : PartialSimpleCyclePacking G maxLength) :
    ∀ vertex : V, Even (degreeCount P.selectedGraph vertex) := by
  apply even_degreeCount_finsetSup_of_pairwiseDisjoint Finset.univ P.cycleGraph
  · simpa using P.pairwiseDisjoint_cycleGraph
  · intro cycle _
    exact P.even_degreeCount_cycleGraph cycle

/-- The direct used-edge graph of a packing has even degree at every vertex. -/
theorem even_degree_usedEdgesGraph [DecidableRel G.Adj]
    (P : PartialSimpleCyclePacking G maxLength) :
    ∀ vertex : V,
      Even ((SimpleGraph.fromEdgeSet (↑P.usedEdges : Set (Sym2 V))).degree vertex) := by
  intro vertex
  have hselected := P.even_degreeCount_selectedGraph vertex
  have hsame : degreeCount P.selectedGraph vertex =
      degreeCount (SimpleGraph.fromEdgeSet (↑P.usedEdges : Set (Sym2 V))) vertex := by
    rw [P.selectedGraph_eq_usedEdgesGraph]
  rw [hsame] at hselected
  rwa [degreeCount_eq_degree] at hselected

/-- Concatenate two edge-disjoint finite simple-cycle packings in a common
ambient graph.  The resulting family remembers which phase supplied each
cycle and uses the larger of the two length caps. -/
noncomputable def append {leftMaxLength rightMaxLength : Nat}
    (P : PartialSimpleCyclePacking G leftMaxLength)
    (Q : PartialSimpleCyclePacking G rightMaxLength)
    (hdisjoint : Disjoint P.usedEdges Q.usedEdges) :
    PartialSimpleCyclePacking G (max leftMaxLength rightMaxLength) where
  Cycle := Sum P.Cycle Q.Cycle
  instFintypeCycle := inferInstance
  instDecidableEqCycle := inferInstance
  walk := fun cycle => match cycle with
    | .inl cycle => P.walk cycle
    | .inr cycle => Q.walk cycle
  isCycle := fun cycle => by
    cases cycle with
    | inl cycle => exact P.isCycle cycle
    | inr cycle => exact Q.isCycle cycle
  length_le := fun cycle => by
    cases cycle with
    | inl cycle => exact (P.length_le cycle).trans (Nat.le_max_left _ _)
    | inr cycle => exact (Q.length_le cycle).trans (Nat.le_max_right _ _)
  pairwiseDisjoint := by
    intro first _ second _ hne
    cases first with
    | inl first =>
      cases second with
      | inl second =>
        apply P.pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _)
        intro heq
        apply hne
        simpa [heq]
      | inr second =>
        apply Finset.disjoint_left.mpr
        intro edge hedgeFirst hedgeSecond
        exact (Finset.disjoint_left.mp hdisjoint
          (P.cycleEdges_subset_usedEdges first hedgeFirst)
          (Q.cycleEdges_subset_usedEdges second hedgeSecond))
    | inr first =>
      cases second with
      | inl second =>
        apply Finset.disjoint_left.mpr
        intro edge hedgeFirst hedgeSecond
        exact (Finset.disjoint_left.mp hdisjoint
          (P.cycleEdges_subset_usedEdges second hedgeSecond)
          (Q.cycleEdges_subset_usedEdges first hedgeFirst))
      | inr second =>
        apply Q.pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _)
        intro heq
        apply hne
        simpa [heq]

/-- The left-tagged cycles in an appended packing are exactly the cycles of
the left phase. -/
@[simp] theorem walk_append_inl {leftMaxLength rightMaxLength : Nat}
    (P : PartialSimpleCyclePacking G leftMaxLength)
    (Q : PartialSimpleCyclePacking G rightMaxLength)
    (hdisjoint : Disjoint P.usedEdges Q.usedEdges) (cycle : P.Cycle) :
    (P.append Q hdisjoint).walk (Sum.inl cycle) = P.walk cycle := rfl

/-- The right-tagged cycles in an appended packing are exactly the cycles of
the right phase. -/
@[simp] theorem walk_append_inr {leftMaxLength rightMaxLength : Nat}
    (P : PartialSimpleCyclePacking G leftMaxLength)
    (Q : PartialSimpleCyclePacking G rightMaxLength)
    (hdisjoint : Disjoint P.usedEdges Q.usedEdges) (cycle : Q.Cycle) :
    (P.append Q hdisjoint).walk (Sum.inr cycle) = Q.walk cycle := rfl

/-- The used edges of an appended packing are the union of its two phases. -/
theorem usedEdges_append {leftMaxLength rightMaxLength : Nat}
    (P : PartialSimpleCyclePacking G leftMaxLength)
    (Q : PartialSimpleCyclePacking G rightMaxLength)
    (hdisjoint : Disjoint P.usedEdges Q.usedEdges) :
    (P.append Q hdisjoint).usedEdges = P.usedEdges ∪ Q.usedEdges := by
  ext edge
  simp only [usedEdges, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨(_ | cycle), hedge⟩
    · exact Or.inl ⟨_, by simpa [append] using hedge⟩
    · exact Or.inr ⟨_, by simpa [append] using hedge⟩
  · rintro (⟨cycle, hedge⟩ | ⟨cycle, hedge⟩)
    · exact ⟨Sum.inl cycle, by simpa [append] using hedge⟩
    · exact ⟨Sum.inr cycle, by simpa [append] using hedge⟩

/-- If the two packed edge sets cover the ambient graph, their appended
packing is complete. -/
theorem isComplete_append_of_usedEdges_union {leftMaxLength rightMaxLength : Nat}
    (P : PartialSimpleCyclePacking G leftMaxLength)
    (Q : PartialSimpleCyclePacking G rightMaxLength)
    (hdisjoint : Disjoint P.usedEdges Q.usedEdges)
    (hcover : (↑P.usedEdges : Set (Sym2 V)) ∪ (↑Q.usedEdges : Set (Sym2 V)) = G.edgeSet) :
    (P.append Q hdisjoint).IsComplete := by
  unfold IsComplete
  rw [P.usedEdges_append Q hdisjoint]
  simpa using hcover

/-- Every finite simple-cycle peeling yields a complete packing of actual
simple cycles.  The universal vertex-cardinality cap keeps the statement
independent of a separate cycle-length argument. -/
theorem exists_complete_of_simpleCyclePeeling
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (peeling : HasSimpleCyclePeeling G) :
    ∃ P : PartialSimpleCyclePacking G (Fintype.card V), P.IsComplete := by
  induction peeling with
  | empty =>
    refine ⟨empty (⊥ : SimpleGraph V) (Fintype.card V), ?_⟩
    unfold IsComplete
    rw [usedEdges_empty]
    simp
  | @step G start cycle hcycle peeling ih =>
    classical
    letI : DecidableRel G.Adj := Classical.decRel _
    obtain ⟨P, hcomplete⟩ := ih
    have hresidualLe : cycleResidual cycle ≤ G := by
      unfold cycleResidual
      exact sdiff_le
    have husedResidual : P.usedEdges ⊆ (cycleResidual cycle).edgeFinset :=
      P.usedEdges_subset_edgeFinset
    have hdisjoint : Disjoint cycle.edges.toFinset
        (P.lift hresidualLe).usedEdges := by
      rw [usedEdges_lift]
      apply Finset.disjoint_left.2
      intro edge hedgeCycle hedgePacked
      have hedgeResidual := husedResidual hedgePacked
      rw [edgeFinset_cycleResidual] at hedgeResidual
      exact (Finset.mem_sdiff.mp hedgeResidual).2 hedgeCycle
    have hlength : cycle.length ≤ Fintype.card V :=
      simpleCycle_length_le_card_vertices hcycle
    refine ⟨cons cycle hcycle hlength (P.lift hresidualLe) hdisjoint, ?_⟩
    have hcompleteFinset : P.usedEdges = (cycleResidual cycle).edgeFinset := by
      ext edge
      rw [SimpleGraph.mem_edgeFinset]
      rw [← hcomplete]
      rfl
    unfold IsComplete
    rw [usedEdges_cons, usedEdges_lift, hcompleteFinset, edgeFinset_cycleResidual]
    have hsubset : cycle.edges.toFinset ⊆ G.edgeFinset := by
      intro edge hedge
      rw [SimpleGraph.mem_edgeFinset]
      exact cycle.edges_subset_edgeSet (by simpa using hedge)
    rw [Finset.union_sdiff_of_subset hsubset, SimpleGraph.coe_edgeFinset]

/-- A bounded simple-cycle peeling yields a complete packing at its stated
bound, preserving the length control on every cycle. -/
theorem exists_complete_of_boundedSimpleCyclePeeling
    {G : SimpleGraph V} [DecidableRel G.Adj] {bound : Nat}
    (peeling : HasBoundedSimpleCyclePeeling bound G) :
    ∃ P : PartialSimpleCyclePacking G bound, P.IsComplete := by
  induction peeling with
  | empty =>
    refine ⟨empty (⊥ : SimpleGraph V) bound, ?_⟩
    unfold IsComplete
    rw [usedEdges_empty]
    simp
  | @step G start cycle hcycle hlength peeling ih =>
    classical
    letI : DecidableRel G.Adj := Classical.decRel _
    obtain ⟨P, hcomplete⟩ := ih
    have hresidualLe : cycleResidual cycle ≤ G := by
      unfold cycleResidual
      exact sdiff_le
    have husedResidual : P.usedEdges ⊆ (cycleResidual cycle).edgeFinset :=
      P.usedEdges_subset_edgeFinset
    have hdisjoint : Disjoint cycle.edges.toFinset
        (P.lift hresidualLe).usedEdges := by
      rw [usedEdges_lift]
      apply Finset.disjoint_left.2
      intro edge hedgeCycle hedgePacked
      have hedgeResidual := husedResidual hedgePacked
      rw [edgeFinset_cycleResidual] at hedgeResidual
      exact (Finset.mem_sdiff.mp hedgeResidual).2 hedgeCycle
    refine ⟨cons cycle hcycle hlength (P.lift hresidualLe) hdisjoint, ?_⟩
    have hcompleteFinset : P.usedEdges = (cycleResidual cycle).edgeFinset := by
      ext edge
      rw [SimpleGraph.mem_edgeFinset]
      rw [← hcomplete]
      rfl
    unfold IsComplete
    rw [usedEdges_cons, usedEdges_lift, hcompleteFinset, edgeFinset_cycleResidual]
    have hsubset : cycle.edges.toFinset ⊆ G.edgeFinset := by
      intro edge hedge
      rw [SimpleGraph.mem_edgeFinset]
      exact cycle.edges_subset_edgeSet (by simpa using hedge)
    rw [Finset.union_sdiff_of_subset hsubset, SimpleGraph.coe_edgeFinset]

/-- A complete packing identifies every graph edge with exactly one position
in exactly one selected simple cycle.  The equivalence follows from coverage,
the packing's pairwise edge disjointness, and the no-repeated-edge property of
each simple cycle. -/
noncomputable def edgePositionEquiv (P : PartialSimpleCyclePacking G maxLength)
    (hcomplete : P.IsComplete) :
    (Sigma fun cycle => Fin ((P.walk cycle).2.length)) ≃ G.edgeSet := by
  apply Equiv.ofBijective (fun position =>
    ⟨(simpleCycleEdgePositionEquiv (P.isCycle position.1) position.2).1, by
      exact (P.walk position.1).2.edges_subset_edgeSet
        (List.mem_toFinset.mp (simpleCycleEdgePositionEquiv
          (P.isCycle position.1) position.2).2)⟩)
  constructor
  · rintro ⟨first, firstPosition⟩ ⟨second, secondPosition⟩ hEq
    have hedge :
        (simpleCycleEdgePositionEquiv (P.isCycle first) firstPosition).1 =
          (simpleCycleEdgePositionEquiv (P.isCycle second) secondPosition).1 :=
      congrArg Subtype.val hEq
    by_cases hcycle : first = second
    · subst second
      have hposition : firstPosition = secondPosition := by
        apply (simpleCycleEdgePositionEquiv (P.isCycle first)).injective
        exact Subtype.ext hedge
      exact Sigma.ext rfl (heq_of_eq hposition)
    · have hdisjoint := P.pairwiseDisjoint (Set.mem_univ first) (Set.mem_univ second) hcycle
      exact False.elim ((Finset.disjoint_left.mp hdisjoint)
        (simpleCycleEdgePositionEquiv (P.isCycle first) firstPosition).2
        (by rw [hedge]
            exact (simpleCycleEdgePositionEquiv (P.isCycle second) secondPosition).2))
  · rintro ⟨edge, hedge⟩
    have hedgeUsed : edge ∈ P.usedEdges := by
      have : edge ∈ (↑P.usedEdges : Set (Sym2 V)) := by
        rw [hcomplete]
        exact hedge
      exact this
    rcases Finset.mem_biUnion.mp hedgeUsed with ⟨cycle, _, hedgeCycle⟩
    let localEquiv := simpleCycleEdgePositionEquiv (P.isCycle cycle)
    refine ⟨⟨cycle, localEquiv.symm ⟨edge, hedgeCycle⟩⟩, ?_⟩
    apply Subtype.ext
    change (localEquiv (localEquiv.symm ⟨edge, hedgeCycle⟩)).1 = edge
    exact congrArg Subtype.val (localEquiv.apply_symm_apply ⟨edge, hedgeCycle⟩)

theorem edgePositionEquiv_apply (P : PartialSimpleCyclePacking G maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (position : Fin ((P.walk cycle).2.length)) :
    (P.edgePositionEquiv hcomplete ⟨cycle, position⟩).1 =
      (simpleCycleEdgePositionEquiv (P.isCycle cycle) position).1 := rfl

/-- In a complete packing, the sum of all selected cycle lengths is exactly
the number of graph edges. -/
theorem sum_length_eq_edgeSet_card (P : PartialSimpleCyclePacking G maxLength)
    [DecidableRel G.Adj] (hcomplete : P.IsComplete) :
    (∑ cycle : P.Cycle, (P.walk cycle).2.length) = Fintype.card G.edgeSet := by
  calc
    (∑ cycle : P.Cycle, (P.walk cycle).2.length) =
        Fintype.card (Sigma fun cycle => Fin ((P.walk cycle).2.length)) := by simp
    _ = Fintype.card G.edgeSet := Fintype.card_congr (P.edgePositionEquiv hcomplete)

end PartialSimpleCyclePacking

end Graph
end Foundations
end AppliedModelingLib
