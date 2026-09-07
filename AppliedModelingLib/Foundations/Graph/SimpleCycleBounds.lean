import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Bounds for finite simple cycles

These elementary bounds are the residual-cycle ingredient in finite
short-cycle decompositions.  They are stated for Mathlib's simple-graph walks,
so they can be reused independently of a particular decomposition algorithm.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Graph

/-- For a finite subgraph `H` of `G`, every neighbor of a vertex belongs
either to `H` or to the edge residual `G \ H`, but not both.  Thus degree is
additive across the edge deletion.  This is the local invariant behind
successively removing cycles from an Eulerian graph. -/
theorem degree_sdiff_add_degree_of_le
    {V : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H ≤ G) (vertex : V) :
    (G \ H).degree vertex + H.degree vertex = G.degree vertex := by
  have hresidual : (G \ H).neighborFinset vertex =
      G.neighborFinset vertex \ H.neighborFinset vertex := by
    ext neighbor
    simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset,
      SimpleGraph.sdiff_adj]
  have hsubset : H.neighborFinset vertex ⊆ G.neighborFinset vertex := by
    intro neighbor hneighbor
    rw [SimpleGraph.mem_neighborFinset] at hneighbor ⊢
    exact hHG hneighbor
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree, hresidual]
  exact Finset.card_sdiff_add_card_eq_card hsubset

/-- The graph remaining after removing all edges of a walk's simple-cycle
subgraph.  Naming the residual keeps the cycle-removal recursion at a
mathematical graph interface. -/
noncomputable def cycleResidual
    {V : Type*} {G : SimpleGraph V} {start : V} (cycle : G.Walk start start) :
    SimpleGraph V :=
  G \ cycle.toSubgraph.spanningCoe

noncomputable instance walkCycleGraph_decidableRel
    {V : Type*} {G : SimpleGraph V} {start : V} (cycle : G.Walk start start) :
    DecidableRel cycle.toSubgraph.spanningCoe.Adj :=
  Classical.decRel _

noncomputable instance cycleResidual_decidableRel
    {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]
    {start : V} (cycle : G.Walk start start) : DecidableRel (cycleResidual cycle).Adj := by
  unfold cycleResidual
  infer_instance

/-- The residual removes exactly the edges traversed by the cycle. -/
theorem edgeFinset_cycleResidual
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {start : V} (cycle : G.Walk start start) :
    (cycleResidual cycle).edgeFinset = G.edgeFinset \ cycle.edges.toFinset := by
  have hcycleEdges : cycle.toSubgraph.spanningCoe.edgeSet = ↑cycle.edges.toFinset := by
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe, cycle.edgeSet_toSubgraph]
    ext edge
    change edge ∈ cycle.edges ↔ edge ∈ cycle.edges.toFinset
    simp
  ext edge
  rw [SimpleGraph.mem_edgeFinset]
  simp only [cycleResidual, SimpleGraph.edgeSet_sdiff, Set.mem_diff,
    Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
  constructor
  · rintro ⟨hedge, hnot⟩
    refine ⟨hedge, ?_⟩
    intro hmem
    apply hnot
    rw [hcycleEdges]
    simpa using hmem
  · rintro ⟨hedge, hnot⟩
    refine ⟨hedge, ?_⟩
    intro hmem
    apply hnot
    have hmemSet : edge ∈ (↑cycle.edges.toFinset : Set (Sym2 V)) := by
      rw [← hcycleEdges]
      exact hmem
    simpa using hmemSet

/-- The positions of a simple cycle are in explicit bijection with its
distinct traversed edges.  This is the position-to-edge interface needed to
turn an edge-disjoint graph-cycle partition into an indexed decomposition. -/
noncomputable def simpleCycleEdgePositionEquiv
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle) :
    Fin cycle.length ≃ {edge : Sym2 V // edge ∈ cycle.edges.toFinset} := by
  let positionEquiv : Fin cycle.edges.length ≃ {edge : Sym2 V // edge ∈ cycle.edges} :=
    hcycle.isTrail.edges_nodup.getEquiv cycle.edges
  let finEquiv : Fin cycle.length ≃ Fin cycle.edges.length :=
    (Fin.castOrderIso cycle.length_edges.symm).toEquiv
  exact finEquiv.trans (positionEquiv.trans
    (Equiv.subtypeEquivRight (fun edge => List.mem_toFinset.symm)))

/-- The edge traversed at a cyclic position of a closed walk.  This transparent
representative agrees definitionally with `simpleCycleEdgePositionEquiv` on a
simple cycle, while retaining the position information needed for alternating
orientations. -/
noncomputable def simpleCycleEdgeAt
    {V : Type*} {G : SimpleGraph V} {start : V}
    (cycle : G.Walk start start) (position : Fin cycle.length) : Sym2 V :=
  cycle.edges.get (Fin.cast cycle.length_edges.symm position)

/-- The simple-cycle position equivalence sends a position to the edge
traversed at that position. -/
theorem simpleCycleEdgePositionEquiv_apply_edgeAt
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle) (position : Fin cycle.length) :
    (simpleCycleEdgePositionEquiv hcycle position).1 =
      simpleCycleEdgeAt cycle position := by
  rfl

/-- The vertex at a cyclic position of a closed walk. -/
noncomputable def cycleVertexAt
    {V : Type*} {G : SimpleGraph V} {start : V}
    (cycle : G.Walk start start) (position : Fin cycle.length) : V :=
  cycle.getVert position.1

/-- The successor of a position on a nonempty simple cycle, computed modulo
the cycle length. -/
noncomputable def simpleCycleNextPosition
    {V : Type*} {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle)
    (position : Fin cycle.length) : Fin cycle.length :=
  ⟨(position.1 + 1) % cycle.length,
    Nat.mod_lt _ (SimpleGraph.Walk.not_nil_iff_lt_length.mp hcycle.not_nil)⟩

/-- The edge at a cycle position joins the vertex at that position to the
vertex at its modular successor.  This includes the closing edge without a
separate endpoint convention. -/
theorem simpleCycleEdgeAt_eq_cycleVertexAt_succ
    {V : Type*} {G : SimpleGraph V} {start : V}
    (cycle : G.Walk start start) (hcycle : cycle.IsCycle) (position : Fin cycle.length) :
    simpleCycleEdgeAt cycle position =
      s(cycleVertexAt cycle position,
        cycleVertexAt cycle (simpleCycleNextPosition hcycle position)) := by
  unfold simpleCycleEdgeAt cycleVertexAt SimpleGraph.Walk.edges
  rw [List.get_eq_getElem, List.getElem_map]
  rw [SimpleGraph.Walk.darts_getElem_eq_getVert]
  simp only [SimpleGraph.Dart.edge_mk, Fin.val_cast]
  unfold simpleCycleNextPosition
  by_cases hlast : position.1 + 1 = cycle.length
  · have hnext : (position.1 + 1) % cycle.length = 0 := by
      rw [hlast, Nat.mod_self]
    have hleft : cycle.getVert (position.1 + 1) = start := by
      rw [hlast, cycle.getVert_length]
    rw [hleft]
    simp only [hnext, cycle.getVert_zero]
  · have hlt : position.1 + 1 < cycle.length := by
      omega
    simp only [Nat.mod_eq_of_lt hlt]

/-- The predecessor of a cyclic position on a nonempty simple cycle.  At the
distinguished zero position it wraps to the final position. -/
noncomputable def simpleCyclePreviousPosition
    {V : Type*} {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle)
    (position : Fin cycle.length) : Fin cycle.length :=
  if hzero : position.1 = 0 then
    ⟨cycle.length - 1,
      Nat.sub_lt (SimpleGraph.Walk.not_nil_iff_lt_length.mp hcycle.not_nil)
        (by omega)⟩
  else
    ⟨position.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) position.2⟩

theorem simpleCyclePreviousPosition_val_of_zero
    {V : Type*} {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle)
    (position : Fin cycle.length) (hzero : position.1 = 0) :
    (simpleCyclePreviousPosition hcycle position).1 = cycle.length - 1 := by
  unfold simpleCyclePreviousPosition
  rw [dif_pos hzero]

theorem simpleCyclePreviousPosition_val_of_ne_zero
    {V : Type*} {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle)
    (position : Fin cycle.length) (hzero : position.1 ≠ 0) :
    (simpleCyclePreviousPosition hcycle position).1 = position.1 - 1 := by
  unfold simpleCyclePreviousPosition
  rw [dif_neg hzero]

theorem simpleCycleNextPosition_val_of_lt_last
    {V : Type*} {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle)
    (position : Fin cycle.length) (hlt : position.1 + 1 < cycle.length) :
    (simpleCycleNextPosition hcycle position).1 = position.1 + 1 := by
  unfold simpleCycleNextPosition
  simp only [Nat.mod_eq_of_lt hlt]

theorem simpleCycleNextPosition_val_of_last
    {V : Type*} {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle)
    (position : Fin cycle.length) (hlast : position.1 + 1 = cycle.length) :
    (simpleCycleNextPosition hcycle position).1 = 0 := by
  unfold simpleCycleNextPosition
  simp only [hlast, Nat.mod_self]

/-- Moving backward and then forward returns every nonzero cycle position. -/
theorem simpleCycleNext_previous_of_ne_zero
    {V : Type*} {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle)
    (position : Fin cycle.length) (hzero : position.1 ≠ 0) :
    simpleCycleNextPosition hcycle (simpleCyclePreviousPosition hcycle position) = position := by
  apply Fin.ext
  have hpreviousVal := simpleCyclePreviousPosition_val_of_ne_zero hcycle position hzero
  have hprevious_lt : (simpleCyclePreviousPosition hcycle position).1 + 1 < cycle.length := by
    rw [hpreviousVal]
    omega
  rw [simpleCycleNextPosition_val_of_lt_last hcycle
    (simpleCyclePreviousPosition hcycle position) hprevious_lt]
  rw [hpreviousVal]
  omega

/-- Moving forward and then backward returns every nonfinal cycle position. -/
theorem simpleCyclePrevious_next_of_lt_last
    {V : Type*} {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle)
    (position : Fin cycle.length) (hlt : position.1 + 1 < cycle.length) :
    simpleCyclePreviousPosition hcycle (simpleCycleNextPosition hcycle position) = position := by
  apply Fin.ext
  have hnextval := simpleCycleNextPosition_val_of_lt_last hcycle position hlt
  have hnextnonzero : (simpleCycleNextPosition hcycle position).1 ≠ 0 := by
    rw [hnextval]
    omega
  rw [simpleCyclePreviousPosition_val_of_ne_zero hcycle
    (simpleCycleNextPosition hcycle position) hnextnonzero]
  rw [hnextval]
  omega

/-- The predecessor and successor operations are inverse permutations of the
positions of a nonempty simple cycle. -/
theorem simpleCycleNext_previous
    {V : Type*} {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle)
    (position : Fin cycle.length) :
    simpleCycleNextPosition hcycle (simpleCyclePreviousPosition hcycle position) = position := by
  by_cases hzero : position.1 = 0
  · apply Fin.ext
    have hprevval := simpleCyclePreviousPosition_val_of_zero hcycle position hzero
    have hlast : (simpleCyclePreviousPosition hcycle position).1 + 1 = cycle.length := by
      rw [hprevval]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt
        (SimpleGraph.Walk.not_nil_iff_lt_length.mp hcycle.not_nil))
    rw [simpleCycleNextPosition_val_of_last hcycle
      (simpleCyclePreviousPosition hcycle position) hlast]
    exact hzero.symm
  · exact simpleCycleNext_previous_of_ne_zero hcycle position hzero

theorem simpleCyclePrevious_next
    {V : Type*} {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle)
    (position : Fin cycle.length) :
    simpleCyclePreviousPosition hcycle (simpleCycleNextPosition hcycle position) = position := by
  by_cases hlast : position.1 + 1 = cycle.length
  · apply Fin.ext
    have hnextval := simpleCycleNextPosition_val_of_last hcycle position hlast
    have hprevval := simpleCyclePreviousPosition_val_of_zero hcycle
      (simpleCycleNextPosition hcycle position) (by simpa [hnextval])
    rw [hprevval]
    omega
  · have hlt : position.1 + 1 < cycle.length := by omega
    exact simpleCyclePrevious_next_of_lt_last hcycle position hlt

/-- A simple cycle contributes at least one edge to the residual deletion. -/
theorem simpleCycle_edges_toFinset_nonempty
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {start : V} {cycle : G.Walk start start}
    (hcycle : cycle.IsCycle) : cycle.edges.toFinset.Nonempty := by
  rw [List.toFinset_nonempty_iff]
  intro hedges
  cases cycle with
  | nil => exact hcycle.not_nil SimpleGraph.Walk.nil_nil
  | cons _ _ => simp at hedges

/-- Removing a simple cycle strictly decreases the number of residual edges. -/
theorem card_edgeFinset_cycleResidual_lt
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {start : V} {cycle : G.Walk start start}
    (hcycle : cycle.IsCycle) :
    (cycleResidual cycle).edgeFinset.card < G.edgeFinset.card := by
  have hsubset : cycle.edges.toFinset ⊆ G.edgeFinset := by
    intro edge hedge
    rw [SimpleGraph.mem_edgeFinset]
    exact cycle.edges_subset_edgeSet (by simpa using hedge)
  have hcard : (G.edgeFinset \ cycle.edges.toFinset).card +
      cycle.edges.toFinset.card = G.edgeFinset.card :=
    Finset.card_sdiff_add_card_eq_card hsubset
  have hpositive : 0 < cycle.edges.toFinset.card :=
    Finset.card_pos.mpr (simpleCycle_edges_toFinset_nonempty hcycle)
  rw [edgeFinset_cycleResidual]
  omega

/-- A simple cycle in a finite simple graph visits at most every vertex once.

Mathlib records a cycle as a closed walk whose tail is a simple path.  The
tail has strictly fewer vertices than the ambient finite vertex type; adding
back the distinguished start vertex gives the claimed cycle-length bound. -/
theorem simpleCycle_length_le_card_vertices
    {V : Type*} [Fintype V] {G : SimpleGraph V} {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle) :
    cycle.length ≤ Fintype.card V := by
  have htail : cycle.tail.length < Fintype.card V :=
    hcycle.isPath_tail.length_lt
  rw [← cycle.length_tail_add_one hcycle.not_nil]
  exact Nat.succ_le_of_lt htail

/-- Bypassing repeated interior vertices of a closed walk cannot increase its
length.  This is the length control needed when a graph search first produces
a closed trail and then extracts a simple cycle. -/
theorem cycleBypass_length_le
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {start : V}
    (trail : G.Walk start start) :
    trail.cycleBypass.length ≤ trail.length := by
  cases trail with
  | nil => rfl
  | cons _ tail =>
    exact Nat.succ_le_succ (tail.length_bypass_le)

/-- Every nonempty closed trail contains a simple cycle of no greater length,
using only edges of the original trail. -/
theorem exists_simpleCycle_of_closedTrail
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {start : V}
    (trail : G.Walk start start) (htrail : trail.IsTrail) (hnil : trail ≠ .nil) :
    ∃ cycle : G.Walk start start, cycle.IsCycle ∧ cycle.length ≤ trail.length ∧
      cycle.edges ⊆ trail.edges :=
  ⟨trail.cycleBypass, htrail.isCycle_cycleBypass hnil,
    cycleBypass_length_le trail, trail.edges_cycleBypass_subset⟩

/-- A non-tree edge closes the unique tree path between its endpoints into a
simple cycle.  Its length is exactly one more than that tree distance.

This is the cycle-extraction step used when a breadth-first search first
encounters an edge absent from its search tree. -/
theorem exists_simpleCycle_of_tree_closing_edge
    {V : Type*} {G T : SimpleGraph V} {u v : V}
    (hTle : T ≤ G) (hTree : T.IsTree) (hnotTree : ¬ T.Adj u v)
    (hadj : G.Adj u v) :
    ∃ cycle : G.Walk u u, cycle.IsCycle ∧ cycle.length = T.dist v u + 1 := by
  obtain ⟨path, hpath, hlength⟩ := hTree.connected.exists_path_of_dist v u
  have hnotedge : s(u, v) ∉ path.edges := by
    intro hedge
    exact hnotTree ((T.mem_edgeSet).mp (path.edges_subset_edgeSet hedge))
  let graphPath : G.Path v u := ⟨path.mapLe hTle, hpath.mapLe hTle⟩
  refine ⟨SimpleGraph.Walk.cons hadj graphPath, ?_, ?_⟩
  · apply graphPath.cons_isCycle hadj
    change s(u, v) ∉ (path.mapLe hTle).edges
    rw [path.edges_mapLe_eq_edges hTle]
    exact hnotedge
  · change (SimpleGraph.Walk.cons hadj (path.mapLe hTle)).length = T.dist v u + 1
    rw [SimpleGraph.Walk.length_cons]
    change (path.map (.ofLE hTle)).length + 1 = T.dist v u + 1
    rw [SimpleGraph.Walk.length_map]
    exact congrArg (fun k => k + 1) hlength

/-- The spanning graph of a simple cycle has even degree at every vertex:
vertices off the cycle have degree zero and the cycle vertices have degree
two. -/
theorem even_degree_spanningCoe_of_simpleCycle
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {start : V} {cycle : G.Walk start start}
    (hcycle : cycle.IsCycle) :
    ∀ vertex : V, Even (cycle.toSubgraph.spanningCoe.degree vertex) := by
  intro vertex
  let cycleGraph : SimpleGraph V := cycle.toSubgraph.spanningCoe
  letI : DecidableRel cycleGraph.Adj := walkCycleGraph_decidableRel cycle
  change Even (cycleGraph.degree vertex)
  have hcycles : cycleGraph.IsCycles := by
    exact hcycle.isCycles_spanningCoe_toSubgraph
  have hcycleEven : Even (cycleGraph.degree vertex) := by
    by_cases hnonempty : (cycleGraph.neighborSet vertex).Nonempty
    · rw [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
        hcycles hnonempty]
      exact even_two
    · have hempty : cycleGraph.neighborSet vertex = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hnonempty
      rw [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      simp [hempty]
  exact hcycleEven

/-- Removing the edges of a simple cycle preserves even degree at every
vertex.  This is the Eulerian invariant of the cycle-removal phase in the
source decomposition algorithm. -/
theorem even_degree_sdiff_simpleCycle
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {start : V} {cycle : G.Walk start start}
    (hdegree : ∀ vertex : V, Even (G.degree vertex)) (hcycle : cycle.IsCycle) :
    ∀ vertex : V, Even ((cycleResidual cycle).degree vertex) := by
  intro vertex
  let cycleGraph : SimpleGraph V := cycle.toSubgraph.spanningCoe
  letI : DecidableRel cycleGraph.Adj := walkCycleGraph_decidableRel cycle
  have hcycleGraphLe : cycleGraph ≤ G := cycle.toSubgraph.spanningCoe_le
  have hcycleEven : Even (cycleGraph.degree vertex) := by
    exact even_degree_spanningCoe_of_simpleCycle hcycle vertex
  have hsum : (G \ cycleGraph).degree vertex + cycleGraph.degree vertex =
      G.degree vertex :=
    degree_sdiff_add_degree_of_le hcycleGraphLe vertex
  have hdegreeVertex := hdegree vertex
  rw [← hsum] at hdegreeVertex
  change Even ((G \ cycleGraph).degree vertex)
  exact (Nat.even_add.mp hdegreeVertex).mpr hcycleEven

/-- A finite nonempty simple graph whose vertices all have degree at least two
contains a simple cycle.

The proof is the finite forest argument used by the pruning phase of a
short-cycle decomposition.  If the graph were acyclic, a nontrivial connected
component would be a tree and hence would contain a degree-one vertex.  The
component neighbor type is explicitly identified with the original neighbor
type, so that contradicts the original minimum-degree hypothesis. -/
theorem exists_simpleCycle_of_forall_two_le_degree
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : ∀ vertex : V, 2 ≤ G.degree vertex) :
    ∃ (start : V) (cycle : G.Walk start start), cycle.IsCycle := by
  classical
  by_contra hnoCycle
  have hacyclic : G.IsAcyclic := by
    intro start cycle hcycle
    exact hnoCycle ⟨start, cycle, hcycle⟩
  let root : V := Classical.choice (inferInstance : Nonempty V)
  have hrootPositive : 0 < G.degree root := by
    exact lt_of_lt_of_le (by decide) (hdegree root)
  obtain ⟨neighbor, hrootAdj⟩ := (G.degree_pos_iff_exists_adj root).mp hrootPositive
  let component : G.ConnectedComponent := G.connectedComponentMk root
  have hrootMem : root ∈ component.supp := by
    simpa [component] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := G) root)
  have hneighborMem : neighbor ∈ component.supp :=
    component.mem_supp_of_adj_mem_supp hrootMem hrootAdj
  letI : Nontrivial component :=
    ⟨⟨⟨root, hrootMem⟩, ⟨neighbor, hneighborMem⟩, by
      intro hEq
      have hrootEq : root = neighbor := congrArg Subtype.val hEq
      subst neighbor
      exact G.loopless.irrefl root hrootAdj⟩⟩
  letI : Fintype component := Fintype.ofFinite component
  letI : DecidableRel component.toSimpleGraph.Adj := Classical.decRel _
  have htree : component.toSimpleGraph.IsTree :=
    hacyclic.isTree_connectedComponent component
  obtain ⟨componentVertex, hcomponentDegree⟩ :=
    htree.exists_vert_degree_one_of_nontrivial
  have hdegreeEq : component.toSimpleGraph.degree componentVertex =
      G.degree componentVertex.1 := by
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      ← SimpleGraph.card_neighborSet_eq_degree]
    apply Fintype.card_congr
    exact
      { toFun := fun adjacent =>
          ⟨adjacent.1.1,
            (component.toSimpleGraph_adj componentVertex.2 adjacent.1.2).mp adjacent.2⟩
        invFun := fun adjacent =>
          let hadjacent : adjacent.1 ∈ component.supp :=
            component.mem_supp_of_adj_mem_supp componentVertex.2 adjacent.2
          ⟨⟨adjacent.1, hadjacent⟩,
            (component.toSimpleGraph_adj componentVertex.2 hadjacent).mpr adjacent.2⟩
        left_inv := by
          intro adjacent
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro adjacent
          rfl }
  have horiginalDegree : G.degree componentVertex.1 = 1 := by
    rw [← hdegreeEq]
    exact hcomponentDegree
  have hminimum := hdegree componentVertex.1
  omega

/-- The post-pruning graph in the Chu et al. short-cycle construction has no
vertices of degree at most two, hence it has a simple cycle whenever it is
nonempty. -/
theorem exists_simpleCycle_of_forall_three_le_degree
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : ∀ vertex : V, 3 ≤ G.degree vertex) :
    ∃ (start : V) (cycle : G.Walk start start), cycle.IsCycle :=
  exists_simpleCycle_of_forall_two_le_degree fun vertex =>
    (by omega : 2 ≤ 3).trans (hdegree vertex)

/-- An edge in a finite graph whose every nonisolated vertex has degree at
least two lies in a simple cycle.  Isolated vertices are allowed explicitly,
which is the form produced by a degree-pruning phase. -/
theorem exists_simpleCycle_of_adj_of_nonisolated_two_le_degree
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj]
    (hdegree : ∀ vertex : V, 0 < G.degree vertex → 2 ≤ G.degree vertex)
    {root neighbor : V} (hrootAdj : G.Adj root neighbor) :
    ∃ (start : V) (cycle : G.Walk start start), cycle.IsCycle := by
  classical
  by_contra hnoCycle
  have hacyclic : G.IsAcyclic := by
    intro start cycle hcycle
    exact hnoCycle ⟨start, cycle, hcycle⟩
  let component : G.ConnectedComponent := G.connectedComponentMk root
  have hrootMem : root ∈ component.supp := by
    simpa [component] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := G) root)
  have hneighborMem : neighbor ∈ component.supp :=
    component.mem_supp_of_adj_mem_supp hrootMem hrootAdj
  letI : Nontrivial component :=
    ⟨⟨⟨root, hrootMem⟩, ⟨neighbor, hneighborMem⟩, by
      intro hEq
      have hrootEq : root = neighbor := congrArg Subtype.val hEq
      subst neighbor
      exact G.loopless.irrefl root hrootAdj⟩⟩
  letI : Fintype component := Fintype.ofFinite component
  letI : DecidableRel component.toSimpleGraph.Adj := Classical.decRel _
  have htree : component.toSimpleGraph.IsTree :=
    hacyclic.isTree_connectedComponent component
  obtain ⟨componentVertex, hcomponentDegree⟩ :=
    htree.exists_vert_degree_one_of_nontrivial
  have hdegreeEq : component.toSimpleGraph.degree componentVertex =
      G.degree componentVertex.1 := by
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      ← SimpleGraph.card_neighborSet_eq_degree]
    apply Fintype.card_congr
    exact
      { toFun := fun adjacent =>
          ⟨adjacent.1.1,
            (component.toSimpleGraph_adj componentVertex.2 adjacent.1.2).mp adjacent.2⟩
        invFun := fun adjacent =>
          let hadjacent : adjacent.1 ∈ component.supp :=
            component.mem_supp_of_adj_mem_supp componentVertex.2 adjacent.2
          ⟨⟨adjacent.1, hadjacent⟩,
            (component.toSimpleGraph_adj componentVertex.2 hadjacent).mpr adjacent.2⟩
        left_inv := by
          intro adjacent
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro adjacent
          rfl }
  have horiginalDegree : G.degree componentVertex.1 = 1 := by
    rw [← hdegreeEq]
    exact hcomponentDegree
  have hpositive : 0 < G.degree componentVertex.1 := by
    rw [horiginalDegree]
    omega
  have hminimum := hdegree componentVertex.1 hpositive
  omega

/-- An edge in a finite graph with even degree at every vertex lies in a
simple cycle.  This is the extraction step used to turn an Eulerian residual
into a genuine cycle partition. -/
theorem exists_simpleCycle_of_adj_of_even_degree
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hdegree : ∀ vertex : V, Even (G.degree vertex))
    {root neighbor : V} (hrootAdj : G.Adj root neighbor) :
    ∃ (start : V) (cycle : G.Walk start start), cycle.IsCycle := by
  classical
  by_contra hnoCycle
  have hacyclic : G.IsAcyclic := by
    intro start cycle hcycle
    exact hnoCycle ⟨start, cycle, hcycle⟩
  let component : G.ConnectedComponent := G.connectedComponentMk root
  have hrootMem : root ∈ component.supp := by
    simpa [component] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := G) root)
  have hneighborMem : neighbor ∈ component.supp :=
    component.mem_supp_of_adj_mem_supp hrootMem hrootAdj
  letI : Nontrivial component :=
    ⟨⟨⟨root, hrootMem⟩, ⟨neighbor, hneighborMem⟩, by
      intro hEq
      have hrootEq : root = neighbor := congrArg Subtype.val hEq
      subst neighbor
      exact G.loopless.irrefl root hrootAdj⟩⟩
  letI : Fintype component := Fintype.ofFinite component
  letI : DecidableRel component.toSimpleGraph.Adj := Classical.decRel _
  have htree : component.toSimpleGraph.IsTree :=
    hacyclic.isTree_connectedComponent component
  obtain ⟨componentVertex, hcomponentDegree⟩ :=
    htree.exists_vert_degree_one_of_nontrivial
  have hdegreeEq : component.toSimpleGraph.degree componentVertex =
      G.degree componentVertex.1 := by
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      ← SimpleGraph.card_neighborSet_eq_degree]
    apply Fintype.card_congr
    exact
      { toFun := fun adjacent =>
          ⟨adjacent.1.1,
            (component.toSimpleGraph_adj componentVertex.2 adjacent.1.2).mp adjacent.2⟩
        invFun := fun adjacent =>
          let hadjacent : adjacent.1 ∈ component.supp :=
            component.mem_supp_of_adj_mem_supp componentVertex.2 adjacent.2
          ⟨⟨adjacent.1, hadjacent⟩,
            (component.toSimpleGraph_adj componentVertex.2 hadjacent).mpr adjacent.2⟩
        left_inv := by
          intro adjacent
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro adjacent
          rfl }
  have horiginalDegree : G.degree componentVertex.1 = 1 := by
    rw [← hdegreeEq]
    exact hcomponentDegree
  exact Nat.not_even_one (by simpa [horiginalDegree] using hdegree componentVertex.1)

/-- A `SimpleCyclePeeling` is a finite graph reduced to the empty graph by
repeatedly removing the edges of an actual simple cycle.  It is an inductive
description of a cycle partition rather than a residual bound certificate. -/
inductive HasSimpleCyclePeeling {V : Type*} : SimpleGraph V → Prop
  | empty : HasSimpleCyclePeeling ⊥
  | step {G : SimpleGraph V} {start : V} (cycle : G.Walk start start)
      (hcycle : cycle.IsCycle) :
      HasSimpleCyclePeeling (cycleResidual cycle) → HasSimpleCyclePeeling G

/-- A bounded simple-cycle peeling retains the explicit length cap for every
removed cycle. -/
inductive HasBoundedSimpleCyclePeeling {V : Type*} (bound : ℕ) : SimpleGraph V → Prop
  | empty : HasBoundedSimpleCyclePeeling bound ⊥
  | step {G : SimpleGraph V} {start : V} (cycle : G.Walk start start)
      (hcycle : cycle.IsCycle) (hlength : cycle.length ≤ bound) :
      HasBoundedSimpleCyclePeeling bound (cycleResidual cycle) →
        HasBoundedSimpleCyclePeeling bound G

/-- Edge deletion cannot create an edge crossing a bipartition. -/
theorem cycleResidual_isBipartiteWith
    {V : Type*} {G : SimpleGraph V} {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    {start : V} (cycle : G.Walk start start) :
    (cycleResidual cycle).IsBipartiteWith left right := by
  constructor
  · exact hBipartite.disjoint
  · intro u v hadj
    apply hBipartite.mem_of_adj
    have hresidual : G.Adj u v ∧ ¬ cycle.toSubgraph.spanningCoe.Adj u v := by
      simpa only [cycleResidual, SimpleGraph.sdiff_adj] using hadj
    exact hresidual.1

/-- Deleting all edges incident to a vertex preserves a fixed bipartition.
This is the invariant for either branch of the source degree-pruning phase. -/
theorem isBipartiteWith_deleteIncidenceSet
    {V : Type*} {G : SimpleGraph V} {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right) (vertex : V) :
    (G.deleteIncidenceSet vertex).IsBipartiteWith left right := by
  constructor
  · exact hBipartite.disjoint
  · intro u v hadj
    apply hBipartite.mem_of_adj
    exact (SimpleGraph.deleteIncidenceSet_adj.mp hadj).1

/-- If a pruning step deletes a vertex of degree at most `k`, it discards at
most `k` graph edges.  The exact edge-cardinality identity is provided by
Mathlib; this form is the accounting inequality used in a degree-pruning
trace. -/
theorem card_edgeFinset_sub_card_deleteIncidenceSet_le
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (vertex : V) {k : ℕ} (hdegree : G.degree vertex ≤ k) :
    G.edgeFinset.card - (G.deleteIncidenceSet vertex).edgeFinset.card ≤ k := by
  rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  omega

/-- A positive-degree incidence deletion strictly shrinks the finite edge
set, providing the termination measure for pruning. -/
theorem card_edgeFinset_deleteIncidenceSet_lt
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (vertex : V) (hpositive : 0 < G.degree vertex) :
    (G.deleteIncidenceSet vertex).edgeFinset.card < G.edgeFinset.card := by
  rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  have hdegreeCard : G.degree vertex ≤ G.edgeFinset.card :=
    G.degree_le_card_edgeFinset vertex
  omega

/-- The vertex selected in an incidence-deletion step is isolated in the
residual graph. -/
theorem degree_deleteIncidenceSet_self
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (vertex : V) :
    (G.deleteIncidenceSet vertex).degree vertex = 0 := by
  rw [SimpleGraph.degree_eq_zero]
  intro neighbor hadj
  exact (SimpleGraph.deleteIncidenceSet_adj.mp hadj).2.1 rfl

/-- When a left-side vertex is pruned, it may be removed from the recorded
left part of the residual bipartition because it has become isolated. -/
theorem isBipartiteWith_deleteIncidenceSet_left
    {V : Type*} {G : SimpleGraph V} {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right) {vertex : V}
    (hvertex : vertex ∈ left) :
    (G.deleteIncidenceSet vertex).IsBipartiteWith (left \ {vertex}) right := by
  constructor
  · exact hBipartite.disjoint.mono_left Set.diff_subset
  · intro u v hadj
    rcases hBipartite.mem_of_adj (SimpleGraph.deleteIncidenceSet_adj.mp hadj).1 with h | h
    · exact Or.inl ⟨⟨h.1, by simpa using (SimpleGraph.deleteIncidenceSet_adj.mp hadj).2.1⟩, h.2⟩
    · exact Or.inr ⟨h.1, ⟨h.2, by simpa using (SimpleGraph.deleteIncidenceSet_adj.mp hadj).2.2⟩⟩

/-- Symmetrically, pruning a right-side vertex removes it from the recorded
right part of the residual bipartition. -/
theorem isBipartiteWith_deleteIncidenceSet_right
    {V : Type*} {G : SimpleGraph V} {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right) {vertex : V}
    (hvertex : vertex ∈ right) :
    (G.deleteIncidenceSet vertex).IsBipartiteWith left (right \ {vertex}) := by
  constructor
  · exact hBipartite.disjoint.mono_right Set.diff_subset
  · intro u v hadj
    rcases hBipartite.mem_of_adj (SimpleGraph.deleteIncidenceSet_adj.mp hadj).1 with h | h
    · exact Or.inl ⟨h.1, ⟨h.2, by simpa using (SimpleGraph.deleteIncidenceSet_adj.mp hadj).2.2⟩⟩
    · exact Or.inr ⟨⟨h.1, by simpa using (SimpleGraph.deleteIncidenceSet_adj.mp hadj).2.1⟩, h.2⟩

/-- Every finite Eulerian simple graph has a complete peeling by simple
cycles.  Each recursive step removes at least one edge and the preceding
parity lemma supplies the Eulerian invariant for the residual. -/
theorem exists_simpleCyclePeeling_of_even_degree
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hdegree : ∀ vertex : V, Even (G.degree vertex)) :
    HasSimpleCyclePeeling G := by
  by_cases hbot : G = ⊥
  · subst G
    exact .empty
  · have hadj : ∃ root neighbor : V, G.Adj root neighbor := by
      by_contra hnoAdj
      push Not at hnoAdj
      apply hbot
      ext root neighbor
      simp [hnoAdj root neighbor]
    obtain ⟨root, neighbor, hrootAdj⟩ := hadj
    obtain ⟨start, cycle, hcycle⟩ :=
      exists_simpleCycle_of_adj_of_even_degree hdegree hrootAdj
    exact HasSimpleCyclePeeling.step cycle hcycle
      (exists_simpleCyclePeeling_of_even_degree
        (even_degree_sdiff_simpleCycle hdegree hcycle))
termination_by G.edgeFinset.card
decreasing_by exact card_edgeFinset_cycleResidual_lt hcycle

/-- A simple cycle in a finite bipartite graph has at most twice as many edges
as vertices in either specified side of the bipartition.

The cycle subgraph has degree zero or two at each vertex.  Double-counting its
edges from the chosen bipartition side therefore bounds the number of cycle
edges, which equals the walk length because a cycle is a trail.  This is the
linear residual-cycle estimate used after short-cycle pruning; it does not
assert the separate logarithmic cycle-packing construction. -/
theorem simpleCycle_length_le_two_mul_ncard_of_isBipartiteWith
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    {start : V} {cycle : G.Walk start start} (hcycle : cycle.IsCycle) :
    cycle.length ≤ 2 * left.ncard := by
  classical
  let cycleGraph := cycle.toSubgraph.spanningCoe
  have hcycles : cycleGraph.IsCycles := by
    exact hcycle.isCycles_spanningCoe_toSubgraph
  have hdegree : ∀ vertex : V, cycleGraph.degree vertex ≤ 2 := by
    intro vertex
    by_cases hnonempty : (cycleGraph.neighborSet vertex).Nonempty
    · rw [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
        hcycles hnonempty]
    · have hempty : cycleGraph.neighborSet vertex = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hnonempty
      rw [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      simp [hempty]
  have hBipartiteCycle : cycleGraph.IsBipartiteWith left right :=
    ⟨hBipartite.disjoint, fun _ _ hadj =>
      hBipartite.mem_of_adj (cycle.toSubgraph.adj_sub hadj)⟩
  have hEdges : cycleGraph.edgeFinset = cycle.edges.toFinset := by
    ext edge
    simp [cycleGraph, SimpleGraph.mem_edgeFinset]
  have hlength : cycle.length = cycleGraph.edgeFinset.card := by
    rw [hEdges]
    calc
      cycle.length = cycle.edges.length := cycle.length_edges.symm
      _ = cycle.edges.toFinset.card :=
        (List.toFinset_card_of_nodup hcycle.isTrail.edges_nodup).symm
  have hEdgeSum : ∑ vertex ∈ left.toFinset, cycleGraph.degree vertex =
      cycleGraph.edgeFinset.card := by
    apply cycleGraph.isBipartiteWith_sum_degrees_eq_card_edges
      (s := left.toFinset) (t := right.toFinset)
    simpa using hBipartiteCycle
  calc
    cycle.length = cycleGraph.edgeFinset.card := hlength
    _ = ∑ vertex ∈ left.toFinset, cycleGraph.degree vertex := hEdgeSum.symm
    _ ≤ ∑ _vertex ∈ left.toFinset, 2 := Finset.sum_le_sum fun vertex _ => hdegree vertex
    _ = 2 * left.ncard := by simp [Set.ncard_eq_toFinset_card', Nat.mul_comm]

/-- Every simple cycle in a bipartite graph has even length.  The cycle
subgraph has degree zero or two at every vertex, so its edge count is an even
sum of degrees on either bipartition side. -/
theorem simpleCycle_even_length_of_isBipartiteWith
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    {start : V} {cycle : G.Walk start start} (hcycle : cycle.IsCycle) :
    Even cycle.length := by
  classical
  let cycleGraph := cycle.toSubgraph.spanningCoe
  have hcycles : cycleGraph.IsCycles := by
    exact hcycle.isCycles_spanningCoe_toSubgraph
  have hdegreeEven : ∀ vertex : V, Even (cycleGraph.degree vertex) := by
    intro vertex
    by_cases hnonempty : (cycleGraph.neighborSet vertex).Nonempty
    · rw [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
        hcycles hnonempty]
      exact even_two
    · have hempty : cycleGraph.neighborSet vertex = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hnonempty
      rw [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      simp [hempty]
  have hBipartiteCycle : cycleGraph.IsBipartiteWith left right :=
    ⟨hBipartite.disjoint, fun _ _ hadj =>
      hBipartite.mem_of_adj (cycle.toSubgraph.adj_sub hadj)⟩
  have hEdgeSum : ∑ vertex ∈ left.toFinset, cycleGraph.degree vertex =
      cycleGraph.edgeFinset.card := by
    apply cycleGraph.isBipartiteWith_sum_degrees_eq_card_edges
      (s := left.toFinset) (t := right.toFinset)
    simpa using hBipartiteCycle
  have hEdgesEven : Even cycleGraph.edgeFinset.card := by
    rw [← hEdgeSum]
    apply Finset.even_sum
    intro vertex _
    exact hdegreeEven vertex
  have hEdges : cycleGraph.edgeFinset = cycle.edges.toFinset := by
    ext edge
    simp [cycleGraph, SimpleGraph.mem_edgeFinset]
  have hlength : cycle.length = cycleGraph.edgeFinset.card := by
    rw [hEdges]
    calc
      cycle.length = cycle.edges.length := cycle.length_edges.symm
      _ = cycle.edges.toFinset.card :=
        (List.toFinset_card_of_nodup hcycle.isTrail.edges_nodup).symm
  rw [hlength]
  exact hEdgesEven

/-- A finite Eulerian bipartite graph has a full peeling into simple cycles,
each of length at most twice the cardinality of either chosen side.  This is
the rigorous residual-cycle decomposition used after the short-cycle phase of
the Seshadri--Ugander construction. -/
theorem exists_boundedSimpleCyclePeeling_of_even_degree_of_isBipartiteWith
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    (hdegree : ∀ vertex : V, Even (G.degree vertex)) :
    HasBoundedSimpleCyclePeeling (2 * left.ncard) G := by
  by_cases hbot : G = ⊥
  · subst G
    exact .empty
  · have hadj : ∃ root neighbor : V, G.Adj root neighbor := by
      by_contra hnoAdj
      push Not at hnoAdj
      apply hbot
      ext root neighbor
      simp [hnoAdj root neighbor]
    obtain ⟨root, neighbor, hrootAdj⟩ := hadj
    obtain ⟨start, cycle, hcycle⟩ :=
      exists_simpleCycle_of_adj_of_even_degree hdegree hrootAdj
    exact HasBoundedSimpleCyclePeeling.step cycle hcycle
      (simpleCycle_length_le_two_mul_ncard_of_isBipartiteWith hBipartite hcycle)
      (exists_boundedSimpleCyclePeeling_of_even_degree_of_isBipartiteWith
        (cycleResidual_isBipartiteWith hBipartite cycle)
        (even_degree_sdiff_simpleCycle hdegree hcycle))
termination_by G.edgeFinset.card
decreasing_by exact card_edgeFinset_cycleResidual_lt hcycle

end Graph
end Foundations
end AppliedModelingLib
