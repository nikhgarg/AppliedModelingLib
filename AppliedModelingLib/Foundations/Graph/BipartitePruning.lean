import AppliedModelingLib.Foundations.Graph.BipartiteBFS

/-!
# Bipartite low-degree pruning

This module formalizes the degree-pruning phase used before a breadth-first
short-cycle search.  In a finite bipartite graph it repeatedly deletes left
vertices of degree at most two and right vertices of degree at most one.  The
resulting residual has the required minimum degrees on every nonisolated
vertex, and the discarded edge budget is charged once to each deleted vertex.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Graph

/-- Degree is monotone under edge deletion. -/
theorem degree_mono_of_le
    {V : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H ≤ G) (vertex : V) :
    H.degree vertex ≤ G.degree vertex := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro neighbor hneighbor
  rw [SimpleGraph.mem_neighborFinset] at hneighbor ⊢
  exact hHG hneighbor

/-- Once the two-one pruning phase leaves an edge, its terminal degree
conditions force a simple cycle.  The later BFS argument strengthens this
existence statement with the source's logarithmic length bound. -/
theorem exists_simpleCycle_of_bipartite_two_one_stable
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    (hleft : ∀ vertex : V, vertex ∈ left → G.degree vertex = 0 ∨ 3 ≤ G.degree vertex)
    (hright : ∀ vertex : V, vertex ∈ right → G.degree vertex = 0 ∨ 2 ≤ G.degree vertex)
    {root neighbor : V} (hrootAdj : G.Adj root neighbor) :
    ∃ (start : V) (cycle : G.Walk start start), cycle.IsCycle := by
  apply exists_simpleCycle_of_adj_of_nonisolated_two_le_degree ?_ hrootAdj
  intro vertex hpositive
  obtain ⟨neighbor, hvertexAdj⟩ :=
    (G.degree_pos_iff_exists_adj vertex).mp hpositive
  rcases hBipartite.mem_of_adj hvertexAdj with hmem | hmem
  · rcases hleft vertex hmem.1 with hzero | hlarge
    · omega
    · omega
  · rcases hright vertex hmem.1 with hzero | hlarge
    · omega
    · exact hlarge

/-- The concrete pruning phase of the bipartite short-cycle construction.

Every nonisolated left vertex of the output has degree at least three, every
nonisolated right vertex has degree at least two, and the number of deleted
edges is at most two per left vertex plus one per right vertex. -/
theorem exists_bipartite_two_one_pruning
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right) :
    ∃ H : SimpleGraph V, ∃ instH : DecidableRel H.Adj,
      letI : DecidableRel H.Adj := instH
      H ≤ G ∧ H.IsBipartiteWith left right ∧
        (∀ vertex : V, vertex ∈ left → H.degree vertex = 0 ∨ 3 ≤ H.degree vertex) ∧
        (∀ vertex : V, vertex ∈ right → H.degree vertex = 0 ∨ 2 ≤ H.degree vertex) ∧
        G.edgeFinset.card - H.edgeFinset.card ≤ 2 * left.ncard + right.ncard := by
  classical
  by_cases hleft : ∃ vertex : V, vertex ∈ left ∧
      0 < G.degree vertex ∧ G.degree vertex ≤ 2
  · obtain ⟨vertex, hvertexLeft, hpositive, hsmall⟩ := hleft
    obtain ⟨H, instH, hHResidual, hHBipartite, hHLeft, hHRight, hbudget⟩ :=
      exists_bipartite_two_one_pruning
        (G := G.deleteIncidenceSet vertex) (left := left \ {vertex}) (right := right)
        (isBipartiteWith_deleteIncidenceSet_left hBipartite hvertexLeft)
    letI : DecidableRel H.Adj := instH
    refine ⟨H, instH, hHResidual.trans (SimpleGraph.deleteIncidenceSet_le G vertex), ?_, ?_,
      ?_, ?_⟩
    · constructor
      · exact hBipartite.disjoint
      · intro u v hadj
        exact hBipartite.mem_of_adj
          (hHResidual.trans (SimpleGraph.deleteIncidenceSet_le G vertex) hadj)
    · intro x hx
      by_cases hxvertex : x = vertex
      · subst x
        left
        apply Nat.eq_zero_of_le_zero
        calc
          H.degree vertex ≤ (G.deleteIncidenceSet vertex).degree vertex :=
            degree_mono_of_le hHResidual vertex
          _ = 0 := degree_deleteIncidenceSet_self vertex
      · exact hHLeft x ⟨hx, by simpa [Set.mem_singleton_iff] using hxvertex⟩
    · intro x hx
      exact hHRight x hx
    · have hcardResidual :
          (G.deleteIncidenceSet vertex).edgeFinset.card =
            G.edgeFinset.card - G.degree vertex :=
        SimpleGraph.card_edgeFinset_deleteIncidenceSet G vertex
      have hResidualLe : (G.deleteIncidenceSet vertex).edgeFinset.card ≤
          G.edgeFinset.card :=
        Finset.card_le_card
          (SimpleGraph.edgeFinset_mono (SimpleGraph.deleteIncidenceSet_le G vertex))
      have hHle : H.edgeFinset.card ≤ (G.deleteIncidenceSet vertex).edgeFinset.card :=
        Finset.card_le_card (SimpleGraph.edgeFinset_mono hHResidual)
      have hsplit : G.edgeFinset.card - H.edgeFinset.card =
          (G.edgeFinset.card - (G.deleteIncidenceSet vertex).edgeFinset.card) +
            ((G.deleteIncidenceSet vertex).edgeFinset.card - H.edgeFinset.card) :=
        (tsub_add_tsub_cancel hResidualLe hHle).symm
      have hdegreeCard : G.degree vertex ≤ G.edgeFinset.card :=
        G.degree_le_card_edgeFinset vertex
      have hleftCard : (left \ {vertex}).ncard + 1 = left.ncard :=
        Set.ncard_diff_singleton_add_one hvertexLeft
      calc
        G.edgeFinset.card - H.edgeFinset.card =
            (G.edgeFinset.card - (G.deleteIncidenceSet vertex).edgeFinset.card) +
              ((G.deleteIncidenceSet vertex).edgeFinset.card - H.edgeFinset.card) := hsplit
        _ = G.degree vertex +
              ((G.deleteIncidenceSet vertex).edgeFinset.card - H.edgeFinset.card) := by
              rw [hcardResidual, tsub_tsub_cancel_of_le hdegreeCard]
        _ ≤ 2 + (2 * (left \ {vertex}).ncard + right.ncard) :=
              Nat.add_le_add hsmall hbudget
        _ = 2 * left.ncard + right.ncard := by
              rw [← hleftCard, Nat.mul_add]
              omega
  · by_cases hright : ∃ vertex : V, vertex ∈ right ∧
      0 < G.degree vertex ∧ G.degree vertex ≤ 1
    · obtain ⟨vertex, hvertexRight, hpositive, hsmall⟩ := hright
      obtain ⟨H, instH, hHResidual, hHBipartite, hHLeft, hHRight, hbudget⟩ :=
        exists_bipartite_two_one_pruning
          (G := G.deleteIncidenceSet vertex) (left := left) (right := right \ {vertex})
          (isBipartiteWith_deleteIncidenceSet_right hBipartite hvertexRight)
      letI : DecidableRel H.Adj := instH
      refine ⟨H, instH, hHResidual.trans (SimpleGraph.deleteIncidenceSet_le G vertex), ?_, ?_,
        ?_, ?_⟩
      · constructor
        · exact hBipartite.disjoint
        · intro u v hadj
          exact hBipartite.mem_of_adj
            (hHResidual.trans (SimpleGraph.deleteIncidenceSet_le G vertex) hadj)
      · intro x hx
        exact hHLeft x hx
      · intro x hx
        by_cases hxvertex : x = vertex
        · subst x
          left
          apply Nat.eq_zero_of_le_zero
          calc
            H.degree vertex ≤ (G.deleteIncidenceSet vertex).degree vertex :=
              degree_mono_of_le hHResidual vertex
            _ = 0 := degree_deleteIncidenceSet_self vertex
        · exact hHRight x ⟨hx, by simpa [Set.mem_singleton_iff] using hxvertex⟩
      · have hcardResidual :
            (G.deleteIncidenceSet vertex).edgeFinset.card =
              G.edgeFinset.card - G.degree vertex :=
          SimpleGraph.card_edgeFinset_deleteIncidenceSet G vertex
        have hResidualLe : (G.deleteIncidenceSet vertex).edgeFinset.card ≤
            G.edgeFinset.card :=
          Finset.card_le_card
            (SimpleGraph.edgeFinset_mono (SimpleGraph.deleteIncidenceSet_le G vertex))
        have hHle : H.edgeFinset.card ≤ (G.deleteIncidenceSet vertex).edgeFinset.card :=
          Finset.card_le_card (SimpleGraph.edgeFinset_mono hHResidual)
        have hsplit : G.edgeFinset.card - H.edgeFinset.card =
            (G.edgeFinset.card - (G.deleteIncidenceSet vertex).edgeFinset.card) +
              ((G.deleteIncidenceSet vertex).edgeFinset.card - H.edgeFinset.card) :=
          (tsub_add_tsub_cancel hResidualLe hHle).symm
        have hdegreeCard : G.degree vertex ≤ G.edgeFinset.card :=
          G.degree_le_card_edgeFinset vertex
        have hrightCard : (right \ {vertex}).ncard + 1 = right.ncard :=
          Set.ncard_diff_singleton_add_one hvertexRight
        calc
          G.edgeFinset.card - H.edgeFinset.card =
              (G.edgeFinset.card - (G.deleteIncidenceSet vertex).edgeFinset.card) +
                ((G.deleteIncidenceSet vertex).edgeFinset.card - H.edgeFinset.card) := hsplit
          _ = G.degree vertex +
                ((G.deleteIncidenceSet vertex).edgeFinset.card - H.edgeFinset.card) := by
                rw [hcardResidual, tsub_tsub_cancel_of_le hdegreeCard]
          _ ≤ 1 + (2 * left.ncard + (right \ {vertex}).ncard) :=
                Nat.add_le_add hsmall hbudget
          _ = 2 * left.ncard + right.ncard := by
                rw [← hrightCard]
                omega
    · refine ⟨G, inferInstance, le_rfl, hBipartite, ?_, ?_, by omega⟩
      · intro vertex hvertex
        by_cases hzero : G.degree vertex = 0
        · exact Or.inl hzero
        · right
          have hpositive : 0 < G.degree vertex := Nat.pos_of_ne_zero hzero
          have hnotSmall : ¬ G.degree vertex ≤ 2 := by
            intro hsmall
            exact hleft ⟨vertex, hvertex, hpositive, hsmall⟩
          omega
      · intro vertex hvertex
        by_cases hzero : G.degree vertex = 0
        · exact Or.inl hzero
        · right
          have hpositive : 0 < G.degree vertex := Nat.pos_of_ne_zero hzero
          have hnotSmall : ¬ G.degree vertex ≤ 1 := by
            intro hsmall
            exact hright ⟨vertex, hvertex, hpositive, hsmall⟩
          omega
termination_by G.edgeFinset.card
decreasing_by
  · exact card_edgeFinset_deleteIncidenceSet_lt vertex hpositive
  · exact card_edgeFinset_deleteIncidenceSet_lt vertex hpositive

/-- The cardinality of a finite graph's edge set, independent of a particular
decidable presentation of adjacency. -/
noncomputable def edgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ := Nat.card G.edgeSet

/-- The cardinality of a vertex's neighbor set, independent of a particular
finite enumeration of those neighbors. -/
noncomputable def degreeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (vertex : V) : ℕ := Nat.card (G.neighborSet vertex)

theorem edgeCount_eq_edgeFinset_card
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : edgeCount G = G.edgeFinset.card := by
  classical
  rw [edgeCount, Nat.card_eq_fintype_card]
  exact SimpleGraph.edgeFinset_card.symm

theorem degreeCount_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (vertex : V)
    [Fintype (G.neighborSet vertex)] : degreeCount G vertex = G.degree vertex := by
  classical
  rw [degreeCount, Nat.card_eq_fintype_card,
    SimpleGraph.card_neighborSet_eq_degree]

/-- A source-faithful trace of repeated low-degree pruning and cycle removal.
The `discardLeft` and `discardRight` steps account for deleted edges; the
`cycle` step records an actual simple cycle, with the logarithmic BFS length
cap, before recursing on the edge residual. -/
inductive BipartiteCyclePacking {V : Type*} [Fintype V] [DecidableEq V] :
    (G : SimpleGraph V) → Set V → Set V → Nat → Prop
  | done (G : SimpleGraph V) (left right : Set V) :
      edgeCount G = 0 →
      BipartiteCyclePacking G left right 0
  | discardLeft (G : SimpleGraph V) (left right : Set V) (vertex : V) (k : Nat) :
      vertex ∈ left → 0 < degreeCount G vertex → degreeCount G vertex ≤ 2 →
      BipartiteCyclePacking (G.deleteIncidenceSet vertex) (left \ {vertex}) right k →
      BipartiteCyclePacking G left right (degreeCount G vertex + k)
  | discardRight (G : SimpleGraph V) (left right : Set V) (vertex : V) (k : Nat) :
      vertex ∈ right → 0 < degreeCount G vertex → degreeCount G vertex ≤ 1 →
      BipartiteCyclePacking (G.deleteIncidenceSet vertex) left (right \ {vertex}) k →
      BipartiteCyclePacking G left right (degreeCount G vertex + k)
  | cycle (G : SimpleGraph V) (left right : Set V) (start : V)
      (walk : G.Walk start start) (k : Nat) :
      walk.IsCycle → walk.length ≤ 4 * Nat.log 2 left.ncard →
      BipartiteCyclePacking (cycleResidual walk) left right k →
      BipartiteCyclePacking G left right k

/-- In a finite bipartite graph, repeatedly prune left degree at most two and
right degree at most one, and otherwise remove an actual simple cycle.  The
constructed trace terminates with no edges, charges all discarded edges by at
most `2 |left| + |right|`, and caps each selected cycle at
`4 * floor(log₂ |left|)`. -/
theorem exists_bipartite_two_one_cycle_packing
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right) :
    ∃ k, BipartiteCyclePacking G left right k ∧
      k ≤ 2 * left.ncard + right.ncard := by
  classical
  by_cases hleft : ∃ vertex : V, vertex ∈ left ∧
      0 < degreeCount G vertex ∧ degreeCount G vertex ≤ 2
  · obtain ⟨vertex, hvertexLeft, hpositive, hsmall⟩ := hleft
    obtain ⟨k, hpacking, hbudget⟩ :=
      exists_bipartite_two_one_cycle_packing
        (G := G.deleteIncidenceSet vertex) (left := left \ {vertex}) (right := right)
        (isBipartiteWith_deleteIncidenceSet_left hBipartite hvertexLeft)
    refine ⟨degreeCount G vertex + k,
      BipartiteCyclePacking.discardLeft G left right vertex k hvertexLeft hpositive hsmall hpacking,
      ?_⟩
    have hleftCard : (left \ {vertex}).ncard + 1 = left.ncard :=
      Set.ncard_diff_singleton_add_one hvertexLeft
    calc
      degreeCount G vertex + k ≤ 2 + (2 * (left \ {vertex}).ncard + right.ncard) :=
        Nat.add_le_add hsmall hbudget
      _ = 2 * left.ncard + right.ncard := by
        rw [← hleftCard, Nat.mul_add]
        omega
  · by_cases hright : ∃ vertex : V, vertex ∈ right ∧
        0 < degreeCount G vertex ∧ degreeCount G vertex ≤ 1
    · obtain ⟨vertex, hvertexRight, hpositive, hsmall⟩ := hright
      obtain ⟨k, hpacking, hbudget⟩ :=
        exists_bipartite_two_one_cycle_packing
          (G := G.deleteIncidenceSet vertex) (left := left) (right := right \ {vertex})
          (isBipartiteWith_deleteIncidenceSet_right hBipartite hvertexRight)
      refine ⟨degreeCount G vertex + k,
        BipartiteCyclePacking.discardRight G left right vertex k hvertexRight hpositive hsmall hpacking,
        ?_⟩
      have hrightCard : (right \ {vertex}).ncard + 1 = right.ncard :=
        Set.ncard_diff_singleton_add_one hvertexRight
      calc
        degreeCount G vertex + k ≤ 1 + (2 * left.ncard + (right \ {vertex}).ncard) :=
          Nat.add_le_add hsmall hbudget
        _ = 2 * left.ncard + right.ncard := by
          rw [← hrightCard]
          omega
    · by_cases hedgeCount : edgeCount G = 0
      · exact ⟨0, BipartiteCyclePacking.done G left right hedgeCount, by omega⟩
      · have hleftStable : ∀ vertex : V, vertex ∈ left →
            G.degree vertex = 0 ∨ 3 ≤ G.degree vertex := by
          intro vertex hvertex
          by_cases hzero : G.degree vertex = 0
          · exact Or.inl hzero
          · right
            have hpositive : 0 < degreeCount G vertex := by
              rw [degreeCount_eq_degree]
              exact Nat.pos_of_ne_zero hzero
            have hnotSmall : ¬ degreeCount G vertex ≤ 2 := by
              intro hsmall
              exact hleft ⟨vertex, hvertex, hpositive, hsmall⟩
            have hlarge : 3 ≤ degreeCount G vertex := by omega
            rwa [degreeCount_eq_degree] at hlarge
        have hrightStable : ∀ vertex : V, vertex ∈ right →
            G.degree vertex = 0 ∨ 2 ≤ G.degree vertex := by
          intro vertex hvertex
          by_cases hzero : G.degree vertex = 0
          · exact Or.inl hzero
          · right
            have hpositive : 0 < degreeCount G vertex := by
              rw [degreeCount_eq_degree]
              exact Nat.pos_of_ne_zero hzero
            have hnotSmall : ¬ degreeCount G vertex ≤ 1 := by
              intro hsmall
              exact hright ⟨vertex, hvertex, hpositive, hsmall⟩
            have hlarge : 2 ≤ degreeCount G vertex := by omega
            rwa [degreeCount_eq_degree] at hlarge
        have hcardPositive : 0 < G.edgeFinset.card := by
          rw [← edgeCount_eq_edgeFinset_card]
          exact Nat.pos_of_ne_zero hedgeCount
        have hnonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp hcardPositive
        have hneBot : G ≠ ⊥ := SimpleGraph.edgeFinset_nonempty.mp hnonempty
        obtain ⟨root, neighbor, hrootAdj⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hneBot
        obtain ⟨leftRoot, leftNeighbor, hleftRoot, hleftRootAdj⟩ :
            ∃ leftRoot leftNeighbor, leftRoot ∈ left ∧ G.Adj leftRoot leftNeighbor := by
          rcases hBipartite.mem_of_adj hrootAdj with hleft | hright
          · exact ⟨root, neighbor, hleft.1, hrootAdj⟩
          · exact ⟨neighbor, root, hright.2, hrootAdj.symm⟩
        obtain ⟨start, cycle, hcycle, hcycleLength⟩ :=
          exists_simpleCycle_of_bipartite_two_one_stable_length_le_four_log
            hBipartite hleftStable hrightStable hleftRoot hleftRootAdj
        obtain ⟨k, hpacking, hbudget⟩ :=
          exists_bipartite_two_one_cycle_packing
            (G := cycleResidual cycle) (left := left) (right := right)
            (cycleResidual_isBipartiteWith hBipartite cycle)
        refine ⟨k,
          BipartiteCyclePacking.cycle G left right start cycle k hcycle
            hcycleLength hpacking,
          hbudget⟩
termination_by edgeCount G
decreasing_by
  · rw [edgeCount_eq_edgeFinset_card, edgeCount_eq_edgeFinset_card]
    have hpositiveDegree : 0 < G.degree vertex := by
      rw [← degreeCount_eq_degree]
      exact hpositive
    exact card_edgeFinset_deleteIncidenceSet_lt vertex hpositiveDegree
  · rw [edgeCount_eq_edgeFinset_card, edgeCount_eq_edgeFinset_card]
    have hpositiveDegree : 0 < G.degree vertex := by
      rw [← degreeCount_eq_degree]
      exact hpositive
    exact card_edgeFinset_deleteIncidenceSet_lt vertex hpositiveDegree
  · rw [edgeCount_eq_edgeFinset_card, edgeCount_eq_edgeFinset_card]
    exact card_edgeFinset_cycleResidual_lt hcycle

end Graph
end Foundations
end AppliedModelingLib
