import AppliedModelingLib.Foundations.Graph.BipartitePacking

/-!
# Parity accounting for bipartite cycle packings

The sharper residual bound in the Seshadri--Ugander short-cycle packing
argument charges a left-side deletion both for its removed edges and for the
right-degree parities it can change.  This module makes that accounting
explicit for the constructive `BipartiteCyclePacking` trace.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Graph

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Deleting the incidence set of `deleted` leaves the degree of any distinct,
non-neighboring vertex unchanged. -/
theorem degree_deleteIncidenceSet_eq_of_not_adj
    {G : SimpleGraph V} [DecidableRel G.Adj] {deleted other : V}
    (hother : other ≠ deleted) (hnot : ¬ G.Adj other deleted) :
    (G.deleteIncidenceSet deleted).degree other = G.degree other := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext neighbor
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset,
    SimpleGraph.deleteIncidenceSet_adj]
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, hother, ?_⟩
    intro hneighbor
    subst neighbor
    exact hnot h

/-- The finite set of vertices in `right` whose graph degree is odd. -/
noncomputable def oddDegreeFinset (G : SimpleGraph V) (right : Set V) : Finset V :=
  right.toFinite.toFinset.filter fun vertex => Odd (degreeCount G vertex)

/-- The number of vertices in `right` whose graph degree is odd. -/
noncomputable def oddDegreeCount (G : SimpleGraph V) (right : Set V) : Nat :=
  (oddDegreeFinset G right).card

theorem oddDegreeCount_eq_card (G : SimpleGraph V) (right : Set V) :
    oddDegreeCount G right = (oddDegreeFinset G right).card := rfl

/-- Away from the deleted vertex, only its neighbors can become newly odd. -/
theorem oddDegreeFinset_deleteIncidenceSet_subset_union
    {G : SimpleGraph V} [DecidableRel G.Adj] {right : Set V} {deleted : V}
    (hnotRight : deleted ∉ right) :
    oddDegreeFinset (G.deleteIncidenceSet deleted) right ⊆
      oddDegreeFinset G right ∪ G.neighborFinset deleted := by
  classical
  intro other hother
  simp only [oddDegreeFinset, Finset.mem_filter, Set.Finite.mem_toFinset,
    Finset.mem_union] at hother ⊢
  by_cases hodd : Odd (degreeCount G other)
  · exact Or.inl ⟨hother.1, hodd⟩
  · right
    rw [SimpleGraph.mem_neighborFinset]
    by_contra hnotAdj
    have hotherNe : other ≠ deleted := by
      intro hEq
      subst other
      exact hnotRight hother.1
    have hdegree : degreeCount (G.deleteIncidenceSet deleted) other =
        degreeCount G other := by
      rw [degreeCount_eq_degree, degreeCount_eq_degree,
        degree_deleteIncidenceSet_eq_of_not_adj hotherNe (fun h => hnotAdj h.symm)]
    rw [hdegree] at hother
    exact hodd hother.2

/-- Deleting a vertex outside the designated right side creates at most one
new odd right degree for each deleted incidence. -/
theorem oddDegreeCount_deleteIncidenceSet_le
    {G : SimpleGraph V} [DecidableRel G.Adj] {right : Set V} {deleted : V}
    (hnotRight : deleted ∉ right) :
    oddDegreeCount (G.deleteIncidenceSet deleted) right ≤
      oddDegreeCount G right + degreeCount G deleted := by
  classical
  rw [oddDegreeCount_eq_card, oddDegreeCount_eq_card, degreeCount_eq_degree]
  calc
    (oddDegreeFinset (G.deleteIncidenceSet deleted) right).card ≤
        (oddDegreeFinset G right ∪ G.neighborFinset deleted).card :=
      Finset.card_le_card (oddDegreeFinset_deleteIncidenceSet_subset_union hnotRight)
    _ ≤ (oddDegreeFinset G right).card + (G.neighborFinset deleted).card :=
      Finset.card_union_le _ _
    _ = (oddDegreeFinset G right).card + G.degree deleted := by rfl

/-- Removing a simple cycle preserves the oddness of every vertex degree. -/
theorem odd_degree_cycleResidual_iff
    {G : SimpleGraph V} [DecidableRel G.Adj] {start : V}
    {cycle : G.Walk start start} (hcycle : cycle.IsCycle) (vertex : V) :
    Odd ((cycleResidual cycle).degree vertex) ↔ Odd (G.degree vertex) := by
  let cycleGraph : SimpleGraph V := cycle.toSubgraph.spanningCoe
  letI : DecidableRel cycleGraph.Adj := walkCycleGraph_decidableRel cycle
  have hcycleGraphLe : cycleGraph ≤ G := cycle.toSubgraph.spanningCoe_le
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
  have hsum : (G \ cycleGraph).degree vertex + cycleGraph.degree vertex =
      G.degree vertex :=
    degree_sdiff_add_degree_of_le hcycleGraphLe vertex
  change Odd ((G \ cycleGraph).degree vertex) ↔ Odd (G.degree vertex)
  constructor
  · intro hodd
    rw [← hsum, Nat.odd_add]
    exact ⟨fun _ => hcycleEven, fun _ => hodd⟩
  · intro hodd
    rw [← hsum, Nat.odd_add] at hodd
    exact hodd.mpr hcycleEven

theorem oddDegreeFinset_cycleResidual
    {G : SimpleGraph V} [DecidableRel G.Adj] {right : Set V}
    {start : V} {cycle : G.Walk start start} (hcycle : cycle.IsCycle) :
    oddDegreeFinset (cycleResidual cycle) right = oddDegreeFinset G right := by
  classical
  ext vertex
  simp only [oddDegreeFinset, Finset.mem_filter, Set.Finite.mem_toFinset]
  rw [degreeCount_eq_degree, degreeCount_eq_degree]
  exact and_congr Iff.rfl (odd_degree_cycleResidual_iff hcycle vertex)

theorem oddDegreeCount_cycleResidual
    {G : SimpleGraph V} [DecidableRel G.Adj] {right : Set V}
    {start : V} {cycle : G.Walk start start} (hcycle : cycle.IsCycle) :
    oddDegreeCount (cycleResidual cycle) right = oddDegreeCount G right := by
  rw [oddDegreeCount_eq_card, oddDegreeCount_eq_card,
    oddDegreeFinset_cycleResidual hcycle]

/-- Deleting a right-side vertex leaves the other right degrees unchanged in
a bipartite graph, so the new odd vertices form a subset of the old odd
vertices with the deleted vertex removed. -/
theorem oddDegreeFinset_deleteIncidenceSet_right_subset_erase
    {G : SimpleGraph V} [DecidableRel G.Adj] {left right : Set V} {deleted : V}
    (hBipartite : G.IsBipartiteWith left right) (hdeleted : deleted ∈ right) :
    oddDegreeFinset (G.deleteIncidenceSet deleted) (right \ {deleted}) ⊆
      (oddDegreeFinset G right).erase deleted := by
  classical
  intro other hother
  simp only [Finset.mem_erase, oddDegreeFinset, Finset.mem_filter,
    Set.Finite.mem_toFinset, Set.mem_diff, Set.mem_singleton_iff] at hother ⊢
  refine ⟨hother.1.2, ⟨hother.1.1, ?_⟩⟩
  have hnotAdj : ¬ G.Adj other deleted := by
    intro hadj
    rcases hBipartite.mem_of_adj hadj with hleftRight | hrightLeft
    · exact (Set.disjoint_left.mp hBipartite.disjoint hleftRight.1) hother.1.1
    · exact (Set.disjoint_left.mp hBipartite.disjoint hrightLeft.2) hdeleted
  have hdegree : degreeCount (G.deleteIncidenceSet deleted) other =
      degreeCount G other := by
    rw [degreeCount_eq_degree, degreeCount_eq_degree,
      degree_deleteIncidenceSet_eq_of_not_adj hother.1.2 hnotAdj]
  rw [← hdegree]
  exact hother.2

theorem oddDegreeCount_deleteIncidenceSet_right_le_sub_one
    {G : SimpleGraph V} [DecidableRel G.Adj] {left right : Set V} {deleted : V}
    (hBipartite : G.IsBipartiteWith left right) (hdeleted : deleted ∈ right)
    (hdegree : degreeCount G deleted = 1) :
    oddDegreeCount (G.deleteIncidenceSet deleted) (right \ {deleted}) ≤
      oddDegreeCount G right - 1 := by
  classical
  rw [oddDegreeCount_eq_card, oddDegreeCount_eq_card]
  calc
    (oddDegreeFinset (G.deleteIncidenceSet deleted) (right \ {deleted})).card ≤
        ((oddDegreeFinset G right).erase deleted).card :=
      Finset.card_le_card
        (oddDegreeFinset_deleteIncidenceSet_right_subset_erase hBipartite hdeleted)
    _ = (oddDegreeFinset G right).card - 1 := by
      rw [Finset.card_erase_of_mem]
      simp only [oddDegreeFinset, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨hdeleted, by simp [hdegree]⟩

/-- The source's parity-refined pruning account: left deletions can create at
most one new odd right degree per removed incidence, right deletions consume an
odd degree-one right vertex, and deleting a cycle preserves all degree parity. -/
theorem BipartiteCyclePacking.parity_budget
    {G : SimpleGraph V} {left right : Set V} {k : Nat}
    (hBipartite : G.IsBipartiteWith left right)
    (packing : BipartiteCyclePacking G left right k) :
    k ≤ 4 * left.ncard + oddDegreeCount G right := by
  classical
  induction packing with
  | done G left right hzero =>
    omega
  | @discardLeft G left right vertex k hleft hpositive hsmall packing ih =>
    letI : DecidableRel G.Adj := Classical.decRel _
    have hBipartiteResidual : (G.deleteIncidenceSet vertex).IsBipartiteWith
        (left \ {vertex}) right :=
      isBipartiteWith_deleteIncidenceSet_left hBipartite hleft
    have hbudget := ih hBipartiteResidual
    have hodd : oddDegreeCount (G.deleteIncidenceSet vertex) right ≤
        oddDegreeCount G right + degreeCount G vertex :=
      oddDegreeCount_deleteIncidenceSet_le (by
        intro hvertexRight
        exact (Set.disjoint_left.mp hBipartite.disjoint hleft) hvertexRight)
    have hleftCard : (left \ {vertex}).ncard + 1 = left.ncard :=
      Set.ncard_diff_singleton_add_one hleft
    calc
      degreeCount G vertex + k ≤ 2 +
          (4 * (left \ {vertex}).ncard +
            oddDegreeCount (G.deleteIncidenceSet vertex) right) :=
        Nat.add_le_add hsmall hbudget
      _ ≤ 2 + (4 * (left \ {vertex}).ncard +
            (oddDegreeCount G right + degreeCount G vertex)) :=
        Nat.add_le_add_left (Nat.add_le_add_left hodd _) _
      _ ≤ 4 * left.ncard + oddDegreeCount G right := by
        rw [← hleftCard]
        omega
  | @discardRight G left right vertex k hright hpositive hsmall packing ih =>
    letI : DecidableRel G.Adj := Classical.decRel _
    have hBipartiteResidual : (G.deleteIncidenceSet vertex).IsBipartiteWith left
        (right \ {vertex}) :=
      isBipartiteWith_deleteIncidenceSet_right hBipartite hright
    have hbudget := ih hBipartiteResidual
    have hdegree : degreeCount G vertex = 1 := by omega
    have hodd : oddDegreeCount (G.deleteIncidenceSet vertex) (right \ {vertex}) ≤
        oddDegreeCount G right - 1 :=
      oddDegreeCount_deleteIncidenceSet_right_le_sub_one hBipartite hright hdegree
    have hoddPositive : 0 < oddDegreeCount G right := by
      rw [oddDegreeCount_eq_card]
      apply Finset.card_pos.mpr
      refine ⟨vertex, ?_⟩
      simp only [oddDegreeFinset, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨hright, by simp [hdegree]⟩
    calc
      degreeCount G vertex + k ≤ 1 +
          (4 * left.ncard +
            oddDegreeCount (G.deleteIncidenceSet vertex) (right \ {vertex})) :=
        Nat.add_le_add hsmall hbudget
      _ ≤ 1 + (4 * left.ncard + (oddDegreeCount G right - 1)) :=
        Nat.add_le_add_left (Nat.add_le_add_left hodd _) _
      _ ≤ 4 * left.ncard + oddDegreeCount G right := by omega
  | @cycle G left right start walk k hcycle hlength packing ih =>
    letI : DecidableRel G.Adj := Classical.decRel _
    have hBipartiteResidual : (cycleResidual walk).IsBipartiteWith left right :=
      cycleResidual_isBipartiteWith hBipartite walk
    have hbudget := ih hBipartiteResidual
    rw [oddDegreeCount_cycleResidual hcycle] at hbudget
    exact hbudget

end Graph
end Foundations
end AppliedModelingLib
