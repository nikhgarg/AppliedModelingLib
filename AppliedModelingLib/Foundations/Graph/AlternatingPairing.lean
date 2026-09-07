import AppliedModelingLib.Foundations.Graph.EvenPairing
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Alternating pairings and cycle graphs

Two disjoint perfect pairings of one finite carrier form a 2-regular graph.
This file gives the graph-theoretic representation used to turn even-degree
incidence data into alternating cycles.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Graph

open scoped symmDiff

variable {α : Type*}

/-- Two endpoint pairings on one carrier whose paired neighbors are distinct
at every point. -/
structure AlternatingPairing (α : Type*) where
  first : EvenPairing α
  second : EvenPairing α
  distinct : ∀ x, first.perm x ≠ second.perm x

namespace AlternatingPairing

/-- The simple graph formed by one pairing. -/
def pairingGraph (p : EvenPairing α) : SimpleGraph α where
  Adj x y := p.perm x = y
  symm := by
    intro x y h
    rw [← h]
    exact p.apply_apply x
  loopless := ⟨fun x => p.apply_ne x⟩

theorem pairingGraph_adj_iff (p : EvenPairing α) (x y : α) :
    (pairingGraph p).Adj x y ↔ p.perm x = y := Iff.rfl

/-- Regard a pairing graph as a spanning subgraph of the complete graph. -/
def matchingSubgraph (p : EvenPairing α) : (⊤ : SimpleGraph α).Subgraph :=
  SimpleGraph.toSubgraph (G := (⊤ : SimpleGraph α)) (pairingGraph p) le_top

theorem matchingSubgraph_isPerfectMatching (p : EvenPairing α) :
    (matchingSubgraph p).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro x
  refine ⟨p.perm x, ?_, ?_⟩
  · change p.perm x = p.perm x
    rfl
  · intro y hy
    change p.perm x = y at hy
    exact hy.symm

/-- The symmetric-difference graph of the two pairing matchings. -/
def cycleGraph (A : AlternatingPairing α) : SimpleGraph α :=
  (matchingSubgraph A.first).spanningCoe ∆
    (matchingSubgraph A.second).spanningCoe

/-- The union of two pairing matchings is a graph of cycles. The distinctness
condition below rules out isolated vertices. -/
theorem cycleGraph_isCycles (A : AlternatingPairing α) : A.cycleGraph.IsCycles :=
  (matchingSubgraph_isPerfectMatching A.first).symmDiff_isCycles
    (matchingSubgraph_isPerfectMatching A.second)

/-- Along every cycle of the symmetric-difference graph, edges alternate
between the first pairing and the second pairing. -/
theorem cycleGraph_isAlternatingFirst (A : AlternatingPairing α) :
    A.cycleGraph.IsAlternating (matchingSubgraph A.first).spanningCoe :=
  (matchingSubgraph_isPerfectMatching A.first).isAlternating_symmDiff_left
    (matchingSubgraph_isPerfectMatching A.second)

theorem cycleGraph_adj_first (A : AlternatingPairing α) (x : α) :
    A.cycleGraph.Adj x (A.first.perm x) := by
  simp only [cycleGraph, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
    SimpleGraph.Subgraph.spanningCoe_adj, matchingSubgraph, SimpleGraph.toSubgraph_adj]
  left
  constructor
  · change A.first.perm x = A.first.perm x
    rfl
  · intro h
    change A.second.perm x = A.first.perm x at h
    exact A.distinct x h.symm

theorem cycleGraph_adj_second (A : AlternatingPairing α) (x : α) :
    A.cycleGraph.Adj x (A.second.perm x) := by
  simp only [cycleGraph, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
    SimpleGraph.Subgraph.spanningCoe_adj, matchingSubgraph, SimpleGraph.toSubgraph_adj]
  right
  constructor
  · change A.second.perm x = A.second.perm x
    rfl
  · intro h
    change A.first.perm x = A.second.perm x at h
    exact A.distinct x h

theorem cycleGraph_neighbors_nonempty (A : AlternatingPairing α) (x : α) :
    (A.cycleGraph.neighborSet x).Nonempty :=
  ⟨A.first.perm x, by
    simpa only [SimpleGraph.mem_neighborSet] using A.cycleGraph_adj_first x⟩

/-- A graph is the disjoint union of the supports of its connected components.
This equivalence is kept explicit because cycle decompositions need an actual
edge-indexing map, not only a coverage proposition. -/
noncomputable def componentFiberEquiv (G : SimpleGraph α) :
    (Σ c : G.ConnectedComponent, {x : α // x ∈ c.supp}) ≃ α where
  toFun := fun z => z.2.1
  invFun := fun x => ⟨G.connectedComponentMk x,
    ⟨x, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩⟩
  left_inv := by
    rintro ⟨c, ⟨x, hx⟩⟩
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx
    subst c
    rfl
  right_inv := by
    intro x
    rfl

/-- Finite component indices enumerate the original carrier exactly once. -/
noncomputable def componentIndexEquiv (G : SimpleGraph α) [Fintype α] :
    (Σ c : G.ConnectedComponent,
      Fin c.supp.ncard) ≃ α := by
  classical
  exact (Equiv.sigmaCongrRight fun c => by
    letI : Fintype {x : α // x ∈ c.supp} := (Set.toFinite _).fintype
    have hcard : Fintype.card {x : α // x ∈ c.supp} = c.supp.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact (Fintype.equivFinOfCardEq hcard).symm).trans
      (componentFiberEquiv G)

theorem componentIndexEquiv_symm_fst (G : SimpleGraph α) [Fintype α] (x : α) :
    ((componentIndexEquiv G).symm x).1 = G.connectedComponentMk x := by
  classical
  rfl

end AlternatingPairing

namespace EvenPairing

/-- A fixed-point-free involutive pairing partitions every finite carrier
into pairs, hence its cardinality is even. -/
theorem even_card [Fintype α] (p : EvenPairing α) :
    Even (Fintype.card α) :=
  (AlternatingPairing.matchingSubgraph_isPerfectMatching p).even_card

end EvenPairing

end Graph
end Foundations
end AppliedModelingLib
