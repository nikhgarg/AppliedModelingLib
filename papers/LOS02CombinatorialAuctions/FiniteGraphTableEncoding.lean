import LOS02CombinatorialAuctions.MainTheorems

/-!
# Executable finite graph-table input

The native Theorem 6.1 complexity claim needs an actual finite input
representation.  This module supplies only the first source-safe layer: for a
fixed finite vertex carrier `Fin n`, a Boolean adjacency table is flattened by
the computable `Finset.univ` enumeration, with an exact length theorem.  It is
not yet a machine-step theorem for the graph-to-incidence reduction.
-/

namespace LOS02CombinatorialAuctions

structure FiniteGraphTable (n : Nat) where
  adjacency : Fin n → Fin n → Bool

def FiniteGraphTable.bits {n : Nat} (G : FiniteGraphTable n) : List Bool :=
  (List.ofFn (fun v : Fin n => List.ofFn (G.adjacency v))).flatten

/-- One unit of work per materialized adjacency bit. -/
def FiniteGraphTable.adjacencyReadSteps {n : Nat}
    (G : FiniteGraphTable n) : Nat := G.bits.length

/-- Executable incidence table over the ordered edge universe `Fin n × Fin n`.
For symmetric adjacency, the two orientations represent the same unordered
edge for feasibility purposes; this avoids a noncomputable `Sym2` enumeration
at the machine-input layer. -/
def FiniteGraphTable.orderedIncidenceEntry {n : Nat}
    (G : FiniteGraphTable n) (v u w : Fin n) : Bool :=
  G.adjacency u w && (v = u || v = w)

def FiniteGraphTable.orderedIncidenceRow {n : Nat}
    (G : FiniteGraphTable n) (v : Fin n) : List Bool :=
  (List.ofFn (fun u : Fin n =>
    List.ofFn (fun w : Fin n =>
      G.orderedIncidenceEntry v u w))).flatten

def FiniteGraphTable.orderedIncidenceBits {n : Nat}
    (G : FiniteGraphTable n) : List Bool :=
  (List.ofFn (FiniteGraphTable.orderedIncidenceRow G)).flatten

/-- A transparent work counter for materializing the ordered incidence table.
This counts emitted table cells only; it is not a complete Turing/RAM model
for the source reduction. -/
def FiniteGraphTable.orderedIncidenceMaterializationSteps {n : Nat}
    (G : FiniteGraphTable n) : Nat := G.orderedIncidenceBits.length

/-- The finite set represented by one ordered-incidence row. -/
def FiniteGraphTable.orderedIncidentSet {n : Nat}
    (G : FiniteGraphTable n) (v : Fin n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => G.orderedIncidenceEntry v p.1 p.2 = true)

@[simp] theorem FiniteGraphTable.mem_orderedIncidentSet_iff {n : Nat}
    (G : FiniteGraphTable n) (v : Fin n) (p : Fin n × Fin n) :
    p ∈ G.orderedIncidentSet v ↔
      G.adjacency p.1 p.2 = true ∧ (v = p.1 ∨ v = p.2) := by
  simp [FiniteGraphTable.orderedIncidentSet,
    FiniteGraphTable.orderedIncidenceEntry]

@[simp] theorem FiniteGraphTable.orderedIncidenceEntry_eq_true {n : Nat}
    (G : FiniteGraphTable n) (v u w : Fin n) :
    G.orderedIncidenceEntry v u w = true ↔
      G.adjacency u w = true ∧ (v = u ∨ v = w) := by
  simp [FiniteGraphTable.orderedIncidenceEntry]

@[simp] theorem FiniteGraphTable.orderedIncidenceRow_length {n : Nat}
    (G : FiniteGraphTable n) (v : Fin n) :
    (G.orderedIncidenceRow v).length = n * n := by
  simp [FiniteGraphTable.orderedIncidenceRow, List.sum_ofFn]

@[simp] theorem FiniteGraphTable.bits_length {n : Nat}
    (G : FiniteGraphTable n) :
    G.bits.length = n * n := by
  simp [FiniteGraphTable.bits, List.sum_ofFn]

@[simp] theorem FiniteGraphTable.adjacencyReadSteps_eq {n : Nat}
    (G : FiniteGraphTable n) :
    G.adjacencyReadSteps = n * n := by
  exact FiniteGraphTable.bits_length G

@[simp] theorem FiniteGraphTable.orderedIncidenceBits_length {n : Nat}
    (G : FiniteGraphTable n) :
    G.orderedIncidenceBits.length = n * (n * n) := by
  simp [FiniteGraphTable.orderedIncidenceBits, List.sum_ofFn]

@[simp] theorem FiniteGraphTable.orderedIncidenceMaterializationSteps_eq
    {n : Nat} (G : FiniteGraphTable n) :
    G.orderedIncidenceMaterializationSteps = n * (n * n) := by
  exact FiniteGraphTable.orderedIncidenceBits_length G

theorem finiteGraph_orderedIncidenceBits_length_le_polynomial_in_input
    {n : Nat} (G : FiniteGraphTable n) :
    G.orderedIncidenceBits.length ≤ (G.bits.length + 1) ^ 2 := by
  rw [FiniteGraphTable.orderedIncidenceBits_length,
    FiniteGraphTable.bits_length]
  nlinarith [Nat.zero_le n]

theorem finiteGraph_orderedIncidenceMaterializationSteps_polynomial_in_input
    {n : Nat} (G : FiniteGraphTable n) :
    G.orderedIncidenceMaterializationSteps ≤ (G.bits.length + 1) ^ 2 := by
  exact finiteGraph_orderedIncidenceBits_length_le_polynomial_in_input G

theorem finiteGraph_adjacencyReadSteps_polynomial :
    AppliedModelingLib.Complexity.PolynomiallyBounded (fun n : Nat => n * n) := by
  refine ⟨1, 2, ?_⟩
  intro n
  have hn : n * n ≤ (n + 1) * (n + 1) := by
    nlinarith [Nat.zero_le n]
  simpa [Nat.pow_two] using hn

def FiniteGraphTable.ofSimpleGraph {n : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : FiniteGraphTable n where
  adjacency := fun v w => decide (G.Adj v w)

/-! A table-to-graph semantic adapter.  The Boolean table is allowed to be
arbitrary at the representation layer; the two hypotheses below are exactly
the simple-graph symmetry and loop-freeness conditions needed to recover its
adjacency relation. -/
def FiniteGraphTable.toSimpleGraph {n : Nat}
    (G : FiniteGraphTable n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun v w => G.adjacency v w = true)

/-- Away from the diagonal, symmetry alone identifies a Boolean adjacency
table with the adjacency relation induced by `SimpleGraph.fromRel`.  No
loop-freeness premise is needed because `SimpleGraph` already removes loops. -/
theorem FiniteGraphTable.toSimpleGraph_adj_iff_of_ne
    {n : Nat} (G : FiniteGraphTable n)
    (hsymm : ∀ v w, G.adjacency v w = G.adjacency w v)
    {v w : Fin n} (hvw : v ≠ w) :
    G.toSimpleGraph.Adj v w ↔ G.adjacency v w = true := by
  simp only [FiniteGraphTable.toSimpleGraph, SimpleGraph.fromRel_adj]
  rw [and_iff_right hvw]
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · rw [hsymm] at h
      exact h
  · intro h
    exact Or.inl h

theorem FiniteGraphTable.toSimpleGraph_adj_iff
    {n : Nat} (G : FiniteGraphTable n)
    (hsymm : ∀ v w, G.adjacency v w = G.adjacency w v)
    (hloop : ∀ v, G.adjacency v v = false)
    (v w : Fin n) :
    G.toSimpleGraph.Adj v w ↔ G.adjacency v w = true := by
  by_cases hvw : v = w
  · subst w
    simp [FiniteGraphTable.toSimpleGraph, hloop]
  · exact FiniteGraphTable.toSimpleGraph_adj_iff_of_ne G hsymm hvw

@[simp] theorem FiniteGraphTable.ofSimpleGraph_bits_length {n : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (FiniteGraphTable.ofSimpleGraph G).bits.length = n * n := by
  simp

@[simp] theorem FiniteGraphTable.ofSimpleGraph_orderedIncidenceEntry_eq_true
    {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v u w : Fin n) :
    (FiniteGraphTable.ofSimpleGraph G).orderedIncidenceEntry v u w = true ↔
      G.Adj u w ∧ (v = u ∨ v = w) := by
  simp [FiniteGraphTable.orderedIncidenceEntry,
    FiniteGraphTable.ofSimpleGraph]

theorem FiniteGraphTable.ofSimpleGraph_orderedIncidenceEntry_swap
    {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v u w : Fin n) :
    (FiniteGraphTable.ofSimpleGraph G).orderedIncidenceEntry v u w =
      (FiniteGraphTable.ofSimpleGraph G).orderedIncidenceEntry v w u := by
  simp [FiniteGraphTable.orderedIncidenceEntry, FiniteGraphTable.ofSimpleGraph,
    G.adj_comm, Bool.or_comm]

@[simp] theorem FiniteGraphTable.ofSimpleGraph_mem_orderedIncidentSet_iff
    {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (p : Fin n × Fin n) :
    p ∈ (FiniteGraphTable.ofSimpleGraph G).orderedIncidentSet v ↔
      G.Adj p.1 p.2 ∧ (v = p.1 ∨ v = p.2) := by
  simp [FiniteGraphTable.orderedIncidentSet,
    FiniteGraphTable.orderedIncidenceEntry,
    FiniteGraphTable.ofSimpleGraph]

theorem FiniteGraphTable.ofSimpleGraph_orderedIncidentSets_overlap_of_adj
    {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (huv : u ≠ v) (hadj : G.Adj u v) :
    ((FiniteGraphTable.ofSimpleGraph G).orderedIncidentSet u ∩
      (FiniteGraphTable.ofSimpleGraph G).orderedIncidentSet v).Nonempty := by
  refine ⟨(u, v), ?_⟩
  simp [hadj, huv, FiniteGraphTable.ofSimpleGraph]

theorem FiniteGraphTable.ofSimpleGraph_adj_of_orderedIncidentSets_overlap
    {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (huv : u ≠ v)
    (hoverlap : ((FiniteGraphTable.ofSimpleGraph G).orderedIncidentSet u ∩
      (FiniteGraphTable.ofSimpleGraph G).orderedIncidentSet v).Nonempty) :
    G.Adj u v := by
  rcases hoverlap with ⟨p, hp⟩
  have hpu := (Finset.mem_inter.mp hp).1
  have hpv := (Finset.mem_inter.mp hp).2
  have hu := (FiniteGraphTable.ofSimpleGraph_mem_orderedIncidentSet_iff G u p).mp hpu
  have hv := (FiniteGraphTable.ofSimpleGraph_mem_orderedIncidentSet_iff G v p).mp hpv
  rcases hu.2 with hpu | hpu <;> rcases hv.2 with hpv | hpv
  · exact False.elim (huv (hpu.trans hpv.symm))
  · simpa [hpu, hpv] using hu.1
  · simpa [hpu, hpv, G.adj_comm] using hu.1
  · exact False.elim (huv (hpu.trans hpv.symm))

theorem FiniteGraphTable.ofSimpleGraph_orderedIncidentSets_overlap_iff_adj
    {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (huv : u ≠ v) :
    ((FiniteGraphTable.ofSimpleGraph G).orderedIncidentSet u ∩
      (FiniteGraphTable.ofSimpleGraph G).orderedIncidentSet v).Nonempty ↔
      G.Adj u v := by
  constructor
  · exact FiniteGraphTable.ofSimpleGraph_adj_of_orderedIncidentSets_overlap G huv
  · exact FiniteGraphTable.ofSimpleGraph_orderedIncidentSets_overlap_of_adj G huv

/-- Pairwise-disjoint feasibility for the executable ordered-good encoding. -/
def FiniteGraphTable.orderedSetPackingFeasible
    {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (selected : Finset (Fin n)) : Prop :=
  ∀ ⦃u v : Fin n⦄, u ∈ selected → v ∈ selected → u ≠ v →
    Disjoint
      ((FiniteGraphTable.ofSimpleGraph G).orderedIncidentSet u)
      ((FiniteGraphTable.ofSimpleGraph G).orderedIncidentSet v)

theorem FiniteGraphTable.orderedSetPackingFeasible_iff_graphIndependentSelection
    {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (selected : Finset (Fin n)) :
    FiniteGraphTable.orderedSetPackingFeasible G selected ↔
      AppliedModelingLib.Auction.GraphIndependentSelection G selected := by
  constructor
  · intro hfeas u v hu hv huv hadj
    have hdisj := hfeas hu hv huv
    have hoverlap :=
      FiniteGraphTable.ofSimpleGraph_orderedIncidentSets_overlap_of_adj
        G huv hadj
    rcases hoverlap with ⟨e, he⟩
    exact (Finset.disjoint_left.mp hdisj)
      (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp he).2
  · intro hind u v hu hv huv
    apply Finset.disjoint_left.mpr
    intro e he_u he_v
    have hoverlap :
        ((FiniteGraphTable.ofSimpleGraph G).orderedIncidentSet u ∩
          (FiniteGraphTable.ofSimpleGraph G).orderedIncidentSet v).Nonempty :=
      ⟨e, Finset.mem_inter.mpr ⟨he_u, he_v⟩⟩
    have hadj :=
      FiniteGraphTable.ofSimpleGraph_adj_of_orderedIncidentSets_overlap
        G huv hoverlap
    exact (hind hu hv huv) hadj

/-! A uniform typed map on already encoded Boolean tables. This is the
machine-facing part of the incidence construction; it deliberately does not
claim that arbitrary real-valued bids or the complete source reduction have a
machine encoding. -/

noncomputable def finPairIndex {n : Nat} (p : Fin n × Fin n) : Fin (n * n) :=
  Fin.cast (by simp) ((Fintype.equivFin (Fin n × Fin n)) p)

noncomputable def finTripleOfIndex {n : Nat} (i : Fin (n * (n * n))) :
    Fin n × (Fin n × Fin n) :=
    (Fintype.equivFin (Fin n × (Fin n × Fin n))).symm
    (Fin.cast (by simp) i)

noncomputable def finTripleIndex {n : Nat}
    (triple : Fin n × (Fin n × Fin n)) : Fin (n * (n * n)) :=
  Fin.cast (by simp)
    ((Fintype.equivFin (Fin n × (Fin n × Fin n))) triple)

@[simp] theorem finTripleOfIndex_finTripleIndex {n : Nat}
    (triple : Fin n × (Fin n × Fin n)) :
    finTripleOfIndex (finTripleIndex triple) = triple := by
  simp [finTripleOfIndex, finTripleIndex]

noncomputable def FiniteGraphTable.ofEncodedAdjacency {n : Nat}
    (adjacency : Fin (n * n) → Bool) : FiniteGraphTable n where
  adjacency := fun v w => adjacency (finPairIndex (v, w))

def FiniteGraphTable.encodedOrderedSetPackingFeasible
    {n : Nat} (adjacency : Fin (n * n) → Bool)
    (selected : Finset (Fin n)) : Prop :=
  ∀ ⦃u v : Fin n⦄, u ∈ selected → v ∈ selected → u ≠ v →
    Disjoint
      ((FiniteGraphTable.ofEncodedAdjacency adjacency).orderedIncidentSet u)
      ((FiniteGraphTable.ofEncodedAdjacency adjacency).orderedIncidentSet v)

theorem FiniteGraphTable.encodedOrderedSetPackingFeasible_iff_graphIndependentSelection
    {n : Nat} (adjacency : Fin (n * n) → Bool)
    (hsymm : ∀ v w, adjacency (finPairIndex (v, w)) =
      adjacency (finPairIndex (w, v)))
    (hloop : ∀ v, adjacency (finPairIndex (v, v)) = false)
    (selected : Finset (Fin n)) :
    FiniteGraphTable.encodedOrderedSetPackingFeasible adjacency selected ↔
      AppliedModelingLib.Auction.GraphIndependentSelection
        (FiniteGraphTable.ofEncodedAdjacency adjacency).toSimpleGraph selected := by
  constructor
  · intro hfeas u v hu hv huv hadj
    have hdisj := hfeas hu hv huv
    have hmem_u := (FiniteGraphTable.mem_orderedIncidentSet_iff
        (FiniteGraphTable.ofEncodedAdjacency adjacency) u (u, v)).2
        ⟨by
          rw [← FiniteGraphTable.toSimpleGraph_adj_iff
            (FiniteGraphTable.ofEncodedAdjacency adjacency) hsymm hloop u v]
          exact hadj, Or.inl rfl⟩
    have hmem_v := (FiniteGraphTable.mem_orderedIncidentSet_iff
        (FiniteGraphTable.ofEncodedAdjacency adjacency) v (u, v)).2
        ⟨by
          rw [← FiniteGraphTable.toSimpleGraph_adj_iff
            (FiniteGraphTable.ofEncodedAdjacency adjacency) hsymm hloop u v]
          exact hadj, Or.inr rfl⟩
    exact (Finset.disjoint_left.mp hdisj) hmem_u hmem_v
  · intro hind u v hu hv huv
    apply Finset.disjoint_left.mpr
    intro p hpu hpv
    have hu' := (FiniteGraphTable.mem_orderedIncidentSet_iff
      (FiniteGraphTable.ofEncodedAdjacency adjacency) u p).1 hpu
    have hv' := (FiniteGraphTable.mem_orderedIncidentSet_iff
      (FiniteGraphTable.ofEncodedAdjacency adjacency) v p).1 hpv
    have hswap :
        (FiniteGraphTable.ofEncodedAdjacency adjacency).adjacency p.1 p.2 =
          (FiniteGraphTable.ofEncodedAdjacency adjacency).adjacency p.2 p.1 := by
      simpa [FiniteGraphTable.ofEncodedAdjacency] using hsymm p.1 p.2
    have hadj : (FiniteGraphTable.ofEncodedAdjacency adjacency).toSimpleGraph.Adj u v := by
      rw [FiniteGraphTable.toSimpleGraph_adj_iff
        (FiniteGraphTable.ofEncodedAdjacency adjacency) hsymm hloop]
      rcases hu'.2 with hpu | hpu <;> rcases hv'.2 with hpv | hpv
      · exact False.elim (huv (hpu.trans hpv.symm))
      · simpa [hpu, hpv] using hu'.1
      · have h := hu'.1
        rw [hswap] at h
        simpa [hpu, hpv] using h
      · exact False.elim (huv (hpu.trans hpv.symm))
    exact (hind hu hv huv) hadj

/-- The ordered-incidence packing construction only compares distinct
bidders.  Consequently, a symmetric adjacency table yields the same
feasibility/independence correspondence even when its diagonal is arbitrary. -/
theorem FiniteGraphTable.encodedOrderedSetPackingFeasible_iff_graphIndependentSelection_of_symmetric
    {n : Nat} (adjacency : Fin (n * n) → Bool)
    (hsymm : ∀ v w, adjacency (finPairIndex (v, w)) =
      adjacency (finPairIndex (w, v)))
    (selected : Finset (Fin n)) :
    FiniteGraphTable.encodedOrderedSetPackingFeasible adjacency selected ↔
      AppliedModelingLib.Auction.GraphIndependentSelection
        (FiniteGraphTable.ofEncodedAdjacency adjacency).toSimpleGraph selected := by
  constructor
  · intro hfeas u v hu hv huv hadj
    have hdisj := hfeas hu hv huv
    have hmem_u := (FiniteGraphTable.mem_orderedIncidentSet_iff
        (FiniteGraphTable.ofEncodedAdjacency adjacency) u (u, v)).2
        ⟨by
          rw [← FiniteGraphTable.toSimpleGraph_adj_iff_of_ne
            (FiniteGraphTable.ofEncodedAdjacency adjacency) (by
              simpa [FiniteGraphTable.ofEncodedAdjacency] using hsymm) huv]
          exact hadj, Or.inl rfl⟩
    have hmem_v := (FiniteGraphTable.mem_orderedIncidentSet_iff
        (FiniteGraphTable.ofEncodedAdjacency adjacency) v (u, v)).2
        ⟨by
          rw [← FiniteGraphTable.toSimpleGraph_adj_iff_of_ne
            (FiniteGraphTable.ofEncodedAdjacency adjacency) (by
              simpa [FiniteGraphTable.ofEncodedAdjacency] using hsymm) huv]
          exact hadj, Or.inr rfl⟩
    exact (Finset.disjoint_left.mp hdisj) hmem_u hmem_v
  · intro hind u v hu hv huv
    apply Finset.disjoint_left.mpr
    intro p hpu hpv
    have hu' := (FiniteGraphTable.mem_orderedIncidentSet_iff
      (FiniteGraphTable.ofEncodedAdjacency adjacency) u p).1 hpu
    have hv' := (FiniteGraphTable.mem_orderedIncidentSet_iff
      (FiniteGraphTable.ofEncodedAdjacency adjacency) v p).1 hpv
    have hswap :
        (FiniteGraphTable.ofEncodedAdjacency adjacency).adjacency p.1 p.2 =
          (FiniteGraphTable.ofEncodedAdjacency adjacency).adjacency p.2 p.1 := by
      simpa [FiniteGraphTable.ofEncodedAdjacency] using hsymm p.1 p.2
    have hadj : (FiniteGraphTable.ofEncodedAdjacency adjacency).toSimpleGraph.Adj u v := by
      rw [FiniteGraphTable.toSimpleGraph_adj_iff_of_ne
        (FiniteGraphTable.ofEncodedAdjacency adjacency) (by
          simpa [FiniteGraphTable.ofEncodedAdjacency] using hsymm) huv]
      rcases hu'.2 with hpu | hpu <;> rcases hv'.2 with hpv | hpv
      · exact False.elim (huv (hpu.trans hpv.symm))
      · simpa [hpu, hpv] using hu'.1
      · have h := hu'.1
        rw [hswap] at h
        simpa [hpu, hpv] using h
      · exact False.elim (huv (hpu.trans hpv.symm))
    exact (hind hu hv huv) hadj

noncomputable def orderedIncidenceTableMap {n : Nat}
    (adjacency : Fin (n * n) → Bool) : Fin (n * (n * n)) → Bool :=
  fun i =>
    let triple := finTripleOfIndex i
    adjacency (finPairIndex (triple.2.1, triple.2.2)) &&
      (triple.1 = triple.2.1 || triple.1 = triple.2.2)

theorem orderedIncidenceTableMap_eq_encoded_orderedIncidenceEntry
    {n : Nat} (adjacency : Fin (n * n) → Bool)
    (i : Fin (n * (n * n))) :
    orderedIncidenceTableMap adjacency i =
      (FiniteGraphTable.ofEncodedAdjacency adjacency).orderedIncidenceEntry
        (finTripleOfIndex i).1 (finTripleOfIndex i).2.1
        (finTripleOfIndex i).2.2 := by
  simp [orderedIncidenceTableMap, FiniteGraphTable.ofEncodedAdjacency,
    FiniteGraphTable.orderedIncidenceEntry]

noncomputable def FiniteGraphTable.orderedIncidentSetFromMap {n : Nat}
    (adjacency : Fin (n * n) → Bool) (v : Fin n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p =>
    orderedIncidenceTableMap adjacency (finTripleIndex (v, p)) = true)

@[simp] theorem FiniteGraphTable.mem_orderedIncidentSetFromMap_iff {n : Nat}
    (adjacency : Fin (n * n) → Bool) (v : Fin n) (p : Fin n × Fin n) :
    p ∈ FiniteGraphTable.orderedIncidentSetFromMap adjacency v ↔
      p ∈ (FiniteGraphTable.ofEncodedAdjacency adjacency).orderedIncidentSet v := by
    simp [FiniteGraphTable.orderedIncidentSetFromMap,
    FiniteGraphTable.mem_orderedIncidentSet_iff,
    orderedIncidenceTableMap, FiniteGraphTable.ofEncodedAdjacency,
    finTripleOfIndex_finTripleIndex]

noncomputable def FiniteGraphTable.mapOrderedSetPackingFeasible
    {n : Nat} (adjacency : Fin (n * n) → Bool)
    (selected : Finset (Fin n)) : Prop :=
  ∀ ⦃u v : Fin n⦄, u ∈ selected → v ∈ selected → u ≠ v →
    Disjoint
      (FiniteGraphTable.orderedIncidentSetFromMap adjacency u)
      (FiniteGraphTable.orderedIncidentSetFromMap adjacency v)

theorem FiniteGraphTable.mapOrderedSetPackingFeasible_iff_encoded
    {n : Nat} (adjacency : Fin (n * n) → Bool)
    (selected : Finset (Fin n)) :
    FiniteGraphTable.mapOrderedSetPackingFeasible adjacency selected ↔
      FiniteGraphTable.encodedOrderedSetPackingFeasible adjacency selected := by
  constructor
  · intro h u v hu hv huv
    have hdisj := h hu hv huv
    apply Finset.disjoint_left.mpr
    intro p hpu hpv
    exact (Finset.disjoint_left.mp hdisj)
      ((FiniteGraphTable.mem_orderedIncidentSetFromMap_iff adjacency u p).2 hpu)
      ((FiniteGraphTable.mem_orderedIncidentSetFromMap_iff adjacency v p).2 hpv)
  · intro h u v hu hv huv
    have hdisj := h hu hv huv
    apply Finset.disjoint_left.mpr
    intro p hpu hpv
    exact (Finset.disjoint_left.mp hdisj)
      ((FiniteGraphTable.mem_orderedIncidentSetFromMap_iff adjacency u p).1 hpu)
      ((FiniteGraphTable.mem_orderedIncidentSetFromMap_iff adjacency v p).1 hpv)

@[simp] theorem orderedIncidenceTableMap_output_size {n : Nat}
    (adjacency : Fin (n * n) → Bool) :
    (AppliedModelingLib.Complexity.boolTableEncoding (n * (n * n))).size
      (orderedIncidenceTableMap adjacency) = n * (n * n) := by
  simp

noncomputable def orderedIncidenceTablePolynomialTimeMap (n : Nat) :
    AppliedModelingLib.Complexity.PolynomialTimeMap
      (Fin (n * n) → Bool) (Fin (n * (n * n)) → Bool)
      (AppliedModelingLib.Complexity.boolTableEncoding (n * n))
      (AppliedModelingLib.Complexity.boolTableEncoding (n * (n * n))) where
  map := orderedIncidenceTableMap
  steps := fun _ => n * (n * n)
  steps_bound := by
    refine ⟨1, 2, ?_⟩
    intro adjacency
    simp only [one_mul]
    rw [AppliedModelingLib.Complexity.boolTableEncoding_size]
    nlinarith [Nat.zero_le n]
  output_bound := by
    refine ⟨1, 2, ?_⟩
    intro adjacency
    rw [orderedIncidenceTableMap_output_size]
    simp only [one_mul]
    rw [AppliedModelingLib.Complexity.boolTableEncoding_size]
    nlinarith [Nat.zero_le n]

@[simp] theorem orderedIncidenceTablePolynomialTimeMap_steps_eq
    {n : Nat} (adjacency : Fin (n * n) → Bool) :
    (orderedIncidenceTablePolynomialTimeMap n).steps adjacency =
      n * (n * n) := by
  rfl

/-! A tape-level version of the same finite map.  This keeps the flattened
    output as the explicit `List Bool` word used by the source-style encoding,
    while retaining separate polynomial work and output witnesses. -/

noncomputable def orderedIncidenceListPolynomialTimeMap (n : Nat) :
    AppliedModelingLib.Complexity.PolynomialTimeMap
      (Fin (n * n) → Bool) (List Bool)
      (AppliedModelingLib.Complexity.boolTableEncoding (n * n))
      AppliedModelingLib.Complexity.listBoolEncoding where
  map := fun adjacency => List.ofFn (orderedIncidenceTableMap adjacency)
  steps := fun _ => n * (n * n)
  steps_bound := by
    refine ⟨1, 2, ?_⟩
    intro adjacency
    simp only [one_mul]
    rw [AppliedModelingLib.Complexity.boolTableEncoding_size]
    nlinarith [Nat.zero_le n]
  output_bound := by
    refine ⟨1, 2, ?_⟩
    intro adjacency
    change (List.ofFn (orderedIncidenceTableMap adjacency)).length ≤ _
    simp only [List.length_ofFn]
    rw [AppliedModelingLib.Complexity.boolTableEncoding_size]
    nlinarith [Nat.zero_le n]

@[simp] theorem orderedIncidenceListPolynomialTimeMap_steps_eq
    {n : Nat} (adjacency : Fin (n * n) → Bool) :
    (orderedIncidenceListPolynomialTimeMap n).steps adjacency =
      n * (n * n) := by
  simp [orderedIncidenceListPolynomialTimeMap]

/-! The finite unit-weight reduction appends one unary code for each vertex.
    Its machine-facing output is still a Boolean tape, so this is a concrete
    polynomial map for the unit-weight branch only. -/

noncomputable def orderedIncidenceUnitWeightListPolynomialTimeMap (n : Nat) :
    AppliedModelingLib.Complexity.PolynomialTimeMap
      (Fin (n * n) → Bool) (List Bool)
      (AppliedModelingLib.Complexity.boolTableEncoding (n * n))
      AppliedModelingLib.Complexity.listBoolEncoding where
  map := fun adjacency =>
    List.ofFn (orderedIncidenceTableMap adjacency) ++
      paper_graph_unit_weight_vector_code (Fin n)
  steps := fun _ => n * (n * n) + n * 2
  steps_bound := by
    refine ⟨3, 3, ?_⟩
    intro adjacency
    rw [AppliedModelingLib.Complexity.boolTableEncoding_size]
    let m := n * n
    have hn : n ≤ m + 1 := by
      dsimp [m]
      nlinarith [Nat.zero_le n]
    have hm : m ≤ m + 1 := Nat.le_succ m
    have hmul : n * m ≤ (m + 1) * (m + 1) :=
      Nat.mul_le_mul hn hm
    have hsq_pos : m + 1 ≤ (m + 1) * (m + 1) := by
      calc
        m + 1 = (m + 1) * 1 := by omega
        _ ≤ (m + 1) * (m + 1) :=
          Nat.mul_le_mul_left (m + 1) (by omega)
    have htw : n * 2 ≤ 2 * ((m + 1) * (m + 1)) := by
      calc
        n * 2 ≤ (m + 1) * 2 := Nat.mul_le_mul_right 2 hn
        _ = 2 * (m + 1) := by omega
        _ ≤ 2 * ((m + 1) * (m + 1)) :=
          Nat.mul_le_mul_left 2 hsq_pos
    have hsum : n * m + n * 2 ≤ 3 * ((m + 1) * (m + 1)) := by
      calc
        n * m + n * 2 ≤ (m + 1) * (m + 1) +
            2 * ((m + 1) * (m + 1)) := Nat.add_le_add hmul htw
        _ = 3 * ((m + 1) * (m + 1)) := by ring
    have hcube : (m + 1) * (m + 1) ≤ (m + 1) ^ 3 := by
      calc
        (m + 1) * (m + 1) = ((m + 1) * (m + 1)) * 1 := by omega
        _ ≤ ((m + 1) * (m + 1)) * (m + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = (m + 1) ^ 3 := by ring
    have hscaled : 3 * ((m + 1) * (m + 1)) ≤ 3 * (m + 1) ^ 3 :=
      Nat.mul_le_mul_left 3 hcube
    simpa [m] using (le_trans hsum hscaled)
  output_bound := by
    refine ⟨3, 3, ?_⟩
    intro adjacency
    change (List.ofFn (orderedIncidenceTableMap adjacency) ++
      paper_graph_unit_weight_vector_code (Fin n)).length ≤ _
    rw [List.length_append, List.length_ofFn,
      paper_graph_unit_weight_vector_code_size]
    rw [AppliedModelingLib.Complexity.boolTableEncoding_size]
    let m := n * n
    have hn : n ≤ m + 1 := by
      dsimp [m]
      nlinarith [Nat.zero_le n]
    have hm : m ≤ m + 1 := Nat.le_succ m
    have hmul : n * m ≤ (m + 1) * (m + 1) :=
      Nat.mul_le_mul hn hm
    have hsq_pos : m + 1 ≤ (m + 1) * (m + 1) := by
      calc
        m + 1 = (m + 1) * 1 := by omega
        _ ≤ (m + 1) * (m + 1) :=
          Nat.mul_le_mul_left (m + 1) (by omega)
    have htw : n * 2 ≤ 2 * ((m + 1) * (m + 1)) := by
      calc
        n * 2 ≤ (m + 1) * 2 := Nat.mul_le_mul_right 2 hn
        _ = 2 * (m + 1) := by omega
        _ ≤ 2 * ((m + 1) * (m + 1)) :=
          Nat.mul_le_mul_left 2 hsq_pos
    have hsum : n * m + n * 2 ≤ 3 * ((m + 1) * (m + 1)) := by
      calc
        n * m + n * 2 ≤ (m + 1) * (m + 1) +
            2 * ((m + 1) * (m + 1)) := Nat.add_le_add hmul htw
        _ = 3 * ((m + 1) * (m + 1)) := by ring
    have hcube : (m + 1) * (m + 1) ≤ (m + 1) ^ 3 := by
      calc
        (m + 1) * (m + 1) = ((m + 1) * (m + 1)) * 1 := by omega
        _ ≤ ((m + 1) * (m + 1)) * (m + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = (m + 1) ^ 3 := by ring
    have hscaled : 3 * ((m + 1) * (m + 1)) ≤ 3 * (m + 1) ^ 3 :=
      Nat.mul_le_mul_left 3 hcube
    simpa [m] using (le_trans hsum hscaled)

@[simp] theorem orderedIncidenceUnitWeightListPolynomialTimeMap_steps_eq
    {n : Nat} (adjacency : Fin (n * n) → Bool) :
    (orderedIncidenceUnitWeightListPolynomialTimeMap n).steps adjacency =
      n * (n * n) + n * 2 := by
  simp [orderedIncidenceUnitWeightListPolynomialTimeMap]

@[simp] theorem orderedIncidenceUnitWeightListPolynomialTimeMap_output_size_eq
    {n : Nat} (adjacency : Fin (n * n) → Bool) :
    AppliedModelingLib.Complexity.listBoolEncoding.size
        ((orderedIncidenceUnitWeightListPolynomialTimeMap n).map adjacency) =
      n * (n * n) + n * 2 := by
  simp [orderedIncidenceUnitWeightListPolynomialTimeMap,
    AppliedModelingLib.Complexity.listBoolEncoding_size,
    paper_graph_unit_weight_vector_code_size]

/-! A uniform input layer for the hardness reduction.  The preceding maps are
    parameterized by `n`; the source theorem, however, varies the number of
    vertices.  A terminated unary header makes that varying index part of one
    binary word, followed by the `n*n` adjacency bits. -/

abbrev UniformGraphInput := Sigma (fun n : Nat => Fin (n * n) → Bool)

def uniformGraphInputCode (input : UniformGraphInput) : List Bool :=
  AppliedModelingLib.Complexity.unaryIndexEncode input.1 ++
    List.ofFn input.2

theorem uniformGraphInputCode_injective :
    Function.Injective uniformGraphInputCode := by
  rintro ⟨n, adjacency⟩ ⟨m, adjacency'⟩ hcode
  have hheader := congrArg AppliedModelingLib.Complexity.unaryIndexDecode hcode
  simp [uniformGraphInputCode,
    AppliedModelingLib.Complexity.unaryIndexDecode_encode_append] at hheader
  have hnm : n = m := hheader
  subst m
  have htail : List.ofFn adjacency = List.ofFn adjacency' := by
    exact List.append_right_injective _ hcode
  have hadjacency : adjacency = adjacency' :=
    AppliedModelingLib.Complexity.listOfFn_injective htail
  cases hadjacency
  rfl

noncomputable def uniformGraphInputEncoding :
    AppliedModelingLib.Complexity.BinaryEncoding UniformGraphInput :=
  AppliedModelingLib.Complexity.encodingOfInjectiveList
    uniformGraphInputCode uniformGraphInputCode_injective

@[simp] theorem uniformGraphInputEncoding_size
    (input : UniformGraphInput) :
    uniformGraphInputEncoding.size input = input.1 + 1 + input.1 * input.1 := by
  change (uniformGraphInputCode input).length = _
  simp [uniformGraphInputCode,
    AppliedModelingLib.Complexity.unaryIndexEncode_length]

noncomputable def uniformGraphReductionOutput (input : UniformGraphInput) : List Bool :=
  List.ofFn (orderedIncidenceTableMap input.2) ++
    paper_graph_unit_weight_vector_code (Fin input.1)

@[simp] theorem uniformGraphReductionOutput_size (input : UniformGraphInput) :
    (uniformGraphReductionOutput input).length =
      input.1 * (input.1 * input.1) + input.1 * 2 := by
  simp [uniformGraphReductionOutput,
    paper_graph_unit_weight_vector_code_size]

/-! The uniform map has a concrete emitted-cell cost.  This is still an
    encoding/runtime layer, not the paper's NP-hardness theorem: the latter
    additionally needs a machine decision model and complexity-class bridge. -/
noncomputable def uniformGraphReductionPolynomialTimeMap :
    AppliedModelingLib.Complexity.PolynomialTimeMap
      UniformGraphInput (List Bool)
      uniformGraphInputEncoding AppliedModelingLib.Complexity.listBoolEncoding where
  map := uniformGraphReductionOutput
  steps := fun input => (uniformGraphReductionOutput input).length
  steps_bound := by
    refine ⟨3, 3, ?_⟩
    rintro ⟨n, adjacency⟩
    rw [uniformGraphReductionOutput_size, uniformGraphInputEncoding_size]
    let s := n + 1 + n * n + 1
    have hs : 1 ≤ s := by dsimp [s]; omega
    have hn : n ≤ s := by dsimp [s]; omega
    have hnn : n * n ≤ s * s :=
      Nat.mul_le_mul hn hn
    have hcube : s ^ 3 + 2 * s ≤ 3 * s ^ 3 := by
      nlinarith [Nat.zero_le s, Nat.one_le_iff_ne_zero.mpr (by omega : s ≠ 0)]
    have hout : n * (n * n) + n * 2 ≤ s ^ 3 + 2 * s := by
      have hleft : n * (n * n) ≤ s * s * s := by
        exact le_trans (Nat.mul_le_mul_left n hnn) (by
          have : n ≤ s := hn
          nlinarith [Nat.zero_le (n * n), Nat.zero_le s])
      have hright : n * 2 ≤ 2 * s := by
        simpa [Nat.mul_comm] using (Nat.mul_le_mul_right 2 hn)
      nlinarith [hleft, hright, Nat.zero_le (n * n)]
    dsimp [s] at hcube hout ⊢
    nlinarith [hout, hcube]
  output_bound := by
    refine ⟨3, 3, ?_⟩
    rintro ⟨n, adjacency⟩
    rw [AppliedModelingLib.Complexity.listBoolEncoding_size,
      uniformGraphReductionOutput_size, uniformGraphInputEncoding_size]
    let s := n + 1 + n * n + 1
    have hs : 1 ≤ s := by dsimp [s]; omega
    have hn : n ≤ s := by dsimp [s]; omega
    have hnn : n * n ≤ s * s := Nat.mul_le_mul hn hn
    have hcube : s ^ 3 + 2 * s ≤ 3 * s ^ 3 := by
      nlinarith [Nat.zero_le s, Nat.one_le_iff_ne_zero.mpr (by omega : s ≠ 0)]
    have hleft : n * (n * n) ≤ s * s * s := by
      exact le_trans (Nat.mul_le_mul_left n hnn) (by
        nlinarith [Nat.zero_le (n * n), Nat.zero_le s])
    have hright : n * 2 ≤ 2 * s := by
      simpa [Nat.mul_comm] using (Nat.mul_le_mul_right 2 hn)
    have hout : n * (n * n) + n * 2 ≤ s ^ 3 + 2 * s := by
      nlinarith [hleft, hright]
    change n * (n * n) + n * 2 ≤ 3 * s ^ 3
    nlinarith [hout, hcube]

@[simp] theorem uniformGraphReductionPolynomialTimeMap_steps_eq
    (input : UniformGraphInput) :
    uniformGraphReductionPolynomialTimeMap.steps input =
      (uniformGraphReductionOutput input).length := by
  rfl

/-! Uniform decision-level correctness for the semantic reduction.  The
    computational encoding above is deliberately kept separate from this
    theorem: the recovered simple graph is the mathematical source object,
    while the Boolean-table hypotheses identify its ordered incidence map. -/

noncomputable def uniformGraphInputSimpleGraph
    (input : UniformGraphInput) : SimpleGraph (Fin input.1) :=
  (FiniteGraphTable.ofEncodedAdjacency input.2).toSimpleGraph

noncomputable def uniformGraphInputIndependentSetDecision
    (input : UniformGraphInput) (threshold : ℝ) :
    AppliedModelingLib.Auction.GraphIndependentSetDecisionInstance (Fin input.1) where
  graph := uniformGraphInputSimpleGraph input
  threshold := threshold

noncomputable def uniformGraphInputWeightedSetPackingDecision
    (input : UniformGraphInput) (threshold : ℝ) :
    AppliedModelingLib.Auction.WeightedSetPackingDecisionInstance
      (Fin input.1) (Sym2 (Fin input.1)) :=
  AppliedModelingLib.Auction.graphIndependentSetDecisionToWeightedSetPackingDecision
    (uniformGraphInputIndependentSetDecision input threshold)

theorem uniformGraphInput_independentSet_iff_weightedSetPacking
    (input : UniformGraphInput) (threshold : ℝ) :
    AppliedModelingLib.Auction.GraphIndependentSetDecisionProblem
        (uniformGraphInputIndependentSetDecision input threshold) ↔
      AppliedModelingLib.Auction.WeightedSetPackingDecisionProblem
        (uniformGraphInputWeightedSetPackingDecision input threshold) := by
  exact
    AppliedModelingLib.Auction.graphIndependentSetDecisionProblem_iff_weightedSetPackingDecisionProblem_graphIncident
      (uniformGraphInputIndependentSetDecision input threshold)

theorem uniformGraphInput_ordered_map_feasibility_iff
    (input : UniformGraphInput)
    (hsymm : ∀ v w, input.2 (finPairIndex (v, w)) =
      input.2 (finPairIndex (w, v)))
    (hloop : ∀ v, input.2 (finPairIndex (v, v)) = false)
    (selected : Finset (Fin input.1)) :
    FiniteGraphTable.mapOrderedSetPackingFeasible input.2 selected ↔
      AppliedModelingLib.Auction.GraphIndependentSelection
        (uniformGraphInputSimpleGraph input) selected := by
  rw [FiniteGraphTable.mapOrderedSetPackingFeasible_iff_encoded]
  simpa [uniformGraphInputSimpleGraph] using
    (FiniteGraphTable.encodedOrderedSetPackingFeasible_iff_graphIndependentSelection
      input.2 hsymm hloop selected)

/-- The explicit ordered-incidence auction remains faithful for symmetric raw
tables with arbitrary diagonal entries: a bidder's own loop good cannot
overlap any distinct bidder's row. -/
theorem uniformGraphInput_ordered_map_feasibility_iff_of_symmetric
    (input : UniformGraphInput)
    (hsymm : ∀ v w, input.2 (finPairIndex (v, w)) =
      input.2 (finPairIndex (w, v)))
    (selected : Finset (Fin input.1)) :
    FiniteGraphTable.mapOrderedSetPackingFeasible input.2 selected ↔
      AppliedModelingLib.Auction.GraphIndependentSelection
        (uniformGraphInputSimpleGraph input) selected := by
  rw [FiniteGraphTable.mapOrderedSetPackingFeasible_iff_encoded]
  simpa [uniformGraphInputSimpleGraph] using
    (FiniteGraphTable.encodedOrderedSetPackingFeasible_iff_graphIndependentSelection_of_symmetric
      input.2 hsymm selected)

/-! Structured target representation for the unit-weight subfamily.  Unit
    weights are implicit in this target, exactly as in the pinned hardness
    construction; the encoded payload is the ordered incidence table. -/

abbrev UniformUnitWeightAuctionInput :=
  Sigma (fun n : Nat => Fin (n * (n * n)) → Bool)

def uniformUnitWeightAuctionInputCode
    (input : UniformUnitWeightAuctionInput) : List Bool :=
  AppliedModelingLib.Complexity.unaryIndexEncode input.1 ++
    List.ofFn input.2

theorem uniformUnitWeightAuctionInputCode_injective :
    Function.Injective uniformUnitWeightAuctionInputCode := by
  rintro ⟨n, table⟩ ⟨m, table'⟩ hcode
  have hheader := congrArg AppliedModelingLib.Complexity.unaryIndexDecode hcode
  simp [uniformUnitWeightAuctionInputCode,
    AppliedModelingLib.Complexity.unaryIndexDecode_encode_append] at hheader
  have hnm : n = m := hheader
  subst m
  have htail : List.ofFn table = List.ofFn table' := by
    exact List.append_right_injective _ hcode
  have htable : table = table' :=
    AppliedModelingLib.Complexity.listOfFn_injective htail
  cases htable
  rfl

noncomputable def uniformUnitWeightAuctionInputEncoding :
    AppliedModelingLib.Complexity.BinaryEncoding UniformUnitWeightAuctionInput :=
  AppliedModelingLib.Complexity.encodingOfInjectiveList
    uniformUnitWeightAuctionInputCode uniformUnitWeightAuctionInputCode_injective

@[simp] theorem uniformUnitWeightAuctionInputEncoding_size
    (input : UniformUnitWeightAuctionInput) :
    uniformUnitWeightAuctionInputEncoding.size input =
      input.1 + 1 + input.1 * (input.1 * input.1) := by
  change (uniformUnitWeightAuctionInputCode input).length = _
  simp [uniformUnitWeightAuctionInputCode,
    AppliedModelingLib.Complexity.unaryIndexEncode_length]

noncomputable def uniformGraphToUnitWeightAuctionInput
    (input : UniformGraphInput) : UniformUnitWeightAuctionInput :=
  ⟨input.1, orderedIncidenceTableMap input.2⟩

@[simp] theorem uniformGraphToUnitWeightAuctionInput_table
    (input : UniformGraphInput) :
    (uniformGraphToUnitWeightAuctionInput input).2 =
      orderedIncidenceTableMap input.2 := by
  rfl

noncomputable def uniformGraphToUnitWeightAuctionPolynomialTimeMap :
    AppliedModelingLib.Complexity.PolynomialTimeMap
      UniformGraphInput UniformUnitWeightAuctionInput
      uniformGraphInputEncoding uniformUnitWeightAuctionInputEncoding where
  map := uniformGraphToUnitWeightAuctionInput
  steps := fun input =>
    input.1 * (input.1 * input.1)
  steps_bound := by
    refine ⟨1, 3, ?_⟩
    rintro ⟨n, adjacency⟩
    rw [uniformGraphInputEncoding_size]
    let s := n + 1 + n * n + 1
    have hs : 1 ≤ s := by dsimp [s]; omega
    have hn : n ≤ s := by dsimp [s]; omega
    have hnn : n * n ≤ s * s := Nat.mul_le_mul hn hn
    have hleft : n * (n * n) ≤ s ^ 3 := by
      exact le_trans (Nat.mul_le_mul_left n hnn) (by
        nlinarith [Nat.zero_le (n * n), Nat.zero_le s])
    dsimp [s] at hleft ⊢
    nlinarith [hleft]
  output_bound := by
    refine ⟨2, 3, ?_⟩
    rintro ⟨n, adjacency⟩
    rw [uniformUnitWeightAuctionInputEncoding_size,
      uniformGraphInputEncoding_size]
    let s := n + 1 + n * n + 1
    have hs : 1 ≤ s := by dsimp [s]; omega
    have hn : n ≤ s := by dsimp [s]; omega
    have hnn : n * n ≤ s * s := Nat.mul_le_mul hn hn
    have hleft : n * (n * n) ≤ s ^ 3 := by
      exact le_trans (Nat.mul_le_mul_left n hnn) (by
        nlinarith [Nat.zero_le (n * n), Nat.zero_le s])
    have hs_cube : s ≤ s ^ 3 := by
      nlinarith [Nat.zero_le s]
    have hn_header : n + 1 ≤ s := by
      dsimp [s]
      omega
    have htarget : n + 1 + n * (n * n) ≤ 2 * s ^ 3 := by
      nlinarith [hleft, hs_cube, hn_header]
    dsimp [s] at htarget
    change n + 1 + n * (n * n) ≤ 2 * s ^ 3
    nlinarith [htarget]

@[simp] theorem uniformGraphToUnitWeightAuctionPolynomialTimeMap_steps_eq
    (input : UniformGraphInput) :
    uniformGraphToUnitWeightAuctionPolynomialTimeMap.steps input =
      input.1 * (input.1 * input.1) := by
  rfl

/-! A source-valid subtype makes the symmetry and loop-free hypotheses part of
    the input domain. -/

def uniformGraphInputSymmetric (input : UniformGraphInput) : Prop :=
  ∀ v w, input.2 (finPairIndex (v, w)) =
    input.2 (finPairIndex (w, v))

def uniformGraphInputLoopFree (input : UniformGraphInput) : Prop :=
  ∀ v, input.2 (finPairIndex (v, v)) = false

abbrev UniformSimpleGraphInput :=
  {input : UniformGraphInput //
    uniformGraphInputSymmetric input ∧ uniformGraphInputLoopFree input}

noncomputable def finPairOfIndex {n : Nat} (i : Fin (n * n)) : Fin n × Fin n :=
  (Fintype.equivFin (Fin n × Fin n)).symm (Fin.cast (by simp) i)

@[simp] theorem finPairOfIndex_finPairIndex {n : Nat}
    (p : Fin n × Fin n) : finPairOfIndex (finPairIndex p) = p := by
  simp [finPairOfIndex, finPairIndex]

@[simp] theorem finPairIndex_finPairOfIndex {n : Nat}
    (i : Fin (n * n)) : finPairIndex (finPairOfIndex i) = i := by
  simp [finPairOfIndex, finPairIndex]

noncomputable def uniformSimpleGraphComplement
    (input : UniformSimpleGraphInput) : UniformSimpleGraphInput := by
  let table : UniformGraphInput :=
    ⟨input.1.1, fun i =>
      let p := finPairOfIndex i
      if p.1 = p.2 then false else !(input.1.2 i)⟩
  have hsymm : uniformGraphInputSymmetric table := by
    intro v w
    dsimp [table]
    simp only [finPairOfIndex_finPairIndex]
    by_cases hvw : v = w
    · subst w
      simp
    · simp [hvw, Ne.symm hvw, input.property.1 v w]
  have hloop : uniformGraphInputLoopFree table := by
    intro v
    dsimp [table]
    simp only [finPairOfIndex_finPairIndex]
    simp
  exact ⟨table, hsymm, hloop⟩

theorem uniformSimpleGraphComplement_adj_iff
    (input : UniformSimpleGraphInput) (v w : Fin input.1.1) :
    (uniformGraphInputSimpleGraph
        (uniformSimpleGraphComplement input).1).Adj v w ↔
      v ≠ w ∧ ¬(uniformGraphInputSimpleGraph input.1).Adj v w := by
  simp only [uniformGraphInputSimpleGraph]
  rw [FiniteGraphTable.toSimpleGraph_adj_iff
    (FiniteGraphTable.ofEncodedAdjacency
      (uniformSimpleGraphComplement input).1.2)
    (uniformSimpleGraphComplement input).property.1
    (uniformSimpleGraphComplement input).property.2]
  rw [FiniteGraphTable.toSimpleGraph_adj_iff
    (FiniteGraphTable.ofEncodedAdjacency input.1.2)
    input.property.1 input.property.2]
  simp [uniformSimpleGraphComplement, FiniteGraphTable.ofEncodedAdjacency,
    finPairOfIndex_finPairIndex]

def uniformSimpleGraphInputCode (input : UniformSimpleGraphInput) : List Bool :=
  uniformGraphInputCode input.1

theorem uniformSimpleGraphInputCode_injective :
    Function.Injective uniformSimpleGraphInputCode := by
  intro input input' hcode
  apply Subtype.ext
  exact uniformGraphInputCode_injective hcode

noncomputable def uniformSimpleGraphInputEncoding :
    AppliedModelingLib.Complexity.BinaryEncoding UniformSimpleGraphInput :=
  AppliedModelingLib.Complexity.encodingOfInjectiveList
    uniformSimpleGraphInputCode uniformSimpleGraphInputCode_injective

@[simp] theorem uniformSimpleGraphInputEncoding_size
    (input : UniformSimpleGraphInput) :
    uniformSimpleGraphInputEncoding.size input =
      input.1.1 + 1 + input.1.1 * input.1.1 := by
  change (uniformSimpleGraphInputCode input).length = _
  simp [uniformSimpleGraphInputCode, uniformGraphInputCode,
    AppliedModelingLib.Complexity.unaryIndexEncode_length]

noncomputable def uniformSimpleGraphComplementPolynomialTimeMap :
    AppliedModelingLib.Complexity.PolynomialTimeMap
      UniformSimpleGraphInput UniformSimpleGraphInput
      uniformSimpleGraphInputEncoding uniformSimpleGraphInputEncoding where
  map := uniformSimpleGraphComplement
  steps := fun input => input.1.1 * input.1.1
  steps_bound := by
    refine ⟨1, 2, ?_⟩
    intro input
    rw [uniformSimpleGraphInputEncoding_size]
    nlinarith [Nat.zero_le (input.1.1 + 1 + input.1.1 * input.1.1)]
  output_bound := by
    refine ⟨1, 1, ?_⟩
    intro input
    rw [uniformSimpleGraphInputEncoding_size]
    simp only [uniformSimpleGraphComplement]
    rw [uniformSimpleGraphInputEncoding_size]
    simp only [pow_one]
    omega

@[simp] theorem uniformSimpleGraphComplementPolynomialTimeMap_steps_eq
    (input : UniformSimpleGraphInput) :
    uniformSimpleGraphComplementPolynomialTimeMap.steps input =
      input.1.1 * input.1.1 := by
  rfl

/-- Complementing a graph table preserves its chosen binary input length. -/
theorem uniformSimpleGraphComplement_encoding_size
    (input : UniformSimpleGraphInput) :
    uniformSimpleGraphInputEncoding.size (uniformSimpleGraphComplement input) =
      uniformSimpleGraphInputEncoding.size input := by
  rw [uniformSimpleGraphInputEncoding_size]
  simp only [uniformSimpleGraphComplement]
  rw [uniformSimpleGraphInputEncoding_size]

/-- Complementing a graph table is size-nonexpanding in the chosen encoding. -/
theorem uniformSimpleGraphComplement_encoding_size_nonexpanding
    (input : UniformSimpleGraphInput) :
    uniformSimpleGraphInputEncoding.size (uniformSimpleGraphComplement input) ≤
      uniformSimpleGraphInputEncoding.size input := by
  rw [uniformSimpleGraphComplement_encoding_size]

noncomputable def uniformSimpleGraphToUnitWeightAuctionInput
    (input : UniformSimpleGraphInput) : UniformUnitWeightAuctionInput :=
  uniformGraphToUnitWeightAuctionInput input.1

noncomputable def uniformSimpleGraphToUnitWeightAuctionPolynomialTimeMap :
    AppliedModelingLib.Complexity.PolynomialTimeMap
      UniformSimpleGraphInput UniformUnitWeightAuctionInput
      uniformSimpleGraphInputEncoding uniformUnitWeightAuctionInputEncoding where
  map := uniformSimpleGraphToUnitWeightAuctionInput
  steps := fun input => input.1.1 * (input.1.1 * input.1.1)
  steps_bound := by
    refine ⟨1, 3, ?_⟩
    intro input
    rw [uniformSimpleGraphInputEncoding_size]
    let s := input.1.1 + 1 + input.1.1 * input.1.1 + 1
    have hn : input.1.1 ≤ s := by dsimp [s]; omega
    have hnn : input.1.1 * input.1.1 ≤ s * s := Nat.mul_le_mul hn hn
    have hleft : input.1.1 * (input.1.1 * input.1.1) ≤ s ^ 3 := by
      exact le_trans (Nat.mul_le_mul_left _ hnn) (by
        nlinarith [Nat.zero_le (input.1.1 * input.1.1), Nat.zero_le s])
    dsimp [s] at hleft ⊢
    nlinarith [hleft]
  output_bound := by
    refine ⟨2, 3, ?_⟩
    intro input
    rw [uniformUnitWeightAuctionInputEncoding_size,
      uniformSimpleGraphInputEncoding_size]
    let s := input.1.1 + 1 + input.1.1 * input.1.1 + 1
    have hs : 1 ≤ s := by dsimp [s]; omega
    have hn : input.1.1 ≤ s := by dsimp [s]; omega
    have hnn : input.1.1 * input.1.1 ≤ s * s := Nat.mul_le_mul hn hn
    have hleft : input.1.1 * (input.1.1 * input.1.1) ≤ s ^ 3 := by
      exact le_trans (Nat.mul_le_mul_left _ hnn) (by
        nlinarith [Nat.zero_le (input.1.1 * input.1.1), Nat.zero_le s])
    have hs_cube : s ≤ s ^ 3 := by nlinarith [Nat.zero_le s]
    have hn_header : input.1.1 + 1 ≤ s := by dsimp [s]; omega
    have hout : input.1.1 + 1 + input.1.1 * (input.1.1 * input.1.1) ≤
        2 * s ^ 3 := by nlinarith [hleft, hs_cube, hn_header]
    dsimp [s] at hout
    change input.1.1 + 1 + input.1.1 * (input.1.1 * input.1.1) ≤
      2 * s ^ 3
    nlinarith [hout]

@[simp] theorem uniformSimpleGraphToUnitWeightAuctionPolynomialTimeMap_steps_eq
    (input : UniformSimpleGraphInput) :
    uniformSimpleGraphToUnitWeightAuctionPolynomialTimeMap.steps input =
      input.1.1 * (input.1.1 * input.1.1) := by
  rfl

/-- The source's clique-complement and graph-to-auction maps compose to a
single concrete encoded polynomial-work transformation. -/
noncomputable def uniformSimpleGraphCliqueToUnitWeightAuctionPolynomialTimeMap :
    AppliedModelingLib.Complexity.PolynomialTimeMap
      UniformSimpleGraphInput UniformUnitWeightAuctionInput
      uniformSimpleGraphInputEncoding uniformUnitWeightAuctionInputEncoding :=
  AppliedModelingLib.Complexity.PolynomialTimeMap.comp_of_size_nonexpanding
    uniformSimpleGraphComplementPolynomialTimeMap
    uniformSimpleGraphToUnitWeightAuctionPolynomialTimeMap
    uniformSimpleGraphComplement_encoding_size_nonexpanding

noncomputable def uniformUnitWeightAuctionRow
    {n : Nat} (table : Fin (n * (n * n)) → Bool) (v : Fin n) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => table (finTripleIndex (v, p)) = true)

def uniformUnitWeightAuctionFeasible
    {n : Nat} (table : Fin (n * (n * n)) → Bool)
    (selected : Finset (Fin n)) : Prop :=
  ∀ ⦃u v : Fin n⦄, u ∈ selected → v ∈ selected → u ≠ v →
    Disjoint (uniformUnitWeightAuctionRow table u)
      (uniformUnitWeightAuctionRow table v)

def uniformUnitWeightAuctionDecision
    (input : UniformUnitWeightAuctionInput) (threshold : Nat) : Prop :=
  ∃ selected : Finset (Fin input.1),
    uniformUnitWeightAuctionFeasible input.2 selected ∧
      threshold ≤ selected.card

def uniformSimpleGraphIndependentDecision
    (input : UniformSimpleGraphInput) (threshold : Nat) : Prop :=
  ∃ selected : Finset (Fin input.1.1),
    AppliedModelingLib.Auction.GraphIndependentSelection
      (uniformGraphInputSimpleGraph input.1) selected ∧
      threshold ≤ selected.card

@[simp] theorem uniformGraphToUnitWeightAuctionInput_row
    (input : UniformGraphInput) (v : Fin input.1) :
    uniformUnitWeightAuctionRow
        (uniformGraphToUnitWeightAuctionInput input).2 v =
      FiniteGraphTable.orderedIncidentSetFromMap input.2 v := by
  ext p
  rfl

theorem uniformSimpleGraphInput_decision_correct
    (input : UniformSimpleGraphInput) (threshold : Nat) :
    uniformSimpleGraphIndependentDecision input threshold ↔
      uniformUnitWeightAuctionDecision
        (uniformSimpleGraphToUnitWeightAuctionInput input) threshold := by
  constructor
  · rintro ⟨selected, hind, hcard⟩
    refine ⟨selected, ?_, hcard⟩
    have hrow (w : Fin input.1.1) :
        uniformUnitWeightAuctionRow
            (uniformSimpleGraphToUnitWeightAuctionInput input).2 w =
          FiniteGraphTable.orderedIncidentSetFromMap input.1.2 w := by
      simpa [uniformSimpleGraphToUnitWeightAuctionInput] using
        (uniformGraphToUnitWeightAuctionInput_row input.1 w)
    intro u v hu hv huv
    rw [hrow u, hrow v]
    have hfeasible :=
      (uniformGraphInput_ordered_map_feasibility_iff input.1
        input.property.1 input.property.2 selected).2 hind
    exact hfeasible hu hv huv
  · rintro ⟨selected, hfeasible, hcard⟩
    refine ⟨selected, ?_, hcard⟩
    have hfeasible' : FiniteGraphTable.mapOrderedSetPackingFeasible
        input.1.2 selected := by
      intro u v hu hv huv
      have hrow := hfeasible hu hv huv
      have hrow' (w : Fin input.1.1) :
          uniformUnitWeightAuctionRow
              (uniformSimpleGraphToUnitWeightAuctionInput input).2 w =
            FiniteGraphTable.orderedIncidentSetFromMap input.1.2 w := by
        simpa [uniformSimpleGraphToUnitWeightAuctionInput] using
          (uniformGraphToUnitWeightAuctionInput_row input.1 w)
      simpa [hrow' u, hrow' v] using hrow
    exact
      (uniformGraphInput_ordered_map_feasibility_iff input.1
        input.property.1 input.property.2 selected).1 hfeasible'

def uniformSimpleGraphCliqueDecision
    (input : UniformSimpleGraphInput) (threshold : Nat) : Prop :=
  ∃ selected : Finset (Fin input.1.1),
    AppliedModelingLib.Auction.GraphCliqueSelection
      (uniformGraphInputSimpleGraph input.1) selected ∧
      threshold ≤ selected.card

theorem uniformSimpleGraphCliqueDecision_iff_complement_independentDecision
    (input : UniformSimpleGraphInput) (threshold : Nat) :
    uniformSimpleGraphCliqueDecision input threshold ↔
      uniformSimpleGraphIndependentDecision
        (uniformSimpleGraphComplement input) threshold := by
  constructor
  · rintro ⟨selected, hclique, hcard⟩
    refine ⟨selected, ?_, hcard⟩
    intro u v hu hv huv hadj
    have hcomp := (uniformSimpleGraphComplement_adj_iff input u v).1 hadj
    exact hcomp.2 (hclique hu hv huv)
  · rintro ⟨selected, hind, hcard⟩
    refine ⟨selected, ?_, hcard⟩
    intro u v hu hv huv
    by_contra hnot
    apply (hind hu hv huv)
    exact (uniformSimpleGraphComplement_adj_iff input u v).2 ⟨huv, hnot⟩

noncomputable def uniformSimpleGraphInputPolynomialReduction
    (threshold : Nat) :
    AppliedModelingLib.Complexity.PolynomialTimeReduction
      (fun input => uniformSimpleGraphIndependentDecision input threshold)
      (fun input => uniformUnitWeightAuctionDecision input threshold) :=
  AppliedModelingLib.Complexity.PolynomialTimeMap.toPolynomialTimeReduction
    uniformSimpleGraphToUnitWeightAuctionPolynomialTimeMap
    (fun input => by
      simpa [uniformSimpleGraphToUnitWeightAuctionPolynomialTimeMap] using
        (uniformSimpleGraphInput_decision_correct input threshold))

/-- The fully encoded decision reduction used by the source's clique route:
graph clique is reduced through graph complementation to a unit-weight
single-minded welfare instance, with concrete polynomial work and output-size
bounds for the composed map. -/
noncomputable def uniformSimpleGraphCliquePolynomialReduction
    (threshold : Nat) :
    AppliedModelingLib.Complexity.PolynomialTimeReduction
      (fun input => uniformSimpleGraphCliqueDecision input threshold)
      (fun input => uniformUnitWeightAuctionDecision input threshold) :=
  AppliedModelingLib.Complexity.PolynomialTimeMap.toPolynomialTimeReduction
    uniformSimpleGraphCliqueToUnitWeightAuctionPolynomialTimeMap
    (fun input => by
      rw [uniformSimpleGraphCliqueDecision_iff_complement_independentDecision]
      simpa [uniformSimpleGraphCliqueToUnitWeightAuctionPolynomialTimeMap,
        AppliedModelingLib.Complexity.PolynomialTimeMap.comp_of_size_nonexpanding,
        AppliedModelingLib.Complexity.PolynomialTimeMap.comp_of_closed] using
        (uniformSimpleGraphInput_decision_correct
          (uniformSimpleGraphComplement input) threshold))

end LOS02CombinatorialAuctions
