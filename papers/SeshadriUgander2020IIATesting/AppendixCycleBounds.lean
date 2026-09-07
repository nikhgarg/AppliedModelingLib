import SeshadriUgander2020IIATesting.ChoiceSystem
import AppliedModelingLib.Foundations.Graph.SimpleCycleBounds
import AppliedModelingLib.Foundations.Graph.BipartitePruning
import AppliedModelingLib.Foundations.Graph.BipartitePacking
import AppliedModelingLib.Foundations.Graph.BipartiteParity
import AppliedModelingLib.Foundations.Graph.CompleteCyclePacking

/-!
# Incidence-graph cycle bounds

This file records the elementary residual-cycle part of Appendix Lemma 10 of
Seshadri--Ugander (2020).  The short-cycle packing construction is separate:
here an already constructed *simple* cycle in the comparison-incidence graph
is bounded by twice the number of items, exactly as used for the Eulerian
remainder in the source proof.
-/

namespace SeshadriUgander2020IIATesting

namespace ChoiceFrame

variable (F : ChoiceFrame)

/-- The source comparison-incidence graph.  Its vertices are the disjoint
union of items and observed choice sets; an edge records membership of an item
in a set. -/
def incidenceGraph : SimpleGraph (Sum F.Item F.SetId) where
  Adj u v :=
    match u, v with
    | Sum.inl x, Sum.inr C => x ∈ F.members C
    | Sum.inr C, Sum.inl x => x ∈ F.members C
    | _, _ => False
  symm := by
    intro u v
    cases u <;> cases v <;> simp
  loopless := ⟨by
    intro vertex hadj
    cases vertex <;> simpa using hadj⟩

noncomputable instance : DecidableRel F.incidenceGraph.Adj := by
  classical
  exact Classical.decRel _

/-- The incidence-graph edge corresponding to one observed item/set
membership.  This is the concrete edge-level source-to-model map used when
turning graph cycles into the paper's observation-indexed decomposition. -/
noncomputable def observationEdge (o : F.Observation) : Sym2 (Sum F.Item F.SetId) :=
  s(Sum.inl o.2.1, Sum.inr o.1)

theorem observationEdge_mem_edgeSet (o : F.Observation) :
    F.observationEdge o ∈ F.incidenceGraph.edgeSet := by
  change F.incidenceGraph.Adj (Sum.inl o.2.1) (Sum.inr o.1)
  exact o.2.2

theorem observationEdge_injective : Function.Injective F.observationEdge := by
  rintro ⟨firstSet, firstItem⟩ ⟨secondSet, secondItem⟩ heq
  dsimp [observationEdge] at heq
  rcases Sym2.eq_iff.mp heq with hs | hs
  · have hset : firstSet = secondSet := Sum.inr.inj hs.2
    have hitem : firstItem.1 = secondItem.1 := Sum.inl.inj hs.1
    cases hset
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hitem))
  · exact (Sum.inl_ne_inr hs.1).elim

theorem observationEdge_surjective_edgeSet (edge : F.incidenceGraph.edgeSet) :
    ∃ o : F.Observation, F.observationEdge o = edge.1 := by
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet] at hedge
    cases u with
    | inl item =>
      cases v with
      | inl item' => simp [incidenceGraph] at hedge
      | inr setId =>
        refine ⟨⟨setId, item, ?_⟩, ?_⟩
        · simpa [incidenceGraph] using hedge
        · simp [observationEdge]
    | inr setId =>
      cases v with
      | inl item =>
        refine ⟨⟨setId, item, ?_⟩, ?_⟩
        · simpa [incidenceGraph] using hedge
        · simp [observationEdge]
      | inr setId' => simp [incidenceGraph] at hedge

/-- Observed memberships and incidence-graph edges are the same finite
support, with an explicit equivalence rather than merely equal cardinality. -/
noncomputable def observationEdgeEquiv : F.Observation ≃ F.incidenceGraph.edgeSet := by
  apply Equiv.ofBijective (fun o => ⟨F.observationEdge o, F.observationEdge_mem_edgeSet o⟩)
  constructor
  · intro first second heq
    exact F.observationEdge_injective (congrArg Subtype.val heq)
  · intro edge
    obtain ⟨o, ho⟩ := F.observationEdge_surjective_edgeSet edge
    refine ⟨o, ?_⟩
    apply Subtype.ext
    exact ho

/-- The item side of the comparison-incidence graph. -/
def itemVertices : Set (Sum F.Item F.SetId) := Set.range Sum.inl

/-- The choice-set side of the comparison-incidence graph. -/
def setVertices : Set (Sum F.Item F.SetId) := Set.range Sum.inr

/-- The comparison-incidence graph is bipartite in its item and choice-set
vertex classes. -/
theorem incidenceGraph_isBipartiteWith :
    F.incidenceGraph.IsBipartiteWith F.itemVertices F.setVertices := by
  constructor
  · rw [Set.disjoint_left]
    intro vertex hitem hset
    rcases hitem with ⟨item, hitem⟩
    rcases hset with ⟨setId, hset⟩
    rw [← hitem] at hset
    simpa using hset
  · intro u v hadj
    cases u with
    | inl item =>
      cases v with
      | inl _ => simp [incidenceGraph] at hadj
      | inr setId => exact Or.inl ⟨⟨item, rfl⟩, ⟨setId, rfl⟩⟩
    | inr setId =>
      cases v with
      | inl item => exact Or.inr ⟨⟨setId, rfl⟩, ⟨item, rfl⟩⟩
      | inr _ => simp [incidenceGraph] at hadj

/-- The item vertex class has precisely one vertex per source item. -/
theorem itemVertices_ncard : F.itemVertices.ncard = Fintype.card F.Item := by
  rw [itemVertices, Set.ncard_range_of_injective Sum.inl_injective,
    Nat.card_eq_fintype_card]

/-- The choice-set vertex class has precisely one vertex per observed choice
set. -/
theorem setVertices_ncard : F.setVertices.ncard = Fintype.card F.SetId := by
  rw [setVertices, Set.ncard_range_of_injective Sum.inr_injective,
    Nat.card_eq_fintype_card]

/-- An item-side degree in the comparison-incidence graph is exactly the
number of observed choice sets containing that item. -/
theorem incidenceGraph_degree_item (item : F.Item) :
    F.incidenceGraph.degree (Sum.inl item) = (F.occurrences item).card := by
  rw [← F.occurrence_card item, ← SimpleGraph.card_neighborSet_eq_degree]
  apply Fintype.card_congr
  exact
    { toFun := fun neighbor =>
        match neighbor with
        | ⟨Sum.inl _, hadj⟩ => False.elim (by simpa [incidenceGraph] using hadj)
        | ⟨Sum.inr setId, hadj⟩ =>
            ⟨setId, by simpa [incidenceGraph] using hadj⟩
      invFun := fun occurrence =>
        ⟨Sum.inr occurrence.1, by simpa [incidenceGraph] using occurrence.2⟩
      left_inv := by
        rintro ⟨(_ | setId), hadj⟩
        · exact False.elim (by simpa [incidenceGraph] using hadj)
        · apply Subtype.ext
          rfl
      right_inv := by
        rintro ⟨setId, hsetId⟩
        rfl }

/-- A choice-set-side degree in the comparison-incidence graph is exactly the
cardinality of that observed choice set. -/
theorem incidenceGraph_degree_set (setId : F.SetId) :
    F.incidenceGraph.degree (Sum.inr setId) = (F.members setId).card := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  calc
    Fintype.card (F.incidenceGraph.neighborSet (Sum.inr setId)) =
        Fintype.card {item : F.Item // item ∈ F.members setId} := by
      apply Fintype.card_congr
      exact
        { toFun := fun neighbor =>
            match neighbor with
            | ⟨Sum.inl item, hadj⟩ =>
                ⟨item, by simpa [incidenceGraph] using hadj⟩
            | ⟨Sum.inr _, hadj⟩ => False.elim (by simpa [incidenceGraph] using hadj)
          invFun := fun item =>
            ⟨Sum.inl item.1, by simpa [incidenceGraph] using item.2⟩
          left_inv := by
            rintro ⟨(_ | item), hadj⟩
            · apply Subtype.ext
              rfl
            · exact False.elim (by simpa [incidenceGraph] using hadj)
          right_inv := by
            rintro ⟨item, hitem⟩
            rfl }
    _ = (F.members setId).card := by simp

/-- The source Eulerian condition is precisely even degree at every vertex of
the concrete comparison-incidence graph. -/
theorem eulerian_iff_incidenceGraph_even_degree :
    F.Eulerian ↔ ∀ vertex : Sum F.Item F.SetId,
      Even (F.incidenceGraph.degree vertex) := by
  constructor
  · intro hEulerian vertex
    cases vertex with
    | inl item => simpa [F.incidenceGraph_degree_item item] using hEulerian.item_even item
    | inr setId => simpa [F.incidenceGraph_degree_set setId] using hEulerian.set_even setId
  · intro heven
    exact
      { set_even := fun setId => by
          simpa [F.incidenceGraph_degree_set setId] using heven (Sum.inr setId)
        item_even := fun item => by
          simpa [F.incidenceGraph_degree_item item] using heven (Sum.inl item) }

/-- Double-counting memberships: summing item occurrence counts gives the
source incidence count `d = Σ_C |C|`. -/
theorem sum_occurrence_card_eq_incidenceCount :
    ∑ item : F.Item, (F.occurrences item).card = F.incidenceCount := by
  classical
  unfold occurrences incidenceCount
  calc
    (∑ item : F.Item,
        (Finset.univ.filter fun setId => item ∈ F.members setId).card) =
        ∑ item : F.Item, ∑ setId : F.SetId,
          if item ∈ F.members setId then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro item _
      symm
      simpa using
        (Finset.sum_boole (fun setId : F.SetId => item ∈ F.members setId) Finset.univ)
    _ = ∑ setId : F.SetId, ∑ item : F.Item,
          if item ∈ F.members setId then 1 else 0 := Finset.sum_comm
    _ = ∑ setId : F.SetId, (F.members setId).card := by
      apply Finset.sum_congr rfl
      intro setId _
      simpa using
        (Finset.sum_boole (fun item : F.Item => item ∈ F.members setId) Finset.univ)

/-- The edge count of the concrete comparison-incidence graph is the source
quantity `d = Σ_C |C|`. -/
theorem incidenceGraph_edgeFinset_card :
    F.incidenceGraph.edgeFinset.card = F.incidenceCount := by
  classical
  let itemEmbedding : F.Item ↪ Sum F.Item F.SetId :=
    ⟨Sum.inl, Sum.inl_injective⟩
  have hitemFinset : F.itemVertices.toFinset = Finset.univ.map itemEmbedding := by
    ext vertex
    cases vertex <;> simp [itemVertices, itemEmbedding]
  have hDegreeSum :
      (∑ vertex ∈ F.itemVertices.toFinset, F.incidenceGraph.degree vertex) =
        ∑ item : F.Item, F.incidenceGraph.degree (Sum.inl item) := by
    rw [hitemFinset]
    simp [itemEmbedding]
  have hBipartiteDegreeSum :
      (∑ vertex ∈ F.itemVertices.toFinset, F.incidenceGraph.degree vertex) =
        F.incidenceGraph.edgeFinset.card := by
    apply F.incidenceGraph.isBipartiteWith_sum_degrees_eq_card_edges
      (s := F.itemVertices.toFinset) (t := F.setVertices.toFinset)
    simpa using F.incidenceGraph_isBipartiteWith
  calc
    F.incidenceGraph.edgeFinset.card =
        ∑ item : F.Item, F.incidenceGraph.degree (Sum.inl item) := by
      rw [← hDegreeSum, hBipartiteDegreeSum]
    _ = ∑ item : F.Item, (F.occurrences item).card := by
      simp_rw [F.incidenceGraph_degree_item]
    _ = F.incidenceCount := F.sum_occurrence_card_eq_incidenceCount

/-- Appendix Lemma 10's residual-cycle estimate: every simple cycle in the
comparison-incidence graph has length at most `2n`, where `n` is the number of
items.  This is independent of the still-separate short-cycle packing step. -/
theorem incidence_simpleCycle_length_le_two_mul_itemCard
    {start : Sum F.Item F.SetId} {cycle : F.incidenceGraph.Walk start start}
    (hcycle : cycle.IsCycle) :
    cycle.length ≤ 2 * Fintype.card F.Item := by
  have hbound :=
    AppliedModelingLib.Foundations.Graph.simpleCycle_length_le_two_mul_ncard_of_isBipartiteWith
      (F.incidenceGraph_isBipartiteWith) hcycle
  rw [F.itemVertices_ncard] at hbound
  exact hbound

/-- Every simple cycle in the source comparison-incidence graph has even
length, as required for its alternating orientation. -/
theorem incidence_simpleCycle_even_length
    {start : Sum F.Item F.SetId} {cycle : F.incidenceGraph.Walk start start}
    (hcycle : cycle.IsCycle) : Even cycle.length :=
  AppliedModelingLib.Foundations.Graph.simpleCycle_even_length_of_isBipartiteWith
    F.incidenceGraph_isBipartiteWith hcycle

/-- Every nontrivial simple cycle of the incidence graph visits a choice-set
vertex.  This permits a canonical cyclic rotation whose distinguished vertex
is on the choice-set side. -/
theorem exists_set_vertex_on_incidence_simpleCycle
    {start : Sum F.Item F.SetId} {cycle : F.incidenceGraph.Walk start start}
    (hcycle : cycle.IsCycle) :
    ∃ setId : F.SetId, Sum.inr setId ∈ cycle.support := by
  cases start with
  | inr setId =>
    refine ⟨setId, ?_⟩
    simpa using cycle.getVert_mem_support 0
  | inl item =>
    have hadj : F.incidenceGraph.Adj (Sum.inl item) cycle.snd :=
      cycle.adj_snd hcycle.not_nil
    have hmem : cycle.snd ∈ cycle.support.tail :=
      cycle.snd_mem_tail_support hcycle.not_nil
    cases hsnd : cycle.snd with
    | inl item' =>
      rw [hsnd] at hadj
      simp [incidenceGraph] at hadj
    | inr setId =>
      refine ⟨setId, ?_⟩
      have : Sum.inr setId ∈ cycle.support.tail := by simpa [hsnd] using hmem
      exact List.mem_of_mem_tail this

/-- The selected choice-set vertex at which an actual packed incidence cycle
is canonically based. -/
noncomputable def packingCycleBaseSet
    {maxLength : Nat}
    (P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking
      F.incidenceGraph maxLength) (cycle : P.Cycle) : F.SetId :=
  Classical.choose (F.exists_set_vertex_on_incidence_simpleCycle (P.isCycle cycle))

theorem packingCycleBaseSet_mem_support
    {maxLength : Nat}
    (P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking
      F.incidenceGraph maxLength) (cycle : P.Cycle) :
    Sum.inr (F.packingCycleBaseSet P cycle) ∈ (P.walk cycle).2.support :=
  Classical.choose_spec (F.exists_set_vertex_on_incidence_simpleCycle (P.isCycle cycle))

/-- Rotate one packed simple cycle to the choice-set side.  Rotation preserves
its unordered edge support and its simple-cycle property. -/
noncomputable def normalizedPackingCycleWalk
    {maxLength : Nat}
    (P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking
      F.incidenceGraph maxLength) (cycle : P.Cycle) :
    F.incidenceGraph.Walk (Sum.inr (F.packingCycleBaseSet P cycle))
      (Sum.inr (F.packingCycleBaseSet P cycle)) :=
  (P.walk cycle).2.rotate (Sum.inr (F.packingCycleBaseSet P cycle))
    (F.packingCycleBaseSet_mem_support P cycle)

theorem normalizedPackingCycleWalk_isCycle
    {maxLength : Nat}
    (P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking
      F.incidenceGraph maxLength) (cycle : P.Cycle) :
    (F.normalizedPackingCycleWalk P cycle).IsCycle :=
  (P.isCycle cycle).rotate (F.packingCycleBaseSet_mem_support P cycle)

theorem normalizedPackingCycleWalk_length
    {maxLength : Nat}
    (P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking
      F.incidenceGraph maxLength) (cycle : P.Cycle) :
    (F.normalizedPackingCycleWalk P cycle).length = (P.walk cycle).2.length :=
  SimpleGraph.Walk.length_rotate _ _ _

theorem normalizedPackingCycleWalk_edges_toFinset
    {maxLength : Nat}
    (P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking
      F.incidenceGraph maxLength) (cycle : P.Cycle) :
    (F.normalizedPackingCycleWalk P cycle).edges.toFinset =
      (P.walk cycle).2.edges.toFinset := by
  ext edge
  simp only [List.mem_toFinset]
  exact (SimpleGraph.Walk.rotate_edges _ _ _).perm.mem_iff

/-- A complete packing can be recentered independently at a choice-set vertex
of each of its cycles without changing its cycle indices, length bounds, or
edge partition.  This normal form is the convenient input for the source's
alternating orientation. -/
noncomputable def normalizedPacking
    {maxLength : Nat}
    (P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking
      F.incidenceGraph maxLength) :
    AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking F.incidenceGraph maxLength where
  Cycle := P.Cycle
  instFintypeCycle := P.instFintypeCycle
  instDecidableEqCycle := P.instDecidableEqCycle
  walk := fun cycle => ⟨Sum.inr (F.packingCycleBaseSet P cycle),
    F.normalizedPackingCycleWalk P cycle⟩
  isCycle := fun cycle => F.normalizedPackingCycleWalk_isCycle P cycle
  length_le := fun cycle => by
    rw [F.normalizedPackingCycleWalk_length]
    exact P.length_le cycle
  pairwiseDisjoint := by
    intro first _ second _ hne
    simpa only [F.normalizedPackingCycleWalk_edges_toFinset] using
      P.pairwiseDisjoint (Set.mem_univ first) (Set.mem_univ second) hne

theorem normalizedPacking_cycle_edges_toFinset
    {maxLength : Nat}
    (P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking
      F.incidenceGraph maxLength) (cycle : P.Cycle) :
    ((F.normalizedPacking P).walk cycle).2.edges.toFinset =
      (P.walk cycle).2.edges.toFinset :=
  F.normalizedPackingCycleWalk_edges_toFinset P cycle

theorem normalizedPacking_usedEdges
    {maxLength : Nat}
    (P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking
      F.incidenceGraph maxLength) :
    (F.normalizedPacking P).usedEdges = P.usedEdges := by
  ext edge
  simp only [AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking.usedEdges,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨cycle, hedge⟩
    exact ⟨cycle, by
      rw [F.normalizedPacking_cycle_edges_toFinset] at hedge
      exact hedge⟩
  · rintro ⟨cycle, hedge⟩
    exact ⟨cycle, by
      rw [F.normalizedPacking_cycle_edges_toFinset]
      exact hedge⟩

theorem normalizedPacking_isComplete
    {maxLength : Nat}
    (P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking
      F.incidenceGraph maxLength) (hcomplete : P.IsComplete) :
    (F.normalizedPacking P).IsComplete := by
  unfold AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking.IsComplete
  rw [F.normalizedPacking_usedEdges]
  exact hcomplete

/-- Along an incidence-graph walk begun at a choice-set vertex, every even
walk index is again a choice-set vertex. -/
theorem incidenceWalk_getVert_two_mul_is_set
    {baseSet : F.SetId} {endVertex : Sum F.Item F.SetId}
    (walk : F.incidenceGraph.Walk (Sum.inr baseSet) endVertex)
    (k : Nat) (hbound : 2 * k < walk.length) :
    ∃ setId : F.SetId, walk.getVert (2 * k) = Sum.inr setId := by
  induction k with
  | zero => exact ⟨baseSet, walk.getVert_zero⟩
  | succ k ih =>
    have hprevious : 2 * k < walk.length := by omega
    obtain ⟨setId, hset⟩ := ih hprevious
    have hadjItem := walk.adj_getVert_succ hprevious
    rw [hset] at hadjItem
    cases hitem : walk.getVert (2 * k + 1) with
    | inr setId' =>
      rw [hitem] at hadjItem
      simp [incidenceGraph] at hadjItem
    | inl item =>
      have hitemBound : 2 * k + 1 < walk.length := by omega
      have hadjSet := walk.adj_getVert_succ hitemBound
      rw [hitem] at hadjSet
      cases hset' : walk.getVert (2 * k + 1 + 1) with
      | inl item' =>
        rw [hset'] at hadjSet
        simp [incidenceGraph] at hadjSet
      | inr setId' => exact ⟨setId', by rfl⟩

/-- Along an incidence-graph walk begun at a choice-set vertex, every odd
walk index is an item vertex. -/
theorem incidenceWalk_getVert_two_mul_add_one_is_item
    {baseSet : F.SetId} {endVertex : Sum F.Item F.SetId}
    (walk : F.incidenceGraph.Walk (Sum.inr baseSet) endVertex)
    (k : Nat) (hbound : 2 * k + 1 < walk.length) :
    ∃ item : F.Item, walk.getVert (2 * k + 1) = Sum.inl item := by
  have hprevious : 2 * k < walk.length := by omega
  obtain ⟨setId, hset⟩ := F.incidenceWalk_getVert_two_mul_is_set walk k hprevious
  have hadj := walk.adj_getVert_succ hprevious
  rw [hset] at hadj
  cases hitem : walk.getVert (2 * k + 1) with
  | inr setId' =>
    rw [hitem] at hadj
    simp [incidenceGraph] at hadj
  | inl item => exact ⟨item, rfl⟩

/-- The parity form of `incidenceWalk_getVert_two_mul_is_set`, convenient for
cycle positions rather than natural-number walk indices. -/
theorem incidenceWalk_getVert_even_is_set
    {baseSet : F.SetId} {endVertex : Sum F.Item F.SetId}
    (walk : F.incidenceGraph.Walk (Sum.inr baseSet) endVertex)
    (position : Fin walk.length) (heven : Even position.1) :
    ∃ setId : F.SetId, walk.getVert position.1 = Sum.inr setId := by
  rcases heven with ⟨k, hposition⟩
  have hbound : 2 * k < walk.length := by
    rw [show 2 * k = k + k by omega, ← hposition]
    exact position.2
  obtain ⟨setId, hset⟩ := F.incidenceWalk_getVert_two_mul_is_set walk k hbound
  refine ⟨setId, ?_⟩
  rw [hposition]
  simpa [show k + k = 2 * k by omega] using hset

/-- The parity form of `incidenceWalk_getVert_two_mul_add_one_is_item`. -/
theorem incidenceWalk_getVert_odd_is_item
    {baseSet : F.SetId} {endVertex : Sum F.Item F.SetId}
    (walk : F.incidenceGraph.Walk (Sum.inr baseSet) endVertex)
    (position : Fin walk.length) (hodd : Odd position.1) :
    ∃ item : F.Item, walk.getVert position.1 = Sum.inl item := by
  rcases hodd with ⟨k, hposition⟩
  have hbound : 2 * k + 1 < walk.length := by omega
  obtain ⟨item, hitem⟩ := F.incidenceWalk_getVert_two_mul_add_one_is_item walk k hbound
  refine ⟨item, ?_⟩
  rw [hposition]
  simpa [show k + k + 1 = 2 * k + 1 by omega] using hitem

/-- The source's Appendix-Lemma-9 pruning phase is now constructed for the
concrete incidence graph.  Deleting item vertices of degree at most two and
choice-set vertices of degree at most one leaves only isolated vertices or
the stated minimum degrees, while discarding at most `2n + m` edges. -/
theorem incidenceGraph_has_two_one_pruning :
    ∃ H : SimpleGraph (Sum F.Item F.SetId), ∃ instH : DecidableRel H.Adj,
      letI : DecidableRel H.Adj := instH
      H ≤ F.incidenceGraph ∧
        H.IsBipartiteWith F.itemVertices F.setVertices ∧
        (∀ vertex : Sum F.Item F.SetId, vertex ∈ F.itemVertices →
          H.degree vertex = 0 ∨ 3 ≤ H.degree vertex) ∧
        (∀ vertex : Sum F.Item F.SetId, vertex ∈ F.setVertices →
          H.degree vertex = 0 ∨ 2 ≤ H.degree vertex) ∧
        F.incidenceGraph.edgeFinset.card - H.edgeFinset.card ≤
          2 * Fintype.card F.Item + Fintype.card F.SetId := by
  obtain ⟨H, instH, hle, hBipartite, hleft, hright, hbudget⟩ :=
    AppliedModelingLib.Foundations.Graph.exists_bipartite_two_one_pruning
      (F.incidenceGraph_isBipartiteWith)
  letI : DecidableRel H.Adj := instH
  refine ⟨H, instH, hle, hBipartite, hleft, hright, ?_⟩
  rw [F.itemVertices_ncard, F.setVertices_ncard] at hbudget
  exact hbudget

/-- The breadth-first cycle-extraction step of Appendix Lemma 9 in the
concrete incidence graph.  Under the terminal two-one degree conditions, a
nonempty residual has an actual simple cycle with the source's logarithmic
floor bound. -/
theorem incidenceGraph_stable_has_source_short_cycle
    (hleft : ∀ vertex : Sum F.Item F.SetId, vertex ∈ F.itemVertices →
      F.incidenceGraph.degree vertex = 0 ∨ 3 ≤ F.incidenceGraph.degree vertex)
    (hright : ∀ vertex : Sum F.Item F.SetId, vertex ∈ F.setVertices →
      F.incidenceGraph.degree vertex = 0 ∨ 2 ≤ F.incidenceGraph.degree vertex)
    {root neighbor : Sum F.Item F.SetId}
    (hroot : root ∈ F.itemVertices) (hrootAdj : F.incidenceGraph.Adj root neighbor) :
    ∃ (start : Sum F.Item F.SetId) (cycle : F.incidenceGraph.Walk start start),
      cycle.IsCycle ∧
        cycle.length ≤ 2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊ := by
  obtain ⟨start, cycle, hcycle, hlength⟩ :=
    AppliedModelingLib.Foundations.Graph.exists_simpleCycle_of_bipartite_two_one_stable_length_le_source_log_bound
      (F.incidenceGraph_isBipartiteWith) hleft hright hroot hrootAdj
  rw [F.itemVertices_ncard] at hlength
  exact ⟨start, cycle, hcycle, hlength⟩

/-- The full prune/remove loop of Appendix Lemma 9 is now a constructed trace
for the concrete incidence graph.  It reaches an edgeless residual, charges
at most `2n + m` discarded edges, and records every selected simple cycle
with the stronger `4 * floor(log₂ n)` breadth-first cap. -/
theorem incidenceGraph_has_two_one_cycle_packing :
    ∃ k,
      AppliedModelingLib.Foundations.Graph.BipartiteCyclePacking
        F.incidenceGraph F.itemVertices F.setVertices k ∧
      k ≤ 2 * Fintype.card F.Item + Fintype.card F.SetId := by
  obtain ⟨k, hpacking, hbudget⟩ :=
    AppliedModelingLib.Foundations.Graph.exists_bipartite_two_one_cycle_packing
      (F.incidenceGraph_isBipartiteWith)
  rw [F.itemVertices_ncard, F.setVertices_ncard] at hbudget
  exact ⟨k, hpacking, hbudget⟩

/-- The second accounting bound in Appendix Lemma 9.  Besides the universal
`2n+m` deletion charge, the same constructed trace costs at most four per
item plus the number of odd-degree choice-set vertices in the input graph. -/
theorem incidenceGraph_has_parity_refined_two_one_cycle_packing :
    ∃ k,
      AppliedModelingLib.Foundations.Graph.BipartiteCyclePacking
        F.incidenceGraph F.itemVertices F.setVertices k ∧
      k ≤ 2 * Fintype.card F.Item + Fintype.card F.SetId ∧
      k ≤ 4 * Fintype.card F.Item +
        AppliedModelingLib.Foundations.Graph.oddDegreeCount F.incidenceGraph F.setVertices := by
  obtain ⟨k, hpacking, hbudget⟩ := F.incidenceGraph_has_two_one_cycle_packing
  have hparity := hpacking.parity_budget (F.incidenceGraph_isBipartiteWith)
  rw [F.itemVertices_ncard] at hparity
  exact ⟨k, hpacking, hbudget, hparity⟩

/-- Under the paper's Eulerian balance condition, every choice-set vertex of
the incidence graph has even degree, so the odd-right-vertex correction in
Appendix Lemma 9 vanishes. -/
theorem eulerian_incidenceGraph_oddDegreeCount_setVertices_eq_zero
    (hEulerian : F.Eulerian) :
    AppliedModelingLib.Foundations.Graph.oddDegreeCount F.incidenceGraph F.setVertices = 0 := by
  classical
  have heven := (F.eulerian_iff_incidenceGraph_even_degree).mp hEulerian
  rw [AppliedModelingLib.Foundations.Graph.oddDegreeCount_eq_card]
  apply Finset.card_eq_zero.mpr
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨vertex, hvertex⟩
  simp only [AppliedModelingLib.Foundations.Graph.oddDegreeFinset, Finset.mem_filter,
    Set.Finite.mem_toFinset] at hvertex
  rw [AppliedModelingLib.Foundations.Graph.degreeCount_eq_degree] at hvertex
  exact (Nat.not_odd_iff_even.mpr (heven vertex)) hvertex.2

/-- The concrete partial cycle decomposition supplied by Appendix Lemma 9:
the selected cycles are actual, simple, edge-disjoint, and have the source's
logarithmic cap; all other comparison-incidence edges are bounded by `2n+m`. -/
theorem incidenceGraph_has_source_short_cycle_packing :
    ∃ P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking F.incidenceGraph
        (2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊),
      F.incidenceCount - P.usedEdges.card ≤
        2 * Fintype.card F.Item + Fintype.card F.SetId := by
  obtain ⟨k, hpacking, hbudget⟩ := F.incidenceGraph_has_two_one_cycle_packing
  obtain ⟨P, hresidual⟩ := hpacking.exists_partialSimpleCyclePacking
  have hsourceCap : 4 * Nat.log 2 F.itemVertices.ncard ≤
      2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊ := by
    rw [F.itemVertices_ncard]
    exact AppliedModelingLib.Foundations.Graph.four_natLog_le_two_natFloor_two_logb _
  refine ⟨P.relaxLength hsourceCap, ?_⟩
  rw [P.usedEdges_relaxLength]
  calc
    F.incidenceCount - P.usedEdges.card =
        AppliedModelingLib.Foundations.Graph.edgeCount F.incidenceGraph - P.usedEdges.card := by
      rw [AppliedModelingLib.Foundations.Graph.edgeCount_eq_edgeFinset_card,
        F.incidenceGraph_edgeFinset_card]
    _ ≤ k := hresidual
    _ ≤ 2 * Fintype.card F.Item + Fintype.card F.SetId := hbudget

/-- The complete short-cycle phase of Appendix Lemma 9 for an Eulerian
comparison-incidence graph.  The selected cycles are actual, simple, and
edge-disjoint with the source logarithmic cap; the uncovered edges satisfy
both source deletion accounts, hence their minimum. -/
theorem eulerian_incidenceGraph_has_source_short_cycle_packing
    (hEulerian : F.Eulerian) :
    ∃ P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking F.incidenceGraph
        (2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊),
      F.incidenceCount - P.usedEdges.card ≤
        min (2 * Fintype.card F.Item + Fintype.card F.SetId)
          (4 * Fintype.card F.Item) := by
  obtain ⟨k, hpacking, hfirst, hsecond⟩ :=
    F.incidenceGraph_has_parity_refined_two_one_cycle_packing
  obtain ⟨P, hresidual⟩ := hpacking.exists_partialSimpleCyclePacking
  have hsourceCap : 4 * Nat.log 2 F.itemVertices.ncard ≤
      2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊ := by
    rw [F.itemVertices_ncard]
    exact AppliedModelingLib.Foundations.Graph.four_natLog_le_two_natFloor_two_logb _
  refine ⟨P.relaxLength hsourceCap, ?_⟩
  rw [P.usedEdges_relaxLength]
  apply le_min
  · calc
      F.incidenceCount - P.usedEdges.card =
          AppliedModelingLib.Foundations.Graph.edgeCount F.incidenceGraph - P.usedEdges.card := by
        rw [AppliedModelingLib.Foundations.Graph.edgeCount_eq_edgeFinset_card,
          F.incidenceGraph_edgeFinset_card]
      _ ≤ k := hresidual
      _ ≤ 2 * Fintype.card F.Item + Fintype.card F.SetId := hfirst
  · calc
      F.incidenceCount - P.usedEdges.card =
          AppliedModelingLib.Foundations.Graph.edgeCount F.incidenceGraph - P.usedEdges.card := by
        rw [AppliedModelingLib.Foundations.Graph.edgeCount_eq_edgeFinset_card,
          F.incidenceGraph_edgeFinset_card]
      _ ≤ k := hresidual
      _ ≤ 4 * Fintype.card F.Item +
          AppliedModelingLib.Foundations.Graph.oddDegreeCount F.incidenceGraph F.setVertices := hsecond
      _ = 4 * Fintype.card F.Item := by
        rw [F.eulerian_incidenceGraph_oddDegreeCount_setVertices_eq_zero hEulerian,
          Nat.add_zero]

/-- The Eulerian comparison-incidence graph has a complete peeling by actual
simple graph cycles, each of length at most `2n`.  This formalizes the
residual-cycle step of Appendix Lemma 10 after its separate short-cycle
packing phase has stopped. -/
theorem eulerian_incidenceGraph_has_boundedSimpleCyclePeeling
    (hEulerian : F.Eulerian) :
    AppliedModelingLib.Foundations.Graph.HasBoundedSimpleCyclePeeling
      (2 * Fintype.card F.Item) F.incidenceGraph := by
  have hpeeling :=
    AppliedModelingLib.Foundations.Graph.exists_boundedSimpleCyclePeeling_of_even_degree_of_isBipartiteWith
      (F.incidenceGraph_isBipartiteWith)
      ((F.eulerian_iff_incidenceGraph_even_degree).mp hEulerian)
  rw [F.itemVertices_ncard] at hpeeling
  exact hpeeling

/-- The Eulerian long-cycle phase is a complete partition, not merely a
peeling trace: all incidence edges belong to one finite edge-disjoint family
of actual simple cycles, each with the source `2n` length cap. -/
theorem eulerian_incidenceGraph_has_complete_cycle_packing
    (hEulerian : F.Eulerian) :
    ∃ P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking F.incidenceGraph
        (2 * Fintype.card F.Item),
      P.IsComplete := by
  exact AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking.exists_complete_of_boundedSimpleCyclePeeling
    (F.eulerian_incidenceGraph_has_boundedSimpleCyclePeeling hEulerian)

/-- The explicit Eulerian `2n` packing has total length equal to the source
incidence count `d`; this is the graph-partition form of the first numerical
identity in Appendix Lemma 10. -/
theorem eulerian_incidenceGraph_exists_complete_cycle_packing_with_total_length
    (hEulerian : F.Eulerian) :
    ∃ P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking F.incidenceGraph
        (2 * Fintype.card F.Item),
      P.IsComplete ∧
        (∑ cycle : P.Cycle, (P.walk cycle).2.length) = F.incidenceCount := by
  obtain ⟨P, hcomplete⟩ := F.eulerian_incidenceGraph_has_complete_cycle_packing hEulerian
  refine ⟨P, hcomplete, ?_⟩
  calc
    (∑ cycle : P.Cycle, (P.walk cycle).2.length) =
        Fintype.card F.incidenceGraph.edgeSet := P.sum_length_eq_edgeSet_card hcomplete
    _ = F.incidenceGraph.edgeFinset.card := SimpleGraph.edgeFinset_card.symm
    _ = F.incidenceCount := F.incidenceGraph_edgeFinset_card

/-- Given a complete graph-cycle packing, the paper's observations are indexed
by exactly one position of exactly one selected cycle.  This is the concrete
edge-to-observation part of the bridge to `CycleDecomposition`. -/
noncomputable def observationPositionEquiv
    {maxLength : Nat}
    (P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking
      F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) :
    (Sigma fun cycle => Fin ((P.walk cycle).2.length)) ≃ F.Observation :=
  (P.edgePositionEquiv hcomplete).trans F.observationEdgeEquiv.symm

theorem observationEdge_observationPositionEquiv_apply
    {maxLength : Nat}
    (P : AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking
      F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (position : Fin ((P.walk cycle).2.length)) :
    F.observationEdge (F.observationPositionEquiv P hcomplete ⟨cycle, position⟩) =
      (AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
        (P.isCycle cycle) position).1 := by
  have h := F.observationEdgeEquiv.apply_symm_apply
    (P.edgePositionEquiv hcomplete ⟨cycle, position⟩)
  change F.observationEdge
      (F.observationEdgeEquiv.symm (P.edgePositionEquiv hcomplete ⟨cycle, position⟩)) = _
  rw [← P.edgePositionEquiv_apply hcomplete cycle position]
  exact congrArg Subtype.val h

end ChoiceFrame

end SeshadriUgander2020IIATesting
