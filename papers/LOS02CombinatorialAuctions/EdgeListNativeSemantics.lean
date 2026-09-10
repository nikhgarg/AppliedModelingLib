import LOS02CombinatorialAuctions.EdgeListNativeMachine
import LOS02CombinatorialAuctions.FiniteGraphTableEncoding

/-!
# Semantic bridge for the streamed edge-list reduction

The native Theorem 6.1 transducer retains an ordered list of edge occurrences,
whereas the source reduction begins from an undirected simple graph.  This
module identifies the simple graph represented by the stream and proves that
the two streamed rows assigned to each edge have exactly the source incidence
semantics.  Repeated occurrences and choice of orientation are representation
details: they do not affect which pairs of distinct bidders share a good.
-/

namespace LOS02CombinatorialAuctions

open AppliedModelingLib.Complexity

/-- The undirected simple graph represented by an ordered edge stream.  A
loop occurrence is ignored by `SimpleGraph.fromRel`, exactly as required for a
simple-graph source instance. -/
def unaryEdgeListSimpleGraph (input : UnaryEdgeListGraphInput) :
    SimpleGraph (Fin input.1) :=
  SimpleGraph.fromRel (fun u v => (u, v) ∈ input.2)

/-- The edge-stream relation recovered by forgetting endpoint orientation. -/
def unaryEdgeListAdj {n : Nat} (edges : List (Fin n × Fin n))
    (u v : Fin n) : Prop :=
  (u, v) ∈ edges ∨ (v, u) ∈ edges

theorem unaryEdgeListSimpleGraph_adj_iff (input : UnaryEdgeListGraphInput)
    (u v : Fin input.1) :
    (unaryEdgeListSimpleGraph input).Adj u v ↔
      u ≠ v ∧ unaryEdgeListAdj input.2 u v := by
  rfl

/-- The goods requested by one bidder in an edge list: every endpoint pair
incident to that bidder, with repeated records quotiented by `Finset`. -/
def unaryEdgeListRequestedItems (input : UnaryEdgeListGraphInput)
    (v : Fin input.1) : Finset (Fin input.1 × Fin input.1) :=
  input.2.toFinset.filter (fun edge => v = edge.1 ∨ v = edge.2)

@[simp] theorem mem_unaryEdgeListRequestedItems_iff
    (input : UnaryEdgeListGraphInput) (v : Fin input.1)
    (item : Fin input.1 × Fin input.1) :
    item ∈ unaryEdgeListRequestedItems input v ↔
      item ∈ input.2 ∧ (v = item.1 ∨ v = item.2) := by
  simp [unaryEdgeListRequestedItems]

/-- The finite set of goods requested by one bidder from a streamed auction
incidence list. -/
def unaryEdgeListAuctionRequestedItems (input : UnaryEdgeListAuctionInput)
    (v : Fin input.1) : Finset (Fin input.1 × Fin input.1) :=
  (input.2.filterMap fun record =>
    if record.1 = v then some record.2 else none).toFinset

/-- The native transducer's row for each bidder is precisely the finite set of
edge pairs incident to that vertex in the input stream. -/
theorem unaryEdgeListAuctionRequestedItems_map
    (input : UnaryEdgeListGraphInput) (v : Fin input.1) :
    unaryEdgeListAuctionRequestedItems (unaryEdgeListGraphToAuction input) v =
      unaryEdgeListRequestedItems input v := by
  rcases input with ⟨n, edges⟩
  ext item
  change item ∈
      (List.filterMap (fun record =>
        if record.1 = v then some record.2 else none)
        (edges.flatMap edgeIncidenceRecords)).toFinset ↔
    item ∈ edges.toFinset.filter (fun edge => v = edge.1 ∨ v = edge.2)
  constructor
  · intro hitem
    have hitem' := List.mem_toFinset.mp hitem
    rcases List.mem_filterMap.mp hitem' with ⟨record, hrecord, houtput⟩
    rcases List.mem_flatMap.mp hrecord with ⟨edge, hedge, hrecordEdge⟩
    simp [edgeIncidenceRecords] at hrecordEdge
    rcases hrecordEdge with hrecordEdge | hrecordEdge
    · subst record
      by_cases hfirst : edge.1 = v
      · simp [hfirst] at houtput
        subst item
        exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hedge,
          Or.inl hfirst.symm⟩
      · simp [hfirst] at houtput
    · subst record
      by_cases hsecond : edge.2 = v
      · simp [hsecond] at houtput
        subst item
        exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hedge,
          Or.inr hsecond.symm⟩
      · simp [hsecond] at houtput
  · rintro hitem
    rcases Finset.mem_filter.mp hitem with ⟨hitem, hendpoint | hendpoint⟩
    · apply List.mem_toFinset.mpr
      apply List.mem_filterMap.mpr
      refine ⟨(item.1, item), ?_, ?_⟩
      · apply List.mem_flatMap.mpr
        exact ⟨item, List.mem_toFinset.mp hitem, by simp [edgeIncidenceRecords]⟩
      · simp [hendpoint.symm]
    · apply List.mem_toFinset.mpr
      apply List.mem_filterMap.mpr
      refine ⟨(item.2, item), ?_, ?_⟩
      · apply List.mem_flatMap.mpr
        exact ⟨item, List.mem_toFinset.mp hitem, by simp [edgeIncidenceRecords]⟩
      · simp [hendpoint.symm]

/-- Pairwise-disjoint feasibility for a streamed unit-weight auction instance. -/
def unaryEdgeListAuctionFeasible (input : UnaryEdgeListAuctionInput)
    (selected : Finset (Fin input.1)) : Prop :=
  ∀ ⦃u v : Fin input.1⦄, u ∈ selected → v ∈ selected → u ≠ v →
    Disjoint
      (unaryEdgeListAuctionRequestedItems input u)
      (unaryEdgeListAuctionRequestedItems input v)

/-- The source construction is semantically exact on the undirected simple
graph represented by the edge stream: a selected bidder set has pairwise
disjoint requested goods exactly when it is an independent vertex set.  This
is unaffected by an edge's stored orientation or by duplicate occurrences. -/
theorem unaryEdgeListAuctionFeasible_map_iff_graphIndependentSelection
    (input : UnaryEdgeListGraphInput) (selected : Finset (Fin input.1)) :
    unaryEdgeListAuctionFeasible (unaryEdgeListGraphToAuction input) selected ↔
      AppliedModelingLib.Auction.GraphIndependentSelection
        (unaryEdgeListSimpleGraph input) selected := by
  constructor
  · intro hfeasible u v hu hv huv hadj
    have hdisjoint : Disjoint
        (unaryEdgeListRequestedItems input u)
        (unaryEdgeListRequestedItems input v) := by
      simpa only [unaryEdgeListAuctionRequestedItems_map] using
        (hfeasible hu hv huv)
    rcases (unaryEdgeListSimpleGraph_adj_iff input u v).mp hadj with
      ⟨_, hforward | hreverse⟩
    · have hmemU : (u, v) ∈ unaryEdgeListRequestedItems input u :=
        (mem_unaryEdgeListRequestedItems_iff input u (u, v)).mpr
          ⟨hforward, Or.inl rfl⟩
      have hmemV : (u, v) ∈ unaryEdgeListRequestedItems input v :=
        (mem_unaryEdgeListRequestedItems_iff input v (u, v)).mpr
          ⟨hforward, Or.inr rfl⟩
      exact (Finset.disjoint_left.mp hdisjoint) hmemU hmemV
    · have hmemU : (v, u) ∈ unaryEdgeListRequestedItems input u :=
        (mem_unaryEdgeListRequestedItems_iff input u (v, u)).mpr
          ⟨hreverse, Or.inr rfl⟩
      have hmemV : (v, u) ∈ unaryEdgeListRequestedItems input v :=
        (mem_unaryEdgeListRequestedItems_iff input v (v, u)).mpr
          ⟨hreverse, Or.inl rfl⟩
      exact (Finset.disjoint_left.mp hdisjoint) hmemU hmemV
  · intro hindependent u v hu hv huv
    apply Finset.disjoint_left.mpr
    intro item hmemU hmemV
    rw [unaryEdgeListAuctionRequestedItems_map] at hmemU hmemV
    have hU := (mem_unaryEdgeListRequestedItems_iff input u item).mp hmemU
    have hV := (mem_unaryEdgeListRequestedItems_iff input v item).mp hmemV
    have hadj : (unaryEdgeListSimpleGraph input).Adj u v := by
      rw [unaryEdgeListSimpleGraph_adj_iff]
      refine ⟨huv, ?_⟩
      rcases hU.2 with hU | hU <;> rcases hV.2 with hV | hV
      · exact False.elim (huv (hU.trans hV.symm))
      · subst u
        subst v
        exact Or.inl hU.1
      · subst u
        subst v
        exact Or.inr hU.1
      · exact False.elim (huv (hU.trans hV.symm))
    exact (hindependent hu hv huv) hadj

/-- Independent-set threshold decision for the simple graph represented by an
edge stream.  The threshold is a common parameter of the two languages; the
native transducer changes only the graph/auction payload. -/
def unaryEdgeListGraphIndependentDecision (threshold : Nat)
    (input : UnaryEdgeListGraphInput) : Prop :=
  ∃ selected : Finset (Fin input.1),
    AppliedModelingLib.Auction.GraphIndependentSelection
      (unaryEdgeListSimpleGraph input) selected ∧
      threshold ≤ selected.card

/-- Unit-weight set-packing threshold decision for a streamed auction input. -/
def unaryEdgeListAuctionDecision (threshold : Nat)
    (input : UnaryEdgeListAuctionInput) : Prop :=
  ∃ selected : Finset (Fin input.1),
    unaryEdgeListAuctionFeasible input selected ∧ threshold ≤ selected.card

/-- The source direct construction preserves every independent-set threshold
decision on the simple graph encoded by its edge stream. -/
theorem unaryEdgeListGraphToAuction_decision_correct
    (threshold : Nat) (input : UnaryEdgeListGraphInput) :
    unaryEdgeListGraphIndependentDecision threshold input ↔
      unaryEdgeListAuctionDecision threshold
        (unaryEdgeListGraphToAuction input) := by
  constructor
  · rintro ⟨selected, hindependent, hcard⟩
    exact ⟨selected,
      (unaryEdgeListAuctionFeasible_map_iff_graphIndependentSelection input selected).mpr
        hindependent,
      hcard⟩
  · rintro ⟨selected, hfeasible, hcard⟩
    exact ⟨selected,
      (unaryEdgeListAuctionFeasible_map_iff_graphIndependentSelection input selected).mp
        hfeasible,
      hcard⟩

/-- A genuine finite-TM2 many-one reduction for the graph-to-streamed-auction
part of Theorem 6.1.  Its machine is the checked transducer in
`EdgeListNativeMachine`; correctness is the preceding exact decision bridge.
It does not yet assert the source's clique hardness or inapproximability
consequences. -/
noncomputable def unaryEdgeListGraphToAuctionTM2PolynomialReduction
    (threshold : Nat) :
    TM2PolynomialTimeReduction
      unaryEdgeListGraphInputEncoding unaryEdgeListAuctionInputEncoding
      (unaryEdgeListGraphIndependentDecision threshold)
      (unaryEdgeListAuctionDecision threshold) where
  reduction :=
    { map := unaryEdgeListGraphToAuction
      correct := unaryEdgeListGraphToAuction_decision_correct threshold }
  machine := by
    simpa [TM2PolynomialTimeMap] using EdgeListNativeMachine.computableInPolyTime

/-- The variable threshold is part of the encoded source instance. -/
def unaryEdgeListGraphThresholdDecision
    (input : UnaryEdgeListGraphThresholdInput) : Prop :=
  unaryEdgeListGraphIndependentDecision input.1 input.2

/-- The target decision instance retains its encoded threshold. -/
def unaryEdgeListAuctionThresholdDecision
    (input : UnaryEdgeListAuctionThresholdInput) : Prop :=
  unaryEdgeListAuctionDecision input.1 input.2

theorem unaryEdgeListGraphThresholdToAuction_decision_correct
    (input : UnaryEdgeListGraphThresholdInput) :
    unaryEdgeListGraphThresholdDecision input ↔
      unaryEdgeListAuctionThresholdDecision
        (unaryEdgeListGraphThresholdToAuction input) := by
  rcases input with ⟨threshold, input⟩
  exact unaryEdgeListGraphToAuction_decision_correct threshold input

/-- The original finite TM2 machine can carry the threshold because its first
terminated-unary header is copied without inspecting its numeric meaning. -/
noncomputable def unaryEdgeListGraphThresholdToAuctionComputableInPolyTime :
    Turing.TM2ComputableInPolyTime
      unaryEdgeListGraphThresholdInputEncoding.encode
      unaryEdgeListAuctionThresholdInputEncoding.encode
      unaryEdgeListGraphThresholdToAuction where
  tm := EdgeListNativeMachine.machine
  inputAlphabet := BooleanListMap.boolIdentityEquiv
  outputAlphabet := BooleanListMap.boolIdentityEquiv
  time := 7 * Polynomial.X
  outputsFun input := by
    rcases input with ⟨threshold, ⟨n, edges⟩⟩
    simp only [unaryEdgeListGraphThresholdInputEncoding,
      unaryEdgeListAuctionThresholdInputEncoding, encodingOfInjectiveList]
    change Turing.TM2OutputsInTime EdgeListNativeMachine.machine
      (List.map (fun bit => bit)
        (unaryEdgeListGraphThresholdInputCode ⟨threshold, ⟨n, edges⟩⟩))
      (some (List.map (fun bit => bit)
        (unaryEdgeListAuctionThresholdInputCode
          (unaryEdgeListGraphThresholdToAuction ⟨threshold, ⟨n, edges⟩⟩)))) _
    rw [unaryEdgeListAuctionThresholdInputCode_map]
    simpa [unaryEdgeListGraphThresholdInputEncoding,
      unaryEdgeListAuctionThresholdInputEncoding, BooleanListMap.boolIdentityEquiv,
      unaryEdgeListGraphThresholdInputCode, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] using
      (EdgeListNativeMachine.outputsInTime_with_header
        (unaryEdgeListThresholdHeader threshold n) edges)

/-- A variable-threshold native TM2 many-one reduction for the direct
edge-list construction in Theorem 6.1.  It establishes only the graph to
unit-weight auction leg; clique complementation and the cited hardness results
remain separate obligations. -/
noncomputable def unaryEdgeListGraphThresholdToAuctionTM2PolynomialReduction :
    TM2PolynomialTimeReduction
      unaryEdgeListGraphThresholdInputEncoding
      unaryEdgeListAuctionThresholdInputEncoding
      unaryEdgeListGraphThresholdDecision
      unaryEdgeListAuctionThresholdDecision where
  reduction :=
    { map := unaryEdgeListGraphThresholdToAuction
      correct := unaryEdgeListGraphThresholdToAuction_decision_correct }
  machine := by
    simpa [TM2PolynomialTimeMap] using
      unaryEdgeListGraphThresholdToAuctionComputableInPolyTime

end LOS02CombinatorialAuctions
