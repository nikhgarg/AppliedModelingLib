import LOS02CombinatorialAuctions.FiniteGraphTableEncoding
import AppliedModelingLib.Algorithms.Complexity.TuringMachine

/-!
# Native Boolean-table complement for the Theorem 6.1 source route

The source proof transfers clique hardness through graph complementation.
This module lowers the Boolean-table part of that transfer to an actual TM2
machine.  It is deliberately a raw table transformation: preserving the
simple-graph loop convention and expanding a graph table to explicit auction
bid rows are separate source-specific obligations.
-/

namespace LOS02CombinatorialAuctions

open AppliedModelingLib.Complexity

/-- Complement every Boolean entry of a uniformly encoded adjacency table.
At this representation boundary the diagonal is also complemented; a later
simple-graph adapter must account for the source convention that loops are
ignored. -/
noncomputable def uniformGraphInputBitwiseComplement
    (input : UniformGraphInput) : UniformGraphInput :=
  ⟨input.1, fun index => !(input.2 index)⟩

/-- The table complement keeps the unary vertex header and negates precisely
the flattened Boolean payload. -/
theorem uniformGraphInputBitwiseComplement_code
    (input : UniformGraphInput) :
    uniformGraphInputCode (uniformGraphInputBitwiseComplement input) =
      unaryIndexEncode input.1 ++ (List.ofFn input.2).map (!·) := by
  rcases input with ⟨n, adjacency⟩
  simp [uniformGraphInputBitwiseComplement, uniformGraphInputCode,
    List.map_ofFn, Function.comp_def]

/-- The raw Boolean-table complement has an actual finite TM2 realization.
The machine copies the terminated-unary vertex header and transforms only the
following adjacency payload. -/
noncomputable def uniformGraphInputBitwiseComplementComputableInPolyTime :
    Turing.TM2ComputableInPolyTime
      uniformGraphInputEncoding.encode uniformGraphInputEncoding.encode
      uniformGraphInputBitwiseComplement where
  tm := UnaryHeaderBooleanListMap.machine Bool.not
  inputAlphabet := BooleanListMap.boolIdentityEquiv
  outputAlphabet := BooleanListMap.boolIdentityEquiv
  time := 2 * Polynomial.X + 2
  outputsFun input := by
    rcases input with ⟨n, adjacency⟩
    have hsource :
        uniformGraphInputEncoding.encode ⟨n, adjacency⟩ =
          unaryIndexEncode n ++ List.ofFn adjacency :=
      rfl
    have htarget :
        uniformGraphInputEncoding.encode
            (uniformGraphInputBitwiseComplement ⟨n, adjacency⟩) =
          unaryIndexEncode n ++ (List.ofFn adjacency).map Bool.not := by
      change uniformGraphInputCode
          (uniformGraphInputBitwiseComplement ⟨n, adjacency⟩) = _
      simpa using uniformGraphInputBitwiseComplement_code ⟨n, adjacency⟩
    rw [hsource, htarget]
    change Turing.TM2OutputsInTime (UnaryHeaderBooleanListMap.machine Bool.not)
      (List.map (fun bit => bit) (unaryIndexEncode n ++ List.ofFn adjacency))
      (some (List.map (fun bit => bit)
        (unaryIndexEncode n ++ (List.ofFn adjacency).map Bool.not))) _
    simpa [uniformGraphInputEncoding, uniformGraphInputCode,
      uniformGraphInputBitwiseComplement, BooleanListMap.boolIdentityEquiv,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Nat.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.map_ofFn, Function.comp_def] using
      UnaryHeaderBooleanListMap.outputsInTime Bool.not n (List.ofFn adjacency)

/-- On a source-valid simple graph table, bitwise negation realizes the graph
complement at every pair of distinct vertices. The diagonal changes at the
raw encoding level but is ignored by `SimpleGraph.fromRel`. -/
theorem uniformGraphInputBitwiseComplement_adj_iff
    (input : UniformSimpleGraphInput) (v w : Fin input.1.1) :
    (uniformGraphInputSimpleGraph
        (uniformGraphInputBitwiseComplement input.1)).Adj v w ↔
      v ≠ w ∧ ¬(uniformGraphInputSimpleGraph input.1).Adj v w := by
  by_cases hvw : v = w
  · subst w
    simp [uniformGraphInputSimpleGraph, FiniteGraphTable.toSimpleGraph]
  · simp [uniformGraphInputSimpleGraph, FiniteGraphTable.toSimpleGraph,
      FiniteGraphTable.ofEncodedAdjacency, uniformGraphInputBitwiseComplement,
      hvw, input.property.1 v w]

/-- Independent-set threshold decision for a raw uniformly encoded graph
table. The graph constructor retains the standard simple-graph convention, so
diagonal table entries are semantically ignored. -/
def uniformGraphInputIndependentDecision
    (input : UniformGraphInput) (threshold : Nat) : Prop :=
  ∃ selected : Finset (Fin input.1),
    AppliedModelingLib.Auction.GraphIndependentSelection
      (uniformGraphInputSimpleGraph input) selected ∧
      threshold ≤ selected.card

/-- Bitwise complementation preserves table symmetry.  Its diagonal need not
remain loop-free, which is harmless for the distinct-bidder feasibility
relation used by the explicit incidence auction. -/
theorem uniformGraphInputBitwiseComplement_symmetric
    (input : UniformSimpleGraphInput) :
    ∀ v w,
      (uniformGraphInputBitwiseComplement input.1).2 (finPairIndex (v, w)) =
        (uniformGraphInputBitwiseComplement input.1).2 (finPairIndex (w, v)) := by
  intro v w
  simp [uniformGraphInputBitwiseComplement, input.property.1 v w]

/-- The explicit unit-weight incidence auction has exactly the independent
sets of a symmetric raw graph table, even if its diagonal entries are
arbitrary.  This is the semantic table-expansion half of the source reduction;
its native TM2 materializer is a separate obligation. -/
theorem uniformGraphInputIndependentDecision_iff_unitWeightAuctionDecision
    (input : UniformGraphInput)
    (hsymm : ∀ v w, input.2 (finPairIndex (v, w)) =
      input.2 (finPairIndex (w, v)))
    (threshold : Nat) :
    uniformGraphInputIndependentDecision input threshold ↔
      uniformUnitWeightAuctionDecision
        (uniformGraphToUnitWeightAuctionInput input) threshold := by
  constructor
  · rintro ⟨selected, hind, hcard⟩
    refine ⟨selected, ?_, hcard⟩
    intro u v hu hv huv
    rw [uniformGraphToUnitWeightAuctionInput_row input u,
      uniformGraphToUnitWeightAuctionInput_row input v]
    exact
      (uniformGraphInput_ordered_map_feasibility_iff_of_symmetric
        input hsymm selected).2 hind hu hv huv
  · rintro ⟨selected, hfeasible, hcard⟩
    refine ⟨selected, ?_, hcard⟩
    apply
      (uniformGraphInput_ordered_map_feasibility_iff_of_symmetric
        input hsymm selected).1
    intro u v hu hv huv
    have hrow := hfeasible hu hv huv
    simpa only [uniformGraphToUnitWeightAuctionInput_row] using hrow

/-- The source clique decision is exactly the raw-table independent-set
decision after the native bitwise complement. -/
theorem uniformSimpleGraphCliqueDecision_iff_bitwiseComplement_independentDecision
    (input : UniformSimpleGraphInput) (threshold : Nat) :
    uniformSimpleGraphCliqueDecision input threshold ↔
      uniformGraphInputIndependentDecision
        (uniformGraphInputBitwiseComplement input.1) threshold := by
  constructor
  · rintro ⟨selected, hclique, hcard⟩
    refine ⟨selected, ?_, hcard⟩
    intro u v hu hv huv hadj
    exact (uniformGraphInputBitwiseComplement_adj_iff input u v).mp hadj |>.2
      (hclique hu hv huv)
  · rintro ⟨selected, hindependent, hcard⟩
    refine ⟨selected, ?_, hcard⟩
    intro u v hu hv huv
    by_contra hnotadj
    apply (hindependent hu hv huv)
    exact (uniformGraphInputBitwiseComplement_adj_iff input u v).mpr
      ⟨huv, hnotadj⟩

/-- The source's direct graph-to-auction construction is semantically exact
after native raw-table complementation.  The diagonal Boolean entries produced
by bitwise complement are intentionally retained: they are removed by graph
semantics and cannot create an overlap between distinct bidder rows. -/
theorem uniformSimpleGraphCliqueDecision_iff_bitwiseComplement_unitWeightAuctionDecision
    (input : UniformSimpleGraphInput) (threshold : Nat) :
    uniformSimpleGraphCliqueDecision input threshold ↔
      uniformUnitWeightAuctionDecision
        (uniformGraphToUnitWeightAuctionInput
          (uniformGraphInputBitwiseComplement input.1)) threshold := by
  rw [uniformSimpleGraphCliqueDecision_iff_bitwiseComplement_independentDecision]
  exact uniformGraphInputIndependentDecision_iff_unitWeightAuctionDecision
    (uniformGraphInputBitwiseComplement input.1)
    (uniformGraphInputBitwiseComplement_symmetric input) threshold

/-- The same finite TM2 program realizes bitwise complementation when the
source input is restricted to symmetric, loop-free graph tables. -/
noncomputable def uniformSimpleGraphCliqueToRawIndependentComputableInPolyTime :
    Turing.TM2ComputableInPolyTime
      uniformSimpleGraphInputEncoding.encode uniformGraphInputEncoding.encode
      (fun input => uniformGraphInputBitwiseComplement input.1) where
  tm := UnaryHeaderBooleanListMap.machine Bool.not
  inputAlphabet := BooleanListMap.boolIdentityEquiv
  outputAlphabet := BooleanListMap.boolIdentityEquiv
  time := 2 * Polynomial.X + 2
  outputsFun input := by
    rcases input with ⟨⟨n, adjacency⟩, hgraph⟩
    have hsource :
        uniformSimpleGraphInputEncoding.encode ⟨⟨n, adjacency⟩, hgraph⟩ =
          unaryIndexEncode n ++ List.ofFn adjacency :=
      rfl
    have htarget :
        uniformGraphInputEncoding.encode
            (uniformGraphInputBitwiseComplement ⟨n, adjacency⟩) =
          unaryIndexEncode n ++ (List.ofFn adjacency).map Bool.not := by
      change uniformGraphInputCode
          (uniformGraphInputBitwiseComplement ⟨n, adjacency⟩) = _
      simpa using uniformGraphInputBitwiseComplement_code ⟨n, adjacency⟩
    rw [hsource, htarget]
    change Turing.TM2OutputsInTime (UnaryHeaderBooleanListMap.machine Bool.not)
      (List.map (fun bit => bit) (unaryIndexEncode n ++ List.ofFn adjacency))
      (some (List.map (fun bit => bit)
        (unaryIndexEncode n ++ (List.ofFn adjacency).map Bool.not))) _
    simpa [uniformSimpleGraphInputEncoding, uniformGraphInputEncoding,
      uniformGraphInputCode, uniformGraphInputBitwiseComplement,
      BooleanListMap.boolIdentityEquiv, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Nat.mul_comm, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, List.map_ofFn, Function.comp_def] using
      UnaryHeaderBooleanListMap.outputsInTime Bool.not n (List.ofFn adjacency)

/-- A genuine native TM2 many-one reduction for the clique-to-independent-set
complement step used implicitly by the source's Theorem 6.1 proof. Its target
is still a raw graph-table language, not the paper's explicit auction language. -/
noncomputable def uniformSimpleGraphCliqueToRawIndependentTM2PolynomialReduction
    (threshold : Nat) :
    TM2PolynomialTimeReduction
      uniformSimpleGraphInputEncoding uniformGraphInputEncoding
      (fun input => uniformSimpleGraphCliqueDecision input threshold)
      (fun input => uniformGraphInputIndependentDecision input threshold) where
  reduction :=
    { map := fun input => uniformGraphInputBitwiseComplement input.1
      correct := fun input =>
        uniformSimpleGraphCliqueDecision_iff_bitwiseComplement_independentDecision
          input threshold }
  machine := uniformSimpleGraphCliqueToRawIndependentComputableInPolyTime

end LOS02CombinatorialAuctions
