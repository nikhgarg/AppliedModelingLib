import LOS02CombinatorialAuctions.FiniteGraphTableEncoding

/-!
# Executable row-major encoding for the Theorem 6.1 reduction

The existing finite semantic reduction indexes pairs and triples through a
general finite-type equivalence.  A native Turing machine needs a concrete tape
order instead.  This module uses the standard computable `Fin` product
equivalence, so an input graph table and its ordered-incidence output are
serialized in row-major order.  It establishes the executable representation
and its pointwise correspondence; supplying the TM2 program remains a separate
next step.
-/

namespace LOS02CombinatorialAuctions

/-- The computable row-major index for an ordered pair of vertices. -/
def rowMajorPairEquiv (n : Nat) :
    Fin n × Fin n ≃ Fin (n * n) :=
  finProdFinEquiv

/-- The computable row-major index for an applicant and an ordered edge. -/
def rowMajorTripleEquiv (n : Nat) :
    Fin n × (Fin n × Fin n) ≃ Fin (n * (n * n)) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) (rowMajorPairEquiv n)).trans
    (finProdFinEquiv : Fin n × Fin (n * n) ≃ Fin (n * (n * n)))

/-- A unit-weight auction table whose index order is explicitly the computable
row-major `Fin` product order. -/
abbrev RowMajorUnitWeightAuctionInput :=
  Sigma (fun n : Nat => Fin (n * (n * n)) → Bool)

/-- Binary source code for a row-major unit-weight auction input: a terminated
unary vertex count followed by its row-major incidence table. -/
def rowMajorUnitWeightAuctionInputCode
    (input : RowMajorUnitWeightAuctionInput) : List Bool :=
  AppliedModelingLib.Complexity.unaryIndexEncode input.1 ++ List.ofFn input.2

theorem rowMajorUnitWeightAuctionInputCode_injective :
    Function.Injective rowMajorUnitWeightAuctionInputCode := by
  rintro ⟨n, table⟩ ⟨m, table'⟩ hcode
  have hheader := congrArg AppliedModelingLib.Complexity.unaryIndexDecode hcode
  simp [rowMajorUnitWeightAuctionInputCode,
    AppliedModelingLib.Complexity.unaryIndexDecode_encode_append] at hheader
  have hnm : n = m := hheader
  subst m
  have htail : List.ofFn table = List.ofFn table' := by
    exact List.append_right_injective _ hcode
  have htable : table = table' :=
    AppliedModelingLib.Complexity.listOfFn_injective htail
  cases htable
  rfl

noncomputable def rowMajorUnitWeightAuctionInputEncoding :
    AppliedModelingLib.Complexity.BinaryEncoding RowMajorUnitWeightAuctionInput :=
  AppliedModelingLib.Complexity.encodingOfInjectiveList
    rowMajorUnitWeightAuctionInputCode rowMajorUnitWeightAuctionInputCode_injective

@[simp] theorem rowMajorUnitWeightAuctionInputEncoding_size
    (input : RowMajorUnitWeightAuctionInput) :
    rowMajorUnitWeightAuctionInputEncoding.size input =
      input.1 + 1 + input.1 * (input.1 * input.1) := by
  change (rowMajorUnitWeightAuctionInputCode input).length = _
  simp [rowMajorUnitWeightAuctionInputCode,
    AppliedModelingLib.Complexity.unaryIndexEncode_length]

/-- The direct, computably indexed ordered-incidence map used by the source's
unit-price Clique-to-auction construction. -/
def rowMajorOrderedIncidenceTableMap {n : Nat}
    (adjacency : Fin (n * n) → Bool) : Fin (n * (n * n)) → Bool :=
  fun i =>
    let triple := (rowMajorTripleEquiv n).symm i
    adjacency (rowMajorPairEquiv n triple.2) &&
      (decide (triple.1 = triple.2.1) || decide (triple.1 = triple.2.2))

/-- The source graph-to-unit-weight-auction map with the exact serial order
that a binary machine must emit. -/
def uniformGraphToRowMajorUnitWeightAuctionInput
    (input : UniformGraphInput) : RowMajorUnitWeightAuctionInput :=
  ⟨input.1, rowMajorOrderedIncidenceTableMap input.2⟩

/-- The literal nested row-major bit stream that the native reduction machine
must emit after its unary vertex-count header. -/
def rowMajorOrderedIncidenceBitStream (input : UniformGraphInput) : List Bool :=
  (List.ofFn fun v : Fin input.1 =>
    (List.ofFn fun u : Fin input.1 =>
      List.ofFn fun w : Fin input.1 =>
        input.2 (rowMajorPairEquiv input.1 (u, w)) &&
          (decide (v = u) || decide (v = w))).flatten).flatten

theorem rowMajorUnitWeightAuctionInputCode_map_eq_bitStream
    (input : UniformGraphInput) :
    rowMajorUnitWeightAuctionInputCode
        (uniformGraphToRowMajorUnitWeightAuctionInput input) =
      AppliedModelingLib.Complexity.unaryIndexEncode input.1 ++
        rowMajorOrderedIncidenceBitStream input := by
  rcases input with ⟨n, adjacency⟩
  change AppliedModelingLib.Complexity.unaryIndexEncode n ++
      List.ofFn (rowMajorOrderedIncidenceTableMap adjacency) =
    AppliedModelingLib.Complexity.unaryIndexEncode n ++
      rowMajorOrderedIncidenceBitStream ⟨n, adjacency⟩
  have htail : List.ofFn (rowMajorOrderedIncidenceTableMap adjacency) =
      rowMajorOrderedIncidenceBitStream ⟨n, adjacency⟩ := by
    rw [List.ofFn_mul]
    change (List.ofFn fun v : Fin n =>
      List.ofFn fun j : Fin (n * n) =>
        rowMajorOrderedIncidenceTableMap adjacency
          ⟨v.val * (n * n) + j.val,
            (Nat.add_lt_add_left j.isLt _).trans_eq (by
              exact Nat.succ_mul _ _ |>.symm) |>.trans_le
              (Nat.mul_le_mul_right _ v.isLt)⟩).flatten = _
    unfold rowMajorOrderedIncidenceBitStream
    congr 1
    rw [List.ofFn_inj]
    funext v
    rw [List.ofFn_mul]
    congr 1
    rw [List.ofFn_inj]
    funext u
    rw [List.ofFn_inj]
    funext w
    have huw : u.val * n + w.val < n * n :=
      (Nat.add_lt_add_left w.isLt _).trans_eq (by
        exact Nat.succ_mul _ _ |>.symm) |>.trans_le
        (Nat.mul_le_mul_right _ u.isLt)
    have hindex : (⟨v.val * (n * n) + (u.val * n + w.val),
        (Nat.add_lt_add_left huw _).trans_eq (by
          exact Nat.succ_mul _ _ |>.symm) |>.trans_le
          (Nat.mul_le_mul_right _ v.isLt)⟩ :
        Fin (n * (n * n))) = rowMajorTripleEquiv n (v, (u, w)) := by
      apply Fin.ext
      simp [rowMajorTripleEquiv, rowMajorPairEquiv, finProdFinEquiv]
      ac_rfl
    rw [hindex]
    unfold rowMajorOrderedIncidenceTableMap
    rw [(rowMajorTripleEquiv n).symm_apply_apply]
  rw [htail]

@[simp] theorem rowMajorOrderedIncidenceTableMap_apply
    {n : Nat} (adjacency : Fin (n * n) → Bool)
    (v u w : Fin n) :
    rowMajorOrderedIncidenceTableMap adjacency
        (rowMajorTripleEquiv n (v, (u, w))) =
      (adjacency (rowMajorPairEquiv n (u, w)) &&
        (decide (v = u) || decide (v = w))) := by
  unfold rowMajorOrderedIncidenceTableMap
  rw [(rowMajorTripleEquiv n).symm_apply_apply]

@[simp] theorem uniformGraphToRowMajorUnitWeightAuctionInput_apply
    (input : UniformGraphInput) (v u w : Fin input.1) :
    (uniformGraphToRowMajorUnitWeightAuctionInput input).2
        (rowMajorTripleEquiv input.1 (v, (u, w))) =
      (input.2 (rowMajorPairEquiv input.1 (u, w)) &&
        (decide (v = u) || decide (v = w))) := by
  exact rowMajorOrderedIncidenceTableMap_apply input.2 v u w

/-- The finite row requested by a bidder in the row-major unit-weight target. -/
def rowMajorUnitWeightAuctionRow
    {n : Nat} (table : Fin (n * (n * n)) → Bool) (v : Fin n) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p =>
    table (rowMajorTripleEquiv n (v, p)) = true)

/-- Feasibility of a selected bidder set in the row-major unit-weight target. -/
def rowMajorUnitWeightAuctionFeasible
    {n : Nat} (table : Fin (n * (n * n)) → Bool)
    (selected : Finset (Fin n)) : Prop :=
  ∀ ⦃u v : Fin n⦄, u ∈ selected → v ∈ selected → u ≠ v →
    Disjoint (rowMajorUnitWeightAuctionRow table u)
      (rowMajorUnitWeightAuctionRow table v)

@[simp] theorem mem_rowMajorUnitWeightAuctionRow_iff
    {n : Nat} (table : Fin (n * (n * n)) → Bool)
    (v : Fin n) (p : Fin n × Fin n) :
    p ∈ rowMajorUnitWeightAuctionRow table v ↔
      table (rowMajorTripleEquiv n (v, p)) = true := by
  simp [rowMajorUnitWeightAuctionRow]

@[simp] theorem mem_rowMajorUnitWeightAuctionRow_map_iff
    (input : UniformGraphInput) (v : Fin input.1) (p : Fin input.1 × Fin input.1) :
    p ∈ rowMajorUnitWeightAuctionRow
        (uniformGraphToRowMajorUnitWeightAuctionInput input).2 v ↔
      input.2 (rowMajorPairEquiv input.1 p) = true ∧
        (v = p.1 ∨ v = p.2) := by
  rcases input with ⟨n, adjacency⟩
  change p ∈ rowMajorUnitWeightAuctionRow
      (rowMajorOrderedIncidenceTableMap adjacency) v ↔
    adjacency (rowMajorPairEquiv n p) = true ∧ (v = p.1 ∨ v = p.2)
  rw [mem_rowMajorUnitWeightAuctionRow_iff]
  rw [rowMajorOrderedIncidenceTableMap_apply adjacency v p.1 p.2]
  simp

/-- Symmetry in the concrete row-major binary representation. -/
def rowMajorGraphInputSymmetric (input : UniformGraphInput) : Prop :=
  ∀ v w, input.2 (rowMajorPairEquiv input.1 (v, w)) =
    input.2 (rowMajorPairEquiv input.1 (w, v))

/-- Loop-freeness in the concrete row-major binary representation. -/
def rowMajorGraphInputLoopFree (input : UniformGraphInput) : Prop :=
  ∀ v, input.2 (rowMajorPairEquiv input.1 (v, v)) = false

/-- The finite simple graph represented by a row-major Boolean adjacency table. -/
def rowMajorGraphInputSimpleGraph (input : UniformGraphInput) :
    SimpleGraph (Fin input.1) :=
  SimpleGraph.fromRel (fun v w =>
    input.2 (rowMajorPairEquiv input.1 (v, w)) = true)

theorem rowMajorGraphInputSimpleGraph_adj_iff
    (input : UniformGraphInput)
    (hsymm : rowMajorGraphInputSymmetric input)
    (hloop : rowMajorGraphInputLoopFree input)
    (v w : Fin input.1) :
    (rowMajorGraphInputSimpleGraph input).Adj v w ↔
      input.2 (rowMajorPairEquiv input.1 (v, w)) = true := by
  by_cases hvw : v = w
  · subst w
    simp only [rowMajorGraphInputSimpleGraph, SimpleGraph.fromRel_adj]
    rw [hloop v]
    simp
  · simp only [rowMajorGraphInputSimpleGraph, SimpleGraph.fromRel_adj]
    rw [and_iff_right hvw]
    constructor
    · intro h
      rcases h with h | h
      · exact h
      · rw [hsymm] at h
        exact h
    · intro h
      exact Or.inl h

/-- The direct row-major incidence construction preserves exactly the
graph-independent selections required by the source reduction. -/
theorem rowMajorGraphToAuction_feasible_iff_graphIndependent
    (input : UniformGraphInput)
    (hsymm : rowMajorGraphInputSymmetric input)
    (hloop : rowMajorGraphInputLoopFree input)
    (selected : Finset (Fin input.1)) :
    rowMajorUnitWeightAuctionFeasible
        (uniformGraphToRowMajorUnitWeightAuctionInput input).2 selected ↔
      AppliedModelingLib.Auction.GraphIndependentSelection
        (rowMajorGraphInputSimpleGraph input) selected := by
  constructor
  · intro hfeasible u v hu hv huv hadj
    have hdisjoint := hfeasible hu hv huv
    have hmem_u : (u, v) ∈ rowMajorUnitWeightAuctionRow
        (uniformGraphToRowMajorUnitWeightAuctionInput input).2 u := by
      rw [mem_rowMajorUnitWeightAuctionRow_map_iff]
      refine ⟨?_, Or.inl rfl⟩
      rw [← rowMajorGraphInputSimpleGraph_adj_iff input hsymm hloop u v]
      exact hadj
    have hmem_v : (u, v) ∈ rowMajorUnitWeightAuctionRow
        (uniformGraphToRowMajorUnitWeightAuctionInput input).2 v := by
      rw [mem_rowMajorUnitWeightAuctionRow_map_iff]
      refine ⟨?_, Or.inr rfl⟩
      rw [← rowMajorGraphInputSimpleGraph_adj_iff input hsymm hloop u v]
      exact hadj
    exact (Finset.disjoint_left.mp hdisjoint) hmem_u hmem_v
  · intro hind u v hu hv huv
    apply Finset.disjoint_left.mpr
    intro p hpu hpv
    have hu' := (mem_rowMajorUnitWeightAuctionRow_map_iff input u p).mp hpu
    have hv' := (mem_rowMajorUnitWeightAuctionRow_map_iff input v p).mp hpv
    have hswap : input.2 (rowMajorPairEquiv input.1 (p.1, p.2)) =
        input.2 (rowMajorPairEquiv input.1 (p.2, p.1)) := hsymm p.1 p.2
    have hadj : (rowMajorGraphInputSimpleGraph input).Adj u v := by
      rw [rowMajorGraphInputSimpleGraph_adj_iff input hsymm hloop]
      rcases hu'.2 with hpu | hpu <;> rcases hv'.2 with hpv | hpv
      · exact False.elim (huv (hpu.trans hpv.symm))
      · simpa [hpu, hpv] using hu'.1
      · have h := hu'.1
        change input.2 (rowMajorPairEquiv input.1 (p.1, p.2)) = true at h
        rw [hpu, hpv, ← hswap]
        exact h
      · exact False.elim (huv (hpu.trans hpv.symm))
    exact (hind hu hv huv) hadj

end LOS02CombinatorialAuctions
