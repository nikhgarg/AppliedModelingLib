import AppliedModelingLib.Algorithms.Complexity.FiniteEncoding
import Mathlib.Data.Nat.Pairing

/-!
# Streamed edge-list encodings for the Theorem 6.1 reduction

The printed reduction constructs one unit-valued bid for every graph vertex and
gives that bid precisely its incident graph edges.  A dense `n^3` incidence
table is useful for finite semantic reasoning but is not the only faithful
machine representation.  This module supplies the source-nearer streamed
representation: an input is a unary vertex count followed by unary endpoint
pairs, and the target is the same vertex count followed by incidence triples.

The encodings are self-delimiting because every natural number is represented
by a terminated unary word.  The actual TM2 transducer is developed separately;
the results here establish the exact input and output bit streams it must
realize.
-/

namespace LOS02CombinatorialAuctions

open AppliedModelingLib.Complexity

/-- Concatenate terminated unary words for a finite list of natural numbers. -/
def unaryNatListEncode (entries : List Nat) : List Bool :=
  entries.flatMap unaryIndexEncode

@[simp] theorem unaryNatListEncode_nil : unaryNatListEncode [] = [] :=
  rfl

@[simp] theorem unaryNatListEncode_cons (entry : Nat) (entries : List Nat) :
    unaryNatListEncode (entry :: entries) =
      unaryIndexEncode entry ++ unaryNatListEncode entries := by
  rfl

/-- The unary stream length is the sum of the terminated-word lengths. -/
theorem unaryNatListEncode_length (entries : List Nat) :
    (unaryNatListEncode entries).length = (entries.map fun entry => entry + 1).sum := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp [unaryNatListEncode, unaryIndexEncode_length]

/-- Decode the first terminated unary word and retain the unconsumed suffix. -/
def unaryIndexDecodePrefix : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: tail => some (0, tail)
  | true :: tail => do
    let (index, suffix) ← unaryIndexDecodePrefix tail
    return (index + 1, suffix)

@[simp] theorem unaryIndexDecodePrefix_encode_append (index : Nat) (tail : List Bool) :
    unaryIndexDecodePrefix (unaryIndexEncode index ++ tail) = some (index, tail) := by
  induction index with
  | zero => simp [unaryIndexEncode, unaryIndexDecodePrefix]
  | succ index ih =>
      simp [unaryIndexEncode, unaryIndexDecodePrefix, ih]

theorem unaryNatListEncode_injective : Function.Injective unaryNatListEncode := by
  intro entries entries' hcode
  induction entries generalizing entries' with
  | nil =>
      cases entries' with
      | nil => rfl
      | cons entry entries' =>
          exfalso
          have hnonempty : unaryNatListEncode (entry :: entries') ≠ [] := by
            intro hempty
            have hlength := congrArg List.length hempty
            simp [unaryNatListEncode, unaryIndexEncode_length] at hlength
          exact hnonempty hcode.symm
  | cons entry entries ih =>
      cases entries' with
      | nil =>
          exfalso
          have hnonempty : unaryNatListEncode (entry :: entries) ≠ [] := by
            intro hempty
            have hlength := congrArg List.length hempty
            simp [unaryNatListEncode, unaryIndexEncode_length] at hlength
          exact hnonempty hcode
      | cons entry' entries' =>
          have hprefix := congrArg unaryIndexDecodePrefix hcode
          simp only [unaryNatListEncode_cons,
            unaryIndexDecodePrefix_encode_append] at hprefix
          have hentry : entry = entry' := congrArg Prod.fst (Option.some.inj hprefix)
          have htail : unaryNatListEncode entries = unaryNatListEncode entries' :=
            congrArg Prod.snd (Option.some.inj hprefix)
          subst entry'
          exact congrArg (List.cons entry) (ih htail)

/-- Flatten an ordered edge list into the two endpoint indices of each edge. -/
def unaryEdgeListWords {n : Nat} (edges : List (Fin n × Fin n)) : List Nat :=
  edges.flatMap fun edge => [edge.1.val, edge.2.val]

theorem unaryEdgeListWords_injective {n : Nat} :
    Function.Injective (unaryEdgeListWords (n := n)) := by
  intro edges edges' hwords
  induction edges generalizing edges' with
  | nil =>
      cases edges' with
      | nil => rfl
      | cons edge edges' =>
          simp [unaryEdgeListWords] at hwords
  | cons edge edges ih =>
      cases edges' with
      | nil =>
          simp [unaryEdgeListWords] at hwords
      | cons edge' edges' =>
          simp only [unaryEdgeListWords, List.flatMap_cons, List.cons_append] at hwords
          have hfirst : edge.1.val = edge'.1.val := by
            simpa using congrArg List.head! hwords
          have hsecond : edge.2.val = edge'.2.val := by
            simpa [hfirst] using congrArg (fun values => values[1]!) hwords
          have htail : unaryEdgeListWords edges = unaryEdgeListWords edges' := by
            simpa [hfirst, hsecond] using congrArg (fun values => values.drop 2) hwords
          have hedge : edge = edge' := by
            apply Prod.ext <;> apply Fin.ext
            · exact hfirst
            · exact hsecond
          subst edge'
          exact congrArg (List.cons edge) (ih htail)

/-- A variable-size edge-list graph, with each endpoint represented by a finite
vertex index. Edge order and repetitions are retained in the binary carrier;
the later semantic bridge can impose simple-graph conditions where needed. -/
abbrev UnaryEdgeListGraphInput := Sigma fun n : Nat => List (Fin n × Fin n)

/-- The exact machine input stream: a unary vertex count, followed by the unary
endpoint words of each ordered edge record. -/
def unaryEdgeListGraphInputCode (input : UnaryEdgeListGraphInput) : List Bool :=
  unaryIndexEncode input.1 ++ unaryNatListEncode (unaryEdgeListWords input.2)

theorem unaryEdgeListGraphInputCode_injective :
    Function.Injective unaryEdgeListGraphInputCode := by
  rintro ⟨n, edges⟩ ⟨n', edges'⟩ hcode
  have hprefix := congrArg unaryIndexDecodePrefix hcode
  simp only [unaryEdgeListGraphInputCode,
    unaryIndexDecodePrefix_encode_append] at hprefix
  have hn : n = n' := congrArg Prod.fst (Option.some.inj hprefix)
  subst n'
  have hwords : unaryEdgeListWords edges = unaryEdgeListWords edges' := by
    apply unaryNatListEncode_injective
    exact congrArg Prod.snd (Option.some.inj hprefix)
  have hedges := unaryEdgeListWords_injective hwords
  subst edges'
  rfl

/-- A binary encoding for variable-size unary edge-list graph inputs. -/
noncomputable def unaryEdgeListGraphInputEncoding :
    BinaryEncoding UnaryEdgeListGraphInput :=
  encodingOfInjectiveList unaryEdgeListGraphInputCode
    unaryEdgeListGraphInputCode_injective

/-- A streamed incidence record `(v, (u, w))` says that bidder `v` requests
the good represented by the ordered endpoint pair `(u, w)`. The semantic
target will quotient or otherwise identify duplicate endpoint representations
when it forms graph edges. -/
abbrev UnaryEdgeListIncidence (n : Nat) := Fin n × (Fin n × Fin n)

/-- Flatten streamed incidence records into their three unary endpoint words. -/
def unaryIncidenceListWords {n : Nat}
    (incidences : List (UnaryEdgeListIncidence n)) : List Nat :=
  incidences.flatMap fun incidence =>
    [incidence.1.val, incidence.2.1.val, incidence.2.2.val]

theorem unaryIncidenceListWords_append {n : Nat}
    (incidences incidences' : List (UnaryEdgeListIncidence n)) :
    unaryIncidenceListWords (incidences ++ incidences') =
      unaryIncidenceListWords incidences ++ unaryIncidenceListWords incidences' := by
  simp [unaryIncidenceListWords]

theorem unaryIncidenceListWords_injective {n : Nat} :
    Function.Injective (unaryIncidenceListWords (n := n)) := by
  intro incidences incidences' hwords
  induction incidences generalizing incidences' with
  | nil =>
      cases incidences' with
      | nil => rfl
      | cons incidence incidences' =>
          simp [unaryIncidenceListWords] at hwords
  | cons incidence incidences ih =>
      cases incidences' with
      | nil =>
          simp [unaryIncidenceListWords] at hwords
      | cons incidence' incidences' =>
          simp only [unaryIncidenceListWords, List.flatMap_cons, List.cons_append] at hwords
          have hfirst : incidence.1.val = incidence'.1.val := by
            simpa using congrArg List.head! hwords
          have hsecond : incidence.2.1.val = incidence'.2.1.val := by
            simpa [hfirst] using congrArg (fun values => values[1]!) hwords
          have hthird : incidence.2.2.val = incidence'.2.2.val := by
            simpa [hfirst, hsecond] using congrArg (fun values => values[2]!) hwords
          have htail : unaryIncidenceListWords incidences =
              unaryIncidenceListWords incidences' := by
            simpa [hfirst, hsecond, hthird] using
              congrArg (fun values => values.drop 3) hwords
          have hincidence : incidence = incidence' := by
            apply Prod.ext
            · apply Fin.ext
              exact hfirst
            · apply Prod.ext <;> apply Fin.ext
              · exact hsecond
              · exact hthird
          subst incidence'
          exact congrArg (List.cons incidence) (ih htail)

/-- The streamed unit-weight auction target: a vertex count and the incidence
records that list every requested graph edge under each bidder endpoint. -/
abbrev UnaryEdgeListAuctionInput :=
  Sigma fun n : Nat => List (UnaryEdgeListIncidence n)

/-- The exact machine output stream: the vertex count followed by unary
bidder/endpoint incidence triples. -/
def unaryEdgeListAuctionInputCode (input : UnaryEdgeListAuctionInput) : List Bool :=
  unaryIndexEncode input.1 ++ unaryNatListEncode (unaryIncidenceListWords input.2)

theorem unaryEdgeListAuctionInputCode_injective :
    Function.Injective unaryEdgeListAuctionInputCode := by
  rintro ⟨n, incidences⟩ ⟨n', incidences'⟩ hcode
  have hprefix := congrArg unaryIndexDecodePrefix hcode
  simp only [unaryEdgeListAuctionInputCode,
    unaryIndexDecodePrefix_encode_append] at hprefix
  have hn : n = n' := congrArg Prod.fst (Option.some.inj hprefix)
  subst n'
  have hwords : unaryIncidenceListWords incidences =
      unaryIncidenceListWords incidences' := by
    apply unaryNatListEncode_injective
    exact congrArg Prod.snd (Option.some.inj hprefix)
  have hincidences := unaryIncidenceListWords_injective hwords
  subst incidences'
  rfl

/-- A binary encoding for variable-size streamed unit-weight auction inputs. -/
noncomputable def unaryEdgeListAuctionInputEncoding :
    BinaryEncoding UnaryEdgeListAuctionInput :=
  encodingOfInjectiveList unaryEdgeListAuctionInputCode
    unaryEdgeListAuctionInputCode_injective

/-! A decision threshold can share the opaque unary header used by the native
transducer.  `Nat.pair` is injective, so the header records both its threshold
and vertex-count components even though the machine only copies the header. -/

/-- A streamed graph instance together with its natural decision threshold. -/
abbrev UnaryEdgeListGraphThresholdInput := Nat × UnaryEdgeListGraphInput

/-- The opaque header shared by the source and target threshold encodings. -/
def unaryEdgeListThresholdHeader (threshold vertexCount : Nat) : Nat :=
  Nat.pair threshold vertexCount

/-- The threshold and vertex-count pair is carried in one self-delimiting
unary header, followed by the edge endpoint stream. -/
def unaryEdgeListGraphThresholdInputCode
    (input : UnaryEdgeListGraphThresholdInput) : List Bool :=
  unaryIndexEncode (unaryEdgeListThresholdHeader input.1 input.2.1) ++
    unaryNatListEncode (unaryEdgeListWords input.2.2)

theorem unaryEdgeListGraphThresholdInputCode_injective :
    Function.Injective unaryEdgeListGraphThresholdInputCode := by
  rintro ⟨threshold, ⟨n, edges⟩⟩ ⟨threshold', ⟨n', edges'⟩⟩ hcode
  have hprefix := congrArg unaryIndexDecodePrefix hcode
  simp only [unaryEdgeListGraphThresholdInputCode,
    unaryIndexDecodePrefix_encode_append] at hprefix
  have hheader : Nat.pair threshold n = Nat.pair threshold' n' :=
    congrArg Prod.fst (Option.some.inj hprefix)
  have hpair : (threshold, n) = (threshold', n') := by
    simpa only [Nat.unpair_pair] using congrArg Nat.unpair hheader
  have hthreshold : threshold = threshold' := congrArg Prod.fst hpair
  have hn : n = n' := congrArg Prod.snd hpair
  subst threshold'
  subst n'
  have hwords : unaryEdgeListWords edges = unaryEdgeListWords edges' := by
    apply unaryNatListEncode_injective
    exact congrArg Prod.snd (Option.some.inj hprefix)
  have hedges := unaryEdgeListWords_injective hwords
  subst edges'
  rfl

/-- A binary encoding for variable-threshold streamed graph decision inputs. -/
noncomputable def unaryEdgeListGraphThresholdInputEncoding :
    BinaryEncoding UnaryEdgeListGraphThresholdInput :=
  encodingOfInjectiveList unaryEdgeListGraphThresholdInputCode
    unaryEdgeListGraphThresholdInputCode_injective

/-- A streamed auction instance together with the preserved natural decision
threshold. -/
abbrev UnaryEdgeListAuctionThresholdInput := Nat × UnaryEdgeListAuctionInput

/-- The target uses the same opaque threshold/vertex-count header. -/
def unaryEdgeListAuctionThresholdInputCode
    (input : UnaryEdgeListAuctionThresholdInput) : List Bool :=
  unaryIndexEncode (unaryEdgeListThresholdHeader input.1 input.2.1) ++
    unaryNatListEncode (unaryIncidenceListWords input.2.2)

theorem unaryEdgeListAuctionThresholdInputCode_injective :
    Function.Injective unaryEdgeListAuctionThresholdInputCode := by
  rintro ⟨threshold, ⟨n, incidences⟩⟩ ⟨threshold', ⟨n', incidences'⟩⟩ hcode
  have hprefix := congrArg unaryIndexDecodePrefix hcode
  simp only [unaryEdgeListAuctionThresholdInputCode,
    unaryIndexDecodePrefix_encode_append] at hprefix
  have hheader : Nat.pair threshold n = Nat.pair threshold' n' :=
    congrArg Prod.fst (Option.some.inj hprefix)
  have hpair : (threshold, n) = (threshold', n') := by
    simpa only [Nat.unpair_pair] using congrArg Nat.unpair hheader
  have hthreshold : threshold = threshold' := congrArg Prod.fst hpair
  have hn : n = n' := congrArg Prod.snd hpair
  subst threshold'
  subst n'
  have hwords : unaryIncidenceListWords incidences =
      unaryIncidenceListWords incidences' := by
    apply unaryNatListEncode_injective
    exact congrArg Prod.snd (Option.some.inj hprefix)
  have hincidences := unaryIncidenceListWords_injective hwords
  subst incidences'
  rfl

/-- A binary encoding for variable-threshold streamed auction decision inputs. -/
noncomputable def unaryEdgeListAuctionThresholdInputEncoding :
    BinaryEncoding UnaryEdgeListAuctionThresholdInput :=
  encodingOfInjectiveList unaryEdgeListAuctionThresholdInputCode
    unaryEdgeListAuctionThresholdInputCode_injective

/-- The two incidence records generated by the source construction for one
ordered graph-edge occurrence. -/
def edgeIncidenceRecords {n : Nat} (edge : Fin n × Fin n) :
    List (UnaryEdgeListIncidence n) :=
  [(edge.1, (edge.1, edge.2)), (edge.2, (edge.1, edge.2))]

/-- Apply the source's direct incidence construction to every encoded edge. -/
def unaryEdgeListGraphToAuction (input : UnaryEdgeListGraphInput) :
    UnaryEdgeListAuctionInput :=
  ⟨input.1, input.2.flatMap edgeIncidenceRecords⟩

/-- The decision reduction preserves the threshold while applying the native
edge-list-to-incidence map to the graph payload. -/
def unaryEdgeListGraphThresholdToAuction
    (input : UnaryEdgeListGraphThresholdInput) :
    UnaryEdgeListAuctionThresholdInput :=
  (input.1, unaryEdgeListGraphToAuction input.2)

/-- The natural-number words emitted by the streamed incidence construction.
Each input edge contributes the two triples `(u,u,w)` and `(w,u,w)`. -/
def unaryEdgeIncidenceOutputWords {n : Nat} (edges : List (Fin n × Fin n)) : List Nat :=
  edges.flatMap fun edge =>
    [edge.1.val, edge.1.val, edge.2.val, edge.2.val, edge.1.val, edge.2.val]

theorem unaryIncidenceListWords_edgeIncidenceRecords {n : Nat}
    (edge : Fin n × Fin n) :
    unaryIncidenceListWords (edgeIncidenceRecords edge) =
      [edge.1.val, edge.1.val, edge.2.val, edge.2.val, edge.1.val, edge.2.val] := by
  rfl

theorem unaryEdgeListGraphToAuction_words (input : UnaryEdgeListGraphInput) :
    unaryIncidenceListWords (unaryEdgeListGraphToAuction input).2 =
      unaryEdgeIncidenceOutputWords input.2 := by
  rcases input with ⟨n, edges⟩
  change unaryIncidenceListWords (edges.flatMap edgeIncidenceRecords) =
    unaryEdgeIncidenceOutputWords edges
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      rw [List.flatMap_cons, unaryIncidenceListWords_append,
        unaryIncidenceListWords_edgeIncidenceRecords]
      simp [unaryEdgeIncidenceOutputWords, ih]

theorem unaryEdgeListAuctionInputCode_map (input : UnaryEdgeListGraphInput) :
    unaryEdgeListAuctionInputCode (unaryEdgeListGraphToAuction input) =
      unaryIndexEncode input.1 ++
        unaryNatListEncode (unaryEdgeIncidenceOutputWords input.2) := by
  rcases input with ⟨n, edges⟩
  change unaryIndexEncode n ++ unaryNatListEncode
      (unaryIncidenceListWords (edges.flatMap edgeIncidenceRecords)) =
    unaryIndexEncode n ++ unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)
  have hwords : unaryIncidenceListWords (edges.flatMap edgeIncidenceRecords) =
      unaryEdgeIncidenceOutputWords edges := by
    simpa [unaryEdgeListGraphToAuction] using
      (unaryEdgeListGraphToAuction_words ⟨n, edges⟩)
  exact congrArg (fun words => unaryIndexEncode n ++ unaryNatListEncode words) hwords

theorem unaryEdgeListAuctionThresholdInputCode_map
    (input : UnaryEdgeListGraphThresholdInput) :
    unaryEdgeListAuctionThresholdInputCode
      (unaryEdgeListGraphThresholdToAuction input) =
      unaryIndexEncode (unaryEdgeListThresholdHeader input.1 input.2.1) ++
        unaryNatListEncode (unaryEdgeIncidenceOutputWords input.2.2) := by
  rcases input with ⟨threshold, ⟨n, edges⟩⟩
  change unaryIndexEncode (unaryEdgeListThresholdHeader threshold n) ++
      unaryNatListEncode
        (unaryIncidenceListWords (edges.flatMap edgeIncidenceRecords)) =
    unaryIndexEncode (unaryEdgeListThresholdHeader threshold n) ++
      unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)
  have hwords := unaryEdgeListGraphToAuction_words ⟨n, edges⟩
  change unaryIncidenceListWords (edges.flatMap edgeIncidenceRecords) =
    unaryEdgeIncidenceOutputWords edges at hwords
  exact congrArg
    (fun words => unaryIndexEncode (unaryEdgeListThresholdHeader threshold n) ++
      unaryNatListEncode words) hwords

end LOS02CombinatorialAuctions
