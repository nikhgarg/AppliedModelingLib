import AppliedModelingLib.Algorithms.Complexity.Encoding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin

/-! Concrete finite-index encodings for machine-level complexity models. -/

namespace AppliedModelingLib
namespace Complexity

universe u

/-- `List.ofFn` is injective on functions with a fixed finite domain. -/
theorem listOfFn_injective {n : Nat} {α : Type u} :
    Function.Injective (@List.ofFn α n) := by
  intro f g h
  funext i
  have he := congrArg (fun xs => xs[i.val]?) h
  simp [i.isLt] at he
  exact he

noncomputable def encodingOfInjectiveList
    {α : Type u} (encode : α → List Bool) (hinj : Function.Injective encode) :
    BinaryEncoding α where
  encode := encode
  decode := by
    classical
    exact fun code =>
      if h : ∃ x, encode x = code then some (Classical.choose h) else none
  decode_encode := by
    intro x
    have h : ∃ y, encode y = encode x := ⟨x, rfl⟩
    simp only [dif_pos h]
    congr 1
    exact hinj (Classical.choose_spec h)

/-! This constructor is public so paper-local encodings can use a
    self-delimiting header followed by a finite Boolean table without
    duplicating an arbitrary decoder implementation.  Injectivity remains the
    explicit machine-representation obligation. -/

theorem encodingOfInjectiveList_encode_injective
    {α : Type u} (encode : α → List Bool)
    (hinj : Function.Injective encode) :
    Function.Injective (encodingOfInjectiveList encode hinj).encode := by
  exact hinj

/-! A finite Boolean table is a source-faithful representation for an
incidence row once the carrier has been indexed by `Fin n`. -/
noncomputable def boolTableEncoding (n : Nat) :
    BinaryEncoding (Fin n → Bool) :=
  encodingOfInjectiveList List.ofFn listOfFn_injective

@[simp] theorem boolTableEncoding_size (n : Nat) (row : Fin n → Bool) :
    (boolTableEncoding n).size row = n := by
  change (List.ofFn row).length = n
  simp

/-- Turn a finite set of indexed goods into its Boolean incidence row. -/
def finsetToBoolRow {n : Nat} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ s)

/-- Recover the finite set represented by a Boolean incidence row. -/
def boolRowToFinset {n : Nat} (row : Fin n → Bool) : Finset (Fin n) :=
  Finset.filter (fun i => row i = true) Finset.univ

@[simp] theorem boolRowToFinset_finsetToBoolRow {n : Nat}
    (s : Finset (Fin n)) : boolRowToFinset (finsetToBoolRow s) = s := by
  ext i
  simp [boolRowToFinset, finsetToBoolRow]

/-- Encode a finite set on an arbitrary finite carrier by its canonical index. -/
noncomputable def finiteSetToBoolRow {α : Type u} [Fintype α] (s : Finset α) :
    Fin (Fintype.card α) → Bool :=
  by
    classical
    exact fun i => decide ((Fintype.equivFin α).symm i ∈ s)

/-- Decode an arbitrary finite-carrier incidence row. -/
noncomputable def boolRowToFiniteSet {α : Type u} [Fintype α]
    (row : Fin (Fintype.card α) → Bool) : Finset α :=
  (boolRowToFinset row).map (Fintype.equivFin α).symm.toEmbedding

@[simp] theorem boolRowToFiniteSet_finiteSetToBoolRow
    {α : Type u} [Fintype α] (s : Finset α) :
    boolRowToFiniteSet (finiteSetToBoolRow s) = s := by
  classical
  ext x
  simp [boolRowToFiniteSet, finiteSetToBoolRow, boolRowToFinset]

/-- A verified binary encoding of finite subsets of a finite carrier. -/
noncomputable def finiteSetEncoding (α : Type u) [Fintype α] :
    BinaryEncoding (Finset α) where
  encode := fun s => (boolTableEncoding (Fintype.card α)).encode
    (finiteSetToBoolRow s)
  decode := fun code =>
    ((boolTableEncoding (Fintype.card α)).decode code).map boolRowToFiniteSet
  decode_encode := by
    intro s
    rw [(boolTableEncoding (Fintype.card α)).decode_encode]
    simp [boolRowToFiniteSet_finiteSetToBoolRow]

@[simp] theorem finiteSetEncoding_size (α : Type u) [Fintype α]
    (s : Finset α) :
    (finiteSetEncoding α).size s = Fintype.card α := by
  change (boolTableEncoding (Fintype.card α)).size (finiteSetToBoolRow s) = _
  exact boolTableEncoding_size _ _

/-- Unary binary code for a natural index, terminated by `false`. -/
def unaryIndexEncode : Nat → List Bool
  | 0 => [false]
  | k + 1 => true :: unaryIndexEncode k

/-- Decode the prefix before the first terminating `false`. -/
def unaryIndexDecode : List Bool → Option Nat
  | [] => none
  | false :: _ => some 0
  | true :: xs => (unaryIndexDecode xs).map Nat.succ

@[simp] theorem unaryIndexEncode_length (k : Nat) :
    (unaryIndexEncode k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [unaryIndexEncode, ih]

theorem unaryIndexDecode_encode (k : Nat) :
    unaryIndexDecode (unaryIndexEncode k) = some k := by
  induction k with
  | zero => simp [unaryIndexEncode, unaryIndexDecode]
  | succ k ih =>
      simp [unaryIndexEncode, unaryIndexDecode, ih]

theorem unaryIndexDecode_encode_append (k : Nat) (tail : List Bool) :
    unaryIndexDecode (unaryIndexEncode k ++ tail) = some k := by
  induction k with
  | zero => simp [unaryIndexEncode, unaryIndexDecode]
  | succ k ih =>
      simp [unaryIndexEncode, unaryIndexDecode, ih]

/-- A verified unary encoding of nonnegative integer weights. -/
def unaryNatEncoding : BinaryEncoding Nat where
  encode := unaryIndexEncode
  decode := unaryIndexDecode
  decode_encode := by
    intro k
    exact unaryIndexDecode_encode k

@[simp] theorem unaryNatEncoding_size (k : Nat) :
    unaryNatEncoding.size k = k + 1 := by
  simp [BinaryEncoding.size, unaryNatEncoding]

/-- Decode a terminated unary index when it lies in `Fin n`. -/
def unaryFinDecode (n : Nat) : List Bool → Option (Fin n) :=
  fun code => (unaryIndexDecode code).bind fun k =>
    if h : k < n then some ⟨k, h⟩ else none

/-- A verified binary encoding of the finite index type `Fin n`. -/
def unaryFinEncoding (n : Nat) : BinaryEncoding (Fin n) where
  encode := fun i => unaryIndexEncode i.val
  decode := unaryFinDecode n
  decode_encode := by
    intro i
    simp [unaryFinDecode, unaryIndexDecode_encode, i.isLt]

@[simp] theorem unaryFinEncoding_size (n : Nat) (i : Fin n) :
    (unaryFinEncoding n).size i = i.val + 1 := by
  simp [BinaryEncoding.size, unaryFinEncoding]

/-- Encode an arbitrary finite carrier through its canonical `Fin` index. -/
noncomputable def finiteTypeEncoding (α : Type u) [Fintype α] :
    BinaryEncoding α where
  encode := fun x => unaryIndexEncode (Fintype.equivFin α x).val
  decode := fun code =>
    (unaryFinDecode (Fintype.card α) code).map (Fintype.equivFin α).symm
  decode_encode := by
    intro x
    simp [unaryFinDecode, unaryIndexDecode_encode, (Fintype.equivFin α x).isLt]

@[simp] theorem finiteTypeEncoding_size (α : Type u) [Fintype α] (x : α) :
    (finiteTypeEncoding α).size x = (Fintype.equivFin α x).val + 1 := by
  simp [BinaryEncoding.size, finiteTypeEncoding]

end Complexity
end AppliedModelingLib
