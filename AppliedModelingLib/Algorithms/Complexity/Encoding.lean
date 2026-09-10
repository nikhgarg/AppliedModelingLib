import AppliedModelingLib.Algorithms.Complexity.Classes

/-!
# Encoding-aware computational maps

The abstract complexity classes in `Classes.lean` intentionally leave the
machine model external.  This module supplies the smallest reusable bridge for
paper formalizations that need to make that boundary explicit: a total binary
encoding with a decoding section, a step-counted map, and separate polynomial
bounds for work and output length.

This is original library infrastructure; no external Lean code is copied.
It does not identify a particular RAM/Turing-machine implementation or prove
NP/ZPP facts.  Those remain model-specific obligations.
-/

namespace AppliedModelingLib
namespace Complexity

universe u v

/-- A total binary code with a partial decoder and a correctness section. -/
structure BinaryEncoding (α : Type u) where
  encode : α → List Bool
  decode : List Bool → Option α
  decode_encode : ∀ x, decode (encode x) = some x

namespace BinaryEncoding

variable {α : Type u}

/-- Encoded length is the input-size measure exposed to a machine model. -/
def size (E : BinaryEncoding α) (x : α) : Nat := (E.encode x).length

/-- Any decodable binary encoding is injective. -/
theorem encode_injective (E : BinaryEncoding α) : Function.Injective E.encode := by
  intro x y hxy
  have hdecode : E.decode (E.encode x) = E.decode (E.encode y) := congrArg E.decode hxy
  simpa [E.decode_encode] using hdecode

end BinaryEncoding

/-- The identity binary encoding for already-flattened Boolean tapes.

This is useful when a finite construction has explicitly chosen its machine
word to be a `List Bool`; the decoder is total on such tapes, so the only
encoding obligation is the required round trip. -/
def listBoolEncoding : BinaryEncoding (List Bool) where
  encode := id
  decode := some
  decode_encode := by
    intro code
    rfl

@[simp] theorem listBoolEncoding_size (code : List Bool) :
    listBoolEncoding.size code = code.length := by
  rfl

/-- A natural-valued resource is polynomially bounded in an input size. -/
def PolynomiallyBounded (f : Nat → Nat) : Prop :=
  ∃ c d : Nat, ∀ n, f n ≤ c * (n + 1) ^ d

theorem PolynomiallyBounded.comp {f g : Nat → Nat}
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => g (f n)) := by
  rcases hf with ⟨c₁, d₁, hf⟩
  rcases hg with ⟨c₂, d₂, hg⟩
  refine ⟨c₂ * (c₁ + 1) ^ d₂, d₁ * d₂, ?_⟩
  intro n
  have hpow : 1 ≤ (n + 1) ^ d₁ := by
    exact Nat.one_le_pow d₁ (n + 1) (by omega)
  have hbase : f n + 1 ≤ (c₁ + 1) * (n + 1) ^ d₁ := by
    calc
      f n + 1 ≤ c₁ * (n + 1) ^ d₁ + 1 := Nat.add_le_add_right (hf n) 1
      _ ≤ c₁ * (n + 1) ^ d₁ + (n + 1) ^ d₁ :=
        Nat.add_le_add_left hpow _
      _ = (c₁ + 1) * (n + 1) ^ d₁ := by
        simp [Nat.add_mul]
  calc
    g (f n) ≤ c₂ * (f n + 1) ^ d₂ := hg (f n)
    _ ≤ c₂ * ((c₁ + 1) * (n + 1) ^ d₁) ^ d₂ :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase d₂)
    _ = c₂ * (c₁ + 1) ^ d₂ * (n + 1) ^ (d₁ * d₂) := by
      simp [Nat.mul_pow, Nat.pow_mul, Nat.mul_assoc]

/-!
Polynomial bounds are also closed under pointwise addition.  Keeping this
lemma in the encoding layer lets a concrete machine model combine separate
work counters without introducing a paper-specific arithmetic certificate.
-/

theorem PolynomiallyBounded.add {f g : Nat → Nat}
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n + g n) := by
  rcases hf with ⟨c₁, d₁, hf⟩
  rcases hg with ⟨c₂, d₂, hg⟩
  refine ⟨c₁ + c₂, d₁ + d₂, ?_⟩
  intro n
  let b : Nat := n + 1
  have hb : 1 ≤ b := by
    dsimp [b]
    omega
  have hpow₁ : b ^ d₁ ≤ b ^ (d₁ + d₂) := by
    rw [Nat.pow_add]
    exact Nat.le_mul_of_pos_right _ (Nat.pow_pos hb)
  have hpow₂ : b ^ d₂ ≤ b ^ (d₁ + d₂) := by
    rw [Nat.pow_add]
    have hleft : 1 ≤ b ^ d₁ := Nat.one_le_pow _ _ hb
    exact Nat.le_mul_of_pos_left _ hleft
  calc
    f n + g n ≤ c₁ * b ^ d₁ + c₂ * b ^ d₂ :=
      Nat.add_le_add (hf n) (hg n)
    _ ≤ c₁ * b ^ (d₁ + d₂) + c₂ * b ^ (d₁ + d₂) := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_left c₁ hpow₁)
        (Nat.mul_le_mul_left c₂ hpow₂)
    _ = (c₁ + c₂) * b ^ (d₁ + d₂) := by
      rw [Nat.add_mul]
    _ = (c₁ + c₂) * (n + 1) ^ (d₁ + d₂) := by
      rfl

/-- A concrete costed map between binary encodings.

`steps` is an explicit machine-work counter supplied by the chosen execution
model.  The two polynomial witnesses are kept separate: a runtime bound does
not automatically imply an output-size bound without a model theorem.
-/
structure PolynomialTimeMap
    (α : Type u) (β : Type v)
    (sourceEncoding : BinaryEncoding α)
    (targetEncoding : BinaryEncoding β) where
  map : α → β
  steps : α → Nat
  steps_bound : ∃ c d : Nat, ∀ x,
    steps x ≤ c * (sourceEncoding.size x + 1) ^ d
  output_bound : ∃ c d : Nat, ∀ x,
    targetEncoding.size (map x) ≤ c * (sourceEncoding.size x + 1) ^ d

/-! The encoding-aware map predicate is the concrete counterpart of the
    abstract `PolynomialTime` field in `Classes.lean`.  Keeping it here makes
    the bridge available without choosing a Turing/RAM semantics. -/

def EncodingPolynomialTime
    {α : Type u} {β : Type v}
    (sourceEncoding : BinaryEncoding α)
    (targetEncoding : BinaryEncoding β)
    (f : α → β) : Prop :=
  ∃ P : PolynomialTimeMap α β sourceEncoding targetEncoding, P.map = f

/-- A deterministic decider with an explicit encoded polynomial work bound.

This is the smallest machine-facing semantics needed to distinguish a
correct decision procedure from an abstract `P` membership premise.  The
`steps` field is intentionally supplied by the chosen execution model; this
structure does not identify a Turing-machine instruction set. -/
structure DeterministicPolynomialDecider
    (α : Type u) (sourceEncoding : BinaryEncoding α)
    (language : α → Prop) where
  decide : α → Bool
  correct : ∀ x, decide x = true ↔ language x
  steps : α → Nat
  steps_bound : ∃ c d : Nat, ∀ x,
    steps x ≤ c * (sourceEncoding.size x + 1) ^ d

/-- Encoded deterministic polynomial-time membership. -/
def DeterministicP
    {α : Type u} (sourceEncoding : BinaryEncoding α)
    (language : α → Prop) : Prop :=
  Nonempty (DeterministicPolynomialDecider α sourceEncoding language)

theorem DeterministicPolynomialDecider.deterministicP
    {α : Type u} {E : BinaryEncoding α} {language : α → Prop}
    (D : DeterministicPolynomialDecider α E language) :
    DeterministicP E language :=
  ⟨D⟩

theorem DeterministicPolynomialDecider.correct_iff
    {α : Type u} {E : BinaryEncoding α} {language : α → Prop}
    (D : DeterministicPolynomialDecider α E language) (x : α) :
    D.decide x = true ↔ language x :=
  D.correct x

/-- A certificate verifier with explicit witness-size and verification-work
    bounds.  The verifier cost is polynomial in the combined encoded input and
    witness sizes, matching the usual certificate formulation without fixing a
    particular machine instruction set. -/
structure PolynomialCertificateVerifier
    (α : Type u) (β : Type v)
    (sourceEncoding : BinaryEncoding α)
    (witnessEncoding : BinaryEncoding β)
    (language : α → Prop) where
  verify : α → β → Bool
  correct : ∀ x, language x ↔ ∃ witness, verify x witness = true
  witness_size_bound : ∃ c d : Nat, ∀ x witness,
    verify x witness = true →
      witnessEncoding.size witness ≤ c * (sourceEncoding.size x + 1) ^ d
  steps : α → β → Nat
  steps_bound : ∃ c d : Nat, ∀ x witness,
    steps x witness ≤ c *
      (sourceEncoding.size x + witnessEncoding.size witness + 1) ^ d

/-- Encoded NP membership under the explicit certificate interface. -/
def EncodedNP
    {α : Type u} {β : Type v}
    (sourceEncoding : BinaryEncoding α)
    (witnessEncoding : BinaryEncoding β)
    (language : α → Prop) : Prop :=
  Nonempty (PolynomialCertificateVerifier α β sourceEncoding witnessEncoding language)

/-! Class-valued wrappers for a fixed encoding universe. -/

def EncodedPClass {α : Type u} (sourceEncoding : BinaryEncoding α) :
    Set (DecisionProblem α) :=
  {language | DeterministicP sourceEncoding language}

def EncodedNPClass {α : Type u} {β : Type v}
    (sourceEncoding : BinaryEncoding α)
    (witnessEncoding : BinaryEncoding β) :
    Set (DecisionProblem α) :=
  {language | EncodedNP sourceEncoding witnessEncoding language}

def punitEncoding : BinaryEncoding PUnit where
  encode := fun _ => [false]
  decode := fun code => if code = [false] then some PUnit.unit else none
  decode_encode := by simp

@[simp] theorem punitEncoding_size (x : PUnit) :
    punitEncoding.size x = 1 := by
  rfl

private noncomputable def deciderToVerifier
    {α : Type u} {E : BinaryEncoding α} {language : α → Prop}
    (D : DeterministicPolynomialDecider α E language) :
    PolynomialCertificateVerifier α PUnit E punitEncoding language where
  verify := fun x _ => D.decide x
  correct := by
    intro x
    constructor
    · intro hx
      exact ⟨PUnit.unit, (D.correct x).2 hx⟩
    · rintro ⟨_, h⟩
      exact (D.correct x).1 h
  witness_size_bound := by
    rcases D.steps_bound with ⟨c, d, hc⟩
    refine ⟨1, 1, ?_⟩
    intro x witness _
    simp only [punitEncoding_size]
    have hpos : 1 ≤ E.size x + 1 := by omega
    simp [Nat.pow_one]
  steps := fun x _ => D.steps x
  steps_bound := by
    rcases D.steps_bound with ⟨c, d, hc⟩
    refine ⟨c, d, ?_⟩
    intro x witness
    simp only [punitEncoding_size]
    have hbase : E.size x + 1 ≤ E.size x + 1 + 1 := by omega
    exact Nat.le_trans (hc x) (by
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hbase d))

theorem deterministicP_subset_encodedNP
    {α : Type u} {E : BinaryEncoding α} {language : α → Prop}
    (hP : language ∈ EncodedPClass E) :
    language ∈ EncodedNPClass E punitEncoding := by
  rcases hP with ⟨D⟩
  exact ⟨deciderToVerifier D⟩

theorem PolynomialCertificateVerifier.encodedNP
    {α : Type u} {β : Type v}
    {EA : BinaryEncoding α} {EB : BinaryEncoding β}
    {language : α → Prop}
    (V : PolynomialCertificateVerifier α β EA EB language) :
    EncodedNP EA EB language :=
  ⟨V⟩

theorem PolynomialCertificateVerifier.correct_iff
    {α : Type u} {β : Type v}
    {EA : BinaryEncoding α} {EB : BinaryEncoding β}
    {language : α → Prop}
    (V : PolynomialCertificateVerifier α β EA EB language) (x : α) :
    language x ↔ ∃ witness, V.verify x witness = true :=
  V.correct x

namespace PolynomialTimeMap

variable {α : Type u} {β : Type v} {γ : Type*}
variable {EA : BinaryEncoding α} {EB : BinaryEncoding β} {EC : BinaryEncoding γ}

theorem encodingPolynomialTime (f : PolynomialTimeMap α β EA EB) :
    EncodingPolynomialTime EA EB f.map :=
  ⟨f, rfl⟩

/-! Turn a concrete encoded map into the abstract reduction interface once its
    semantic correctness has been proved.  The runtime field is exactly the
    encoding-aware map predicate above, so this constructor does not assert a
    machine model that the project has not supplied. -/

def toPolynomialTimeReduction
    {source : DecisionProblem α} {target : DecisionProblem β}
    (f : PolynomialTimeMap α β EA EB)
    (correct : ∀ x, source x ↔ target (f.map x)) :
    PolynomialTimeReduction source target where
  reduction := {
    map := f.map
    correct := correct }
  PolynomialTime := EncodingPolynomialTime EA EB
  polynomialTime := f.encodingPolynomialTime

@[simp] theorem map_apply (f : PolynomialTimeMap α β EA EB) (x : α) :
    f.map x = f.map x := rfl

/-!
Composition deliberately takes the chosen machine-model closure theorem as an
explicit premise.  This avoids claiming that arbitrary polynomial witnesses
compose until the encoding/cost model has supplied the relevant arithmetic.
-/

/-- Compose two costed maps once the machine model proves the composed bounds. -/
def comp_of_closed
    (f : PolynomialTimeMap α β EA EB)
    (g : PolynomialTimeMap β γ EB EC)
    (steps_comp_bound : ∃ c d : Nat, ∀ x,
      f.steps x + g.steps (f.map x) ≤ c * (EA.size x + 1) ^ d)
    (output_comp_bound : ∃ c d : Nat, ∀ x,
      EC.size (g.map (f.map x)) ≤ c * (EA.size x + 1) ^ d) :
    PolynomialTimeMap α γ EA EC where
  map := fun x => g.map (f.map x)
  steps := fun x => f.steps x + g.steps (f.map x)
  steps_bound := steps_comp_bound
  output_bound := output_comp_bound

/-- Compose two costed maps when the first map does not increase encoded input
size.  This is a reusable closure rule for reductions such as complementation
or relabeling, whose output uses no more bits than their input.  As elsewhere
in this module, the work counter is supplied by the chosen execution model;
the result proves only its explicit polynomial bound. -/
def comp_of_size_nonexpanding
    (f : PolynomialTimeMap α β EA EB)
    (g : PolynomialTimeMap β γ EB EC)
    (hsize : ∀ x, EB.size (f.map x) ≤ EA.size x) :
    PolynomialTimeMap α γ EA EC := by
  refine comp_of_closed f g ?_ ?_
  · rcases f.steps_bound with ⟨c₁, d₁, hf⟩
    rcases g.steps_bound with ⟨c₂, d₂, hg⟩
    refine ⟨c₁ + c₂, d₁ + d₂, ?_⟩
    intro x
    let b := EA.size x + 1
    have hb : 1 ≤ b := by
      dsimp [b]
      omega
    have hfg : g.steps (f.map x) ≤ c₂ * b ^ d₂ := by
      calc
        g.steps (f.map x) ≤ c₂ * (EB.size (f.map x) + 1) ^ d₂ := hg _
        _ ≤ c₂ * b ^ d₂ := by
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_left
          dsimp [b]
          exact Nat.add_le_add_right (hsize x) 1
    have hpow₁ : b ^ d₁ ≤ b ^ (d₁ + d₂) := by
      rw [Nat.pow_add]
      exact Nat.le_mul_of_pos_right _ (Nat.pow_pos hb)
    have hpow₂ : b ^ d₂ ≤ b ^ (d₁ + d₂) := by
      rw [Nat.pow_add]
      have hleft : 1 ≤ b ^ d₁ := Nat.one_le_pow _ _ hb
      exact Nat.le_mul_of_pos_left _ hleft
    calc
      f.steps x + g.steps (f.map x) ≤ c₁ * b ^ d₁ + c₂ * b ^ d₂ := by
        exact Nat.add_le_add (hf x) hfg
      _ ≤ c₁ * b ^ (d₁ + d₂) + c₂ * b ^ (d₁ + d₂) := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left c₁ hpow₁)
          (Nat.mul_le_mul_left c₂ hpow₂)
      _ = (c₁ + c₂) * (EA.size x + 1) ^ (d₁ + d₂) := by
        rw [Nat.add_mul]
  · rcases g.output_bound with ⟨c, d, hg⟩
    refine ⟨c, d, ?_⟩
    intro x
    calc
      EC.size (g.map (f.map x)) ≤ c * (EB.size (f.map x) + 1) ^ d := hg _
      _ ≤ c * (EA.size x + 1) ^ d := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        exact Nat.add_le_add_right (hsize x) 1

theorem correct_encoding_section (f : PolynomialTimeMap α β EA EB) (x : α) :
    EB.decode (EB.encode (f.map x)) = some (f.map x) :=
  EB.decode_encode _

end PolynomialTimeMap

end Complexity
end AppliedModelingLib
