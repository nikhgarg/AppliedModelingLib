import AppliedModelingLib.Algorithms.Complexity.Classes
import AppliedModelingLib.Algorithms.Complexity.FiniteEncoding
import Mathlib.Computability.TuringMachine.Computable

/-!
# Native TM2 polynomial-time reductions

This module supplies the concrete execution meaning missing from the abstract
`PolynomialTimeReduction` interface.  A `TM2PolynomialTimeReduction` carries
an actual finite multitape Turing machine, its polynomial step bound, and a
many-one correctness proof.  It is deliberately narrower than a complexity
class theory: proving that a concrete map has such a machine, or that a source
language is NP-hard, remains a mathematical obligation.

## Upstream provenance and license

This module directly reuses the *definitions*, unchanged, from Mathlib
[`Mathlib/Computability/TuringMachine/Computable.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Computability/TuringMachine/Computable.lean),
at the repository's pinned Mathlib commit
[`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/tree/5450b53e5ddc75d46418fabb605edbf36bd0beb6),
under Apache-2.0.  In particular, it uses
`Turing.TM2ComputableInPolyTime` and `Turing.idComputableInPolyTime`; the
former packages a finite TM2 machine and its polynomial bound on actual
transition steps.  The local API and proofs are new; no upstream proof text is
copied or ported.

Compatibility was checked against the pinned dependency with a focused Lean
probe on 2026-09-08.  `#print axioms Turing.idComputableInPolyTime` reports
only `propext`, `Classical.choice`, and `Quot.sound`.  The imported Mathlib
file has an unrelated `proof_wanted` declaration for composition; this module
does not use that declaration or expose a composition theorem.
-/

namespace AppliedModelingLib
namespace Complexity

/--
An actual finite multitape-Turing-machine computation of `map` whose running
time is bounded by a polynomial in the selected binary input encoding.

The input and output alphabets are `Bool`, so this is a machine model over the
same binary tapes used by `BinaryEncoding`; it is not an abstract caller-supplied
cost counter.
-/
abbrev TM2PolynomialTimeMap
    {α β : Type}
    (sourceEncoding : BinaryEncoding α)
    (targetEncoding : BinaryEncoding β)
    (map : α → β) : Type 1 :=
  Turing.TM2ComputableInPolyTime sourceEncoding.encode targetEncoding.encode map

/--
A deterministic decision procedure realized by a finite TM2 machine.  Its
Boolean output is encoded by Mathlib's standard one-symbol Boolean encoding,
and `correct` is the exact accepted-language equivalence.
-/
structure TM2PolynomialDecider
    {Source : Type}
    (sourceEncoding : BinaryEncoding Source)
    (language : DecisionProblem Source) where
  decide : Source → Bool
  machine : Turing.TM2ComputableInPolyTime
    sourceEncoding.encode Computability.encodeBool decide
  correct : ∀ x, decide x = true ↔ language x

/--
The deterministic polynomial-time language class induced by the concrete TM2
model and a selected binary input encoding.  Membership contains an actual
finite machine witness, not only an execution-cost assertion.
-/
def TM2PClass {Source : Type} (sourceEncoding : BinaryEncoding Source) :
    Set (DecisionProblem Source) :=
  {language | Nonempty (TM2PolynomialDecider sourceEncoding language)}

namespace TM2PolynomialDecider

variable {Source : Type}
variable {sourceEncoding : BinaryEncoding Source}
variable {language : DecisionProblem Source}

theorem accepts_iff
    (D : TM2PolynomialDecider sourceEncoding language) (x : Source) :
    D.decide x = true ↔ language x :=
  D.correct x

theorem mem_TM2PClass
    (D : TM2PolynomialDecider sourceEncoding language) :
    language ∈ TM2PClass sourceEncoding :=
  ⟨D⟩

end TM2PolynomialDecider

/--
A many-one reduction implemented by a finite TM2 machine with a polynomial
transition bound.  This is the native reduction target required before a paper
can turn a semantic instance map into a standard polynomial-time reduction.
-/
structure TM2PolynomialTimeReduction
    {Source Target : Type}
    (sourceEncoding : BinaryEncoding Source)
    (targetEncoding : BinaryEncoding Target)
    (source : DecisionProblem Source)
    (target : DecisionProblem Target) where
  reduction : ManyOneReduction source target
  machine : TM2PolynomialTimeMap sourceEncoding targetEncoding reduction.map

namespace TM2PolynomialTimeReduction

variable {Source Target : Type}
variable {sourceEncoding : BinaryEncoding Source}
variable {targetEncoding : BinaryEncoding Target}
variable {source : DecisionProblem Source} {target : DecisionProblem Target}

/-- The machine-level reduction preserves the source decision predicate. -/
theorem correct
    (R : TM2PolynomialTimeReduction sourceEncoding targetEncoding source target)
    (x : Source) :
    source x ↔ target (R.reduction.map x) :=
  R.reduction.correct x

/--
Forget the implementation only after recording that the abstract
`PolynomialTime` predicate means actual TM2 polynomial-time execution under
these encodings.  This avoids treating an arbitrary step-count certificate as
a native machine proof.
-/
def toPolynomialTimeReduction
    (R : TM2PolynomialTimeReduction sourceEncoding targetEncoding source target) :
    PolynomialTimeReduction source target where
  reduction := R.reduction
  PolynomialTime := fun map => Nonempty
    (TM2PolynomialTimeMap sourceEncoding targetEncoding map)
  polynomialTime := ⟨R.machine⟩

/--
Identity is a real TM2 polynomial-time reduction, supplied by Mathlib's finite
machine construction.  It is a small executable sanity check for the chosen
binary encoding interface, not a substitute for a paper-specific reduction.
-/
noncomputable def id
    (encoding : BinaryEncoding Source)
    (language : DecisionProblem Source) :
    TM2PolynomialTimeReduction encoding encoding language language where
  reduction :=
    { map := _root_.id
      correct := fun _ => Iff.rfl }
  machine := by
    simpa [TM2PolynomialTimeMap] using
      (Turing.idComputableInPolyTime encoding.encode)

theorem id_correct
    (encoding : BinaryEncoding Source)
    (language : DecisionProblem Source)
    (x : Source) :
    language x ↔ language ((id encoding language).reduction.map x) :=
  (id encoding language).correct x

end TM2PolynomialTimeReduction

/-!
## A concrete Boolean-list transducer

The native interface above is useful only when a downstream development can
exhibit a finite machine.  The construction below is a small reusable building
block: it maps any Boolean function over a bit list, with a fully checked TM2
program and a linear transition bound.  Its temporary stack first reverses the
input, so the second pass restores the input order while emitting transformed
bits.  This is intentionally a list-transducer primitive, not a claim that an
arbitrary structured encoding map has been lowered to TM2.
-/

namespace BooleanListMap

open Turing
open Turing.TM2.Stmt

/-- A finite three-stack TM2 machine that maps `transform` over a Boolean
input list.  Stack `0` is input, stack `1` is temporary reversal storage, and
stack `2` is output. -/
def machine (transform : Bool → Bool) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ := fun _ => Bool
  Λ := Bool
  main := false
  σ := Option Bool
  initialState := none
  m := fun phase =>
    if phase then
      pop 1 (fun _ bit => bit)
        (branch Option.isSome
          (push 2 (fun state => transform (state.getD false)) (goto fun _ => true))
          halt)
    else
      pop 0 (fun _ bit => bit)
        (branch Option.isSome
          (push 1 (fun state => state.getD false) (goto fun _ => false))
          (goto fun _ => true))

/-- An explicit configuration for the two-pass Boolean-list machine. -/
def config (label : Option Bool) (state : Option Bool)
    (input temporary output : List Bool) :
    Turing.TM2.Cfg (fun _ : Fin 3 => Bool) Bool (Option Bool) where
  l := label
  var := state
  stk := Function.update
    (Function.update (Function.update (fun _ => []) 0 input) 1 temporary) 2 output

theorem initList_eq_config (transform : Bool → Bool) (input : List Bool) :
    Turing.initList (machine transform) input =
      config (some false) none input [] [] := by
  simp [Turing.initList, config, machine]
  congr 2
  funext k
  fin_cases k <;> simp

theorem haltList_eq_config (transform : Bool → Bool) (output : List Bool) :
    Turing.haltList (machine transform) output =
      config none none [] [] output := by
  simp [Turing.haltList, config, machine]
  congr 2
  funext k
  fin_cases k <;> simp

theorem input_step_cons (transform : Bool → Bool) (state : Option Bool) (bit : Bool)
    (input temporary output : List Bool) :
    (machine transform).step
      (config (some false) state (bit :: input) temporary output) =
      some (config (some false) (some bit) input (bit :: temporary) output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem input_step_nil (transform : Bool → Bool) (state : Option Bool)
    (temporary output : List Bool) :
    (machine transform).step (config (some false) state [] temporary output) =
      some (config (some true) none [] temporary output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem temporary_step_cons (transform : Bool → Bool) (state : Option Bool) (bit : Bool)
    (temporary output : List Bool) :
    (machine transform).step
      (config (some true) state [] (bit :: temporary) output) =
      some (config (some true) (some bit) [] temporary (transform bit :: output)) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem temporary_step_nil (transform : Bool → Bool) (state : Option Bool)
    (output : List Bool) :
    (machine transform).step (config (some true) state [] [] output) =
      some (config none none [] [] output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

/-- Package one deterministic machine transition as a time-one computation. -/
def oneStep {α : Type} (f : α → Option α) (a b : α) (h : f a = some b) :
    StateTransition.EvalsToInTime f a (some b) 1 :=
  { steps := 1
    evals_in_steps := by simpa only [Function.iterate_one, Function.comp_apply,
      Option.bind_eq_bind] using h
    steps_le_m := le_rfl }

/-- The first pass consumes the input and reverses it onto the temporary stack. -/
def run_input (transform : Bool → Bool) (input temporary output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime (machine transform).step
      (config (some false) state input temporary output)
      (some (config (some true) none [] (input.reverse ++ temporary) output))
      (input.length + 1) := by
  induction input generalizing temporary state with
  | nil =>
      simpa using oneStep _ _ _ (input_step_nil transform state temporary output)
  | cons bit input ih =>
      have hfirst := oneStep _ _ _
        (input_step_cons transform state bit input temporary output)
      have hrest := ih (bit :: temporary) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans _ 1 (input.length + 1) _ _ _ hfirst hrest

/-- The second pass restores input order and emits the transformed bits. -/
def run_temporary (transform : Bool → Bool) (temporary output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime (machine transform).step
      (config (some true) state [] temporary output)
      (some (config none none [] [] (temporary.reverse.map transform ++ output)))
      (temporary.length + 1) := by
  induction temporary generalizing output state with
  | nil =>
      simpa using oneStep _ _ _ (temporary_step_nil transform state output)
  | cons bit temporary ih =>
      have hfirst := oneStep _ _ _
        (temporary_step_cons transform state bit temporary output)
      have hrest := ih (transform bit :: output) (some bit)
      simpa [List.reverse_cons, List.map_append, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans _ 1 (temporary.length + 1) _ _ _ hfirst hrest

/-- The concrete machine maps every input bit in at most `2 * n + 2` TM2
transitions, where `n` is the input length. -/
def outputsInTime (transform : Bool → Bool) (input : List Bool) :
    Turing.TM2OutputsInTime (machine transform) input
      (some (input.map transform)) (2 * input.length + 2) := by
  have hinput := run_input transform input [] [] none
  have htemporary := run_temporary transform input.reverse [] none
  have hinput' : StateTransition.EvalsToInTime (machine transform).step
      (config (some false) none input [] [])
      (some (config (some true) none [] input.reverse []))
      (input.length + 1) := by
    simpa using hinput
  have htemporary' : StateTransition.EvalsToInTime (machine transform).step
      (config (some true) none [] input.reverse [])
      (some (config none none [] [] (input.map transform)))
      (input.reverse.length + 1) := by
    simpa using htemporary
  have h := StateTransition.EvalsToInTime.trans _ (input.length + 1)
    (input.reverse.length + 1) _ _ _ hinput' htemporary'
  rw [Turing.TM2OutputsInTime, initList_eq_config, Option.map_some,
    haltList_eq_config]
  have h' : StateTransition.EvalsToInTime (machine transform).step
      (config (some false) none input [] [])
      (some (config none none [] [] (input.map transform)))
      (input.length + (input.length + 2)) := by
    simpa [List.length_reverse, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  convert h' using 1
  omega

/-- The self-equivalence used to regard a raw Boolean list as both machine
input and output. -/
def boolIdentityEquiv : Bool ≃ Bool where
  toFun := fun bit => bit
  invFun := fun bit => bit
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem boolIdentityEquiv_symm_coe :
    (↑(boolIdentityEquiv.symm) : Bool → Bool) = id :=
  rfl

@[simp] theorem boolIdentityEquiv_symm_map (bits : List Bool) :
    bits.map (↑(boolIdentityEquiv.symm) : Bool → Bool) = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simpa using congrArg (List.cons bit) ih

@[simp] theorem boolIdentityEquiv_invFun_map (bits : List Bool) :
    bits.map boolIdentityEquiv.invFun = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simpa [boolIdentityEquiv] using congrArg (List.cons bit) ih

/-- A native polynomial-time TM2 witness for an elementwise Boolean-list map.
This is reusable execution infrastructure for bit-level encodings. -/
noncomputable def computableInPolyTime (transform : Bool → Bool) :
    Turing.TM2ComputableInPolyTime id id (List.map transform : List Bool → List Bool) where
  tm := machine transform
  inputAlphabet := boolIdentityEquiv
  outputAlphabet := boolIdentityEquiv
  time := 2 * Polynomial.X + 2
  outputsFun input := by
    change Turing.TM2OutputsInTime (machine transform)
      (List.map (fun bit => bit) input)
      (some (List.map (fun bit => bit) (input.map transform))) _
    simpa [boolIdentityEquiv, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Nat.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      outputsInTime transform input

end BooleanListMap

/-!
## A header-preserving Boolean-list transducer

Structured finite encodings commonly begin with one terminated-unary natural
number, followed by a Boolean payload.  The machine below copies that dynamic
header exactly and applies a Boolean transformation only after its terminating
`false`.  This is a machine component, rather than an assertion that every
map with such an encoding has been lowered to TM2.
-/

namespace UnaryHeaderBooleanListMap

open Turing
open Turing.TM2.Stmt

/-- Finite-control phases for a map that preserves one terminated-unary
header and transforms the remaining Boolean payload. -/
inductive Phase where
  | header
  | payload
  | transfer
  deriving DecidableEq, Fintype

/-- A finite three-stack TM2 machine. Stack `0` is input, stack `1`
accumulates the reverse output, and stack `2` is the output. The header phase
copies `true` tokens until it copies the first `false`; only the payload phase
applies `transform`. -/
def machine (transform : Bool → Bool) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ := fun _ => Bool
  Λ := Phase
  main := .header
  σ := Option Bool
  initialState := none
  m
    | .header =>
      pop 0 (fun _ bit => bit)
        (branch Option.isSome
          (branch (fun state => state.getD false)
            (push 1 (fun state => state.getD false) (goto fun _ => .header))
            (push 1 (fun state => state.getD false) (goto fun _ => .payload)))
          (goto fun _ => .transfer))
    | .payload =>
      pop 0 (fun _ bit => bit)
        (branch Option.isSome
          (push 1 (fun state => transform (state.getD false))
            (goto fun _ => .payload))
          (goto fun _ => .transfer))
    | .transfer =>
      pop 1 (fun _ bit => bit)
        (branch Option.isSome
          (push 2 (fun state => state.getD false) (goto fun _ => .transfer))
          halt)

/-- An explicit configuration for the header-preserving machine. -/
def config (label : Option Phase) (state : Option Bool)
    (input reversedOutput output : List Bool) :
    Turing.TM2.Cfg (fun _ : Fin 3 => Bool) Phase (Option Bool) where
  l := label
  var := state
  stk := Function.update
    (Function.update (Function.update (fun _ => []) 0 input) 1 reversedOutput) 2 output

theorem initList_eq_config (transform : Bool → Bool) (input : List Bool) :
    Turing.initList (machine transform) input =
      config (some .header) none input [] [] := by
  simp [Turing.initList, config, machine]
  congr 2
  funext k
  fin_cases k <;> simp

theorem haltList_eq_config (transform : Bool → Bool) (output : List Bool) :
    Turing.haltList (machine transform) output =
      config none none [] [] output := by
  simp [Turing.haltList, config, machine]
  congr 2
  funext k
  fin_cases k <;> simp

theorem header_step_true (transform : Bool → Bool) (state : Option Bool)
    (input reversedOutput output : List Bool) :
    (machine transform).step
      (config (some .header) state (true :: input) reversedOutput output) =
      some (config (some .header) (some true) input
        (true :: reversedOutput) output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem header_step_false (transform : Bool → Bool) (state : Option Bool)
    (input reversedOutput output : List Bool) :
    (machine transform).step
      (config (some .header) state (false :: input) reversedOutput output) =
      some (config (some .payload) (some false) input
        (false :: reversedOutput) output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem header_step_nil (transform : Bool → Bool) (state : Option Bool)
    (reversedOutput output : List Bool) :
    (machine transform).step
      (config (some .header) state [] reversedOutput output) =
      some (config (some .transfer) none [] reversedOutput output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem payload_step_cons (transform : Bool → Bool) (state : Option Bool)
    (bit : Bool) (input reversedOutput output : List Bool) :
    (machine transform).step
      (config (some .payload) state (bit :: input) reversedOutput output) =
      some (config (some .payload) (some bit) input
        (transform bit :: reversedOutput) output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem payload_step_nil (transform : Bool → Bool) (state : Option Bool)
    (reversedOutput output : List Bool) :
    (machine transform).step
      (config (some .payload) state [] reversedOutput output) =
      some (config (some .transfer) none [] reversedOutput output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem transfer_step_cons (transform : Bool → Bool) (state : Option Bool)
    (bit : Bool) (reversedOutput output : List Bool) :
    (machine transform).step
      (config (some .transfer) state [] (bit :: reversedOutput) output) =
      some (config (some .transfer) (some bit) [] reversedOutput
        (bit :: output)) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem transfer_step_nil (transform : Bool → Bool) (state : Option Bool)
    (output : List Bool) :
    (machine transform).step
      (config (some .transfer) state [] [] output) =
      some (config none none [] [] output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

/-- Package one deterministic machine transition as a time-one computation. -/
def oneStep {α : Type} (f : α → Option α) (a b : α) (h : f a = some b) :
    StateTransition.EvalsToInTime f a (some b) 1 :=
  BooleanListMap.oneStep f a b h

/-- Transfer an accumulated reverse stream to the designated output stack. -/
def run_transfer (transform : Bool → Bool) (reversedOutput output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime (machine transform).step
      (config (some .transfer) state [] reversedOutput output)
      (some (config none none [] [] (reversedOutput.reverse ++ output)))
      (reversedOutput.length + 1) := by
  induction reversedOutput generalizing output state with
  | nil =>
      simpa using oneStep _ _ _ (transfer_step_nil transform state output)
  | cons bit reversedOutput ih =>
      have hfirst := oneStep _ _ _
        (transfer_step_cons transform state bit reversedOutput output)
      have hrest := ih (bit :: output) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using
        StateTransition.EvalsToInTime.trans _ 1 (reversedOutput.length + 1)
          _ _ _ hfirst hrest

/-- Transform a suffix after a copied header, then transfer the complete
accumulator. -/
def run_payload (transform : Bool → Bool) (payload reversedOutput output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime (machine transform).step
      (config (some .payload) state payload reversedOutput output)
      (some (config none none [] []
        (reversedOutput.reverse ++ payload.map transform ++ output)))
      (2 * payload.length + reversedOutput.length + 2) := by
  induction payload generalizing reversedOutput output state with
  | nil =>
      have hfirst := oneStep _ _ _ (payload_step_nil transform state reversedOutput output)
      have htransfer := run_transfer transform reversedOutput output none
      have h := StateTransition.EvalsToInTime.trans _ 1
        (reversedOutput.length + 1) _ _ _ hfirst htransfer
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  | cons bit payload ih =>
      have hfirst := oneStep _ _ _
        (payload_step_cons transform state bit payload reversedOutput output)
      have hrest := ih (transform bit :: reversedOutput) output (some bit)
      have h := StateTransition.EvalsToInTime.trans _ 1
        (2 * payload.length + (transform bit :: reversedOutput).length + 2)
        _ _ _ hfirst hrest
      convert h using 1 <;>
        simp [List.map_cons, List.reverse_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm, List.append_assoc]
      all_goals omega

/-- Scan one terminated-unary header, copy it, transform the remaining
payload, and transfer the entire output. The generalized accumulator form is
what makes the dynamic header usable inside other finite TM2 constructions. -/
def run (transform : Bool → Bool) (header : Nat) (payload reversedOutput output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime (machine transform).step
      (config (some .header) state
        (unaryIndexEncode header ++ payload) reversedOutput output)
      (some (config none none [] []
        (reversedOutput.reverse ++ unaryIndexEncode header ++
          payload.map transform ++ output)))
      (2 * (unaryIndexEncode header ++ payload).length + reversedOutput.length + 2) := by
  induction header generalizing payload reversedOutput output state with
  | zero =>
      have hfirst := oneStep _ _ _
        (header_step_false transform state payload reversedOutput output)
      have hrest := run_payload transform payload (false :: reversedOutput)
        output (some false)
      have h := StateTransition.EvalsToInTime.trans _ 1
        (2 * payload.length + (false :: reversedOutput).length + 2)
        _ _ _ hfirst hrest
      convert h using 1 <;>
        simp [unaryIndexEncode, List.reverse_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm, List.append_assoc]
      all_goals omega
  | succ header ih =>
      have hfirst := oneStep _ _ _
        (header_step_true transform state
          (unaryIndexEncode header ++ payload) reversedOutput output)
      have hrest := ih payload (true :: reversedOutput) output (some true)
      have h := StateTransition.EvalsToInTime.trans _ 1
        (2 * (unaryIndexEncode header ++ payload).length +
          (true :: reversedOutput).length + 2)
        _ _ _ hfirst hrest
      convert h using 1 <;>
        simp [unaryIndexEncode, List.reverse_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm, List.append_assoc]
      all_goals omega

/-- The native transducer realizes a header-preserving Boolean map in linear
time in the complete encoded stream. -/
def outputsInTime (transform : Bool → Bool) (header : Nat) (payload : List Bool) :
    Turing.TM2OutputsInTime (machine transform)
      (unaryIndexEncode header ++ payload)
      (some (unaryIndexEncode header ++ payload.map transform))
      (2 * (unaryIndexEncode header ++ payload).length + 2) := by
  rw [Turing.TM2OutputsInTime, initList_eq_config, Option.map_some,
    haltList_eq_config]
  have h := run transform header payload [] [] none
  simpa using h

/-- A binary encoding for one terminated-unary header followed by an arbitrary
Boolean payload. -/
abbrev Input := Nat × List Bool

def inputCode (input : Input) : List Bool :=
  unaryIndexEncode input.1 ++ input.2

theorem inputCode_injective : Function.Injective inputCode := by
  rintro ⟨header, payload⟩ ⟨header', payload'⟩ hcode
  have hheader := congrArg unaryIndexDecode hcode
  simp [inputCode, unaryIndexDecode_encode_append] at hheader
  subst header'
  have hpayload : payload = payload' :=
    List.append_right_injective (unaryIndexEncode header) hcode
  subst payload'
  rfl

noncomputable def inputEncoding : BinaryEncoding Input :=
  encodingOfInjectiveList inputCode inputCode_injective

@[simp] theorem inputEncoding_encode (input : Input) :
    inputEncoding.encode input = inputCode input :=
  rfl

@[simp] theorem inputEncoding_size (header : Nat) (payload : List Bool) :
    inputEncoding.size (header, payload) = header + 1 + payload.length := by
  change (unaryIndexEncode header ++ payload).length = _
  simp [unaryIndexEncode_length]

/-- Transform only the payload of a terminated-unary-header input. -/
def map (transform : Bool → Bool) (input : Input) : Input :=
  (input.1, input.2.map transform)

/-- A native polynomial-time witness for the reusable header-preserving map. -/
noncomputable def computableInPolyTime (transform : Bool → Bool) :
    Turing.TM2ComputableInPolyTime inputEncoding.encode inputEncoding.encode
      (map transform) where
  tm := machine transform
  inputAlphabet := BooleanListMap.boolIdentityEquiv
  outputAlphabet := BooleanListMap.boolIdentityEquiv
  time := 2 * Polynomial.X + 2
  outputsFun input := by
    rcases input with ⟨header, payload⟩
    change Turing.TM2OutputsInTime (machine transform)
      (List.map (fun bit => bit) (unaryIndexEncode header ++ payload))
      (some (List.map (fun bit => bit)
        (unaryIndexEncode header ++ payload.map transform))) _
    simpa [inputEncoding_encode, inputCode, map, BooleanListMap.boolIdentityEquiv,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Nat.mul_comm,
      Nat.add_comm, Nat.add_left_comm] using outputsInTime transform header payload

end UnaryHeaderBooleanListMap

/-!
## A concrete Boolean-list reversal transducer

The row-major auction reduction repeatedly moves a finite tape through a
working stack and later restores it. The construction below isolates that
fundamental stack operation as a native TM2 program: it reverses a Boolean
list directly onto its output stack.
-/

namespace BooleanListReverse

open Turing
open Turing.TM2.Stmt

/-- A finite two-stack TM2 machine that maps `input` to `input.reverse`. -/
def machine : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ :=
    pop 0 (fun _ bit => bit)
      (branch Option.isSome
        (push 1 (fun state => state.getD false) (goto fun _ => ()))
        halt)

/-- An explicit configuration for the Boolean-list reversal machine. -/
def config (label : Option Unit) (state : Option Bool)
    (input output : List Bool) :
    Turing.TM2.Cfg (fun _ : Fin 2 => Bool) Unit (Option Bool) where
  l := label
  var := state
  stk := Function.update (Function.update (fun _ => []) 0 input) 1 output

theorem initList_eq_config (input : List Bool) :
    Turing.initList machine input = config (some ()) none input [] := by
  simp [Turing.initList, config, machine]
  congr 2
  funext k
  fin_cases k <;> simp

theorem haltList_eq_config (output : List Bool) :
    Turing.haltList machine output = config none none [] output := by
  simp [Turing.haltList, config, machine]
  congr 2
  funext k
  fin_cases k <;> simp

theorem step_cons (state : Option Bool) (bit : Bool) (input output : List Bool) :
    machine.step (config (some ()) state (bit :: input) output) =
      some (config (some ()) (some bit) input (bit :: output)) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem step_nil (state : Option Bool) (output : List Bool) :
    machine.step (config (some ()) state [] output) =
      some (config none none [] output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

/-- The exhibited reversal run uses one terminal transition plus one transition
per input bit. -/
def run (input output : List Bool) (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some ()) state input output)
      (some (config none none [] (input.reverse ++ output)))
      (input.length + 1) := by
  induction input generalizing output state with
  | nil =>
      simpa using BooleanListMap.oneStep _ _ _ (step_nil state output)
  | cons bit input ih =>
      have hfirst := BooleanListMap.oneStep _ _ _ (step_cons state bit input output)
      have hrest := ih (bit :: output) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans _ 1 (input.length + 1) _ _ _ hfirst hrest

/-- The concrete machine reverses every input list in at most `n + 1` TM2
transitions. -/
def outputsInTime (input : List Bool) :
    Turing.TM2OutputsInTime machine input (some input.reverse) (input.length + 1) := by
  have h := run input [] none
  rw [Turing.TM2OutputsInTime, initList_eq_config, Option.map_some,
    haltList_eq_config]
  simpa using h

/-- A native polynomial-time TM2 witness for Boolean-list reversal.

This is reusable stack-transducer infrastructure for machine-facing binary
encodings. -/
noncomputable def computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id (List.reverse : List Bool → List Bool) where
  tm := machine
  inputAlphabet := BooleanListMap.boolIdentityEquiv
  outputAlphabet := BooleanListMap.boolIdentityEquiv
  time := Polynomial.X + 1
  outputsFun input := by
    change Turing.TM2OutputsInTime machine
      (List.map (fun bit => bit) input)
      (some (List.map (fun bit => bit) input.reverse)) _
    simpa [BooleanListMap.boolIdentityEquiv, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      outputsInTime input

end BooleanListReverse

/-!
## A concrete Boolean-list duplication transducer

The row-major auction reduction must preserve one input table while using it in
multiple output passes.  The machine below supplies the reusable primitive
that duplicates a Boolean tape.  It reverses the input once, copies that
reversed tape to two output stacks, reverses the second copy onto the temporary
stack, and appends it to the first output copy.
-/

namespace BooleanListDuplicate

open Turing
open Turing.TM2.Stmt

/-- Finite-control phases for the four-stack Boolean-list duplicator. -/
inductive Phase where
  | input
  | temporary
  | firstOutput
  | secondOutput
  | copy
  | temporaryCopy
  | finalTemporary
  | finalOutput
  deriving DecidableEq, Fintype

/-- A finite four-stack TM2 machine that maps `input` to `input ++ input`. -/
def machine : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 2
  Γ := fun _ => Bool
  Λ := Phase
  main := .input
  σ := Option Bool
  initialState := none
  m
    | .input =>
      pop 0 (fun _ bit => bit)
        (branch Option.isSome
          (push 1 (fun state => state.getD false) (goto fun _ => .input))
          (goto fun _ => .temporary))
    | .temporary =>
      pop 1 (fun _ bit => bit)
        (branch Option.isSome
          (goto fun _ => .firstOutput)
          (goto fun _ => .copy))
    | .firstOutput =>
      push 2 (fun state => state.getD false) (goto fun _ => .secondOutput)
    | .secondOutput =>
      push 3 (fun state => state.getD false) (goto fun _ => .temporary)
    | .copy =>
      pop 3 (fun _ bit => bit)
        (branch Option.isSome
          (goto fun _ => .temporaryCopy)
          (goto fun _ => .finalTemporary))
    | .temporaryCopy =>
      push 1 (fun state => state.getD false) (goto fun _ => .copy)
    | .finalTemporary =>
      pop 1 (fun _ bit => bit)
        (branch Option.isSome
          (goto fun _ => .finalOutput)
          halt)
    | .finalOutput =>
      push 2 (fun state => state.getD false) (goto fun _ => .finalTemporary)

/-- An explicit configuration for the four-stack Boolean-list duplicator. -/
def config (label : Option Phase) (state : Option Bool)
    (input temporary output copy : List Bool) :
    Turing.TM2.Cfg (fun _ : Fin 4 => Bool) Phase (Option Bool) where
  l := label
  var := state
  stk := Function.update
    (Function.update
      (Function.update
        (Function.update (fun _ => []) 0 input) 1 temporary) 2 output) 3 copy

theorem initList_eq_config (input : List Bool) :
    Turing.initList machine input =
      config (some .input) none input [] [] [] := by
  simp [Turing.initList, config, machine]
  congr 2
  funext k
  fin_cases k <;> simp

theorem haltList_eq_config (output : List Bool) :
    Turing.haltList machine output =
      config none none [] [] output [] := by
  simp [Turing.haltList, config, machine]
  congr 2
  funext k
  fin_cases k <;> simp

theorem input_step_cons (state : Option Bool) (bit : Bool)
    (input temporary output copy : List Bool) :
    machine.step
      (config (some .input) state (bit :: input) temporary output copy) =
      some (config (some .input) (some bit) input (bit :: temporary) output copy) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem input_step_nil (state : Option Bool)
    (temporary output copy : List Bool) :
    machine.step (config (some .input) state [] temporary output copy) =
      some (config (some .temporary) none [] temporary output copy) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem temporary_step_cons (state : Option Bool) (bit : Bool)
    (input temporary output copy : List Bool) :
    machine.step
      (config (some .temporary) state input (bit :: temporary) output copy) =
      some (config (some .firstOutput) (some bit) input temporary output copy) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem temporary_step_nil (state : Option Bool)
    (input output copy : List Bool) :
    machine.step (config (some .temporary) state input [] output copy) =
      some (config (some .copy) none input [] output copy) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem firstOutput_step (bit : Bool)
    (input temporary output copy : List Bool) :
    machine.step
      (config (some .firstOutput) (some bit) input temporary output copy) =
      some (config (some .secondOutput) (some bit) input temporary (bit :: output) copy) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem secondOutput_step (bit : Bool)
    (input temporary output copy : List Bool) :
    machine.step
      (config (some .secondOutput) (some bit) input temporary output copy) =
      some (config (some .temporary) (some bit) input temporary output (bit :: copy)) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem copy_step_cons (state : Option Bool) (bit : Bool)
    (input temporary output copy : List Bool) :
    machine.step
      (config (some .copy) state input temporary output (bit :: copy)) =
      some (config (some .temporaryCopy) (some bit) input temporary output copy) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem copy_step_nil (state : Option Bool)
    (input temporary output : List Bool) :
    machine.step (config (some .copy) state input temporary output []) =
      some (config (some .finalTemporary) none input temporary output []) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem temporaryCopy_step (bit : Bool)
    (input temporary output copy : List Bool) :
    machine.step
      (config (some .temporaryCopy) (some bit) input temporary output copy) =
      some (config (some .copy) (some bit) input (bit :: temporary) output copy) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem finalTemporary_step_cons (state : Option Bool) (bit : Bool)
    (input temporary output copy : List Bool) :
    machine.step
      (config (some .finalTemporary) state input (bit :: temporary) output copy) =
      some (config (some .finalOutput) (some bit) input temporary output copy) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem finalTemporary_step_nil (state : Option Bool)
    (input output copy : List Bool) :
    machine.step (config (some .finalTemporary) state input [] output copy) =
      some (config none none input [] output copy) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem finalOutput_step (bit : Bool)
    (input temporary output copy : List Bool) :
    machine.step
      (config (some .finalOutput) (some bit) input temporary output copy) =
      some (config (some .finalTemporary) (some bit) input temporary (bit :: output) copy) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

/-- The first pass consumes the input and reverses it onto the temporary stack. -/
def run_input (input temporary output copy : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .input) state input temporary output copy)
      (some (config (some .temporary) none [] (input.reverse ++ temporary) output copy))
      (input.length + 1) := by
  induction input generalizing temporary state with
  | nil =>
      simpa using BooleanListMap.oneStep _ _ _
        (input_step_nil state temporary output copy)
  | cons bit input ih =>
      have hfirst := BooleanListMap.oneStep _ _ _
        (input_step_cons state bit input temporary output copy)
      have hrest := ih (bit :: temporary) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans _ 1 (input.length + 1) _ _ _ hfirst hrest

/-- The second pass copies the reversed temporary stack to both output stacks. -/
def run_temporary (temporary output copy : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .temporary) state [] temporary output copy)
      (some (config (some .copy) none [] []
        (temporary.reverse ++ output) (temporary.reverse ++ copy)))
      (3 * temporary.length + 1) := by
  induction temporary generalizing output copy state with
  | nil =>
      simpa using BooleanListMap.oneStep _ _ _
        (temporary_step_nil state [] output copy)
  | cons bit temporary ih =>
      have hfirst := BooleanListMap.oneStep _ _ _
        (temporary_step_cons state bit [] temporary output copy)
      have hsecond := BooleanListMap.oneStep _ _ _
        (firstOutput_step bit [] temporary output copy)
      have hthird := BooleanListMap.oneStep _ _ _
        (secondOutput_step bit [] temporary (bit :: output) copy)
      have hfirstSecond := StateTransition.EvalsToInTime.trans _ 1 1 _ _ _ hfirst hsecond
      have hfirstThird := StateTransition.EvalsToInTime.trans _ 2 1 _ _ _ hfirstSecond hthird
      have hrest := ih (bit :: output) (bit :: copy) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_add] using
        StateTransition.EvalsToInTime.trans _ 3 (3 * temporary.length + 1) _ _ _
          hfirstThird hrest

/-- The third pass reverses the second output copy onto the temporary stack. -/
def run_copy (temporary output copy : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .copy) state [] temporary output copy)
      (some (config (some .finalTemporary) none [] (copy.reverse ++ temporary) output []))
      (2 * copy.length + 1) := by
  induction copy generalizing temporary output state with
  | nil =>
      simpa using BooleanListMap.oneStep _ _ _
        (copy_step_nil state [] temporary output)
  | cons bit copy ih =>
      have hfirst := BooleanListMap.oneStep _ _ _
        (copy_step_cons state bit [] temporary output copy)
      have hsecond := BooleanListMap.oneStep _ _ _
        (temporaryCopy_step bit [] temporary output copy)
      have hfirstSecond := StateTransition.EvalsToInTime.trans _ 1 1 _ _ _ hfirst hsecond
      have hrest := ih (bit :: temporary) output (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_add] using
        StateTransition.EvalsToInTime.trans _ 2 (2 * copy.length + 1) _ _ _
          hfirstSecond hrest

/-- The final pass appends the reversed second copy to the first output copy. -/
def run_finalTemporary (temporary output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .finalTemporary) state [] temporary output [])
      (some (config none none [] [] (temporary.reverse ++ output) []))
      (2 * temporary.length + 1) := by
  induction temporary generalizing output state with
  | nil =>
      simpa using BooleanListMap.oneStep _ _ _
        (finalTemporary_step_nil state [] output [])
  | cons bit temporary ih =>
      have hfirst := BooleanListMap.oneStep _ _ _
        (finalTemporary_step_cons state bit [] temporary output [])
      have hsecond := BooleanListMap.oneStep _ _ _
        (finalOutput_step bit [] temporary output [])
      have hfirstSecond := StateTransition.EvalsToInTime.trans _ 1 1 _ _ _ hfirst hsecond
      have hrest := ih (bit :: output) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_add] using
        StateTransition.EvalsToInTime.trans _ 2 (2 * temporary.length + 1) _ _ _
          hfirstSecond hrest

/-- The concrete machine duplicates every input bit in at most `8 * n + 4`
TM2 transitions, where `n` is the input length. -/
def outputsInTime (input : List Bool) :
    Turing.TM2OutputsInTime machine input (some (input ++ input))
      (8 * input.length + 4) := by
  have hinput := run_input input [] [] [] none
  have htemporary := run_temporary input.reverse [] [] none
  have hcopy := run_copy [] input input none
  have hfinal := run_finalTemporary input.reverse input none
  have hinput' : StateTransition.EvalsToInTime machine.step
      (config (some .input) none input [] [] [])
      (some (config (some .temporary) none [] input.reverse [] []))
      (input.length + 1) := by
    simpa using hinput
  have htemporary' : StateTransition.EvalsToInTime machine.step
      (config (some .temporary) none [] input.reverse [] [])
      (some (config (some .copy) none [] [] input input))
      (3 * input.length + 1) := by
    simpa [List.length_reverse] using htemporary
  have hcopy' : StateTransition.EvalsToInTime machine.step
      (config (some .copy) none [] [] input input)
      (some (config (some .finalTemporary) none [] input.reverse input []))
      (2 * input.length + 1) := by
    simpa using hcopy
  have hfinal' : StateTransition.EvalsToInTime machine.step
      (config (some .finalTemporary) none [] input.reverse input [])
      (some (config none none [] [] (input ++ input) []))
      (2 * input.length + 1) := by
    simpa [List.length_reverse] using hfinal
  have hinputTemporary := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hinput' htemporary'
  have hinputTemporaryCopy :=
    StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hinputTemporary hcopy'
  have h := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hinputTemporaryCopy hfinal'
  rw [Turing.TM2OutputsInTime, initList_eq_config, Option.map_some,
    haltList_eq_config]
  have h' : StateTransition.EvalsToInTime machine.step
      (config (some .input) none input [] [] [])
      (some (config none none [] [] (input ++ input) []))
      (8 * input.length + 4) := by
    convert h using 1 ; omega
  exact h'

/-- A native polynomial-time TM2 witness for Boolean-list duplication.

This is reusable execution infrastructure for bit-level encodings: it records
the concrete finite machine and its checked linear transition bound. -/
noncomputable def computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id (fun input : List Bool => input ++ input) where
  tm := machine
  inputAlphabet := BooleanListMap.boolIdentityEquiv
  outputAlphabet := BooleanListMap.boolIdentityEquiv
  time := 8 * Polynomial.X + 4
  outputsFun input := by
    change Turing.TM2OutputsInTime machine
      (List.map (fun bit => bit) input)
      (some (List.map (fun bit => bit) (input ++ input))) _
    simpa [BooleanListMap.boolIdentityEquiv, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Nat.mul_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using outputsInTime input

end BooleanListDuplicate

end Complexity
end AppliedModelingLib
