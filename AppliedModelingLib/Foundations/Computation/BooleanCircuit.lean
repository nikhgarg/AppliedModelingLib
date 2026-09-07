import Mathlib.Data.Fin.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.Nat.Bitwise
import Batteries.Data.BitVec.Lemmas
import Init.Data.BitVec.Bitblast

/-!
# Sequential Boolean gate DAGs

This is a small, paper-independent representation of finite Boolean circuits.
Gates are stored in topological order, and a gate may cite only an input wire
or an earlier gate.  Thus `gateCount` is an actual DAG gate count rather than
an unverified symbolic size annotation.
-/

namespace AppliedModelingLib.Computation

/-- Fixed-width words are equal when all of their little-endian bits agree.
This fills the small extensionality gap left by the core bit-vector API and
is useful when proving that a composed Boolean circuit returns a whole word. -/
theorem bitVec_eq_of_getLsb_eq {width : ℕ} {left right : BitVec width}
    (hbits : ∀ bit : Fin width, left.getLsb bit = right.getLsb bit) :
    left = right := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit < width
  · have h := hbits ⟨bit, hbit⟩
    simpa [BitVec.getLsb] using h
  · have hwidth : width ≤ bit := Nat.le_of_not_gt hbit
    have hpow : 2 ^ width ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hwidth
    have hleft : left.toNat < 2 ^ bit := left.isLt.trans_le hpow
    have hright : right.toNat < 2 ^ bit := right.isLt.trans_le hpow
    rw [Nat.testBit_eq_false_of_lt hleft, Nat.testBit_eq_false_of_lt hright]

/-- A wire available after `gateCount` gates: either one of the input bits or
an earlier gate output. -/
inductive BooleanWire (inputCount : ℕ) (gateCount : ℕ) where
  | input : Fin inputCount → BooleanWire inputCount gateCount
  | gate : Fin gateCount → BooleanWire inputCount gateCount

/-- A two-input Boolean gate whose arguments may cite only earlier wires. -/
inductive BooleanGate (inputCount : ℕ) (priorGateCount : ℕ) where
  | constant : Bool → BooleanGate inputCount priorGateCount
  | nand : BooleanWire inputCount priorGateCount →
      BooleanWire inputCount priorGateCount → BooleanGate inputCount priorGateCount

/-- Evaluate one available wire from primary inputs and already-computed gate
outputs. -/
def BooleanWire.eval
    {inputCount gateCount : ℕ} (inputs : Fin inputCount → Bool)
    (gates : Fin gateCount → Bool) : BooleanWire inputCount gateCount → Bool
  | .input i => inputs i
  | .gate i => gates i

/-- NAND is functionally complete, so every gate in this base representation
has a standard two-input Boolean realization. -/
def BooleanGate.eval
    {inputCount priorGateCount : ℕ} (inputs : Fin inputCount → Bool)
    (previous : Fin priorGateCount → Bool) :
    BooleanGate inputCount priorGateCount → Bool
  | .constant value => value
  | .nand left right => !(left.eval inputs previous && right.eval inputs previous)

/-- A topologically ordered list of Boolean gates.  Adding a gate exposes its
output only to later gates. -/
inductive BooleanGateList (inputCount : ℕ) : ℕ → Type
  | nil : BooleanGateList inputCount 0
  | snoc {priorGateCount : ℕ} : BooleanGateList inputCount priorGateCount →
      BooleanGate inputCount priorGateCount →
      BooleanGateList inputCount (priorGateCount + 1)

/-- Evaluate all gates in a topologically ordered list. -/
def BooleanGateList.eval
    {inputCount : ℕ} : {gateCount : ℕ} →
      BooleanGateList inputCount gateCount → (Fin inputCount → Bool) →
        Fin gateCount → Bool
  | 0, .nil, _, wire => Fin.elim0 wire
  | priorGateCount + 1, .snoc previous gate, inputs, wire =>
      if hprior : wire.val < priorGateCount then
        previous.eval inputs ⟨wire.val, hprior⟩
      else
        gate.eval inputs (previous.eval inputs)

/-- A sequential circuit builder whose currently available wires are all
primary inputs followed by the outputs of prior gates.  It is convenient for
constructing shared arithmetic circuits one gate at a time. -/
inductive BooleanCircuitBuilder (inputCount : ℕ) : ℕ → Type
  | start : BooleanCircuitBuilder inputCount 0
  | constant {priorGateCount : ℕ} : BooleanCircuitBuilder inputCount priorGateCount →
      Bool → BooleanCircuitBuilder inputCount (priorGateCount + 1)
  | nand {priorGateCount : ℕ} : BooleanCircuitBuilder inputCount priorGateCount →
      Fin (inputCount + priorGateCount) → Fin (inputCount + priorGateCount) →
      BooleanCircuitBuilder inputCount (priorGateCount + 1)

/-- Evaluate every currently available wire of a sequential circuit builder. -/
def BooleanCircuitBuilder.eval
    {inputCount : ℕ} : {gateCount : ℕ} →
      BooleanCircuitBuilder inputCount gateCount → (Fin inputCount → Bool) →
        Fin (inputCount + gateCount) → Bool
  | 0, .start, inputValues, wire => inputValues (Fin.cast (by simp) wire)
  | priorGateCount + 1, .constant previous value, inputs, wire =>
      if hprior : wire.val < inputCount + priorGateCount then
        previous.eval inputs ⟨wire.val, hprior⟩
      else
        value
  | priorGateCount + 1, .nand previous left right, inputs, wire =>
      if hprior : wire.val < inputCount + priorGateCount then
        previous.eval inputs ⟨wire.val, hprior⟩
      else
        !(previous.eval inputs left && previous.eval inputs right)

/-- The newest NAND gate of a builder has the expected semantics. -/
theorem BooleanCircuitBuilder.eval_nand_last
    {inputCount priorGateCount : ℕ}
    (previous : BooleanCircuitBuilder inputCount priorGateCount)
    (left right : Fin (inputCount + priorGateCount))
    (inputs : Fin inputCount → Bool) :
    (BooleanCircuitBuilder.nand previous left right).eval inputs
      ⟨inputCount + priorGateCount,
        by
          change inputCount + priorGateCount < inputCount + priorGateCount + 1
          exact Nat.lt_succ_self _⟩ =
        !(previous.eval inputs left && previous.eval inputs right) := by
  simp [BooleanCircuitBuilder.eval]

/-- The newest constant gate of a builder has its declared Boolean value. -/
theorem BooleanCircuitBuilder.eval_constant_last
    {inputCount priorGateCount : ℕ}
    (previous : BooleanCircuitBuilder inputCount priorGateCount)
    (value : Bool) (inputs : Fin inputCount → Bool) :
    (BooleanCircuitBuilder.constant previous value).eval inputs
      ⟨inputCount + priorGateCount,
        by
          change inputCount + priorGateCount < inputCount + priorGateCount + 1
          exact Nat.lt_succ_self _⟩ = value := by
  simp [BooleanCircuitBuilder.eval]

/-- Convert a builder wire number into its typed input-or-earlier-gate form. -/
def BooleanWire.ofFin (inputCount gateCount : ℕ)
    (wire : Fin (inputCount + gateCount)) : BooleanWire inputCount gateCount :=
  if hinput : wire.val < inputCount then
    .input ⟨wire.val, hinput⟩
  else
    .gate ⟨wire.val - inputCount,
      Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt hinput) wire.isLt⟩

/-- Turn a builder into the underlying topologically ordered gate list. -/
def BooleanCircuitBuilder.toGateList
    {inputCount : ℕ} : {gateCount : ℕ} →
      BooleanCircuitBuilder inputCount gateCount → BooleanGateList inputCount gateCount
  | 0, .start => .nil
  | _ + 1, .constant previous value =>
      .snoc previous.toGateList (.constant value)
  | priorGateCount + 1, .nand previous left right =>
      .snoc previous.toGateList
        (.nand (BooleanWire.ofFin inputCount priorGateCount left)
          (BooleanWire.ofFin inputCount priorGateCount right))

/-- Regard an old wire as available after additional gates have been appended. -/
def BooleanWire.liftRight
    {inputCount gateCount : ℕ} (additionalGateCount : ℕ) :
    BooleanWire inputCount gateCount → BooleanWire inputCount (gateCount + additionalGateCount)
  | .input inputBit => .input inputBit
  | .gate gateIndex => .gate ⟨gateIndex.val,
      lt_of_lt_of_le gateIndex.isLt (Nat.le_add_right gateCount additionalGateCount)⟩

/-- Translate a wire of an appended gate list: primary inputs are substituted
by outer wires, while inner gate references are shifted past the outer list. -/
def BooleanWire.appendTranslate
    {outerInputCount outerGateCount innerInputCount priorInnerGateCount : ℕ}
    (inputMap : Fin innerInputCount → BooleanWire outerInputCount outerGateCount) :
    BooleanWire innerInputCount priorInnerGateCount →
      BooleanWire outerInputCount (outerGateCount + priorInnerGateCount)
  | .input inputBit => (inputMap inputBit).liftRight priorInnerGateCount
  | .gate gateIndex => .gate ⟨outerGateCount + gateIndex.val,
      Nat.add_lt_add_left gateIndex.isLt outerGateCount⟩

/-- Translate one appended gate under an outer input substitution. -/
def BooleanGate.appendTranslate
    {outerInputCount outerGateCount innerInputCount priorInnerGateCount : ℕ}
    (inputMap : Fin innerInputCount → BooleanWire outerInputCount outerGateCount) :
    BooleanGate innerInputCount priorInnerGateCount →
      BooleanGate outerInputCount (outerGateCount + priorInnerGateCount)
  | .constant value => .constant value
  | .nand left right =>
      .nand (left.appendTranslate inputMap) (right.appendTranslate inputMap)

/-- Append a gate DAG after another one while substituting the appended DAG's
primary inputs by wires already available in the outer DAG. -/
def BooleanGateList.appendMapped
    {outerInputCount outerGateCount innerInputCount : ℕ}
    (outer : BooleanGateList outerInputCount outerGateCount)
    (inputMap : Fin innerInputCount → BooleanWire outerInputCount outerGateCount) :
    {innerGateCount : ℕ} → BooleanGateList innerInputCount innerGateCount →
      BooleanGateList outerInputCount (outerGateCount + innerGateCount)
  | 0, .nil => outer
  | _ + 1, .snoc previous gate =>
      BooleanGateList.snoc (outer.appendMapped inputMap previous)
        (gate.appendTranslate inputMap)

/-- Evaluating an old wire after adjoining one gate gives its old value. -/
theorem BooleanGateList.eval_snoc_old
    {inputCount priorGateCount : ℕ}
    (previous : BooleanGateList inputCount priorGateCount)
    (gate : BooleanGate inputCount priorGateCount)
    (inputs : Fin inputCount → Bool) (wire : Fin priorGateCount) :
    (BooleanGateList.snoc previous gate).eval inputs (Fin.castAdd 1 wire) =
      previous.eval inputs wire := by
  simp [BooleanGateList.eval]

/-- The final wire of a freshly adjoined gate evaluates the gate against the
previous gate values. -/
theorem BooleanGateList.eval_snoc_last
    {inputCount priorGateCount : ℕ}
    (previous : BooleanGateList inputCount priorGateCount)
    (gate : BooleanGate inputCount priorGateCount)
    (inputs : Fin inputCount → Bool) :
    (BooleanGateList.snoc previous gate).eval inputs
      ⟨priorGateCount, Nat.lt_succ_self priorGateCount⟩ =
        gate.eval inputs (previous.eval inputs) := by
  simp [BooleanGateList.eval]

/-- Every already-available wire retains its value when a new gate is added. -/
theorem BooleanGateList.eval_snoc_old_wire
    {inputCount priorGateCount : ℕ}
    (previous : BooleanGateList inputCount priorGateCount)
    (gate : BooleanGate inputCount priorGateCount)
    (inputs : Fin inputCount → Bool)
    (wire : BooleanWire inputCount priorGateCount) :
    (wire.liftRight 1).eval inputs
        ((BooleanGateList.snoc previous gate).eval inputs) =
      wire.eval inputs (previous.eval inputs) := by
  cases wire with
  | input inputBit => rfl
  | gate gateIndex =>
      change (BooleanGateList.snoc previous gate).eval inputs
          (Fin.castAdd 1 gateIndex) = previous.eval inputs gateIndex
      exact BooleanGateList.eval_snoc_old previous gate inputs gateIndex

/-- Lifting a wire past a successor number of gates is the same as lifting it
past the old gates and then past the final gate. -/
theorem BooleanWire.liftRight_succ
    {inputCount gateCount : ℕ} (wire : BooleanWire inputCount gateCount)
    (additionalGateCount : ℕ) :
    wire.liftRight (additionalGateCount + 1) =
      (wire.liftRight additionalGateCount).liftRight 1 := by
  cases wire <;> rfl

/-- Translating a gate preserves its truth function when each of its input
wires has the translated value. -/
theorem BooleanGate.eval_appendTranslate
    {outerInputCount outerGateCount innerInputCount priorInnerGateCount : ℕ}
    (inputMap : Fin innerInputCount → BooleanWire outerInputCount outerGateCount)
    (gate : BooleanGate innerInputCount priorInnerGateCount)
    (outerInputs : Fin outerInputCount → Bool)
    (outerValues : Fin outerGateCount → Bool)
    (appendedValues : Fin (outerGateCount + priorInnerGateCount) → Bool)
    (innerValues : Fin priorInnerGateCount → Bool)
    (translatedWireValues : ∀ wire : BooleanWire innerInputCount priorInnerGateCount,
      (wire.appendTranslate inputMap).eval outerInputs appendedValues =
        wire.eval
          (fun inputBit => (inputMap inputBit).eval outerInputs outerValues)
          innerValues) :
    (gate.appendTranslate inputMap).eval outerInputs appendedValues =
      gate.eval
        (fun inputBit => (inputMap inputBit).eval outerInputs outerValues)
        innerValues := by
  cases gate with
  | constant value => rfl
  | nand left right =>
      simp only [BooleanGate.appendTranslate, BooleanGate.eval]
      rw [translatedWireValues left, translatedWireValues right]

/-- Appending a substituted gate list has the semantics of first evaluating
the outer list and then evaluating the inner list on the substituted wires. -/
theorem BooleanGateList.appendMapped_eval
    {outerInputCount outerGateCount innerInputCount : ℕ}
    (outer : BooleanGateList outerInputCount outerGateCount)
    (inputMap : Fin innerInputCount → BooleanWire outerInputCount outerGateCount)
    (outerInputs : Fin outerInputCount → Bool) :
    {innerGateCount : ℕ} → (inner : BooleanGateList innerInputCount innerGateCount) →
      (∀ outerWire : BooleanWire outerInputCount outerGateCount,
        (outerWire.liftRight innerGateCount).eval outerInputs
          ((outer.appendMapped inputMap inner).eval outerInputs) =
            outerWire.eval outerInputs (outer.eval outerInputs)) ∧
      (∀ innerWire : BooleanWire innerInputCount innerGateCount,
        (innerWire.appendTranslate inputMap).eval outerInputs
          ((outer.appendMapped inputMap inner).eval outerInputs) =
            innerWire.eval
              (fun inputBit =>
                (inputMap inputBit).eval outerInputs (outer.eval outerInputs))
              (inner.eval
                (fun inputBit =>
                  (inputMap inputBit).eval outerInputs (outer.eval outerInputs))))
  | 0, .nil => by
      constructor
      · intro outerWire
        cases outerWire <;> rfl
      · intro innerWire
        cases innerWire with
        | input inputBit =>
            change BooleanWire.eval outerInputs (outer.eval outerInputs)
                ((inputMap inputBit).liftRight 0) =
              (inputMap inputBit).eval outerInputs (outer.eval outerInputs)
            cases inputMap inputBit <;> rfl
        | gate gateIndex => exact Fin.elim0 gateIndex
  | priorInnerGateCount + 1, .snoc previous gate => by
      obtain ⟨houter, hinner⟩ :=
        BooleanGateList.appendMapped_eval outer inputMap outerInputs previous
      have houter' : ∀ outerWire : BooleanWire outerInputCount outerGateCount,
          (outerWire.liftRight (priorInnerGateCount + 1)).eval outerInputs
            ((outer.appendMapped inputMap (BooleanGateList.snoc previous gate)).eval outerInputs) =
              outerWire.eval outerInputs (outer.eval outerInputs) := by
        intro outerWire
        change (outerWire.liftRight (priorInnerGateCount + 1)).eval outerInputs
            ((BooleanGateList.snoc (outer.appendMapped inputMap previous)
              (gate.appendTranslate inputMap)).eval outerInputs) =
            outerWire.eval outerInputs (outer.eval outerInputs)
        rw [BooleanWire.liftRight_succ]
        exact
          (BooleanGateList.eval_snoc_old_wire
            (outer.appendMapped inputMap previous)
            (gate.appendTranslate inputMap) outerInputs
            (outerWire.liftRight priorInnerGateCount)).trans (houter outerWire)
      refine ⟨houter', ?_⟩
      intro innerWire
      cases innerWire with
      | input inputBit =>
          simpa [BooleanWire.appendTranslate] using houter' (inputMap inputBit)
      | gate gateIndex =>
          by_cases hprior : gateIndex.val < priorInnerGateCount
          · let oldIndex : Fin priorInnerGateCount := ⟨gateIndex.val, hprior⟩
            let outerOldIndex : Fin (outerGateCount + priorInnerGateCount) :=
              ⟨outerGateCount + gateIndex.val,
                Nat.add_lt_add_left hprior outerGateCount⟩
            have hOld := hinner (BooleanWire.gate oldIndex)
            change
              (BooleanGateList.snoc (outer.appendMapped inputMap previous)
                (gate.appendTranslate inputMap)).eval outerInputs
                  (Fin.castAdd 1 outerOldIndex) =
                (BooleanGateList.snoc previous gate).eval
                  (fun inputBit =>
                    (inputMap inputBit).eval outerInputs (outer.eval outerInputs))
                  (Fin.castAdd 1 oldIndex)
            rw [BooleanGateList.eval_snoc_old,
              BooleanGateList.eval_snoc_old]
            simpa [BooleanWire.appendTranslate] using hOld
          · have hlast : gateIndex.val = priorInnerGateCount := by
              exact Nat.eq_of_lt_succ_of_not_lt gateIndex.isLt hprior
            have hgateIndex : gateIndex =
                ⟨priorInnerGateCount, Nat.lt_succ_self priorInnerGateCount⟩ :=
              Fin.ext hlast
            rw [hgateIndex]
            change
              (BooleanGateList.snoc (outer.appendMapped inputMap previous)
                (gate.appendTranslate inputMap)).eval outerInputs
                  ⟨outerGateCount + priorInnerGateCount,
                    Nat.add_lt_add_left (Nat.lt_succ_self priorInnerGateCount)
                      outerGateCount⟩ =
                (BooleanGateList.snoc previous gate).eval
                  (fun inputBit =>
                    (inputMap inputBit).eval outerInputs (outer.eval outerInputs))
                  ⟨priorInnerGateCount, Nat.lt_succ_self priorInnerGateCount⟩
            rw [BooleanGateList.eval_snoc_last,
              BooleanGateList.eval_snoc_last]
            exact BooleanGate.eval_appendTranslate inputMap gate outerInputs
              (outer.eval outerInputs)
              ((outer.appendMapped inputMap previous).eval outerInputs)
              (previous.eval
                (fun inputBit =>
                  (inputMap inputBit).eval outerInputs (outer.eval outerInputs)))
              hinner

/-- A Boolean circuit is a sequential gate DAG together with designated
output wires. -/
structure BooleanCircuit where
  inputCount : ℕ
  gateCount : ℕ
  outputCount : ℕ
  gates : BooleanGateList inputCount gateCount
  outputs : Fin outputCount → BooleanWire inputCount gateCount

/-- Select any collection of currently available builder wires as the outputs
of an actual Boolean circuit. -/
def BooleanCircuitBuilder.toCircuit
    {inputCount gateCount outputCount : ℕ}
    (builder : BooleanCircuitBuilder inputCount gateCount)
    (outputs : Fin outputCount → Fin (inputCount + gateCount)) : BooleanCircuit where
  inputCount := inputCount
  gateCount := gateCount
  outputCount := outputCount
  gates := builder.toGateList
  outputs := fun output => BooleanWire.ofFin inputCount gateCount (outputs output)

/-- Functional semantics of a Boolean circuit. -/
def BooleanCircuit.eval (circuit : BooleanCircuit) :
    (Fin circuit.inputCount → Bool) → Fin circuit.outputCount → Bool :=
  fun inputs output =>
    (circuit.outputs output).eval inputs (circuit.gates.eval inputs)

/-- Compose an inner circuit after an outer circuit by wiring each inner input
to an already available outer wire.  The result is a single sequential DAG. -/
def BooleanCircuit.compose
    (outer inner : BooleanCircuit)
    (inputMap : Fin inner.inputCount → BooleanWire outer.inputCount outer.gateCount) :
    BooleanCircuit where
  inputCount := outer.inputCount
  gateCount := outer.gateCount + inner.gateCount
  outputCount := inner.outputCount
  gates := outer.gates.appendMapped inputMap inner.gates
  outputs := fun output => (inner.outputs output).appendTranslate inputMap

/-- Composition has exactly the sum of the two literal gate counts. -/
theorem BooleanCircuit.compose_gateCount
    (outer inner : BooleanCircuit)
    (inputMap : Fin inner.inputCount → BooleanWire outer.inputCount outer.gateCount) :
    (outer.compose inner inputMap).gateCount = outer.gateCount + inner.gateCount := rfl

/-- Composition evaluates the outer circuit's gate DAG and then the inner
circuit on the values supplied by the chosen outer wires. -/
theorem BooleanCircuit.eval_compose
    (outer inner : BooleanCircuit)
    (inputMap : Fin inner.inputCount → BooleanWire outer.inputCount outer.gateCount)
    (inputs : Fin outer.inputCount → Bool) (output : Fin inner.outputCount) :
    (outer.compose inner inputMap).eval inputs output =
      inner.eval
        (fun inputBit =>
          (inputMap inputBit).eval inputs (outer.gates.eval inputs))
        output := by
  obtain ⟨_, hinner⟩ :=
    BooleanGateList.appendMapped_eval outer.gates inputMap inputs inner.gates
  simpa [BooleanCircuit.compose, BooleanCircuit.eval] using hinner (inner.outputs output)

/-- A Boolean circuit whose input and output arities are carried in its type.
This typed façade is convenient for building word-level circuits while keeping
the underlying gates and their literal count transparent. -/
structure BooleanCircuitIO (inputCount outputCount : ℕ) where
  gateCount : ℕ
  gates : BooleanGateList inputCount gateCount
  outputs : Fin outputCount → BooleanWire inputCount gateCount

/-- Evaluate an arity-indexed Boolean circuit. -/
def BooleanCircuitIO.eval {inputCount outputCount : ℕ}
    (circuit : BooleanCircuitIO inputCount outputCount) :
    (Fin inputCount → Bool) → Fin outputCount → Bool :=
  fun inputs output => (circuit.outputs output).eval inputs (circuit.gates.eval inputs)

/-- Forget arity indices while retaining the exact underlying gate DAG. -/
def BooleanCircuitIO.toCircuit {inputCount outputCount : ℕ}
    (circuit : BooleanCircuitIO inputCount outputCount) : BooleanCircuit where
  inputCount := inputCount
  gateCount := circuit.gateCount
  outputCount := outputCount
  gates := circuit.gates
  outputs := circuit.outputs

/-- View an existing circuit under specified input and output arities. -/
def BooleanCircuit.toIO {inputCount outputCount : ℕ}
    (circuit : BooleanCircuit)
    (hinput : circuit.inputCount = inputCount)
    (houtput : circuit.outputCount = outputCount) :
    BooleanCircuitIO inputCount outputCount :=
  match hinput, houtput with
  | rfl, rfl =>
      { gateCount := circuit.gateCount
        gates := circuit.gates
        outputs := circuit.outputs }

/-- Reindexing a circuit by proved input and output arities leaves its literal
gate count unchanged. -/
theorem BooleanCircuit.toIO_gateCount {inputCount outputCount : ℕ}
    (circuit : BooleanCircuit)
    (hinput : circuit.inputCount = inputCount)
    (houtput : circuit.outputCount = outputCount) :
    (circuit.toIO hinput houtput).gateCount = circuit.gateCount := by
  unfold BooleanCircuit.toIO
  cases hinput
  cases houtput
  rfl

/-- The arity-indexed view has exactly the original circuit semantics after
the certified input and output index casts. -/
theorem BooleanCircuit.eval_toIO {inputCount outputCount : ℕ}
    (circuit : BooleanCircuit)
    (hinput : circuit.inputCount = inputCount)
    (houtput : circuit.outputCount = outputCount)
    (inputs : Fin inputCount → Bool) (output : Fin outputCount) :
    (circuit.toIO hinput houtput).eval inputs output =
      circuit.eval
        (fun inputBit => inputs (Fin.cast hinput inputBit))
        (Fin.cast houtput.symm output) := by
  unfold BooleanCircuit.toIO
  cases hinput
  cases houtput
  rfl

theorem BooleanCircuitIO.eval_toCircuit {inputCount outputCount : ℕ}
    (circuit : BooleanCircuitIO inputCount outputCount)
    (inputs : Fin inputCount → Bool) (output : Fin outputCount) :
    circuit.toCircuit.eval inputs output = circuit.eval inputs output := rfl

/-- Compose a typed inner circuit after a typed outer gate DAG by supplying
each inner input from an available outer wire. -/
def BooleanCircuitIO.compose
    {outerInputCount outerOutputCount innerInputCount innerOutputCount : ℕ}
    (outer : BooleanCircuitIO outerInputCount outerOutputCount)
    (inner : BooleanCircuitIO innerInputCount innerOutputCount)
    (inputMap : Fin innerInputCount → BooleanWire outerInputCount outer.gateCount) :
    BooleanCircuitIO outerInputCount innerOutputCount where
  gateCount := outer.gateCount + inner.gateCount
  gates := outer.gates.appendMapped inputMap inner.gates
  outputs := fun output => (inner.outputs output).appendTranslate inputMap

theorem BooleanCircuitIO.compose_gateCount
    {outerInputCount outerOutputCount innerInputCount innerOutputCount : ℕ}
    (outer : BooleanCircuitIO outerInputCount outerOutputCount)
    (inner : BooleanCircuitIO innerInputCount innerOutputCount)
    (inputMap : Fin innerInputCount → BooleanWire outerInputCount outer.gateCount) :
    (outer.compose inner inputMap).gateCount = outer.gateCount + inner.gateCount := rfl

theorem BooleanCircuitIO.eval_compose
    {outerInputCount outerOutputCount innerInputCount innerOutputCount : ℕ}
    (outer : BooleanCircuitIO outerInputCount outerOutputCount)
    (inner : BooleanCircuitIO innerInputCount innerOutputCount)
    (inputMap : Fin innerInputCount → BooleanWire outerInputCount outer.gateCount)
    (inputs : Fin outerInputCount → Bool) (output : Fin innerOutputCount) :
    (outer.compose inner inputMap).eval inputs output =
      inner.eval
        (fun inputBit =>
          (inputMap inputBit).eval inputs (outer.gates.eval inputs))
        output := by
  obtain ⟨_, hinner⟩ :=
    BooleanGateList.appendMapped_eval outer.gates inputMap inputs inner.gates
  simpa [BooleanCircuitIO.compose, BooleanCircuitIO.eval] using hinner (inner.outputs output)

/-- The one-gate circuit computing NAND of two input bits. -/
def BooleanCircuit.nand (inputCount : ℕ) (left right : Fin inputCount) :
    BooleanCircuit where
  inputCount := inputCount
  gateCount := 1
  outputCount := 1
  gates := .snoc .nil (.nand (.input left) (.input right))
  outputs := fun _ => .gate 0

/-- The one-gate NAND circuit has its expected truth-table semantics. -/
theorem BooleanCircuit.eval_nand (inputCount : ℕ) (left right : Fin inputCount)
    (inputs : Fin inputCount → Bool) :
    (BooleanCircuit.nand inputCount left right).eval inputs
      ⟨0, by simp [BooleanCircuit.nand]⟩ =
      !(inputs left && inputs right) := by
  rfl

/-- A one-gate Boolean negation circuit. -/
def BooleanCircuit.not (inputCount : ℕ) (input : Fin inputCount) : BooleanCircuit :=
  BooleanCircuit.nand inputCount input input

theorem BooleanCircuit.eval_not (inputCount : ℕ) (input : Fin inputCount)
    (inputs : Fin inputCount → Bool) :
    (BooleanCircuit.not inputCount input).eval inputs
      ⟨0, by simp [BooleanCircuit.not, BooleanCircuit.nand]⟩ = !inputs input := by
  simp [BooleanCircuit.not, BooleanCircuit.eval_nand]

/-- A two-gate Boolean conjunction circuit. -/
def BooleanCircuit.and (inputCount : ℕ) (left right : Fin inputCount) : BooleanCircuit where
  inputCount := inputCount
  gateCount := 2
  outputCount := 1
  gates := .snoc (.snoc .nil (.nand (.input left) (.input right)))
    (.nand (.gate 0) (.gate 0))
  outputs := fun _ => .gate 1

theorem BooleanCircuit.eval_and (inputCount : ℕ) (left right : Fin inputCount)
    (inputs : Fin inputCount → Bool) :
    (BooleanCircuit.and inputCount left right).eval inputs
      ⟨0, by simp [BooleanCircuit.and]⟩ = (inputs left && inputs right) := by
  change Bool.not (Bool.not (inputs left && inputs right) &&
      Bool.not (inputs left && inputs right)) = (inputs left && inputs right)
  cases inputs left <;> cases inputs right <;> rfl

/-- A three-gate Boolean disjunction circuit. -/
def BooleanCircuit.or (inputCount : ℕ) (left right : Fin inputCount) : BooleanCircuit where
  inputCount := inputCount
  gateCount := 3
  outputCount := 1
  gates := .snoc (.snoc (.snoc .nil (.nand (.input left) (.input left)))
    (.nand (.input right) (.input right))) (.nand (.gate 0) (.gate 1))
  outputs := fun _ => .gate 2

theorem BooleanCircuit.eval_or (inputCount : ℕ) (left right : Fin inputCount)
    (inputs : Fin inputCount → Bool) :
    (BooleanCircuit.or inputCount left right).eval inputs
      ⟨0, by simp [BooleanCircuit.or]⟩ = (inputs left || inputs right) := by
  change Bool.not (Bool.not (inputs left && inputs left) &&
      Bool.not (inputs right && inputs right)) = (inputs left || inputs right)
  cases inputs left <;> cases inputs right <;> rfl

/-- A four-gate exclusive-or circuit. -/
def BooleanCircuit.xor (inputCount : ℕ) (left right : Fin inputCount) : BooleanCircuit where
  inputCount := inputCount
  gateCount := 4
  outputCount := 1
  gates := .snoc
    (.snoc
      (.snoc
        (.snoc .nil (.nand (.input left) (.input right)))
        (.nand (.input left) (.gate 0)))
      (.nand (.input right) (.gate 0)))
    (.nand (.gate 1) (.gate 2))
  outputs := fun _ => .gate 3

theorem BooleanCircuit.eval_xor (inputCount : ℕ) (left right : Fin inputCount)
    (inputs : Fin inputCount → Bool) :
    (BooleanCircuit.xor inputCount left right).eval inputs
      ⟨0, by simp [BooleanCircuit.xor]⟩ = (inputs left ^^ inputs right) := by
  change Bool.not (Bool.not (inputs left && Bool.not (inputs left && inputs right)) &&
      Bool.not (inputs right && Bool.not (inputs left && inputs right))) =
    (inputs left ^^ inputs right)
  cases inputs left <;> cases inputs right <;> rfl

/-- A four-gate multiplexer: select the high input when the selector is true,
and the low input otherwise. -/
def BooleanCircuit.mux (inputCount : ℕ)
    (selector high low : Fin inputCount) : BooleanCircuit where
  inputCount := inputCount
  gateCount := 4
  outputCount := 1
  gates := .snoc
    (.snoc
      (.snoc
        (.snoc .nil (.nand (.input selector) (.input high)))
        (.nand (.input selector) (.input selector)))
      (.nand (.gate 1) (.input low)))
    (.nand (.gate 0) (.gate 2))
  outputs := fun _ => .gate 3

theorem BooleanCircuit.eval_mux (inputCount : ℕ)
    (selector high low : Fin inputCount) (inputs : Fin inputCount → Bool) :
    (BooleanCircuit.mux inputCount selector high low).eval inputs
      ⟨0, by simp [BooleanCircuit.mux]⟩ =
        if inputs selector then inputs high else inputs low := by
  change Bool.not (Bool.not (inputs selector && inputs high) &&
      Bool.not (Bool.not (inputs selector && inputs selector) && inputs low)) =
    if inputs selector then inputs high else inputs low
  cases inputs selector <;> cases inputs high <;> cases inputs low <;> rfl

/-- The first newly produced output of a prefix-preserving full adder. -/
def BooleanCircuit.fullAdderSumOutput (prefixCount : ℕ) : Fin (prefixCount + 2) :=
  ⟨prefixCount, Nat.lt_succ_of_le (Nat.le_succ _)⟩

/-- The carry output of a prefix-preserving full adder. -/
def BooleanCircuit.fullAdderCarryOutput (prefixCount : ℕ) : Fin (prefixCount + 2) :=
  ⟨prefixCount + 1, Nat.lt_succ_self _⟩

/-- A nine-gate full adder which also forwards a prefix of Boolean outputs.
Its first three inputs are the two addends and the incoming carry; the
remaining inputs are the forwarded prefix. -/
def BooleanCircuit.fullAdderWithPrefix (prefixCount : ℕ) : BooleanCircuit where
  inputCount := 3 + prefixCount
  gateCount := 9
  outputCount := prefixCount + 2
  gates := .snoc
    (.snoc
      (.snoc
        (.snoc
          (.snoc
            (.snoc
              (.snoc
                (.snoc
                  (.snoc .nil (.nand (.input 0) (.input 1)))
                  (.nand (.input 0) (.gate 0)))
                (.nand (.input 1) (.gate 0)))
              (.nand (.gate 1) (.gate 2)))
            (.nand (.gate 3) (.input 2)))
          (.nand (.gate 3) (.gate 4)))
        (.nand (.input 2) (.gate 4)))
      (.nand (.gate 5) (.gate 6)))
    (.nand (.gate 0) (.gate 4))
  outputs := fun output =>
    if hprefix : output.val < prefixCount then
      .input (Fin.natAdd 3 ⟨output.val, hprefix⟩)
    else if _ : output.val = prefixCount then
      .gate 7
    else
      .gate 8

/-- A forwarded full-adder output is the correspondingly shifted input wire. -/
theorem BooleanCircuit.fullAdderWithPrefix_outputs_old
    (prefixCount : ℕ) (old : Fin prefixCount) :
    (BooleanCircuit.fullAdderWithPrefix prefixCount).outputs (Fin.castAdd 2 old) =
      BooleanWire.input (Fin.natAdd 3 old) := by
  simp [BooleanCircuit.fullAdderWithPrefix, old.isLt]
  apply Fin.ext
  rfl

/-- The designated sum output is the seventh indexed gate of the full adder. -/
theorem BooleanCircuit.fullAdderWithPrefix_outputs_sum
    (prefixCount : ℕ) :
    (BooleanCircuit.fullAdderWithPrefix prefixCount).outputs
      (BooleanCircuit.fullAdderSumOutput prefixCount) =
        BooleanWire.gate ⟨7, by simp [BooleanCircuit.fullAdderWithPrefix]⟩ := by
  simp [BooleanCircuit.fullAdderWithPrefix,
    BooleanCircuit.fullAdderSumOutput]

/-- The designated carry output is the final gate of the full adder. -/
theorem BooleanCircuit.fullAdderWithPrefix_outputs_carry
    (prefixCount : ℕ) :
    (BooleanCircuit.fullAdderWithPrefix prefixCount).outputs
      (BooleanCircuit.fullAdderCarryOutput prefixCount) =
        BooleanWire.gate ⟨8, by simp [BooleanCircuit.fullAdderWithPrefix]⟩ := by
  have hlt : ¬ prefixCount + 1 < prefixCount :=
    Nat.not_lt_of_ge (Nat.le_succ prefixCount)
  simp [BooleanCircuit.fullAdderWithPrefix,
    BooleanCircuit.fullAdderCarryOutput, hlt]

/-- The forwarding outputs of a full adder retain their input values. -/
theorem BooleanCircuit.eval_fullAdderWithPrefix_old
    (prefixCount : ℕ) (old : Fin prefixCount)
    (inputs : Fin (3 + prefixCount) → Bool) :
    (BooleanCircuit.fullAdderWithPrefix prefixCount).eval inputs
      (Fin.castAdd 2 old) =
      inputs (Fin.natAdd 3 old) := by
  change BooleanWire.eval inputs
      ((BooleanCircuit.fullAdderWithPrefix prefixCount).gates.eval inputs)
      ((BooleanCircuit.fullAdderWithPrefix prefixCount).outputs (Fin.castAdd 2 old)) = _
  rw [BooleanCircuit.fullAdderWithPrefix_outputs_old]
  rfl

/-- The full-adder sum output is the exclusive-or of its two addends and
incoming carry. -/
theorem BooleanCircuit.eval_fullAdderWithPrefix_sum
    (prefixCount : ℕ) (inputs : Fin (3 + prefixCount) → Bool) :
    (BooleanCircuit.fullAdderWithPrefix prefixCount).eval inputs
      (BooleanCircuit.fullAdderSumOutput prefixCount) =
        ((inputs 0 ^^ inputs 1) ^^ inputs 2) := by
  change BooleanWire.eval inputs
      ((BooleanCircuit.fullAdderWithPrefix prefixCount).gates.eval inputs)
      ((BooleanCircuit.fullAdderWithPrefix prefixCount).outputs
        (BooleanCircuit.fullAdderSumOutput prefixCount)) = _
  rw [BooleanCircuit.fullAdderWithPrefix_outputs_sum]
  simp only [BooleanCircuit.fullAdderWithPrefix]
  by_cases hzero : inputs 0 = true <;>
    by_cases hone : inputs 1 = true <;>
    by_cases htwo : inputs 2 = true <;>
    simp [BooleanGateList.eval, BooleanGate.eval, BooleanWire.eval,
      hzero, hone, htwo]

/-- The full-adder carry output is set exactly when at least two of the three
input bits are set. -/
theorem BooleanCircuit.eval_fullAdderWithPrefix_carry
    (prefixCount : ℕ) (inputs : Fin (3 + prefixCount) → Bool) :
    (BooleanCircuit.fullAdderWithPrefix prefixCount).eval inputs
      (BooleanCircuit.fullAdderCarryOutput prefixCount) =
        ((inputs 0 && inputs 1) || (inputs 2 && (inputs 0 ^^ inputs 1))) := by
  change BooleanWire.eval inputs
      ((BooleanCircuit.fullAdderWithPrefix prefixCount).gates.eval inputs)
      ((BooleanCircuit.fullAdderWithPrefix prefixCount).outputs
        (BooleanCircuit.fullAdderCarryOutput prefixCount)) = _
  rw [BooleanCircuit.fullAdderWithPrefix_outputs_carry]
  simp only [BooleanCircuit.fullAdderWithPrefix]
  by_cases hzero : inputs 0 = true <;>
    by_cases hone : inputs 1 = true <;>
    by_cases htwo : inputs 2 = true <;>
    simp [BooleanGateList.eval, BooleanGate.eval, BooleanWire.eval,
      hzero, hone, htwo]

/-- Typed presentation of the nine-gate prefix-preserving full adder. -/
def BooleanCircuitIO.fullAdderWithPrefix (prefixCount : ℕ) :
    BooleanCircuitIO (3 + prefixCount) (prefixCount + 2) :=
  (BooleanCircuit.fullAdderWithPrefix prefixCount).toIO rfl rfl

theorem BooleanCircuitIO.fullAdderWithPrefix_gateCount (prefixCount : ℕ) :
    (BooleanCircuitIO.fullAdderWithPrefix prefixCount).gateCount = 9 := rfl

theorem BooleanCircuitIO.eval_fullAdderWithPrefix_old
    (prefixCount : ℕ) (old : Fin prefixCount)
    (inputs : Fin (3 + prefixCount) → Bool) :
    (BooleanCircuitIO.fullAdderWithPrefix prefixCount).eval inputs
      (Fin.castAdd 2 old) = inputs (Fin.natAdd 3 old) :=
  BooleanCircuit.eval_fullAdderWithPrefix_old prefixCount old inputs

theorem BooleanCircuitIO.eval_fullAdderWithPrefix_sum
    (prefixCount : ℕ) (inputs : Fin (3 + prefixCount) → Bool) :
    (BooleanCircuitIO.fullAdderWithPrefix prefixCount).eval inputs
      (BooleanCircuit.fullAdderSumOutput prefixCount) =
        ((inputs 0 ^^ inputs 1) ^^ inputs 2) :=
  BooleanCircuit.eval_fullAdderWithPrefix_sum prefixCount inputs

theorem BooleanCircuitIO.eval_fullAdderWithPrefix_carry
    (prefixCount : ℕ) (inputs : Fin (3 + prefixCount) → Bool) :
    (BooleanCircuitIO.fullAdderWithPrefix prefixCount).eval inputs
      (BooleanCircuit.fullAdderCarryOutput prefixCount) =
        ((inputs 0 && inputs 1) || (inputs 2 && (inputs 0 ^^ inputs 1))) :=
  BooleanCircuit.eval_fullAdderWithPrefix_carry prefixCount inputs

/-- A one-gate false carry wire. -/
def BooleanCircuitIO.zeroCarry (inputCount : ℕ) : BooleanCircuitIO inputCount 1 where
  gateCount := 1
  gates := .snoc .nil (.constant false)
  outputs := fun _ => .gate 0

theorem BooleanCircuitIO.eval_zeroCarry (inputCount : ℕ)
    (inputs : Fin inputCount → Bool) :
    (BooleanCircuitIO.zeroCarry inputCount).eval inputs ⟨0, by simp⟩ = false := by
  rfl

/-- A topologically ordered bank of literal Boolean constants.  This is the
hardware representation of a fixed finite-precision update value; its gates
do not depend on the individual whose prediction is being updated. -/
def BooleanGateList.constantBits (inputCount : ℕ) :
    (width : ℕ) → (Fin width → Bool) → BooleanGateList inputCount width
  | 0, _ => .nil
  | width + 1, bits =>
      .snoc (BooleanGateList.constantBits inputCount width
        (fun old => bits (Fin.castAdd 1 old)))
        (.constant (bits (Fin.last width)))

/-- Every output of a literal constant bank has its specified value. -/
theorem BooleanGateList.eval_constantBits (inputCount width : ℕ)
    (bits : Fin width → Bool) (inputs : Fin inputCount → Bool) (bit : Fin width) :
    (BooleanGateList.constantBits inputCount width bits).eval inputs bit = bits bit := by
  induction width with
  | zero => exact Fin.elim0 bit
  | succ width ih =>
      by_cases hprior : bit.val < width
      · let old : Fin width := ⟨bit.val, hprior⟩
        have hold : bit = Fin.castAdd 1 old := Fin.ext rfl
        rw [hold, BooleanGateList.constantBits, BooleanGateList.eval_snoc_old]
        exact ih (fun old => bits (Fin.castAdd 1 old)) old
      · have hlastValue : bit.val = width :=
          Nat.eq_of_lt_succ_of_not_lt bit.isLt hprior
        have hlast : bit = Fin.last width := Fin.ext hlastValue
        rw [hlast, BooleanGateList.constantBits]
        change
          (BooleanGateList.snoc (BooleanGateList.constantBits inputCount width
            (fun old => bits (Fin.castAdd 1 old)))
            (.constant (bits (Fin.last width)))).eval inputs
              ⟨width, Nat.lt_succ_self width⟩ = bits (Fin.last width)
        rw [BooleanGateList.eval_snoc_last]
        rfl

/-- Supply a fixed Boolean word as gates while preserving a separate primary
input word.  It is the literal hard-coded addend used by one compiled update. -/
def BooleanCircuitIO.constantWord (width : ℕ) (bits : Fin width → Bool) :
    BooleanCircuitIO width width where
  gateCount := width
  gates := BooleanGateList.constantBits width width bits
  outputs := fun bit => .gate bit

/-- A constant-word supplier returns exactly its hard-coded word. -/
theorem BooleanCircuitIO.eval_constantWord (width : ℕ) (bits : Fin width → Bool)
    (inputs : Fin width → Bool) (bit : Fin width) :
    (BooleanCircuitIO.constantWord width bits).eval inputs bit = bits bit := by
  exact BooleanGateList.eval_constantBits width width bits inputs bit

/-- A hard-coded output word over an arbitrary primary-input layout.  The
word is useful as the initializer of a compiled prediction circuit, where
individual-encoding inputs are present but ignored. -/
def BooleanCircuitIO.constantWordOnInputs (inputCount width : ℕ)
    (bits : Fin width → Bool) : BooleanCircuitIO inputCount width where
  gateCount := width
  gates := BooleanGateList.constantBits inputCount width bits
  outputs := fun bit => .gate bit

theorem BooleanCircuitIO.constantWordOnInputs_gateCount (inputCount width : ℕ)
    (bits : Fin width → Bool) :
    (BooleanCircuitIO.constantWordOnInputs inputCount width bits).gateCount = width := rfl

theorem BooleanCircuitIO.eval_constantWordOnInputs (inputCount width : ℕ)
    (bits : Fin width → Bool) (inputs : Fin inputCount → Bool) (bit : Fin width) :
    (BooleanCircuitIO.constantWordOnInputs inputCount width bits).eval inputs bit = bits bit := by
  exact BooleanGateList.eval_constantBits inputCount width bits inputs bit

/-- Wire a variable word and a literal word into the two inputs of the
ripple adder. -/
def BooleanCircuitIO.rippleAdderConstantInputMap (width : ℕ)
    (outer : BooleanCircuitIO width width) :
    Fin (width + width) → BooleanWire width outer.gateCount :=
  Fin.addCases BooleanWire.input outer.outputs

/-- The first half of the constant-adder wiring is the variable input word. -/
theorem BooleanCircuitIO.eval_rippleAdderConstantInputMap_left (width : ℕ)
    (outer : BooleanCircuitIO width width) (inputs : Fin width → Bool)
    (bit : Fin width) :
    (BooleanCircuitIO.rippleAdderConstantInputMap width outer (Fin.castAdd width bit)).eval
      inputs (outer.gates.eval inputs) = inputs bit := by
  simp only [BooleanCircuitIO.rippleAdderConstantInputMap, Fin.addCases_left]
  rfl

/-- The second half of the constant-adder wiring is the supplied literal word. -/
theorem BooleanCircuitIO.eval_rippleAdderConstantInputMap_right (width : ℕ)
    (outer : BooleanCircuitIO width width) (inputs : Fin width → Bool)
    (bit : Fin width) :
    (BooleanCircuitIO.rippleAdderConstantInputMap width outer (Fin.natAdd width bit)).eval
      inputs (outer.gates.eval inputs) = outer.eval inputs bit := by
  unfold BooleanCircuitIO.rippleAdderConstantInputMap
  rw [Fin.addCases_right]
  rfl

/-- The carry output of a ripple-adder prefix after its processed sum bits. -/
def BooleanCircuitIO.rippleCarryOutput (processed : ℕ) : Fin (processed + 1) :=
  Fin.last processed

/-- Wire the next two word bits, the prior carry, and every prior sum bit
into one prefix-preserving full-adder stage. -/
def BooleanCircuitIO.rippleAdderStepInputMap
    (width processed : ℕ) (hprocessed : processed + 1 ≤ width)
    (outer : BooleanCircuitIO (width + width) (processed + 1)) :
    Fin (3 + processed) → BooleanWire (width + width) outer.gateCount :=
  let bitInRange : processed < width := Nat.lt_of_succ_le hprocessed
  fun input =>
    Fin.addCases
      (fun adderInput =>
        Fin.cases
          (.input ⟨processed,
            lt_of_lt_of_le bitInRange (Nat.le_add_right width width)⟩)
          (fun remaining =>
            Fin.cases
              (.input ⟨width + processed,
                Nat.add_lt_add_left bitInRange width⟩)
              (fun final =>
                Fin.cases
                  (outer.outputs (BooleanCircuitIO.rippleCarryOutput processed))
                  (fun impossible => Fin.elim0 impossible) final)
              remaining)
          adderInput)
      (fun old => outer.outputs (Fin.castAdd 1 old))
      input

/-- A ripple-adder prefix over two `width`-bit input words.  Its outputs are
the low-order processed sum bits followed by the carry bit. -/
def BooleanCircuitIO.rippleAdderPrefix (width : ℕ) :
    (processed : ℕ) → processed ≤ width →
      BooleanCircuitIO (width + width) (processed + 1)
  | 0, _ => BooleanCircuitIO.zeroCarry (width + width)
  | processed + 1, hprocessed =>
      let outer := BooleanCircuitIO.rippleAdderPrefix width processed
        (Nat.le_trans (Nat.le_succ processed) hprocessed)
      outer.compose (BooleanCircuitIO.fullAdderWithPrefix processed)
        (BooleanCircuitIO.rippleAdderStepInputMap width processed hprocessed outer)

/-- The ripple-adder prefix contains one false-carry gate and nine gates for
each processed bit. -/
theorem BooleanCircuitIO.rippleAdderPrefix_gateCount (width : ℕ) :
    ∀ (processed : ℕ) (hprocessed : processed ≤ width),
      (BooleanCircuitIO.rippleAdderPrefix width processed hprocessed).gateCount =
        1 + 9 * processed
  | 0, _ => rfl
  | processed + 1, hprocessed => by
      let hprevious : processed ≤ width :=
        Nat.le_trans (Nat.le_succ processed) hprocessed
      rw [BooleanCircuitIO.rippleAdderPrefix]
      rw [BooleanCircuitIO.compose_gateCount,
        BooleanCircuitIO.fullAdderWithPrefix_gateCount]
      rw [BooleanCircuitIO.rippleAdderPrefix_gateCount width processed hprevious]
      omega

/-- The complete `width`-bit ripple adder, including its final carry bit. -/
def BooleanCircuitIO.rippleAdder (width : ℕ) :
    BooleanCircuitIO (width + width) (width + 1) :=
  BooleanCircuitIO.rippleAdderPrefix width width (Nat.le_refl width)

theorem BooleanCircuitIO.rippleAdder_gateCount (width : ℕ) :
    (BooleanCircuitIO.rippleAdder width).gateCount = 1 + 9 * width :=
  BooleanCircuitIO.rippleAdderPrefix_gateCount width width (Nat.le_refl width)

/-- The concrete ripple-adder circuit for adding one variable word to one
hard-coded word. -/
def BooleanCircuitIO.rippleAdderWithConstant (width : ℕ) (bits : Fin width → Bool) :
    BooleanCircuitIO width (width + 1) :=
  (BooleanCircuitIO.constantWord width bits).compose (BooleanCircuitIO.rippleAdder width)
    (BooleanCircuitIO.rippleAdderConstantInputMap width
      (BooleanCircuitIO.constantWord width bits))

/-- The literal constant bank and the ripple arithmetic use exactly
`10 * width + 1` NAND/constant gates. -/
theorem BooleanCircuitIO.rippleAdderWithConstant_gateCount (width : ℕ)
    (bits : Fin width → Bool) :
    (BooleanCircuitIO.rippleAdderWithConstant width bits).gateCount = 10 * width + 1 := by
  rw [BooleanCircuitIO.rippleAdderWithConstant, BooleanCircuitIO.compose_gateCount,
    BooleanCircuitIO.rippleAdder_gateCount]
  change width + (1 + 9 * width) = 10 * width + 1
  omega

/-- An arity-indexed circuit with no outputs and no gates.  It is useful as
the left side of a composition that merely rewires a small circuit. -/
def BooleanCircuitIO.empty (inputCount : ℕ) : BooleanCircuitIO inputCount 0 where
  gateCount := 0
  gates := .nil
  outputs := Fin.elim0

/-- Typed two-input conjunction. -/
def BooleanCircuitIO.and : BooleanCircuitIO 2 1 :=
  (BooleanCircuit.and 2 0 1).toIO rfl rfl

theorem BooleanCircuitIO.and_gateCount : BooleanCircuitIO.and.gateCount = 2 := rfl

theorem BooleanCircuitIO.eval_and (inputs : Fin 2 → Bool) :
    BooleanCircuitIO.and.eval inputs 0 = (inputs 0 && inputs 1) :=
  BooleanCircuit.eval_and 2 0 1 inputs

/-- Typed three-input multiplexer.  The first input is the selector, followed
by the high and low data inputs. -/
def BooleanCircuitIO.mux : BooleanCircuitIO 3 1 :=
  (BooleanCircuit.mux 3 0 1 2).toIO rfl rfl

theorem BooleanCircuitIO.mux_gateCount : BooleanCircuitIO.mux.gateCount = 4 := rfl

theorem BooleanCircuitIO.eval_mux (inputs : Fin 3 → Bool) :
    BooleanCircuitIO.mux.eval inputs 0 =
      if inputs 0 then inputs 1 else inputs 2 :=
  BooleanCircuit.eval_mux 3 0 1 2 inputs

/-- The three non-prefix inputs of a prefix-preserving multiplexer stage. -/
def BooleanCircuitIO.muxPrefixInputMap (prefixCount : ℕ) :
    Fin 3 → BooleanWire (3 + prefixCount) 0 :=
  Fin.cases (.input 0)
    (fun remaining => Fin.cases (.input 1) (fun _ => .input 2) remaining)

/-- Apply a multiplexer to three designated inputs while forwarding a prefix
of already-computed word bits. -/
def BooleanCircuitIO.muxWithPrefix (prefixCount : ℕ) :
    BooleanCircuitIO (3 + prefixCount) (prefixCount + 1) :=
  let composed := (BooleanCircuitIO.empty (3 + prefixCount)).compose
    BooleanCircuitIO.mux (BooleanCircuitIO.muxPrefixInputMap prefixCount)
  { gateCount := composed.gateCount
    gates := composed.gates
    outputs := fun output =>
      if hprefix : output.val < prefixCount then
        .input (Fin.natAdd 3 ⟨output.val, hprefix⟩)
      else
        composed.outputs 0 }

theorem BooleanCircuitIO.muxWithPrefix_gateCount (prefixCount : ℕ) :
    (BooleanCircuitIO.muxWithPrefix prefixCount).gateCount = 4 := by
  change 0 + 4 = 4
  rfl

/-- Prefix outputs of a multiplexer stage are forwarded unchanged. -/
theorem BooleanCircuitIO.eval_muxWithPrefix_old (prefixCount : ℕ)
    (old : Fin prefixCount) (inputs : Fin (3 + prefixCount) → Bool) :
    (BooleanCircuitIO.muxWithPrefix prefixCount).eval inputs
      (Fin.castAdd 1 old) = inputs (Fin.natAdd 3 old) := by
  unfold BooleanCircuitIO.muxWithPrefix
  dsimp
  simp [BooleanCircuitIO.eval, old.isLt]
  change inputs ⟨3 + old.val, by omega⟩ = inputs (Fin.natAdd 3 old)
  congr 1

/-- The last output of a multiplexer stage has the usual mux truth table. -/
theorem BooleanCircuitIO.eval_muxWithPrefix_last (prefixCount : ℕ)
    (inputs : Fin (3 + prefixCount) → Bool) :
    (BooleanCircuitIO.muxWithPrefix prefixCount).eval inputs
      (Fin.last prefixCount) =
        if inputs 0 then inputs 1 else inputs 2 := by
  unfold BooleanCircuitIO.muxWithPrefix
  dsimp
  have hnot : ¬ prefixCount < prefixCount := Nat.lt_irrefl _
  simp only [BooleanCircuitIO.eval]
  simp only [Fin.last]
  rw [dif_neg hnot]
  change
    ((BooleanCircuitIO.empty (3 + prefixCount)).compose BooleanCircuitIO.mux
      (BooleanCircuitIO.muxPrefixInputMap prefixCount)).eval inputs 0 = _
  rw [BooleanCircuitIO.eval_compose, BooleanCircuitIO.eval_mux]
  rfl

/-- Wire one shared enable bit, the next updated-word bit, the next old-word
bit, and the already selected prefix into a multiplexing stage. -/
def BooleanCircuitIO.muxWordStepInputMap
    (width processed : ℕ) (hprocessed : processed + 1 ≤ width)
    (outer : BooleanCircuitIO (width + width + 1) processed) :
    Fin (3 + processed) → BooleanWire (width + width + 1) outer.gateCount :=
  let bitInRange : processed < width := Nat.lt_of_succ_le hprocessed
  Fin.addCases
    (fun muxInput =>
      Fin.cases
        (.input (Fin.last (width + width)))
        (fun remaining =>
          Fin.cases
            (.input ⟨width + processed,
              lt_of_lt_of_le (Nat.add_lt_add_left bitInRange width)
                (Nat.le_succ (width + width))⟩)
            (fun _ => .input ⟨processed,
              lt_of_lt_of_le bitInRange
                (Nat.le_trans (Nat.le_add_right width width)
                  (Nat.le_succ _))⟩)
            remaining)
        muxInput)
    outer.outputs

/-- A prefix of a conditional word: every processed bit is the updated bit
when the common enable input is true and the old bit otherwise. -/
def BooleanCircuitIO.muxWordPrefix (width : ℕ) :
    (processed : ℕ) → processed ≤ width →
      BooleanCircuitIO (width + width + 1) processed
  | 0, _ => BooleanCircuitIO.empty (width + width + 1)
  | processed + 1, hprocessed =>
      let hprevious : processed ≤ width :=
        Nat.le_trans (Nat.le_succ processed) hprocessed
      let outer := BooleanCircuitIO.muxWordPrefix width processed hprevious
      outer.compose (BooleanCircuitIO.muxWithPrefix processed)
        (BooleanCircuitIO.muxWordStepInputMap width processed hprocessed outer)

/-- Selecting between two words uses exactly four gates per word bit. -/
theorem BooleanCircuitIO.muxWordPrefix_gateCount (width : ℕ) :
    ∀ (processed : ℕ) (hprocessed : processed ≤ width),
      (BooleanCircuitIO.muxWordPrefix width processed hprocessed).gateCount = 4 * processed
  | 0, _ => by
      change 0 = 4 * 0
      simp
  | processed + 1, hprocessed => by
      let hprevious : processed ≤ width :=
        Nat.le_trans (Nat.le_succ processed) hprocessed
      rw [BooleanCircuitIO.muxWordPrefix,
        BooleanCircuitIO.compose_gateCount,
        BooleanCircuitIO.muxWithPrefix_gateCount,
        BooleanCircuitIO.muxWordPrefix_gateCount width processed hprevious]
      omega

/-- Every completed conditional-word output has the ordinary multiplexer
semantics at its corresponding word position. -/
theorem BooleanCircuitIO.eval_muxWordPrefix (width : ℕ)
    (inputs : Fin (width + width + 1) → Bool) :
    ∀ (processed : ℕ) (hprocessed : processed ≤ width) (bit : Fin processed),
      (BooleanCircuitIO.muxWordPrefix width processed hprocessed).eval inputs bit =
        if inputs (Fin.last (width + width)) then
          inputs ⟨width + bit.val,
            lt_of_lt_of_le
              (Nat.add_lt_add_left (lt_of_lt_of_le bit.isLt hprocessed) width)
              (Nat.le_succ (width + width))⟩
        else
          inputs ⟨bit.val,
            lt_of_lt_of_le (lt_of_lt_of_le bit.isLt hprocessed)
              (Nat.le_trans (Nat.le_add_right width width) (Nat.le_succ _))⟩
  | 0, _, bit => Fin.elim0 bit
  | processed + 1, hprocessed, bit => by
      let hprevious : processed ≤ width :=
        Nat.le_trans (Nat.le_succ processed) hprocessed
      let outer := BooleanCircuitIO.muxWordPrefix width processed hprevious
      let inputMap := BooleanCircuitIO.muxWordStepInputMap
        width processed hprocessed outer
      change (outer.compose (BooleanCircuitIO.muxWithPrefix processed)
        inputMap).eval inputs bit = _
      by_cases hprior : bit.val < processed
      · let old : Fin processed := ⟨bit.val, hprior⟩
        have hold : bit = Fin.castAdd 1 old := Fin.ext rfl
        rw [hold, BooleanCircuitIO.eval_compose,
          BooleanCircuitIO.eval_muxWithPrefix_old]
        unfold inputMap BooleanCircuitIO.muxWordStepInputMap
        rw [Fin.addCases_right]
        change outer.eval inputs old = _
        rw [BooleanCircuitIO.eval_muxWordPrefix width inputs processed hprevious old]
        split <;> congr 1
      · have hlastValue : bit.val = processed :=
          Nat.eq_of_lt_succ_of_not_lt bit.isLt hprior
        have hlast : bit = Fin.last processed := Fin.ext hlastValue
        rw [hlast, BooleanCircuitIO.eval_compose,
          BooleanCircuitIO.eval_muxWithPrefix_last]
        unfold inputMap BooleanCircuitIO.muxWordStepInputMap
        have hzero : (0 : Fin (3 + processed)) =
            Fin.castAdd processed (0 : Fin 3) := by
          apply Fin.ext
          rfl
        have hone : (1 : Fin (3 + processed)) =
            Fin.castAdd processed (1 : Fin 3) := by
          apply Fin.ext
          change 1 % (3 + processed) = 1
          exact Nat.mod_eq_of_lt (by omega)
        have htwo : (2 : Fin (3 + processed)) =
            Fin.castAdd processed (2 : Fin 3) := by
          apply Fin.ext
          change 2 % (3 + processed) = 2
          exact Nat.mod_eq_of_lt (by omega)
        rw [hzero, hone, htwo]
        simp only [Fin.addCases_left]
        have honeThree : (1 : Fin 3) = Fin.succ (0 : Fin 2) := by decide
        have htwoThree : (2 : Fin 3) = Fin.succ (Fin.succ (0 : Fin 1)) := by decide
        rw [honeThree, htwoThree]
        simp only [Fin.cases_zero, Fin.cases_succ]
        change
          (if inputs (Fin.last (width + width)) then
            inputs ⟨width + processed, _⟩ else inputs ⟨processed, _⟩) = _
        split <;> congr 1

/-- The full `width`-bit conditional word circuit.  Its inputs are an old
word, an updated word, and one final enable bit, in that order. -/
def BooleanCircuitIO.muxWord (width : ℕ) :
    BooleanCircuitIO (width + width + 1) width :=
  BooleanCircuitIO.muxWordPrefix width width (Nat.le_refl width)

theorem BooleanCircuitIO.muxWord_gateCount (width : ℕ) :
    (BooleanCircuitIO.muxWord width).gateCount = 4 * width :=
  BooleanCircuitIO.muxWordPrefix_gateCount width width (Nat.le_refl width)

/-- Each full conditional-word output selects its corresponding updated or
old word bit according to the shared final enable input. -/
theorem BooleanCircuitIO.eval_muxWord (width : ℕ)
    (inputs : Fin (width + width + 1) → Bool) (bit : Fin width) :
    (BooleanCircuitIO.muxWord width).eval inputs bit =
      if inputs (Fin.last (width + width)) then
        inputs ⟨width + bit.val,
          lt_of_lt_of_le (Nat.add_lt_add_left bit.isLt width)
            (Nat.le_succ (width + width))⟩
      else
        inputs ⟨bit.val,
          lt_of_lt_of_le bit.isLt
            (Nat.le_trans (Nat.le_add_right width width) (Nat.le_succ _))⟩ := by
  exact BooleanCircuitIO.eval_muxWordPrefix width inputs width
    (Nat.le_refl width) bit

/-- Run a word circuit and a one-bit predicate on the same inputs, retaining
both results.  The word gates come first, so the predicate may be appended as
one genuine topological DAG while the old word outputs remain available for a
subsequent conditional-word mux. -/
def BooleanCircuitIO.pairWordPredicate {inputCount width : ℕ}
    (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1) :
    BooleanCircuitIO inputCount (width + 1) :=
  let composed := word.compose predicate (fun inputBit => BooleanWire.input inputBit)
  { gateCount := composed.gateCount
    gates := composed.gates
    outputs := Fin.lastCases (composed.outputs 0)
      (fun wordBit => (word.outputs wordBit).liftRight predicate.gateCount) }

/-- Pairing a word and predicate appends exactly the predicate's gates. -/
theorem BooleanCircuitIO.pairWordPredicate_gateCount {inputCount width : ℕ}
    (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1) :
    (word.pairWordPredicate predicate).gateCount = word.gateCount + predicate.gateCount := rfl

/-- The word outputs of a paired word/predicate circuit retain their original
semantics. -/
theorem BooleanCircuitIO.eval_pairWordPredicate_word {inputCount width : ℕ}
    (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1)
    (inputs : Fin inputCount → Bool) (wordBit : Fin width) :
    (word.pairWordPredicate predicate).eval inputs (Fin.castSucc wordBit) =
      word.eval inputs wordBit := by
  unfold BooleanCircuitIO.pairWordPredicate
  simp only [BooleanCircuitIO.eval]
  rw [Fin.lastCases_castSucc]
  exact (BooleanGateList.appendMapped_eval word.gates
    (fun inputBit => BooleanWire.input inputBit) inputs predicate.gates).1 (word.outputs wordBit)

/-- The final output of a paired word/predicate circuit is the predicate. -/
theorem BooleanCircuitIO.eval_pairWordPredicate_predicate {inputCount width : ℕ}
    (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1)
    (inputs : Fin inputCount → Bool) :
    (word.pairWordPredicate predicate).eval inputs (Fin.last width) =
      predicate.eval inputs 0 := by
  unfold BooleanCircuitIO.pairWordPredicate
  simp only [BooleanCircuitIO.eval]
  rw [Fin.lastCases_last]
  exact BooleanCircuitIO.eval_compose word predicate
    (fun inputBit => BooleanWire.input inputBit) inputs 0

/-- Append one literal constant word after a word/predicate pair.  The output
is the new word, but the earlier word and predicate wires remain available in
the underlying DAG for a final mux. -/
def BooleanCircuitIO.pairWordPredicateWithConstant {inputCount width : ℕ}
    (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1) (bits : Fin width → Bool) :
    BooleanCircuitIO inputCount width :=
  (word.pairWordPredicate predicate).compose
    (BooleanCircuitIO.constantWordOnInputs (width + 1) width bits)
    (fun inputBit => (word.pairWordPredicate predicate).outputs inputBit)

/-- Appending the literal replacement word costs exactly one constant gate per
word bit. -/
theorem BooleanCircuitIO.pairWordPredicateWithConstant_gateCount
    {inputCount width : ℕ} (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1) (bits : Fin width → Bool) :
    (word.pairWordPredicateWithConstant predicate bits).gateCount =
      word.gateCount + predicate.gateCount + width := by
  rw [BooleanCircuitIO.pairWordPredicateWithConstant,
    BooleanCircuitIO.compose_gateCount,
    BooleanCircuitIO.pairWordPredicate_gateCount,
    BooleanCircuitIO.constantWordOnInputs_gateCount]

/-- The appended constant word has its declared value independently of the
program input. -/
theorem BooleanCircuitIO.eval_pairWordPredicateWithConstant
    {inputCount width : ℕ} (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1) (bits : Fin width → Bool)
    (inputs : Fin inputCount → Bool) (wordBit : Fin width) :
    (word.pairWordPredicateWithConstant predicate bits).eval inputs wordBit = bits wordBit := by
  rw [BooleanCircuitIO.pairWordPredicateWithConstant,
    BooleanCircuitIO.eval_compose]
  exact BooleanCircuitIO.eval_constantWordOnInputs (width + 1) width bits _ wordBit

/-- Wire the old word, the appended literal word, and the paired predicate
into one `muxWord`. -/
def BooleanCircuitIO.conditionalConstantWordInputMap {inputCount width : ℕ}
    (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1) (bits : Fin width → Bool) :
    Fin (width + width + 1) →
      BooleanWire inputCount
        (word.pairWordPredicateWithConstant predicate bits).gateCount :=
  let paired := word.pairWordPredicate predicate
  fun input =>
    if hold : input.val < width then
      (paired.outputs ⟨input.val, lt_trans hold (Nat.lt_succ_self width)⟩).liftRight width
    else if hconstant : input.val < width + width then
      (word.pairWordPredicateWithConstant predicate bits).outputs
        ⟨input.val - width,
          Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt hold) hconstant⟩
    else
      (paired.outputs (Fin.last width)).liftRight width

/-- The old input half of a conditional replacement mux reads the original
word circuit. -/
theorem BooleanCircuitIO.eval_conditionalConstantWordInputMap_old
    {inputCount width : ℕ} (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1) (bits : Fin width → Bool)
    (inputs : Fin inputCount → Bool) (wordBit : Fin width) :
    (word.conditionalConstantWordInputMap predicate bits
      (Fin.castAdd (width + 1) wordBit)).eval inputs
      ((word.pairWordPredicateWithConstant predicate bits).gates.eval inputs) =
        word.eval inputs wordBit := by
  unfold BooleanCircuitIO.conditionalConstantWordInputMap
  simp
  have hpair := BooleanGateList.appendMapped_eval
    (word.pairWordPredicate predicate).gates
    (fun inputBit => (word.pairWordPredicate predicate).outputs inputBit) inputs
    (BooleanCircuitIO.constantWordOnInputs (width + 1) width bits).gates
  change
    (((word.pairWordPredicate predicate).outputs (Fin.castSucc wordBit)).liftRight width).eval
      inputs ((word.pairWordPredicateWithConstant predicate bits).gates.eval inputs) = _
  unfold BooleanCircuitIO.pairWordPredicateWithConstant
  exact (hpair.1 ((word.pairWordPredicate predicate).outputs (Fin.castSucc wordBit))).trans
    (BooleanCircuitIO.eval_pairWordPredicate_word word predicate inputs wordBit)

/-- The updated input half of a conditional replacement mux is its declared
literal word. -/
theorem BooleanCircuitIO.eval_conditionalConstantWordInputMap_updated
    {inputCount width : ℕ} (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1) (bits : Fin width → Bool)
    (inputs : Fin inputCount → Bool) (wordBit : Fin width) :
    (word.conditionalConstantWordInputMap predicate bits
      (Fin.castAdd 1 (Fin.natAdd width wordBit))).eval inputs
      ((word.pairWordPredicateWithConstant predicate bits).gates.eval inputs) = bits wordBit := by
  unfold BooleanCircuitIO.conditionalConstantWordInputMap
  have hnotOld : ¬ (Fin.castAdd 1 (Fin.natAdd width wordBit)).val < width := by
    change ¬ width + wordBit.val < width
    omega
  have hnotInner : ¬ wordBit.val + width < width := by omega
  simp [hnotInner]
  change (word.pairWordPredicateWithConstant predicate bits).eval inputs wordBit = _
  exact BooleanCircuitIO.eval_pairWordPredicateWithConstant word predicate bits inputs wordBit

/-- The final input of a conditional replacement mux evaluates the paired
predicate. -/
theorem BooleanCircuitIO.eval_conditionalConstantWordInputMap_enable
    {inputCount width : ℕ} (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1) (bits : Fin width → Bool)
    (inputs : Fin inputCount → Bool) :
    (word.conditionalConstantWordInputMap predicate bits (Fin.last (width + width))).eval
      inputs ((word.pairWordPredicateWithConstant predicate bits).gates.eval inputs) =
        predicate.eval inputs 0 := by
  unfold BooleanCircuitIO.conditionalConstantWordInputMap
  have hnotOld : ¬ (width + width : ℕ) < width := by omega
  simp [hnotOld]
  have hpair := BooleanGateList.appendMapped_eval
    (word.pairWordPredicate predicate).gates
    (fun inputBit => (word.pairWordPredicate predicate).outputs inputBit) inputs
    (BooleanCircuitIO.constantWordOnInputs (width + 1) width bits).gates
  change
    (((word.pairWordPredicate predicate).outputs (Fin.last width)).liftRight width).eval
      inputs ((word.pairWordPredicateWithConstant predicate bits).gates.eval inputs) = _
  unfold BooleanCircuitIO.pairWordPredicateWithConstant
  exact (hpair.1 ((word.pairWordPredicate predicate).outputs (Fin.last width))).trans
    (BooleanCircuitIO.eval_pairWordPredicate_predicate word predicate inputs)

/-- Conditionally replace every bit of a word by a hard-coded word.  This is
the finite lookup primitive used to implement the post-processing of a
compiled calibration predictor. -/
def BooleanCircuitIO.conditionalConstantWord {inputCount width : ℕ}
    (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1) (bits : Fin width → Bool) :
    BooleanCircuitIO inputCount width :=
  (word.pairWordPredicateWithConstant predicate bits).compose
    (BooleanCircuitIO.muxWord width)
    (word.conditionalConstantWordInputMap predicate bits)

/-- One conditional literal-word replacement adds its predicate, one literal
word, and a four-gate-per-bit mux to the original word circuit. -/
theorem BooleanCircuitIO.conditionalConstantWord_gateCount
    {inputCount width : ℕ} (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1) (bits : Fin width → Bool) :
    (word.conditionalConstantWord predicate bits).gateCount =
      word.gateCount + predicate.gateCount + 5 * width := by
  rw [BooleanCircuitIO.conditionalConstantWord,
    BooleanCircuitIO.compose_gateCount,
    BooleanCircuitIO.pairWordPredicateWithConstant_gateCount,
    BooleanCircuitIO.muxWord_gateCount]
  omega

/-- A conditional literal-word replacement takes the new literal word exactly
when the predicate is true, and otherwise preserves the original word. -/
theorem BooleanCircuitIO.eval_conditionalConstantWord
    {inputCount width : ℕ} (word : BooleanCircuitIO inputCount width)
    (predicate : BooleanCircuitIO inputCount 1) (bits : Fin width → Bool)
    (inputs : Fin inputCount → Bool) (wordBit : Fin width) :
    (word.conditionalConstantWord predicate bits).eval inputs wordBit =
      if predicate.eval inputs 0 then bits wordBit else word.eval inputs wordBit := by
  rw [BooleanCircuitIO.conditionalConstantWord, BooleanCircuitIO.eval_compose,
    BooleanCircuitIO.eval_muxWord]
  rw [BooleanCircuitIO.eval_conditionalConstantWordInputMap_enable]
  split
  · have hindex :
        (⟨width + wordBit.val,
          lt_of_lt_of_le (Nat.add_lt_add_left wordBit.isLt width)
            (Nat.le_succ (width + width))⟩ : Fin (width + width + 1)) =
          Fin.castAdd 1 (Fin.natAdd width wordBit) := Fin.ext rfl
    rw [hindex]
    exact BooleanCircuitIO.eval_conditionalConstantWordInputMap_updated
      word predicate bits inputs wordBit
  · have hindex :
        (⟨wordBit.val,
          lt_of_lt_of_le wordBit.isLt
            (Nat.le_trans (Nat.le_add_right width width) (Nat.le_succ _))⟩ :
          Fin (width + width + 1)) = Fin.castAdd (width + 1) wordBit := Fin.ext rfl
    rw [hindex]
    exact BooleanCircuitIO.eval_conditionalConstantWordInputMap_old
      word predicate bits inputs wordBit

/-- Wire an old primary word, an already-computed updated word, and the final
primary enable bit into `muxWord`.  This is the standard final stage of a
conditional fixed-point update. -/
def BooleanCircuitIO.oldUpdatedEnableMuxInputMap (width : ℕ)
    (outer : BooleanCircuitIO (width + 1) width) :
    Fin (width + width + 1) → BooleanWire (width + 1) outer.gateCount :=
  fun input =>
    if hold : input.val < width then
      .input ⟨input.val, lt_of_lt_of_le hold (Nat.le_succ width)⟩
    else if hupdated : input.val < width + width then
      outer.outputs ⟨input.val - width,
        Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt hold) hupdated⟩
    else
      .input (Fin.last width)

/-- The old half of the update mux wiring is the corresponding primary bit. -/
theorem BooleanCircuitIO.eval_oldUpdatedEnableMuxInputMap_old (width : ℕ)
    (outer : BooleanCircuitIO (width + 1) width)
    (inputs : Fin (width + 1) → Bool) (bit : Fin width) :
    (BooleanCircuitIO.oldUpdatedEnableMuxInputMap width outer
      (Fin.castAdd (width + 1) bit)).eval inputs (outer.gates.eval inputs) =
        inputs (Fin.castAdd 1 bit) := by
  unfold BooleanCircuitIO.oldUpdatedEnableMuxInputMap
  have hinput : Fin.castAdd (width + 1) bit =
      (⟨bit.val,
        lt_of_lt_of_le bit.isLt
          (Nat.le_trans (Nat.le_add_right width width) (Nat.le_succ _))⟩ :
        Fin (width + width + 1)) := by
    apply Fin.ext
    rfl
  rw [hinput]
  rw [dif_pos bit.isLt]
  rfl

/-- The updated half of the mux wiring is the corresponding output of the
preceding circuit. -/
theorem BooleanCircuitIO.eval_oldUpdatedEnableMuxInputMap_updated (width : ℕ)
    (outer : BooleanCircuitIO (width + 1) width)
    (inputs : Fin (width + 1) → Bool) (bit : Fin width) :
    (BooleanCircuitIO.oldUpdatedEnableMuxInputMap width outer
      ⟨width + bit.val,
        lt_of_lt_of_le (Nat.add_lt_add_left bit.isLt width)
          (Nat.le_succ (width + width))⟩).eval inputs (outer.gates.eval inputs) =
        outer.eval inputs bit := by
  unfold BooleanCircuitIO.oldUpdatedEnableMuxInputMap
  have hnotOld : ¬ width + bit.val < width := by omega
  have hupdated : width + bit.val < width + width := by
    exact Nat.add_lt_add_left bit.isLt width
  rw [dif_neg hnotOld, dif_pos hupdated]
  congr 2
  apply Fin.ext
  change (width + bit.val) - width = bit.val
  omega

/-- The final mux input is the primary enable bit. -/
theorem BooleanCircuitIO.eval_oldUpdatedEnableMuxInputMap_enable (width : ℕ)
    (outer : BooleanCircuitIO (width + 1) width)
    (inputs : Fin (width + 1) → Bool) :
    (BooleanCircuitIO.oldUpdatedEnableMuxInputMap width outer
      (Fin.last (width + width))).eval inputs (outer.gates.eval inputs) =
        inputs (Fin.last width) := by
  unfold BooleanCircuitIO.oldUpdatedEnableMuxInputMap
  have hlast : Fin.last (width + width) =
      (⟨width + width, Nat.lt_succ_self _⟩ : Fin (width + width + 1)) :=
    Fin.ext rfl
  rw [hlast]
  have hnotOld : ¬ width + width < width := by omega
  have hnotUpdated : ¬ width + width < width + width := Nat.lt_irrefl _
  rw [dif_neg hnotOld, dif_neg hnotUpdated]
  rfl

/-- Lift a word circuit to an input layout containing the word followed by one
extra control bit.  The control bit is intentionally left untouched for a
later conditional-word stage. -/
def BooleanCircuitIO.liftWordWithEnable (width : ℕ)
    (circuit : BooleanCircuitIO width width) : BooleanCircuitIO (width + 1) width :=
  (BooleanCircuitIO.empty (width + 1)).compose circuit
    (fun bit => .input (Fin.castAdd 1 bit))

theorem BooleanCircuitIO.liftWordWithEnable_gateCount (width : ℕ)
    (circuit : BooleanCircuitIO width width) :
    (BooleanCircuitIO.liftWordWithEnable width circuit).gateCount = circuit.gateCount := by
  change 0 + circuit.gateCount = circuit.gateCount
  exact Nat.zero_add _

theorem BooleanCircuitIO.eval_liftWordWithEnable (width : ℕ)
    (circuit : BooleanCircuitIO width width)
    (inputs : Fin (width + 1) → Bool) (bit : Fin width) :
    (BooleanCircuitIO.liftWordWithEnable width circuit).eval inputs bit =
      circuit.eval (fun wordBit => inputs (Fin.castAdd 1 wordBit)) bit := by
  rw [BooleanCircuitIO.liftWordWithEnable, BooleanCircuitIO.eval_compose]
  rfl

/-- Typed two-input disjunction. -/
def BooleanCircuitIO.or : BooleanCircuitIO 2 1 :=
  (BooleanCircuit.or 2 0 1).toIO rfl rfl

theorem BooleanCircuitIO.or_gateCount : BooleanCircuitIO.or.gateCount = 3 := rfl

theorem BooleanCircuitIO.eval_or (inputs : Fin 2 → Bool) :
    BooleanCircuitIO.or.eval inputs 0 = (inputs 0 || inputs 1) :=
  BooleanCircuit.eval_or 2 0 1 inputs

/-- The two non-prefix inputs of a prefix-preserving binary gate: the next
word bit is first and the shared selector bit is second. -/
def BooleanCircuitIO.binaryPrefixInputMap (prefixCount : ℕ) :
    Fin 2 → BooleanWire (2 + prefixCount) 0 :=
  Fin.cases
    (.input 0)
    (fun _ => .input 1)

/-- Apply any two-input, one-output circuit to two designated inputs while
forwarding a prefix of outputs. -/
def BooleanCircuitIO.binaryWithPrefix (prefixCount : ℕ)
    (binary : BooleanCircuitIO 2 1) :
    BooleanCircuitIO (2 + prefixCount) (prefixCount + 1) :=
  let composed := (BooleanCircuitIO.empty (2 + prefixCount)).compose binary
    (BooleanCircuitIO.binaryPrefixInputMap prefixCount)
  { gateCount := composed.gateCount
    gates := composed.gates
    outputs := fun output =>
      if hprefix : output.val < prefixCount then
        .input (Fin.natAdd 2 ⟨output.val, hprefix⟩)
      else
        composed.outputs 0 }

/-- A prefix-preserving binary stage has exactly the gates of its binary
component. -/
theorem BooleanCircuitIO.binaryWithPrefix_gateCount (prefixCount : ℕ)
    (binary : BooleanCircuitIO 2 1) :
    (BooleanCircuitIO.binaryWithPrefix prefixCount binary).gateCount = binary.gateCount := by
  change 0 + binary.gateCount = binary.gateCount
  exact Nat.zero_add _

/-- Prefix outputs of a binary stage are passed through unchanged. -/
theorem BooleanCircuitIO.eval_binaryWithPrefix_old (prefixCount : ℕ)
    (binary : BooleanCircuitIO 2 1) (old : Fin prefixCount)
    (inputs : Fin (2 + prefixCount) → Bool) :
    (BooleanCircuitIO.binaryWithPrefix prefixCount binary).eval inputs
      (Fin.castAdd 1 old) = inputs (Fin.natAdd 2 old) := by
  unfold BooleanCircuitIO.binaryWithPrefix
  dsimp
  simp [BooleanCircuitIO.eval, old.isLt]
  change inputs ⟨2 + old.val, by omega⟩ = inputs (Fin.natAdd 2 old)
  congr 1

/-- The final output of a binary stage applies the component circuit to its
two designated inputs. -/
theorem BooleanCircuitIO.eval_binaryWithPrefix_last (prefixCount : ℕ)
    (binary : BooleanCircuitIO 2 1) (inputs : Fin (2 + prefixCount) → Bool) :
    (BooleanCircuitIO.binaryWithPrefix prefixCount binary).eval inputs
      (Fin.last prefixCount) =
        binary.eval
          (fun inputBit =>
            Fin.cases (inputs 0) (fun _ => inputs 1) inputBit) 0 := by
  unfold BooleanCircuitIO.binaryWithPrefix
  dsimp
  have hnot : ¬ prefixCount < prefixCount := Nat.lt_irrefl _
  simp only [BooleanCircuitIO.eval]
  simp only [Fin.last]
  rw [dif_neg hnot]
  change
    ((BooleanCircuitIO.empty (2 + prefixCount)).compose binary
      (BooleanCircuitIO.binaryPrefixInputMap prefixCount)).eval inputs 0 =
      binary.eval
        (fun inputBit =>
          Fin.cases (inputs 0) (fun _ => inputs 1) inputBit) 0
  rw [BooleanCircuitIO.eval_compose]
  congr 1
  funext inputBit
  refine Fin.cases ?_ ?_ inputBit
  · rfl
  · intro _
    rfl

/-- Supply the next word bit, the shared selector, and the old prefix to a
prefix-preserving binary stage. -/
def BooleanCircuitIO.binarySelectorStepInputMap
    (width processed : ℕ) (hprocessed : processed + 1 ≤ width)
    (outer : BooleanCircuitIO (width + 1) processed) :
    Fin (2 + processed) → BooleanWire (width + 1) outer.gateCount :=
  Fin.addCases
    (fun binaryInput =>
      Fin.cases
        (.input ⟨processed,
          lt_of_lt_of_le (Nat.lt_of_succ_le hprocessed) (Nat.le_succ width)⟩)
        (fun _ => .input (Fin.last width)) binaryInput)
    outer.outputs

/-- Repeatedly apply a two-input circuit to a word and one shared selector.
The resulting output word has one component per input-word bit. -/
def BooleanCircuitIO.binarySelectorPrefix (width : ℕ)
    (binary : BooleanCircuitIO 2 1) :
    (processed : ℕ) → processed ≤ width → BooleanCircuitIO (width + 1) processed
  | 0, _ => BooleanCircuitIO.empty (width + 1)
  | processed + 1, hprocessed =>
      let hprevious : processed ≤ width :=
        Nat.le_trans (Nat.le_succ processed) hprocessed
      let outer := BooleanCircuitIO.binarySelectorPrefix width binary processed hprevious
      outer.compose (BooleanCircuitIO.binaryWithPrefix processed binary)
        (BooleanCircuitIO.binarySelectorStepInputMap width processed hprocessed outer)

/-- A repeated selector uses one copy of the binary component per processed
word bit. -/
theorem BooleanCircuitIO.binarySelectorPrefix_gateCount (width : ℕ)
    (binary : BooleanCircuitIO 2 1) :
    ∀ (processed : ℕ) (hprocessed : processed ≤ width),
      (BooleanCircuitIO.binarySelectorPrefix width binary processed hprocessed).gateCount =
        processed * binary.gateCount
  | 0, _ => by
      change 0 = 0 * binary.gateCount
      simp
  | processed + 1, hprocessed => by
      let hprevious : processed ≤ width :=
        Nat.le_trans (Nat.le_succ processed) hprocessed
      rw [BooleanCircuitIO.binarySelectorPrefix,
        BooleanCircuitIO.compose_gateCount,
        BooleanCircuitIO.binaryWithPrefix_gateCount,
        BooleanCircuitIO.binarySelectorPrefix_gateCount width binary processed hprevious]
      simp [Nat.succ_mul]

/-- Every completed selector output is the component circuit applied to the
corresponding input-word bit and the shared final selector input. -/
theorem BooleanCircuitIO.eval_binarySelectorPrefix (width : ℕ)
    (binary : BooleanCircuitIO 2 1) (inputs : Fin (width + 1) → Bool) :
    ∀ (processed : ℕ) (hprocessed : processed ≤ width) (bit : Fin processed),
      (BooleanCircuitIO.binarySelectorPrefix width binary processed hprocessed).eval
        inputs bit =
        binary.eval
          (fun binaryInput =>
            Fin.cases (inputs (Fin.castLE (Nat.le_succ_of_le hprocessed) bit))
              (fun _ => inputs (Fin.last width)) binaryInput) 0
  | 0, _, bit => Fin.elim0 bit
  | processed + 1, hprocessed, bit => by
      let hprevious : processed ≤ width :=
        Nat.le_trans (Nat.le_succ processed) hprocessed
      let outer := BooleanCircuitIO.binarySelectorPrefix width binary processed hprevious
      let inputMap := BooleanCircuitIO.binarySelectorStepInputMap
        width processed hprocessed outer
      change (outer.compose (BooleanCircuitIO.binaryWithPrefix processed binary)
        inputMap).eval inputs bit = _
      by_cases hprior : bit.val < processed
      · let old : Fin processed := ⟨bit.val, hprior⟩
        have hold : bit = Fin.castAdd 1 old := Fin.ext rfl
        rw [hold, BooleanCircuitIO.eval_compose,
          BooleanCircuitIO.eval_binaryWithPrefix_old]
        unfold inputMap BooleanCircuitIO.binarySelectorStepInputMap
        rw [Fin.addCases_right]
        change outer.eval inputs old = _
        rw [BooleanCircuitIO.eval_binarySelectorPrefix width binary inputs
          processed hprevious old]
        congr 2
      · have hlastValue : bit.val = processed :=
          Nat.eq_of_lt_succ_of_not_lt bit.isLt hprior
        have hlast : bit = Fin.last processed := Fin.ext hlastValue
        rw [hlast, BooleanCircuitIO.eval_compose,
          BooleanCircuitIO.eval_binaryWithPrefix_last]
        congr 2
        funext binaryInput
        refine Fin.cases ?_ ?_ binaryInput
        · rfl
        · intro remaining
          have hremaining : remaining = 0 := Fin.eq_zero remaining
          subst remaining
          unfold inputMap BooleanCircuitIO.binarySelectorStepInputMap
          rw [Fin.cases_succ, Fin.cases_succ]
          have hone : (1 : Fin (2 + processed)) =
              Fin.castAdd processed (1 : Fin 2) := by
            apply Fin.ext
            change 1 % (2 + processed) = 1
            exact Nat.mod_eq_of_lt (by omega)
          rw [hone, Fin.addCases_left]
          have honeTwo : (1 : Fin 2) = Fin.succ 0 := by decide
          rw [honeTwo, Fin.cases_succ]
          congr 1

/-- The complete word-and-selector circuit. -/
def BooleanCircuitIO.binarySelector (width : ℕ) (binary : BooleanCircuitIO 2 1) :
    BooleanCircuitIO (width + 1) width :=
  BooleanCircuitIO.binarySelectorPrefix width binary width (Nat.le_refl width)

theorem BooleanCircuitIO.binarySelector_gateCount (width : ℕ)
    (binary : BooleanCircuitIO 2 1) :
    (BooleanCircuitIO.binarySelector width binary).gateCount = width * binary.gateCount :=
  BooleanCircuitIO.binarySelectorPrefix_gateCount width binary width (Nat.le_refl width)

theorem BooleanCircuitIO.eval_binarySelector (width : ℕ)
    (binary : BooleanCircuitIO 2 1) (inputs : Fin (width + 1) → Bool)
    (bit : Fin width) :
    (BooleanCircuitIO.binarySelector width binary).eval inputs bit =
      binary.eval
        (fun binaryInput =>
          Fin.cases (inputs (Fin.castAdd 1 bit))
            (fun _ => inputs (Fin.last width)) binaryInput) 0 := by
  exact BooleanCircuitIO.eval_binarySelectorPrefix width binary inputs width
    (Nat.le_refl width) bit

/-- Bitwise disjunction of a word with one shared selector bit.  When that
selector is an addition carry, this turns every output bit on and hence clips
an overflowing unsigned sum to the all-ones word. -/
def BooleanCircuitIO.orWithSelector (width : ℕ) : BooleanCircuitIO (width + 1) width :=
  BooleanCircuitIO.binarySelector width BooleanCircuitIO.or

theorem BooleanCircuitIO.orWithSelector_gateCount (width : ℕ) :
    (BooleanCircuitIO.orWithSelector width).gateCount = 3 * width := by
  rw [BooleanCircuitIO.orWithSelector, BooleanCircuitIO.binarySelector_gateCount,
    BooleanCircuitIO.or_gateCount]
  omega

theorem BooleanCircuitIO.eval_orWithSelector (width : ℕ)
    (inputs : Fin (width + 1) → Bool) (bit : Fin width) :
    (BooleanCircuitIO.orWithSelector width).eval inputs bit =
      (inputs (Fin.castAdd 1 bit) || inputs (Fin.last width)) := by
  rw [BooleanCircuitIO.orWithSelector, BooleanCircuitIO.eval_binarySelector,
    BooleanCircuitIO.eval_or]
  have hone : (1 : Fin 2) = Fin.succ 0 := by decide
  rw [hone, Fin.cases_zero, Fin.cases_succ]

/-- Bitwise conjunction of a word with one shared selector bit.  When that
selector records that a subtraction did not underflow, this turns every bit
off on underflow and therefore clips the result to zero. -/
def BooleanCircuitIO.andWithSelector (width : ℕ) : BooleanCircuitIO (width + 1) width :=
  BooleanCircuitIO.binarySelector width BooleanCircuitIO.and

theorem BooleanCircuitIO.andWithSelector_gateCount (width : ℕ) :
    (BooleanCircuitIO.andWithSelector width).gateCount = 2 * width := by
  rw [BooleanCircuitIO.andWithSelector, BooleanCircuitIO.binarySelector_gateCount,
    BooleanCircuitIO.and_gateCount]
  omega

theorem BooleanCircuitIO.eval_andWithSelector (width : ℕ)
    (inputs : Fin (width + 1) → Bool) (bit : Fin width) :
    (BooleanCircuitIO.andWithSelector width).eval inputs bit =
      (inputs (Fin.castAdd 1 bit) && inputs (Fin.last width)) := by
  rw [BooleanCircuitIO.andWithSelector, BooleanCircuitIO.eval_binarySelector,
    BooleanCircuitIO.eval_and]
  have hone : (1 : Fin 2) = Fin.succ 0 := by decide
  rw [hone, Fin.cases_zero, Fin.cases_succ]

/-- Add a hard-coded nonnegative fixed-point shift and clip the overflowing
case to the all-ones word.  This is the Boolean implementation of
`min(1, x + delta)` on a fixed unsigned grid. -/
def BooleanCircuitIO.saturatingAddConstant (width : ℕ) (bits : Fin width → Bool) :
    BooleanCircuitIO width width :=
  let outer := BooleanCircuitIO.rippleAdderWithConstant width bits
  outer.compose (BooleanCircuitIO.orWithSelector width) outer.outputs

/-- The concrete positive saturating update has linear size. -/
theorem BooleanCircuitIO.saturatingAddConstant_gateCount (width : ℕ)
    (bits : Fin width → Bool) :
    (BooleanCircuitIO.saturatingAddConstant width bits).gateCount = 13 * width + 1 := by
  rw [BooleanCircuitIO.saturatingAddConstant,
    BooleanCircuitIO.compose_gateCount,
    BooleanCircuitIO.rippleAdderWithConstant_gateCount,
    BooleanCircuitIO.orWithSelector_gateCount]
  omega

/-- Each output bit of the positive saturating circuit is the modular sum bit
OR its overflow carry. -/
theorem BooleanCircuitIO.eval_saturatingAddConstant (width : ℕ)
    (bits inputs : Fin width → Bool) (bit : Fin width) :
    (BooleanCircuitIO.saturatingAddConstant width bits).eval inputs bit =
      ((BooleanCircuitIO.rippleAdderWithConstant width bits).eval inputs
        (Fin.castAdd 1 bit) ||
        (BooleanCircuitIO.rippleAdderWithConstant width bits).eval inputs
          (BooleanCircuitIO.rippleCarryOutput width)) := by
  rw [BooleanCircuitIO.saturatingAddConstant, BooleanCircuitIO.eval_compose,
    BooleanCircuitIO.eval_orWithSelector]
  rfl

/-- The zero-gate identity word circuit, used for a compiled update whose
hard-coded shift is exactly zero. -/
def BooleanCircuitIO.identityWord (width : ℕ) : BooleanCircuitIO width width where
  gateCount := 0
  gates := .nil
  outputs := BooleanWire.input

theorem BooleanCircuitIO.eval_identityWord (width : ℕ)
    (inputs : Fin width → Bool) (bit : Fin width) :
    (BooleanCircuitIO.identityWord width).eval inputs bit = inputs bit := rfl

/-- Add a hard-coded two's-complement word and retain the sum only when the
addition carries out.  For a nonzero magnitude `d`, supplying `-d` as the
hard-coded word implements `max(0, x - d)`; the zero magnitude is handled by
`identityWord`, since modular addition by zero has no carry. -/
def BooleanCircuitIO.saturatingSubtractTwosComplement (width : ℕ)
    (twosComplementBits : Fin width → Bool) : BooleanCircuitIO width width :=
  let outer := BooleanCircuitIO.rippleAdderWithConstant width twosComplementBits
  outer.compose (BooleanCircuitIO.andWithSelector width) outer.outputs

/-- The nonzero negative saturating update has linear size. -/
theorem BooleanCircuitIO.saturatingSubtractTwosComplement_gateCount (width : ℕ)
    (twosComplementBits : Fin width → Bool) :
    (BooleanCircuitIO.saturatingSubtractTwosComplement width twosComplementBits).gateCount =
      12 * width + 1 := by
  rw [BooleanCircuitIO.saturatingSubtractTwosComplement,
    BooleanCircuitIO.compose_gateCount,
    BooleanCircuitIO.rippleAdderWithConstant_gateCount,
    BooleanCircuitIO.andWithSelector_gateCount]
  omega

/-- Each output bit of the negative saturating circuit is the modular sum bit
AND its carry-out, so underflow yields the all-zero word. -/
theorem BooleanCircuitIO.eval_saturatingSubtractTwosComplement (width : ℕ)
    (twosComplementBits inputs : Fin width → Bool) (bit : Fin width) :
    (BooleanCircuitIO.saturatingSubtractTwosComplement width twosComplementBits).eval
      inputs bit =
      ((BooleanCircuitIO.rippleAdderWithConstant width twosComplementBits).eval inputs
        (Fin.castAdd 1 bit) &&
        (BooleanCircuitIO.rippleAdderWithConstant width twosComplementBits).eval inputs
          (BooleanCircuitIO.rippleCarryOutput width)) := by
  rw [BooleanCircuitIO.saturatingSubtractTwosComplement,
    BooleanCircuitIO.eval_compose, BooleanCircuitIO.eval_andWithSelector]
  rfl

/-- Concatenate two equal-width Boolean words into the input word expected by
the ripple adder. -/
def BooleanCircuitIO.wordInputs {width : ℕ}
    (left right : Fin width → Bool) : Fin (width + width) → Bool :=
  Fin.addCases left right

theorem BooleanCircuitIO.wordInputs_left {width : ℕ}
    (left right : Fin width → Bool) (bit : Fin width) :
    BooleanCircuitIO.wordInputs left right (Fin.castAdd width bit) = left bit := by
  simp [BooleanCircuitIO.wordInputs]

theorem BooleanCircuitIO.wordInputs_right {width : ℕ}
    (left right : Fin width → Bool) (bit : Fin width) :
    BooleanCircuitIO.wordInputs left right (Fin.natAdd width bit) = right bit := by
  unfold BooleanCircuitIO.wordInputs
  rw [Fin.addCases_right]

/-- The carry entering the next stage of the ordinary ripple-carry addition
of two Boolean words, with least-significant bits indexed first. -/
def BooleanCircuitIO.rippleCarry {width : ℕ}
    (left right : Fin width → Bool) :
    (processed : ℕ) → processed ≤ width → Bool
  | 0, _ => false
  | processed + 1, hprocessed =>
      let bit : Fin width := ⟨processed, Nat.lt_of_succ_le hprocessed⟩
      (left bit && right bit) ||
        (BooleanCircuitIO.rippleCarry left right processed
          (Nat.le_trans (Nat.le_succ processed) hprocessed) &&
          (left bit ^^ right bit))

/-- The sum bit at one position, using the carry generated by all lower
positions. -/
def BooleanCircuitIO.rippleSumBit {width : ℕ}
    (left right : Fin width → Bool) (bit : Fin width) : Bool :=
  (left bit ^^ right bit) ^^
    BooleanCircuitIO.rippleCarry left right bit.val (Nat.le_of_lt bit.isLt)

/-- The first full-adder input at a ripple stage evaluates to the next left
word bit. -/
theorem BooleanCircuitIO.eval_rippleAdderStepInputMap_left
    {width processed : ℕ} (hprocessed : processed + 1 ≤ width)
    (outer : BooleanCircuitIO (width + width) (processed + 1))
    (left right : Fin width → Bool) :
    (BooleanCircuitIO.rippleAdderStepInputMap width processed hprocessed outer
      (0 : Fin (3 + processed))).eval
        (BooleanCircuitIO.wordInputs left right)
        (outer.gates.eval (BooleanCircuitIO.wordInputs left right)) =
      left ⟨processed, Nat.lt_of_succ_le hprocessed⟩ := by
  let bit : Fin width := ⟨processed, Nat.lt_of_succ_le hprocessed⟩
  change BooleanCircuitIO.wordInputs left right
      ⟨processed,
        lt_of_lt_of_le bit.isLt (Nat.le_add_right width width)⟩ = left bit
  change BooleanCircuitIO.wordInputs left right (Fin.castAdd width bit) = left bit
  exact BooleanCircuitIO.wordInputs_left left right bit

/-- The second full-adder input at a ripple stage evaluates to the next right
word bit. -/
theorem BooleanCircuitIO.eval_rippleAdderStepInputMap_right
    {width processed : ℕ} (hprocessed : processed + 1 ≤ width)
    (outer : BooleanCircuitIO (width + width) (processed + 1))
    (left right : Fin width → Bool) :
    (BooleanCircuitIO.rippleAdderStepInputMap width processed hprocessed outer
      (1 : Fin (3 + processed))).eval
        (BooleanCircuitIO.wordInputs left right)
        (outer.gates.eval (BooleanCircuitIO.wordInputs left right)) =
      right ⟨processed, Nat.lt_of_succ_le hprocessed⟩ := by
  let bit : Fin width := ⟨processed, Nat.lt_of_succ_le hprocessed⟩
  have hinput : (1 : Fin (3 + processed)) = Fin.castAdd processed (1 : Fin 3) :=
    by
      apply Fin.ext
      change 1 % (3 + processed) = 1
      apply Nat.mod_eq_of_lt
      omega
  rw [hinput]
  simp only [BooleanCircuitIO.rippleAdderStepInputMap, Fin.addCases_left]
  have hone : (1 : Fin 3) = Fin.succ (0 : Fin 2) := by decide
  rw [hone, Fin.cases_succ, Fin.cases_zero]
  change BooleanCircuitIO.wordInputs left right
      ⟨width + processed, Nat.add_lt_add_left bit.isLt width⟩ = right bit
  change BooleanCircuitIO.wordInputs left right (Fin.natAdd width bit) = right bit
  exact BooleanCircuitIO.wordInputs_right left right bit

/-- The third full-adder input at a ripple stage is the previous carry. -/
theorem BooleanCircuitIO.eval_rippleAdderStepInputMap_carry
    {width processed : ℕ} (hprocessed : processed + 1 ≤ width)
    (outer : BooleanCircuitIO (width + width) (processed + 1))
    (left right : Fin width → Bool) :
    (BooleanCircuitIO.rippleAdderStepInputMap width processed hprocessed outer
      (2 : Fin (3 + processed))).eval
        (BooleanCircuitIO.wordInputs left right)
        (outer.gates.eval (BooleanCircuitIO.wordInputs left right)) =
      outer.eval (BooleanCircuitIO.wordInputs left right)
        (BooleanCircuitIO.rippleCarryOutput processed) := by
  have hinput : (2 : Fin (3 + processed)) = Fin.castAdd processed (2 : Fin 3) :=
    by
      apply Fin.ext
      change 2 % (3 + processed) = 2
      apply Nat.mod_eq_of_lt
      omega
  rw [hinput]
  simp only [BooleanCircuitIO.rippleAdderStepInputMap, Fin.addCases_left]
  have htwo : (2 : Fin 3) = Fin.succ (1 : Fin 2) := by decide
  have hone : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
  rw [htwo, Fin.cases_succ, hone, Fin.cases_succ, Fin.cases_zero]
  rfl

/-- The remaining full-adder inputs forward the already computed sum bits. -/
theorem BooleanCircuitIO.eval_rippleAdderStepInputMap_old
    {width processed : ℕ} (hprocessed : processed + 1 ≤ width)
    (outer : BooleanCircuitIO (width + width) (processed + 1))
    (left right : Fin width → Bool) (old : Fin processed) :
    (BooleanCircuitIO.rippleAdderStepInputMap width processed hprocessed outer
      (Fin.natAdd 3 old)).eval
        (BooleanCircuitIO.wordInputs left right)
        (outer.gates.eval (BooleanCircuitIO.wordInputs left right)) =
      outer.eval (BooleanCircuitIO.wordInputs left right) (Fin.castAdd 1 old) := by
  unfold BooleanCircuitIO.rippleAdderStepInputMap
  rw [Fin.addCases_right]
  rfl

/-- After `processed` ripple stages, the final circuit output is precisely
the carry generated by the corresponding prefix of the two input words. -/
theorem BooleanCircuitIO.eval_rippleAdderPrefix_carry
    (width : ℕ) (left right : Fin width → Bool) :
    ∀ (processed : ℕ) (hprocessed : processed ≤ width),
      (BooleanCircuitIO.rippleAdderPrefix width processed hprocessed).eval
        (BooleanCircuitIO.wordInputs left right)
        (BooleanCircuitIO.rippleCarryOutput processed) =
        BooleanCircuitIO.rippleCarry left right processed hprocessed
  | 0, _ => rfl
  | processed + 1, hprocessed => by
      let hprevious : processed ≤ width :=
        Nat.le_trans (Nat.le_succ processed) hprocessed
      let outer := BooleanCircuitIO.rippleAdderPrefix width processed hprevious
      let inputMap := BooleanCircuitIO.rippleAdderStepInputMap
        width processed hprocessed outer
      change (outer.compose (BooleanCircuitIO.fullAdderWithPrefix processed)
        inputMap).eval (BooleanCircuitIO.wordInputs left right)
          (BooleanCircuitIO.rippleCarryOutput (processed + 1)) = _
      have hcarryOutput : BooleanCircuitIO.rippleCarryOutput (processed + 1) =
          BooleanCircuit.fullAdderCarryOutput processed := Fin.ext rfl
      rw [hcarryOutput, BooleanCircuitIO.eval_compose,
        BooleanCircuitIO.eval_fullAdderWithPrefix_carry]
      rw [BooleanCircuitIO.eval_rippleAdderStepInputMap_left,
        BooleanCircuitIO.eval_rippleAdderStepInputMap_right,
        BooleanCircuitIO.eval_rippleAdderStepInputMap_carry]
      rw [BooleanCircuitIO.eval_rippleAdderPrefix_carry width left right
        processed hprevious]
      rfl

/-- Every non-carry output of a ripple-adder prefix is its corresponding
least-significant sum bit. -/
theorem BooleanCircuitIO.eval_rippleAdderPrefix_sum
    (width : ℕ) (left right : Fin width → Bool) :
    ∀ (processed : ℕ) (hprocessed : processed ≤ width) (old : Fin processed),
      (BooleanCircuitIO.rippleAdderPrefix width processed hprocessed).eval
        (BooleanCircuitIO.wordInputs left right) (Fin.castAdd 1 old) =
        BooleanCircuitIO.rippleSumBit left right (Fin.castLE hprocessed old)
  | 0, _, old => Fin.elim0 old
  | processed + 1, hprocessed, old => by
      let hprevious : processed ≤ width :=
        Nat.le_trans (Nat.le_succ processed) hprocessed
      let outer := BooleanCircuitIO.rippleAdderPrefix width processed hprevious
      let inputMap := BooleanCircuitIO.rippleAdderStepInputMap
        width processed hprocessed outer
      change (outer.compose (BooleanCircuitIO.fullAdderWithPrefix processed)
        inputMap).eval (BooleanCircuitIO.wordInputs left right)
          (Fin.castAdd 1 old) = _
      by_cases hprior : old.val < processed
      · let previousOutput : Fin processed := ⟨old.val, hprior⟩
        have holdOutput : Fin.castAdd 1 old = Fin.castAdd 2 previousOutput :=
          Fin.ext rfl
        rw [holdOutput]
        calc
          (outer.compose (BooleanCircuitIO.fullAdderWithPrefix processed)
              inputMap).eval (BooleanCircuitIO.wordInputs left right)
                (Fin.castAdd 2 previousOutput) =
              (BooleanCircuitIO.fullAdderWithPrefix processed).eval
                (fun inputBit =>
                  (inputMap inputBit).eval (BooleanCircuitIO.wordInputs left right)
                    (outer.gates.eval (BooleanCircuitIO.wordInputs left right)))
                (Fin.castAdd 2 previousOutput) := by
                  rw [BooleanCircuitIO.eval_compose]
          _ = (inputMap (Fin.natAdd 3 previousOutput)).eval
                (BooleanCircuitIO.wordInputs left right)
                (outer.gates.eval (BooleanCircuitIO.wordInputs left right)) :=
                  BooleanCircuitIO.eval_fullAdderWithPrefix_old processed
                    previousOutput _
          _ = outer.eval (BooleanCircuitIO.wordInputs left right)
                (Fin.castAdd 1 previousOutput) :=
                  BooleanCircuitIO.eval_rippleAdderStepInputMap_old hprocessed
                    outer left right previousOutput
          _ = BooleanCircuitIO.rippleSumBit left right
                (Fin.castLE hprevious previousOutput) :=
                  BooleanCircuitIO.eval_rippleAdderPrefix_sum width left right
                    processed hprevious previousOutput
          _ = BooleanCircuitIO.rippleSumBit left right
                (Fin.castLE hprocessed old) := by
                  congr 1
      · have hlastValue : old.val = processed :=
          Nat.eq_of_lt_succ_of_not_lt old.isLt hprior
        have hlast : old = ⟨processed, Nat.lt_succ_self processed⟩ :=
          Fin.ext hlastValue
        rw [hlast]
        have hsumOutput :
            Fin.castAdd 1 (⟨processed, Nat.lt_succ_self processed⟩ :
              Fin (processed + 1)) =
              BooleanCircuit.fullAdderSumOutput processed := Fin.ext rfl
        rw [hsumOutput]
        calc
          (outer.compose (BooleanCircuitIO.fullAdderWithPrefix processed)
              inputMap).eval (BooleanCircuitIO.wordInputs left right)
                (BooleanCircuit.fullAdderSumOutput processed) =
              (BooleanCircuitIO.fullAdderWithPrefix processed).eval
                (fun inputBit =>
                  (inputMap inputBit).eval (BooleanCircuitIO.wordInputs left right)
                    (outer.gates.eval (BooleanCircuitIO.wordInputs left right)))
                (BooleanCircuit.fullAdderSumOutput processed) := by
                  rw [BooleanCircuitIO.eval_compose]
          _ =
              (((inputMap 0).eval (BooleanCircuitIO.wordInputs left right)
                (outer.gates.eval (BooleanCircuitIO.wordInputs left right)) ^^
              (inputMap 1).eval (BooleanCircuitIO.wordInputs left right)
                (outer.gates.eval (BooleanCircuitIO.wordInputs left right))) ^^
              (inputMap 2).eval (BooleanCircuitIO.wordInputs left right)
                (outer.gates.eval (BooleanCircuitIO.wordInputs left right))) :=
                  BooleanCircuitIO.eval_fullAdderWithPrefix_sum processed _
          _ = BooleanCircuitIO.rippleSumBit left right
                ⟨processed, Nat.lt_of_succ_le hprocessed⟩ := by
                  rw [BooleanCircuitIO.eval_rippleAdderStepInputMap_left,
                    BooleanCircuitIO.eval_rippleAdderStepInputMap_right,
                    BooleanCircuitIO.eval_rippleAdderStepInputMap_carry,
                    BooleanCircuitIO.eval_rippleAdderPrefix_carry width left right
                      processed hprevious]
                  rfl
          _ = BooleanCircuitIO.rippleSumBit left right
                (Fin.castLE hprocessed
                  ⟨processed, Nat.lt_succ_self processed⟩) := by
                  congr 1

/-- Read a bit vector in least-significant-bit order, which is the convention
used by the ripple circuit. -/
def BooleanCircuitIO.bitVecBits {width : ℕ} (value : BitVec width) :
    Fin width → Bool :=
  fun bit => value.getLsb bit

/-- The Boolean majority truth table in the form used by a full adder. -/
theorem BooleanCircuitIO.bool_atLeastTwo_eq (left right carry : Bool) :
    Bool.atLeastTwo left right carry =
      ((left && right) || (carry && (left ^^ right))) := by
  cases left <;> cases right <;> cases carry <;> rfl

/-- Exclusive-or is associative on Boolean values. -/
theorem BooleanCircuitIO.bool_xor_assoc (first second third : Bool) :
    ((first ^^ second) ^^ third) = (first ^^ (second ^^ third)) := by
  cases first <;> cases second <;> cases third <;> rfl

/-- The circuit's recursively specified carry agrees with Lean's standard
bit-vector carry for ordinary addition. -/
theorem BooleanCircuitIO.rippleCarry_bitVec
    {width : ℕ} (left right : BitVec width) :
    ∀ (processed : ℕ) (hprocessed : processed ≤ width),
      BooleanCircuitIO.rippleCarry (BooleanCircuitIO.bitVecBits left)
        (BooleanCircuitIO.bitVecBits right) processed hprocessed =
        BitVec.carry processed left right false
  | 0, _ => by simp [BooleanCircuitIO.rippleCarry]
  | processed + 1, hprocessed => by
      let hprevious : processed ≤ width :=
        Nat.le_trans (Nat.le_succ processed) hprocessed
      rw [BooleanCircuitIO.rippleCarry]
      rw [BooleanCircuitIO.rippleCarry_bitVec left right processed hprevious,
        BitVec.carry_succ]
      change
        ((left.getLsb ⟨processed, Nat.lt_of_succ_le hprocessed⟩ &&
          right.getLsb ⟨processed, Nat.lt_of_succ_le hprocessed⟩) ||
          (BitVec.carry processed left right false &&
            (left.getLsb ⟨processed, Nat.lt_of_succ_le hprocessed⟩ ^^
              right.getLsb ⟨processed, Nat.lt_of_succ_le hprocessed⟩))) =
          Bool.atLeastTwo (left.getLsbD processed) (right.getLsbD processed)
            (BitVec.carry processed left right false)
      rw [BooleanCircuitIO.bool_atLeastTwo_eq]
      change
        ((left.getLsbD processed && right.getLsbD processed) ||
          (BitVec.carry processed left right false &&
            (left.getLsbD processed ^^ right.getLsbD processed))) =
          ((left.getLsbD processed && right.getLsbD processed) ||
            (BitVec.carry processed left right false &&
              (left.getLsbD processed ^^ right.getLsbD processed)))
      rfl

/-- Each non-carry output of the ripple circuit is the corresponding bit of
the modular bit-vector sum. -/
theorem BooleanCircuitIO.eval_rippleAdder_bitVec_sum
    {width : ℕ} (left right : BitVec width) (bit : Fin width) :
    (BooleanCircuitIO.rippleAdder width).eval
      (BooleanCircuitIO.wordInputs (BooleanCircuitIO.bitVecBits left)
        (BooleanCircuitIO.bitVecBits right)) (Fin.castAdd 1 bit) =
      (left + right).getLsb bit := by
  rw [show BooleanCircuitIO.rippleAdder width =
    BooleanCircuitIO.rippleAdderPrefix width width (Nat.le_refl width) from rfl]
  rw [BooleanCircuitIO.eval_rippleAdderPrefix_sum]
  simp only [BooleanCircuitIO.rippleSumBit]
  rw [BooleanCircuitIO.rippleCarry_bitVec left right]
  change ((left.getLsbD bit.val ^^ right.getLsbD bit.val) ^^
      BitVec.carry bit.val left right false) = (left + right).getLsbD bit.val
  rw [BitVec.getLsbD_add bit.isLt left right]
  exact BooleanCircuitIO.bool_xor_assoc _ _ _

/-- The final ripple-circuit output is the overflow carry of bit-vector
addition. -/
theorem BooleanCircuitIO.eval_rippleAdder_bitVec_carry
    {width : ℕ} (left right : BitVec width) :
    (BooleanCircuitIO.rippleAdder width).eval
      (BooleanCircuitIO.wordInputs (BooleanCircuitIO.bitVecBits left)
        (BooleanCircuitIO.bitVecBits right))
      (BooleanCircuitIO.rippleCarryOutput width) =
        BitVec.carry width left right false := by
  rw [show BooleanCircuitIO.rippleAdder width =
    BooleanCircuitIO.rippleAdderPrefix width width (Nat.le_refl width) from rfl]
  rw [BooleanCircuitIO.eval_rippleAdderPrefix_carry]
  exact BooleanCircuitIO.rippleCarry_bitVec left right width (Nat.le_refl width)

/-- The word seen by the ripple component of a constant-adder is its primary
input word followed by the literal word. -/
theorem BooleanCircuitIO.rippleAdderWithConstant_innerInputs (width : ℕ)
    (bits inputs : Fin width → Bool) :
    (fun inputBit =>
      (BooleanCircuitIO.rippleAdderConstantInputMap width
        (BooleanCircuitIO.constantWord width bits) inputBit).eval inputs
          ((BooleanCircuitIO.constantWord width bits).gates.eval inputs)) =
        BooleanCircuitIO.wordInputs inputs bits := by
  funext inputBit
  refine Fin.addCases ?_ ?_ inputBit
  · intro bit
    calc
      (BooleanCircuitIO.rippleAdderConstantInputMap width
        (BooleanCircuitIO.constantWord width bits) (Fin.castAdd width bit)).eval inputs
          ((BooleanCircuitIO.constantWord width bits).gates.eval inputs) = inputs bit :=
        BooleanCircuitIO.eval_rippleAdderConstantInputMap_left width
          (BooleanCircuitIO.constantWord width bits) inputs bit
      _ = BooleanCircuitIO.wordInputs inputs bits (Fin.castAdd width bit) :=
        (BooleanCircuitIO.wordInputs_left inputs bits bit).symm
  · intro bit
    calc
      (BooleanCircuitIO.rippleAdderConstantInputMap width
        (BooleanCircuitIO.constantWord width bits) (Fin.natAdd width bit)).eval inputs
          ((BooleanCircuitIO.constantWord width bits).gates.eval inputs) =
          (BooleanCircuitIO.constantWord width bits).eval inputs bit :=
        BooleanCircuitIO.eval_rippleAdderConstantInputMap_right width
          (BooleanCircuitIO.constantWord width bits) inputs bit
      _ = bits bit := BooleanCircuitIO.eval_constantWord width bits inputs bit
      _ = BooleanCircuitIO.wordInputs inputs bits (Fin.natAdd width bit) :=
        (BooleanCircuitIO.wordInputs_right inputs bits bit).symm

/-- A constant-adder's low-order outputs are the actual modular sum bits. -/
theorem BooleanCircuitIO.eval_rippleAdderWithConstant_bitVec_sum
    {width : ℕ} (left right : BitVec width) (bit : Fin width) :
    (BooleanCircuitIO.rippleAdderWithConstant width
      (BooleanCircuitIO.bitVecBits right)).eval
        (BooleanCircuitIO.bitVecBits left) (Fin.castAdd 1 bit) =
      (left + right).getLsb bit := by
  rw [BooleanCircuitIO.rippleAdderWithConstant, BooleanCircuitIO.eval_compose]
  rw [BooleanCircuitIO.rippleAdderWithConstant_innerInputs]
  exact BooleanCircuitIO.eval_rippleAdder_bitVec_sum left right bit

/-- A constant-adder's final output is precisely the carry out of the
unsigned addition. -/
theorem BooleanCircuitIO.eval_rippleAdderWithConstant_bitVec_carry
    {width : ℕ} (left right : BitVec width) :
    (BooleanCircuitIO.rippleAdderWithConstant width
      (BooleanCircuitIO.bitVecBits right)).eval
        (BooleanCircuitIO.bitVecBits left)
        (BooleanCircuitIO.rippleCarryOutput width) =
      BitVec.carry width left right false := by
  rw [BooleanCircuitIO.rippleAdderWithConstant, BooleanCircuitIO.eval_compose]
  rw [BooleanCircuitIO.rippleAdderWithConstant_innerInputs]
  exact BooleanCircuitIO.eval_rippleAdder_bitVec_carry left right

/-- Bit-vector semantics of the positive saturating circuit: every output bit
is the ordinary sum bit, unless unsigned addition carries out, in which case
the circuit emits all ones. -/
theorem BooleanCircuitIO.eval_saturatingAddConstant_bitVec
    {width : ℕ} (left right : BitVec width) (bit : Fin width) :
    (BooleanCircuitIO.saturatingAddConstant width
      (BooleanCircuitIO.bitVecBits right)).eval
        (BooleanCircuitIO.bitVecBits left) bit =
      ((left + right).getLsb bit || BitVec.carry width left right false) := by
  rw [BooleanCircuitIO.eval_saturatingAddConstant,
    BooleanCircuitIO.eval_rippleAdderWithConstant_bitVec_sum,
    BooleanCircuitIO.eval_rippleAdderWithConstant_bitVec_carry]

/-- Bit-vector semantics of the lower-saturating two's-complement circuit.
For a nonzero magnitude `d`, instantiate `right` with `-d`; its carry is the
usual no-underflow flag for `left - d`. -/
theorem BooleanCircuitIO.eval_saturatingSubtractTwosComplement_bitVec
    {width : ℕ} (left right : BitVec width) (bit : Fin width) :
    (BooleanCircuitIO.saturatingSubtractTwosComplement width
      (BooleanCircuitIO.bitVecBits right)).eval
        (BooleanCircuitIO.bitVecBits left) bit =
      ((left + right).getLsb bit && BitVec.carry width left right false) := by
  rw [BooleanCircuitIO.eval_saturatingSubtractTwosComplement,
    BooleanCircuitIO.eval_rippleAdderWithConstant_bitVec_sum,
    BooleanCircuitIO.eval_rippleAdderWithConstant_bitVec_carry]

/-- Adding the two's-complement of a nonzero unsigned threshold carries out
exactly when the input is at least that threshold.  This is the arithmetic
comparison primitive used to compile fixed-grid bin membership tests. -/
theorem BooleanCircuitIO.carry_add_neg_eq_decide_le
    {width : ℕ} (input threshold : BitVec width) (hthreshold : threshold ≠ 0) :
    BitVec.carry width input (-threshold) false =
      decide (threshold.toNat ≤ input.toNat) := by
  rw [BitVec.carry_width]
  simp only [Bool.toNat_false, Nat.add_zero, BitVec.toNat_neg]
  have hthresholdNat : threshold.toNat ≠ 0 := by
    intro hzero
    apply hthreshold
    exact BitVec.toNat_injective hzero
  have hthresholdPos : 0 < threshold.toNat := Nat.pos_of_ne_zero hthresholdNat
  have hnegLt : 2 ^ width - threshold.toNat < 2 ^ width := by omega
  rw [Nat.mod_eq_of_lt hnegLt]
  by_cases hle : threshold.toNat ≤ input.toNat
  · have hcarry : input.toNat + (2 ^ width - threshold.toNat) ≥ 2 ^ width := by
      omega
    simp [hle, hcarry]
  · have hnoCarry : ¬ input.toNat + (2 ^ width - threshold.toNat) ≥ 2 ^ width := by
      omega
    simp [hle, hnoCarry]

/-- A one-gate Boolean predicate that always accepts. -/
def BooleanCircuitIO.truePredicate (inputCount : ℕ) : BooleanCircuitIO inputCount 1 where
  gateCount := 1
  gates := .snoc .nil (.constant true)
  outputs := fun _ => .gate 0

theorem BooleanCircuitIO.eval_truePredicate (inputCount : ℕ)
    (inputs : Fin inputCount → Bool) :
    (BooleanCircuitIO.truePredicate inputCount).eval inputs 0 = true := rfl

/-- A literal circuit deciding whether an unsigned word is at least one
hard-coded threshold.  A zero threshold is handled by the one-gate true
predicate; otherwise a two's-complement addition exposes the comparison in
its final carry wire. -/
def BooleanCircuitIO.atLeastConstant (width : ℕ) (threshold : BitVec width) :
    BooleanCircuitIO width 1 :=
  if threshold = 0 then
    BooleanCircuitIO.truePredicate width
  else
    let adder := BooleanCircuitIO.rippleAdderWithConstant width
      (BooleanCircuitIO.bitVecBits (-threshold))
    { gateCount := adder.gateCount
      gates := adder.gates
      outputs := fun _ => adder.outputs (BooleanCircuitIO.rippleCarryOutput width) }

/-- A hard-coded threshold comparison has linear Boolean-circuit size. -/
theorem BooleanCircuitIO.atLeastConstant_gateCount_le (width : ℕ)
    (threshold : BitVec width) :
    (BooleanCircuitIO.atLeastConstant width threshold).gateCount ≤ 10 * width + 1 := by
  unfold BooleanCircuitIO.atLeastConstant
  split
  · change 1 ≤ 10 * width + 1
    omega
  · rw [BooleanCircuitIO.rippleAdderWithConstant_gateCount]

/-- The threshold circuit decides exactly the usual unsigned numerical order. -/
theorem BooleanCircuitIO.eval_atLeastConstant_bitVec
    {width : ℕ} (input threshold : BitVec width) :
    (BooleanCircuitIO.atLeastConstant width threshold).eval
      (BooleanCircuitIO.bitVecBits input) 0 =
        decide (threshold.toNat ≤ input.toNat) := by
  unfold BooleanCircuitIO.atLeastConstant
  split
  · rename_i hzero
    subst threshold
    simp [BooleanCircuitIO.eval_truePredicate]
  · rename_i hthreshold
    change
      (BooleanCircuitIO.rippleAdderWithConstant width
        (BooleanCircuitIO.bitVecBits (-threshold))).eval
          (BooleanCircuitIO.bitVecBits input)
          (BooleanCircuitIO.rippleCarryOutput width) = _
    rw [BooleanCircuitIO.eval_rippleAdderWithConstant_bitVec_carry]
    exact BooleanCircuitIO.carry_add_neg_eq_decide_le input threshold hthreshold

/-- Negate the one output of a Boolean predicate circuit with one NAND gate. -/
def BooleanCircuitIO.notPredicate {inputCount : ℕ}
    (predicate : BooleanCircuitIO inputCount 1) : BooleanCircuitIO inputCount 1 where
  gateCount := predicate.gateCount + 1
  gates := .snoc predicate.gates
    (.nand (predicate.outputs 0) (predicate.outputs 0))
  outputs := fun _ => .gate ⟨predicate.gateCount, Nat.lt_succ_self _⟩

theorem BooleanCircuitIO.notPredicate_gateCount {inputCount : ℕ}
    (predicate : BooleanCircuitIO inputCount 1) :
    predicate.notPredicate.gateCount = predicate.gateCount + 1 := rfl

theorem BooleanCircuitIO.eval_notPredicate {inputCount : ℕ}
    (predicate : BooleanCircuitIO inputCount 1)
    (inputs : Fin inputCount → Bool) :
    predicate.notPredicate.eval inputs 0 = !(predicate.eval inputs 0) := by
  change
    (BooleanGateList.snoc predicate.gates
      (.nand (predicate.outputs 0) (predicate.outputs 0))).eval inputs
        ⟨predicate.gateCount, Nat.lt_succ_self _⟩ = _
  rw [BooleanGateList.eval_snoc_last]
  change Bool.not (predicate.eval inputs 0 && predicate.eval inputs 0) =
    Bool.not (predicate.eval inputs 0)
  cases predicate.eval inputs 0 <;> rfl

/-- A literal circuit deciding whether an unsigned word is strictly below one
hard-coded threshold. -/
def BooleanCircuitIO.lessThanConstant (width : ℕ) (threshold : BitVec width) :
    BooleanCircuitIO width 1 :=
  (BooleanCircuitIO.atLeastConstant width threshold).notPredicate

theorem BooleanCircuitIO.lessThanConstant_gateCount_le (width : ℕ)
    (threshold : BitVec width) :
    (BooleanCircuitIO.lessThanConstant width threshold).gateCount ≤ 10 * width + 2 := by
  rw [BooleanCircuitIO.lessThanConstant,
    BooleanCircuitIO.notPredicate_gateCount]
  have hsize := BooleanCircuitIO.atLeastConstant_gateCount_le width threshold
  omega

/-- The strict-threshold circuit decides the usual unsigned strict order. -/
theorem BooleanCircuitIO.eval_lessThanConstant_bitVec
    {width : ℕ} (input threshold : BitVec width) :
    (BooleanCircuitIO.lessThanConstant width threshold).eval
      (BooleanCircuitIO.bitVecBits input) 0 =
        decide (input.toNat < threshold.toNat) := by
  rw [BooleanCircuitIO.lessThanConstant, BooleanCircuitIO.eval_notPredicate,
    BooleanCircuitIO.eval_atLeastConstant_bitVec]
  by_cases hle : threshold.toNat ≤ input.toNat
  · have hnotLt : ¬ input.toNat < threshold.toNat := by omega
    simp [hle, hnotLt]
  · have hlt : input.toNat < threshold.toNat := by omega
    simp [hle, hlt]

/-- Run two one-output predicates on the same primary inputs and retain both
outputs.  The second predicate is appended after the first, so the result is
one genuine topologically ordered gate DAG. -/
def BooleanCircuitIO.pairPredicates {inputCount : ℕ}
    (first second : BooleanCircuitIO inputCount 1) : BooleanCircuitIO inputCount 2 :=
  let composed := first.compose second (fun inputBit => BooleanWire.input inputBit)
  { gateCount := composed.gateCount
    gates := composed.gates
    outputs := fun output =>
      Fin.cases ((first.outputs 0).liftRight second.gateCount)
        (fun _ => composed.outputs 0) output }

theorem BooleanCircuitIO.pairPredicates_gateCount {inputCount : ℕ}
    (first second : BooleanCircuitIO inputCount 1) :
    (BooleanCircuitIO.pairPredicates first second).gateCount =
      first.gateCount + second.gateCount := rfl

/-- The first paired-predicate output has the first predicate's semantics. -/
theorem BooleanCircuitIO.eval_pairPredicates_first {inputCount : ℕ}
    (first second : BooleanCircuitIO inputCount 1)
    (inputs : Fin inputCount → Bool) :
    (BooleanCircuitIO.pairPredicates first second).eval inputs 0 = first.eval inputs 0 := by
  unfold BooleanCircuitIO.pairPredicates
  dsimp
  obtain ⟨houter, _⟩ := BooleanGateList.appendMapped_eval first.gates
    (fun inputBit => BooleanWire.input inputBit) inputs second.gates
  exact houter (first.outputs 0)

/-- The second paired-predicate output has the second predicate's semantics. -/
theorem BooleanCircuitIO.eval_pairPredicates_second {inputCount : ℕ}
    (first second : BooleanCircuitIO inputCount 1)
    (inputs : Fin inputCount → Bool) :
    (BooleanCircuitIO.pairPredicates first second).eval inputs 1 = second.eval inputs 0 := by
  unfold BooleanCircuitIO.pairPredicates
  dsimp
  change (first.compose second (fun inputBit => BooleanWire.input inputBit)).eval
    inputs 0 = second.eval inputs 0
  rw [BooleanCircuitIO.eval_compose]
  rfl

/-- Conjoin two predicate circuits over the same primary inputs. -/
def BooleanCircuitIO.andPredicates {inputCount : ℕ}
    (first second : BooleanCircuitIO inputCount 1) : BooleanCircuitIO inputCount 1 :=
  let paired := BooleanCircuitIO.pairPredicates first second
  paired.compose BooleanCircuitIO.and
    (Fin.cases (paired.outputs 0) (fun _ => paired.outputs 1))

theorem BooleanCircuitIO.andPredicates_gateCount {inputCount : ℕ}
    (first second : BooleanCircuitIO inputCount 1) :
    (BooleanCircuitIO.andPredicates first second).gateCount =
      first.gateCount + second.gateCount + 2 := by
  rw [BooleanCircuitIO.andPredicates, BooleanCircuitIO.compose_gateCount,
    BooleanCircuitIO.pairPredicates_gateCount, BooleanCircuitIO.and_gateCount]

/-- Predicate conjunction has exactly the ordinary Boolean-and semantics. -/
theorem BooleanCircuitIO.eval_andPredicates {inputCount : ℕ}
    (first second : BooleanCircuitIO inputCount 1)
    (inputs : Fin inputCount → Bool) :
    (BooleanCircuitIO.andPredicates first second).eval inputs 0 =
      (first.eval inputs 0 && second.eval inputs 0) := by
  unfold BooleanCircuitIO.andPredicates
  dsimp
  rw [BooleanCircuitIO.eval_compose, BooleanCircuitIO.eval_and]
  change
    ((BooleanCircuitIO.pairPredicates first second).eval inputs 0 &&
      (BooleanCircuitIO.pairPredicates first second).eval inputs 1) = _
  rw [BooleanCircuitIO.eval_pairPredicates_first,
    BooleanCircuitIO.eval_pairPredicates_second]

/-- A half-open interval of unsigned fixed-grid codes.  `upper = none`
denotes the final, unbounded-above bin; it includes the all-ones code. -/
structure UnsignedHalfOpenInterval (width : ℕ) where
  lower : BitVec width
  upper : Option (BitVec width)

/-- The literal Boolean predicate for membership in one fixed-grid interval. -/
def UnsignedHalfOpenInterval.circuit {width : ℕ}
    (interval : UnsignedHalfOpenInterval width) : BooleanCircuitIO width 1 :=
  match interval.upper with
  | none => BooleanCircuitIO.atLeastConstant width interval.lower
  | some upper => BooleanCircuitIO.andPredicates
      (BooleanCircuitIO.atLeastConstant width interval.lower)
      (BooleanCircuitIO.lessThanConstant width upper)

/-- Every fixed-grid interval test has linear size in the code width. -/
theorem UnsignedHalfOpenInterval.circuit_gateCount_le {width : ℕ}
    (interval : UnsignedHalfOpenInterval width) :
    interval.circuit.gateCount ≤ 20 * width + 5 := by
  cases hupper : interval.upper with
  | none =>
      simp only [UnsignedHalfOpenInterval.circuit, hupper]
      have hsize := BooleanCircuitIO.atLeastConstant_gateCount_le width interval.lower
      omega
  | some upper =>
      simp only [UnsignedHalfOpenInterval.circuit, hupper,
        BooleanCircuitIO.andPredicates_gateCount]
      have hlower := BooleanCircuitIO.atLeastConstant_gateCount_le width interval.lower
      have hupperSize := BooleanCircuitIO.lessThanConstant_gateCount_le width upper
      omega

/-- Boolean numerical membership in a half-open fixed-grid interval. -/
def UnsignedHalfOpenInterval.contains {width : ℕ}
    (interval : UnsignedHalfOpenInterval width) (input : BitVec width) : Bool :=
  decide (interval.lower.toNat ≤ input.toNat) &&
    match interval.upper with
    | none => true
    | some upper => decide (input.toNat < upper.toNat)

/-- The interval circuit decides exactly its half-open unsigned order test. -/
theorem UnsignedHalfOpenInterval.eval_circuit_bitVec {width : ℕ}
    (interval : UnsignedHalfOpenInterval width) (input : BitVec width) :
    interval.circuit.eval (BooleanCircuitIO.bitVecBits input) 0 =
      interval.contains input := by
  cases hupper : interval.upper with
  | none =>
      simp only [UnsignedHalfOpenInterval.circuit, hupper]
      rw [BooleanCircuitIO.eval_atLeastConstant_bitVec]
      simp [UnsignedHalfOpenInterval.contains, hupper]
  | some upper =>
      simp only [UnsignedHalfOpenInterval.circuit, hupper]
      rw [
        BooleanCircuitIO.eval_andPredicates,
        BooleanCircuitIO.eval_atLeastConstant_bitVec,
        BooleanCircuitIO.eval_lessThanConstant_bitVec]
      unfold UnsignedHalfOpenInterval.contains
      rw [hupper]

/-- Lift a one-output predicate to a larger primary-input layout by supplying
each of its inputs from a chosen primary wire. -/
def BooleanCircuitIO.liftPredicate {inputCount targetInputCount : ℕ}
    (predicate : BooleanCircuitIO inputCount 1)
    (inputMap : Fin inputCount → BooleanWire targetInputCount 0) :
    BooleanCircuitIO targetInputCount 1 :=
  (BooleanCircuitIO.empty targetInputCount).compose predicate inputMap

theorem BooleanCircuitIO.liftPredicate_gateCount {inputCount targetInputCount : ℕ}
    (predicate : BooleanCircuitIO inputCount 1)
    (inputMap : Fin inputCount → BooleanWire targetInputCount 0) :
    (BooleanCircuitIO.liftPredicate predicate inputMap).gateCount = predicate.gateCount := by
  change 0 + predicate.gateCount = predicate.gateCount
  exact Nat.zero_add _

theorem BooleanCircuitIO.eval_liftPredicate {inputCount targetInputCount : ℕ}
    (predicate : BooleanCircuitIO inputCount 1)
    (inputMap : Fin inputCount → BooleanWire targetInputCount 0)
    (inputs : Fin targetInputCount → Bool) :
    (BooleanCircuitIO.liftPredicate predicate inputMap).eval inputs 0 =
      predicate.eval (fun inputBit => (inputMap inputBit).eval inputs Fin.elim0) 0 := by
  rw [BooleanCircuitIO.liftPredicate, BooleanCircuitIO.eval_compose]
  rfl

/-- A finite family of single-output Boolean circuits over one shared input
encoding.  This is the appropriate interface when a paper assumes that a
family of predicates, rather than arbitrary finite sets, has small circuits. -/
structure BooleanPredicateCircuitFamily (Input Index : Type*) where
  inputCount : ℕ
  encode : Input → Fin inputCount → Bool
  circuit : Index → BooleanCircuit
  inputCount_eq : ∀ index, (circuit index).inputCount = inputCount
  outputCount_eq : ∀ index, (circuit index).outputCount = 1
  sizeBound : ℕ
  size_le : ∀ index, (circuit index).gateCount ≤ sizeBound

/-- Evaluate the designated output of one predicate circuit on an encoded
input.  The casts are justified by the family-wide input/output arities. -/
def BooleanPredicateCircuitFamily.eval
    {Input Index : Type*} (family : BooleanPredicateCircuitFamily Input Index)
    (index : Index) (input : Input) : Bool :=
  (family.circuit index).eval
    (fun bit => family.encode input (Fin.cast (family.inputCount_eq index) bit))
    (Fin.cast (family.outputCount_eq index).symm 0)

end AppliedModelingLib.Computation
