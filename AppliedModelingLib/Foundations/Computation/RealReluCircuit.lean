import AppliedModelingLib.Foundations.Computation.ThreeCNF
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Finite scalar ReLU circuits

An inductive, acyclic computation-graph representation of scalar feedforward
ReLU networks.  It is deliberately small: inputs, real constants, affine
addition/subtraction gates, and ReLU gates.  The syntax is sufficient for
explicit reductions to box-constrained scalar-network optimization.

Before this module was written, the pinned Mathlib checkout and public Lean
repositories were searched for a compatible ReLU-network verification
reduction.  None was found.  No external code or proof was copied or ported.
The only imported foundations are Mathlib (Apache-2.0 at the repository's
pinned revision) and this repository's credited finite three-CNF semantics.
-/

namespace AppliedModelingLib.Computation

/-- A finite acyclic scalar circuit with affine and ReLU gates. -/
inductive RealReluCircuit (inputCount : ℕ) where
  | input : Fin inputCount → RealReluCircuit inputCount
  | constant : ℝ → RealReluCircuit inputCount
  | add : RealReluCircuit inputCount → RealReluCircuit inputCount →
      RealReluCircuit inputCount
  | sub : RealReluCircuit inputCount → RealReluCircuit inputCount →
      RealReluCircuit inputCount
  | relu : RealReluCircuit inputCount → RealReluCircuit inputCount

namespace RealReluCircuit

/-- Evaluation of a finite scalar ReLU circuit. -/
noncomputable def eval {inputCount : ℕ} :
    RealReluCircuit inputCount → (Fin inputCount → ℝ) → ℝ
  | .input i, x => x i
  | .constant c, _ => c
  | .add left right, x => left.eval x + right.eval x
  | .sub left right, x => left.eval x - right.eval x
  | .relu inner, x => max (inner.eval x) 0

/-- Number of syntax nodes, a concrete representation-size measure. -/
def nodeCount {inputCount : ℕ} : RealReluCircuit inputCount → ℕ
  | .input _ => 1
  | .constant _ => 1
  | .add left right => 1 + left.nodeCount + right.nodeCount
  | .sub left right => 1 + left.nodeCount + right.nodeCount
  | .relu inner => 1 + inner.nodeCount

/-- Every explicit constant in a circuit is either zero or one. -/
def UsesOnlyZeroOneConstants {inputCount : ℕ} : RealReluCircuit inputCount → Prop
  | .input _ => True
  | .constant value => value = 0 ∨ value = 1
  | .add left right => left.UsesOnlyZeroOneConstants ∧ right.UsesOnlyZeroOneConstants
  | .sub left right => left.UsesOnlyZeroOneConstants ∧ right.UsesOnlyZeroOneConstants
  | .relu inner => inner.UsesOnlyZeroOneConstants

/-- `max accumulated new`, arranged so the accumulated circuit occurs once. -/
def maxWithNew {inputCount : ℕ} (new accumulated : RealReluCircuit inputCount) :
    RealReluCircuit inputCount :=
  .add (.relu (.sub accumulated new)) new

/-- `min new accumulated`, arranged so the accumulated circuit occurs once. -/
def minWithNew {inputCount : ℕ} (new accumulated : RealReluCircuit inputCount) :
    RealReluCircuit inputCount :=
  .sub new (.relu (.sub new accumulated))

lemma usesOnlyZeroOneConstants_maxWithNew {inputCount : ℕ}
    {new accumulated : RealReluCircuit inputCount}
    (hnew : new.UsesOnlyZeroOneConstants)
    (haccumulated : accumulated.UsesOnlyZeroOneConstants) :
    (maxWithNew new accumulated).UsesOnlyZeroOneConstants := by
  exact ⟨⟨haccumulated, hnew⟩, hnew⟩

lemma usesOnlyZeroOneConstants_minWithNew {inputCount : ℕ}
    {new accumulated : RealReluCircuit inputCount}
    (hnew : new.UsesOnlyZeroOneConstants)
    (haccumulated : accumulated.UsesOnlyZeroOneConstants) :
    (minWithNew new accumulated).UsesOnlyZeroOneConstants := by
  exact ⟨hnew, hnew, haccumulated⟩

@[simp] theorem eval_input {inputCount : ℕ} (i : Fin inputCount)
    (x : Fin inputCount → ℝ) :
    (RealReluCircuit.input i).eval x = x i := rfl

@[simp] theorem eval_constant {inputCount : ℕ} (c : ℝ)
    (x : Fin inputCount → ℝ) :
    (RealReluCircuit.constant c : RealReluCircuit inputCount).eval x = c := rfl

@[simp] theorem eval_add {inputCount : ℕ} (left right : RealReluCircuit inputCount)
    (x : Fin inputCount → ℝ) :
    (RealReluCircuit.add left right).eval x = left.eval x + right.eval x := rfl

@[simp] theorem eval_sub {inputCount : ℕ} (left right : RealReluCircuit inputCount)
    (x : Fin inputCount → ℝ) :
    (RealReluCircuit.sub left right).eval x = left.eval x - right.eval x := rfl

@[simp] theorem eval_relu {inputCount : ℕ} (inner : RealReluCircuit inputCount)
    (x : Fin inputCount → ℝ) :
    (RealReluCircuit.relu inner).eval x = max (inner.eval x) 0 := rfl

@[simp] theorem eval_maxWithNew {inputCount : ℕ}
    (new accumulated : RealReluCircuit inputCount) (x : Fin inputCount → ℝ) :
    (maxWithNew new accumulated).eval x = max (accumulated.eval x) (new.eval x) := by
  rw [maxWithNew, eval_add, eval_relu, eval_sub]
  rcases le_total (accumulated.eval x) (new.eval x) with h | h
  · rw [max_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    ring

@[simp] theorem eval_minWithNew {inputCount : ℕ}
    (new accumulated : RealReluCircuit inputCount) (x : Fin inputCount → ℝ) :
    (minWithNew new accumulated).eval x = min (new.eval x) (accumulated.eval x) := by
  rw [minWithNew, eval_sub, eval_relu, eval_sub]
  rcases le_total (new.eval x) (accumulated.eval x) with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    ring

@[simp] theorem nodeCount_maxWithNew {inputCount : ℕ}
    (new accumulated : RealReluCircuit inputCount) :
    (maxWithNew new accumulated).nodeCount = 3 + 2 * new.nodeCount + accumulated.nodeCount := by
  simp [maxWithNew, nodeCount]
  omega

@[simp] theorem nodeCount_minWithNew {inputCount : ℕ}
    (new accumulated : RealReluCircuit inputCount) :
    (minWithNew new accumulated).nodeCount = 3 + 2 * new.nodeCount + accumulated.nodeCount := by
  simp [minWithNew, nodeCount]
  omega

/-- Real score of a signed literal: `x` for positive, `1-x` for negative. -/
def literalCircuit {inputCount : ℕ} (literal : ThreeCNFLiteral (Fin inputCount)) :
    RealReluCircuit inputCount :=
  if literal.2 then .input literal.1 else .sub (.constant 1) (.input literal.1)

/-- Maximum of the three real literal scores in one clause. -/
def clauseCircuit {inputCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin inputCount) (Fin clauseCount)) (clause : Fin clauseCount) :
    RealReluCircuit inputCount :=
  maxWithNew (literalCircuit (formula.literal clause 2))
    (maxWithNew (literalCircuit (formula.literal clause 1))
      (literalCircuit (formula.literal clause 0)))

/-- Minimum of all clause scores, with the empty conjunction assigned score one. -/
def formulaCircuit {inputCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin inputCount) (Fin clauseCount)) :
    RealReluCircuit inputCount :=
  (List.ofFn fun clause => clauseCircuit formula clause).foldr
    minWithNew (.constant 1)

lemma usesOnlyZeroOneConstants_literalCircuit {inputCount : ℕ}
    (literal : ThreeCNFLiteral (Fin inputCount)) :
    (literalCircuit literal).UsesOnlyZeroOneConstants := by
  cases h : literal.2 <;> simp [literalCircuit, h, UsesOnlyZeroOneConstants]

lemma usesOnlyZeroOneConstants_clauseCircuit {inputCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin inputCount) (Fin clauseCount)) (clause : Fin clauseCount) :
    (clauseCircuit formula clause).UsesOnlyZeroOneConstants := by
  apply usesOnlyZeroOneConstants_maxWithNew
  · exact usesOnlyZeroOneConstants_literalCircuit _
  · apply usesOnlyZeroOneConstants_maxWithNew <;>
      exact usesOnlyZeroOneConstants_literalCircuit _

lemma usesOnlyZeroOneConstants_foldr_minWithNew {inputCount : ℕ}
    {circuits : List (RealReluCircuit inputCount)}
    (hcircuits : ∀ circuit ∈ circuits, circuit.UsesOnlyZeroOneConstants) :
    (circuits.foldr minWithNew (.constant 1)).UsesOnlyZeroOneConstants := by
  induction circuits with
  | nil => simp [UsesOnlyZeroOneConstants]
  | cons head tail ih =>
      apply usesOnlyZeroOneConstants_minWithNew
      · exact hcircuits head (by simp)
      · exact ih (by
          intro circuit hcircuit
          exact hcircuits circuit (by simp [hcircuit]))

/-- The three-CNF reduction circuit has no non-unit explicit constants. -/
theorem usesOnlyZeroOneConstants_formulaCircuit {inputCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin inputCount) (Fin clauseCount)) :
    (formulaCircuit formula).UsesOnlyZeroOneConstants := by
  apply usesOnlyZeroOneConstants_foldr_minWithNew
  intro circuit hcircuit
  simp only [List.mem_ofFn] at hcircuit
  obtain ⟨clause, rfl⟩ := hcircuit
  exact usesOnlyZeroOneConstants_clauseCircuit formula clause

/-- The box `[0,1]^inputCount`. -/
def InUnitBox {inputCount : ℕ} (x : Fin inputCount → ℝ) : Prop :=
  ∀ i, 0 ≤ x i ∧ x i ≤ 1

/-- Embed a Boolean assignment as a vertex of the unit box. -/
def realAssignment {inputCount : ℕ} (assignment : Fin inputCount → Bool) :
    Fin inputCount → ℝ :=
  fun i => if assignment i then 1 else 0

/-- Round only exact upper endpoints to `true`; all other coordinates become `false`. -/
noncomputable def booleanAssignment {inputCount : ℕ} (x : Fin inputCount → ℝ) :
    Fin inputCount → Bool :=
  fun i => decide (x i = 1)

lemma realAssignment_inUnitBox {inputCount : ℕ} (assignment : Fin inputCount → Bool) :
    InUnitBox (realAssignment assignment) := by
  intro i
  cases h : assignment i <;> simp [realAssignment, h]

@[simp] theorem eval_literalCircuit {inputCount : ℕ}
    (literal : ThreeCNFLiteral (Fin inputCount)) (x : Fin inputCount → ℝ) :
    (literalCircuit literal).eval x = if literal.2 then x literal.1 else 1 - x literal.1 := by
  cases h : literal.2 <;> simp [literalCircuit, h]

lemma eval_literalCircuit_mem_unitInterval {inputCount : ℕ}
    (literal : ThreeCNFLiteral (Fin inputCount)) {x : Fin inputCount → ℝ}
    (hx : InUnitBox x) :
    0 ≤ (literalCircuit literal).eval x ∧ (literalCircuit literal).eval x ≤ 1 := by
  rw [eval_literalCircuit]
  cases literal.2 <;> simp
  · constructor <;> linarith [hx literal.1]
  · exact hx literal.1

lemma eval_literalCircuit_realAssignment_eq_one_iff {inputCount : ℕ}
    (literal : ThreeCNFLiteral (Fin inputCount)) (assignment : Fin inputCount → Bool) :
    (literalCircuit literal).eval (realAssignment assignment) = 1 ↔
      ThreeCNF.SatisfiesLiteral assignment literal := by
  rcases literal with ⟨variableIndex, sign⟩
  cases hsign : sign <;> cases hassignment : assignment variableIndex <;>
    simp [eval_literalCircuit, realAssignment, ThreeCNF.SatisfiesLiteral, hassignment]

lemma satisfiesLiteral_booleanAssignment_of_eval_eq_one {inputCount : ℕ}
    (literal : ThreeCNFLiteral (Fin inputCount)) {x : Fin inputCount → ℝ}
    (heval : (literalCircuit literal).eval x = 1) :
    ThreeCNF.SatisfiesLiteral (booleanAssignment x) literal := by
  rcases literal with ⟨variableIndex, sign⟩
  cases hsign : sign
  · have hxzero : x variableIndex = 0 := by
      simp [eval_literalCircuit, hsign] at heval
      linarith
    simp [ThreeCNF.SatisfiesLiteral, booleanAssignment, hxzero]
  · have hxone : x variableIndex = 1 := by
      simpa [eval_literalCircuit, hsign] using heval
    simp [ThreeCNF.SatisfiesLiteral, booleanAssignment, hxone]

@[simp] theorem eval_clauseCircuit {inputCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin inputCount) (Fin clauseCount)) (clause : Fin clauseCount)
    (x : Fin inputCount → ℝ) :
    (clauseCircuit formula clause).eval x =
      max ((literalCircuit (formula.literal clause 0)).eval x)
        (max ((literalCircuit (formula.literal clause 1)).eval x)
          ((literalCircuit (formula.literal clause 2)).eval x)) := by
  simp [clauseCircuit, max_assoc]

lemma eval_clauseCircuit_le_one {inputCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin inputCount) (Fin clauseCount)) (clause : Fin clauseCount)
    {x : Fin inputCount → ℝ} (hx : InUnitBox x) :
    (clauseCircuit formula clause).eval x ≤ 1 := by
  rw [eval_clauseCircuit]
  exact max_le
    (eval_literalCircuit_mem_unitInterval _ hx).2
    (max_le (eval_literalCircuit_mem_unitInterval _ hx).2
      (eval_literalCircuit_mem_unitInterval _ hx).2)

lemma one_le_eval_clauseCircuit_iff {inputCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin inputCount) (Fin clauseCount)) (clause : Fin clauseCount)
    {x : Fin inputCount → ℝ} (hx : InUnitBox x) :
    1 ≤ (clauseCircuit formula clause).eval x ↔
      ∃ slot, (literalCircuit (formula.literal clause slot)).eval x = 1 := by
  rw [eval_clauseCircuit]
  constructor
  · intro h
    rcases le_max_iff.mp h with h0 | h12
    · exact ⟨0, le_antisymm (eval_literalCircuit_mem_unitInterval _ hx).2 h0⟩
    · rcases le_max_iff.mp h12 with h1 | h2
      · exact ⟨1, le_antisymm (eval_literalCircuit_mem_unitInterval _ hx).2 h1⟩
      · exact ⟨2, le_antisymm (eval_literalCircuit_mem_unitInterval _ hx).2 h2⟩
  · rintro ⟨slot, hslot⟩
    fin_cases slot
    · have hs : (literalCircuit (formula.literal clause 0)).eval x = 1 := by
        simpa using hslot
      rw [hs]
      exact le_max_left _ _
    · have hs : (literalCircuit (formula.literal clause 1)).eval x = 1 := by
        simpa using hslot
      rw [hs]
      exact le_max_of_le_right (le_max_left _ _)
    · have hs : (literalCircuit (formula.literal clause 2)).eval x = 1 := by
        simpa using hslot
      rw [hs]
      exact le_max_of_le_right (le_max_right _ _)

lemma eval_foldr_minWithNew {inputCount : ℕ}
    (circuits : List (RealReluCircuit inputCount)) (x : Fin inputCount → ℝ) :
    (circuits.foldr minWithNew (.constant 1)).eval x =
      (circuits.map fun circuit => circuit.eval x).foldr min 1 := by
  induction circuits with
  | nil => simp
  | cons head tail ih => simp [ih]

@[simp] theorem eval_formulaCircuit {inputCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin inputCount) (Fin clauseCount))
    (x : Fin inputCount → ℝ) :
    (formulaCircuit formula).eval x =
      ((List.ofFn fun clause => (clauseCircuit formula clause).eval x).foldr min 1) := by
  simp [formulaCircuit, eval_foldr_minWithNew, Function.comp_def]

lemma one_le_foldr_min_iff (values : List ℝ) :
    1 ≤ values.foldr min 1 ↔ ∀ value ∈ values, 1 ≤ value := by
  induction values with
  | nil => simp
  | cons head tail ih => simp [ih]

lemma one_le_eval_formulaCircuit_iff {inputCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin inputCount) (Fin clauseCount))
    {x : Fin inputCount → ℝ} (hx : InUnitBox x) :
    1 ≤ (formulaCircuit formula).eval x ↔
      ∀ clause, ∃ slot, (literalCircuit (formula.literal clause slot)).eval x = 1 := by
  rw [eval_formulaCircuit, one_le_foldr_min_iff]
  constructor
  · intro hall clause
    have hclause := hall ((clauseCircuit formula clause).eval x) (by simp)
    exact (one_le_eval_clauseCircuit_iff formula clause hx).mp hclause
  · intro hall value hvalue
    simp only [List.mem_ofFn] at hvalue
    obtain ⟨clause, rfl⟩ := hvalue
    exact (one_le_eval_clauseCircuit_iff formula clause hx).mpr (hall clause)

/--
The explicit box-constrained scalar ReLU circuit reaches threshold one exactly
when the input three-CNF is satisfiable.
-/
theorem satisfiable_iff_exists_unitBox_formulaCircuit {inputCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin inputCount) (Fin clauseCount)) :
    formula.Satisfiable ↔
      ∃ x : Fin inputCount → ℝ, InUnitBox x ∧ 1 ≤ (formulaCircuit formula).eval x := by
  constructor
  · rintro ⟨assignment, hsatisfies⟩
    refine ⟨realAssignment assignment, realAssignment_inUnitBox assignment, ?_⟩
    rw [one_le_eval_formulaCircuit_iff formula (realAssignment_inUnitBox assignment)]
    intro clause
    obtain ⟨slot, hslot⟩ := hsatisfies clause
    exact ⟨slot, (eval_literalCircuit_realAssignment_eq_one_iff _ _).2 hslot⟩
  · rintro ⟨x, hx, hthreshold⟩
    refine ⟨booleanAssignment x, ?_⟩
    rw [one_le_eval_formulaCircuit_iff formula hx] at hthreshold
    intro clause
    obtain ⟨slot, hslot⟩ := hthreshold clause
    exact ⟨slot, satisfiesLiteral_booleanAssignment_of_eval_eq_one _ hslot⟩

lemma nodeCount_literalCircuit_le_three {inputCount : ℕ}
    (literal : ThreeCNFLiteral (Fin inputCount)) :
    (literalCircuit literal).nodeCount ≤ 3 := by
  cases h : literal.2 <;> simp [literalCircuit, h, nodeCount]

lemma nodeCount_clauseCircuit_le_twentyOne {inputCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin inputCount) (Fin clauseCount)) (clause : Fin clauseCount) :
    (clauseCircuit formula clause).nodeCount ≤ 21 := by
  rw [clauseCircuit, nodeCount_maxWithNew, nodeCount_maxWithNew]
  have h0 := nodeCount_literalCircuit_le_three (formula.literal clause 0)
  have h1 := nodeCount_literalCircuit_le_three (formula.literal clause 1)
  have h2 := nodeCount_literalCircuit_le_three (formula.literal clause 2)
  omega

lemma nodeCount_foldr_minWithNew_le {inputCount : ℕ}
    (circuits : List (RealReluCircuit inputCount))
    (hsize : ∀ circuit ∈ circuits, circuit.nodeCount ≤ 21) :
    (circuits.foldr minWithNew (.constant 1)).nodeCount ≤ 45 * circuits.length + 1 := by
  induction circuits with
  | nil => simp [nodeCount]
  | cons head tail ih =>
      simp only [List.foldr_cons, nodeCount_minWithNew, List.length_cons]
      have hhead := hsize head (by simp)
      have htail : ∀ circuit ∈ tail, circuit.nodeCount ≤ 21 := by
        intro circuit hcircuit
        exact hsize circuit (by simp [hcircuit])
      have hi := ih htail
      omega

/-- The reduction circuit has at most `45 * clauseCount + 1` syntax nodes. -/
theorem nodeCount_formulaCircuit_le {inputCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin inputCount) (Fin clauseCount)) :
    (formulaCircuit formula).nodeCount ≤ 45 * clauseCount + 1 := by
  rw [formulaCircuit]
  have h := nodeCount_foldr_minWithNew_le
    (List.ofFn fun clause => clauseCircuit formula clause) (by
      intro circuit hcircuit
      simp only [List.mem_ofFn] at hcircuit
      obtain ⟨clause, rfl⟩ := hcircuit
      exact nodeCount_clauseCircuit_le_twentyOne formula clause)
  simpa using h

end RealReluCircuit
end AppliedModelingLib.Computation
