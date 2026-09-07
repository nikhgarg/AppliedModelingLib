import Mathlib.Data.Fintype.Order

/-!
# Finite three-CNF semantics

A small typed semantic layer for reductions that start from a three-CNF
formula.  Machine encodings and complexity classes deliberately live outside
this module: the declarations here isolate the finite mathematical fact that a
three-CNF is satisfiable exactly when one can choose a mutually consistent
literal occurrence from every clause.

Before introducing this API, the repository and its pinned Mathlib were
searched for a finite 3SAT layer.  None was present.  Two upstream projects
were also inspected: `SamuelSchlesinger/complexitylib` and
`PierreSenellart/descriptive-complexity`.  Both are Apache-2.0 and provide
machine-checked 3SAT completeness, but their available 3SAT revisions target
later Lean/Mathlib pins than this repository's `v4.30.0-rc2`.  No definition,
statement, or proof below is copied or ported from either project.
-/

namespace AppliedModelingLib.Computation

/-- A literal is a variable together with the Boolean value that satisfies it. -/
abbrev ThreeCNFLiteral (Variable : Type*) := Variable × Bool

/-- A typed three-CNF has exactly three literal occurrences in every clause. -/
structure ThreeCNF (Variable Clause : Type*) where
  literal : Clause → Fin 3 → ThreeCNFLiteral Variable

namespace ThreeCNF

variable {Variable Clause : Type*}

/-- A Boolean assignment satisfies a literal when it gives its displayed sign. -/
def SatisfiesLiteral (assignment : Variable → Bool)
    (literal : ThreeCNFLiteral Variable) : Prop :=
  assignment literal.1 = literal.2

/-- Standard semantic satisfiability for a typed three-CNF. -/
def Satisfiable (formula : ThreeCNF Variable Clause) : Prop :=
  ∃ assignment : Variable → Bool, ∀ clause, ∃ slot,
    SatisfiesLiteral assignment (formula.literal clause slot)

/-- Two literal occurrences contradict when they require opposite values of one variable. -/
def Contradictory (left right : ThreeCNFLiteral Variable) : Prop :=
  left.1 = right.1 ∧ left.2 ≠ right.2

/-- Literal contradiction is symmetric. -/
theorem contradictory_comm (left right : ThreeCNFLiteral Variable) :
    Contradictory left right ↔ Contradictory right left := by
  constructor <;> rintro ⟨hvariable, hsign⟩
  · exact ⟨hvariable.symm, hsign.symm⟩
  · exact ⟨hvariable.symm, hsign.symm⟩

/-- The literal occurrence selected from a clause by `choice`. -/
def selectedLiteral (formula : ThreeCNF Variable Clause)
    (choice : Clause → Fin 3) (clause : Clause) : ThreeCNFLiteral Variable :=
  formula.literal clause (choice clause)

/-- A clausewise choice is consistent when choices from distinct clauses never contradict. -/
def PairwiseCompatible (formula : ThreeCNF Variable Clause)
    (choice : Clause → Fin 3) : Prop :=
  ∀ (left right : Clause), left ≠ right →
    ¬ Contradictory (selectedLiteral formula choice left)
      (selectedLiteral formula choice right)

/-- The assignment canonically induced by a compatible clausewise choice. -/
noncomputable def assignmentOfChoice (formula : ThreeCNF Variable Clause)
    (choice : Clause → Fin 3) (v : Variable) : Bool := by
  classical
  exact if ∃ clause,
        (selectedLiteral formula choice clause).1 = v ∧
          (selectedLiteral formula choice clause).2 = true
      then true else false

/-- Every selected literal of a compatible choice is true under its canonical assignment. -/
theorem satisfiesLiteral_assignmentOfChoice
    (formula : ThreeCNF Variable Clause) (choice : Clause → Fin 3)
    (hcompatible : PairwiseCompatible formula choice) (clause : Clause) :
    SatisfiesLiteral (assignmentOfChoice formula choice)
      (selectedLiteral formula choice clause) := by
  classical
  let chosen := selectedLiteral formula choice clause
  by_cases hpositive : chosen.2 = true
  · have hexists : ∃ other,
        (selectedLiteral formula choice other).1 = chosen.1 ∧
          (selectedLiteral formula choice other).2 = true :=
      ⟨clause, rfl, hpositive⟩
    simp [SatisfiesLiteral, assignmentOfChoice, chosen, hexists, hpositive]
  · have hnegative : chosen.2 = false := Bool.eq_false_of_not_eq_true hpositive
    have hnoPositive : ¬ ∃ other,
        (selectedLiteral formula choice other).1 = chosen.1 ∧
          (selectedLiteral formula choice other).2 = true := by
      rintro ⟨other, hsameVariable, hotherPositive⟩
      by_cases hsameClause : other = clause
      · subst other
        exact hpositive hotherPositive
      · exact hcompatible other clause hsameClause
          ⟨hsameVariable, by
            have hclauseNegative :
                (selectedLiteral formula choice clause).2 = false := by
              simpa only [chosen] using hnegative
            simp [hotherPositive, hclauseNegative]⟩
    simp [SatisfiesLiteral, assignmentOfChoice, chosen, hnoPositive, hnegative]

/--
A three-CNF is satisfiable exactly when it admits one pairwise compatible
literal occurrence per clause.
-/
theorem satisfiable_iff_exists_pairwiseCompatible (formula : ThreeCNF Variable Clause) :
    formula.Satisfiable ↔ ∃ choice : Clause → Fin 3,
      formula.PairwiseCompatible choice := by
  classical
  constructor
  · rintro ⟨assignment, hsatisfies⟩
    choose choice hchoice using hsatisfies
    refine ⟨choice, ?_⟩
    intro left right _ hcontradictory
    have hleft := hchoice left
    have hright := hchoice right
    change SatisfiesLiteral assignment (selectedLiteral formula choice left) at hleft
    change SatisfiesLiteral assignment (selectedLiteral formula choice right) at hright
    unfold SatisfiesLiteral at hleft hright
    exact hcontradictory.2 (by
      rw [← hleft, ← hright, hcontradictory.1])
  · rintro ⟨choice, hcompatible⟩
    refine ⟨assignmentOfChoice formula choice, ?_⟩
    intro clause
    exact ⟨choice clause,
      satisfiesLiteral_assignmentOfChoice formula choice hcompatible clause⟩

/-! ## Satisfiability-preserving finite padding -/

/-- Embed an old finite variable into a type with one fresh variable. -/
def embedFinVariable {variableCount : ℕ} (oldVariable : Fin variableCount) :
    Fin (variableCount + 1) :=
  ⟨oldVariable, Nat.lt_succ_of_lt oldVariable.isLt⟩

/-- The fresh variable added by finite clause padding. -/
def freshFinVariable (variableCount : ℕ) : Fin (variableCount + 1) :=
  ⟨variableCount, Nat.lt_succ_self variableCount⟩

/--
Pad a finite three-CNF table to at least three clauses.  Original clauses are
embedded verbatim; each new clause consists of three copies of one fresh
positive literal and is therefore simultaneously satisfiable.
-/
def padToAtLeastThreeClauses {variableCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin variableCount) (Fin clauseCount)) :
    ThreeCNF (Fin (variableCount + 1)) (Fin (max 3 clauseCount)) where
  literal clause slot :=
    if hclause : clause.val < clauseCount then
      let original := formula.literal ⟨clause.val, hclause⟩ slot
      (embedFinVariable original.1, original.2)
    else
      (freshFinVariable variableCount, true)

/-- Finite padding preserves and reflects three-CNF satisfiability. -/
theorem padToAtLeastThreeClauses_satisfiable_iff
    {variableCount clauseCount : ℕ}
    (formula : ThreeCNF (Fin variableCount) (Fin clauseCount)) :
    (padToAtLeastThreeClauses formula).Satisfiable ↔ formula.Satisfiable := by
  classical
  constructor
  · rintro ⟨assignment, hassignment⟩
    refine ⟨fun oldVariable => assignment (embedFinVariable oldVariable), ?_⟩
    intro clause
    have hclauseBound : clause.val < max 3 clauseCount :=
      clause.isLt.trans_le (le_max_right 3 clauseCount)
    let paddedClause : Fin (max 3 clauseCount) := ⟨clause.val, hclauseBound⟩
    obtain ⟨slot, hslot⟩ := hassignment paddedClause
    refine ⟨slot, ?_⟩
    simpa [SatisfiesLiteral, padToAtLeastThreeClauses, paddedClause,
      clause.isLt] using hslot
  · rintro ⟨assignment, hassignment⟩
    let paddedAssignment : Fin (variableCount + 1) → Bool :=
      fun paddedVariable =>
        if hvariable : paddedVariable.val < variableCount then
          assignment ⟨paddedVariable.val, hvariable⟩
        else true
    refine ⟨paddedAssignment, ?_⟩
    intro clause
    by_cases hclause : clause.val < clauseCount
    · let originalClause : Fin clauseCount := ⟨clause.val, hclause⟩
      obtain ⟨slot, hslot⟩ := hassignment originalClause
      refine ⟨slot, ?_⟩
      simpa [SatisfiesLiteral, padToAtLeastThreeClauses, paddedAssignment,
        originalClause, hclause, embedFinVariable] using hslot
    · refine ⟨0, ?_⟩
      simp [SatisfiesLiteral, padToAtLeastThreeClauses, paddedAssignment,
        hclause, freshFinVariable]

end ThreeCNF

end AppliedModelingLib.Computation
