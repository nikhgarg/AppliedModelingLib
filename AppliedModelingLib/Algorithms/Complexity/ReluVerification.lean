import AppliedModelingLib.Algorithms.Complexity.Classes
import AppliedModelingLib.Foundations.Computation.RealReluCircuit

/-!
# Three-CNF reductions to scalar ReLU optimization

This module packages the explicit finite reduction from three-CNF
satisfiability to threshold feasibility for a scalar ReLU circuit on a unit
box.  The reduction correctness and its linear circuit-size bound are checked
without assuming a complexity class or a machine encoding.  A separate
constructor upgrades it to the library's abstract polynomial-time-reduction
interface once a chosen encoding model proves the construction polynomial.

The mathematical construction is a direct reduction, not copied from an
external Lean development.  Before it was introduced, the pinned Mathlib
checkout and public Lean repositories were searched for a compatible
ReLU-verification reduction; none was found.
-/

namespace AppliedModelingLib.Complexity

open AppliedModelingLib.Computation

/-- A finite three-CNF formula with its variable and clause counts bundled. -/
structure FiniteThreeCNFInstance where
  variableCount : ℕ
  clauseCount : ℕ
  formula : ThreeCNF (Fin variableCount) (Fin clauseCount)

/-- The standard satisfiability language for bundled finite three-CNF formulas. -/
def FiniteThreeCNFSatisfiability : DecisionProblem FiniteThreeCNFInstance :=
  fun problem => problem.formula.Satisfiable

/--
A scalar ReLU threshold-feasibility problem.  Besides the circuit data, the
bundle records its decision predicate and proves that it is exactly threshold
feasibility on the unit box.  This makes the domain constraint part of the
problem semantics, rather than relying on a documentation convention.
-/
structure BoxReluThresholdInstance where
  inputCount : ℕ
  circuit : RealReluCircuit inputCount
  threshold : ℝ
  feasible : (Fin inputCount → ℝ) → Prop :=
    fun x => RealReluCircuit.InUnitBox x ∧ threshold ≤ circuit.eval x
  feasible_iff : ∀ x,
    feasible x ↔ RealReluCircuit.InUnitBox x ∧ threshold ≤ circuit.eval x := by
      intro x
      rfl

/-- Does a scalar ReLU circuit reach its threshold somewhere on the unit box? -/
def BoxReluThresholdDecision : DecisionProblem BoxReluThresholdInstance :=
  fun problem =>
    ∃ x : Fin problem.inputCount → ℝ, problem.feasible x

/--
The explicit reduction: literal scores are `x_i` or `1-x_i`, clauses take
their maximum literal score, and the formula takes the minimum clause score.
-/
def threeCNFToBoxReluThreshold
    (problem : FiniteThreeCNFInstance) : BoxReluThresholdInstance where
  inputCount := problem.variableCount
  circuit := RealReluCircuit.formulaCircuit problem.formula
  threshold := 1

/-- The explicit three-CNF-to-ReLU threshold map preserves the decision answer. -/
theorem finiteThreeCNFSatisfiability_iff_boxReluThresholdDecision
    (problem : FiniteThreeCNFInstance) :
    FiniteThreeCNFSatisfiability problem ↔
      BoxReluThresholdDecision (threeCNFToBoxReluThreshold problem) := by
  simpa only [BoxReluThresholdDecision,
    BoxReluThresholdInstance.feasible_iff] using
    RealReluCircuit.satisfiable_iff_exists_unitBox_formulaCircuit problem.formula

/-- The compiled direct many-one reduction from three-CNF satisfiability. -/
def finiteThreeCNFSatisfiability_manyOneReduction_boxReluThresholdDecision :
    ManyOneReduction FiniteThreeCNFSatisfiability BoxReluThresholdDecision where
  map := threeCNFToBoxReluThreshold
  correct := finiteThreeCNFSatisfiability_iff_boxReluThresholdDecision

/-- The target circuit has at most `45 * clauseCount + 1` syntax nodes. -/
theorem threeCNFToBoxReluThreshold_nodeCount_le
    (problem : FiniteThreeCNFInstance) :
    (threeCNFToBoxReluThreshold problem).circuit.nodeCount ≤
      45 * problem.clauseCount + 1 := by
  exact RealReluCircuit.nodeCount_formulaCircuit_le problem.formula

/-- The reduction introduces only zero/one explicit constants. -/
theorem threeCNFToBoxReluThreshold_usesOnlyZeroOneConstants
    (problem : FiniteThreeCNFInstance) :
    (threeCNFToBoxReluThreshold problem).circuit.UsesOnlyZeroOneConstants := by
  exact RealReluCircuit.usesOnlyZeroOneConstants_formulaCircuit problem.formula

/-- The reduction uses the strict coordinate bounds `0 < 1`. -/
theorem threeCNFToBoxReluThreshold_strictCoordinateBounds
    (problem : FiniteThreeCNFInstance)
    (coordinate : Fin (threeCNFToBoxReluThreshold problem).inputCount) :
    (0 : ℝ) < 1 := by
  positivity

/--
Upgrade the checked direct reduction to an abstract polynomial-time reduction
after a concrete encoding model verifies that its instance map is polynomial.
-/
def finiteThreeCNFSatisfiability_polynomialTimeReduction_boxReluThresholdDecision
    (PolynomialTime :
      (FiniteThreeCNFInstance → BoxReluThresholdInstance) → Prop)
    (hpolynomial : PolynomialTime threeCNFToBoxReluThreshold) :
    PolynomialTimeReduction FiniteThreeCNFSatisfiability BoxReluThresholdDecision where
  reduction := finiteThreeCNFSatisfiability_manyOneReduction_boxReluThresholdDecision
  PolynomialTime := PolynomialTime
  polynomialTime := hpolynomial

/--
Under any standard hardness model closed under polynomial many-one reductions,
three-CNF hardness transfers to scalar ReLU threshold feasibility.  The only
external computational premise is polynomiality in the selected encoding;
semantic correctness and linear output size are proved above.
-/
theorem boxReluThreshold_hard_of_threeCNFSatisfiability_hard
    (hardness : PolynomialReductionClosedHardness)
    (PolynomialTime :
      (FiniteThreeCNFInstance → BoxReluThresholdInstance) → Prop)
    (hpolynomial : PolynomialTime threeCNFToBoxReluThreshold)
    (hthreeCNF : hardness.Hard FiniteThreeCNFSatisfiability) :
    hardness.Hard BoxReluThresholdDecision := by
  exact hardness.apply
    (finiteThreeCNFSatisfiability_polynomialTimeReduction_boxReluThresholdDecision
      PolynomialTime hpolynomial)
    hthreeCNF

/-- A dependent exact optimizer for scalar ReLU circuits over their unit boxes. -/
abbrev BoxReluOptimizer :=
  (problem : BoxReluThresholdInstance) → Fin problem.inputCount → ℝ

/-- An optimizer is feasible and weakly dominates every feasible input. -/
def SolvesBoxReluOptimization (optimizer : BoxReluOptimizer) : Prop :=
  ∀ problem,
    RealReluCircuit.InUnitBox (optimizer problem) ∧
      ∀ x, RealReluCircuit.InUnitBox x →
        problem.circuit.eval x ≤ problem.circuit.eval (optimizer problem)

/--
One call to any exact box-constrained ReLU optimizer answers every reduced
three-CNF instance by comparing the returned objective value with one.
-/
theorem finiteThreeCNFSatisfiability_iff_optimizer_reaches_one
    (optimizer : BoxReluOptimizer) (hoptimizer : SolvesBoxReluOptimization optimizer)
    (problem : FiniteThreeCNFInstance) :
    FiniteThreeCNFSatisfiability problem ↔
      1 ≤ (threeCNFToBoxReluThreshold problem).circuit.eval
        (optimizer (threeCNFToBoxReluThreshold problem)) := by
  let target := threeCNFToBoxReluThreshold problem
  have hsolves := hoptimizer target
  constructor
  · intro hsatisfiable
    have htarget : BoxReluThresholdDecision target :=
      (finiteThreeCNFSatisfiability_iff_boxReluThresholdDecision problem).mp hsatisfiable
    obtain ⟨x, hx, hthreshold⟩ := htarget
    exact hthreshold.trans (hsolves.2 x hx)
  · intro hthreshold
    apply (finiteThreeCNFSatisfiability_iff_boxReluThresholdDecision problem).mpr
    exact ⟨optimizer target, hsolves.1, hthreshold⟩

end AppliedModelingLib.Complexity
