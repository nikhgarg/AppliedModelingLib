import AppliedModelingLib.Foundations.Probability.FiniteDistributionalRobustness
import AppliedModelingLib.Foundations.Probability.FiniteTransportMatrix

/-!
# Finite constrained distributionally robust optimization

This module connects finite fixed-nominal kernel matrices to pointwise robust
envelopes.  Together with the compact scalar Lagrange-duality theorem in
`FiniteTransportMatrix`, it supplies the finite-dimensional core of the
constrained Wasserstein-DRO equality: a transport-budget constrained value is
equal to the infimum over nonnegative penalties of the nominal expected
pointwise penalized envelope.

The module deliberately keeps the transport cost and the action and nominal
state types general.  A paper-specific source-to-model bridge can impose a
common state space and a zero diagonal cost to construct the strict feasible
kernel required by constrained strong duality.
-/

@[expose] public section

namespace AppliedModelingLib
namespace FiniteConstrainedDRO

open scoped BigOperators

variable {Action Nominal : Type*}
variable [Fintype Action] [DecidableEq Action] [Nonempty Action]
variable [Fintype Nominal] [DecidableEq Nominal]

/-- The finite source-PMF constrained transport value. -/
noncomputable def constrainedTransportValue (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (radius : ℝ) : ℝ :=
  sSup ((fun source : PMF Action => pmfExp source loss) ''
    {source | FiniteCoupling.finiteTransportCost source nominal cost ≤ radius})

/--
Weak duality for a fixed nonnegative transport penalty.  Any source law within
the transport budget has expected loss bounded by the penalty times the budget
plus the nominal expected penalized envelope.  The feasibility premise keeps
the `sSup` formulation meaningful even before a stricter Slater condition is
available for strong duality.
-/
theorem constrainedTransportValue_le_penalizedEnvelope
    (nominal : PMF Nominal) (loss : Action → ℝ) (cost : Action → Nominal → ℝ)
    (radius penalty : ℝ)
    (hcost : ∀ action nominalIndex, 0 ≤ cost action nominalIndex)
    (hpenalty : 0 ≤ penalty)
    (hfeasible : ∃ source : PMF Action,
      FiniteCoupling.finiteTransportCost source nominal cost ≤ radius) :
    constrainedTransportValue nominal loss cost radius ≤
      penalty * radius +
        pmfExp nominal (FiniteDRO.envelope (FiniteDRO.penalizedPayoff loss cost penalty)) := by
  unfold constrainedTransportValue
  rcases hfeasible with ⟨witness, hwitness⟩
  refine csSup_le ⟨pmfExp witness loss, witness, hwitness, rfl⟩ ?_
  rintro value ⟨source, hsource, rfl⟩
  have hpenalized := FiniteDRO.penalized_sourceValue_le_envelope nominal loss cost hcost
    penalty hpenalty (source := source)
  have hbudget : penalty * FiniteCoupling.finiteTransportCost source nominal cost ≤
      penalty * radius :=
    mul_le_mul_of_nonneg_left hsource hpenalty
  linarith

/-- Finite constrained source values have the pointwise loss-envelope upper bound. -/
theorem bddAbove_constrainedTransportValues (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (radius : ℝ) :
    BddAbove ((fun source : PMF Action => pmfExp source loss) ''
      {source | FiniteCoupling.finiteTransportCost source nominal cost ≤ radius}) := by
  let payoff : Action → Nominal → ℝ := fun action _ => loss action
  refine ⟨pmfExp nominal (FiniteDRO.envelope payoff), ?_⟩
  rintro value ⟨source, _hsource, rfl⟩
  let coupling := FiniteCoupling.independentCoupling source nominal
  let kernel := FiniteDRO.Kernel.ofFiniteCoupling coupling
  calc
    pmfExp source loss = coupling.expectedCost payoff := by
      unfold FiniteCoupling.expectedCost payoff
      exact (coupling.pmfExp_fst loss).symm
    _ = kernel.expectedPayoff payoff := rfl
    _ ≤ pmfExp nominal (FiniteDRO.envelope payoff) :=
      FiniteDRO.kernel_expectedPayoff_le_envelope nominal payoff kernel

/-- Every feasible source value is bounded by the finite constrained transport value. -/
theorem sourceValue_le_constrainedTransportValue (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (radius : ℝ)
    (source : PMF Action)
    (hsource : FiniteCoupling.finiteTransportCost source nominal cost ≤ radius) :
    pmfExp source loss ≤ constrainedTransportValue nominal loss cost radius := by
  unfold constrainedTransportValue
  exact le_csSup (bddAbove_constrainedTransportValues nominal loss cost radius)
    ⟨source, hsource, rfl⟩

/--
A deterministic pointwise perturbation whose cost is within the common budget
has expected value no larger than the distributionally robust value at that
budget.  This is the reusable lower half of test-set certificates comparing
an average of pointwise attacks with an average-cost transport ball.
-/
theorem selectedPointwiseBudgetValue_le_constrainedTransportValue
    (nominal : PMF Nominal) (loss : Action → ℝ) (cost : Action → Nominal → ℝ)
    (radius : ℝ) (select : Nominal → Action)
    (hcost : ∀ action nominalIndex, 0 ≤ cost action nominalIndex)
    (hselect : ∀ nominalIndex, cost (select nominalIndex) nominalIndex ≤ radius) :
    pmfExp nominal (fun nominalIndex => loss (select nominalIndex)) ≤
      constrainedTransportValue nominal loss cost radius := by
  let source : PMF Action := nominal.map select
  let graphCoupling : FiniteCoupling source nominal := FiniteCoupling.graph nominal select
  have hgraphCost : graphCoupling.expectedCost cost ≤ radius := by
    rw [FiniteCoupling.expectedCost_graph]
    exact pmfExp_le_of_forall_le nominal
      (fun nominalIndex => cost (select nominalIndex) nominalIndex) radius hselect
  have hsource : FiniteCoupling.finiteTransportCost source nominal cost ≤ radius :=
    (FiniteCoupling.finiteTransportCost_le_expectedCost cost hcost graphCoupling).trans hgraphCost
  calc
    pmfExp nominal (fun nominalIndex => loss (select nominalIndex)) =
        pmfExp source loss := by
      dsimp only [source]
      exact (pmfExp_map nominal select loss).symm
    _ ≤ constrainedTransportValue nominal loss cost radius :=
      sourceValue_le_constrainedTransportValue nominal loss cost radius source hsource

/--
The full finite test-certificate sandwich: selected pointwise attacks lie
inside the average-cost transport ball, while any nonnegative Lagrange penalty
upper-bounds that ball by the nominal pointwise penalized envelope.
-/
theorem selectedPointwiseBudgetValue_le_constrainedTransportValue_le_penalizedEnvelope
    (nominal : PMF Nominal) (loss : Action → ℝ) (cost : Action → Nominal → ℝ)
    (radius penalty : ℝ) (select : Nominal → Action)
    (hcost : ∀ action nominalIndex, 0 ≤ cost action nominalIndex)
    (hselect : ∀ nominalIndex, cost (select nominalIndex) nominalIndex ≤ radius)
    (hpenalty : 0 ≤ penalty) :
    pmfExp nominal (fun nominalIndex => loss (select nominalIndex)) ≤
        constrainedTransportValue nominal loss cost radius ∧
      constrainedTransportValue nominal loss cost radius ≤
        penalty * radius +
          pmfExp nominal (FiniteDRO.envelope (FiniteDRO.penalizedPayoff loss cost penalty)) := by
  constructor
  · exact selectedPointwiseBudgetValue_le_constrainedTransportValue nominal loss cost radius
      select hcost hselect
  · let source : PMF Action := nominal.map select
    let graphCoupling : FiniteCoupling source nominal := FiniteCoupling.graph nominal select
    have hgraphCost : graphCoupling.expectedCost cost ≤ radius := by
      rw [FiniteCoupling.expectedCost_graph]
      exact pmfExp_le_of_forall_le nominal
        (fun nominalIndex => cost (select nominalIndex) nominalIndex) radius hselect
    have hsource : FiniteCoupling.finiteTransportCost source nominal cost ≤ radius :=
      (FiniteCoupling.finiteTransportCost_le_expectedCost cost hcost graphCoupling).trans hgraphCost
    exact constrainedTransportValue_le_penalizedEnvelope nominal loss cost radius penalty hcost
      hpenalty ⟨source, hsource⟩

/-- The deterministic pointwise penalized-argmax kernel. -/
noncomputable def penalizedArgmaxKernel (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (penalty : ℝ) :
    FiniteDRO.Kernel Action nominal :=
  FiniteDRO.Kernel.graph nominal
    (FiniteDRO.argmax (FiniteDRO.penalizedPayoff loss cost penalty))

/-- The adversarial source marginal induced by the penalized-argmax kernel. -/
noncomputable def penalizedArgmaxSource (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (penalty : ℝ) : PMF Action :=
  (penalizedArgmaxKernel nominal loss cost penalty).law.map Prod.fst

/-- The graph coupling between the induced source marginal and the nominal law. -/
noncomputable def penalizedArgmaxCoupling (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (penalty : ℝ) :
    FiniteCoupling (penalizedArgmaxSource nominal loss cost penalty) nominal :=
  (penalizedArgmaxKernel nominal loss cost penalty).toFiniteCoupling

/-- The transport cost achieved by the pointwise penalized-argmax graph. -/
noncomputable def penalizedArgmaxAchievedCost (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (penalty : ℝ) : ℝ :=
  (penalizedArgmaxCoupling nominal loss cost penalty).expectedCost cost

/--
The pointwise penalized-argmax source value is exactly the nominal envelope
plus penalty times its graph coupling's achieved transport cost.
-/
theorem penalizedArgmaxSource_value_eq_envelope_add_cost (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (penalty : ℝ) :
    pmfExp (penalizedArgmaxSource nominal loss cost penalty) loss =
      pmfExp nominal
          (FiniteDRO.envelope (FiniteDRO.penalizedPayoff loss cost penalty)) +
        penalty * penalizedArgmaxAchievedCost nominal loss cost penalty := by
  let payoff := FiniteDRO.penalizedPayoff loss cost penalty
  let kernel := penalizedArgmaxKernel nominal loss cost penalty
  let coupling := penalizedArgmaxCoupling nominal loss cost penalty
  have hcoupling :
      pmfExp (penalizedArgmaxSource nominal loss cost penalty) loss -
          penalty * penalizedArgmaxAchievedCost nominal loss cost penalty =
        (FiniteDRO.Kernel.ofFiniteCoupling coupling).expectedPayoff payoff := by
    exact FiniteDRO.coupling_penalizedPayoff_eq_expectedPayoff
      nominal loss cost penalty coupling
  have hkernel :
      (FiniteDRO.Kernel.ofFiniteCoupling coupling).expectedPayoff payoff =
        kernel.expectedPayoff payoff := by
    rfl
  have hvalue : kernel.expectedPayoff payoff =
      pmfExp nominal (FiniteDRO.envelope payoff) := by
    unfold kernel penalizedArgmaxKernel
    rw [FiniteDRO.Kernel.expectedPayoff_graph]
    apply pmfExp_congr
    intro state
    exact FiniteDRO.argmax_attains payoff state
  dsimp only [payoff] at hcoupling hkernel hvalue ⊢
  linarith

/--
For a positive penalty, the penalized-argmax graph is a minimum-cost coupling
between its induced source marginal and the nominal law.  Any cheaper coupling
would have a strictly larger penalized payoff than the pointwise envelope.
-/
theorem finiteTransportCost_penalizedArgmaxSource_eq_achievedCost
    (nominal : PMF Nominal) (loss : Action → ℝ)
    (cost : Action → Nominal → ℝ) (penalty : ℝ)
    (hcost : ∀ action nominalIndex, 0 ≤ cost action nominalIndex)
    (hpenalty : 0 < penalty) :
    FiniteCoupling.finiteTransportCost
        (penalizedArgmaxSource nominal loss cost penalty) nominal cost =
      penalizedArgmaxAchievedCost nominal loss cost penalty := by
  let source := penalizedArgmaxSource nominal loss cost penalty
  let graphCoupling := penalizedArgmaxCoupling nominal loss cost penalty
  obtain ⟨optimalCoupling, hoptimal⟩ :=
    FiniteTransportMatrix.exists_expectedCost_eq_finiteTransportCost
      source nominal cost hcost
  have hoptimalPayoff := FiniteDRO.coupling_penalizedPayoff_le_envelope
    nominal loss cost penalty optimalCoupling
  have hgraphValue := penalizedArgmaxSource_value_eq_envelope_add_cost
    nominal loss cost penalty
  have hgraph_le_optimal : graphCoupling.expectedCost cost ≤
      optimalCoupling.expectedCost cost := by
    dsimp only [source] at hoptimalPayoff hgraphValue
    dsimp only [graphCoupling, penalizedArgmaxAchievedCost] at hgraphValue ⊢
    nlinarith
  apply le_antisymm
  · exact FiniteCoupling.finiteTransportCost_le_expectedCost cost hcost graphCoupling
  · rw [← hoptimal]
    exact hgraph_le_optimal

/--
At the graph coupling's achieved radius, the constrained robust value is
exactly the induced adversarial source value.  This equality only needs a
nonnegative penalty; positivity is needed separately to identify the graph
cost with the transport infimum between its marginals.
-/
theorem constrainedTransportValue_at_penalizedArgmaxAchievedCost
    (nominal : PMF Nominal) (loss : Action → ℝ)
    (cost : Action → Nominal → ℝ) (penalty : ℝ)
    (hcost : ∀ action nominalIndex, 0 ≤ cost action nominalIndex)
    (hpenalty : 0 ≤ penalty) :
    constrainedTransportValue nominal loss cost
        (penalizedArgmaxAchievedCost nominal loss cost penalty) =
      pmfExp (penalizedArgmaxSource nominal loss cost penalty) loss := by
  let source := penalizedArgmaxSource nominal loss cost penalty
  let coupling := penalizedArgmaxCoupling nominal loss cost penalty
  let achieved := penalizedArgmaxAchievedCost nominal loss cost penalty
  have hfeasible : FiniteCoupling.finiteTransportCost source nominal cost ≤ achieved := by
    exact FiniteCoupling.finiteTransportCost_le_expectedCost cost hcost coupling
  apply le_antisymm
  · have hupper := constrainedTransportValue_le_penalizedEnvelope nominal loss cost
      achieved penalty hcost hpenalty ⟨source, hfeasible⟩
    have hvalue := penalizedArgmaxSource_value_eq_envelope_add_cost
      nominal loss cost penalty
    dsimp only [source, achieved] at hupper hvalue ⊢
    linarith
  · exact sourceValue_le_constrainedTransportValue nominal loss cost achieved source hfeasible

/-- Finite constrained kernel-matrix values have the pointwise payoff-envelope upper bound. -/
theorem bddAbove_constrainedKernelValues (nominal : PMF Nominal)
    (payoff cost : Action → Nominal → ℝ) (radius : ℝ) :
    BddAbove ((fun matrix => FiniteTransportMatrix.matrixExpectation matrix payoff) ''
      {matrix | matrix ∈ FiniteTransportMatrix.kernelMatrices (Source := Action)
        (fun nominalIndex => (nominal nominalIndex).toReal) ∧
        FiniteTransportMatrix.matrixExpectation matrix cost ≤ radius}) := by
  refine ⟨pmfExp nominal (FiniteDRO.envelope payoff), ?_⟩
  rintro value ⟨matrix, ⟨hmatrix, _hbudget⟩, rfl⟩
  let coupling := FiniteTransportMatrix.finiteCouplingOfKernelMatrix nominal matrix hmatrix
  let kernel := FiniteDRO.Kernel.ofFiniteCoupling coupling
  calc
    FiniteTransportMatrix.matrixExpectation matrix payoff = coupling.expectedCost payoff :=
      (FiniteTransportMatrix.finiteCouplingOfKernelMatrix_expectedCost nominal matrix hmatrix payoff).symm
    _ = kernel.expectedPayoff payoff := rfl
    _ ≤ pmfExp nominal (FiniteDRO.envelope payoff) :=
      FiniteDRO.kernel_expectedPayoff_le_envelope nominal payoff kernel

/--
The source-PMF constrained value equals the equivalent fixed-nominal
kernel-matrix constrained value, once at least one source PMF satisfies the
transport budget.  The proof uses finite transport attainment in the
source-to-kernel direction and the primal transport inequality in reverse.
-/
theorem constrainedTransportValue_eq_constrainedKernelValue (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (radius : ℝ)
    (hcost : ∀ action nominalIndex, 0 ≤ cost action nominalIndex)
    (hfeasible : ∃ source : PMF Action,
      FiniteCoupling.finiteTransportCost source nominal cost ≤ radius) :
    constrainedTransportValue nominal loss cost radius =
      FiniteTransportMatrix.constrainedKernelValue
        (fun nominalIndex => (nominal nominalIndex).toReal)
        (fun action _ => loss action) cost radius := by
  let sourceValues := (fun source : PMF Action => pmfExp source loss) ''
    {source | FiniteCoupling.finiteTransportCost source nominal cost ≤ radius}
  let kernelValues := (fun matrix => FiniteTransportMatrix.matrixExpectation matrix
      (fun action _ => loss action)) ''
    {matrix | matrix ∈ FiniteTransportMatrix.kernelMatrices (Source := Action)
      (fun nominalIndex => (nominal nominalIndex).toReal) ∧
      FiniteTransportMatrix.matrixExpectation matrix cost ≤ radius}
  have hsource_ne : sourceValues.Nonempty := by
    obtain ⟨source, hsource⟩ := hfeasible
    exact ⟨pmfExp source loss, source, hsource, rfl⟩
  have hkernel_ne : kernelValues.Nonempty := by
    obtain ⟨source, hsource⟩ := hfeasible
    obtain ⟨coupling, hcoupling⟩ :=
      FiniteTransportMatrix.exists_expectedCost_eq_finiteTransportCost source nominal cost hcost
    let matrix := FiniteTransportMatrix.matrixOfFiniteCoupling coupling
    have hmatrix : matrix ∈ FiniteTransportMatrix.kernelMatrices (Source := Action)
        (fun nominalIndex => (nominal nominalIndex).toReal) :=
      FiniteTransportMatrix.matrixOfFiniteCoupling_mem_kernelMatrices coupling
    have hbudget : FiniteTransportMatrix.matrixExpectation matrix cost ≤ radius := by
      rw [FiniteTransportMatrix.matrixExpectation_matrixOfFiniteCoupling coupling cost]
      change coupling.expectedCost cost ≤ radius
      rw [hcoupling]
      exact hsource
    exact ⟨FiniteTransportMatrix.matrixExpectation matrix (fun action _ => loss action),
      matrix, ⟨hmatrix, hbudget⟩, rfl⟩
  have hsource_bdd : BddAbove sourceValues :=
    bddAbove_constrainedTransportValues nominal loss cost radius
  have hkernel_bdd : BddAbove kernelValues :=
    bddAbove_constrainedKernelValues nominal (fun action _ => loss action) cost radius
  change sSup sourceValues = sSup kernelValues
  apply le_antisymm
  · refine csSup_le hsource_ne ?_
    rintro value ⟨source, hsource, rfl⟩
    obtain ⟨coupling, hcoupling⟩ :=
      FiniteTransportMatrix.exists_expectedCost_eq_finiteTransportCost source nominal cost hcost
    let matrix := FiniteTransportMatrix.matrixOfFiniteCoupling coupling
    have hmatrix : matrix ∈ FiniteTransportMatrix.kernelMatrices (Source := Action)
        (fun nominalIndex => (nominal nominalIndex).toReal) :=
      FiniteTransportMatrix.matrixOfFiniteCoupling_mem_kernelMatrices coupling
    have hbudget : FiniteTransportMatrix.matrixExpectation matrix cost ≤ radius := by
      rw [FiniteTransportMatrix.matrixExpectation_matrixOfFiniteCoupling coupling cost]
      change coupling.expectedCost cost ≤ radius
      rw [hcoupling]
      exact hsource
    have hvalue : pmfExp source loss =
        FiniteTransportMatrix.matrixExpectation matrix (fun action _ => loss action) := by
      calc
        pmfExp source loss = pmfExp coupling.law (fun pair => loss pair.1) :=
          (coupling.pmfExp_fst loss).symm
        _ = FiniteTransportMatrix.matrixExpectation matrix (fun action _ => loss action) := by
          symm
          exact FiniteTransportMatrix.matrixExpectation_matrixOfFiniteCoupling coupling _
    exact le_csSup hkernel_bdd ⟨matrix, ⟨hmatrix, hbudget⟩, hvalue.symm⟩
  · refine csSup_le hkernel_ne ?_
    rintro value ⟨matrix, ⟨hmatrix, hbudget⟩, rfl⟩
    let coupling := FiniteTransportMatrix.finiteCouplingOfKernelMatrix nominal matrix hmatrix
    let source := coupling.law.map Prod.fst
    have hsource : FiniteCoupling.finiteTransportCost source nominal cost ≤ radius := by
      calc
        FiniteCoupling.finiteTransportCost source nominal cost ≤ coupling.expectedCost cost :=
          FiniteCoupling.finiteTransportCost_le_expectedCost cost hcost coupling
        _ = FiniteTransportMatrix.matrixExpectation matrix cost :=
          FiniteTransportMatrix.finiteCouplingOfKernelMatrix_expectedCost nominal matrix hmatrix cost
        _ ≤ radius := hbudget
    have hvalue : FiniteTransportMatrix.matrixExpectation matrix (fun action _ => loss action) =
        pmfExp source loss := by
      calc
        FiniteTransportMatrix.matrixExpectation matrix (fun action _ => loss action) =
            coupling.expectedCost (fun action _ => loss action) :=
          (FiniteTransportMatrix.finiteCouplingOfKernelMatrix_expectedCost nominal matrix hmatrix _).symm
        _ = pmfExp coupling.law (fun pair => loss pair.1) := rfl
        _ = pmfExp source loss := coupling.pmfExp_fst loss
    exact le_csSup hsource_bdd ⟨source, hsource, hvalue.symm⟩

/-- The fixed-nominal kernel-matrix supremum is its finite pointwise envelope. -/
theorem kernelMatrixValue_eq_envelope (nominal : PMF Nominal)
    (payoff : Action → Nominal → ℝ) :
    sSup ((fun matrix => FiniteTransportMatrix.matrixExpectation matrix payoff) ''
      FiniteTransportMatrix.kernelMatrices (Source := Action)
        (fun nominalIndex => (nominal nominalIndex).toReal)) =
      pmfExp nominal (FiniteDRO.envelope payoff) := by
  let envelopeValue := pmfExp nominal (FiniteDRO.envelope payoff)
  have hupper : ∀ matrix ∈ FiniteTransportMatrix.kernelMatrices (Source := Action)
      (fun nominalIndex => (nominal nominalIndex).toReal),
      FiniteTransportMatrix.matrixExpectation matrix payoff ≤ envelopeValue := by
    intro matrix hmatrix
    let coupling := FiniteTransportMatrix.finiteCouplingOfKernelMatrix nominal matrix hmatrix
    let kernel := FiniteDRO.Kernel.ofFiniteCoupling coupling
    have hmatrix_value : FiniteTransportMatrix.matrixExpectation matrix payoff =
        kernel.expectedPayoff payoff := by
      calc
        FiniteTransportMatrix.matrixExpectation matrix payoff = coupling.expectedCost payoff :=
          (FiniteTransportMatrix.finiteCouplingOfKernelMatrix_expectedCost nominal matrix hmatrix
            payoff).symm
        _ = kernel.expectedPayoff payoff := rfl
    rw [hmatrix_value]
    exact FiniteDRO.kernel_expectedPayoff_le_envelope nominal payoff kernel
  let witnessKernel : FiniteDRO.Kernel Action nominal :=
    FiniteDRO.Kernel.graph nominal (FiniteDRO.argmax payoff)
  let witnessCoupling := FiniteDRO.Kernel.toFiniteCoupling witnessKernel
  let witnessMatrix := FiniteTransportMatrix.matrixOfFiniteCoupling witnessCoupling
  have hwitness_mem : witnessMatrix ∈ FiniteTransportMatrix.kernelMatrices (Source := Action)
      (fun nominalIndex => (nominal nominalIndex).toReal) :=
    FiniteTransportMatrix.matrixOfFiniteCoupling_mem_kernelMatrices witnessCoupling
  have hwitness_value : FiniteTransportMatrix.matrixExpectation witnessMatrix payoff = envelopeValue := by
    calc
      FiniteTransportMatrix.matrixExpectation witnessMatrix payoff =
          pmfExp witnessCoupling.law (fun pair => payoff pair.1 pair.2) :=
        FiniteTransportMatrix.matrixExpectation_matrixOfFiniteCoupling witnessCoupling payoff
      _ = witnessKernel.expectedPayoff payoff := rfl
      _ = envelopeValue := FiniteDRO.kernelOptimalityCertificate_witness_value nominal payoff
  have hbdd : BddAbove ((fun matrix => FiniteTransportMatrix.matrixExpectation matrix payoff) ''
      FiniteTransportMatrix.kernelMatrices (Source := Action)
        (fun nominalIndex => (nominal nominalIndex).toReal)) := by
    refine ⟨envelopeValue, ?_⟩
    rintro value ⟨matrix, hmatrix, rfl⟩
    exact hupper matrix hmatrix
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨FiniteTransportMatrix.matrixExpectation witnessMatrix payoff,
        witnessMatrix, hwitness_mem, rfl⟩
    · rintro value ⟨matrix, hmatrix, rfl⟩
      exact hupper matrix hmatrix
  · exact le_csSup hbdd ⟨witnessMatrix, hwitness_mem, hwitness_value⟩

/--
At a fixed penalty, the kernel-matrix scalar Lagrange objective is the
nominal expectation of the pointwise penalized envelope plus `penalty * radius`.
-/
theorem scalarDualObjective_eq_envelope (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (radius penalty : ℝ) :
    Optimization.scalarDualObjective
      (FiniteTransportMatrix.kernelMatrices (Source := Action)
        (fun nominalIndex => (nominal nominalIndex).toReal))
      (fun matrix => FiniteTransportMatrix.matrixExpectation matrix (fun action _ => loss action))
      (fun matrix => FiniteTransportMatrix.matrixExpectation matrix cost - radius)
      penalty =
      penalty * radius + pmfExp nominal
        (FiniteDRO.envelope (FiniteDRO.penalizedPayoff loss cost penalty)) := by
  let domain := FiniteTransportMatrix.kernelMatrices (Source := Action)
    (fun nominalIndex => (nominal nominalIndex).toReal)
  let payoff := FiniteDRO.penalizedPayoff loss cost penalty
  let envelopeValue := pmfExp nominal (FiniteDRO.envelope payoff)
  have hformula : ∀ matrix, Optimization.scalarLagrangian
      (fun matrix => FiniteTransportMatrix.matrixExpectation matrix (fun action _ => loss action))
      (fun matrix => FiniteTransportMatrix.matrixExpectation matrix cost - radius)
      matrix penalty =
      FiniteTransportMatrix.matrixExpectation matrix payoff + penalty * radius := by
    intro matrix
    unfold Optimization.scalarLagrangian payoff FiniteDRO.penalizedPayoff
    rw [FiniteTransportMatrix.matrixExpectation_sub_mul]
    ring
  have hupper : ∀ matrix ∈ domain,
      Optimization.scalarLagrangian
        (fun matrix => FiniteTransportMatrix.matrixExpectation matrix (fun action _ => loss action))
        (fun matrix => FiniteTransportMatrix.matrixExpectation matrix cost - radius)
        matrix penalty ≤ envelopeValue + penalty * radius := by
    intro matrix hmatrix
    rw [hformula]
    let coupling := FiniteTransportMatrix.finiteCouplingOfKernelMatrix nominal matrix hmatrix
    let kernel := FiniteDRO.Kernel.ofFiniteCoupling coupling
    have hmatrix_value : FiniteTransportMatrix.matrixExpectation matrix payoff =
        kernel.expectedPayoff payoff := by
      calc
        FiniteTransportMatrix.matrixExpectation matrix payoff = coupling.expectedCost payoff :=
          (FiniteTransportMatrix.finiteCouplingOfKernelMatrix_expectedCost nominal matrix hmatrix
            payoff).symm
        _ = kernel.expectedPayoff payoff := rfl
    rw [hmatrix_value]
    exact add_le_add_left (FiniteDRO.kernel_expectedPayoff_le_envelope nominal payoff kernel) _
  let witnessKernel : FiniteDRO.Kernel Action nominal :=
    FiniteDRO.Kernel.graph nominal (FiniteDRO.argmax payoff)
  let witnessCoupling := FiniteDRO.Kernel.toFiniteCoupling witnessKernel
  let witnessMatrix := FiniteTransportMatrix.matrixOfFiniteCoupling witnessCoupling
  have hwitness_mem : witnessMatrix ∈ domain :=
    FiniteTransportMatrix.matrixOfFiniteCoupling_mem_kernelMatrices witnessCoupling
  have hwitness_value : Optimization.scalarLagrangian
      (fun matrix => FiniteTransportMatrix.matrixExpectation matrix (fun action _ => loss action))
      (fun matrix => FiniteTransportMatrix.matrixExpectation matrix cost - radius)
      witnessMatrix penalty = envelopeValue + penalty * radius := by
    rw [hformula]
    have hmatrix_value : FiniteTransportMatrix.matrixExpectation witnessMatrix payoff =
        envelopeValue := by
      calc
        FiniteTransportMatrix.matrixExpectation witnessMatrix payoff =
            pmfExp witnessCoupling.law (fun pair => payoff pair.1 pair.2) :=
          FiniteTransportMatrix.matrixExpectation_matrixOfFiniteCoupling witnessCoupling payoff
        _ = witnessKernel.expectedPayoff payoff := rfl
        _ = envelopeValue := FiniteDRO.kernelOptimalityCertificate_witness_value nominal payoff
    rw [hmatrix_value]
  have hbdd : BddAbove ((fun matrix => Optimization.scalarLagrangian
      (fun matrix => FiniteTransportMatrix.matrixExpectation matrix (fun action _ => loss action))
      (fun matrix => FiniteTransportMatrix.matrixExpectation matrix cost - radius)
      matrix penalty) '' domain) := by
    refine ⟨envelopeValue + penalty * radius, ?_⟩
    rintro value ⟨matrix, hmatrix, rfl⟩
    exact hupper matrix hmatrix
  unfold Optimization.scalarDualObjective
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨_, witnessMatrix, hwitness_mem, rfl⟩
    · rintro value ⟨matrix, hmatrix, rfl⟩
      have := hupper matrix hmatrix
      linarith
  · have hle := le_csSup hbdd ⟨witnessMatrix, hwitness_mem, hwitness_value⟩
    linarith

/-- The finite pointwise-envelope form of the constrained transport dual. -/
noncomputable def constrainedTransportEnvelopeDualValue (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (radius : ℝ) : ℝ :=
  sInf ((fun penalty => penalty * radius +
    pmfExp nominal (FiniteDRO.envelope (FiniteDRO.penalizedPayoff loss cost penalty))) '' Set.Ici 0)

/-- The kernel-matrix scalar dual is exactly the finite pointwise-envelope dual. -/
theorem constrainedKernelDualValue_eq_envelopeDualValue (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (radius : ℝ) :
    FiniteTransportMatrix.constrainedKernelDualValue
      (fun nominalIndex => (nominal nominalIndex).toReal)
      (fun action _ => loss action) cost radius =
      constrainedTransportEnvelopeDualValue nominal loss cost radius := by
  unfold FiniteTransportMatrix.constrainedKernelDualValue
    Optimization.scalarDualValue constrainedTransportEnvelopeDualValue
  apply congrArg sInf
  ext value
  constructor
  · rintro ⟨penalty, hpenalty, rfl⟩
    exact ⟨penalty, hpenalty,
      (scalarDualObjective_eq_envelope nominal loss cost radius penalty).symm⟩
  · rintro ⟨penalty, hpenalty, rfl⟩
    exact ⟨penalty, hpenalty, scalarDualObjective_eq_envelope nominal loss cost radius penalty⟩

/--
Finite constrained transport duality under an explicit strict budget-feasible
kernel.  This is the source-PMF constrained value, not merely a coupling-form
relaxation: finite transport attainment proves their equality.
-/
theorem constrainedTransportValue_eq_envelopeDualValue (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (radius : ℝ)
    (hcost : ∀ action nominalIndex, 0 ≤ cost action nominalIndex)
    (hstrict : ∃ matrix ∈ FiniteTransportMatrix.kernelMatrices (Source := Action)
      (fun nominalIndex => (nominal nominalIndex).toReal),
      FiniteTransportMatrix.matrixExpectation matrix cost < radius) :
    constrainedTransportValue nominal loss cost radius =
      constrainedTransportEnvelopeDualValue nominal loss cost radius := by
  obtain ⟨strictMatrix, hstrictMatrix, hstrictCost⟩ := hstrict
  let strictCoupling := FiniteTransportMatrix.finiteCouplingOfKernelMatrix nominal
    strictMatrix hstrictMatrix
  let strictSource := strictCoupling.law.map Prod.fst
  have hfeasible : ∃ source : PMF Action,
      FiniteCoupling.finiteTransportCost source nominal cost ≤ radius := by
    refine ⟨strictSource, ?_⟩
    calc
      FiniteCoupling.finiteTransportCost strictSource nominal cost ≤
          strictCoupling.expectedCost cost :=
        FiniteCoupling.finiteTransportCost_le_expectedCost cost hcost strictCoupling
      _ = FiniteTransportMatrix.matrixExpectation strictMatrix cost :=
        FiniteTransportMatrix.finiteCouplingOfKernelMatrix_expectedCost nominal strictMatrix
          hstrictMatrix cost
      _ ≤ radius := hstrictCost.le
  calc
    constrainedTransportValue nominal loss cost radius =
        FiniteTransportMatrix.constrainedKernelValue
          (fun nominalIndex => (nominal nominalIndex).toReal)
          (fun action _ => loss action) cost radius :=
      constrainedTransportValue_eq_constrainedKernelValue nominal loss cost radius hcost hfeasible
    _ = FiniteTransportMatrix.constrainedKernelDualValue
          (fun nominalIndex => (nominal nominalIndex).toReal)
          (fun action _ => loss action) cost radius :=
      FiniteTransportMatrix.constrainedKernelValue_eq_dualValue
        (fun nominalIndex => (nominal nominalIndex).toReal)
        (fun action _ => loss action) cost radius
        ⟨strictMatrix, hstrictMatrix, hstrictCost⟩
    _ = constrainedTransportEnvelopeDualValue nominal loss cost radius :=
      constrainedKernelDualValue_eq_envelopeDualValue nominal loss cost radius

/--
A common finite state space, zero diagonal cost, and a positive radius supply
the strict kernel required by finite constrained transport duality.
-/
theorem exists_strictKernelMatrix_of_selfCost_zero
    {State : Type*} [Fintype State] [DecidableEq State]
    (nominal : PMF State) (cost : State → State → ℝ) (radius : ℝ)
    (hradius : 0 < radius) (hselfCost : ∀ state, cost state state = 0) :
    ∃ matrix ∈ FiniteTransportMatrix.kernelMatrices (Source := State)
      (fun state => (nominal state).toReal),
      FiniteTransportMatrix.matrixExpectation matrix cost < radius := by
  let coupling := FiniteCoupling.graph nominal id
  let matrix := FiniteTransportMatrix.matrixOfFiniteCoupling coupling
  have hmatrix : matrix ∈ FiniteTransportMatrix.kernelMatrices (Source := State)
      (fun state => (nominal state).toReal) :=
    FiniteTransportMatrix.matrixOfFiniteCoupling_mem_kernelMatrices coupling
  refine ⟨matrix, hmatrix, ?_⟩
  have hcost_zero : coupling.expectedCost cost = 0 := by
    rw [FiniteCoupling.expectedCost_graph]
    have hzero : (fun state => cost (id state) state) = fun _ => (0 : ℝ) := by
      funext state
      simpa using hselfCost state
    rw [hzero, pmfExp_const]
  calc
    FiniteTransportMatrix.matrixExpectation matrix cost = coupling.expectedCost cost :=
      FiniteTransportMatrix.matrixExpectation_matrixOfFiniteCoupling coupling cost
    _ = 0 := hcost_zero
    _ < radius := hradius

/--
The finite common-state constrained transport formula under the source's
standard nonnegative, zero-self-cost, positive-radius assumptions.
-/
theorem constrainedTransportValue_eq_envelopeDualValue_of_selfCost_zero
    {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]
    (nominal : PMF State) (loss : State → ℝ) (cost : State → State → ℝ) (radius : ℝ)
    (hcost : ∀ first second, 0 ≤ cost first second)
    (hselfCost : ∀ state, cost state state = 0) (hradius : 0 < radius) :
    constrainedTransportValue nominal loss cost radius =
      constrainedTransportEnvelopeDualValue nominal loss cost radius := by
  apply constrainedTransportValue_eq_envelopeDualValue nominal loss cost radius hcost
  exact exists_strictKernelMatrix_of_selfCost_zero nominal cost radius hradius hselfCost

end FiniteConstrainedDRO
end AppliedModelingLib
