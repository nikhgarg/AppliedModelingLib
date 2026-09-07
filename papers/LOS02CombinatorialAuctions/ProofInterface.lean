import LOS02CombinatorialAuctions.MainTheorems

/-!
# Proof Interface: Truth Revelation in Approximately Efficient Combinatorial Auctions

This file is the broad proof-facing compatibility surface for the LOS 2002
combinatorial-auction formalization. The compact human-review surface is
`PaperInterface.lean`.
-/

namespace LOS02CombinatorialAuctions
namespace ProofInterface

open AppliedModelingLib.Auction

/-! ## Paper Definitions -/

/-- Paper utility in a combinatorial auction. -/
abbrev utility {Bidder Item : Type*}
    (M : CombinatorialAuction Bidder Item)
    (values reports : CombinatorialReport Bidder Item) (i : Bidder) : ℝ :=
  LOS02CombinatorialAuctions.paper_combinatorial_utility M values reports i

/-- Paper dominant-strategy truthfulness predicate on an admissible domain. -/
abbrev truthfulOn {Bidder Item : Type*} [DecidableEq Bidder]
    (M : CombinatorialAuction Bidder Item)
    (admissible : CombinatorialReport Bidder Item → Prop) : Prop :=
  LOS02CombinatorialAuctions.paper_combinatorial_truthful_on M admissible

/-- Nonnegative direct bundle-value reports, matching the source type space. -/
abbrev nonnegativeValues {Bidder Item : Type*}
    (values : CombinatorialReport Bidder Item) : Prop :=
  CombinatorialAuction.NonnegativeValues values

/-- Section 4 generalized Vickrey auction from a supplied allocation rule. -/
noncomputable abbrev generalizedVickreyAuction
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item) :
    CombinatorialAuction Bidder Item :=
  LOS02CombinatorialAuctions.paper_generalized_vickrey_auction alloc

/-- Welfare-maximization certificate for the GVA allocation rule. -/
abbrev gvaWelfareMaximizingAllocationRule
    {Bidder Item : Type*} [Fintype Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item) :
    Prop :=
  LOS02CombinatorialAuctions.paper_gva_welfare_maximizing_allocation_rule alloc

/-- Paper-facing accepted-set mechanism for single-minded bid profiles. -/
abbrev singleMindedAcceptedMechanism (Bidder Item : Type*) :=
  SingleMindedAcceptedMechanism Bidder Item

/-- Truthfulness predicate for single-minded bid-profile mechanisms. -/
abbrev singleMindedTruthfulOn
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (admissible : (Bidder → SingleMindedBid Item) → Prop) : Prop :=
  M.TruthfulOn admissible

/-- Nonempty, nonnegative single-minded bid profiles. -/
abbrev nonnegativeNonemptySingleMindedProfile
    {Bidder Item : Type*} [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) : Prop :=
  SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile bids

/-- Weighted set-packing feasibility used in Theorem 6.1's reduction. -/
abbrev setPackingFeasible
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (selected : Finset Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_set_packing_feasible sets selected

/-- Weighted set-packing objective used in Theorem 6.1's reduction. -/
noncomputable abbrev weightedSetPackingValue
    {Bidder : Type*} [DecidableEq Bidder]
    (weights : Bidder → ℝ) (selected : Finset Bidder) : ℝ :=
  LOS02CombinatorialAuctions.paper_weighted_set_packing_value weights selected

/-- Encode a weighted set-packing instance as single-minded bids. -/
abbrev setPackingSingleMindedBids
    {Bidder Item : Type*}
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ) :
    Bidder → SingleMindedBid Item :=
  LOS02CombinatorialAuctions.paper_set_packing_single_minded_bids sets weights

/--
The Theorem 6.1 set-packing encoding preserves feasibility exactly.
-/
theorem theorem6_1_set_packing_feasibility_encoding_correct
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (selected : Finset Bidder) :
    PairwiseDisjointDesired
        (setPackingSingleMindedBids sets weights) selected ↔
      setPackingFeasible sets selected := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_set_packing_feasibility_encoding_correct
      sets weights selected

/--
The Theorem 6.1 set-packing encoding preserves objective value exactly.
-/
theorem theorem6_1_set_packing_value_encoding_correct
    {Bidder Item : Type*} [DecidableEq Bidder]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (selected : Finset Bidder) :
    LOS02CombinatorialAuctions.paper_single_minded_total_value
        (setPackingSingleMindedBids sets weights) selected =
      weightedSetPackingValue weights selected := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_set_packing_value_encoding_correct
      sets weights selected

/-- Optimal selections for weighted set packing. -/
abbrev weightedSetPackingOptimal
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (selected : Finset Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_weighted_set_packing_optimal
    sets weights selected

/-- Optimal accepted sets for single-minded welfare maximization. -/
abbrev singleMindedOptimalAcceptedSet
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (selected : Finset Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_single_minded_optimal_accepted_set
    bids selected

/-- Multiplicative approximation guarantee for weighted set packing. -/
abbrev weightedSetPackingApproximationAtLeast
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (factor : ℝ) (selected : Finset Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_weighted_set_packing_approximation_at_least
    sets weights factor selected

/-- Multiplicative approximation guarantee for single-minded welfare. -/
abbrev singleMindedApproximationAtLeast
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (factor : ℝ) (selected : Finset Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_single_minded_approximation_at_least
    bids factor selected

/-- Exact single-minded welfare solvers. -/
abbrev singleMindedOptimalSolver
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_single_minded_optimal_solver solver

/-- Exact weighted set-packing solvers. -/
abbrev weightedSetPackingOptimalSolver
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (solver :
      (Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_weighted_set_packing_optimal_solver solver

/-- Uniform approximation solvers for single-minded welfare. -/
abbrev singleMindedApproximationSolverAtLeast
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_single_minded_approximation_solver_at_least
    factor solver

/-- Uniform approximation solvers for weighted set packing. -/
abbrev weightedSetPackingApproximationSolverAtLeast
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (solver :
      (Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_weighted_set_packing_approximation_solver_at_least
    factor solver

/-- Compose a single-minded welfare solver with the Theorem 6.1 encoding. -/
abbrev setPackingSolverOfSingleMindedSolver
    {Bidder Item : Type*}
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder)
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ) : Finset Bidder :=
  LOS02CombinatorialAuctions.paper_set_packing_solver_of_single_minded_solver
    solver sets weights

/-- Threshold decision instances for weighted set packing. -/
abbrev weightedSetPackingDecisionInstance (Bidder Item : Type*) :=
  LOS02CombinatorialAuctions.paper_weighted_set_packing_decision_instance
    Bidder Item

/-- Threshold decision instances for single-minded welfare maximization. -/
abbrev singleMindedWelfareDecisionInstance (Bidder Item : Type*) :=
  LOS02CombinatorialAuctions.paper_single_minded_welfare_decision_instance
    Bidder Item

/-- Weighted set-packing threshold decision problem. -/
noncomputable abbrev weightedSetPackingDecisionProblem
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item] :
    AppliedModelingLib.Complexity.DecisionProblem
      (weightedSetPackingDecisionInstance Bidder Item) :=
  LOS02CombinatorialAuctions.paper_weighted_set_packing_decision_problem

/-- Single-minded welfare threshold decision problem. -/
noncomputable abbrev singleMindedWelfareDecisionProblem
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item] :
    AppliedModelingLib.Complexity.DecisionProblem
      (singleMindedWelfareDecisionInstance Bidder Item) :=
  LOS02CombinatorialAuctions.paper_single_minded_welfare_decision_problem

/-- The set-to-bid encoding as a map of threshold decision instances. -/
abbrev setPackingDecisionToSingleMindedWelfareDecision
    {Bidder Item : Type*}
    (problem : weightedSetPackingDecisionInstance Bidder Item) :
    singleMindedWelfareDecisionInstance Bidder Item :=
  LOS02CombinatorialAuctions.paper_set_packing_decision_to_single_minded_welfare_decision
    problem

/-- Graph independent-set feasibility used in Theorem 6.1's proof route. -/
abbrev graphIndependentSelection
    {Vertex : Type*}
    (G : SimpleGraph Vertex) (selected : Finset Vertex) : Prop :=
  LOS02CombinatorialAuctions.paper_graph_independent_selection G selected

/-- Maximum independent sets by cardinality. -/
abbrev maximumIndependentSelection
    {Vertex : Type*}
    (G : SimpleGraph Vertex) (selected : Finset Vertex) : Prop :=
  LOS02CombinatorialAuctions.paper_maximum_independent_selection G selected

/-- Graph clique selections used in the classic Theorem 6.1 hardness route. -/
abbrev graphCliqueSelection
    {Vertex : Type*}
    (G : SimpleGraph Vertex) (selected : Finset Vertex) : Prop :=
  LOS02CombinatorialAuctions.paper_graph_clique_selection G selected

/-- Maximum cliques by cardinality. -/
abbrev maximumCliqueSelection
    {Vertex : Type*}
    (G : SimpleGraph Vertex) (selected : Finset Vertex) : Prop :=
  LOS02CombinatorialAuctions.paper_maximum_clique_selection G selected

/-- Threshold decision instances for graph independent set. -/
abbrev graphIndependentSetDecisionInstance (Vertex : Type*) :=
  LOS02CombinatorialAuctions.paper_graph_independent_set_decision_instance
    Vertex

/-- Threshold decision instances for graph clique. -/
abbrev graphCliqueDecisionInstance (Vertex : Type*) :=
  LOS02CombinatorialAuctions.paper_graph_clique_decision_instance Vertex

/-- Graph independent-set threshold decision problem. -/
abbrev graphIndependentSetDecisionProblem {Vertex : Type*} :
    AppliedModelingLib.Complexity.DecisionProblem
      (graphIndependentSetDecisionInstance Vertex) :=
  LOS02CombinatorialAuctions.paper_graph_independent_set_decision_problem

/-- Graph clique threshold decision problem. -/
abbrev graphCliqueDecisionProblem {Vertex : Type*} :
    AppliedModelingLib.Complexity.DecisionProblem
      (graphCliqueDecisionInstance Vertex) :=
  LOS02CombinatorialAuctions.paper_graph_clique_decision_problem

/-- Reduce clique threshold decision to independent-set threshold decision by complementing. -/
abbrev graphCliqueDecisionToIndependentSetComplementDecision
    {Vertex : Type*}
    (problem : graphCliqueDecisionInstance Vertex) :
    graphIndependentSetDecisionInstance Vertex :=
  LOS02CombinatorialAuctions.paper_graph_clique_decision_to_independent_set_complement_decision
    problem

/-- Encode independent-set threshold decision as weighted set packing. -/
noncomputable abbrev graphIndependentSetDecisionToWeightedSetPackingDecision
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (problem : graphIndependentSetDecisionInstance Vertex) :
    weightedSetPackingDecisionInstance Vertex (Sym2 Vertex) :=
  LOS02CombinatorialAuctions.paper_graph_independent_set_decision_to_weighted_set_packing_decision
    problem

/-- Encode clique threshold decision as weighted set packing on complement edges. -/
noncomputable abbrev graphCliqueDecisionToWeightedSetPackingDecision
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (problem : graphCliqueDecisionInstance Vertex) :
    weightedSetPackingDecisionInstance Vertex (Sym2 Vertex) :=
  LOS02CombinatorialAuctions.paper_graph_clique_decision_to_weighted_set_packing_decision
    problem

/-- Encode clique threshold decision as single-minded welfare on complement-edge goods. -/
noncomputable abbrev graphCliqueDecisionToSingleMindedWelfareDecision
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (problem : graphCliqueDecisionInstance Vertex) :
    singleMindedWelfareDecisionInstance Vertex (Sym2 Vertex) :=
  LOS02CombinatorialAuctions.paper_graph_clique_decision_to_single_minded_welfare_decision
    problem

/-- Encode a graph as a set-packing instance whose goods are graph edges. -/
noncomputable abbrev graphIncidentSets
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj] :
    Vertex → Finset (Sym2 Vertex) :=
  LOS02CombinatorialAuctions.paper_graph_incident_sets G

/-- Unit vertex weights for the independent-set reduction. -/
abbrev graphUnitWeights (Vertex : Type*) : Vertex → ℝ :=
  LOS02CombinatorialAuctions.paper_graph_unit_weights Vertex

/--
Theorem 6.1, formalized reduction layer: the set-packing encoding preserves
both feasibility and optimal objective value.  The computational complexity
classes used for the paper's NP-hardness consequence are not modeled here.
-/
theorem theorem6_1_weighted_set_packing_reduction
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (selected : Finset Bidder) :
    weightedSetPackingOptimal sets weights selected ↔
      singleMindedOptimalAcceptedSet
        (setPackingSingleMindedBids sets weights) selected := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_weighted_set_packing_reduction
      sets weights selected

/--
Theorem 6.1 solver-transfer form: any exact solver for single-minded welfare
maximization gives an exact solver for weighted set packing after composing
with the paper's set-to-bid encoding.
-/
theorem theorem6_1_optimal_solver_reduction
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder)
    (hsolver : singleMindedOptimalSolver solver) :
    weightedSetPackingOptimalSolver
      (setPackingSolverOfSingleMindedSolver solver) := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_optimal_solver_reduction
      solver hsolver

/--
Theorem 6.1 approximation-preserving form: the set-to-bid encoding preserves a
multiplicative approximation guarantee for each selected set.
-/
theorem theorem6_1_approximation_preserving_reduction
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (factor : ℝ) (selected : Finset Bidder) :
    weightedSetPackingApproximationAtLeast sets weights factor selected ↔
      singleMindedApproximationAtLeast
        (setPackingSingleMindedBids sets weights) factor selected := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_approximation_preserving_reduction
      sets weights factor selected

/--
Theorem 6.1 approximation-solver transfer: any single-minded welfare solver
with a uniform multiplicative guarantee gives a weighted set-packing solver with
the same guarantee via the paper's set-to-bid encoding.
-/
theorem theorem6_1_approximation_solver_reduction
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder)
    (hsolver : singleMindedApproximationSolverAtLeast factor solver) :
    weightedSetPackingApproximationSolverAtLeast factor
      (setPackingSolverOfSingleMindedSolver solver) := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_approximation_solver_reduction
      factor solver hsolver

/--
Theorem 6.1 decision-problem encoding correctness: the weighted set-packing
threshold question is true exactly when the encoded single-minded welfare
threshold question is true.
-/
theorem theorem6_1_decision_problem_encoding_correct
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (problem : weightedSetPackingDecisionInstance Bidder Item) :
    weightedSetPackingDecisionProblem problem ↔
      singleMindedWelfareDecisionProblem
        (setPackingDecisionToSingleMindedWelfareDecision problem) := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_decision_problem_encoding_correct
      problem

/--
Theorem 6.1 as an abstract many-one reduction between threshold decision
problems.
-/
noncomputable def theorem6_1_decision_problem_reduction
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item] :
    AppliedModelingLib.Complexity.ManyOneReduction
      (weightedSetPackingDecisionProblem (Bidder := Bidder) (Item := Item))
      (singleMindedWelfareDecisionProblem (Bidder := Bidder) (Item := Item)) :=
  LOS02CombinatorialAuctions.paper_theorem6_1_decision_problem_reduction

/--
Theorem 6.1 as an abstract polynomial-time reduction, conditional on an
external runtime certificate for the set-to-bid encoding.
-/
noncomputable def theorem6_1_polynomial_time_decision_problem_reduction
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (PolynomialTime :
      (weightedSetPackingDecisionInstance Bidder Item →
        singleMindedWelfareDecisionInstance Bidder Item) → Prop)
    (hpoly :
      PolynomialTime setPackingDecisionToSingleMindedWelfareDecision) :
    AppliedModelingLib.Complexity.PolynomialTimeReduction
      (weightedSetPackingDecisionProblem (Bidder := Bidder) (Item := Item))
      (singleMindedWelfareDecisionProblem (Bidder := Bidder) (Item := Item)) :=
  LOS02CombinatorialAuctions.paper_theorem6_1_polynomial_time_decision_problem_reduction
    PolynomialTime hpoly

/--
External reduction-consequence form of Theorem 6.1 for threshold decision
problems: any external consequence that follows from a many-one reduction out of
weighted set packing follows for the encoded single-minded welfare target.
-/
theorem theorem6_1_external_decision_reduction_consequence
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (C :
      AppliedModelingLib.Complexity.ExternalReductionConsequence
        (weightedSetPackingDecisionProblem
          (Bidder := Bidder) (Item := Item))
        (singleMindedWelfareDecisionProblem
          (Bidder := Bidder) (Item := Item)))
    (hsource : C.SourceHard) :
    C.Consequence :=
  LOS02CombinatorialAuctions.paper_theorem6_1_external_decision_reduction_consequence
    C hsource

/--
External polynomial-reduction consequence form of Theorem 6.1 for threshold
decision problems, conditional on an external runtime certificate for the
set-to-bid encoding.
-/
theorem theorem6_1_external_polynomial_time_decision_reduction_consequence
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (PolynomialTime :
      (weightedSetPackingDecisionInstance Bidder Item →
        singleMindedWelfareDecisionInstance Bidder Item) → Prop)
    (hpoly :
      PolynomialTime setPackingDecisionToSingleMindedWelfareDecision)
    (C :
      AppliedModelingLib.Complexity.ExternalPolynomialReductionConsequence
        (weightedSetPackingDecisionProblem
          (Bidder := Bidder) (Item := Item))
        (singleMindedWelfareDecisionProblem
          (Bidder := Bidder) (Item := Item)))
    (hsource : C.SourceHard) :
    C.Consequence :=
  LOS02CombinatorialAuctions.paper_theorem6_1_external_polynomial_time_decision_reduction_consequence
    PolynomialTime hpoly C hsource

/--
Hardness-transfer form of Theorem 6.1: any abstract hardness notion closed
under many-one reductions transfers from weighted set packing to single-minded
welfare through the compiled set-to-bid reduction.
-/
theorem theorem6_1_set_packing_hardness_transfers_to_single_minded
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (H : AppliedModelingLib.Complexity.ReductionClosedHardness)
    (hsource :
      H.Hard
        (weightedSetPackingDecisionProblem
          (Bidder := Bidder) (Item := Item))) :
    H.Hard
      (singleMindedWelfareDecisionProblem
        (Bidder := Bidder) (Item := Item)) :=
  LOS02CombinatorialAuctions.paper_theorem6_1_set_packing_hardness_transfers_to_single_minded
    H hsource

/--
Polynomial-time hardness-transfer form of Theorem 6.1, conditional on an
external runtime certificate for the set-to-bid encoding.
-/
theorem theorem6_1_set_packing_polynomial_hardness_transfers_to_single_minded
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (PolynomialTime :
      (weightedSetPackingDecisionInstance Bidder Item →
        singleMindedWelfareDecisionInstance Bidder Item) → Prop)
    (hpoly :
      PolynomialTime setPackingDecisionToSingleMindedWelfareDecision)
    (H : AppliedModelingLib.Complexity.PolynomialReductionClosedHardness)
    (hsource :
      H.Hard
        (weightedSetPackingDecisionProblem
          (Bidder := Bidder) (Item := Item))) :
    H.Hard
      (singleMindedWelfareDecisionProblem
        (Bidder := Bidder) (Item := Item)) :=
  LOS02CombinatorialAuctions.paper_theorem6_1_set_packing_polynomial_hardness_transfers_to_single_minded
    PolynomialTime hpoly H hsource

/--
Conditional external-complexity form of Theorem 6.1 for exact optimization.
External set-packing hardness transfers to single-minded allocation through the
compiled LOS02 encoding.
-/
theorem theorem6_1_external_optimal_solver_complexity_consequence
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (FeasibleSM :
      ((Bidder → SingleMindedBid Item) → Finset Bidder) → Prop)
    (FeasibleWSP :
      ((Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) → Prop)
    (complexityConsequence : Prop)
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder)
    (hsolver : singleMindedOptimalSolver solver)
    (hfeasible : FeasibleSM solver)
    (hfeasible_transfer :
      FeasibleSM solver →
        FeasibleWSP (setPackingSolverOfSingleMindedSolver solver))
    (hexternal :
      ∀ wspSolver,
        weightedSetPackingOptimalSolver wspSolver →
          FeasibleWSP wspSolver → complexityConsequence) :
    complexityConsequence := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_external_optimal_solver_complexity_consequence
      FeasibleSM FeasibleWSP complexityConsequence solver hsolver hfeasible
      hfeasible_transfer hexternal

/--
Conditional external-complexity form of Theorem 6.1 for approximation. External
set-packing inapproximability transfers to single-minded allocation through the
compiled LOS02 encoding.
-/
theorem theorem6_1_external_approximation_solver_complexity_consequence
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (FeasibleSM :
      ((Bidder → SingleMindedBid Item) → Finset Bidder) → Prop)
    (FeasibleWSP :
      ((Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) → Prop)
    (complexityConsequence : Prop)
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder)
    (hsolver : singleMindedApproximationSolverAtLeast factor solver)
    (hfeasible : FeasibleSM solver)
    (hfeasible_transfer :
      FeasibleSM solver →
        FeasibleWSP (setPackingSolverOfSingleMindedSolver solver))
    (hexternal :
      ∀ wspSolver,
        weightedSetPackingApproximationSolverAtLeast factor wspSolver →
          FeasibleWSP wspSolver → complexityConsequence) :
    complexityConsequence := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_external_approximation_solver_complexity_consequence
      factor FeasibleSM FeasibleWSP complexityConsequence solver hsolver
      hfeasible hfeasible_transfer hexternal

/--
Named `NP = ZPP` specialization of the exact external-complexity wrapper.
External exact set-packing hardness transfers to single-minded allocation
through the compiled LOS02 encoding.
-/
theorem theorem6_1_external_optimal_solver_np_eq_zpp
    {Bidder Item Language : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (complexityModel :
      AppliedModelingLib.Complexity.ComplexityClassModel Language)
    (FeasibleSM :
      ((Bidder → SingleMindedBid Item) → Finset Bidder) → Prop)
    (FeasibleWSP :
      ((Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) → Prop)
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder)
    (hsolver : singleMindedOptimalSolver solver)
    (hfeasible : FeasibleSM solver)
    (hfeasible_transfer :
      FeasibleSM solver →
        FeasibleWSP (setPackingSolverOfSingleMindedSolver solver))
    (hexternal :
      ∀ wspSolver,
        weightedSetPackingOptimalSolver wspSolver →
          FeasibleWSP wspSolver → complexityModel.npEqZPP) :
    complexityModel.npEqZPP := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_external_optimal_solver_np_eq_zpp
      complexityModel FeasibleSM FeasibleWSP solver hsolver hfeasible
      hfeasible_transfer hexternal

/--
Named `NP = ZPP` specialization of the approximation external-complexity
wrapper. External set-packing inapproximability transfers to single-minded
allocation through the compiled LOS02 encoding.
-/
theorem theorem6_1_external_approximation_solver_np_eq_zpp
    {Bidder Item Language : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (complexityModel :
      AppliedModelingLib.Complexity.ComplexityClassModel Language)
    (FeasibleSM :
      ((Bidder → SingleMindedBid Item) → Finset Bidder) → Prop)
    (FeasibleWSP :
      ((Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) → Prop)
    (solver : (Bidder → SingleMindedBid Item) → Finset Bidder)
    (hsolver : singleMindedApproximationSolverAtLeast factor solver)
    (hfeasible : FeasibleSM solver)
    (hfeasible_transfer :
      FeasibleSM solver →
        FeasibleWSP (setPackingSolverOfSingleMindedSolver solver))
    (hexternal :
      ∀ wspSolver,
        weightedSetPackingApproximationSolverAtLeast factor wspSolver →
          FeasibleWSP wspSolver → complexityModel.npEqZPP) :
    complexityModel.npEqZPP := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_external_approximation_solver_np_eq_zpp
      factor complexityModel FeasibleSM FeasibleWSP solver hsolver hfeasible
      hfeasible_transfer hexternal

/-- Abstract randomized-class model for the source note after Theorem 6.1. -/
abbrev randomizedComplexityClassModel (Language : Type*) :=
  LOS02CombinatorialAuctions.paper_randomized_complexity_class_model Language

/-- Source complexity note: in the abstract model, `P = NP` implies `NP = ZPP`. -/
theorem complexity_note_p_eq_np_implies_np_eq_zpp
    {Language : Type*}
    (complexityModel : randomizedComplexityClassModel Language)
    (h : complexityModel.pEqNP) :
    complexityModel.toComplexityClassModel.npEqZPP := by
  exact
    LOS02CombinatorialAuctions.paper_complexity_note_p_eq_np_implies_np_eq_zpp
      complexityModel h

/-- Source complexity note: `NP = ZPP` implies `NP = RP` in the abstract model. -/
theorem complexity_note_np_eq_zpp_implies_np_eq_rp
    {Language : Type*}
    (complexityModel : randomizedComplexityClassModel Language)
    (h : complexityModel.toComplexityClassModel.npEqZPP) :
    complexityModel.NP = complexityModel.RP := by
  exact
    LOS02CombinatorialAuctions.paper_complexity_note_np_eq_zpp_implies_np_eq_rp
      complexityModel h

/-- Source complexity note: `NP = ZPP` implies `NP = co-RP` in the abstract model. -/
theorem complexity_note_np_eq_zpp_implies_np_eq_corp
    {Language : Type*}
    (complexityModel : randomizedComplexityClassModel Language)
    (h : complexityModel.toComplexityClassModel.npEqZPP) :
    complexityModel.NP = complexityModel.coRP := by
  exact
    LOS02CombinatorialAuctions.paper_complexity_note_np_eq_zpp_implies_np_eq_corp
      complexityModel h

/-- Source complexity note: `NP = ZPP` implies `NP = co-NP` in the abstract model. -/
theorem complexity_note_np_eq_zpp_implies_np_eq_conp
    {Language : Type*}
    (complexityModel : randomizedComplexityClassModel Language)
    (h : complexityModel.toComplexityClassModel.npEqZPP) :
    complexityModel.NP = complexityModel.coNP := by
  exact
    LOS02CombinatorialAuctions.paper_complexity_note_np_eq_zpp_implies_np_eq_conp
      complexityModel h

/--
Source complexity note: `NP = ZPP` gives the packaged randomized-class collapse
`NP = RP`, `NP = co-RP`, and `NP = co-NP` in the abstract model.
-/
theorem complexity_note_np_eq_zpp_implies_randomized_collapse
    {Language : Type*}
    (complexityModel : randomizedComplexityClassModel Language)
    (h : complexityModel.toComplexityClassModel.npEqZPP) :
    complexityModel.NP = complexityModel.RP ∧
      complexityModel.NP = complexityModel.coRP ∧
      complexityModel.NP = complexityModel.coNP := by
  exact
    LOS02CombinatorialAuctions.paper_complexity_note_np_eq_zpp_implies_randomized_collapse
      complexityModel h

/--
Theorem 6.1 graph-incidence reduction layer: independent vertex sets are
exactly feasible set-packing selections when goods are graph edges and each
vertex requests its incident edges.
-/
theorem theorem6_1_graph_independent_set_feasibility_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    setPackingFeasible (graphIncidentSets G) selected ↔
      graphIndependentSelection G selected := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_graph_independent_set_feasibility_reduction
      G selected

/--
Theorem 6.1 graph-incidence optimality reduction: maximum independent sets are
exactly optimal unit-weight set-packing selections under the graph-edge
incidence encoding.
-/
theorem theorem6_1_independent_set_set_packing_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    maximumIndependentSelection G selected ↔
      weightedSetPackingOptimal
        (graphIncidentSets G) (graphUnitWeights Vertex) selected := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_independent_set_set_packing_reduction
      G selected

/--
Theorem 6.1 graph-to-single-minded allocation reduction: maximum independent
sets are exactly optimal accepted sets after encoding graph edges as goods and
vertices as unit-value single-minded bids.
-/
theorem theorem6_1_independent_set_allocation_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    maximumIndependentSelection G selected ↔
      singleMindedOptimalAcceptedSet
        (setPackingSingleMindedBids
          (graphIncidentSets G) (graphUnitWeights Vertex)) selected := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_independent_set_allocation_reduction
      G selected

/--
Theorem 6.1 clique-complement layer: cliques in a graph are exactly
independent sets in its complement, preserving maximum-cardinality optimality.
-/
theorem theorem6_1_clique_complement_independent_set_reduction
    {Vertex : Type*}
    (G : SimpleGraph Vertex) (selected : Finset Vertex) :
    maximumCliqueSelection G selected ↔
      maximumIndependentSelection Gᶜ selected := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_clique_complement_independent_set_reduction
      G selected

/--
Theorem 6.1 clique-to-set-packing reduction: maximum cliques are exactly
optimal unit-weight set-packing selections after complementing the graph and
using complement-edge incidence sets.
-/
theorem theorem6_1_clique_complement_set_packing_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    maximumCliqueSelection G selected ↔
      weightedSetPackingOptimal
        (graphIncidentSets Gᶜ) (graphUnitWeights Vertex) selected := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_clique_complement_set_packing_reduction
      G selected

/--
Theorem 6.1 clique-to-single-minded allocation reduction: maximum cliques are
exactly optimal accepted sets after complementing the graph and encoding
complement edges as goods.
-/
theorem theorem6_1_clique_complement_allocation_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    maximumCliqueSelection G selected ↔
      singleMindedOptimalAcceptedSet
        (setPackingSingleMindedBids
          (graphIncidentSets Gᶜ) (graphUnitWeights Vertex)) selected := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_clique_complement_allocation_reduction
      G selected

/--
Theorem 6.1 clique decision reduction: clique threshold decision is independent
set threshold decision on the complement graph.
-/
theorem theorem6_1_clique_decision_complement_independent_set_reduction
    {Vertex : Type*}
    (problem : graphCliqueDecisionInstance Vertex) :
    graphCliqueDecisionProblem problem ↔
      graphIndependentSetDecisionProblem
        (graphCliqueDecisionToIndependentSetComplementDecision problem) := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_clique_decision_complement_independent_set_reduction
      problem

/--
Theorem 6.1 independent-set decision reduction: independent-set threshold
decision is unit-weight set-packing threshold decision on graph edges.
-/
theorem theorem6_1_independent_set_decision_set_packing_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (problem : graphIndependentSetDecisionInstance Vertex) :
    graphIndependentSetDecisionProblem problem ↔
      weightedSetPackingDecisionProblem
        (graphIndependentSetDecisionToWeightedSetPackingDecision problem) := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_independent_set_decision_set_packing_reduction
      problem

/--
Theorem 6.1 clique-to-set-packing decision reduction: clique threshold decision
is unit-weight set-packing threshold decision on complement edges.
-/
theorem theorem6_1_clique_decision_set_packing_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (problem : graphCliqueDecisionInstance Vertex) :
    graphCliqueDecisionProblem problem ↔
      weightedSetPackingDecisionProblem
        (graphCliqueDecisionToWeightedSetPackingDecision problem) := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_clique_decision_set_packing_reduction
      problem

/--
Theorem 6.1 clique-to-single-minded decision reduction: clique threshold
decision is single-minded welfare threshold decision on complement-edge goods.
-/
theorem theorem6_1_clique_decision_single_minded_welfare_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (problem : graphCliqueDecisionInstance Vertex) :
    graphCliqueDecisionProblem problem ↔
      singleMindedWelfareDecisionProblem
        (graphCliqueDecisionToSingleMindedWelfareDecision problem) := by
  exact
    LOS02CombinatorialAuctions.paper_theorem6_1_clique_decision_single_minded_welfare_reduction
      problem

/-- Theorem 6.1 clique-to-independent-set complement as an abstract many-one reduction. -/
noncomputable def theorem6_1_clique_decision_complement_many_one_reduction
    {Vertex : Type*} :
    AppliedModelingLib.Complexity.ManyOneReduction
      (graphCliqueDecisionProblem (Vertex := Vertex))
      (graphIndependentSetDecisionProblem (Vertex := Vertex)) :=
  LOS02CombinatorialAuctions.paper_theorem6_1_clique_decision_complement_many_one_reduction

/-- Theorem 6.1 independent-set-to-set-packing as an abstract many-one reduction. -/
noncomputable def theorem6_1_independent_set_decision_many_one_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex] :
    AppliedModelingLib.Complexity.ManyOneReduction
      (graphIndependentSetDecisionProblem (Vertex := Vertex))
      (weightedSetPackingDecisionProblem
        (Bidder := Vertex) (Item := Sym2 Vertex)) :=
  LOS02CombinatorialAuctions.paper_theorem6_1_independent_set_decision_many_one_reduction

/-- Theorem 6.1 clique-to-set-packing as an abstract many-one reduction. -/
noncomputable def theorem6_1_clique_decision_set_packing_many_one_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex] :
    AppliedModelingLib.Complexity.ManyOneReduction
      (graphCliqueDecisionProblem (Vertex := Vertex))
      (weightedSetPackingDecisionProblem
        (Bidder := Vertex) (Item := Sym2 Vertex)) :=
  LOS02CombinatorialAuctions.paper_theorem6_1_clique_decision_set_packing_many_one_reduction

/-- Theorem 6.1 clique-to-single-minded welfare as an abstract many-one reduction. -/
noncomputable def theorem6_1_clique_decision_single_minded_many_one_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex] :
    AppliedModelingLib.Complexity.ManyOneReduction
      (graphCliqueDecisionProblem (Vertex := Vertex))
      (singleMindedWelfareDecisionProblem
        (Bidder := Vertex) (Item := Sym2 Vertex)) :=
  LOS02CombinatorialAuctions.paper_theorem6_1_clique_decision_single_minded_many_one_reduction

/--
Theorem 6.1 clique-to-single-minded welfare as an abstract polynomial-time
reduction, conditional on an external runtime certificate for the complement
edge-incidence set-to-bid encoding.
-/
noncomputable def theorem6_1_clique_decision_single_minded_polynomial_time_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (PolynomialTime :
      (graphCliqueDecisionInstance Vertex →
        singleMindedWelfareDecisionInstance Vertex (Sym2 Vertex)) → Prop)
    (hpoly :
      PolynomialTime graphCliqueDecisionToSingleMindedWelfareDecision) :
    AppliedModelingLib.Complexity.PolynomialTimeReduction
      (graphCliqueDecisionProblem (Vertex := Vertex))
      (singleMindedWelfareDecisionProblem
        (Bidder := Vertex) (Item := Sym2 Vertex)) :=
  LOS02CombinatorialAuctions.paper_theorem6_1_clique_decision_single_minded_polynomial_time_reduction
    PolynomialTime hpoly

/--
External reduction-consequence form of Theorem 6.1 for the classic clique
hardness route: any external consequence that follows from a many-one reduction
out of clique follows for the encoded single-minded welfare target.
-/
theorem theorem6_1_external_clique_decision_single_minded_reduction_consequence
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (C :
      AppliedModelingLib.Complexity.ExternalReductionConsequence
        (graphCliqueDecisionProblem (Vertex := Vertex))
        (singleMindedWelfareDecisionProblem
          (Bidder := Vertex) (Item := Sym2 Vertex)))
    (hsource : C.SourceHard) :
    C.Consequence :=
  LOS02CombinatorialAuctions.paper_theorem6_1_external_clique_decision_single_minded_reduction_consequence
    C hsource

/--
External polynomial-reduction consequence form of Theorem 6.1 for the classic
clique hardness route, conditional on an external runtime certificate for the
compiled clique-to-single-minded encoding.
-/
theorem theorem6_1_external_clique_polynomial_time_single_minded_reduction_consequence
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (PolynomialTime :
      (graphCliqueDecisionInstance Vertex →
        singleMindedWelfareDecisionInstance Vertex (Sym2 Vertex)) → Prop)
    (hpoly :
      PolynomialTime graphCliqueDecisionToSingleMindedWelfareDecision)
    (C :
      AppliedModelingLib.Complexity.ExternalPolynomialReductionConsequence
        (graphCliqueDecisionProblem (Vertex := Vertex))
        (singleMindedWelfareDecisionProblem
          (Bidder := Vertex) (Item := Sym2 Vertex)))
    (hsource : C.SourceHard) :
    C.Consequence :=
  LOS02CombinatorialAuctions.paper_theorem6_1_external_clique_polynomial_time_single_minded_reduction_consequence
    PolynomialTime hpoly C hsource

/--
Hardness-transfer form of Theorem 6.1 for the classic clique route: any
abstract hardness notion closed under many-one reductions transfers from clique
to single-minded welfare through the compiled complement-edge encoding.
-/
theorem theorem6_1_clique_hardness_transfers_to_single_minded
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (H : AppliedModelingLib.Complexity.ReductionClosedHardness)
    (hsource :
      H.Hard (graphCliqueDecisionProblem (Vertex := Vertex))) :
    H.Hard
      (singleMindedWelfareDecisionProblem
        (Bidder := Vertex) (Item := Sym2 Vertex)) :=
  LOS02CombinatorialAuctions.paper_theorem6_1_clique_hardness_transfers_to_single_minded
    H hsource

/--
Polynomial-time hardness-transfer form of Theorem 6.1 for the classic clique
route, conditional on an external runtime certificate for the compiled
complement-edge encoding.
-/
theorem theorem6_1_clique_polynomial_hardness_transfers_to_single_minded
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (PolynomialTime :
      (graphCliqueDecisionInstance Vertex →
        singleMindedWelfareDecisionInstance Vertex (Sym2 Vertex)) → Prop)
    (hpoly :
      PolynomialTime graphCliqueDecisionToSingleMindedWelfareDecision)
    (H : AppliedModelingLib.Complexity.PolynomialReductionClosedHardness)
    (hsource :
      H.Hard (graphCliqueDecisionProblem (Vertex := Vertex))) :
    H.Hard
      (singleMindedWelfareDecisionProblem
        (Bidder := Vertex) (Item := Sym2 Vertex)) :=
  LOS02CombinatorialAuctions.paper_theorem6_1_clique_polynomial_hardness_transfers_to_single_minded
    PolynomialTime hpoly H hsource

/-- Finite-or-infinite critical-value certificate for accepted-set mechanisms. -/
abbrev singleMindedCriticalValueWithInfinityCertificate
    {Bidder Item : Type*} [DecidableEq Bidder]
    (M : SingleMindedAcceptedMechanism Bidder Item) :=
  M.CriticalValueWithInfinityCertificate

/--
Finite-or-infinite critical-value certificate restricted to the source
nonempty, nonnegative single-minded report domain.
-/
abbrev singleMindedNonnegativeCriticalValueWithInfinityCertificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item) :=
  M.NonnegativeCriticalValueWithInfinityCertificate

/-- Definition 7.1: average amount per good for a single-minded bid. -/
noncomputable abbrev averageAmountPerGood {Item : Type*} [DecidableEq Item]
    (b : SingleMindedBid Item) : ℝ :=
  LOS02CombinatorialAuctions.paper_average_amount_per_good b

/--
If a bid's declared value is below `|s| * c(n)`, its average amount per good is
below `c(n)`.
-/
theorem averageAmountPerGood_lt_of_value_lt_bundleSize_mul
    {Item : Type*} [DecidableEq Item]
    (b n : SingleMindedBid Item) (hb : b.desired.Nonempty)
    (hlt : b.value < b.bundleSize * n.averageAmountPerGood) :
    averageAmountPerGood b < averageAmountPerGood n := by
  exact
    LOS02CombinatorialAuctions.paper_average_amount_per_good_lt_of_value_lt_bundleSize_mul
      b n hb hlt

/--
If a bid's declared value is above `|s| * c(n)`, its average amount per good is
above `c(n)`.
-/
theorem averageAmountPerGood_lt_of_bundleSize_mul_lt_value
    {Item : Type*} [DecidableEq Item]
    (b n : SingleMindedBid Item) (hb : b.desired.Nonempty)
    (hlt : b.bundleSize * n.averageAmountPerGood < b.value) :
    averageAmountPerGood n < averageAmountPerGood b := by
  exact
    LOS02CombinatorialAuctions.paper_average_amount_per_good_lt_of_bundleSize_mul_lt_value
      b n hb hlt

/--
On the nonnegative source domain, shrinking a nonempty desired bundle while
weakly increasing value weakly increases the average amount per good.
-/
theorem averageAmountPerGood_le_of_subset_value_le
    {Item : Type*} [DecidableEq Item]
    (b : SingleMindedBid Item) {s : Bundle Item} {v : ℝ}
    (hb_nonempty : b.desired.Nonempty) (hs : s.Nonempty)
    (hsub : s ⊆ b.desired)
    (hb_nonneg : 0 ≤ b.value) (hle : b.value ≤ v) :
    averageAmountPerGood b ≤
      averageAmountPerGood
        ({ desired := s, value := v } : SingleMindedBid Item) := by
  exact
    LOS02CombinatorialAuctions.paper_average_amount_per_good_le_of_subset_value_le
      b hb_nonempty hs hsub hb_nonneg hle

/-- The square-root norm used in Theorem 7.2, `a / sqrt(|s|)`. -/
noncomputable abbrev sqrtAmountNorm {Item : Type*} [DecidableEq Item]
    (b : SingleMindedBid Item) : ℝ :=
  LOS02CombinatorialAuctions.paper_sqrt_amount_norm b

/-- Concrete LOS02 order: decreasing average amount per good with deterministic tie-breaks. -/
noncomputable abbrev averageOrderOf
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) : List Bidder :=
  LOS02CombinatorialAuctions.paper_average_order_of bids

/-- The concrete LOS02 average order has no duplicate bidders. -/
theorem averageOrderOf_nodup
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    (averageOrderOf bids).Nodup := by
  exact LOS02CombinatorialAuctions.paper_average_order_of_nodup bids

/-- Every bidder appears in the concrete LOS02 average order. -/
theorem averageOrderOf_mem
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (i : Bidder) :
    i ∈ averageOrderOf bids := by
  exact LOS02CombinatorialAuctions.paper_average_order_of_mem bids i

/-- The concrete LOS02 average order is weakly average-descending. -/
theorem averageOrderOf_average_descending
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    LOS02CombinatorialAuctions.paper_average_amount_descending
      bids (averageOrderOf bids) := by
  exact LOS02CombinatorialAuctions.paper_average_order_of_average_descending bids

/--
Section 10 source-order movement step: replacing an accepted bidder's report by
a nonempty subset bundle with weakly larger value moves that bidder weakly
earlier in the concrete average order on the nonnegative domain.
-/
theorem theorem10_2_average_order_update_moves_earlier
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    (hbids : nonnegativeNonemptySingleMindedProfile bids)
    {j : Bidder} {s : Bundle Item} {v : ℝ}
    (hupdated :
      nonnegativeNonemptySingleMindedProfile
        (Function.update bids j { desired := s, value := v }))
    (hsub : s ⊆ (bids j).desired)
    (hle : (bids j).value ≤ v) :
    ∃ pref rest suffix tail,
      averageOrderOf bids = (pref ++ rest) ++ j :: suffix ∧
        averageOrderOf (Function.update bids j { desired := s, value := v }) =
          pref ++ j :: tail ∧
        j ∉ pref ∧ j ∉ rest ∧ j ∉ suffix := by
  exact
    LOS02CombinatorialAuctions.paper_theorem10_2_average_order_update_moves_earlier
      bids hbids hupdated hsub hle

/--
Changing only one bidder's value leaves the concrete LOS02 average order
unchanged after erasing that bidder.
-/
theorem averageOrderOf_erase_valueUpdate
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) (value : ℝ) :
    (averageOrderOf
        (LOS02CombinatorialAuctions.paper_single_minded_value_update
          bids j value)).erase j =
      (averageOrderOf bids).erase j := by
  exact
    LOS02CombinatorialAuctions.paper_average_order_of_erase_value_update
      bids j value

/-- Split form of concrete-order erase-stability under a value-only update. -/
theorem averageOrderOf_erase_valueUpdate_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder : averageOrderOf bids = before ++ j :: base) :
    (averageOrderOf
        (LOS02CombinatorialAuctions.paper_single_minded_value_update
          bids j value)).erase j =
      before ++ base := by
  exact
    LOS02CombinatorialAuctions.paper_average_order_of_erase_value_update_of_split
      bids value horder

/--
Concrete-order sortedness, duplicate-freeness, membership, and global
erase-stability facts for a value-only update around a displayed split.
-/
theorem averageOrderOf_valueUpdate_global_facts_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder : averageOrderOf bids = before ++ j :: base) :
    let updated :=
      LOS02CombinatorialAuctions.paper_single_minded_value_update
        bids j value
    let updatedOrder := averageOrderOf updated
    LOS02CombinatorialAuctions.paper_average_amount_descending
      updated updatedOrder ∧
      updatedOrder.Nodup ∧
      j ∈ updatedOrder ∧
      updatedOrder.erase j = before ++ base := by
  exact
    LOS02CombinatorialAuctions.paper_average_order_value_update_global_facts_of_split
      bids value horder

/--
After a value-only update, the concrete average order is obtained by inserting
`j` into the original order with `j` erased.
-/
theorem averageOrderOf_valueUpdate_eq_orderedInsertErase_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder : averageOrderOf bids = before ++ j :: base) :
    averageOrderOf
        (LOS02CombinatorialAuctions.paper_single_minded_value_update
          bids j value) =
      (before ++ base).orderedInsert
        (AppliedModelingLib.Auction.singleMindedAverageTieRel
          (LOS02CombinatorialAuctions.paper_single_minded_value_update
            bids j value))
        j := by
  exact
    LOS02CombinatorialAuctions.paper_average_order_of_value_update_eq_ordered_insert_erase_of_split
      bids value horder

/--
The prefix state before `j`, after erasing accepted `j`, is unchanged by a
value-only update to `j`.
-/
theorem averageValueUpdate_prefixStateErase_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder : averageOrderOf bids = before ++ j :: base)
    (hjaccepted :
      j ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])) :
    (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])).erase j =
      singleMindedGreedyAcceptedFromState
        (LOS02CombinatorialAuctions.paper_single_minded_value_update
          bids j value) ∅ before := by
  exact
    LOS02CombinatorialAuctions.paper_average_value_update_prefix_state_erase_of_split
      bids value horder hjaccepted

/--
Concrete local suffix window for value-only updates around a displayed average
order split.
-/
noncomputable abbrev averageValueUpdateWindow
    {Bidder Item : Type*} [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    (j : Bidder) (base : List Bidder) (value : ℝ) : List Bidder :=
  LOS02CombinatorialAuctions.paper_average_value_update_window bids j base value

/--
The concrete suffix window is average-descending, duplicate-free, contains `j`,
and erases back to the original suffix `base`.
-/
theorem averageValueUpdateWindow_facts_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder : averageOrderOf bids = before ++ j :: base) :
    let window := averageValueUpdateWindow bids j base value
    LOS02CombinatorialAuctions.paper_average_amount_descending
      (LOS02CombinatorialAuctions.paper_single_minded_value_update
        bids j value) window ∧
      window.Nodup ∧
      window.erase j = base ∧
      j ∈ window := by
  exact
    LOS02CombinatorialAuctions.paper_average_value_update_window_facts_of_split
      bids value horder

/--
For the concrete average-order suffix window, local acceptance of `j` after
erasing accepted `j` is equivalent to acceptance by the full updated greedy
mechanism.
-/
theorem averageValueUpdateWindow_membership_iff_mechanism_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder : averageOrderOf bids = before ++ j :: base)
    (hjaccepted :
      j ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])) :
    j ∈ singleMindedGreedyAcceptedFromOrder
        (LOS02CombinatorialAuctions.paper_single_minded_value_update
          bids j value)
        (averageOrderOf
          (LOS02CombinatorialAuctions.paper_single_minded_value_update
            bids j value)) ↔
      j ∈ singleMindedGreedyAcceptedFromState
        (LOS02CombinatorialAuctions.paper_single_minded_value_update
          bids j value)
        ((singleMindedGreedyAcceptedFromState bids ∅
          (before ++ [j])).erase j)
        (averageValueUpdateWindow bids j base value) := by
  exact
    LOS02CombinatorialAuctions.paper_average_value_update_window_membership_iff_mechanism_of_split
      bids value horder hjaccepted

/-- Total value of a finite set of single-minded bids. -/
noncomputable abbrev singleMindedTotalValue
    {Bidder Item : Type*} [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) (selected : Finset Bidder) : ℝ :=
  LOS02CombinatorialAuctions.paper_single_minded_total_value bids selected

/--
Value-only perturbation of a single-minded bid profile, preserving every
desired bundle. This is the report change used in Theorem 10.2's critical-price
argument.
-/
abbrev valueUpdate
    {Bidder Item : Type*} [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) (value : ℝ) :
    Bidder → SingleMindedBid Item :=
  LOS02CombinatorialAuctions.paper_single_minded_value_update bids j value

/-- A value-only perturbation preserves every desired bundle. -/
theorem valueUpdate_desired
    {Bidder Item : Type*} [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item)
    (j : Bidder) (value : ℝ) (k : Bidder) :
    (valueUpdate bids j value k).desired = (bids k).desired := by
  exact
    LOS02CombinatorialAuctions.paper_single_minded_value_update_desired
      bids j value k

/-- A value-only perturbation preserves which bid pairs conflict. -/
theorem valueUpdate_conflict_iff
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (j : Bidder) (value : ℝ) (i k : Bidder) :
    SingleMindedBidsConflict (valueUpdate bids j value) i k ↔
      SingleMindedBidsConflict bids i k := by
  exact
    LOS02CombinatorialAuctions.paper_single_minded_value_update_conflict_iff
      bids j value i k

/-- Greedy accepted set from an explicit bid order. -/
abbrev greedyAcceptedFromOrder
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) :
    Finset Bidder :=
  LOS02CombinatorialAuctions.paper_single_minded_greedy_accepted_from_order
    bids order

/-- Section 10 average-amount-per-good descending order predicate. -/
abbrev averageAmountDescending
    {Bidder Item : Type*} [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_average_amount_descending bids order

/-- Greedy allocation from an explicit bid order. -/
abbrev greedyAllocationFromOrder
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) :
    BundleAllocation Bidder Item :=
  LOS02CombinatorialAuctions.paper_single_minded_greedy_allocation_from_order
    bids order

/-- The paper's concrete average-order greedy accepted set. -/
noncomputable abbrev averageGreedyAcceptedSet
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) : Finset Bidder :=
  LOS02CombinatorialAuctions.paper_average_greedy_accepted_set bids

/-- The paper's concrete average-order greedy allocation. -/
noncomputable abbrev averageGreedyAllocation
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    BundleAllocation Bidder Item :=
  LOS02CombinatorialAuctions.paper_average_greedy_allocation bids

/-- Definition 10.1 payment formula from the supplied `n(j)` function. -/
noncomputable abbrev greedyPaymentFromNextDenied
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder)
    (nextDenied : Bidder → Option Bidder) (j : Bidder) : ℝ :=
  LOS02CombinatorialAuctions.paper_greedy_payment_from_next_denied
    bids accepted nextDenied j

/--
Definition 10.1 condition at a greedy prefix state: bid `i` is denied because
of accepted bid `j`.
-/
abbrev greedyDeniedBecauseOfAtState
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBefore : Finset Bidder) (j i : Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_greedy_denied_because_of_at_state
    bids acceptedBefore j i

/--
Definition 10.1 `n(j)` search from a supplied greedy prefix state and a suffix
after `j`.
-/
abbrev greedyFirstDeniedBecauseOfFromState
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (suffix : List Bidder) (j : Bidder) : Option Bidder :=
  LOS02CombinatorialAuctions.paper_greedy_first_denied_because_of_from_state
    bids acceptedBeforeSuffix suffix j

/--
Definition 10.1 `n(j)` search from an explicit split of the sorted order into
the bids before `j`, bid `j`, and the suffix after `j`.
-/
abbrev greedyNextDeniedFromSplit
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j : Bidder) : Option Bidder :=
  LOS02CombinatorialAuctions.paper_greedy_next_denied_from_split
    bids pre suffix j

/-- Definition 10.1 `n(j)` search from the full sorted greedy order. -/
abbrev greedyNextDeniedFromOrder
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (j : Bidder) : Option Bidder :=
  LOS02CombinatorialAuctions.paper_greedy_next_denied_from_order
    bids order j

/-- Definition 10.1 payment rule computed from the full sorted greedy order. -/
noncomputable abbrev greedyPaymentFromOrder
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (j : Bidder) : ℝ :=
  LOS02CombinatorialAuctions.paper_greedy_payment_from_order
    bids order j

/-- The paper's concrete average-order Definition 10.1 payment rule. -/
noncomputable abbrev averageGreedyPayment
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) : ℝ :=
  LOS02CombinatorialAuctions.paper_average_greedy_payment bids j

/-- Greedy accepted-set mechanism generated by a paper-supplied order rule. -/
noncomputable abbrev greedyAcceptedMechanismFromOrderOf
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder) :
    SingleMindedAcceptedMechanism Bidder Item :=
  LOS02CombinatorialAuctions.paper_single_minded_greedy_accepted_mechanism_from_order_of
    orderOf

/-- The paper's concrete average-order greedy accepted-set mechanism. -/
noncomputable abbrev averageGreedyAcceptedMechanism
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder] :
    SingleMindedAcceptedMechanism Bidder Item :=
  LOS02CombinatorialAuctions.paper_average_greedy_accepted_mechanism
    (Bidder := Bidder) (Item := Item)

/--
Full-order Definition 10.1 denied-because-of relation, packaged around the
first occurrence of `j` in the sorted greedy order.
-/
abbrev greedyDeniedBecauseOfAfterInOrder
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (j i : Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_greedy_denied_because_of_after_in_order
    bids order j i

/-! ## Formalized Paper-Facing Statements -/

/-- The reject-all direct combinatorial auction is dominant-strategy truthful. -/
theorem reject_all_truthful
    {Bidder Item : Type*} [DecidableEq Bidder] :
    (rejectAllAuction : CombinatorialAuction Bidder Item).TruthfulDominantStrategy := by
  exact LOS02CombinatorialAuctions.paper_combinatorial_reject_all_truthful

/-- The reject-all direct combinatorial auction has no positive transfers. -/
theorem reject_all_no_positive_transfers
    {Bidder Item : Type*} :
    (rejectAllAuction : CombinatorialAuction Bidder Item).NoPositiveTransfers := by
  exact LOS02CombinatorialAuctions.paper_combinatorial_reject_all_no_positive_transfers

/-- Theorem 4.1: a welfare-maximizing generalized Vickrey auction is truthful. -/
theorem theorem4_1_generalized_vickrey_truthful
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item)
    (hmax : gvaWelfareMaximizingAllocationRule alloc) :
    (generalizedVickreyAuction alloc).TruthfulDominantStrategy := by
  exact
    LOS02CombinatorialAuctions.paper_theorem4_1_generalized_vickrey_truthful
      alloc hmax

/--
Proposition 4.2: with nonnegative bundle values, a truthful bidder's GVA utility
is nonnegative.
-/
theorem proposition4_2_generalized_vickrey_truthful_utility_nonneg
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item)
    (hmax : gvaWelfareMaximizingAllocationRule alloc)
    (values : CombinatorialReport Bidder Item)
    (hvalues : nonnegativeValues values) (i : Bidder) :
    0 ≤ (generalizedVickreyAuction alloc).utility values values i := by
  exact
    LOS02CombinatorialAuctions.paper_proposition4_2_generalized_vickrey_truthful_utility_nonneg
      alloc hmax values hvalues i

/--
Target-bundle critical-price mechanisms are truthful on normalized bundle
valuations when each bidder's offered price is independent of that bidder's own
report.
-/
theorem target_bundle_threshold_truthful_on_normalized
    {Bidder Item : Type*} [DecidableEq Bidder]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind : BundlePriceOwnReportIndependent price) :
    truthfulOn (targetBundleThresholdAuction target price)
      CombinatorialAuction.Normalized := by
  exact
    LOS02CombinatorialAuctions.paper_combinatorial_target_bundle_threshold_truthful_on_normalized
      target price hind

/--
Target-bundle critical-price mechanisms are truthful on nonempty single-minded
valuation profiles when each bidder's offered price is independent of that
bidder's own report.
-/
theorem target_bundle_threshold_truthful_on_single_minded
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind : BundlePriceOwnReportIndependent price) :
    truthfulOn (targetBundleThresholdAuction target price)
      IsNonemptySingleMindedProfile := by
  exact
    LOS02CombinatorialAuctions.paper_combinatorial_target_bundle_threshold_truthful_on_single_minded
      target price hind

/--
Target-bundle threshold allocations are feasible when every accepted target is
contained in the goods set and accepted targets are pairwise disjoint.
-/
theorem target_bundle_threshold_feasible_of_pairwise_disjoint
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder] [DecidableEq Item]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (reports : CombinatorialReport Bidder Item)
    (goods : Finset Item)
    (hgoods : ∀ i,
      i ∈ targetBundleWinners target price reports → target i ⊆ goods)
    (hdisjoint :
      PairwiseDisjointDesired
        (targetAsSingleMindedBids target reports)
        (targetBundleWinners target price reports)) :
    IsFeasibleBundleAllocation
      ((targetBundleThresholdAuction target price).allocation reports)
      goods := by
  exact
    LOS02CombinatorialAuctions.paper_combinatorial_target_bundle_threshold_feasible_of_pairwise_disjoint
      target price reports goods hgoods hdisjoint

/--
Theorem 9.6, source-shaped accepted-set form: Exactness is represented by the
accepted-set mechanism model, and Monotonicity, Participation, and Critical
imply truthful single-minded declarations.
-/
theorem theorem9_6_single_minded_truthful_of_axioms
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hmono : M.Monotonicity)
    (hpart : M.Participation)
    (C : M.CriticalValueCertificate) :
    singleMindedTruthfulOn M nonnegativeNonemptySingleMindedProfile := by
  exact
    LOS02CombinatorialAuctions.paper_theorem9_6_single_minded_truthful_of_axioms
      M hmono hpart C

/--
Theorem 9.6 with the source's infinite critical-value branch represented by
`none` in the critical-value certificate.
-/
theorem theorem9_6_single_minded_truthful_of_infinity_axioms
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hmono : M.Monotonicity)
    (hpart : M.Participation)
    (C : M.CriticalValueWithInfinityCertificate) :
    singleMindedTruthfulOn M nonnegativeNonemptySingleMindedProfile := by
  exact
    LOS02CombinatorialAuctions.paper_theorem9_6_single_minded_truthful_of_infinity_axioms
      M hmono hpart C

/--
Domain-aware Theorem 9.6: critical-value clauses are required only on nonempty,
nonnegative single-minded reports.
-/
theorem theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hmono : M.MonotonicityOn nonnegativeNonemptySingleMindedProfile)
    (hpart : M.Participation)
    (C : M.NonnegativeCriticalValueWithInfinityCertificate) :
    singleMindedTruthfulOn M nonnegativeNonemptySingleMindedProfile := by
  exact
    LOS02CombinatorialAuctions.paper_theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms
      M hmono hpart C

/--
Lemma 9.1 threshold existence: monotonicity gives either a finite nonnegative
critical value for a fixed nonempty desired set, or an infinite branch in which
the bidder never wins at any nonnegative declared value.
-/
theorem lemma9_1_exists_nonnegative_critical_value_of_monotonicity
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hmono : M.MonotonicityOn nonnegativeNonemptySingleMindedProfile)
    (reports : Bidder → SingleMindedBid Item)
    (hreports : nonnegativeNonemptySingleMindedProfile reports)
    (i : Bidder) (s : Finset Item) (hs : s.Nonempty) :
    (∃ c : ℝ,
      0 ≤ c ∧
        (∀ v, 0 ≤ v → v < c →
          i ∉ M.accepted
            (Function.update reports i { desired := s, value := v })) ∧
        (∀ v, 0 ≤ v → c < v →
          i ∈ M.accepted
            (Function.update reports i { desired := s, value := v }))) ∨
      (∀ v, 0 ≤ v →
        i ∉ M.accepted
          (Function.update reports i { desired := s, value := v })) := by
  exact
    LOS02CombinatorialAuctions.paper_lemma9_1_exists_nonnegative_critical_value_of_monotonicity
      M hmono reports hreports i s hs

/--
Lemma 9.2 denied-bidder utility case: Participation makes every denied
nonempty single-minded type's utility equal to zero.
-/
theorem lemma9_2_denied_bidder_utility_eq_zero
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hpart : M.Participation)
    (values reports : Bidder → SingleMindedBid Item)
    (hvalues : nonnegativeNonemptySingleMindedProfile values)
    {i : Bidder}
    (hdeny : i ∉ M.accepted reports) :
    M.utility values reports i = 0 := by
  exact
    LOS02CombinatorialAuctions.paper_lemma9_2_denied_bidder_utility_eq_zero
      M hpart values reports hvalues hdeny

/--
Lemma 9.3 truthful-utility case: under Participation and the source-domain
critical-value certificate, truthful reporting gives nonnegative utility.
-/
theorem lemma9_3_truthful_utility_nonnegative_of_nonnegative_infinity_certificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hpart : M.Participation)
    (C : M.NonnegativeCriticalValueWithInfinityCertificate)
    (values : Bidder → SingleMindedBid Item)
    (hvalues : nonnegativeNonemptySingleMindedProfile values)
    (i : Bidder) :
    0 ≤ M.utility values values i := by
  exact
    LOS02CombinatorialAuctions.paper_lemma9_3_truthful_utility_nonnegative_of_nonnegative_infinity_certificate
      M hpart C values hvalues i

/--
Lemma 9.4 value-only deviation case: changing only bidder `i`'s declared value
cannot improve utility once the Theorem 9.6 source-domain axioms hold.
-/
theorem lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hmono : M.MonotonicityOn nonnegativeNonemptySingleMindedProfile)
    (hpart : M.Participation)
    (C : M.NonnegativeCriticalValueWithInfinityCertificate)
    (values : Bidder → SingleMindedBid Item)
    (hvalues : nonnegativeNonemptySingleMindedProfile values)
    (i : Bidder) {v' : ℝ} (hv' : 0 ≤ v') :
    M.utility values
        (Function.update values i
          { desired := (values i).desired, value := v' }) i ≤
      M.utility values values i := by
  exact
    LOS02CombinatorialAuctions.paper_lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms
      M hmono hpart C values hvalues i hv'

/--
Lemma 9.5 critical-price monotonicity: a nonempty smaller desired set has finite
critical value at most the finite critical value for a larger desired set.
-/
theorem lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hmono : M.MonotonicityOn nonnegativeNonemptySingleMindedProfile)
    (C : M.NonnegativeCriticalValueWithInfinityCertificate)
    (reports : Bidder → SingleMindedBid Item)
    (hreports : nonnegativeNonemptySingleMindedProfile reports)
    (i : Bidder) {sSmall sLarge : Finset Item} {pLarge : ℝ}
    (hsSmall : sSmall.Nonempty) (hsLarge : sLarge.Nonempty)
    (hsub : sSmall ⊆ sLarge)
    (hLarge : C.threshold reports i sLarge = some pLarge) :
    ∃ pSmall,
      C.threshold reports i sSmall = some pSmall ∧ pSmall ≤ pLarge := by
  exact
    LOS02CombinatorialAuctions.paper_lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate
      M hmono C reports hreports i hsSmall hsLarge hsub hLarge

/-- The greedy accepted set has pairwise-disjoint desired bundles. -/
theorem greedy_accepted_pairwise_disjoint
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) :
    PairwiseDisjointDesired bids
      (greedyAcceptedFromOrder bids order) := by
  exact
    LOS02CombinatorialAuctions.paper_single_minded_greedy_accepted_pairwise_disjoint
      bids order

/-- The greedy fold preserves pairwise-disjoint accepted states. -/
theorem greedy_accepted_from_state_pairwise_disjoint
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (order : List Bidder)
    (haccepted : PairwiseDisjointDesired bids accepted) :
    PairwiseDisjointDesired bids
      (singleMindedGreedyAcceptedFromState bids accepted order) := by
  exact
    LOS02CombinatorialAuctions.paper_single_minded_greedy_accepted_from_state_pairwise_disjoint
      bids accepted order haccepted

/-- The greedy allocation is feasible when accepted desired bundles lie in `goods`. -/
theorem greedy_allocation_feasible
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (goods : Finset Item)
    (hgoods : ∀ i,
      i ∈ greedyAcceptedFromOrder bids order → (bids i).desired ⊆ goods) :
    IsFeasibleBundleAllocation
      (greedyAllocationFromOrder bids order) goods := by
  exact
    LOS02CombinatorialAuctions.paper_single_minded_greedy_allocation_feasible
      bids order goods hgoods

/-- The concrete average-order greedy accepted set is pairwise disjoint. -/
theorem averageGreedyAcceptedSet_pairwise_disjoint
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    PairwiseDisjointDesired bids (averageGreedyAcceptedSet bids) := by
  exact
    LOS02CombinatorialAuctions.paper_average_greedy_accepted_pairwise_disjoint
      bids

/-- The concrete average-order greedy allocation is feasible under the goods-scope premise. -/
theorem averageGreedyAllocation_feasible
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (goods : Finset Item)
    (hgoods : ∀ i,
      i ∈ averageGreedyAcceptedSet bids → (bids i).desired ⊆ goods) :
    IsFeasibleBundleAllocation (averageGreedyAllocation bids) goods := by
  exact
    LOS02CombinatorialAuctions.paper_average_greedy_allocation_feasible
      bids goods hgoods

/--
Concrete Section 7 greedy allocation scheme for the paper's average-order list:
the accepted bids are conflict-free and the induced allocation is feasible under
the usual goods-scope premise.
-/
theorem averageOrder_greedy_allocation_scheme
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (goods : Finset Item)
    (hgoods : ∀ i,
      i ∈ averageGreedyAcceptedSet bids → (bids i).desired ⊆ goods) :
    PairwiseDisjointDesired bids (averageGreedyAcceptedSet bids) ∧
      IsFeasibleBundleAllocation (averageGreedyAllocation bids) goods := by
  exact
    LOS02CombinatorialAuctions.paper_average_order_greedy_allocation_scheme
      bids goods hgoods

/-- Denied bids pay zero in the greedy payment formula. -/
theorem greedy_payment_eq_zero_of_denied
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder)
    (nextDenied : Bidder → Option Bidder) {j : Bidder}
    (hj : j ∉ accepted) :
    greedyPaymentFromNextDenied bids accepted nextDenied j = 0 := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_payment_eq_zero_of_denied
      bids accepted nextDenied hj

/-- Granted bids with no `n(j)` pay zero in the greedy payment formula. -/
theorem greedy_payment_eq_zero_of_no_next
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder)
    (nextDenied : Bidder → Option Bidder) {j : Bidder}
    (hj : j ∈ accepted) (hnext : nextDenied j = none) :
    greedyPaymentFromNextDenied bids accepted nextDenied j = 0 := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_payment_eq_zero_of_no_next
      bids accepted nextDenied hj hnext

/-- If `n(j)` exists, the greedy payment is `|s_j| * c(n(j))`. -/
theorem greedy_payment_eq_of_next
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder)
    (nextDenied : Bidder → Option Bidder) {j n : Bidder}
    (hj : j ∈ accepted) (hnext : nextDenied j = some n) :
    greedyPaymentFromNextDenied bids accepted nextDenied j =
      (bids j).bundleSize * (bids n).averageAmountPerGood := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_payment_eq_of_next
      bids accepted nextDenied hj hnext

/--
If the prefix-state `n(j)` search returns `n`, then `n` is in the later suffix
and satisfies the prefix-local denied-because-of condition at its turn.
-/
theorem greedy_first_denied_because_of_from_state_some_spec
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (suffix : List Bidder) (j n : Bidder)
    (hnext :
      greedyFirstDeniedBecauseOfFromState
        bids acceptedBeforeSuffix suffix j = some n) :
    n ∈ suffix ∧
      SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids acceptedBeforeSuffix suffix j n := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_first_denied_because_of_from_state_some_spec
      bids acceptedBeforeSuffix suffix j n hnext

/--
If the prefix-state `n(j)` search returns `n`, then no earlier bid in a
duplicate-free displayed suffix is a prefix-local denied-because-of candidate.
-/
theorem greedy_first_denied_because_of_from_state_some_no_earlier_candidate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (pre post : List Bidder) (j n m : Bidder)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      greedyFirstDeniedBecauseOfFromState
        bids acceptedBeforeSuffix (pre ++ n :: post) j = some n)
    (hm : m ∈ pre) :
    ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids acceptedBeforeSuffix (pre ++ n :: post) j m := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_first_denied_because_of_from_state_some_no_earlier_candidate
      bids acceptedBeforeSuffix pre post j n m hnodup hnext hm

/--
If the prefix-state `n(j)` search returns `n` at a displayed split, then `n`
is denied because of `j` exactly at the greedy state after processing the
displayed prefix.
-/
theorem greedy_first_denied_because_of_from_state_some_at_split
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (pre post : List Bidder) (j n : Bidder)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      greedyFirstDeniedBecauseOfFromState
        bids acceptedBeforeSuffix (pre ++ n :: post) j = some n) :
    SingleMindedGreedyDeniedBecauseOfAtState bids
      (singleMindedGreedyAcceptedFromState bids acceptedBeforeSuffix pre) j n := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_first_denied_because_of_from_state_some_at_split
      bids acceptedBeforeSuffix pre post j n hnodup hnext

/--
Critical-price progress for the `n(j) = n` case: before the first
denied-because-of candidate, erasing the blocker `j` preserves the greedy prefix
state, so the candidate `n` is accepted in the erased/lowered run.
-/
theorem greedy_next_denied_accepted_after_erasing_blocker
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder) (pre post : List Bidder) {j n : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hjpre : j ∉ pre)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      greedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: post) j = some n) :
    n ∈ singleMindedGreedyAcceptedFromState bidsLow
      (acceptedWithJ.erase j) (pre ++ n :: post) := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_accepted_after_erasing_blocker
      acceptedWithJ pre post hsame hjpre hnodup hnext

/--
Critical-price progress for the `n(j) = n` case: after erasing `j`, the
candidate `n` is accepted already at its split point.
-/
theorem greedy_next_denied_accepted_at_split_after_erasing_blocker
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder) (pre post : List Bidder) {j n : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hjpre : j ∉ pre)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      greedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: post) j = some n) :
    n ∈ singleMindedGreedyAcceptedFromState bidsLow
      (acceptedWithJ.erase j) (pre ++ [n]) := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_accepted_at_split_after_erasing_blocker
      acceptedWithJ pre post hsame hjpre hnodup hnext

/--
Fixed-order below-threshold skeleton for the `n(j) = n` case: if the
erased/lowered order places `j` after its conflicting `n(j)` blocker, then `j`
is rejected in that lowered run.
-/
theorem greedy_next_denied_rejected_after_erasing_blocker
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder)
    (pre nextPost between tail : List Bidder) {j n : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hjpre : j ∉ pre)
    (hjbetween : j ∉ between)
    (hjtail : j ∉ tail)
    (hnodup : (pre ++ n :: nextPost).Nodup)
    (hnext :
      greedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n)
    (hconflict : SingleMindedBidsConflict bidsLow j n) :
    j ∉ singleMindedGreedyAcceptedFromState bidsLow
      (acceptedWithJ.erase j) (((pre ++ [n]) ++ between) ++ j :: tail) := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_rejected_after_erasing_blocker
      acceptedWithJ pre nextPost between tail hsame hjpre hjbetween hjtail
      hnodup hnext hconflict

/--
Value-update below-threshold skeleton for the `n(j) = n` case: if the
value-lowered order places `j` after its original `n(j)` blocker, then `j` is
rejected.
-/
theorem greedy_next_denied_rejected_after_value_update
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost between tail : List Bidder) {j n : Bidder} (value : ℝ)
    (hjpre : j ∉ pre)
    (hjbetween : j ∉ between)
    (hjtail : j ∉ tail)
    (hnodup : (pre ++ n :: nextPost).Nodup)
    (hnext :
      greedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n) :
    j ∉ singleMindedGreedyAcceptedFromState
      (valueUpdate bids j value) (acceptedWithJ.erase j)
      (((pre ++ [n]) ++ between) ++ j :: tail) := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_rejected_after_value_update
      bids acceptedWithJ pre nextPost between tail value hjpre hjbetween
      hjtail hnodup hnext

/--
Above-threshold structural acceptance: if the raised run reaches `j` before any
denied-because-of candidate, then erasing `j` from the original prefix state and
rerunning accepts `j`.
-/
theorem greedy_accepts_after_erasing_blocker_of_no_candidate_prefix
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsHigh : Bidder → SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder) (pref tail : List Bidder) {j : Bidder}
    (hsame : ∀ k, k ≠ j → bidsHigh k = bids k)
    (hjdesired : (bidsHigh j).desired = (bids j).desired)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hjpref : j ∉ pref)
    (hno :
      ∀ i, i ∈ pref →
        ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState
          bids acceptedWithJ pref j i) :
    j ∈ singleMindedGreedyAcceptedFromState bidsHigh
      (acceptedWithJ.erase j) (pref ++ j :: tail) := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_accepts_after_erasing_blocker_of_no_candidate_prefix
      acceptedWithJ pref tail hsame hjdesired hjaccepted hpairwise hjpref hno

/--
Value-update above-threshold skeleton: if the value-raised run reaches `j`
before any original denied-because-of candidate, then erasing `j` from the
original accepted prefix and rerunning accepts `j`.
-/
theorem greedy_accepts_after_value_update_of_no_candidate_prefix
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder) (pref tail : List Bidder) {j : Bidder}
    (value : ℝ)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hjpref : j ∉ pref)
    (hno :
      ∀ i, i ∈ pref →
        ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState
          bids acceptedWithJ pref j i) :
    j ∈ singleMindedGreedyAcceptedFromState
      (valueUpdate bids j value) (acceptedWithJ.erase j)
      (pref ++ j :: tail) := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_accepts_after_value_update_of_no_candidate_prefix
      bids acceptedWithJ pref tail value hjaccepted hpairwise hjpref hno

/--
Finite critical-window composition for the `n(j) = n` case. Reposition
certificates for the changed sorted orders are enough to prove rejection below
the Definition 10.1 payment and acceptance above it.
-/
theorem greedy_value_update_local_critical_window
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost lowOrder highOrder : List Bidder) {j n : Bidder}
    (lowValue highValue : ℝ)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hjpre : j ∉ pre)
    (hnodup : (pre ++ n :: nextPost).Nodup)
    (hnext :
      greedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n)
    (hlow_reposition :
      lowValue < (bids j).bundleSize * (bids n).averageAmountPerGood →
        ∃ between tail,
          lowOrder = (((pre ++ [n]) ++ between) ++ j :: tail) ∧
            j ∉ between ∧ j ∉ tail)
    (hhigh_reposition :
      (bids j).bundleSize * (bids n).averageAmountPerGood < highValue →
        ∃ pref rest tail,
          pre = pref ++ rest ∧ highOrder = pref ++ j :: tail) :
    (lowValue < (bids j).bundleSize * (bids n).averageAmountPerGood →
      j ∉ singleMindedGreedyAcceptedFromState
        (valueUpdate bids j lowValue) (acceptedWithJ.erase j) lowOrder) ∧
    ((bids j).bundleSize * (bids n).averageAmountPerGood < highValue →
      j ∈ singleMindedGreedyAcceptedFromState
        (valueUpdate bids j highValue) (acceptedWithJ.erase j) highOrder) := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_value_update_local_critical_window
      bids acceptedWithJ pre nextPost lowOrder highOrder lowValue highValue
      hjaccepted hpairwise hjpre hnodup hnext hlow_reposition
      hhigh_reposition

/--
If the prefix-state `n(j)` search returns none, then no bid in the suffix is a
prefix-local denied-because-of candidate for `j`.
-/
theorem greedy_first_denied_because_of_from_state_none_no_candidate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (suffix : List Bidder) (j : Bidder)
    (hnext :
      greedyFirstDeniedBecauseOfFromState
        bids acceptedBeforeSuffix suffix j = none) :
    ∀ n, n ∈ suffix →
      ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids acceptedBeforeSuffix suffix j n := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_first_denied_because_of_from_state_none_no_candidate
      bids acceptedBeforeSuffix suffix j hnext

/--
If the split-order `n(j)` search returns `n`, then `n` occurs after `j` in the
given split and is denied because of `j` in the prefix-local sense.
-/
theorem greedy_next_denied_from_split_some_spec
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j n : Bidder)
    (hnext : greedyNextDeniedFromSplit bids pre suffix j = some n) :
    n ∈ suffix ∧
      SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
        (singleMindedGreedyAcceptedFromState bids ∅ (pre ++ [j]))
        suffix j n := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_from_split_some_spec
      bids pre suffix j n hnext

/-- Any returned split-order `n(j)` follows `j` in the supplied sorted order. -/
theorem greedy_next_denied_from_split_precedes
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j n : Bidder)
    (hnext : greedyNextDeniedFromSplit bids pre suffix j = some n) :
    SingleMindedPrecedes (pre ++ j :: suffix) j n := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_from_split_precedes
      bids pre suffix j n hnext

/--
In an average-descending order, a strict lower average prevents a bid from
preceding the higher-average bid.
-/
theorem averageAmountDescending_not_precedes_of_lt
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {order : List Bidder} {earlier later : Bidder}
    (hsorted : averageAmountDescending bids order)
    (hlt : averageAmountPerGood (bids earlier) <
      averageAmountPerGood (bids later)) :
    ¬ SingleMindedPrecedes order earlier later := by
  exact
    LOS02CombinatorialAuctions.paper_average_amount_descending_not_precedes_of_lt
      hsorted hlt

/--
In a duplicate-free average-descending order, a strict lower average gives a
displayed split with the higher-average bid before the lower-average bid, and
the lower-average bid absent from the surrounding pieces.
-/
theorem averageAmountDescending_exists_split_nodup_of_lt
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {order : List Bidder} {higher lower : Bidder}
    (hsorted : averageAmountDescending bids order)
    (hnodup : order.Nodup)
    (hhigher : higher ∈ order) (hlower : lower ∈ order)
    (hlt : averageAmountPerGood (bids lower) <
      averageAmountPerGood (bids higher)) :
    ∃ pre between tail,
      order = ((pre ++ [higher]) ++ between) ++ lower :: tail ∧
        lower ∉ pre ∧ lower ∉ between ∧ lower ∉ tail := by
  exact
    LOS02CombinatorialAuctions.paper_average_amount_descending_exists_split_nodup_of_lt
      hsorted hnodup hhigher hlower hlt

/--
In an average-descending order, a bid below `|s_j| * c(n)` must appear after
`n` whenever both bids occur in the order.
-/
theorem averageAmountDescending_precedes_of_value_lt_payment
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {order : List Bidder} {j n : Bidder}
    (hsorted : averageAmountDescending bids order)
    (hj : j ∈ order) (hn : n ∈ order) (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).value <
        (bids j).bundleSize * (bids n).averageAmountPerGood) :
    SingleMindedPrecedes order n j := by
  exact
    LOS02CombinatorialAuctions.paper_average_amount_descending_precedes_of_value_lt_payment
      hsorted hj hn hjn hj_nonempty hlt

/--
In an average-descending order, a bid above `|s_j| * c(n)` must appear before
`n` whenever both bids occur in the order.
-/
theorem averageAmountDescending_precedes_of_payment_lt_value
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {order : List Bidder} {j n : Bidder}
    (hsorted : averageAmountDescending bids order)
    (hj : j ∈ order) (hn : n ∈ order) (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).bundleSize * (bids n).averageAmountPerGood <
        (bids j).value) :
    SingleMindedPrecedes order j n := by
  exact
    LOS02CombinatorialAuctions.paper_average_amount_descending_precedes_of_payment_lt_value
      hsorted hj hn hjn hj_nonempty hlt

/--
For a value-only perturbation below `|s_j| * c(n)`, any duplicate-free
average-descending updated order places `n` before `j`.
-/
theorem averageAmountDescending_exists_split_nodup_of_valueUpdate_lt_payment
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {orderUpdated : List Bidder} {j n : Bidder} (value : ℝ)
    (hsorted : averageAmountDescending (valueUpdate bids j value) orderUpdated)
    (hnodup : orderUpdated.Nodup)
    (hj : j ∈ orderUpdated) (hn : n ∈ orderUpdated)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt : value < (bids j).bundleSize * (bids n).averageAmountPerGood) :
    ∃ pre between tail,
      orderUpdated = ((pre ++ [n]) ++ between) ++ j :: tail ∧
        j ∉ pre ∧ j ∉ between ∧ j ∉ tail := by
  exact
    LOS02CombinatorialAuctions.paper_average_amount_descending_exists_split_nodup_of_value_update_lt_payment
      value hsorted hnodup hj hn hjn hj_nonempty hlt

/--
For a value-only perturbation above `|s_j| * c(n)`, any duplicate-free
average-descending updated order places `j` before `n`.
-/
theorem averageAmountDescending_exists_split_nodup_of_payment_lt_valueUpdate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {orderUpdated : List Bidder} {j n : Bidder} (value : ℝ)
    (hsorted : averageAmountDescending (valueUpdate bids j value) orderUpdated)
    (hnodup : orderUpdated.Nodup)
    (hj : j ∈ orderUpdated) (hn : n ∈ orderUpdated)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt : (bids j).bundleSize * (bids n).averageAmountPerGood < value) :
    ∃ pre between tail,
      orderUpdated = ((pre ++ [j]) ++ between) ++ n :: tail ∧
        n ∉ pre ∧ n ∉ between ∧ n ∉ tail := by
  exact
    LOS02CombinatorialAuctions.paper_average_amount_descending_exists_split_nodup_of_payment_lt_value_update
      value hsorted hnodup hj hn hjn hj_nonempty hlt

/--
Below-threshold repositioning with explicit erase-stability of the non-`j`
order: the updated sorted order has the original `pre ++ n :: nextPost` after
erasing `j`, so `j` appears after that original `n`.
-/
theorem averageAmountDescending_exists_reposition_of_valueUpdate_lt_payment_and_erase
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {orderUpdated pre nextPost : List Bidder} {j n : Bidder} (value : ℝ)
    (hsorted : averageAmountDescending (valueUpdate bids j value) orderUpdated)
    (hnodup : orderUpdated.Nodup)
    (hj : j ∈ orderUpdated) (hn : n ∈ orderUpdated)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt : value < (bids j).bundleSize * (bids n).averageAmountPerGood)
    (herase : orderUpdated.erase j = pre ++ n :: nextPost) :
    ∃ between tail,
      orderUpdated = (((pre ++ [n]) ++ between) ++ j :: tail) ∧
        j ∉ between ∧ j ∉ tail := by
  exact
    LOS02CombinatorialAuctions.paper_average_amount_descending_exists_reposition_of_value_update_lt_payment_and_erase
      value hsorted hnodup hj hn hjn hj_nonempty hlt herase

/--
Above-threshold repositioning with explicit erase-stability of the non-`j`
order: the updated sorted order reaches `j` before the original `n(j)` point.
-/
theorem averageAmountDescending_exists_reposition_of_payment_lt_valueUpdate_and_erase
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    {orderUpdated pre nextPost : List Bidder} {j n : Bidder} (value : ℝ)
    (hsorted : averageAmountDescending (valueUpdate bids j value) orderUpdated)
    (hnodup : orderUpdated.Nodup)
    (hj : j ∈ orderUpdated) (hn : n ∈ orderUpdated)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt : (bids j).bundleSize * (bids n).averageAmountPerGood < value)
    (herase : orderUpdated.erase j = pre ++ n :: nextPost) :
    ∃ pref rest tail,
      pre = pref ++ rest ∧ orderUpdated = pref ++ j :: tail := by
  exact
    LOS02CombinatorialAuctions.paper_average_amount_descending_exists_reposition_of_payment_lt_value_update_and_erase
      value hsorted hnodup hj hn hjn hj_nonempty hlt herase

/--
Source-shaped finite critical-window endpoint for the `n(j) = n` case, assuming
the low/high value-updated sorted orders preserve the non-`j` order by erasure.
-/
theorem greedy_value_update_local_critical_window_of_sorted_erase
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost lowOrder highOrder : List Bidder) {j n : Bidder}
    (lowValue highValue : ℝ)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hjpre : j ∉ pre)
    (hnodup_original : (pre ++ n :: nextPost).Nodup)
    (hnext :
      greedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n)
    (hlow_sorted : averageAmountDescending (valueUpdate bids j lowValue) lowOrder)
    (hhigh_sorted : averageAmountDescending (valueUpdate bids j highValue) highOrder)
    (hlow_nodup : lowOrder.Nodup)
    (hhigh_nodup : highOrder.Nodup)
    (hlow_erase : lowOrder.erase j = pre ++ n :: nextPost)
    (hhigh_erase : highOrder.erase j = pre ++ n :: nextPost)
    (hj_low : j ∈ lowOrder) (hj_high : j ∈ highOrder)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty) :
    (lowValue < (bids j).bundleSize * (bids n).averageAmountPerGood →
      j ∉ singleMindedGreedyAcceptedFromState
        (valueUpdate bids j lowValue) (acceptedWithJ.erase j) lowOrder) ∧
    ((bids j).bundleSize * (bids n).averageAmountPerGood < highValue →
      j ∈ singleMindedGreedyAcceptedFromState
        (valueUpdate bids j highValue) (acceptedWithJ.erase j) highOrder) := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_value_update_local_critical_window_of_sorted_erase
      bids acceptedWithJ pre nextPost lowOrder highOrder lowValue highValue
      hjaccepted hpairwise hjpre hnodup_original hnext hlow_sorted
      hhigh_sorted hlow_nodup hhigh_nodup hlow_erase hhigh_erase
      hj_low hj_high hjn hj_nonempty

/--
Monotonicity support: if a strengthened report for `j` reaches `j` after a
prefix that had no original conflict with `j`, then the greedy run accepts `j`.
-/
theorem greedy_accepts_after_shrink_of_no_prefix_conflict
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsStrong : Bidder → SingleMindedBid Item}
    (acceptedBefore : Finset Bidder) (pref tail : List Bidder) {j : Bidder}
    (hsame : ∀ k, k ≠ j → bidsStrong k = bids k)
    (hjdesired_subset : (bidsStrong j).desired ⊆ (bids j).desired)
    (hjaccepted : j ∉ acceptedBefore)
    (hjpref : j ∉ pref)
    (hno :
      ¬ (singleMindedGreedyConflictingAccepted bids
        (singleMindedGreedyAcceptedFromState bids acceptedBefore pref)
        j).Nonempty) :
    j ∈ singleMindedGreedyAcceptedFromState bidsStrong acceptedBefore
      (pref ++ j :: tail) := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_accepts_after_shrink_of_no_prefix_conflict
      acceptedBefore pref tail hsame hjdesired_subset hjaccepted hjpref hno

/--
Monotonicity support in the source proof shape: if strengthening `j` moves it
earlier from `(pref ++ rest) ++ j :: suffix` to `pref ++ j :: tail`, and the
original run accepted `j`, then the strengthened run accepts `j`.
-/
theorem greedy_accepts_after_shrink_of_original_accepts_before_move
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsStrong : Bidder → SingleMindedBid Item}
    (acceptedBefore : Finset Bidder)
    (pref rest suffix tail : List Bidder) {j : Bidder}
    (hsame : ∀ k, k ≠ j → bidsStrong k = bids k)
    (hjdesired_subset : (bidsStrong j).desired ⊆ (bids j).desired)
    (hjaccepted : j ∉ acceptedBefore)
    (hjpref : j ∉ pref)
    (hjrest : j ∉ rest)
    (hjsuffix : j ∉ suffix)
    (hacc :
      j ∈ singleMindedGreedyAcceptedFromState bids acceptedBefore
        ((pref ++ rest) ++ j :: suffix)) :
    j ∈ singleMindedGreedyAcceptedFromState bidsStrong acceptedBefore
      (pref ++ j :: tail) := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_accepts_after_shrink_of_original_accepts_before_move
      acceptedBefore pref rest suffix tail hsame hjdesired_subset hjaccepted
      hjpref hjrest hjsuffix hacc

/--
The greedy accepted-set mechanism is monotone once the paper's sorted order rule
certifies that every accepted strengthened report moves `j` weakly earlier.
-/
theorem greedy_accepted_mechanism_monotonicity_of_order_moves_earlier
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (hmove :
      ∀ bids j s v,
        j ∈ singleMindedGreedyAcceptedFromOrder bids (orderOf bids) →
          s ⊆ (bids j).desired →
            (bids j).value ≤ v →
              ∃ pref rest suffix tail,
                orderOf bids = (pref ++ rest) ++ j :: suffix ∧
                  orderOf (Function.update bids j { desired := s, value := v }) =
                    pref ++ j :: tail ∧
                  j ∉ pref ∧ j ∉ rest ∧ j ∉ suffix) :
    (greedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf).Monotonicity := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_accepted_mechanism_monotonicity_of_order_moves_earlier
      orderOf hmove

/--
Local sorted-window package for the finite `n(j) = n` branch of the greedy
critical-price proof.
-/
abbrev sortedEraseCriticalWindow
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder) (j : Bidder)
    (base : List Bidder) (windowOrder : ℝ → List Bidder) : Prop :=
  LOS02CombinatorialAuctions.paper_sorted_erase_critical_window
    orderOf bids acceptedWithJ j base windowOrder

/--
Full-order sorted-window package for instantiating the source Section 10
critical-price branches from a split of the original greedy order around `j`.
-/
abbrev fullOrderSortedEraseCriticalWindow
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder) (j : Bidder)
    (base : List Bidder) (windowOrder : ℝ → List Bidder) :=
  LOS02CombinatorialAuctions.paper_source_sorted_erase_critical_window
    orderOf bids acceptedWithJ j base windowOrder

/--
The concrete average-order suffix window supplies the sorted/duplicate-free/
erase-stable local window fields. The remaining assumptions are the bridges
from the local suffix rerun back to the full updated greedy mechanism.
-/
theorem averageValueUpdateWindow_sortedEraseCriticalWindowOfSplit
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    {before base : List Bidder} {j : Bidder}
    (horder : averageOrderOf bids = before ++ j :: base)
    (hreject : ∀ v,
      j ∉ singleMindedGreedyAcceptedFromState
          (valueUpdate bids j v)
          (acceptedWithJ.erase j)
          (averageValueUpdateWindow bids j base v) →
        j ∉ singleMindedGreedyAcceptedFromOrder
          (valueUpdate bids j v)
          (averageOrderOf (valueUpdate bids j v)))
    (haccept : ∀ v,
      j ∈ singleMindedGreedyAcceptedFromState
          (valueUpdate bids j v)
          (acceptedWithJ.erase j)
          (averageValueUpdateWindow bids j base v) →
        j ∈ singleMindedGreedyAcceptedFromOrder
          (valueUpdate bids j v)
          (averageOrderOf (valueUpdate bids j v))) :
    sortedEraseCriticalWindow
      averageOrderOf bids acceptedWithJ j base
      (averageValueUpdateWindow bids j base) := by
  exact
    LOS02CombinatorialAuctions.paper_average_value_update_window_sorted_erase_critical_window_of_split
      bids acceptedWithJ horder hreject haccept

/--
Source-window constructor for the concrete average-order suffix window. It
packages the original split, accepted prefix, and local suffix-window facts.
-/
noncomputable def averageValueUpdateWindow_fullOrderSortedEraseCriticalWindowOfSplit
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder}
    (horder : averageOrderOf bids = before ++ j :: base)
    (hjaccepted :
      j ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j]))
    (hreject : ∀ v,
      j ∉ singleMindedGreedyAcceptedFromState
          (valueUpdate bids j v)
          ((singleMindedGreedyAcceptedFromState bids ∅
            (before ++ [j])).erase j)
          (averageValueUpdateWindow bids j base v) →
        j ∉ singleMindedGreedyAcceptedFromOrder
          (valueUpdate bids j v)
          (averageOrderOf (valueUpdate bids j v)))
    (haccept : ∀ v,
      j ∈ singleMindedGreedyAcceptedFromState
          (valueUpdate bids j v)
          ((singleMindedGreedyAcceptedFromState bids ∅
            (before ++ [j])).erase j)
          (averageValueUpdateWindow bids j base v) →
        j ∈ singleMindedGreedyAcceptedFromOrder
          (valueUpdate bids j v)
          (averageOrderOf (valueUpdate bids j v))) :
    fullOrderSortedEraseCriticalWindow
      averageOrderOf bids
      (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j]))
      j base (averageValueUpdateWindow bids j base) :=
  LOS02CombinatorialAuctions.paper_average_value_update_window_source_sorted_erase_critical_window_of_split
    bids horder hjaccepted hreject haccept

/--
Concrete average-order source-window constructor with the local-to-global bridge
discharged by the ordered-insertion suffix-window equivalence.
-/
theorem averageValueUpdateWindow_sortedEraseCriticalWindowOfSourceSplit
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder}
    (horder : averageOrderOf bids = before ++ j :: base)
    (hjaccepted :
      j ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])) :
    sortedEraseCriticalWindow
      averageOrderOf bids
      (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j]))
      j base (averageValueUpdateWindow bids j base) := by
  exact
    LOS02CombinatorialAuctions.paper_average_value_update_window_sorted_erase_critical_window_of_split_data
      bids horder hjaccepted

/--
Concrete average-order source-window package for the split around an accepted
bid `j`, with no remaining bridge assumptions.
-/
noncomputable def averageValueUpdateWindow_fullOrderSortedEraseCriticalWindowOfSourceSplit
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder}
    (horder : averageOrderOf bids = before ++ j :: base)
    (hjaccepted :
      j ∈ singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j])) :
    fullOrderSortedEraseCriticalWindow
      averageOrderOf bids
      (singleMindedGreedyAcceptedFromState bids ∅ (before ++ [j]))
      j base (averageValueUpdateWindow bids j base) :=
  LOS02CombinatorialAuctions.paper_average_value_update_window_source_sorted_erase_critical_window_of_split_data
    bids horder hjaccepted

/--
Finite accepted-branch theorem for Definition 10.1: for an accepted bid with
`n(j) = n`, a sorted erase-stable local window proves rejection below
`|s_j| * c(n)`, acceptance above it, and equality of the actual greedy payment.
-/
theorem greedy_accepted_mechanism_finite_branch_of_next_denied_some
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost : List Bidder) {j n : Bidder}
    (windowOrder : ℝ → List Bidder)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hjpre : j ∉ pre)
    (hnodup_original : (pre ++ n :: nextPost).Nodup)
    (hnext_state :
      greedyFirstDeniedBecauseOfFromState
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n)
    (hwindow :
      sortedEraseCriticalWindow orderOf bids acceptedWithJ j
        (pre ++ n :: nextPost) windowOrder)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hj_final : j ∈ singleMindedGreedyAcceptedFromOrder bids (orderOf bids))
    (hnext_order : greedyNextDeniedFromOrder bids (orderOf bids) j = some n) :
    let M := greedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf
    let p := (bids j).bundleSize * (bids n).averageAmountPerGood
    (∀ v, v < p → j ∉ M.accepted (valueUpdate bids j v)) ∧
    (∀ v, p < v → j ∈ M.accepted (valueUpdate bids j v)) ∧
    M.payment bids j = p := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_accepted_mechanism_finite_branch_of_next_denied_some
      orderOf bids acceptedWithJ pre nextPost windowOrder hjaccepted
      hpairwise hjpre hnodup_original hnext_state hwindow hjn
      hj_nonempty hj_final hnext_order

/--
No-next accepted branch for Definition 10.1 over the nonnegative value domain:
if the local `n(j)` search returns none, the zero payment is the critical
threshold. Nonnegative values below zero are impossible, while every positive
value is accepted from the erase-stable no-candidate window.
-/
theorem greedy_accepted_mechanism_zero_branch_of_next_denied_none
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (base : List Bidder) {j : Bidder}
    (windowOrder : ℝ → List Bidder)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : PairwiseDisjointDesired bids acceptedWithJ)
    (hnext_state :
      greedyFirstDeniedBecauseOfFromState bids acceptedWithJ base j = none)
    (hwindow :
      sortedEraseCriticalWindow orderOf bids acceptedWithJ j base windowOrder)
    (hj_final : j ∈ singleMindedGreedyAcceptedFromOrder bids (orderOf bids))
    (hnext_order : greedyNextDeniedFromOrder bids (orderOf bids) j = none) :
    let M := greedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf
    (∀ v, 0 ≤ v → v < 0 → j ∉ M.accepted (valueUpdate bids j v)) ∧
    (∀ v, 0 < v → j ∈ M.accepted (valueUpdate bids j v)) ∧
    M.payment bids j = 0 := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_accepted_mechanism_zero_branch_of_next_denied_none
      orderOf bids acceptedWithJ base windowOrder hjaccepted hpairwise
      hnext_state hwindow hj_final hnext_order

/--
Source-window finite branch for Definition 10.1: a full-order split around `j`
derives the local finite critical branch from the full-order `n(j)=n` search.
-/
theorem greedy_accepted_mechanism_finite_branch_of_sorted_window
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost : List Bidder) {j n : Bidder}
    (windowOrder : ℝ → List Bidder)
    (hsource :
      fullOrderSortedEraseCriticalWindow orderOf bids acceptedWithJ j
        (pre ++ n :: nextPost) windowOrder)
    (hnext_order :
      greedyNextDeniedFromOrder bids (orderOf bids) j = some n)
    (hj_nonempty : (bids j).desired.Nonempty) :
    let M := greedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf
    let p := (bids j).bundleSize * (bids n).averageAmountPerGood
    (∀ v, v < p → j ∉ M.accepted (valueUpdate bids j v)) ∧
    (∀ v, p < v → j ∈ M.accepted (valueUpdate bids j v)) ∧
    M.payment bids j = p := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_accepted_mechanism_finite_branch_of_sorted_window
      orderOf bids acceptedWithJ pre nextPost windowOrder hsource
      hnext_order hj_nonempty

/--
Source-window zero branch for Definition 10.1: a full-order split around `j`
with no next denied bid gives zero payment and acceptance at every positive
value over the nonnegative value domain.
-/
theorem greedy_accepted_mechanism_zero_branch_of_sorted_window
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (base : List Bidder) {j : Bidder}
    (windowOrder : ℝ → List Bidder)
    (hsource :
      fullOrderSortedEraseCriticalWindow orderOf bids acceptedWithJ j
        base windowOrder)
    (hnext_order :
      greedyNextDeniedFromOrder bids (orderOf bids) j = none) :
    let M := greedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf
    (∀ v, 0 ≤ v → v < 0 → j ∉ M.accepted (valueUpdate bids j v)) ∧
    (∀ v, 0 < v → j ∈ M.accepted (valueUpdate bids j v)) ∧
    M.payment bids j = 0 := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_accepted_mechanism_zero_branch_of_sorted_window
      orderOf bids acceptedWithJ base windowOrder hsource hnext_order

/--
Source-window data for the accepted-bid critical branch of Definition 10.1. It
provides the full-order sorted-window package for whichever case the `n(j)`
search returns.
-/
abbrev sourceCriticalBranchWindows
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) :=
  LOS02CombinatorialAuctions.paper_source_critical_branch_windows
    orderOf bids j

/--
For any bidder accepted by the concrete average-order greedy run, the average
order supplies source critical-branch windows for the finite and no-next cases.
-/
noncomputable def averageCriticalBranchWindowsOfAccepted
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) {j : Bidder}
    (hjacc :
      j ∈ singleMindedGreedyAcceptedFromOrder bids (averageOrderOf bids)) :
    sourceCriticalBranchWindows averageOrderOf bids j :=
  LOS02CombinatorialAuctions.paper_average_source_critical_branch_windows_of_accepted
    bids hjacc

/--
Source branch data sufficient to build the nonnegative-domain critical-value
certificate for the LOS02 greedy accepted-set mechanism.
-/
abbrev nonnegativeCriticalBranchData
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder) :=
  LOS02CombinatorialAuctions.paper_nonnegative_critical_source_branch_data
    orderOf

/--
Accepted-bid criticality for the full greedy mechanism: the actual Definition
10.1 payment is the critical threshold for changing only the accepted bidder's
value on the nonnegative report domain, assuming source windows for the finite
and no-next branches.
-/
theorem greedy_accepted_mechanism_payment_critical_of_branch_windows
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (bids : Bidder → SingleMindedBid Item) {j : Bidder}
    (hwindows : sourceCriticalBranchWindows orderOf bids j)
    (hj_nonempty : (bids j).desired.Nonempty) :
    let M := greedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf
    (∀ v, 0 ≤ v → v < M.payment bids j →
      j ∉ M.accepted (valueUpdate bids j v)) ∧
    (∀ v, M.payment bids j < v →
      j ∈ M.accepted (valueUpdate bids j v)) := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_accepted_mechanism_payment_critical_of_branch_windows
      orderOf bids hwindows hj_nonempty

/--
Concrete average-order accepted-bid criticality: if `j` is accepted by the
average-order greedy run, its Definition 10.1 payment is the critical threshold
for value-only deviations on the nonnegative domain.
-/
theorem averageGreedy_acceptedPaymentCriticalOfAccepted
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) {j : Bidder}
    (hjacc : j ∈ singleMindedGreedyAcceptedFromOrder bids (averageOrderOf bids))
    (hj_nonempty : (bids j).desired.Nonempty) :
    let M := averageGreedyAcceptedMechanism
      (Bidder := Bidder) (Item := Item)
    (∀ v, 0 ≤ v → v < M.payment bids j →
      j ∉ M.accepted (valueUpdate bids j v)) ∧
    (∀ v, M.payment bids j < v →
      j ∈ M.accepted (valueUpdate bids j v)) := by
  exact
    LOS02CombinatorialAuctions.paper_average_greedy_accepted_mechanism_payment_critical_of_accepted
      bids hjacc hj_nonempty

/--
Candidate all-bidder critical threshold for the concrete average-order greedy
mechanism, selecting an accepted nonnegative value-only branch when one exists.
-/
noncomputable abbrev averageGreedyCriticalThreshold
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (reports : Bidder → SingleMindedBid Item) (i : Bidder)
    (s : Bundle Item) : Option ℝ :=
  LOS02CombinatorialAuctions.paper_average_greedy_critical_threshold
    reports i s

/--
If the candidate threshold has no accepted nonnegative value-only branch, every
nonnegative value-only report for the target bundle is denied.
-/
theorem averageGreedyCriticalThreshold_noneDenied
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (reports : Bidder → SingleMindedBid Item) (i : Bidder)
    (s : Bundle Item)
    (hthreshold : averageGreedyCriticalThreshold reports i s = none) :
    ∀ v, 0 ≤ v →
      i ∉ (averageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item)).accepted
          (Function.update reports i { desired := s, value := v }) := by
  exact
    LOS02CombinatorialAuctions.paper_average_greedy_critical_threshold_none_denied
      reports i s hthreshold

/--
Finite values returned by the candidate threshold carry the source branch data
needed by the nonnegative critical-value certificate.
-/
noncomputable def averageGreedyCriticalThreshold_someBranch
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (reports : Bidder → SingleMindedBid Item)
    (hreports :
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile reports)
    (i : Bidder) (s : Bundle Item) (p : ℝ)
    (hs : s.Nonempty)
    (hthreshold : averageGreedyCriticalThreshold reports i s = some p) :
    AppliedModelingLib.Auction.SingleMindedSomeThresholdBranch
      averageOrderOf reports i s p :=
  LOS02CombinatorialAuctions.paper_average_greedy_critical_threshold_some_branch
    reports hreports i s p hs hthreshold

/--
Build the Theorem 10.2 nonnegative-domain critical-value certificate from the
source branch data. This is the paper-facing assembly point after the concrete
sorted-order branch data have been supplied.
-/
noncomputable def greedy_nonnegativeCriticalCertificateOfSourceBranchData
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (data : nonnegativeCriticalBranchData orderOf) :
    (greedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item)
      orderOf).NonnegativeCriticalValueWithInfinityCertificate :=
  LOS02CombinatorialAuctions.paper_greedy_nonnegative_critical_certificate_of_branch_data
    orderOf data

/--
Concrete average-order assembly point for the Theorem 10.2
nonnegative-domain critical-value certificate.
-/
noncomputable def averageGreedy_nonnegativeCriticalCertificateOfSourceBranchData
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (data :
      nonnegativeCriticalBranchData
        (averageOrderOf (Bidder := Bidder) (Item := Item))) :
    SingleMindedAcceptedMechanism.NonnegativeCriticalValueWithInfinityCertificate
      (averageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item)) :=
  LOS02CombinatorialAuctions.paper_average_greedy_nonnegative_critical_certificate_of_branch_data
    (Bidder := Bidder) (Item := Item) data

/--
Concrete source-branch data for the average-order greedy mechanism on the
nonempty nonnegative single-minded domain.
-/
noncomputable def averageGreedyNonnegativeCriticalBranchData
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder] :
    nonnegativeCriticalBranchData
      (averageOrderOf (Bidder := Bidder) (Item := Item)) :=
  LOS02CombinatorialAuctions.paper_average_greedy_nonnegative_critical_source_branch_data
    (Bidder := Bidder) (Item := Item)

/--
Concrete nonnegative-domain critical-value certificate for the average-order
greedy accepted-set/payment mechanism.
-/
noncomputable def averageGreedyNonnegativeCriticalCertificate
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder] :
    SingleMindedAcceptedMechanism.NonnegativeCriticalValueWithInfinityCertificate
      (averageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item)) :=
  LOS02CombinatorialAuctions.paper_average_greedy_nonnegative_critical_certificate
    (Bidder := Bidder) (Item := Item)

/--
Source-shaped below-threshold rejection bridge: in an average-descending order,
if `j` is below `|s_j| * c(n)`, `n` is accepted before `j`, and `n` conflicts
with `j`, then `j` is rejected.
-/
theorem greedy_rejected_of_average_threshold_and_prefix_accept
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → SingleMindedBid Item}
    (acceptedBefore : Finset Bidder) (order : List Bidder) {j n : Bidder}
    (hsorted : averageAmountDescending bids order)
    (hnodup : order.Nodup)
    (hjorder : j ∈ order) (hnorder : n ∈ order)
    (hjn : j ≠ n)
    (hjaccepted : j ∉ acceptedBefore)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).value <
        (bids j).bundleSize * (bids n).averageAmountPerGood)
    (hprefix_accept :
      ∀ pre between tail,
        order = ((pre ++ [n]) ++ between) ++ j :: tail →
          n ∈ singleMindedGreedyAcceptedFromState
            bids acceptedBefore ((pre ++ [n]) ++ between))
    (hconflict : SingleMindedBidsConflict bids j n) :
    j ∉ singleMindedGreedyAcceptedFromState bids acceptedBefore order := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_rejected_of_average_threshold_and_prefix_accept
      acceptedBefore order hsorted hnodup hjorder hnorder hjn hjaccepted
      hj_nonempty hlt hprefix_accept hconflict

/--
If the full-order `n(j)` search returns `n`, then `n` satisfies the full-order
denied-because-of relation after the first occurrence of `j`.
-/
theorem greedy_next_denied_from_order_some_spec
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (j n : Bidder)
    (hnext : greedyNextDeniedFromOrder bids order j = some n) :
    greedyDeniedBecauseOfAfterInOrder bids order j n := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_from_order_some_spec
      bids order j n hnext

/--
If the full-order `n(j)` search returns none, then no full-order
denied-because-of candidate exists after the first occurrence of `j`.
-/
theorem greedy_next_denied_from_order_none_no_candidate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (j : Bidder)
    (hnext : greedyNextDeniedFromOrder bids order j = none) :
    ∀ n, ¬ greedyDeniedBecauseOfAfterInOrder bids order j n := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_from_order_none_no_candidate
      bids order j hnext

/--
The full-order `n(j)` search agrees with the split-order search at the first
occurrence split of `j`.
-/
theorem greedy_next_denied_from_order_eq_split
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j : Bidder)
    (hpre : j ∉ pre) :
    greedyNextDeniedFromOrder bids (pre ++ j :: suffix) j =
      greedyNextDeniedFromSplit bids pre suffix j := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_from_order_eq_split
      bids pre suffix j hpre

/--
For a duplicate-free order, the full-order `n(j)` search agrees with any
displayed split around `j`.
-/
theorem greedy_next_denied_from_order_eq_split_of_nodup
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    {order pre suffix : List Bidder} {j : Bidder}
    (horder : order = pre ++ j :: suffix)
    (hnodup : order.Nodup) :
    greedyNextDeniedFromOrder bids order j =
      greedyNextDeniedFromSplit bids pre suffix j := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_from_order_eq_split_of_nodup
      bids horder hnodup

/--
If the full-order `n(j)` search returns `n` at a first occurrence split, then
`n` is in the suffix and satisfies the prefix-local denied-because-of condition.
-/
theorem greedy_next_denied_from_order_some_spec_of_split
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j n : Bidder)
    (hpre : j ∉ pre)
    (hnext : greedyNextDeniedFromOrder bids (pre ++ j :: suffix) j = some n) :
    n ∈ suffix ∧
      SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
        (singleMindedGreedyAcceptedFromState bids ∅ (pre ++ [j]))
        suffix j n := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_from_order_some_spec_of_split
      bids pre suffix j n hpre hnext

/--
If the full-order `n(j)` search returns none at a first occurrence split, then
no later bid in that suffix is denied because of `j`.
-/
theorem greedy_next_denied_from_order_none_no_candidate_of_split
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j : Bidder)
    (hpre : j ∉ pre)
    (hnext : greedyNextDeniedFromOrder bids (pre ++ j :: suffix) j = none) :
    ∀ n, n ∈ suffix →
      ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
        (singleMindedGreedyAcceptedFromState bids ∅ (pre ++ [j]))
        suffix j n := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_from_order_none_no_candidate_of_split
      bids pre suffix j hpre hnext

/-- Any returned full-order `n(j)` follows `j` in the supplied sorted order. -/
theorem greedy_next_denied_from_order_precedes_of_split
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j n : Bidder)
    (hpre : j ∉ pre)
    (hnext : greedyNextDeniedFromOrder bids (pre ++ j :: suffix) j = some n) :
    SingleMindedPrecedes (pre ++ j :: suffix) j n := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_from_order_precedes_of_split
      bids pre suffix j n hpre hnext

/--
If the split-order `n(j)` search returns none, then no later bid in that suffix
is denied because of `j` in the prefix-local sense.
-/
theorem greedy_next_denied_from_split_none_no_candidate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (pre suffix : List Bidder) (j : Bidder)
    (hnext : greedyNextDeniedFromSplit bids pre suffix j = none) :
    ∀ n, n ∈ suffix →
      ¬ SingleMindedGreedyDeniedBecauseOfInSuffixFromState bids
        (singleMindedGreedyAcceptedFromState bids ∅ (pre ++ [j]))
        suffix j n := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_next_denied_from_split_none_no_candidate
      bids pre suffix j hnext

/-- Denied bids pay zero under the full-order greedy payment rule. -/
theorem greedy_payment_from_order_eq_zero_of_denied
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) {j : Bidder}
    (hj : j ∉ greedyAcceptedFromOrder bids order) :
    greedyPaymentFromOrder bids order j = 0 := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_payment_from_order_eq_zero_of_denied
      bids order hj

/-- Granted bids with no full-order `n(j)` pay zero. -/
theorem greedy_payment_from_order_eq_zero_of_no_next
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) {j : Bidder}
    (hj : j ∈ greedyAcceptedFromOrder bids order)
    (hnext : greedyNextDeniedFromOrder bids order j = none) :
    greedyPaymentFromOrder bids order j = 0 := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_payment_from_order_eq_zero_of_no_next
      bids order hj hnext

/-- If full-order `n(j)` exists, the greedy payment is `|s_j| * c(n(j))`. -/
theorem greedy_payment_from_order_eq_of_next
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) {j n : Bidder}
    (hj : j ∈ greedyAcceptedFromOrder bids order)
    (hnext : greedyNextDeniedFromOrder bids order j = some n) :
    greedyPaymentFromOrder bids order j =
      (bids j).bundleSize * (bids n).averageAmountPerGood := by
  exact
    LOS02CombinatorialAuctions.paper_greedy_payment_from_order_eq_of_next
      bids order hj hnext

/-- Denied bids pay zero under the concrete average-order greedy payment rule. -/
theorem averageGreedyPayment_eq_zero_of_denied
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) {j : Bidder}
    (hj : j ∉ averageGreedyAcceptedSet bids) :
    averageGreedyPayment bids j = 0 := by
  exact
    LOS02CombinatorialAuctions.paper_average_greedy_payment_eq_zero_of_denied
      bids hj

/-- Granted bids with no `n(j)` pay zero under the concrete average-order rule. -/
theorem averageGreedyPayment_eq_zero_of_no_next
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) {j : Bidder}
    (hj : j ∈ averageGreedyAcceptedSet bids)
    (hnext : greedyNextDeniedFromOrder bids (averageOrderOf bids) j = none) :
    averageGreedyPayment bids j = 0 := by
  exact
    LOS02CombinatorialAuctions.paper_average_greedy_payment_eq_zero_of_no_next
      bids hj hnext

/-- If concrete average-order `n(j)` exists, the payment is `|s_j| * c(n(j))`. -/
theorem averageGreedyPayment_eq_of_next
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) {j n : Bidder}
    (hj : j ∈ averageGreedyAcceptedSet bids)
    (hnext : greedyNextDeniedFromOrder bids (averageOrderOf bids) j = some n) :
    averageGreedyPayment bids j =
      (bids j).bundleSize * (bids n).averageAmountPerGood := by
  exact
    LOS02CombinatorialAuctions.paper_average_greedy_payment_eq_of_next
      bids hj hnext

/-- The greedy accepted-set mechanism satisfies Participation. -/
theorem greedy_accepted_mechanism_participation
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder) :
    (greedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf).Participation := by
  exact
    LOS02CombinatorialAuctions.paper_single_minded_greedy_accepted_mechanism_participation
      orderOf

/--
The concrete average-order greedy accepted-set rule is monotone on the
nonempty nonnegative single-minded domain.
-/
theorem averageGreedyAcceptedMechanism_nonnegativeMonotonicity
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder] :
    (averageGreedyAcceptedMechanism
      (Bidder := Bidder) (Item := Item)).MonotonicityOn
        nonnegativeNonemptySingleMindedProfile := by
  exact
    LOS02CombinatorialAuctions.paper_average_greedy_accepted_mechanism_nonnegative_monotonicity
      (Bidder := Bidder) (Item := Item)

/--
Theorem 10.2, source-shaped accepted-set certificate form. The full-order
Definition 10.1 payments already satisfy Participation; the remaining obligations
are Monotonicity and the finite-or-infinite critical-value certificate.
-/
theorem theorem10_2_greedy_truthful_of_infinity_certificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (hmono :
      (greedyAcceptedMechanismFromOrderOf
        (Bidder := Bidder) (Item := Item) orderOf).Monotonicity)
    (C :
      (greedyAcceptedMechanismFromOrderOf
        (Bidder := Bidder) (Item := Item)
        orderOf).CriticalValueWithInfinityCertificate) :
    singleMindedTruthfulOn
      (greedyAcceptedMechanismFromOrderOf
        (Bidder := Bidder) (Item := Item) orderOf)
      nonnegativeNonemptySingleMindedProfile := by
  exact
    LOS02CombinatorialAuctions.paper_theorem10_2_greedy_truthful_of_infinity_certificate
      orderOf hmono C

/--
Theorem 10.2, domain-aware accepted-set certificate form: the greedy mechanism is
truthful on nonempty, nonnegative single-minded profiles once monotonicity and
the nonnegative-domain critical-value certificate are supplied.
-/
theorem theorem10_2_greedy_truthful_of_nonnegative_infinity_certificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf : (Bidder → SingleMindedBid Item) → List Bidder)
    (hmono :
      (greedyAcceptedMechanismFromOrderOf
        (Bidder := Bidder) (Item := Item) orderOf).MonotonicityOn
          nonnegativeNonemptySingleMindedProfile)
    (C :
      (greedyAcceptedMechanismFromOrderOf
        (Bidder := Bidder) (Item := Item)
        orderOf).NonnegativeCriticalValueWithInfinityCertificate) :
    singleMindedTruthfulOn
      (greedyAcceptedMechanismFromOrderOf
        (Bidder := Bidder) (Item := Item) orderOf)
      nonnegativeNonemptySingleMindedProfile := by
  exact
    LOS02CombinatorialAuctions.paper_theorem10_2_greedy_truthful_of_nonnegative_infinity_certificate
      orderOf hmono C

/--
Theorem 10.2 specialized to the concrete average-order greedy mechanism. Once
monotonicity and the concrete source branch data are supplied, truthfulness on
the nonempty nonnegative single-minded domain follows.
-/
theorem theorem10_2_averageGreedy_truthful_of_nonnegative_sourceBranchData
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (hmono :
      (averageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item)).MonotonicityOn
          nonnegativeNonemptySingleMindedProfile)
    (data :
      nonnegativeCriticalBranchData
        (averageOrderOf (Bidder := Bidder) (Item := Item))) :
    singleMindedTruthfulOn
      (averageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item))
      nonnegativeNonemptySingleMindedProfile := by
  exact
    LOS02CombinatorialAuctions.paper_theorem10_2_average_greedy_truthful_of_nonnegative_source_branch_data
      (Bidder := Bidder) (Item := Item) hmono data

/--
Theorem 10.2 specialized to the concrete average-order critical-value
certificate. The remaining hypothesis is monotonicity of the concrete
average-order greedy accepted-set rule.
-/
theorem theorem10_2_averageGreedy_truthful_of_monotonicity
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (hmono :
      (averageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item)).Monotonicity) :
    singleMindedTruthfulOn
      (averageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item))
      nonnegativeNonemptySingleMindedProfile := by
  exact
    LOS02CombinatorialAuctions.paper_theorem10_2_average_greedy_truthful_of_monotonicity
      (Bidder := Bidder) (Item := Item) hmono

/--
LOS02 Theorem 10.2 for the concrete average-order greedy
accepted-set/payment mechanism on nonempty nonnegative single-minded profiles.
-/
theorem theorem10_2_averageGreedy_truthful
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder] :
    singleMindedTruthfulOn
      (averageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item))
      nonnegativeNonemptySingleMindedProfile := by
  exact
    LOS02CombinatorialAuctions.paper_theorem10_2_average_greedy_truthful
      (Bidder := Bidder) (Item := Item)

/--
Theorem 10.2, fixed-target critical-price certificate form. A greedy
allocation/payment implementation with Definition 10.1 payments is truthful on
nonempty single-minded profiles once its prices are own-report independent.
-/
theorem theorem10_2_greedy_threshold_truthful_of_certificate
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item]
    (target : Bidder → Bundle Item)
    (orderOf : CombinatorialReport Bidder Item → List Bidder)
    (nextDenied : CombinatorialReport Bidder Item → Bidder → Option Bidder)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (C :
      LOS02CombinatorialAuctions.GreedyCriticalPriceCertificate
        target orderOf nextDenied price) :
    truthfulOn (targetBundleThresholdAuction target price)
      IsNonemptySingleMindedProfile := by
  exact
    LOS02CombinatorialAuctions.paper_theorem10_2_greedy_threshold_truthful_of_certificate
      target orderOf nextDenied price C

/--
Theorem 10.2, full-order Definition 10.1 payment certificate form. This is the
same fixed-target critical-price endpoint, specialized to the full-order greedy
payment rule.
-/
theorem theorem10_2_greedy_threshold_truthful_of_full_order_payment_certificate
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item]
    (target : Bidder → Bundle Item)
    (orderOf : CombinatorialReport Bidder Item → List Bidder)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind : BundlePriceOwnReportIndependent price)
    (haccepted : ∀ reports,
      targetBundleWinners target price reports =
        singleMindedGreedyAcceptedFromOrder
          (targetAsSingleMindedBids target reports) (orderOf reports))
    (hprice : ∀ reports j,
      price reports j =
        singleMindedGreedyPaymentFromOrder
          (targetAsSingleMindedBids target reports) (orderOf reports) j) :
    truthfulOn (targetBundleThresholdAuction target price)
      IsNonemptySingleMindedProfile := by
  exact
    LOS02CombinatorialAuctions.paper_theorem10_2_greedy_threshold_truthful_of_full_order_payment_certificate
      target orderOf price hind haccepted hprice

/--
Theorem 7.2 source proof step: a rejected bid in the sorted greedy order has an
earlier accepted conflicting blocker whose square-root norm is weakly larger.
-/
theorem theorem7_2_rejected_bid_has_preceding_sqrt_blocker
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (order : List Bidder) (i : Bidder)
    (hsorted : SingleMindedSqrtNormDescending bids order)
    (hi_order : i ∈ order)
    (hnot_final : i ∉ greedyAcceptedFromOrder bids order) :
    ∃ j, ∃ g,
      j ∈ greedyAcceptedFromOrder bids order ∧
        SingleMindedPrecedes order j i ∧
          g ∈ (bids i).desired ∧
            g ∈ (bids j).desired ∧
              (bids i).sqrtAmountNorm ≤ (bids j).sqrtAmountNorm := by
  exact
    LOS02CombinatorialAuctions.paper_theorem7_2_rejected_bid_has_preceding_sqrt_blocker
      bids order i hsorted hi_order hnot_final

/--
Theorem 7.2 source proof step: when the optimal and greedy sets are disjoint,
the preceding-blocker lemma packages into the order-level blocking certificate.
-/
noncomputable def theorem7_2_order_blocking_certificate_of_disjoint
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    [Inhabited Bidder] [Inhabited Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal : Finset Bidder) (order : List Bidder)
    (hsorted : SingleMindedSqrtNormDescending bids order)
    (hoptimal_order : ∀ i, i ∈ optimal → i ∈ order)
    (hoptimal_greedy_disjoint :
      Disjoint optimal (greedyAcceptedFromOrder bids order)) :
    SingleMindedGreedyOrderBlockingCertificate bids optimal
      (greedyAcceptedFromOrder bids order) order :=
  LOS02CombinatorialAuctions.paper_theorem7_2_order_blocking_certificate_of_disjoint
    bids optimal order hsorted hoptimal_order hoptimal_greedy_disjoint

/--
Theorem 7.2 counting step: a source-shaped blocking certificate implies the
paper's square-root-norm-squared bound.
-/
theorem theorem7_2_blocking_certificate_normsq_bound
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hgreedy_nonempty : ∀ j, j ∈ greedy → (bids j).desired.Nonempty)
    (C : SingleMindedGreedyBlockingCertificate bids optimal greedy) :
    singleMindedSqrtNormSqSum bids optimal ≤
      ∑ j ∈ greedy, (bids j).value ^ 2 := by
  exact
    LOS02CombinatorialAuctions.paper_theorem7_2_blocking_certificate_normsq_bound
      bids optimal greedy hoptimal_disjoint hgreedy_nonempty C

/--
Theorem 7.2, algebraic certificate form: if the square-root-norm greedy
execution supplies the paper's blocking inequality, the optimal single-minded
allocation value is at most `sqrt(k)` times the greedy value, where `k` is the
number of goods.
-/
theorem theorem7_2_sqrt_norm_approx_of_blocking_bound
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (goods : Finset Item)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg : ∀ i, i ∈ greedy → 0 ≤ (bids i).value)
    (hblocking :
      singleMindedSqrtNormSqSum bids optimal ≤
        ∑ j ∈ greedy, (bids j).value ^ 2) :
    singleMindedTotalValue bids optimal ≤
      Real.sqrt (goods.card : ℝ) * singleMindedTotalValue bids greedy := by
  exact
    LOS02CombinatorialAuctions.paper_theorem7_2_sqrt_norm_approx_of_blocking_bound
      bids optimal greedy goods hoptimal_goods hoptimal_disjoint
      hoptimal_nonempty hoptimal_value_nonneg hgreedy_value_nonneg hblocking

/--
Theorem 7.2, source-shaped certificate form: if every optimal bid is associated
with a conflicting greedy bid and blocked good, the optimal single-minded
allocation value is at most `sqrt(k)` times the greedy value.
-/
theorem theorem7_2_sqrt_norm_approx_of_blocking_certificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (goods : Finset Item)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty : ∀ i, i ∈ greedy → (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg : ∀ i, i ∈ greedy → 0 ≤ (bids i).value)
    (C : SingleMindedGreedyBlockingCertificate bids optimal greedy) :
    singleMindedTotalValue bids optimal ≤
      Real.sqrt (goods.card : ℝ) * singleMindedTotalValue bids greedy := by
  exact
    LOS02CombinatorialAuctions.paper_theorem7_2_sqrt_norm_approx_of_blocking_certificate
      bids optimal greedy goods hoptimal_goods hoptimal_disjoint
      hoptimal_nonempty hgreedy_nonempty hoptimal_value_nonneg
      hgreedy_value_nonneg C

/--
Theorem 7.2, source-order certificate form: if every optimal bid has an earlier
conflicting greedy blocker with weakly larger square-root norm, then greedy is a
`sqrt(k)` approximation.
-/
theorem theorem7_2_sqrt_norm_approx_of_order_blocking_certificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (goods : Finset Item) (order : List Bidder)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty : ∀ i, i ∈ greedy → (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg : ∀ i, i ∈ greedy → 0 ≤ (bids i).value)
    (C :
      SingleMindedGreedyOrderBlockingCertificate
        bids optimal greedy order) :
    singleMindedTotalValue bids optimal ≤
      Real.sqrt (goods.card : ℝ) * singleMindedTotalValue bids greedy := by
  exact
    LOS02CombinatorialAuctions.paper_theorem7_2_sqrt_norm_approx_of_order_blocking_certificate
      bids optimal greedy goods order hoptimal_goods hoptimal_disjoint
      hoptimal_nonempty hgreedy_nonempty hoptimal_value_nonneg
      hgreedy_value_nonneg C

/--
Theorem 7.2, common-bid removal bridge: the source proof may remove bids common
to optimal and greedy before proving the approximation bound. This theorem
lifts the reduced bound back to the original optimal and greedy allocations.
-/
theorem theorem7_2_common_bid_removal_bridge
    {Bidder Item : Type*} [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (factor : ℝ)
    (hfactor : 1 ≤ factor)
    (hcommon_nonneg : ∀ i, i ∈ optimal ∩ greedy → 0 ≤ (bids i).value)
    (hreduced :
      singleMindedTotalValue bids (optimal \ greedy) ≤
        factor * singleMindedTotalValue bids (greedy \ optimal)) :
    singleMindedTotalValue bids optimal ≤
      factor * singleMindedTotalValue bids greedy := by
  exact
    LOS02CombinatorialAuctions.paper_theorem7_2_common_bid_removal_bridge
      bids optimal greedy factor hfactor hcommon_nonneg hreduced

/--
Theorem 7.2, disjoint sorted-greedy case: after removing common greedy/optimal
bids as in the source proof, the square-root-norm greedy allocation is a
`sqrt(k)` approximation.
-/
theorem theorem7_2_sqrt_norm_approx_of_sorted_order_disjoint
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    [Inhabited Bidder] [Inhabited Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal : Finset Bidder) (goods : Finset Item) (order : List Bidder)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty :
      ∀ i, i ∈ greedyAcceptedFromOrder bids order →
        (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg :
      ∀ i, i ∈ greedyAcceptedFromOrder bids order → 0 ≤ (bids i).value)
    (hsorted : SingleMindedSqrtNormDescending bids order)
    (hoptimal_order : ∀ i, i ∈ optimal → i ∈ order)
    (hoptimal_greedy_disjoint :
      Disjoint optimal (greedyAcceptedFromOrder bids order)) :
    singleMindedTotalValue bids optimal ≤
      Real.sqrt (goods.card : ℝ) *
        singleMindedTotalValue bids (greedyAcceptedFromOrder bids order) := by
  exact
    LOS02CombinatorialAuctions.paper_theorem7_2_sqrt_norm_approx_of_sorted_order_disjoint
      bids optimal goods order hoptimal_goods hoptimal_disjoint
      hoptimal_nonempty hgreedy_nonempty hoptimal_value_nonneg
      hgreedy_value_nonneg hsorted hoptimal_order hoptimal_greedy_disjoint

/--
Theorem 7.2 for the explicit sorted greedy run. This endpoint includes the
source common-bid removal step by filtering away bids that touch goods requested
by bids common to the optimal and greedy accepted sets.
-/
theorem theorem7_2_sqrt_norm_approx_of_sorted_order
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    [Inhabited Bidder] [Inhabited Item]
    (bids : Bidder → SingleMindedBid Item)
    (optimal : Finset Bidder) (goods : Finset Item) (order : List Bidder)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty :
      ∀ i, i ∈ greedyAcceptedFromOrder bids order →
        (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg :
      ∀ i, i ∈ greedyAcceptedFromOrder bids order → 0 ≤ (bids i).value)
    (hsorted : SingleMindedSqrtNormDescending bids order)
    (hoptimal_order : ∀ i, i ∈ optimal → i ∈ order) :
    singleMindedTotalValue bids optimal ≤
      Real.sqrt (goods.card : ℝ) *
        singleMindedTotalValue bids (greedyAcceptedFromOrder bids order) := by
  exact
    LOS02CombinatorialAuctions.paper_theorem7_2_sqrt_norm_approx_of_sorted_order
      bids optimal goods order hoptimal_goods hoptimal_disjoint
      hoptimal_nonempty hgreedy_nonempty hoptimal_value_nonneg
      hgreedy_value_nonneg hsorted hoptimal_order

end ProofInterface
end LOS02CombinatorialAuctions
