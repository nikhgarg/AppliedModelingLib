import AppliedModelingLib.Algorithms.Complexity.Classes
import AppliedModelingLib.MechanismDesign.Auctions.Combinatorial

/-!
# Paper-Facing Theorems: Truth Revelation in Approximately Efficient Combinatorial Auctions

This folder owns the Lehmann-O'Callaghan-Shoham 2002 combinatorial-auction
track. The closed Lean statements currently live in the reusable auction
library; this file re-exports only the combinatorial-auction surface under the
citation-specific namespace.
-/

namespace LOS02CombinatorialAuctions

/--
The reject-all direct combinatorial auction is dominant-strategy truthful.
-/
theorem paper_combinatorial_reject_all_truthful
    {Bidder Item : Type*} [DecidableEq Bidder] :
    (AppliedModelingLib.Auction.rejectAllAuction :
      AppliedModelingLib.Auction.CombinatorialAuction Bidder Item).TruthfulDominantStrategy := by
  exact AppliedModelingLib.Auction.rejectAllAuction_truthful

/--
The reject-all direct combinatorial auction has no positive transfers.
-/
theorem paper_combinatorial_reject_all_no_positive_transfers
    {Bidder Item : Type*} :
    (AppliedModelingLib.Auction.rejectAllAuction :
      AppliedModelingLib.Auction.CombinatorialAuction Bidder Item).NoPositiveTransfers := by
  exact AppliedModelingLib.Auction.rejectAllAuction_noPositiveTransfers

/-- Paper Definition: Utility in a Combinatorial Auction.
    $u_i(v_i, b) = v_i(A_i(b)) - p_i(b)$
-/
def paper_combinatorial_utility {Bidder Item : Type*}
    (M : AppliedModelingLib.Auction.CombinatorialAuction Bidder Item)
    (values reports : AppliedModelingLib.Auction.CombinatorialReport Bidder Item)
    (i : Bidder) : ℝ :=
  values i (M.allocation reports i) - M.payment reports i

theorem paper_combinatorial_utility_eq {Bidder Item : Type*}
    (M : AppliedModelingLib.Auction.CombinatorialAuction Bidder Item)
    (values reports : AppliedModelingLib.Auction.CombinatorialReport Bidder Item)
    (i : Bidder) :
    paper_combinatorial_utility M values reports i =
      M.utility values reports i := by
  rfl

/-- Paper Definition: Dominant Strategy Truthful on admissible domain.
    $v_i(A_i(v_i, b_{-i})) - p_i(v_i, b_{-i}) \ge v_i(A_i(b_i, b_{-i})) - p_i(b_i, b_{-i})$
-/
def paper_combinatorial_truthful_on {Bidder Item : Type*}
    [DecidableEq Bidder]
    (M : AppliedModelingLib.Auction.CombinatorialAuction Bidder Item)
    (admissible : AppliedModelingLib.Auction.CombinatorialReport Bidder Item → Prop) :
    Prop :=
  ∀ (values : AppliedModelingLib.Auction.CombinatorialReport Bidder Item),
    admissible values →
      ∀ (i : Bidder) (report : AppliedModelingLib.Auction.Bundle Item → ℝ),
        paper_combinatorial_utility M values
            (Function.update values i report) i ≤
          paper_combinatorial_utility M values values i

theorem paper_combinatorial_truthful_on_eq {Bidder Item : Type*}
    [DecidableEq Bidder]
    (M : AppliedModelingLib.Auction.CombinatorialAuction Bidder Item)
    (admissible : AppliedModelingLib.Auction.CombinatorialReport Bidder Item → Prop) :
    paper_combinatorial_truthful_on M admissible ↔
      M.TruthfulDominantStrategyOn admissible := by
  rfl

/--
Target-bundle critical-price mechanisms are truthful on normalized bundle
valuations when each bidder's offered price is independent of that bidder's own
report.
-/
theorem paper_combinatorial_target_bundle_threshold_truthful_on_normalized
    {Bidder Item : Type*} [DecidableEq Bidder]
    (target : Bidder → AppliedModelingLib.Auction.Bundle Item)
    (price :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind : AppliedModelingLib.Auction.BundlePriceOwnReportIndependent price) :
    paper_combinatorial_truthful_on
      (AppliedModelingLib.Auction.targetBundleThresholdAuction target price)
      AppliedModelingLib.Auction.CombinatorialAuction.Normalized := by
  rw [paper_combinatorial_truthful_on_eq]
  exact
    AppliedModelingLib.Auction.targetBundleThresholdAuction_truthfulOn_normalized
      target price hind

/--
Target-bundle critical-price mechanisms are truthful on nonempty single-minded
valuation profiles when each bidder's offered price is independent of that
bidder's own report.
-/
theorem paper_combinatorial_target_bundle_threshold_truthful_on_single_minded
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (target : Bidder → AppliedModelingLib.Auction.Bundle Item)
    (price :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind : AppliedModelingLib.Auction.BundlePriceOwnReportIndependent price) :
    paper_combinatorial_truthful_on
      (AppliedModelingLib.Auction.targetBundleThresholdAuction target price)
      AppliedModelingLib.Auction.IsNonemptySingleMindedProfile := by
  rw [paper_combinatorial_truthful_on_eq]
  exact
    AppliedModelingLib.Auction.targetBundleThresholdAuction_truthfulOn_singleMindedProfiles
      target price hind

/--
Target-bundle threshold allocations are feasible when every accepted target is
contained in the goods set and accepted targets are pairwise disjoint.
-/
theorem paper_combinatorial_target_bundle_threshold_feasible_of_pairwise_disjoint
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item]
    (target : Bidder → AppliedModelingLib.Auction.Bundle Item)
    (price :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item → Bidder → ℝ)
    (reports : AppliedModelingLib.Auction.CombinatorialReport Bidder Item)
    (goods : Finset Item)
    (hgoods : ∀ i,
      i ∈ AppliedModelingLib.Auction.targetBundleWinners target price reports →
        target i ⊆ goods)
    (hdisjoint :
      AppliedModelingLib.Auction.PairwiseDisjointDesired
        (AppliedModelingLib.Auction.targetAsSingleMindedBids target reports)
        (AppliedModelingLib.Auction.targetBundleWinners target price reports)) :
    AppliedModelingLib.Auction.IsFeasibleBundleAllocation
      ((AppliedModelingLib.Auction.targetBundleThresholdAuction target price).allocation
        reports)
      goods := by
  exact
    AppliedModelingLib.Auction.targetBundleThresholdAuction_feasible_of_pairwiseDisjoint
      target price reports goods hgoods hdisjoint

/-- LOS02 Section 4 GVA generated by a welfare-maximizing allocation rule. -/
noncomputable abbrev paper_generalized_vickrey_auction
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    (alloc :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item →
        AppliedModelingLib.Auction.BundleAllocation Bidder Item) :
    AppliedModelingLib.Auction.CombinatorialAuction Bidder Item :=
  AppliedModelingLib.Auction.generalizedVickreyAuction alloc

/-- Paper-facing welfare-maximization condition for the GVA allocation rule. -/
def paper_gva_welfare_maximizing_allocation_rule
    {Bidder Item : Type*} [Fintype Bidder]
    (alloc :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item →
        AppliedModelingLib.Auction.BundleAllocation Bidder Item) : Prop :=
  AppliedModelingLib.Auction.WelfareMaximizingAllocationRule alloc

/-- LOS02 Theorem 4.1: the generalized Vickrey auction is truthful. -/
theorem paper_theorem4_1_generalized_vickrey_truthful
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    (alloc :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item →
        AppliedModelingLib.Auction.BundleAllocation Bidder Item)
    (hmax : paper_gva_welfare_maximizing_allocation_rule alloc) :
    (paper_generalized_vickrey_auction alloc).TruthfulDominantStrategy := by
  exact AppliedModelingLib.Auction.generalizedVickreyAuction_truthful alloc hmax

/-- LOS02 Proposition 4.2: a truthful GVA bidder has nonnegative utility. -/
theorem paper_proposition4_2_generalized_vickrey_truthful_utility_nonneg
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    (alloc :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item →
        AppliedModelingLib.Auction.BundleAllocation Bidder Item)
    (hmax : paper_gva_welfare_maximizing_allocation_rule alloc)
    (values : AppliedModelingLib.Auction.CombinatorialReport Bidder Item)
    (hvalues :
      AppliedModelingLib.Auction.CombinatorialAuction.NonnegativeValues values)
    (i : Bidder) :
    0 ≤
      (paper_generalized_vickrey_auction alloc).utility values values i := by
  exact
    AppliedModelingLib.Auction.generalizedVickreyAuction_truthful_utility_nonneg
      alloc hmax values hvalues i

/-- LOS02 Definition 7.1: average amount per good, `a / |s|`. -/
noncomputable abbrev paper_average_amount_per_good {Item : Type*}
    [DecidableEq Item] (b : AppliedModelingLib.Auction.SingleMindedBid Item) : ℝ :=
  AppliedModelingLib.Auction.SingleMindedBid.averageAmountPerGood b

/--
If a bid's declared value is below `|s| * c(n)`, its average amount per good is
below `c(n)`. This is the algebraic ordering step in the Theorem 10.2
critical-price proof.
-/
theorem paper_average_amount_per_good_lt_of_value_lt_bundleSize_mul
    {Item : Type*} [DecidableEq Item]
    (b n : AppliedModelingLib.Auction.SingleMindedBid Item)
    (hb : b.desired.Nonempty)
    (hlt : b.value < b.bundleSize * n.averageAmountPerGood) :
    paper_average_amount_per_good b < paper_average_amount_per_good n := by
  exact
    AppliedModelingLib.Auction.SingleMindedBid.averageAmountPerGood_lt_of_value_lt_bundleSize_mul
      b n hb hlt

/--
If a bid's declared value is above `|s| * c(n)`, its average amount per good is
above `c(n)`. This is the algebraic ordering step in the above-threshold half of
the Theorem 10.2 critical-price proof.
-/
theorem paper_average_amount_per_good_lt_of_bundleSize_mul_lt_value
    {Item : Type*} [DecidableEq Item]
    (b n : AppliedModelingLib.Auction.SingleMindedBid Item)
    (hb : b.desired.Nonempty)
    (hlt : b.bundleSize * n.averageAmountPerGood < b.value) :
    paper_average_amount_per_good n < paper_average_amount_per_good b := by
  exact
    AppliedModelingLib.Auction.SingleMindedBid.averageAmountPerGood_lt_of_bundleSize_mul_lt_value
      b n hb hlt

/--
On the nonnegative source domain, shrinking a nonempty desired bundle while
weakly increasing value weakly increases the average amount per good. This is
the paper's Section 10 monotonicity comparison for strengthened bids.
-/
theorem paper_average_amount_per_good_le_of_subset_value_le
    {Item : Type*} [DecidableEq Item]
    (b : AppliedModelingLib.Auction.SingleMindedBid Item)
    {s : AppliedModelingLib.Auction.Bundle Item} {v : ℝ}
    (hb_nonempty : b.desired.Nonempty) (hs : s.Nonempty)
    (hsub : s ⊆ b.desired)
    (hb_nonneg : 0 ≤ b.value) (hle : b.value ≤ v) :
    paper_average_amount_per_good b ≤
      paper_average_amount_per_good
        ({ desired := s, value := v } :
          AppliedModelingLib.Auction.SingleMindedBid Item) := by
  exact
    AppliedModelingLib.Auction.SingleMindedBid.averageAmountPerGood_le_of_subset_value_le
      b hb_nonempty hs hsub hb_nonneg hle

/-- LOS02 Theorem 7.2 square-root greedy norm, `a / sqrt(|s|)`. -/
noncomputable abbrev paper_sqrt_amount_norm {Item : Type*}
    [DecidableEq Item] (b : AppliedModelingLib.Auction.SingleMindedBid Item) : ℝ :=
  AppliedModelingLib.Auction.SingleMindedBid.sqrtAmountNorm b

/-- Paper-facing total value of a selected finite set of single-minded bids. -/
noncomputable abbrev paper_single_minded_total_value
    {Bidder Item : Type*} [DecidableEq Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (selected : Finset Bidder) : ℝ :=
  AppliedModelingLib.Auction.singleMindedTotalValue bids selected

/-- The weighted set-packing feasibility predicate used in Theorem 6.1's reduction. -/
abbrev paper_set_packing_feasible
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (selected : Finset Bidder) : Prop :=
  AppliedModelingLib.Auction.SetPackingFeasible sets selected

/-- The weighted set-packing objective used in Theorem 6.1's reduction. -/
noncomputable abbrev paper_weighted_set_packing_value
    {Bidder : Type*} [DecidableEq Bidder]
    (weights : Bidder → ℝ) (selected : Finset Bidder) : ℝ :=
  AppliedModelingLib.Auction.weightedSetPackingValue weights selected

/-- Encode weighted set packing as a single-minded bid profile. -/
abbrev paper_set_packing_single_minded_bids
    {Bidder Item : Type*}
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ) :
    Bidder → AppliedModelingLib.Auction.SingleMindedBid Item :=
  AppliedModelingLib.Auction.setPackingSingleMindedBids sets weights

/--
The Theorem 6.1 set-packing encoding preserves feasibility exactly: pairwise
disjoint encoded single-minded accepted sets are precisely feasible
set-packing selections.
-/
theorem paper_theorem6_1_set_packing_feasibility_encoding_correct
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (selected : Finset Bidder) :
    AppliedModelingLib.Auction.PairwiseDisjointDesired
        (paper_set_packing_single_minded_bids sets weights) selected ↔
      paper_set_packing_feasible sets selected := by
  exact
    AppliedModelingLib.Auction.pairwiseDisjointDesired_setPackingSingleMindedBids_iff
      sets weights selected

/--
The Theorem 6.1 set-packing encoding preserves objective value exactly.
-/
theorem paper_theorem6_1_set_packing_value_encoding_correct
    {Bidder Item : Type*} [DecidableEq Bidder]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (selected : Finset Bidder) :
    paper_single_minded_total_value
        (paper_set_packing_single_minded_bids sets weights) selected =
      paper_weighted_set_packing_value weights selected := by
  exact
    AppliedModelingLib.Auction.singleMindedTotalValue_setPackingSingleMindedBids
      sets weights selected

/-- Optimal selections for weighted set packing. -/
abbrev paper_weighted_set_packing_optimal
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (selected : Finset Bidder) : Prop :=
  AppliedModelingLib.Auction.WeightedSetPackingOptimal sets weights selected

/-- Optimal accepted sets for single-minded welfare maximization. -/
abbrev paper_single_minded_optimal_accepted_set
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (selected : Finset Bidder) : Prop :=
  AppliedModelingLib.Auction.SingleMindedOptimalAcceptedSet bids selected

/-- Multiplicative approximation guarantee for weighted set packing. -/
abbrev paper_weighted_set_packing_approximation_at_least
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (factor : ℝ) (selected : Finset Bidder) : Prop :=
  AppliedModelingLib.Auction.WeightedSetPackingApproximationAtLeast
    sets weights factor selected

/-- Multiplicative approximation guarantee for single-minded welfare. -/
abbrev paper_single_minded_approximation_at_least
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (factor : ℝ) (selected : Finset Bidder) : Prop :=
  AppliedModelingLib.Auction.SingleMindedApproximationAtLeast bids factor selected

/-- Exact single-minded welfare solvers. -/
abbrev paper_single_minded_optimal_solver
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (solver :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder) :
    Prop :=
  AppliedModelingLib.Auction.SingleMindedOptimalSolver solver

/-- Exact weighted set-packing solvers. -/
abbrev paper_weighted_set_packing_optimal_solver
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (solver :
      (Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) : Prop :=
  AppliedModelingLib.Auction.WeightedSetPackingOptimalSolver solver

/-- Uniform approximation solvers for single-minded welfare. -/
abbrev paper_single_minded_approximation_solver_at_least
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (solver :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder) :
    Prop :=
  AppliedModelingLib.Auction.SingleMindedApproximationSolverAtLeast factor solver

/-- Uniform approximation solvers for weighted set packing. -/
abbrev paper_weighted_set_packing_approximation_solver_at_least
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (solver :
      (Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) : Prop :=
  AppliedModelingLib.Auction.WeightedSetPackingApproximationSolverAtLeast factor solver

/-- Compose a single-minded welfare solver with the Theorem 6.1 encoding. -/
abbrev paper_set_packing_solver_of_single_minded_solver
    {Bidder Item : Type*}
    (solver :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder)
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ) :
    Finset Bidder :=
  AppliedModelingLib.Auction.setPackingSolverOfSingleMindedSolver solver sets weights

/-- Threshold decision instances for weighted set packing. -/
abbrev paper_weighted_set_packing_decision_instance (Bidder Item : Type*) :=
  AppliedModelingLib.Auction.WeightedSetPackingDecisionInstance Bidder Item

/-- Threshold decision instances for single-minded welfare maximization. -/
abbrev paper_single_minded_welfare_decision_instance (Bidder Item : Type*) :=
  AppliedModelingLib.Auction.SingleMindedWelfareDecisionInstance Bidder Item

/-- Weighted set-packing threshold decision problem. -/
noncomputable abbrev paper_weighted_set_packing_decision_problem
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item] :
    AppliedModelingLib.Complexity.DecisionProblem
      (paper_weighted_set_packing_decision_instance Bidder Item) :=
  AppliedModelingLib.Auction.WeightedSetPackingDecisionProblem

/-- Single-minded welfare threshold decision problem. -/
noncomputable abbrev paper_single_minded_welfare_decision_problem
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item] :
    AppliedModelingLib.Complexity.DecisionProblem
      (paper_single_minded_welfare_decision_instance Bidder Item) :=
  AppliedModelingLib.Auction.SingleMindedWelfareDecisionProblem

/-- The set-to-bid encoding as a map of threshold decision instances. -/
abbrev paper_set_packing_decision_to_single_minded_welfare_decision
    {Bidder Item : Type*}
    (problem : paper_weighted_set_packing_decision_instance Bidder Item) :
    paper_single_minded_welfare_decision_instance Bidder Item :=
  AppliedModelingLib.Auction.setPackingDecisionToSingleMindedWelfareDecision problem

/-- Graph independent-set feasibility used in the Theorem 6.1 proof route. -/
abbrev paper_graph_independent_selection
    {Vertex : Type*}
    (G : SimpleGraph Vertex) (selected : Finset Vertex) : Prop :=
  AppliedModelingLib.Auction.GraphIndependentSelection G selected

/-- Maximum independent sets by cardinality. -/
abbrev paper_maximum_independent_selection
    {Vertex : Type*}
    (G : SimpleGraph Vertex) (selected : Finset Vertex) : Prop :=
  AppliedModelingLib.Auction.MaximumIndependentSelection G selected

/-- Graph clique selections used in the classic Theorem 6.1 hardness route. -/
abbrev paper_graph_clique_selection
    {Vertex : Type*}
    (G : SimpleGraph Vertex) (selected : Finset Vertex) : Prop :=
  AppliedModelingLib.Auction.GraphCliqueSelection G selected

/-- Maximum cliques by cardinality. -/
abbrev paper_maximum_clique_selection
    {Vertex : Type*}
    (G : SimpleGraph Vertex) (selected : Finset Vertex) : Prop :=
  AppliedModelingLib.Auction.MaximumCliqueSelection G selected

/-- Threshold decision instances for graph independent set. -/
abbrev paper_graph_independent_set_decision_instance (Vertex : Type*) :=
  AppliedModelingLib.Auction.GraphIndependentSetDecisionInstance Vertex

/-- Threshold decision instances for graph clique. -/
abbrev paper_graph_clique_decision_instance (Vertex : Type*) :=
  AppliedModelingLib.Auction.GraphCliqueDecisionInstance Vertex

/-- Graph independent-set threshold decision problem. -/
abbrev paper_graph_independent_set_decision_problem {Vertex : Type*} :
    AppliedModelingLib.Complexity.DecisionProblem
      (paper_graph_independent_set_decision_instance Vertex) :=
  AppliedModelingLib.Auction.GraphIndependentSetDecisionProblem

/-- Graph clique threshold decision problem. -/
abbrev paper_graph_clique_decision_problem {Vertex : Type*} :
    AppliedModelingLib.Complexity.DecisionProblem
      (paper_graph_clique_decision_instance Vertex) :=
  AppliedModelingLib.Auction.GraphCliqueDecisionProblem

/-- Reduce clique threshold decision to independent-set threshold decision by complementing. -/
abbrev paper_graph_clique_decision_to_independent_set_complement_decision
    {Vertex : Type*}
    (problem : paper_graph_clique_decision_instance Vertex) :
    paper_graph_independent_set_decision_instance Vertex :=
  AppliedModelingLib.Auction.graphCliqueDecisionToIndependentSetComplementDecision
    problem

/-- Encode independent-set threshold decision as weighted set packing. -/
noncomputable abbrev paper_graph_independent_set_decision_to_weighted_set_packing_decision
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (problem : paper_graph_independent_set_decision_instance Vertex) :
    paper_weighted_set_packing_decision_instance Vertex (Sym2 Vertex) :=
  AppliedModelingLib.Auction.graphIndependentSetDecisionToWeightedSetPackingDecision
    problem

/-- Encode clique threshold decision as weighted set packing on complement edges. -/
noncomputable abbrev paper_graph_clique_decision_to_weighted_set_packing_decision
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (problem : paper_graph_clique_decision_instance Vertex) :
    paper_weighted_set_packing_decision_instance Vertex (Sym2 Vertex) :=
  AppliedModelingLib.Auction.graphCliqueDecisionToWeightedSetPackingDecision problem

/-- Encode clique threshold decision as single-minded welfare on complement-edge goods. -/
noncomputable abbrev paper_graph_clique_decision_to_single_minded_welfare_decision
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (problem : paper_graph_clique_decision_instance Vertex) :
    paper_single_minded_welfare_decision_instance Vertex (Sym2 Vertex) :=
  AppliedModelingLib.Auction.graphCliqueDecisionToSingleMindedWelfareDecision problem

/-- Encode a graph as a set-packing instance whose goods are graph edges. -/
noncomputable abbrev paper_graph_incident_sets
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj] :
    Vertex → Finset (Sym2 Vertex) :=
  AppliedModelingLib.Auction.graphIncidentSets G

/-- Unit vertex weights for the independent-set reduction. -/
abbrev paper_graph_unit_weights (Vertex : Type*) : Vertex → ℝ :=
  AppliedModelingLib.Auction.graphUnitWeights Vertex

/--
LOS02 Theorem 6.1 set-packing reduction layer: under the paper's set-to-bid
encoding, weighted set-packing optimality is exactly single-minded welfare
optimality.  The surrounding NP-hardness/NP=ZPP complexity facts remain external
to the current Lean library.
-/
theorem paper_theorem6_1_weighted_set_packing_reduction
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (selected : Finset Bidder) :
    paper_weighted_set_packing_optimal sets weights selected ↔
      paper_single_minded_optimal_accepted_set
        (paper_set_packing_single_minded_bids sets weights) selected := by
  exact
    AppliedModelingLib.Auction.weightedSetPackingOptimal_iff_singleMindedOptimalAcceptedSet
      sets weights selected

/--
Theorem 6.1 solver-transfer form: any exact solver for single-minded welfare
maximization gives an exact solver for weighted set packing after composing
with the paper's set-to-bid encoding.
-/
theorem paper_theorem6_1_optimal_solver_reduction
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (solver :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder)
    (hsolver : paper_single_minded_optimal_solver solver) :
    paper_weighted_set_packing_optimal_solver
      (paper_set_packing_solver_of_single_minded_solver solver) := by
  exact
    AppliedModelingLib.Auction.weightedSetPackingOptimalSolver_of_singleMindedOptimalSolver
      solver hsolver

/--
Theorem 6.1 approximation-preserving form: the set-to-bid encoding preserves a
multiplicative approximation guarantee for each selected set.
-/
theorem paper_theorem6_1_approximation_preserving_reduction
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ)
    (factor : ℝ) (selected : Finset Bidder) :
    paper_weighted_set_packing_approximation_at_least
        sets weights factor selected ↔
      paper_single_minded_approximation_at_least
        (paper_set_packing_single_minded_bids sets weights) factor selected := by
  exact
    AppliedModelingLib.Auction.weightedSetPackingApproximationAtLeast_iff_singleMindedApproximationAtLeast
      sets weights factor selected

/--
Theorem 6.1 approximation-solver transfer: any single-minded welfare solver
with a uniform multiplicative guarantee gives a weighted set-packing solver with
the same guarantee via the paper's set-to-bid encoding.
-/
theorem paper_theorem6_1_approximation_solver_reduction
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (solver :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder)
    (hsolver :
      paper_single_minded_approximation_solver_at_least factor solver) :
    paper_weighted_set_packing_approximation_solver_at_least factor
      (paper_set_packing_solver_of_single_minded_solver solver) := by
  exact
    AppliedModelingLib.Auction.weightedSetPackingApproximationSolverAtLeast_of_singleMindedApproximationSolverAtLeast
      factor solver hsolver

/--
Theorem 6.1 decision-problem encoding correctness: the weighted set-packing
threshold question is true exactly when the encoded single-minded welfare
threshold question is true.
-/
theorem paper_theorem6_1_decision_problem_encoding_correct
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (problem : paper_weighted_set_packing_decision_instance Bidder Item) :
    paper_weighted_set_packing_decision_problem problem ↔
      paper_single_minded_welfare_decision_problem
        (paper_set_packing_decision_to_single_minded_welfare_decision problem) := by
  exact
    AppliedModelingLib.Auction.weightedSetPackingDecisionProblem_iff_singleMindedWelfareDecisionProblem
      problem

/--
Theorem 6.1 as an abstract many-one reduction between threshold decision
problems.
-/
noncomputable def paper_theorem6_1_decision_problem_reduction
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item] :
    AppliedModelingLib.Complexity.ManyOneReduction
      (paper_weighted_set_packing_decision_problem
        (Bidder := Bidder) (Item := Item))
      (paper_single_minded_welfare_decision_problem
        (Bidder := Bidder) (Item := Item)) :=
  AppliedModelingLib.Auction.weightedSetPackingDecisionProblem_manyOneReduction_singleMindedWelfareDecisionProblem

/--
Theorem 6.1 as an abstract polynomial-time reduction, conditional on an
external runtime certificate for the set-to-bid encoding.
-/
noncomputable def paper_theorem6_1_polynomial_time_decision_problem_reduction
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (PolynomialTime :
      (paper_weighted_set_packing_decision_instance Bidder Item →
        paper_single_minded_welfare_decision_instance Bidder Item) → Prop)
    (hpoly :
      PolynomialTime
        paper_set_packing_decision_to_single_minded_welfare_decision) :
    AppliedModelingLib.Complexity.PolynomialTimeReduction
      (paper_weighted_set_packing_decision_problem
        (Bidder := Bidder) (Item := Item))
      (paper_single_minded_welfare_decision_problem
        (Bidder := Bidder) (Item := Item)) :=
  AppliedModelingLib.Auction.weightedSetPackingDecisionProblem_polynomialTimeReduction_singleMindedWelfareDecisionProblem
    PolynomialTime hpoly

/--
External reduction-consequence form of Theorem 6.1 for threshold decision
problems: any external consequence that follows from a many-one reduction out of
weighted set packing follows for the encoded single-minded welfare target.
-/
theorem paper_theorem6_1_external_decision_reduction_consequence
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (C :
      AppliedModelingLib.Complexity.ExternalReductionConsequence
        (paper_weighted_set_packing_decision_problem
          (Bidder := Bidder) (Item := Item))
        (paper_single_minded_welfare_decision_problem
          (Bidder := Bidder) (Item := Item)))
    (hsource : C.SourceHard) :
    C.Consequence :=
  C.apply paper_theorem6_1_decision_problem_reduction hsource

/--
External polynomial-reduction consequence form of Theorem 6.1 for threshold
decision problems, conditional on an external runtime certificate for the
set-to-bid encoding.
-/
theorem paper_theorem6_1_external_polynomial_time_decision_reduction_consequence
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (PolynomialTime :
      (paper_weighted_set_packing_decision_instance Bidder Item →
        paper_single_minded_welfare_decision_instance Bidder Item) → Prop)
    (hpoly :
      PolynomialTime
        paper_set_packing_decision_to_single_minded_welfare_decision)
    (C :
      AppliedModelingLib.Complexity.ExternalPolynomialReductionConsequence
        (paper_weighted_set_packing_decision_problem
          (Bidder := Bidder) (Item := Item))
        (paper_single_minded_welfare_decision_problem
          (Bidder := Bidder) (Item := Item)))
    (hsource : C.SourceHard) :
    C.Consequence :=
  C.apply
    (paper_theorem6_1_polynomial_time_decision_problem_reduction
      PolynomialTime hpoly)
    hsource

/--
Hardness-transfer form of Theorem 6.1: any abstract hardness notion closed
under many-one reductions transfers from weighted set packing to single-minded
welfare through the compiled set-to-bid reduction.
-/
theorem paper_theorem6_1_set_packing_hardness_transfers_to_single_minded
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (H : AppliedModelingLib.Complexity.ReductionClosedHardness)
    (hsource :
      H.Hard
        (paper_weighted_set_packing_decision_problem
          (Bidder := Bidder) (Item := Item))) :
    H.Hard
      (paper_single_minded_welfare_decision_problem
        (Bidder := Bidder) (Item := Item)) :=
  H.apply paper_theorem6_1_decision_problem_reduction hsource

/--
Polynomial-time hardness-transfer form of Theorem 6.1, conditional on an
external runtime certificate for the set-to-bid encoding.
-/
theorem paper_theorem6_1_set_packing_polynomial_hardness_transfers_to_single_minded
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (PolynomialTime :
      (paper_weighted_set_packing_decision_instance Bidder Item →
        paper_single_minded_welfare_decision_instance Bidder Item) → Prop)
    (hpoly :
      PolynomialTime
        paper_set_packing_decision_to_single_minded_welfare_decision)
    (H : AppliedModelingLib.Complexity.PolynomialReductionClosedHardness)
    (hsource :
      H.Hard
        (paper_weighted_set_packing_decision_problem
          (Bidder := Bidder) (Item := Item))) :
    H.Hard
      (paper_single_minded_welfare_decision_problem
        (Bidder := Bidder) (Item := Item)) :=
  H.apply
    (paper_theorem6_1_polynomial_time_decision_problem_reduction
      PolynomialTime hpoly)
    hsource

/--
Conditional external-complexity form of Theorem 6.1 for exact optimization. If
the source's external set-packing hardness theorem says every feasible exact
weighted set-packing solver implies `complexityConsequence`, and feasibility is
preserved by composing with the LOS02 encoding, then any feasible exact
single-minded allocation solver implies the same consequence.
-/
theorem paper_theorem6_1_external_optimal_solver_complexity_consequence
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (FeasibleSM :
      ((Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder) → Prop)
    (FeasibleWSP :
      ((Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) → Prop)
    (complexityConsequence : Prop)
    (solver :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder)
    (hsolver : paper_single_minded_optimal_solver solver)
    (hfeasible : FeasibleSM solver)
    (hfeasible_transfer :
      FeasibleSM solver →
        FeasibleWSP (paper_set_packing_solver_of_single_minded_solver solver))
    (hexternal :
      ∀ wspSolver,
        paper_weighted_set_packing_optimal_solver wspSolver →
          FeasibleWSP wspSolver → complexityConsequence) :
    complexityConsequence := by
  let externalConsequence :
      AppliedModelingLib.Complexity.ExternalSolverConsequence
        ((Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) := {
    Solves := paper_weighted_set_packing_optimal_solver
    Feasible := FeasibleWSP
    Consequence := complexityConsequence
    consequence_of_solver := hexternal }
  exact
    externalConsequence.apply
      (paper_set_packing_solver_of_single_minded_solver solver)
      (paper_theorem6_1_optimal_solver_reduction solver hsolver)
      (hfeasible_transfer hfeasible)

/--
Conditional external-complexity form of Theorem 6.1 for approximation. If the
source's external set-packing inapproximability theorem says every feasible
weighted set-packing approximation solver with factor `factor` implies
`complexityConsequence`, and feasibility is preserved by composing with the
LOS02 encoding, then any feasible single-minded approximation solver with the
same factor implies that consequence.
-/
theorem paper_theorem6_1_external_approximation_solver_complexity_consequence
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (FeasibleSM :
      ((Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder) → Prop)
    (FeasibleWSP :
      ((Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) → Prop)
    (complexityConsequence : Prop)
    (solver :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder)
    (hsolver :
      paper_single_minded_approximation_solver_at_least factor solver)
    (hfeasible : FeasibleSM solver)
    (hfeasible_transfer :
      FeasibleSM solver →
        FeasibleWSP (paper_set_packing_solver_of_single_minded_solver solver))
    (hexternal :
      ∀ wspSolver,
        paper_weighted_set_packing_approximation_solver_at_least factor
            wspSolver →
          FeasibleWSP wspSolver → complexityConsequence) :
    complexityConsequence := by
  let externalConsequence :
      AppliedModelingLib.Complexity.ExternalSolverConsequence
        ((Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) := {
    Solves := paper_weighted_set_packing_approximation_solver_at_least factor
    Feasible := FeasibleWSP
    Consequence := complexityConsequence
    consequence_of_solver := hexternal }
  exact
    externalConsequence.apply
      (paper_set_packing_solver_of_single_minded_solver solver)
      (paper_theorem6_1_approximation_solver_reduction factor solver hsolver)
      (hfeasible_transfer hfeasible)

/--
Named `NP = ZPP` specialization of the exact external-complexity wrapper. If an
external set-packing hardness theorem says every feasible exact weighted
set-packing solver collapses the supplied abstract classes from `NP` to `ZPP`,
then a feasible exact single-minded allocation solver has the same consequence.
-/
theorem paper_theorem6_1_external_optimal_solver_np_eq_zpp
    {Bidder Item Language : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (complexityModel :
      AppliedModelingLib.Complexity.ComplexityClassModel Language)
    (FeasibleSM :
      ((Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder) → Prop)
    (FeasibleWSP :
      ((Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) → Prop)
    (solver :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder)
    (hsolver : paper_single_minded_optimal_solver solver)
    (hfeasible : FeasibleSM solver)
    (hfeasible_transfer :
      FeasibleSM solver →
        FeasibleWSP (paper_set_packing_solver_of_single_minded_solver solver))
    (hexternal :
      ∀ wspSolver,
        paper_weighted_set_packing_optimal_solver wspSolver →
          FeasibleWSP wspSolver → complexityModel.npEqZPP) :
    complexityModel.npEqZPP := by
  exact
    paper_theorem6_1_external_optimal_solver_complexity_consequence
      FeasibleSM FeasibleWSP complexityModel.npEqZPP solver hsolver hfeasible
      hfeasible_transfer hexternal

/--
Named `NP = ZPP` specialization of the approximation external-complexity
wrapper. If an external set-packing inapproximability theorem says every
feasible weighted set-packing approximation solver with factor `factor`
collapses the supplied abstract classes from `NP` to `ZPP`, then a feasible
single-minded approximation solver with the same factor has that consequence.
-/
theorem paper_theorem6_1_external_approximation_solver_np_eq_zpp
    {Bidder Item Language : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (factor : ℝ)
    (complexityModel :
      AppliedModelingLib.Complexity.ComplexityClassModel Language)
    (FeasibleSM :
      ((Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder) → Prop)
    (FeasibleWSP :
      ((Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) → Prop)
    (solver :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → Finset Bidder)
    (hsolver :
      paper_single_minded_approximation_solver_at_least factor solver)
    (hfeasible : FeasibleSM solver)
    (hfeasible_transfer :
      FeasibleSM solver →
        FeasibleWSP (paper_set_packing_solver_of_single_minded_solver solver))
    (hexternal :
      ∀ wspSolver,
        paper_weighted_set_packing_approximation_solver_at_least factor
            wspSolver →
          FeasibleWSP wspSolver → complexityModel.npEqZPP) :
    complexityModel.npEqZPP := by
  exact
    paper_theorem6_1_external_approximation_solver_complexity_consequence
      factor FeasibleSM FeasibleWSP complexityModel.npEqZPP solver hsolver
      hfeasible hfeasible_transfer hexternal

/-- Abstract randomized-class model for the source note after Theorem 6.1. -/
abbrev paper_randomized_complexity_class_model (Language : Type*) :=
  AppliedModelingLib.Complexity.RandomizedComplexityClassModel Language

/-- Source complexity note: in the abstract model, `P = NP` implies `NP = ZPP`. -/
theorem paper_complexity_note_p_eq_np_implies_np_eq_zpp
    {Language : Type*}
    (complexityModel : paper_randomized_complexity_class_model Language)
    (h : complexityModel.pEqNP) :
    complexityModel.toComplexityClassModel.npEqZPP := by
  exact
    AppliedModelingLib.Complexity.RandomizedComplexityClassModel.npEqZPP_of_pEqNP
      (M := complexityModel) h

/-- Source complexity note: `NP = ZPP` implies `NP = RP` in the abstract model. -/
theorem paper_complexity_note_np_eq_zpp_implies_np_eq_rp
    {Language : Type*}
    (complexityModel : paper_randomized_complexity_class_model Language)
    (h : complexityModel.toComplexityClassModel.npEqZPP) :
    complexityModel.NP = complexityModel.RP := by
  exact
    AppliedModelingLib.Complexity.RandomizedComplexityClassModel.npEqRP_of_npEqZPP
      (M := complexityModel) h

/-- Source complexity note: `NP = ZPP` implies `NP = co-RP` in the abstract model. -/
theorem paper_complexity_note_np_eq_zpp_implies_np_eq_corp
    {Language : Type*}
    (complexityModel : paper_randomized_complexity_class_model Language)
    (h : complexityModel.toComplexityClassModel.npEqZPP) :
    complexityModel.NP = complexityModel.coRP := by
  exact
    AppliedModelingLib.Complexity.RandomizedComplexityClassModel.npEqCoRP_of_npEqZPP
      (M := complexityModel) h

/-- Source complexity note: `NP = ZPP` implies `NP = co-NP` in the abstract model. -/
theorem paper_complexity_note_np_eq_zpp_implies_np_eq_conp
    {Language : Type*}
    (complexityModel : paper_randomized_complexity_class_model Language)
    (h : complexityModel.toComplexityClassModel.npEqZPP) :
    complexityModel.NP = complexityModel.coNP := by
  exact
    (AppliedModelingLib.Complexity.RandomizedComplexityClassModel.coNPEqNP_of_npEqZPP
      (M := complexityModel) h).symm

/--
Source complexity note: `NP = ZPP` gives the packaged randomized-class collapse
`NP = RP`, `NP = co-RP`, and `NP = co-NP` in the abstract model.
-/
theorem paper_complexity_note_np_eq_zpp_implies_randomized_collapse
    {Language : Type*}
    (complexityModel : paper_randomized_complexity_class_model Language)
    (h : complexityModel.toComplexityClassModel.npEqZPP) :
    complexityModel.NP = complexityModel.RP ∧
      complexityModel.NP = complexityModel.coRP ∧
      complexityModel.NP = complexityModel.coNP := by
  exact
    AppliedModelingLib.Complexity.RandomizedComplexityClassModel.randomized_collapse_of_npEqZPP
      (M := complexityModel) h

/--
Theorem 6.1 graph-incidence reduction layer: independent vertex sets are
exactly feasible set-packing selections when goods are graph edges and each
vertex requests its incident edges.
-/
theorem paper_theorem6_1_graph_independent_set_feasibility_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    paper_set_packing_feasible (paper_graph_incident_sets G) selected ↔
      paper_graph_independent_selection G selected := by
  exact
    AppliedModelingLib.Auction.setPackingFeasible_graphIncidentSets_iff_graphIndependentSelection
      G selected

/--
Theorem 6.1 graph-incidence optimality reduction: maximum independent sets are
exactly optimal unit-weight set-packing selections under the graph-edge
incidence encoding.
-/
theorem paper_theorem6_1_independent_set_set_packing_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    paper_maximum_independent_selection G selected ↔
      paper_weighted_set_packing_optimal
        (paper_graph_incident_sets G) (paper_graph_unit_weights Vertex)
        selected := by
  exact
    AppliedModelingLib.Auction.maximumIndependentSelection_iff_weightedSetPackingOptimal_graphIncidentSets
      G selected

/--
Theorem 6.1 graph-to-single-minded allocation reduction: maximum independent
sets are exactly optimal accepted sets after encoding graph edges as goods and
vertices as unit-value single-minded bids.
-/
theorem paper_theorem6_1_independent_set_allocation_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    paper_maximum_independent_selection G selected ↔
      paper_single_minded_optimal_accepted_set
        (paper_set_packing_single_minded_bids
          (paper_graph_incident_sets G) (paper_graph_unit_weights Vertex))
        selected := by
  exact
    AppliedModelingLib.Auction.maximumIndependentSelection_iff_singleMindedOptimalAcceptedSet_graphIncident
      G selected

/--
Theorem 6.1 clique-complement layer: cliques in a graph are exactly
independent sets in its complement, preserving maximum-cardinality optimality.
-/
theorem paper_theorem6_1_clique_complement_independent_set_reduction
    {Vertex : Type*}
    (G : SimpleGraph Vertex) (selected : Finset Vertex) :
    paper_maximum_clique_selection G selected ↔
      paper_maximum_independent_selection Gᶜ selected := by
  exact
    AppliedModelingLib.Auction.maximumCliqueSelection_iff_maximumIndependentSelection_compl
      G selected

/--
Theorem 6.1 clique-to-set-packing reduction: maximum cliques are exactly
optimal unit-weight set-packing selections after complementing the graph and
using complement-edge incidence sets.
-/
theorem paper_theorem6_1_clique_complement_set_packing_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    paper_maximum_clique_selection G selected ↔
      paper_weighted_set_packing_optimal
        (paper_graph_incident_sets Gᶜ) (paper_graph_unit_weights Vertex)
        selected := by
  exact
    AppliedModelingLib.Auction.maximumCliqueSelection_iff_weightedSetPackingOptimal_complGraphIncidentSets
      G selected

/--
Theorem 6.1 clique-to-single-minded allocation reduction: maximum cliques are
exactly optimal accepted sets after complementing the graph and encoding
complement edges as goods.
-/
theorem paper_theorem6_1_clique_complement_allocation_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (selected : Finset Vertex) :
    paper_maximum_clique_selection G selected ↔
      paper_single_minded_optimal_accepted_set
        (paper_set_packing_single_minded_bids
          (paper_graph_incident_sets Gᶜ) (paper_graph_unit_weights Vertex))
        selected := by
  exact
    AppliedModelingLib.Auction.maximumCliqueSelection_iff_singleMindedOptimalAcceptedSet_complGraphIncident
      G selected

/--
Theorem 6.1 clique decision reduction: clique threshold decision is independent
set threshold decision on the complement graph.
-/
theorem paper_theorem6_1_clique_decision_complement_independent_set_reduction
    {Vertex : Type*}
    (problem : paper_graph_clique_decision_instance Vertex) :
    paper_graph_clique_decision_problem problem ↔
      paper_graph_independent_set_decision_problem
        (paper_graph_clique_decision_to_independent_set_complement_decision
          problem) := by
  exact
    AppliedModelingLib.Auction.graphCliqueDecisionProblem_iff_graphIndependentSetDecisionProblem_compl
      problem

/--
Theorem 6.1 independent-set decision reduction: independent-set threshold
decision is unit-weight set-packing threshold decision on graph edges.
-/
theorem paper_theorem6_1_independent_set_decision_set_packing_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (problem : paper_graph_independent_set_decision_instance Vertex) :
    paper_graph_independent_set_decision_problem problem ↔
      paper_weighted_set_packing_decision_problem
        (paper_graph_independent_set_decision_to_weighted_set_packing_decision
          problem) := by
  exact
    AppliedModelingLib.Auction.graphIndependentSetDecisionProblem_iff_weightedSetPackingDecisionProblem_graphIncident
      problem

/--
Theorem 6.1 clique-to-set-packing decision reduction: clique threshold decision
is unit-weight set-packing threshold decision on complement edges.
-/
theorem paper_theorem6_1_clique_decision_set_packing_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (problem : paper_graph_clique_decision_instance Vertex) :
    paper_graph_clique_decision_problem problem ↔
      paper_weighted_set_packing_decision_problem
        (paper_graph_clique_decision_to_weighted_set_packing_decision
          problem) := by
  exact
    AppliedModelingLib.Auction.graphCliqueDecisionProblem_iff_weightedSetPackingDecisionProblem_complGraphIncident
      problem

/--
Theorem 6.1 clique-to-single-minded decision reduction: clique threshold
decision is single-minded welfare threshold decision on complement-edge goods.
-/
theorem paper_theorem6_1_clique_decision_single_minded_welfare_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (problem : paper_graph_clique_decision_instance Vertex) :
    paper_graph_clique_decision_problem problem ↔
      paper_single_minded_welfare_decision_problem
        (paper_graph_clique_decision_to_single_minded_welfare_decision
          problem) := by
  exact
    AppliedModelingLib.Auction.graphCliqueDecisionProblem_iff_singleMindedWelfareDecisionProblem_complGraphIncident
      problem

/-- Theorem 6.1 clique-to-independent-set complement as an abstract many-one reduction. -/
noncomputable def paper_theorem6_1_clique_decision_complement_many_one_reduction
    {Vertex : Type*} :
    AppliedModelingLib.Complexity.ManyOneReduction
      (paper_graph_clique_decision_problem (Vertex := Vertex))
      (paper_graph_independent_set_decision_problem (Vertex := Vertex)) :=
  AppliedModelingLib.Auction.graphCliqueDecisionProblem_manyOneReduction_graphIndependentSetDecisionProblem_compl

/-- Theorem 6.1 independent-set-to-set-packing as an abstract many-one reduction. -/
noncomputable def paper_theorem6_1_independent_set_decision_many_one_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex] :
    AppliedModelingLib.Complexity.ManyOneReduction
      (paper_graph_independent_set_decision_problem (Vertex := Vertex))
      (paper_weighted_set_packing_decision_problem
        (Bidder := Vertex) (Item := Sym2 Vertex)) :=
  AppliedModelingLib.Auction.graphIndependentSetDecisionProblem_manyOneReduction_weightedSetPackingDecisionProblem_graphIncident

/-- Theorem 6.1 clique-to-set-packing as an abstract many-one reduction. -/
noncomputable def paper_theorem6_1_clique_decision_set_packing_many_one_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex] :
    AppliedModelingLib.Complexity.ManyOneReduction
      (paper_graph_clique_decision_problem (Vertex := Vertex))
      (paper_weighted_set_packing_decision_problem
        (Bidder := Vertex) (Item := Sym2 Vertex)) :=
  AppliedModelingLib.Auction.graphCliqueDecisionProblem_manyOneReduction_weightedSetPackingDecisionProblem_complGraphIncident

/-- Theorem 6.1 clique-to-single-minded welfare as an abstract many-one reduction. -/
noncomputable def paper_theorem6_1_clique_decision_single_minded_many_one_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex] :
    AppliedModelingLib.Complexity.ManyOneReduction
      (paper_graph_clique_decision_problem (Vertex := Vertex))
      (paper_single_minded_welfare_decision_problem
        (Bidder := Vertex) (Item := Sym2 Vertex)) :=
  AppliedModelingLib.Auction.graphCliqueDecisionProblem_manyOneReduction_singleMindedWelfareDecisionProblem_complGraphIncident

/--
Theorem 6.1 clique-to-single-minded welfare as an abstract polynomial-time
reduction, conditional on an external runtime certificate for the complement
edge-incidence set-to-bid encoding.
-/
noncomputable def paper_theorem6_1_clique_decision_single_minded_polynomial_time_reduction
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (PolynomialTime :
      (paper_graph_clique_decision_instance Vertex →
        paper_single_minded_welfare_decision_instance Vertex (Sym2 Vertex)) →
        Prop)
    (hpoly :
      PolynomialTime
        paper_graph_clique_decision_to_single_minded_welfare_decision) :
    AppliedModelingLib.Complexity.PolynomialTimeReduction
      (paper_graph_clique_decision_problem (Vertex := Vertex))
      (paper_single_minded_welfare_decision_problem
        (Bidder := Vertex) (Item := Sym2 Vertex)) :=
  AppliedModelingLib.Auction.graphCliqueDecisionProblem_polynomialTimeReduction_singleMindedWelfareDecisionProblem_complGraphIncident
    PolynomialTime hpoly

/--
External reduction-consequence form of Theorem 6.1 for the classic clique
hardness route: any external consequence that follows from a many-one reduction
out of clique follows for the encoded single-minded welfare target.
-/
theorem paper_theorem6_1_external_clique_decision_single_minded_reduction_consequence
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (C :
      AppliedModelingLib.Complexity.ExternalReductionConsequence
        (paper_graph_clique_decision_problem (Vertex := Vertex))
        (paper_single_minded_welfare_decision_problem
          (Bidder := Vertex) (Item := Sym2 Vertex)))
    (hsource : C.SourceHard) :
    C.Consequence :=
  C.apply
    paper_theorem6_1_clique_decision_single_minded_many_one_reduction
    hsource

/--
External polynomial-reduction consequence form of Theorem 6.1 for the classic
clique hardness route, conditional on an external runtime certificate for the
compiled clique-to-single-minded encoding.
-/
theorem paper_theorem6_1_external_clique_polynomial_time_single_minded_reduction_consequence
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (PolynomialTime :
      (paper_graph_clique_decision_instance Vertex →
        paper_single_minded_welfare_decision_instance Vertex (Sym2 Vertex)) →
        Prop)
    (hpoly :
      PolynomialTime
        paper_graph_clique_decision_to_single_minded_welfare_decision)
    (C :
      AppliedModelingLib.Complexity.ExternalPolynomialReductionConsequence
        (paper_graph_clique_decision_problem (Vertex := Vertex))
        (paper_single_minded_welfare_decision_problem
          (Bidder := Vertex) (Item := Sym2 Vertex)))
    (hsource : C.SourceHard) :
    C.Consequence :=
  C.apply
    (paper_theorem6_1_clique_decision_single_minded_polynomial_time_reduction
      PolynomialTime hpoly)
    hsource

/--
Hardness-transfer form of Theorem 6.1 for the classic clique route: any
abstract hardness notion closed under many-one reductions transfers from clique
to single-minded welfare through the compiled complement-edge encoding.
-/
theorem paper_theorem6_1_clique_hardness_transfers_to_single_minded
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (H : AppliedModelingLib.Complexity.ReductionClosedHardness)
    (hsource :
      H.Hard (paper_graph_clique_decision_problem (Vertex := Vertex))) :
    H.Hard
      (paper_single_minded_welfare_decision_problem
        (Bidder := Vertex) (Item := Sym2 Vertex)) :=
  H.apply
    paper_theorem6_1_clique_decision_single_minded_many_one_reduction
    hsource

/--
Polynomial-time hardness-transfer form of Theorem 6.1 for the classic clique
route, conditional on an external runtime certificate for the compiled
complement-edge encoding.
-/
theorem paper_theorem6_1_clique_polynomial_hardness_transfers_to_single_minded
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (PolynomialTime :
      (paper_graph_clique_decision_instance Vertex →
        paper_single_minded_welfare_decision_instance Vertex (Sym2 Vertex)) →
        Prop)
    (hpoly :
      PolynomialTime
        paper_graph_clique_decision_to_single_minded_welfare_decision)
    (H : AppliedModelingLib.Complexity.PolynomialReductionClosedHardness)
    (hsource :
      H.Hard (paper_graph_clique_decision_problem (Vertex := Vertex))) :
    H.Hard
      (paper_single_minded_welfare_decision_problem
        (Bidder := Vertex) (Item := Sym2 Vertex)) :=
  H.apply
    (paper_theorem6_1_clique_decision_single_minded_polynomial_time_reduction
      PolynomialTime hpoly)
    hsource

/--
Paper-facing value-only perturbation of a single-minded bid profile. This is
the report change used in the critical-price proof of Theorem 10.2.
-/
abbrev paper_single_minded_value_update
    {Bidder Item : Type*} [DecidableEq Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (j : Bidder) (value : ℝ) : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item :=
  AppliedModelingLib.Auction.singleMindedValueUpdate bids j value

/-- A value-only perturbation preserves every desired bundle. -/
theorem paper_single_minded_value_update_desired
    {Bidder Item : Type*} [DecidableEq Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (j : Bidder) (value : ℝ) (k : Bidder) :
    (paper_single_minded_value_update bids j value k).desired =
      (bids k).desired := by
  exact AppliedModelingLib.Auction.singleMindedValueUpdate_desired bids j value k

/-- A value-only perturbation preserves which bid pairs conflict. -/
theorem paper_single_minded_value_update_conflict_iff
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (j : Bidder) (value : ℝ) (i k : Bidder) :
    AppliedModelingLib.Auction.SingleMindedBidsConflict
        (paper_single_minded_value_update bids j value) i k ↔
      AppliedModelingLib.Auction.SingleMindedBidsConflict bids i k := by
  exact
    AppliedModelingLib.Auction.singleMindedValueUpdate_conflict_iff
      bids j value i k

/-- Paper-facing LOS02 greedy accepted set from an explicit bid order. -/
abbrev paper_single_minded_greedy_accepted_from_order
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) : Finset Bidder :=
  AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order

/-- LOS02 Section 10 average-amount-per-good descending order predicate. -/
abbrev paper_average_amount_descending
    {Bidder Item : Type*} [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) : Prop :=
  AppliedModelingLib.Auction.SingleMindedAverageAmountDescending bids order

/-- Concrete LOS02 order: decreasing average amount per good with deterministic tie-breaks. -/
noncomputable abbrev paper_average_order_of
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) :
    List Bidder :=
  AppliedModelingLib.Auction.singleMindedAverageOrderOf bids

/-- The concrete LOS02 average order has no duplicate bidders. -/
theorem paper_average_order_of_nodup
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) :
    (paper_average_order_of bids).Nodup := by
  exact AppliedModelingLib.Auction.singleMindedAverageOrderOf_nodup bids

/-- Every bidder appears in the concrete LOS02 average order. -/
theorem paper_average_order_of_mem
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (i : Bidder) :
    i ∈ paper_average_order_of bids := by
  exact AppliedModelingLib.Auction.singleMindedAverageOrderOf_mem bids i

/-- The concrete LOS02 average order satisfies the average-descending predicate. -/
theorem paper_average_order_of_average_descending
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) :
    paper_average_amount_descending bids (paper_average_order_of bids) := by
  exact AppliedModelingLib.Auction.singleMindedAverageOrderOf_average_descending bids

/--
Section 10 source-order movement step: on the nonnegative single-minded domain,
replacing an accepted bidder's report by a nonempty subset bundle with weakly
larger value moves that bidder weakly earlier in the concrete average order.
-/
theorem paper_theorem10_2_average_order_update_moves_earlier
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (hbids :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile
        bids)
    {j : Bidder} {s : AppliedModelingLib.Auction.Bundle Item} {v : ℝ}
    (hupdated :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile
        (Function.update bids j { desired := s, value := v }))
    (hsub : s ⊆ (bids j).desired)
    (hle : (bids j).value ≤ v) :
    ∃ pref rest suffix tail,
      paper_average_order_of bids = (pref ++ rest) ++ j :: suffix ∧
        paper_average_order_of
            (Function.update bids j { desired := s, value := v }) =
          pref ++ j :: tail ∧
        j ∉ pref ∧ j ∉ rest ∧ j ∉ suffix := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageOrderOf_nonnegative_update_moves_earlier
      bids hbids hupdated hsub hle

/--
Changing only one bidder's value leaves the concrete LOS02 average order
unchanged after erasing that bidder.
-/
theorem paper_average_order_of_erase_value_update
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (j : Bidder) (value : ℝ) :
    (paper_average_order_of
        (AppliedModelingLib.Auction.singleMindedValueUpdate bids j value)).erase j =
      (paper_average_order_of bids).erase j := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageOrderOf_erase_valueUpdate
      bids j value

/-- Split form of concrete-order erase-stability under a value-only update. -/
theorem paper_average_order_of_erase_value_update_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder : paper_average_order_of bids = before ++ j :: base) :
    (paper_average_order_of
        (AppliedModelingLib.Auction.singleMindedValueUpdate bids j value)).erase j =
      before ++ base := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageOrderOf_erase_valueUpdate_of_split
      bids value horder

/--
Concrete-order sortedness, duplicate-freeness, membership, and global
erase-stability facts for a value-only update around a displayed split.
-/
theorem paper_average_order_value_update_global_facts_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder : paper_average_order_of bids = before ++ j :: base) :
    let updated := AppliedModelingLib.Auction.singleMindedValueUpdate bids j value
    let updatedOrder := paper_average_order_of updated
    paper_average_amount_descending updated updatedOrder ∧
      updatedOrder.Nodup ∧
      j ∈ updatedOrder ∧
      updatedOrder.erase j = before ++ base := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageOrderOf_valueUpdate_global_facts_of_split
      bids value horder

/--
After a value-only update, the concrete average order is obtained by inserting
`j` into the original order with `j` erased.
-/
theorem paper_average_order_of_value_update_eq_ordered_insert_erase_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder : paper_average_order_of bids = before ++ j :: base) :
    paper_average_order_of
        (AppliedModelingLib.Auction.singleMindedValueUpdate bids j value) =
      (before ++ base).orderedInsert
        (AppliedModelingLib.Auction.singleMindedAverageTieRel
          (AppliedModelingLib.Auction.singleMindedValueUpdate bids j value))
        j := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageOrderOf_valueUpdate_eq_orderedInsert_erase_of_split
      bids value horder

/--
The prefix state before `j`, after erasing accepted `j`, is unchanged by a
value-only update to `j`.
-/
theorem paper_average_value_update_prefix_state_erase_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder : paper_average_order_of bids = before ++ j :: base)
    (hjaccepted :
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        bids ∅ (before ++ [j])) :
    (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        bids ∅ (before ++ [j])).erase j =
      AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        (AppliedModelingLib.Auction.singleMindedValueUpdate bids j value)
        ∅ before := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageValueUpdate_prefix_state_erase_of_split
      bids value horder hjaccepted

/--
Concrete local suffix window for value-only updates around a displayed average
order split. It is the updated average-order insertion of `j` into the original
post-`j` suffix `base`.
-/
noncomputable abbrev paper_average_value_update_window
    {Bidder Item : Type*} [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (j : Bidder) (base : List Bidder) (value : ℝ) : List Bidder :=
  AppliedModelingLib.Auction.singleMindedAverageValueUpdateWindow bids j base value

/--
The concrete suffix window is average-descending, duplicate-free, contains `j`,
and erases back to the original suffix `base`.
-/
theorem paper_average_value_update_window_facts_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder : paper_average_order_of bids = before ++ j :: base) :
    let window := paper_average_value_update_window bids j base value
    paper_average_amount_descending
      (AppliedModelingLib.Auction.singleMindedValueUpdate bids j value) window ∧
      window.Nodup ∧
      window.erase j = base ∧
      j ∈ window := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageValueUpdateWindow_facts_of_split
      bids value horder

/--
For the concrete average-order suffix window, local acceptance of `j` after
erasing accepted `j` is equivalent to acceptance by the full updated greedy
mechanism.
-/
theorem paper_average_value_update_window_membership_iff_mechanism_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder} (value : ℝ)
    (horder : paper_average_order_of bids = before ++ j :: base)
    (hjaccepted :
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        bids ∅ (before ++ [j])) :
    j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
        (AppliedModelingLib.Auction.singleMindedValueUpdate bids j value)
        (paper_average_order_of
          (AppliedModelingLib.Auction.singleMindedValueUpdate bids j value)) ↔
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        (AppliedModelingLib.Auction.singleMindedValueUpdate bids j value)
        ((AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState bids ∅
          (before ++ [j])).erase j)
        (paper_average_value_update_window bids j base value) := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageValueUpdateWindow_membership_iff_mechanism_of_split
      bids value horder hjaccepted

/-- Paper-facing LOS02 greedy allocation from an explicit bid order. -/
abbrev paper_single_minded_greedy_allocation_from_order
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) :
    AppliedModelingLib.Auction.BundleAllocation Bidder Item :=
  AppliedModelingLib.Auction.singleMindedGreedyAllocationFromOrder bids order

/-- The paper's concrete average-order greedy accepted set. -/
noncomputable abbrev paper_average_greedy_accepted_set
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) :
    Finset Bidder :=
  paper_single_minded_greedy_accepted_from_order bids
    (paper_average_order_of bids)

/-- The paper's concrete average-order greedy allocation. -/
noncomputable abbrev paper_average_greedy_allocation
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) :
    AppliedModelingLib.Auction.BundleAllocation Bidder Item :=
  paper_single_minded_greedy_allocation_from_order bids
    (paper_average_order_of bids)

/-- The greedy accepted set has pairwise-disjoint desired bundles. -/
theorem paper_single_minded_greedy_accepted_pairwise_disjoint
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) :
    AppliedModelingLib.Auction.PairwiseDisjointDesired bids
      (paper_single_minded_greedy_accepted_from_order bids order) := by
  exact AppliedModelingLib.Auction.singleMindedGreedyAccepted_pairwiseDisjoint
    bids order

/-- The greedy fold preserves pairwise-disjoint accepted states. -/
theorem paper_single_minded_greedy_accepted_from_state_pairwise_disjoint
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (accepted : Finset Bidder) (order : List Bidder)
    (haccepted : AppliedModelingLib.Auction.PairwiseDisjointDesired bids accepted) :
    AppliedModelingLib.Auction.PairwiseDisjointDesired bids
      (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        bids accepted order) := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState_pairwiseDisjoint
      bids accepted order haccepted

/-- The greedy allocation is feasible when accepted desired bundles lie in `goods`. -/
theorem paper_single_minded_greedy_allocation_feasible
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) (goods : Finset Item)
    (hgoods : ∀ i,
      i ∈ paper_single_minded_greedy_accepted_from_order bids order →
        (bids i).desired ⊆ goods) :
    AppliedModelingLib.Auction.IsFeasibleBundleAllocation
      (paper_single_minded_greedy_allocation_from_order bids order) goods := by
  exact AppliedModelingLib.Auction.singleMindedGreedyAllocation_feasible
    bids order goods hgoods

/-- The concrete average-order greedy accepted set is pairwise disjoint. -/
theorem paper_average_greedy_accepted_pairwise_disjoint
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) :
    AppliedModelingLib.Auction.PairwiseDisjointDesired bids
      (paper_average_greedy_accepted_set bids) := by
  exact
    paper_single_minded_greedy_accepted_pairwise_disjoint
      bids (paper_average_order_of bids)

/-- The concrete average-order greedy allocation is feasible under the goods-scope premise. -/
theorem paper_average_greedy_allocation_feasible
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (goods : Finset Item)
    (hgoods : ∀ i,
      i ∈ paper_average_greedy_accepted_set bids → (bids i).desired ⊆ goods) :
    AppliedModelingLib.Auction.IsFeasibleBundleAllocation
      (paper_average_greedy_allocation bids) goods := by
  exact
    paper_single_minded_greedy_allocation_feasible
      bids (paper_average_order_of bids) goods hgoods

/--
Concrete Section 7 greedy allocation scheme for the paper's average-order list:
the accepted bids are conflict-free and the induced allocation is feasible under
the usual goods-scope premise.
-/
theorem paper_average_order_greedy_allocation_scheme
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (goods : Finset Item)
    (hgoods : ∀ i,
      i ∈ paper_average_greedy_accepted_set bids → (bids i).desired ⊆ goods) :
    AppliedModelingLib.Auction.PairwiseDisjointDesired bids
        (paper_average_greedy_accepted_set bids) ∧
      AppliedModelingLib.Auction.IsFeasibleBundleAllocation
        (paper_average_greedy_allocation bids) goods := by
  constructor
  · exact paper_average_greedy_accepted_pairwise_disjoint bids
  · exact paper_average_greedy_allocation_feasible bids goods hgoods

/--
LOS02 Theorem 9.6, source-shaped accepted-set form. Exactness is built into the
single-minded accepted-set mechanism model; Monotonicity, Participation, and
Critical imply truthful single-minded declarations on nonempty, nonnegative
types.
-/
theorem paper_theorem9_6_single_minded_truthful_of_axioms
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : AppliedModelingLib.Auction.SingleMindedAcceptedMechanism Bidder Item)
    (hmono :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.Monotonicity M)
    (hpart :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.Participation M)
    (C :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.CriticalValueCertificate
        M) :
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.TruthfulOn M
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  exact
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.truthfulOn_of_monotonicity_participation_critical
      M hmono hpart C

/--
LOS02 Theorem 9.6 with the source's infinite critical-value case. Exactness is
built into the single-minded accepted-set mechanism model; Monotonicity,
Participation, and the finite-or-infinite Critical axiom imply truthful
single-minded declarations on nonempty, nonnegative types.
-/
theorem paper_theorem9_6_single_minded_truthful_of_infinity_axioms
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : AppliedModelingLib.Auction.SingleMindedAcceptedMechanism Bidder Item)
    (hmono :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.Monotonicity M)
    (hpart :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.Participation M)
    (C :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.CriticalValueWithInfinityCertificate
        M) :
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.TruthfulOn M
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  exact
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.truthfulOn_of_monotonicity_participation_infinity_critical
      M hmono hpart C

/--
Domain-aware LOS02 Theorem 9.6. The critical-value clauses are only required on
nonempty, nonnegative single-minded reports, matching the source type space.
-/
theorem paper_theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : AppliedModelingLib.Auction.SingleMindedAcceptedMechanism Bidder Item)
    (hmono :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.MonotonicityOn M
        AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile)
    (hpart :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.Participation M)
    (C :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeCriticalValueWithInfinityCertificate
        M) :
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.TruthfulOn M
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  exact
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.truthfulOn_of_monotonicityOn_participation_nonnegative_infinity_critical
      M hmono hpart C

/--
Lemma 9.1 threshold existence on the source nonnegative domain: for a fixed
nonempty desired bundle, monotonicity gives either a finite nonnegative critical
value with strict below/above behavior, or an infinite branch where the bidder
never wins at any nonnegative declared value.
-/
theorem paper_lemma9_1_exists_nonnegative_critical_value_of_monotonicity
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : AppliedModelingLib.Auction.SingleMindedAcceptedMechanism Bidder Item)
    (hmono :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.MonotonicityOn M
        AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile)
    (reports : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (hreports :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile
        reports)
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
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.exists_nonnegative_critical_value_of_monotonicityOn
      M hmono reports hreports i s hs

/--
Lemma 9.2 denied-bidder utility case: under Participation, a denied
single-minded bidder with a nonempty true desired bundle receives zero utility.
-/
theorem paper_lemma9_2_denied_bidder_utility_eq_zero
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : AppliedModelingLib.Auction.SingleMindedAcceptedMechanism Bidder Item)
    (hpart :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.Participation M)
    (values reports : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (hvalues :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile
        values)
    {i : Bidder}
    (hdeny : i ∉ M.accepted reports) :
    M.utility values reports i = 0 := by
  exact
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.utility_eq_zero_of_denied_participation
      M hpart values reports (hvalues i).1 hdeny

/--
Lemma 9.3 truthful-utility case for the source nonnegative domain: truthful
reporting gives nonnegative utility under the nonnegative critical-value
certificate.
-/
theorem paper_lemma9_3_truthful_utility_nonnegative_of_nonnegative_infinity_certificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : AppliedModelingLib.Auction.SingleMindedAcceptedMechanism Bidder Item)
    (hpart :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.Participation M)
    (C :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeCriticalValueWithInfinityCertificate
        M)
    (values : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (hvalues :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile
        values)
    (i : Bidder) :
    0 ≤ M.utility values values i := by
  exact
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.utility_nonneg_truthful_of_nonnegative_infinity_certificate
      M hpart C values hvalues i

/--
Lemma 9.4 value-only deviation case: once the Theorem 9.6 axioms hold on the
nonnegative domain, changing only bidder `i`'s value cannot improve utility.
-/
theorem paper_lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : AppliedModelingLib.Auction.SingleMindedAcceptedMechanism Bidder Item)
    (hmono :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.MonotonicityOn M
        AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile)
    (hpart :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.Participation M)
    (C :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeCriticalValueWithInfinityCertificate
        M)
    (values : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (hvalues :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile
        values)
    (i : Bidder) {v' : ℝ} (hv' : 0 ≤ v') :
    M.utility values
        (Function.update values i
          { desired := (values i).desired, value := v' }) i ≤
      M.utility values values i := by
  have htruth :=
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.truthfulOn_of_monotonicityOn_participation_nonnegative_infinity_critical
      M hmono hpart C
  exact
    htruth values hvalues i { desired := (values i).desired, value := v' }
      (AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.nonnegativeNonemptyProfile_update
        values hvalues i (hvalues i).1 hv')

/--
Lemma 9.5 critical-payment monotonicity on the source domain: if a larger
desired set has finite critical value `pLarge`, then any nonempty smaller set
has finite critical value at most `pLarge`.
-/
theorem paper_lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : AppliedModelingLib.Auction.SingleMindedAcceptedMechanism Bidder Item)
    (hmono :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.MonotonicityOn M
        AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile)
    (C :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeCriticalValueWithInfinityCertificate
        M)
    (reports : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (hreports :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile
        reports)
    (i : Bidder) {sSmall sLarge : Finset Item} {pLarge : ℝ}
    (hsSmall : sSmall.Nonempty) (hsLarge : sLarge.Nonempty)
    (hsub : sSmall ⊆ sLarge)
    (hLarge : C.threshold reports i sLarge = some pLarge) :
    ∃ pSmall,
      C.threshold reports i sSmall = some pSmall ∧ pSmall ≤ pLarge := by
  exact
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeCriticalValueWithInfinityCertificate.finite_threshold_mono_of_monotone
      C hmono reports hreports i hsSmall hsLarge hsub hLarge

/-- LOS02 Definition 10.1 payment formula from the supplied `n(j)` function. -/
noncomputable abbrev paper_greedy_payment_from_next_denied
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (accepted : Finset Bidder)
    (nextDenied : Bidder → Option Bidder) (j : Bidder) : ℝ :=
  AppliedModelingLib.Auction.singleMindedGreedyPaymentFromNextDenied
    bids accepted nextDenied j

/-- Denied bids pay zero in the LOS02 greedy payment formula. -/
theorem paper_greedy_payment_eq_zero_of_denied
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (accepted : Finset Bidder)
    (nextDenied : Bidder → Option Bidder) {j : Bidder}
    (hj : j ∉ accepted) :
    paper_greedy_payment_from_next_denied bids accepted nextDenied j = 0 := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyPaymentFromNextDenied_eq_zero_of_denied
      bids accepted nextDenied hj

/-- Granted bids with no `n(j)` pay zero in the LOS02 greedy payment formula. -/
theorem paper_greedy_payment_eq_zero_of_no_next
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (accepted : Finset Bidder)
    (nextDenied : Bidder → Option Bidder) {j : Bidder}
    (hj : j ∈ accepted) (hnext : nextDenied j = none) :
    paper_greedy_payment_from_next_denied bids accepted nextDenied j = 0 := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyPaymentFromNextDenied_eq_zero_of_no_next
      bids accepted nextDenied hj hnext

/-- If `n(j)` exists, the LOS02 greedy payment is `|s_j| * c(n(j))`. -/
theorem paper_greedy_payment_eq_of_next
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (accepted : Finset Bidder)
    (nextDenied : Bidder → Option Bidder) {j n : Bidder}
    (hj : j ∈ accepted) (hnext : nextDenied j = some n) :
    paper_greedy_payment_from_next_denied bids accepted nextDenied j =
      (bids j).bundleSize * (bids n).averageAmountPerGood := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyPaymentFromNextDenied_eq_of_next
      bids accepted nextDenied hj hnext

/--
Source-local Definition 10.1 condition: at a particular greedy prefix state,
later bid `i` is denied because of accepted bid `j`.
-/
abbrev paper_greedy_denied_because_of_at_state
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedBefore : Finset Bidder) (j i : Bidder) : Prop :=
  AppliedModelingLib.Auction.SingleMindedGreedyDeniedBecauseOfAtState
    bids acceptedBefore j i

/--
Definition 10.1 `n(j)` search from a supplied greedy prefix state and a suffix
after `j`.
-/
abbrev paper_greedy_first_denied_because_of_from_state
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (suffix : List Bidder) (j : Bidder) : Option Bidder :=
  AppliedModelingLib.Auction.singleMindedGreedyFirstDeniedBecauseOfFromState
    bids acceptedBeforeSuffix suffix j

/--
Definition 10.1 `n(j)` search from an explicit split of the sorted order into
the bids before `j`, bid `j`, and the suffix after `j`.
-/
abbrev paper_greedy_next_denied_from_split
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (pre suffix : List Bidder) (j : Bidder) : Option Bidder :=
  AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromSplit bids pre suffix j

/-- Definition 10.1 `n(j)` search from the full sorted greedy order. -/
abbrev paper_greedy_next_denied_from_order
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) (j : Bidder) : Option Bidder :=
  AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromOrder bids order j

/-- Definition 10.1 payment rule computed from the full sorted greedy order. -/
noncomputable abbrev paper_greedy_payment_from_order
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) (j : Bidder) : ℝ :=
  AppliedModelingLib.Auction.singleMindedGreedyPaymentFromOrder bids order j

/-- The paper's concrete average-order Definition 10.1 payment rule. -/
noncomputable abbrev paper_average_greedy_payment
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (j : Bidder) : ℝ :=
  paper_greedy_payment_from_order bids (paper_average_order_of bids) j

/--
Full-order Definition 10.1 denied-because-of relation, packaged around the
first occurrence of `j` in the sorted greedy order.
-/
abbrev paper_greedy_denied_because_of_after_in_order
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) (j i : Bidder) : Prop :=
  AppliedModelingLib.Auction.SingleMindedGreedyDeniedBecauseOfAfterInOrderFromState
    bids ∅ order j i

/--
If the prefix-state `n(j)` search returns `n`, then `n` is in the later suffix
and satisfies the prefix-local denied-because-of condition at its turn.
-/
theorem paper_greedy_first_denied_because_of_from_state_some_spec
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (suffix : List Bidder) (j n : Bidder)
    (hnext :
      paper_greedy_first_denied_because_of_from_state
        bids acceptedBeforeSuffix suffix j = some n) :
    n ∈ suffix ∧
      AppliedModelingLib.Auction.SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids acceptedBeforeSuffix suffix j n := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyFirstDeniedBecauseOfFromState_some_spec
      bids acceptedBeforeSuffix suffix j n hnext

/--
If the prefix-state `n(j)` search returns `n`, then no earlier bid in a
duplicate-free displayed suffix is a prefix-local denied-because-of candidate.
-/
theorem paper_greedy_first_denied_because_of_from_state_some_no_earlier_candidate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (pre post : List Bidder) (j n m : Bidder)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      paper_greedy_first_denied_because_of_from_state
        bids acceptedBeforeSuffix (pre ++ n :: post) j = some n)
    (hm : m ∈ pre) :
    ¬ AppliedModelingLib.Auction.SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids acceptedBeforeSuffix (pre ++ n :: post) j m := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyFirstDeniedBecauseOfFromState_some_no_earlier_candidate
      bids acceptedBeforeSuffix pre post j n m hnodup hnext hm

/--
If the prefix-state `n(j)` search returns `n` at a displayed split, then `n`
is denied because of `j` exactly at the greedy state after processing the
displayed prefix.
-/
theorem paper_greedy_first_denied_because_of_from_state_some_at_split
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (pre post : List Bidder) (j n : Bidder)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      paper_greedy_first_denied_because_of_from_state
        bids acceptedBeforeSuffix (pre ++ n :: post) j = some n) :
    AppliedModelingLib.Auction.SingleMindedGreedyDeniedBecauseOfAtState bids
      (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        bids acceptedBeforeSuffix pre) j n := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyFirstDeniedBecauseOfFromState_some_at_split
      bids acceptedBeforeSuffix pre post j n hnodup hnext

/--
Critical-price progress for the `n(j) = n` case: before the first
denied-because-of candidate, erasing the blocker `j` preserves the greedy prefix
state, so the candidate `n` is accepted in the erased/lowered run.
-/
theorem paper_greedy_next_denied_accepted_after_erasing_blocker
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder) (pre post : List Bidder) {j n : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hjpre : j ∉ pre)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      paper_greedy_first_denied_because_of_from_state
        bids acceptedWithJ (pre ++ n :: post) j = some n) :
    n ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState bidsLow
      (acceptedWithJ.erase j) (pre ++ n :: post) := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState_mem_nextDenied_after_erasing_blocker
      acceptedWithJ pre post hsame hjpre hnodup hnext

/--
Critical-price progress for the `n(j) = n` case: after erasing `j`, the
candidate `n` is accepted already at its split point.
-/
theorem paper_greedy_next_denied_accepted_at_split_after_erasing_blocker
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder) (pre post : List Bidder) {j n : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hjpre : j ∉ pre)
    (hnodup : (pre ++ n :: post).Nodup)
    (hnext :
      paper_greedy_first_denied_because_of_from_state
        bids acceptedWithJ (pre ++ n :: post) j = some n) :
    n ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState bidsLow
      (acceptedWithJ.erase j) (pre ++ [n]) := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState_mem_nextDenied_after_erasing_blocker_at_split
      acceptedWithJ pre post hsame hjpre hnodup hnext

/--
Fixed-order below-threshold skeleton for the `n(j) = n` case: if the
erased/lowered order places `j` after its conflicting `n(j)` blocker, then `j`
is rejected in that lowered run.
-/
theorem paper_greedy_next_denied_rejected_after_erasing_blocker
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsLow : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder)
    (pre nextPost between tail : List Bidder) {j n : Bidder}
    (hsame : ∀ k, k ≠ j → bidsLow k = bids k)
    (hjpre : j ∉ pre)
    (hjbetween : j ∉ between)
    (hjtail : j ∉ tail)
    (hnodup : (pre ++ n :: nextPost).Nodup)
    (hnext :
      paper_greedy_first_denied_because_of_from_state
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n)
    (hconflict : AppliedModelingLib.Auction.SingleMindedBidsConflict bidsLow j n) :
    j ∉ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState bidsLow
      (acceptedWithJ.erase j) (((pre ++ [n]) ++ between) ++ j :: tail) := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState_rejects_nextDenied_after_erasing_blocker
      acceptedWithJ pre nextPost between tail hsame hjpre hjbetween hjtail
      hnodup hnext hconflict

/--
Value-update below-threshold skeleton for the `n(j) = n` case: if the
value-lowered order places `j` after its original `n(j)` blocker, then `j` is
rejected. The theorem derives the preserved conflict from the value-only update.
-/
theorem paper_greedy_next_denied_rejected_after_value_update
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost between tail : List Bidder) {j n : Bidder} (value : ℝ)
    (hjpre : j ∉ pre)
    (hjbetween : j ∉ between)
    (hjtail : j ∉ tail)
    (hnodup : (pre ++ n :: nextPost).Nodup)
    (hnext :
      paper_greedy_first_denied_because_of_from_state
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n) :
    j ∉ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
      (paper_single_minded_value_update bids j value) (acceptedWithJ.erase j)
      (((pre ++ [n]) ++ between) ++ j :: tail) := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState_rejects_nextDenied_after_value_update
      bids acceptedWithJ pre nextPost between tail value hjpre hjbetween
      hjtail hnodup hnext

/--
Above-threshold structural acceptance: if the raised run reaches `j` before any
denied-because-of candidate, then erasing `j` from the original prefix state and
rerunning accepts `j`.
-/
theorem paper_greedy_accepts_after_erasing_blocker_of_no_candidate_prefix
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsHigh : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    (acceptedWithJ : Finset Bidder) (pref tail : List Bidder) {j : Bidder}
    (hsame : ∀ k, k ≠ j → bidsHigh k = bids k)
    (hjdesired : (bidsHigh j).desired = (bids j).desired)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : AppliedModelingLib.Auction.PairwiseDisjointDesired bids acceptedWithJ)
    (hjpref : j ∉ pref)
    (hno :
      ∀ i, i ∈ pref →
        ¬ AppliedModelingLib.Auction.SingleMindedGreedyDeniedBecauseOfInSuffixFromState
          bids acceptedWithJ pref j i) :
    j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState bidsHigh
      (acceptedWithJ.erase j) (pref ++ j :: tail) := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState_accepts_after_erasing_blocker_of_no_candidate_prefix
      acceptedWithJ pref tail hsame hjdesired hjaccepted hpairwise hjpref hno

/--
Value-update above-threshold skeleton: if the value-raised run reaches `j`
before any original denied-because-of candidate, then erasing `j` from the
original accepted prefix and rerunning accepts `j`.
-/
theorem paper_greedy_accepts_after_value_update_of_no_candidate_prefix
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder) (pref tail : List Bidder) {j : Bidder}
    (value : ℝ)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : AppliedModelingLib.Auction.PairwiseDisjointDesired bids acceptedWithJ)
    (hjpref : j ∉ pref)
    (hno :
      ∀ i, i ∈ pref →
        ¬ AppliedModelingLib.Auction.SingleMindedGreedyDeniedBecauseOfInSuffixFromState
          bids acceptedWithJ pref j i) :
    j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
      (paper_single_minded_value_update bids j value) (acceptedWithJ.erase j)
      (pref ++ j :: tail) := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState_accepts_after_value_update_of_no_candidate_prefix
      bids acceptedWithJ pref tail value hjaccepted hpairwise hjpref hno

/--
Finite critical-window composition for the `n(j) = n` case. Once the changed
average-descending orders are certified to place a lower value after `n` and a
higher value before any original `n(j)` candidate, the corresponding value-only
updates reject below the Definition 10.1 payment and accept above it.
-/
theorem paper_greedy_value_update_local_critical_window
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost lowOrder highOrder : List Bidder) {j n : Bidder}
    (lowValue highValue : ℝ)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : AppliedModelingLib.Auction.PairwiseDisjointDesired bids acceptedWithJ)
    (hjpre : j ∉ pre)
    (hnodup : (pre ++ n :: nextPost).Nodup)
    (hnext :
      paper_greedy_first_denied_because_of_from_state
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
      j ∉ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        (paper_single_minded_value_update bids j lowValue)
        (acceptedWithJ.erase j) lowOrder) ∧
    ((bids j).bundleSize * (bids n).averageAmountPerGood < highValue →
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        (paper_single_minded_value_update bids j highValue)
        (acceptedWithJ.erase j) highOrder) := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyValueUpdate_local_critical_window
      bids acceptedWithJ pre nextPost lowOrder highOrder lowValue highValue
      hjaccepted hpairwise hjpre hnodup hnext hlow_reposition
      hhigh_reposition

/--
If the prefix-state `n(j)` search returns none, then no bid in the suffix is a
prefix-local denied-because-of candidate for `j`.
-/
theorem paper_greedy_first_denied_because_of_from_state_none_no_candidate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedBeforeSuffix : Finset Bidder)
    (suffix : List Bidder) (j : Bidder)
    (hnext :
      paper_greedy_first_denied_because_of_from_state
        bids acceptedBeforeSuffix suffix j = none) :
    ∀ n, n ∈ suffix →
      ¬ AppliedModelingLib.Auction.SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids acceptedBeforeSuffix suffix j n := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyFirstDeniedBecauseOfFromState_none_no_candidate
      bids acceptedBeforeSuffix suffix j hnext

/--
If the split-order `n(j)` search returns `n`, then `n` occurs after `j` in the
given split and is denied because of `j` in the prefix-local sense.
-/
theorem paper_greedy_next_denied_from_split_some_spec
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (pre suffix : List Bidder) (j n : Bidder)
    (hnext :
      paper_greedy_next_denied_from_split bids pre suffix j = some n) :
    n ∈ suffix ∧
      AppliedModelingLib.Auction.SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids
        (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
          bids ∅ (pre ++ [j]))
        suffix j n := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromSplit_some_spec
      bids pre suffix j n hnext

/-- Any returned split-order `n(j)` follows `j` in the supplied sorted order. -/
theorem paper_greedy_next_denied_from_split_precedes
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (pre suffix : List Bidder) (j n : Bidder)
    (hnext :
      paper_greedy_next_denied_from_split bids pre suffix j = some n) :
    AppliedModelingLib.Auction.SingleMindedPrecedes (pre ++ j :: suffix) j n := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromSplit_precedes
      bids pre suffix j n hnext

/--
In an average-descending order, a strict lower average prevents a bid from
preceding the higher-average bid.
-/
theorem paper_average_amount_descending_not_precedes_of_lt
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    {order : List Bidder} {earlier later : Bidder}
    (hsorted : paper_average_amount_descending bids order)
    (hlt :
      paper_average_amount_per_good (bids earlier) <
        paper_average_amount_per_good (bids later)) :
    ¬ AppliedModelingLib.Auction.SingleMindedPrecedes order earlier later := by
  exact
    AppliedModelingLib.Auction.SingleMindedAverageAmountDescending.not_precedes_of_average_lt
      hsorted hlt

/--
In a duplicate-free average-descending order, a strict lower average gives a
displayed split with the higher-average bid before the lower-average bid, and
the lower-average bid absent from the surrounding pieces.
-/
theorem paper_average_amount_descending_exists_split_nodup_of_lt
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    {order : List Bidder} {higher lower : Bidder}
    (hsorted : paper_average_amount_descending bids order)
    (hnodup : order.Nodup)
    (hhigher : higher ∈ order) (hlower : lower ∈ order)
    (hlt :
      paper_average_amount_per_good (bids lower) <
        paper_average_amount_per_good (bids higher)) :
    ∃ pre between tail,
      order = ((pre ++ [higher]) ++ between) ++ lower :: tail ∧
        lower ∉ pre ∧ lower ∉ between ∧ lower ∉ tail := by
  exact
    AppliedModelingLib.Auction.SingleMindedAverageAmountDescending.exists_split_nodup_of_average_lt
      hsorted hnodup hhigher hlower hlt

/--
In an average-descending order, a bid below `|s_j| * c(n)` must appear after
`n` whenever both bids occur in the order.
-/
theorem paper_average_amount_descending_precedes_of_value_lt_payment
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    {order : List Bidder} {j n : Bidder}
    (hsorted : paper_average_amount_descending bids order)
    (hj : j ∈ order) (hn : n ∈ order) (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).value <
        (bids j).bundleSize * (bids n).averageAmountPerGood) :
    AppliedModelingLib.Auction.SingleMindedPrecedes order n j := by
  exact
    AppliedModelingLib.Auction.SingleMindedAverageAmountDescending.precedes_of_value_lt_bundleSize_mul_average
      hsorted hj hn hjn hj_nonempty hlt

/--
In an average-descending order, a bid above `|s_j| * c(n)` must appear before
`n` whenever both bids occur in the order.
-/
theorem paper_average_amount_descending_precedes_of_payment_lt_value
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    {order : List Bidder} {j n : Bidder}
    (hsorted : paper_average_amount_descending bids order)
    (hj : j ∈ order) (hn : n ∈ order) (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).bundleSize * (bids n).averageAmountPerGood <
        (bids j).value) :
    AppliedModelingLib.Auction.SingleMindedPrecedes order j n := by
  exact
    AppliedModelingLib.Auction.SingleMindedAverageAmountDescending.precedes_of_bundleSize_mul_average_lt_value
      hsorted hj hn hjn hj_nonempty hlt

/--
For a value-only perturbation below `|s_j| * c(n)`, any duplicate-free
average-descending updated order places `n` before `j`.
-/
theorem paper_average_amount_descending_exists_split_nodup_of_value_update_lt_payment
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    {orderUpdated : List Bidder} {j n : Bidder} (value : ℝ)
    (hsorted :
      paper_average_amount_descending
        (paper_single_minded_value_update bids j value) orderUpdated)
    (hnodup : orderUpdated.Nodup)
    (hj : j ∈ orderUpdated) (hn : n ∈ orderUpdated)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      value < (bids j).bundleSize * (bids n).averageAmountPerGood) :
    ∃ pre between tail,
      orderUpdated = ((pre ++ [n]) ++ between) ++ j :: tail ∧
        j ∉ pre ∧ j ∉ between ∧ j ∉ tail := by
  exact
    AppliedModelingLib.Auction.SingleMindedAverageAmountDescending.exists_split_nodup_of_value_update_lt_payment
      value hsorted hnodup hj hn hjn hj_nonempty hlt

/--
For a value-only perturbation above `|s_j| * c(n)`, any duplicate-free
average-descending updated order places `j` before `n`.
-/
theorem paper_average_amount_descending_exists_split_nodup_of_payment_lt_value_update
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    {orderUpdated : List Bidder} {j n : Bidder} (value : ℝ)
    (hsorted :
      paper_average_amount_descending
        (paper_single_minded_value_update bids j value) orderUpdated)
    (hnodup : orderUpdated.Nodup)
    (hj : j ∈ orderUpdated) (hn : n ∈ orderUpdated)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).bundleSize * (bids n).averageAmountPerGood < value) :
    ∃ pre between tail,
      orderUpdated = ((pre ++ [j]) ++ between) ++ n :: tail ∧
        n ∉ pre ∧ n ∉ between ∧ n ∉ tail := by
  exact
    AppliedModelingLib.Auction.SingleMindedAverageAmountDescending.exists_split_nodup_of_payment_lt_value_update
      value hsorted hnodup hj hn hjn hj_nonempty hlt

/--
Below-threshold repositioning with explicit erase-stability of the non-`j`
order: the updated sorted order has the original `pre ++ n :: nextPost` after
erasing `j`, so `j` appears after that original `n`.
-/
theorem paper_average_amount_descending_exists_reposition_of_value_update_lt_payment_and_erase
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    {orderUpdated pre nextPost : List Bidder} {j n : Bidder} (value : ℝ)
    (hsorted :
      paper_average_amount_descending
        (paper_single_minded_value_update bids j value) orderUpdated)
    (hnodup : orderUpdated.Nodup)
    (hj : j ∈ orderUpdated) (hn : n ∈ orderUpdated)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      value < (bids j).bundleSize * (bids n).averageAmountPerGood)
    (herase : orderUpdated.erase j = pre ++ n :: nextPost) :
    ∃ between tail,
      orderUpdated = (((pre ++ [n]) ++ between) ++ j :: tail) ∧
        j ∉ between ∧ j ∉ tail := by
  exact
    AppliedModelingLib.Auction.SingleMindedAverageAmountDescending.exists_reposition_of_value_update_lt_payment_and_erase
      value hsorted hnodup hj hn hjn hj_nonempty hlt herase

/--
Above-threshold repositioning with explicit erase-stability of the non-`j`
order: the updated sorted order reaches `j` before the original `n(j)` point.
-/
theorem paper_average_amount_descending_exists_reposition_of_payment_lt_value_update_and_erase
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    {orderUpdated pre nextPost : List Bidder} {j n : Bidder} (value : ℝ)
    (hsorted :
      paper_average_amount_descending
        (paper_single_minded_value_update bids j value) orderUpdated)
    (hnodup : orderUpdated.Nodup)
    (hj : j ∈ orderUpdated) (hn : n ∈ orderUpdated)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hlt :
      (bids j).bundleSize * (bids n).averageAmountPerGood < value)
    (herase : orderUpdated.erase j = pre ++ n :: nextPost) :
    ∃ pref rest tail,
      pre = pref ++ rest ∧ orderUpdated = pref ++ j :: tail := by
  exact
    AppliedModelingLib.Auction.SingleMindedAverageAmountDescending.exists_reposition_of_payment_lt_value_update_and_erase
      value hsorted hnodup hj hn hjn hj_nonempty hlt herase

/--
Source-shaped finite critical-window endpoint for the `n(j) = n` case, assuming
the low/high value-updated sorted orders preserve the non-`j` order by erasure.
-/
theorem paper_greedy_value_update_local_critical_window_of_sorted_erase
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost lowOrder highOrder : List Bidder) {j n : Bidder}
    (lowValue highValue : ℝ)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : AppliedModelingLib.Auction.PairwiseDisjointDesired bids acceptedWithJ)
    (hjpre : j ∉ pre)
    (hnodup_original : (pre ++ n :: nextPost).Nodup)
    (hnext :
      paper_greedy_first_denied_because_of_from_state
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n)
    (hlow_sorted :
      paper_average_amount_descending
        (paper_single_minded_value_update bids j lowValue) lowOrder)
    (hhigh_sorted :
      paper_average_amount_descending
        (paper_single_minded_value_update bids j highValue) highOrder)
    (hlow_nodup : lowOrder.Nodup)
    (hhigh_nodup : highOrder.Nodup)
    (hlow_erase : lowOrder.erase j = pre ++ n :: nextPost)
    (hhigh_erase : highOrder.erase j = pre ++ n :: nextPost)
    (hj_low : j ∈ lowOrder) (hj_high : j ∈ highOrder)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty) :
    (lowValue < (bids j).bundleSize * (bids n).averageAmountPerGood →
      j ∉ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        (paper_single_minded_value_update bids j lowValue)
        (acceptedWithJ.erase j) lowOrder) ∧
    ((bids j).bundleSize * (bids n).averageAmountPerGood < highValue →
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        (paper_single_minded_value_update bids j highValue)
        (acceptedWithJ.erase j) highOrder) := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyValueUpdate_local_critical_window_of_sorted_erase
      bids acceptedWithJ pre nextPost lowOrder highOrder lowValue highValue
      hjaccepted hpairwise hjpre hnodup_original hnext hlow_sorted
      hhigh_sorted hlow_nodup hhigh_nodup hlow_erase hhigh_erase
      hj_low hj_high hjn hj_nonempty

/--
Monotonicity support: if a strengthened report for `j` reaches `j` after a
prefix that had no original conflict with `j`, then the greedy run accepts `j`.
-/
theorem paper_greedy_accepts_after_shrink_of_no_prefix_conflict
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsStrong : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    (acceptedBefore : Finset Bidder) (pref tail : List Bidder) {j : Bidder}
    (hsame : ∀ k, k ≠ j → bidsStrong k = bids k)
    (hjdesired_subset : (bidsStrong j).desired ⊆ (bids j).desired)
    (hjaccepted : j ∉ acceptedBefore)
    (hjpref : j ∉ pref)
    (hno :
      ¬ (AppliedModelingLib.Auction.singleMindedGreedyConflictingAccepted
        bids
        (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
          bids acceptedBefore pref) j).Nonempty) :
    j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
      bidsStrong acceptedBefore (pref ++ j :: tail) := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState_accepts_after_shrink_of_no_prefix_conflict
      acceptedBefore pref tail hsame hjdesired_subset hjaccepted hjpref hno

/--
Monotonicity support in the source proof shape: if strengthening `j` moves it
earlier from `(pref ++ rest) ++ j :: suffix` to `pref ++ j :: tail`, and the
original run accepted `j`, then the strengthened run accepts `j`.
-/
theorem paper_greedy_accepts_after_shrink_of_original_accepts_before_move
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids bidsStrong : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    (acceptedBefore : Finset Bidder)
    (pref rest suffix tail : List Bidder) {j : Bidder}
    (hsame : ∀ k, k ≠ j → bidsStrong k = bids k)
    (hjdesired_subset : (bidsStrong j).desired ⊆ (bids j).desired)
    (hjaccepted : j ∉ acceptedBefore)
    (hjpref : j ∉ pref)
    (hjrest : j ∉ rest)
    (hjsuffix : j ∉ suffix)
    (hacc :
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        bids acceptedBefore ((pref ++ rest) ++ j :: suffix)) :
    j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
      bidsStrong acceptedBefore (pref ++ j :: tail) := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState_accepts_after_shrink_of_original_accepts_before_move
      acceptedBefore pref rest suffix tail hsame hjdesired_subset hjaccepted
      hjpref hjrest hjsuffix hacc

/--
The greedy accepted-set mechanism is monotone once the paper's sorted order rule
certifies that every accepted strengthened report moves `j` weakly earlier while
preserving the relative order of the bids before the new occurrence of `j`.
-/
theorem paper_greedy_accepted_mechanism_monotonicity_of_order_moves_earlier
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder)
    (hmove :
      ∀ bids j s v,
        j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
          bids (orderOf bids) →
          s ⊆ (bids j).desired →
            (bids j).value ≤ v →
              ∃ pref rest suffix tail,
                orderOf bids = (pref ++ rest) ++ j :: suffix ∧
                  orderOf (Function.update bids j { desired := s, value := v }) =
                    pref ++ j :: tail ∧
                  j ∉ pref ∧ j ∉ rest ∧ j ∉ suffix) :
    (AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf).Monotonicity := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf_monotonicity_of_order_moves_earlier
      orderOf hmove

/--
Local sorted-window package for the finite `n(j) = n` branch of the greedy
critical-price proof.
-/
abbrev paper_sorted_erase_critical_window
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder)
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder) (j : Bidder)
    (base : List Bidder) (windowOrder : ℝ → List Bidder) : Prop :=
  AppliedModelingLib.Auction.SingleMindedSortedEraseCriticalWindow
    orderOf bids acceptedWithJ j base windowOrder

/--
Full-order sorted-window package for instantiating the source Section 10
critical-price branches from a split of the original greedy order around `j`.
-/
abbrev paper_source_sorted_erase_critical_window
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder)
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder) (j : Bidder)
    (base : List Bidder) (windowOrder : ℝ → List Bidder) :=
  AppliedModelingLib.Auction.SingleMindedFullOrderSortedEraseCriticalWindow
    orderOf bids acceptedWithJ j base windowOrder

/--
The concrete average-order suffix window supplies the sorted/duplicate-free/
erase-stable local window fields. The only remaining assumptions are the two
bridges from the local suffix rerun back to the full updated greedy mechanism.
-/
theorem paper_average_value_update_window_sorted_erase_critical_window_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    {before base : List Bidder} {j : Bidder}
    (horder : paper_average_order_of bids = before ++ j :: base)
    (hreject : ∀ v,
      j ∉ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
          (AppliedModelingLib.Auction.singleMindedValueUpdate bids j v)
          (acceptedWithJ.erase j)
          (paper_average_value_update_window bids j base v) →
        j ∉ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
          (AppliedModelingLib.Auction.singleMindedValueUpdate bids j v)
          (paper_average_order_of
            (AppliedModelingLib.Auction.singleMindedValueUpdate bids j v)))
    (haccept : ∀ v,
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
          (AppliedModelingLib.Auction.singleMindedValueUpdate bids j v)
          (acceptedWithJ.erase j)
          (paper_average_value_update_window bids j base v) →
        j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
          (AppliedModelingLib.Auction.singleMindedValueUpdate bids j v)
          (paper_average_order_of
            (AppliedModelingLib.Auction.singleMindedValueUpdate bids j v))) :
    paper_sorted_erase_critical_window
      paper_average_order_of bids acceptedWithJ j base
      (paper_average_value_update_window bids j base) := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageValueUpdateWindow_sortedEraseCriticalWindow_of_split
      bids acceptedWithJ horder hreject haccept

/--
Source-window constructor for the concrete average-order suffix window. It
packages the original split, accepted prefix, and local suffix-window facts; the
full-mechanism accept/reject bridge remains explicit.
-/
noncomputable def paper_average_value_update_window_source_sorted_erase_critical_window_of_split
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder}
    (horder : paper_average_order_of bids = before ++ j :: base)
    (hjaccepted :
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        bids ∅ (before ++ [j]))
    (hreject : ∀ v,
      j ∉ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
          (AppliedModelingLib.Auction.singleMindedValueUpdate bids j v)
          ((AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState bids ∅
            (before ++ [j])).erase j)
          (paper_average_value_update_window bids j base v) →
        j ∉ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
          (AppliedModelingLib.Auction.singleMindedValueUpdate bids j v)
          (paper_average_order_of
            (AppliedModelingLib.Auction.singleMindedValueUpdate bids j v)))
    (haccept : ∀ v,
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
          (AppliedModelingLib.Auction.singleMindedValueUpdate bids j v)
          ((AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState bids ∅
            (before ++ [j])).erase j)
          (paper_average_value_update_window bids j base v) →
        j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
          (AppliedModelingLib.Auction.singleMindedValueUpdate bids j v)
          (paper_average_order_of
            (AppliedModelingLib.Auction.singleMindedValueUpdate bids j v))) :
    paper_source_sorted_erase_critical_window
      paper_average_order_of bids
      (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState bids ∅
        (before ++ [j]))
      j base (paper_average_value_update_window bids j base) :=
  AppliedModelingLib.Auction.singleMindedAverageValueUpdateWindow_fullOrderSortedEraseCriticalWindow_of_split
    bids horder hjaccepted hreject haccept

/--
Concrete average-order source-window constructor with the local-to-global bridge
discharged by the ordered-insertion suffix-window equivalence.
-/
theorem paper_average_value_update_window_sorted_erase_critical_window_of_split_data
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder}
    (horder : paper_average_order_of bids = before ++ j :: base)
    (hjaccepted :
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        bids ∅ (before ++ [j])) :
    paper_sorted_erase_critical_window
      paper_average_order_of bids
      (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        bids ∅ (before ++ [j]))
      j base (paper_average_value_update_window bids j base) := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageValueUpdateWindow_sortedEraseCriticalWindow_of_split_data
      bids horder hjaccepted

/--
Concrete average-order source-window package for the split around an accepted
bid `j`, with no remaining bridge assumptions.
-/
noncomputable def paper_average_value_update_window_source_sorted_erase_critical_window_of_split_data
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    {before base : List Bidder} {j : Bidder}
    (horder : paper_average_order_of bids = before ++ j :: base)
    (hjaccepted :
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        bids ∅ (before ++ [j])) :
    paper_source_sorted_erase_critical_window
      paper_average_order_of bids
      (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
        bids ∅ (before ++ [j]))
      j base (paper_average_value_update_window bids j base) :=
  AppliedModelingLib.Auction.singleMindedAverageValueUpdateWindow_fullOrderSortedEraseCriticalWindow_of_split_data
    bids horder hjaccepted

/--
Finite accepted-branch theorem for Definition 10.1: for an accepted bid with
`n(j) = n`, a sorted erase-stable local window proves rejection below
`|s_j| * c(n)`, acceptance above it, and equality of the actual greedy payment.
-/
theorem paper_greedy_accepted_mechanism_finite_branch_of_next_denied_some
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder)
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost : List Bidder) {j n : Bidder}
    (windowOrder : ℝ → List Bidder)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : AppliedModelingLib.Auction.PairwiseDisjointDesired bids acceptedWithJ)
    (hjpre : j ∉ pre)
    (hnodup_original : (pre ++ n :: nextPost).Nodup)
    (hnext_state :
      paper_greedy_first_denied_because_of_from_state
        bids acceptedWithJ (pre ++ n :: nextPost) j = some n)
    (hwindow :
      paper_sorted_erase_critical_window orderOf bids acceptedWithJ j
        (pre ++ n :: nextPost) windowOrder)
    (hjn : j ≠ n)
    (hj_nonempty : (bids j).desired.Nonempty)
    (hj_final :
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
        bids (orderOf bids))
    (hnext_order :
      paper_greedy_next_denied_from_order bids (orderOf bids) j = some n) :
    let M := AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf
    let p := (bids j).bundleSize * (bids n).averageAmountPerGood
    (∀ v, v < p →
      j ∉ M.accepted (paper_single_minded_value_update bids j v)) ∧
    (∀ v, p < v →
      j ∈ M.accepted (paper_single_minded_value_update bids j v)) ∧
    M.payment bids j = p := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanism_finite_branch_of_nextDenied_some
      orderOf bids acceptedWithJ pre nextPost windowOrder hjaccepted
      hpairwise hjpre hnodup_original hnext_state hwindow hjn
      hj_nonempty hj_final hnext_order

/--
No-next accepted branch for Definition 10.1 over the nonnegative value domain:
if the local `n(j)` search returns none, the zero payment is the critical
threshold. Nonnegative values below zero are impossible, while every positive
value is accepted from the erase-stable no-candidate window.
-/
theorem paper_greedy_accepted_mechanism_zero_branch_of_next_denied_none
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder)
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (base : List Bidder) {j : Bidder}
    (windowOrder : ℝ → List Bidder)
    (hjaccepted : j ∈ acceptedWithJ)
    (hpairwise : AppliedModelingLib.Auction.PairwiseDisjointDesired bids acceptedWithJ)
    (hnext_state :
      paper_greedy_first_denied_because_of_from_state
        bids acceptedWithJ base j = none)
    (hwindow :
      paper_sorted_erase_critical_window orderOf bids acceptedWithJ j
        base windowOrder)
    (hj_final :
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
        bids (orderOf bids))
    (hnext_order :
      paper_greedy_next_denied_from_order bids (orderOf bids) j = none) :
    let M := AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf
    (∀ v, 0 ≤ v → v < 0 →
      j ∉ M.accepted (paper_single_minded_value_update bids j v)) ∧
    (∀ v, 0 < v →
      j ∈ M.accepted (paper_single_minded_value_update bids j v)) ∧
    M.payment bids j = 0 := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanism_zero_branch_of_nextDenied_none
      orderOf bids acceptedWithJ base windowOrder hjaccepted hpairwise
      hnext_state hwindow hj_final hnext_order

/--
Source-window finite branch for Definition 10.1: a full-order split around `j`
derives the local finite critical branch from the full-order `n(j)=n` search.
-/
theorem paper_greedy_accepted_mechanism_finite_branch_of_sorted_window
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder)
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (pre nextPost : List Bidder) {j n : Bidder}
    (windowOrder : ℝ → List Bidder)
    (hsource :
      paper_source_sorted_erase_critical_window orderOf bids acceptedWithJ j
        (pre ++ n :: nextPost) windowOrder)
    (hnext_order :
      paper_greedy_next_denied_from_order bids (orderOf bids) j = some n)
    (hj_nonempty : (bids j).desired.Nonempty) :
    let M := AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf
    let p := (bids j).bundleSize * (bids n).averageAmountPerGood
    (∀ v, v < p →
      j ∉ M.accepted (paper_single_minded_value_update bids j v)) ∧
    (∀ v, p < v →
      j ∈ M.accepted (paper_single_minded_value_update bids j v)) ∧
    M.payment bids j = p := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanism_finite_branch_of_sorted_window
      orderOf bids acceptedWithJ pre nextPost windowOrder hsource
      hnext_order hj_nonempty

/--
Source-window zero branch for Definition 10.1: a full-order split around `j`
with no next denied bid gives zero payment and acceptance at every positive
value over the nonnegative value domain.
-/
theorem paper_greedy_accepted_mechanism_zero_branch_of_sorted_window
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder)
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (acceptedWithJ : Finset Bidder)
    (base : List Bidder) {j : Bidder}
    (windowOrder : ℝ → List Bidder)
    (hsource :
      paper_source_sorted_erase_critical_window orderOf bids acceptedWithJ j
        base windowOrder)
    (hnext_order :
      paper_greedy_next_denied_from_order bids (orderOf bids) j = none) :
    let M := AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf
    (∀ v, 0 ≤ v → v < 0 →
      j ∉ M.accepted (paper_single_minded_value_update bids j v)) ∧
    (∀ v, 0 < v →
      j ∈ M.accepted (paper_single_minded_value_update bids j v)) ∧
    M.payment bids j = 0 := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanism_zero_branch_of_sorted_window
      orderOf bids acceptedWithJ base windowOrder hsource hnext_order

/--
Source-window data for the accepted-bid critical branch of Definition 10.1. It
provides the full-order sorted-window package for whichever case the `n(j)`
search returns.
-/
abbrev paper_source_critical_branch_windows
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder)
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) (j : Bidder) :=
  AppliedModelingLib.Auction.SingleMindedCriticalBranchWindows orderOf bids j

/--
For any bidder accepted by the concrete average-order greedy run, the average
order supplies the source critical-branch windows for both the finite and
no-next cases.
-/
noncomputable def paper_average_source_critical_branch_windows_of_accepted
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    {j : Bidder}
    (hjacc :
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
        bids (paper_average_order_of bids)) :
    paper_source_critical_branch_windows paper_average_order_of bids j :=
  AppliedModelingLib.Auction.singleMindedAverageCriticalBranchWindows_of_accepted
    bids hjacc

/--
Source branch data sufficient to build the nonnegative-domain critical-value
certificate for the LOS02 greedy accepted-set mechanism.
-/
abbrev paper_nonnegative_critical_source_branch_data
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder) :=
  AppliedModelingLib.Auction.SingleMindedNonnegativeCriticalBranchData orderOf

/--
Accepted-bid criticality for the full greedy mechanism: the actual Definition
10.1 payment is the critical threshold for changing only the accepted bidder's
value on the nonnegative report domain, assuming source windows for the finite
and no-next branches.
-/
theorem paper_greedy_accepted_mechanism_payment_critical_of_branch_windows
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder)
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) {j : Bidder}
    (hwindows : paper_source_critical_branch_windows orderOf bids j)
    (hj_nonempty : (bids j).desired.Nonempty) :
    let M := AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) orderOf
    (∀ v, 0 ≤ v → v < M.payment bids j →
      j ∉ M.accepted (paper_single_minded_value_update bids j v)) ∧
    (∀ v, M.payment bids j < v →
      j ∈ M.accepted (paper_single_minded_value_update bids j v)) := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanism_payment_critical_of_branch_windows
      orderOf bids hwindows hj_nonempty

/--
Concrete average-order accepted-bid criticality: if `j` is accepted by the
average-order greedy run, its Definition 10.1 payment is the critical threshold
for value-only deviations on the nonnegative domain.
-/
theorem paper_average_greedy_accepted_mechanism_payment_critical_of_accepted
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) {j : Bidder}
    (hjacc :
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
        bids (paper_average_order_of bids))
    (hj_nonempty : (bids j).desired.Nonempty) :
    let M := AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item) paper_average_order_of
    (∀ v, 0 ≤ v → v < M.payment bids j →
      j ∉ M.accepted (paper_single_minded_value_update bids j v)) ∧
    (∀ v, M.payment bids j < v →
      j ∈ M.accepted (paper_single_minded_value_update bids j v)) := by
  exact
    paper_greedy_accepted_mechanism_payment_critical_of_branch_windows
      paper_average_order_of bids
      (paper_average_source_critical_branch_windows_of_accepted bids hjacc)
      hj_nonempty

/--
Candidate all-bidder critical threshold for the concrete average-order greedy
mechanism, defined by selecting an accepted nonnegative value-only branch when
one exists. This closes the definitional `none` and `some branch` plumbing; the
final source-data certificate still needs a canonical selector for own-value
independence and accepted-payment equality.
-/
noncomputable abbrev paper_average_greedy_critical_threshold
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (reports : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (i : Bidder) (s : AppliedModelingLib.Auction.Bundle Item) : Option ℝ :=
  AppliedModelingLib.Auction.singleMindedAverageGreedyCriticalThreshold
    reports i s

/--
If the candidate average-order threshold has no accepted nonnegative
value-only branch, every nonnegative value-only report for the target bundle is
denied. This discharges the `none_denied` shape for that candidate threshold.
-/
theorem paper_average_greedy_critical_threshold_none_denied
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (reports : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (i : Bidder) (s : AppliedModelingLib.Auction.Bundle Item)
    (hthreshold :
      paper_average_greedy_critical_threshold reports i s = none) :
    ∀ v, 0 ≤ v →
      i ∉ (AppliedModelingLib.Auction.singleMindedAverageGreedyAcceptedMechanism
        (Bidder := Bidder) (Item := Item)).accepted
          (Function.update reports i { desired := s, value := v }) := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageGreedyCriticalThreshold_none_denied
      reports i s hthreshold

/--
Whenever the candidate average-order threshold returns a finite price, the
chosen accepted branch supplies the source-window package needed by the
nonnegative-domain critical-value certificate.
-/
noncomputable def paper_average_greedy_critical_threshold_some_branch
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (reports : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (hreports :
      AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile
        reports)
    (i : Bidder) (s : AppliedModelingLib.Auction.Bundle Item) (p : ℝ)
    (hs : s.Nonempty)
    (hthreshold :
      paper_average_greedy_critical_threshold reports i s = some p) :
    AppliedModelingLib.Auction.SingleMindedSomeThresholdBranch
      paper_average_order_of reports i s p :=
  AppliedModelingLib.Auction.singleMindedAverageGreedyCriticalThreshold_some_branch
    reports hreports i s p hs hthreshold

/--
Build the Theorem 10.2 nonnegative-domain critical-value certificate from the
source branch data. This is the paper-facing assembly point after the concrete
sorted-order branch data have been supplied.
-/
noncomputable def paper_greedy_nonnegative_critical_certificate_of_branch_data
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder)
    (data : paper_nonnegative_critical_source_branch_data orderOf) :
    (AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf
      (Bidder := Bidder) (Item := Item)
      orderOf).NonnegativeCriticalValueWithInfinityCertificate :=
  AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanism_nonnegativeCriticalValueWithInfinityCertificate_of_branch_data
    orderOf data

/--
Concrete average-order assembly point for the Theorem 10.2
nonnegative-domain critical-value certificate.
-/
noncomputable def paper_average_greedy_nonnegative_critical_certificate_of_branch_data
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (data :
      paper_nonnegative_critical_source_branch_data
        (Bidder := Bidder) (Item := Item)
        (AppliedModelingLib.Auction.singleMindedAverageOrderOf
          (Bidder := Bidder) (Item := Item))) :
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeCriticalValueWithInfinityCertificate
        (AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf
          (Bidder := Bidder) (Item := Item)
          (AppliedModelingLib.Auction.singleMindedAverageOrderOf
            (Bidder := Bidder) (Item := Item))) :=
  paper_greedy_nonnegative_critical_certificate_of_branch_data
    (Bidder := Bidder) (Item := Item)
    (AppliedModelingLib.Auction.singleMindedAverageOrderOf
      (Bidder := Bidder) (Item := Item))
    data

/--
Concrete source-branch data for the average-order greedy mechanism on the
nonempty nonnegative single-minded domain.
-/
noncomputable def paper_average_greedy_nonnegative_critical_source_branch_data
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder] :
    paper_nonnegative_critical_source_branch_data
      (Bidder := Bidder) (Item := Item)
      (AppliedModelingLib.Auction.singleMindedAverageOrderOf
        (Bidder := Bidder) (Item := Item)) :=
  AppliedModelingLib.Auction.singleMindedAverageGreedyNonnegativeCriticalBranchData

/--
Concrete nonnegative-domain critical-value certificate for the average-order
greedy accepted-set/payment mechanism.
-/
noncomputable def paper_average_greedy_nonnegative_critical_certificate
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder] :
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeCriticalValueWithInfinityCertificate
        (AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf
          (Bidder := Bidder) (Item := Item)
          (AppliedModelingLib.Auction.singleMindedAverageOrderOf
            (Bidder := Bidder) (Item := Item))) :=
  paper_average_greedy_nonnegative_critical_certificate_of_branch_data
    (paper_average_greedy_nonnegative_critical_source_branch_data
      (Bidder := Bidder) (Item := Item))

/--
Source-shaped below-threshold rejection bridge: in an average-descending order,
if `j` is below `|s_j| * c(n)`, `n` is accepted before `j`, and `n` conflicts
with `j`, then `j` is rejected.
-/
theorem paper_greedy_rejected_of_average_threshold_and_prefix_accept
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    {bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item}
    (acceptedBefore : Finset Bidder) (order : List Bidder) {j n : Bidder}
    (hsorted : paper_average_amount_descending bids order)
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
          n ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
            bids acceptedBefore ((pre ++ [n]) ++ between))
    (hconflict : AppliedModelingLib.Auction.SingleMindedBidsConflict bids j n) :
    j ∉ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
      bids acceptedBefore order := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState_rejects_of_average_threshold_and_prefix_accept
      acceptedBefore order hsorted hnodup hjorder hnorder hjn hjaccepted
      hj_nonempty hlt hprefix_accept hconflict

/--
If the full-order `n(j)` search returns `n`, then `n` satisfies the full-order
denied-because-of relation after the first occurrence of `j`.
-/
theorem paper_greedy_next_denied_from_order_some_spec
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) (j n : Bidder)
    (hnext : paper_greedy_next_denied_from_order bids order j = some n) :
    paper_greedy_denied_because_of_after_in_order bids order j n := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromOrder_some_spec
      bids order j n hnext

/--
If the full-order `n(j)` search returns none, then no full-order
denied-because-of candidate exists after the first occurrence of `j`.
-/
theorem paper_greedy_next_denied_from_order_none_no_candidate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) (j : Bidder)
    (hnext : paper_greedy_next_denied_from_order bids order j = none) :
    ∀ n, ¬ paper_greedy_denied_because_of_after_in_order bids order j n := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromOrder_none_no_candidate
      bids order j hnext

/--
The full-order `n(j)` search agrees with the split-order search at the first
occurrence split of `j`.
-/
theorem paper_greedy_next_denied_from_order_eq_split
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (pre suffix : List Bidder) (j : Bidder)
    (hpre : j ∉ pre) :
    paper_greedy_next_denied_from_order bids (pre ++ j :: suffix) j =
      paper_greedy_next_denied_from_split bids pre suffix j := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromOrder_eq_split
      bids pre suffix j hpre

/--
For a duplicate-free order, the full-order `n(j)` search agrees with any
displayed split around `j`.
-/
theorem paper_greedy_next_denied_from_order_eq_split_of_nodup
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    {order pre suffix : List Bidder} {j : Bidder}
    (horder : order = pre ++ j :: suffix)
    (hnodup : order.Nodup) :
    paper_greedy_next_denied_from_order bids order j =
      paper_greedy_next_denied_from_split bids pre suffix j := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromOrder_eq_split_of_nodup
      bids horder hnodup

/--
If the full-order `n(j)` search returns `n` at a first occurrence split, then
`n` is in the suffix and satisfies the prefix-local denied-because-of condition.
-/
theorem paper_greedy_next_denied_from_order_some_spec_of_split
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (pre suffix : List Bidder) (j n : Bidder)
    (hpre : j ∉ pre)
    (hnext :
      paper_greedy_next_denied_from_order
        bids (pre ++ j :: suffix) j = some n) :
    n ∈ suffix ∧
      AppliedModelingLib.Auction.SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids
        (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
          bids ∅ (pre ++ [j]))
        suffix j n := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromOrder_some_spec_of_split
      bids pre suffix j n hpre hnext

/--
If the full-order `n(j)` search returns none at a first occurrence split, then
no later bid in that suffix is denied because of `j`.
-/
theorem paper_greedy_next_denied_from_order_none_no_candidate_of_split
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (pre suffix : List Bidder) (j : Bidder)
    (hpre : j ∉ pre)
    (hnext :
      paper_greedy_next_denied_from_order
        bids (pre ++ j :: suffix) j = none) :
    ∀ n, n ∈ suffix →
      ¬ AppliedModelingLib.Auction.SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids
        (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
          bids ∅ (pre ++ [j]))
        suffix j n := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromOrder_none_no_candidate_of_split
      bids pre suffix j hpre hnext

/-- Any returned full-order `n(j)` follows `j` in the supplied sorted order. -/
theorem paper_greedy_next_denied_from_order_precedes_of_split
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (pre suffix : List Bidder) (j n : Bidder)
    (hpre : j ∉ pre)
    (hnext :
      paper_greedy_next_denied_from_order
        bids (pre ++ j :: suffix) j = some n) :
    AppliedModelingLib.Auction.SingleMindedPrecedes (pre ++ j :: suffix) j n := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromOrder_precedes_of_split
      bids pre suffix j n hpre hnext

/--
If the split-order `n(j)` search returns none, then no later bid in that suffix
is denied because of `j` in the prefix-local sense.
-/
theorem paper_greedy_next_denied_from_split_none_no_candidate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (pre suffix : List Bidder) (j : Bidder)
    (hnext :
      paper_greedy_next_denied_from_split bids pre suffix j = none) :
    ∀ n, n ∈ suffix →
      ¬ AppliedModelingLib.Auction.SingleMindedGreedyDeniedBecauseOfInSuffixFromState
        bids
        (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromState
          bids ∅ (pre ++ [j]))
        suffix j n := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromSplit_none_no_candidate
      bids pre suffix j hnext

/-- Denied bids pay zero under the full-order greedy payment rule. -/
theorem paper_greedy_payment_from_order_eq_zero_of_denied
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) {j : Bidder}
    (hj :
      j ∉ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order) :
    paper_greedy_payment_from_order bids order j = 0 := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyPaymentFromOrder_eq_zero_of_denied
      bids order hj

/-- Granted bids with no full-order `n(j)` pay zero. -/
theorem paper_greedy_payment_from_order_eq_zero_of_no_next
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) {j : Bidder}
    (hj :
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order)
    (hnext : paper_greedy_next_denied_from_order bids order j = none) :
    paper_greedy_payment_from_order bids order j = 0 := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyPaymentFromOrder_eq_zero_of_no_next
      bids order hj hnext

/-- If full-order `n(j)` exists, the greedy payment is `|s_j| * c(n(j))`. -/
theorem paper_greedy_payment_from_order_eq_of_next
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) {j n : Bidder}
    (hj :
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order)
    (hnext : paper_greedy_next_denied_from_order bids order j = some n) :
    paper_greedy_payment_from_order bids order j =
      (bids j).bundleSize * (bids n).averageAmountPerGood := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyPaymentFromOrder_eq_of_next
      bids order hj hnext

/-- Denied bids pay zero under the concrete average-order greedy payment rule. -/
theorem paper_average_greedy_payment_eq_zero_of_denied
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) {j : Bidder}
    (hj : j ∉ paper_average_greedy_accepted_set bids) :
    paper_average_greedy_payment bids j = 0 := by
  exact
    paper_greedy_payment_from_order_eq_zero_of_denied
      bids (paper_average_order_of bids) hj

/-- Granted bids with no `n(j)` pay zero under the concrete average-order rule. -/
theorem paper_average_greedy_payment_eq_zero_of_no_next
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) {j : Bidder}
    (hj : j ∈ paper_average_greedy_accepted_set bids)
    (hnext :
      paper_greedy_next_denied_from_order bids (paper_average_order_of bids) j =
        none) :
    paper_average_greedy_payment bids j = 0 := by
  exact
    paper_greedy_payment_from_order_eq_zero_of_no_next
      bids (paper_average_order_of bids) hj hnext

/-- If concrete average-order `n(j)` exists, the payment is `|s_j| * c(n(j))`. -/
theorem paper_average_greedy_payment_eq_of_next
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) {j n : Bidder}
    (hj : j ∈ paper_average_greedy_accepted_set bids)
    (hnext :
      paper_greedy_next_denied_from_order bids (paper_average_order_of bids) j =
        some n) :
    paper_average_greedy_payment bids j =
      (bids j).bundleSize * (bids n).averageAmountPerGood := by
  exact
    paper_greedy_payment_from_order_eq_of_next
      bids (paper_average_order_of bids) hj hnext

/--
The LOS02 greedy accepted-set mechanism generated by a paper-supplied order
rule and the full-order Definition 10.1 payment rule.
-/
noncomputable abbrev paper_single_minded_greedy_accepted_mechanism_from_order_of
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder) :
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism Bidder Item :=
  AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf orderOf

/-- The paper's concrete average-order greedy accepted-set mechanism. -/
noncomputable abbrev paper_average_greedy_accepted_mechanism
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder] :
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism Bidder Item :=
  paper_single_minded_greedy_accepted_mechanism_from_order_of
    (Bidder := Bidder) (Item := Item)
    (AppliedModelingLib.Auction.singleMindedAverageOrderOf
      (Bidder := Bidder) (Item := Item))

/-- The LOS02 greedy accepted-set mechanism satisfies Participation. -/
theorem paper_single_minded_greedy_accepted_mechanism_participation
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder) :
    (paper_single_minded_greedy_accepted_mechanism_from_order_of
      (Bidder := Bidder) (Item := Item) orderOf).Participation := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyAcceptedMechanismFromOrderOf_participation
      orderOf

/-- The concrete average-order greedy accepted-set mechanism satisfies Participation. -/
theorem paper_average_greedy_accepted_mechanism_participation
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder] :
    (paper_average_greedy_accepted_mechanism
      (Bidder := Bidder) (Item := Item)).Participation := by
  exact
    paper_single_minded_greedy_accepted_mechanism_participation
      (Bidder := Bidder) (Item := Item)
      (AppliedModelingLib.Auction.singleMindedAverageOrderOf
        (Bidder := Bidder) (Item := Item))

/--
The concrete average-order greedy accepted-set rule is monotone on the
nonempty nonnegative single-minded domain.
-/
theorem paper_average_greedy_accepted_mechanism_nonnegative_monotonicity
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder] :
    (paper_average_greedy_accepted_mechanism
      (Bidder := Bidder) (Item := Item)).MonotonicityOn
        AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageGreedyAcceptedMechanism_nonnegative_monotonicity
      (Bidder := Bidder) (Item := Item)

/--
LOS02 Theorem 10.2, source-shaped accepted-set certificate form. Once the greedy
accepted-set/payment mechanism is shown monotone and equipped with the
finite-or-infinite critical-value certificate, truthfulness follows from Theorem
9.6; Participation is already proved from the Definition 10.1 payment formula.
-/
theorem paper_theorem10_2_greedy_truthful_of_infinity_certificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder)
    (hmono :
      (paper_single_minded_greedy_accepted_mechanism_from_order_of
        (Bidder := Bidder) (Item := Item) orderOf).Monotonicity)
    (C :
      (paper_single_minded_greedy_accepted_mechanism_from_order_of
        (Bidder := Bidder) (Item := Item)
        orderOf).CriticalValueWithInfinityCertificate) :
    (paper_single_minded_greedy_accepted_mechanism_from_order_of
      (Bidder := Bidder) (Item := Item) orderOf).TruthfulOn
        AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  exact
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.truthfulOn_of_monotonicity_participation_infinity_critical
      (paper_single_minded_greedy_accepted_mechanism_from_order_of
        (Bidder := Bidder) (Item := Item) orderOf)
      hmono
      (paper_single_minded_greedy_accepted_mechanism_participation orderOf)
      C

/--
LOS02 Theorem 10.2, domain-aware accepted-set certificate form. The greedy
accepted-set/payment mechanism is truthful on nonempty nonnegative
single-minded profiles once it is monotone and equipped with the critical-value
certificate whose clauses are restricted to that same domain.
-/
theorem paper_theorem10_2_greedy_truthful_of_nonnegative_infinity_certificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (orderOf :
      (Bidder → AppliedModelingLib.Auction.SingleMindedBid Item) → List Bidder)
    (hmono :
      (paper_single_minded_greedy_accepted_mechanism_from_order_of
        (Bidder := Bidder) (Item := Item) orderOf).MonotonicityOn
          AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile)
    (C :
      (paper_single_minded_greedy_accepted_mechanism_from_order_of
        (Bidder := Bidder) (Item := Item)
        orderOf).NonnegativeCriticalValueWithInfinityCertificate) :
    (paper_single_minded_greedy_accepted_mechanism_from_order_of
      (Bidder := Bidder) (Item := Item) orderOf).TruthfulOn
        AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  exact
    AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.truthfulOn_of_monotonicityOn_participation_nonnegative_infinity_critical
      (paper_single_minded_greedy_accepted_mechanism_from_order_of
        (Bidder := Bidder) (Item := Item) orderOf)
      hmono
      (paper_single_minded_greedy_accepted_mechanism_participation orderOf)
      C

/--
Theorem 10.2 specialized to the concrete average-order greedy mechanism. Once
monotonicity and the concrete source branch data are supplied, truthfulness on
the nonempty nonnegative single-minded domain follows.
-/
theorem paper_theorem10_2_average_greedy_truthful_of_nonnegative_source_branch_data
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (hmono :
      (paper_average_greedy_accepted_mechanism
        (Bidder := Bidder) (Item := Item)).MonotonicityOn
          AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile)
    (data :
      paper_nonnegative_critical_source_branch_data
        (Bidder := Bidder) (Item := Item)
        (AppliedModelingLib.Auction.singleMindedAverageOrderOf
          (Bidder := Bidder) (Item := Item))) :
    (paper_average_greedy_accepted_mechanism
      (Bidder := Bidder) (Item := Item)).TruthfulOn
        AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  exact
    paper_theorem10_2_greedy_truthful_of_nonnegative_infinity_certificate
      (Bidder := Bidder) (Item := Item)
      (AppliedModelingLib.Auction.singleMindedAverageOrderOf
        (Bidder := Bidder) (Item := Item))
      hmono
      (paper_average_greedy_nonnegative_critical_certificate_of_branch_data
        (Bidder := Bidder) (Item := Item) data)

/--
Theorem 10.2 specialized to the concrete average-order critical-value
certificate. The remaining hypothesis is the monotonicity of the concrete
average-order greedy accepted-set rule.
-/
theorem paper_theorem10_2_average_greedy_truthful_of_monotonicity
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (hmono :
      (paper_average_greedy_accepted_mechanism
        (Bidder := Bidder) (Item := Item)).Monotonicity) :
    (paper_average_greedy_accepted_mechanism
      (Bidder := Bidder) (Item := Item)).TruthfulOn
        AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  exact
    paper_theorem10_2_average_greedy_truthful_of_nonnegative_source_branch_data
      (Bidder := Bidder) (Item := Item)
      (AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.monotonicityOn_of_monotonicity
        (paper_average_greedy_accepted_mechanism
          (Bidder := Bidder) (Item := Item))
        AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile
        hmono)
      (paper_average_greedy_nonnegative_critical_source_branch_data
        (Bidder := Bidder) (Item := Item))

/--
LOS02 Theorem 10.2 for the concrete average-order greedy
accepted-set/payment mechanism on nonempty nonnegative single-minded profiles.
-/
theorem paper_theorem10_2_average_greedy_truthful
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder] :
    (paper_average_greedy_accepted_mechanism
      (Bidder := Bidder) (Item := Item)).TruthfulOn
        AppliedModelingLib.Auction.SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  exact
    AppliedModelingLib.Auction.singleMindedAverageGreedyAcceptedMechanism_truthfulOn_nonnegative
      (Bidder := Bidder) (Item := Item)

/--
Certificate connecting the Definition 10.1 greedy allocation/payment objects to
the reusable fixed-target critical-price theorem. The concrete Theorem 10.2
entry point above discharges this route for the average-order greedy mechanism;
this auxiliary certificate remains available for future variants of the
critical-price construction.
-/
structure GreedyCriticalPriceCertificate
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item]
    (target : Bidder → AppliedModelingLib.Auction.Bundle Item)
    (orderOf :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item → List Bidder)
    (nextDenied :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item →
        Bidder → Option Bidder)
    (price :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item → Bidder → ℝ) :
    Prop where
  ownReportIndependent :
    AppliedModelingLib.Auction.BundlePriceOwnReportIndependent price
  accepted_eq : ∀ reports,
    AppliedModelingLib.Auction.targetBundleWinners target price reports =
      AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
        (AppliedModelingLib.Auction.targetAsSingleMindedBids target reports)
        (orderOf reports)
  payment_eq : ∀ reports j,
    price reports j =
      AppliedModelingLib.Auction.singleMindedGreedyPaymentFromNextDenied
        (AppliedModelingLib.Auction.targetAsSingleMindedBids target reports)
        (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
          (AppliedModelingLib.Auction.targetAsSingleMindedBids target reports)
          (orderOf reports))
        (nextDenied reports) j

/--
Build the Theorem 10.2 critical-price certificate from the full-order
Definition 10.1 payment rule.
-/
theorem paper_greedy_critical_price_certificate_of_full_order_payment
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item]
    (target : Bidder → AppliedModelingLib.Auction.Bundle Item)
    (orderOf :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item → List Bidder)
    (price :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind :
      AppliedModelingLib.Auction.BundlePriceOwnReportIndependent price)
    (haccepted : ∀ reports,
      AppliedModelingLib.Auction.targetBundleWinners target price reports =
        AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
          (AppliedModelingLib.Auction.targetAsSingleMindedBids target reports)
          (orderOf reports))
    (hprice : ∀ reports j,
      price reports j =
        AppliedModelingLib.Auction.singleMindedGreedyPaymentFromOrder
          (AppliedModelingLib.Auction.targetAsSingleMindedBids target reports)
          (orderOf reports) j) :
    GreedyCriticalPriceCertificate target orderOf
      (fun reports j =>
        AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromOrder
          (AppliedModelingLib.Auction.targetAsSingleMindedBids target reports)
          (orderOf reports) j)
      price := by
  refine ⟨hind, haccepted, ?_⟩
  intro reports j
  simpa [AppliedModelingLib.Auction.singleMindedGreedyPaymentFromOrder]
    using hprice reports j

/--
LOS02 Theorem 10.2, fixed-target critical-price certificate form. A greedy
allocation/payment implementation that satisfies the certificate inherits the
existing critical-price truthfulness theorem for nonempty single-minded
profiles.
-/
theorem paper_theorem10_2_greedy_threshold_truthful_of_certificate
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item]
    (target : Bidder → AppliedModelingLib.Auction.Bundle Item)
    (orderOf :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item → List Bidder)
    (nextDenied :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item →
        Bidder → Option Bidder)
    (price :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item → Bidder → ℝ)
    (C : GreedyCriticalPriceCertificate target orderOf nextDenied price) :
    paper_combinatorial_truthful_on
      (AppliedModelingLib.Auction.targetBundleThresholdAuction target price)
      AppliedModelingLib.Auction.IsNonemptySingleMindedProfile := by
  exact
    paper_combinatorial_target_bundle_threshold_truthful_on_single_minded
      target price C.ownReportIndependent

/--
LOS02 Theorem 10.2, full-order Definition 10.1 payment certificate form. Once
the full-order greedy payment rule is shown to be an own-report-independent
critical price for the greedy accepted set, truthfulness follows from the
reusable critical-price theorem.
-/
theorem paper_theorem10_2_greedy_threshold_truthful_of_full_order_payment_certificate
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item]
    (target : Bidder → AppliedModelingLib.Auction.Bundle Item)
    (orderOf :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item → List Bidder)
    (price :
      AppliedModelingLib.Auction.CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind :
      AppliedModelingLib.Auction.BundlePriceOwnReportIndependent price)
    (haccepted : ∀ reports,
      AppliedModelingLib.Auction.targetBundleWinners target price reports =
        AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder
          (AppliedModelingLib.Auction.targetAsSingleMindedBids target reports)
          (orderOf reports))
    (hprice : ∀ reports j,
      price reports j =
        AppliedModelingLib.Auction.singleMindedGreedyPaymentFromOrder
          (AppliedModelingLib.Auction.targetAsSingleMindedBids target reports)
          (orderOf reports) j) :
    paper_combinatorial_truthful_on
      (AppliedModelingLib.Auction.targetBundleThresholdAuction target price)
      AppliedModelingLib.Auction.IsNonemptySingleMindedProfile := by
  exact
    paper_theorem10_2_greedy_threshold_truthful_of_certificate
      target orderOf
      (fun reports j =>
        AppliedModelingLib.Auction.singleMindedGreedyNextDeniedFromOrder
          (AppliedModelingLib.Auction.targetAsSingleMindedBids target reports)
          (orderOf reports) j)
      price
      (paper_greedy_critical_price_certificate_of_full_order_payment
        target orderOf price hind haccepted hprice)

/--
Theorem 7.2 source proof step: a rejected bid in the sorted greedy order has an
earlier accepted conflicting blocker whose square-root norm is weakly larger.
-/
theorem paper_theorem7_2_rejected_bid_has_preceding_sqrt_blocker
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (order : List Bidder) (i : Bidder)
    (hsorted : AppliedModelingLib.Auction.SingleMindedSqrtNormDescending bids order)
    (hi_order : i ∈ order)
    (hnot_final :
      i ∉ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order) :
    ∃ j, ∃ g,
      j ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order ∧
        AppliedModelingLib.Auction.SingleMindedPrecedes order j i ∧
          g ∈ (bids i).desired ∧
            g ∈ (bids j).desired ∧
              (bids i).sqrtAmountNorm ≤ (bids j).sqrtAmountNorm := by
  exact
    AppliedModelingLib.Auction.singleMindedGreedyRejectedBid_exists_order_blocker
      bids order i hsorted hi_order hnot_final

/--
Theorem 7.2 source proof step: when the optimal and greedy sets are disjoint,
the preceding-blocker lemma packages into the order-level blocking certificate.
-/
noncomputable def paper_theorem7_2_order_blocking_certificate_of_disjoint
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    [Inhabited Bidder] [Inhabited Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (optimal : Finset Bidder) (order : List Bidder)
    (hsorted : AppliedModelingLib.Auction.SingleMindedSqrtNormDescending bids order)
    (hoptimal_order : ∀ i, i ∈ optimal → i ∈ order)
    (hoptimal_greedy_disjoint :
      Disjoint optimal
        (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order)) :
    AppliedModelingLib.Auction.SingleMindedGreedyOrderBlockingCertificate bids optimal
      (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order)
      order :=
  AppliedModelingLib.Auction.singleMindedGreedyOrderBlockingCertificateOfDisjoint
    bids optimal order hsorted hoptimal_order hoptimal_greedy_disjoint

/--
Theorem 7.2 counting step: a source-shaped blocking certificate implies the
paper's square-root-norm-squared bound.
-/
theorem paper_theorem7_2_blocking_certificate_normsq_bound
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (optimal greedy : Finset Bidder)
    (hoptimal_disjoint :
      AppliedModelingLib.Auction.PairwiseDisjointDesired bids optimal)
    (hgreedy_nonempty : ∀ j, j ∈ greedy → (bids j).desired.Nonempty)
    (C :
      AppliedModelingLib.Auction.SingleMindedGreedyBlockingCertificate
        bids optimal greedy) :
    AppliedModelingLib.Auction.singleMindedSqrtNormSqSum bids optimal ≤
      ∑ j ∈ greedy, (bids j).value ^ 2 := by
  exact
    AppliedModelingLib.Auction.singleMindedSqrtNormSqSum_le_sum_sq_of_blocking_certificate
      bids optimal greedy hoptimal_disjoint hgreedy_nonempty C

/--
LOS02 Theorem 7.2, algebraic certificate form. Once the greedy execution proves
the paper's blocking inequality, the optimal single-minded allocation value is
at most `sqrt(k)` times the greedy value.
-/
theorem paper_theorem7_2_sqrt_norm_approx_of_blocking_bound
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (goods : Finset Item)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : AppliedModelingLib.Auction.PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg : ∀ i, i ∈ greedy → 0 ≤ (bids i).value)
    (hblocking :
      AppliedModelingLib.Auction.singleMindedSqrtNormSqSum bids optimal ≤
        ∑ j ∈ greedy, (bids j).value ^ 2) :
    paper_single_minded_total_value bids optimal ≤
      Real.sqrt (goods.card : ℝ) *
        paper_single_minded_total_value bids greedy := by
  exact
    AppliedModelingLib.Auction.singleMinded_sqrt_greedy_approx_of_blocking_bound
      bids optimal greedy goods hoptimal_goods hoptimal_disjoint
      hoptimal_nonempty hoptimal_value_nonneg hgreedy_value_nonneg hblocking

/--
LOS02 Theorem 7.2, source-shaped blocking-certificate form. The certificate
assigns every optimal bid to a conflicting greedy bid and blocked good, exactly
matching the paper's multiplicity argument.
-/
theorem paper_theorem7_2_sqrt_norm_approx_of_blocking_certificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (goods : Finset Item)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : AppliedModelingLib.Auction.PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty : ∀ i, i ∈ greedy → (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg : ∀ i, i ∈ greedy → 0 ≤ (bids i).value)
    (C :
      AppliedModelingLib.Auction.SingleMindedGreedyBlockingCertificate
        bids optimal greedy) :
    paper_single_minded_total_value bids optimal ≤
      Real.sqrt (goods.card : ℝ) *
        paper_single_minded_total_value bids greedy := by
  exact
    AppliedModelingLib.Auction.singleMinded_sqrt_greedy_approx_of_blocking_certificate
      bids optimal greedy goods hoptimal_goods hoptimal_disjoint
      hoptimal_nonempty hgreedy_nonempty hoptimal_value_nonneg
      hgreedy_value_nonneg C

/--
LOS02 Theorem 7.2, source-order certificate form. The certificate says every
optimal bid is blocked by an earlier greedy bid with weakly larger square-root
norm.
-/
theorem paper_theorem7_2_sqrt_norm_approx_of_order_blocking_certificate
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (goods : Finset Item) (order : List Bidder)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : AppliedModelingLib.Auction.PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty : ∀ i, i ∈ greedy → (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg : ∀ i, i ∈ greedy → 0 ≤ (bids i).value)
    (C :
      AppliedModelingLib.Auction.SingleMindedGreedyOrderBlockingCertificate
        bids optimal greedy order) :
    paper_single_minded_total_value bids optimal ≤
      Real.sqrt (goods.card : ℝ) *
        paper_single_minded_total_value bids greedy := by
  exact
    AppliedModelingLib.Auction.singleMinded_sqrt_greedy_approx_of_order_blocking_certificate
      bids optimal greedy goods order hoptimal_goods hoptimal_disjoint
      hoptimal_nonempty hgreedy_nonempty hoptimal_value_nonneg
      hgreedy_value_nonneg C

/--
LOS02 Theorem 7.2, common-bid removal bridge. If the source proof's reduced
instance after deleting bids common to optimal and greedy satisfies the
approximation bound, then the original optimal and greedy values satisfy the
same bound.
-/
theorem paper_theorem7_2_common_bid_removal_bridge
    {Bidder Item : Type*} [DecidableEq Bidder]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (optimal greedy : Finset Bidder) (factor : ℝ)
    (hfactor : 1 ≤ factor)
    (hcommon_nonneg : ∀ i, i ∈ optimal ∩ greedy → 0 ≤ (bids i).value)
    (hreduced :
      paper_single_minded_total_value bids (optimal \ greedy) ≤
        factor * paper_single_minded_total_value bids (greedy \ optimal)) :
    paper_single_minded_total_value bids optimal ≤
      factor * paper_single_minded_total_value bids greedy := by
  exact
    AppliedModelingLib.Auction.singleMindedTotalValue_common_bid_removal_bridge
      bids optimal greedy factor hfactor hcommon_nonneg hreduced

/--
LOS02 Theorem 7.2, disjoint sorted-greedy case. This closes the paper's
approximation argument after the source proof's reduction removing bids common
to the greedy and optimal allocations.
-/
theorem paper_theorem7_2_sqrt_norm_approx_of_sorted_order_disjoint
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    [Inhabited Bidder] [Inhabited Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (optimal : Finset Bidder) (goods : Finset Item) (order : List Bidder)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : AppliedModelingLib.Auction.PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty :
      ∀ i,
        i ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order →
          (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg :
      ∀ i,
        i ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order →
          0 ≤ (bids i).value)
    (hsorted : AppliedModelingLib.Auction.SingleMindedSqrtNormDescending bids order)
    (hoptimal_order : ∀ i, i ∈ optimal → i ∈ order)
    (hoptimal_greedy_disjoint :
      Disjoint optimal
        (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order)) :
    paper_single_minded_total_value bids optimal ≤
      Real.sqrt (goods.card : ℝ) *
        paper_single_minded_total_value bids
          (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order) := by
  exact
    AppliedModelingLib.Auction.singleMinded_sqrt_greedy_approx_of_sorted_order_disjoint
      bids optimal goods order hoptimal_goods hoptimal_disjoint
      hoptimal_nonempty hgreedy_nonempty hoptimal_value_nonneg
      hgreedy_value_nonneg hsorted hoptimal_order hoptimal_greedy_disjoint

/--
LOS02 Theorem 7.2 for the explicit sorted greedy run. This endpoint includes
the source proof's common-bid removal step by filtering away bids that touch
goods requested by bids common to the optimal and greedy accepted sets.
-/
theorem paper_theorem7_2_sqrt_norm_approx_of_sorted_order
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    [Inhabited Bidder] [Inhabited Item]
    (bids : Bidder → AppliedModelingLib.Auction.SingleMindedBid Item)
    (optimal : Finset Bidder) (goods : Finset Item) (order : List Bidder)
    (hoptimal_goods : ∀ i, i ∈ optimal → (bids i).desired ⊆ goods)
    (hoptimal_disjoint : AppliedModelingLib.Auction.PairwiseDisjointDesired bids optimal)
    (hoptimal_nonempty : ∀ i, i ∈ optimal → (bids i).desired.Nonempty)
    (hgreedy_nonempty :
      ∀ i,
        i ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order →
          (bids i).desired.Nonempty)
    (hoptimal_value_nonneg : ∀ i, i ∈ optimal → 0 ≤ (bids i).value)
    (hgreedy_value_nonneg :
      ∀ i,
        i ∈ AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order →
          0 ≤ (bids i).value)
    (hsorted : AppliedModelingLib.Auction.SingleMindedSqrtNormDescending bids order)
    (hoptimal_order : ∀ i, i ∈ optimal → i ∈ order) :
    paper_single_minded_total_value bids optimal ≤
      Real.sqrt (goods.card : ℝ) *
        paper_single_minded_total_value bids
          (AppliedModelingLib.Auction.singleMindedGreedyAcceptedFromOrder bids order) := by
  exact
    AppliedModelingLib.Auction.singleMinded_sqrt_greedy_approx_of_sorted_order
      bids optimal goods order hoptimal_goods hoptimal_disjoint
      hoptimal_nonempty hgreedy_nonempty hoptimal_value_nonneg
      hgreedy_value_nonneg hsorted hoptimal_order

end LOS02CombinatorialAuctions
