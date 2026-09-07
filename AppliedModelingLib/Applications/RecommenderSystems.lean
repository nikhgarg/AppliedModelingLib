import AppliedModelingLib.Applications.RecommenderSystems.Policy
import AppliedModelingLib.Applications.RecommenderSystems.Allocation
import AppliedModelingLib.Applications.RecommenderSystems.AllocationSequence
import AppliedModelingLib.Applications.RecommenderSystems.Classwise
import AppliedModelingLib.Applications.RecommenderSystems.PolicyAveraging
import AppliedModelingLib.Applications.RecommenderSystems.TopKOracle

/-!
# Recommender-System Applications

Aggregate import for reusable recommender-system primitives.

## Main declarations

- `AppliedModelingLib.Applications.RecommenderSystems.Policy`: finite recommendation
  policies, supports, and fairness primitives.
- `AppliedModelingLib.Applications.RecommenderSystems.Allocation`: finite count
  allocations and support/count algebra.
- `AppliedModelingLib.Applications.RecommenderSystems.AllocationSequence`: feasible and
  optimal allocation sequences, target-profile convergence, sublinear
  scaled-count profile bridges, and certificate-shaped wrappers for pairwise
  scaled-count/FOC/eventual floor arguments.
- `AppliedModelingLib.Applications.RecommenderSystems.Classwise`: classwise and
  type-indexed aggregation helpers.
- `AppliedModelingLib.Applications.RecommenderSystems.PolicyAveraging`: averaging
  finite policy kernels over finite groups.
- `AppliedModelingLib.Applications.RecommenderSystems.TopKOracle`: bridges
  probability-side top-`k` expectation oracles to finite count-allocation
  objectives and marginal-return assumptions.
-/
