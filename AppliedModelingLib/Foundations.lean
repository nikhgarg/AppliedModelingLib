import AppliedModelingLib.Foundations.Graph
import AppliedModelingLib.Foundations.Math
import AppliedModelingLib.Foundations.Combinatorics
import AppliedModelingLib.Foundations.Computation
import AppliedModelingLib.Foundations.Optimization
import AppliedModelingLib.Foundations.Probability

/-!
# Broad foundations prelude

Legacy aggregate import for paper-independent mathematical foundations. It is
supported for compatibility and interactive exploration; new paper interfaces
should normally import the smallest documented family facade or leaf module.

## Main declarations

- `AppliedModelingLib.Foundations.Math`: finite sums/rankings/rounding, asymptotics,
  continuity, and elementary real-analysis helpers.
- `AppliedModelingLib.Foundations.Graph`: graph and cycle primitives.
- `AppliedModelingLib.Foundations.Computation`: finite formula semantics and reduction
  cores that do not duplicate machine-level complexity libraries.
- `AppliedModelingLib.Foundations.Optimization`: finite argmax, finite feasible search,
  linear-expectation decision interfaces, and feasible-set optimality
  certificates.
- `AppliedModelingLib.Foundations.Probability`: finite PMFs, kernels, conditional
  probability, measure inequalities, sampling, stochastic processes,
  admissions/testing wrappers, order-statistic interfaces, and
  large-deviation certificates.
-/
