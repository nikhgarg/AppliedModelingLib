import AppliedModelingLib.Foundations.Optimization.Approximation
import AppliedModelingLib.Foundations.Optimization.AveragePooling
import AppliedModelingLib.Foundations.Optimization.Averaging
import AppliedModelingLib.Foundations.Optimization.Argmax
import AppliedModelingLib.Foundations.Optimization.Bisection
import AppliedModelingLib.Foundations.Optimization.ConvexPower
import AppliedModelingLib.Foundations.Optimization.Certificate
import AppliedModelingLib.Foundations.Optimization.CompactPerturbation
import AppliedModelingLib.Foundations.Optimization.CoordinatewiseSmooth
import AppliedModelingLib.Foundations.Optimization.DualSmoothEnvelope
import AppliedModelingLib.Foundations.Optimization.DualStrongConcaveArgmax
import AppliedModelingLib.Foundations.Optimization.Endpoint
import AppliedModelingLib.Foundations.Optimization.ExpectedSubgradient
import AppliedModelingLib.Foundations.Optimization.FiniteSearch
import AppliedModelingLib.Foundations.Optimization.FiniteSoftmax
import AppliedModelingLib.Foundations.Optimization.LinearProgram
import AppliedModelingLib.Foundations.Optimization.ScalarStrongDuality
import AppliedModelingLib.Foundations.Optimization.MeasureThreshold
import AppliedModelingLib.Foundations.Optimization.MirrorDescent
import AppliedModelingLib.Foundations.Optimization.MoveGraph
import AppliedModelingLib.Foundations.Optimization.PointwiseSupremum
import AppliedModelingLib.Foundations.Optimization.ProjectedSubgradient
import AppliedModelingLib.Foundations.Optimization.NonconvexSmoothDescent
import AppliedModelingLib.Foundations.Optimization.FiniteAdaptiveDescent
import AppliedModelingLib.Foundations.Optimization.SmoothStrongConvex
import AppliedModelingLib.Foundations.Optimization.StrongConcaveArgmax
import AppliedModelingLib.Foundations.Optimization.SmoothEnvelope
import AppliedModelingLib.Foundations.Optimization.SmoothComposition
import AppliedModelingLib.Foundations.Optimization.SquaredLInfProx
import AppliedModelingLib.Foundations.Optimization.StandardActivations
import AppliedModelingLib.Foundations.Optimization.StochasticSubgradient
import AppliedModelingLib.Foundations.Optimization.ProjectedStochasticConvergence
import AppliedModelingLib.Foundations.Optimization.ThresholdExchange

/-!
# Optimization Foundations

Aggregate import for reusable optimization primitives.

## Main declarations

- `AppliedModelingLib.Foundations.Optimization.Argmax`: finite argmax, pointwise
  maximization, and finite linear expectation interfaces used by classification,
  recommendation, and decision-rule papers.
- `AppliedModelingLib.Foundations.Optimization.ConvexPower`: coordinatewise power
  domination across convex hulls and finite-product power transport, used when
  transferring exponent-indexed convexified feasible images.
- `AppliedModelingLib.Foundations.Optimization.Approximation`: primal-dual/benchmark
  sandwich certificates for approximation and competitive-ratio proofs.
- `AppliedModelingLib.Foundations.Optimization.AveragePooling`: finite Euclidean
  average-pooling maps with operator bounds from window sizes and coordinate
  overlap, and zero derivative variation.
- `AppliedModelingLib.Foundations.Optimization.Averaging`: finite and measure-theoretic
  averaging certificates that produce global minimizers.
- `AppliedModelingLib.Foundations.Optimization.Bisection`: concrete loop-count helpers
  for nested bisection style algorithms.
- `AppliedModelingLib.Foundations.Optimization.Certificate`: reusable optimality
  certificates for maximization/minimization arguments over explicit feasible
  sets.
- `AppliedModelingLib.Foundations.Optimization.CompactPerturbation`: compact-gap
  stability for exact integer-scaled objective perturbations, without an
  argmax-continuity assumption.
- `AppliedModelingLib.Foundations.Optimization.CoordinatewiseSmooth`: dimension-free
  finite-Euclidean lifting of scalar value and derivative smoothness bounds.
- `AppliedModelingLib.Foundations.Optimization.Endpoint`: one-dimensional endpoint-move
  calculus from derivative signs, including first/last-zero stopping lemmas.
- `AppliedModelingLib.Foundations.Optimization.FiniteSearch`: existence of optimizers
  over nonempty finite feasible sets and finite encodings of feasible regions.
- `AppliedModelingLib.Foundations.Optimization.LinearProgram`: lightweight finite LP
  primal/dual feasibility, weak duality, and optimality certificates.
- `AppliedModelingLib.Foundations.Optimization.ScalarStrongDuality`: compact scalar
  convex-program strong duality under a strict Slater condition.
- `AppliedModelingLib.Foundations.Optimization.MeasureThreshold`: finite-measure
  threshold-attainment helpers with boundary randomization.
- `AppliedModelingLib.Foundations.Optimization.MirrorDescent`: certificate-factored
  Bregman mirror-step bounds, including the abstract estimate used by
  entropy/KL mirror descent.
- `AppliedModelingLib.Foundations.Optimization.MoveGraph`: exchange/local-move
  optimality from reachability and monotone moves.
- `AppliedModelingLib.Foundations.Optimization.PointwiseSupremum`: bounded
  pointwise-supremum and penalized-payoff stability facts that do not assume an
  attained maximizer.
- `AppliedModelingLib.Foundations.Optimization.ProjectedSubgradient`: paper-independent
  vocabulary for projected (stochastic) subgradient iterations: the subgradient
  inequality, the projected update rule, and Robbins-Monro step-size conditions.
- `AppliedModelingLib.Foundations.Optimization.ExpectedSubgradient`: the interchange
  theorem identifying an expected sampled subgradient as a subgradient of the
  expected objective.
- `AppliedModelingLib.Foundations.Optimization.StochasticSubgradient`: conditional
  finite-coordinate pairing, martingale, and deterministic descent lemmas for
  stochastic subgradient convergence.
- `AppliedModelingLib.Foundations.Optimization.ProjectedStochasticConvergence`: the
  full finite-coordinate projected stochastic-subgradient convergence theorem
  and outcome-indexed convergence-to-a-set API.
- `AppliedModelingLib.Foundations.Optimization.NonconvexSmoothDescent`: one-step
  inexact smooth descent with separated sampling and approximation errors.
- `AppliedModelingLib.Foundations.Optimization.FiniteAdaptiveDescent`: finite iid
  adaptive-trajectory factorization and finite-horizon expected descent.
- `AppliedModelingLib.Foundations.Optimization.FiniteSoftmax`: finite Euclidean
  softmax and negative-log-softmax calculus, including the dimension-free
  Jacobian bound and checked first-order smooth-map constructor.
- `AppliedModelingLib.Foundations.Optimization.SmoothStrongConvex`: first-order
  quadratic models for smooth and strongly convex functions.
- `AppliedModelingLib.Foundations.Optimization.StrongConcaveArgmax`: first-order
  stability of attained strongly-concave argmax selections.
- `AppliedModelingLib.Foundations.Optimization.SmoothEnvelope`: differentiability and
  smoothness of stable, attained pointwise envelopes.
- `AppliedModelingLib.Foundations.Optimization.DualStrongConcaveArgmax`: dual-space
  stability of strongly-concave argmax selections in arbitrary real normed spaces.
- `AppliedModelingLib.Foundations.Optimization.DualSmoothEnvelope`: Fréchet-differential
  smoothness of stable, attained pointwise envelopes without a Hilbert-space
  gradient identification.
- `AppliedModelingLib.Foundations.Optimization.SmoothComposition`: global
  first-order smoothness bounds under composition, including constant-
  derivative continuous linear maps.
- `AppliedModelingLib.Foundations.Optimization.SquaredLInfProx`: the corrected
  decreasing-sort threshold and coordinatewise clipping formula for the
  proximal map of a squared finite sup norm.
- `AppliedModelingLib.Foundations.Optimization.StandardActivations`: checked sigmoid
  and scale-one ELU value/Jacobian Lipschitz constants, both scalar and
  coordinatewise on finite Euclidean spaces.
- `AppliedModelingLib.Foundations.Optimization.ThresholdExchange`: finite weighted
  threshold-exchange inequalities for threshold and fractional-knapsack
  dominance proofs.
-/
