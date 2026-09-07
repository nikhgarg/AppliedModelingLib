# Optimization Library Roadmap

This tracks reusable optimization work suggested by the current paper queue.
The goal is the same as the probability roadmap: move recurring proof seams
into `AppliedModelingLib` once they are plausibly useful for a second paper, while
leaving source-specific objectives and notation in `papers/`.

## Current Entrypoint

- `AppliedModelingLib.Foundations.Optimization`
  - `Approximation`: primal-dual/benchmark sandwich certificates for
    approximation and competitive-ratio proofs, including additive-error
    variants.
  - `Argmax`: finite pointwise argmax, finite rule optimization, and abstract
    monotone/finite-linear expected objectives.
  - `Certificate`: explicit feasible-set optimality predicates plus
    maximization/minimization certificates.
  - `FiniteSearch`: optimizer existence over nonempty finite feasible sets and
    finite codes that cover a feasible region.
  - `LinearProgram`: finite standard-form maximization LPs, primal/dual
    feasibility, weak duality, and primal/dual optimality certificates.
  - `MoveGraph`: exchange/local-move optimality from reachability and objective
    monotonicity along moves.
  - `ChoiceEquilibrium`: static choice-equilibrium data with feasibility,
    best-response, and consistency projections.
  - `BinaryChoice`: two-action no-profitable-deviation predicates, projection
    from choice equilibria, threshold/tiebreak consequences, and direct
    contradiction lemmas from profitable binary deviations.

## Reusable Seams To Promote

### 1. Candidate-plus-bound certificates

Status: reusable core started in `Optimization.Certificate`.

Common source pattern: construct a feasible candidate, prove it achieves value
`V`, then prove every feasible point is bounded above or below by `V`.

Useful for:

- GCG user-item fairness LP certificates and closed-form optimality witnesses.
- GN driver-surge endpoint/current-bound selection certificates.
- Digital-goods and online-algorithm lower-bound certificates.
- Any paper theorem whose proof is a direct primal/dual or exchange upper bound.

Next lemmas:

- supremum/infimum bridges from `feasibleValueSet` once a paper needs an
  `sSup` or `sInf` statement rather than a direct optimality predicate.
- equality-case extraction: if the upper bound is tight only on a described
  support, turn it into a uniqueness/structure theorem.

### 2. Finite feasible search

Status: reusable core started in `Optimization.FiniteSearch`; richer
paper-specific code records remain paper-local in diversity-aware recommendation.

Common source pattern: encode an infinite-looking feasible family by a finite
code, maximize by `Fintype`, then decode the optimizer.

Useful for:

- fixed-total count allocations in diversity-aware recommendation papers.
- finite threshold/prefix policy families in digital-goods auctions.
- finite action/menu searches in GLM/LG testing papers.

Reusable target:

- done: a generic finite-code/decode wrapper proving existence of a maximizer
  or minimizer when every feasible point has an equivalent finite code.
- next: finite argmax lemmas that return bundled optimality certificates when a
  paper wants to store the optimizer plus its certified value.

### 3. Exchange and first-order conditions for integer allocations

Status: reusable move-graph core started in `Optimization.MoveGraph`; concrete
integer count-vector exchange lemmas remain paper-local in diversity-aware recommendation paper work and
recommender allocation files.

Common source pattern: a feasible integer allocation is optimal if every
one-unit feasible move has nonpositive marginal gain; conversely, an optimum
has no improving one-unit move.

Useful for:

- diversity-aware recommendation diminishing-return allocation objectives.
- recommendation exposure/item-fairness reallocations.
- matching or assignment papers with local swap arguments.

Reusable target:

- done: finite/general move-graph optimality from reachability plus monotone
  moves.
- one-unit exchange lemmas for count vectors with fixed total.
- weighted forward/backward marginal comparisons as reusable theorem schemas.

### 4. LP and weak-duality certificates

Status: lightweight weak-duality/certificate core started in
`Optimization.LinearProgram`; BFS support/rank theorems remain future work.

Common source pattern: formulate a small paper LP, provide a closed-form primal
candidate and a matching dual or separating inequality, then certify the
objective value.

Useful for:

- GCG LP reductions and basic-feasible-support claims.
- GLM/LG threshold mixture or admissions optimization if cast as finite LPs.
- auction lower bounds where finite distributions are dual witnesses.

Auction-specific notes:

- MSVV AdWords uses standard LP weak duality plus a primal-dual sandwich:
  offline optimum is at most a dual objective, and the Balance/MSVV revenue
  covers a ratio-scaled dual objective up to finite small-bids error. Use
  `UpperBoundApproximationCertificate` or
  `UpperBoundApproximationWithErrorCertificate` for this algebraic endpoint.
- GHW digital goods uses many certificate-style bounds that are not full LP
  duality: benchmark domination by a feasible fixed price, dyadic-bin
  certificates, ranked monotone-payment upper bounds, and deterministic
  threshold/bid-independent lower-bound witnesses. These fit better as
  `UpperBoundCertificate`, `LowerBoundCertificate`, finite-search, and
  threshold-prefix lemmas than as a generic BFS framework.
- MSVV Theorem 9 and similar auction lower bounds should use the generic Yao
  layer in `AppliedModelingLib.Algorithms.Complexity.Yao`, especially
  `RandomizedUpperPayoffCertificate`, before adding paper-specific permutation
  or layer-count fields.
- LOS combinatorial auctions likely need monotonicity/critical-value and greedy
  approximation certificates before LP/BFS. A full welfare-maximization LP
  would be useful only after the exact GVA or allocation LP is encoded.

Reusable target:

- done: standard nonnegative-variable finite maximization LP records with
  `Ax <= b`.
- done: weak duality over finite sums.
- done: primal/dual certificate-to-optimality wrappers using
  `UpperBoundCertificate`/`LowerBoundCertificate`.
- next: equality-form LP wrappers and minimization wrappers if a paper needs a
  source statement in that syntax.
- later: active-support and basic-feasible-solution counting/rank lemmas.

### 5. Convexity, Jensen, and global optimum certificates

Status: mature but mostly located in econometrics/rating-model files.

Common source pattern: prove convexity/concavity, apply Jensen or endpoint
logic, and derive a global minimum/maximum.

Useful for:

- MBJG producer-fairness binary rating-system design.
- GLM/LG testing score transformations and Blackwell comparisons.
- continuous pricing/policy shape results in GN.

Reusable target:

- move paper-independent convex/Jensen/global-minimum predicates out of
  rating-model-specific namespaces once no active agent is editing the same
  files.
- small wrappers for strict convexity/concavity plus equality-case structure.
- interval endpoint optimum lemmas for convex/concave one-dimensional
  objectives.

### 6. Threshold and sorted-prefix policies

Status: spread across auctions, admissions/testing, matching, and GN work.

Common source pattern: sort alternatives by score, then show an optimal policy
is a prefix, suffix, or threshold set.

Useful for:

- GHW digital goods and online/ad auction thresholds.
- GLM/LG testing/admissions rules.
- GN interval/threshold driver policies.
- recommendation top-k and exposure allocation rules.

Reusable target:

- score-rank prefix/suffix optimality from monotone marginal gains.
- threshold policy equivalence under monotone transformations.
- finite prefix search existence and comparison lemmas.

### 7. Static choice and binary-deviation certificates

Status: reusable core started in `Optimization.ChoiceEquilibrium` and
`Optimization.BinaryChoice`.

Common source pattern: a paper defines a static action rule, feasible actions,
best responses, and consistency; then later proof steps need only a projected
one-sided or two-sided no-profitable-deviation condition over a binary policy.

Useful for:

- GLM/LG testing papers with report/take-test versus withhold/no-test actions.
- Mechanism and platform papers that reduce equilibrium behavior to a local
  binary deviation.
- Threshold-policy proofs where no-deviation plus a tie-break identifies the
  policy as a lower or upper cutoff rule.

Reusable target:

- done: generic static equilibrium projection to one-sided and two-sided
  binary no-deviation predicates, plus a.e. equilibrium constructors from
  pointwise feasibility/best-response facts outside a null exception set.
- done: contradiction lemmas for chosen/unchosen profitable deviations and a
  threshold/tiebreak iff rule, with null-tie wrappers for continuous-law
  cutoff games.
- next: variants for multi-action menus whose proof only needs a named pair of
  deviation actions.

### 7. Minimax, Yao, and lower-bound games

Status: partially reusable in algorithms/complexity plus paper-local MSVV/GHW
certificates.

Common source pattern: exhibit a distribution over instances or a deterministic
strategy certificate, then transfer expected lower bounds through minimax/Yao.

Useful for:

- MSVV AdWords lower bounds.
- GHW digital goods lower-bound distributions.
- EC online-learning or auction lower bounds.

Reusable target:

- finite game value upper/lower certificates.
- deterministic-strategy lower-bound wrappers under a fixed input
  distribution.
- distributional lower-bound composition lemmas for independent phases.

### 8. Asymptotic optimal profiles

Status: paper-local in diversity-aware recommendation.

Common source pattern: identify a finite optimum for each scale, normalize it,
and prove convergence to an optimal continuous/profile limit.

Useful for:

- diversity-aware recommendation limits.
- market-size asymptotics in matching and auctions.
- GLM/LG testing policies under growing cohorts.

Reusable target:

- normalized finite allocation profiles.
- compactness-free epsilon certificates for asymptotic upper/lower bounds.
- transfer from finite optimality certificates to limiting optimal values.

## Promotion Rule

Upstream a lemma when it satisfies at least one of these:

- the same proof seam appears in two paper folders;
- it is a generic mathematical bridge such as weak duality, finite argmax,
  exchange optimality, or candidate-plus-bound optimality;
- a future paper would otherwise need to duplicate a certificate shell and only
  change notation.

Keep source-specific objectives, closed-form candidates, and long arithmetic
specializations inside the paper folder until a second paper needs exactly the
same algebra.
