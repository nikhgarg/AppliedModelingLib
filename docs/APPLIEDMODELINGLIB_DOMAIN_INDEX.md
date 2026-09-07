# AppliedModelingLib Domain Index

This file tracks where reusable declarations live and where to start reading
when you need material from a domain quickly.

This is a curated discovery index, not dependency evidence. Lean's loaded
environment remains authoritative for declarations and imports. The root
`import AppliedModelingLib` is intentionally broad, so start from
the narrow entrypoints below. For repository layers and workflow boundaries,
see [Architecture](ARCHITECTURE.md). The
[optimization roadmap](OPTIMIZATION_LIBRARY_ROADMAP.md) describes planned
optimization extensions.

## Foundations

- Entrypoint: `AppliedModelingLib.Foundations`
- Narrow entrypoints: `AppliedModelingLib.Foundations.Math`,
  `AppliedModelingLib.Foundations.Computation`,
  `AppliedModelingLib.Foundations.Graph`,
  `AppliedModelingLib.Foundations.Probability.Finite`,
  `AppliedModelingLib.Foundations.Probability.GaussianModels`,
  `AppliedModelingLib.Foundations.Probability.Concentration`,
  `AppliedModelingLib.Foundations.Probability.Processes`,
  `AppliedModelingLib.Foundations.Probability.PoissonPalm`,
  `AppliedModelingLib.Foundations.Optimization`,
  `AppliedModelingLib.Foundations.Econometrics`
- Modules:
  - `AppliedModelingLib.Foundations.Computation`:
    `ThreeCNF`, `RealReluCircuit`, `BooleanCircuit`
    - `ThreeCNF`: typed finite three-CNF semantics, mutually compatible
      literal selections, and satisfiability-preserving finite padding.
    - `RealReluCircuit`: finite scalar affine/ReLU syntax, evaluation and
      node counts, unit-box literal/clause/formula circuits, and the checked
      threshold-one equivalence for three-CNF with a linear node bound.
  - `AppliedModelingLib.Foundations.Math`:
    `FiniteSum`, `FiniteRanking`, `FiniteRounding`, `FiniteSigns`,
    `Sequence`, `Asymptotics`, `ConvexCombination`, `IntervalCrossing`,
    `EpsilonContinuity`, `PositiveDenominator`, `AffineThreshold`,
    `ThresholdCharacterization`, `PairCondition`, `ExponentialBounds`
    - `FiniteSum`: finite weighted-sum bounds, injective subfamily sum
      comparisons, weighted-share race bounds, finite averaging/cardinality
      lower bounds, Cauchy-Schwarz, ordered-pair double-sum regrouping by an
      injective key, pairwise cross-ratio-to-weighted-average comparisons, and
      finite telescoping/crossing helpers.
    - `FiniteRanking`: finite-set ranking by real scores with deterministic
      tie-breaking, lower/upper rank prefix sets, rank-prefix cardinalities,
      rank-prefix monotonicity, and lower-vs-upper score comparisons.
    - `Asymptotics`: `TendsToZero` helpers, inverse-rate and inverse-square-root
      rate bridges, `1 / log n` and `log n / sqrt n` limit helpers,
      asymptotic-equivalence ratio/sandwich helpers, bounded-ratio-to-zero
      lemmas, fixed finite-sum assembly over a common scale, negligible
      remainder addition on that scale, nonnegative `C / n` domination,
      finite-prefix replacement for zero-convergent schedules, and
      order-closed limit comparison for real sequences.
    - `ConvexCombination`: two-point weighted averages, denominator
      positivity from positive/nonnegative weights, componentwise above/below
      target comparisons, weighted-gap sign comparisons, and continuity of
      parameterized weighted averages. Use this for LG-style pooled estimates
      before adding paper-local fraction algebra.
    - `ThresholdCharacterization`: one-dimensional monotone cutoff lemmas,
      lower/upper cutoff strategies, compact interval crossings, unbounded
      continuous strict-monotone/strict-antitone crossing, and strict-antitone
      capacity cutoffs with the upper-region characterization
      `{z | f z <= level} = {z | cutoff <= z}`; includes
      `CapacityThreshold` for source-facing capacity equation plus upper-region
      characterizations.
    - `PairCondition`: exact-one-of-two propositional packaging for
      two-branch source cases, including bridges from qualified cutoff
      case analyses and finite pair membership.
    - `ExponentialBounds`: elementary `exp`/`log` inequalities for finite
      probability products, including `exp(-2/x) <= 1 - 1/x` for `x >= 2` and
      its finite-power form.
    - `EuclideanNets`: volumetric finite nets for unit spheres and closed
      balls in finite-dimensional real normed spaces, bounded-subset nets whose
      centers remain in the subset (including the zero-radius case), and
      finite-net lifting bounds for symmetric quadratic forms.
  - `AppliedModelingLib.Foundations.Graph`
  - `AppliedModelingLib.Foundations.Optimization`
    (`Approximation`, `Argmax`, `Certificate`, `PointwiseSupremum`, `FiniteSearch`,
    `LinearProgram`, `MoveGraph`, `ChoiceEquilibrium`, `ChoiceEquilibriumAE`,
    `BinaryChoice`, `BinaryChoiceAE`, `BinaryPolicyGame`,
    `StrategicEquilibrium`, `Endpoint`)
    - `Approximation`: benchmark/dual upper-bound sandwich certificates for
      approximation and competitive-ratio proofs, including additive-error
      variants.
    - `Argmax`: finite argmax, pointwise maximization, average/expected
      objective wrappers, monotone and finite-linear expectation interfaces,
      and finite posterior-score decision optimality.
    - `Certificate`: feasible-value sets, maximizer/minimizer predicates,
      candidate-plus-upper-bound and candidate-plus-lower-bound certificates,
      and strict variants for uniqueness/structure proofs.
    - `PointwiseSupremum`: bounded pointwise real suprema, penalized-payoff
      stability, antitonicity, convexity on a convex penalty domain, and an
      explicit relative-penalty modulus from bounded loss and a zero-cost
      reference action, all without an assumed maximizer; measurable-selection
      claims stay explicit in the consuming paper model.
    - `FiniteSearch`: optimizer existence over nonempty finite feasible
      subtypes, decidable finite feasible predicates, and finite codes that
      cover a feasible region.
    - `LinearProgram`: standard finite maximization LPs with nonnegative
      variables and `Ax <= b`, primal/dual feasibility, finite weak duality,
      support/active-constraint scaffolds, and primal/dual optimality
      certificates.
    - `MoveGraph`: reusable exchange/local-move optimality, proving global
      maximization or minimization from reachability and objective monotonicity
      along feasible moves.
    - `ChoiceEquilibrium`: static choice-equilibrium data, feasibility,
      best-response, and consistency projections.
    - `ChoiceEquilibriumAE`: almost-everywhere choice-equilibrium data for
      continuous or mixed information laws, including a constructor from
      pointwise feasibility and best response outside a null exception set.
    - `BinaryChoice`: two-action no-profitable-deviation predicates,
      projections from static choice equilibria, and threshold/tiebreak
      consequences for binary choice rules.
    - `BinaryChoiceAE`: almost-everywhere binary no-profitable-deviation
      predicates, conversions to and from raw Boolean best-response clauses,
      off-null-set constructors, a.e. projection from choice equilibria,
      no-tie/null-tie threshold identification, and affine cutoff consequences.
    - `BinaryPolicyGame`: two-player binary policy equilibrium predicates,
      low/high case-split iff theorems, feasible-policy variants, and
      objective-comparison bridges for policy-pair games.
    - `StrategicEquilibrium`: combined agent/policy equilibrium data with
      almost-everywhere agent feasibility and best-response projections,
      policy best-response projections, and consistency projections.
    - `Endpoint`: one-dimensional endpoint-move calculus from derivative
      signs, first/last-zero stopping lemmas, and one-sided local
      improvement/decrease steps for cutoff and interval-endpoint proofs.
    - `SmoothComposition`: global value, derivative-norm, and
      derivative-Lipschitz bounds under composition, with continuous linear
      maps as zero-curvature layers; the reusable analytic core for the
      SNVD17 neural-network smoothness calculation.
    - `DualStrongConcaveArgmax` and `DualSmoothEnvelope`: arbitrary-real-norm
      dual-space stability of attained strongly-concave argmax selections and
      Fréchet-differential smoothness of their pointwise envelopes.  These
      retain explicit attainment and feasible-direction first-order conditions
      rather than silently identifying a derivative with a Hilbert gradient.
    - `CoordinatewiseSmooth`: dimension-free lifting of scalar value,
      derivative-norm, and derivative-Lipschitz bounds to finite Euclidean
      coordinatewise maps.
    - `AveragePooling`: finite Euclidean average-pooling operators with the
      `sqrt(overlap * maxSize) / minSize` bound and constant derivative.
    - `StandardActivations`: checked scalar and finite-coordinate sigmoid and
      scale-one ELU maps, with the dimension-free constants used by SNVD17.
    - `FiniteSoftmax`: finite Euclidean softmax probabilities, the sharp
      dimension-free softmax-Jacobian operator bound, global softmax
      Lipschitzness, and a negative-log-softmax first-order smooth map with
      value/gradient bound `sqrt 2` and derivative smoothness `1`.
    - `SquaredLInfProx`: finite decreasing-sort active-index selection, the
      corrected threshold equation, and coordinatewise clipping as a global
      minimizer of the squared-sup-norm proximal objective.
    - Queueing externality pricing lives at
      `AppliedModelingLib.Queueing.ExternalityPricing`; the former optimization
      path was removed after every live consumer migrated.
    - Roadmap: [`docs/OPTIMIZATION_LIBRARY_ROADMAP.md`](OPTIMIZATION_LIBRARY_ROADMAP.md)
      tracks finite feasible search, exchange optimality, LP certificates,
      convexity/Jensen wrappers, threshold policies, minimax/Yao certificates,
      and asymptotic allocation profiles.

  - `AppliedModelingLib.Foundations.Probability`: broad compatibility prelude. Prefer
    one of the following family entrypoints for new code:
    - `Probability.Finite`: finite PMFs, expectations, mixtures, iid samples,
      finite kernels, atoms, and simplex representations.
    - `Probability.GaussianModels`: Gaussian analytic interfaces, finite
      Gaussian models, signal kernels, changes of measure, and hazard/quantile
      calculations.
    - `Probability.Concentration`: finite-sample concentration, independent
      bounded variables, finite iid measure-product decompositions for
      arbitrary-law bounded-difference arguments, large-deviation interfaces, deterministic empirical
      and population cover bridges, and finite-cover lifts from a
      general-measure empirical process to a finite center class (including
      IID score classes with bounded intervals `[a,b]`, specialized when useful
      to scores normalized from `[0,B]`).  It also provides one-sided
      finite-bracket transfers: a finite family of lower/upper brackets with
      controlled population width reduces a non-finite class to Hoeffding
      concentration of the lower brackets.
    - `Probability.ConvergingTogether`: bounded-Lipschitz approximation
      bounds, common-space perturbation transport, and extended
      continuous-mapping theorems for maps continuous almost everywhere under
      the limiting law, including maps known measurable only after
      composition with the random inputs.
    - `Probability.SkorokhodJ1`: finite- and local-horizon `J₁` path spaces,
      explicit Borel structures, finite-step measurability, and deterministic
      convergence transport. Local convergence is preserved by negation and
      by adding a second convergent path sequence when its limiting path is
      continuous; this does not claim global continuity or Borel
      measurability of addition at arbitrary jump-path pairs. The
      `ContinuousLocalPath` subtype records the valid right-continuity
      premise and supports the corresponding topological addition map.
    - `Probability.Processes`: iid sequences, finite and continuous-time
      Markov models, MDPs, and Poisson-process primitives.
    - `Probability.PoissonParameterKernel`: the measurable Markov kernel from
      a nonnegative Poisson mean to its count, for genuinely random exposure
      constructions rather than parameterized-law assertions.
    - `Probability.PoissonMoments`: Poisson first, second, and centered
      moment identities, including the square about an arbitrary fixed real
      center used in random-exposure variance calculations.
    - `Probability.PoissonPalm`: Poisson primitives, tagged-arrival paths, and
      explicit Palm/Campbell/PASTA interfaces.

    The broad compatibility surface currently includes
    (`FiniteExpectation`, `FiniteMixture`, `FiniteLabel`, `FiniteSupportMGF`, `FiniteRatingComparison`, `Kernel`, `Conditional`,
    `FiniteTransport`, `FiniteDistributionalRobustness`,
    `FiniteConstrainedDistributionalRobustness`, `FiniteTransportMatrix`,
    `LargeDeviations`, `OrderStatistics`, `RealDistribution`, `MarkovChain`, `CTMC`, `MDP`,
    `RenewalReward`, `ContinuousReward`, `Gaussian`, `BivariateGaussian`,
    `StochasticDominance`, `MeasureInequalities`,
    `Occupancy`, `Admissions`, `FairCoin`, `Weighted`, `WithoutReplacement`,
    `RandomUtility`, `RandomUtilityDensity`)
    - `FiniteConstrainedDistributionalRobustness`: finite constrained-DRO
      weak and strong duality, attained transport couplings, penalized-argmax
      source laws, exact robust-value identities at achieved graph radii, and
      the test-certificate sandwich from pointwise budget-feasible attacks to
      constrained transport values to penalized envelopes.
    - `MeasureTransport`: arbitrary probability couplings and marginal
      integration, including real expected-cost transport witnesses and an
      epsilon-optimal weak penalized-DRO certificate for an infimum-defined
      real transport ball.  It does not assume an optimal plan, strong
      transport duality, or a measurable pointwise optimizer.
    - `FiniteExpectation`: finite PMF expectations/probabilities, relabeling,
      product-uniform decompositions, event-probability congruence, finite
      identical-product PMFs and all-coordinate event probabilities,
      singleton/product atom probabilities, PMF map/bind probability and
      expectation decompositions,
      uniform product collision probabilities, prescribed-coordinate
      probabilities and collision probabilities for uniform finite functions,
      uniform event-probability relabeling, pointwise range relabeling for
      uniform finite function spaces and injective finite-function subtypes,
      expected finite-count linearity, finite union bounds, reciprocal-count
      perturbation bounds, expected-count lower bounds from uniformly likely
      finite subfamilies, event-indicator expectation upper bounds, independent
      pair indicator-event factorization, finite-PMF variance, second-moment
      formulas for indicator counts, pairwise-negative-correlation variance
      bounds, and Chebyshev lower-tail wrappers.
    - `FiniteMixture`: binary PMF mixtures, finite event shares, indexed
      positive-event-or-blank splits, blank-on-zero-share indexed values,
      positive-share mixture cancellation, PMF pushforward support lemmas, and
      raw-relevance equivalences for event-share binary mixtures.
    - `FiniteLabel`: finite-label indicator integrals, label shares, aggregate
      score masses, pointwise posterior-simplex API, bounded finite-label
      score integrability, simplex mass-sum identities, finite-label MAE
      bounds/integrability, and the bridge from finite PMF expectations to the
      abstract `Decision.FiniteLinearExpectation` optimizer interface.
    - `Kernel`: finite prior/signal-kernel joint laws and signal marginals,
      real signal probabilities, posterior expectation formulas,
      denominator-clearing and constant-one posterior identities, posterior
      nonnegativity/upper/interval bounds, and finite law-of-iterated
      expectation for kernel joint laws.
    - `Conditional`: finite PMF conditional expectations and conditional
      probabilities, denominator-clearing and constant-one conditional
      expectation identities, indicator-expectation bounds,
      nonnegativity/upper/interval conditional-expectation bounds,
      event-intersection/product/complement formulas,
      congruence of conditional target events on the conditioning event,
      full conditional-probability congruence for equivalent conditioning
      events, conditioning-on-sure-event simplification,
      nested-event product lower bounds from per-step conditional lower bounds,
      finite-state conditional-mixture/refinement upper bounds and equalities,
      and the algebraic bridge from conditional negative dependence to pairwise
      negative correlation.
    - `MeasureInequalities`: real-valued measure/probability wrappers,
      finite-subset mass transfer, positivity bridges from nonzero finite
      `ENNReal` mass to real-valued mass, positive finite `withDensity` mass,
      boundary-null a.e. congruence for functions, predicates, Boolean
      indicators, set indicators, and strict/weak real cutoffs, positive-mass
      contradictions for a.e. weak/strict inequalities, selected-below-
      reference a.e. implication contradictions and cutoff-event positive-mass
      transfers, null
      symmetric-difference congruence for adding/removing common context sets
      and merging touching intervals/rays up to null endpoints, plus
      finite-intersection probability lower bounds and Hoeffding-style
      independent bounded-sum bounds.
    - `ContinuousReward`: accepted-set mass/time/reward primitives over
      positive real domains, reward/time union and difference formulas,
      measure-zero component simplifications, average-reward comparison from
      pointwise inequalities, renewal-reward and average-reward aliases,
      add/remove marginal renewal-rate comparisons, zero-component
      union/difference invariance, and positive-domain bridges from zero
      accepted time to zero accepted mass.
    - `Gaussian`: Gaussian location-scale standardization, an abstract
      standard-normal CDF/density API, conjugate one-signal posterior
      precision/variance/mean formulas, posterior-mean monotonicity, finite
      signal-family posterior mean monotonicity, posterior weights, and
      posterior-mean law wrappers, posterior-variance reduction under finite
      signals, nonzero-noise-mean signal centering, posterior/raw-signal
      threshold conversion, positive-affine location-scale transformations,
      threshold pass-probability monotonicity in cutoffs and means,
      finite-mixture tail mass/capacity certificates, and a hazard-rate
      certificate boundary with location-scale tail positivity, density/tail
      hazard conversion, upper-tail conditional mean monotonicity, hazard
      domination of positive standardized thresholds, upper-tail mean-above-
      threshold certificates, positive Gaussian mass from a threshold to its
      upper-tail conditional mean, and finite-mixture admitted-mean accounting
      for GLM/LG-style testing papers.
    - `BivariateGaussian`: correlated standard-Gaussian product laws,
      coordinate projections/no-atoms, Owen affine standardization and
      vertical/horizontal boundary-zero helpers, plus independent Gaussian pair
      measures with arbitrary standard deviation, canonical variance-`1/2`
      scaling, strict winner-below-cutoff and both-below-cutoff events, and the
      reusable strict conditional winner-ratio scaling bridge for RUM Gaussian
      reductions.
    - `FiniteSupportMGF`: finite-support MGF/log-MGF algebra, Legendre
      objectives, real and `WithTop` rate-function scaffolding, and finite
      rating-scale LDP model wrappers for rating-system large-deviation proofs,
      including `withTopRealScale`, `FiniteRatingLDPModel.rateFunctionTop`,
      `FiniteRatingLDPModel.pairwiseRateObjectiveTop`, and
      `FiniteRatingLDPModel.pairwiseThresholdRateTop`.
    - `FiniteRatingComparison`: finite-rating pairwise comparison
      infrastructure for finite rating-system proofs:
      source-facing log-MGF/rate wrappers, support-safe pairwise threshold
      rates, tilted score means, two-sample and floor-count comparison
      probabilities, finite `P_k`/`1 - P_k` algebra, integer-rate block
      comparisons, and pairwise LDP certificate constructors reusable by finite
      rating-scale large-deviation papers.
    - `LargeDeviations`: negative normalized log-decay rates, exact
      exponential-rate certificates, eventual exponential upper-bound
      and lower-bound certificates, conversion from exact rates to weaker
      upper/lower bounds, finite weighted-sum aggregation, and pairwise
      ranking-error aggregation certificates, with aggregate lower bounds from
      a single positive-weight component or one certified pairwise error.
    - `OrderStatistics`: top-`k` expected-value oracles, marginal top-`k`
      values, diminishing/nonnegative marginal predicates, finite-type
      scaled-marginal limit certificates, bottom-indexed
      `μ(rank, sampleSize)` mean bridges, and eventual multiplicative
      marginal sandwiches and strict marginal comparisons from scaled weight
      gaps for diversity-aware recommendation style order-statistic proofs.
    - `RealDistribution`: lower CDF mass, upper-tail mass, CDF/tail
      monotonicity, `ProbabilityTheory.cdf` identification, and upper-tail
      complement formulas plus threshold/capacity certificates for real-valued
      threshold and order-statistic proofs.
    - `Weighted`: finite normalized weighted PMFs over nonnegative real
      weights, filtered/excluding-set weighted PMFs, available-mass splitting,
      available-subtype weighted PMFs, full-support available-mass positivity,
      constant-scaling of available mass, and the `p_w / (1 - prevMass)` atom
      formula for finite without-replacement deferred-decision draws.
    - `WithoutReplacement`: recursive finite weighted sampling without
      replacement over structurally fresh lists, cons/tail projection helpers,
      finite prefix sets, omission-event positivity under full support,
      first/head-tail/conditional-tail laws, atom product and atom-sum event
      formulas, positive constant-scaling invariance for event and conditional
      probabilities, pointwise-weight convergence for fixed fresh-list events,
      and the positive prefix-set next-draw law
      `finiteWithoutReplacementPMF_prefixSet_conditional_next_prob_excluding`.
    - `Occupancy`: used/empty-bin sets, ordered first-hit balls and first-hit
      cardinality, occupancy PMF, reciprocal empty-bin expectations, used-bin
      subset/equality comparisons, bin/domain relabeling for used and empty
      bins, one-ball recurrence bounds.
    - `RandomUtility`: additive-noise well-ordering predicates, Gaussian and
      Laplacian density kernels, one-coordinate contraction geometry,
      three-alternative top/bottom preservation and swap-middle geometry, and
      pointwise `swap12`/`swap23` density-product comparisons for continuous
      RUM proofs.
    - `RandomUtilityDensity`: three-coordinate additive-RUM score densities,
      density measurability/positivity/normalization helpers, finite atom
      density-swap mass comparisons, and continuous `withDensity` swap
      comparisons for measure-preserving score-coordinate maps.
  - `AppliedModelingLib.Foundations.Econometrics`
    (`RatingModels`)

## Queueing

- Entrypoint: `AppliedModelingLib.Queueing`
- Narrow entrypoints:
  - `AppliedModelingLib.Queueing.GPS`: deterministic fluid-GPS comparison,
    almost-everywhere service-rate floors, and normalized GPS allocation.
    The narrow owner modules are `Queueing.GPS.Core`,
    `Queueing.GPS.AERateFloor`, and `Queueing.GPS.AENormalizedAllocation`.
  - `AppliedModelingLib.Queueing.GPS.FiniteHorizon`: executable finite GPS traces,
    segment and FCFS projections, completion accounting, reset/fence proofs,
    and their measurability layer. Its declaration owners live under the same
    queueing subtree. This larger family is intentionally not imported by the
    basic `Queueing.GPS` entrypoint.
  - `AppliedModelingLib.Queueing.MM1`: reusable M/M/1 response-time formulas and the
    queueing-domain interfaces they consume.
  - `AppliedModelingLib.Queueing.ExternalityPricing`: queueing externality prices and
    marginal-cost identities.
  - `AppliedModelingLib.Queueing.NonpreemptivePriority`: base nonpreemptive-priority
    model; import narrower trace, stationarity, or performance leaves when
    extending those proof families.
  - `AppliedModelingLib.Queueing.ManyServerDiffusionPath`: one-dimensional
    additively driven queue-diffusion paths, including global and
    source-domain (`[0, ∞)`) relations, Grönwall stability bounds, and local
    `J₁` convergence of solutions from converging forcing paths and initial
    states. It also supplies the solvable source-domain input subtype and a
    selected solution map continuous at continuous forcing paths, for
    relation-based weak-convergence transports.
  - `AppliedModelingLib.Queueing.RenewalArrival`: deterministic renewal
    arrival epochs and completed-arrival counts on nonexplosive gap paths,
    together with an iid-product Borel--Cantelli bridge proving nonexplosion
    from nonnegative gaps and positive mass above one fixed threshold; import
    a probability model separately for renewal-limit results.
  - `AppliedModelingLib.Queueing.ManyServerServiceSemigroup`: the zero-arrival
    specialization of the many-server uniformized kernel, Poissonized at the
    aggregate service-clock rate; it supplies the exact arrival-free
    exponential-service transition semigroup.
  - `AppliedModelingLib.Queueing.RandomDurationKernel`: Poissonizes a
    countable potential-event kernel at a measurable random nonnegative
    exposure and retains the initial state, producing a genuine Markov
    transition kernel.

## Applications

- Entrypoints: `AppliedModelingLib.Applications.Admissions`,
  `AppliedModelingLib.Applications.RecommenderSystems`
- Admissions modules:
  - `PolicySurface`: compact policy surfaces for group fairness, individual
    fairness, group academic-merit improvement, and diversity improvement.
  - `StrategicPolicy`: two-school/two-group policy surfaces, override rows,
    weighted objectives, and groupwise objective-comparison algebra.
  - `StrategicApplication`: reusable student application cutoffs, payoffs, and
    two-school application-region definitions.
- Recommender-systems modules:
  - `Policy`, `Allocation`, `AllocationSequence`
  - `Classwise`, `PolicyAveraging`
  - `Allocation`: finite integer allocations, total/support/share/objective
    primitives, one-unit move/marginal interfaces, weighted forward/backward
    marginals, exchange conditions, fixed-total optimality, exact exchange
    objective accounting, finite FOC lemmas, diminishing-returns marginal
    monotonicity, large scaled-gap-to-FOC contradiction bridges, finite-prefix
    scaled-count bounds from positive weight floors, share nonnegativity and
    sum-to-one facts, finite count-pigeonhole facts, plus the generic pairwise
    scaled-count to weighted target count-closeness bridge, scaled-count to
    target-share closeness bridges, and uniform-average count-balance bridges
    `Allocation.exists_count_gt_of_card_mul_lt_total` and
    `Allocation.count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded`,
    `Allocation.count_abs_sub_uniform_average_le_C_of_pairwise_bounded`, and
    `Allocation.count_abs_sub_uniform_average_le_one_of_pairwise_balanced`;
    it also includes `Allocation.FeasibleCode` and
    `Allocation.exists_isOptimalAtTotal` for finite fixed-total count-objective
    maximization.
  - `AllocationSequence`: feasible and optimal fixed-total allocation
    sequences, uniform target-share approximation, coordinatewise convergence
    to target profiles, asymptotic profile targets over generic fixed-total
    objectives, and reusable endpoints turning sublinear pairwise scaled-count
    bounds, FOC large-gap dominance, or floor-aware/eventual FOC dominance into
    asymptotic profile convergence. Use
    `Allocation.PairwiseScaledSublinearProfileCertificate`,
    `Allocation.PairwiseScaledSublinearFOCCertificate`, and
    `Allocation.PairwiseScaledEventualSublinearFOCCertificate` when a paper
    wants certificate-shaped hypotheses with conversion methods.

## Mechanism Design

- Entrypoint: `AppliedModelingLib.MechanismDesign.Auctions`
- Modules:
  - `DigitalGoods`, `Combinatorial`
    - `DigitalGoods`: prior-free digital-goods auction primitives and
      paper-facing revenue/truthfulness support.
    - `Combinatorial`: direct combinatorial auctions, generalized Vickrey
      auctions, single-minded bid profiles, weighted set-packing encodings,
      LOS02 greedy allocation/payment support, and abstract reduction/complexity
      wrappers.

## Markets

- Entrypoint: `AppliedModelingLib.Markets.Matching`
- Modules:
  - `Matching/Basic`, `Matching/DeferredAcceptance`, `Matching/ManyToOne`
    - `Basic`: one-to-one assignment API, side swapping, woman-side relabeling
      of assignments, stability, and stability invariance under side swapping
      and woman-side relabeling.
    - `DeferredAcceptance`: one-to-one DA, strict/all-acceptable domains,
      proposer optimality, uniqueness of men-optimal stable matchings,
      women-proposing role reversal, women-optimality, women-pessimality,
      men-pessimality of women-proposing DA, stability, DA completeness, and
      stable-completeness on equal-size all-acceptable markets.

## Learning

- Entrypoint: `AppliedModelingLib.Learning.Bandits.ThompsonSampling`
- Modules:
  - Bayesian-bandit primitives and posterior update lemmas used by papers

## Algorithms

- Entrypoints: `AppliedModelingLib.Algorithms.Online`,
  `AppliedModelingLib.Algorithms.Complexity.Classes`,
  `AppliedModelingLib.Algorithms.Complexity.ReluVerification`,
  `AppliedModelingLib.Algorithms.Complexity.Yao`
- Modules:
  - `Online/AdWords`, `Online/Regret`
  - `Complexity/Classes`: abstract decision-problem, reduction,
    reduction-closed hardness, randomized-class collapse, and
    complexity-consequence interfaces for paper-local reductions
  - `Complexity/ReluVerification`: bundled finite three-CNF and scalar-ReLU
    threshold languages, a checked direct many-one reduction with linear
    circuit size and zero/one constants, conditional polynomial-hardness
    transfer, and the one-call exact-optimizer bridge
  - `Complexity/Yao`: finite expectation algebra for Yao-style lower-bound
    certificates

## Social Choice

- Entrypoint: `AppliedModelingLib.SocialChoice`
- Narrow entrypoints: `AppliedModelingLib.SocialChoice.FairDivision`,
  `AppliedModelingLib.SocialChoice.Ranking`
- Modules:
  - `FairDivision/IndivisibleGoods`, `FairDivision/BoundedEnvyAlgorithm`
  - `Ranking/Basic`, `Ranking/Kendall`, `Ranking/Probability`,
    `Ranking/Approval`, `Ranking/Mallows`, `Ranking/MallowsPayoff`,
    `Ranking/MallowsRankFactorization`, `Ranking/MallowsSequential`,
    `Ranking/Payoff`, `Ranking/RankPower`, `Ranking/Score`,
    `Ranking/Sequential`, `Ranking/SequentialPayoff`
    - `Ranking/Basic`: finite candidate universes with at least two
      candidates, full rankings as permutations, top-two choices, top-two
      swaps, rank lookup, and the "best remaining after one candidate is
      removed" primitive used by sequential selection proofs.
    - `Ranking/Kendall`: inversion predicates/finsets, Kendall tau distance,
      first/second-choice deletion formulas, relabeling through `cycleRange`
      and `cycleIcc`, center-transposition invariance, and center-order value
      gap predicates.
    - `Ranking/Probability`: discrete measurable-space instance for ranking
      spaces, `firstChoiceProb`, pushforward PMFs from continuous ranking maps,
      and event-probability bridges for first-choice and best-remaining events.
    - `Ranking/Approval`: finite K-approval score indicators, pair-up/down/zero
      event probabilities, score-gap event equivalences, first/two-approval
      decompositions, and all-but-one approval facts such as `lastRank`,
      `approvedByK_allButOne_iff_rankOf_ne_lastRank`,
      `kApprovalPairUpProb_allButOne_eq_rankOf_lastProb`, and
      `kApprovalPairDownProb_allButOne_eq_rankOf_lastProb` for GGSG-style
      one-loser/Mallows boundary arguments.
    - `Ranking/Mallows`: finite Mallows weights and partition functions,
      normalized Mallows-law specifications, first/first-second/pair-correct
      and pair-wrong weights/probabilities, and finite partition/probability
      normalization identities.
    - `Ranking/MallowsPayoff`: Mallows first-choice value-gap weights,
      `firstChoiceGapMass` normalization, miss-probability denominator forms,
      and positive-denominator clearing lemmas for finite Mallows payoff sums.
    - `Ranking/MallowsRankFactorization`: assumption-driven Mallows
      rank-factorization packages and algebra for first-choice tails,
      removal-renormalized rank sums, and first-weight prefixes. Concrete
      source-specific factorization constructors stay in paper files until
      their fiber decompositions are reusable.
    - `Ranking/MallowsSequential`: Mallows best-in-feasible-set fiber weights,
      pair/correct-wrong fiber identities, swap-reindexed fiber sums,
      fiber-partition normalization, expected best-in-set payoff normalization,
      and the cross-ratio bridge from Mallows fibers to expected best-in-set
      dominance.
    - `Ranking/Payoff`: first-choice miss probabilities, top-vs-runner-up
      value gaps, first/second-mover utility primitives, pair-lifted
      reranking gains, independent-reranking and weak-competition preference
      predicates, first-choice gap masses, collision-probability differences,
      disagreement-conditional gain forms, finite first-choice fiber
      decompositions, welfare decompositions, and first-mover-law switch payoff
      identities for ranking laws.
    - `Ranking/RankPower`: finite geometric rank-power sums, prefix sums,
      removal-renormalized rank sums, best-after-removal rank weights,
      positivity/closed-form geometric identities, and rank-power
      cross-ratio helpers used by Mallows rank-factorization proofs.
    - `Ranking/Score`: pure three-score ranking maps for three-candidate
      comparisons, concrete score-induced rankings, no-tie and score-order
      predicates, first/second-choice simplification, best-remaining-after-one
      simplification, and score-order implications from first-choice or
      best-remaining outcomes.
    - `Ranking/Sequential`: probability-free best-in-set and
      candidate-position swap helpers for sequential choice proofs, including
      `bestInSet`, rank-minimality/membership lemmas, center-rank relabeling,
      `swapCandidatePositions`, its involutive equivalence, rank extensionality
      helpers, deterministic best-in-set value improvement from correcting an
      inverted pair, and adjacent-correction reachability/monotonicity
      predicates such as `AdjacentSwapImproves`, `AdjacentCorrection`,
      `WeakBruhatLe`, and `SwapImprovesOn`; it also owns bounded prefix-cut
      indicators such as `deleteFirstChoicePrefixCut`,
      `bestInSetPrefixCutIndicator`, `centerPrefixCutValue`, and
      `adjacentSwapImproves_bestInSetPrefixCutIndicator`.
    - `Ranking/SequentialPayoff`: finite PMF expectations of the best feasible
      candidate, including `expectedBestInSet`, `expectedBestAfterRemoval`,
      and full-set/singleton/removed-singleton simplification lemmas.

## Navigation tips

- Use the domain entrypoint as the first import from that area.
- Then import narrower modules only when you need paper-specific helper lemmas.
- New reusable theorems should land under `AppliedModelingLib/`; paper-specific proof
  code should remain in `papers/`.
