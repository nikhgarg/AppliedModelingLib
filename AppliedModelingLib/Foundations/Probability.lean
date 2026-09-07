import AppliedModelingLib.Foundations.Probability.Admissions
import AppliedModelingLib.Foundations.Probability.Bernoulli
import AppliedModelingLib.Foundations.Probability.BrownianMotion
import AppliedModelingLib.Foundations.Probability.BoundedDensity
import AppliedModelingLib.Foundations.Probability.BoundedDifferences
import AppliedModelingLib.Foundations.Probability.MeasureBoundedDifferences
import AppliedModelingLib.Foundations.Probability.BivariateGaussian
import AppliedModelingLib.Foundations.Probability.CTMC
import AppliedModelingLib.Foundations.Probability.Conditional
import AppliedModelingLib.Foundations.Probability.CadlagPath
import AppliedModelingLib.Foundations.Probability.SkorokhodJ1
import AppliedModelingLib.Foundations.Probability.WeakConvergenceCDF
import AppliedModelingLib.Foundations.Probability.CountableMixture
import AppliedModelingLib.Foundations.Probability.ContinuousLikelihoodBurden
import AppliedModelingLib.Foundations.Probability.ContinuousReward
import AppliedModelingLib.Foundations.Probability.ContinuousStochasticDominance
import AppliedModelingLib.Foundations.Probability.Exponential
import AppliedModelingLib.Foundations.Probability.ExponentialMemoryless
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrival
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalBoundedStopping
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalBoundedStoppingBlock
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalUnboundedStopping
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalFuture
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalHeadTail
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalPostArrival
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalIncrementBoundary
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalDeterministicNoArrival
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalResidualTail
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalDeterministicResidualTail
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalTimeSliceReconstruction
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalForwardPoisson
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalNonexplosion
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCount
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalOccupation
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalCappedExit
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalMGF
import AppliedModelingLib.Foundations.Probability.PoissonMomentGenerating
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMGF
import AppliedModelingLib.Foundations.Probability.ExponentialMarkedRenewalWorkMGF
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalErlang
import AppliedModelingLib.Foundations.Probability.ExponentialGammaConvolution
import AppliedModelingLib.Foundations.Probability.ExponentialGammaCDF
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import AppliedModelingLib.Foundations.Probability.EquilibriumPoissonBase
import AppliedModelingLib.Foundations.Probability.PoissonEquilibriumHalves
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionProductFactors
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionDeterministicTimeContinuation
import AppliedModelingLib.Foundations.Probability.FairCoin
import AppliedModelingLib.Foundations.Probability.FiniteAdaptiveMGF
import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Foundations.Probability.FiniteExpectedGradient
import AppliedModelingLib.Foundations.Probability.FiniteIidMaximal
import AppliedModelingLib.Foundations.Probability.FiniteExponentialRace
import AppliedModelingLib.Foundations.Probability.FiniteEventDrift
import AppliedModelingLib.Foundations.Probability.FiniteEventIIDBridge
import AppliedModelingLib.Foundations.Probability.FiniteEventCappedStopping
import AppliedModelingLib.Foundations.Probability.FiniteEmpiricalMultinomialCounts
import AppliedModelingLib.Foundations.Probability.FiniteConstrainedDistributionalRobustness
import AppliedModelingLib.Foundations.Probability.FiniteLabel
import AppliedModelingLib.Foundations.Probability.FiniteMixture
import AppliedModelingLib.Foundations.Probability.FiniteMeasurablePartition
import AppliedModelingLib.Foundations.Probability.FiniteMultinomialEntropy
import AppliedModelingLib.Foundations.Probability.FiniteProductMultinomialCounts
import AppliedModelingLib.Foundations.Probability.FiniteProductTernaryCounts
import AppliedModelingLib.Foundations.Probability.FiniteProductCoordinateFactors
import AppliedModelingLib.Foundations.Probability.FiniteKernelProduct
import AppliedModelingLib.Foundations.Probability.FiniteKLDataProcessing
import AppliedModelingLib.Foundations.Probability.FiniteRankingEvents
import AppliedModelingLib.Foundations.Probability.FiniteSupportMGF
import AppliedModelingLib.Foundations.Probability.FiniteTypeLogMass
import AppliedModelingLib.Foundations.Probability.FiniteTransportMatrix
import AppliedModelingLib.Foundations.Probability.FinsetVariance
import AppliedModelingLib.Foundations.Probability.Gaussian
import AppliedModelingLib.Foundations.Probability.GaussianDerivatives
import AppliedModelingLib.Foundations.Probability.GaussianHazardInverse
import AppliedModelingLib.Foundations.Probability.GaussianMathlib
import AppliedModelingLib.Foundations.Probability.GaussianMills
import AppliedModelingLib.Foundations.Probability.GaussianQuantile
import AppliedModelingLib.Foundations.Probability.InformationOrder
import AppliedModelingLib.Foundations.Probability.IIDLargeDeviations
import AppliedModelingLib.Foundations.Probability.IidPrefixStopping
import AppliedModelingLib.Foundations.Probability.IidStatePrefixStopping
import AppliedModelingLib.Foundations.Probability.IidPredictableStoppedReward
import AppliedModelingLib.Foundations.Probability.IidExternalWeightedMartingale
import AppliedModelingLib.Foundations.Probability.IidExternalWeightedReward
import AppliedModelingLib.Foundations.Probability.IidStateWeightedStoppedReward
import AppliedModelingLib.Foundations.Probability.StationaryPoissonFutureInputFactors
import AppliedModelingLib.Foundations.Probability.StationaryPoissonFutureIidSection
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkFutureMarkFactors
import AppliedModelingLib.Foundations.Probability.StationaryPoissonFutureTimeSliceSection
import AppliedModelingLib.Foundations.Probability.IidSequence
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import AppliedModelingLib.Foundations.Probability.IntegralLargeDeviations
import AppliedModelingLib.Foundations.Probability.Kernel
import AppliedModelingLib.Foundations.Probability.KernelAdaptiveCap
import AppliedModelingLib.Foundations.Probability.KernelAdaptiveUnionBound
import AppliedModelingLib.Foundations.Probability.LargeDeviations
import AppliedModelingLib.Foundations.Probability.LogDensityRatio
import AppliedModelingLib.Foundations.Probability.MarkovChain
import AppliedModelingLib.Foundations.Probability.MDP
import AppliedModelingLib.Foundations.Probability.MeasureAtoms
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import AppliedModelingLib.Foundations.Probability.MovingIntervalAverage
import AppliedModelingLib.Foundations.Probability.MonotoneCounts
import AppliedModelingLib.Foundations.Probability.Occupancy
import AppliedModelingLib.Foundations.Probability.OrderStatistics
import AppliedModelingLib.Foundations.Probability.Pareto
import AppliedModelingLib.Foundations.Probability.PoissonProcess
import AppliedModelingLib.Foundations.Probability.ForwardPoisson
import AppliedModelingLib.Foundations.Probability.ForwardPoissonStopping
import AppliedModelingLib.Foundations.Probability.ForwardStoppedPoisson
import AppliedModelingLib.Foundations.Probability.MulticlassForwardPoisson
import AppliedModelingLib.Foundations.Probability.MulticlassForwardPoissonSuperposition
import AppliedModelingLib.Foundations.Probability.PoissonStopping
import AppliedModelingLib.Foundations.Probability.PoissonFiniteHorizonMarkedThinning
import AppliedModelingLib.Foundations.Probability.Processes.Palm.SelectedMarkedTransport
import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.Campbell
import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.MarkedPointSet
import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.JointFlow
import AppliedModelingLib.Foundations.Probability.Processes.Markov.StationaryTrajectory
import AppliedModelingLib.Foundations.Probability.Processes.Palm.Core
import AppliedModelingLib.Foundations.Probability.Processes.Palm.QueueLengthPASTA
import AppliedModelingLib.Foundations.Probability.PalmArrivalPath
import AppliedModelingLib.Foundations.Probability.PalmArrivalPathNonexplosion
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionFlow
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionExponentialSplit
import AppliedModelingLib.Foundations.Probability.Processes.Palm.QueueLengthPASTA
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionStationaryBase
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionBaseArrivals
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionMarkedTransport
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionCampbellBridge
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionEquilibriumSection
import AppliedModelingLib.Foundations.Probability.PalmCampbell
import AppliedModelingLib.Foundations.Probability.PalmMarkedCampbell
import AppliedModelingLib.Foundations.Probability.PalmProductTaggedArrival
import AppliedModelingLib.Foundations.Probability.PalmFiniteTaggedArrival
import AppliedModelingLib.Foundations.Probability.NormalizedKernelDensity
import AppliedModelingLib.Foundations.Probability.RandomUtility
import AppliedModelingLib.Foundations.Probability.RandomUtilityDensity
import AppliedModelingLib.Foundations.Probability.RealDistribution
import AppliedModelingLib.Foundations.Probability.RealIntervalPartition
import AppliedModelingLib.Foundations.Probability.RenewalReward
import AppliedModelingLib.Foundations.Probability.RademacherCompressedSensing
import AppliedModelingLib.Foundations.Probability.StochasticDominance
import AppliedModelingLib.Foundations.Probability.StieltjesAbsolutelyContinuous
import AppliedModelingLib.Foundations.Probability.StieltjesIntegrationByParts
import AppliedModelingLib.Foundations.Probability.SubgaussianSquares
import AppliedModelingLib.Foundations.Probability.Symmetry
import AppliedModelingLib.Foundations.Probability.Weighted
import AppliedModelingLib.Foundations.Probability.WithoutReplacement
import AppliedModelingLib.Foundations.Probability.EventuallyStableFiniteReplay
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalTwoStreamHeadTail
import AppliedModelingLib.Foundations.Probability.ExponentialRateScaling
import AppliedModelingLib.Foundations.Probability.ExponentialUnequalRateConvolution
import AppliedModelingLib.Foundations.Probability.MeasurableCountableEvaluation
import AppliedModelingLib.Foundations.Probability.MulticlassStationaryPoisson
import AppliedModelingLib.Foundations.Probability.MulticlassStationaryPoissonAdmissionWork
import AppliedModelingLib.Foundations.Probability.PalmCampbellProductLift
import AppliedModelingLib.Foundations.Probability.PalmTaggedArrivalFiniteLedger
import AppliedModelingLib.Foundations.Probability.PalmTaggedPoissonWorkFutureRate
import AppliedModelingLib.Foundations.Probability.PalmTaggedPoissonWorkFutureMGF
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkPastRate
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkFutureRate
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkFutureMGF
import AppliedModelingLib.Foundations.Probability.ResponseTailIntegrability
import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalPredecessorStateFactors

/-!
# Broad probability prelude

Legacy aggregate for the full probability development, including finite
probability, Gaussian analysis, concentration, stochastic processes,
Palm/Poisson theory, and queueing-specific constructions. This remains a
supported compatibility import, but new paper interfaces should normally use
the smallest leaf module or one of these curated family entrypoints:

- `AppliedModelingLib.Foundations.Probability.Finite`
- `AppliedModelingLib.Foundations.Probability.GaussianModels`
- `AppliedModelingLib.Foundations.Probability.Concentration`
- `AppliedModelingLib.Foundations.Probability.Processes`
- `AppliedModelingLib.Foundations.Probability.PoissonPalm`

## Main declarations

- Finite PMF expectation/probability APIs:
  `AppliedModelingLib.Foundations.Probability.FiniteExpectation`,
  `AppliedModelingLib.Foundations.Probability.FiniteExpectedGradient`,
  `AppliedModelingLib.Foundations.Probability.Conditional`,
  `AppliedModelingLib.Foundations.Probability.Kernel`,
  `AppliedModelingLib.Foundations.Probability.FiniteMixture`, and
  `AppliedModelingLib.Foundations.Probability.FiniteLabel`.
  `FiniteExpectation` includes iid finite-product PMFs, coordinate-dependent
  product-event factorization, option-extension product decompositions, and
  finite-product reindexing/binomial success-count formulas.
  `FiniteExpectedGradient` supplies the exact finite-PMF
  gradient/expectation interchange used by smooth stochastic optimization.
- Continuous measure and concentration helpers:
  `AppliedModelingLib.Foundations.Probability.Bernoulli`,
  `AppliedModelingLib.Foundations.Probability.BoundedDensity`,
  `AppliedModelingLib.Foundations.Probability.ContinuousReward`,
  `AppliedModelingLib.Foundations.Probability.MeasureInequalities`,
  `AppliedModelingLib.Foundations.Probability.FairCoin`, and
  `AppliedModelingLib.Foundations.Probability.FinsetVariance`.
- Large-deviation scaffolding:
  `AppliedModelingLib.Foundations.Probability.FiniteSupportMGF`,
  `AppliedModelingLib.Foundations.Probability.FiniteMultinomialEntropy`,
  `AppliedModelingLib.Foundations.Probability.FiniteProductMultinomialCounts`,
  `AppliedModelingLib.Foundations.Probability.IIDLargeDeviations`,
  `AppliedModelingLib.Foundations.Probability.IntegralLargeDeviations`, and
  `AppliedModelingLib.Foundations.Probability.LargeDeviations`.
- Finite information orders:
  `AppliedModelingLib.Foundations.Probability.InformationOrder`.
- Order-statistic interfaces:
  `AppliedModelingLib.Foundations.Probability.OrderStatistics`.
  This includes finite at-most-`k` top-sum maximization and tuple-level
  order-statistic integration interfaces, plus pointwise top-k sample-extension
  and two-level top-mass marginal bounds. It also provides the bridge from an
  upper-order-statistic threshold event to an iid strict-success count, finite
  iid expected top-k wrappers, and option-step marginal identities for adding
  one iid draw.
- Real distribution tail/CDF helpers:
  `AppliedModelingLib.Foundations.Probability.RealDistribution`.
- Continuous heavy-tail distribution helpers:
  `AppliedModelingLib.Foundations.Probability.Pareto`, including finite iid
  product-measure wrappers, closed-form Pareto upper-tail/CDF mass, and
  threshold-count and upper-order-statistic survival binomial formulas, plus
  support-scale tail-integral reductions.
- Dynamic and stochastic-process support:
  `AppliedModelingLib.Foundations.Probability.MarkovChain`,
  `AppliedModelingLib.Foundations.Probability.MDP`,
  `AppliedModelingLib.Foundations.Probability.CTMC`, and
  `AppliedModelingLib.Foundations.Probability.RenewalReward`.
  `AppliedModelingLib.Foundations.Probability.PoissonProcess` includes reusable
  Poisson count likelihoods, no-arrival and interarrival-tail kernels, ordered
  observation windows, thinning-count algebra, homogeneous process-law
  interfaces, and finite-product likelihood collapses for event-count
  observation models. `ExponentialInterarrival` constructs the canonical iid
  exponential product space and a first-arrival natural-filtration/stopping
  certificate. `ExponentialInterarrivalForwardPoisson` builds its canonical
  renewal count into a concrete forward-time Poisson process with finite
  independent increments; it intentionally makes no all-times, stationary,
  or Palm-process claim.
  `Queueing` supplies deterministic FCFS comparator transfers, while
  `QueueingGeometric` proves the exact geometric state tail and independent
  product-space coupling used by the M/M/1 calculation. `QueueingMM1` proves
  the analytic stationary-M/M/1 count mixture conditional on an explicit
  stationary/Palm tagged-arrival coupling and records the no-atom strict-to-
  weak tail bridge.  These modules do not derive a queue's geometric
  stationarity, construct the Palm law, or derive the fluid-GPS recurrence.
  `QueueingPostTagFalseMarkCount` names the actual false-edge potential-service
  count on a tagged gap/marked path and proves its structural measurability,
  bounds, and monotonicity.  On the direct selected marked-Palm M/M/1 path,
  `QueueingMM1ForwardReverseMarkedPalmPostTagCount` now proves its fixed-
  horizon marked-thinning Poisson law and its independence from the selected
  pre-arrival queue state; it does not construct response dynamics or GPS.
  `ForwardPoisson` supplies a probability-law interface for forward
  nonnegative-time Poisson counts after a tag, and `PalmArrivalPath` constructs
  a two-sided iid-exponential-gap candidate tagged path with its arrival at
  time zero. `PalmProductTaggedArrival` independently adjoins that path to a
  supplied base law, proves exponential tagged-gap laws and base/gap
  independence, and proves the resulting product PASTA queue-state
  certificate. It can also adjoin a stationary embedded trajectory while
  retaining its coordinate marginal, while explicitly not calling any of
  these product laws a Campbell/Palm transform. `PalmFiniteTaggedArrival`
  identifies every finite block of post-tag gaps and cumulative epochs with
  the corresponding iid exponential and finite-arrival density laws.
  `PalmPASTA` makes the remaining stationary-base versus Palm-tagged-law
  distinction explicit and derives tagged queue-state tails from a supplied
  PASTA identity. `PalmCampbell` now states a verifiable finite-window
  Campbell/Palm certificate, including recentering and locally finite arrival
  enumeration, so a paper-facing theorem can require genuine Palm provenance.
  `EquilibriumPoissonBase` constructs the correct origin-split equilibrium
  configuration, finite exact window enumerators, and unmarked intensity
  calibration, while `PoissonSuspensionFlow` constructs and normalizes the
  measurable exponential special flow. Its countable good-carrier partition
  now proves the real-time action and measure preservation, and
  `PoissonSuspensionStationaryBase` packages it as a genuine
  `ShiftInvariantProbabilityLaw`. `PoissonSuspensionBaseArrivals` supplies
  its concrete arrivals, recentering, exact finite enumerators, and every
  non-mass-transport field of the Campbell certificate.
  `PoissonSuspensionExponentialSplit` proves the local exponential
  residual/age split for the origin-straddling Palm gap.
  `PoissonSuspensionMarkedTransport` proves the fixed-index branch transport
  and already packages the resulting genuine stationary Campbell/Palm
  certificate. Independently, `PoissonEquilibriumHalves`,
  `PoissonSuspensionProductFactors`, and
  `PoissonSuspensionCampbellBridge` now prove the full
  suspension-to-equilibrium measure identity by tensorizing the central-gap
  residual/age split with the two iid tails. The direct marked certificate and
  this equilibrium-coordinate identity are separate from PASTA, which remains
  a separate queue-state theorem.
  `PalmRenewalService` independently adjoins a concrete canonical
  iid-exponential renewal-service path to an already tagged arrival law and
  derives the fixed-horizon Poisson completion-count law and queue/count
  independence needed by the M/M/1 calculation. For the canonical renewal
  time at a measurable queue index, it also derives measurability, the a.e.
  response/count event identity, and atomlessness, yielding a fully concrete
  count-level certificate once the inherited queue tail is supplied. This
  product construction is intentionally not a stationary Campbell/Palm
  construction and makes no independent-increments claim.
  `ForwardStoppedPoisson` precisely packages the still-needed strong-Markov
  conditional law for a count increment after a forward stopping time and
  derives its exponential survival consequence; fixed-time independent
  increments alone do not imply that field.
  `ForwardPoissonStopping` supplies the compatible forward natural filtration
  and native first-count-arrival stopping-time certificate needed to connect a
  concrete post-tag or post-incident count path to that stopped-law boundary.
  `ExponentialMemoryless` proves the full measure-level deterministic
  residual law for a positive-rate exponential variable: after survival past
  a fixed elapsed time, its shifted residual is the original exponential
  measure scaled by the survival mass.
  `ExponentialInterarrivalResidualTail` lifts that identity to an iid
  interarrival path after a fixed first-gap survival event, preserving the
  entire residual path law up to its survival mass.
  `ExponentialInterarrivalFuture` proves deterministic-index regeneration of
  the iid exponential path and its next-gap stopping-time bridge; it does not
  promote that fact to a conditional or infinite-tail strong-Markov law.
  `ExponentialInterarrivalBoundedStopping` proves that the first uninspected
  coordinate after a bounded prefix-measurable discrete stopping index retains
  the exponential law, while keeping the conditional and whole-future-tail
  strong-Markov upgrades explicit.
  `ExponentialInterarrivalBoundedStoppingBlock` extends this to every finite
  post-stop block, with its full iid exponential product law, but remains a
  bounded-index finite-horizon result.
  `ExponentialInterarrivalUnboundedStopping` removes the bounded-index
  condition for every total prefix-measurable discrete index and proves the
  same finite post-stop iid block law.  It does not assert an infinite shifted
  tail, a conditional law, or a continuous-time strong-Markov theorem.
  `ExponentialInterarrivalNonexplosion` proves almost-sure divergence of the
  canonical one-sided renewal epochs and finiteness of the arrivals before
  every finite time, but does not turn those epochs into an all-times Poisson
  count process.
  `ExponentialInterarrivalRenewalCount` supplies that measurable one-sided
  renewal count, its threshold/cardinality identities, and its natural
  filtration, while leaving Poisson increment and strong-Markov laws open.
  `ExponentialInterarrivalErlang` proves that each finite arrival epoch has
  the repeated exponential-convolution law. `ExponentialGammaConvolution`
  identifies every canonical `arrivalTime n` and positive
  `postTagArrival (n + 1)` with its positive-integer Gamma law, while
  `ExponentialGammaCDF` proves the corresponding finite Erlang CDF series.
  `ExponentialInterarrivalRenewalCountMarginal` combines these results to
  prove the canonical renewal count's full fixed-time Poisson PMF and
  `HasLaw` statement. It still does not establish Poisson increments,
  stationary two-sided counts, or a continuous-time strong-Markov theorem.
  `ExponentialInterarrivalPostArrival` upgrades that fixed-time statement at
  every deterministic arrival index: the post-arrival count is a fresh-tail
  count and has the Poisson law. It also exposes the full finite pre-arrival
  prefix as independent of the entire future tail. It is not a
  deterministic-clock increment theorem.
  `ExponentialInterarrivalIncrementBoundary` then proves the exact
  a.e. pathwise deterministic-clock increment identity in terms of a
  residual tail. `ExponentialInterarrivalDeterministicNoArrival` discharges
  the zero-increment consequence at every deterministic nonnegative clock by
  summing the countable straddling-gap fibers, proving the exact no-arrival
  exponential tail. `ExponentialInterarrivalDeterministicResidualTail` then
  proves that the complete residual path at any nonnegative deterministic
  clock has the original iid exponential law and consequently that every
  deterministic nonnegative-time increment has its Poisson law. It also
  proves that the accumulated count is independent of that residual path and
  of the immediately following deterministic increment.
  `ExponentialInterarrivalForwardPoisson` recursively upgrades this to finite
  joint independent increments and constructs the canonical forward
  `ForwardHomogeneousPoissonCountingProcessByLaw`. It does not establish a
  stationary two-sided count or a random/stopping-time result.
  `QueueingMM1Stationary` proves that the normalized geometric mass satisfies
  detailed and global generator balance for stable M/M/1 rates, while leaving
  the countable nonexplosive-CTMC and generator-to-semigroup construction
  explicit.
  `QueueingMM1Uniformization` upgrades that mass to an invariant PMF for the
  reflected countable uniformized birth--death jump kernel through detailed
  balance and identifies that PMF exactly with Mathlib's geometric measure,
  but does not yet construct its continuous-time Poisson-clock path.
  `QueueingMM1Kernel` lifts countable PMF kernels (including augmented
  state/mark spaces) to Mathlib's `Kernel.Invariant` interface and proves
  invariance for every finite kernel power.
  `QueueingMM1Trajectory` constructs the stationary Ionescu--Tulcea embedded
  trajectory and proves all of its marginals geometric, while leaving the
  continuous-time Poisson-clock time change explicit.
  `QueueingMM1TrajectoryTransition` proves its full finite-prefix-to-next
  recurrence, stationary consecutive-pair law, and exact initial/`n`-step pair
  law `π ⊗ₘ K^n`. `PoissonFiniteHorizonMarkedThinning` constructs a literal
  finite-horizon Poisson count with an iid finite Boolean mark vector and
  proves the exact product-of-Poisson law for its retained and discarded mark
  counts. This is a count-and-mark construction, not yet a point-process path,
  Palm law, or PASTA theorem. `QueueingMM1MarkedUniformization` makes each reflected
  M/M/1 edge an explicit Bernoulli arrival/potential-service mark and proves
  that the stationary pre-edge state and recovered mark have the product law;
  its marked tail event consequently factors as well. This is embedded-time
  only, not thinning or PASTA.
  `QueueingMM1MarkedStateTrajectory` upgrades this to a literal augmented
  state `(Q_n, M_n)` chain: it proves the geometric-state/Bernoulli-mark PMF
  is invariant, its state/current-mark coordinate has the exact product law,
  and two consecutive marks on its stationary Ionescu--Tulcea trajectory have
  the Bernoulli product law. `QueueingMM1MarkedSuspension` then defines the
  pathwise real-time action that couples a good Poisson suspension to a
  two-sided embedded path, synchronizing event relabeling with its clock
  crossing index. Its checked skew-product transfer now proves real-time
  measure preservation, and packages a `ShiftInvariantProbabilityLaw`, for
  any embedded path law invariant under every integer relabeling. Supplying
  that full invariant M/M/1 path law remains separate, so neither module yet
  claims thinning, Palm, or PASTA semantics.
  `QueueingMM1TwoSidedMarkedFactor` gives a compatible route to that path: it
  recovers every mark from a reversible unmarked trajectory edge, proves that
  edge-marking commutes with integer reindexing, and gives the exact
  state/current-mark product law at every integer index. It likewise stops
  short of full path shift invariance.
  `QueueingMM1TwoSidedMarkedSuspension` forms the resulting two-sided marked
  M/M/1 path together with the good Poisson suspension, yielding the concrete
  product measure on which the timed action is defined and retaining every
  coordinate's state/mark law. The generic invariant skew-product bridge is
  now available. `QueueingTwoSidedFullStationarity` supplies the required
  full integer-shift invariant law for the forward/reverse carrier.
  `QueueingMM1ForwardReverseMarkedSuspension` additionally supplies the
  stationarity-facing carrier: it edge-marks the generic forward/reverse
  two-sided M/M/1 construction, records the detailed-balance reverse-pair
  condition and its time-zero geometric/Bernoulli law, and packages the exact
  route from a full unmarked shift theorem to a real-time stationary marked
  suspension. Its product suspension also retains the embedded time-zero
  geometric/Bernoulli marginal and its elementary arrival-mark/state-tail
  factorization. Conditioning its true embedded mark gives a probability
  path with the same geometric pre-arrival tail, and pairing that path with a
  tagged Poisson-gap path gives a literal `TaggedArrivalAtZero` candidate.
  `QueueingMM1ForwardReverseMarkedPalm` now invokes the full shift theorem,
  the product Campbell lift, and selected-point covariance to construct a
  genuine stationary Palm certificate for true M/M/1 arrivals; at the
  uniformization clock its intensity is exactly the physical arrival rate.
  It also packages the matching geometric law of the base and selected-tag
  embedded coordinate-zero queue statistic as a PASTA certificate.  Its
  direct selected tag additionally has verified finite iid mark prefixes and,
  through the path-derived false-mark count, fixed-horizon marked thinning
  and queue/service-count independence. This is not yet a real-time
  queue-occupancy construction: response dynamics and GPS
  response dynamics remain separate obligations.
  `QueueingSelectedMarkedPalm` supplies the checked selection algebra once a
  marked all-event Campbell certificate is available: conditioning preserves
  the tag-at-zero and strict-arrival facts, a true-zero-mark slice factors
  exactly, and the selected Campbell count has intensity `rate * p`.
  `QueueingTimedEmbeddedCampbell` now proves that all-event certificate for
  a Poisson suspension with any independent embedded path law invariant under
  every integer relabeling, and `QueueingTimedEmbeddedMarkedPointSet` proves
  that its selected marked point set covaries under the real-time flow.
  `PalmMarkedCampbell` packages these facts as a genuine selected marked
  Campbell/Palm certificate using the all-event enumeration plus a covariant
  Boolean selector, avoiding a noncanonical separate re-enumeration of the
  surviving true points.
  `QueueingMM1TwoSidedTrajectory` constructs a state-anchored
  integer-indexed embedded trajectory and, under detailed balance, proves its
  cross-zero pair has the stationary transition law. The generic
  `QueueingTwoSidedReverseTrajectory` instead accepts a forward and reverse
  kernel with an explicit pair-balance condition, proving the same one-edge
  shift consistency without assuming reversibility. It also exposes exact
  cross-zero and forward triple and four-coordinate laws and derives their
  one-step shift equalities from pair balance by conditional-Fubini
  reordering. Neither construction
  claims full integer-shift invariance or Palm semantics.
  `QueueingTwoSidedReverseFiniteWindows` extends that generic construction to
  arbitrary cross-zero windows and arbitrary pure-past reverse prefixes, each
  with an explicit finite-dimensional law under pair balance.
  `QueueingTwoSidedFullStationarity` completes the mixed-window recurrence,
  reindexes finite integer intervals, and applies the cylinder criterion to
  prove full integer-shift measure preservation.
  `QueueingTwoSidedPathCylinder` proves the generic final extension principle:
  equality of every finite contiguous integer-window restriction determines a
  two-sided product-path probability law, and hence establishes a measurable
  integer relabeling as measure-preserving; it is now used by the full
  forward/reverse stationarity proof.
  `QueueingMM1TwoSidedTrajectoryShift` proves that every adjacent embedded
  window has the stationary transition law under detailed balance; the
  forward/reverse construction's full path invariance is now supplied by
  `QueueingTwoSidedFullStationarity`.
  `QueueingMM1TrajectoryTimeChange` turns the `n`-step law into the exact
  mixture for an exogenous measurable index on a separate product-space
  clock factor. `QueueingMM1TrajectoryPoissonClock` specializes that mixture
  to a supplied forward Poisson clock and proves the fixed-time joint
  state--external-clock-count product law for uniformized M/M/1, including
  the rate-aligned clock marginal. These remain fixed-time independent-product
  results: they do not prove marked thinning, a CTMC semigroup, a Palm law, or
  PASTA.
  `PalmArrivalPathNonexplosion` transfers canonical renewal nonexplosion to
  both gap directions of the candidate tagged path, without claiming a
  Campbell/Palm identity or stationary Poisson increments.
  `PalmPASTAMM1` turns a supplied geometric stationary base-state law into the
  pre-arrival tagged tail needed by the M/M/1 response certificate through the
  explicit PASTA state-law bridge.
- Finite sampling and occupancy tools:
  `AppliedModelingLib.Foundations.Probability.Weighted`,
  `AppliedModelingLib.Foundations.Probability.WithoutReplacement`, and
  `AppliedModelingLib.Foundations.Probability.Occupancy`.
- Admissions/testing and stochastic-order wrappers:
  `AppliedModelingLib.Foundations.Probability.Admissions`,
  `AppliedModelingLib.Foundations.Probability.BivariateGaussian`,
  `AppliedModelingLib.Foundations.Probability.Gaussian`,
  `AppliedModelingLib.Foundations.Probability.GaussianMathlib`,
  `AppliedModelingLib.Foundations.Probability.GaussianMills`,
  `AppliedModelingLib.Foundations.Probability.GaussianDerivatives`,
  `AppliedModelingLib.Foundations.Probability.GaussianQuantile`,
  `AppliedModelingLib.Foundations.Probability.GaussianHazardInverse`, and
  `AppliedModelingLib.Foundations.Probability.StochasticDominance`.
  `BivariateGaussian` includes correlated standard-Gaussian laws and
  independent two-coordinate Gaussian product/variance-scaling bridges for
  RUM-style conditional winner-ratio proofs.
- Random-utility noise, contraction, and density-product inequalities:
  `AppliedModelingLib.Foundations.Probability.RandomUtility` and
  `AppliedModelingLib.Foundations.Probability.RandomUtilityDensity`.
-/
