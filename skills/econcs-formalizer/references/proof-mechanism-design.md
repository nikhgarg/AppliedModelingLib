# Mechanism Design and Auctions

Use for `AppliedModelingLib/MechanismDesign/Auctions/*`, digital goods, GSP/position
auctions, combinatorial auctions, and generic mechanism-design wrappers.

## Digital Goods and Posted Prices

- When starting a mechanism-design or auction paper, first look at nearby
  formalized papers and `AppliedModelingLib/MechanismDesign` for proof moves that should
  become reusable EC infrastructure. Build the reusable layer during the paper
  proof when it directly helps the active theorem and is likely useful for
  another auction/mechanism paper.
- For strategic papers with continuous types, endogenous ranks, cutoffs, or
  null-set tie behavior, include a shared-library reuse checkpoint in the paper
  plan before adding local equilibrium or distribution interfaces. Inspect the
  generic optimization, probability, admissions/testing, and mechanism-design
  modules for the proof shape, then route the paper proof through the matching
  shared API. If no API fits, document the exact missing abstraction and keep
  the paper-local replacement narrow enough to extract later.
- For auction papers, attack the named theorem through the shortest faithful
  model level. Finite bidder models are often right for digital goods, but do
  not build a finite analogue as ritual if the paper statement or proof closes
  more directly through a certificate, threshold characterization, or
  expectation interface.
- For admissions/testing strategic-threshold games, separate payoff
  threshold algebra from endogenous equilibrium existence. First prove the
  binary action payoff cutoff using the displayed probability law and inverse
  CDF, then add a paper-facing wrapper that expands any projected Gaussian
  scale into the source precision expression. Leave global fixed-point or
  school-threshold uniqueness as the next explicit seam rather than hiding it
  inside the cutoff lemma.
- For strategic threshold uniqueness proofs, strengthen weak cutoff
  best-response statements to strict payoff order away from the cutoff before
  attacking the fixed point. The reusable route is: strict inverse-CDF tail
  lemmas in `StandardGaussianQuantileAPI`, strict payoff/probability algebra,
  then a paper-facing theorem saying apply strictly dominates above the cutoff
  and not applying strictly dominates below it.
- For continuous Gaussian strategy games, default to an a.e. equilibrium
  surface for strategy, best-response, uniqueness, and cutoff-boundary claims;
  do not force pointwise best response at null cutoff boundaries unless the
  paper explicitly needs it. The reusable library surface is
  `AppliedModelingLib.IsChoiceEquilibriumAE` with projections
  `isChoiceEquilibriumAE_feasible_ae`,
  `isChoiceEquilibriumAE_best_response_ae`,
  `isChoiceEquilibriumAE_consistency`, the pointwise bridge
  `isChoiceEquilibriumAE_of_pointwise`, and the off-null-set constructor
  `isChoiceEquilibriumAE_of_forall_not_mem_null`.
- For binary cutoff strategies with null boundaries, use
  `AppliedModelingLib.NoProfitableBinaryChoiceDeviationAE` and
  `bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_no_tie`
  before writing paper-local a.e. case splits. If the payoff is affine with a
  positive slope, `chosen_reference_le_value_ae_of_affine_noProfitableBinaryChoiceDeviationAE`
  and `unchosen_value_le_reference_ae_of_affine_noProfitableBinaryChoiceDeviationAE`
  extract the cutoff-side inequalities directly. Use
  `noProfitableBinaryChoiceDeviationAE_of_bool_best_response_ae` and
  `bool_best_response_ae_of_noProfitableBinaryChoiceDeviationAE` to move
  between raw `∀ action : Bool` best-response clauses and the named predicate.
  If the only discrepancy is strict versus weak cutoff syntax at a null
  indifference level, use `ae_iff_le_lt_of_level_null`,
  `ae_iff_lt_le_of_level_null`, `ae_eq_decide_of_ae_iff`, or
  `ae_eq_if_of_ae_iff` from `MeasureInequalities` instead of adding a
  paper-local tie-convention field. When the proof already has a null payoff
  tie set, use
  `choice_rule_iff_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie`
  or
  `bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie`
  directly.
- LG21 is the nearest model for Gaussian reporting/taking games with null
  boundary behavior. Its route defines `lg21SourceEquilibriumAE` in
  `papers/LG21TestOptionalPolicies/Theorem32AEEquilibrium.lean`, exposes
  `lg21SourceEquilibriumAE_of_sourceEquilibrium`, and then proves a.e.
  best-response consequences such as
  `lg21OptionalReportingBaseSourceEquilibriumData_actorMean_le_reported_score_ae`
  plus contradiction bridges like
  `lg21_ae_property_contradicts_positive_failure_mass`. When a similar proof
  starts treating an indifference cutoff as a pointwise obligation, inspect
  these released wrappers before adding new assumptions.
- Reuse the LG21 pattern at the library layer, not by copying LG21-specific
  wrappers: project an a.e. equilibrium to `IsChoiceEquilibriumAE`, project
  binary actions to `NoProfitableBinaryChoiceDeviationAE`, derive affine
  chosen/unchosen inequalities with the positive-slope helpers, and use
  `ae_property_contradicts_positive_failure_mass` for any positive-mass
  violation. Keep pointwise equilibrium wrappers only as compatibility bridges
  into the a.e. public theorem.
- For two-school strategic application regions, define the incremental payoff
  explicitly before proving best response: below the fallback school's cutoff
  the value is the preferred-school value, while above it the incremental value
  is the value difference. Prove the low/high cutoff region iff nonnegative
  incremental payoff, then separately prove the region indicator pointwise
  maximizes the binary apply/not-apply payoff.
- To prove uniqueness of a threshold/region strategy, first prove strict
  payoff signs away from every cutoff and then assume only the paper's
  tie-breaking convention at cutoff points. Split on the region boundary
  predicates, force the strategy by pointwise best-response inequalities in
  strict branches, and use the tie-breaking hypotheses only in equality cases.
- For school capacity fixed points, separate the scalar cutoff theorem from the
  probabilistic applicant-mass formula. First prove a reusable theorem that a
  continuous strictly decreasing applicant-mass function with end limits
  `totalMass` at `-∞` and `0` at `+∞` has a unique capacity cutoff and sublevel
  region. Then instantiate continuity, monotonicity, and limits from the
  paper's Gaussian or strategic applicant-mass expression.
- For strategic admissions cost-threshold arguments, do not hide the
  intermediate-value step inside an opaque certificate. Prove or reuse a
  one-dimensional decreasing-crossing theorem first: a continuous strictly
  decreasing merit term with opposite endpoint comparisons gives a positive
  threshold and exact weak/strict side characterizations. In `AppliedModelingLib` this
  is the role of
  `exists_threshold_of_continuous_strictAntiOn_Icc_crossing` and
  `exists_threshold_le_of_continuous_strictAntiOn_Icc`. When the source proof
  uses an actual cost interval such as `[0,v]`, prefer the interval theorem
  `exists_threshold_of_continuous_strictAntiOn_Icc_crossing_interval` or the
  paper wrapper over normalizing to `[0,1]` unless normalization makes the
  concrete algebra easier.
- If the source derives cost-monotonicity indirectly, keep that structure in
  Lean. Prove the cost-to-cutoff map is continuous/strictly increasing, prove
  the cutoff-to-merit map is continuous/strictly decreasing, and compose them
  via `continuousOn_comp_of_mapsTo`, `strictAntiOn_comp_strictMonoOn`, or the
  paper wrapper
  `paper_proposition5_cost_merit_continuous_strictAntiOn_of_cutoff_strictMono`.
  This is usually faster and more auditable than assuming a black-box
  cost-to-merit monotonicity fact.
- If a monotone-composition theorem has a `Set.MapsTo` premise only because
  the cutoff-domain was stated abstractly, immediately add the `Set.univ`
  specialization when the concrete merit formula is real-valued. This removes
  a noisy obligation from downstream paper wrappers. Prefer `_univ` entry
  points for cost-threshold lemmas whenever no smaller domain is needed.
- For two-school full-test application payoffs, encode the displayed CDF
  expression first and prove monotonicity directly from signs. A typical term
  has negative CDF coefficients, while each standardized cutoff
  `(q_i - q) / scale` strictly decreases in projected skill `q`; strict CDF
  monotonicity plus `0 < v2 < v1` closes the "student strategy is threshold
  form" monotonicity claim before any school fixed-point work.
- When the paper solves an indifference equation with an inverse CDF, first
  prove the algebraic CDF equation from the zero-payoff equation, then apply the
  quantile API with the probability-domain premise explicit. Do not spend time
  deriving `(0,1)` membership from economic assumptions until the formula
  theorem itself is green; expose that domain as the next paper-facing
  obligation.
- To prove a cutoff increases in cost, use zero comparison and strict payoff
  monotonicity rather than differentiating the implicit inverse-CDF formula.
  Since cost usually enters as `-c`, evaluate the higher-cost payoff at the
  lower-cost zero to get a negative value, then strict monotonicity in skill
  forces the higher-cost zero to lie to the right.
- After the two-point cutoff-in-cost comparison is proved, immediately package
  the function-level version: any selected cutoff function satisfying the
  zero-payoff equation at each cost is `StrictMonoOn` over the cost domain.
  This is the form needed for later monotone-composition and
  threshold-crossing arguments.
- When a zero-payoff cutoff solves an equation of the form
  `basePayoff q - cost = 0`, do not leave selected-cutoff continuity as a
  certificate.  Prove the selected cutoff is a right inverse of the strictly
  increasing `basePayoff`, then apply
  `continuousOn_rightInverse_of_strictMono`.  This yields selected-cutoff
  continuity without differentiating the implicit equation.
- For two-policy school games, define a concrete binary-policy surface whose
  equilibrium predicate unfolds to the weighted objective best-response
  condition before writing high-level theorem wrappers.  This removes repeated
  assumptions of the form "policy-pair equilibrium iff binary equilibrium" and
  keeps the paper-facing theorem focused on mass, merit, no-tie, and cutoff
  premises.  After the surface is defined, add a theorem specialized to that
  surface at the lowest useful bridge layer, so later wrappers take only the
  objective-condition proofs rather than reintroducing the binary-equilibrium
  equivalence as a hypothesis.
- When a full/full equilibrium claim says both schools keep the current policy
  iff two cost-boundary inequalities hold, prove the source composition
  generically: if each school's keep region has boundaries
  `(cA <= fA_i cB, cB <= fB_i cA)`, the joint equilibrium region uses the
  pointwise minima of the two schools' boundaries.  This is faster and more
  faithful than constructing fixed-cost boundary constants.
- When a paper condition requires two ordered cost thresholds from related
  monotone merit crossings, construct both roots in one wrapper and prove the
  ordering there instead of passing a loose `lowRoot < highRoot` premise
  through downstream statements. Build both crossings, expose each side
  characterization, and prove the strict root ordering from the high-threshold
  merit comparison at the lower root.
- After constructing ordered thresholds, immediately compose them with the
  paper's mass/cutoff equivalences and companion school objective split if
  this yields a named condition bundle. This avoids leaving a proved threshold
  lemma disconnected from the paper theorem.
  Apply the same pattern to one-threshold cases: after constructing a
  condition threshold, compose it with mass/cutoff identities and weighted
  objective bookkeeping when that closes a named source-condition bundle.
- Once the part-level condition bundles are proved, add the paper-level wrapper
  immediately if it is mostly existential packaging. Construct the threshold
  functions from the part-level merit crossings and compose them with the
  binary policy-equilibrium bridge. This gives the human-facing file one
  theorem to audit before proving the concrete objective premises.
- After proving a strategic payoff is continuous and strictly increasing, use a
  generic crossing lemma before specializing tail limits. The reusable theorem
  `existsUnique_zero_and_nonneg_iff_of_continuous_strictMono_crossing` turns
  one negative payoff point and one positive payoff point into a unique cutoff
  and an exact nonnegative upper-threshold region.
- When a condition wrapper assumes an objective comparison is equivalent to a
  merit inequality, immediately add the formula-level version if the source
  proof actually identifies the two objective values separately. The bridge is
  usually elementary rewriting, and it keeps the concrete-model target as
  value equalities rather than custom iff lemmas.
- When a strategic proof says a mass inequality is "equivalent" to a cutoff
  case, check whether the mass is simply a strictly antitone upper-tail
  function evaluated at the cutoff. If so, prove a tiny paper-facing bridge
  with `StrictAnti.lt_iff_gt`: `M = K cutoff` gives
  `M < K reference ↔ reference < cutoff`, and
  `M > K reference ↔ cutoff < reference`. This is much faster than expanding
  Gaussian integrals or tail formulas again, and it keeps the paper statement
  auditable.
- When a two-group strategic proof is a source-level case split ("no group
  triggers the cutoff case", "both groups trigger it but that is impossible",
  "only group A triggers it", "only group B triggers it"), first package that
  logic as an exact-one propositional bridge. Then plug in the economic
  qualifiers and mass/cutoff translations separately. This avoids duplicating
  symmetric case analysis inside every paper-facing objective theorem.
- When a school-deviation objective premise includes a displayed weighted
  academic-merit inequality plus a separate mass feasibility condition, split
  the bridge into bookkeeping facts instead of assuming the whole iff. First
  rewrite each objective value to the source weighted-merit expression, carry
  the mass feasibility hypothesis separately, and add a no-tie premise if the
  source uses a strict inequality but the game objective is weak preference.
  Then compose that smaller bridge into the paper-facing equilibrium wrapper.
- When generated policy-state tables leave many branch-conditioned
  posterior/admitted-merit row equalities, create a compact row-package
  structure and a packaged objective bridge before attacking the source game.
  The concrete Bayesian-game proof should target that package with a.e.
  strategy and posterior-law facts, while the already-compiled bridge handles
  table bookkeeping and weighted-objective algebra. This avoids repeatedly
  threading flat `honlyA`/`honlyB` premises through Theorem 3 and Proposition 5
  wrappers.
- For strategic admissions equilibrium theorems that are still certificate
  based, make the certificate target source-shaped before doing fixed-point
  work. Define the paper's displayed inequalities, exactly-one-group clauses,
  policy-pair notation, and threshold-mass functions as Lean `Prop`/`def`
  declarations, then let the certificate prove the concrete game satisfies
  those definitions. This makes the human-facing theorem auditable and prevents
  opaque fields like `subFullEquilibriumIff : Prop` from hiding whether the
  Lean statement actually matches the paper.
- For strategic applicant-pool fixed points, do not treat applicant mass as an
  exogenous scalar function if the paper's capacity equation first substitutes
  student application thresholds. Define the self-consistent mass map
  explicitly by substituting the group cutoff into the application-gated joint
  applicant mass before solving capacity, then prove the `∃!` equilibrium
  against that map. This isolates the analytic obligations as identification
  and regularity of the application-gated mass rather than vague "equilibrium
  consistency".
- Reuse the shared admissions, testing, optimization, and game modules before
  adding paper-local strategic scaffolding. Search
  `AppliedModelingLib.Applications.Admissions.PolicySurface`,
  `AppliedModelingLib.Applications.Admissions.StrategicPolicy`,
  `AppliedModelingLib.Applications.Admissions.StrategicApplication`,
  `AppliedModelingLib.Foundations.Optimization.StrategicEquilibrium`,
  `AppliedModelingLib.Foundations.Optimization.ChoiceEquilibriumAE`, and
  `AppliedModelingLib.Foundations.Optimization.BinaryPolicyGame` during intake. If a
  paper-local alias unfolds to a shared definition, add the shared definition
  to the local `simp` or `unfold` list rather than changing the source-facing
  theorem statement.
- For application-gated strategic applicant masses, a fast source-faithful route
  is to formalize the joint event before the closed-form CDF. Define
  `π_g * P(q_sub >= qApply, q_full >= qAdmit)` as a measure-backed upper-orthant
  mass, prove moving-threshold continuity/strict decrease/endpoints from finite
  open-positive nonatomic joint laws, then compose those component facts through
  the finite group-sum fixed point. Keep the bivariate-normal/Owen-CDF identity
  as the remaining analytic identification seam rather than blocking the source
  equilibrium theorem on the displayed formula.
- When the paper's named equilibrium lemma only needs the application-gated
  source event and the closed-form bivariate/Owen expression is introduced in a
  later proposition, close the equilibrium lemma at the density-backed source
  event surface.  Prove open-positive and boundary-null regularity from
  normalized positive Lebesgue densities, mark the named lemma green there, and
  track the Owen/CDF identity under the proposition that actually uses the
  displayed formula.
- For strategic diversity criteria that compare two schools' group shares,
  split the proof into mass bookkeeping before analytic identities.  First
  define the paper's displayed group masses (`D_g`, tail mass, and case-split
  combinations) and prove the reusable algebra
  `mass_1 / C_1 > mass_2 / C_2 ↔ mass_1 / mass_2 > C_1 / C_2` under positive
  capacities and positive denominator mass.  Then leave only the model-side
  Gaussian/Owen integral identities as the concrete analytic seam.
- For bivariate CDF/Owen selection formulas, peel off the measure bookkeeping
  before attempting Gaussian density algebra.  A common bracket
  `Phi(A) - Phi_2(A,B;rho)` is just the vertical strip mass
  `P(Z_1 <= A, B <= Z_2)` once the first marginal CDF, lower-left bivariate
  CDF, and zero horizontal-boundary mass are known.  Prove this generic strip
  identity first, then separately prove the transformed Gaussian law supplies
  the advertised CDFs.
- For Owen affine selection identities, avoid formalizing tabulated integrals
  directly when a Gaussian linear-map proof is shorter.  Define the
  standardizing map `(X,Z) ↦ ((X - c Z)/sqrt(1+c^2), Z)`, prove its law equals
  the correlated standard-Gaussian law with
  `rho = -c/sqrt(1+c^2)` by `charFunDual`/product Gaussian characteristic
  functions, and then prove the affine event preimage is the vertical strip.
  This gives a reusable source-affine mass bridge before any first-moment
  Owen identity is attempted.
- For Owen first-moment identities, prove the standardized analytic identity
  in the shared Gaussian library first, then bind source scaling afterward. The
  useful route is product-density completion of squares for
  `∫ phi(z) phi(A*sqrt(1+c^2)+c*z)`, integration by parts for
  `∫ z*phi(z)*Phi(A*sqrt(1+c^2)+c*z)`, and integrability by bounding shifted
  densities plus splitting the `z*phi(z)` tail at zero. Keep the displayed
  paper formula separate from the verified upper-tail endpoint until the
  source scaling is checked; if they differ by a boundary term, add an audit
  theorem proving equality only in the degenerate case or proving non-equality
  under ordinary nonzero assumptions. For finite enrollment regions, derive
  finite-interval product-density and first-moment theorems by subtracting two
  proved upper-tail identities before doing any paper-specific algebra.
- For `kappa`-style lower-tail Owen first moments, it can be faster and more
  faithful to prove the lower-tail theorem directly once the upper-tail route
  has supplied the integration-by-parts pattern. Add the shared identities
  `standardGaussianDensity_mul_affine_integral_Iic` and
  `standardGaussian_firstMoment_affineCDF_integral_Iic` to the probability
  library, then expose paper wrappers for
  `∫_{-∞}^{q} z φ(z) Φ(A*sqrt(1+c^2)+c*z) dz`. Then add a thin source-scaling
  bridge if the displayed expression differs only by a density scaling or
  cutoff substitution. Keep that premise explicit: a source-specific prefactor
  or boundary-density argument is an additional obligation, so the normalized
  lower-tail integral alone does not prove the full displayed formula.
  If the source density is raw normal rather than standard normal, prove the
  reusable scaling fact `scale * normalDensity L raw = phi (L.standardize raw)`
  once and then use a source-density formula wrapper, instead of forcing the
  paper formula to pretend every density argument is already standardized.
  In Lean statements, parenthesize `c * (∫ ...) - boundary`; otherwise the
  parser may absorb the subtraction into the integrand and waste a proof loop.
- Keep lower-tail selection masses separate from lower-tail product-density
  terms. In integration-by-parts proofs, `∫ phi(z) * phi(offset+c*z)` is only
  the derivative/product term, while the admitted/enrolled mass is
  `∫ phi(z) * Phi(offset+c*z)`. If the paper's normalized merit formula has a
  `mu * mass / tau` term, the mass premise must refer to the affine-CDF
  selection integral or its measure-event wrapper, not the product-density
  integral. A fast audit is to name both declarations explicitly, e.g.
  `OwenProductLowerTail` versus `OwenSelectionLowerTail`, before wiring the
  final `kappa` bridge.
- When a two-school proof writes the nonpreferred school's mass as
  `eligible tail - D_g`, first prove the algebraic CDF bookkeeping before
  attacking source densities: if the eligible tail is
  `pi * sigmaTilde * Phi(A)` and `D_g = pi * sigmaTilde * (Phi(A)-Phi_2)`,
  then the residual is `pi * sigmaTilde * Phi_2`. This often turns a confusing
  "lower-tail mass" obligation into two smaller seams: the affine total-mass
  substitution and the integral/event identity for the lower rectangle.
- When a residual mass is a lower-left rectangle under a nondegenerate
  Gaussian law, discharge positivity immediately from open-positive measure
  support instead of carrying a loose positivity premise through diversity
  ratio theorems. The reusable lemma is
  `lowerLeftRectangleMass_pos_of_isOpenPosMeasure`; for correlated Gaussians,
  combine it with the existing `correlatedStandardGaussianLaw_isOpenPosMeasure`
  proof and the paper's automatic `rho^2 < 1` algebra.
- For complementary two-school residual masses, look for a decomposition into
  `lowerLeft + (Phi(A_new)-Phi(A_old))`. Once the affine-argument order is
  explicit, positivity follows from lower-left positivity plus CDF monotonicity;
  this is usually faster than expanding all source density integrals again.
- For a lower-tail affine-CDF integral, the direct product-measure route is
  usually faster than another Owen-table lookup. Define the affine lower event
  `P(X <= A*D+c*Z, Z <= B)`, use `Measure.prod_apply_symm` to condition on
  `Z`, rewrite the section as `Phi(A*D+c*z)`, and then use
  `integral_gaussianReal_eq_integral_smul` to convert the outer standard
  Gaussian measure to `phi(z) dz`. Compose this with the existing affine
  standardization map to get the lower-left bivariate rectangle.
- When a later algebraic theorem assumes these selection cores are positive,
  avoid carrying positivity as a paper premise for concrete bivariate normals.
  Prove a reusable open-positive-measure lemma that every nonempty vertical
  upper strip has positive mass, then instantiate it for the nondegenerate
  correlated Gaussian law. This usually removes two noisy hypotheses from the
  paper-facing ratio/comparison theorem.
- When closing a bivariate-normal CDF seam, do not leave `Phi_2` as a bare
  function longer than necessary.  Define the correlated standard-Gaussian law
  as the pushforward of independent standard normals by
  `(U,V) ↦ (U, rho * U + sqrt(1-rho^2) * V)`, define
  `Phi_2(x,y;rho)` as its lower-left rectangle mass, and prove the easy source
  facts immediately: the first marginal is standard normal, clipped horizontal
  boundaries are null for `rho^2 < 1`, and paper correlation parameters such as
  `-z / sqrt(1+z^2)` satisfy `rho^2 < 1`.
- After that first bivariate-CDF seam is in place, keep pushing generic law
  facts before returning to paper algebra.  The useful reusable sequence is:
  prove the second marginal is standard normal using mathlib Gaussian scaling
  plus convolution; derive nonatomic marginals; prove lower-left rectangle/CDF
  continuity from zero vertical/horizontal boundary mass; and prove
  open-positivity for nondegenerate correlations by showing the source affine
  map is continuous and surjective from the product of open-positive standard
  Gaussian measures.  These facts then discharge continuity, strict monotonicity
  via open-positive upper-orthant lemmas, and endpoint regularity without
  repeating bivariate density calculations in paper files.
- After proving correlated-Gaussian upper-orthant regularity, immediately
  compose it into the named source-event fixed-point theorem. Do not leave the
  session at a green per-component regularity lemma if the paper endpoint is
  just a finite-sum wrapper away; expose both the per-component package and the
  paper-facing `existsUnique` theorem in the human interface.
- When a paper theorem is group-indexed, avoid stopping at a one-representative
  type theorem. After the single-group payoff/cutoff calculation is green,
  immediately package the group-indexed equilibrium object with common school
  cutoffs and per-group costs/precision scales. This prevents the DAG from
  looking greener than the paper and avoids redoing the same wrapper work
  later.
- For two-school, two-policy admissions games, prove the normal-form
  unilateral-deviation bridge before the source inequalities. Each candidate
  pair `(P_sub,P_full)`, `(P_full,P_sub)`, and `(P_full,P_full)` should reduce
  to the two objective comparisons obtained by switching one school while
  holding the other fixed. Then connect the paper's analytic inequalities to
  those objective comparisons.
- Audit existential cost-boundary statements before treating them as substantive
  strategic conclusions. If a theorem only says there exist positive functions
  characterizing an equilibrium region, the bare existential may be provable by
  case-splitting on the equilibrium predicate and choosing artificial constant
  boundaries. Record that as an abstract statement-level closure, but keep the
  economically meaningful task separate: derive the intended boundary functions
  from continuity, monotonicity, and the concrete strategic fixed point.
- Prove truthfulness at the threshold-rule level: if the threshold offered to
  bidder `i` is independent of `i`'s report, accepting iff bid exceeds that
  threshold is DSIC.
- Instantiate random-sampling or market-price auctions by proving the relevant
  own-bid-independence lemma.
- For fixed-price benchmarks, define a finite bidder-value candidate benchmark
  early. Reduce arbitrary feasible prices to bidder-value prices using the
  minimum accepted bidder value: raising to that value preserves the sale count
  lower bound and weakly increases revenue.
- For random-sampling digital-goods auctions, first prove the deterministic
  cross-sample threshold mechanism truthful for an arbitrary fixed partition;
  only after that add probability over partitions and revenue approximation.
- For weighted-pairing or selected-pair auction lower bounds, write the
  expected-payment/revenue formula as a concrete finite double sum first. When
  the proof keeps only same-bin or otherwise selected ordered pairs, define the
  selected pair index type and embed it injectively into the full pair index;
  then compare sums with `FiniteSum.sum_le_sum_of_injective_nonneg`. This is
  faster and more auditable than repeatedly expanding the full auction sum.
- For bucket/bin auction proofs, prefer actual `Finset` buckets over abstract
  pre-ranked arrays once the algebraic bridge is stable. Use a finite-ranking
  helper to derive value-sorted ranks, within-bin membership, image equality,
  and injectivity; use subtype/finset wrappers to derive high-low pair
  injections from disjoint bucket halves.
- For dyadic partition arguments, make the partition theorem tolerate empty
  bins. Canonical power-of-two ranges often include empty buckets, and requiring
  every bin to be nonempty forces irrelevant side proofs. Bound each empty bin
  by benchmark nonnegativity and each nonempty bin by the usual fixed-price
  floor argument.
- When a binning proof naturally has a classifier `bucketOf : Agent -> Bucket`,
  define buckets as classifier fibers. Then prove coverage by swapping sums over
  agents and buckets and using a singleton indicator sum; this avoids carrying
  manual disjointness and partition assumptions through every theorem.
- For dyadic largest-bucket arguments such as `|M| t = Ω(F)`, formalize the
  proof as a finite geometric-tail recurrence (`tail_j <= mass_j + tail_{j+1}/2`)
  plus a largest-total-bucket-to-floor-mass bridge. This is faster and more
  auditable than repeatedly unfolding all powers-of-two buckets in the main
  auction theorem.
- When the paper's dyadic tail starts at the fixed price, set the tail base to
  the price itself if that is faithful. This can remove factor-two slack from
  the winner-count bridge and make the "largest bucket has at least two
  bidders" contradiction close cleanly.
- For GHW-style `F >= 2h` largest-bucket size claims, prove the contrapositive
  with a strict finite geometric-tail lemma: if the largest dyadic bucket has
  at most one bidder, every bucket mass is at most `h`, so the finite dyadic
  tail is strictly below `2h`, contradicting `F >= 2h`.
- For paper statements involving `log h` dyadic bins, avoid fighting
  `Real.log` until the analytic endpoint truly needs it. A faster faithful
  route is often to take a natural-number log certificate such as
  `values i <= 2^(m+1)`, construct the `m+1` factor-two bins by induction on
  powers of two, and state the theorem with the explicit hypothesis
  `(m+1 : ℝ) <= s^2` or the relevant log-bound certificate.
- Once the natural-number dyadic certificate is closed, add the paper-facing
  real-log wrapper as a thin theorem rather than refactoring the bin proof.
  For base-two logs over normalized bids, set `m = Nat.ceil (Real.logb 2 h)`,
  use `Real.logb_le_iff_le_rpow` and `Real.rpow_natCast` to get
  `h <= 2^m <= 2^(m+1)`, then use `Nat.ceil_lt_add_one` to bound
  `m+1 <= Real.logb 2 h + 2`. This keeps analytic imports narrow
  (`Mathlib.Analysis.SpecialFunctions.Log.Base`) and preserves a green
  dyadic theorem if exact paper log constants are still caveated.
- In weighted-pairing Theorem 7.2-style proofs, keep the fixed-price tail base
  separate from the selected largest bucket's floor. The fixed-price bound uses
  the bucket containing the price (`p <= 2 * baseFloor`) to count winners, while
  the high/low rank split uses the selected bucket floor `t`; forcing these to
  be the same creates unnecessary and non-paper assumptions.
- For repeated-bid tightness examples, model the actual population with
  dependent finite types such as `Sigma fun level => Fin (count level)` plus a
  separate `Fin s` top block. Prove the source's bookkeeping facts first
  (per-level total mass, total bid value, top-price fixed-price revenue, and
  classifier revenue split) before attacking the raw expected-payment
  inequalities.
- When a theorem's proof only needs a size/value precondition in one case split,
  derive it inside that branch instead of assuming it globally. For GHW-style
  arguments, `F <= T/s`, `F >= 2h`, and `2 <= s` give the `4h <= T` precondition
  for the Theorem 7.1 branch, while the largest-bucket branch should not inherit
  that extra assumption.
- Use a nonnegative offer-price wrapper around finite candidate prices so
  no-positive-transfer and expected-revenue nonnegativity proofs do not inherit
  infeasible negative candidate values from empty samples.
- When a finite candidate benchmark is positive and all bidder values are at
  least one, prove the selected candidate offer price is at least one before
  entering dyadic-bucket arguments. This avoids carrying an arbitrary
  benchmark-attaining price and ties the paper-facing `F^(2)` theorem directly
  to the reusable finite-candidate benchmark API.
- For deterministic single-parameter lower bounds, avoid starting with a real
  infimum unless the theorem truly needs it. In a fixed-other-bids offer slice,
  prove the fast DSIC atoms first: any two winning reports pay the same price;
  if a lower report wins then higher reports win; and if a higher report loses
  then lower reports lose. When a winning report exists, the common winning
  payment itself is the critical price: reports below it lose by feasibility,
  reports above it win by truthfulness, and the boundary may be open or closed.
- When lifting a deterministic offer-slice characterization back to a full
  digital-goods auction, define the induced fixed-other-bids offer once. Prove
  `LosersPayZero` from IR plus no-positive-transfers, use binary allocation to
  identify offer utility with the original auction utility, and then apply the
  offer-slice theorem. This is faster and cleaner than re-proving the critical
  price argument inside the full auction model.
- For binary deterministic bid-independent lower bounds, formalize arbitrary
  threshold prices directly before specializing to the paper's two-price WLOG.
  Classifying an offer as "high" when it is above the low value `1` proves the
  same adversarial transition and avoids spending proof effort on a separate
  normalization argument.
- When a paper's bid-independent auction is anonymous and takes a set/multiset
  of other bid values, bridge it to a count-threshold theorem by defining a
  canonical erased-bid representation for the restricted input family (for
  example, a list with all high values followed by all low values). This closes
  the paper's anonymous binary restriction without pretending it covers a
  stronger identity-aware threshold model.
- When moving between count-threshold and anonymous erased-list models on
  binary values, define the list rule by counting high values and low `1`
  values in the erased list, then prove it agrees on the canonical
  repeated-value list. This is usually faster and more source-faithful than
  carrying an opaque representation hypothesis through every downstream
  theorem.
- For ranked-auction telescoping proofs with terms like `V_j = b_j * (n-j)`,
  prove `V_j <= F` once from the actual sorted bid profile and fixed-price
  benchmark. Use the upper-rank finset of bidders with rank at least `j` to
  show price `b_j` has at least `n-j` winners, then feed that feasible price to
  the benchmark API. This removes a repetitive certificate hypothesis from the
  main revenue theorem.
- In ranked-auction Theorem 8.2-style proofs, do not keep adjacent monotone win
  probabilities as a primitive if the paper gives the two adjacent truthfulness
  comparisons. Prove `p_j <= p_{j+1}` by applying the Lemma 8.1 algebra to the
  low-value and high-value adjacent deviations, with only `p_0 = 0` plus
  nonnegativity of the first real win probability for the dummy endpoint. Keep
  these adjacent assumptions bounded to `j+1 < n`; if a helper asks for all
  natural indices, add the bounded finite-sum variant instead of fabricating
  out-of-range comparisons.
- Prefer payment-form ranked revenue wrappers before introducing conditional
  expected costs. Define `gain i = p_{i+1} * b_i - payment_i`; the high-value
  adjacent truthfulness inequality gives the recursion
  `gain_i + p_{i+1}(b_{i+1}-b_i) <= gain_{i+1}`, while the low/high adjacent
  payment inequalities and strict adjacent ranked bids give monotone win
  probabilities. This usually removes an artificial `expectedCost` variable
  from the paper-facing Theorem 8.2 seam and leaves only the concrete
  randomized-auction DSIC-to-ranked-payment bridge.
- Once a ranked-payment wrapper is green, stop adding more conditional algebra
  variants. The next useful proof work is the model bridge: define the concrete
  anonymous/sorted-bid randomized auction interface, prove its expected revenue
  decomposes as the ranked payment sum, and derive the adjacent payment-form
  truthfulness inequalities from DSIC. Record that exact bridge in the README
  if stopping before it is proved.
- When a lower-bound construction returns a feasible benchmark lower bound,
  strengthen it to the actual benchmark before declaring the paper endpoint
  closed. For finite candidate fixed-price benchmarks this usually means
  proving the constructed prices (`1` and the high value `H` in two-value GHW
  inputs) are feasible and then replacing the abstract certificate by the
  benchmark itself.
- If a finite benchmark API requires `[Nonempty Agent]` but a theorem quantifies
  over counts that may be zero, introduce a small paper-specific benchmark
  wrapper with an explicit empty case. Then prove all constructed witnesses are
  nonempty locally. This avoids leaking typeclass witnesses into the
  paper-facing statement.

## GSP and Position Auctions

- Start with `PositionOutcome`: per-click payments, utility, revenue, welfare,
  and feasibility.
- A concrete non-truthfulness witness is a good first theorem before building a
  generic bid-sorting mechanism and equilibrium comparisons.
- Use local envy-freeness as an outcome-level certificate for "no profitable
  assigned-slot deviation" before proving full Nash equilibrium of a sorted GSP
  mechanism.
- For EOS-style local envy-free/stable-assignment lemmas, do not label missing
  appendix derivations as caveats when the assumptions are in the paper. If the
  current Lean wrapper assumes global all-assigned-slot no-rematch but the paper
  defines adjacent local envy-freeness and derives global no-rematch from
  equilibrium, assortativity, and telescoping adjacent inequalities, mark the
  row conditional and name that missing bridge.
- Likewise, when the paper's stable-assignment-to-GSP converse assumes
  `N > K`, invokes Shapley-Shubik to get an efficient/assortative assignment,
  and then constructs bids, a Lean outcome-level `StableAssignment ->
  SlotEnvyFree` shortcut is conditional, not caveated. The remaining work is
  the characterization plus bid-construction/static-equilibrium bridge.

## Combinatorial Auctions

- Reuse the fair-division bundle/allocation layer. Keep feasibility separate
  from direct mechanisms because approximation algorithms may leave goods
  unallocated.
- For single-minded bidders, define bundle-containment valuations before proving
  greedy allocation or critical-value payment theorems.
- Prove pairwise-disjoint accepted-set feasibility separately from greedy
  optimality; this lets the greedy algorithm theorem focus on acceptance
  invariants and critical-price monotonicity.

## General Mechanism Wrappers

- Define the paper's scalar functions exactly (`f`, `g`, `h`, utilities,
  welfare), prove algebraic equivalences to existing mechanism predicates, then
  prove the theorem from a small payoff/crossing certificate.
- When approximation proof is too large for the current pass, package it as a
  named certificate whose statement is exactly the benchmark/revenue inequality
  needed by the paper-facing theorem.

## Dynamic Games, PBE, and Schedule Certificates

- For long dynamic-game proofs, keep a theorem-specific scratch plan beside the
  paper files. Record current Lean endpoints, the exact mathematical gap, the
  next bridge lemmas, why they should be true, and which assumptions are genuine
  source assumptions versus temporary certificate fields. When Lean gets too
  low-level, write the informal recurrence, induction, or history construction
  first, then translate only the stable pieces into named Lean declarations and
  audit wrappers.
- In EOS-style finite dropout/PBE proofs, exact-drop histories, finite
  completed-rank wrappers, core-vs-full source-completion certificates, and
  derived-outcome bridges make the extensive-form gap visible while still
  allowing verified algebra to accumulate. If a scratch proof shows that some
  certificate fields are consequences of other fields, formalize the smaller
  core certificate and a derived bridge before continuing.
- When a source proof uses local payoff comparisons as the sequential
  rationality step, promote the raw algebra into named payoff definitions and a
  small best-response predicate before proving the full dynamic-game
  obligation. In EOS Theorem 8, exposing continue payoff, drop payoff, and the
  finite `B*` one-step best-response theorem made the remaining
  belief/sequential-rationality lift auditable.
- If the source proof uses strict exclusion directions, add an off-threshold
  strict wrapper pairing the strict payoff inequality with the strategy's
  actual drop/not-drop action. If behavioral uniqueness depends on tie-breaking
  at an indifference threshold, make tie-breaking a named predicate and prove a
  characterization theorem from local best response plus tie-breaking to the
  paper cutoff rule.
- When a PBE predicate existentially packages a belief and a
  sequential-rationality proof, do not keep behavioral facts as opaque
  "every PBE behaves this way" obligations if the source proof is really about
  sequential rationality. Add a certificate proving local best response and
  tie-breaking from `isSequentiallyRational`, then unpack the PBE witness in a
  thin bridge.
- If the source proof defines sequential rationality by local deviations,
  sharpen the certificate to an iff between `isSequentiallyRational` and the
  audited local optimality/tie-breaking predicates. The reverse direction
  should lift the named strategy's local proof to game-level sequential
  rationality; the forward direction should replace opaque arbitrary-PBE
  behavior fields. If the paper says the best response is belief-independent,
  add an ex-post local-deviation certificate layer and conversion lemmas to the
  local-deviation core and one-sided source steps.
- For recursive or hard-to-audit paper-facing premises such as clock-sorted
  finite schedules, add `nil`, `cons`, `singleton`, pair, and
  append-singleton helpers so humans can verify concrete instances by local
  inequalities. If a finite schedule theorem asks separately that the completed
  set is contained in the schedule, add an all-scheduled constructor for the
  common case `completed = scheduledRanks.toFinset`.
- When a concrete history condition is local to realized transitions, make it a
  first-class history object instead of a global predicate over all possible
  states. For exact schedules, add a conversion to the annotated history object
  and a terminal-history certificate constructor. This gives the audit path:
  clock-sorted schedule -> exact schedule -> annotated finite history ->
  terminal records/source certificate.
- If a sharper concrete-history certificate is introduced, mirror the ordinary
  certificate stack with forgetful constructors and obligation ledgers:
  terminal-history certificate, terminal/dynamic certificate, core source
  certificate, full source certificate, finite source certificate, and direct
  paper-facing endpoints.
- For nonempty finite schedules, expose an append-singleton final-clock lemma:
  if the schedule is `scheduledPrefix ++ [lastRank]`, the final clock is the
  last scheduled threshold. Then provide endpoints whose terminality premise
  compares unscheduled thresholds to that last threshold instead of to a
  recursively computed final state.
- When recursive schedule sortedness mixes initial-clock and adjacent-threshold
  obligations, split out an adjacent-threshold sorted predicate. Prove a bridge
  from initial-clock-plus-threshold-sorted to the recursive predicate and
  discharge the initial-clock inequality automatically for cold starts.
- Expose intermediate certificate constructors as first-class definitions, not
  only final theorem endpoints. If a terminal-dynamic certificate is built from
  a concrete strategy-consistent terminal history, expose the terminal-history
  behavior certificate and direct facts such as scheduled-rank terminal records
  and final-state active iff unscheduled.
- When the final source boundary combines source PBE semantics with an exact
  terminal history, create a single bundled source-completion certificate that
  proves the final unique-PBE conclusion. If exact terminal-history completion
  is only finite, expose a finite analogue with the completed set and
  inactive-on-completed proof as fields, and derive the finite
  unique-PBE terminal-record conclusion from it.
- If a source-shaped checker already instantiates the ex-post/local-deviation
  semantics, add constructors from exact histories and exact schedules into the
  finite bundled certificate, plus an all-scheduled variant. If an adjacent
  source-obligation layer already has a sorted-schedule endpoint, add a direct
  endpoint from the sharper ex-post/local-deviation layer and an all-scheduled
  specialization. For small concrete schedules, mirror singleton/pair helpers
  at that sharper layer.
- For source-completion certificates, expose obligation-conjunction theorems
  for each important layer. The full certificate should list all source
  obligations, while core, one-sided, ex-post, sequential-rationality,
  one-step/tie-break, and local-deviation certificates should list only their
  minimized obligations. Also expose direct downstream endpoints from reduced
  certificates to named-strategy PBE, PBE strategy equality, the cutoff/action
  rule, unique PBE, outcome equality, and compact paper conclusions, so audit
  files can cite one theorem from the minimized source obligation.
- If several paper-facing or audit endpoints repeatedly rebuild the same PBE,
  terminal-history, or source-completion object, stop adding aliases and move
  the construction into a source-layer bridge theorem. The interface and audit
  files should call that strongest bridge with `exact`/`simpa`; repeated
  schedule, belief, or terminal-record construction belongs in the bridge file.
- For proof-dependent certificate wrappers, watch inferred result types. If an
  endpoint's type depends on local proof witnesses or a `Classical.choose`
  reconstruction, Lean may reject an otherwise obvious wrapper because the
  expected proposition is not definitionally the same. Prefer routing through a
  stable theorem whose conclusion is stated with the final paper-facing objects,
  or introduce such a theorem, instead of fighting positional arguments and
  proof-dependent metavariables in the wrapper.
- For belief-explicit state-game variants, prove the source-extensive theorem
  once and derive the belief-explicit endpoint through the established PBE
  equivalence and projection lemmas. Do not duplicate the schedule/PBE
  construction just to add belief, history, or terminal-record fields that are
  already carried by the source theorem.
- For cold-start sorted-schedule endpoints, prefer a direct all-scheduled or
  append-singleton source theorem whose conclusion includes the terminal-record
  and completion facts needed by the paper. This is usually cleaner than
  reconstructing source-completion certificates from schedule proofs inside
  `ProofInterface.lean` or `PostPaperAudit.lean`.
- For exact finite schedules, expose deterministic-final-state facts:
  scheduled ranks have terminal records equal to their threshold, and from an
  all-active initial state the active ranks are exactly the unscheduled ranks.
  If an endpoint already contains terminal-record conclusions but its name only
  says `exists_unique_pbe`, add a paper-facing alias whose name explicitly says
  `with_terminal_record_conclusion`.
- When a paper theorem includes a continuity restriction on a strategy formula,
  formalize continuity of the numeric policy formula itself, not just
  monotonicity or affine algebra; expose both scalar and indexed/update forms
  if the theorem is rank-indexed.
- When a theorem states "same payoff" and the formalization already proves slot
  and payment equality, add a utility-extensionality bridge and a direct
  paper-facing utility-equality endpoint so reviewers do not have to unfold the
  quasilinear utility definition. If the theorem has both all-rank and finite
  completed-rank routes, expose the payoff endpoint for both routes.
- When a source model uses a convention such as an empty history value, add a
  named theorem that rewrites the general formula under that convention, plus
  the indexed specialization if the theorem is rank-indexed.
- When strict monotonicity is used in a source uniqueness argument, add the
  corresponding injectivity theorem so later uniqueness proofs can cite the
  identification property directly.
- If the source proof uses a named scalar such as `q`, expose source-proof-line
  aliases for the defining formula, expected interval, endpoint, monotonicity,
  and continuity checks after proving the lower-level algebra.
- At abstract game-interface layers, expose payoff-equality bridges from
  same-allocation/same-payment fields before building more specialized
  endpoints. Also expose outcome-equality-to-payoff-equality bridges when
  stronger outcome equality is already the common endpoint.
- When a certificate field captures a paper phrase such as "best response
  regardless of beliefs," expose a direct theorem with that conclusion instead
  of leaving reviewers to inspect the field projection manually. When final
  theorem objects wrap a source certificate, lift the endpoint to those final
  objects too.
- If an iff endpoint converts source sequential rationality into a local
  paper-facing predicate, expose the direct theorem discharging that predicate
  from the named-strategy best-response obligation. When the only use of a
  belief argument is to instantiate a belief-independent result, expose a
  `[Nonempty Belief]` citation form. When a paper-facing strategy is named,
  expose the named-strategy `for all beliefs` iff source-local-predicate
  endpoint, not only the arbitrary-strategy iff.

## Strategic Admissions Source-Model Closure

- For two-school standardized-testing models, do not introduce a fresh
  theorem-level certificate after the paper's condition wrappers are source
  shaped. Continue by proving the concrete inputs to the existing wrappers:
  strategic applicant-pool mass identities, school objective value formulas,
  mass feasibility, zero-contribution facts, and no-tie inequalities.
- When a school weighted-merit objective collapses because one group has zero
  contribution under a policy pair, prove that bookkeeping lemma directly and
  use it to remove objective-equality premises from later bridges. Keep the
  surviving-group mass and no-tie assumptions separate; they are economic
  model facts, not algebraic rewrites.
- For Proposition-5-style condition bundles, once cutoff/merit-crossing
  wrappers construct the cost thresholds, the next best target is the concrete
  Gaussian game data feeding those wrappers. Avoid restating conditions
  (10)--(14) manually; use the established paper-level wrapper and discharge
  its concrete premises.
- For large theorem wrappers with repeated interval or feasibility premises,
  add small composition endpoints rather than copying the whole signature into
  every downstream theorem. If parts (i) and (ii) are interval endpoints and
  part (iii) follows from positive costs, add one source-shaped theorem that
  composes those facts and exposes only the remaining model premises.
- When a generated policy-state or objective table overrides only one school
  row, expose a fallback-row theorem under the distinct-school hypothesis
  (`J1 != J2`) immediately. Downstream source-model proofs should state the
  untouched school's no-deviation or objective premise on the ordinary fallback
  row, not on the generated override function.

## Generalized-English Source-History and PBE Lessons

- For threshold generalized-English auction histories, ordinary
  strategy-consistent histories are usually too weak for exact terminal-record
  conclusions: an active bidder can drop after its threshold and record an
  overshot clock. Before trying to close a paper-level PBE theorem, prove either
  exact-drop history, no-overshoot history, or a source transition relation
  such as clock discipline that prevents overshoot at every realized dropout.
- Attack source-history gaps at the transition level first. Prove a one-step
  invariant saying a legal clock advance cannot pass any active threshold, or
  a local dropout step records exactly the active bidder's threshold; then lift
  it to histories and only then feed the result into terminal-record or
  source-completion endpoints.
- Keep the source PBE seam separate from outcome algebra. For generalized
  English/GSP-style proofs, the durable split is concrete belief consistency,
  a game-level sequential-rationality iff against a local reachable/off-path
  predicate, behavioral PBE characterization, and source-history generation.
  Slot/payment/utility equality should be downstream of those certificates, not
  repeated as source assumptions.
- In infinite-rank source models, a finite schedule cannot prove all ranks are
  inactive from an all-active cold start. Use completed-rank endpoints for
  finite paper checks, or introduce a finite-active source state whose inactive
  outside ranks already carry exact records. Do not paper over the distinction
  with an all-terminal wrapper.
- For finite exact-record PBE endpoints, make the finite state explicit rather
  than pretending a finite schedule completed an infinite cold start. A robust
  pattern is: displayed active ranks are `List (Fin n)`, internal ranks are the
  translated natural list, inactive outside ranks start with exact records,
  complete displayed schedules prove active-to-inactive for every `Fin n` rank,
  and a canonical price-sorted wrapper discharges threshold-sortedness,
  no-duplication, and completeness internally. Keep any source-timing or
  threshold-event premise visible in the final theorem unless the real source
  transition relation has proved it.
- For belief-explicit source-extensive PBE checkers, let the belief object carry
  the generated source history and terminality proof. Then expose projection
  theorems that recover generated history, terminality, and exact/no-overshoot
  records from an accepted PBE witness; this keeps the human-facing PBE surface
  honest about which source evidence was checked.

## Anonymous Digital-Goods Source Models

- In identity-aware `DigitalGoodsAuction` developments, do not try to derive
  anonymous set-of-bids behavior from DSIC/IR/NPT/binary allocation alone:
  personalized posted prices satisfy those primitives. If the paper works over
  sets or sorted lists of bids, introduce a source-shaped factorization model
  and prove it implies the proof-facing bridge certificate.
- For ranked revenue upper bounds, weak DSIC plus bid-independent set-of-bids
  pricing may be too weak: a two-bidder threshold rule can charge the high
  bidder `100` and the low bidder `1` on bids `{1, 100}`, earning `101` while
  the fixed-price benchmark is `100`. Require the adjacent sorted-bid
  report-substitution condition used by the paper proof, or record the source
  theorem as needing correction.
- For deterministic lower bounds, make the human-facing theorem consume the
  original deterministic auction family when possible. Use Lemma 9.2 to select
  representative erased-list critical prices internally from deterministic
  truthfulness/IR/NPT/binary allocation, and keep primitive erased-bid-list
  price rules as bid-independent specializations rather than replacing the
  arbitrary auction theorem.
- Prefer source fields that name the paper semantics, such as adjacent
  sorted-bid report substitution or erased-bid-list offer factorization, over
  final proof certificates like ranked payment recurrences or erased-bid
  representative equality. Keep the raw certificate theorem available as an
  internal adapter, but make `PaperInterface.lean` consume the source-shaped
  model.
- After replacing an old certificate-based theorem with a source-shaped final
  theorem, scrub broad paper-module export lists too. It is easy for
  `PaperInterface.lean` to be clean while `GHW01DigitalGoods.MainTheorems`
  still re-exports older coupled-outcome, sorted-bid, or erased-list adapters
  that read like public paper assumptions.
- When a randomized-auction source proof uses raw CDF monotonicity plus an
  inverse-CDF/common-quantile thought experiment, first try to prove the needed
  revenue recursion directly from the raw CDF order. For digital-goods ranked
  offers, a finite PMF layer-cake/surplus argument can turn adjacent CDF
  monotonicity into both monotone acceptance probabilities and the adjacent
  gain recursion, avoiding a public coupled-outcome certificate. Keep any
  common-seed coupled model as an auxiliary audit form unless the final
  paper-facing theorem genuinely needs it as a source assumption.
