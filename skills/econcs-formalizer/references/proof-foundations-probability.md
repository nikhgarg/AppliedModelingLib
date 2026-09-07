# Foundations: Probability

Use for `AppliedModelingLib/Foundations/Probability/*`, finite PMFs, expectations,
conditional probability, finite variance, finite Markov kernels/chains/MDPs,
stochastic dominance/couplings, concentration, measure inequalities,
continuous densities, CTMCs, renewal-reward reductions, and RUM/noise models.

## Continuous Integral Asymptotics

- For order-statistic or tail-integral asymptotics, split the proof into
  auditable source layers before attempting the final limit: define the exact
  source integrand/integral, prove source-kernel measurability and
  integrability from the distribution assumptions, prove the source change of
  variables, identify the rescaled pointwise kernel limit, evaluate the limiting
  integral, and only then assemble finite sums or reflected source losses.
- When the paper splits an integral at a fixed threshold and then rescales,
  formalize both sides of the split. Prove the below-threshold and
  above-threshold change-of-variables statements, then prove the corresponding
  rescaled split at the growing threshold. This keeps the paper proof and the
  dominated-convergence proof route comparable.
- Keep tail-negligibility proofs scalar when possible. A typical route is:
  nonnegativity of the source tail, an envelope from bounded support plus a
  positive lower CDF/tail floor, a polynomial-times-geometric scalar limit, and
  a squeeze. Afterward, add a bridge converting source-tail negligibility plus
  source change of variables into rescaled-tail convergence to zero.
- For near-zero asymptotics, expose a bridge theorem that turns convergence of
  the growing rescaled integral into the original source-integral asymptotic.
  A second bridge should turn full rescaled convergence plus tail convergence
  into that growing-interval convergence. This gives future agents two honest
  routes: direct near-zero analysis or global dominated convergence plus a
  verified negligible tail.
- Use explicit certificate structures for hard dominated-convergence or
  source-split obligations. Certificates should separate source assumptions
  (CDF/density asymptotics, bounded support, range bounds), analytic envelope
  fields, and final assembly theorems. Do not hide a missing near-zero or tail
  proof inside a single broad "asymptotic certificate" if the paper proves
  those pieces separately.
- For bounded-support finite-sample top-`k` order-statistic proofs, use the
  shared reflected-sample bridges before writing paper-specific algebra:
  `expectedSampleTopKEndpointLoss_eq_expectedReflectedBottomKSum`,
  `expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic`, and
  `expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic_of_le`.
  The fixed-`k` version is the right entry point after the eventual
  sample-size prefix in asymptotic arguments.
- If a source states expected order statistics as a bottom-indexed
  `μ(rank, sampleSize)` function, use the shared
  `orderStatisticTopKSumFromMean`, `sampleOrderStatisticValue`,
  `expectedSampleOrderStatisticMean`, and `expectedOrderStatisticMeanSeq`
  bridge in `OrderStatistics` before adding paper-local notation.  The generic
  bridge already connects that source notation to `sampleTopKSum` and
  reflected endpoint-loss expectations.
- For a fixed finite family of rank terms with a common asymptotic scale, use
  `AppliedModelingLib.Math.finite_sum_asymptoticEquivalent_common_scale` instead of
  rebuilding finite-sum asymptotic algebra in a paper file. If the paper has a
  main term plus an `o(scale)` remainder, use
  `AppliedModelingLib.Math.asymptoticEquivalent_add_negligible_common_scale`.
- For bounded order-statistic or tail-integral source kernels, prefer a direct
  adjacent finite-difference asymptotic when the source kernel is available.
  Prove the adjacent-drop limit for each fixed rank term, assemble the finite
  rank sum with the shared finite-sum asymptotic lemma, and convert eventual
  endpoint-loss equality at consecutive sample sizes into the source forward
  marginal. Keep a generic scaled-drop bridge only as a fallback for callers
  that truly provide no source kernel or adjacent-difference proof.

## Measure-Zero And Almost-Everywhere Seams

- For continuous type spaces and Gaussian threshold games, do not strengthen a
  paper claim to pointwise behavior at cutoff ties or off-support states unless
  the source explicitly needs it. Use an a.e. statement over the realized
  information law, then add a separate pointwise-to-a.e. bridge for models that
  really are pointwise.
- Treat boundary-null facts as first-class lemmas. For intervals, rectangles,
  and upper orthants, prove the boundary set has zero measure from no-atoms or
  density assumptions, then use the a.e. indicator route for continuity or
  limit statements. Existing reusable entry points include
  `ae_of_forall_not_mem_null`, `ae_eq_of_forall_not_mem_null`,
  `ae_iff_of_forall_not_mem_null`, `ae_eq_decide_of_ae_iff`,
  `ae_eq_if_of_ae_iff`, `ae_eq_setIndicator_of_ae_iff_mem`,
  `ae_eq_setIndicator_of_forall_not_mem_null`,
  `ae_iff_le_lt_of_level_null`, `ae_iff_lt_le_of_level_null`,
  `MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure`,
  `measure_eq_zero_iff_ae_notMem`,
  `lowerLeftRectangleMass_continuous_of_boundary_null`,
  `lowerLeftRectangleMass_continuous_of_noAtoms_marginals`,
  `upperOrthantMass_diagonal_continuous_of_boundary_null`, and
  `upperOrthantMass_diagonal_continuous_of_noAtoms_marginals`.
- For Gaussian laws, try no-atoms before adding a bespoke zero-boundary-mass
  assumption. Useful compiled facts include `standardGaussianMeasure_noAtoms`,
  `continuous_cdf_of_noAtoms`,
  `correlatedStandardGaussianLaw_noAtoms_map_fst`, and
  `correlatedStandardGaussianLaw_noAtoms_map_snd`.
- For LG/GLM-style upper-tail instability intervals, use
  `standardGaussian_toMeasure_Ico_threshold_normalUpperTailMean_pos` when the
  interval is `[threshold, upperTailMean)`. It packages the strict upper-tail
  mean comparison and the positive Gaussian interval-mass fact, so paper files
  do not need a local `hupper` followed by `GaussianScaleLaw.toMeasure_Ico_pos`.
- For KR-style random-utility Gaussian reductions that normalize an arbitrary
  positive standard deviation to the paper's variance-`1/2` convention, use
  `AppliedModelingLib.Foundations.Probability.BivariateGaussian` before adding
  paper-local scaling proofs. The reusable entry points are
  `gaussianVarianceFromStd`, `canonicalHalfVarianceScale`,
  `gaussianReal_map_canonicalHalfVarianceScale`,
  `independentGaussianPairMeasureWithStd`,
  `independentGaussianPairMeasureHalf`, `pairStrictWinnerBelowEvent`,
  `pairStrictBothBelowEvent`, and
  `independentGaussianStrictConditionalWinnerRatioWithStd_eq_scaled`.
  Paper files should keep theorem-numbered names as thin wrappers over these
  declarations.
- Keep strict/weak threshold semantics explicit. A.e. equivalence lets strict
  and weak cutoff policies differ on a null boundary, but the paper-facing
  theorem should say which version is used for pointwise wrappers and which
  version is only identified a.e. Use the level-null cutoff lemmas before
  adding paper-local assumptions equating strict and weak threshold events.
- For endpoint-touching interval algebra, use null symmetric-difference lemmas
  before writing paper-local set extensionality. Reusable names include
  `measure_set_congr_of_symmDiff_null`,
  `measure_symmDiff_union_left_eq_zero`,
  `measure_symmDiff_diff_left_eq_zero`,
  `measure_diff_left_congr_of_symmDiff_null`,
  `measure_symmDiff_Ioo_union_Ioo_touching_eq_zero`,
  `measure_symmDiff_Ioo_union_Ioi_touching_eq_zero`,
  `ae_eq_set_union_left`, `ae_eq_set_diff_left`,
  `ae_eq_Ioo_union_Ioo_touching`, and `ae_eq_Ioo_union_Ioi_touching`. These
  are the right tools for GN-style "open interval plus adjacent interval/ray"
  rewrites when the shared endpoint has zero mass.
- For a.e. source-equilibrium contradictions of the form "selected types must
  satisfy `reference <= value`, but there is positive mass of selected types
  with `value < reference`", use
  `ae_imp_le_contradicts_positive_selected_lt_mass`. If the source gives
  positive mass for a cutoff interval instead of the selected event directly,
  use `positive_selected_lt_mass_of_positive_lower_lt_mass` to transfer that
  mass through the cutoff rule. This is the reusable LG pattern for both
  optional-reporting reporters and report-required test takers, and it applies
  to any continuous-type binary-choice paper with an a.e. best-response
  implication.

## Continuous Reward And CTMC Seams

- For two-state CTMC reward papers, separate primitive accounting from reward
  rates. Prove measured `T`, `Q`, and scaled-earning identities first, then
  derive measured reward-rate statements only when positive mass/time
  denominators are available.
- For accepted-set continuous reward accounting over real trip lengths or
  quantities, use `ContinuousReward` before adding policy-local algebra:
  `acceptedSetReward_union`, `acceptedSetTime_union`,
  `acceptedSetReward_diff`, `acceptedSetTime_diff`,
  `acceptedSetReward_eq_zero_of_measure_zero`,
  `acceptedSetTime_eq_zero_of_measure_zero`,
  `continuousSetRenewalRewardRate_le_union_of_le_average`,
  `continuousSetRenewalRewardRate_le_diff_of_average_le`,
  `continuousSetRenewalRewardRate_lt_union_of_lt_average`,
  `continuousSetRenewalRewardRate_lt_diff_of_average_lt`,
  `continuousSetRenewalRewardRate_diff_eq_self_of_zero_component`, and
  `continuousSetRenewalRewardRate_union_eq_self_of_zero_component`. In
  paper files, local wrappers should usually be one `simpa` after unfolding
  paper aliases for reward, time, average rate, and renewal reward.
- When an older CTMC source certificate stores a fixed-state identity as
  scaled earning `W = R*T` but the next lemma needs the measured reward-rate
  equality, add the tiny converse bridge from
  `gn21MeasuredStateRewardRate_eq_scaled_primitives`.  Use the positive
  accepted-mass and scaled-time facts from the neighboring Lemma 9/10 source
  data instead of adding a new paper assumption.
- When a CTMC proof has accumulated several theorem wrappers, stop adding
  new wrappers once there is a source-faithful public endpoint. Instead build
  one constructor that consumes the paper's actual source fields and derives
  local theorem names, reward-rate equalities, positivity side facts, or
  aggregate aliases internally. This keeps the next proof pass focused on the
  mathematical source obligations rather than on plumbing.
- If a paper proof is source-ordered, keep that order in the reusable
  constructor. For GN21-style Lemma 9 then Lemma 10 routes, build one
  sequential reward-rate certificate from the feasible/optimal source fields
  and reuse it for a.e. uniqueness; do not convert measured reward-rate data
  back to scaled source data and then immediately recover reward rates unless
  the weak-IC layer specifically needs the aggregate source package.
- For source proofs that state scalar cutoff inequalities but downstream
  endpoint certificates need aggregate cross-ratio fields, add tiny bridge
  lemmas in the paper folder from the scalar cutoff fact to the aggregate
  field. Keep the direction explicit: do not replace a remaining pointwise
  rejected-tail comparison with an aggregate assumption unless the paper has
  already proved that aggregation step.
- In long CTMC closeouts, keep the active proof boundary in this shape:
  public paper-facing wrapper, per-price/source-selection constructor, exact
  remaining source fields, and the validation command that last passed. This
  avoids reopening older broad routes such as all-feasible policy lemmas when
  the paper proof only needs optimal-policy endpoint/source selection.
- When a source lemma fixes an arbitrary current policy but the theorem
  constructs prices using accept-all target rates, introduce an effective
  current ratio instead of rewriting the current reward rate to the target
  rate. The reusable pattern is: target accounting `z = ratio*(m-Rtarget)`,
  current reward bound `Rcurrent <= Rtarget`, positivity of `m-Rtarget`, then
  construct `z/(m-Rcurrent)` and prove it is positive and no larger than the
  target ratio.
- Prefer sequential CTMC IC routes when the paper proof is sequential. Move
  the state whose lemma works with the arbitrary current fixed state first;
  after that state is accept-all, discharge the second-state lemma with the
  theorem's target accept-all accounting. This avoids false fixed-state
  reward-rate equalities.
- For denominator-valid CTMC a.e.-uniqueness, do not force a symmetric
  two-state candidate certificate if the source proof is sequential. Prove the
  first-state a.e. accept-all claim, use measured-reward a.e. congruence to
  replace that state by exact accept-all while preserving positive-mass
  optimality, then prove the second-state candidate with that fixed
  accept-all policy. This avoids an artificial obligation to prove
  fixed-state source data for the original arbitrary current policy.
- Audit fixed-state transfer assumptions algebraically. If lower and upper
  bounds demand opposite cross-ratio directions, do not assume equality unless
  the source proves it. Try replacing one direction with a direct endpoint
  sign proof; for GN21 Lemma 9, current lower-endpoint nonpositivity plus only
  the upper fixed-state comparison is enough.
- For CTMC fixed-state complement comparisons, exploit the monotonicity of
  `q(t)/t` before adding certificate fields. A reject-long policy has accepted
  trips shorter than every rejected trip, so strict antitonicity of `q(t)/t`
  gives the lower pointwise side after cross-multiplication and integration.
  In Lean, prove the pointwise cross-product first, rewrite
  `setIntegral_mono_on` with `integral_const_mul`, then scale by the
  nonnegative arrival rate. This often turns a false-looking complement
  equality assumption into a single remaining upper-inequality obligation.
- For renewal-reward papers, do not leave every stochastic step behind an
  opaque "LLN certificate" if the source proof only needs IID cycle averages.
  Mathlib has `ProbabilityTheory.strong_law_ae_real`; wrap it once for
  empirical means and reward/time quotients, then define a paper-local
  IID-cycle model whose fields are the cycle random variables, integrability,
  pairwise independence, identical distribution, and the expected-cycle
  identities from Wald/geometric calculations. This closes sample-path
  ratio/time-fraction theorems with strong-law proof terms and keeps only the
  source's actual cycle-construction assumptions in the theorem signature.
- For cutoff/threshold reward objectives with possible atoms on the threshold
  boundary, do not default to a zero-boundary-mass assumption.  Prove the
  one-sided dominated-convergence limits for the primitive set integrals:
  approaching from below sends strict and complete threshold sets to the
  complete threshold, while approaching from above sends both to the strict
  threshold.  Then lift payment/time limits through the renewal-reward quotient
  and prove upper semicontinuity of the max objective from the two one-sided
  limits, since each one-sided limit is bounded by the pointwise max.
- Keep the paper-facing source boundary honest: denominator-valid reward-rate
  routes should quantify over feasible measurable policies with positive mass,
  while broader measurable wrappers should either keep explicit positive-mass
  obligations or use scaled-earning/accounting forms that avoid division.
- If a denominator-valid CTMC theorem already has a compiled positive-mass IC
  construction, add the a.e.-uniqueness layer by destructing that construction
  and applying a positive-mass Theorem 4/Lemma 5 marginal-response certificate
  to the constructed prices.  Do not redo the scalar price construction just to
  add uniqueness; the marginal certificate should be checked only at the
  existing `m,z` witness and over positive-mass measurable optima.
- When a continuous CTMC reward formula divides by accepted mass, audit the
  zero-mass semantics before trying to lift a positive-mass theorem to all
  feasible policies.  In Lean, real division totalizes `1 / 0` and `0 / 0` to
  `0`; this can make a zero-mass state's cycle time/reward rate vanish instead
  of representing an infinite wait or an undefined source expression.  If one
  state has zero accepted mass and the other state is nondegenerate, the
  two-state reward may collapse to the other state's reward rate, so a blanket
  "zero-mass policies are strictly dominated by accept-all" bridge can be
  false.  Prefer a positive-mass/nondegenerate theorem surface, an explicit
  zero-mass dominance certificate, or an extended-real/partial reward
  interface.  Add tiny simplification lemmas for the zero-mass cases before
  spending tokens on a doomed dominance proof.
- For all-feasible CTMC lifts, build the zero-mass dominance certificate by
  separating the witness choice from the strict comparison.  A useful pattern
  is a fixed positive-mass witness constructor, plus an accept-all
  specialization that consumes accept-all positive mass and the single source
  obligation `zero-mass policy reward < accept-all reward`.  This keeps the
  full-domain theorem surface honest and avoids repeatedly rebuilding the same
  existential witness in paper proofs.
- If a CTMC source theorem is already closed on the paper's
  denominator-valid positive-mass domain, do not keep marking that paper
  result as caveated just because a broader all-feasible totalized abstraction
  fails.  Put the positive-mass paper theorem on the review surface, record the
  all-feasible lift as an optional strengthening with its exact extra
  certificate, and name any zero-mass obstruction theorem so future agents do
  not retry the same false bridge.
- Before adding a new zero-mass bridge, search for compiled all-feasible
  endpoints whose assumption bundle already quantifies over feasible policies.
  In GN21, the source-faithful route is the feasible sequential Lemma 9 then
  Lemma 10 current-bounds endpoint; the zero-mass dominance certificate is only
  one optional lift route and can be incompatible with the current totalized
  real reward.  If the source mathematics treats zero-mass rewards as
  undefined, use a partial/defined reward interface instead of forcing Lean's
  totalized `ℝ` quotient to carry the source semantics.  The useful pattern is
  a structure with `value : (σ) -> positiveMassFeasible σ -> ℝ`, an optional
  `value?` for arbitrary feasible policies, and a theorem that positive-mass IC
  of the total reward implies IC for the defined-reward view.
- Avoid all-candidate nondegeneracy records for Lemma 5/Theorem 4 adapters
  when the candidate universe contains the empty policy.  Empty policies are
  measurable feasible subsets but cannot satisfy positive accepted-mass or
  positive-denominator fields.  If the paper proof only compares an optimum to
  the accept-all candidate, use the candidate-only accept-all certificate route
  and let the a.e. uniqueness lemma turn that single comparison into the paper
  conclusion.
- For GN21-style two-state CTMC surge proofs, the useful "support any ratio"
  paragraph is a small-ratio construction, not a claim that the current fixed
  reward equals the target accept-all reward. Prove a scalar lemma of the form:
  for any envelope `Rmax`, if `0 < R2*T2 - Rmax*(T2-1)` and the Lemma 9 upper
  endpoint is positive, choose a sufficiently small positive surge ratio so
  `m2 > Rmax`, accounting holds, and `z2 < U*(m2-Rmax)`. Then wrap it with the
  current lower-endpoint nonpositivity to get a feasible Lemma 9 ratio.
- For signed structured-price envelopes, use two layers. First prove the
  current reward is below `Rmax = m0` when `z0 <= 0`, or below
  `Rmax = m0 + z0*lambda12` when `0 <= z0`. Second prove the small-ratio
  zero-ratio numerator `0 < R2*T2 - Rmax*(T2-1)`. The `Rmax = R2` branch is
  immediate from `R2 > 0`; the positive-`z0` branch should be derived from the
  non-surge ratio formula/feasibility assumptions, or recorded as the exact
  missing source regime condition.
- When a GN21 small-surge route has a sign-selected `Rmax` envelope and the
  source has normalized accept-all masses, do not carry `Rmax` as a public
  paper assumption if it is just `if z0 <= 0 then R2 else max R2
  (arrival0*z0)`.  Add a no-`Rmax` wrapper that sign-splits this value
  internally, derives `R1 > 0` and `R1 < R2` from `R1 = rho*R2`, `R2 > 0`, and
  `C < rho < 1`, and then calls the older envelope theorem.  Mirror this for
  the fixed-lower-cross route when the paper supplies
  `T_current * Q_acceptAll <= T_acceptAll * Q_current`; this avoids a
  stronger per-policy current final-sign assumption and keeps the public source
  boundary closer to the paper proof.  If the paper has the accept-all lower
  endpoint only as a cross-multiplied final-sign inequality, add one more
  wrapper that derives the divided lower endpoint from the primitive
  denominator signs before calling the fixed-cross theorem.
- GN21 file-organization lesson: when a CTMC proof route has made
  `MainTheorems.lean` unwieldy, add a new proof-route module for the stable
  declaration cluster while keeping `MainTheorems.lean` as the stable source
  ledger. Validate with targeted builds of the new route module and then the
  paper root. Do not do a risky broad declaration move unless the cluster
  already builds in place, and never use `git reset` to recover in a shared
  worktree.
- GN21 explicit counterexample lesson: for a measured CTMC non-IC result,
  prefer an isolated atomic-instance file over exact exponential arithmetic in
  the main ledger.  Prove the weighted-Dirac `singleStateTripMass`,
  `singleStateTripTime`, and `singleStateTripPayment` reductions once using
  `Measure.restrict_add`, `Measure.restrict_smul`, `restrict_dirac`,
  `integral_add_measure`, `integral_smul_measure`, and `integrable_dirac`.
  Then reduce the aggregate reward to named `Q,T,W` primitives and prove the
  strict comparison from rational envelopes on switch probabilities.  This is
  much faster than asking `ring_nf`/`nlinarith` to simplify formulas containing
  `Real.exp`; use `Real.add_one_lt_exp` only to get the one lower switch bound
  needed for the rational envelope.
- GN21 route-selection lesson: the finite/infinite pointwise upper-transfer
  branch is not the default paper path for Theorem 3.  For reject-long CTMC
  policies, the proved monotonicity gives the lower-transfer direction; the
  upper-transfer branch needs an extra source upper/equality assumption.  Use
  the small-surge sequential route instead: move surge to accept-all with
  small slack, then apply the non-surge Lemma 10 comparison after surge is
  fixed at accept-all.
- GN21 Theorem 4 exact-endpoint lesson: when the exact one-threshold
  non-accept-all endpoint route is already compiled, expose it through a split
  frontier module and `PaperInterface` before doing more algebra.  The useful
  next proof obligation is deriving the finite-ray source-selection fields and
  fixed-state aggregate-cross endpoint facts from the paper primitives for
  arbitrary measurable optima; reassembling the accept-all unique-optimality
  conclusion is not the bottleneck.
- GN21 Theorem 4 AE-route lesson: if the source theorem is only up to measure
  zero, prefer the positive-rejected-mass representative route over forcing
  exact selector equality.  Use existence-based certificates such as
  `GN21Theorem3MiddleRerouteAEPolicyFormSourceExistenceData` and route through
  `to_shape_replacement_rejected_mass_improvements_existence_of_shape_replacements`;
  `to_accept_all_certificate` derives accept-all optimality, so do not add a
  separate accept-all-optimality assumption just to call an older wrapper.
- GN21 Theorem 4 source-boundary lesson: before proving a new fixed-price
  accept-all uniqueness theorem, check `Theorem4Frontier.lean` for direct
  wrappers from the active Theorem 3 source packages.  The light equality,
  feasible-canonical, fixed-response equality, by-policy-form middle-cutoff,
  aggregate surge-cross, and scalar surge-cutoff packages already lower to the
  a.e. Theorem 4 conclusion; the remaining source work should derive one of
  those packages from paper primitives, not rebuild rejected-mass or
  accept-all-optimality plumbing.
- GN21 Lemma 5 adapter lesson: when state source data are response-dependent,
  obtain the marginal-response fields through the fixed-response converter
  such as `D.to_fixed_response hρ`; using the base policy-form data directly
  can silently give the wrong response type and waste a build cycle.
- GN21 Theorem 4 a.e. lesson: when a frozen fixed-state continuation
  objective is a positive affine transform of a Lemma 5 marginal-response
  reward, prefer the a.e. positive-affine bridge
  (`Lemma5PositiveResponsePolicyFormData.feasiblePolicyFormAlmostEverywhere_of_positive_affine_*`,
  `...of_dynamicStateReward_positive_affine`, and the GN21
  `...to_feasible_policy_form_ae_positive_affine` adapters) over exact
  canonical-dominance data unless the endpoint route truly needs exact forms.
  This avoids introducing `hstrict_mass` obligations stronger than the
  source's null-boundary convention.
- GN21 Theorem 4 exact-form lesson: if the endpoint route truly needs feasible
  policy-canonical dominance, do not rebuild all-optima packaging by hand.
  Feed the per-state fixed-response source records, current openness,
  continuity, strict-mass witness, and positive-affine objective identity into
  `Theorem4AllMeasurableGN21FixedResponsePolicyCanonicalDominancePositiveAffineData`;
  its `.to_feasible_policy_canonical_dominance` method produces the exact
  Theorem 4 certificate.  Use this only when the positive-affine identity is
  true; otherwise stay on the quotient-cross-multiplication
  marginal-optimality/a.e. route.  The remaining hard work is proving the
  relevant statewise fields, not reassembling allowed-policy-form wrappers.
- GN21 Lemma 5 current-branch lesson: when an optimum is already in a
  canonical middle branch, add or use a current-policy replacement constructor
  instead of rebuilding optimizer-replacement certificates.  Prove equality to
  the canonical accept-middle/reject-middle policy from the exact shape plus
  `σ ⊆ acceptAllPolicy`, then discharge strictness with the corresponding
  Lemma 5 policy-form constructor.
- To avoid token-heavy Lean retries in CTMC algebra, name the denominator and
  numerator identities before using inequalities. Prove `m-r = numerator/den`
  and `z = ratio*B/den`, then transfer slack by
  `div_lt_div_of_pos_right` instead of letting `ring_nf` expand a whole
  reward-rate inequality. For small-ratio existence, choose
  `ratio = min upper (min eps_slack eps_positive) / 2` and derive each
  half-bound with explicit positive-denominator multiplication.
- When the current Lemma 9 upper endpoint varies with the fixed current
  policy, prove a policy-uniform positive lower bound first and transfer slack
  with one monotonic multiplication lemma. This is cheaper and clearer than
  rebuilding the surge construction for every current upper expression.
- GN21 post-closeout lesson: record the positive-denominator domain before
  proving reward-rate theorems.  A paper may say "trip distribution has
  positive mass" or normalize accept-all mass, but arbitrary feasible policies
  can still accept a zero-measure set.  If the source reward is undefined at
  zero accepted mass, expose a positive-mass theorem surface or a partial
  `definedReward` interface; do not let Lean's totalized `ℝ` division silently
  define the source expression.
- GN21 post-closeout lesson: continuous/a.e. proof work was faster than a
  finite detour once the paper-facing theorem was continuous.  Use finite or
  atomic models for sanity checks and counterexamples, but close the named
  paper theorem over measurable sets, integrals, and a.e. policy equality when
  that is the source statement.
- GN21 post-closeout lesson: split stochastic, algebraic, and policy-shape
  obligations into reusable seams.  Renewal-reward strong-law wrappers,
  two-state CTMC switch/time-fraction identities, positive-denominator
  reward-rate bridges, endpoint-move calculus, and a.e. interval-policy
  replacement lemmas should be extracted to library modules when a second paper
  needs them or when the paper-local file becomes too large to navigate.
  For continuous accepted-set reward accounting, start from
  `AppliedModelingLib.Foundations.Probability.ContinuousReward` instead of recreating
  trip-mass/time/payment wrappers in each paper.
- For CTMC papers with explicit counterexamples, isolate the counterexample in
  a narrow module and reduce continuous weighted-Dirac integrals to named
  aggregate primitives before proving strict comparisons.  Use finite/atomic
  arithmetic to witness existential non-IC claims, not as a replacement for the
  source's continuous theorem surface.
- After finishing a CTMC/renewal-reward paper, do a library-lift audit before
  final handoff.  Typical lift candidates are: continuous accepted-set mass,
  time, and payment primitives; two-state CTMC reward-rate accounting and
  time-fraction decompositions; positive-denominator/partial-reward APIs;
  endpoint derivative-to-global-move calculus; and finite atomic measure
  reduction lemmas.  If you move paper-local definitions to library
  primitives, keep the paper-facing formulas explicit and call the library
  through thin `simpa` wrappers; opaque aliases can break existing proof shapes
  and make `PaperInterface.lean` harder to review.  Document candidates even if
  you defer the extraction.

## Finite PMF and Expectation Seams

- For finite expectation decompositions, prove pointwise identities first, then
  `pmfExp`/`pmfPairExp` sum identities, then the paper-facing equivalence.
  Group by the event or fiber appearing in the paper.
- For sequential weighted without-replacement or "first distinct draw" models,
  audit conditioning/deletion claims before proving them. Conditioning on an
  item being absent from the first `k` distinct draws is generally not the same
  as deleting that item's weight when weights are nonuniform and `k >= 2`. If a
  source proof says conditioning equals deletion, test a small numeric model
  outside Lean, then formalize the inequality actually needed directly. Keep
  false equalities or false deletion upper bounds only as clearly named rejected
  scratch targets, never as theorem assumptions hidden inside green
  paper-facing results. If small audits show the generalized theorem is false,
  record the counterexample and redirect the paper proof to a corrected
  statement instead of continuing proof search.
- For probability-delta comparisons, prove the tiny indicator inequality over
  the finite outcome type, then lift it with a generic PMF lemma comparing
  indicator differences.
- For finite-PMF event bounds, use
  `pmfExp_le_const_mul_pmfProb_of_forall_le_indicator` when a pointwise
  estimate has the form `X x <= C * 1_E x`, and use
  `pmfPairExp_indicator_and_eq_mul_pmfProb` when an independent pair event
  factors into separate left/right indicators. Keep paper-local copies as thin
  wrappers if old theorem names are part of the paper interface.
- For finite independent-sampling concentration, check Mathlib's
  `Probability.Moments.SubGaussian` before proving Chernoff/Hoeffding from
  scratch. A fast reusable seam is: compose independent variables with a
  centering map, use `hasSubgaussianMGF_of_mem_Icc` for bounded variables, and
  expose a paper-facing wrapper over `measure_sum_ge_le_of_iIndepFun`.
- If a broad shared probability file is dirty or being edited by another
  formalization thread, do not spend proof time repairing unrelated theorem
  experiments. Put the needed stable seam in a focused module with distinct
  names, import that module in the paper-facing file, and leave the shared file
  unstaged unless you intentionally own its changes.
- For strict event monotonicity, split the larger event into the smaller event
  plus a residual event and prove positive residual mass from a finite atom
  witness.
- For two-outcome probabilities, first prove `wrong = 1 - correct`, then turn
  `wrong < correct` into `1 / 2 < correct` when that matches the paper proof.
- For pairwise probability monotonicity, define unnormalized `correctWeight`
  and `wrongWeight`, prove their sum is the partition/mass of the relevant
  sample space, and only then normalize. If the paper proof cancels common
  factors to a reduced finite sum, expose a named reduction bridge from actual
  weights to reduced weights; keep the source theorem conditional until that
  bridge is discharged.
- For finite analytic PMF families, prove continuity at the atom level
  `fun theta => ((mu theta) a).toReal`, then lift through finite expectation
  lemmas such as `epsilonContinuousAt_pmfExp_of_atom`.
- For pure PMFs, use lemmas such as `pmfExp_pure`,
  `pmfPairExp_pure_left`, and `pmfPairExp_pure_right` when available.
- For finite-label papers, start from
  `AppliedModelingLib.Foundations.Probability.FiniteLabel`: use
  `finiteLabelIndicator`, `finiteLabelShare`,
  `finiteLabelAggregateScore`, `FiniteLabelSimplex`,
  `sum_finiteLabelShare_eq_measureReal_univ`,
  `sum_finiteLabelAggregateScore_eq_measureReal_univ_of_measurable_simplex`,
  and the finite-label MAE bounds/integrability lemmas before writing
  paper-local indicator integrals. This is the DSWG-style source interface for
  label shares, aggregate posteriors, posterior-simplex constraints, and
  classifier-error terms.
- For finite Bayesian signal kernels, use
  `AppliedModelingLib.Foundations.Probability.Kernel`:
  `pmfKernelJoint`, `pmfKernelSignalMarginal`,
  `pmfKernelSignalProb`, `pmfKernelPosteriorExpectation`,
  `pmfKernelPosteriorExpectation_mul_signalProb_eq_sum_of_pos`,
  `pmfKernelPosteriorExpectation_const_one_eq_one_of_pos`,
  `pmfKernelPosteriorExpectation_nonneg_of_nonneg`,
  `pmfKernelPosteriorExpectation_le_of_forall_le`,
  `pmfKernelPosteriorExpectation_mem_Icc_of_mem_Icc`, and
  `pmfKernelJointExp`. For admissions/testing papers using
  `AdmissionsModel`, prefer the thin `admissionsPosteriorExpectation_*`
  wrappers.
- For ordinary finite conditional expectations, use
  `pmfConditionalExp_mul_prob_eq_indicatorExp_of_pos`,
  `pmfConditionalExp_const_one_eq_one_of_pos`,
  `pmfIndicatorExp_nonneg_of_nonneg`,
  `pmfIndicatorExp_le_prob_mul_of_forall_le`,
  `pmfConditionalExp_nonneg_of_nonneg`,
  `pmfConditionalExp_le_of_forall_le_of_pos`, and
  `pmfConditionalExp_mem_Icc_of_mem_Icc_of_pos`. These are the right tools for
  bounded posterior estimates, resampling policies, and conditioning-on-event
  arguments before introducing source-specific Gaussian algebra.
- For finite binary-mixture or test-reporting policies, start from
  `AppliedModelingLib.Foundations.Probability.FiniteMixture` instead of writing
  paper-local event-share algebra. Use `binaryMixturePMF`,
  `pmfEventShare`, `indexedPMFEventShare`, full-support bridges such as
  `indexedPMFEventShare_pos_of_full_support_exists`,
  `indexedEventPositiveOrBlank`, `indexedValueBlankOnZeroEventShare`,
  `pmf_mixture_cancel_right`, `extensional_law_mixture_cancel_right`,
  `pmf_map_apply_toReal_pos_of_pos`, and
  `indexedBinaryMixturePMF_no_positive_event_raw_relevance_iff_selected_eq_unselected_on_positive_event`.
  The robust route is: model the source mixture with a finite event share,
  normalize the full-feature law to be blank when the share is zero, prove raw
  relevance only on positive-event profiles, and use positive-share
  cancellation to turn equality of the mixture with the unselected law into
  equality of selected and unselected component laws.
- For Gaussian admissions/testing papers, start with
  `AppliedModelingLib.Foundations.Probability.Gaussian` before making paper-local
  definitions. Use `GaussianScaleLaw.standardize`,
  `StandardGaussianCDFAPI.normalCDF_mono`,
  `GaussianPriorSignal.posteriorVariance_eq_mul_div`,
  `GaussianPriorSignal.posteriorMean_eq_weightedAverage`,
  `GaussianPriorSignal.posteriorMean_eq_priorMean_add_signalWeight_mul`,
  `GaussianPriorSignal.posteriorMean_mono`,
  `GaussianPriorSignal.posteriorMeanSignalCutoff`,
  `GaussianPriorSignal.threshold_le_posteriorMean_iff`,
  `GaussianPriorSignal.threshold_le_posteriorMeanOfSignalWithNoiseMean_iff`,
  `GaussianPriorSignal.thresholdPassProb_posteriorMeanRawSignalScaleLaw`,
  `GaussianPriorSignal.posteriorMeanLaw`, and
  `GaussianSignalFamily.posteriorMean_mono_of_pointwise_le` for conjugate
  Gaussian posterior algebra. Use
  `GaussianSignalFamily.posteriorMean_eq_weighted_sum` for finite feature sets,
  `GaussianSignalFamily.posteriorVariance_le_priorVar`, and
  `GaussianSignalFamily.posteriorMeanVariance_nonneg` for finite-feature
  posterior variance comparisons,
  `GaussianSignalFamily.posteriorMeanLaw` and
  `GaussianOffsetSignalFamily.posteriorMeanLaw` when a source lemma states the
  distribution of estimated skill/posterior mean,
  and use `GaussianOffsetSignalFamily` when source features have the form
  `q + noiseMean k + centeredNoise k`. Use
  `GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt`
  when a testing paper compares posterior-score marginal scales across
  different feature sets; this avoids forcing full/test-free features into the
  same finite index type just to reuse same-index precision lemmas.
  For school-capacity cutoffs with finitely many Gaussian applicant groups, use
  `StandardGaussianCDFAPI.mixtureTailMass` and
  `existsUnique_mixtureTailMass_eq_and_region_of_capacity_mem_Ioo` before
  writing paper-local intermediate-value arguments; it gives both the unique
  capacity-realizing cutoff and the upper-threshold region characterization
  from CDF end limits, nonnegative weights, a positive group weight, and
  capacity in `(0, totalWeight)`.
  Use
  `GaussianOffsetSignalFamily.conditionalPosteriorMeanScaleLaw` and
  `GaussianOffsetSignalFamily.conditionalPosteriorMeanScaleLaw_standardize_threshold`
  when a paper conditions on true skill and writes the posterior-score
  admission probability as `1 - Phi((priorTerm - precision*(q-threshold)) /
  sqrt precision)`.
  Use `StandardGaussianTailLimitAPI` when the paper concludes that a difference
  of high-skill admission probabilities tends to zero because both affine
  upper tails tend to one. Use `StandardGaussianAnalyticAPI` when a paper lemma
  needs the doubled-log density comparison and the high-skill CDF tail limit to
  refer to the same abstract normal CDF/density implementation.
  Use
  `GaussianScaleLaw.affineImage` and
  `StandardGaussianCDFAPI.thresholdPassProb_affineImage_pos` when a paper
  pushes a Gaussian signal through a positive affine posterior-score map. Use
  `StandardGaussianCDFAPI.thresholdPassProb_antitone_threshold` and
  `StandardGaussianCDFAPI.thresholdPassProb_le_of_mean_le_same_scale` for
  cutoff/mean monotonicity. Use
  `StandardGaussianQuantileAPI.lt_standardTail_iff_lt_quantile_one_sub` and
  `StandardGaussianQuantileAPI.standardTail_lt_iff_quantile_one_sub_lt` for
  strict best-response or threshold-uniqueness arguments around an inverse-CDF
  cutoff; prove strict payoff order from these lemmas instead of duplicating
  CDF algebra in a paper file. Use
  high-skill affine-tail delta wrappers only after auditing the exact slope
  order they require. A source phrase like "unequal precision" may give only a
  full-policy ordering, while an eventual comparison of full-minus-sub upper
  tails can require a separate test-free slope ordering; keep that extra
  premise explicit unless it is actually derived from the raw model. Use
  direction-specific wrappers for high-skill comparative statics: if the theorem
  statement, surrounding narrative, and appendix proof disagree about whether
  a gap is larger before or after a policy change, prove both algebraic
  directions under the corresponding delta inequality and document the source
  mismatch before choosing a preferred paper-facing endpoint. Use
  `StandardGaussianCDFAPI.mixtureTailMass_antitone_threshold` and
  `StandardGaussianCDFAPI.MixtureThresholdCertificate` for source equations
  where a common admission cutoff realizes a finite group-mixture capacity.
  When a paper assumes a cutoff family continuously clears fixed capacity, first
  try proving continuity from the capacity equation itself: a finite Gaussian
  mixture mass is continuous in the access parameter and strictly antitone in
  the cutoff, so the level-set squeeze often removes a standalone continuity
  hypothesis from the paper-facing theorem. Use
  `AppliedModelingLib.Foundations.Probability.GaussianDerivatives` for admissions
  lemmas that differentiate affine standardized Gaussian upper tails:
  `StandardGaussianDerivativeAPI.affineUpperTail_hasDerivAt`,
  `StandardGaussianDerivativeAPI.affineUpperTailDifference_hasDerivAt`, and
  the corresponding continuity lemmas discharge raw derivative/continuity
  premises quickly. Use
  `StandardGaussianDerivativeAPI.affineUpperTail_gt_iff_cutoff_lt_of_slope_lt`
  when a paper states that one affine Gaussian admission probability exceeds
  another exactly above a skill cutoff. When a paper compares normal-density terms by taking logs,
  check whether the source silently doubled logs and canceled the shared
  standard-normal normalizing constant; if so, use
  `StandardGaussianDoubledLogDensityAPI` and prove a doubled-log identity
  instead of trying to force an impossible raw `log weighted = -z^2 + log
  precision` equality.
  Mathlib has concrete real Gaussian measures and PDF facts in
  `Mathlib.Probability.Distributions.Gaussian.Real` (`gaussianReal`,
  `gaussianPDFReal`, Gaussian laws, affine transforms, moments). Use those
  before creating any new primitive normal-distribution definitions. For the
  concrete standard-normal CDF/density layer, use
  `AppliedModelingLib.Foundations.Probability.GaussianMathlib`: continuity is fastest
  through `ProbabilityTheory.cdf` as a Stieltjes function plus `NoAtoms`,
  strict monotonicity through positive Gaussian mass on `Ioc` via
  `setLIntegral_pos_iff` and `support_gaussianPDF`, and the median through
  `gaussianReal_map_neg` plus `probReal_compl_eq_one_sub`. For real
  standard-normal quantiles, use `standardGaussianCDFOrderIso` and
  `standardGaussianQuantileAPI`; remember that the true inverse CDF is
  continuous on `(0,1)`, not globally on all real inputs, so paper proofs
  should prove their quantile arguments lie in `(0,1)` from selectivity or
  capacity assumptions. The concrete standard-normal inverse-Mills/hazard
  bridge now lives in `AppliedModelingLib.Foundations.Probability.GaussianMills` and
  `AppliedModelingLib.Foundations.Probability.GaussianMathlib`: use
  `standardGaussianHazardInverseCertificate` when a paper needs the real
  standard-normal hazard, and remember the inverse law is only stated for
  positive right-hand sides (`0 < y`) because the hazard is positive. Keep
  paper-specific or nonstandard hazard/truncated-normal derivations behind
  `GaussianHazardCertificate` or `GaussianHazardInverseCertificate` until their
  concrete bridge is proved. Once a hazard certificate is supplied, use
  `GaussianHazardCertificate.normalTail_pos`,
  `GaussianHazardCertificate.normalDensity_div_normalTail_eq_hazard_div_scale`,
  `GaussianHazardCertificate.normalUpperTailMean_mono_threshold`,
  `GaussianHazardCertificate.normalUpperTailMean_gt_threshold`,
  `GaussianHazardCertificate.mixtureTailMass_pos`, and
  `GaussianHazardCertificate.mixtureUpperTailMean_mul_tailMass_eq_numerator`
  for location-scale tail, academic-merit, and finite-mixture admitted-mean
  comparisons. The certificate field
  `GaussianHazardCertificate.hazard_gt_arg_of_pos` packages the Mills-ratio
  fact that the standard-normal hazard is above every positive standardized
  cutoff; the concrete mathlib-backed standard-normal theorem is
  `standardGaussian_normalUpperTailMean_gt_threshold`.
  For no-barrier admissions cutoffs, prefer constructing thresholds with
  `StandardGaussianCDFAPI.exists_mixtureTailMass_eq_of_capacity_mem_Ioo` plus
  concrete `standardGaussianCDF_tendsto_atBot`/`standardGaussianCDF_tendsto_atTop`
  instead of leaving separate capacity-equation assumptions for each policy.
  When a paper needs the concrete derivative of the standard-normal CDF, avoid
  leaving a derivative certificate in the paper folder.  In
  `GaussianMathlib`, prove `cdf x = ∫ y in Iic x, density y` with
  `ProbabilityTheory.gaussianReal_apply_eq_integral`, convert `measureReal`
  via `ENNReal.toReal_ofReal` using density nonnegativity, and then apply the
  interval-integral fundamental theorem to `u ↦ ∫ y in Iic u, density y`.
  This gives `standardGaussianCDF_hasDerivAt_density` and the reusable
  `standardGaussianAnalyticAPI`.  For doubled-log density comparisons, prove
  the standard-normal elementary density formula once and set the constant to
  `2 * log ((sqrt (2*pi))⁻¹)`.
  For admissions threshold statements, distinguish the main-body real-threshold
  claim from stronger appendix interior-threshold claims. A continuous strictly
  monotone scalar score on `[0,1]` has a real cutoff for its strict or weak lower
  set without endpoint-crossing assumptions; use
  `exists_threshold_of_continuous_strictMonoOn_Icc` or
  `exists_threshold_le_of_continuous_strictMonoOn_Icc`. Only use endpoint
  crossing lemmas when the paper explicitly needs an interior threshold.
  For access-barrier threshold theorems that use `Φ⁻¹` or `HR⁻¹`, keep the
  analytic inverse facts narrow: use `StandardGaussianQuantileAPI` for
  quantile monotonicity/continuity/positivity above one half, and use
  `GaussianHazardInverseCertificate` only for the order bridge
  `HR(z) <= y ↔ z <= HR⁻¹(y)`. Then prove the paper's algebraic
  monotonicity separately with scalar lemmas such as
  `sqrt_fractionalLinear_const_mul_lt_of_rho_lt_one` and
  `sqrt_fractionalLinear_mul_const_lt_of_one_lt_rho`, instead of assuming the
  whole `β` or `η` characterization.
  For diversity under fixed group-A access barriers, prefer the capacity
  equation route to differentiating the displayed `η` formula: prove the
  admission cutoff is strictly increasing in group-B access from the capacity
  equations and positive tails, then infer diversity monotonicity from the
  falling group-A tail share. If the source defines diversity as the admitted
  group-B share, first use the capacity equation to rewrite that direct share
  as the complement of admitted group-A mass over capacity; do this algebraic
  bridge once instead of carrying both diversity formulas through the proof.
  Prefer one explicit metric-definition endpoint after proving the route:
  define admitted-share diversity and Gaussian upper-tail academic merit in
  Lean, then prove the paper theorem from those definitions. This is more
  audit-friendly than a theorem whose hypotheses are already-expanded hazard
  equations.
  For no-barrier Gaussian admissions comparisons, a fast threshold route is:
  prove the dropped-feature threshold is above the common mean from selective
  capacity, show the full-policy mixture tail at that lower threshold is
  strictly larger because both group scales increased, then use antitonicity of
  the full-policy mixture tail to force `thresholdSub < thresholdFull`. For
  group academic merit, combine the strict same-threshold scale comparison of
  `normalUpperTailMean` with monotonicity in the threshold instead of trying to
  prove a new two-parameter truncated-normal theorem.
- For finite rating-scale large-deviation papers, start with
  `AppliedModelingLib.Foundations.Probability.FiniteSupportMGF`: use `finiteMGF`,
  `finiteLogMGF`, `finiteLegendreValue`, `finiteRateFunction`, and
  `FiniteRatingLDPModel` to state source log-MGF and rate-function formulas
  before adding paper-specific rating designs or ranking rules.
  For finite-support boundary cases, use the extended-rate layer instead of
  forcing false real-valued interior hypotheses: `finiteRateFunctionTop`,
  `withTopRealScale`, `FiniteRatingLDPModel.rateFunctionTop`,
  `FiniteRatingLDPModel.pairwiseRateObjectiveTop`,
  `FiniteRatingLDPModel.pairwiseThresholdRate`, and
  `FiniteRatingLDPModel.pairwiseThresholdRateTop`.  A good source-facing
  pattern is: prove the interior real-valued Chernoff/rate formula where the
  stationary tilt exists, expose one-sided or eventually-zero branches as
  `WithTop` boundary cases, then wrap the paper theorem so these branches are
  visible but not mislabeled as unfinished certificates.
  For finite ranking-learning papers, keep the layers separate: pairwise
  finite-support log-MGF rate, ternary score-gap/K-approval specialization,
  then finite relevant-pair aggregation.  Do not start with the aggregate
  theorem; it is usually a one-line consumer of pairwise certificates once the
  pairwise finite-support endpoints are source-shaped.
- For exponential-rate aggregation, use
  `AppliedModelingLib.Foundations.Probability.LargeDeviations`: represent the analytic
  distribution-family theorem as an `ExponentialRateCertificate` or
  `LargeDeviationRateCertificate`, convert exact rates to weaker eventual
  upper bounds with
  `ExponentialRateCertificate.hasExpUpperBoundWithConst_of_lt`, convert exact
  rates to weaker eventual lower bounds with
  `ExponentialRateCertificate.hasExpLowerBoundWithConst_of_gt`, and aggregate
  finite unions or weighted sums with
  `finite_weighted_sum_hasExpUpperBoundWithConst`,
  `finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates`,
  `finite_weighted_sum_hasExpLowerBoundWithConst_of_component`,
  `finite_weighted_sum_hasExpLowerBoundWithConst_of_rate_certificate_component`,
  `PairwiseErrorUpperBoundCertificate.aggregateError_hasExpUpperBoundWithConst`,
  or
  `PairwiseErrorRateCertificate.aggregateError_hasExpUpperBoundWithConst_of_lt`.
  Use
  `PairwiseErrorRateCertificate.aggregateError_hasExpLowerBoundWithConst_of_component_gt`
  when a lower-bound or optimality argument needs to show the aggregate cannot
  decay faster than one positive-weight pairwise error.
  Keep Gartner-Ellis, Cramer, and Laplace-principle derivations behind an
  explicit certificate unless the paper needs the analytic proof itself.
- For accuracy-diversity/order-statistic papers, separate the reusable layers:
  finite separable-optimization and FOC bridges belong in optimization or the
  recommender layer; top-`k` expectation oracles and distribution-family
  asymptotic certificates belong in probability. Use
  `AppliedModelingLib.Foundations.Probability.OrderStatistics`:
  `TopKExpectationOracle`, `TopKExpectationOracle.marginalTopK`,
  `TopKExpectationOracle.HasDiminishingReturnsAt`,
  `TopKExpectationOracle.HasNonnegativeMarginalsAt`, and
  `TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_marginal_sandwich`,
  `TopKExpectationOracle.ScaledMarginalLimitCertificate.marginal_lt_of_scaled_gap`,
  and
  `TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_same_count_marginal_lt_of_weight_gap`.
  For pointwise real samples, the same file now provides
  `ascendingOrderStatistic`, `upperOrderStatistic`, `sampleTopKSum`,
  `sampleTopKEndpointLoss_eq_reflectedBottomKSum`, and
  `upperOrderStatistic_eq_endpoint_sub_reflectedAscending`. For expectations
  over a finite sample law, use
  `expectedSampleTopKSum_eq_sum_expectedUpperOrderStatistic` and
  `expectedSampleTopKEndpointLoss_eq_expectedReflectedBottomKSum`. The generic
  sorted-tuple measurability and bounded-support integrability layer is also
  available: `ascendingOrderStatistic_measurable`,
  `reflectedAscendingOrderStatistic_measurable`,
  `sampleTopKSum_integrable_of_ae_bounds`, and
  `reflectedAscendingOrderStatistic_integrable_of_ae_bounds`. For finite
  layer-cake arguments, use
  `ascendingOrderStatistic_eq_integral_rank_count_indicator` and
  `reflectedBottomKSum_eq_integral_rank_count_indicator`; for measure-level
  arguments, use `reflectedBottomKRankCountLayer` and
  `expectedReflectedBottomKSum_eq_integral_rank_count_layer_of_integrable`.
  If the finite sample law has coordinatewise a.e. bounds, discharge the
  product/Fubini integrability side with
  `reflectedBottomKRankCountLayer_integrable_prod_of_ae_bounds` before
  specializing to a distribution's iid CDF/binomial-count law. For iid real
  product laws, lift one-dimensional support to coordinatewise sample support
  with `iidProductMeasure_forall_bounds_ae`.
  For iid product laws, the generic finite-count facts are
  `iidProductMeasure_successCount_eq_real`,
  `iidProductMeasure_successCount_le_real`, and
  `iidProductMeasure_successCount_eq_indicator_integral`; PRPKG's reflected
  bounded branch wraps these as
  `paper_definition3_iid_reflected_count_layer_inner_integral_binomial` and
  `paper_definition3_iid_reflected_count_layer_inner_integral_kernel`, with
  outer fixed-`k` assembly in
  `paper_definition3_iid_reflected_count_layer_integral_kernel_of_integrable_of_le`.
  Concrete bounded, exponential, and Pareto order-statistic integrals should be
  proved once as certificate providers and then fed into the paper's
  homogeneity/FOC certificates.
- For bounded reflected-CDF arguments, use
  `AppliedModelingLib.Probability.reflectedCDFMass μ M` instead of expanding
  `Measure.real {y | M - y <= x}` in a paper folder. The library supplies
  `reflectedCDFMass_measurable`, `reflectedCDFMass_mono`,
  `reflectedCDFMass_nonneg`, `reflectedCDFMass_le_one`, and
  `reflectedCDFMass_eq_one_of_ae_bounds`, so bounded iid PRPKG wrappers only
  need base support, positive support width, and the concrete near-zero
  `BoundedTailCDFPowerSandwich` proof for that reflected CDF. If the CDF is
  eventually exactly `(c / beta) * x ^ beta`, use
  `BoundedTailCDFPowerSandwich.of_eventually_eq_const_mul_power`; the identity
  reflected CDF has `BoundedTailCDFPowerSandwich.identity_beta_one`. For the
  concrete continuous uniform law on `[0,1]`, PRPKG has `uniform01Measure` and
  `uniform01_reflectedCDFMass_eventually_eq_power`.
- For PRPKG bounded loss-to-marginal steps, do not subtract asymptotic
  equivalents. The compiled bridge is
  `bounded_source_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop`; it
  takes `A - h(q) ~ C*boundedTailScale beta q` plus the explicit scaled-drop
  limit `(q+1)*((A-h(q))-(A-h(q+1)))/(A-h(q)) -> 1/beta` and returns the
  forward marginal asymptotic with `boundedPowerMarginalScale`. The helper
  `boundedTailScale_div_succ_ratio_eventually_eq_rpow` records the necessary
  off-by-one scale ratio `((q+1)/q)^(1/beta)`, and
  `boundedTailScale_div_succ_ratio_tendsto_one` proves its limit. Source-level
  PRPKG wrappers ending in `_and_scaled_drop` combine this with bounded
  reflected-CDF Lemma 1 endpoints. Convert the resulting source marginal into
  the shared probability-to-optimization interface with
  `BoundedOrderStatisticScaledMarginalCertificate.toTopKScaledMarginalLimitCertificate`
  or the paper-facing
  `paper_theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_loss_ae_and_scaled_drop`.
  For exact uniform `[0,1]` order-statistic means, PRPKG also has the direct
  bounded `β = 1` certificate
  `paper_theorem1_ii_uniform_order_statistic_scaled_marginal_certificate`;
  the source-oracle sequence wrappers then reuse the exact uniform top-`k`
  theorem via
  `paper_theorem1_ii_uniform_order_statistic_toConsumptionModel_eq`.
- For PRPKG-style continuous order-statistic branches, do not reopen the
  already-closed optimization wrappers when the missing layer is a sampled-law
  bridge. Use the existing real tuple and expectation source interfaces, then
  add only the missing law-specific iid-product/CDF layer: closed reflected-CDF
  identities for bounded upper support, Pareto CDF/gamma-ratio facts, and
  finite-prefix wrappers for fixed `k` asymptotics. In PRPKG,
  `sampleOrderStatisticValue`,
  `orderStatisticTopKSumFromSample_eq_sampleTopKSum`, and
  `expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum`, plus
  `paper_lemma1_bounded_support_order_statistic_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support`
  are the compiled bridge names. Treat exact power-marginal oracles as optimizer
  checkpoints only; the paper proof is not closed until the actual distribution
  yields the corresponding scaled-marginal or source-loss certificate.
- For bounded-support top-`k` proofs, keep the reflection step separate from
  the tail asymptotic. A reusable bridge should prove that upper
  order-statistic means for `X` with endpoint `M` equal `M` minus lower
  order-statistic means for the reflected variable `M - X`; the paper-local
  Lemma D.2 layer should only consume the resulting reflected-CDF integral
  terms. Handle the `min k a` versus fixed-`k` asymptotic boundary with an
  eventual `k ≤ a` or finite-prefix lemma rather than strengthening every
  identity to all small sample sizes.
- For Pareto top-`k` proofs, a certificate boundary matching the source's cited
  order-statistic facts is acceptable before a full gamma-integral proof. Keep
  the fields auditable: maximum-order-statistic asymptotic, fixed-rank gamma
  multiplier, strict concavity or diminishing marginals, positive leading
  constant, and the resulting `TopKExpectationOracle.ScaledMarginalLimitCertificate`.
  In PRPKG, the compiled boundary is
  `ParetoOrderStatisticScaledMarginalCertificate`, whose key source field is
  `marginal_ratio_tendsto`; it converts to the reusable scaled-marginal
  certificate via `toTopKScaledMarginalLimitCertificate`. For rank-by-rank
  gamma-ratio proofs, prefer `ofFiniteRankScaledLimits`: prove the scaled
  marginal limit for each fixed `i : Fin k`, then discharge the aggregate
  constant with a finite sum identity. In PRPKG, `paretoRankMarginalCoeff` is
  the canonical gamma coefficient and `ofParetoRankScaledLimits` builds the
  aggregate certificate from those per-rank limits. If the source proof first
  establishes the fixed-rank value asymptotic and an explicit scaled-drop
  limit, `pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop`
  converts those two facts into the per-rank scaled marginal limit. If the
  source formula is the cited gamma-ratio expression itself, use
  `paretoRankGammaRatioMean_scaled_limit`; the remaining work is then only to
  identify actual Pareto order-statistic means with that exact sequence.
  The reusable gamma-ratio route lives in
  `AppliedModelingLib.Foundations.Math.GammaAsymptotics`: it proves the shifted product
  identity against `Real.GammaSeq`, uses `Real.GammaSeq_tendsto_Gamma` to get
  `Γ(q+1)/Γ(q+1-δ) ~ q^δ` for `0 < δ < 1`, and exposes
  `scaled_difference_limit_of_value_asymptotic_and_scaled_drop` for the generic
  finite-difference step. Reuse
  `AppliedModelingLib.Math.gamma_ratio_nat_add_one_sub_asymptoticEquivalent`,
  `AppliedModelingLib.Math.scaled_difference_limit_of_value_asymptotic_and_scaled_drop`,
  `paretoRankGammaRatioMean_value_asymptoticEquivalent`,
  `paretoRankGammaRatioMean_succ_div_self`,
  `paretoRankGammaRatioMean_scaled_drop`, and
  `pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop` rather than
  subtracting asymptotic equivalents.
- For real-valued threshold/tail arguments, use
  `AppliedModelingLib.Foundations.Probability.RealDistribution`: `lowerCDFMass`,
  `upperTailMass`, `lowerCDFMass_mono`, `upperTailMass_antitone`,
  `lowerCDFMass_eq_cdf`, `upperTailMass_eq_one_sub_cdf`,
  `reflectedCDFMass`, and `UpperTailThresholdCertificate`. Put concrete
  distribution-family tail asymptotics on top of these wrappers instead of
  repeating `Measure.real (Iic x)`, `Measure.real (Ioi x)`, or reflected
  endpoint-event algebra in paper folders.
- For finite union bounds over paper-indexed bad events, first prove the event
  inclusion or exact event equivalence, then use
  `pmfProb_exists_mem_le_sum` for a finite index set or
  `pmfProb_exists_le_card_mul` when every indexed event has the same upper
  bound `eps`. Keep any paper shorthand such as `choose(k+2,2) <= k^2` as an
  explicit arithmetic side condition if it is not literally true in the stated
  parameter range.
- For expected finite counts, use
  `pmfExp_card_filter_eq_sum_pmfProb` to turn
  `E[#{a | p ω a}]` into `sum_a Pr[p ω a]`. This is the right first move for
  paper lines like `c_k(n) = sum_g Pr[g has property]`; do not hand-expand the
  double sum in the paper folder.
- For lower bounds on expected finite counts, use
  `pmfExp_card_filter_ge_card_mul_of_forall_mem_prob_ge`: it is enough to
  identify a finite subfamily `s` and prove every event in `s` has probability
  at least `rate`. This is the clean wrapper for source arguments that sum
  over a tail block of indices after proving a uniform per-index probability
  lower bound.
- For finite-PMF variance and Chebyshev steps, use `pmfVariance`,
  `pmfProb_abs_sub_mean_gt_le_variance_div_sq`, and
  `pmfProb_lt_half_expectation_le_four_div_expectation_of_variance_le_expectation`.
  When the actual sampling law satisfies `Var(Y) <= E[Y]`, obtain
  `Pr[Y < E[Y]/2] <= 4/E[Y]`, and finally bound reciprocal-successor
  expectations by splitting on the lower-half event.
- For variance of a sum of indicator events under pairwise negative
  correlation, use
  `pmfVariance_card_filter_le_pmfExp_card_filter_of_pairwise_inter_le_mul`.
  It packages the second-moment expansion
  `pmfExp_card_filter_sq_eq_sum_pmfProb_inter` and the
  `E[S^2] - E[S]^2` variance identity, so paper folders only need to prove
  the event-level inequality
  `Pr[E_i ∧ E_j] <= Pr[E_i] * Pr[E_j]` for distinct indices.
- For paper proofs that establish negative correlation through a conditional
  comparison such as `Pr[F_i | F_j] <= Pr[F_i]`, use
  `pmfConditionalProb_eq_inter_div_of_pos` and
  `pmfProb_inter_le_mul_of_conditionalProb_le` from
  `AppliedModelingLib.Foundations.Probability.Conditional`. For independent
  copies across agents, keep the `n`th-power identities explicit and compose
  them with `pow_le_pow_left₀`. Establish the event-level inequality for the
  actual sampling law first; without-replacement sampling does not automatically
  grant every proposed negative-correlation statement. If that comparison is
  unavailable, look for a direct variance argument, such as Efron–Stein, and
  prove its hypotheses for the actual sampling law.
  Retained conditional `_from_*` lemmas are tools, not proofs that their
  comparison or limiting-law hypotheses hold in the source model.
- For deferred-decision prefix products, avoid reproving the multiplication
  chain in each paper. Use `pmfProb_ge_pow_of_nested_conditionalProb_ge`:
  prove `event 0` is certain, `event (r+1) -> event r`, and a per-step lower
  bound on `Pr[event (r+1) | event r]`. If the source phrases the step as an
  upper bound on the next-hit event, first use
  `one_sub_le_pmfConditionalProb_compl_of_conditionalProb_le`; if the complement
  target is only equivalent under the current prefix, use
  `pmfConditionalProb_congr_of_condition`; if both the conditioning event and
  target need to be replaced, use `pmfConditionalProb_congr`. For a recursive
  fresh-list model, express omission through the realized prefix set and use
  the concrete PMF's prefix-set theorems to supply the filtered
  without-replacement law.
- For weighted without-replacement deferred-decision steps, state the one-step
  law through `finiteWeightedPMFExcluding_apply_toReal_eq_div_one_sub` rather
  than re-normalizing by hand: after excluding the realized prefix set, the
  available mass is `1 - prevMass` and the next atom is `p_w/(1-prevMass)`.
  If the paper conditions only on a coarse prefix event while the source law is
  statewise for realized prefixes, use
  `pmfConditionalProb_le_of_state_refinement` to average upper bounds and
  `pmfConditionalProb_eq_of_state_refinement` when every refined state has the
  same conditional probability. At the paper interface, have the concrete
  process prove prefix positivity and statewise filtered atom equalities, then
  instantiate the product-model theorem instead of restating its tail/rank
  algebra.
- For independent identical finite copies, use `pmfProduct` and
  `pmfProduct_prob_forall` instead of supplying an `n`th-power identity by
  hand. Build the paper-facing product-model endpoint only after the one-copy
  law is available. Product identities can transport a proved one-copy
  dependence inequality, but cannot supply that inequality themselves.
  Use `pmfProb_congr` for pointwise-equivalent event shapes before invoking
  the product theorem.
- For ranked popularity tails, place thin paper wrappers over
  `FiniteRanking.lowerRankFinset_mono` to discharge the rank-cardinality and
  pointwise popularity assumptions. Handle ranked top-prefix mass with
  `FiniteSum.finset_sum_le_sum_of_card_le_pairwise_sdiff`, proving both the
  deterministic top-prefix bound and its realized-prefix specialization.
- For prefix-state algorithms whose concrete sample is a list, prefer a
  prefix-set interface. Prove that omission is nonmembership in the realized
  prefix set, then derive `w ∉ previous` and available-mass positivity from the
  realized-prefix event and `prevMass <= Q`. The concrete recursive sampler
  should supply the statewise filtered-draw equality. Under full support and
  `k < #W`, prove omission and positive-prefix events have positive probability
  before invoking conditional-probability wrappers.
- For concrete finite without-replacement laws, use
  `AppliedModelingLib.Foundations.Probability.WithoutReplacement`. The key constructors
  are `finiteWeightedPMFAvailable`, `finiteFreshList`,
  `finiteWithoutReplacementPMF`, `finiteWithoutReplacementPMF_head_prob`,
  `finiteWithoutReplacementPMF_head_tail_prob`,
  `finiteWithoutReplacementPMF_conditional_tail_event_prob`, and
  `finiteWithoutReplacementPMF_prefixSet_conditional_next_prob_excluding`.
  Use `finiteWithoutReplacementPMF_omit_atom_pos` for positive probability of
  avoiding a fixed atom when full support and enough alternatives are available.
  Use `finiteAvailableWeight_const_mul`,
  `finiteFreshListAtomWeight_const_mul`,
  `finiteWithoutReplacementPMF_event_prob_const_mul`, and
  `finiteWithoutReplacementPMF_conditional_prob_const_mul` when a paper scales
  all finite approximation weights by a positive constant; this preserves event
  and conditional event probabilities.
  For convergence of finite weighted samplers, use
  `finiteFreshListAtomWeight`, `finiteWithoutReplacementPMF_atom_toReal`,
  `finiteWithoutReplacementPMF_event_prob_eq_sum_atomWeight`,
  `finiteAvailableWeight_tendsto`, `finiteFreshListAtomWeight_tendsto`, and
  `finiteWithoutReplacementPMF_event_prob_tendsto`; combine event convergence
  with
  `pmfConditionalProb_tendsto_of_inter_tendsto_of_condition_tendsto` when the
  paper needs conditional event convergence. Full-support availability is
  supplied by `finiteAvailableWeight_pos_of_full_support_of_card_lt`. Expose
  thin paper-facing aliases for the sampler, zero-prefix formula,
  positive-prefix atom law, and conditional omission law rather than duplicating
  their probability proofs.
- For negligible-perturbation expectation arguments where two natural-valued
  counts agree on a good event, use
  `pmfExpReciprocalSucc_le_add_prob_of_eq_on_event`. It reduces the proof to
  bounding `Pr[Ebar]`; the pointwise reciprocal loss on the bad event is at
  most `1`.
- For uniform finite experiments, reuse the generic uniform tools before
  expanding sums: `pmfExp_uniformPMF_equiv` for relabeling across equivalent
  finite spaces, `pmfExp_uniformPMF_prod` for product/nested-expectation
  decompositions, `pmfProb_uniformPMF_finset` for converting finite events
  to `card(event) / card(space)`, `pmfProb_uniformPMF_singleton` for atom mass,
  `pmfProb_uniformPMF_equiv` and
  `pmfProb_uniformPMF_eq_of_comp_equiv` for event-probability exchangeability
  under finite sample-space relabelings, and
  `pmfProb_uniformPMF_fun_range_relabel` when the sample space is a uniformly
  drawn finite function and the relabeling is pointwise on the range. For
  ordered without-replacement samples represented as injective finite
  functions, use `injectiveFunRangeRelabelEquiv` and
  `pmfProb_uniformPMF_injective_fun_range_relabel`,
  `pmfProb_uniformPMF_prod_fst_eq` for one coordinate of a product draw,
  `pmfProb_uniformPMF_prod_fst_event` for any event depending only on the left
  coordinate of a uniform product draw,
  `pmfProb_uniformPMF_prod_eq_pair` for a prescribed pair of independent
  product coordinates, and `pmfProb_uniformPMF_fun_eq_pair_of_ne` for two
  distinct prescribed coordinates of a uniformly drawn finite function. Use
  `pmfProb_uniformPMF_prod_eq_diag` and `pmfProb_uniformPMF_fun_eq_of_ne` for
  diagonal/collision events. In
  random-list proofs, keep these distinct from a broader redundancy event; a
  `1/n^2` claim is usually valid only after reducing to two prescribed
  coordinate values, while a plain two-draw collision is `1/n` and is strictly
  larger than `1/n^2` when `n > 1`. A single "redundant slot" event should
  usually be bounded by a union over earlier-slot collisions, giving a
  `#earlier / n` bound unless the source supplies a sharper prescribed-value
  reduction.
- For balls-into-bins arguments, use
  `AppliedModelingLib.Foundations.Probability.Occupancy`: deterministic used/empty-bin
  sets, `occupancyFirstHitBalls` for ordered first appearances, bin/domain
  relabeling for used and empty bins, the uniform `occupancyPMF`, and
  reciprocal empty-bin expectations.
  Immorlica-Mahdian's Lemma 6.3 is closed generically by a one-ball recurrence:
  adding one uniformly chosen ball multiplies `E[1/(Y+1)]` by at most
  `(#bins+1)/#bins`; iterating from zero balls gives the geometric bound, then
  `Real.add_one_le_exp` converts it to `exp(m/n)/n`. Use this recurrence route
  when the source inclusion-exclusion proof is not essential to a downstream
  named dependency.
- When identifying a paper's occupancy experiment with `Fin m`/`Fin n`, prove
  or pass explicit equivalences and then use
  `occupancyReciprocalExpectation_domain_equiv` and
  `occupancyReciprocalExpectation_bin_equiv`. This keeps paper-local labels
  such as men, proposal slots, and women separate from the generic occupancy
  proof over standard finite types.
- For occupancy comparisons such as "experiment 5 names all women experiment 4
  names, and possibly more", reduce the paper statement to
  `occupancyUsedBins assignment₁ ⊆ occupancyUsedBins assignment₂` and apply
  `occupancyEmptyBins_card_le_of_usedBins_subset`. Then lift that deterministic
  count inequality to reciprocal expectations with
  `pmfExpReciprocalSucc_mono_of_forall_ge`.
  If one experiment is a slot restriction of another, use
  `occupancyUsedBins_comp_subset` to get the used-bin inclusion directly.
- For occupancy equalities such as "Experiments 2 and 3 name the same women",
  reduce to equality of used-bin sets and apply
  `occupancyEmptyBins_card_eq_of_usedBins_eq`.
- For ordered draw-prefix arguments, first identify used bins with first
  appearances with `occupancyFirstHitBalls_image_eq_usedBins` and
  `occupancyFirstHitBalls_card_eq_usedBins`. This is the clean route for
  Immorlica-Mahdian-style claims that a `k+2` prefix with at most `k` distinct
  names is equivalent to having two redundant slots, and it lets you state the
  concrete bad-prefix event as exactly an existential union over indexed
  redundant-pair events before applying the finite union bound.

## Finite Markov Chains and Dynamic Models

- For dynamic EC/platform papers with controlled actions, start with
  `AppliedModelingLib.Foundations.Probability.MDP`: `FiniteMDP`, `FiniteMDP.Policy`,
  `controlledKernel`, `actionValue`, `policyValueStep`, `horizonValue`,
  `optimalStep`, `optimalValue`, and occupancy masses.
- For passive dynamics, use the finite kernel interface in
  `AppliedModelingLib.Foundations.Probability.MarkovChain`: `FiniteMarkovKernel`,
  `transitionProb`, `step`, `iterate`, `expectedNext`, `drift`, `Stationary`,
  `Absorbing`, `ExpectedLe`, and `StochasticallyMonotone`.
- Model policy-induced dynamics with `controlledKernel` when actions matter, or
  as separate kernels over the same finite state type when the paper already
  fixes policies. Compare fixed kernels with `ExpectedLe K L V` for the
  observable or Lyapunov/potential function `V`, then lift to
  `drift_le_of_expectedLe`.
- For queueing, surge, and imbalance papers, define the paper's state type
  first, then a potential such as queue length, imbalance, waiting cost, or
  welfare loss. Prove one-step drift bounds before attempting stationary or
  long-run claims.
- Use `Stationary` only for true steady-state claims. If the paper only needs
  one-step improvement, monotonicity, or a Foster-style drift condition, keep
  the theorem at the `expectedNext`/`drift` layer and record the stationary
  bridge as a separate named assumption or future library seam.
- For monotone dynamics, use `StochasticallyMonotone` when the paper compares
  states under every monotone observable. Use `ExpectedLe` when the comparison
  is only for the paper's specific value function or welfare/potential metric.
- For finite first-order stochastic dominance, use
  `AppliedModelingLib.Foundations.Probability.StochasticDominance`.
  `PMF.FirstOrderLe μ ν` is the expectation order against every monotone
  observable, and `PMF.MonotoneCoupling` is the certificate interface for a
  joint distribution supported on ordered pairs. Use this for admissions,
  recommendation, and platform-policy comparisons before introducing
  paper-specific CDF algebra.
- For Gaussian threshold comparisons in testing papers, first reduce the paper
  claim to monotonicity of posterior means or standardized CDF arguments using
  `GaussianPriorSignal`/`GaussianSignalFamily`; only then add the minimal
  analytic CDF or hazard certificate needed for the remaining one-dimensional
  normal-tail comparison.
- Keep finite Markov kernels in the probability foundations layer. Paper
  folders should contain only the concrete state encoding, transition law,
  policy parameters, and paper-facing wrappers.

## Measure Inequalities and Bonferroni

- For textbook probability inequalities that appear in a paper, upstream a
  generic statement in `MeasureInequalities.lean` and leave paper wrappers thin.
  Finite union bounds, complement/intersection bounds, and Bonferroni
  truncations are reusable enough for `AppliedModelingLib`.
- For finite Bonferroni proofs, prove the pointwise counting identity first:
  the sum over `powersetCard k` of event indicators equals
  `(activeEvents.card.choose k : ℝ)`. Then use alternating binomial-sum lemmas
  and integrate the pointwise inequality.
- When converting indicator functions to set integrals, introduce explicit set
  names and local equalities for unions/intersections. Avoid relying on one
  large `simp` after unfolding all set notation; prove membership/indicator
  equivalences with `if_pos`/`if_neg` or explicit `Set.mem_iUnion` /
  `Set.mem_iInter` bridges.
- For probability/complement lower bounds, prove the de Morgan set equality
  explicitly, then use `probReal_compl_eq_one_sub` and the finite union bound.
- Keep real-valued probability goals consistently in either `measureProb` or
  `μ.real`; when crossing between them, unfold `Measure.real` locally rather
  than rewriting through large expressions.
- For continuous finite-mass side conditions, use
  `measure_ne_top_of_subset_of_ne_top`,
  `measureReal_pos_of_measure_ne_zero_ne_top`,
  `measure_pos_of_measureReal_pos`, and
  `withDensity_measureReal_pos_of_pos_on` from `MeasureInequalities`. These
  are the generic GN-style helpers for proving positive real mass from a
  positive finite `ENNReal` mass and a positive density on a measurable set.
- For random-sampling auction proofs where the bad event depends on a
  sample-selected threshold, avoid stopping at a loose union over candidate
  prices if the paper uses a top-prefix argument. Split the proof into:
  deterministic selected-large bridge (often from `alpha * h <= F` plus
  `singlePriceRevenue <= saleCount * h`), selected-bad subset of a fixed
  top-prefix underrepresentation event, finite prefix union bound, and a
  separate geometric-tail lemma. Keep the top-prefix interface explicit until
  its construction is proved, so the remaining paper assumption is auditable.
- When a paper says "top `i` bids" and the rest of the proof only needs that
  threshold winner sets of size at most `i` lie in the prefix, a fast concrete
  model is a sorted `Fin n → ℝ` bid vector with a monotonicity assumption. Define
  the prefix as indices `< i`, prove its cardinality by an equivalence with
  `Fin i`, and prove threshold closure by contradiction using `i + 1` winners.
- For randomized mechanisms whose expectation has a simple finite formula,
  write the expected-payment/revenue double sum directly before introducing
  probability objects. For weighted-pairing-style auctions, the random draw
  "choose `j` with probability proportional to `v_j` and charge `v_j` if
  accepted" becomes a deterministic sum of terms like
  `v_j^2 / (total - v_i)`, which is faster to bound than modeling the sampling
  kernel first.

## Continuous Probability and RUM

- Do not force a finite analogue when the paper theorem is genuinely continuous
  and a direct density/change-of-variables statement is shorter and more
  faithful.
- If the source theorem is measure-theoretic, probabilistic, CTMC-based, or
  long-run average reward based, formalize that layer directly instead of
  parking it behind finite scaffolding. It is fine to state paper-local
  hypotheses for hard analytic facts such as integrability, measurability,
  renewal-reward limits, or almost-sure convergence, but the theorem wrapper
  should expose the source-level measures, integrals, probabilities, and limits
  rather than a finite substitute.
- For continuous reward formulas, first define the exact paper quantities:
  event mass, set integral of payments, set integral of times, reward ratio,
  and accept-all policy. Then prove algebraic dominance lemmas under explicit
  measurability/integrability and positivity hypotheses. Only after that decide
  whether the renewal theorem or LLN bridge needs a reusable library statement
  or a paper-local assumption.
- For CTMC papers, prove the closed-form transition probabilities, ODE/forward
  equation, and probability bounds in `AppliedModelingLib` when reusable. In the paper
  folder, add source-level bridge statements connecting those probabilities to
  the paper's integrals, cycle probabilities, or time fractions; do not mark the
  stochastic theorem green until the process/renewal bridge is discharged or
  explicitly assumed in the theorem signature and status ledger.
- For renewal-cycle CTMC wrappers, keep opaque algebraic side conditions out of
  the main source model when they follow from primitive assumptions. Carry
  arrival/switch positivity, feasible-policy measurability/subset facts, and
  positive accepted mass, then derive denominator nonzero, cross-probability
  nonzero, state-cycle-time nonzero, and total-cycle-time nonzero locally in
  the theorem proof before invoking quotient/strong-law algebra.
- Split continuous RUM proofs into layers: payoff/certificate algebra over
  rankings, continuous density/change-of-variables inequalities over scores,
  and concrete model instantiation proving support, positive source regions,
  normalization, and score-to-ranking interface facts.
- Upstream only paper-neutral RUM infrastructure. Good `AppliedModelingLib` candidates
  include additive noise well-ordering, Gaussian/Laplacian kernels, scalar
  contraction geometry, pointwise density-product swap inequalities, finite
  density-product atom comparisons, and continuous `withDensity`
  change-of-variables comparisons. The pure order/noise layer lives in
  `AppliedModelingLib.Foundations.Probability.RandomUtility`; finite and continuous
  score-density wrappers live in
  `AppliedModelingLib.Foundations.Probability.RandomUtilityDensity`. Reuse
  `StrictlyWellOrderedNoise`, `WeaklyWellOrderedNoise`,
  `gaussianNoiseKernel_strictlyWellOrdered`,
  `laplacianNoiseKernel_weaklyWellOrdered`, `rumContractScore`,
  `rumContractScore_preserves_weak_order`,
  `rumContractScore_preserves_strict_order`,
  `rum3_contract_top_first_of_original_top_first`,
  `rum3_contract_bottom_first_imp_original_bottom_first`,
  `rum3_swap_middle_transition_geometry`,
  `rum3_swap_middle_source_score_lt`,
  `weaklyWellOrderedNoise_swap12_density3_le`, and
  `strictlyWellOrderedNoise_swap23_density3_lt`; then call
  `rum3ScoreDensityENN`, `rum3_swap12_mass_le_of_density_formula`,
  `rum3_swap23_mass_lt_of_density_formula`,
  `rum3_withDensity_swap12_measure_le_of_density_formula`, and
  `rum3_withDensity_swap23_measure_lt_of_density_formula` before proving
  KR-style local versions. Keep concrete ranking encodings, six hard-coded
  three-candidate rankings, lambda/delta payoff certificates, and
  theorem-number wrappers in the paper folder unless a second paper actually
  needs that same abstraction.
- For continuous distributional inputs that feed a finite theorem over
  rankings, push the measure through the ranking map and convert the finite
  pushforward to a `PMF`. Prove a bridge saying `pmfProb` equals the continuous
  preimage mass.
- For continuous delta inequalities over finite summaries, push the measure
  through the finite summary, apply the finite indicator-difference lemma, and
  pull the result back with a measure-probability bridge.
- For `swapi`/change-of-variables arguments, first prove a reusable
  `withDensity` mass comparison under a measure-preserving measurable
  equivalence and density monotonicity. Then add the paper-local score-geometry
  wrapper proving source regions map into target regions.
- For strict continuous analogues of finite atom witnesses, use a positive
  measure source subset plus a finite source integral. A useful reusable seam is
  a `withDensity` strict comparison lemma with hypotheses like `Measurable D`,
  finite source integral, and positive source measure.
- When a finite certificate seems to require full support of all induced
  rankings, inspect the downstream field actually using it before proving every
  ranking fiber. Often only one strict inequality such as `lambdaOne < 1` is
  needed; for continuous RUMs this can be discharged faster by proving positive
  mass of the exact wrong-choice event and using an identity like
  `wrongProb = 1 - lambdaOne`.
- For concrete continuous support obligations, use explicit open boxes inside
  the target event rather than trying to characterize the whole event. Prove a
  reusable "open box has nonzero volume, and subsets inherit nonzero measure"
  lemma, then instantiate tiny boxes for each lambda source/corrected-top
  region.
- Expose normalized score-law assumptions as the integral equation
  `lintegral D = 1` plus an `IsProbabilityMeasure (mu.withDensity D)` bridge.
  The same equation should discharge finite-source-integral side conditions by
  monotonicity against the full integral.
- Treat ties in real-valued score RUMs explicitly. Either work on no-tie/full
  measure subtypes, prove almost-everywhere ranking-interface lemmas, or state a
  tie-breaking convention and prove score/ranking facts for it.
- After an abstract `withDensity` theorem compiles, add concrete score-space
  utilities for the intended product shape: coordinate projections, measurable
  coordinate swaps, measure-preserving swap lemmas, normalization bridges, and
  finite-source-integral bridges. Align product nesting with Mathlib's product
  measure conventions, for example `(ℝ × ℝ) × ℝ`, so later instantiations do
  not waste time on associativity rewrites.
- When a paper-facing probability theorem is stuck with a premise like
  "source metric field equals the displayed probability formula," close it with
  a canonical source surface when possible. Define the surface so the metric
  field unfolds to the tail probability, expectation, or integral appearing in
  the paper, prove a thin source-surface endpoint, and make the DAG/README point
  to that endpoint rather than to the older abstract formula-premise theorem.
- For source-affine Gaussian formulas, keep three layers separate: the
  standardized integral identity, the raw source-density scaling, and the
  paper's named source substitutions. After proving the normalized theorem,
  add thin wrappers for raw-normal density arguments and for displayed source
  definitions such as `a'_g(q)` and `b'_g`; this avoids repeatedly expanding
  square-root denominators and prevents standardized-density facts from being
  mistaken for source-density facts.
- When an arXiv TeX source gives a different-looking Gaussian formula than the
  PDF text extraction, treat the TeX line as authoritative for the wrapper and
  record the mismatch in the paper plan/report. Do not repair the formula from
  intuition unless the Lean proof is explicitly proving a corrected theorem and
  the validation report says so.
- For Gaussian admission formulas, audit whether a displayed CDF argument is
  written as `(mu - q) / sigma * sqrt(ratio)` or should be
  `(mu - q) / (sigma * sqrt(ratio))` from the law's scale. If surrounding
  conditional-density algebra implies the reciprocal standardization, preserve
  a literal-source definition for audit and introduce a corrected source-algebra
  definition with comments pointing to the conditioning line. For source-affine
  cutoff terms, derive the numerator and denominator from the conditional
  probability before trusting the display; missing precision factors should
  become explicit corrected wrappers, not hidden assumptions.

## Lean Patterns

- Prefer `pmfExp`/`pmfProb` abstractions over hand-expanding `PMF` internals.
- For uniform PMFs over finite spaces, use relabeling lemmas such as
  `pmfExp_uniformPMF_comp_equiv`, `pmfExp_uniformPMF_eq_of_comp_equiv`,
  `pmfProb_uniformPMF_equiv`, `pmfProb_uniformPMF_eq_of_comp_equiv`, or
  `pmfProb_uniformPMF_fun_range_relabel`. For injective-function subtypes, use
  `pmfProb_uniformPMF_injective_fun_range_relabel`.
- Open `ENNReal` scope in files that state `ℝ≥0∞` or `∫⁻` expressions.
- When event hypotheses contain abbreviations, normalize each component with
  local equalities before rewriting larger probability goals.
