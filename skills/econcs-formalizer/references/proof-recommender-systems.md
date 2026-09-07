# Applications: Recommender Systems

Use for `AppliedModelingLib/Applications/RecommenderSystems/*`, accuracy/diversity,
producer fairness, discretization bias, classwise policies, and count
allocation.

## Accuracy, Diversity, and Count Allocation

- Split recommendation diversity/homogeneity proofs into three layers: finite
  exchange or first-order conditions forcing pairwise count balance; a generic
  representation lemma converting count error to share/homogeneity error; and
  the asymptotic or order-statistic layer.
- For symmetric i.i.d. Bernoulli items, the finite balance proof should cancel
  the common positive likelihood-success coefficient and use strict
  antitonicity of `(1 - q)^k` under `0 < q < 1`.
- For uniform `[0,1]`, `k = 1` recommendation values, use the closed form
  `1 - 1 / (q + 1)` for the expected maximum of `q` samples. Its forward
  marginal is `1 / ((q + 1) * (q + 2))`; the positive-count backward marginal is
  `1 / (q * (q + 1))`.
- For square-root homogeneity, separate exact marginal algebra, a target-profile
  representation bridge, and the real-relaxation/integer-rounding theorem.
- For separable objectives, discharge exchange certificates by showing
  likelihoods are a positive scale times squared shifted targets and anchors
  bracket those targets.
- For decaying Bernoulli all-consumed objectives, keep the generic ranked
  Bernoulli value/marginal layer separate from the paper-specific decay
  sequence. For every positive `α`, the FOC can be stronger than the paper's
  scalar sum-asymptotic route: cancel the positive scale, convert inverse-power
  marginal comparisons into bounded scaled counts `a_t / p_t^(1/α)`, then use a
  generic pairwise-scaled count bridge for exact `C/N` homogeneity. Treat
  `α = 0` and `c = 0` explicitly; the paper-style `1/α` target and objective
  can degenerate there.
- For asymptotic recommendation homogeneity, an `O(1)` pairwise scaled-count
  bound is stronger than necessary. If finite FOCs plus tail/product
  asymptotics give `|a_i/w_i - a_j/w_j| ≤ ε_N N` with `ε_N → 0`, use a
  sublinear pairwise-scaled bridge to get the γ-profile limit.
- For the finite weighted averaging step, call
  `AppliedModelingLib.Allocation.count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded`.
  PRPKG's
  `GammaHomogeneityProfile.count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded`
  is only a paper-facing wrapper. This lemma converts pairwise bounded scaled
  counts `|count_i / w_i - count_j / w_j| ≤ C` into
  `|count_t - w_t * (N / sum w)| ≤ C * w_t`.
- For finite count-pigeonhole steps, call
  `AppliedModelingLib.Allocation.exists_count_gt_of_card_mul_lt_total`: if total count
  exceeds `Fintype.card κ * K`, some coordinate count exceeds `K`. PRPKG's
  `exists_count_gt_of_card_mul_lt_total` wrappers only rewrite
  `Fintype.card (Fin T)` to `T`.
- For uniform count-balance steps, use
  `AppliedModelingLib.Allocation.count_abs_sub_uniform_average_le_C_of_pairwise_bounded`
  or
  `AppliedModelingLib.Allocation.count_abs_sub_uniform_average_le_one_of_pairwise_balanced`.
  PRPKG's uniform-profile wrappers should only translate the average from
  `Fintype.card (Fin T)` to `T`.
- For fixed-total finite count-objective existence, use
  `AppliedModelingLib.Allocation.exists_isOptimalAtTotal`. It packages the finite code
  `Allocation.FeasibleCode`, decodes fixed-total allocations, and returns an
  objective maximizer for any finite nonempty coordinate type. PRPKG's
  `ConsumptionModel.exists_isOptimalAtTotal` is a wrapper.
- For one-unit exchange and FOC arguments over weighted separable count
  objectives, use the shared allocation layer first:
  `AppliedModelingLib.Allocation.objective_moveOne_eq` for exact marginal accounting,
  `AppliedModelingLib.Allocation.objective_le_objective_moveOne_of_exchangeCondition`
  for weak improvement, and
  `AppliedModelingLib.Allocation.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum`
  for the optimum FOC. Diminishing-returns comparisons should call
  `AppliedModelingLib.Allocation.marginal_antitone_of_diminishing`,
  `AppliedModelingLib.Allocation.weightedForwardMarginal_antitone_of_diminishing`,
  `AppliedModelingLib.Allocation.weightedBackwardMarginal_eq_weightedForwardMarginal_pred`,
  or
  `AppliedModelingLib.Allocation.weightedBackwardMarginal_le_weightedForwardMarginal_of_diminishing`.
  PRPKG's `ConsumptionModel.*` exchange theorems are paper-facing wrappers
  around these generic declarations.
- When the product/tail estimate is naturally one-sided, use the FOC-to-
  sublinear bridge: prove that any scaled-count gap larger than `ε_N N` makes
  the source backward marginal strictly smaller than the destination forward
  marginal. The finite FOC rules out the gap, and the sublinear scaled-count
  bridge gives the sequence limit.
  The allocation-level theorem for the first step is
  `AppliedModelingLib.Allocation.pairwise_scaled_abs_le_of_large_gap_backward_lt_forward`;
  it converts a large-gap marginal-dominance hypothesis plus fixed-total
  optimality into pairwise scaled-count bounds. Use
  `AppliedModelingLib.Allocation.share_abs_sub_weighted_target_le_error_total_weight_of_pairwise_scaled`
  when the next step is directly a target-share error bound.
  If an asymptotic certificate needs deliberately large errors for finitely
  many small `N`, use `AppliedModelingLib.Math.tendsToZero_if_lt_const`.
  For finite prefixes with positive target weights and `N < threshold`, use
  `AppliedModelingLib.Allocation.pairwise_scaled_abs_le_of_total_lt`.
- For sequence-level target-profile conclusions, use
  `AppliedModelingLib.Allocation.AsymptoticProfileTarget`,
  `AppliedModelingLib.Allocation.AsymptoticProfile`, and
  `AppliedModelingLib.Allocation.OptimalSequence.convergesToProfile_of_asymptoticProfile`
  rather than defining a new paper-local sequence interface. When the finite
  proof gives pairwise scaled-count gaps `≤ ε_N N`, call
  `AppliedModelingLib.Allocation.asymptoticProfile_of_pairwise_scaled_sublinear`; when
  it gives the FOC-style large-gap marginal dominance hypothesis directly,
  call `AppliedModelingLib.Allocation.asymptoticProfile_of_large_gap_backward_lt_forward`.
  When the marginal dominance estimate is only eventual and requires all
  compared counts above a fixed floor, call
  `AppliedModelingLib.Allocation.asymptoticProfile_of_eventual_large_gap_backward_lt_forward`;
  it absorbs finite prefixes with a large temporary error schedule.
- Prefer the certificate-shaped allocation API when paper statements already
  package hypotheses as records:
  `AppliedModelingLib.Allocation.PairwiseScaledSublinearProfileCertificate`,
  `AppliedModelingLib.Allocation.PairwiseScaledSublinearFOCCertificate`, and
  `AppliedModelingLib.Allocation.PairwiseScaledEventualSublinearFOCCertificate`.
  The FOC certificate has
  `.toPairwiseScaledSublinearProfileCertificate`; the eventual certificate has
  `.toPairwiseScaledSublinearFOCCertificate`; all three expose
  `.asymptoticProfile`. In PRPKG, preserve source-facing certificate names but
  add a `.toShared` adapter and delegate conversions/endpoints through these
  shared records rather than copying the finite-prefix proof.
- For PRPKG continuous order-statistic branches, let the probability layer
  produce `TopKScaledMarginalLimitCertificate` or a source-loss asymptotic
  certificate, then feed that into the existing floor-aware eventual FOC bridge.
  The compiled source bridge now starts from
  `AppliedModelingLib.Probability.sampleTopKSum` /
  `sampleTopKEndpointLoss_eq_reflectedBottomKSum`, passes through
  `orderStatisticTopKSumFromSample_eq_sampleTopKSum`, and reaches
  `paper_lemma1_bounded_support_order_statistic_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support`.
  The measure-level bridge is `expectedOrderStatisticMeanSeq`; use its top-`k`
  and endpoint-loss theorems before introducing paper-local FOC wrappers.
  When a bounded finite sample law has coordinatewise a.e. bounds, use
  `paper_definition3_expected_order_statistic_mean_seq_topk_sum_eq_expected_sample_topk_sum_of_ae_bounds`
  and
  `paper_definition3_expected_order_statistic_mean_seq_topk_endpoint_loss_eq_expected_reflected_bottom_sum_of_ae_bounds`
  to avoid reproving sorted-tuple measurability/integrability at the paper
  level. For fixed finite-rank asymptotic assembly, use the library lemmas
  `AppliedModelingLib.Math.finite_sum_asymptoticEquivalent_common_scale` and
  `AppliedModelingLib.Math.asymptoticEquivalent_add_negligible_common_scale`; PRPKG's
  paper-local names should remain wrappers around these. For the finite
  deterministic layer-cake step, use
  `paper_definition3_reflected_bottom_sum_eq_integral_rank_count_indicator`;
  the measure-level count-layer bridge is
  `expectedReflectedBottomKSum_eq_integral_rank_count_layer_of_integrable`,
  and bounded coordinate support discharges the required product/Fubini
  integrability through
  `reflectedBottomKRankCountLayer_integrable_prod_of_ae_bounds`.
  The fixed-threshold iid product/binomial-count evaluation is already exposed
  as `paper_definition3_iid_reflected_count_layer_inner_integral_binomial`,
  with the bounded Lemma D.2 kernel form
  `paper_definition3_iid_reflected_count_layer_inner_integral_kernel`; the
  outer positive-threshold assembly is
  `paper_definition3_iid_reflected_count_layer_integral_kernel_of_integrable_of_le`.
  Bounded support for `G` gives the finite kernel-integrability bundle through
  `paper_lemmaD2_bounded_integral_kernel_eventually_fin_integrableOn_of_bounded_support`,
  so the first iid bounded Lemma 1 endpoint is
  `paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support`;
  it defines `G` as `x ↦ P[M - X <= x]`, so no separate reflected-CDF identity
  is needed.
  The stronger endpoint
  `paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail`
  uses `reflectedCDFMass` and derives reflected-CDF measurability,
  monotonicity, range, and upper-support saturation from one-dimensional
  a.e. bounds. Prefer it when the only law-specific analytic input left is
  `BoundedTailCDFPowerSandwich (reflectedCDFMass baseMeasure M) beta c`.
  If the concrete law proves an exact local identity
  `reflectedCDFMass baseMeasure M x = (c / beta) * x ^ beta` eventually as
  `x -> 0+`, use
  `paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power`;
  the helper `BoundedTailCDFPowerSandwich.of_eventually_eq_const_mul_power`
  builds the tail sandwich. For uniform-style reflected CDF `G(x)=x`, the
  ready certificate is `BoundedTailCDFPowerSandwich.identity_beta_one`.
  The continuous uniform `[0,1]` law is already packaged as `uniform01Measure`,
  with `uniform01_reflectedCDFMass_eventually_eq_power` and the Lemma 1
  endpoint
  `paper_lemma1_uniform01_iid_reflected_cdf_count_layer_top_k_loss_asymptotic`.
  To convert bounded-source loss asymptotics into first-difference/marginal
  asymptotics, do not subtract asymptotic equivalents. Use
  `bounded_source_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop` or
  the source-level wrappers
  `paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail_and_scaled_drop`
  and
  `paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power_and_scaled_drop`.
  These require the explicit scaled-drop limit
  `(q+1)*((A-h(q))-(A-h(q+1)))/(A-h(q)) -> 1/beta`. The finite scale ratio is
  eventually `((q+1)/q)^(1/beta)`, proved by
  `boundedTailScale_div_succ_ratio_eventually_eq_rpow`, and only then tends to
  one. The bounded source marginal certificate is
  `BoundedOrderStatisticScaledMarginalCertificate`; use
  `BoundedOrderStatisticScaledMarginalCertificate.ofLossAsymptoticAndScaledDrop`
  and `.toTopKScaledMarginalLimitCertificate`, or the paper-facing
  `paper_theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_loss_ae_and_scaled_drop`,
  to feed the reusable optimization layer.
  For the exact uniform `[0,1]` order-statistic closed form, use the direct
  bounded `β = 1` certificate
  `paper_theorem1_ii_uniform_order_statistic_scaled_marginal_certificate`
  instead of rebuilding the generic loss-to-drop route. The matching
  source-oracle sequence wrappers are
  `paper_theorem1_ii_uniform_order_statistic_sequence_homogeneity_of_paper_bound`
  and `paper_theorem1_ii_uniform_order_statistic_sequence_formula_of_paper_bound`.
  Use `iidProductMeasure_forall_bounds_ae` when a paper-local wrapper still
  has product-sample support in its hypotheses. The remaining law-specific
  bounded work is one-dimensional support, positive support width, and the
  Lemma D.2 near-zero tail sandwich for that reflected CDF.
  For bounded-support Lemma 1, prefer the aggregate endpoint
  `paper_lemma1_bounded_support_expected_reflected_bottom_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support`
  when the distribution proof naturally identifies `expectedReflectedBottomKSum`
  as a single reflected-CDF integral double sum.
  Use
  `paper_definition3_expected_reflected_bottom_sum_eq_sum_reflected_order_statistic_integrals_of_le`
  after the eventual `k ≤ a` prefix to turn that aggregate into a fixed
  `Fin k` sum of reflected lower order-statistic integrals.
  For Pareto Lemma D.4, an `AsymptoticEquivalent` marginal proof can feed
  `paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_asymptotic_equivalent`
  directly; do not manually rebuild the source certificate unless the proof is
  already in `marginal_ratio_tendsto` form. If the calculation is naturally
  per fixed rank, use
  `paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_finite_rank_scaled_limits`;
  it reduces the source obligation to scaled limits for each `i : Fin k` plus
  the finite coefficient sum. If using the paper's gamma-ratio constants, use
  `paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_pareto_rank_scaled_limits`
  with `paretoRankMarginalCoeff`; the positivity and coefficient sum are
  supplied by the Pareto module. If the rank proof is naturally staged as a
  value asymptotic plus scaled drop, first apply
  `paper_lemmaD4_pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop`.
  If it uses the cited exact gamma-ratio sequence, apply
  `paper_lemmaD4_pareto_rank_gamma_ratio_mean_scaled_limit` directly and spend
  effort only on proving that the concrete Pareto order-statistic mean equals
  that sequence. The gamma-ratio sequence layer is now closed through
  `AppliedModelingLib.Foundations.Math.GammaAsymptotics` plus PRPKG wrappers:
  `paretoRankGammaRatioMean_value_asymptoticEquivalent`,
  `paretoRankGammaRatioMean_succ_div_self`,
  `paretoRankGammaRatioMean_scaled_drop`, and
  `paretoRankGammaRatioMean_scaled_limit`; do not reopen that algebra unless
  the actual Pareto law uses a different sequence. The PDF's equation (135)
  appears to print a denominator inconsistent with equations (77), (131), and
  Lemma D.4; keep the literal source discrepancy in the paper handoff and use
  the derivation-consistent `a^(1/α)` scaling for compiled wrappers.
  Do not add another paper-local optimizer interface unless the new probability
  certificate cannot express the source marginal comparison.
- For decaying Bernoulli top-one objectives, check `α = 0` before doing product
  asymptotics: rank success probabilities become constant, so the model should
  reduce to the existing i.i.d. Bernoulli satisfaction model and reuse its
  uniform-homogeneity theorem.
- For positive-`α` decaying Bernoulli top-one objectives, first prove count
  divergence of finite optima. The decay probability tends to zero, so a large
  source count has last-item marginal below any fixed destination-count
  marginal; a finite pairwise/fixed-floor threshold plus the FOC rules out
  destinations at or below that floor for large totals.
- After count divergence, separate the raw product estimate from finite
  optimization. Use a floor-aware eventual product certificate: prove that
  beyond a fixed count floor and eventually in `N`, any scaled-count gap larger
  than `ε_N N` makes the top-one source backward marginal strictly smaller
  than the destination forward marginal, assuming the source and destination
  counts are bounded by the finite total `N`. Then use a finite-protected error
  schedule for the finitely many small totals, the count-divergence theorem to
  supply the floor, count-total bounds from feasibility, and the
  FOC-to-sublinear bridge to obtain the paper's sequence-limit theorem.
- For the `0 < α < 1` top-one product estimate, factor the survival-product
  ratio over the interval between destination and source counts. Bound
  `∏(1-q_i)` by `exp(-∑ q_i)`, lower-bound the interval sum by gap length
  times the right-end success probability, and use a log-likelihood-ratio
  inequality to turn the scalar exponential bound into marginal dominance.
  Use the concrete schedule `ε_N = (N+1)^((α-1)/2)`: it tends to zero, while
  `(ε_N N - 1) q_N → ∞` for `0 < α < 1`, so it eventually dominates all finite
  log-likelihood ratios and closes the subunit branch under the explicit
  probability-validity assumptions.
- For the `α = 1` top-one product estimate, do not rely on the paper's displayed
  finite telescope unless `c` has actually been specialized to an integer. For
  real `c`, prove the finite harmonic-log route instead: show
  `log((x+1)/x) ≤ 1/x`, telescope the interval log sum, derive the
  survival-product ratio bound `P_r/P_q ≤ ((q+1+d)/(r+1+d))^c`, and then combine
  it with the source/destination success ratio and weights `p_t^(1/(1+c))`.
  The large scaled-gap-to-shifted-scalar bridge closes the raw-ordered case
  once the error schedule dominates the fixed shift
  `(1+d) * ∑_t 1 / p_t^(1/(1+c))`. Nonuniform target weights can still make a
  large scaled-count gap occur with the opposite raw order; use the reverse
  product layer there. The reverse layer bounds the inverse interval product by
  the same endpoint ratio times an explicit log-correction sum from
  `-log(1-c/x) - c log((x+1)/x)`, and an exponential scalar bridge turns the
  corrected shifted-count inequality into marginal dominance. Bound each
  correction term by `c * (1 + 2 * c) / x^2`, sum over an interval by its length
  times the left-endpoint inverse-square term, and feed the resulting
  nonnegative correction through the shift
  `1 + d + B * (exp(E / (1 + c)) - 1)`. The PRPKG alpha-one seam separates
  raw-order shift growth from reverse-order corrected-shift growth, and the
  concrete quarter-error certificate closes the branch: use
  `ε_N = (N+1)^(-1/4)` so both `ε_N N → ∞` and `ε_N^3 N → ∞`; the cube growth
  dominates the correction-sum bound after scaling by the finite target-weight
  sum.
- For the `α > 1` top-one product estimate, use target weights
  `w_t = p_t^(1/α)` and keep the proof in the same raw/reverse split as the
  `α = 1` branch. The raw-order bridge only needs the shifted-count term to be
  dominated by `ε_N N`. In the reverse-order bridge, bound the interval success
  sum by its left endpoint:
  `2 * ∑_{i=qsrc-1}^{qdst-1} q_i ≤
  (2*c*∑_t w_t^(-α)) * N * (ε_N N)^(-α)`, feed this through
  `exp(E/α)-1 ≤ exp(1)*(E/α)` once the scaled argument is below one, and bound
  the correction by a constant times `N^2 * (ε_N N)^(-α)`. The concrete
  schedule `ε_N = (N+1)^(-(α-1)/(2*(α+1)))` closes the branch because
  `ε_N → 0`, `ε_N N → ∞`, `N*(ε_N N)^(-α) → 0`, and
  `N^2*(ε_N N)^(-(α+1)) → 0`. These two limit lemmas are generic continuous
  asymptotic tools and should be reused for similar superunit inverse-power
  correction arguments before inventing a new schedule.
- Generic ranked-Bernoulli value and marginal lemmas are reusable across
  recommender papers, but keep them local while only one paper uses them or
  while the exact import topology is still changing. Move them into the shared
  recommender/probability library once a second paper needs them or the proof
  shape has stabilized.
- For finite fixed-total count-allocation optimization, encode allocations as
  functions into `Fin (N + 1)` plus a total-sum proof, optimize over that finite
  code space, then decode to the paper allocation type.
- For all-consumed linear recommendation objectives, prove both directions when
  the paper says recommendations contain only the argmax type: first show an
  all-on-argmax allocation is optimal by comparing per-item scores, then use
  the one-step FOC to show any type with strictly lower per-item score must have
  zero count in every optimum. The second direction needs strict score
  inequality and positive common mean; weak argmax assumptions only prove an
  optimal witness, not uniqueness of support.

## Policy and Fairness Layers

- For finite fair-division allocation theorems in recommender settings, first
  prove the theorem for an abstract marginal bound. Then add a paper-facing
  corollary instantiating the bound as the finite maximum one-good marginal
  value.
- For symmetry/type-reduction arguments, prove weighted sums by type-cardinality
  equal sums over original agents, and finite minima over agents equal finite
  minima over types when representatives witness every fiber.
- For baseline constrained problems at `gamma = 0`, reduce the constraint to
  nonnegativity when objectives are normalized nonnegative utilities. Witness
  nonemptiness with an arbitrary default policy.
- For finite symmetric recommendation LPs, avoid proving a generic "selected
  BFS" theorem if the paper result can be closed by a canonical closed-form
  construction. Prove the canonical first-crossing or first-closed pivot exists,
  prove its denominator/nonnegativity bounds, and use that pivot to build the
  closed policy/certificate. Keep selected-BFS statements as auxiliary
  explicit-input variants unless the source theorem genuinely needs arbitrary
  selected optima.
- When the recommendation model has mirror symmetry, prove the first half
  directly and derive the second half by a mirror-equivalence theorem preserving
  the objective, constraints, and optimal values.
- If a displayed paper formula depends on an implicit modeling convention, such
  as a center item counted once in a half-LP but twice in a full mirrored
  policy, split the theorem names by convention and prove an explicit bridge or
  explanation. Do not hide convention differences inside the executable model.
- For user-item fairness paper examples, do not leave source examples as bare
  definitions if they appear in the DAG. Formalize the small checked claims
  that make the example auditable, or mark the example honestly as not
  formalized. For finite two-item smoke examples over `Real`, avoid
  `native_decide`; use `finiteMin_eq_of_forall`, `Finset.sup'_le`,
  `AppliedModelingLib.le_finiteMax`, `AppliedModelingLib.Policy.agentScore_pure`, and, for raw
  item probabilities under deterministic policies, unfold `AppliedModelingLib.Policy.pure`
  and simplify with `PMF.pure_apply`.
- In opposing-type LP/pivot proofs, large contexts can make a final solver call
  more expensive than the math. Before using `linarith` at the end of a long
  branch, name the scalar bounds you need (for example `ell ≤ q`, `q' ≤ ell'`,
  then `q' ≤ q`) and close by contradiction against the strict monotonicity
  fact. This is usually faster and gives better failure locations.
- If a canonical closed-form/certificate construction now discharges a previous
  selected-BFS or denominator assumption, immediately update README/DAG wording
  from `conditional` or `formalized with caveat` to `formalized`. Keep auxiliary
  explicit-input selected-BFS lemmas, but do not let their older status text
  make the final source wrapper look conditional.

## Discretization Bias

- Prove the actual paper-level continuous/probability theorem when requested;
  do not silently replace it with a finite adaptation. Use finite wrappers only
  as intermediate algebra when they are explicitly connected back to the paper
  statement.
- Keep finite expected-objective bridges generic: deterministic objective,
  expected objective, monotone/linear expectation interface, then paper-facing
  theorem.
- If row-wise Bayes or conditional distribution identities are still assumed,
  name those assumptions in the theorem and README exactly; do not mark the
  source theorem fully formalized until they are instantiated from the model.
