# Foundations: Optimization

Use for `AppliedModelingLib/Foundations/Optimization/*`, argmax existence, objective
comparison wrappers, finite rule optimization, and paper-facing optimality
statements.

Start with `docs/OPTIMIZATION_LIBRARY_ROADMAP.md` when deciding whether an
optimization proof seam should stay paper-local or move to `AppliedModelingLib`.

## Proof Seams

- Before adding a paper-local equilibrium, optimizer, threshold, cutoff,
  certificate, or a.e. exception wrapper, write the shared-library reuse
  checkpoint in the paper plan. The checkpoint should name the relevant
  `AppliedModelingLib` modules/declarations inspected and the shared API being used, or
  state the source-specific obstruction. If the code starts accumulating local
  wrappers for a standard concept, stop and refresh this checkpoint before
  adding another wrapper.
- For "candidate plus universal bound" proofs, use
  `AppliedModelingLib.Optimization.UpperBoundCertificate` for maximization and
  `AppliedModelingLib.Optimization.LowerBoundCertificate` for minimization. These are
  the preferred wrappers for paper LP certificates, exchange upper bounds,
  endpoint/current-bound certificates, and finite lower-bound arguments.
- Use `StrictUpperBoundCertificate` / `StrictLowerBoundCertificate` when the
  paper also proves uniqueness or a strict structure theorem away from the
  candidate. Keep equality-case algebra paper-local until a second paper needs
  the same condition.
- For finite deterministic-rule optimization statements, first prove a generic
  maximizer-existence theorem over the finite function type
  `(instances -> actions)`. Keep paper folders responsible for defining the
  paper-specific objective and applying the generic result.
- For finite feasible regions that are awkward to optimize over directly, use
  `exists_isMaximizerOn_of_finite_code` or
  `exists_isMinimizerOn_of_finite_code`: define a finite code type, prove every
  feasible code decodes to a feasible object, and prove every source-feasible
  object is covered by some feasible code.
- For expected objective wrappers, separate the deterministic objective from
  the expectation operator. Prove a monotone/linear expectation interface once,
  then instantiate paper theorems by rewriting the expected paper objective to
  the generic expected objective.
- For stochastic-gradient, stochastic-subgradient, or SSGM convergence seams,
  do not assume the final paper endpoints directly. Encode the algorithm,
  source distributions, norms, objectives, and finite-dimensional hypotheses as
  concrete source-model records; define theorem-shaped convergence records for
  the reusable analytic theorem; and, if needed, use a single paper-local axiom
  for that convergence record. Then prove the paper endpoints from the source
  model plus that axiom so the recursive audit exposes exactly the external
  theorem boundary.
- For paper statements that say an optimizer exists, avoid hiding the optimizer
  in an opaque certificate. Prove the argmax/existence theorem in the generic
  library and make the paper theorem a thin wrapper with exact assumptions.
- For static action-rule papers, use
  `AppliedModelingLib.Foundations.Optimization.ChoiceEquilibrium` before creating a
  paper-local equilibrium record. Package chosen action, feasibility,
  best-response, and consistency once, then project with
  `isChoiceEquilibrium_feasible`, `isChoiceEquilibrium_best_response`, and
  `isChoiceEquilibrium_consistency`. If a later source lemma only needs a
  named binary deviation, use
  `noProfitableBinaryChoiceDeviation_of_choiceEquilibrium_payoff_projection`
  or `noProfitableUnchosenDeviation_of_choiceEquilibrium_payoff_projection`
  rather than restating the full equilibrium.
- For continuous type spaces, cutoff ties, or "except on a null set"
  equilibrium prose, check `ChoiceEquilibriumAE` before writing any
  paper-local a.e. equilibrium wrapper. Its constructors and projections
  (`isChoiceEquilibriumAE_of_pointwise`,
  `isChoiceEquilibriumAE_of_forall_not_mem_null`,
  `isChoiceEquilibriumAE_best_response_ae`, and
  `isChoiceEquilibriumAE_consistency`) should be the default route for
  continuous admissions/testing/strategic-ranking equilibria. Put the null
  cutoff/tie set and model-specific payoff rewrite in the paper; keep the
  a.e. equilibrium shell in the library.
- If a continuous equilibrium proof starts accumulating paper-local wrappers
  for ranks, endogenous cutoffs, tie-breaking, or effort-allocation best
  responses, pause before adding the next wrapper and search both
  `AppliedModelingLib.Foundations.Optimization` and the relevant probability/ranking
  modules for an existing bridge. A missed shared API is a workflow bug: update
  the outside-of-Lean plan with the declarations inspected and either use the
  shared theorem or record the source-specific obstruction.
- For two-action best-response/cutoff proofs, use
  `AppliedModelingLib.Foundations.Optimization.BinaryChoice`:
  `NoProfitableBinaryChoiceDeviation`,
  `not_all_choose_of_noProfitableBinaryChoiceDeviation_exists_other_better`,
  `not_no_choose_of_noProfitableBinaryChoiceDeviation_exists_choose_better`,
  `exists_chosen_and_unchosen_of_noProfitableBinaryChoiceDeviation_crosses`,
  and `choice_rule_iff_threshold_of_noProfitableBinaryChoiceDeviation_tiebreak`.
  This is the reusable path for "some chosen value prefers the other action"
  and "some unchosen value prefers the chosen action" contradictions before
  deriving threshold structure.
- For LP sparsity or BFS-style results, separate the linear-programming theorem
  from finite counting consequences. Encode the active-support bound first,
  then prove reusable counting lemmas over finite supports.
- For finite LP-heavy papers where a full solver would be overkill, define the
  exact paper-local equality-form or epigraph LP; prove weak duality for the
  exact variables; construct the closed-form primal witness; construct the
  matching dual/certificate; prove feasibility, tightness/complementary
  slackness, and uniqueness; then finish with an `UpperBoundCertificate` or
  `LowerBoundCertificate` and wrap this as the paper theorem. This can fully
  verify a source result without a generic LP solver when the final wrapper
  constructs or discharges every certificate internally. Generalize the LP
  record only after a second paper needs the same constraint shape.
- For standard finite maximization LPs with `x >= 0` and `Ax <= b`, use
  `StandardMaxLP.weak_duality` and `StandardMaxLPCertificate.isMaximizerOn`.
  This is the right first abstraction for GCG-style closed primal/dual
  certificates. Full basic-feasible-solution/rank support is heavier; add it
  only when a source theorem needs the BFS support-size statement itself.
- For online-auction or primal-dual competitive-ratio proofs, separate the
  generic sandwich from the paper accounting. Use
  `UpperBoundApproximationCertificate` when `benchmark <= dual` and
  `ratio * dual <= achieved`; use
  `UpperBoundApproximationWithErrorCertificate` for small-bids or finite-error
  variants.
- For auction lower bounds by hard input distributions, prefer the generic Yao
  certificate `AppliedModelingLib.Decision.RandomizedUpperPayoffCertificate`; keep
  source-specific permutation, layer-count, or benchmark-normalization fields
  in the paper folder.
- For normalized objective values, prove boundedness before compactness or
  supremum reasoning. Finite PMF expectations are often bounded by row maxima,
  giving immediate `BddAbove` side conditions.
- For optimization reductions, prove lift/descend functional preservation,
  symmetrization dominance, and then `sSup` equality from explicit nonempty and
  bounded-above feasible-value conditions.
- For exchange proofs over integer allocations, state the local move relation
  explicitly. Prove "global optimum has no improving move" immediately from
  `IsMaximizerOn`, and only prove the harder converse after establishing the
  feasible move graph is connected by those moves. Once reachability is
  available, finish with `isMaximizerOn_of_reachable_nonincreasing` or
  `isMinimizerOn_of_reachable_nondecreasing`.
- For continuous-paper proofs that say "approximate by a finite object, apply
  local endpoint/exchange moves until a canonical object remains, then pass to
  a limit", split the seam into three reusable facts instead of repeatedly
  unfolding the source prose: a finite descent theorem over a natural-valued
  complexity, an arbitrary-close finite-seed bridge, and a compact/canonical
  maximizer bridge showing the original target value is attained or exceeded.
  Keep the paper-specific work in the one-step move certificate; this avoids
  token-heavy rewrites of the same termination and epsilon/maximizer argument.
- For one-dimensional cutoff or interval-endpoint moves, start from
  `AppliedModelingLib.Foundations.Optimization.Endpoint`.  It contains derivative-sign
  to endpoint-monotonicity lemmas, first/last-zero stopping dichotomies, and
  one-sided local improvement/decrease lemmas.  Keep paper-local wrappers when
  the source names the endpoint claim, but do not duplicate the generic
  calculus proof in the paper folder.
- For optimization claims proved in the source by a first-order condition,
  never let `derivative = 0` stand in for a global maximum.  First write the
  objective as a function of the paper's choice variable, compute the
  derivative condition, and identify the global shape condition that turns a
  stationary point into an optimum.  For one-dimensional weighted tradeoffs
  `W_beta = beta*M + (1-beta)*U`, a natural repair is monotonicity of the
  marginal tradeoff `-U'/M'`, equivalently a supporting-hyperplane/frontier
  condition; componentwise concavity is often too strong or simply the wrong
  condition.  Test any proposed primitive repair on the simplest source-shaped
  primitives allowed by the paper before treating it as derivable.  If the
  paper's primitives do not imply the shape condition, expose it as a visible
  source assumption or mark the result partial; do not hide it in a certificate
  or endpoint wrapper.
- When the approximation seeds are bounded but the canonical objects may be
  unbounded, do not use the bounded seed type as the descent domain.  Embed the
  bounded seeds into a finite coded domain that also represents rays, tails, or
  the full feasible domain, then state descent and maximizer data over that
  larger domain.  This prevents a later impossible maximizer/canonical-shape
  obligation for accept-all or tail policies.
- Do not assume raw component count is the right descent measure.  If a proof
  step can jump directly from a noncanonical finite object to a canonical one,
  use a shape-specific "badness" complexity that is zero on canonical objects
  and positive on noncanonical ones; this turns canonical dominance into a
  terminating finite-descent step without manufacturing artificial endpoint
  count decreases.
- When source endpoint lemmas naturally produce ordinary policies rather than
  elements of the finite coded domain, add a narrow conversion wrapper from
  those source policies into equal coded representatives.  This keeps the hard
  calculus in source language and avoids forcing every endpoint proof to build
  interval/ray codes manually.
- In noncomputable bridges from proof-level policy forms to `Type`-valued
  replacement data, do not `rcases` an `Exists` proof inside a term returning
  `Type`; Lean cannot eliminate Prop existentials that way.  Use
  `Classical.choose` / `Classical.choose_spec` to recover the threshold
  parameters, then rewrite the chosen policy to the canonical replacement.
- When several source routes produce a feasible Lemma 5 optimizer-replacement
  certificate, add one generic `of_optimizer_replacement_subset` adapter to
  the paper's concrete replacement-data type, then specialize it to
  policy-canonical dominance, positive-response marginal certificates, or
  endpoint certificates.  This avoids duplicating the shape/threshold
  extraction proof.
- If the source-facing certificate is proof-valued, avoid packing it under
  `Sigma`; Lean expects a `Type` there and proof-valued structures may live in
  `Prop`.  Use ordinary `Exists` fields for proof-only choices, then `rcases`
  them at the use site.

## Lean Patterns

- If an optimizer proof over functions becomes unwieldy, introduce a finite
  coded feasible type and decode after using `Fintype`.
- Keep objective aliases paper-facing and formula-explicit; push only the
  reusable argmax/ordering theorem into the library.
- When lifting from a paper proof into an optimization module, leave
  source-facing definitions formula-explicit in the paper and make them call
  the library theorem by `simpa`; changing the source definitions into opaque
  generic aliases can break old `unfold`/`rw` proof scripts and hide the formula
  a human needs to review.
- When comparing objectives, expose monotonicity as a named field or theorem
  rather than unfolding expectation internals inside every paper wrapper.
- Prefer theorem statements over opaque bundled witnesses in `PaperInterface`;
  bundled certificates are implementation tools and belong in proof files,
  post-paper audit ledgers, or reusable foundation modules.
