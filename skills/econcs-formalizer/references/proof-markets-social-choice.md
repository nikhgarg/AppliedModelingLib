# Markets and Social Choice

Use for `AppliedModelingLib/Markets/*`, `AppliedModelingLib/SocialChoice/*`, matching, fair
division, rankings, Mallows models, and social-choice/ranking papers.

## STV/RCV and Voting Rules

- For ranked-choice voting papers, build reusable semantics under
  `AppliedModelingLib.SocialChoice.Voting` before paper-local theorem work. Keep ballot
  primitives, active-set updates, tallies, winners, eliminations, transfers,
  tie-breakers, and replay/process predicates in the shared layer when they are
  paper-neutral.
- Search the shared voting modules before scaffolding paper-local definitions:
  use `Voting.Ballot` for finite ballots and next-active preference,
  `Voting.STV` for deterministic STV traces and transfer-rule interfaces,
  `Voting.STV.Structures` for final-order and win/loss replay predicates,
  `Voting.STV.SolidCoalition` for same-party quota-process invariants, and
  `Voting.Thiele` for approval/committee-score comparisons.
- Distinguish three objects that are easy to conflate: bare trace or transfer
  data, the proposition-valued replay/process validity predicate over that
  data, and the source theorem conclusion. Bare traces can be source-model
  witness data, but replay validity, surplus-transfer preservation, terminal
  process claims, and ballot-to-candidate isolation should be proved from the
  primitive ballots, tie-breaking, and transfer rule, or marked as explicit
  partial boundaries.
- Do not treat a `Replay`, `Trace`, `Process`, `Bridge`, `Certificate`, or
  `SourcePrimitive`-named premise as source-backed just because it resembles a
  process description. The premise must either be proved from primitive
  ballots/tie-breaking/transfer rules, linked to a specific source assumption,
  or exposed as a boundary in the audit artifacts.
- Keep empirical election audits, simulations, redistricting experiments, and
  real-data claims as data/code boundaries unless their data pipeline is also
  formalized. The Lean target should be the deterministic election semantics,
  structure-validity theorem, or source theorem reduction that is independent
  of those empirical artifacts.
- For strategy or manipulation papers, separate ballot-change vectors and
  strategy spaces from fixed-trace replay validity and payoff/order
  consequences. Close fixed-structure replay and validity lemmas first; expose
  optimization/search or empirical computation as a separate boundary when it
  is not part of the Lean proof.

## Matching and Fair Division

- For matching, keep preference, blocking-pair, stability, and algorithmic
  invariants separate. Paper-facing theorem wrappers should call generic
  deferred-acceptance correctness when possible.
- For Gale-Shapley/Roth-style one-to-one marriage results, close the
  men-proposing DA chain in the reusable library: stability, rejected-pair
  impossibility, men-optimality, equal-size all-acceptable completeness, and
  then women-pessimality by the blocking-pair argument from men-optimality.
  Use the library `womenDeferredAcceptance` role-reversal primitive for
  women-proposing DA statements; it already packages stability and
  women-optimality from swapped men-optimality, and men-pessimality from the
  swapped women-pessimal theorem.
  Proposal-order independence can often be captured first as uniqueness of the
  men-optimal stable matching; keep a separate caveat until an arbitrary
  proposal-order trace has been modeled and connected to that uniqueness
  theorem.
  Follow the paper's named lemma route when the user asks for a paper
  formalization, even when a shorter modern proof exists: make the named paper
  lemma available as a wrapper or bridge, then use cleaner library facts inside
  it. This keeps the audit surface source-faithful without duplicating every
  low-level argument.
  Check the model notation before adding preference caveats. Classic matching
  papers often assume strict preferences through notation such as ordered lists,
  `P`, or "prefers" comparisons; if so, expose strictness as the local domain
  assumption instead of treating it as an extra caveat.
  For papers that cite Roth/Dubins-Freedman truthfulness rather than reproving
  it, prefer a thin paper-local wrapper around the existing Roth Theorem 5
  declarations, with the strict equal-size domain exposed in the local paper
  notation.
  For exchangeability or random-market arguments, use
  `Assignment.relabelWomen` and `isStable_relabelWomen_iff` to prove that
  stable-partner events are invariant under woman-side relabeling before
  invoking finite uniform probability relabeling.
  Keep optional-list/rural-hospitals strengthenings separate from complete
  all-acceptable wrappers, and make the domain assumption visible in paper
  theorem names and README rows.
- For Roth rural-hospitals or college-admissions papers, reuse the one-to-one
  stable-matching/DA layer where possible, but introduce capacities as a
  separate abstraction. Do not mix complete-marriage all-acceptable wrappers
  with optional hospital/resident acceptability; rural-hospitals statements
  usually need unmatched/underfilled-set invariance and should advertise those
  assumptions explicitly.
- For random matching arguments, keep three layers separate: deterministic
  matching facts such as `X_mu(g) >= Y_g`, the concrete fresh-list probability
  law, and the Chebyshev/variance bridge. A defect in a stochastic lemma should
  not contaminate the matching layer. State any restricted variance theorem
  with its exact sampling-law hypotheses and keep the deterministic trace proof
  independent.
- Do not infer a conditional deletion identity for a nonuniform
  without-replacement law. Before using a comparison such as
  `Pr[omit i | omit j] <= Pr[omit i]`, enumerate the smallest supported laws
  and verify the inequality on exact ordered atoms. When it holds under the
  required draw regime, a robust route is to prove hit-event negative
  correlation first, split the outside hazard sums, prove the resulting scalar
  inequality, and complement via
  `pmfProb_not_and_not_le_mul_of_inter_le_mul`.
- Do not generalize a fixed-draw negative-correlation calculation without
  checking the next draw and support sizes. If exact enumeration finds positive
  covariance or a variance-bound failure, retain the valid restricted theorem
  and switch the paper endpoint to a tail-count route: instantiate the rank tail
  used by the lower-bound sum and prove either its pairwise negative correlation
  or its variance bound directly.
- For resumed deferred-acceptance traces, use target divorce plus arbitrary-start
  DA with target-exception invariants. Prove accepted-list nodup/order and final
  stable-except-target facts separately, then package the blocking-pair witness
  preference condition and final target-removal property in one compact
  completion certificate. Avoid replacing the target-divorcing trace with a
  non-divorcing held-set equality that does not model the source transition.
- For Algorithm 4.2 fresh-list/deferred-decision arguments, prefer concrete
  prefix-set laws for the recursive weighted-without-replacement PMF over
  opaque "conditional law equals filtered draw" hypotheses. Build expectation
  lower bounds on ranked tails, then feed only the required tail count into the
  concentration step.
- For manipulation-rank or "no need to misrepresent" statements, formalize the
  source wording rather than a nearby stronger or weaker slogan. "No need to
  misrepresent the first choice" may mean every arbitrary report is weakly
  dominated by a first-choice-preserving report, not that every false-top report
  is unprofitable. If a theorem quantifies over every rank `k > 1`, finite
  `k = 2` or `k = 3` witnesses are not enough; build the parameterized family,
  padding, or scaling construction that the paper claims.
- For college-admissions/hospitals-residents capacity models, first build a
  generic many-to-one assignment API with applicant matches, finite college
  rosters, consistency, quota feasibility, individual rationality, and blocking
  pairs. Then prove the cloned-seat bridge: define `CollegeSeat quota` as a
  dependent sigma over colleges and `Fin (quota c)`, add explicit `Fintype` and
  `DecidableEq` instances at that abstraction boundary, run ordinary
  one-to-one deferred acceptance over seats, and collapse the assignment back to
  rosters.
- In cloned-seat many-to-one proofs, close quota feasibility by injecting each
  roster member into the seat copy chosen from its one-to-one match. Close the
  free-seat blocking case with a companion lemma: if a collapsed roster has
  cardinality below quota, then some cloned seat for that college is unmatched;
  prove it by contradiction and inject seats into the roster via the
  one-to-one consistency field.
- To lift stability from cloned seats to colleges, split a many-to-one blocking
  pair into either a free-seat case or a replacement case. The free-seat case
  blocks the stable seat assignment using the empty cloned seat; the replacement
  case uses the currently assigned applicant's cloned seat. Keep all seat values
  definitionally equal to the owning college's value so `simp` can finish most
  valuation rewrites.
- For fair division, reuse bundle/allocation primitives. Prove feasibility,
  marginal-value, and envy/fairness predicates separately before combining them
  in paper wrappers.
- For finite fair-division allocation theorems, first prove a theorem for an
  abstract marginal bound, then instantiate it with the paper's finite maximum
  one-good marginal value.
- For fair-division PTAS/FPTAS rounding arguments, keep the actual source
  allocation, rounded allocation, selected search witness, comparison IP, and
  output allocation tied together in the theorem surface. If an endpoint
  returns both proof payload and an external runtime consequence, add tiny
  projections for the verified payload and the external consequence so future
  wrappers do not unpack nested conjunctions by hand.
- For bounded-optimum or local-reallocation claims, close the finite exact
  allocation source theorem first, then route it into rounded-supply or typed
  high/low provider wrappers. Do not redo the descent proof while working on
  finite-search, IP-realization, or output-transfer endpoints; those later
  layers should consume the bounded-optimum wrapper as a source-shaped input.

## Rankings and Mallows

- For rank-weight monotonicity, first prove the PMF/fiber decomposition, convert
  to a pure rank-only weight formula, then prove a generic cleared
  weighted-average lemma from pairwise cross-ratio or prefix dominance.
- Use `AppliedModelingLib.SocialChoice.Ranking.Basic` for paper-independent finite
  ranking primitives before adding paper-local notation. It provides
  `Candidate`, `Ranking`, `firstChoice`, `secondChoice`, `rankOf`,
  `swapTopTwo`, `bestRemainingAfter`, and the standard top-two/rank simp
  lemmas. Paper-local ranking modules should usually be compatibility layers
  over these shared primitives.
- Use `AppliedModelingLib.SocialChoice.Ranking.Kendall` for inversion predicates,
  inversion finsets, `kendallTau`, deletion/relabeling formulas through
  `cycleRange` and `cycleIcc`, and center-transposition invariance. Keep
  paper-local Kendall modules as naming wrappers around these shared facts.
- Use `AppliedModelingLib.SocialChoice.Ranking.Probability` when a continuous random
  ranking map must be turned into a finite ranking law. It provides the
  discrete measurable-space instance, `firstChoiceProb`,
  `rankingPMFOfMeasure`, `rankingPMFOfMeasure_eventProb`,
  `bestRemainingAfterProb_rankingPMFOfMeasure`, and
  `firstChoiceProb_rankingPMFOfMeasure`. In paper files, keep theorem-number
  names such as `rumRankingPMFOfMeasure`, but implement them as wrappers around
  the shared pushforward and event-probability bridge.
- Use `AppliedModelingLib.SocialChoice.Ranking.Approval` before adding local K-approval
  or top-tier scoring notation. It owns `approvedByK`, pair-up/down
  probabilities, score-gap equivalences, `lastRank`,
  `approvedByK_allButOne_iff_rankOf_ne_lastRank`,
  `kApprovalPairUpProb_allButOne_eq_rankOf_lastProb`, and
  `kApprovalPairDownProb_allButOne_eq_rankOf_lastProb`. For one-loser or
  all-but-one approval papers, keep paper-local terminology as thin wrappers
  over the shared last-rank and all-but-one lemmas.
- For top-tier K-approval under Mallows-style laws, separate the reusable proof
  route into three layers: finite-support pairwise rate or score-gap algebra,
  the K-approval ternary/all-but-one specialization, and the paper's
  relevant-pair aggregation. Boundary or no-randomization statements often
  reduce to a pivotal pair plus a last-rank probability formula; make those
  library wrappers reusable when a second paper needs the same fact, but keep
  paper-specific top-window or goal-language wrappers local.
- Use `AppliedModelingLib.SocialChoice.Ranking.Mallows` for the paper-independent
  finite Mallows law/weight layer: `mallowsWeight`, `mallowsPartition`,
  `MallowsSpec`, first/first-second/pair-correct/pair-wrong weights and
  probabilities, and finite normalization identities. If a paper already has a
  source-facing local Mallows structure, prefer an explicit adapter to the
  shared structure over a broad rewrite that breaks existing field projections.
- Use `AppliedModelingLib.SocialChoice.Ranking.MallowsSequential` for Mallows laws over
  a feasible remaining set before copying paper-local sequential finite sums. It owns
  `MallowsSpec.bestInSetWeight`, pair best-in-set/correct-wrong fiber
  identities, swap-reindexed best-in-set fiber sums, nonnegativity/zero-mass
  and partition lemmas, expected-best normalization by unnormalized fibers, and
  `expectedBestInSet_le_of_bestInSetWeight_cross`. Bridge paper-local
  definitions with small `[simp]` adapter lemmas rather than importing a paper
  module from the shared library.
- Use `AppliedModelingLib.SocialChoice.Ranking.RankPower` before copying finite
  geometric rank-sum algebra from a paper file. It owns `candidateRankPowerSum`,
  `candidateRankReversePowerSum`, `candidateRankPrefixPowerSum`,
  `candidateRankRemovalPowerSum`, `candidateRankBestAfterRemovalWeight`,
  the removal-sum closed form and `(1 - q)` identity, best-after-removal
  below/above/self simplifications, rank-power positivity/monotonicity, and
  the inner nonnegativity/strictness helpers used in Mallows
  rank-factorization proofs. Keep paper-facing theorem names as wrappers around
  this module when they are source-facing.
- Use `AppliedModelingLib.SocialChoice.Ranking.MallowsRankFactorization` when a paper
  has already established first/top-two Mallows fiber factorization. It owns
  the assumption package `MallowsSpec.RankFactorization`, the first-tail versus
  removal-sum identity, and first-weight prefix algebra. Keep paper-facing
  factorization structures stable and call shared lemmas through adapters;
  leave concrete fiber-decomposition constructors paper-local until a second
  paper needs the same decomposition.
- Use `AppliedModelingLib.SocialChoice.Ranking.Payoff` for paper-neutral finite
  ranking-law payoff algebra before proving paper-local versions. It
  provides `firstChoiceMissProb`, `valueGap`, `expectedFirstMoverUtility`,
  `expectedSecondMoverShared`, `secondMoverUtility`,
  `expectedSecondMoverIndependent`, `expectedWelfareOrdered`,
  `rerankingGainOnPair`, `expectedRerankingGain`,
  `secondMoverFirstLawSwitchGain`, first-choice probability bounds and
  sum-to-one, miss-probability complement and positivity,
  `firstChoiceGapMass`, `firstChoiceCollisionDiff`,
  `sum_firstChoiceGapMass_eq_expectedGap`,
  `expectedFirstMoverUtility_eq_sum_firstChoiceProb`,
  `expectedSecondMoverShared_eq_sum_secondChoiceProb`,
  `innerRerankingGain_eq_missProb_mul_gap`,
  `expectedRerankingGain_eq_expect_missProb_mul_gap`,
  `expectedRerankingGain_eq_sum_firstChoiceMissProb_mul_firstChoiceGapMass`,
  `expectedCollisionLossDiff_eq_sum_collisionDiff_mul_firstChoiceGapMass`, and
  `secondMoverFirstLawSwitchGain_eq_expected_collision_loss_diff`. Preserve
  paper-facing names, but delegate generic finite-sum proofs to this shared
  module.
- Use `AppliedModelingLib.SocialChoice.Ranking.Score` for three-score ranking
  maps before writing paper-local case splits. It provides `rum3RankByScores`,
  `rum3RankByScoreFns`, the six concrete three-candidate rankings, no-tie and
  top/middle/bottom score predicates, first/second-choice simp lemmas,
  `bestRemainingAfter_rum3RankByScores_remove*`, and the score-order
  consequences from first-choice or best-remaining outcomes. Keep measurability
  of score functions in the RUM/probability file; the score module is pure
  finite social-choice code.
- Use `AppliedModelingLib.SocialChoice.Ranking.Sequential` for probability-free
  sequential choice primitives before adding paper-local definitions. It owns
  `bestInSet`, rank-minimality and membership lemmas, full-set/
  removed-singleton/singleton/pair simplifications, center-rank relabeling,
  candidate-position swaps, swap rank simp lemmas, rank extensionality helpers,
  deterministic best-in-set value improvement after correcting an inverted
  pair, adjacent-correction reachability/monotonicity predicates, and bounded
  prefix-cut indicators:
  `deleteFirstChoicePrefixCut`, `bestInSetPrefixCutIndicator`,
  `centerPrefixCutValue`, `weaklyOrderedBy_centerPrefixCutValue`,
  `bestInSetPrefixCutIndicator_eq_centerPrefixCutValue`, and
  `adjacentSwapImproves_bestInSetPrefixCutIndicator`. Keep theorem-facing
  definitions reducible when later proofs unfold them, but prove generic lemmas
  by delegating to the shared module.
- Use `AppliedModelingLib.SocialChoice.Ranking.SequentialPayoff` for PMF expectations of
  the best feasible candidate. It provides `expectedBestInSet`,
  `expectedBestAfterRemoval`, and full-set/singleton/removed-singleton
  simplifications. Paper-local expected-best-after-removal names should be
  wrappers around this shared definition when possible.
- Use the library finite-sum layer before writing Mallows-local algebra:
  `AppliedModelingLib.FiniteSum.pair_sum_eq_ordered_swap_sum_of_injective_key`
  performs the `(i,j)`/`(j,i)` regrouping by a reference rank key, and
  `AppliedModelingLib.FiniteSum.weighted_average_cross_nonneg_of_pairwise` /
  `AppliedModelingLib.FiniteSum.weighted_average_cross_pos_of_pairwise` discharge the
  weak/strict pairwise-cross-ratio weighted-average comparison. Paper-local
  ordered-pair regrouping lemmas should usually be compatibility wrappers
  around these shared lemmas.
- If conditioning or deleting a rank creates piecewise weights, prove small
  closed-form below/above/self lemmas and a deletion-sum geometric identity
  before attempting the all-cases theorem.
- For Mallows/ranking proofs, match pairwise decompositions when the paper
  compares `(i,j)` and `(j,i)` top-two events. Prove the top-two expansion,
  define ordered-pair terms, then prove antisymmetric swap identities.
- Use the shared adjacent-order and bounded prefix-cut APIs before
  recursive prefix-cut proofs. The generic declarations now live in
  `AppliedModelingLib.SocialChoice.Ranking.Sequential`; keep the recursive
  identity-center Mallows dominance stack paper-local until a second paper
  needs the same subset-marginal recursion.
- Keep three Mallows layers separate: denominator-cleared paper sum, top-two
  pair/bracket regrouping, and rank-factorization formulas for first/top-two
  fibers.
- Check strictness and boundary cases before claiming a Mallows theorem is
  assumption-free. State needed interior-parameter and candidate-count
  assumptions at the wrapper.
- For weaker-competition Mallows totals, use the paper's conditional-gap route:
  rank-only conditional gap, adjacent-rank antitonicity, finite MLR
  weighted-average inequality, and the positive same-human square-weighted gap.
- For Mallows "first mover beats second mover" lemmas, first prove the generic
  collision-loss identity
  `firstMover - independentSecond = sum firstChoiceProb * firstChoiceGapMass`.
  Then use the rank-factorized first-choice and first-choice-gap weights to
  reduce the sum to a positive scalar times the same-human square-weighted
  conditional-gap sum. This is usually faster than expanding the full
  two-ranking expectation directly.
- For Mallows pairwise-correctness monotonicity, separate the paper's
  cancellation-reduced endpoint-position inequality from the later permutation
  bridge. With inverse parameter `q = phi^-1`, correct endpoint placements have
  lower Kendall exponents than incorrect placements, so prove a strict
  cross-product inequality for the reduced weights and then translate the final
  statement as "probability decreases in `q`" rather than "increases in
  `phi`". Keep this rank-only core as a helper, not as a replacement DAG node
  for the paper's full Lemma 8.
- For the full Mallows pairwise-correctness theorem, introduce actual
  `pairCorrectWeight`, `pairWrongWeight`, and `pairCorrectProb` first, with a
  theorem that correct+wrong weights equal the Mallows partition for a
  center-ordered pair. Then prove a `PairPositionReduction`-style bridge saying
  both actual weights are the same positive scale times the reduced
  endpoint-position weights. The final paper wrapper should consume this bridge
  internally; an explicit-input reduction theorem is only conditional progress.
- For sequential best-of-remaining Mallows claims, do not treat pairwise
  correct-ranking monotonicity as automatically proving expected top-of-set
  utility dominance. State the exact remaining-set dominance theorem needed:
  for every feasible hired set, the more accurate ranking law gives weakly or
  strictly higher `expectedBestInSet` on the remaining candidates. Pairwise
  Lemma-8-style declarations are useful inputs, but the source theorem remains
  conditional until the top-of-remaining-set lift is formalized (often via
  subset/restriction rank-factorization or another explicit stochastic
  dominance bridge).
- For nonconvex remaining-set Mallows dominance, keep the exact best-in-set
  fiber target separate from broader weak-Bruhat or prefix-dominance targets.
  Do not assume the Mallows marginal on an arbitrary nonconsecutive subset is a
  same-parameter Mallows law on that subset; gap-dependent factors can appear.
  Start with the two-candidate and full-remaining-set cases, then decide
  whether center-convex, co-singleton, or explicit deletion/tilting recurrences
  are the right reusable layer for the paper.
- For arbitrary first-choice or prefix-cut decompositions, avoid pointwise
  monotonicity assumptions on every branch. Sum over the finite insertion or
  first-choice branches first, expose aggregate brackets or pair-sums, and use
  diagonal-plus-weighted regrouping when individual two-branch brackets can be
  negative but the total recurrence should cancel.
- For stubborn sequential Mallows optimality proofs, shrink the target before
  trying a broad weak-order monotonicity theorem. A useful route is: delete
  absent extremes and trivial cuts, reduce to a same-size prefix-cut
  weighted-extremes cancellation, prove the first-choice prefix-cut probability
  comparisons, and then route the paper theorem through remaining-utility
  dominance. If this route replaces a proof sketch that appeals to a broader
  monotonicity principle, record the mathematical route concisely in the final
  report rather than listing implementation lemma names.
- When using loose Kendall-layer index bounds, prove and reuse no-gap support
  lemmas before chaining adjacent layer inequalities: if a higher identity
  Kendall layer is nonempty, every lower layer is nonempty. This lets adjacent
  cleared-average inequalities telescope without division-by-zero side cases.
- For ranking fibers over `Fin`, normalize first-choice rank `r` with
  `Fin.cycleRange r`; normalize ordered top-two ranks `r < s` with
  `cycleRange r` followed by `cycleIcc 1 s`; normalize swapped top-two ranks
  with `cycleRange s` followed by `cycleIcc 1 (r+1)`.

## Social Choice Probability Bridges

- When only a ranking law changes, first try
  `Ranking.Payoff.secondMoverFirstLawSwitchGain_eq_expected_collision_loss_diff`
  or `expectedSecondMoverIndependent_le_of_collisionProb_le_and_gap_nonneg`.
  These rewrite second-mover payoff differences as candidatewise collision
  probability deltas times value gaps and often turn a game/probability theorem
  into the scalar inequality written in the paper.
- For finite conditional utilities with exactly two possible continuation
  values, use a generic two-outcome expectation lemma
  (`E[f] = Pr[event] * x + (1 - Pr[event]) * y`) before specializing notation.
- For strict probability bounds such as `Pr[event] < 1`, prove positive mass
  outside the event and apply a finite PMF complement lemma.
