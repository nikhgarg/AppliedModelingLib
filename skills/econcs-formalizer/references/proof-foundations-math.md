# Foundations: Math

Use for `AppliedModelingLib/Foundations/Math/*`, graph/counting helpers, finite rounding,
finite signs, asymptotics, and interval-crossing arguments.

## Proof Seams

- For sign and inequality arguments, create certificate structures whose fields
  are exactly the nonnegativity, strict positivity, monotonicity, or comparison
  facts needed by the theorem. Prefer sum-level certificates for expectation or
  objective theorems.
- For denominator-cleared finite sums, define the unnormalized numerator, prove
  denominator positivity once, and expose normalized/cleared positivity
  equivalences in both directions.
- For finite exchange arguments, use a generic two-point finite-sum update
  lemma: if two functions differ only at `src` and `dst`, the total sum changes
  by the two pointwise deltas. Then derive first-order inequalities from no
  profitable exchange.
- For finite expectation or revenue lower bounds that keep a disjoint subfamily
  of summands, avoid bespoke nested-sum rewrites. Define an injective map from
  the selected index type into the full index type and use
  `FiniteSum.sum_le_sum_of_injective_nonneg`, with nonnegativity of the full
  summands, to compare the selected sum to the full sum.
- For finite double sums over ordered pairs, use
  `FiniteSum.pair_sum_eq_ordered_swap_sum_of_injective_key` when a paper pairs
  `(i,j)` with `(j,i)` according to a reference ranking or score key. If the
  index type itself is linearly ordered, `FiniteSum.pair_sum_eq_ordered_swap_sum`
  is the shorter wrapper.
- For denominator-cleared weighted averages, use
  `FiniteSum.weighted_average_cross_nonneg_of_pairwise` and
  `FiniteSum.weighted_average_cross_pos_of_pairwise`: pairwise cross-ratio
  dominance plus a weakly or strictly decreasing payoff gives the cleared
  average comparison. This is the generic core behind Mallows MLR comparisons,
  rank-layer stochastic dominance, and many finite scoring-rule/rate
  comparisons.
- For two-component pooled estimates over real values, use
  `AppliedModelingLib.Foundations.Math.ConvexCombination` instead of rebuilding
  denominator-cleared algebra. Define paper notation locally, then prove
  comparisons through `twoPointWeightedAverage` with
  `lt_twoPointWeightedAverage_of_lt_components`,
  `twoPointWeightedAverage_lt_of_components_lt`,
  `lt_twoPointWeightedAverage_of_weighted_gap_pos`, or
  `twoPointWeightedAverage_lt_of_weighted_gap_neg`. For parameterized pooled
  estimates, use `continuous_twoPointWeightedAverage` after proving the
  denominator is nonzero or positive.
- For finset-to-finset mass comparisons, use
  `FiniteSum.finset_sum_le_sum_of_injOn_nonneg`: provide an injection from the
  source finset into the target finset, prove pointwise domination along the
  injection, and prove nonnegativity for unused target terms. This is the right
  helper for top-k domination lines such as "any previously selected block has
  total probability at most the top-k block's mass."
- For finite weighted-race arguments, use
  `FiniteSum.weight_share_le_inv_card_add_one_of_forall_le`: if every element
  of a finite comparison set has weight at least the distinguished element's
  weight, then the distinguished element's share of the combined weight is at
  most `1 / (card + 1)`. This is the clean algebraic core for first-hit
  probability bounds like Immorlica-Mahdian Equation (4.1).
- For finite popularity-tail averaging, use
  `FiniteSum.card_mul_le_sum_of_forall_le` and
  `FiniteSum.le_div_card_of_sum_le_of_forall_le`: if every member of a finite
  tail has mass at least `p_w` but the tail's total mass is at most `T`, then
  `p_w <= T / tail.card`. This is the source algebra behind
  Immorlica-Mahdian Lemma 4.3's `p_w <= (1-Q)/(w-k)` line.
- When a proof needs "sort these finitely many objects by score, with ties
  broken arbitrarily", do not leave ranking/injectivity/monotonicity as paper
  assumptions. Build or reuse a finite-ranking helper that maps each object to
  a lexicographic `(score, tie-breaker)` key, enumerates the finite key set with
  `Finset.orderEmbOfFin`, and proves membership, image equality, injectivity,
  and score monotonicity once.
- For finite rounding, split into a reusable no-crossing combinatorial theorem,
  a paper-specific exchange certificate ruling out crossings at optima, and the
  final triangle-inequality or share-error bound.
- For floor/ceiling thresholds around a real optimum, use separate lower and
  upper integer anchors when one anchor cannot serve both roles.
- For real-log or ceiling wrappers around a finite theorem, prove the finite
  theorem first and add the analytic wrapper as a thin layer. Put the
  `Nat.ceil`, `Real.logb`, `rpow_natCast`, and coefficient-rounding facts in
  the wrapper; do not thread analytic side conditions through the combinatorial
  proof. Check exact theorem signatures with `#check`/`exact?` in `/tmp`
  before editing the main file, especially for power monotonicity lemmas whose
  base hypothesis may be `1 <= b` rather than `0 <= b`.
- For analytic crossing proofs, first prove the finite algebra conditionally
  from a named crossing certificate. Then instantiate continuity/limit facts in
  small generic interval modules.
- For unbounded decreasing capacity equations, use
  `existsUnique_eq_and_upper_region_of_continuous_strictAnti_tendsto_atBot_atTop`.
  It packages both the unique cutoff `f cutoff = level` and the source-facing
  upper-region characterization `f z <= level ↔ cutoff <= z`. GLM-style
  school-cutoff and Gaussian-mixture capacity proofs should be thin wrappers
  around this lemma once continuity, strict antitonicity, and endpoint limits
  are available.
- For probability or count sequences bounded by `C / n`, use
  `TendsToZero_of_nonneg_le_const_div` when the sequence is nonnegative, and
  `TendsToZero_of_eventually_abs_le_inv` when you already have an eventual
  absolute-value bound. For bounded counts divided by `n`, use
  `TendsToZero_ratio_of_nonneg_bounded`.
- For analytic statements of the form `x_n ~ y_n`, use
  `AsymptoticEquivalent` rather than restating ratio convergence locally. Use
  `AsymptoticEquivalent.eventually_ratio_mem_Icc` for ratio bounds and
  `AsymptoticEquivalent.eventually_sandwich_of_pos_right` when downstream
  probability or optimization code needs an eventual multiplicative sandwich.
- For paper asymptotics with logarithmic cutoffs, use
  `tendsto_const_div_log_nat_nhds_zero` for `C / log n` terms and
  `tendsto_log_div_sqrt_nat_nhds_zero` for `log n / sqrt n` terms. When a
  paper gives a pre-division count bound such as
  `C n / log n + D sqrt n log n`, first divide by `n` on an eventual
  positive tail, simplify `sqrt n / n` using `Real.sq_sqrt`, and then combine
  the two zero limits with `TendsToZero_of_eventually_abs_le_tendsto_zero`.
- For finite probability-product lower bounds of the form
  `(1 - 1/d)^N`, use `AppliedModelingLib.Foundations.Math.ExponentialBounds`:
  `exp_neg_two_div_le_one_sub_inv_of_two_le` gives
  `exp(-(2/d)) <= 1 - 1/d` when `d >= 2`, and
  `exp_neg_two_mul_nat_div_le_one_sub_inv_pow_of_two_le` raises it to
  `exp(-(2N/d)) <= (1 - 1/d)^N`. This is the clean analytic core for
  Immorlica-Mahdian Lemma 4.3's
  `(1 - 1/(w-k))^(nk) >= exp(-2nk/(w-k))` step.
- Do not assume an intermediate-value crossing gives the needed one-sided sign.
  If the proof needs positivity immediately to the right, use a last-nonpositive
  or first-nonnegative compact-interval lemma and state the interval sign-change
  explicitly.

## Lean Patterns

- For singleton indicator sums:

```lean
simpa using
  (Finset.sum_ite_eq' Finset.univ key
    (fun _ => weight))
```

- For sums of divisions over reals, import
  `Mathlib.Algebra.BigOperators.Field` and use `Finset.sum_div`.
- For compact-interval theorems needing mathlib `ContinuousOn`, convert a
  pointwise epsilon-delta interface with a small bridge such as
  `continuousOn_of_forall_epsilonContinuousAt`; keep topology imports local to
  generic interval/analysis modules.
- Keep imports narrow. Prefer specific Mathlib modules over `import Mathlib` in
  new or actively repaired files.
- If adding one analytic lemma to an otherwise combinatorial file, try the
  narrow leaf import in a scratch file first. For example, base-log wrappers
  should import `Mathlib.Analysis.SpecialFunctions.Log.Base`, not all of
  Mathlib.
- If a Lean goal is not moving after a few local attempts, extract the exact
  algebraic, finite-sum, relabeling, or monotonicity fact as a named helper
  lemma before returning to the main theorem.
- After `field_simp`, `ring_nf`, or `simp` changes an inequality goal, inspect
  the new target before adding another tactic. These tactics often close the
  goal or convert `0 ≤ a - b` into `b ≤ a`; use `sub_nonneg.mp` /
  `sub_pos.mp` deliberately instead of pushing another algebra tactic by habit.
- For strict finite-sum positivity, name the witness term and prove all other
  terms nonnegative before expanding the whole sum. This avoids broad
  pointwise algebra in the final theorem.
