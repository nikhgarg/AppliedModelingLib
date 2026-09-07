# Source Clarifications for *An Algorithmic Framework for Bias Bounties*

Source: [arXiv:2201.10408v4](https://arxiv.org/abs/2201.10408v4); line references are to its `main.tex`.

## Conditional group loss and null groups

- Definition 2's divided conditional loss → value zero on zero-mass groups, with mass-weighted loss as the primitive (lines 319–331). Division is undefined there; Definition 7 already requires positive certificate mass.

## Bayes optimality and Observation 4

- Pointwise conditional-risk optimality → modelwise almost-everywhere optimality against every admissible integrable alternative model for arbitrary population laws (lines 333–351). A null-point change cannot affect any subgroup integral: for example, under uniform features on `[0,1]`, changing an otherwise optimal binary predictor only at zero preserves every integrated loss. For countably many labels, action comparisons share one full-measure set; on finite positive-mass support the pointwise conclusion follows.

## Adaptive certificate checking

- Theorem 11's undefined confidence symbol and transcript count → failure bound `2 N exp(-n epsilon^2/32)`, where `n` is sample size, `epsilon>0` the certificate threshold, `U` the submission horizon, and `N=U(U+1)^floor(2/epsilon)` (lines 549–603). At failure probability `delta`, it suffices that `n >= (32/epsilon^2) * (log(2U/delta) + floor(2/epsilon)*log(U+1))`. For `0 < epsilon <= 1`, `U >= 1`, and `0 < delta <= 1`, this is at most `96 epsilon^-3 log(2U/delta)`, the paper's claimed sample rate; the explicit formula is sharper in its confidence dependence.
- Algorithm 2's completed transcript may contain one more acceptance than a queried prefix: its non-strict guard allows a final acceptance at count `floor(2/epsilon)`, after which no later query is made (lines 524–547). The sparse count applies to queried prefixes.

## Shared state in Algorithm 4

- Interleaved submissions and repairs → one shared checker transcript, with the protected-history scan restarted after each accepted repair (lines 671–713). A model change can make an earlier rejected repair improve loss; restarting supplies Theorem 14's monotonicity and cubic query bound.

## Fresh blocks, integer rounds, and the Lemma 15 typo

- Algorithm 5's optimization/stopping dataset `D` → the current fresh block `D_t`; real horizon `2/epsilon` → `ceil(2/epsilon)` rounds (lines 786–811). For `0 < epsilon <= 1`, the rounded count is at most `3/epsilon`, so the oracle and sample rates remain `O(1/epsilon)` in the number of blocks.
- Lemma 15's undefined `g_p` → the quantified group `g` (lines 773–779).

## Lemma 22 proof route

- Disagreement-normalized counts treated as population masses → the identity “disagreement empirical risk = group-independent constant minus certificate objective” (lines 957–990). Minimizing the former therefore maximizes the latter, proving the same lemma.

## Algorithm 6 and Theorem 23

- Full-sweep stopping → two coordinate-gap tests at the same returned pair; arbitrary-start positive certificate → local optimality, with positive initialization additionally giving positivity (lines 991–1025). The [Algorithm 6 note](ALGORITHM6_THEOREM23_CLARIFICATION.pdf) gives the exact tests, response bound, and zero-value counterexample.
