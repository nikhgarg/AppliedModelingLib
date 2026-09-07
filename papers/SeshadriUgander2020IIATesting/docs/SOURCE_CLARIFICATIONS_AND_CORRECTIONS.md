# Source clarifications and corrections

## Lemma 2 mixture reduction

- Membership of the orientation mixture in the separated alternatives → averaging a fixed test's errors over separated components. With `d` comparison coordinates and opposite orientation vectors `b,-b`, the laws `(1+epsilon b)/d` and `(1-epsilon b)/d` average to the uniform IIA law `1/d`; positive component separation need not survive mixing. Some component has error at least the average. Each component is `delta`-separated when `epsilon>=2 mu(sigma) delta`, where `mu(sigma)` is the cycle decomposition's mean length. The same `4 n delta` sufficient condition and testing conclusion follow, with `n` the number of items.

## Theorem 1 perturbation range

- **Theorem 1’s display → explicit range `2 mu(sigma) delta <= 1`.** The source defines perturbations only for `epsilon` in `[0,1]`; its proof chooses `epsilon=2 mu(sigma) delta`, where `mu(sigma)` is mean cycle length and `delta` the testing separation. This states the witness’s valid range; no counterexample to a broader lower bound is supplied.

## Le Cam coefficient in the proof of Theorem 1

- Coefficient `1/4` before total variation in the first proof line → `1/2`. Applying `TV <= (1/2)sqrt(chi^2)` then gives the subsequent `1/4` coefficient used by the theorem.

## Appendix comparison-incidence bound

- The rational mean-cycle-length branch without a denominator condition → require `d-4n+8 log_2(n)>0`, where `d` is the number of comparison-incidence edges and `n` the number of items. The checked result states that case condition explicitly while retaining the unconditional `2n` branch. The real-logarithmic simplification used for the printed dispersion bound is checked for `n ≥ 4`.

## All-even-subsets endpoint

- The appendix corollary prints the range `n ≥ 2`. At `n = 2`, the relevant comparison-incidence graph is not Eulerian, so the stated construction does not apply. The checked theorem begins at `n = 3`, proves the `n = 3` case directly, and proves all `n ≥ 4` cases from the general construction.
