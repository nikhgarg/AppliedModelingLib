# Governing-Model Clarification

## Model readings

- **Accumulating ratings → positive sampling rates `g(theta)>0`.** This makes explicit the growing-sample regime used by the paper’s convergence and large-deviation arguments (`cited publication:669–670, 745`).
- **Independent rating histories → a product probability law.** This realizes the independence used in the Appendix’s pairwise factorization; the ranking objective uses only those pairwise marginals (`cited publication:1638–1642`).

## Theorem 1 reading

- The printed adjacent-pair minimum through `i=M-1` → `0<=i<=M-2`, where `M` is the number of ordered seller types: the last printed term refers to an undefined next type.
- Strict cross-quality upper-tail comparisons at every rating → only above the lowest rating. At the lowest rating the upper-tail probability is one for every type, so it cannot be strictly increasing.
- Real-valued intermediate rate costs → extended-real Legendre costs inside the infimum, so thresholds outside rating support have infinite cost. The final minimum is finite. This avoids a terminal full-support assumption and retains the stated exponential rate for the ranking error.

## Displayed indices and finite-state route

- In the aggregate-score display, `n_k(theta)+1` summands indexed through `n_k(theta)` → exactly `n_k(theta)` ratings, indexed from zero through `n_k(theta)-1`.
- The Appendix's continuum substitution → a finite iid probability comparison with a fixed-constant event sandwich before taking normalized logarithms. This supplies the discrete probability rate without treating the continuum integral as an exact finite probability.

## Population-state boundary

- Theorem 1's population recurrence → an explicitly declared iid rating law. The formalization has not connected that law to the printed recurrence, whose transition uses `n_k` and `n_(k-1)` while updating `mu_k` to `mu_(k+1)`. This is an unproved model connection, not a counterexample to the ranking-rate theorem.
