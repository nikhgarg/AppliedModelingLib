# Appendix Lemma 2, `(p = ∞, q = 1)`: corrected exceptional event

## Scope

This note concerns the final case of Appendix C.4, Lemma 2, on printed
page 351 of Garg, Kamble, Goel, Marn, and Munagala (2019).  The second
heading on that page is printed as `(p = 1, q = ∞)`, but its displayed
active-coordinate construction and its `L1` query constraint clearly show
that it is the `(p = ∞, q = 1)` case.

## Minor correction

Let `i₀` be a coordinate attaining
`max_i |x_i - v_i|`, and write `r` for the query radius.  The printed bad
event contains only the near-tie condition

```
exists j != i₀, |x_i₀ - v_i₀| < |x_j - v_j| + r.
```

For the displayed single-coordinate step to be an exact minimizer, the
exceptional event must also include the active-coordinate crossing condition

```
|x_i₀ - v_i₀| < r.
```

Equivalently, off the corrected bad event the active displacement is at least
`r`, and every other displacement is at most the active displacement minus
`r`.  The response that moves exactly radius `r` toward the ideal on the
active coordinate then minimizes `||y-v||_∞` over `||y-x||_1 <= r`; its
cost is `|x_i₀-v_i₀|-r`, while every feasible candidate has at least that
cost on the active coordinate.

The omitted condition matters already in one dimension: the printed near-tie
event is empty, yet a step of radius larger than `|x-v|` crosses the ideal and
is not an optimizer.  The corrected exceptional event resolves this case.

## Effect on the paper and formalization

This is a local appendix-proof correction, not a weakening of the stated
convergence result.  Under C1--C3, its additional crossing event is a
coordinate slab of width `2r`.  The near-tie component is a finite union of
diagonal strips in the bounded decision domain.  A bounded full-dimensional
density assigns their union probability `O(r)`, so the corrected event has
the same rate required by the stochastic-approximation argument.

The formalization proves this corrected geometry and its linear probability
bound, then applies the resulting stochastic-subgradient convergence argument.
The main-text Theorem 1 conclusion remains exact.
