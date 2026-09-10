# Proposition 2: coordinatewise-boundary reading of Model B

Proposition 2 uses the following reading of its Model B response rule:

> Move every coordinate toward its ideal, up to its coordinatewise boundary.

For an `L∞` neighborhood of radius `r_t`, every non-tied coordinate therefore
moves by exactly `r_t` toward the corresponding coordinate of the sampled
voter's ideal. A tied coordinate does not move. This is the coordinatewise
rule used by the paper's proof of Proposition 2, which says to treat each
dimension separately and describes the coordinate as increasing or decreasing
by `r_t` according to the side of the voter's ideal (Appendix C.7).

## Relation to the general Model B formula

Earlier in the paper, Model B is written as movement along the utility-gradient
ray, normalized by the neighborhood norm. For an `L∞` neighborhood, a literal
reading gives coordinate increment

```text
r_t * (partial_m f_v(x) / ||partial f_v(x)||_infinity).
```

That expression reaches the boundary in the coordinate with largest derivative
magnitude. It reaches every active coordinate boundary only when the normalized
active-coordinate magnitudes agree. Proposition 2's proof instead uses only the
sign of each coordinate derivative and moves every active coordinate the full
radius. The formalization makes that proof convention explicit rather than
inferring it from the more general normalized-gradient-ray display.

The distinction is mathematically observable. For example, on `[-1,1]^2`, let
the ideal `Y` be uniform and define the decomposable concave utility

```text
f_y(x) = - a(y_1) |x_1-y_1| - 2 |x_2-y_2|,

a(y_1) = 1     if y_1 >= 0,
         1/2   if y_1 < 0.
```

Under the literal normalized-gradient-ray rule, the first-coordinate drift
vanishes at `x_1 = 1/4`, not at the ordinary median `x_1 = 0`. Thus that literal
variant targets a weighted median. Under the coordinatewise-boundary rule used
in the Proposition 2 proof, the positive coordinate weights do not affect the
step: each coordinate moves by its sign, so the ordinary coordinatewise median
is the correct target.

## Coordinatewise feasible geometry

On product domains, each coordinate can be varied independently and the limit
is a coordinatewise median. On a general convex feasible set, those medians
may be infeasible. The checked constrained conclusion instead minimizes
expected coordinatewise absolute distance over the feasible set. The
[constrained-domain explanation](PROPOSITION2_C1_CORRECTION.md) gives the
geometry and an example.

The normalized-gradient-ray rule is a distinct model whose coordinate weights
can change the limit, as the example above shows. Proposition 2's formalization
uses the coordinatewise rule described by the source proof.
