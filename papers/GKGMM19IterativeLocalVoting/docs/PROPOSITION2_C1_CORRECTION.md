# Proposition 2: medians on a constrained feasible set

## C1 corrected target

- **Limit on a general convex domain:** Proposition 2's coordinatewise medians
  → minimizers of expected coordinatewise absolute distance over the feasible
  set. For an ideal point $V$ and feasible set $X$, the target is

$$\operatorname{argmin}_{x\in X}\;\mathbb{E}\!\left[\sum_i |x_i-V_i|\right].$$

The result covers Model A and the
[coordinatewise Model B rule used in the proof](SOURCE_CLARIFICATIONS.md#proposition-2s-coordinatewise-model-b).
On a product domain, this is exactly the feasible coordinatewise median set.
On a coupled domain, separate coordinate medians can be infeasible.

The source is [Proposition 2 and its Appendix C.5 proof](https://www.jair.org/index.php/jair/article/view/11358).
C1 requires a bounded, closed, convex feasible set; it does not require a
product domain. The constrained target applies under C1 without adding that
geometric restriction.

## Why the coordinatewise median can be infeasible

Take
$$X=\{x\in\mathbb{R}^3:x_i\geq0,\;1\leq x_1+x_2+x_3\leq2\}.$$
Draw the ideal point from an equal mixture of uniform distributions on balls
of radius $0<r<0.05$ centered at $(1,0.05,0.05)$, $(0.05,1,0.05)$, and
$(0.05,0.05,1)$. These balls lie inside $X$, and the mixture has a bounded
measurable density. The decomposable utility
$f_v(x)=-\sum_i(x_i-v_i)^2$ has the unique ideal point $v$, so this example
satisfies C1–C3.

Two thirds of each coordinate's marginal mass is near $0.05$. Its unique
median lies strictly between $0.05$ and $0.10$, so the coordinatewise median
vector has sum below $0.30$ and lies outside $X$. Algorithm 1 projects each
iterate into the closed set $X$ and therefore cannot converge to that vector.
Minimizing expected absolute distance over $X$ gives a feasible target.
