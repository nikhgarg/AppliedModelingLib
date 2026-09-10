# Appendix C Lemma 1 Laplacian Source Note

The printed global strict inequality needs a local correction. The formalization
proves the weak global inequality, the exact region of strictness, and the
downstream Laplace conclusions without assuming the false global strict form.

Source: Kleinberg and Raghavan, [*Algorithmic Monoculture and Social Welfare*](https://arxiv.org/abs/2101.05853), Appendix C Definition 4 and Lemma 1.

## Paper Statement
Appendix C Definition 4 defines a noise kernel to be strictly well-ordered by a pointwise product inequality for four ordered score locations. Appendix C Lemma 1 then states that both Gaussian and Laplacian noise are strictly well-ordered.

The Gaussian strict statement is proved in Lean.

For the Laplacian kernel, the global strict statement is not true as a pointwise statement over all ordered quadruples.

## Statement Proved In Lean
Lean proves the globally valid weak Laplacian statement:

For every nonnegative Laplace rate `lambda`, the Laplacian density kernel satisfies the weak well-ordering inequality.

Lean also proves strict Laplacian well-ordering on the overlap/local region. Concretely, for ordered locations `a > b` and `c > d`, the extra condition is

```text
b < c and d < a.
```

Equivalently, the open intervals `(b,a)` and `(d,c)` overlap. That is the strictness condition available from the analytic inequality itself.

The downstream Laplace route does not require the false global strict form. It uses the weak comparison for the density-swap step, and strict payoff improvement comes from later support and monotonicity facts. No named theorem or main-text result is affected.

## Downstream Use
The overlap condition is not stated elsewhere in the paper's Definition 4, Lemma 1, Theorem 6, or Lemma 3 source text. Those passages use the global wording "for any `a > b` and `c > d`."

Lean therefore does not prove the downstream Laplace result by treating the overlap theorem as a global replacement for Definition 4. Instead, the formalization takes a different valid route for Laplacian noise:

- global weak Laplacian well-ordering supplies the non-strict density-swap comparisons;
- the strict downstream conclusions come from separate support, monotonicity, and positive-probability arguments in the three-candidate Laplace source model;
- the strict overlap theorem records the exact local condition under which the paper's pointwise strict inequality is true, but it is not used as a hidden global assumption.

## Counterexample To The Global Strict Statement
Using the unnormalized Laplacian kernel

```text
f_x(y) = exp(-lambda * |y - x|)
```

take `lambda = 1` and the all-positive ordered locations

```text
a = 11, b = 10, c = 2, d = 1.
```

The global strict claim would require a strict inequality between the two products appearing in Definition 4. But both sides are equal:

```text
f_a(c) * f_b(d)
= exp(-|2 - 11|) * exp(-|1 - 10|)
= exp(-9) * exp(-9)
= exp(-18),
```

and

```text
f_a(d) * f_b(c)
= exp(-|1 - 11|) * exp(-|2 - 10|)
= exp(-10) * exp(-8)
= exp(-18).
```

So the strict inequality fails even with `a`, `b`, `c`, and `d` all strictly positive. The correct global statement is weak inequality; strictness requires the overlap/local condition `b < c` and `d < a`, not positivity. In this example, the condition fails because `b = 10` and `c = 2`, so the two intervals are separated.
