# Theorem 3: full-space result and constrained-space alternative

## The two formal results

The formalization separates the paper’s zero-direction conclusion from the
effect of projection onto a constrained decision space.

### Full-space result

Under the explicit full-space condition, every aggregate direction is feasible.
The formalization proves the paper’s conclusion: a convergent Model B trajectory
has zero aggregate directional field at its limit. This field is the population
average of voters’ normalized utility gradients.

### Constrained-space alternative

For a constrained decision space, the formalization proves an alternative:
either the limiting aggregate field is zero, or the feasibility condition used
by the zero-field argument fails. Constraints can prevent a step in the aggregate
direction even when that direction is nonzero.

The condition requires a positive step in the limiting aggregate direction to
remain feasible from the relevant late iterates. The alternative concerns this
trajectory condition; it does not assert that every aggregate direction is
blocked at the limiting point.

## Relation to the paper

Theorem 3 and Appendix C.6 state the zero-direction conclusion. The full-space
result proves that conclusion under the explicit full-space condition. The
constrained alternative is an additional result for the projected setting;
it does not establish the unrestricted zero-field conclusion on every bounded
convex domain. The [precise feasibility condition](SOURCE_CLARIFICATIONS.md#theorem-3s-full-space-and-projected-readings)
is recorded in the source clarification.
