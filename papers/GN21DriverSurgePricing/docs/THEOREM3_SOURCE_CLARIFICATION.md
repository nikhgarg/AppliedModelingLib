# Theorem 3 Proof-Route Clarification

Theorem 3 asserts that, for ordered target rates, there are structured prices
under which an optimal policy accepts every surge trip and all non-surge trips
below a cutoff. In its higher-ratio regime it further gives the accept-all
conclusion.

## Printed proof route

The printed Lemma 9 fixes a non-surge policy before it selects a feasible surge
price ratio. Its conclusion therefore has the form “for each policy, there is
a feasible ratio.” The subsequent Theorem 3 argument needs the stronger
conclusion that one chosen ratio works against every policy. The clarification
concerns the quantifier order required by that proof route.

## Direct proof

A direct proof selects one structured price before the optimality comparison
and splits the target-rate range into two cases. Above an explicit threshold,
the fixed-price Bellman comparison gives accept-all. At or below that threshold,
the non-surge cutoff is zero (the empty non-surge policy) and the surge policy
is accept-all; the resulting statewise inequalities give optimality. The
paper's cutoff domain includes zero and permits the required sign of the
non-surge adjustment.

Thus the stated Theorem 3 conclusion remains valid on its source policy domain.
The direct proof changes the route used to establish that conclusion.
