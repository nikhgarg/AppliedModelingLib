# Source Clarifications

Source: Mendelson and Whang, *Optimal Incentive-Compatible Priority Pricing
for the M/M/1 Queue*.

## Positive-flow and interior reading

- **Theorem 1, pp. 873–874: marginal externality identity for every class →
  a selected class with $\lambda_i^*>0$.** Other optimal flows remain
  nonnegative. The identity is
  $$p_i=\sum_jv_j\lambda_j^*\partial_iW_j(\lambda^*),$$
  where $v_j$ is delay cost, $W_j$ mean system time, and $p_i$ class $i$'s
  price. For welfare
  $F(\lambda)=\sum_jV_j(\lambda_j)-\sum_jv_j\lambda_jW_j(\lambda)$,
  an interior optimum has $\partial_iF=0$; the source demand equality
  $V_i'=p_i+v_iW_i$ gives the formula. At zero flow only one-sided optimality
  follows. This proof establishes the identity for participating classes,
  without proving that every boundary class violates it.

## Effect on the theorem conclusions

- **Theorems 2–4, pp. 876–881: nonnegative flows → positive flow for every
  class** for strict self-selection and strict cheating-penalty comparisons,
  retaining the source's stable stationary domain and strict delay-cost
  order. Theorem 2 gives $C_i(i)<C_i(k)$ for every other priority $k$, where
  $C_i(k)$ is class $i$'s total cost at $k$. Theorems 3–4 give positive
  penalties off the assigned priority and strict increase in both directions.
  Adjacent comparison formulas contain a class-arrival-rate factor; unused
  levels can make it zero and permit indifference. This narrower strict
  domain does not refute weak incentive compatibility at zero flows, and the
  observation is not a full necessity proof for every strict conclusion.
