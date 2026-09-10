# Strategic Ranking: source clarifications and theorem scope

Source: [*Strategic Ranking*](https://proceedings.mlr.press/v151/liu22b.html),
AISTATS 2022. Write $p$ for effort cost, $g$ for production, $f$ for the skill
quantile, $0<\rho<1$ for capacity, and $0<c\le1-\rho$ for a two-level cutoff.
The high admission reward is $q(c)=\rho/(1-c)$.

## Stated model: known priorities and continuum best response

- **Ties and equilibrium:** applicants know their fixed tie priority before
  choosing effort. A unilateral deviation holds priorities and the population
  score distribution fixed. One full-measure set of applicants must each
  best respond against every feasible deviation; uniqueness is up to a null
  set. Differentiability is read on domain interiors, with endpoint continuity.

## Proposition 3.1

- **Pure-randomization optimum:** weight conditional band means by their
  population shares. Welfare is admission reward $\rho$ minus nonnegative
  effort cost, and pure randomization attains $\rho$. The proof's extra
  uniqueness assertion is not needed for the stated optimum.
- **Cutoff monotonicity:** sufficient additional conditions are
  $$
  x\mapsto\log f(1-e^{-x})\text{ concave on }(0,\infty),\qquad
  z\mapsto\log C(e^z)\text{ concave where }g(0)<e^z\le g(E),
  $$
  where $E=p^{-1}(1)$ and $C=p\circ g^{-1}$. They imply
  $W(d)\le W(c)$ for $0<c\le d\le1-\rho$, holding the market fixed.
  They apply only to monotonicity, not the pure-randomization optimum.
- **Why a restriction is needed:** with
  $p(e)=e^2$, $g(e)=e$, $f(t)=(1-t^2/4)^{-1/2}$, and $\rho=3/10$,
  actual equilibrium welfare satisfies
  $W(1/10)=18/665<14/495=W(1/5)$.
- **Welfare derivative:** if $A(c)=\int_c^1H(c,t)\,dt$ is total effort cost,
  the boundary term in the printed derivative changes sign:
  $W'(c)=H(c,c)-\int_c^1\partial_cH(c,t)\,dt$.

For differentiable positive interior skill, the sufficient skill condition is
that $(1-t)f'(t)/f(t)$ is nonincreasing. It is weaker than log concavity:
$f(t)=1/(2-t)$ separates them. Nondegenerate uniform skill on a nonnegative
interval satisfies it; all $p(e)=e^r$, $g(e)=e^s$ with $r>1$, $0<s\le1$
satisfy the cost condition. These are sufficient conditions, not a necessity claim.

## Associated normalization and access corrections

- **Proposition 3.2:** private utility is the unnormalized
  $\mathbb E[vZ]=\rho\mathbb E[v\mid Z=1]$. Admitted score is
  $\max\{g(p^{-1}(q(c)))f(c),g(0)f(t)\}$, retaining baseline production.
  These corrections to the proof preserve the monotonicity and deterministic optimum.
- **Proposition 3.3:** the proof's condition $g(p^{-1}(x))=x$ conflicts with
  strict convexity of cost and concavity of production. Use
  $p(e)=e^2$, $g(e)=e$, $f(t)=t^3$, $\rho=1/2$, cutoffs $(0,1/4,3/4,1)$,
  and rewards $(0,1/2,1)$ instead. Private utility exceeds $9/128$, versus
  deterministic utility $1/16$, proving the stated existential improvement.
- **Proposition 3.4:** for $p(e)=e^2$, $g(e)=\sqrt e$, $f(t)=t$,
  societal utility is $\rho^{1/4}c(1-c)^{3/4}$, globally maximized at
  $c=4/7$. Interior feasibility requires $\rho<3/7$, replacing the proof's
  $\rho<5/9$; this proves its existential conclusion.
- **Proposition 4.1:** use the mixture's generalized quantile and clip group
  thresholds to $[0,1]$, extending CDFs by zero and one outside support.
  This handles disjoint and touching supports without a smooth inverse.
- **Proposition 4.4:** pure-randomization access is $\rho$, replacing zero in
  the proof, and $\theta_B(c)\ge c$, strictly at positive cutoffs. At exhausted
  support the threshold is one and access is zero. Finite differences prove
  monotonicity without differentiating at support joins.

## Propositions 4.2 and 4.3: exact under clarified weak/strict interpretation

- **Welfare-gap strictness:** $\Delta=W^A-W^B\ge0$ almost everywhere, with
  zero gap under pure randomization. Among types admitted in both groups,
  $\Delta(c,t)>0$ exactly when disadvantaged effort $e^B_c(t)>0$.
  Positive baseline production can permit admission with zero effort.
- **Cutoff comparisons:** for $0<c\le d\le1-\rho$, almost every type admitted
  in both groups at $d$ has $\Delta(d,t)\ge\Delta(c,t)$, strictly if $c<d$
  and $e^B_c(t)>0$.
- **Derivatives:** the same signs apply where derivatives along feasible
  cutoffs exist; deterministic admission uses the one-sided derivative.
  Smooth primitives can still yield kinks at mixture-support junctions.
  For each fixed type, the canonical gap is differentiable almost everywhere
  on the interior common-admission domain, not necessarily at every cutoff
  for every representative of the equilibrium family.

## Appendix effort comparative statics and Proposition B.1

- **Corollary A.1:** use the stated $i<k$ range, replacing $i<k-1$ in the
  proof, and retain baseline clipping and the above-baseline condition for
  strict comparisons.
- **Proposition B.1:** with $X=\max_i\alpha_i f_i(t_i)$ and population CDF
  $F_X$, rank preservation means
  $\lambda(\theta_{post})=\lambda(F_X(X))$ almost everywhere. Different
  ranks can receive the same reward within a policy band. Effort is allocated
  to a maximizing coordinate, unique almost everywhere under independent
  continuous skills; total effort is endogenous, with no fixed budget.

## Proposition B.2

- **Budget:** impose the stated constraint $e^M,e^U\ge0$,
  $e^M+e^U=B$ directly. The extra penalty in the displayed payoff is zero
  on this domain and does not itself enforce the constraint.
- **Global optimum:** sufficient additional conditions are affine skill
  $f_M(t)=a+bt$ with $a\ge0$, $b>0$; $g(0)=0$; $B\ge E=p^{-1}(1)$;
  concavity of $g^2$ on $(0,B)$; and convexity of $x/C(x)$ on
  $[g(p^{-1}(\rho)),g(E)]$, where $C=p\circ g^{-1}$.
  Cost is twice differentiable on $(0,E)$, production twice differentiable
  on $(0,B)$ with continuous $g''$, and source endpoint continuity is retained.
  Unmeasurable skill is independent and regular, with positive finite mean.

Under these conditions, each $c\in(0,1-\rho)$ maximizes a weighted utility
$\beta M+(1-\beta)U$ for some $\beta\in(0,1)$, over all
$0<d\le1-\rho$ and for every equilibrium, holding the market fixed.
The weight does not depend on equilibrium selection. The domain includes
deterministic admission; pure randomization is a separate one-level policy.
Square-root production, quadratic cost, affine measurable skill, and $B\ge1$
give an example satisfying the conditions.

- **Utility calculation:** include conditional normalization and the
  independent skill factor $\kappa_U=\mathbb E[f_U(t_U)]$:
  $$
  M(c)=g(p^{-1}(q(c)))f_M(c),\qquad
  U(c)=\frac{\kappa_U}{1-c}\int_c^1
  g\!\left(B-g^{-1}\!\left(M(c)/f_M(t)\right)\right)\,dt.
  $$
  Differentiation includes the changing-population term. Curvature establishes
  global optimality; stationarity alone does not.
- **Counterexample without the added conditions:** with $p(e)=e^2$, $g(e)=e$,
  $f_M(t)=1/(2-t)$, $f_U(t)=t$, $B=1$, and $\rho=1/16$, the interior cutoff
  $7/16$ is beaten for every positive weight by $9/25$ or $5/9$ in actual equilibria.
