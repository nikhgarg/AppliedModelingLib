# Source Clarifications: Accuracy-Diversity

## Value and type-support restrictions

- Corollary 1's type probabilities $p_t$ → $p_t>0$ for every type in the
  current proof. Whether the conclusion holds with zero-probability types
  remains unresolved.
- Theorem 1(ii)'s merely upper-bounded conditional value law → an upper-bounded
  law with nonnegative values almost surely. This is a sufficient condition in
  the current allocation proof; that proof does not cover arbitrary translated
  negative laws, and necessity for the conclusion is unresolved.
- All-coordinate share limits → positive preferred-type mass for every named
  type. A zero-mass coordinate needs a separate supportwise formulation, so
  positivity is needed only for the stated all-coordinate conclusion.

## Proposition 2 and the finite uniform model

- Relaxed allocation $a_t=N s_t-1$ → $(N+T)s_t-1$, where $s_t=\sqrt{p_t}/\sum_j\sqrt{p_j}$, $p_t$ is type weight, $T$ the type count, and $N$ the budget. The printed coordinates sum to $N-T$, not $N$.
- Printed rounding error $(T+1)/N$ → checked bound $(2T+1)/N$ on $|a_t/N-s_t|$ in the positive top-$k$ domain, where $k$ is the consumption count. The optimizer shift alone does not refute the sharper bound; its proof remains open here. Both bounds give the same square-root share limit.

## Theorem 2: independent rank-varying Bernoulli values

- “Identically distributed” rank coordinates → independent Bernoulli coordinates with rank-dependent probability $c((i+1)+d)^{-\alpha}$, where $i$ is the zero-based rank, $c$ the scale, $d$ the rank shift, and $\alpha$ the decay exponent. Top-one results use $c>0$, $d\ge0$, and first probability strictly below one: flat cases $c=0$ or first probability one need not force universal homogeneous shares.
- The all-consumed $p_t^{1/\alpha}$ formula at $\alpha=0$ → choose a type of maximal $p_t$ separately at zero exponent. The positive-exponent power law retains its stated domain; cross-type independence is unnecessary because the objective conditions on the selected type.

## Theorem 1 and Appendix Lemma D.1 share asymptotics

Here $h(a)$ is one type's expected top-$k$ value from an allocation of $a$ items (or the abstract one-type objective in D.1), and $p_t$ is type $t$'s selection probability.

- The all-type finite-discrete Theorem 1(i) route explicitly uses positive type weights and a nonnegative common value law with a positive top value, a strictly lower nonnegative second bound, and positive mass at the top and below it. These conditions support divergence of every optimal allocation coordinate; the present theorem does not establish an all-coordinate limit without them.
- D.1(i)'s $B>0,\ \sigma<0$ in $\log(A-h(a))/(B a^\sigma)\to1$ → $B<0,\ \sigma>0$ and eventually $A-h(a)>0$, describing approach to saturation $A$. Under the printed signs, weights $(1/4,3/4)$, $h(a)=1-1/(a+1)$, $A=2$, $B=1$, and $\sigma=-1$ satisfy the limit but give square-root shares rather than uniform shares.
- D.1's power-branch comparison of original objectives → comparison of deficits $A-h(a)$; a strict deficit ratio need not reverse the objective ratio as both objectives tend to $A\sum_t p_t$. The logarithmic branch maximizes, rather than minimizes, $\sum_t p_t\log(x_t)$, where $x_t$ are allocation shares. The logarithmic and sublinear-power branches use strict discrete concavity, and all four branches require positive weights for asserted coordinates.

## Order statistics and integer rounding

- Exponential/Pareto marginal and strict-concavity statements → eventual statements on valid order-statistic ranks. The exponential rate is $\lambda>0$; for fixed upper-rank offset $r$, $\mu(q-r,q)-\log(q)/\lambda\to(\gamma_{\mathrm{EM}}-H_r)/\lambda$, where $\mu$ is the expected order statistic and $H_r$ the harmonic number; $\gamma_{\mathrm{EM}}$ is the Euler–Mascheroni constant. The Pareto density is $\alpha x^{-\alpha-1}$ on its support, with $\alpha>1$.
- Lemma D.5's convex maximization wording → strictly concave maximization. For real/integer fixed-sum maximizers $x,a$ across $m$ coordinates, the checked window is $\lfloor x_t\rfloor<a_t+m$ and $a_t<\lfloor x_t\rfloor+m$. A derivative-free strict-concavity comparison supplies the rounding argument.

## Proposition 4

- Equation (18)'s membership in an infimum → the real inequality $\Gamma(\pi)\le\Gamma(\alpha)$ for every profile $\alpha$, with $\pi$ uniform and $\Gamma$ the source objective. Equation (20)'s unweighted surface integral → the preference-weighted measure in Equation (17); full support does not equate those finite integrals.
- The pointwise-supremum Laplace step uses regularity, such as a continuous
  nonconstant radial kernel valued in $(0,1]$ on realized distances. This is a
  sufficient current proof condition, and its necessity for Proposition 4 is
  unresolved. Nonconstancy alone is insufficient: under a nonatomic uniform
  measure, $g=1$ at one point and zero elsewhere gives
  $\log(\int e^{ng}\,d\mu)/n=0$ while $\sup g=1$. This diagnoses that inference
  outside the continuous-kernel domain; it does not refute Proposition 4 under
  all its hypotheses.

## All-consumed and Bernoulli endpoints

- Theorem 1(v)'s maximal-type-weight optimizer → a weak optimizer when the common conditional mean is nonnegative; uniqueness requires positive mean. An all-consumed item contributes its type weight times that mean.

- Theorem 3's log-share formula → $0<q_t<1$ for every Bernoulli parameter, so $1/\log(1/(1-q_t))$ is finite and defined.
- Corollary 3's $q>0$ → $0<q<1$ for its universal share conclusion. With at least two positively likely types and $q=1$, giving each one item attains success probability one and permits nonuniform optimal sequences.
