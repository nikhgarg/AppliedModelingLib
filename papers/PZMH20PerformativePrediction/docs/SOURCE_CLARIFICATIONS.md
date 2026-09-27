# Source Clarifications

Source: *Performative Prediction*, PMLR 119 and its
[official supplement](https://proceedings.mlr.press/v119/perdomo20a/perdomo20a-supp.pdf).
RRM denotes repeated population risk minimization; RERM uses empirical risk,
and REGD uses empirical projected gradients.

## Proposition 3.6(c): compatible regularity constants

- **Arbitrary positive $\beta,\gamma$ → $0<\gamma\leq\beta$**
  (Proposition 3.6, p. 5). Strong convexity gives
  $\gamma|u-v|^2\leq(\ell'(u)-\ell'(v))(u-v)$; gradient smoothness bounds
  the right side by $\beta|u-v|^2$. Thus a nontrivial parameter interval
  requires $\gamma\leq\beta$.
- **The squared-loss example for equal constants →
  $\ell(z;\theta)=\gamma\theta^2/2-\beta z\theta$ for every compatible pair**
  (Appendix E.2). With $D(\theta)=\delta_{1+\epsilon\theta}$, RRM gives
  $G(\theta)=\beta/\gamma+(\beta\epsilon/\gamma)\theta$.
  At the paper's threshold $\epsilon\geq\gamma/\beta$, the multiplier is
  at least one and the intercept is positive, so the orbit from zero diverges.
  At equality, each step adds $\beta/\gamma$. Here $\delta_x$ is point mass at $x$.

## Proposition 3.6(a)--(b): concrete counterexample models

- **Part (b)'s unspecified large hinge penalty →
  $C=\gamma(\epsilon^{-2}+2)$**, with $a=-1/(2\epsilon)$ and parameter
  interval $[a,2]$. For every $\epsilon,\gamma>0$, this satisfies
  $\gamma(1-a)\leq2C\epsilon$ and $2\gamma\leq C$, making the frozen-risk
  minimizers alternate $2,a,2,a,\ldots$ in the source's regularized-hinge
  construction (Appendix E.2). This is a witness choice, not a population
  assumption.

## Theorem 3.10: dimension and adaptive uniformity

Source: Theorem 3.10, p. 6; Appendix E.4.

- **One printed all-dimension sample budget → separate checked routes, without
  the printed big-O formula.** The direct RERM route covers every positive data
  dimension with an explicit selected-shell schedule: inverse-square times one
  radius logarithm at $m=1$, inverse-square times a squared-radius logarithm
  at $m=2$, and the supercritical inverse-dimension power at $m>2$. The REGD
  route remains the explicit supercritical ($m>2$) schedule. Here $m$ is data
  dimension, $\epsilon$ distribution sensitivity, $\delta$ target distance,
  and $p$ total failure probability. A Bernoulli mass estimate fluctuates on
  scale $n^{-1/2}$, exactly its Wasserstein error on $\{0,1\}$, so the
  printed $r^{-1}$ sample dependence at $m=1$ does not supply accuracy $r.
  [Fournier–Guillin Theorems 1–2](https://arxiv.org/pdf/1312.2128) distinguish
  $m=1$, $m=2$ with a logarithmic correction, and $m>2$.
- **RERM regularity on $\Theta$ and $Z=\bigcup_{\theta\in\Theta}\operatorname{supp}D(\theta)$
  → the source-domain model carrier.** The recovered direct raw-$W_1$ RERM
  route uses its laws, loss integrability, A1/A2 lower model, sensitivity, and
  minimization only on the declared feasible domain. It does not retain the
  historical data-Lipschitz loss bridge. The separate RGD finite-sample route
  still records its older global analytic regularity boundary explicitly.
- **A finite exponential moment separately at each deployment → one common
  bound over every law reached along every adaptive history:**
  $$\int e^{\lambda\|z\|^\alpha}\,dD(\theta)(z)\leq K,
  \qquad\lambda>0,\quad\alpha>1+s,\quad0<s\leq1.$$
  Pointwise finiteness does not itself give a uniform $K$ for an adaptive
  sequence. This is a substantive uniformity premise of the current proof;
  the batch selector splits bounded-region and tail errors and allocates
  round failure budgets $6p/[\pi^2(t+1)^2]$. Necessity of the uniform bound
  under all source hypotheses is unresolved.
- **Explicit sample-count formula → dimension-regime schedules; logarithmic
  burn-in → recovered source-style entry threshold.** For contraction factor
  $q$, target radius $R$,
  sampling perturbation $e$, and outer factor $q\leq q_{\rm out}<1$, retain
  $$e\leq(q_{\rm out}-q)R,\qquad e\leq(1-q)R.$$
  These inequalities keep sampling noise within the contraction slack.
  The proof instantiates the source-style condition
  $$t_0\ \geq\ \frac{\log(d_0/R)}{1-q_{\rm out}}$$
  (with the RERM outer factor $2\epsilon\beta/\gamma$) and then keeps every
  later iterate within $R$ with probability at least $1-p$. The printed common
  all-dimension sample-count formula is not valid in every positive dimension;
  the proved dimension-regime schedules replace it.
- **RERM gradient regularity → direct minimizer perturbation, without a
  data-Lipschitz loss comparison.** The recovered RERM proof uses A1's
  data-gradient bound and A2's strong-convexity lower model to convert its raw
  $W_1$ event directly into a parameter perturbation. REGD instead uses
  $e=h\beta W$ for step $h\geq0$. Both branches retain the integrability and
  numerical tolerances their respective adaptive concentration constructions
  actually consume.

## Proposition 4.1: stable-point existence

- **Continuity of the loss and distribution map on the source domain
  $\Theta$ and support union $Z$ → joint continuity of the decoupled expected
  risk on $\Theta\times\Theta$.** This remains the explicit continuity bridge
  needed by the compact best-response proof. The current model is defined on
  $\Theta$, so it does not require a total off-domain law or loss extension;
  pointwise loss convexity is likewise imposed only on the feasible domain.
- **Compact $\Theta$ in the displayed proposition → nonempty compact convex
  $\Theta$.** Convexity is already part of the paper's global parameter-space
  setup, so making it explicit here adds no source-model restriction. A
  compact nonconvex example shows only that the displayed proposition would be
  false if read without that global setup.

## Proposition 4.2: valid Bernoulli probabilities

- **Only $|\mu+\epsilon|\leq1/2$ → also $|\mu|\leq1/2$** for the
  Appendix E.5 witness
  $Y\mid X\sim\mathrm{Bernoulli}(1/2+(\mu+\epsilon\theta)X)$,
  uniform $X\in\{-1,1\}$ and $\theta\in[0,1]$. Both endpoint bounds are
  needed for valid intermediate probabilities.
- **Valid parameters:** $\mu=-3/8$, $\epsilon=3/4$ give probabilities in
  $[1/8,7/8]$. With $f_\phi(x)=\phi x+1/2$ and squared loss,
  $$\operatorname{PR}(\theta)=\tfrac14+\tfrac34\theta-\tfrac12\theta^2.$$
  This is strictly concave although the loss is strongly convex and jointly
  smooth, giving the intended counterexample with a valid data law.

<a id="theorems-35-and-38-population-scope"></a>

## Theorems 3.5 and 3.8: recovered source-domain scope

- **The closed convex source parameter space $\Theta$ → the actual Lean
  parameter carrier.** `MeasurePerformativeModelOn` defines laws, losses, and
  expected risks only for admissible parameters. Theorem 3.5 now proves its
  transport contraction directly from on-domain A1/A2, loss integrability, and
  Wasserstein sensitivity; it has no off-domain or population-gradient
  integrability premise. Theorem 3.8 records expected-gradient integrability
  on $\Theta$ because that is the population update displayed in the source,
  then proves its projected contraction and rate on the same domain. This is a
  clarification of the paper's model domain, not an additional economic
  assumption or a change to either conclusion.
- **The source's finite-dimensional $Theta\subseteq\mathbb R^d$ → explicit
  finite-dimensional Lean parameter spaces.** Theorem 3.8 does not separately
  assume $\gamma\leq\beta$: A1/A2 derive it on every non-singleton domain;
  the singleton case satisfies the displayed conclusion directly.

## Historical all-ambient route for Theorems 3.5 and 3.8

- **A1, A2, Wasserstein sensitivity, and analytic conditions on the source
  domain $\Theta$ and support union $Z$ → the same conditions over every
  ambient parameter and every datum in the chosen Lean data carrier.** The
  prior targets also required expected-loss and gradient integrability for
  every ambient deployed/evaluated parameter pair, together with local loss
  measurability and pointwise parameter differentiation there. Their
  contraction, stability, and convergence conclusions remain restricted to
  $\Theta$. Making the model total outside $\Theta$ is a representation
  choice, and choosing the data carrier as $Z$ removes the apparent
  off-support strengthening. The parameter-global hypotheses still restrict
  the prior formalization beyond the paper; no derivation from the
  source-domain assumptions is proved, and necessity is unresolved.

<a id="corollary-51-whole-space-population-scope"></a>

## Corollary 5.1: recovered strategic source-domain scope

- **The strategic-classification corollary → its domain-relative strategic
  profile and Stackelberg benchmark.** The current endpoint keeps the source's
  closed convex parameter domain, induced distribution, selected response, and
  Stackelberg comparison. It obtains RRM convergence from the recovered
  domain-relative theorem and proves the displayed objective-gap upper bound.
  No whole-space extension or performative-optimum substitution is required.
- **The source's Euclidean parameter setting → an explicit
  finite-dimensional parameter-space binder.** This is a source specialization
  of a previously more-general Lean endpoint, not an added condition.

## Historical whole-space route for Corollary 5.1

- **RRM, performative optimality, stability, and regularity on the source's
  closed convex domain $\Theta$ → RRM, optimality, stability, A1, A2,
  Wasserstein sensitivity, loss Lipschitzness, integrability, measurability,
  and differentiation on the entire ambient parameter carrier.** The current
  prior target had no separate domain argument and started from any ambient initial
  point. Choosing the Lean data carrier as $Z$ can make its all-datum
  quantifiers source-relative; the whole-parameter-space restriction remains.
  No reduction from the source-domain corollary is proved, and necessity of
  this stronger scope is unresolved.

- **Strategic-classification Stackelberg conclusion → performative-optimum
  comparison.** The target does not identify the performative optimum with
  a Stackelberg equilibrium; that interpretation bridge remains unproved.
