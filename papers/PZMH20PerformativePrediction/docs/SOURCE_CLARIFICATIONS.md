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

- **All dimensions with sample budget
  $n_t=O((\epsilon\delta)^{-m}\log(t/p))$ → $m>2$ and an explicit sufficient
  batch selector, without the printed big-O budget.** Here $m$ is data
  dimension, $\epsilon$ distribution sensitivity, $\delta$ target distance,
  and $p$ total failure probability. A Bernoulli mass estimate fluctuates on
  scale $n^{-1/2}$, exactly its Wasserstein error on $\{0,1\}$, so the
  displayed $r^{-1}$ sample dependence at $m=1$ does not supply accuracy $r$.
  [Fournier–Guillin Theorems 1–2](https://arxiv.org/pdf/1312.2128) distinguish
  $m=1$, $m=2$ with a logarithmic correction, and $m>2$.
- **Regularity on $\Theta$ and $Z=\bigcup_{\theta\in\Theta}\operatorname{supp}D(\theta)$
  → regularity on the entire parameter and data spaces.** A1/A2 hold for all
  parameter/data pairs; sensitivity, loss/gradient integrability, and loss
  differentiation hold for all ambient parameters. RERM's data-Lipschitz loss
  bound is global too. This restricts the models covered by the current proof;
  necessity of the stronger scope is unresolved.
- **A finite exponential moment separately at each deployment → one common
  bound over every law reached along every adaptive history:**
  $$\int e^{\lambda\|z\|^\alpha}\,dD(\theta)(z)\leq K,
  \qquad\lambda>0,\quad\alpha>1+s,\quad0<s\leq1.$$
  Pointwise finiteness does not itself give a uniform $K$ for an adaptive
  sequence. This is a substantive uniformity premise of the current proof;
  the batch selector splits bounded-region and tail errors and allocates
  round failure budgets $6p/[\pi^2(t+1)^2]$. Necessity of the uniform bound
  under all source hypotheses is unresolved.
- **Explicit sample-count and burn-in formulas → sufficient error budgets
  and some finite entry time.** For contraction factor $q$, target radius $R$,
  sampling perturbation $e$, and outer factor $q\leq q_{\rm out}<1$, retain
  $$e\leq(q_{\rm out}-q)R,\qquad e\leq(1-q)R.$$
  These inequalities keep sampling noise within the contraction slack.
  The proof derives a finite $t_0$ after which the iterates stay within $R$ with
  probability at least $1-p$. Matching the paper's displayed sample-count
  and logarithmic burn-in bounds remains unproved.
- **RERM gradient regularity alone → an additional data-Lipschitz loss
  comparison:** for loss constant $L_z$, Wasserstein tolerance $W$, and
  risk tolerance $\tau$, require $L_zW\leq\tau$ and use
  $e=\sqrt{4\tau/\gamma}$. Strong convexity converts risk error to parameter
  error; gradient smoothness alone does not give this loss-Lipschitz premise.
  REGD instead uses $e=h\beta W$ for step $h\geq0$. Both branches need
  integrable sampled quantities and tolerances fitting the concentration
  selector's bounded-region and tail budgets. Necessity of these current-proof
  premises is unresolved.

## Proposition 4.1: stable-point existence

- **Continuity of the loss and distribution map on the source domain
  $\Theta$ and support union $Z$ → expected-loss integrability for every
  ambient deployed/evaluated parameter pair and joint continuity of the
  decoupled expected risk on the full ambient parameter product.** The current
  target also requires loss convexity on $\Theta$ for every datum in the
  chosen data carrier. Defining a total model outside $\Theta$ is a
  representation choice, and taking the data carrier to be $Z$ makes the
  all-datum quantifier source-relative. The global integrability and
  continuity conditions still constrain the off-domain extension; they are
  sufficient for the current fixed-point proof, and their necessity is
  unresolved.
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

## Theorems 3.5 and 3.8: population scope

- **A1, A2, Wasserstein sensitivity, and analytic conditions on the source
  domain $\Theta$ and support union $Z$ → the same conditions over every
  ambient parameter and every datum in the chosen Lean data carrier.** The
  current targets also require expected-loss and gradient integrability for
  every ambient deployed/evaluated parameter pair, together with local loss
  measurability and pointwise parameter differentiation there. Their
  contraction, stability, and convergence conclusions remain restricted to
  $\Theta$. Making the model total outside $\Theta$ is a representation
  choice, and choosing the data carrier as $Z$ removes the apparent
  off-support strengthening. The parameter-global hypotheses still restrict
  the current formalization beyond the paper; no derivation from the
  source-domain assumptions is proved, and necessity is unresolved.

<a id="corollary-51-whole-space-population-scope"></a>

## Corollary 5.1: whole-space population scope

- **RRM, performative optimality, stability, and regularity on the source's
  closed convex domain $\Theta$ → RRM, optimality, stability, A1, A2,
  Wasserstein sensitivity, loss Lipschitzness, integrability, measurability,
  and differentiation on the entire ambient parameter carrier.** The current
  target has no separate domain argument and starts from any ambient initial
  point. Choosing the Lean data carrier as $Z$ can make its all-datum
  quantifiers source-relative; the whole-parameter-space restriction remains.
  No reduction from the source-domain corollary is proved, and necessity of
  this stronger scope is unresolved.

- **Strategic-classification Stackelberg conclusion → performative-optimum
  comparison.** The target does not identify the performative optimum with
  a Stackelberg equilibrium; that interpretation bridge remains unproved.
