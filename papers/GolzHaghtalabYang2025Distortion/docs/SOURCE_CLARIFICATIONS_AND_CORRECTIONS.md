# Source Clarifications and Corrections

Source: Gölz, Haghtalab, and Yang, *Distortion of AI Alignment: Does Preference
Optimization Optimize for Preferences?*, [arXiv:2505.23749](https://arxiv.org/abs/2505.23749).

## Theorem 5 and Theorem 12 optimization notation

- **A maximum over $0<\gamma<1$ → every strict sub-bound below a coefficient
  attained by that parameterized construction.** Theorem 12's formal Appendix
  version supplies Theorem 5's informal lower-bound optimization without
  asserting that a maximum is attained on the open interval.

## Theorem 6 proof arithmetic

- **Appendix F.2 sigmoid increment $3\delta$ → $\delta/3$**, where $\delta$
  is the construction parameter defined below.
- **Asymptotic $e^{\Omega(\beta)}$ → the explicit tail $\beta\geq10$.** The
  theorem asserts a large-$\beta$ rate, so it needs a concrete tail witness,
  not a uniform finite-$\beta$ inequality. The checked construction uses
  $\beta\geq10$; its auxiliary $e^\beta\geq100$ estimate follows from that
  cutoff and is an internal proof fact, not a second theorem premise.
  Together with the finite copy count below and reference mass below both
  welfare thresholds, these sufficient choices prove the stated
  $e^\beta/(44\beta)$ distortion lower bound eventually for literal iid
  reports.
- **Positive sign claimed for $\log(1-\epsilon)$ → use
  $\log(1/(1-\epsilon))>0$**, for the reference-mass parameter
  $0<\epsilon<1$ in the KL argument.

## Theorem 6 sequence size

- **“For $m\geq3$” → a sequence whose every finite instance has
  $m(\beta)\geq3$.** The theorem concerns a sequence as $\beta$ grows, and
  Appendix F.2 itself requires $m-2\geq4e^\beta$. Its construction therefore
  makes the choice-set size depend on $\beta$, rather than asserting a new
  fixed-$m$ lower bound. The checked finite construction uses
  $$\delta(\beta)=\frac{10}{10+e^\beta},\quad
  \operatorname{copies}(\beta)=
  \left\lceil\frac2{\delta(\beta)(1/3-e/10)}\right\rceil,\quad
  m(\beta)=\operatorname{copies}(\beta)+2,$$
  where $e$ is Euler's number. This replaces the insufficient unrestricted
  lower-bound argument for the copy count. It gives $m(\beta)\geq3$ in every
  sequence instance and the stated exponential tail; a separate fixed-$m$
  theorem is neither needed nor claimed here.

## Proposition 13 KL sign

- **Appendix F.4 minimizing-player negative KL penalty → positive penalty.**
  Equation (15), the preceding best-response inequality, and the Lagrangian
  require this sign in the constrained-to-regularized direction.

## Appendix F.3 DPO--RLHF equivalence

- **$\pi_{\rm ref}(x)e^{r^*(x)/\beta}$ → divide by its sum over $x$.**
  Here $r^*$ is a Bradley–Terry maximum-likelihood reward, defined only up to
  an additive constant. Its normalized exponential tilt is invariant to that
  constant and equals the DPO policy and regularized RLHF optimizer when the
  temperature and regularization weights satisfy $\beta=\lambda$. The
  missing normalizer is a formula correction, not an added theorem premise.

## Empirical Borda finite zero-incidence convention

- **Undefined quotient when an alternative has no sampled comparisons →
  Borda score zero.** The source's finite-report welfare expectation includes
  this event. The convention completes that finite rule; it assigns a zero
  win rate, not the indifference score $1/2$.

## Corollary 4 finite zero-incidence convention

- **Undefined pairwise margin when an off-diagonal pair was never sampled →
  neutral antisymmetric margin zero**, followed by an exact equilibrium of
  the finite zero-sum game. This completes the Maximal-Lotteries rule on an
  event included in the source's finite-sample expectation.
