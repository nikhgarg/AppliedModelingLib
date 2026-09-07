# Source Clarifications

Source: Kleinberg and Raghavan, [*Algorithmic Monoculture and Social
Welfare*, arXiv v2](https://arxiv.org/abs/2101.05853).

## Noise normalizations and ranking laws

- **Section 3.1 Gumbel weights $e^{\theta x_i}$ →
  $e^{(\pi/\sqrt6)\theta x_i}$ under unit-variance noise.** Here $x_i$ is
  candidate value and $\theta$ ranking accuracy. A Gumbel scale $s$ gives
  weights $e^{\theta x_i/s}$; unit variance requires $s=\sqrt6/\pi$.
  The ranking family is unchanged after rescaling accuracy, but equal
  numerical parameters otherwise denote different noise levels (source lines
  497–540). The unit-variance specialization assumes the standard identity
  $\operatorname{Var}(-\log T)=\pi^2/6$ for $T\sim\mathrm{Exp}(1)$;
  that special-value identity is not proved here.

## Strictness and candidate-domain readings

- **Theorem 3 strict welfare conclusion → at least three candidates.** With two firms and two candidates
  of values $(1,0)$, both are
  hired and total welfare is always $1$, precluding strict welfare loss from
  shared rankings.
- **Theorem 5 differentiable full-support density → global absolute
  continuity with an integrable almost-everywhere derivative
  ($f\in W^{1,1}$).** This sufficient replacement permits differentiation of
  translated densities in $L^1$ and covers Gaussian and Laplace noise,
  including Laplace's corner (source lines 784–817). Smooth full support alone
  permits narrow paired density peaks whose difference distribution has an
  infinite derivative at a positive gap; the [explicit counterexample](THEOREM5_SMOOTH_DENSITY_COUNTEREXAMPLE_2026-07-24.pdf)
  has mean zero and variance one. It is a mathematical argument, not a
  Lean-checked counterexample. Necessity of the sufficient $W^{1,1}$ condition
  remains unresolved.
- **Appendix C Lemma 1:** the global strict Laplace comparison becomes weak
  globally and strict on overlap; the [four-point calculation](LAPLACIAN_SOURCE_CLARIFICATION.md)
  gives the exact change and replacement argument.
- **Appendix F Lemma 4 weakly decreasing likelihood ratio → a strict ratio
  comparison at some ordered pair** for the strict expectation inequality
  $\sum_i p_iy_i<\sum_i q_iy_i$, with increasing outcomes $y_i$ and positive
  normalized weights $p_i,q_i$. If “decreasing” is weak, $p=q$ gives equality;
  if strictness was intended, this makes its witness explicit.

## Appendix algebra and sequential experiments

- **Appendix C.1:** $h'\ge0$ everywhere and $h'>0$ somewhere, with
  $h(a)\to L$, imply $h(a)\le L$, not $h(a)<L$ at every finite cutoff.
  A function may reach its limit and then stay constant. The Laplace proof
  establishes each finite-cutoff strict gap directly; the Gaussian proof
  establishes $h'>0$ at every cutoff (source lines 1134–1148).
- **Theorem 4's sequential experiment:** each firm chooses before candidates
  are exhausted ($k<n$ for $k$ firms and $n$ candidates), with a fresh independent
  human ranking drawn after the remaining set is fixed. This is the source
  proof's setting; its strict comparison requires a choice of candidates
  (source lines 620–631, 3176–3180).
- **Appendix C Gaussian product comparison → Definition 4's direction:**
  the log-product cross difference is positive for $a>b,c>d$.
- **Appendix C.9:** $g(t)\delta\sqrt\pi+1/g(t+\delta)-1$ →
  $g(t)[\delta\sqrt\pi+1/g(t+\delta)]-1$. Here $g(t)=(1+\operatorname{erf}(t))e^{t^2}$,
  $\operatorname{erf}$ is the Gaussian error function, and
  $\delta=x_i-x_j>0$ in the source normalized coordinates.
  The missing multiplication changes the finite expression.
- **Appendix D.1 cross inequality → the direction of its preceding increasing
  likelihood-ratio calculation**, with ranking mass proportional to
  $\phi^{-\mathrm{distance}}$ and inverse-accuracy parameter $q=\phi^{-1}$.
- **Appendix E.3 swapped term:**
  $-\phi^{-(|i-j|+1)}\Pr[\tau_1=x_i]$ → the same term with a plus sign,
  as in the next display. Here $\tau_1$ is the first-ranked candidate.

## Representation boundaries

- **Finite-support and simulation remarks → no unrestricted formal theorem.**
  Finite computations and the multi-firm numerical example establish neither
  all finite-support noise extensions nor a general complexity guarantee.

- **Theorem 2's “any candidate distribution $D$” → an outer law with ordered
  support and defined ranking/payoff expectations.** The checked Gaussian and
  Laplace result uses candidate values that are strictly ordered almost surely,
  have finite first moments, and give measurable ranking probabilities and
  well-defined conditional and payoff expectations. These conditions make the
  source's Definitions 2--3 meaningful for an outer distribution; the source
  does not enumerate them in its Theorem 2 statement.

- **Equation (6) regularity on ordered source support → regularity of the
  supplied ranking family on every value profile** in the current endpoint.
  This is a current proof restriction outside source-supported profiles.
  Necessity of the stronger total-family input is unresolved.

## Theorem 1: strict-improvement domain

- **Definition 1 full-set strictness → the standing strictly ordered candidate
  values.** The source fixes $x_1>\cdots>x_n$ before stating Definition 1 and
  Theorem 1 (lines 133--138 and 244--246). Its strict comparison is therefore
  evaluated on those ordered candidate profiles, including when values are
  drawn from $D$; it is not a condition on profiles with tied candidate values.
  The formalized Theorem 1 uses that same source domain.
