# Source clarifications

Source: [official arXiv version](https://arxiv.org/pdf/2204.08620), main model
and Appendices B.1–B.2, C.2.

## Lemma 1 and Proposition 1: calendar-time first reports

- **Birth-window eventual reports → first reports inside the calendar-time
  window.** An incident born earlier can count if first reported inside the
  window. The proof must therefore displace retained incident births by their
  first-report delays, rather than only thin births. The stationary marked
  displacement theorem gives the observed homogeneous Poisson process.
- **Proposition 1 nonidentifiability construction → positive observed rate.**
  This makes its two compensating latent incident rates positive. The
  zero-detection process is covered separately by Lemma 1.

## Appendix B.2: likelihood-factorization algebra

- **Condition 1: point probability → conditional density.** In continuous
  time, read the displayed $P(S=t)$ as a density $g(s\mid T_1)$ for the
  selected start $S$, given the first report time $T_1$. The density
  integrates to one, does not depend on the reporting rate, and selects a
  start between $T_1$ and the observation horizon $T$ when $T_1\le T$.
  The likelihood uses its value at the observed start. This preserves the
  paper's selection rule and independence from subsequent reports.
- **Equation (30) first post-start gap → $t_{m+1}-s$**, where $s$ is the
  selected start after report $m$ and $t_{m+1}$ the next report time.
- **Equation (31) residual normalization → multiply by $M!/(e-s)^M$**, where
  $M$ is the post-start count and $e$ the endpoint. This converts
  $\lambda^Me^{-\lambda(e-s)}$ into the Poisson count mass with mean
  $\lambda(e-s)$. It repairs the algebra without changing the likelihood
  factorization. For a history-responsive endpoint, that factor alone is not
  a Poisson law conditional on the endpoints: the residual records selection.

## Equation (3): rate-estimation convention

- **Count-over-exposure estimator → nonnegative rates and strictly positive
  total exposure.** A zero count then has the attained maximum-likelihood
  estimate zero, rather than an unattained positive-rate limit.


## Lemma 2: conditioning on an observed first report

- **Observed first report:** condition on the actual first report, then select
  a start between that report and the observation horizon. The subsequent
  interarrival times are independent exponential draws. This proves the
  waiting-time conclusion in Lemma 2 and the shifted-process result in
  Appendix D.8.2.
- The first report need not occur before the horizon on every possible path;
  the claim concerns paths on which it has been observed. This is a
  conditioning convention, not an additional behavioral assumption.
