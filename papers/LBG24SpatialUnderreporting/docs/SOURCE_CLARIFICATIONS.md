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

- **Source → formalized:** Appendix Theorem 2, Condition 1 selects a start
  after a realized first report within the observation window. The current
  Lemma 2 model instead requires an unconditional exponential first arrival
  to lie before a fixed finite horizon $H$ for every outcome.
- **Why this needs repair:** for reporting rate $\lambda>0$, the exponential
  law gives $P(T_1>H)=e^{-\lambda H}>0$, contradicting that bound. No process
  satisfies both premises, so the Lemma 2 and Appendix D.8.2 proofs do not
  establish the source claims.
- **Scope:** the main likelihood-factorization proof uses a separate causal
  observation model. This finding concerns the formalization's conditioning,
  not a counterexample to the paper's waiting-time result.
