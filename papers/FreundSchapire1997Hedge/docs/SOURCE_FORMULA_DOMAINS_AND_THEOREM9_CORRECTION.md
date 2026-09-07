# Source Formula Domains

Source: Freund and Schapire, [*A Decision-Theoretic Generalization of On-Line
Learning and an Application to Boosting*](https://doi.org/10.1006/jcss.1997.1504).

## Lemma 1 and Theorem 2: the Hedge parameter endpoints

- **Algorithm-box $\beta\in[0,1]$ → $0<\beta\leq1$ in Lemma 1 and
  $0<\beta<1$ in Theorem 2.** At $\beta=0$, a positive-loss round can zero
  every weight, leaving the normalized allocation undefined. Theorem 2 also
  uses $\log\beta$ and divides by $1-\beta$.

## Lemma 4: the zero-loss-bound extension

- **Undefined tuning formula at $\overline L=0$ → its continuous extension
  $\beta=0$.** Here $\overline L$ bounds cumulative loss. The inequality in
  this branch reduces to $R\leq R$, where $R$ is the comparator term. The
  source specifies no endpoint convention for its division or $L\log\beta$.

## Theorem 5: the tuned Hedge parameter

- **Unqualified $\beta=g(\widetilde L/\log N)$ → $N\geq2$ and
  $\widetilde L>0$**, where $N$ is the expert count, $\widetilde L$ the loss
  bound, and $g(z)=1/(1+\sqrt{2/z})$. Otherwise a denominator in the tuning
  formula is zero. These restrictions are needed for that displayed formula;
  necessity for the regret guarantee is not claimed (one expert is trivial).

## Theorem 6: endpoint errors

- **Prose error range $\epsilon_t\in[0,1]$ → $0<\epsilon_t<1$ for executed
  Figure 2 rounds.** At zero error, $\log(1/\beta_t)$ is not finite and
  normalization can fail; at unit error, $\beta_t=\epsilon_t/(1-\epsilon_t)$
  divides by zero. An endpoint execution needs a stopping or limiting rule
  absent from the display. This is a definedness issue, not a counterexample
  to the bound with a suitable endpoint convention.

## Theorems 10--12: endpoint errors in the variant algorithms

- **Undefined executed-round endpoints in Figures 3–5 →
  $0<\epsilon_t\leq1/2$ for M1 and AdaBoost.R, and $0<\epsilon_t<1$ for M2.**
  The excluded endpoints have the quotient/logarithm problems above; the
  upper-half stopping regime of M1 and AdaBoost.R is already in the source.
