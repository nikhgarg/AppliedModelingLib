# Source Clarifications

## Proposition 2: pairwise rate and finite-sample bound

- **One-sided support:** if the score gap is nonnegative and has zero-gap
  probability $p_0>0$, the rate is $-\log p_0$ and the error probability is
  $p_0^N$. If every positive-mass gap is strictly positive, errors vanish for
  every positive $N$; this is represented by extended rate $+\infty$.

## Proposition 4: outcome rate and $M^2$ bound

- **One-sided pairs:** a zero-gap pair contributes rate $-\log p_0$; an
  eventually error-free pair contributes extended rate $+\infty$ and cannot
  lower the minimum. This includes score gaps with no negative realization.
