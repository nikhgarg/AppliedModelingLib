# Source Clarifications

## Theorem 3.1: variance at Bernoulli endpoints

- Strictly decreasing conditional variance on `0<=q_v<=1` → weak decrease on that interval and strict decrease only for `0<q_v<1` under a strict prior-strength increase (Theorem 3.1 and Appendix A). Here `q_v` is true quality. At `q_v=0` or `1`, the Bernoulli variance is zero for every prior strength, so strict decrease fails.

## Appendix D, Equation (20): Beta prior shape

- `Beta(C,1)` → `Beta(C,1-C)`. With prior strength `m>0` and `0<C<1`, the scaled law is `Beta(m C,m(1-C))`, yielding the displayed posterior mean `(k+m C)/(n+m)` after `k` positive reviews among `n` observations.

## Appendix E, Equation (21): Dirichlet posterior average

- The count-only average → `sum_j (alphaHat_j+N_j) r_j / sum_j (alphaHat_j+N_j)`, where `alphaHat_j` are prior pseudo-counts, `N_j` observed counts, and `r_j` rating scores. The Dirichlet update requires the prior terms. Zero prior weight recovers the count-only formula algebraically when the observed total is positive, but all-zero shapes do not define a proper Dirichlet prior.
