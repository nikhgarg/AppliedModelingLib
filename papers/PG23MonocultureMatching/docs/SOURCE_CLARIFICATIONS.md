# PG23 Source Clarifications

## Cutoff probabilities and support arguments

- **Equal Cutoffs (including differential access): connected support → also
  zero probability of every exact score level.** Connected support alone
  permits atoms: half point mass at zero plus half uniform mass on $[0,1]$
  has $\Pr(Z=0)=1/2$. This refutes only the inference to zero boundary mass.
- **Probability Formula and Theorems 1--2: add atomless noise** to identify
  the source's strict-tail formulas with its weak matching events:
  $$\Pr(v+X\geq P)=\Pr(v+X>P).$$
  Without atomlessness, their difference is $\Pr(X=P-v)$. The formalized
  Theorems 1--2 state the weak events and prove this identification.
- **Theorem 3: add atomless values** to derive the equality of baseline
  and differential monoculture cutoffs from market clearing. Necessity for
  the source conclusion is unresolved; no counterexample is known here.
- **Corollary 4 and the strict Theorem 1--2 comparisons: add nondegenerate
  noise.** The proof uses two distinct support points; necessity of the full
  regularity package for the source conclusions is unproved.
- **Unqualified appendix intervals/endpoints → nonempty open intervals
  meeting the support interior.** A singleton has zero uniform mass, while
  an endpoint atom can make the lower-endpoint CDF positive. The interior
  argument also permits unbounded support.

## Welfare and the application game

- **Theorem 1: add absolute integrability of value and atomless values** for
  the welfare limit and strict comparison. Necessity for the broader theorem
  is unproved. Theorem 2's eventual-advantage branch also uses atomless values.
- **Differential-access Nash sentence → ex-ante expected payoffs over
  same-cardinality application sets**, with ranking-monotone utility and
  the equal-cutoff success law. The current incentive result does not cover
  unrestricted application counts or different information timing.

## Uniform maximum-concentration example

- **Footnote means $1-n/(n+1)$ and $(n-1)/n$ →
  $\mathbb E[X^{(n)}]=n/(n+1)$; Chebyshev
  denominator $\varepsilon$ → $\varepsilon^2$.** Here $X^{(n)}$ is the
  maximum of $n$ iid uniform-$[0,1]$ draws. Its variance is
  $n/[(n+1)^2(n+2)]$, so the corrected tail bound is
  $n/[\varepsilon^2(n+1)^2(n+2)]\to0$ for every $\varepsilon>0$.
  The illustrative maximum-concentration conclusion follows; this is not a
  premise of the named results.
