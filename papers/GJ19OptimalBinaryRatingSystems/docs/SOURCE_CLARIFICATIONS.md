# Source Clarifications: GJ19 Optimal Binary Rating Systems

Source line numbers refer to the retained publication text and supplement.

## Local formulas and proof clarifications

- **KL footnote 6, main lines 519–526:** $a\log(b/a)+(1-a)\log((1-b)/(1-a))$ →
  $a\log(a/b)+(1-a)\log((1-a)/(1-b))$. Both ratios are reversed.
  The latter is the standard nonnegative divergence used in the proof; this
  is a local sign clarification, with no added premise.
- **C.5 endpoints, Appendix C lines 1593–1599:** repeated $t_0=1$ →
  $t_{M-1}=1$, alongside $t_0=0$, for an $M$-level rating vector.
- **Algorithm 1, Appendix B lines 779–837:** outer midpoint →
  $j_{M-2}=(u+\ell)/2$, where $u,\ell$ are the current bounds; both endpoint
  rates use the candidate vector, and the final helper call includes its
  target-rate argument. The main-paper description determines these choices.
- **First endpoint rate, Appendix C lines 2206–2226:**
  $-g_1\log t_1$ → $-g_1\log(1-t_1)$, where $g_1$ is the first matching rate
  and $t_1$ the first interior level.
- **Lower-bound notation, Appendix C lines 1586–1597:**
  $t_1\ge O(M^{-3})$ is read as $t_1\ge c/M^3$ for some fixed $c>0$.
  This is an intermediate lower bound on the first positive rating level;
  Theorem 3.2's big-$O$ runtime is unchanged.
- **Uniformity, Appendix C lines 1081–1141:** full-square uniform rate
  convergence → separated-cell or weighted essential-infimum arguments.
  The full-square claim fails near the diagonal; the rate proof uses the
  separated domain.
- **Remark C.2, Appendix C lines 1321–1325:** joint strict convexity →
  interior continuity, zero value on the diagonal, positivity off it, and
  strict coordinatewise separation. Multiple diagonal minima preclude joint
  strict convexity.

## Theorem 3.2: an explicit grid and runtime bound

- **Same asymptotic runtime, with explicit constants:** the finite operation
  bound gives the paper's $O(M\log^2(M/\epsilon))$ rate for $M$ rating levels and additive error
  $0<\epsilon\leq1$. The paper bounds matching rates above and away from
  zero; for a fixed matching function, the proved grid spacing $\delta$ has
  $1/\delta=O(M^2/\epsilon)$, yielding that operation count.
- **Endpoint scope:** the displayed formalized runtime theorem covers $M>3$
  levels. Its explicit count is
  $M[\log_2(\max\{1,1/\delta\})+2]^2$; this is a refinement of the
  runtime rate, not a slower asymptotic guarantee.

## Lemma C.4: the two objective comparisons

- **Paper:** the gap between limiting and current ranking quality, $W-W_k$,
  decays exponentially at a positive rate if and only if the rating rule uses
  finitely many probability levels.
- **Formalized:** the finite-level positive-rate proof omits pairs assigned
  the same level; the other direction proves zero rate for a separately
  defined pairwise-error integral.
- **Missing proof:** connect both integrals to $W-W_k$ and establish the
  adjacent-rate formula in Theorem 3.1, equation (3) (main lines 487–517).
  Equal assigned rating probabilities need not make a pair's finite-sample
  ranking contribution zero when sample counts differ: with common probability
  $1/3$, two samples beat one by signed ordering probability $2/27$.
  Erasing those pairs therefore needs a proof. This finite-sample example does
  not refute the paper's asymptotic characterization.
- **Two-level endpoint:** the formalized optimization covers $M\ge3$.
  With two deterministic endpoint levels, cross-cell separation has infinite
  rate, which the current real-valued rate formula does not represent.
