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

<a id="lemma-c4-the-two-objective-comparisons"></a>

## Theorem 3.1 and Lemmas C.3–C.4: cross-bin ranking rates

- **Rate-comparison domain:** the paper's cross-bin reading is made explicit as
  $\beta_1\ne\beta_2$, where $\beta_i$ is item $i$'s assigned rating
  probability. Items in the same bin are not asymptotically distinguished by
  the rating system. For the paper's pair weight $w$ and signed ranking
  accuracy $P_k$, the limiting and finite objectives are
  $$
  W^{\mathrm{cross}}=\int_{\beta_1\ne\beta_2}w,\qquad
  W_k^{\mathrm{cross}}=\int_{\beta_1\ne\beta_2}wP_k.
  $$
  Therefore
  $$
  W^{\mathrm{cross}}-W_k^{\mathrm{cross}}
  =\int_{\beta_1\ne\beta_2}w(1-P_k),
  $$
  exactly the error quantity analyzed in Appendix C. Theorem 3.1 and Lemmas
  C.3–C.4 are formalized with this intended reading. No assumption that
  matching rates are constant within bins is needed.

- **Complement notation (supplement lines 1150–1171):** read
  $\bar P_k=1-P_k$ on cross-bin pairs, with zero contribution from same-bin
  pairs. Applying the complement formula to every pair would give a different
  quantity: identical score laws and counts have signed $P_k=0$, hence
  $1-P_k=1$. Nor can same-bin signed contributions always be canceled when
  counts differ: with common rating probability $1/3$, two samples beat one
  by signed ordering probability $2/27$. These observations explain the
  domain convention; they do not change the intended rate conclusion.

- **Two-level endpoint:** a real-valued rate formula for at least three
  rating levels → a separate extended-rate statement for two levels. Uniform
  positive matching rates make the two-level error eventually zero, so its
  exponential rate is $+\infty$. This is an endpoint clarification.
