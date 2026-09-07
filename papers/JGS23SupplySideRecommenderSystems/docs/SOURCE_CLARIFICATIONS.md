# Source Clarifications

Source: arXiv v3 of *Supply-Side Equilibria in Recommender Systems*
([arXiv:2206.13489v3](https://arxiv.org/abs/2206.13489v3)). This memo records only
material differences between the numbered source statements and the
formalized statements. A restriction is not claimed to be necessary without a
counterexample in the source domain.

Here \(N\) is the number of users, \(P\) the number of producers, and
\(\beta\) the cost exponent.

## One-dimensional law and genre convention

- **Corollary 1 and Lemma 3 — Typo.** Original:
  \(F(q)=(q/N)^{\beta/(P-1)}\) on \([0,N^{1/\beta}]\). Formalized:
  \(F(q)=(q^\beta/N)^{1/(P-1)}\), clipped to zero and one outside that
  interval, and the resulting equilibrium construction. Reason: the printed
  CDF generally does not equal one at \(q=N^{1/\beta}\).

- **Example 1 — Formalization gap.** Original: the displayed one-dimensional law
  is the unique symmetric mixed equilibrium. Formalized: the corrected law is
  a symmetric mixed equilibrium. Reason: the equilibrium calculation does not
  by itself establish uniqueness among all symmetric mixed laws. No
  source-domain counterexample establishes that uniqueness fails.

- **Theorem 1 and the paper's genre definition — Typo.** Original: normalize
  every point in topological support. Formalized: normalize each nonzero
  support point,
  \[
  G(\mu)=\{p/\lVert p\rVert:p\in\operatorname{supp}\mu,\ p\ne0\}.
  \]
  Reason: zero can belong to topological support when production approaches
  zero, and normalization is undefined there.

- **Lemma 4 — Formalization gap.** Original: the equilibrium genre lies in the
  span of the user vectors, with strictly positive user scores stated as a
  consequence. Formalized: strictly positive scores are derived directly from
  a single-nonzero-genre symmetric equilibrium with nonzero nonnegative users.
  Reason: span membership alone does not imply positive scores; for example,
  \(e_1\) lies in \(\operatorname{span}\{e_1,e_2\}\) but has zero score against
  \(e_2\). The separate span conclusion is not asserted.

## Single-genre optimization and thresholds

- **Lemmas 1 and 5--7 — Formalization gap.** Original: an unrestricted infimum or
  minimax formulation over score ratios. Formalized: an attained positive
  score vector \(y^*\) maximizes the coordinate product and satisfies
  \[
  \sum_i\frac{y_i}{y_i^*}\le N
  \]
  for every feasible score vector \(y\). Reason: positivity makes every ratio
  defined, and attainment supplies the optimizer used in the supporting
  inequality.

- **Lemma 8 — Formalization gap.** Original: for every nonempty
  \(R\subset(0,\infty)^N\), the displayed sup-inf ratio equals \(N\).
  Formalized: the value-\(N\) conclusion at an attained coordinate-product
  maximizer. Reason: the printed unrestricted statement does not hold on its
  full domain. Take \(N=1\) and \(R=(0,\infty)\). For every \(y'>0\),
  \(\inf_{y>0}y'/y=0\), so the displayed supremum is \(0\), not \(1\).

- **Corollaries 2, 3, and 5 — Formalization gap.** Original: conclusions packaged
  through the supremum threshold \(\beta^*\). Formalized: existence at
  \(\beta=1\); existence for every \(0<\beta\le q\) under the \(L^q\) route;
  and exclusion at a fixed exponent satisfying
  \[
  \beta>\frac{\log N}{\log N-\log Z},\qquad 1<Z<N.
  \]
  Here \(Z\) bounds the total user score of nonnegative content with norm at
  most one, after normalizing each user's maximum unit-content score to one.
  Reason: these are the pointwise consequences proved by the optimization
  route. They do not by themselves establish attainment of \(\beta^*\), the
  equality \(\beta^*=q\), or the extended endpoint when \(Z=N\).

- **Corollaries 4 and 6 — Typo.** Original: the printed one-population formula
  and normalization at every support point enter the two-user and welfare
  arguments. Formalized: the same conclusions use the corrected CDF and the
  nonzero genre convention above. Reason: these are the local corrections
  needed to make the displayed formulas defined; they do not narrow the
  economic conclusions.

## Two-user characterization, phase results, and profit

- **Lemma 2 — Additional premise; formalization gap.** Original: a generic
  necessary-and-sufficient C1--C3 characterization (support maximization,
  marginal-CDF compatibility, and realization by nonnegative content) written
  with strict CDFs. Formalized: under score-tie nullness, symmetric mixed Nash
  is equivalent to nonnegative support plus maximization, at every support
  action, of the actual payoff expressed through strict score CDFs. Reason: a
  CDF value alone does not encode a producer's share of a tie at an atom.
  Score-tie nullness is sufficient for the strict-CDF step; its necessity for
  every tie-aware characterization remains unresolved.

- **Theorem 2 and Propositions 9--10 — Formalization gap.** Original: the two-user
  phase statement is presented for general equal-population user vectors.
  Formalized: the selected endpoint uses
  \(u_1=(1,0)\), \(u_2=(\cos\theta,\sin\theta)\), and
  \(\beta_c=2/(1-\cos\theta)\). It proves the lower and upper phase conclusions
  under the score-law and radial regularity stated in the paper. Reason: the
  selected statement does not assert transport from every source user pair to
  this canonical realization. The restriction is not claimed to be
  necessary.

- **Lemma 9 — Formalization gap.** Original: the displayed Gram-form cost is the
  cost of every content vector with given scores in arbitrary dimension.
  Formalized: it is the minimum squared norm over a feasible score fibre in
  the canonical two-dimensional realization,
  \[
  \frac{z_1^2+z_2^2-2z_1z_2\cos\theta}{\sin^2\theta}.
  \]
  Reason: the arbitrary-dimensional identity does not hold for the following
  source-domain witness. Take nonnegative unit users
  \(u_1=(3/5,4/5,0)\), \(u_2=(3/5,0,4/5)\) and content
  \(p=(0,1,0)\). Its score pair is \((4/5,0)\) and its squared norm is \(1\),
  while the printed Gram quadratic is \(25/34\).

- **Lemma 10 — Formalization gap.** Original: the displayed cost derivatives are
  identified with equilibrium density derivatives. Formalized: the cost
  derivative identities. Reason: the equilibrium-to-density identification
  does not follow from the cost calculation alone and is not asserted.

- **Lemma 12 — Additional premise; formalization gap.** Original: when the
  two-user score support locally follows a differentiable graph
  \(z_2=g(z_1)\), support optimality (C1) is used to conclude
  \[
  g'(z_1)\left(\frac{\beta-2}{\beta}\cos(\theta-2\phi)-\cos\theta\right)\le0,
  \qquad (z_1,g(z_1))=(r\cos\phi,r\cos(\theta-\phi)).
  \]
  Formalized: this inequality follows from explicit differentiated
  first-order identities along the support graph and a negative-semidefinite
  payoff Hessian. Deriving those premises from equilibrium and C1 remains
  unproved; their necessity as economic assumptions is unresolved.

- **Propositions 7--8 — Formalization gap.** Original: positive and zero expected
  producer profit. Formalized: the corresponding conclusion for every support
  action; Proposition 7 uses the Euclidean norm and nonzero nonnegative users.
  Reason: passing from support-action payoff to expected profit requires the
  population-law and integrability bridge.

## Infinite-producer limit

- **Definition 1 — Typo.** Original: the product exponent is indexed by user
  although the weights are attached to genres. Formalized: genre weights,
  \[
  U(p)=\sum_i\prod_g
  F_g\!\left(\frac{u_i\cdot p}{u_i\cdot v_g}\right)^{w_g}-c(p),
  \qquad w_g\ge0,\quad\sum_gw_g=1,
  \]
  on the positive-denominator domain. Reason: the corrected indexing matches
  the genre mixture described by Definition 1.

- **Theorems 3--4 — Typo fixed; formalization gap.** Original: Theorem 3 states the
  two-genre construction for any two linearly independent nonnegative user
  vectors, while Theorem 4 defines
  \[
  \theta^*=\arccos\!\left(
    \frac{\langle u_1,u_2\rangle}{\lVert u_1\rVert_2\lVert u_2\rVert_2}
  \right)<0.
  \]
  Formalized: canonical users with \(0<\theta<\pi/2\) and
  \(\beta>2/(1-\cos\theta)\). Reason: the displayed arccosine is nonnegative
  on the source domain, so the printed strict-negative hypothesis has no
  instance. The checked result supplies the strictly acute construction; it
  does not assert the general-user or orthogonal endpoints. No counterexample
  establishes that the acute-angle restriction is necessary for every
  coherent infinite-producer theorem.

- **Theorem 4 genre weights — Typo.** Original:
  \(\alpha_1=\alpha_2=2\), despite Definition 1 requiring
  \(\alpha_1+\alpha_2=1\). Formalized:
  \(\alpha_1=\alpha_2=1/2\). Reason: the formalized weights define the stated
  equal two-genre probability mixture.

- **Theorem 4 quality-cap constant — Typo.** With user angle \(\theta\),
  maximizing genre angle \(\phi\), and
  \(C_2=\cos(\theta-\phi)/\cos\phi\), the CDF constant changes from
  \[
  C_1=\frac{\sin\theta\cos\phi}{\sin(\theta-\phi)}
  \quad\longrightarrow\quad
  C_1=\frac{\sin\theta}{\cos\phi\sin(\theta-\phi)}=1+C_2^\beta.
  \]
  Reason: at the upper support quality \(a=C_1^{1/\beta}\), a genre has total two-user gross payoff \(1+C_2^\beta\) and pays cost \(a^\beta=C_1\). Equality gives the zero
  payoff required by support approaching zero. The paper's first-order identity
  for \(\phi\) gives the displayed equality to \(1+C_2^\beta\).
