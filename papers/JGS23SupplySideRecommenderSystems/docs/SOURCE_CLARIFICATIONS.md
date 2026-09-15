# Source Clarifications

Source: arXiv v3 of *Supply-Side Equilibria in Recommender Systems*
([arXiv:2206.13489v3](https://arxiv.org/abs/2206.13489v3)). This memo records only
material differences between the numbered source statements and the
formalized statements. A restriction is not claimed to be necessary without a
counterexample in the source domain.

Here $N$ is the number of users, $P$ the number of producers, and
$\beta$ the cost exponent.

## Clarified regularity and notation

For the two-user C1 results below, the paper's definition of C1 in
`arxiv-update.tex:680-690` is read literally: each $H_i$ is a distribution
function on $\mathbb R_{\geq 0}$, hence monotone, and
$S\subseteq\mathbb R_{\geq 0}^N$.  These are regularity conditions already
present in the source setup, not additional economic restrictions.  In Lemma
12, the free angular symbol in the displayed bracket is the polar parameter
$\phi$ of the score pair
$(r\cos\phi,r\cos(\theta^*-\phi))$; the curve's bound variable is its
first coordinate.  This resolves only notation and does not change the
conclusion or its domain.

## One-dimensional law and genre convention

- **Corollary 1 and Lemma 3 — Typo.** Original:
  $F(q)=(q/N)^{\beta/(P-1)}$ on $[0,N^{1/\beta}]$. Formalized:
  $F(q)=(q^\beta/N)^{1/(P-1)}$, clipped to zero and one outside that
  interval, and the resulting equilibrium construction. Reason: the printed
  CDF generally does not equal one at $q=N^{1/\beta}$.

- **Example 1 — Exact.** In the one-user, one-dimensional Euclidean model,
  the displayed power-law measure is the unique symmetric mixed equilibrium.

- **Theorem 1 and the paper's genre definition — Exact with a normalization
  convention.** Normalize each nonzero
  support point,
  $$
  G(\mu)=\{p/\lVert p\rVert:p\in\operatorname{supp}\mu,\ p\ne0\}.
  $$
  Zero can belong to topological support when production approaches zero;
  the zero vector is left unnormalized.

- **Lemma 4 — Positive-score conclusion exact; span wording corrected.**
  Original: the equilibrium genre lies in the span of the user vectors, with
  strictly positive user scores stated parenthetically.  A checked
  counterexample to the span wording uses the paper's stated arbitrary-norm
  domain (model definition, `arxiv-update.tex:268–274`): with one
  user $(1,2)$, two producers, $\ell_1$ cost, exponent one, and singleton
  genre $(0,1)$, the constructed ray law is a source symmetric mixed Nash
  equilibrium and has user score $2$, but $(0,1)$ is not in the span of
  $(1,2)$. Against the uniform ray $(0,Q)$, $Q\sim U[0,1]$, a deviation
  $(a,b)\ge0$ has payoff $\min(1,a/2+b)-a-b\le0$; each ray action in
  support has payoff zero. Thus the example satisfies the actual Nash model,
  not merely a relaxed optimization condition. The lemma's introductory
  sentence and proof (`arxiv-update.tex:956–963`) establish the
  positive-score conclusion directly from a single-nonzero-genre symmetric
  equilibrium, nonzero nonnegative users, and perturbation-cost continuity.

## Single-genre optimization and thresholds

- **Lemmas 1 and 5--7 — Source regularity made explicit.** The score-ratio
  optimization uses a positive score vector $y^*$ that attains the
  coordinate-product maximum and satisfies
  $$
  \sum_i\frac{y_i}{y_i^*}\le N
  $$
  for every feasible score vector $y$. Reason: positivity makes every ratio
  defined, and attainment supplies the optimizer used in the supporting
  inequality.

- **Lemma 8 — Exact with bounded-product regularity.** The abstract display
  states that the sup-inf ratio equals $N$ for every nonempty
  $R\subset(0,\infty)^N$.
  The proof's product-maximization argument needs a finite positive product
  supremum; the checked version uses an attained maximum. The paper's
  bounded norm-ball score-set application supplies this regularity. The
  abstract phrase “every set” also includes $N=1$, $R=(0,\infty)$, where
  every inner infimum is zero. That unbounded example explains the omitted
  qualification in the abstract lemma; it does not refute the source market
  application. Attainment is sufficient and is not asserted necessary.

- **Corollary 2 — Exact.** Original:
  $\beta^*\ge1$. Formalized: the source product-condition definition of
  $\beta^*$ contains exponent one under the stated compact convex source-norm
  regularity, as well as yielding the explicit single-ray equilibrium at
  $\beta=1$.

- **Corollary 3 — Exact with a dimension clarification.**
  Original: $\beta^*\ge q$ for $\ell_q$ cost, with equality for standard
  basis users. Formalized: $q$ belongs to the source product-condition
  exponent set, so $\beta^*\ge q$, and the construction gives the stated
  singleton equilibrium for every $0<\beta\le q$. For the standard basis
  with at least two users, the opposite strict product gap above $q$ gives
  the exact equality $\beta^*=q$. The source should state that nontrivial
  dimension: with only one basis user, the powered score image remains an
  interval for every exponent and the threshold is unbounded rather than
  equal to finite $q$.

- **Corollary 5 — Exact with regularity conditions.** For the normalized
  finite cases, the formalization proves the source product-condition bounds
  $$
    \beta^*\le1\quad(Z=1),\qquad
    \beta^*\le\frac{\log N}{\log N-\log Z}\quad(1<Z<N).
  $$
  The proof uses the source's nonnegative users, score-one unit witnesses,
  aggregate bound, and compact unit sublevels to turn the strict
  convex-hull product improvement into a statement about the supremum.
  It also proves the consequent no-singleton-equilibrium exclusion above the
  finite interior threshold.  The prose endpoint $Z=N$, described as
  infinity in the source, is intentionally outside the real-valued displayed
  quotient because its denominator is zero.

- **Corollary 4 — Exact.** Original:
  $\beta^*=2/(1-\cos\theta^*)$ for two equally sized nonzero user
  populations with $\ell_2^\beta$ cost. Formalized: the source's own
  product-condition definition of $\beta^*$, including its supremum, is
  exactly the displayed finite phase threshold. The accompanying
  fixed-exponent equilibrium iff is stated with the zero-safe nonzero-support
  genre convention. Thus the threshold equality itself is exact; only the
  nonzero genre convention makes the normalization well-defined.

- **Corollary 6 — Exact.** The welfare conclusion uses the nonzero genre
  convention above; the zero vector is left unnormalized.

## Two-user characterization, phase results, and profit

- **Lemma 2 — Exact with an atomless score-law clarification.**
  Original: a generic necessary-and-sufficient C1--C3 characterization
  (support maximization, marginal-CDF compatibility, and realization by
  nonnegative content) written with weak CDFs. Formalized: for the source's
  continuous proper norm-power model, an actual symmetric Nash law supplies
  all C1 ingredients—null score fibres, realised-support preimages, and
  attained induced fibre costs—and therefore proves the source weak-CDF C1
  direction. The canonical C2--C3 probability data are also derived from the
  source Nash law. For the converse, atomless score laws make the CDF formula
  equal the tie-aware winning probability, giving the checked equivalence.
  This is the reading used in the paper's continuous score-law applications.
  Without it, the one-dimensional zero-Dirac law satisfies the displayed
  weak-CDF C1--C3 data but loses the tie-payoff information. With one user,
  two producers and linear cost, staying at zero pays $1/2$, while producing
  $0<\epsilon<1/2$ pays $1-\epsilon>1/2$. That example explains the
  qualification for atomic candidate laws; it does not challenge the
  atomless application.

- **Theorem 2 and Propositions 9--10 — Regularity clarification.** Original: the
  two-user phase statement is presented for arbitrary nonnegative,
  linearly independent equal-population user vectors. Formalized: the same
  arbitrary-user equal-population market, with its angle written explicitly as
  $$
    \frac{\langle u_1,u_2\rangle}{\lVert u_1\rVert_2\lVert u_2\rVert_2}
      = \cos\theta,
    \qquad 0<\theta\leq\pi/2,
  $$
  and with $\beta_c=2/(1-\cos\theta)$. It proves both threshold
  implications under the paper's score-law regularity and an explicit finite
  conditional radial-law representation for the upper branch. Reason: the
  angle and nonzero-user clauses unpack the source's nonnegative linear
  independence condition; the representation makes the phrase “conditional
  distribution of $\lVert p\rVert$ along each genre” mathematically
  definite.

- **Lemma 9 — Cost formula on equilibrium support.** The displayed squared
  cost is
  $$
  \frac{z_1^2+z_2^2-2z_1z_2\cos\theta}{\sin^2\theta}.
  $$
  It is the minimum cost for feasible scores in the canonical two-dimensional
  model and holds on equilibrium support in any dimension. It need not hold
  at every other feasible score pair: take nonnegative unit users
  $u_1=(3/5,4/5,0)$, $u_2=(3/5,0,4/5)$ and content $p=(0,1,0)$.
  The scores are $(4/5,0)$. Zero second score forces the first and third
  content coordinates to vanish, so $p$ is the only nonnegative content with
  those scores and has squared cost $1$. The displayed formula gives $25/34$.
  This is a counterexample to the unrestricted cost formula, not an
  equilibrium counterexample; the [reduction below](#theorem-2-reduction-to-the-two-user-plane)
  proves why Theorem 2's equilibrium application remains valid.

- **Lemma 10 — Smooth interior first-order conditions.** Identify the cost
  derivatives with the derivatives of the maximum-score CDFs at nonzero
  interior equilibrium support points, using the source's smoothness
  assumptions. Absolute continuity alone gives these identities almost
  everywhere, rather than selecting a pointwise density at every support
  point. Boundary optimality uses one-sided conditions. The canonical
  calculation is applied after Theorem 2's dimension reduction.

- **Lemma 12 — Slope inequality by support optimality.** In canonical
  coordinates, the formalization proves the displayed inequality
  $$
  g'(z_1)\left(\frac{\beta-2}{\beta}\cos(\theta-2\phi)-\cos\theta\right)\le0,
  \qquad (z_1,g(z_1))=(r\cos\phi,r\cos(\theta-\phi)).
  $$
  Comparing four nearby score pairs using equilibrium optimality (C1)
  determines the graph's monotonicity from the sign of the cost's mixed
  partial derivative. This proves the slope condition without the printed
  density-differentiation argument. The standalone lemma uses canonical
  coordinates; the reduction below supplies this setting for Theorem 2.

- **Propositions 7--8 — Exact.** Original: positive
  and zero expected producer profit. Formalized: the corrected source-facing
  endpoints prove those literal expected-profit integrals, with the population
  law and payoff integrability derived from source Nash. Proposition 7 retains
  its explicit normalized Euclidean/nonzero-user domain; Proposition 8 retains
  the singleton-genre and finite-dimensional norm regularity used in its
  source proof.

### Theorem 2: reduction to the two-user plane

- **Proof route:** using the displayed induced-cost formula on arbitrary
  feasible score pairs → first reducing an equilibrium to the canonical
  two-dimensional model. The source uses Lemmas 9–12 in the proofs of
  Propositions 9–10 (Appendices D.1 and D.4). Its equilibrium condition C1
  supplies the needed restriction to the cone between the two user directions.

The formalization derives that cone restriction and proves that the Gram cost
formula holds on equilibrium support in any dimension. It then maps the
original equilibrium to two dimensions with exactly the same two user scores
and production costs. Every candidate deviation in the canonical model has
an original-space counterpart with at least as high scores and no greater
cost, so the mapped law is an equilibrium as well. This establishes the
reduction without assuming that rotating coordinates preserves nonnegative
content.

The canonical calculations then prove the two branches of Theorem 2:
below $\beta_c=2/(1-\cos\theta)$ every equilibrium is single-genre, and
above it no finite-genre equilibrium satisfies the stated conditional-law
regularity. The reduction preserves the relevant genre conclusions. Thus
Lemma 9's failure away from equilibrium does not restrict Theorem 2 to two
dimensions or change its phase threshold.

## Infinite-producer limit

- **Definition 1 — Typo.** Original: the product exponent is indexed by user
  although the weights are attached to genres. Formalized: genre weights,
  $$
  U(p)=\sum_i\prod_g
  F_g\!\left(\frac{u_i\cdot p}{u_i\cdot v_g}\right)^{w_g}-c(p),
  \qquad w_g\ge0,\quad\sum_gw_g=1,
  $$
  on the positive-denominator domain. Reason: the corrected indexing matches
  the genre mixture described by Definition 1.

- **Theorems 3--4 — Corrected source statements.** Original: Theorem 3 states the
  two-genre construction for any two linearly independent nonnegative user
  vectors, while Theorem 4 defines
  $$
  \theta^*=\arccos\!\left(
    \frac{\langle u_1,u_2\rangle}{\lVert u_1\rVert_2\lVert u_2\rVert_2}
  \right)<0.
  $$
  Formalized: canonical users with $0<\theta<\pi/2$ and
  $\beta>2/(1-\cos\theta)$. Reason: the displayed arccosine is nonnegative
  on the source domain, so the printed strict-negative hypothesis has no
  instance. The checked corrected result is the strictly acute construction;
  it does not claim that this angle restriction is necessary for every
  coherent infinite-producer formulation.

- **Theorems 3--4 genre witnesses — Explicit construction.** The corrected
  canonical endpoint identifies the two genres as
  $[\cos\phi,\sin\phi]$ and
  $[\cos(\theta-\phi),\sin(\theta-\phi)]$, where $\phi$
  is the selected compact angular maximizer.  It also proves that these
  witnesses are distinct: equality would make their first cosine scores equal
  and hence force $C_2=1$, contradicting the candidate condition
  $C_2<1$.  This records the source's two-genre construction in canonical
  coordinates; it is not an additional source correction.

- **Theorem 4 genre weights — Typo.** Original:
  $\alpha_1=\alpha_2=2$, despite Definition 1 requiring
  $\alpha_1+\alpha_2=1$. Formalized:
  $\alpha_1=\alpha_2=1/2$. Reason: the formalized weights define the stated
  equal two-genre probability mixture.

- **Theorem 4 quality-cap constant — Typo.** With user angle $\theta$,
  maximizing genre angle $\phi$, and
  $C_2=\cos(\theta-\phi)/\cos\phi$, the CDF constant changes from
  $$
  C_1=\frac{\sin\theta\cos\phi}{\sin(\theta-\phi)}
  \quad\longrightarrow\quad
  C_1=\frac{\sin\theta}{\cos\phi\sin(\theta-\phi)}=1+C_2^\beta.
  $$
  Reason: at the upper support quality $a=C_1^{1/\beta}$, a genre has total two-user gross payoff $1+C_2^\beta$ and pays cost $a^\beta=C_1$. Equality gives the zero
  payoff required by support approaching zero. The paper's first-order identity
  for $\phi$ gives the displayed equality to $1+C_2^\beta$.
