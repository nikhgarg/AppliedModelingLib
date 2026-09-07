# Source clarifications and corrections

Source: the official NeurIPS 2024 paper.

## Post-Theorem 3.7 proof-location sentence

- The paragraph attributes a linearly infeasible pairwise-majority-consistent (PMC) ranking to Appendix A.6 → that example belongs to Appendix B. Appendix A.6's strict-majority relation has a directed cycle among its positive-axis candidates and a reverse cycle among its negative-axis candidates, so no transitive PMC ranking exists there.


- The formalization therefore records the source sentence as a proof-location error. It proves the actual Appendix-A.6 fact that no PMC ranking exists, and it proves the Appendix-B infeasibility example under its own Appendix-B source owner. Theorem 3.7 itself is unchanged.

## Lemmas 3.4--3.5: the perturbation seam

- Lemma 3.4's weak zero-perturbation inclusion → a strict cone for every minimizer. Here `OPT(0)` is the zero-perturbation minimizer set and `r` the candidate score.

- At `epsilon = 0`, each copied candidate used in the proof has the same feature vector as its original. The paper defines the region `R_{c' over c}` by the weak comparison `r(c') >= r(c)`. Consequently, the printed Lemma 3.4 inclusion `OPT(0) subset R_{c' over c}` is true for every parameter and supplies no strict margin from the boundary. It therefore cannot by itself justify the open-set stability step printed in Lemma 3.5.

- The source's coordinate bounds give `theta_1>A3>0` and `theta_2<A4` for every core minimizer `theta`. Choosing `delta>0` with `delta A4<A3` yields `theta_1>0` and `delta theta_2<theta_1`, ranking each original above its copy for every positive perturbation.
- Lemma 3.5's open-set inference → a strict infimum gap on the closed half-space where the copy weakly outranks its original, for all sufficiently small `epsilon>0`. Coercivity, uniform continuity on a compact set, and an exterior lower bound establish the gap. Theorem 3.1's hypotheses and impossibility conclusion do not change.

## Theorem 3.1 positive-input branch: restricted-infimum sign

- `inf_{y <= 0} loss(y) < inf_y loss(y)` → `inf_{y <= 0} loss(y) > inf_y loss(y)`. The preceding proof gives loss at least `loss(0)` on nonpositive inputs and a strictly better positive input. “Lower bounded by `loss(0)` from above” correspondingly means “bounded below by `loss(0)`.”

## Appendix A.1: one-sided derivatives

- Ordinary derivative data → one-sided convex derivatives for the four-point argument supporting Lemma 3.2; ordinary differentiability at the selected points is unnecessary.
- The later abbreviation `-2w,-w,w,2w` → the originally selected points `-w,-w/2,w/2,w`, which the displayed threshold calculation uses.

## Six-candidate feasibility witness

- Footnote 7's parameter `(1,1)` → `(delta,2)` for the ranking `a>a'>b>b'>c'>c`. With the printed feature `x_{c'}=(-epsilon,delta epsilon)` and `0<delta<1`, `(1,1)` gives `c>c'`; the replacement gives the required strict order on the source construction's parameter domain.

## Rule-level tie conventions

- The LCPO, Copeland, and leximax-plurality correspondences → selectors with profile-independent candidate or ranking tie keys in the checked rule-level results. A single-valued selector need not admit such a key; necessity of this restriction for the broader claims is not established. LCPO means leximax Copeland subject to Pareto optimality.
- Theorem C.5's “without loss of generality” first-profile output → an explicit premise that the Pareto-Kemeny rule returns the source ranking `v1` there. The reduction from every selector to that local case remains a formalization gap; necessity of the local choice is unknown.
