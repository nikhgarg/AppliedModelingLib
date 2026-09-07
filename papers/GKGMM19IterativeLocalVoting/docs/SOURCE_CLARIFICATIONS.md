# Source Clarifications

## Algorithm 1's query and projection

- Model B's undefined normalized-gradient step at zero gradient → remain at the current point (Definitions 1–3 and Algorithm 1).

## Definition 2 weights and Appendix Theorem 5 bias

- Appendix Theorem 5's almost-sure summability of a possibly adapted random bias → a deterministic summable bias sequence in the current theorem. This suffices for the main-text executions, whose bias is zero; it does not establish the broader random-bias statement.

## Appendix Theorem 5: nonunique minimizers

- The main proofs' invocation of a unique-minimizer theorem → convergence to a point in the minimizer set. C1–C3 allow the one-dimensional ideal law with density one on `[-1,-1/2]` and `[1/2,1]` and zero elsewhere; every point of `[-1/2,1/2]` minimizes expected absolute distance. The replacement uses convergence of squared-distance potentials, compactness to obtain a minimizer subsequence, and that potential to force convergence of the full path. Finitely many affine-spanning minimizers supply a common probability-one event, avoiding an uncountable intersection.

## Appendix C.4 Lemma 2: the infinity-one case

- The printed heading `(p=1,q=infinity)` → `(p=infinity,q=1)`, matching the displayed utility and query norms (p. 351).
- Near ties alone → near ties or active-coordinate crossing. If `i0` maximizes `|x_i-v_i|`, with current point `x`, ideal `v`, and query radius `r`, the bad event additionally includes `|x_i0-v_i0|<r`. Outside it and the near-tie event `exists j!=i0, |x_i0-v_i0|<|x_j-v_j|+r`, moving the active coordinate distance `r` toward its ideal minimizes infinity-norm cost on the `L1` query ball. In one dimension the near-tie event is empty, but an overshooting step need not minimize cost. Bounded density and support give probability `O(r)` for the added crossing slabs and near-tie strips, preserving the convergence estimate.

## Proposition 1 and Appendix C.6 Lemma 4

- The Appendix identifies “some coordinate block is within radius `r`” with a full-vector Euclidean ball → containment in the union of coordinate slabs `|x_i-z_i|<r`, where `x` is the ideal point and `z` the current point. Bounded support (C1) and bounded density (C3) bound the union's probability by a constant times `r`, supplying the estimate needed for Proposition 1.

## Proposition 2's coordinatewise Model B

- The general normalized-gradient ray → the Appendix C.7 proof's coordinatewise rule: move each non-tied decomposition coordinate the full `L-infinity` radius toward its sampled ideal. The target is the ordinary coordinatewise median. A literal normalized ray can weight coordinates differently: derivative magnitudes `1` or `1/2` in the first coordinate and `2` in the second produce a weighted-median first-coordinate target.
- C1's bounded closed convex feasible set → a set additionally closed under replacing one coordinate of a feasible point by the corresponding coordinate of another feasible point. The triangle `x>=0, y>=0, x+y<=1` satisfies C1 but replacement of the first coordinate of `(0,1)` by that of `(1,0)` leaves it. This shows the added geometric restriction is stronger; it does not show the restriction is necessary for Proposition 2 or refute the broader conclusion.

## Theorem 3's full-space and projected readings

- Theorem 3's zero aggregate directional field at a convergent trace's limit under C1–C3 → zero field under an additional condition making every aggregate direction feasible; on a constrained projected space, the checked conclusion is “zero field or no feasible aggregate direction.” A binding constraint can prevent motion in a preferred direction. These statements neither prove nor refute zero field on every bounded convex set allowed by C1.
