# Appendix Theorem 5 and nonunique minimizers

This is a proof-route correction, not a counterexample to the paper's
convergence claims.

The printed Appendix Theorem 5 (`cited publication:1995-2035`) assumes that the
convex objective has a **unique** minimizer `x*` and concludes almost-sure
convergence to that point.  The proofs of Theorem 1 and Proposition 2 invoke
that theorem.  However, the main-text assumptions C1--C3 require only a
bounded measurable density for ideal points.  They do not imply uniqueness of
the societal optimum or of a coordinatewise median.

For example, in one dimension let the feasible set be `[-1, 1]` and let the
ideal point have density one on `[-1, -1/2] ∪ [1/2, 1]` and zero elsewhere.
This is a bounded measurable density satisfying C3.  The expected `L1` cost
has every point of `[-1/2, 1/2]` as a minimizer.  Thus Appendix Theorem 5
cannot directly justify the `(p,q) = (1,∞)` and `(∞,1)` branches of Theorem 1,
nor Proposition 2's explicitly set-valued median conclusion, without an
additional uniqueness argument.

The formalization proves the main conclusions using a minimizer-set argument:

1. For every minimizer, projected stochastic-subgradient descent makes the
   squared Euclidean distance to that minimizer converge almost surely.
2. Compactness and the objective-descent argument provide a subsequence whose
   limit is a minimizer.
3. The convergent distance potential to that subsequential minimizer forces
   the whole sample path to converge to it.

The almost-sure argument does not intersect events indexed by every minimizer.
Finitely many fixed minimizers supply affine anchors: differences of their
squared-distance potentials control the potential to any minimizer in their
affine span. Together with a minimizer subsequence, this proves convergence of
the whole path to a point in the minimizer set. The limit need not be a fixed
minimizer chosen in advance.

This extension of Appendix Theorem 5 supplies the nonunique-minimizer cases in
the main convergence results without adding a uniqueness assumption.
