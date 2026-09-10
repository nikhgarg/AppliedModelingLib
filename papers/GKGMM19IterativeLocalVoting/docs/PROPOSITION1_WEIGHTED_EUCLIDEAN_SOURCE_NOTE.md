# Proposition 1 and Appendix C.6 Lemma 4: source clarification

## Effect on Proposition 1

The convergence argument required for the weighted-Euclidean Proposition 1
has been checked for a concrete iid joint model of voter weights and ideal
points, for both response models. In the finite coordinate model, raw Model A
maximizers exist pointwise by compactness and continuity; the Euclidean
projection is constructed from C1; and the Definition 2 social utility is
defined as the expected sampled utility and proved equivalent to negative
population cost.

For the general finite weighted multi-block raw maximization problem, the
formalization uses the Borel water-filling rule

\[
s_k=\min\{d_k,\lambda a_k\},
\]

where `d_k` is the current block-to-ideal distance, `a_k` is the normalized
nonnegative weight, and `\lambda` is the maximum over the finitely many
candidate saturated-block multipliers.  The response moves distance `s_k`
toward the ideal on each block.  Finite maxima, arithmetic operations, and
square root make this rule Borel.  Its proof of exactness separates two cases:
if uncapped positive weight remains, the amounts exhaust the query's squared
radius and a finite Cauchy--Schwarz argument proves optimality; otherwise all
positive-weight blocks are at their ideals and the sampled cost is zero.

Thus the concrete iid Definition 2 model has a canonical measurable exact
Model A execution, rather than an abstract response-selection input.  Applying
the resulting Proposition 1 endpoint to a particular paper instance still
requires the displayed C1/C2 geometry and ideal-support facts for that
instance; this is ordinary source-model instantiation, not a tie-breaking or
stochastic-convergence gap.

The Appendix C.6 event estimate used by Proposition 1 follows directly from
C3, as explained below.

## Appendix C.6, Lemma 4

In the first part of Appendix C.6 Lemma 4, the exceptional event is

\[
B(x,r)=\{(w,z): \exists k,\ \lVert x^k-z^k\rVert_2<r\},
\]

where `k` ranges over component coordinate blocks. The printed proof then
treats this as the full-vector event `\{\lVert x-z\rVert_2<r\}`. With more
than one block the events are not equal: an ideal point can be close on one
block while far away on another.

The bound actually used in the subsequent convergence argument nevertheless
holds. Every nonempty block has a coordinate, and

\[
\lVert x^k-z^k\rVert_2<r
\quad\Longrightarrow\quad
|x_i-z_i|<r
\quad\text{for some coordinate }i\text{ in block }k.
\]

Consequently,

\[
B(x,r)\subseteq\{z:\exists i,\ |x_i-z_i|<r\}.
\]

The C1/C2/C3 bounded-density argument bounds the right-hand coordinate-slab
event by `C r`. Since this uses only the ideal-point marginal, it applies to
the joint voter law without requiring weights and ideals to be independent
within a voter. Thus the required exceptional-event probability remains
linear in `r`, which is sufficient for the summable descent-error estimate.

This is a minor correction to the printed lemma proof, not a caveat on the
main-text Proposition 1.
