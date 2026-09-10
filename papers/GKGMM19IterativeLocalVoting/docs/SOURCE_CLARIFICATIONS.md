# Source clarifications

These notes refer to the [published JAIR article](https://www.jair.org/index.php/jair/article/view/11358).
The separate [Proposition 2 note](PROPOSITION2_C1_CORRECTION.md#c1-corrected-target)
explains the convergence target when constraints couple coordinates.

## Proposition 2's coordinatewise Model B

- **Response convention:** the general normalized-gradient step → the
  coordinatewise rule used for Proposition 2. Each non-tied coordinate moves
  the full $L^\infty$ query radius toward its sampled ideal, followed by
  Algorithm 1's projection onto the feasible set. The Appendix C.5 proof
  uses this step away from crossings of the ideal.
  This gives the ordinary median target on product domains and the
  [constrained target](PROPOSITION2_C1_CORRECTION.md#c1-corrected-target)
  on general convex domains.

The distinction matters because a normalized gradient can give different
step lengths to voters on opposite sides of a coordinate. For example, first
coordinate derivative magnitudes of $1$ and $1/2$, with second-coordinate
magnitude $2$, produce first-coordinate movements of $r/2$ and $r/4$ after
$L^\infty$ normalization. Their balance is a weighted median.

## Theorem 3's full-space and projected readings

- **Two conclusions:** the zero-field result holds under an explicit tail
  feasibility condition. On bounded convex domains, the formalization also
  proves the alternative: the limiting aggregate field is zero or that
  condition fails. Here $G(x)$ is the population mean of voters' normalized
  utility gradients; the condition requires a positive step in $G(x^*)$ to
  remain feasible from the relevant late iterates. A binding constraint can
  prevent such a step.

More precisely, if $G(x^*)\ne0$ and its inner product with $G(x_t)$ is bounded
away from zero on a tail, then for each projected iterate on that tail the
condition requires some $a>0$ with $x_{t+1}+aG(x^*)\in X$. The checked
alternative is $G(x^*)=0$ or failure of this tail condition. This does not
establish that every aggregate direction is blocked at the limit.

The source is Theorem 3 and Appendix C.6. Whether its assumptions imply the
needed condition, or another argument proves $G(x^*)=0$ on every C1 domain,
remains unresolved.

## Algorithm 1's query and projection

- **Zero gradient:** the undefined normalized-gradient step → staying at the
  current point.

<a id="definition-2-weights-and-appendix-theorem-5-bias"></a>

## Appendix Theorem 5: random bias

- **Random bias:** Appendix Theorem 5's almost-sure summability condition is
  read sample by sample. The bias may depend on past observations; it need not
  have a deterministic summable envelope. The process and conditional
  expectations use the usual measurability and adaptedness conventions.

The explicit regularity also records available subgradients and integrable
products of the noise with the distance from the minimizer. The bounded
feasible set bounds that distance, and the theorem's conditional noise bound
supplies the square-integrability estimate used in the convergence argument.
These conditions concern the stochastic update in Appendix C.1.

## Appendix Theorem 5: nonunique minimizers

- **Extension used by the main proofs:** convergence to a unique minimizer
  → convergence to a point in the minimizer set. The paper's models permit
  nonunique medians: the density equal to one on $[-1,-1/2]$ and $[1/2,1]$
  gives every point of $[-1/2,1/2]$ the same expected absolute distance.
  Convergence of the distance to minimizers, together with compactness,
  establishes convergence to one minimizer without assuming uniqueness.

<a id="appendix-c4-lemma-2-the-infinity-one-case"></a>

## Appendix Lemma 2: the infinity-one case

- **Heading typo:** $(p=1,q=\infty)$ → $(p=\infty,q=1)$ in the proof on
  page 351 (Appendix C.7), matching the displayed utility and query norms.
- **Exceptional event in the proof:** near ties → near ties or crossing the
  active coordinate's ideal. If $i_0$ maximizes $|x_i-v_i|$, the crossing
  event is $|x_{i_0}-v_{i_0}|<r$; the near-tie event is
  $|x_{i_0}-v_{i_0}|<|x_j-v_j|+r$ for some $j\ne i_0$. Outside these
  events, moving the active coordinate distance $r$ toward its ideal minimizes
  infinity-norm cost on the $L^1$ query ball. In one dimension there are no
  ties to another coordinate, but a step can still overshoot the ideal.
  Bounded density and support give probability $O(r)$ for these events,
  proving Lemma 2's stated rate.

<a id="proposition-1-and-appendix-c6-lemma-4"></a>

## Proposition 1 and Appendix Lemma 4

- **Event containment in the proof:** proximity in some coordinate block is
  contained in a union of coordinate slabs, rather than a full-vector
  Euclidean ball. With ideal point $v$ and current point $x$, the slabs are
  $|v_i-x_i|<r$. Bounded support (C1) and bounded density (C3) bound their
  union's probability by $O(r)$, proving Lemma 4's stated estimate for
  Proposition 1. Lemma 4 is stated in Appendix C.5 and proved in C.7.
