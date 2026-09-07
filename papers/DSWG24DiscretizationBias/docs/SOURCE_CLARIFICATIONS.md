# Source Clarifications and Proof-Route Note

## Theorem 1(iii): calibration reading

- **Source reading:** the source's calibration display at score values with
  positive probability, $\Pr(Y=y\mid q_y=c)=c$, uses the standard
  conditional-expectation meaning on every measurable score event $B$:
  $\mathbb E[1_{\{q_y\in B\}}1_{\{Y=y\}}]=\mathbb E[1_{\{q_y\in B\}}q_y]$.
- **Scope:** this is the ordinary calibration definition intended by the
  source proof, including continuous score distributions. It is a source
  clarification rather than an additional theorem assumption.
- **Proof route:** a direct calibration inequality replaces the paper's
  mass-transformation argument; the bound itself is unchanged on that domain.

## Theorem 2(iii) weighted-objective wording

- The main-text “unless gamma=1 and D agrees” wording → for `0 <= gamma < 1`, optimality of an independent rule `D` for the weighted objective `O_N^gamma` implies almost-sure agreement with argmax. It does not require `gamma=1` for an agreeing rule or assert that agreement suffices for optimality.
- Appendix B.1’s one-sample switch proves this necessary-condition reading for the paper’s dataset-dependent reference family: positive-probability disagreement permits a strict improvement. The proof also includes `gamma=0`; no additional statistical assumption is used.

## Pareto-optimal terminology

- **Source → retained helper:** maximizing a weighted objective for some
  $0<\gamma\le1$ → nondominance. The definition correspondence is uncredited;
  Theorem 2(iii)'s domination and weighted-objective comparisons are checked
  separately.
- **Why distinguish them:** among metric pairs $(1,0),(0,1),(0.4,0.4)$, the last
  is nondominated but never maximizes a positive weighted sum. This separates
  the generic definitions; it is not a counterexample to Theorem 2(iii).
