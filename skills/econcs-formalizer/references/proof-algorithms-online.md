# Algorithms: Online

Use for `AppliedModelingLib/Algorithms/Online/*`, AdWords/MSVV, generalized online
matching, regret, and Yao-style lower bounds.

## AdWords and Online Matching

- Use the LP-duality theorem seam before attempting a full `1 - 1/e` proof.
  Prove weak duality once from `DualFeasible`, then package the algorithm
  analysis as a primal-dual competitive certificate with primal feasibility,
  nonnegative ratio, dual variables, dual feasibility, and the scaled
  dual-objective bound.
- Keep Balance/MSVV work in the query-history fold. Run feasibility should be
  closed through a generic `ChoiceRuleFeasible` theorem before dual accounting.
- Treat the small-bids limit as a separate paper-local theorem rather than
  mixing it into the finite LP layer.
- For Section 7 lower-bound families, keep harmonic/asymptotic arguments in a
  reusable asymptotics layer. New family certificates should instantiate the
  deterministic choice/allocation rule and realized-revenue bridge directly.
- Do not add a new harmonic-limit field to lower-bound family certificates if a
  built-in harmonic theorem already supplies it.
- For effective-bid reductions, prove that each transformation preserves the
  small-bids condition and the relevant revenue/feasibility interpretation.

## Yao and Regret

- Separate the distributional lower-bound skeleton from the paper-specific hard
  instance. The skeleton should talk about finite algorithm families,
  distributions over inputs, expected performance, and a pointwise or average
  certificate.
- Algorithmic statements should separate correctness/existence from runtime or
  complexity unless the complexity layer is already in scope.
