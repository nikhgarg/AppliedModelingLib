# Theorem 3 Constrained-Space Source Note

## Status

This is a statement-clarification note about the constrained-space reading of
Theorem 3. The formalization treats Theorem 3 as correct in the full
finite-coordinate space, and as requiring a projected/constrained alternative
in general constrained solution spaces.

No other named GKGMM19 result is affected by this note. Theorems 1--2 and
Propositions 1--2 remain partial for the separate reusable stochastic
subgradient convergence boundary.

## Paper Statement

Section 3.3 states Theorem 3 as follows in paper language:

- assume C1, C2, and C3;
- define the directional field
  `G(x) = E_v[grad f_v(x) / ||grad f_v(x)||_2]`;
- assume `G` is uniformly continuous;
- use `L2` movement constraints;
- voters move according to Model B;
- if an infinite Algorithm 1 trajectory converges to `x*`, then `x*` is a
  directional equilibrium, i.e. `G(x*) = 0`.

The proof intuition in Appendix C.6 is that if `G(x*)` is nonzero, then some
coordinate has a persistent signed drift in a small neighborhood of `x*`.
With the harmonic step-size schedule, this accumulated drift forces the
trajectory to leave every sufficiently small neighborhood of `x*`, contradicting
convergence.

## Corrected Formal Statement

For a projected Algorithm 1 trace over a general constrained solution space,
Lean proves the following no-hidden-premise alternative:

```text
if the projected trajectory converges to x*, then either
  G(x*) = 0
or
  the aggregate direction G(x*) is not a feasible positive direction at the
  projected tail points.
```

The paper-facing Lean row is
`theorem3_zero_or_no_aggregate_feasible_direction_formula`. It exposes the
missing feasibility condition as
`FiniteTheorem3AggregateFeasibleDirectionFormula` rather than hiding it in a
source-record premise.

Lean also proves the exact original Theorem 3 conclusion under the explicit
full-space condition:

```text
E.solutionSpace = Set.univ.
```

The paper-facing Lean row is
`theorem3_statement_of_full_sampled_projected_source_semantics_univ`. In that
case every positive step direction is feasible, so the projected/constrained
alternative collapses to the paper's original endpoint `G(x*) = 0`.

## Why The Extra Condition Appears

The proof in the paper reasons with accumulated unprojected movement: a
nonzero aggregate field creates signed drift, and the trajectory cannot remain
near `x*`.

For a constrained projected algorithm, a nonzero aggregate direction can point
out of the feasible set at a boundary point. Projection can remove the outward
component of the raw update. In that situation, convergence to a boundary point
does not by itself force `G(x*) = 0`; the correct conclusion is that either
the aggregate field vanishes or the aggregate field is blocked by the feasible
set geometry.

This is exactly the distinction captured by
`FiniteFeasibleDirectionAt E.solutionSpace point direction`: a direction is
usable in the residual/projection argument only when some positive step along
that direction remains feasible.

## Relation To Directional Equilibrium / NGA

The constrained-space issue is about convergence of projected dynamics, not
about the definition of directional equilibrium itself. In the source text,
directional equilibrium is the fixed-point condition

```text
G(x*) = 0.
```

If an external DE/NGA analysis studies this equation directly, or studies an
unconstrained/full-space process where every aggregate direction is feasible,
then this note does not create an additional issue for that analysis.

If instead an NGA-style iterative algorithm is projected onto a constrained
feasible set and is claimed to converge only to points with `G(x*) = 0`, then
the same boundary qualification is needed. A nonzero aggregate field may point
out of the feasible set at a boundary point, and projection can cancel that
outward component. The natural constrained conclusion is therefore a
projected-stationarity alternative: either `G(x*) = 0`, or the aggregate
direction is blocked by the feasible-set geometry.

Thus the formalization should not be read as changing the DE fixed-point
definition. It records the extra hypothesis needed to pass from convergence of
a projected iterative process to the unconstrained zero-field fixed point.

## Why This Does Not Undermine The Paper

The note does not affect the main convergence-formalization boundary for the
paper. Theorems 1--2 and Propositions 1--2 are governed by the separate SSGM
convergence theorem boundary.

For Theorem 3 itself:

- in full finite-coordinate space, Lean recovers the original statement;
- in general constrained spaces, Lean proves the natural projected alternative;
- the formalized interface does not assume the missing feasibility condition
  silently;
- the distinction is about the interaction between projection and boundary
  geometry, not about the paper's utility models or directional-field formula.

This is a constrained-space statement clarification: Theorem 3's original
zero-field endpoint is valid when the aggregate drift direction is feasible at
the limit, and this feasibility is automatic in the full-space case. In
constrained projected spaces, the formalization reports the explicit
alternative instead of overclaiming the unconditional zero-field conclusion.

## Formalization References

- `PaperInterface.lean`
  - `theorem3_aggregate_feasible_direction_formula`
  - `theorem3_zero_or_no_aggregate_feasible_direction_formula`
  - `theorem3_statement_of_full_sampled_projected_source_semantics_univ`
- `MainTheorems.lean`
  - `IsDirectionalEquilibrium`
  - `FiniteFeasibleDirectionAt`
  - `FiniteProjectedDirectionalEquilibriumAt`
  - `FiniteTheorem3AggregateFeasibleDirectionFormula`
  - `finiteTheorem3GlobalProjectedAggregateFeasibilitySource_of_univ_solutionSpace`
- `ProofInterface.lean`
  - `proof_theorem3_finite_fullSampledProjectedSourceSemantics_zero_or_no_aggregateFeasibleDirectionFormula`
  - `proof_theorem3Statement_of_fullSampledProjectedSourceSemantics_univ_solutionSpace`
