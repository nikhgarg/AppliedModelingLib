# Governing Corrected Model: GJ18

## Authority and Scope

Recorded 2026-07-24 from the repository user, an author of the paper. This is
the author-approved formalization target for this folder. It is not presented
as a published erratum and does not assert that the archived `cited publication`
already contains every clause below.

The archival baseline remains `cited publication`, SHA-256
`b5378ae6f1ada1674d9f07dd4c1405655a9109e89a9977debab1b89d599f19de`.
The corrected target is a finite-chain model for the paper's ranking objective,
not a derivation of the archive's ill-typed population-state recurrence.

## Corrected Clauses

| Correction ID | Archive anchor | Author-approved governing clause | Relation to archive |
| --- | --- | --- | --- |
| `GJ18-CORR-SELLER-CARRIER-2026-07-24` | `adjectivesmodel.tex:22-24,85-90,111-125` | Seller types are `theta_0 < ... < theta_{M-1}` with `M >= 2` and a uniform prior. | Makes the objective's nonzero denominator and adjacent-pair carrier explicit. |
| `GJ18-CORR-MATCH-RATES-2026-07-24` | `adjectivesmodel.tex:26-29` | For every type, `0 < g(theta) <= 1`; `n_k(theta) = floor(k g(theta))`. | Strengthens the displayed nondecreasing rate condition so every comparison has diverging sample size while preserving at most one match per period. |
| `GJ18-CORR-AGGREGATE-INDEX-2026-07-24` | `adjectivesmodel.tex:54-59` | The aggregate is the average of exactly `n_k(theta)` ratings, indexed for example by `ell = 1, ..., n_k(theta)`, with the stated zero-sample convention. | Corrects the displayed off-by-one summation endpoint. |
| `GJ18-CORR-RATING-CARRIER-2026-07-24` | `adjectivesmodel.tex:32-51` | The ordered rating scale has at least two levels; scores are strictly increasing; within-type tails decrease at displayed cutoffs; cross-type upper tails are strict only above the bottom cutoff. | Excludes the vacuous singleton scale and the impossible strict bottom-tail condition. No terminal full-support clause is added. |
| `GJ18-CORR-IID-STATE-LAW-2026-07-24` | `adjectivesmodel.tex:40,67-73` | Conditional on seller type, rating draws are iid with law `rho(theta, . | Y)` and histories are independent across sellers. At horizon `k`, the state law is the induced finite product law. | Replaces the archive's informal/ill-typed `mu_k` recurrence as the governing state-evolution clause. |
| `GJ18-CORR-ADJACENT-INDEX-2026-07-24` | `adjectivesmodel.tex:111-125; appendix_theory.tex:77-95` | The Theorem 1 minimum ranges over `0 <= i <= M-2`, exactly the valid adjacent pairs. | Corrects the endpoint that can name nonexistent `theta_M`. |
| `GJ18-CORR-EXTENDED-RATE-2026-07-24` | `adjectivesmodel.tex:111-125; appendix_theory.tex:7-8,44-53` | `I(a | theta) = sup_z {z a - Lambda(z | theta)}` is extended-real valued. The pairwise and adjacent minima use extended-real arithmetic; the final corrected-model rate is proved finite and then identified with its real representative. | Corrects the codomain required for out-of-support thresholds. |
| `GJ18-CORR-APPENDIX-DISCRETE-PROOF-2026-07-24` | `appendix_theory.tex:7-69` | The weak-inversion and `1-P_k` rate are proved directly for finite iid product laws, including the fixed-constant comparison. | Replaces the unsupported continuum-integral/Laplace transfer. |

## Corrected Theorem 1

Let `I(a | theta)` have the extended-real convention above and define

```tex
\bar r = \min_{0 \le i \le M-2}\; \inf_{a \in \mathbb R}
  \{g(\theta_{i+1}) I(a \mid \theta_{i+1})
    + g(\theta_i) I(a \mid \theta_i)\}.
```

For the corrected finite ordinal iid model,

```tex
- \lim_{k \to \infty} \frac{1}{k} \log(1-W_k) = \bar r,
```

where `bar r` is finite and is represented by an ordinary real number. The
extended codomain is essential inside the infimum: infeasible thresholds have
infinite cost rather than a spurious default real value. This preserves the
intended conclusion and does not add a terminal-support hypothesis.

## Checked Realization

`ClarifiedSourceModel` is the complete Lean model record for these clauses.
It visibly contains the seller-count, uniform-prior, match-rate, rating-scale,
ordinal-tail, and iid-state-law fields. `PaperInterface.lean` exposes both the
state-level extended-rate theorem and the finite-real-rate theorem for the
corrected `W_k` objective.

The archived `mu_k` recurrence and unrestricted real-valued rate display are
retained only as explicitly recorded archival deltas and diagnostics. No
checked theorem claims to derive the corrected iid state law or corrected rate
codomain from those archived expressions.
