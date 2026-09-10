# Final Validation Report: Supply-Side Equilibria in Recommender Systems

Updated: 2026-09-09

## 1. Human Verdict

The paper’s results on producer equilibria, specialization, and profits are
formalized on the domains listed below.

## 2. Closeout Status

- Completion status: formalized
- One-sentence recap: The formalization covers finite-market equilibria,
  specialization thresholds, two-user geometry, and the infinite-producer limit.

## 3. Source and Scope

- Paper: Meena Jagadeesan, Nikhil Garg, and Jacob Steinhardt,
  *Supply-Side Equilibria in Recommender Systems*.
- Governing source: [arXiv:2206.13489, version 3](https://arxiv.org/abs/2206.13489v3).
- The comparison uses the numbered statements and supporting displays in that
  version. The [clarification memo](docs/SOURCE_CLARIFICATIONS.md) records each
  material change from the source statement to the formalized statement.

## 4. Researcher Summary of Checked Results

| Paper results | Comparison with the paper |
| --- | --- |
| [Theorem 1](docs/SOURCE_CLARIFICATIONS.md#one-dimensional-law-and-genre-convention) | **Exact.** |
| [Theorem 2 and Propositions 9--10](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) | **Exact with source clarification.** The phase transition holds in arbitrary dimension under the source score-law and conditional radial-law regularity; Section 7 explains the dimension-reduction proof. |
| [Definition 1 and Theorems 3--4](docs/SOURCE_CLARIFICATIONS.md#infinite-producer-limit) | **Exact construction after formula corrections, on a restricted angle domain.** Genre weights and the quality cap are corrected; the checked two-genre construction uses canonical users with a strictly acute angle. |
| Propositions 1--3 | **Exact.** |
| [Corollary 1 and Lemma 3](docs/SOURCE_CLARIFICATIONS.md#one-dimensional-law-and-genre-convention) | **Exact after correcting the CDF typo.** |
| [Example 1](docs/SOURCE_CLARIFICATIONS.md#one-dimensional-law-and-genre-convention) | **Exact.** |
| [Lemma 4](docs/SOURCE_CLARIFICATIONS.md#one-dimensional-law-and-genre-convention) | **Positive-score conclusion exact; span assertion corrected.** The positive-score result used by the later argument is proved directly; a source-domain counterexample rules out the printed span assertion. See the [potential generalization](#9-generalizations-conjectures-and-extensions). |
| [Lemmas 1 and 5--8](docs/SOURCE_CLARIFICATIONS.md#single-genre-optimization-and-thresholds) | **Exact with regularity made explicit for the source score sets.** Ratios use positive coordinates and an attained product maximum. Lemma 8's arbitrary-set wording needs a boundedness qualification. |
| [Corollary 2](docs/SOURCE_CLARIFICATIONS.md#single-genre-optimization-and-thresholds) | **Exact.** |
| [Corollary 3](docs/SOURCE_CLARIFICATIONS.md#single-genre-optimization-and-thresholds) | **Exact with a dimension clarification.** The threshold is at least $q$, with equality for at least two standard-basis users. The one-user basis threshold is unbounded. |
| [Corollary 5](docs/SOURCE_CLARIFICATIONS.md#single-genre-optimization-and-thresholds) | **Exact on the finite-formula domain.** The bound and singleton-equilibrium exclusion hold for $Z=1$ and $1<Z<N$; $Z=N$ uses a separate extended-real convention. |
| [Corollary 4](docs/SOURCE_CLARIFICATIONS.md#single-genre-optimization-and-thresholds) | **Exact.** |
| [Corollary 6](docs/SOURCE_CLARIFICATIONS.md#single-genre-optimization-and-thresholds) | **Exact.** |
| Claim 1 and Proposition 4 | **Exact.** |
| Propositions 5--6, Corollary 7, and Lemma 13 | **Exact.** |
| [Lemma 2](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) | **Exact with an atomless score-law clarification.** |
| [Lemma 9](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) | **Exact on equilibrium support; global formula corrected.** The cost formula holds at equilibrium in any dimension, but can fail for other feasible score pairs. |
| [Lemma 10](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) | **Exact on the smooth interior domain.** The canonical derivative calculation applies after dimension reduction; boundary points require one-sided conditions. |
| Lemma 11 | **Exact.** |
| [Lemma 12](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) | **Exact in the canonical calculation.** The slope inequality follows from equilibrium optimality; Theorem 2 transfers arbitrary-dimensional equilibria to this setting. |
| [Propositions 7--8](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) | **Exact.** |

Theorem 3 is the main-text infinite-producer result; Theorem 4 is its formal
appendix version. They are grouped with Definition 1 above.

## 5. Remaining Boundaries and Gaps

The standalone versions of Lemmas 9–12 are stated in canonical
two-dimensional coordinates. Theorem 2 nevertheless covers arbitrary-dimensional
users through the [equilibrium reduction in Section 7](#7-proof-strategy-deviations).
The infinite-producer construction in Theorems 3–4 remains checked for the
canonical strictly acute case; its broader dimension and angle extensions
are outside that construction.

## 6. Additional Assumptions Beyond Paper

The source norm, score-law, and conditional-law regularity is made explicit in
the [clarification memo](docs/SOURCE_CLARIFICATIONS.md). For Lemma 2, the CDF
equivalence uses atomless score laws. Lemma 10's pointwise identities use a
smooth interior support domain. The table states the separate dimension and
angle restrictions; their necessity for broader results is not claimed.

## 7. Proof-Strategy Deviations

**Theorem 2 (and Propositions 9–10):** first reduce an arbitrary-dimensional
equilibrium to the canonical two-dimensional model, preserving scores, costs,
and the relevant genre conclusions. Apply Lemmas 9–12 there; this avoids
using Lemma 9's cost formula away from equilibrium in the original space.
The [reduction accounts for every feasible deviation](docs/SOURCE_CLARIFICATIONS.md#theorem-2-reduction-to-the-two-user-plane),
so Theorem 2 retains its arbitrary-dimensional scope and phase threshold.

The single-genre optimization arguments are discussed in
[their source note](docs/SOURCE_CLARIFICATIONS.md#single-genre-optimization-and-thresholds).

## 8. Proof Tricks Worth Reusing

- Keep uniform tie sharing until score-tie nullness justifies a strict-CDF
  expression.
- Normalize only nonzero support directions when a distribution may approach
  zero content.
- Replace an unrestricted ratio optimizer by a positive attained product
  maximizer, then derive the supporting inequality at that maximizer.

## 9. Generalizations, Conjectures, and Extensions

**Potential correction to Lemma 4 (not yet proved in Lean).** For a smooth
production cost $c$ and an interior equilibrium support action $p>0$, the
proposed statement is $\nabla c(p)\in\operatorname{cone}\{u_1,\ldots,u_N\}$,
the set of nonnegative combinations of user vectors. For
$c(p)=\lVert p\rVert_q^\beta$, $q>1$, this becomes
$p^{q-1}\in\operatorname{cone}\{u_1,\ldots,u_N\}$, with powers taken
coordinatewise. This would recover the span assertion for Euclidean costs
($q=2$) and any number of users. This proposal is outside the checked results
above.

## 10. Source Clarifications and Exact Readings

Genres are normalized at nonzero support points; the zero vector is left
unnormalized. This is the convention for Theorem 1 and Corollary 6, not a
change to their conclusions.

The [source clarification memo](docs/SOURCE_CLARIFICATIONS.md#source-clarifications) is the single
substantive account of the corrected CDF, nonzero genre convention,
optimization domain, threshold endpoints, tie handling, score-cost calculation,
profit interpretation, and infinite-producer construction.
The [one-dimensional formulas and genre convention](docs/SOURCE_CLARIFICATIONS.md#one-dimensional-law-and-genre-convention)
and [two-user formulas and regularity](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit)
give the result-level details.

## 11. Paper Issues or Caveats

None.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) exposes 36 source-facing result
specifications, and [ProofInterface.lean](ProofInterface.lean) supplies their
checked endpoints. The current source-to-Spec and prerequisite ledgers cover
the complete selected result and model surface summarized in Sections 4 and
18--21.

## 13. Paper Assumption Provenance

Result-level hypotheses are visible in the interface specifications, and the
[prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) records the
source models and definitions on which they depend. Conditions already present
in the paper's norm and score-law models are stated as clarifications rather
than additional assumptions.

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) binds each selected result
to its source presentation. The [source-fidelity ledger](FINAL_CLOSURE_RECEIPT.md)
records the CDF, genre, optimization, score-cost, derivative, profit, and
infinite-producer corrections summarized in the public memo.

## 15. Library Lift Pass

The [library semantic ledger](FINAL_CLOSURE_RECEIPT.md) selects no
paper prerequisite for a separate reusable-library review. The selected
results rely on repository probability, fixed-point, compactness, and
optimization foundations while retaining the paper-specific market and
equilibrium definitions in this paper.

## 16. DAG Audit

[DependencyDAG.tex](docs/DependencyDAG.tex) now presents the numbered paper
models and results, their mathematical dependencies, and the result-level
distinction between exact and corrected source statements. The
[compiled diagram](docs/DependencyDAG.pdf) was visually checked for readable
labels, arrow direction, and node overlap.

## 17. Validation Checks

The refreshed [import-closure receipt](FINAL_CLOSURE_RECEIPT.md),
source-to-Spec review, prerequisite review, and focused proof check cover the
current source and Lean surface. The [review packet](docs/HUMAN_REVIEW_PACKET.pdf)
was regenerated and compiled from that surface. Report structure, memo coverage,
and rendered links were checked before the pending terminal validation.

## 18. Paper Definitions Checked

The checked definitions cover the finite market, symmetric mixed equilibrium,
quality and nonzero genre, single- and multi-genre regimes, the powered-score
image, product condition and extended-valued threshold, the two-population and
reparameterized equilibrium models, producer payoff, and Definition 1's
finite-genre formulation of the infinite-producer limit. Exact source routes
appear in the [statement map](audit/paper_statement_map.json) and
[prerequisite ledger](FINAL_CLOSURE_RECEIPT.md).

## 19. Named Theorem Statements Checked

The 36 selected results are Propositions 1--10; Theorems 1--4; Lemmas 1--13;
Corollaries 1--7; Claim 1; and Example 1. Section 4 gives the comparison label
for every group, and the [clarification memo](docs/SOURCE_CLARIFICATIONS.md)
states every material difference.

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) contains
one current source-to-Spec comparison for each of the 36 selected results.
Section 4 and the clarification memo give the reader-facing interpretation of
the exact and corrected-target rows.

## 21. Source-Coverage Audit Ledger

The [statement map](audit/paper_statement_map.json) inventories 47 source
items: 36 selected results and 11 prerequisite model or definition items. The
result and prerequisite comparisons account for this selected inventory.
Coverage is composed from those source-bound result and prerequisite reviews.
