# Final Validation Report: Supply-Side Equilibria in Recommender Systems

Updated: 2026-09-06

## 1. Human Verdict

The selected results are formalized across the finite-market, single-genre,
two-user, profit, and infinite-producer parts of the paper. Local formula
clarifications are reflected in the checked statements, and the
source-faithful results are identified below by paper number.

**Formalization gap:** Theorem 2 uses a specific two-dimensional user model; Theorems 3–4 cover user vectors at angles below 90°; Lemma 2 proves a restricted equilibrium characterization.

## 2. Closeout Status

- Completion status: formalized for the selected statements.
- Scope: finite symmetric equilibria, single-genre structure and thresholds,
  two-user score geometry and phase behavior, producer profit, and the
  infinite-producer construction.
- Reader boundary: the formalization does not establish the broader claims
  listed in Sections 5--6.

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
| Propositions 1--3 | **Exact.** |
| [Corollary 1 and Lemma 3](docs/SOURCE_CLARIFICATIONS.md#one-dimensional-law-and-genre-convention) | **Typo.** The CDF exponent is corrected, and the resulting distribution and equilibrium are proved. |
| [Example 1](docs/SOURCE_CLARIFICATIONS.md#one-dimensional-law-and-genre-convention) | **Formalization gap.** The equilibrium construction is proved; the separate uniqueness sentence is not asserted. |
| [Theorem 1](docs/SOURCE_CLARIFICATIONS.md#one-dimensional-law-and-genre-convention) | **Typo.** The product characterization and its multi-genre alternative are proved with genre normalized only at nonzero support points. |
| [Lemma 4](docs/SOURCE_CLARIFICATIONS.md#one-dimensional-law-and-genre-convention) | **Formalization gap.** The paper's span conclusion remains unproved. |
| [Lemmas 1 and 5--8](docs/SOURCE_CLARIFICATIONS.md#single-genre-optimization-and-thresholds) | **Formalization gap.** The checked optimization route uses positive denominators and an attained product maximizer; it does not assert the unrestricted printed minimax identities. |
| [Corollaries 2, 3, and 5](docs/SOURCE_CLARIFICATIONS.md#single-genre-optimization-and-thresholds) | **Formalization gap.** These are fixed-exponent existence and exclusion results; they do not assert the paper's full supremal-threshold package. |
| [Corollaries 4 and 6](docs/SOURCE_CLARIFICATIONS.md#single-genre-optimization-and-thresholds) | **Typo.** The two-user genre threshold and welfare conclusion are proved after the local formula and zero-normalization corrections. |
| Claim 1 and Proposition 4 | **Exact.** |
| [Theorem 2 and Propositions 9--10](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) | **Formalization gap.** The selected phase results use the canonical two-dimensional realization of the two-user model. |
| Propositions 5--6, Corollary 7, and Lemma 13 | **Exact.** |
| [Lemma 2](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) | **Additional premise; formalization gap.** Score-tie nullness is sufficient for the checked strict-CDF best-response equivalence; its necessity for a general tie-aware characterization is unresolved. The paper's C1--C3 equivalence is not proved. |
| [Lemma 9](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) | **Formalization gap.** The checked identity is the minimum cost over a feasible score fibre in the canonical two-dimensional model, rather than the cost of every content vector in arbitrary dimension. |
| [Lemma 10](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) | **Formalization gap.** The displayed cost derivatives are proved; their identification with equilibrium density derivatives is not asserted. |
| Lemma 11 | **Exact.** |
| [Lemma 12](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) | **Additional premise; formalization gap.** The support-slope inequality is proved from differentiated first-order identities and a negative-semidefinite payoff Hessian. Deriving them from equilibrium and C1 remains unproved; their necessity is unresolved. |
| [Propositions 7--8](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) | **Formalization gap.** The checked conclusions concern every support action; Proposition 7 uses the Euclidean route. Passing to the paper's expected-profit wording requires the corresponding population-law and integrability bridge. |
| [Definition 1 and Theorems 3--4](docs/SOURCE_CLARIFICATIONS.md#infinite-producer-limit) | **Typo fixed; formalization gap.** Genre weights, the CDF quality cap, and the feasible angle domain are corrected; the construction proves the strictly acute two-user case above threshold. |

## 5. Remaining Boundaries and Gaps

- Example 1: uniqueness among all symmetric mixed laws is not proved.
- Lemmas 1, 5, and 8: the unrestricted ratio minimax and sup-inf formulas are
  not proved. Lemma 8 does not hold for a one-dimensional set in its printed
  domain; the memo gives the witness.
- Corollaries 2, 3, and 5: the selected endpoints do not package the results as
  exact claims about attainment or equality of the supremum \(\beta^*\).
- Lemma 4: the span claim is not proved.
- Theorem 2 and Propositions 9--10: the selected endpoints do not assert the
  general-user statement outside the canonical two-dimensional realization.
- Lemma 9: the paper's arbitrary-dimensional content-cost identity does not
  hold for the nonnegative source-domain witness in the memo.
- Lemma 10: the equilibrium-to-density derivation is not proved.
- Propositions 7--8: the support-action conclusions are not promoted to the
  paper's expected-profit wording.
- Theorems 3--4: the orthogonal endpoint and any uniqueness or necessity claim
  outside the corrected strictly acute construction are not proved.

Except for the explicit Lemma 8 and Lemma 9 counterexamples, these omissions
do not establish that the omitted source claims are false or that the stated
restrictions are necessary.

## 6. Additional Assumptions Beyond Paper

- **Lemma 2 — Additional premise.** Score-tie nullness is assumed for the
  strict-CDF best-response equivalence. Its necessity for every possible
  tie-aware characterization remains unresolved.
- **Lemma 12 — Additional premise.** Differentiated first-order identities and
  a negative-semidefinite payoff Hessian are assumed for the graph inequality.
  Establishing them from equilibrium and C1 remains an undischarged bridge;
  the formalization does not claim they are necessary economic assumptions.

The [clarification memo](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit) gives the exact
original-to-formalized comparison for both results.

## 7. Proof-Strategy Deviations

Theorem 1's product characterization is proved using an attained positive
product maximizer and its supporting inequality, bypassing the unrestricted
minimax step. See the [optimization clarification](docs/SOURCE_CLARIFICATIONS.md#single-genre-optimization-and-thresholds).

## 8. Proof Tricks Worth Reusing

- Keep uniform tie sharing until score-tie nullness justifies a strict-CDF
  expression.
- Normalize only nonzero support directions when a distribution may approach
  zero content.
- Replace an unrestricted ratio optimizer by a positive attained product
  maximizer, then derive the supporting inequality at that maximizer.

## 9. Generalizations, Conjectures, and Extensions

None.

## 10. Source Clarifications and Exact Readings

The [source clarification memo](docs/SOURCE_CLARIFICATIONS.md#source-clarifications) is the single
substantive account of the corrected CDF, [nonzero genre convention](docs/SOURCE_CLARIFICATIONS.md#one-dimensional-law-and-genre-convention), positive
optimization domain, fixed-exponent thresholds, tie-aware characterization,
[canonical score-cost calculation](docs/SOURCE_CLARIFICATIONS.md#two-user-characterization-phase-results-and-profit), profit interpretation, and
infinite-producer construction.

## 11. Paper Issues or Caveats

None.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) exposes 36 source-facing result
specifications, and [ProofInterface.lean](ProofInterface.lean) supplies their
checked endpoints. Selected expanded targets were compared directly for
Example 1, Lemma 1, Theorem 2, Proposition 7, and Theorem 4. The result and
prerequisite ledgers bind the remaining interface statements to the same
source inventory.

## 13. Paper Assumption Provenance

[status.json](status.json) lists no standalone paper assumption declaration.
Result-level hypotheses are visible in the interface specifications. The
[prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) records six
source matches and five corrected-target matches for the paper-local models
and definitions. The finite-dimensional norm regularity convention is omitted
from the public context summary because it follows from the paper's norm
model.

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
models and results, their mathematical dependencies, and the three relevant
reader statuses: exact, corrected source text, and formalization gaps. The
[compiled diagram](docs/DependencyDAG.pdf) was visually checked for readable
labels, arrow direction, and node overlap.

## 17. Validation Checks

The extended-valued threshold definition compiles and passes bounded
independent source comparison. Its current closeout evidence is being
synchronized; the retained receipt describes its pinned prior tree.

The retained [focused-build receipt](FINAL_CLOSURE_RECEIPT.md) records
a passing build for its pinned tree. The [import-closure receipt](FINAL_CLOSURE_RECEIPT.md)
records the refreshed checked import surface. The
[review packet](docs/HUMAN_REVIEW_PACKET.pdf) was regenerated from the
authenticated review graph, compiled, and visually inspected. Report structure,
memo coverage, and rendered links pass. The retained
[final closure receipt](FINAL_CLOSURE_RECEIPT.md) describes the most recently
completed terminal transaction.

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
36 recorded machine comparisons: eight source matches and 28 corrected-target
matches. None of these rows carries a human-review judgment; this report gives
the reader-facing interpretation of those machine comparisons.

## 21. Source-Coverage Audit Ledger

The [statement map](audit/paper_statement_map.json) inventories 47 source
items: 36 selected results and 11 prerequisite model or definition items. The
36 result comparisons and 11 prerequisite comparisons account for the full
inventory. Coverage is composed from those source-bound result and
prerequisite reviews.
