# Final Validation Report: Reconciling the accuracy-diversity trade-off in recommendations
Updated: 2026-09-09

## 1. Human Verdict

The selected accuracy–diversity results are formalized under the source
readings below. Proposition 2 has the exact asymptotic conclusion, with a
factor-of-two correction in its finite type-count term.

## 2. Closeout Status

- Completion status: formalized
- One-sentence recap: The formalization proves the selected allocation and
  diversity results on their stated value and probability domains.

## 3. Source and Scope

The source is [arXiv:2307.15142](https://arxiv.org/abs/2307.15142). The scope
includes Equation (4), Definitions 1--3, the named main-text results, and
Appendix Lemmas D.1--D.5. Example 1 remains supplemental illustrative material;
its continuous relaxation does not receive whole-example credit. Simulations,
figures, captions, and other numerical observations are outside this scope.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Example 1, continuous top-one relaxation (Equation 2) | **Supplemental illustration.** The continuous relaxation is proved; Example 1 as a whole is outside the selected result scope. |
| Equation (4); Definitions 1–3; Proposition 5; Lemma 1 | **Exact.** |
| [Corollary 1](docs/SOURCE_CLARIFICATIONS.md#clarified-regularity-conditions) | **Exact with source clarification.** |
| [Theorem 1(i)](docs/SOURCE_CLARIFICATIONS.md#value-and-type-support-restrictions) | **Exact under a nondegeneracy condition.** The top value has positive mass, with positive mass below it; a point mass does not force uniform shares. |
| [Theorem 1(ii)--(iv)](docs/SOURCE_CLARIFICATIONS.md#clarified-regularity-conditions) | **Exact with source clarification.** |
| [Theorem 1(v)](docs/SOURCE_CLARIFICATIONS.md#all-consumed-and-bernoulli-endpoints) | **Exact with source clarification.** The item-value reading is nonnegative; at zero mean a maximal-weight allocation is optimal but need not be unique. |
| [Proposition 2](docs/SOURCE_CLARIFICATIONS.md#proposition-2-and-the-finite-uniform-model) | **Exact asymptotic conclusion.** The finite bound is missing a factor of two in the type-count term: `(T+1)/N` → `(2T+1)/N`. |
| [Theorem 2](docs/SOURCE_CLARIFICATIONS.md#theorem-2-independent-rank-varying-bernoulli-values) | **Exact with source clarification.** Independent Bernoulli values have rank-dependent probabilities. |
| [Appendix Lemma D.1](docs/SOURCE_CLARIFICATIONS.md#theorem-1-and-appendix-lemma-d1-share-asymptotics) | **Exact after correcting the asymptotic signs and optimization comparison.** The saturation branch uses a negative coefficient and positive exponent; the proof compares deficits. |
| [Appendix Lemmas D.2–D.5](docs/SOURCE_CLARIFICATIONS.md#order-statistics-and-integer-rounding) | **Exact with source clarification and a concavity typo corrected.** Order-statistic limits use valid ranks; the rounding lemma maximizes a strictly concave objective. |
| [Proposition 4, Equations (18) and (20)](docs/SOURCE_CLARIFICATIONS.md#proposition-4) | **Exact after correcting the displayed formulas.** Equation (18) is an inequality; Equation (20) uses the preference-weighted measure from Equation (17). |
| [Proposition 4, limit step](docs/SOURCE_CLARIFICATIONS.md#clarified-regularity-conditions) | **Exact with source clarification.** |
| [Theorem 3; Corollary 3](docs/SOURCE_CLARIFICATIONS.md#all-consumed-and-bernoulli-endpoints) | **Exact on the nondegenerate Bernoulli domain.** The share formulas use probabilities strictly between zero and one; deterministic endpoints require separate statements. |

## 5. Remaining Boundaries and Gaps

The selected theoretical results are checked under the readings in Section 6.
Zero-probability types, degenerate value laws, and deterministic Bernoulli
endpoints are not assigned the nondegenerate all-coordinate share conclusions.
Computational claims are outside this theoretical scope.

## 6. Clarified Regularity Conditions

The result table uses the following interpretation of the paper's model and
proof context. These conventions make that reading explicit.

- Corollary 1 and Theorem 1(ii)--(iv) concern types with positive selection
  probability and fixed positive consumption `k`. The paper explicitly fixes
  `k` in Section 3 and Corollary 1, defines `S_{n,k}` as a selected maximizing
  set in Section 1.1, and selects a maximizing allocation in Appendix D.1.
  Positive type probabilities are the intended nondegenerate reading of the
  all-coordinate share formula; zero-probability coordinates need a separate
  support convention.
- Theorem 1(ii) uses nonnegative conditional values almost surely on a finite
  interval with positive upper endpoint and width. This makes the nonnegative
  item-value reading explicit; it does not establish the result for every
  lower-unbounded or translated value law. Theorem 1(i)'s nondegeneracy
  condition is stated separately in the table.
- For Proposition 4, the preference measure is normalized sphere volume with
  an a.e.-measurable density that is positive almost everywhere, and the
  nonconstant radial kernel is continuous with values in `(0,1]`. The density
  need not be continuous: it aligns preference and volume null sets, while
  radial continuity rules out a pointwise Laplace maximum supported only on a
  null spike.

Theorem 1(v) uses the same nonnegative item-value reading. For negative mean,
maximal type weight would minimize rather than maximize expected value.
The Bernoulli formulas use their nondegenerate endpoints. See the
[source clarification record](docs/SOURCE_CLARIFICATIONS.md).

## 7. Proof-Strategy Deviations

Proposition 2's square-root share limit is exact. Its finite error bound needs
a factor of two in the type-count term: $(T+1)/N$ becomes $(2T+1)/N$.
The feasible relaxed allocation is $(N+T)s_t-1$, whose coordinates sum to $N$.
[Exact comparison](docs/SOURCE_CLARIFICATIONS.md#proposition-2-and-the-finite-uniform-model).

The memo also gives [D.1’s deficit and maximization comparisons](docs/SOURCE_CLARIFICATIONS.md#theorem-1-and-appendix-lemma-d1-share-asymptotics) and [Proposition 4’s measure correction](docs/SOURCE_CLARIFICATIONS.md#proposition-4).

## 8. Proof Tricks Worth Reusing

A positive probability-mass atom gives a direct positivity proof for the
finite normalizer in the gamma-share argument.

## 9. Generalizations, Conjectures, and Extensions

A supportwise treatment of zero-PMF coordinates could generalize the
all-coordinate share results, but it is not represented as an already-proved
extension. Any such extension should first specify whether coordinates with
zero selection probability are excluded or assigned a separate convention.

## 10. Source Clarifications and Exact Readings

Theorem 2's rank-dependent Bernoulli probabilities are independent but cannot
also be identically distributed. The [clarified regularity conditions](docs/SOURCE_CLARIFICATIONS.md#clarified-regularity-conditions) apply only to
the rows identified in Section 6; the [order-statistic and rounding domains](docs/SOURCE_CLARIFICATIONS.md#order-statistics-and-integer-rounding) and
other result-local corrections remain separately stated.

## 11. Paper Issues or Caveats

Sections 4--6 state the result domains. Proposition 2's finite constant
correction is separate from its exact asymptotic conclusion.

## 12. Detailed Formalization Evidence

The selected surface contains 25 transparent result specifications from
[PaperInterface.lean](PaperInterface.lean), and [ProofInterface.lean](ProofInterface.lean)
supplies their checked endpoints. The surface covers Equation (4),
Definitions 1--3, the named main-text results, and Appendix Lemmas D.1--D.5
within the domains and corrected statements summarized in Section 4.

## 13. Paper Assumption Provenance

The seven reviewed [paper prerequisites](FINAL_CLOSURE_RECEIPT.md)
expose the model definitions and source conditions used by the selected results.
Their result-specific positivity, support, endpoint, and regularity conditions
are stated in Sections 4, 6, and 10 and the
[source clarification memo](docs/SOURCE_CLARIFICATIONS.md).

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) routes 18 formula
presentations and three equation presentations, including Equation (4), the
homogeneity and order-statistic formulas, the Proposition 2 allocation and
bound, and Appendix D asymptotics. The
[source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) records the
exact or corrected-target status of each selected result.

## 15. Library Lift Pass

The [library semantic ledger](FINAL_CLOSURE_RECEIPT.md) selects no
material reusable-library prerequisite. The accuracy-diversity model,
allocation, order-statistic, and asymptotic constructions remain paper-local.

## 16. DAG Audit

The one-page [DependencyDAG.pdf](docs/DependencyDAG.pdf), generated from
[DependencyDAG.tex](docs/DependencyDAG.tex), was visually inspected at 180 dpi
on 2026-09-07. Its metadata, legend, node labels, borders, and arrows are
legible, with no observed clipping or label/box overlap.

## 17. Validation Checks

The [import-closure receipt](FINAL_CLOSURE_RECEIPT.md) records
the paper import surface. The [closeout record](FINAL_CLOSURE_RECEIPT.md)
records build and acceptance evidence for its pinned inputs. The
[review packet](docs/HUMAN_REVIEW_PACKET.pdf) presents the current selected
statements and governing definitions.

The targeted terminal command is
`python3 scripts/run_paper_closeout.py --paper PRPKG24AccuracyDiversity`.

## 18. Paper Definitions Checked

The checked definitions are Equation (4)'s representation, Definition 1's
gamma homogeneity, Definition 2's sequence homogeneity, and Definition 3's
order-statistic mean. The source map also retains the model and formula
conditions used by their dependent results.

## 19. Named Theorem Statements Checked

The 25 selected result targets cover Theorems 1–3, Corollaries 1 and 3,
Propositions 2, 4, and 5, Lemma 1, and Appendix Lemmas D.1–D.5, with
separate clauses for multipart results. Equation (4) and Definitions 1–3 are
reviewed as governing definitions. Section 4 gives the source comparison.

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) contains
25 selected judgments: four matches and 21 corrected-target matches.
Those technical categories include source conventions and local formula
corrections. Section 4 gives the mathematical comparison; the
[source clarification memo](docs/SOURCE_CLARIFICATIONS.md) gives its basis.

## 21. Source-Coverage Audit Ledger

The [statement map](audit/paper_statement_map.json) retains 70 source items,
including model definitions, formulas, examples, and named results. The current
selected comparison consists of 25 result judgments and seven paper-prerequisite
judgments; source context is not counted as a separate proved result.
