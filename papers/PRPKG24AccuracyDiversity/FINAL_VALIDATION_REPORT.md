# Final Validation Report: PRPKG24 Accuracy-Diversity
Updated: 2026-09-07

## 1. Human Verdict

The paper's named theoretical results are proved on the domains and with the
finite bound stated below.

## 2. Closeout Status

- Completion status: formalized.
- Scope: the paper's named definitions, theoretical results, and Equation (4)'s
  representation definition.
- Human review: not yet recorded.

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
| [Corollary 1](docs/SOURCE_CLARIFICATIONS.md#value-and-type-support-restrictions) | **Current proof restriction:** positive probability for every preferred type; necessity is unresolved. |
| [Theorem 1(i)--(iv)](docs/SOURCE_CLARIFICATIONS.md#value-and-type-support-restrictions) | **Current proof restrictions:** every named type has positive mass for the stated all-coordinate limits; a zero-mass type instead needs a supportwise statement. Parts (i)--(ii) also use nonnegative conditional values, and the proof does not cover translated negative laws; necessity of nonnegativity is unresolved. |
| [Theorem 1(v)](docs/SOURCE_CLARIFICATIONS.md#all-consumed-and-bernoulli-endpoints) | **Additional sign condition:** the common conditional mean is nonnegative. A negative mean reverses the maximal-weight choice; at zero mean every allocation ties. |
| [Proposition 2](docs/SOURCE_CLARIFICATIONS.md#proposition-2-and-the-finite-uniform-model) | **Narrower proved finite bound:** the checked allocation is `(N+T)s_t-1` with error `(2T+1)/N`. The paper's sharper `(T+1)/N` bound remains unproved, while both bounds give the same square-root shares. |
| [Theorem 2](docs/SOURCE_CLARIFICATIONS.md#theorem-2-independent-rank-varying-bernoulli-values) | **Source clarification:** independent Bernoulli coordinates with rank-dependent probabilities. |
| [Appendix Lemma D.1](docs/SOURCE_CLARIFICATIONS.md#theorem-1-and-appendix-lemma-d1-share-asymptotics) | **Changed statement:** corrected sign regimes and deficit comparison replace the printed asymptotic branches. |
| [Appendix Lemmas D.2–D.5](docs/SOURCE_CLARIFICATIONS.md#order-statistics-and-integer-rounding) | **Restricted scope:** eventual valid ranks and the corrected strictly-concave rounding statement. |
| [Proposition 4, Equations (18) and (20)](docs/SOURCE_CLARIFICATIONS.md#proposition-4) | **Formulas corrected:** Equation (18) is an inequality; Equation (20) uses the preference-weighted measure from Equation (17). |
| [Proposition 4, limit step](docs/SOURCE_CLARIFICATIONS.md#proposition-4) | **Current proof condition:** a continuous nonconstant radial kernel suffices for the pointwise-supremum limit. The memo gives a discontinuous diagnostic for the proof step; necessity for Proposition 4 is unresolved. |
| [Theorem 3; Corollary 3](docs/SOURCE_CLARIFICATIONS.md#all-consumed-and-bernoulli-endpoints) | **Restricted scope:** nondegenerate Bernoulli endpoint domains. |

## 5. Remaining Boundaries and Gaps

The current finite Proposition 2 bound is weaker than the printed constant;
see Section 7. The model domains are in Section 6 and the Theorem 2 reading is
in Section 10. Computational claims are outside this theoretical scope.

## 6. Additional Assumptions Beyond Paper

Theorem 1(i)--(ii) use nonnegative conditional values almost surely as a
current proof restriction; necessity is unresolved. Corollary 1 uses positive
probability for every preferred type, with necessity unresolved. All-coordinate share limits use
strictly positive type masses because zero-mass coordinates require a
supportwise statement. Theorem 1(v)'s maximal-weight comparison uses a
nonnegative common mean, and Bernoulli share results exclude their specified
degenerate endpoints. Proposition 4's limit step uses continuous nonconstant
radial kernels as a sufficient proof condition, with necessity unresolved.
See the [domain notes](docs/SOURCE_CLARIFICATIONS.md).

## 7. Proof-Strategy Deviations

The checked Proposition 2 allocation is $(N+T)s_t-1$ and gives the finite
bound $(2T+1)/N$. The paper's $(T+1)/N$ bound is not established or refuted
here. The asymptotic square-root shares are unchanged.
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
also be identically distributed. The memo gives the [value/type domains](docs/SOURCE_CLARIFICATIONS.md#value-and-type-support-restrictions) and [order-statistic/rounding domains](docs/SOURCE_CLARIFICATIONS.md#order-statistics-and-integer-rounding); the result rows link the other clarifications.

<!-- BEGIN GENERATED SETTLED REVIEW CONTEXT -->
<!-- settled-review-context-sha256: 13e8a5cfd0342ec5126326332aad949b034c1b61d6c6e4a929a197023436373b -->
<!-- settled-review-context-presentation-sha256: 1445c07efab7c313e8fc6ec9a4392097e45ac22b21e6380a8d8909ed98c2d35f -->
### Source readings and additional assumptions

- Theorem 1(ii): an upper-bounded conditional value law → an upper-bounded law with nonnegative values almost surely. The current allocation proof does not establish the translated negative-value domain.
- All-coordinate share limits: possibly zero type masses → strictly positive mass for every named type.
<!-- END GENERATED SETTLED REVIEW CONTEXT -->

## 11. Paper Issues or Caveats

The formalization boundaries are stated in the limited-scope paragraph and
Sections 4--6; no claim is made that Proposition 2's sharper bound is false.

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
25 selected judgments: eight matches and 17 corrected-target matches.
The corrected statements and restrictions are explained in the
[source clarification memo](docs/SOURCE_CLARIFICATIONS.md).

## 21. Source-Coverage Audit Ledger

The [statement map](audit/paper_statement_map.json) retains 70 source items,
including model definitions, formulas, examples, and named results. The current
selected comparison consists of 25 result judgments and seven paper-prerequisite
judgments; source context is not counted as a separate proved result.
