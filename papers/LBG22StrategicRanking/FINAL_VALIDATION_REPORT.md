# Final Validation Report: Strategic Ranking

Updated: 2026-09-09

## 1. Human Verdict

The equilibrium, welfare, utility, and fairness results are formalized.
Proposition 3.1’s cutoff-monotonicity claim and Proposition B.2’s weighted
optimum require the additional conditions stated below.

## 2. Closeout Status

- Completion status: formalized
- One-sentence recap: All 18 selected results are proved, with local
  restrictions for two optimization claims.

## 3. Source and Scope

Liu, Garg, and Borgs, [*Strategic Ranking*](https://proceedings.mlr.press/v151/liu22b.html),
AISTATS 2022, PMLR 151, pp. 2489–2518. The scope includes the 18 named
results in the main text and supplement, with their governing definitions.
Empirical implementation and unnumbered social-welfare discussion are outside
this scope. The [model note](docs/SOURCE_CLARIFICATIONS.md#stated-model-known-priorities-and-continuum-best-response)
explains tie priorities and continuum equilibrium.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Proposition 2.1: rank preservation | **Exact.** |
| Theorem 2.2: second-price effort | **Exact.** |
| Proposition 3.1: applicant welfare | **Pure-randomization optimum exact; cutoff monotonicity under additional regularity conditions.** [Details](docs/SOURCE_CLARIFICATIONS.md#proposition-31) |
| Proposition 3.2: private utility | **Exact.** |
| Proposition 3.3: three-level improvement | **Exact.** |
| Proposition 3.4: societal utility | **Exact.** |
| Proposition 4.1: group equilibrium | **Exact.** |
| Proposition 4.2: welfare gap | **Exact with source clarification.** For almost every type, the gap is nonnegative; among types admitted in both groups, it is positive exactly when disadvantaged-group effort is positive. [Details](docs/SOURCE_CLARIFICATIONS.md#propositions-42-and-43-exact-under-clarified-weakstrict-interpretation) |
| Proposition 4.3: gap comparative statics | **Exact with source clarification.** Among types admitted in both groups at the higher cutoff, the gap increases weakly almost everywhere, strictly with positive disadvantaged effort at the lower cutoff; derivative claims apply where differentiability holds. [Details](docs/SOURCE_CLARIFICATIONS.md#propositions-42-and-43-exact-under-clarified-weakstrict-interpretation) |
| Proposition 4.4: access | **Exact.** |
| Corollary A.1: effort comparative statics | **Exact.** |
| Remark A.2: ties in pre-effort skill | **Exact.** |
| Proposition B.1: multidimensional ranking | **Exact with source clarification.** [Rank preservation concerns admission rewards](docs/SOURCE_CLARIFICATIONS.md#appendix-effort-comparative-statics-and-proposition-b1); different weighted-skill ranks can receive the same reward within a policy band. |
| Proposition B.2: weighted utility | **Exact under additional regularity conditions:** affine skill and the stated curvature restrictions. [Details](docs/SOURCE_CLARIFICATIONS.md#proposition-b2) |
| Lemma C.1: tied scores | **Exact.** |
| Lemma C.2: null deviations | **Exact.** |
| Lemma C.3: cost-gap ordering | **Exact.** |
| Lemma C.4: production-gap ordering | **Exact.** |

The [source clarification note](docs/SOURCE_CLARIFICATIONS.md) states the
conditions, formulas, counterexamples, and proof changes in mathematical terms.

## 5. Remaining Boundaries and Gaps

All 18 selected results are proved on the stated domains. The unrestricted
versions of Proposition 3.1’s cutoff monotonicity and Proposition B.2’s
weighted optimum are false; the additional conditions are in Section 6.

## 6. Additional Assumptions Beyond Paper

For Proposition 3.1's monotonicity clause only, put $E=p^{-1}(1)$ and
$C=p\circ g^{-1}$. Require concavity of
$x\mapsto\log f(1-e^{-x})$ on $x>0$, and of
$z\mapsto\log C(e^z)$ where $g(0)<e^z\le g(E)$.
No zero-baseline-production or positive-minimum-skill restriction is added.
The unconditional pure-randomization optimum does not use these premises.

For B.2 only, measurable skill is affine and nondegenerate with nonnegative
lower endpoint. Require $g(0)=0$, $B\ge E=p^{-1}(1)$, concavity of $g^2$
on $(0,B)$, convexity of $x/C(x)$ on
$[g(p^{-1}(\rho)),g(E)]$, twice differentiability of cost and production on
their stated open domains, and continuity of $g''$.
Keep source endpoint continuity and independent regular unmeasurable skill.
The [full B.2 statement](docs/SOURCE_CLARIFICATIONS.md#proposition-b2) spells out
conditional means and the policy domain. No supporting-line or optimizer
property is assumed.

Known priorities, the strong applicant-wise AE quantifier, the hard residual
budget in B.2, and weak/strict interpretation are model/statement
clarifications. They are not additional economic shape assumptions.

## 7. Proof-Strategy Deviations

The proof uses the [correct welfare derivative](docs/SOURCE_CLARIFICATIONS.md#proposition-31),
[normalized utilities and admissible witnesses](docs/SOURCE_CLARIFICATIONS.md#associated-normalization-and-access-corrections),
and the [source effort-comparison indices](docs/SOURCE_CLARIFICATIONS.md#appendix-effort-comparative-statics-and-proposition-b1).
For [Proposition B.2](docs/SOURCE_CLARIFICATIONS.md#proposition-b2), utility
curvature establishes a global optimum; a zero derivative alone would not
suffice.

## 8. Proof Tricks Worth Reusing

Useful techniques include preserving rewards within rank bands, comparing
equilibria under changes on null sets, integrating normalized tail means, and
deriving globally optimal weights from utility curvature.

## 9. Generalizations, Conjectures, and Extensions

The welfare skill condition is strictly broader than log concavity.
For differentiable interior skill it is equivalent to
$(1-t)f'(t)/f(t)$ being nonincreasing. The quantile $1/(2-t)$ separates the
conditions. Every technology $p(e)=e^r,\ g(e)=e^s$, $r>1,\ 0<s\le1$,
satisfies the score-cost condition, including uniform skill on any
nondegenerate nonnegative interval. These are proved supporting extensions,
not extra source claims. The conditions are sufficient, not claimed necessary.
[Mathematical statement](docs/SOURCE_CLARIFICATIONS.md#proposition-31).

## 10. Source Clarifications and Exact Readings

The [memo](docs/SOURCE_CLARIFICATIONS.md) explains the local formula and proof
clarifications. The [weak and strict welfare comparisons](docs/SOURCE_CLARIFICATIONS.md#propositions-42-and-43-exact-under-clarified-weakstrict-interpretation)
need no additional economic assumption; derivative claims apply where the
derivative exists. The two substantive restrictions are stated in Section 6.

## 11. Paper Issues or Caveats

Proposition 3.1’s unrestricted cutoff-monotonicity claim and Proposition B.2’s
every-cutoff optimum have counterexamples. Their restricted versions are
proved under the conditions in Section 6.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) states each selected result;
[ProofInterface.lean](ProofInterface.lean) supplies its proof. The comparison
uses actual equilibrium score distributions and all feasible deviations.

## 13. Paper Assumption Provenance

The source cost, production, skill, policy, and equilibrium assumptions are
recorded in the [model review](FINAL_CLOSURE_RECEIPT.md).
The two additional sets of conditions are stated in Section 6.

## 14. Displayed Formula Provenance

The [source map](audit/paper_statement_map.json) links each named result and
its formulas to the formal statement. The memo distinguishes the restricted
claims from their unrestricted printed versions.

## 15. Library Lift Pass

The proof reuses the shared probability, measure, order, and convexity layers.
General tie-rank and probability-integral-transform work is available in the
shared foundation. Paper-specific population, incentive, and utility bridges
remain in the paper modules. The upper-tail skill and power-technology
extensions are proved locally; no external unpinned Lean code is imported.

## 16. DAG Audit

The [paper-facing DAG](docs/DependencyDAG.pdf) displays all 18 named results
and their governing mathematical dependencies. The two local restriction
nodes are distinct from ordinary clarified results, and B.1 has no fixed
budget. The diagram compiled and was visually inspected: labels, arrowheads,
reading order, and node boundaries are legible without overlap.
The [diagram source](docs/DependencyDAG.tex) is retained. The independent
terminal audit also passed.

## 17. Validation Checks

The paper build, independent mathematical review, final audit, and strict
closeout passed on September 9, 2026. The [closeout record](FINAL_CLOSURE_RECEIPT.md)
links the evidence. Human result annotations remain 0/18.

## 18. Paper Definitions Checked

The source inventory covers the scalar cost/production/skill model,
finite and two-level policies, actual tie-broken ranks, individual best
response and equilibrium, pure randomization and deterministic admission,
applicant/private/societal utility, group population and mixture ranks,
clipped group thresholds, welfare gaps and access, exchangeable multidimensional
costs, the hard-budget multitask model, and conditional weighted utility.
These are semantic declaration routes, not reflexive proof wrappers.

## 19. Named Theorem Statements Checked

Section 4 lists the ten main-text and eight appendix results. Their proofs
cover the domains and conditions stated there.

## 20. Statement and Validation Records

The [statement review](FINAL_CLOSURE_RECEIPT.md) and
[model review](FINAL_CLOSURE_RECEIPT.md) record the comparison
with the source. The [closeout record](FINAL_CLOSURE_RECEIPT.md) selects the
accepted evidence.

## 21. Source-Coverage Audit Ledger

The [source inventory](audit/paper_statement_map.json) includes all 18 named
results and their governing definitions. The unnumbered social-welfare
footnote remains supporting discussion, outside the selected theorem scope.
