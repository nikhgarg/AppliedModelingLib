# Final Validation Report: Axioms for AI Alignment from Human Feedback

Updated: 2026-09-08

## 1. Human Verdict

The linear social-choice impossibilities and rule properties are proved on the
stated selector domains, and Theorem 3.1 retains its source assumptions and
conclusion.

## 2. Closeout Status

- Completion status: formalized.
- Scope: thirteen named results, the attached main-text consequences, and the Appendix B construction.
- Human review: no annotations recorded.

## 3. Source and Scope

The source is Luise Ge, Daniel Halpern, Evi Micha, Ariel D. Procaccia, Itai
Shapira, Yevgeniy Vorobeychik, and Junlin Wu,
[*Axioms for AI Alignment from Human Feedback*](https://arxiv.org/abs/2405.14758),
NeurIPS 2024.

The governing artifact is the published conference PDF and its paper-local,
byte-pinned text extraction. The inventory covers the linear-ranking model;
Definitions 2.1, 2.2, 4.1,
4.2, and C.1; the standard-loss, majority-loss, C1, LCPO, linear-Kemeny,
Pareto-Kemeny, and leximax-plurality rule presentations; and every named result
from Theorem 3.1 through Theorem C.6.

Exact source spans, semantic contexts, and Lean routes are in
`audit/paper_statement_map.json`. The result specifications are in
`PaperInterface.lean`; their proof endpoints are in `ProofInterface.lean`.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Definition 2.2; Lemmas 3.2–3.3; Theorems 3.6–3.7; Appendix B; Theorem C.4 | **Exact.** |
| [Theorem 3.1, positive-input branch](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#theorem-31-positive-input-branch-restricted-infimum-sign) | **Exact impossibility conclusion after correcting the sign typo:** reverse the printed restricted-infimum sign; the impossibility conclusion is unchanged. |
| [Lemmas 3.4–3.5](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#lemmas-3435-the-perturbation-seam) | **Changed statements:** a strict minimizer cone and closed-half-space objective gap replace the invalid weak-inclusion route; Theorem 3.1 is unchanged. |
| [Footnote 7 witness](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#six-candidate-feasibility-witness) | **Exact witness after correcting the parameter typo:** parameter `(delta,2)` replaces `(1,1)`. |
| [Theorem 4.3; Theorems C.2–C.3; Theorem C.6](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#rule-level-tie-conventions) | **Restricted scope:** fixed profile-independent tie keys. The broader selector claims remain unproved; necessity of fixed keys is unknown. |
| [Theorem C.5](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#rule-level-tie-conventions) | **Source clarification with formal witness:** the first-profile output `v1` is an explicit necessary tie choice for this proof route; `c4Ranking_v2_isParetoKemenyMinimizer` exhibits a distinct competing minimizer. |

## 5. Remaining Boundaries and Gaps

Theorem C.5's proof route requires the explicit first-profile tie choice,
which is now justified by a formal competing-minimizer witness. Theorem 4.3
and Theorems C.2–C.3/C.6 retain their fixed-key selector scope; removing
those keys remains an open selector-model obligation.

The strict-cone and closed-half-space arguments for Lemmas 3.4–3.5 do prove Theorem 3.1 with its original assumptions and conclusion.

## 6. Additional Assumptions Beyond Paper

The checked LCPO and leximax-plurality rule-level results use fixed,
profile-independent tie keys selecting among source-eligible outcomes. A
single-valued rule need not in general have such keys, so this is the stated
scope of those formalized rule families, not an automatic consequence of
being a function. Theorem C.5 instead retains the source proof's local choice
of its first-profile output as an explicit premise.

[The source clarifications and corrections memo](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md)
explains these scopes. It does not infer that the paper's claims fail for
other selectors merely because the current statements use these choices.

## 7. Proof-Strategy Deviations

- Lemmas 3.4–3.5 replace the weak zero-perturbation/open-set argument with a strict minimizer cone and a closed-half-space objective gap, proving the same Theorem 3.1.
- The positive-input branch reverses its restricted-infimum sign; [Appendix A.1](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#appendix-a1-one-sided-derivatives) uses one-sided derivatives and consistent point scaling.
- The [paragraph after Theorem 3.7](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#post-theorem-37-proof-location-sentence) attributes Appendix B's infeasible PMC ranking to Appendix A.6, whose majority relation is cyclic.

The [memo](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md) gives the exact changes. Rule-selection restrictions are in Section 6.

## 8. Proof Tricks Worth Reusing

- Express a linear-ranking rule as a finite selector with one stable tie key,
  then prove the social-choice axioms at the rule level.
- Separate nonattainment of a parameter minimum from attainment of a ranking-
  restricted infimum, matching the paper's loss-minimizing-rule definition.
- For perturbative optimizer arguments, prove a strict source-visible cone
  first and take the gap on a closed bad set rather than invoking openness from
  a weak boundary relation.
- Evaluate a large finite feature or score table once in a symbolic lemma;
  downstream comparisons should use focused rewrites and arithmetic.

## 9. Generalizations, Conjectures, and Extensions

The reusable library now supports finite feasible-ranking domains, linear
reward parameters, Pareto and majority axioms, C1 rules, Kemeny disagreement,
LCPO-style lexicographic selectors, and stable tie-broken rule families. The
paper-local constructions retain their exact feature tables and profiles.

## 10. Source Clarifications and Exact Readings

Footnote 7's six-candidate ranking uses parameter `(delta,2)` in place of `(1,1)`; see the [witness note](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#six-candidate-feasibility-witness). Sections 6–7 cover the other statement scopes and proof changes.

## 11. Paper Issues or Caveats

Section 7 explains the proof replacements and misplaced example attribution. Section 6 states the rule-selection scope; Section 10 links the exact local corrections.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) exposes fifteen transparent result
contracts: Definition 2.2 with its consequences, the main-text theorem chain,
the Appendix-B construction, and Theorems C.2--C.6. [ProofInterface.lean](ProofInterface.lean)
supplies one exact-type proof endpoint for each. Other numbered definitions and
rule presentations route through their semantic declarations.

## 13. Paper Assumption Provenance

`Assumptions.lean` introduces no paper-local axiom. Eight material paper-local
and twenty-one reusable-library prerequisites selected by the Lean graph have
current matching source-connected judgments in the
[paper](FINAL_CLOSURE_RECEIPT.md) and
[library](FINAL_CLOSURE_RECEIPT.md) ledgers.

## 14. Displayed Formula Provenance

[The source map](audit/paper_statement_map.json) binds the feature tables,
linear losses, majority and Pareto conditions, Kemeny disagreement, LCPO,
Pareto-Kemeny, and leximax-plurality formulas to the source. Lemmas 3.4--3.5
use documented corrected targets in the
[clarification memo](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md).

## 15. Library Lift Pass

Reusable components include rankings and profiles, finite linear reward
models, feasible rankings, Pareto and majority axioms, C1 rules, Kemeny
disagreement and selectors, LCPO, Pareto-Kemeny, and leximax-plurality. The
loss-specific optimizers, source feature tables, and finite counterexamples
remain paper-local.

## 16. DAG Audit

[The dependency DAG](docs/DependencyDAG.pdf) shows the Lemma 3.2--3.5 route to
Theorem 3.1, keeps attached prose with Definition 2.2 and Theorem 3.7, and
separates Appendix B and the Appendix-C rules. The retained visual inspection
found readable labels, correct arrow direction, and no obscuring overlap.

## 17. Validation Checks

The accepted graph binds fifteen direct judgments, of which twelve match the
source literally and three match documented corrected targets, together with
eight paper and twenty-one library prerequisite matches. Retained focused
interface/root builds passed. See the
[accepted graph](audit/obligation_evidence/current_accepted_graph.json) and
[closure receipt](FINAL_CLOSURE_RECEIPT.md); no new semantic review was run.

## 18. Paper Definitions Checked

Checked definitions include the linear-ranking model; Definitions 2.1, 2.2,
4.1, 4.2, and C.1; and the standard-loss, majority-loss, C1, LCPO,
linear-Kemeny, Pareto-Kemeny, and leximax-plurality rule presentations.

## 19. Named Theorem Statements Checked

- Theorem 3.1 and Lemmas 3.2--3.5: the loss-based impossibility chain, with
  Lemmas 3.4--3.5 on corrected targets.
- Theorems 3.6--3.7 and 4.3, plus the Appendix-B construction: the majority/C1
  conclusions, fixed-tie LCPO, and explicit infeasible profile.
- Theorems C.2--C.6: the Copeland/LCPO, linear-Kemeny, Pareto-Kemeny, and
  leximax-plurality characterizations and impossibilities.

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) records
the fifteen direct comparisons. Premise judgments are in the paper and library
ledgers, and [source-proof fidelity](FINAL_CLOSURE_RECEIPT.md) records
the corrected-source routes.

## 21. Source-Coverage Audit Ledger

[The source map](audit/paper_statement_map.json) inventories the governing
model, definitions, rule presentations, named results, and attached prose
bundles. Every selected result has a direct current judgment, and the
[accepted graph](audit/obligation_evidence/current_accepted_graph.json) binds
the current source, interface, proof, and prerequisite evidence.
