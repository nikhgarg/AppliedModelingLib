# Final Validation Report: Axioms for AI Alignment from Human Feedback

Updated: 2026-09-27

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
| [Lemma 3.4](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#lemmas-3435-the-perturbation-seam) | **Exact.** At the literal zero-perturbation endpoint, each copy has the same feature vector as its original, so the printed weak inclusion holds for every parameter. |
| [Lemma 3.5](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#lemmas-3435-the-perturbation-seam) | **Corrected target.** The literal weak inclusion supplies no margin; a strict positive-perturbation cone and closed-half-space objective gap establish the conclusion used by Theorem 3.1. |
| [Footnote 7 witness](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#six-candidate-feasibility-witness) | **Exact witness after correcting the parameter typo:** parameter `(delta,2)` replaces `(1,1)`. |
| [Theorem 4.3](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#rule-level-tie-conventions) | **Exact under a necessary source clarification:** every fixed, profile-independent injective candidate priority is covered. A profile-dependent tie selector is formally refuted, so the unqualified rule-level reading is false. |
| [Theorem C.2](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#rule-level-tie-conventions) | **Exact under its displayed score-order-consistent tie condition.** |
| [Theorem C.6](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#rule-level-tie-conventions) | **Exact under a necessary source clarification:** every fixed, profile-independent injective candidate priority is covered. The checked profile-dependent selector refutes the unqualified rule-level reading. |
| [Theorem C.3](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#rule-level-tie-conventions) | **Exact under a source-definedness clarification.** Every contraction-consistent linear-Kemeny selector satisfies PMC and separability; fixed profile-independent injective priority is a checked special case. PMC itself is tie-independent because a feasible PMC ranking is the unique minimizer. |
| [Theorem C.5](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#rule-level-tie-conventions) | **Exact.** The first-profile six-ballot classification invoked by the source proof is now derived from the explicit Pareto-constrained Kemeny equality case; a matching appendage covers every selected ballot, with no `v1` tie choice or global tie key. |

## 5. Remaining Boundaries and Gaps

Theorem C.5 derives the source proof's first-profile finite output
classification directly from Pareto-constrained Kemeny minimality. It does not
assume a particular `v1` choice: each of the six possible input-ballot outputs
has a checked matching appendage. Theorem 4.3 and Theorem C.6 have no remaining
selector-model gap under their stated fixed-priority conventions. Theorem C.3
has no remaining gap under contraction consistency of a linear-Kemeny selector.
For C.6, the formal counterexample rules out the broader
arbitrary-selector reading; whether a weaker stable selection law would
suffice remains open.

Lemma 3.4 is a literal zero-endpoint result. Its separate strict
positive-perturbation cone is the supporting margin for the corrected
Lemma 3.5 closed-half-space argument, which proves Theorem 3.1 with its
original assumptions and conclusion.

## 6. Additional Assumptions Beyond Paper

The checked LCPO and leximax-plurality rule-level results use fixed,
profile-independent tie priorities selecting among source-eligible outcomes.
A single-valued rule need not in general have such a priority, so this is the
stated scope of those formalized rule families, not an automatic consequence
of being a function. Linear Kemeny is instead checked for every
contraction-consistent selector: if a selected equal-objective minimizer remains
available after the minimizer set contracts, it remains selected. This is the
precise consistency needed by the source's additive argument; fixed ranking
priority is one checked implementation. Theorem C.5 derives its local finite
input-ballot classification; it adds neither a particular `v1` choice nor a
global tie rule.

The Lean selector predicates are total over finite ranking profiles, whereas
the paper calls a profile only when every submitted ranking is feasible. Thus
the C.6 priority theorem proves a deliberately stronger all-profile extension;
the source-feasible input restriction is represented by `FeasibleProfile` in
the axioms that carry such a guard, while the reusable `RankingSeparability`
predicate is global. This carrier convention is distinct from, and does not
repair, the required fixed-priority tie condition.

[The source clarifications and corrections memo](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md)
explains these scopes. It does not infer that the paper's claims fail for
other selectors merely because the current statements use these choices.

## 7. Proof-Strategy Deviations

- Lemma 3.4 is proved at its literal weak zero-perturbation endpoint. Its distinct strict positive-perturbation cone is then used with a closed-half-space objective gap to repair Lemma 3.5 and prove the same Theorem 3.1.
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

Footnote 7's six-candidate ranking uses parameter `(delta,2)` in place of
`(1,1)`; see the [witness note](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md#six-candidate-feasibility-witness).
The Lemma 3.4 weak inclusion is direct and literal; only Lemma 3.5 requires the
documented strict-cone correction. Theorem C.3 uses the source-definedness
condition of contraction-consistent Kemeny tie selection, whereas the LCPO and
leximax results retain their documented fixed-priority scopes. Sections 6–7
cover the remaining statement scopes and proof changes.

## 11. Paper Issues or Caveats

Section 7 explains the proof replacements and misplaced example attribution. Section 6 states the rule-selection scope; Section 10 links the exact local corrections.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) exposes fifteen transparent result
contracts: Definition 2.2 with its consequences, the main-text theorem chain,
the Appendix-B construction, and Theorems C.2--C.6. [ProofInterface.lean](ProofInterface.lean)
supplies one exact-type proof endpoint for each. Other numbered definitions and
rule presentations route through their semantic declarations.

## 13. Paper Assumption Provenance

`Assumptions.lean` introduces no paper-local axiom. Nine material paper-local
and twenty-two reusable-library prerequisites selected by the Lean graph have
current matching source-connected judgments in the
[paper](FINAL_CLOSURE_RECEIPT.md) and
[library](FINAL_CLOSURE_RECEIPT.md) ledgers.

## 14. Displayed Formula Provenance

[The source map](audit/paper_statement_map.json) binds the feature tables,
linear losses, majority and Pareto conditions, Kemeny disagreement, LCPO,
Pareto-Kemeny, and leximax-plurality formulas to the source. Lemma 3.4 is
bound to its literal zero-endpoint source statement; Lemma 3.5 uses the
documented corrected target in the
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
The regenerated human-review packet was likewise checked on its changed Lemma
3.4 and Theorem C.3 cards; both the byte-pinned source excerpts and current
Lean routes are readable.

## 17. Validation Checks

The current source-to-Spec ledger contains fifteen direct judgments: thirteen
literal source matches and two documented corrected targets. The current
paper- and library-prerequisite ledgers and focused interface/root build receipt
provide the pre-closeout evidence. The strict transaction will issue the
[accepted graph](audit/obligation_evidence/current_accepted_graph.json) and
closure receipt only after the frozen-surface audit passes.

## 18. Paper Definitions Checked

Checked definitions include the linear-ranking model; Definitions 2.1, 2.2,
4.1, 4.2, and C.1; and the standard-loss, majority-loss, C1, LCPO,
linear-Kemeny, Pareto-Kemeny, and leximax-plurality rule presentations.

## 19. Named Theorem Statements Checked

- Theorem 3.1 and Lemmas 3.2--3.5: the loss-based impossibility chain, with
  Lemma 3.4 literal at its zero endpoint and Lemma 3.5 on its corrected target.
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
bundles. Every selected result has a direct current judgment. The final closure
receipt binds the accepted graph to the current source, interface, proof, and
prerequisite evidence when strict validation completes.
