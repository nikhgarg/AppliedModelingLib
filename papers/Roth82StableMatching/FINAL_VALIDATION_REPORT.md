# Final Validation Report: The Economics of Matching: Stability and Incentives

Updated: 2026-09-08

## 1. Human Verdict

Formalized for finite equal sides with complete strict preferences. The
checked results cover stable and side-optimal matching, proposing-side
truthfulness, manipulation impossibilities, and the efficient truthful
procedure. The broad extension to quotas is outside this named-result scope.

## 2. Closeout Status

- Completion status: formalized.
- Scope: ten named results, with their source definitions and model prerequisites.
- Human review: no annotations recorded.

## 3. Source and Scope

The audited source is Alvin E. Roth, *The Economics of Matching: Stability and
Incentives*, *Mathematics of Operations Research* 7(4), 1982. The canonical
local source artifact is `Roth82StableMatching.txt`, SHA-256
`55d2c35a8077a74dc9953dcb6f838fcd6e91edc9e77079a2419f185835a79fd4`.
The source record is linked to https://doi.org/10.1287/moor.7.4.617.

Normal scope follows the repository's named-theory policy. It includes the
paper-facing definitions of the preference profile, matching procedure,
marriage model, complete outcome, stability, individual quotas, stable
procedure, dominant truthfulness, efficiency, side-optimality, and simple
misrepresentation, together with every numbered theorem, corollary, and lemma.
Algorithms, the Section 6 numerical example, proof-local notation, proof
narration, and unnumbered extension prose are deep-only unless needed to prove
one of those endpoints.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Theorems 1–2 | **Exact.** |
| Theorems 3–5; Corollary 5.1; Lemmas 1–2 | **Exact.** |
| Theorems 6–7 | **Exact.** |
| Broad both-sided-quota extension | **Deferred:** the unnumbered claim is not used as credit for a general many-to-many incentive theorem. |

## 5. Remaining Boundaries and Gaps

No mathematical obligation remains in the configured normal named-theory
scope. The broad unnumbered assertion that all arguments carry over virtually
unchanged to arbitrary individual quotas is not used as source credit for a
general many-to-many incentive theorem. The paper's quota-outcome definition
is formalized with explicit finiteness of every partner set and exact finite
cardinality equal to the corresponding quota. The one-to-one
deferred-acceptance machinery used by the named results is checked through the
matching library. The exact many-to-one waiting-list runner is auxiliary quota
support. A future deep-paper review could formulate and prove a precise
responsive-preference theorem for the broad both-sided-quota model.

The proposal algorithms, termination narration, possible-partner notation,
serial-procedure narration, successful-misrepresentation shorthand, and the
Section 6 example remain support or deep-audit material under the normal-scope
policy. They are not missing named results.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

- Audit impossibility theorems against every true and reported profile used by
  the witness; a strictness condition on the true profile alone is not enough
  for a stable-procedure quantifier.
- When embedding a finite manipulation witness into a larger market, assign
  distinct positive fallback scores and force dummy self-matches through
  preference order. Do not use negative dummy scores when the source domain
  makes every pair feasible.
- State source definitions as closed equivalences and source theorems as closed
  propositions, then prove them separately. This exposes the full target even
  when the implementation uses many helper lemmas.
- Connect source algorithms to shared library implementations by a proved
  refinement theorem after establishing the source runner's own semantics.
- When a finite-cardinality API totalizes infinite sets, make finiteness an
  explicit conjunct before using its numeric result as a source quota.
- For incentive statements, audit both the original deviation and every
  existential replacement against the legal action space; checking only the
  truthful profile is insufficient.

## 9. Generalizations, Conjectures, and Extensions

The direct batched waiting-list runner and its refinement to applicant
deferred acceptance can support future many-to-one matching papers. A genuine
many-to-many version of Roth's broad quota sentence would require a precise
outcome model, responsive preferences over partner sets, acceptability and
outside-option conventions, and a separately proved stability and incentive
theorem. It is not obtained merely by cloning seats or renaming agents.

## 10. Source Clarifications and Exact Readings

None.

## 11. Paper Issues or Caveats

None for the selected results. The unproved broad quota extension is identified in Section 5.

## 12. Detailed Formalization Evidence

The current direct review selects ten named-result specifications in `PaperInterface.lean`, with twelve separately reviewed paper prerequisites. `MainTheorems.lean` contains the three-by-three manipulation witness and its positive, strict-preference arbitrary-rank extension. `GeneralMatching.lean` proves refinement of the source waiting-list procedure to the shared deferred-acceptance runner. The claim map binds the source statements to their expanded specifications; the accepted graph and current ledgers are linked in Section 17.

## 13. Paper Assumption Provenance

The paper-facing conditions are the equal finite sides and complete strict
preference profiles of the source marriage model, plus the exact
first-ranked-partner condition used by the source's simple-misrepresentation
reduction. Every true profile and every reported profile used by a stability
or incentive theorem is required to be legal. No stable outcome,
side-optimality conclusion, manipulation witness, or runner invariant is
accepted as a theorem premise.

The source-domain conditions are included in the current prerequisite review linked in Section 17.

## 14. Displayed Formula Provenance

The source has no separately selected displayed-equation item in the normal
inventory. Preference comparisons and blocking-pair clauses are audited inside
their complete definition or theorem proposition.



## 15. Library Lift Pass

The paper reuses the shared assignment, stability, proposer-optimality, and
deferred-acceptance infrastructure. The exact paper-facing model bridges and
finite counterexamples remain paper-local so their source semantics are
inspectable. The source waiting-list runner is connected to the shared runner
only by a proved refinement; shared declaration names supply no paper credit.

## 16. DAG Audit

The dependency-DAG source is `docs/DependencyDAG.tex`, with rendered artifact
`docs/DependencyDAG.pdf`. It shows the 21 source items, the checked
deferred-acceptance support route, and the broad quota prose as deep-only. It
does not promote support algorithms or the unchecked deep-only general quota extension to
normal source results.

**Codex current-protocol DAG inspection (2026-09-03, 21:30--21:31 EDT).** The
rendered one-page PDF was visually inspected at 160 dpi. Its source-definition
groups and ten named-result boxes were legible, the displayed arrows preserved
the result dependencies, and the deep-only quota material remained visually
separated from the normal result surface.

## 17. Validation Checks

The current [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) records 10 matching judgments. The [paper-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) has 12 entries and the [library-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) has 0. The [closure receipt](FINAL_CLOSURE_RECEIPT.md) points to the accepted obligation graph. These saved records distinguish semantic judgments from human annotations; this documentation edit does not reissue them.

## 18. Paper Definitions Checked

| Normal-scope source item | Lean specification and proof | Status |
| --- | --- | --- |
| Preference profile | `preferenceProfile_eq_source_definitionSpec`, `preferenceProfile_eq_source_definition` | Formalized |
| Matching procedure | `matchingProcedure_eq_source_definitionSpec`, `matchingProcedure_eq_source_definition` | Formalized |
| Complete strict marriage model | `sourceMarriageModel_iff_source_definitionSpec`, `sourceMarriageModel_iff_source_definition` | Formalized |
| Complete marriage outcome | `completeMarriageOutcome_iff_source_definitionSpec`, `completeMarriageOutcome_iff_source_definition` | Formalized |
| Stable marriage | `sourceStableMarriage_iff_source_definitionSpec`, `sourceStableMarriage_iff_source_definition` | Formalized |
| Side-optimal stable outcome | `sideOptimalStableOutcome_iff_source_definitionSpec`, `sideOptimalStableOutcome_iff_source_definition` | Formalized |
| Outcome filling individual quotas | `fillsIndividualQuotas_iff_source_definitionSpec`, `fillsIndividualQuotas_iff_source_definition` | Formalized with explicit finite partner sets |
| Stable matching procedure | `sourceStableMatchingProcedure_iff_source_definitionSpec`, `sourceStableMatchingProcedure_iff_source_definition` | Formalized |
| Dominant truthfulness for all agents | `truthfulForAllAgents_iff_source_definitionSpec`, `truthfulForAllAgents_iff_source_definition` | Formalized on legal reports |
| Efficient matching procedure | `efficientMatchingProcedure_iff_source_definitionSpec`, `efficientMatchingProcedure_iff_source_definition` | Formalized on legal reports |
| Simple report ranking the obtained partner first | `manReportStrictlyRanksPartnerFirst_iff_source_definitionSpec`, `manReportStrictlyRanksPartnerFirst_iff_source_definition` | Formalized |

The general `Assignment` carrier, score-table aliases, operational stability,
and deferred-acceptance state machinery remain visible support vocabulary. They
do not create extra normal-scope source items.

## 19. Named Theorem Statements Checked

| Named source result | Lean specification and proof | Status |
| --- | --- | --- |
| Theorem 1: a stable marriage exists | `theorem1_stable_outcome_existsSpec`, `theorem1_stable_outcome_exists` | Formalized |
| Theorem 2: both side-optimal stable outcomes exist | `theorem2_side_optimal_stable_outcomesSpec`, `theorem2_side_optimal_stable_outcomes` | Formalized |
| Theorem 3: no stable procedure is truthful for all agents | `theorem3_no_stable_truthful_procedureSpec`, `theorem3_no_stable_truthful_procedure` | Formalized on legal true and reported profiles |
| Theorem 4: an efficient truthful procedure exists | `theorem4_efficient_truthful_procedure_existsSpec`, `theorem4_efficient_truthful_procedure_exists` | Formalized |
| Theorem 5: the optimal stable procedure is truthful for the proposing side | `theorem5_optimal_side_truthfulSpec`, `theorem5_optimal_side_truthful` | Formalized in both proposal directions |
| Corollary 5.1: a first choice need not be misrepresented | `corollary5_1_first_choice_need_not_be_misrepresentedSpec`, `corollary5_1_first_choice_need_not_be_misrepresented` | Formalized with legal initial and replacement reports |
| Lemma 1: the simple replacement report returns the same partner | `lemma1_simple_report_same_partnerSpec`, `lemma1_simple_report_same_partner` | Formalized |
| Lemma 2: a profitable simple report harms no man | `lemma2_simple_report_harms_no_manSpec`, `lemma2_simple_report_harms_no_man` | Formalized |
| Theorem 6: no outcome is strictly better for every man | `theorem6_no_outcome_strictly_better_for_all_menSpec`, `theorem6_no_outcome_strictly_better_for_all_men` | Formalized |
| Theorem 7: manipulation can occur at every rank after first | `theorem7_later_choice_manipulation_unavoidableSpec`, `theorem7_later_choice_manipulation_unavoidable` | Formalized with positive strict dummy padding |

## 20. Paper-Facing Statement Validator Ledger

The current [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) records 10 matching judgments. The [paper-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) has 12 entries and the [library-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) has 0. The [closure receipt](FINAL_CLOSURE_RECEIPT.md) points to the accepted obligation graph. These saved records distinguish semantic judgments from human annotations; this documentation edit does not reissue them.

| Selected source item | Source-facing specification | Judgment |
| --- | --- | --- |
| `corollary5_1` | `corollary5_1_first_choice_need_not_be_misrepresentedSpec` | matches |
| `lemma1` | `lemma1_simple_report_same_partnerSpec` | matches |
| `lemma2` | `lemma2_simple_report_harms_no_manSpec` | matches |
| `theorem1` | `theorem1_stable_outcome_existsSpec` | matches |
| `theorem2` | `theorem2_side_optimal_stable_outcomesSpec` | matches |
| `theorem3` | `theorem3_no_stable_truthful_procedureSpec` | matches |
| `theorem4` | `theorem4_efficient_truthful_procedure_existsSpec` | matches |
| `theorem5` | `theorem5_optimal_side_truthfulSpec` | matches |
| `theorem6` | `theorem6_no_outcome_strictly_better_for_all_menSpec` | matches |
| `theorem7` | `theorem7_later_choice_manipulation_unavoidableSpec` | matches |

## 21. Source-Coverage Audit Ledger

The [source map](audit/paper_statement_map.json) retains the full source inventory and each item's disposition. The current selected direct results and their judgments are listed in Section 20; definitions and supporting source conditions are reviewed in the separate prerequisite ledger. Source inventory entries are not automatically counted as theorem proofs.
