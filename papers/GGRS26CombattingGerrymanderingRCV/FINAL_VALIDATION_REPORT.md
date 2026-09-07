# Final Validation Report: GGRS26 Combatting Gerrymandering with Ranked Choice Voting

Updated: 2026-09-02

## 1. Human Verdict

The formalization proves Lemma C.1 and Proposition 1: in the stated two-party
solid-coalition model, STV and PAV give each party proportional floor-or-ceiling
seat rounding. The STV result covers every reachable outcome for the admitted
surplus-preserving transfer rules.

The proof uses the exact finite floor-Droop quota; no extra turnout-divisibility
assumption is needed. The [quota note](docs/SOURCE_CLARIFICATIONS.md) states the
inequalities and unchanged electoral model.

## 2. Closeout Status

- Completion status: formalized.
- Selected named results: Lemma C.1 and Proposition 1.
- The redistricting, empirical, and simulation material is outside this theorem scope.

## 3. Source and Scope

The audited source is the published paper, *Combatting Gerrymandering with
Ranked Choice Voting: an Experimental Analysis of Multi-member Districts in the
United States*, available from [Operations Research](https://doi.org/10.1287/opre.2024.1167).

The selected normal paper surface contains two named results. Four source
definitions—the Thiele/PAV rule, STV rule, solid-coalition voter model, and
party-seat selector—are retained only as the material semantic context needed
to interpret those results. Footnote 10 repeats the PAV characterization later
labelled Lemma C.1, and Appendix C repeats Proposition 1; these are alternate
presentations of the same claims, not additional results.

Section 2.1 states the population-ratio band as `(N_k +/- epsilon)/N`. Its
attached footnote specifies `P_ideal = P_total/N`,
`P_k in [N_k P_ideal +/- tau P_ideal/L]`, and
`delta_k = tau/(L N_k)`. These exact clauses are preserved as source-only
deep-audit context at `cited publication:310-319` and `cited publication:348-355`; neither
selected result materially depends on them. Empirical data, map generation,
simulations, figures, and runtime measurements likewise remain outside the
selected theorem-formalization scope.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Lemma C.1 | **Exact.** |
| Proposition 1 | **Exact.** |

## 5. Remaining Boundaries and Gaps

None within the selected mathematical scope. The current support relation
formalizes all outcomes allowed by random within-party tie breaking; it does
not state a tie-breaking probability law or make a distributional conclusion.
This is the scope of Proposition 1 over all reachable election paths.

Empirical data, map generation, simulation outcomes, figures, runtime
measurements, and Section 2.1 redistricting/tolerance prose are outside the
selected theorem-formalization scope.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

The Appendix C proof temporarily simplifies the Droop-quota arithmetic by
assuming turnout is divisible by `M+1`, although Proposition 1 does not impose
that condition. The formal proof replaces that shortcut with exact floor-Droop
arithmetic for every turnout covered by the proposition. The
[quota note](docs/SOURCE_CLARIFICATIONS.md#proposition-1-floor-droop-arithmetic)
gives the exact inequalities.

## 8. Proof Tricks Worth Reusing

- State a family of STV transfer rules through the invariants the paper uses:
  a quota election removes exactly one quota from the winner's support,
  preserves off-support weights, and keeps all weights nonnegative.
- Prove both existence of a terminal execution and the desired statement for
  every reachable terminal, so the universal outcome claim is nonvacuous.
- Define a tie-broken finite optimizer relationally, then construct the
  selected optimizer and prove its least-co-maximizer property.

## 9. Generalizations, Conjectures, and Extensions

No distributional strengthening is claimed. Proposition 1 keeps the paper's
D-favoring cross-party tie convention and proves the result for every terminal
in the full support of its random within-party rule. Its generic transfer-rule
quantifier follows the paper's stated transfer-rule independence. The
development also contains fractional-STV specializations and map-level
support, but they do not enlarge the selected result surface.

## 10. Source Clarifications and Exact Readings

The turnout-divisibility proof change is described in Section 7 and the [quota note](docs/SOURCE_CLARIFICATIONS.md).

## 11. Paper Issues or Caveats

None.

## 12. Detailed Formalization Evidence

The selected surface has two direct contracts:

| Source result | Semantic target | Proof endpoint |
| --- | --- | --- |
| Lemma C.1 | `paper_lemma_c1_pav_selector_eq_unique_integer_intervalSpec` | `paper_lemma_c1_pav_selector_eq_unique_integer_interval` |
| Proposition 1 | `paper_proposition1_source_selected_stv_and_pavSpec` | `paper_proposition1_source_selected_stv_and_pav` |

Proposition 1 quantifies over every surplus-preserving transfer policy in the
source model and proves both terminal existence and the rounded party-seat
claim for every reachable terminal; no precomputed run or result certificate
is assumed.

## 13. Paper Assumption Provenance

No paper-facing axiom or added formalization assumption supplies either
conclusion. The visible premises are the paper's vote-share, turnout,
candidate-count, ballot, tie-breaking, and transfer-rule conditions. The
[paper-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md) and
[library ledger](FINAL_CLOSURE_RECEIPT.md) record current matches for
the graph-selected prerequisites.

## 14. Displayed Formula Provenance

Equation (1), the two-party Thiele objective, supplies the PAV selector used by
both results; Proposition 1 concludes with the floor-or-ceiling seat-share
formula. [The source map](audit/paper_statement_map.json) binds these formulas
to their source presentations without creating duplicate named-result rows.

## 15. Library Lift Pass

The shared layer provides harmonic PAV scoring and first-active-candidate
lookup. The paper-local layer retains the two-party selector, transfer-policy
family, solid-coalition profiles, STV execution, and theorem statements.

## 16. DAG Audit

[The dependency DAG](docs/DependencyDAG.pdf) separates the PAV and STV routes
and marks empirical maps, simulations, figures, and runtime as out of scope.
The retained visual inspection found readable labels, unobscured arrows, and
no clipping or node overlap.

## 17. Validation Checks

Retained focused interface builds passed. The current review graph records two
matching direct results, forty-four matching paper-local prerequisites, and
twelve matching reusable-library prerequisites. The
[accepted graph](audit/obligation_evidence/current_accepted_graph.json) and
[closure receipt](FINAL_CLOSURE_RECEIPT.md) bind this surface; this prose pass
did not rerun Lean or semantic review.

## 18. Paper Definitions Checked

Checked definitions include Thiele/PAV committee scoring, the two-party seat
selector, complete ranked ballots, first-active tallying, floor-Droop quota,
quota election and elimination, surplus-preserving transfers, tie support,
terminal states, and the solid-coalition electorate.

## 19. Named Theorem Statements Checked

- **Lemma C.1:** the selected PAV Republican-seat count is the unique integer
  in the source half-open interval for positive Republican vote share.
- **Proposition 1:** STV and PAV return the source rounded party-seat shares for
  every admitted turnout and every reachable terminal under the stated tie and
  transfer conventions.

## 20. Paper-Facing Statement Validator Ledger

The two direct comparisons are in the
[source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md). Their model
and library dependencies are reviewed in the prerequisite ledgers, and the
[source-fidelity record](FINAL_CLOSURE_RECEIPT.md) documents the
turnout-arithmetic proof replacement.

## 21. Source-Coverage Audit Ledger

[The source map](audit/paper_statement_map.json) retains both selected results,
their four governing definitions, repeated presentations, and explicit scope
exclusions. Both direct result rows have current matching judgments. Empirical
and redistricting material remains outside the selected theorem scope stated
in Sections 3 and 5.
