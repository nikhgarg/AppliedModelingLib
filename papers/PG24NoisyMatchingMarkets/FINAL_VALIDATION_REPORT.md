# Final Validation Report: Wisdom and Foolishness of Noisy Matching Markets

Updated: 2026-09-05

## 1. Human Verdict

The four main attenuation and amplification theorems are proved with their
published conclusions.

**Formalization gap:** Proposition 1 and Propositions 7(ii)--8 have their
qualitative limits proved, while the source polynomial rates remain unproved.
[Details](docs/SOURCE_CLARIFICATIONS.md).

## 2. Closeout Status

- Completion status: formalized for the four main theorems and selected appendix conclusions; three appendix polynomial rates remain unproved.
- Scope: the four main theorems and fifteen named appendix results.
- Human review: no annotations recorded.

## 3. Source and Scope

The source is [*Wisdom and Foolishness of Noisy Matching Markets*](https://arxiv.org/abs/2402.16771)
by Kenny Peng and Nikhil Garg. The formalized scope includes the basic and
extended coalition economies; Hölder value-law and capacity regularity;
beta-max-concentrating and long-tailed noise; cutoff stability and match
probability; Theorems 1--4; and the named results in the attenuation and
amplification appendices. Simulations, figures, examples, and narrative
interpretation are outside the mathematical source inventory.

The two source-model bundles were checked as prerequisites and do not contain
the theorem conclusions they support.

## 4. Researcher Summary of Checked Results

| Result | Comparison with the paper |
| --- | --- |
| Theorems 1–4 | **Exact.** |
| [Proposition 1](docs/SOURCE_CLARIFICATIONS.md#proposition-1-tail-orientation-and-unproved-polynomial-rate) | **Tail typo fixed; polynomial-rate proof gap:** matched mass below the threshold replaces the impossible printed upper-tail display. Uniform qualitative vanishing is proved; the intended `O(C^{-K(β,γ)})` rate remains unproved. |
| Propositions 2–5 and Lemma 6 | **Exact.** |
| Proposition 7(i) | **Exact.** |
| [Proposition 7(ii) and Proposition 8](docs/SOURCE_CLARIFICATIONS.md#proposition-7ii-and-proposition-8-unproved-polynomial-rates) | **Proof gaps:** qualitative convergence is proved, while both printed polynomial rates remain unproved. No counterexample refutes either rate under the full source assumptions. |
| Propositions 9–10; Lemmas 11–13; Propositions 14–15 | **Exact.** |
| [Coalition conditional laws](docs/SOURCE_CLARIFICATIONS.md#coalition-conditional-laws) | **Statement clarified:** conditional kernels are specified almost everywhere on the value-law support. |

## 5. Source Corrections and Clarifications

1. **Proposition 1 tail orientation and rate.** The printed upper-tail
   negative-power display is impossible when limiting supply is positive. The
   surrounding prose, footnote, and Theorem 1 use matched mass below the
   threshold. The corrected lower-tail conclusion is proved qualitatively;
   its intended polynomial rate remains unproved.
2. **Proposition 7(ii) and Proposition 8 rates.** The printed route applies a
   one-draw lower-tail estimate that has not been derived from the paper's
   maximum-concentration assumption. The formalization proves the qualitative
   full-affordance and integral limits needed downstream, but not the printed
   rates.
3. **Proof-only corrections.** The proofs of Propositions 2–5 and Lemma 6
   contain sign, endpoint, event-inclusion, and maximum-growth slips. Their
   displayed conclusions are proved by corrected arguments. The amplification
   appendix also needs an endpoint correction in Proposition 9 and atom-safe
   complements in its product argument.
4. **Coalition conditional law.** The paper's conditional-law wording is
   understood on the value-law support (almost everywhere). This is the
   standard measure-theoretic reading; the theorem endpoints use the literal
   iid affordance law and Theorem 4's exception set is measured under that
   same value law.

For source locations and concise mathematical explanations, see the
[source clarifications](docs/SOURCE_CLARIFICATIONS.md).

## 6. Additional Assumptions Beyond Paper

None in the checked endpoints. A suitable
[one-draw lower-tail bound](docs/SOURCE_CLARIFICATIONS.md#proposition-7ii-and-proposition-8-unproved-polynomial-rates)
would support the printed Proposition 7(ii) route and its downstream
polynomial rates, but the current formalization neither assumes such a bound
nor derives it from maximum concentration.

## 7. Proof-Strategy Deviations

The attenuation proof uses a source-faithful finite dense-cluster/large-gap
construction with natural-number rounding, a genuine cutoff partition, exact
capacity accounting, and atom-safe event bounds. The amplification proof uses
an interior support anchor and finite long-tail shifts to transport the
quantile-window estimate to an arbitrary real target. The exact local replacements and their reasons are in the
[appendix memo](docs/SOURCE_CLARIFICATIONS.md#other-appendix-proof-corrections).

## 8. Reusable Formal Infrastructure

The proofs consume existing reusable probability, finite-product,
order-statistic, and cutoff-market infrastructure. Paper-specific cutoff
geometry, coalition witnesses, and source corrections remain paper-local.
The direct review checks reusable declarations by exact Lean body and source
connection; it does not treat a declaration name or an imported theorem as
semantic evidence.

## 9. Generalizations, Conjectures, and Extensions

No additional generalization is claimed.

## 10. Source Clarifications and Exact Readings

The [source memo](docs/SOURCE_CLARIFICATIONS.md) supplies the exact tail/rate qualifications in Section 5 and proof replacements in Section 7.

## 11. Paper Issues or Caveats

The polynomial rates in Proposition 1, Proposition 7(ii), and Proposition 8
remain unproved. The qualitative replacements suffice for Theorems 1–4. The
missing one-draw estimate has not been derived from maximum concentration, and
no counterexample here refutes the full source rate claims.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) exposes the two source models, the
four main theorems, and the selected attenuation/amplification appendix claims
as transparent targets. [ProofInterface.lean](ProofInterface.lean) contains
their checked endpoints, including the lower-tail and qualitative-rate repairs
identified in Sections 4--5.

## 13. Paper Assumption Provenance

No additional assumption beyond the source models is used. Four primitive
model rows have current matching judgments in the
[paper-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md). Coalition
conditional laws use the almost-everywhere support reading stated in Section 4.

## 14. Displayed Formula Provenance

[The source map](audit/paper_statement_map.json) binds beta-max concentration,
long-tail noise, cutoff stability, match probabilities, capacity rounding,
tail events, and appendix rate displays. The
[source memo](docs/SOURCE_CLARIFICATIONS.md) records the corrected tail
orientation, qualitative replacements, and local proof-formula fixes.

## 15. Library Lift Pass

The proofs use reusable probability, finite-product, order-statistic, and
cutoff-market infrastructure. Paper-specific cutoff geometry, coalition
witnesses, and source corrections remain paper-local; no separate material
library review row is selected by the current graph.

## 16. DAG Audit

[The dependency DAG](docs/DependencyDAG.pdf) groups the literal models, four
main theorems, and fifteen appendix endpoints by proof role. Its retained
2026-09-05 visual inspection found readable labels and arrow directions, with
no clipping, node overlap, or edge crossing through node interiors.

## 17. Validation Checks

The accepted graph records twenty-five matching direct source-to-Spec
judgments and four matching model prerequisites. The coverage ledger separates
ten direct covered items from fifteen support-only appendix items. Retained
focused paper builds and the independent source review passed. See the
[accepted graph](audit/obligation_evidence/current_accepted_graph.json) and
[closure receipt](FINAL_CLOSURE_RECEIPT.md).

## 18. Paper Definitions Checked

Checked definitions include the holder/value and capacity models,
beta-max-concentrating and long-tailed noise, stable-matching cutoffs, match
probability, attenuation/amplification events, coalition value laws, and the
finite rounding and support constructions used in the appendices.

## 19. Named Theorem Statements Checked

- Theorems 1--4: attenuation, amplification, and their coalition versions.
- Appendix attenuation route: corrected Proposition 1; Propositions 2--5;
  Lemma 6; and Propositions 7--8.
- Appendix amplification route: Proposition 9; Proposition 10; Lemmas 11--13;
  and Propositions 14--15.

## 20. Paper-Facing Statement Validator Ledger

The direct comparisons are in the
[source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md); model rows
are in the [paper-prerequisite ledger](FINAL_CLOSURE_RECEIPT.md),
and correction provenance is in
[source-proof fidelity](FINAL_CLOSURE_RECEIPT.md).

## 21. Source-Coverage Audit Ledger

The [coverage ledger](FINAL_CLOSURE_RECEIPT.md) records ten direct covered
items and fifteen support-only items. [The source map](audit/paper_statement_map.json)
also retains the primitive models and correction records. The four main
theorems keep their source conclusions; the appendix rate qualifications remain
visible in Sections 4--5 rather than being counted as exact printed rates.
