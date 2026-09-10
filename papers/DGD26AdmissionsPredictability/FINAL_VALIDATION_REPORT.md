# Final Validation Report: Capacity Constraints Make Admissions Processes Less Predictable

Updated: 2026-09-08

## 1. Human Verdict

The formalization covers the finite-choice results relating capacity,
substitutability, instability, and variability, together with fixed- and
rank-threshold prediction, the abstract NYC priority-queue procedures, and
real-weight linear-assignment admissions.

The exact nonzero-variability claims use positive capacity smaller than the
applicant universe. The NYC results concern the paper's abstract procedures;
they do not verify a program-by-program empirical implementation.

## 2. Closeout Status

- Completion status: formalized.
- Selected scope: 64 source-facing claims, including all five Proposition 2
  procedure claims, and the binary-classifier model used by the ML application.
- The checked mathematical scope includes the real-weight assignment model.
  Conditions and exact corrected displays are described below; the technical
  source and proof records remain in Sections 12 onward.

## 3. Source and Scope

The primary review artifact is the pinned AAAI-26/arXiv source surface with
SHA-256 `e550e1a07d28f2b59bd55f1733964d0a5b7db85bdff60e3b20b788e3a842130d`.
The public source is https://arxiv.org/abs/2601.11513.
The audit read the canonical archived TeX surface before comparing the selected
source claims with the Lean interface. Scope includes the selected definitions,
displayed model formulas, and named results, including the five Proposition 2
claims as abstract queue-procedure results.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Theorem 1, substitutability and instability | **Exact.** |
| Theorem 1, no-zero and exact-one claims | **Necessary domain restriction:** $0<q<\lvert U\rvert$; zero or nonbinding capacity permits instability zero. [Domain](docs/SOURCE_CLARIFICATIONS.md#capacity-variability-and-queue-representation). |
| Proposition 1, fixed-threshold clause | **Exact.** |
| Proposition 1, rank-threshold clauses | **Exact with source clarification:** a fixed tie order specifies rank selection; the instability/variability bounds and exact-one score construction are proved. [Selector](docs/SOURCE_CLARIFICATIONS.md#scores-strict-orders-and-assignment-choices). |
| Theorem 2 | **Exact with source clarification:** variability one means representability by one priority order, regardless of redundant queue copies. The range uses positive binding capacity. [Details](docs/SOURCE_CLARIFICATIONS.md#capacity-variability-and-queue-representation). |
| Proposition 2 | **Exact for the abstract queue procedures.** |
| Lemma A.6, consistency of removable sets | **Exact after correcting the equality typo:** equal choices on two pools imply equality of their removable sets, replacing the printed self-equality. [Correction](docs/SOURCE_CLARIFICATIONS.md#exact-appendix-corrections). |
| Corollary A.3, no consistent tightly-even instability | **Exact after correcting the parameter typo:** the instability parameter is the positive even value $d=2k$ with $k>0$. [Correction](docs/SOURCE_CLARIFICATIONS.md#exact-appendix-corrections). |
| Theorems A.1–A.9; Lemmas A.1–A.5 and A.7; Corollaries A.1–A.2 | **Exact under the [capacity conditions above](docs/SOURCE_CLARIFICATIONS.md#capacity-variability-and-queue-representation).** |
| Lemma A.8 and Theorems A.10–A.11, linear-assignment admissions | **Exact with source clarification:** a fixed generic refinement specifies the choice among tied optimal assignments. [Tie rule](docs/SOURCE_CLARIFICATIONS.md#scores-strict-orders-and-assignment-choices). |

## 5. Remaining Boundaries and Gaps

None within the selected mathematical source-claim scope. The abstract
Proposition 2 procedures are formalized; empirical implementation and
simulation claims are outside the paper's mathematical theorem target. Human
release certification is separate and is not claimed.

## 6. Additional Assumptions Beyond Paper

The exact nonzero-variability results use positive binding capacity
$0<q<|U|$, where $q$ is capacity and $U$ the applicant universe. Zero or
nonbinding capacity permits constant admission decisions.

The [memo](docs/SOURCE_CLARIFICATIONS.md) gives the precise domains and examples.

## 7. Proof-Strategy Deviations

The memo gives the [size-$(q+1)$ pool argument](docs/SOURCE_CLARIFICATIONS.md#capacity-variability-and-queue-representation) and [local appendix formula repairs](docs/SOURCE_CLARIFICATIONS.md#exact-appendix-corrections).

## 8. Proof Tricks Worth Reusing

- Derive the parity bridge from capacity/cardinality accounting rather than
  accepting inserted-applicant nonselection as an extra premise.
- Represent pool-dependent ML claims through an explicit binary membership
  label and prove predictor equality pointwise; this makes the fixed/rank
  threshold consequences small extensional arguments.
- State realized variability with both an upper bound and a concrete witness.
  This prevents an at-most theorem from masquerading as an exact paper claim.
- For finite program examples, define the queue runner computationally and use
  kernel `decide` on small exact carriers. The proof remains replayable by Lean
  and does not rely on `native_decide` or an external certificate.
- For LAP counting, quotient slots by extensional equality of their induced
  strict orders and count the canonical image. This avoids confusing the raw
  number of slots with the number of distinct realized order classes.
- Generalizing the LAP weights from integers to reals required no change in the
  combinatorial proof architecture once the arithmetic assumptions were stated
  at the right abstraction level.

## 9. Generalizations, Conjectures, and Extensions

The checked real-weight LAP argument suggests a reusable generalization to
other linearly ordered additive weight domains, but this was left paper-local
because the present source claims real weights and a generic library API would
need a deliberate design review. The sequential-composition and canonical
order-image lemmas are plausible library-lift candidates for a future cleanup.

No stronger empirical or runtime claim is inferred. The paper describes
training, top-q inference, deferred acceptance, and simulation procedures, but
does not state an asymptotic theorem for them; the formalization therefore
audits their mathematical formulas and choice consequences without inventing a
complexity result.

## 10. Source Clarifications and Exact Readings

Rank selection uses a fixed ex-ante tie order; assignment choices use a fixed
generic refinement of the primary objective. These specify choices when scores
or optimal assignment totals tie. [Tie rules](docs/SOURCE_CLARIFICATIONS.md#scores-strict-orders-and-assignment-choices).

The [appendix corrections](docs/SOURCE_CLARIFICATIONS.md#exact-appendix-corrections) replace the removable-set self-equality, tightly-even parameter, and local set/index expressions. Capacity restrictions are discussed in Section 6.

## 11. Paper Issues or Caveats

None.

## 12. Detailed Formalization Evidence

### Source pin and inventory

- Published paper: AAAI-26, DOI `10.1609/aaai.v40i45.41179`.
- Formula/proof source: arXiv `2601.11513v1`.
- Pinned archive: `cited publication`, SHA-256
  `0d57324d02fc64c4c6b627c71c71cbbf93610b7f0b4b2138da1b436bb9234434`.
- `audit/paper_statement_map.json`: the current typed source map. It sets
  `source_coverage_mode` to `named_theoretical_statements` and records 42
  direct source-to-Spec semantic contracts.
- `audit/v11_raw_source_spec_screening.json`: the current independent
  source-to-expanded-Spec screening ledger for those 42 contracts.

The current source map is anchored in `audit/cited publication` and
compared with the current `PaperInterface.lean` surface. The checked-in TeX
agrees with the pinned archive modulo whitespace. Its inventory also records
the model definitions, which are reviewed directly as semantic prerequisites.

### Review surface and semantic matching

The current source-facing surface has 42 direct source-to-Spec routes,
including the five abstract Proposition 2 procedure rows. The current v11
screening binds the exact source
anchors, expanded Specs, and their source-model contexts, while the Lean graph
checks the recursive proof, declaration, and axiom closure.

The v11 screening records 36 `matches` judgments and six
`matches_approved_corrected_target` judgments. The six paper prerequisites
record `matches`; the 22 library prerequisites record 21 `matches` and one
`matches_approved_corrected_target`. The canonical closure receipt describes
the most recently completed terminal transaction.

### Lean build and proof closure

The typed Lean graph checks all 42 proof contracts and their recursive
dependencies. The strict closeout performs the focused paper build and checks
for proof placeholders and nonstandard axioms.

## 13. Paper Assumption Provenance

No paper-local assumption declarations are needed. Source model and
nondegeneracy conditions are stated directly on the reviewed definitions and
theorems, and their recursive inputs have current source provenance.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No paper-facing assumption declarations are configured. |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The application scores, queue formulas, instability quantities, parity
relations, and real-valued assignment objectives have direct formula or theorem
rows. Local index and parenthesis repairs remain visible in the fidelity ledger.

### Current typed formula records

The fixed-threshold classifier, binary admissions-label formula, and
cohort-dependent rank-threshold formula remain in the typed source inventory.
Their actual functions are reviewed in the semantic-prerequisite lane;
identity restatements are not counted as additional theorem contracts.

## 15. Library Lift Pass

The finite-choice, queue, and assignment infrastructure is reusable. All
paper-specific bridges needed by the selected results are constructed in Lean;
no external certificate remains.

## 16. DAG Audit

`docs/DependencyDAG.tex` groups the selected results and model definitions,
including the abstract Proposition 2 queue procedures. Its status note records
fixed generic tie-breaking as a source-model clarification, not an economic
restriction. `docs/DependencyDAG.pdf` is rebuilt from that TeX and visually
inspected during this closeout for legibility, complete labels, and arrows that
do not cross node text.

## 17. Validation Checks

The current source-to-Spec and prerequisite judgments bind the saved Lean
graph. The strict closeout checks the focused paper build, source coverage,
semantic and proof evidence, document completeness, and accepted graph. The
canonical receipt records the most recently completed transaction.

## 18. Paper Definitions Checked

The checked definitions cover feasible and q-acceptant choice rules,
instability, substitutability, consistency, independence, q-representative
queues, sequential queue variability, parity encodings, and the real-valued
linear-assignment application.

## 19. Named Theorem Statements Checked

All selected named main-text and appendix results have current direct proof
routes, including the no-zero and tight-instability results, inconsistency
equivalences, q-representative characterization, all Proposition 2 queue
procedure results, and the assignment variability endpoint.

## 20. Statement Review Evidence

The current source-to-statement assessment and exact review targets are recorded
in the following artifacts. Mathematical scope and qualifications are explained
with their named results above.

- [Source statement inventory](audit/paper_statement_map.json)
- [Source-to-statement review](FINAL_CLOSURE_RECEIPT.md)
- [Model and definition review](FINAL_CLOSURE_RECEIPT.md)
- [Reusable definitions review](FINAL_CLOSURE_RECEIPT.md)
- [Canonical closeout record](FINAL_CLOSURE_RECEIPT.md)
- [Review packet](docs/HUMAN_REVIEW_PACKET.pdf)

## 21. Source-Coverage Audit Ledger

The source inventory covers the selected results and governing model
definitions. There are 42 direct result judgments and 28 prerequisite
judgments across paper and library declarations. Sections 12 and 14 describe
those records; Section 2 states the paper's completion status.
