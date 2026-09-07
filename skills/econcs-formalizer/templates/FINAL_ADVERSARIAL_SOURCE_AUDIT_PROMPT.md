# Final adversarial source-audit prompt

Use this template in a fresh agent/session that did not author or repair the
paper and did not issue its semantic judgments. Replace only the angle-bracket
fields.

---

You are the final adversarial reviewer for `<PAPER_ID>` in the
AppliedModelingLib development repository. You have no authoring-session context and
must try to falsify the proposed closeout rather than ratify it.

Exact final-audit surface identity: `<SURFACE_SHA256>`

Audit output: `<AGENT_AUDIT_PATH>`

Stable reviewer identity: `<REVIEWER_IDENTITY>`

Review-panel artifact (schema 3 only; omit for schema 2): `<PANEL_PATH>`

This audit runs immediately before strict closeout writes its final
credential. Do **not** report a missing `FINAL_CLOSURE_RECEIPT.md`, accepted
graph pointer, post-audit status stamp, or another artifact that the strict
worker is designed to create only after this audit passes. Inspect the current
frozen source/Lean graph and semantic/proof/build inputs instead. The strict
worker separately fails closed if it cannot issue the resulting credential.

Read the current formalization protocol and the planner-issued final holistic
surface. For a policy-aware schema-3 surface, read its frozen
`closeout_review_policy` assurance and inspect every byte-pinned source region,
inventory row, and semantic-review row in its `terminal_review` projection.
For a historical schema-2 surface with no opted-in review policy, inspect its
complete recorded source/Lean and review surface under the existing single-review
contract. The absence of a region partition, `terminal_review`, policy assurance,
or panel is expected for that schema and is not a blocker; do not migrate or
widen its scope merely to fill those newer fields. In either case, inspect the
typed statement map,
context-isolated semantic ledgers, PaperInterface, ProofInterface, assumption
and boundary surfaces, and the proposed final validation report, dependency
DAG, and human-review packet. A previously accepted obligation graph, focused
build receipt, or final closure receipt is historical pre-credential evidence:
it may be stale precisely because the current frozen surface has not yet been
closed. Do not report that fact as a finding. Report a graph discrepancy only
when the *current planner-issued final holistic surface* conflicts with the
current frozen interface or semantic-review material.

Search affirmatively for:

- omitted primary-scope definitions, conditions, or named and numbered results
  within the terminal source regions; treat standalone unnumbered prose as deep-audit material
  unless it is visibly standalone named/theorem-like theory, supplies a
  material clause or governing dependency of a selected result, or was
  explicitly selected by the maintainer;
- source-to-Lean mismatches in quantifiers, domains, premises, formulas,
  conclusions, edge cases, or material prerequisites;
- hidden assumptions, certificate-shaped proof substitutions, incorrect axiom
  or external-boundary classifications, and invalid proof realization routes;
- source items counted twice or deep-audit material incorrectly placed in the
  human claim denominator; and
- misleading, sparse, stale, or privately unresolvable statements in the
  report, DAG, packet, README, or status projection.

Apply the protocol's review-intensity tier. The terminal challenge actively
tests named main-text results and every material source-model, definition,
assumption, condition, or library prerequisite that governs them. A named
appendix or supplement result still has its source-pinned interface and initial
semantic review, but is not a routine terminal-adversarial target unless it
governs a main-text result or the tracked paper inventory explicitly promotes
it. Do not create a `FAIL`, a repeat semantic-review demand, or new
graph/receipt work solely for an appendix-only issue. A final validation report
may narratively identify a reader-relevant appendix, proof, or prose issue as
a non-blocking note, without making it a checked audit row or a gate; omit
incidental findings. An unnumbered proof display or prose derivation remains
supporting context for its owning result, not a duplicate paper claim.

Default-out-of-scope prose cannot support a `FAIL`. Do not promote an
observation, footnote, empirical convention, explanatory paragraph, or other
unnumbered prose merely because it contains mathematics or differs from an
auxiliary Lean model. To make such a passage blocking, identify the exact
selected named result or definition whose statement or proof premise depends
on it and the tracked source atom that carries that dependency. An unselected
Lean helper or `Spec` is not proof that prose is selected. Importance, the
presence of a formula, or a broad model paragraph is not enough. If the
current inventory mistakenly counts prose-only material, report the blocker as
denominator/scope misclassification whose repair is demotion to deep-audit or
supporting context—not as a demand for a new Spec, theorem, caveat, or semantic
review row. Optional prose observations may be listed separately as editorial
or deep-audit notes, but they do not change the overall verdict.

This is the one terminal broad challenge, not a vehicle for accumulating new
minor observations after the bounded semantic lanes have accepted their rows.
Report a finding only when it names the exact source and Lean/proof artifact,
the affected selected claim or material source-model declaration, and the
concrete mathematical consequence for a formula, quantifier, admissible model
domain, conclusion, or proof route. Do not record notation, presentation,
optional-generalization, or unselected-prose observations as closeout findings.
An already projected maintainer-approved clarification is settled unless its
record is absent, misrouted, or its exact stated scope is exceeded.

Do not use a prior audit verdict, intended paper status, campaign explanation,
or reviewer reassurance as evidence. Recheck exact current artifacts. Do not
repair any finding and do not edit Lean, source files, maps, semantic ledgers,
reports, DAGs, packets, or status.

Edit only `<AGENT_AUDIT_PATH>` and, for policy-aware schema 3, `<PANEL_PATH>`.
Historical schema 2 writes only its single audit document. Do not overwrite a prior
reviewer's audit or panel entry. The first reviewer uses
`docs/AGENT_SOURCE_AUDIT.md`; each additional reviewer uses a distinct
paper-local Markdown path. Bind the report to the exact surface identity above
and give an overall `PASS` only if every row and source region in the chosen
terminal-review projection is complete and accurate. Otherwise give `FAIL` and
list each actionable finding
with exact source and repository anchors, its semantic consequence, and the
specific owning lane that must repair it. Distinguish substantive failures from
optional editorial suggestions.

For a PASS, include these three machine-readable lines verbatim, then describe
the actual independent read in your own words:

    ## Overall status: PASS
    - Reviewed final holistic audit surface identity: `<SURFACE_SHA256>`
    - Final audit scope: `complete_current_surface`

Here `complete_current_surface` means the complete policy-selected terminal
surface, including every primary region and governing promoted dependency; it
does not silently widen `main_primary` to unrelated appendix material. Attest
this scope only after completing that source and terminal-artifact review. A
bounded repair recheck alone cannot make this
attestation, and the implementing agent must not add it to an older report on
the reviewer's behalf.

For a policy-aware schema-3 surface after a PASS, append your own entry to the
schema-1 panel without changing
earlier entries. Record `<REVIEWER_IDENTITY>` as a stable session or reviewer
identity, the audit path and SHA-256, the same reviewed surface identity,
`judgment: PASS`, `scope: complete_current_surface`, an ISO UTC `reviewed_at`,
and true `did_not_author_or_repair` and
`did_not_issue_semantic_judgments` attestations. Copy the required reviewer
count from the planner's frozen `review_policy_assurance`, not from a mutable
source-map reread. Where stable authoring, implementing, or semantic-reviewer
identities are supplied, retain them in `ineligible_reviewer_identities`; your
reviewer identity must not match any of them. The panel's paper and
`review_material_sha256` must bind this paper and `<SURFACE_SHA256>` exactly.

The binding protects the exact reviewed surface. It does not make a particular
English formula evidence: do not add boilerplate merely to satisfy a parser,
and do not downgrade or reopen a paper over a non-material presentation issue.
