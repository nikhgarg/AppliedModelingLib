# Human-Facing Artifacts

Authoritative writing and validation rules for final validation reports,
source-clarification notes, paper-facing dependency DAGs, public summaries, and
website counts. Internal wiki examples, session history, and user-feedback
ledgers are maintenance records rather than human-facing release artifacts.

- Project and website READMEs are landing pages for human readers. Explain the
  purpose, what readers can explore, how to read a formalization, and how to
  contribute. Link to dedicated contributor and maintainer guides for detailed
  commands, generated-content ownership, renderer behavior, audit invariants,
  and agent instructions. Keep those operational rules in the guides or skill;
  do not copy them into landing-page prose.

- Treat every existing `human_summary`, public-note, website-table note, and
  paper-table comment as user-authored public copy, including text recovered
  from the active public checkout. Never replace, expand, paraphrase, or
  remove it because a formalization or audit changed; do so only on the user's
  explicit instruction for that prose. Before regenerating public status,
  compare the paper-local summary with the prior public surface and preserve
  the prior text unless the user has directed a change or it is demonstrably
  no longer true. Put audit detail in the report or sidecars, not the note.
- For a paper with checked named results and a disclosed coverage limitation,
  keep the website library-table status **Formalized**. Put **Formalization gap:**
  followed by the source theorem/proposition number and one brief sentence saying
  what is proved and what remains unproved in the table note and the report.
  Use the source's exact result name when it has no number. Describe the actual
  missing direction, bridge, domain, or bound in ordinary mathematical language.
  Reserve this table note for substantial extra assumptions, simplifications,
  or missing conclusions in the current formalization. Keep ordinary source
  clarifications and minor technical restrictions in the report. Preserve an
  existing **Partially formalized** label for unfinished developments the
  maintainer has explicitly designated; the general display convention must
  not erase that distinction. Do not use “Formalized with gaps” as the status.
  This display convention neither certifies full source coverage nor
  changes machine evidence, release eligibility, private/deferred decisions, or
  an unformalized paper's status. Omit the note for source-implied conditions,
  local typos, and explicit estimates that already prove the claimed rate.
  A public report's **Completion status** uses the same catalog-controlled
  reader label as the website, including the designated partial exceptions.
  Keep pending review and closeout explicit without changing technical status
  or accepted evidence to make the reader labels agree.
- For `FINAL_VALIDATION_REPORT.md`, keep Sections 1--11 as human-facing paper
  assessment. State only the paper result, actual theorem-level boundary,
  genuine beyond-paper assumption, material source-proof departure, or
  status-bearing caveat. Do not put Lean names, file paths, representations,
  helper constructions, audit counts, source hashes, command output, or prior
  implementation history there. Do not explain that a former gap, defect, or
  remediation was resolved: state only the current mathematical disposition.
  Write `None.` for an empty assumptions, deviations, gaps, or caveats section
  rather than converting a resolved implementation detail into a public note.
  Preserve substantive, current Sections 12+ when a report has them: detailed
  formalization evidence, claim/assumption/formula provenance, library lift,
  DAG audit, validation, and source-coverage ledgers are useful technical
  closeout material. Do not delete those sections merely to shorten a report.
  Keep them current, paper-specific, and clearly subordinate to the human
  verdict; exclude raw source-paper text, private plans or handoffs, approval
  records, agent chronology, commands, and historical repair narratives.
  Every final report must include numbered Sections 1--21 from the report
  template. Reorganize equivalent combined material without duplicating it;
  give each technical section concise paper-specific content or an explicit,
  truthful empty/unreviewed disposition. Check the complete structure at the
  terminal document stage, not during source intake or semantic review.
- Generated settled-context text in Sections 1--11 uses the display-only
  `docs/REPORT_CONTEXT_SUMMARIES.json` projection when present. Edit this file
  for wording changes. Its optional `assumption_summaries` maps exact existing
  additional-assumption record digests to display prose; assigning related
  records the same reviewed explanation displays it once. Keep the precise
  conditions in the linked memo, and preserve every underlying record.
  Preserve the legacy semantic record's `report_summary`
  bytes so a prose edit does not invalidate existing reviews. Older records
  fall back to their existing summary or first complete source-facing sentence
  of the semantic meaning. Keep hashes, normalization, stored-field semantics, declaration
  names, and other implementation detail in the typed audit record rather than
  turning a required current-context projection into report-front-matter noise.
- To omit an ordinary unchanged source convention from these generated
  reader-facing sections, list its exact id in the optional
  `omitted_conventions` array of `docs/REPORT_CONTEXT_SUMMARIES.json`. This
  display-only control applies only when the exact
  `convention/<id>` item in `docs/REPORT_MEMO_COVERAGE.json` is already
  classified `not_material` with a nonempty mathematical reason. It cannot
  suppress additional assumptions, corrected targets, material clarifications,
  or any semantic record.
- Writing the report and the paper-facing dependency DAG is part of closeout,
  not an optional release-documentation pass. The planner's evidence phase may
  acquire and review the frozen source/Lean surface before these derived
  products exist; their absence or stale prose must never block source intake,
  Lean graph acquisition, or semantic review. After those evidence lanes are
  current and before terminal acceptance, rewrite
  `FINAL_VALIDATION_REPORT.md` against the current selected
  source-to-expanded-Spec surface; rewrite `docs/DependencyDAG.tex` against the
  current paper-facing definitions, named results, visible conditions, and
  mathematical exclusions; compile `docs/DependencyDAG.pdf`; and visually
  inspect labels, arrowheads, reading order, and node/edge overlap. An existing
  report or DAG from an older protocol is incomplete until its theorem numbers,
  result clusters, review counts, and artifact links describe the current
  surface. The terminal document gate requires all three, but they are not
  semantic closeout inputs and their bytes cannot invalidate or reschedule an
  already completed graph or reviewer judgment. Mere file existence is not
  completion evidence.
- Before drafting or normalizing an existing paper's final report, inventory
  every paper-local source record, source-clarification or correction memo,
  proof-deviation note, formalization audit, working memo, and substantive
  README discussion. Use these materials as drafting leads and completeness
  checklists so current reader-relevant mathematics is not lost merely because
  an older report format changes. Independently verify every retained item
  against the byte-pinned source, final Lean interface, and current audit;
  none of those narrative files grants evidence credit. Summarize each verified
  source clarification, typo, external boundary, or proof deviation at its
  proper theorem/result level and link a current human-readable memo when the
  short report treatment is insufficient. Never replace that substance with a
  statement-map link, a Lean-name inventory, or audit chronology.
- During any re-analysis, use that inventory to recover already settled human
  choices before labeling an item unresolved or requesting feedback again.
  Preserve the prior reading and its reader-facing explanation when current
  source and mathematics still support it. If new evidence conflicts, keep the
  old decision visible in the working analysis and ask only about the precise
  changed point; do not silently overwrite either the decision or the evidence.
- A later prose-only or layout-only improvement is documentation work. Rerun
  the document/status checks and, when applicable, compile and inspect the DAG;
  do not replay semantic review or reissue a final closure receipt unless a
  receipt-bound mathematical input actually changed. This exception is not
  permission to leave a known-stale report or DAG until after closeout.
- Keep the Human Verdict to the present paper-level disposition, covered
  result family, and review state. Do not use it for source conventions,
  correction history, proof machinery, or an implementation inventory. A
  source-faithful representation or convention is not an additional assumption
  or proof-strategy deviation: use `None.` in Sections 6--7 unless there is a
  real mathematical premise beyond the source or a material departure from its
  proof.
- For each material source clarification, source assumption, or statement
  correction mentioned in a report, provide a self-contained, paper-local
  memo and link it from the report. One `docs/SOURCE_CLARIFICATIONS.md` may
  cover several related items. A reference to an audit JSON ledger, an
  internal working memo, or an unexplained assurance that details were checked
  does not satisfy this requirement. That note must give the pinned
  source anchor, corrected or clarified reading, and result-level effect; it
  must not substitute Lean history, declaration inventories, or audit process
  for mathematical detail. When linking out, retain a one- or two-sentence
  mathematical summary in the report; never replace the report's explanation
  with a link alone. A source-clarification note may keep a legacy filename,
  but its current content must be source-facing only: remove closeout history,
  commands, implementation routes, and Lean declaration inventories.
- Default to proportionate, human-facing language: “clarification,” “source
  assumption,” and “intended reading.” Explain the precise condition or formula,
  why it is used, and its effect on the paper's conclusions. Do not frame an
  implicit domain condition, local typo, or repaired proof route as a broad
  failure of the paper. If a printed statement is false, explain the exact
  counterexample or changed conclusion plainly without obscuring that fact;
  distinguish it from the claims that remain valid. Internal `defect` labels
  and status mechanics need not become the reader's vocabulary.
- For each named result, briefly state the actual formalized conclusion and
  any added hypothesis, restricted domain, or corrected formula; say when no
  material change is needed. Link the relevant memo section there and from
  Section 6 when discussing additional assumptions. The memo must compare the
  original and formalized hypotheses, quantifiers, constants, and conclusions,
  and explain why the difference matters. Give concrete parameter choices,
  formulas, and witnesses for corrected constructions or counterexamples;
  classifications and declaration names do not supply mathematical intuition.
- Check global paper assumptions and definitions before calling a condition
  additional. Distinguish what the paper states or implies from what the
  formalization introduces. Explain whether the difference changes economic
  interpretation, admissible instances, the guarantee, or only a technical
  proof condition. Separate local notation/algebra corrections, implicit
  conventions, extra assumptions, narrower formalization scope, and changed
  claims. A narrower formalization does not show that the broader paper claim
  is false. Use neutral, respectful language and describe a needed correction
  surgically; mathematical terms such as sampling error remain appropriate.
- Distinguish a premise required by the current Lean proof from an assumption
  necessary for the paper's theorem. An undischarged premise, failed proof
  attempt, or narrower checked statement does not show that the paper's
  hypotheses are insufficient. Unless a concrete counterexample or mathematical
  argument establishes necessity, state that it is unknown whether the paper's
  conditions imply the premise or another proof avoids it. Confine each
  counterexample to the exact statement and parameter domain it refutes.
  Before using a counterexample to assess the paper, verify that its witness
  satisfies all relevant original assumptions, including the global model.
  A diagnostic outside that domain or a failure of one proof step does not
  refute the stated theorem; explain that narrower evidential role instead.
- Keep each memo explanation to the exact original-to-formalized change, the
  reason, and the evidence. A local typo may take one or two sentences; do not
  reproduce a full recurrence to explain one initial value. State whether a
  counterexample or argument establishes the change, or whether it is only an
  unresolved obligation of the current proof. Do not imply Lean itself is
  incapable of proving a broader theorem. Give each result one substantive
  home among assumptions, proof deviations, and clarifications; use links in
  other relevant sections. Result tables may state the checked conclusion and
  link that discussion without repeating it.
- Write each memo component as concise change-first bullets: **what changes:**
  original condition, formula, or scope → formalized condition, formula, or scope.
  Follow with only the reason and evidence needed to understand that difference.
  List only deviations, extra assumptions, and material clarifications; omit
  unchanged source hypotheses, conditions already implied by the paper or its
  proof, and implementation details. Do not announce that unchanged conclusions,
  constants, labels, objectives, or economic primitives were preserved. Define an
  indispensable symbol or label locally; otherwise remove the reference. A local
  min/max or index switch should normally fit in one bullet. Keep distinct changes
  in separate bullets, and do not hide a restricted domain behind a typo summary.
- Before labeling an explicit finite bound a changed asymptotic rate, simplify it
  under the paper's full setup. State which parameters vary and which quantities
  are fixed constants; check their dependence and valid ranges. Explicit constants
  or a stronger finite estimate that yields the printed big-O rate should be
  labeled the same rate, not a correction. If the rate differs, state the exact
  old/new parameter dependence and whether the difference concerns uniformity.
  Report endpoint restrictions separately. Do not put a long finite-bound
  derivation in a deviations memo when it only makes the existing rate explicit.
- In a result-summary table, omit a restriction note when the condition is already
  stated or implied by the source; mark the result exact unless another material
  difference remains. For an actual added restriction, state briefly whether it
  is required for the displayed formula, sufficient but stronger than necessary,
  or used by the current proof with necessity unresolved. Do not make readers
  open the memo to learn this distinction. The memo should give the precise
  old-to-formalized change and its supporting argument or counterexample. A
  failure of an unrestricted formula does not show that every part of the
  formalized restriction is necessary. Label an unproved source-to-model bridge
  needed for the selected source conclusion, a missing direction, or a weaker
  proved bound as a formalization gap; do not reclassify unfinished source coverage
  as an optional generalization.
- Before adding a repair-inventory entry or scope note, read the full relevant
  source setup, proof context, and recorded governing model decisions. An explicit
  sampling law or model representation supported by that context is not itself
  an extra assumption. Establish which selected source conclusion actually needs
  an unproved connection before calling it a gap; an optional equivalence between
  two source-faithful representations is not automatically missing source coverage.
  Retain a real missing implication or stronger premise, and leave its necessity
  unresolved without evidence. Do not infer exactness merely from a plausible
  reading or an earlier repository decision.
- After writing each memo and its report summary, perform a separate adversarial
  readability pass before closeout. Try to find: (1) a change whose exact old/new
  forms cannot be identified in one skim; (2) an unchanged assumption or proof
  detail presented as a deviation; (3) words or repeated discussions that can be
  removed; (4) an undefined symbol or vague label; (5) a missing effect on the
  covered domain or guarantee; and (6) a claim of necessity unsupported by a
  counterexample satisfying the full source hypotheses or a mathematical argument;
  and (7) a scope note that omits the affected result number or disagrees with the
  report and actual checked statement. Verify numbering from the source document,
  not a TeX label key or its ordinal position. Repair every finding, then reread
  the rendered memo and report together. An
  independent fresh reader may help when delegation is authorized, but the target
  is a human reader. Mechanical coverage/link checks do not replace this pass.
- Hard rule: do not label mathematical targets or assumptions author-approved,
  formalizer-approved, owner-approved, or equivalent in reader-facing reports
  or memos. State what was formalized and under which conditions. Repository
  decisions do not establish paper-author endorsement. Internal authorization
  records and mathematical uses such as approval voting are separate.
- Write these formalization memos as clean, finished explanations. Do not add
  “Codex draft for review,” “Codex addition,” or similar agent labels unless
  the user specifically requests a marked proposal. This convention concerns
  formalization reports and memos, not permission to rewrite manuscript prose
  or maintainer-owned website summaries.
- At document closeout, verify that every material clarification mentioned in
  the report has its explanation, that each memo link resolves to a readable
  document eligible for the intended release, and that memo and report agree
  on assumptions and result-level scope. Inspect the rendered report and memo:
  generated boundary markers must be invisible, while their substantive
  content remains visible. These are document checks; prose/link repairs do
  not reopen unchanged mathematical evidence or rewrite approved summaries.
  Validate fragments using the intended public renderer's heading rules.
  The local preview must use GitHub-compatible identifiers when its public
  counterpart is a GitHub Markdown file; default Pandoc identifiers differ
  for leading section numbers and punctuation. Heading links use visible
  heading text, excluding embedded link destinations. A local-only link pass
  under different identifier rules does not establish public-link correctness.
- Record that review in `docs/REPORT_MEMO_COVERAGE.json` and run
  `python3 -m scripts.report_memo_coverage --paper <PaperId>`. The optional
  `--write-template` writes an incomplete inventory, not an accepted assessment.
  Review every listed source item and every material report mention. A material
  item requires a linked memo path, its reviewed `memo_sha256` (from
  `memo_content_sha256`), and, where useful, an exact memo heading;
  an ordinary representation convention or historical item may be marked
  `not_material` only with its mathematical reason. Add `report/<topic>` entries
  for material report content outside structured source records. Set
  `report_inventory_complete` only after this substantive pass. Report and
  source-item digests bind the document assessment; never refresh them merely
  to silence a stale-inventory error. The terminal document gate checks this
  assessment, including for an already accepted canonical receipt, without
  rescheduling unchanged semantic evidence.
- When migrating an assessment, preserve every existing `report/<topic>`
  item as well as the structured source items. A fresh source inventory cannot
  recover report-only findings. Review a redundant item explicitly and retain
  its disposition or mathematical reason; do not silently drop it from the new
  schema.
- Use the schema-2 result-table assessment for document closeout. Map every
  selected named result from the current source inventory to Section 4; account
  for every table row and explain grouped or split coverage. Verify printed
  numbering from visible source headings or the rendered source, never from
  Lean names or TeX label keys. Bind the reviewed rows, source inventory, and
  precise memo headings so a later edit makes the assessment stale. Templates
  remain incomplete until this review is performed. Do not auto-complete them
  from historical fidelity classifications: those records do not establish
  whether a premise is additional or a source-to-model connection is missing.
  The selected claim set comes from the current source-coverage and semantic
  routes; heading discovery supports printed presentation and cannot silently
  omit a selected clause or promote a quarantined source restatement. Resolve
  a stale report exclusion against that selected scope rather than deleting
  an already reviewed result to make the table smaller. Use one explicit
  `report_home` for each memo item: proof-only repairs may link from Section 7
  without adding a changed-statement note to an Exact result row.
  A shared defect or convention association is a review lead, not proof that
  every associated result is restricted. Check its actual effect on each result;
  retain Exact for source-implied domains and valid strengthenings. Use the
  appropriate main memo location instead of forcing irrelevant result-row notes.
  Mechanical completeness and link checks supplement the adversarial reader
  pass above; they neither issue nor invalidate mathematical judgments.
- If a printed intermediate lemma, strictness condition, or proof step is
  false or has the wrong quantifier scope, but the named result is still true
  by a different source-model proof, record that fact once in Section 7 as a
  proof-strategy deviation, with a cross-reference from Section 10 if useful. State
  why the stated result survives; do not call the paper caveated or downgrade
  it merely because the printed route needs repair.
- Source-clarification, correction, and proof-deviation notes default to
  public-facing, self-contained mathematical explanations unless the user
  explicitly requests a restricted coauthor or author-only artifact. Do not
  label their opening as “author-facing”; state the mathematical issue and
  disposition directly.
- A public source-clarification note must stand on its own for a mathematical
  reader. It may name a published result, cite the stable public paper, and
  point to an official arXiv source file or extract that is included in the
  public projection. Do not expose private approvals, hashes, implementation
  identifiers, Lean declarations, audit history, commands, or repair-agent
  instructions in its prose. Per-paper audit JSON and the canonical closure
  receipt may be public evidence artifacts, and audit sidecars may retain
  internal transcript filenames as provenance, but a human-facing note must
  not link a private transcript or make a private working file necessary to
  understand the mathematics. When no safe existing note exists, write a
  short current-mathematics note rather than exporting a private one.
- Before finalizing any report, explanation memo, README, DAG, review packet,
  dashboard, website page, or other artifact intended for public readers,
  define the prospective public artifact set and inspect every direct link and
  reader-visible repository path. Link only to a target that will be present
  in that public projection or to a stable public external source. Private
  plans, working memos, agent audits, approval records, cached transcripts, and
  handoffs may inform the writing but must not be linked unless the user has
  explicitly approved that target for publication. Official arXiv source and
  source extracts, public per-paper audit JSON, the final closure receipt, the
  paper interface, DAG, and human-review packet are eligible when the release
  projection includes them. If a target's publication status is uncertain,
  leave it unlinked and ask the user rather than creating a dangling or private
  dependency. Repeat this link-boundary check on the prospective public tree,
  not only in the private checkout, before release.
- In a theorem-repair or source-clarification memo, formulate every new
  “consistency,” “compatibility,” “regularity,” or identifiability premise in
  the paper's model primitives before introducing proof notation. Say whether
  it is implied by the printed assumptions, is an additional structural
  assumption, or is only a proof-level witness condition. If the proof uses
  auxiliary supports, covers, matchings, certificates, or couplings, derive
  them from the primitive statement in the appendix and explain their role
  afterward. When the proof-minimal witness condition is weaker than the
  cleanest paper-facing primitive condition, show the implication hierarchy
  and the tradeoff; do not blur them under one informal label.
- Lead a substantive theorem-repair memo with the issue that most changes the
  paper's claim or the coauthor's decision, even when it is a later numbered
  theorem part. The printed order is a useful audit checklist, not a reason to
  bury a false headline theorem behind valid routine clauses. State the
  decision-relevant repaired result in the paper's existing notions and model
  primitives before introducing new terminology or proof objects. Prefer the
  paper's established nouns and relations; if a new notion is needed, show its
  primitive formula first and name it only to simplify subsequent use. Then audit
  the remaining clauses, and place source-anchored edits, counterexamples,
  Lean receipts, and appendix proof machinery afterward. If the clean repair
  is a universal “desired bound or loss of identifiability/stability/another
  valued property” dichotomy, headline that conceptual dichotomy rather than a
  witness-level compatibility condition.
- Preserve a genuine source-proof deviation during report normalization. State
  its source route, the material underspecification or departure, the checked
  paper-level route, and whether the theorem statement changes. Do not delete
  it merely because it is not a paper-level caveat; link a concise paper-local
  note when more than a short report summary is needed.
- The website's **Human review** column must render the saved human
  `reviewed_rows/total_rows` count only. Translation freshness, stale-machine
  evidence, mismatches, and uncertainty belong in audit artifacts, never in
  that public-facing review-count column.
- When a user maintains a paper or website feedback `.txt` file, preserve every
  user note verbatim. After the requested edit is complete and its relevant
  validation has passed, append `done. [brief outcome]` immediately after that
  feedback item; never mark an item done merely because it has been inspected
  or queued.
- In a `DependencyDAG`, show source-presented definitions, models, named
  results, and genuine paper-level dependencies. Do not show Lean proof
  support, implementation helpers, declaration names, or remediation history
  unless a source-presented named lemma itself warrants a node. A source
  definition without a direct theorem edge may still appear, but group it with
  its source-result cluster rather than giving a separate implementation path.
