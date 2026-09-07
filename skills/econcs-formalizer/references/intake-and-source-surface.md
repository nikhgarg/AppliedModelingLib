# Intake and Source Surface

Authoritative rules for starting or resuming a paper, pinning source bytes,
constructing the source statement map, running the non-certifying architecture
pre-pass, and establishing complete source coverage before closeout.

## Start Or Resume A Paper

For a new contributor-owned paper, enter through
`python3 scripts/paper_contribution.py new ...`, not the lower-level
`new_paper.py` generator. The facade requires complete intake metadata,
registers the focused Lake target atomically, and preserves the one-paper pull
request boundary. Use `paper_contribution.py check <paper> --fast` during proof
work and its full check at the source-present closeout boundary. Aggregate
status/docs/site generation belongs to the mechanical aggregate-only follow-up
and must not be added to a one-paper pull request.

When the user assigns an existing paper for full closeout, the requested
outcome is a current accepted closeout—not a diagnosis of which current files
are missing. Treat an old wrapper-heavy `PaperInterface.lean`, absent
`ProofInterface.lean`, absent v11 source map or intake freeze, missing
`status.json`, empty/missing audit ledgers, and missing DAG, packet, report, or
receipt as migration tasks within the assignment. Inspect the existing proofs
and byte-pinned source, refactor the interface to one transparent complete Spec
per source claim, place exact-type proof endpoints in `ProofInterface.lean`,
create the current source routes and paper metadata, repair proofs as needed,
then generate every current audit and human-facing closeout artifact. Do not
stop merely to report that the paper predates the protocol.

The old `PaperInterface.lean` is navigation, not migration authority. Never
turn each old theorem wrapper into a new Spec or infer the denominator from the
number of existing endpoints. First make the source-only inventory of
independently presented named definitions and results. Then write a temporary
source-presentation-to-Spec table showing, for every source item, its one
complete semantic target and all implementation endpoints that support it.
Several finite realizations, asymptotic corollaries, event bounds, resource
envelopes, specializations, or helper variants for one numbered theorem may
belong inside one complete source claim or only in its proof-support DAG; they
do not become separate review rows unless the source independently presents
them. If a proposed migration produces one Spec per old wrapper, stop and
justify every row from the pinned source before freezing.
Conversely, never demote an independently numbered appendix or supplement
lemma merely because the paper uses it to prove a main-text result. It remains
a source claim, receives its own appendix/supplement review row and proof
route, and stays in the denominator. Its default review *intensity*, however,
is one initial source-to-Lean check rather than routine repeated review or a
terminal adversarial pass, unless it governs a main-text result or the
maintainer promotes it. Only Lean-introduced helpers or unnumbered proof
decomposition that the source does not independently present remain
proof-support-only.

Avoid migration churn by completing that structural conversion as one bounded
pre-audit phase. Run the static diagnostic once to inventory all missing or
malformed current-protocol inputs; read the full source surface and existing
proof graph; make the coherent interface/source-map/status refactor; run one
focused Lean build; then freeze the surface before issuing semantic judgments.
After the freeze, follow only the planner's current `next_action`, repairing
the named invalid item rather than repeatedly regenerating the whole paper.
Ordinary choices about filenames, generated schemas, report sections, and DAG
layout belong to the documented protocol and do not require user input. Stop
for the user only when the pinned source is unavailable, the source has a
material ambiguity with genuinely different mathematical outcomes, an
additional assumption or correction needs approval, or the selected theorem
cannot be proved without changing its agreed meaning.

1. At source intake, search the official/published venue and arXiv once. Record
   the official URL/version and the arXiv URL/version (or that no arXiv record
   was found) in paper metadata. The recorded official source governs theorem
   numbering, statements, and constants unless a maintainer records another
   source authority. Reuse that intake record rather than repeating either
   search; a search result never substitutes for a byte-pinned source artifact.
2. Read the current source artifact, `status.json`, `PaperInterface.lean`,
   paper-local audit map, validation report, coordination row, and recent diff.
3. Confirm the exact source version and byte-pinned text/TeX artifact. The
   recorded source material takes precedence over repeated web retrieval.
   For a PDF, run `pdftotext` once, store the resulting text beside the
   byte-pinned artifact in the private source cache, and record the artifact
   hash used for that conversion. Reuse that cached text; do not rerun
   `pdftotext`, re-download the PDF, or repeat the official/arXiv search unless
   the artifact hash changes or a maintainer explicitly requests a refresh.
   Treat extracted reading order as fallible: visually inspect the pinned PDF
   or canonical TeX around columns, sidebars, captions, split headings, and
   page boundaries when they can hide or reorder a named presentation. The
   deterministic extractor is an inventory floor, not proof of completeness.
   If the source arrives as a TeX or text archive, do not treat an unpacked
   working copy as an alternate canonical artifact. Build a deterministic,
   paper-local text surface from explicitly named, byte-pinned archive members,
   record the archive-member provenance in `source_archive_surface`, and put
   every map anchor on that derived surface. The archive, each selected member,
   and generated surface must reconstruct one another exactly. A public
   candidate may retain the provenance record but never the source bytes. In a
   public structural checkout, missing licensed source bytes mean only that
   source content cannot be rechecked there: preserve the pinned provenance and
   final closure receipt, report that limitation as structural/non-certifying,
   and do **not** call the private source review stale or demand reissue solely
   because those bytes are absent. Reissue requires a material source, map,
   interface, proof, or protocol change verified in the private checkout.
4. Build a source-only inventory of named definitions, assumptions/model
   conditions, lemmas, propositions, theorems, corollaries, and visibly named
   theorem-like claims. Map keys and Lean names are navigation only.
5. Check each selected statement outside Lean for domains, quantifiers,
   premise/conclusion direction, constants, signs, normalization, nonvacuity,
   uniqueness, timing, information, equilibrium refinements, and dependencies.
   Split every theorem, lemma, proposition, example, and labelled remark into
   its independent conclusion clauses, including "furthermore," "moreover,"
   and proof-section restatements; one visible clause does not cover the shared
   label. Reopen appendix versions and proof-local displayed formulas when they
   supply constants, normalized models, or auxiliary claims used by a selected
   result, and compare inconsistent main-text/appendix formulas explicitly.
   Before fixing the interface, run an adversarial model-boundary checklist:
   identify which environment, population, signal or noise law, technology,
   metric, and tie convention are exogenous and therefore must remain fixed
   across candidate actions or deviations; record exactly which variables the
   source permits a candidate to choose. Preserve the source's quantification
   mode claim by claim and section by section--in particular, do not replace a
   pointwise or universal statement by an almost-everywhere statement merely
   because a later measure-theoretic section has an approved null-set
   convention. For randomized algorithms, distinguish a probability law from
   the support of its possible executions and from a pathwise theorem about
   every supported execution. For optimization or choice rules, expose the
   source-feasible domain and any fixed but otherwise arbitrary consistent tie
   convention instead of silently choosing one convenient rule.
   For a stateful algorithm, record which sample block, transcript, historical
   scan, restart rule, and stopping test belongs to each iteration. Do not infer
   state ownership from a prose summary when the pseudocode and proof use
   different datasets or histories.
6. Search Mathlib, Cslib, Optlib, `AppliedModelingLib`, and existing paper modules before
   creating a new mathematical abstraction.
   Start with `docs/ARCHITECTURE.md` for repository layers, then use
   `docs/APPLIEDMODELINGLIB_DOMAIN_INDEX.md` and the probability and optimization
   roadmaps to find existing declaration families and narrow imports.
   The root `import AppliedModelingLib` is neither
   a complete catalog nor a lightweight default; prefer the smallest documented
   family facade or leaf module that supplies the needed semantics. Treat these
   documents as discovery aids only: Lean's environment remains authoritative
   for actual declarations and dependencies.
   **Hard external-reuse gate:** Do not import, copy, port, adapt, or rely on
   any declaration or code from an external Lean GitHub repository or library
   until the local module and paper-local reuse ledger record its exact
   repository URL, immutable commit/tag/release URL, upstream file path and
   declarations used, license terms and required notices, and the results of
   Lean/Mathlib compatibility plus `sorry`/nonstandard-axiom checks for the
   used dependency closure. Preserve all required license and NOTICE text with
   copied or ported material. Give exact linked credit in the local module and
   paper-local audit, including a concise account of the adaptation. If any of
   those checks or records is missing, treat the result only as a research lead:
   it is not available for the formalization.
   Before rebuilding a substantial foundational result—such as a fixed-point,
   compactness, topology, convex-analysis, measure-theory, or concentration
   theorem—also search the pinned dependency checkout, upstream Mathlib source
   and documentation, and relevant public Lean formalization repositories.
   Prefer a compatible checked result. If the best result is online but not a
   direct dependency, adapt or port it when it mathematically fits rather than
   silently re-proving a weaker paper-specific substitute. First verify its
   Lean/Mathlib compatibility, license, commit or release, absence of
   `sorry`/nonstandard axioms, and exact source-to-paper bridge. Preserve exact
   attribution in the local module and paper-local audit: repository URL,
   commit/release URL, upstream file path, relevant mathematical documentation
   or theorem source, license notice when required, and a concise account of
   the local adaptation. Never call a ported result a direct imported library
   theorem.
   Before adding paper-support declarations to an existing reusable module,
   inspect whether that module is a high-fanout foundational container. If a
   coherent new result family is needed only by the current paper or a narrow
   set of clients and does not change the existing base API, put it in a new
   reusable successor module that imports the stable base, and import that
   successor explicitly from the paper. Preserve the mathematical namespace
   and qualified declaration names. Do not duplicate code or make a paper-
   local copy, and do not split a module merely to game a receipt hash. The
   purpose is a truthful dependency boundary: additions to specialized norm,
   topology, probability, or optimization layers should not rewrite every
   historical client's imported source container. A genuine edit to an
   existing declaration remains an ordinary semantic change and fails closed.
7. Build a role-typed paper interface. Write each source result as one exact,
   transparent `<name>Spec : Prop`, then put a theorem/lemma of exactly that
   Spec type in `ProofInterface.lean`. It is acceptable and preferred for that
   separate endpoint to begin with `by sorry` in a private draft once the Spec
   itself is source-correct and its assumptions are visible. Write source
   definitions, algorithms, models, assumptions, and conditions as their
   complete actual Lean declarations, without reflexive theorem wrappers, and
   ensure downstream result Specs use those declarations where semantically
   applicable.
8. Run the non-certifying semantic-architecture pre-pass below on the source
   inventory and candidate interface. Refactor role errors, omitted clauses,
   fake wrappers, dead duplicate declarations, and source-model bypasses before
   freezing or issuing any semantic judgment. The pre-pass output is disposable
   diagnostic advice and must never be imported into an audit ledger, receipt,
   or final validation report as evidence.
   As part of that pass, inspect the exact reviewer bundle that the proposed
   graph will project. Every named helper material to a semantic target must be
   visible either by transparent expansion in that target or as an
   identity-bound supporting declaration with its own relevant dependencies.
   A Lean graph that knows a helper's name is not enough if the semantic
   reviewer sees only the name and cannot inspect the governing formula,
   domain, or quantifiers. Repair the shared projection or interface role;
   never teach a paper-specific name list to the queue generator. A deliberately
   generic helper also needs the owning paper use site in its review bundle
   when that use site supplies a material source restriction such as
   nonnegativity, feasibility, or a fixed convention. Dependency expansion
   exposes what a helper uses; it does not by itself expose the parent claim's
   restrictions. Either encode the restriction in the semantic owner or bind
   and display the exact owning use site.
9. Freeze intake before proving: verify the complete normal-scope inventory,
   byte anchors, source premise/conclusion atoms, exact result `Spec` types,
   actual source-model declarations, dependency order, and owning module/agent
   for every obligation. Run one focused
   manifest and semantic statement review on that stable skeleton. The
   underlying scaffold intentionally does not create a dashboard cache; create it
   once only after this freeze. During that fully current initial review, run
   `semantic_audit_reuse.py --bootstrap-current --write` once to seal the
   entry-local semantic identities needed for later item-level reuse. This is
   metadata creation, not a stale-evidence override. A proof-body replacement
   then preserves the statement judgment when its type and semantic dependency
   identity are unchanged.
   Newly scaffolded papers use one prospective intake authority: complete the
   curator-owned `source_named_result_inventory_review` plan in
   `audit/v11_source_map_preparation_config.json`, then let
   `prepare_v11_source_map.py` derive the canonical exact anchors, candidate
   dispositions, and inventory identities in `paper_statement_map.json`. Keep
   proof-obligation order and owners in the generated paper plan; do not create
   a second `audit/intake_freeze.json` container. Historical papers whose
   tracked status already selects `intake_freeze.json` retain direct validation
   under that recorded contract. A trusted pre-rollout commit defines the
   still older legacy cohort. Do not backfill or delete either historical
   marker to change lanes. When the project
   assigns an existing paper to the corpus-upgrade campaign, create a fresh
   migration freeze that records the current source inventory, one-Spec-per-
   claim interface, dependency order, and evidence plan; then rerun the v11
   lanes for that paper. Outside an assigned upgrade campaign, preserve legacy
   evidence and do not rewrite it merely for cosmetic conformance. A new
   paper's tracked `source_inventory_review_required` marker must remain true;
   deleting it is an intake failure, not a downgrade to legacy.
10. Choose the first dependency-ordered proof seam and prove it. Update plans or
   reports only when the source target changes or a handoff is needed.

Throughout formalization, maintain a paper-local working memo (normally
`docs/FORMALIZATION_WORKING_MEMO.md`) of possible source clarifications,
printed-source errors, and proof-strategy deviations as they are encountered.
Record the source location, the observed issue, the current Lean treatment, and
whether the item still needs mathematical review. This memo is a closeout
checklist and drafting aid, not audit evidence: never use its assertions to
establish source fidelity, proof realization, or closure. At closeout, verify
each surviving item independently against the byte-pinned source, the final
Lean declarations, and current audit results; then write only the verified,
reader-relevant conclusions into the source memo and final validation report.
An empty or incomplete working memo does not certify that no deviation or
clarification exists.

Use `templates/FORMALIZATION_PLAN.md` when a new plan is necessary. Do not
recreate a plan merely because an up-to-date one exists.

### Non-certifying semantic-architecture pre-pass

Run this once after drafting the role-typed interface and before intake freeze,
hashing, semantic screening, or proof closeout. It is intentionally allowed to
be broad and adversarial because no conclusion from it receives evidentiary
status. Give the model only the canonical byte-pinned source presentations,
the source-only inventory, the candidate paper-facing Lean declarations, and a
Lean-produced declaration/dependency view. Do not provide prior LLM verdicts,
map paraphrases, final reports, or status labels as semantic inputs.

Use this prompt verbatim, filling only the bracketed inputs:

```text
You are performing a NON-CERTIFYING semantic-architecture pre-pass for a Lean
formalization of an academic paper. Your output is diagnostic advice only. It
must not say that a row passes, matches, is certified, is closed, or is ready
for release. A later independent audit will compare raw source bytes with
Lean-elaborated semantics and issue any admissible judgments.

Inputs:
1. Canonical byte-pinned source presentations: [RAW SOURCE PRESENTATIONS]
2. Source-only inventory with stable item ids: [SOURCE INVENTORY]
3. Candidate paper-facing Lean declarations, including full bodies/types:
   [LEAN DECLARATIONS]
4. Lean-produced direct and transitive declaration dependencies:
   [LEAN DEPENDENCY VIEW]

Analyze the architecture rather than proof tactics.

A. Classify every source item by semantic role: asserted result; definition;
   algorithm/procedure; governing model; assumption/condition; source context;
   or proof support. Flag any disagreement between that role and its Lean route.
B. Results must have one complete proposition-shaped semantic target and a
   distinct proof/refutation endpoint. Definitions, algorithms, models,
   assumptions, and conditions must expose their complete actual Lean
   declarations directly, without an `A <-> A`, `f = f`, alias-equivalence, or
   theorem-shaped restatement used merely to satisfy an audit schema.
C. For every source presentation, enumerate its material semantic atoms from
   the raw text and identify the exact Lean subexpression or declaration that
   represents each atom. Flag omissions, additions, weakened/strengthened
   quantifiers, wrong domains, reversed implications, hidden nonvacuity,
   normalization/sign/constant changes, and assumptions smuggled into records
   or caller-supplied certificates.
D. For every algorithm or dynamic model, explicitly check inputs, outputs,
   initialization, sampling/randomness law, timing/indexing, feasible/query
   sets, transition/update equation, projection, tie behavior when material,
   stopping rule, and returned terminal value. Do not infer any component from
   a declaration name or prose comment. Check the quantifier order as part of
   the model: an algorithm that the source chooses before unknown model or
   instance data must be one uniform witness, not a fresh algorithm chosen
   after that data is revealed. Check operational quantities the same way. A
   record that pairs an executable procedure with an arbitrary cost, runtime,
   stopping count, or output field is underconstrained unless the Lean model
   proves the required connection, for example by a fixed-horizon bound and
   prefix-stability of the stopping count and returned output.
E. Trace each source definition/model/assumption through the Lean dependency
   view to every result Spec it semantically governs. A named standalone source
   definition may remain an independently reviewed declaration with no result
   consumer; record it as standalone and do not manufacture a dependency. It
   cannot, however, discharge a result's source-model obligation unless that
   result consumes it or consumes an independently source-reviewed declaration
   with the same applicable semantics. Flag an unused paper-shaped duplicate, a
   result that bypasses the reviewed declaration through a semantically
   different or uncovered carrier, or multiple competing definitions receiving
   one source item's credit. Code location is irrelevant: apply the same test
   to paper-local and reusable-library declarations.
F. Detect duplicate source rows, one source presentation split into
   implementation fragments, multiple review targets for one semantic claim,
   and proof-support lemmas incorrectly promoted into the paper denominator.
G. Propose the smallest coherent refactor for every finding. For a source role
   that governs a result, prefer one declaration that the downstream graph
   actually consumes over a compatibility wrapper or pairwise engine-version
   bridge. Preserve genuinely standalone source definitions as standalone
   review objects rather than attaching vacuous premises to results.

Return:
- a source-role table;
- a source-atom-to-Lean coverage table;
- a dependency-use table for definitions/models/assumptions;
- findings ordered by severity (`semantic omission`, `role/category error`,
  `dead or bypassed declaration`, `duplication`, `presentation issue`);
- a concrete refactor list and the checks that should be rerun afterward.

For every finding, quote the relevant raw source bytes and show the actual Lean
code/dependency route. If evidence is insufficient, say what is missing. Do not
manufacture a semantic verdict and do not reuse any conclusion from this pass
as later audit evidence.
```

After applying any useful refactor, discard or retain this output only as an
internal planning note. Independently rebuild the source inventory, expanded
Lean surfaces, semantic judgments, and closeout credential from the resulting
candidate. A clean pre-pass is neither necessary nor sufficient for closure;
its value is catching structural mistakes before expensive evidence issuance.

## Source Scope

Normal `named_theoretical_statements` mode requires:

- named theorems, propositions, lemmas, corollaries, and definitions;
- source-labelled theorem-like claims;
- explicitly named assumptions, conditions, or governing models needed by the
  selected results;
- named appendix theory.

Classify each normal-scope row's review intensity at intake. Named main-text
results and their governing semantic prerequisites are `main_text_primary`;
named appendix or supplement results are `appendix_baseline` unless they govern
a primary result or the maintainer promotes them. Both classes retain a
transparent `PaperInterface` contract and source inventory route. The baseline
class receives one independent semantic review but does not automatically add
repeat-review, graph-reissue, or terminal-adversarial obligations. This is a
review-pacing distinction, not permission to hide or delete appendix theory.

Standalone unnumbered prose assertions are **not** normal-scope paper claims by
default, even when they are mathematically interesting or describe an
algorithm's runtime. Keep them visible in the holistic source inventory as
`deep_audit_material`. Promote prose content only when it supplies a material
clause, governing definition/model/condition, or proof-support obligation for a
selected named or numbered result. In that case attach it to the owning named
result as a source atom, semantic prerequisite, or proof-support anchor; do not
manufacture a second paper-claim row merely because the sentence is assertive.
An unnumbered presentation becomes its own normal-scope claim only when the
source visibly names or labels it as a standalone theorem-like result, or when
the maintainer explicitly selects it. Use `deep_paper_with_all_prose_claims`
only when explicitly requested.

Do not create independent normal-scope obligations for standalone equations,
formulas, algorithms, numerical examples, figures, captions, tables,
simulations, empirical observations, or implementation measurements. Inspect
such material when it defines or supports a selected named theorem. Use
`deep_paper_with_all_prose_claims` only when explicitly requested; it requires
its own source-pinned completeness attestation.

An inventory must be source-only and complete independently of the map being
audited. Unknown named presentations fail closed. Repeated source
presentations stay byte-pinned but may be linked to one canonical claim through
the explicit source-presentation alias protocol. Explicitly inventory every
definition-shaped prose presentation, even when the resulting list is empty.
Give each one a source-only scope disposition; retain local notation and
computational/deep-only definitions with content-pinned independent scope
judgments rather than silently dropping them. A catch-all deep-only exclusion
also needs explicit user approval. A canonical normal definition binds to a
map statement only through a current semantic-equivalence receipt pinning both
sides.

Construct that inventory with one combined source-only discovery pass. The
deterministic labelled-heading extractor is the hard floor: it must find every
ordinary theorem, proposition, lemma, corollary, definition, and other
recognized named presentation. Before consulting a Lean declaration, existing
PaperInterface row, or source-map classification, give the complete canonical
source text to a reviewing agent. Ask it to find additional mathematical
presentations that may affect a selected named result, including remarks,
observations, notes, examples, or unlabelled statements that the mechanical
floor may miss. Discovery does not promote prose to the denominator: first ask
whether the passage is visibly a standalone named/theorem-like result, a clause
or governing dependency of a selected named result, or merely standalone prose.
The agent must return exact source locators and source labels, not paraphrases
or proposed Lean names. Put both mechanically and holistically discovered
candidates in the same explicit
`candidate_presentations` ledger, even when that ledger is empty. Classify each
candidate as either `material_named_claim` or `deep_audit_material` with a
source-only semantic basis. A material candidate becomes an ordinary source
claim and receives the full coverage, source-to-Lean, proof, and denominator
obligations; a deep-audit candidate remains recorded but does not inflate the
normal paper surface. No machine or agent candidate may disappear without one
of those dispositions.

Read through mixed definition/prose blocks. A definition can be followed in
the same paragraph or display block by a separately asserted existence,
uniqueness, implication, optimality, or other theorem-like claim. Record that
claim as a candidate when the source presents it independently; never assume
the visible environment kind classifies every sentence inside the span.

Use this source-only candidate prompt when delegating or beginning intake:

```text
Read the complete canonical paper source below without consulting Lean code,
the existing PaperInterface, source-map keys, or prior audit classifications.
The attached deterministic list is a minimum, not a complete inventory. Find
every additional independently reviewable mathematical presentation, with
special attention to labelled remarks, observations, notes, examples, and
unlabelled result statements. Inspect sentences adjoining definitions for
separately asserted existence, uniqueness, or implication claims. For each
additional or mechanically flagged
candidate, return its exact source locator, visible source label (if any), and
one disposition: material_named_claim or deep_audit_material. Give a concise
source-only reason. An unnumbered prose assertion is deep_audit_material by
default. Make it material only if it is visibly presented as a standalone
named/theorem-like result, or record it as context/support for a selected named
result when it supplies a material clause, governing definition/model/condition,
or proof step. Do not create a second claim row for such support. Do not
paraphrase the claim, propose a Lean declaration, or omit a candidate because
it looks easy, repeated, appendix-only, or unused by the current proof plan.
```

For fresh intake or a current-protocol migration, record those curator-owned
decisions once in the preparer's `source_named_result_inventory_review` plan:
the completeness assertion, any visible heading/environment classifications,
and each prose-definition locator and scope disposition. Use stable local
`presentation_id` values to bind prose definitions to map items. Let
`source_inventory_review.py` resolve the canonical source artifact, extract
the named presentations, materialize exact paper-local source anchors, and
derive all presentation and clause digests. Do not hand-copy quote hashes,
presentation hashes, or a second inventory receipt into the configuration.
The preparer must refuse an unclassified or uncovered in-scope presentation;
mechanical materialization never supplies a semantic-match verdict.

After drafting the source-facing interface but before issuing item-level
semantic judgments, run the first adversarial source-to-interface audit. Read
the complete source against the expanded Specs, challenge the inventory and
all claim components, repair every defect found, and obtain a focused build.
This pre-certification pass is deliberately repair-oriented: it grants no
acceptance and does not complete `docs/AGENT_SOURCE_AUDIT.md`.

Treat findings from that pass as design feedback, not just local repair tasks.
Preserve the exact paper finding in its audit lane. Promote a cross-paper or
serious prevention rule into the narrowest intake, proving, or closeout skill
only when the resulting public guidance is self-contained and contains no
unpublished paper or session provenance. Record a sanitized finding and resolution
in the internal project wiki only when the user explicitly authorizes that wiki
update. Wiki maintenance is not an automatic closeout step, and the wiki is not
evidence for a verdict, approval record, proof, or receipt.

Keep a separate final adversarial pass at the end of closeout. After the source
map, expanded Specs, proof endpoints, semantic prerequisites, assumptions,
machine judgments, and compiled inputs are stable, run the planner so it can
freeze the operational transaction and project its location-neutral final
holistic audit surface. Only when the planner emits
`perform_final_adversarial_source_audit` should the agent independently reread
the complete policy-selected terminal surface and write its distinct
paper-local audit document. The first reviewer uses
`docs/AGENT_SOURCE_AUDIT.md`; later reviewers preserve it and use distinct
paths. Record these lines using the exact identity in the planner action:

    ## Overall status: PASS
    - Reviewed final holistic audit surface identity: `<sha256>`
    - Final audit scope: `complete_current_surface`

The exact PASS heading and identity are stable metadata. The reviewer records
the actual independent source/inventory/interface analysis in its own words;
format-only wording changes never require another holistic read.
Record each reviewer's stable identity, audit path and content hash, exact
surface, PASS/scope attestations, UTC time, and independence attestations in
`docs/FINAL_ADVERSARIAL_REVIEW_PANEL.json`. The required count comes from the
planner's frozen policy assurance. If that count rises while the comparison
surface is unchanged, retain the earlier valid entries and schedule only the
missing independent review.

Use the frozen inventory only as navigation, not as proof that it was complete.
Actively search again for omitted source claims, hidden strengthening or
weakening, unmatched premises or conclusions, misclassified candidate
material, and source/Lean semantic mismatches. This final pass may inspect the
completed Lean surface and machine evidence. It cannot be autogenerated,
inferred from green item-level gates, or replaced by source-only intake or the
first adversarial repair pass. A source, inventory, source-connection, Lean
semantic target, prerequisite, status/caveat, or proof-contract repair changes
the semantic surface, so replan and bind the final audit to the replacement
surface. A build refresh, line move, module move, coherent declaration rename,
or other operational-only change does not by itself require another human
holistic audit when the planner proves the complete surface identical.

The final adversarial pass must apply the same normal-scope and review-intensity
rules as intake. It actively challenges `main_text_primary` rows and their
governing prerequisites, not routine `appendix_baseline` rows. A real
appendix-only issue is repaired or summarized proportionately when useful, but
does not fail the primary closeout, force repeat semantic review, or reissue a
graph unless it affects a primary result, its governing dependency, or an
explicitly promoted appendix target. A
newly noticed standalone prose observation is not automatically a missing paper
claim. Record it as deep-audit material unless it is visibly standalone
named/theorem-like theory, a material clause or governing dependency of an
already selected result, or an explicitly maintainer-selected claim. If it
supports a selected result, audit the owning result's source atom,
prerequisite, or proof route rather than inflating the paper denominator.
Default-out-of-scope prose cannot by itself produce a final `FAIL`. The
adversary bears the burden of naming the exact selected definition/result and
tracked source atom that make the passage material. A formula, footnote, broad
model paragraph, or mismatch with unused auxiliary Lean is not sufficient. If
the inventory itself wrongly selected that prose, the blocking finding is the
scope/denominator error and the default repair is demotion, not formalization.

A prior complete final audit may be renewed for a replacement semantic surface
without pretending to reread unchanged material only when the exact canonical
source bytes, complete source inventory and candidate dispositions, and every
unmodified semantic identity are proven unchanged. The agent must directly
reread every changed source/Lean row and its dependencies, then perform a fresh
holistic omission and cross-row consistency check over the complete source and
current interface. The renewed report names the old and new surface identities,
the mechanically established unchanged surface, and the rows reread. Merely
changing a surface hash, copying the old prose, or relying on item-level green
judgments cannot renew this gate.

Do not invent paper-specific omission lanes such as `bibliographic_context`,
`citation_only`, or `not_needed_by_main_text`. Any source presentation,
including a numbered theorem or lemma, may leave the selected formalization
surface only through the single structured user-approved scope-exclusion
route. Keep that item claim-bearing and byte-pinned, record the exact user
instruction and substantive reason, give it zero premise/proof/coverage credit,
and disclose it in the final validation report. Without that explicit
decision, a selected named result remains an ordinary source obligation and
fails closed when unformalized.

When one printed presentation contains multiple independently reviewable
clauses, keep it as one paper row but give each clause one exact verbatim
subquote identity within the shared byte-pinned block. Different atom ids,
paraphrases, or Lean routes do not distinguish source semantics. All closeout
producers and consumers must use the shared source-claim-atom schema; never
hard-code a locally supported schema set in a downstream planner or graph
adapter.
