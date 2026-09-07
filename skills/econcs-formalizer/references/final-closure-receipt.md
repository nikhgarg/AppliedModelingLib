# Final Closure Credential

`papers/<PaperRoot>/audit/obligation_evidence/current_accepted_graph.json`
selects the paper's sole machine acceptance credential. The selected
content-addressed schema-2 graph has one `paper_closure` root. That root depends
on the complete semantic DAG and binds the complete current paper-obligation
index, terminal verification identity, and registered verifier authority.

`FINAL_CLOSURE_RECEIPT.md` remains the one named, human-readable paper-root
closure report. Under schema 6 it is deliberately **not** an acceptance
credential: it only points to the selected accepted graph. A copied, edited,
or newly written Markdown receipt cannot close a paper by itself.
`FINAL_VALIDATION_REPORT.md` states the mathematical verdict. Audit sidecars,
source records, semantic ledgers, build records, and planner/worker files are
inputs or supporting evidence, not alternative final credentials.

Create schema 6 only after the complete graph has passed terminal verification.
Do not backfill it merely to make historical documentation look current. A
current legacy schema-2--4 receipt remains valid under its recorded verifier;
promote it at a deliberate closeout or release boundary, without rerunning
unchanged semantic or Lean producers solely to change formats.

## Required schema-6 pointer

Use this exact shape. The issuer fills the identity from the accepted graph;
never enter them by hand.

````markdown
+++
schema = 6
paper = "<PaperRoot>"
closure_status = "current"
acceptance_credential = false
closed_at = "YYYY-MM-DD"

[accepted_graph]
pointer = "papers/<PaperRoot>/audit/obligation_evidence/current_accepted_graph.json"
graph_sha256 = "<accepted obligation graph identity>"
+++

# Final closure receipt

This file points to the selected accepted obligation graph. The graph's
terminal closure root is the sole machine acceptance credential.
````

Do not add command transcripts, retry history, row-level semantic prose, or
unpinned claims of review. Put mathematical exposition in the validation
report and row-level evidence in its canonical audit artifacts.

## What current validation proves

The graph-native validator authenticates, without invoking a producer, LLM,
Lean elaboration, or focused build:

- the exact current source artifact and archive surface;
- the current structural preflight over the statement map, paper prerequisites,
  and material library review;
- a complete paper index and obligation graph with registered contracts;
- one terminal closure root under a registered engine authority, depending on
  every semantic root and binding the exact paper index and verification record;
- every and only selected paper proof endpoint in the build leaf;
- the exact portable paper identity, toolchain, complete tracked paper-module
  inventory, and one successful dependency-ordered rehashed Lake build over
  every module in that inventory;
- Lean's saved path-independent import closure, repository source/control
  bytes, external `.olean` aggregate, and start/end mutation guards.

An invalid selected graph fails closed. No standalone evidence audit may fall
back to replaying a legacy lane as a second way to grant acceptance. Optional
human review remains visible as reviewer-owned annotation but is not a paper
closeout or release prerequisite.

## Refresh and reuse rule

Reopen only the affected obligations after a material change to selected source
semantics, source routes, paper-facing Specs, proof endpoints, material library
semantics, the Lean import closure, build target/toolchain, or review protocol.
Reuse every unaffected content-addressed leaf whose semantic identity remains
unchanged; an engine version pair is never a compatibility key.

The complete source corpus is byte-pinned once by the current structural
preflight, paper index, and terminal verifier. Each source-atom leaf binds its
exact reviewed quote rather than duplicating the whole-corpus digest. A changed
corpus therefore always requires current source-inventory and anchor
reconciliation and a new terminal index/issuance set. It requires a new
source-to-Lean judgment only when the exact reviewed quote or verbatim context
bundle changed. Do not infer semantic equivalence from filenames, line ranges,
OCR normalization, or a carrier hash alone.

Do **not** reissue semantic evidence merely because aggregate status files,
site rendering, human-report wording, ignored worker traces, timing diagnostics,
checkout paths, machines, or a registered `review_compatible` engine transition
changed. Current validation rechecks portable semantic and Lean identities
directly. If a change is ambiguous, classify it before invoking any producer.

A fresh current command consumes its issuer-protected, nonserializable pass in
the same process to materialize and publish the schema-2 accepted graph. No
serialized trace, stage aggregate, or later finalizer may replace that pass. It
must never issue schema 2--4 as a temporary final receipt. Existing historical
schema-2--4 and schema-5 artifacts remain directly
verifiable under their recorded schemas and may be migrated deliberately; their
readers are not a second current producer path. The live engine has no legacy
final-receipt writer. If a historical receipt is absent or corrupt, do not
reconstruct it from current files: schedule an ordinary fresh graph-native
closeout from whatever exact semantic leaves remain reusable. Git history keeps
the retired producer available for forensic inspection, not execution. A
completed graph-native paper must end with the schema-2 graph selected by
`current_accepted_graph.json` and the schema-6 human pointer above. No receipt
or stage aggregate authorizes skipping a required proof, source review, or
release check.
