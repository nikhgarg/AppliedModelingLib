# Repository and Release Safety

Authoritative repository-boundary rules for private work, shared worktrees,
source caches, and public projection. For the detailed synchronization
procedure, also read `public-private-sync.md`.

## Repository Rules

- Work in `EconCSLib-private` on `main` unless the user explicitly requests a
  branch. Do not edit, commit, push, or serve the public repository unless the
  user explicitly asks.
- For every private Git operation in the shared worktree, use
  `skills/econcs-shared-worktree/SKILL.md`. Claim paper and shared-library
  paths before editing, use its scoped checkpoint command at handoff seams,
  and never use a routine stash or broad `git add -A` to switch work.
- Source-paper cache artifacts (PDFs, extracted text, and source archives) may
  be tracked in the private repository when they are the pinned evidence for a
  paper or are needed for a durable private handoff. Add only the exact artifact
  paths (using `git add -f` when the cache-ignore rules apply). Never include
  those source bytes in a public candidate or release merely because they are
  tracked privately: public export requires the user's explicit permission for
  those exact artifacts. A public checkout retains provenance and digests, not
  the cached source bytes, by default.
- Treat a dirty worktree as shared. Read diffs before editing, preserve other
  agents' work, and coordinate paper ownership in the current coordination
  file. Do not work on a paper assigned to another agent.
- For a user-designated migration wave, keep the recorded remote baseline
  frozen until the wave ends or a blocking dependency/user instruction reopens
  synchronization. Do not repeatedly pull just to discover unrelated work.
- Before validating an integration, compare both sides' changed paths and
  semantic/import overlap. Run focused tests and affected Lean roots for the
  overlap and reuse recorded validation of disjoint incoming paper work. A
  large commit count alone does not require a full build. Reserve a full
  repository build for toolchain, core-import, generated-code, or genuinely
  global shared-semantic changes and for the final release-readiness boundary.
- For public/private export and history safety, read
  `skills/econcs-formalizer/references/public-private-sync.md`. Do not push a
  private commit graph directly to public.
- Preserve the public engine registry's existing history. Export the engine
  and protocol registrations required by the selected public accepted graphs,
  as well as the current tooling registration, using public validation context
  only. Do not copy private sequence numbers, review narratives, or session
  history. Public evidence readers must work without the private registry.
- Regenerate and check status from the committed public candidate in a clean
  checkout. Verify that every selected accepted graph remains readable and
  that each paper's status registers its actual review-packet PDF and TeX.
  A successful rendering from a checkout with extra caches is insufficient.
