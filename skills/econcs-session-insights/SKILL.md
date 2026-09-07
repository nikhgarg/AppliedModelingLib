---
name: econcs-session-insights
description: Maintain the project-local skills wiki, mine agent traces for recurring formalization lessons, preserve feedback examples, and propose validated promotions into operational skills without creating a parallel rulebook. Use when the user says "wiki this", asks to log a project skill lesson, reviews past sessions, distills process insights, updates skills from repeated mistakes, or applies WikiSkill or Skill-DISCO methods to this repository.
---

# AppliedModelingLib Session Insights

Credit: this skill adapts the trace-distillation idea from Guo, Qi, Gu,
Cheng, and Xiong, *SKILL-DISCO: Distilling and Compiling Agent Traces into
Reusable Procedural Skills*, arXiv:2606.26669v1. Their framework normalizes
successful agent traces, clusters repeated procedural structure, and compiles
the stable patterns into reusable skills; this file applies that idea to
AppliedModelingLib formalization sessions.

Its persistent knowledge architecture is inspired by Liyan Tang, Cyrus
Rashtchian, Chun-Sung Ferng, Andrew Tomkins, Da-Cheng Juan, and Tu Vu,
[*WikiSkill: Compiling Agent Experience into Persistent Knowledge for Skill
Evolution*](https://arxiv.org/abs/2608.27454), arXiv:2608.27454. WikiSkill's
separation of raw experience, accumulated wiki knowledge, and executable skills
motivates the project-local boundary below.

Use this skill to turn prior Codex sessions into concise, reusable procedural
guidance for AppliedModelingLib formalization work. The goal is not to preserve history.
The goal is to find repeated execution patterns, repeated user corrections, and
stable cross-paper rules that should affect future agents.

## Project Wiki and Authorization

This repository follows WikiSkill's separation between durable maintenance
knowledge and executable task instructions:

- the private `wiki/` stores consolidated patterns, concrete sanitized
  examples, evolution history, and evaluated skill impacts;
- local raw traces or sensitive evidence stay untracked and never enter the
  wiki verbatim; and
- `skills/` contains the executable instructions used during ordinary work.

Ordinary paper agents use the executable skills, not the maintenance wiki.
Wiki examples explain why a pattern exists; they are not additional acceptance
rules.

Keep wiki examples, feedback ledgers, session provenance, and maintenance
history private by default. "Wiki this" authorizes private knowledge capture;
it does not authorize publication. A public skill contains the general,
self-contained instruction distilled from that evidence, without private
paper findings, unpublished statements, user quotations, or identifying
details. It must remain usable when the wiki and historical ledger are absent.
Read a private ledger only when available and relevant to an authorized
maintenance task. Publishing a private wiki example requires a separate
explicit export decision. Public papers and released formalizations can remain
useful examples in content skills. Preserve methods, diagnostic checks, and
public API guidance; generalize private provenance without stripping the
skill's instructional value. For release checks, follow
`../econcs-formalizer/references/public-private-sync.md`.

Treat these phrases as explicit repository-write authorization:

- **"wiki this"**: finish the in-scope task, then log the concrete example,
  update or create the narrowest relevant wiki pattern, refresh `wiki/index.md`,
  and append `wiki/evolution-log.md`. Do not modify an executable skill.
- **"wiki this and update the relevant skill"**: perform the wiki update and
  propose one narrow executable-skill change, then validate it and record the
  result in `wiki/skill-impact.md`.
- **"mine this session and wiki it"**: run the trace-distillation workflow in
  this skill over the named/current session, then write its sanitized concrete
  examples and consolidated patterns to the wiki. Do not promote executable
  rules unless the user also asks to update the skill.

"Remember this", "for future work", and strong always/never feedback indicate
a likely durable lesson but do not alone authorize a repository wiki write;
ask briefly whether to wiki it unless the surrounding request already grants
project-repository write authority. Ordinary one-off corrections remain local
to the task.

A wiki-only update never authorizes raw-trace retention, commit, push, public
release, external-memory mutation, or an executable-skill edit. A concrete
example records observable context, user feedback, action, outcome or current
validation state, and the boundary on generalization. Never claim access to
hidden reasoning.

## Wiki Maintenance Workflow

1. Read `wiki/index.md`, the relevant pattern, and `wiki/skill-impact.md`.
2. Prefer updating an existing pattern to creating an overlapping one.
3. For a session-mining request, first normalize observable turns and tool
   actions using the Trace Distillation Workflow below; retain provenance to
   the legitimately inspected session without copying the raw transcript.
4. Add one or more dated examples under `wiki/examples/` when the user said
   "wiki this" or "mine this session and wiki it"; sanitize private source
   text, credentials, and unnecessary transcript data.
   For adversarial paper reviews, also update the current dated
   closeout-findings example linked from `wiki/index.md`. Preserve every
   material mismatch or uncertainty and its resolution, but consolidate rows
   under one root cause when their dependency is explicit. Record the stage,
   defect class, earliest prevention stage, and terminal or pending
   disposition. Start a new dated example when the current campaign or release
   batch changes. The paper's canonical audit remains the evidence.
5. State the recurring problem, root cause, evidence, stable action, and scope
   boundary in the pattern page.
6. Refresh the concise index entry and append the maintenance event to the
   evolution log.
7. Change an executable skill only under the stronger combined authorization;
   keep the patch atomic, test discovery and behavior, record accepted or
   rejected impact, and retain a clear rollback.

## Trace Distillation Workflow

1. Start from `~/.codex/history.jsonl`.
   - If the private `references/user-feedback-course-corrections.md` ledger is
     available, first read its `Last reviewed through` timestamp. Its absence
     in a public checkout is intentional; use the task's authorized history
     boundary instead.
   - For routine updates, inspect only history rows and raw session turns after
     that timestamp. Do a full backfill only when the user asks for one or the
     ledger is missing/corrupt.
   - Treat it as the high-level successful-trace index: user goals,
     corrections, status checks, and boundary decisions.
   - Group messages by session id and topic before opening raw session files.
   - Prefer the canonical top-level rollout whose basename contains that
     session id. A guardian, approval-review, continuation, or subagent trace
     may quote the same user messages but is not the execution trace to count.
   - Count event types, command families, repeated failures, and compactions
     first; normalize continuation duplicates before choosing raw-log samples.
   - Do not begin by scanning every raw `~/.codex/sessions/**/*.jsonl` file.
     Session continuations and subagents duplicate long instruction contexts and
     can dominate runtime without adding new procedural signal.

2. Open raw session JSONL files only when needed.
   - Sample sessions that contain repeated correction phrases, failed tools,
     unusual commits, CI fixes, or paper-boundary decisions.
   - Ignore system/developer boilerplate, encrypted reasoning, copied context,
     and repeated continuation payloads.
   - Count actual tool-call events rather than raw string occurrences. Older
     traces encode `function_call`/`exec_command`; newer traces encode
     `custom_tool_call`/`exec` with nested `cmd` fields. Parse both forms, and
     do not count commands quoted inside summaries, outputs, or audit scripts.
   - Extract only normalized operations: user directive, repo/paper context,
     action class, files or tools touched, result, and user correction.

3. Segment normalized operations into subgoals.
   Use these default clusters for AppliedModelingLib:
   - proof planning and theorem closure;
   - source-version and TeX/PDF convention checks;
   - assumption/certificate provenance;
   - reusable library elevation;
   - documentation, DAG, status, and audit timing;
   - public/private repository release hygiene;
   - CI/build/runtime environment handling;
   - subagent coordination and handoff boundaries.

   The private distilled course-correction ledger, when available, is
   `references/user-feedback-course-corrections.md`. Load it when the task asks
   specifically about prior user feedback, repeated corrections, or process
   hardening from session history.

4. Consolidate only repeated lessons.
   A candidate insight is skill-worthy when it appears in at least two sessions,
   affects at least two papers, or corrects a serious workflow failure. Do not
   add one-off paper notation, temporary proof names, or paper-local strategy
   details to a general skill.
   For expensive closeout failures, first separate a genuine evidence-integrity
   repair from a non-blocking tooling improvement. Promote the former as an
   exact closeout decision rule and the latter as deferred follow-up; never
   turn either into a rule that forces a freshly accepted paper through another
   audit without a changed material input.

5. Compile insights into the narrowest appropriate skill file.
   - Main workflow rules go in `skills/econcs-formalizer/SKILL.md`.
   - Private-repository pacing and commit-boundary rules also go in
     `docs/PRIVATE_DEVELOPMENT_WORKFLOW.md`.
   - Math-domain proof tactics go in the relevant reference file under
     `skills/econcs-formalizer/references/`.
   - Public-release rules go in the public/release workflow guidance.
   - If the insight is still experimental, put it in a separate draft skill like
     this one for review before merging.
   - A lesson learned from AppliedModelingLib work must be delivered in this repository's
     skill or workflow surface. A durable machine-level preference source may
     record the broader pattern too, but it never substitutes for the
     project-local rule or its private-repository commit.
   - When evidence is not ready for promotion, preserve it as a project-wiki
     pattern and example rather than adding a speculative executable rule.

6. Validate the skill update.
   - Keep the patch concise and grep for accidental paper-specific names.
   - Check that the new instruction is actionable, not just retrospective.
   - Update the `Last reviewed through` timestamp to the newest processed
     session/history timestamp only after the promoted rules and ledger edits are
     written.
   - Do not commit generated transcript summaries or text caches unless the
     user explicitly asked for them.

## Promotion Destinations

This skill is a provenance and maintenance layer, not a day-to-day paper
formalization rulebook. Durable lessons should be promoted into the narrowest
operational destination:

- `skills/econcs-formalizer/SKILL.md` for active paper formalization workflow,
  source provenance, audits, documentation timing, public/private repo hygiene,
  and subagent use.
- `skills/econcs-formalizer/references/proof-*.md` for math-domain tactics,
  theorem patterns, and reusable proof routes.
- `skills/lean-community-conventions/SKILL.md` for Lean naming, style,
  documentation, and proof-claim gate conventions.
- Paper-local planning or audit files for paper-specific notation, source
  deviations, and temporary proof strategy.

The historical feedback ledger remains private at
`references/user-feedback-course-corrections.md`. If available, load it only when a task asks
to mine prior sessions or backfill old corrections. New user-triggered examples
belong in `wiki/examples/`, with consolidated lessons in `wiki/patterns/`.

## Applying Insights Back to Skills

When merging a draft insight into an operational skill:

1. Rewrite it as a short command or checklist item.
2. Remove references to the session that taught the lesson.
3. Remove paper-specific notation unless the destination is a paper-specific
   reference.
4. Put math-specific proof content in the relevant proof reference, not the main
   workflow skill.
5. Delete or demote any duplicate rule from this session-insights skill once it
   has been promoted.
