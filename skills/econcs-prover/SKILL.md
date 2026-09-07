---
name: econcs-prover
description: Prove or repair Lean theorems in AppliedModelingLib. Use when asked to close sorry/admit gaps, fix failing theorem proofs, repair broken Lean files after API or statement changes, derive paper-facing results from existing paper assumptions, or run compiler-guided proof search for AppliedModelingLib paper or shared-library lemmas. Focuses on proof construction, tactic/API search, source-faithful theorem repair, and targeted Lean validation.
---

# AppliedModelingLib Prover

This is the proof-production skill for AppliedModelingLib. Use it after the paper
statement target is known, or when an existing theorem proof fails and needs to
be repaired.

This skill complements the workflow skills:

- Use `skills/econcs-formalizer/SKILL.md` for paper setup, source inventory,
  paper interface rules, public/private sync, and closeout validation.
- Use `skills/econcs-formalizer/references/proof-strategies.md` to route into
  the smallest relevant domain proof reference.
- Use `skills/lean-community-conventions/SKILL.md` for new shared-library APIs,
  naming, style, and proof-claim gates.
- Read `references/proving-workflow-provenance.md` when updating this skill,
  explaining its literature provenance, or citing why the workflow is designed
  this way.

## Proof Campaign Priority

In an active proof campaign, spend working time closing the next mathematical
or Lean obligation in dependency order. Edit documentation only when the user
explicitly requests it or at a meaningful boundary: a theorem closure, a
paper handoff, a paper transition, or campaign closeout. Do not interrupt an
unfinished proof sequence to refresh plans, status tables, audit reports,
DAGs, dashboards, or generated artifacts merely because an intermediate lemma
changed. While an actionable proof obligation remains, defer routine
documentation work; the default unit of progress is a checked proof, not a
status update.

## Active-Closure Boundary

Count a declaration as a proof endpoint only after a forced Lean check of the
module that imports it. Text inside a block comment, an unimported experiment,
or a stale generated artifact is not evidence of a closed theorem. When a
quarantined continuation looks promising, test it once in an isolated overlay
to classify it; do not uncomment it in the active paper root merely to probe
it. If the overlay fails, record it as experimental proof debt and repair or
rewrite it in a dedicated module before exposing any endpoint through the
paper interface or a closeout plan.

## Strategic-Model Proof Boundary

For a strategic, deviation, or equilibrium theorem, prove the whole semantic
claim rather than a convenient local certificate. Make the action space,
timing, information, belief/off-path convention, payoff comparison, and any
equilibrium-selection or transition refinement explicit in the target or its
proved prerequisites. Test null/off-path branches and outsider as well as
incumbent deviations. A certificate for selected members, one direction of
movement, or a supplied positive-mass set proves only that local response fact;
it does not prove candidate-wide closure, existence, uniqueness, or the source
outcome. Likewise, a universal conditional theorem does not establish a
nonvacuous or existential source conclusion until a valid witness/action family
is constructed and checked.

Hold every source-exogenous primitive fixed across a strategic comparison.
Unless the source explicitly makes it a choice variable, a deviating action or
candidate policy must not choose its own population, type distribution, signal
or noise law, technology, metric, or experiment. Put equality to the fixed
environment at the shared candidate/stability boundary so every downstream
theorem inherits it; do not patch the same condition independently into result
wrappers.

## Command Invocation

In the managed Codex environment, use the default non-login command shell
unless a login shell is specifically required. The current `exec_command`
schema does not expose a `login` parameter, so do not invent one; the user
configuration `allow_login_shell = false` is the durable control. The host's
Ubuntu `im-config` login hook invokes `systemd-cat` in non-graphical sessions
and otherwise emits unrelated `Failed to create stream fd` noise. This is an
execution-environment workaround, not Lean or audit evidence. Keep the
command's working directory and explicit environment arguments instead of
depending on shell-profile side effects.

Do not patch host `im-config` files or user shell profiles for this
environment warning. Keep the command's working directory and explicit
environment arguments self-contained instead.

In shared or resource-constrained proof campaigns, default focused Lean commands
to `LEAN_NUM_THREADS=1`. Run one Lake build at a time in a worktree. Increase
parallelism only for a deliberate integration build after checking available
resources; proof search should not fail because several agents raced the same
Lean artifact cache.

Check Git state when entering or leaving a proof phase, before a risky edit,
and before commit or integration. Do not spend proof-loop iterations repeating
`git status` and equivalent cached/staged diff commands when no Git operation
has occurred. For a long build or audit, keep and wait on its existing process
session; poll at coarse intervals and never launch a duplicate merely because
the command is quiet.

Run semantic Lean overlays in an isolated temporary directory. Overlay helpers
must not materialize temporary `.lean` sources at the repository root. If a tool session is cancelled, first
confirm and terminate its child process tree before retrying; quiet output does
not establish that the original scan stopped.

Treat each successful targeted Lean check as valid until a dependency of that
target changes. Batch a coherent proof edit, run one narrow check, and use its
first error to choose the next edit. Do not rebuild an unchanged target after a
status request, context compaction, JSON/doc edit, or terminal-output loss. Run
the full paper build once when the proof surface is frozen, not after every
helper-level success.

When working as a delegated proof agent, continue the currently assigned
proof obligation unless the coordinator explicitly redirects it; do not reopen
an older workflow or documentation request that has already been completed.

## Proof Loop

### 1. Fix the Target

Start from the exact theorem, not the surrounding paper:

1. Identify the failing declaration, file, and intended source statement.
2. Run the narrowest Lean command that checks the declaration or file.
3. Record the first real error and current goal shape before editing.
4. Confirm whether the theorem statement should be fixed or the proof should be
   repaired.

Do not weaken a paper-facing theorem silently. If the source statement is
conditional, expose the source condition. If the source is false or
underspecified, stop treating the issue as proof search and write a source note
or corrected conditional theorem.

For a missing hypothesis exposed by the proof, distinguish three layers before
changing the target: the paper's model primitives, a structural condition on
those primitives, and the auxiliary witness consumed by the proof. Prefer the
weakest natural structural condition expressible in the model primitives and
prove a named bridge that constructs the witness. A witness-level hypothesis
may still be the mathematically weakest proved theorem, but it must remain
identified as such. Do not rename a chosen support family, cover, matching,
certificate, coupling, or optimizer as “consistency” or “regularity” and present
it as though it were primitive. Record the implication hierarchy when a clean
primitive condition is stronger than the proof-minimal one, and do not claim
equivalence unless both directions are checked.

Before settling for an added structural premise, ask whether the original
model proves a stronger universal repair of the form “intended conclusion, or
the proposed alternative loses a desirable source-defined property.” Express
the adverse branch using the paper's existing conceptual vocabulary and
primitive objects whenever possible. For example, a collision between two
admissible coefficient vectors is naturally a failure of sparse
identifiability; it should not be headlined as a failure of a chosen support
family. Prove the bridge to the auxiliary witness formulation afterward.

Useful commands:

```bash
lake env lean papers/<Paper>/<File>.lean
lake build <known-module-or-target>
rg -n "theorem_name|key_definition|source_phrase" AppliedModelingLib papers Mathlib Cslib
rg -n "sorry|admit|axiom" papers/<Paper> AppliedModelingLib
```

### 2. Retrieve Before Inventing

Before writing a new definition or long helper proof, search existing APIs:

- Search local paper files for already-proved source steps.
- Search `AppliedModelingLib/` for reusable math, probability, optimization, matching,
  social-choice, auction, and graph lemmas.
- Search `Mathlib/`, `Cslib/`, and `Optlib/` if they are present in the Lake
  dependency tree.
- Check potential upstream Lean sources listed in
  `docs/UPSTREAM_LEAN_SOURCES.md` before porting EC/game-theory/social-choice
  infrastructure.

If you use or port material from an upstream Lean source, cite the repository
URL, file/module path, commit or release when available, license status, and
the local adaptation in the paper-local report or library docstring. Do not
copy code from an upstream source without preserving provenance.

### 3. Decompose the Goal

Use the source proof and Lean goal state together:

- State the top-level proof route in one or two concrete obligations.
- Prove helper lemmas only when they discharge repeated or conceptually named
  obligations.
- Keep helper statements stronger only when the stronger form is reusable or
  materially simplifies the proof.
- Prefer source-shaped paper-local wrappers over opaque certificate records.
- Move a helper into `AppliedModelingLib/` only if it is genuinely reusable outside the
  current paper.
- If a conjecture, stronger theorem, or extension looks trivial, leave it until
  the source theorem chain is stable. Then either prove it as explicitly
  beyond-paper material or record it for the final extension pass; do not count
  it as paper coverage.

The best proof route is usually source-faithful, but source fidelity is not a
requirement to mimic every informal sentence. A proof-route deviation is a
substantive change in mathematical approach; record both the original source
route and the Lean route. Missing assumptions, explicit source hypotheses, and
interface notes belong in assumption/status notes, not in proof deviations.

### 4. Run Compiler-Guided Repair

Treat Lean as the verifier and the error message as the next proof-state query:

1. Make one local proof change.
2. Re-run the narrow check.
3. Inspect the new first error or goal.
4. Search or derive the missing premise.
5. Keep the successful fragment and delete exploratory commands.

Use tactic suggestions as hints, not final opaque output:

```lean
  exact?
  apply?
  rw?
  simp?
  aesop?
```

After a suggestion works, simplify it into a readable proof when possible. Do
not leave diagnostic `#check`, `#print`, `set_option pp.all true`, or tactic
probe blocks in committed code unless they are intentionally documented tests.

### 4a. Prevent runaway elaboration and diagnostic output

Do not accept or repeatedly rerun a proof tactic that makes Lean emit a panic,
internal error, crash backtrace, or an enormous repeated diagnostic—even when
the theorem appears to compile and Lean exits zero. Stop on the first such run;
the output is evidence that the tactic/elaborator path is unstable, not harmless
noise. Do not solve it by piping away stderr, showing only `tail`, raising an
output cap, or recording the zero exit code.

Anticipate this problem when a proof repeatedly asks `simp` or `norm_num` to
unfold a large vector, matrix, finite lookup table, nested `Fin` term, or broad
model definition inside many local hypotheses. Prefer this pattern:

1. Define one small, transparent symbolic/evaluation function for the table.
2. Prove once that the original computation equals that function, using a
   bounded `fin_cases`/`norm_num`/`ring` calculation.
3. In downstream proofs, use `rw` with that lemma and `change` each fixed lookup
   into the intended scalar expression.
4. Finish with the narrow arithmetic tactic (`linarith`, `nlinarith`, `ring_nf`,
   or `norm_num`) rather than unfolding the original table again.

Also prefer `simp only` with an explicit short lemma list, named coordinate or
lookup lemmas, and separate normalization steps over a broad `simp [largeDef]`
at many hypotheses. If a one-time evaluation theorem itself stresses the
simplifier, split it into per-coordinate lemmas or prove index equalities
explicitly; never trade a readable kernel proof for megabytes of diagnostics.

During the proof loop, inspect the complete diagnostic stream with a bounded
operator-facing summary. A repeated stack trace or output above the repository's
clean-diagnostic limit is a proof-engineering failure that must be refactored
before proceeding to later theorems. The final focused build checks this again,
but it is a backstop rather than the first time the issue should be noticed.

Treat elapsed time, peak memory, and diagnostic volume as proof-engineering
signals. When a proof or build is unexpectedly slow, memory-heavy, or verbose,
stop after enough evidence to classify the cause and prefer a smaller
mathematical certificate, a reusable bridge lemma, narrower unfolding, or a
better shared runner over larger recursion, heartbeat, memory, or output caps.
Optimize when the cost is material, likely to recur, or blocks reliable work;
do not spend more human/agent time hyperoptimizing a harmless one-off than the
optimization can plausibly save.

Put a recurring remedy in its durable owner: a shared Lean lemma, audit/build
utility, stage skill, or regression test. Keep a genuinely paper-specific
proof decomposition in the paper. A local workaround or hidden shell filter is
not a workflow improvement. Record the concise general rule and a negative or
performance regression when one can be tested robustly without brittle timing
thresholds.

### 5. Classify Failures

When proof search loops, classify the obstruction before continuing:

- **API drift:** theorem or field names changed; repair imports or names.
- **Typeclass/instance gap:** add the missing local instance, `classical`, or
  explicit finite/decidable hypothesis.
- **Hypothesis mismatch:** prove a bridge lemma from existing assumptions
  instead of changing the theorem. If an additional premise is unavoidable,
  seek a model-primitive formulation and prove that it supplies the proof
  witness before exposing the repaired paper-facing statement.
- **Side condition:** isolate nonzero, positivity, finite-support,
  measurability, integrability, or boundedness obligations.
- **Wrong formal target:** the Lean statement does not match the paper claim;
  repair the statement and restart validation for that row.
- **Missing library theorem:** prove the reusable theorem, use an approved
  external boundary, or mark the paper partial. Do not replace it with a broad
  assumption bundle.

## Common Proof Moves

Use these as first-pass tactics before broader redesign.

### Algebra, Order, and Arithmetic

- Normalize expressions with `ring_nf`, `norm_num`, `simp`, or `field_simp`
  only after side conditions are explicit.
- Use `linarith` for linear inequalities and `nlinarith` for polynomial
  inequalities after rewriting hypotheses into the same variables.
- Prove denominators/nonzero conditions early; many EconCS proofs hide them in
  model assumptions.
- When a Lean checker is claimed to implement a paper formula, compare numeric
  domains and operators before proving downstream soundness: rational/real
  division versus natural floor division, casts, rounding, normalization,
  strictness, and zero-denominator behavior. Shared notation or function names
  are not evidence of equivalence. Prove the expanded formula bridge, or expose
  a witness-specific exact computation when the goal is only a counterexample.
  The audit evidence must be an explicit equality/iff conclusion tied to the
  reviewed operator obligations; an unrelated theorem conclusion is not a
  formula bridge.
- When a proof rescales an object more than once, track every normalization
  factor and sign through the finite identity before taking an asymptotic or
  big-O wrapper. Recheck that every side condition used by the asymptotic proof
  covers the theorem's full finite parameter range; add a complementary finite
  argument rather than silently dropping the uncovered regime.
- Compare proof-lemma and theorem quantifiers before reusing the lemma. A
  witness chosen after fixing one deviation (`∀ deviation, ∃ witness`) cannot
  establish one source policy or price that works uniformly
  (`∃ witness, ∀ deviation`); seek a direct uniform proof or expose the real
  source boundary.
- For strict inequalities, check whether the source has an interior condition
  such as `0 < p` and `p < 1`; if so, expose it as an assumption rather than a
  caveat.

### Finite Sets, Lists, and Counting

- Start with extensionality and membership normal forms:
  `ext x`, `simp [Finset.mem_filter]`, `by_cases h : x = y`.
- Keep source-relevant `Fintype`, nonempty, and finiteness assumptions visible.
  Keep `DecidableEq` visible in internal theorem/module signatures when Lean
  needs it, but do not expose it in a source-facing `Spec` unless the source
  semantics genuinely require decidable equality.
- For sums/products, reduce to pointwise equalities before invoking `simp`,
  `sum_congr`, or induction.
- Keep syntax-family cardinality separate from the number of nonempty semantic
  fibers. An exact equality between them needs a construction proving every
  syntax member is realized, or an explicit surjectivity theorem; a family-size
  formula alone proves only the syntactic count.

### Probability, Measure, and Analysis

- Decide whether the source claim is pointwise or almost-everywhere. Many
  continuous EconCS arguments are naturally `ae` statements.
- Preserve that choice at the source-claim boundary. Derive an `ae` projection
  inside the proof when needed, but do not weaken a pointwise or universal
  paper statement because another section uses a null-history convention.
- Separate measurability, integrability, nonnegativity, and finiteness before
  proving the main inequality or convergence claim.
- A strict probability or CDF comparison at a threshold needs the relevant
  boundary event to have zero mass. Connected support alone does not imply
  atomlessness or nondegeneracy. Keep weak clearing inequalities separate from
  the extra regularity used to make them strict.
- In arrival, incident, delay, or reporting models, distinguish birth time,
  report delay, first-report time, and the calendar observation window. An
  event first observed in a window may have been born before the window; do not
  replace a stationary or two-sided process by same-window cohort thinning
  unless the source model makes that restriction.
- Prefer reusable probability lemmas for expectation, variance, distributions,
  CTMCs, and renewal/reward arguments over paper-local re-encodings.

### Optimization and Certificates

- Separate feasibility, objective comparison, optimality, uniqueness, and
  certificate soundness into distinct lemmas.
- Quantify every optimum, infimum, best response, and loss-minimizing condition
  over the source-feasible domain. If the source permits any fixed consistent
  tie convention, parameterize that convention and prove the result for every
  permitted fixed choice; one convenient concrete tie rule is not equivalent.
- A reusable mathematical helper may be more general than one paper's model,
  but its paper-facing semantic owner must reinstate every material source
  restriction. Keep that use-site bridge explicit and reviewable; do not ask a
  reviewer to certify an arbitrary-real, unrestricted, or convention-free
  helper as though it were itself the paper's restricted definition.
- Do not let an `isMax`, `isOptimal`, `certificate`, `bridge`, or `replay`
  field be the whole proof unless another checked row derives that field from
  source primitives.
- For LP and finite optimization, prove the finite/candidate reduction first,
  then prove the chosen candidate's objective inequality.
- Before crediting a finite search as a repaired algorithm, make its semantic
  contract explicit: the literal action space and blank/full/partial policy,
  profile multiplicities and ordered-versus-multiset representation, actual
  source executor for the target, success and failure branches, and whether
  the Lean object is an executable enumeration or only a noncomputable
  specification. Prove any external implementation refinement and runtime
  claim separately; do not infer them from a generic finite selector.
- For universally quantified prefix, suffix, completion, or reordering attacks,
  prove the action family is nonvacuous (inhabited) under explicit carrier and
  capacity conditions. Check that concatenation cannot introduce forbidden
  duplicates;
  do not let a post-transformation validity premise silently erase the actions
  the theorem claims to withstand.
- When an argument computes separate per-candidate maxima or minima, never place
  all extrema into one allocation unless a single coherent admissible witness
  realizes them jointly. Use separate witnesses only for pointwise lower bounds,
  and tie any algorithm claim to the actual runner or a checked refinement and
  result-preservation theorem.
- Compare structured runner outputs component by component against the paper
  definition before proving downstream facts. Record output length, terminal
  components, and projections explicitly; an executor's full trace may contain
  an extra terminal label that the paper's `m-1`-step object omits.
- Do not lift a fixed-quota, one-round, natural-arithmetic theorem or a bound on
  emitted entries/comparisons to a turnout-dependent, multi-round, rational, or
  polynomial WIGM claim. Prove the quota/profile coupling, seat-count/stopping
  coupling, replay across all rounds, arithmetic refinement, and end-to-end cost
  bound as separate bridges. In particular, a runner hardcoded to stop after one
  seat must not use a quota computed from an unconstrained multi-seat election.
- Before crediting a paper theorem whose proof consumes feasibility, cost,
  runtime, or optimality propositions, inspect the current Lean-owned recursive
  closure and premise-provenance surface. Compare every premise semantically
  with the advertised result. A caller-supplied logical component of that
  result is proof debt and cannot itself establish source coverage, regardless
  of declaration or binder names.
- Unfold result-bearing definitions before using them. An iff that expands to
  winner membership, feasibility, or optimality of an independently supplied
  object only characterizes that object; it does not prove that the algorithm
  produced it. Keep source-runner state, Lean-runner state, runner output, and
  independent profile semantics separate until a proved equality, refinement,
  simulation, or result-preservation statement connects them. Merely conjoining
  runner success with an independent characterization earns no algorithmic
  paper credit.
- Audit quantifier and capability scope explicitly: one fixed profile is not
  every legal profile; noncomputable choice is not execution; execution is not
  polynomial time. A polynomial theorem must expose its complexity bound and
  arithmetic/input representation assumptions.
- When an advertised algorithm fails, first diagnose it mathematically outside
  the tactic loop. Test the smallest plausible causes: indexing or off-by-one
  errors, quota recomputation, tie-breaking, activation/transfer chronology,
  omitted terminal mass, prior-winner transfers, and incompatible independently
  optimized extrema. Build the smallest exact counterexample to the failed
  implication, quantify whether the discrepancy is local or large, and test the
  source's intended normal forms before weakening the theorem. A counterexample
  to one guard or proof step does not by itself refute the underlying existence
  theorem or every nearby algorithm.
- A robust repair pattern is: normalize any semantic witness to a canonical
  exact-budget form; derive finite decidable checks from that witness; construct
  the output from those checks without retaining the witness; prove literal
  executor soundness; then prove `none` excludes all source-domain witnesses by
  the normal-form reduction. For flow/path constructions, separately prove exact
  root mass, conservation, endpoint completeness, and zero exhaustion at every
  forbidden intermediate coordinate.

### Mechanisms, Matching, and Social Choice

- Reuse executable semantics for auctions, matching, STV/RCV, rankings, and
  choice functions when available.
- Before introducing a paper-local STV/RCV model, search the shared voting
  library for the existing executable runner, weighted transfer semantics,
  trace/focus APIs, and source-augmentation bridges. Prove against the actual
  runner or a checked refinement instead of rebuilding a smaller model whose
  stopping, quota, or transfer semantics may differ.
- Keep tie-breaking, strictness, support, and feasibility assumptions explicit.
- Separate three different randomized-algorithm claims: the probability law on
  executions, the support relation listing possible executions, and a pathwise
  theorem that holds for every supported execution. Never call unrestricted
  nondeterminism or a support relation an exact probability-law formalization;
  a pathwise theorem may deliberately need only support and should say so.
- Keep every iteration's dataset, fresh block, transcript, accepted repair,
  restart point, and terminal test explicit in the state transition. A proof
  about an unpartitioned sample or a reset history does not certify pseudocode
  that uses fresh blocks or retains prior queries, and conversely.
- Prove equivalence to the paper's algorithmic step before proving downstream
  welfare, stability, monotonicity, or strategyproofness claims.
- In ordinary RCV/STV input semantics, all added ballots are present before the
  rounds run. Treat "earlier/later arrival" in an allocation proof as candidate
  activation, transfer, deadline, or path chronology unless the model explicitly
  has sequential ballot submission. State that interpretation so an audit does
  not confuse physical arrival time with round-level flow.
- Separate single-seat stopping histories from multiwinner execution. With one
  seat, the actual runner stops at the first win, so a positive-loss history has
  shape `L^k W` and has no post-winner surplus transfer. Multiwinner histories
  can interleave losses and wins and can transfer winner surplus; a theorem for
  the no-prior-winner or zero/irrelevant-surplus family does not automatically
  cover those runs. Recheck endogenous Droop quota, remaining seats, weights,
  and suffix behavior before generalizing.

## Repair Guardrails

- Do not leave `sorry`, `admit`, `by omega?`-style failed fragments, temporary
  `axiom`s, `opaque` proof shortcuts, or broad theorem-shaped assumptions in
  final code. Do not use `native_decide` to close a trust-critical paper-facing
  proof or counterexample; replace it with a kernel-reducible computation or an
  explicit structural/arithmetic proof.
- Do not make a paper `formalized` by assuming an intermediate theorem that the
  paper expects to prove.
- When a source proof lemma is false, first determine whether the selected
  theorem is false or only that route fails. A checked independent proof may
  recover the unchanged theorem and should be recorded as a proof deviation;
  it does not make the false lemma true. A false selected theorem requires an
  explicit corrected target, caveat, or partial boundary and cannot be repaired
  by proving a nearby result.
- Do not hide theorem-level conditions inside opaque records merely to shorten
  a paper-facing statement.
- Do not update DAGs, validation reports, dashboards, or website metadata
  during ordinary proof loops unless the user asked for closeout or a real
  proof boundary has been reached.
- Do not edit protected human prose such as the repository README or
  human-written summaries unless the user explicitly asks for that text change.

## Validation Boundary

After closing or repairing a theorem:

1. Run the targeted Lean check for the edited file.
2. Inspect the complete Lean diagnostic stream, not only the process exit code.
   Any `PANIC`, `internal error`, crash backtrace, or pathologically repeated
   diagnostic output is a failed validation even when Lean exits zero. Refactor
   the triggering proof—usually by replacing repeated broad unfolding or
   simplification with one proved symbolic/computational lemma—and rerun until
   the same check is both successful and diagnostically clean. Do not suppress,
   truncate away, or receipt-bind the bad output.
3. Run the narrowest relevant module or paper build if imports changed, applying
   the same clean-diagnostic requirement.
4. Scan the touched files for `sorry`, `admit`, temporary `axiom`, `opaque`, and
   `native_decide`.
5. Inspect the diff for accidental statement weakening or unrelated churn.
6. If the proof changes a paper-facing statement or assumption, update only the
   required source-facing artifacts and defer full closeout unless requested.

At closeout, return to `skills/econcs-formalizer/SKILL.md` and follow its current
`audit-and-closeout.md` and `human-facing-artifacts.md` routes. This skill stops
at proof repair and Lean validation; historical closeout examples are not
current workflow authority.
