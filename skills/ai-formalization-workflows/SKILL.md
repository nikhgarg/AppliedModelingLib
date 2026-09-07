---
name: ai-formalization-workflows
description: Apply workflow lessons from recent AI-assisted formalization systems to AppliedModelingLib paper formalization. Use when planning or reviewing autoformalization pipelines, proof-DAG or blueprint workflows, retrieval-grounded statement translation, compiler-guided repair loops, semantic-alignment checks, multi-agent scheduling, or human-in-the-loop validation for Lean formalization.
---

# AI Formalization Workflows

Use this skill when improving an AppliedModelingLib paper-formalization workflow or
planning automation around statement extraction, dependency ordering,
proof repair, semantic validation, or multi-agent formalization.

Primary survey source: Garg, *EconCSLib: AI-Assisted Lean Formalization for
Economics & Computation research*, arXiv:2606.13306, especially the related-work
discussion of recent LLM-based formalization systems.

For the detailed source ledger and paper-by-paper credits, load
`references/paper-workflow-insights.md`.

## Workflow Stack

### 1. Split Before Proving

Start with a document-to-project plan:

- extract named results, source definitions, proof dependencies, and notation;
- decide which results are paper-facing, reusable library candidates, or local
  helper lemmas;
- create a dependency DAG or blueprint before deep Lean work;
- compile declaration skeletons before trying to close proofs.

Credits: M2F for two-stage statement-then-proof project construction;
ProofFlow and Aria for dependency-graph-driven decomposition; LeanArchitect for
keeping blueprint metadata synchronized with Lean declarations; MathAtlas for
the observation that dependency depth is itself a difficulty signal.

### 2. Ground Translation In Existing APIs

Before inventing definitions, retrieve and inspect existing formal concepts:

- search Mathlib, CSLib, and AppliedModelingLib by concept and theorem role;
- prefer source-compatible library definitions over new local encodings;
- if a new definition is needed, give it a local paper-facing equivalence test
  before relying on it downstream;
- avoid looping on guessed Lean names.

Credits: LeanDojo/ReProver for premise retrieval; CRAMF and Aria for
concept-level grounding against Mathlib definitions; ProofBridge for retrieving
semantically similar theorem/proof pairs.

### 3. Use Compiler-Guided Repair Loops

Treat Lean feedback as the central verifier signal:

- generate a candidate statement or proof;
- run the narrowest Lean check that exercises it;
- parse the concrete error, goal state, imports, and missing premises;
- make local repairs under fixed statement signatures where possible;
- retain successful repairs and useful failed attempts as future retrieval
  examples.

Credits: Baldur for whole-proof generation plus repair from error context;
APOLLO for isolating failing subgoals and recombining repaired subproofs;
OProver for turning verified proofs, failures, and repairs into retrieval memory
and training data; FMC and FormalScience for iterative Lean error feedback.

### 4. Preserve Proof Structure, Then Deviate Explicitly

Default to a lemma-by-lemma proof route that mirrors the source proof. If this
is inefficient or the source is underspecified, switch proof strategy only after
recording the reason:

- mark which source step is being replaced;
- prove the same paper-facing statement or clearly document a source deviation;
- keep the dependency graph honest after the route changes.

Credits: ProofFlow for structural fidelity as a first-class objective; Draft,
Sketch, and Prove for using informal proof sketches to guide formal proving;
LeanArchitect for exposing blueprint inconsistencies.

### 5. Validate Semantic Alignment Separately

Compilation is necessary but not enough. Run a separate translation-alignment
layer for paper-facing statements:

- back-translate Lean statements to LaTeX or natural language without source
  context;
- compare back-translation against source statements;
- use human review for final paper-facing claims;
- flag source deviations, hidden assumptions, and newly introduced axioms;
- treat alignment scores as review aids, not proof of semantic correctness.
- unfold named result predicates and reject self-characterizing iff/membership
  clauses as evidence that an algorithm produced the characterized object;
- track source and Lean runners, their outputs, and independently supplied
  profiles as distinct semantic worlds until a checked refinement or
  preservation proposition connects them;
- compare fixed-instance and universal quantification, and distinguish
  noncomputable existence, executability, and polynomial runtime.
- compare source output arity and projection against the actual formal runner,
  including terminal trace components;
- require nonvacuous carrier/capacity and duplicate-validity evidence for every
  universally quantified adversarial transformation;
- reject combined coordinatewise extrema unless one coherent admissible
  witness realizes them and the result is connected to the actual runner;
- distinguish syntax-family cardinality from nonempty realized fibers, requiring
  surjectivity for exact equality;
- keep fixed-quota, mismatched-seat stopping, one-round, natural-arithmetic, and
  local comparison-count results separate from turnout-dependent full-runner
  polynomial claims; explicitly compare the seat count used by the quota with
  the seat count and stopping rule used by the runner.

Credits: MerLean and the AppliedModelingLib workflow for Lean-to-LaTeX review loops; FormalScience for
multi-stage human review and proof-boundary extraction; FormalAlign and cycle
consistency work for automated semantic-alignment checks.

### 6. Schedule Multi-Agent Work By Dependencies

When the current environment and authorization permit delegation, use
subagents only for work with a stable independent interface:

- assign read-only source/API scouting before proof edits;
- split proof work along independent DAG regions or separate files;
- merge through version control and targeted builds;
- keep shared-library edits narrow and announce API changes before downstream
  paper agents depend on them.

Credits: Automatic Textbook Formalization and AutoformBot/Atlas for
large-scale, version-control-mediated multi-agent formalization; Urban's
topology report for a cheap long-running LLM/checker feedback loop.

### 7. Keep Human-Facing Artifacts Current At Boundaries

At real proof boundaries, update artifacts that let humans review the result:

- paper-facing interface;
- dependency DAG or blueprint;
- validation/audit report;
- status metadata;
- source-deviation and remaining-boundary list.

Do not turn active proof loops into constant status churn.

Credits: AppliedModelingLib for paper-facing interfaces, DAGs, validation reports, and
review dashboards; LeanArchitect for synchronized blueprint metadata; FormalScience
for explicit audit trails through generated intermediate artifacts.

## AppliedModelingLib Application Checklist

When starting or rescuing a paper formalization:

1. Cache the source PDF/TeX once.
2. Build a named-result inventory and dependency DAG.
3. Compile paper-facing declarations and placeholders before proof closure.
4. Run a retrieval pass over Mathlib, CSLib, and AppliedModelingLib for every nontrivial
   concept.
5. Close proofs in dependency order, using compiler-guided repair. Treat Lean
   panic/internal-error output as a failed check even if the process exits zero;
   refactor the triggering tactic and require a clean diagnostic stream.
6. Preserve source proof structure unless a documented deviation is faster and
   still proves the source claim.
7. Back-translate and review paper-facing statements at start and closeout.
8. Promote reusable tools only after they pass the second-paper or future-paper
   test.
9. Update human-facing docs only at proof boundaries or closeout.

This skill complements `skills/econcs-formalizer/SKILL.md`; it supplies external
workflow patterns, while the formalizer skill remains the source of truth for
AppliedModelingLib-specific paper status, audit, and repository rules.
