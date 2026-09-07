# Proving Workflow Provenance

This note records the literature and project-paper sources behind
`../SKILL.md`. It is a provenance map, not an operational checklist.

Primary project source: Nikhil Garg, *EconCSLib: AI-Assisted Lean
Formalization for Economics & Computation research*, arXiv:2606.13306. The
relevant manuscript sections are "Autoformalization and theorem proving
methods", "Agent skill and automation scripts to autoformalize papers", and
Appendix C, "Human Feedback Workflows".

The broader source ledger for AI-formalization workflows lives in
`../../ai-formalization-workflows/references/paper-workflow-insights.md`.

## Project-Level Decomposition and DAGs

- Wang et al., *M2F: Automated Formalization of Mathematical Literature at
  Scale*, arXiv:2602.17016.
  Lesson used here: split long sources into statement skeletons and proof tasks;
  compile stable signatures before proof repair.
- Gloeckle et al., *Automatic Textbook Formalization*, arXiv:2604.03071, and
  Rammal et al., *Formalizing Mathematics at Scale*, arXiv:2605.29955.
  Lesson used here: schedule independent proof work through version control and
  dependency-compatible regions.
- Patel et al., *MathAtlas: A Benchmark for Autoformalization in the Wild*,
  arXiv:2605.14061.
  Lesson used here: dependency depth is a proof-difficulty signal, so hard
  theorem repair should move to shallower subgoals when stuck.
- Cabral et al., *ProofFlow: A Dependency Graph Approach to Faithful Proof
  Autoformalization*, arXiv:2510.15981.
  Lesson used here: preserve source proof structure when possible and record
  real proof-route deviations explicitly.
- Zhu, Monticone, Avigad, and Welleck, *LeanArchitect: Automating Blueprint
  Generation for Humans and AI*, arXiv:2601.22554.
  Lesson used here: keep informal blueprint/DAG metadata synchronized with Lean
  declarations rather than letting proof progress and human-facing artifacts
  diverge.
- Wang et al., *Aria: An Agent For Retrieval and Iterative Auto-Formalization
  via Dependency Graph*, arXiv:2510.04520.
  Lesson used here: recursively decompose formalization targets and ground them
  against retrieved formal concepts before accepting a statement or proof route.
- Jiang et al., *Draft, Sketch, and Prove: Guiding Formal Theorem Provers with
  Informal Proofs*, arXiv:2210.12283.
  Lesson used here: use the informal proof as a decomposition guide, while
  allowing Lean to force missing side conditions or better formal sublemmas.

## Retrieval and Proof-State Access

- Yang et al., *LeanDojo: Theorem Proving with Retrieval-Augmented Language
  Models*, NeurIPS 2023.
  Lesson used here: retrieve accessible premises and nearby proof patterns
  before inventing new APIs.
- Song, Yang, and Anandkumar, *Towards Large Language Models as Copilots for
  Theorem Proving in Lean*, arXiv:2404.12534.
  Lesson used here: use tactic suggestions and premise search as hints inside a
  human/agent-driven Lean loop.
- Lu et al., *Automated Formalization via Conceptual Retrieval-Augmented
  LLMs*, arXiv:2508.06931.
  Lesson used here: retrieve formal definitions for the mathematical concepts,
  not only theorem names.
- Jana et al., *ProofBridge: Auto-Formalization of Natural Language Proofs in
  Lean via Joint Embeddings*, ICLR 2026.
  Lesson used here: look for semantically similar theorem/proof pairs when the
  local statement is not syntactically close to an existing lemma.
- Aniva et al., *Pantograph: A Machine-to-Machine Interaction Interface for
  Advanced Theorem Proving, High Level Reasoning, and Data Extraction in Lean
  4*, TACAS 2025.
  Lesson used here: prefer structured proof-state access when available; avoid
  treating raw shell errors as the only proof-state interface.

## Compiler-Guided Repair

- First et al., *Baldur: Whole-proof Generation and Repair with Large Language
  Models*, FSE 2023.
  Lesson used here: feed failed proof attempts and compiler errors back into
  local repair, rather than regenerating from scratch.
- Ospanov, Farnia, and Yousefzadeh, *APOLLO: Automated LLM and Lean
  Collaboration for Advanced Formal Reasoning*, NeurIPS 2026.
  Lesson used here: isolate failing subgoals, syntax/API errors, solver-ready
  obligations, and remaining hard goals before recombining a repaired proof.
- Ma et al., *OProver: A Unified Framework for Agentic Formal Theorem
  Proving*, arXiv:2605.17283.
  Lesson used here: retain successful repairs and useful failed attempts as
  future retrieval memory.
- Xie et al., *FMC: Formalization of Natural Language Mathematical Competition
  Problems*, arXiv:2507.11275.
  Lesson used here: multiple proof attempts and Lean error feedback help, but
  only verified and quality-filtered fragments should survive.
- Meadows, Zhang, and Freitas, *FormalScience: Scalable Human-in-the-Loop
  Autoformalisation of Science with Agentic Code Generation in Lean*,
  arXiv:2604.23002.
  Lesson used here: keep proof-boundary artifacts and semantic-review evidence
  separate from kernel-checked proof success.

## Novel-Proving Systems and Sampling Discipline

- Han et al., *Proof Artifact Co-training for Theorem Proving with Language
  Models*, arXiv:2102.06203; Lample et al., *Hypertree Proof Search for Neural
  Theorem Proving*, NeurIPS 2022; Polu and Sutskever, *Generative Language
  Modeling for Automated Theorem Proving*, arXiv:2009.03393; and Polu et al.,
  *Formal Mathematics Statement Curriculum Learning*, arXiv:2202.01344.
  Lesson used here: generated proof search can be valuable, but accepted output
  must be reduced to maintainable kernel-checked Lean.
- Lin et al., *Goedel-Prover* and *Goedel-Prover-v2*; Xin et al.,
  *DeepSeek-Prover*; Ren et al., *DeepSeek-Prover-V2*; Wang et al.,
  *Kimina-Prover Preview*; Chen et al., *Seed-Prover*; Lin, Sun, Welleck, and
  Yang, *Lean-STaR*; and Li et al., *HunyuanProver*.
  Lesson used here: self-correction, subgoal decomposition, guided tree search,
  and synthetic-data loops are useful inspiration, but AppliedModelingLib agents should
  still work through narrow Lean checks, local retrieval, and readable final
  proofs.

## Semantic Alignment Boundary

- Ren, Li, and Qi, *MerLean: An Agentic Framework for Autoformalization in
  Quantum Computation*, arXiv:2602.16554.
  Lesson used here: back-translation and human-readable review are necessary
  around new definitions and theorem statements.
- Lu et al., *FormalAlign: Automated Alignment Evaluation for
  Autoformalization*, ICLR 2025, and Shebzukhov, *Improving Lean4
  Autoformalization via Cycle Consistency Fine-tuning*, arXiv:2603.24372.
  Lesson used here: semantic-alignment checks are useful review signals, not a
  replacement for Lean proof checking or human statement review.

## Skill-Update Provenance

- Guo et al., *SKILL-DISCO: Distilling and Compiling Agent Traces into
  Reusable Procedural Skills*, arXiv:2606.26669.
  Lesson used here: durable proof-repair lessons should be promoted into this
  skill or the relevant domain proof reference after they recur in real proof
  sessions.
