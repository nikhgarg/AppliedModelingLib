# Paper Workflow Insights

Last reviewed through: 2026-06-27.

This ledger records the AI-formalization workflow papers reviewed from the
related-work discussion in Garg, *EconCSLib: AI-Assisted Lean Formalization for
Economics & Computation research*, arXiv:2606.13306. It is a credit and source
map for `../SKILL.md`, not a replacement for the operational AppliedModelingLib
formalizer skill.

## Core Source

- Garg, *EconCSLib: AI-Assisted Lean Formalization for Economics & Computation
  research*, arXiv:2606.13306.
  Contribution: paper-oriented human-AI-Lean loop; compact paper-facing Lean
  interfaces; DAGs; post-formalization validation reports; review dashboard;
  LLM-as-judge back-translation; reusable library elevation from papers.

## Project-Scale Formalization

- Wang et al., *M2F: Automated Formalization of Mathematical Literature at
  Scale*, arXiv:2602.17016.
  Contribution: split long-form sources into atomic blocks, infer dependency
  order, compile declaration skeletons first, then repair proofs under fixed
  signatures. Public generated code: <https://github.com/optsuite/ReasBook.git>.

- Gloeckle et al., *Automatic Textbook Formalization*, arXiv:2604.03071.
  Contribution: large multi-agent textbook formalization via shared codebase,
  version control, side-by-side blueprint site, and many agents working in
  parallel on dependency-compatible regions.

- Rammal et al., *Formalizing Mathematics at Scale*, arXiv:2605.29955.
  Contribution: AutoformBot/Atlas pattern: dependency-aware task scheduling,
  collaborative version control, and verifier-equipped LLM agents for
  large-scale Lean library construction.

- Urban, *130k Lines of Formal Topology in Two Weeks: Simple and Cheap
  Autoformalization for Everyone?*, arXiv:2601.03298.
  Contribution: long-running low-overhead LLM/checker loop can scale when the
  proof checker is fast and the feedback loop is simple.

- Wang et al., *MathAtlas: A Benchmark for Autoformalization in the Wild*,
  arXiv:2605.14061.
  Contribution: dependency graphs are evaluation objects, not just planning
  artifacts; deep dependency trees are a difficulty signal and should guide
  scheduling and partial-boundary selection.

## Dependency Graphs, Blueprints, and Structural Fidelity

- Cabral et al., *ProofFlow: A Dependency Graph Approach to Faithful Proof
  Autoformalization*, arXiv:2510.15981.
  Contribution: build a proof-step DAG, formalize intermediate lemmas, and score
  syntactic correctness, semantic faithfulness, and structural fidelity.
  Public code: <https://github.com/Huawei-AI4Math/ProofFlow>.

- Zhu, Monticone, Avigad, and Welleck, *LeanArchitect: Automating Blueprint
  Generation for Humans and AI*, arXiv:2601.22554.
  Contribution: keep informal blueprint metadata and formal Lean declarations
  synchronized from Lean annotations; use generated dependency data to expose
  blueprint inconsistencies and track progress.

- Wang et al., *Aria: An Agent For Retrieval and Iterative Auto-Formalization
  via Dependency Graph*, arXiv:2510.04520.
  Contribution: recursively decompose statements into a dependency graph, then
  construct formalizations from grounded formal concepts; use term-level
  grounding/scoring before accepting translations.

- Jiang et al., *Draft, Sketch, and Prove: Guiding Formal Theorem Provers with
  Informal Proofs*, arXiv:2210.12283.
  Contribution: informal proof sketches can guide proof search and subgoal
  decomposition; use source proof structure as guidance, not as unquestioned
  executable content.

## Retrieval and Grounding

- Yang et al., *LeanDojo: Theorem Proving with Retrieval-Augmented Language
  Models*, NeurIPS 2023.
  Contribution: programmatic Lean interaction, accessible-premise extraction,
  hard-negative premise selection, and retrieval-augmented proving.
  Public code: <https://github.com/lean-dojo/LeanDojo>.

- Lu et al., *Automated Formalization via Conceptual Retrieval-Augmented LLMs*,
  arXiv:2508.06931.
  Contribution: retrieve formal definitions for core mathematical concepts and
  use domain/application context to disambiguate polymorphic concepts.

- Jana et al., *ProofBridge: Auto-Formalization of Natural Language Proofs in
  Lean via Joint Embeddings*, arXiv:2510.15681.
  Contribution: retrieve semantically aligned theorem/proof pairs across
  natural and formal language; evaluate theorem+proof semantic correctness, not
  theorem strings alone.

- Song, Yang, and Anandkumar, *Towards Large Language Models as Copilots for
  Theorem Proving in Lean*, arXiv:2404.12534.
  Contribution: integrate LLM tools into the Lean workflow for tactic
  suggestion, proof search, and premise selection, while keeping humans in the
  loop. Public code: <https://github.com/lean-dojo/LeanCopilot>.

## Compiler-Guided Generation and Repair

- First et al., *Baldur: Whole-Proof Generation and Repair with Large Language
  Models*, arXiv:2303.04910.
  Contribution: whole-proof generation plus repair from failed attempt and
  compiler error context.

- Ospanov, Farnia, and Yousefzadeh, *APOLLO: Automated LLM and Lean
  Collaboration for Advanced Formal Reasoning*, arXiv:2505.05758.
  Contribution: modular repair agents isolate syntax errors, failing sublemmas,
  automated-solver opportunities, and remaining goals before recombining and
  rechecking proofs.

- Ma et al., *OProver: A Unified Framework for Agentic Formal Theorem Proving*,
  arXiv:2605.17283.
  Contribution: failed attempts, compiler feedback, retrieved proofs, and
  successful repairs should become a persistent retrieval/training memory.

- Xie et al., *FMC: Formalization of Natural Language Mathematical Competition
  Problems*, arXiv:2507.11275.
  Contribution: few-shot prompting, Lean error feedback, and multiple samples
  materially improve formalization; keep generated datasets only after quality
  filtering.

- Huang et al., *FormaRL: Enhancing Autoformalization with no Labeled Data*,
  arXiv:2508.18914.
  Contribution: syntax checks and semantic/consistency checks can be converted
  into training rewards, even with little labeled data. Public code:
  <https://github.com/THUNLP-MT/FormaRL>.

## Semantic Alignment and Human Review

- Ren, Li, and Qi, *MerLean: An Agentic Framework for Autoformalization in
  Quantum Computation*, arXiv:2602.16554.
  Contribution: extract statements from LaTeX, formalize to Lean, and translate
  Lean back to human-readable LaTeX so review can focus on new definitions and
  axioms.

- Meadows, Zhang, and Freitas, *FormalScience: Scalable Human-in-the-Loop
  Autoformalisation of Science with Agentic Code Generation in Lean*,
  arXiv:2604.23002.
  Contribution: staged human review, structured QA extraction, Lean prompts,
  batch-level compilation, proof-boundary validation, flattened training data,
  and explicit audit trail for semantic drift. Public code:
  <https://github.com/jmeadows17/formal-science>.

- Lu et al., *FormalAlign: Automated Alignment Evaluation for
  Autoformalization*, arXiv:2410.10135.
  Contribution: automated natural/formal semantic-alignment evaluation can
  reduce but not replace manual verification. Public code:
  <https://github.com/rookie-joe/FormalAlign>.

- Shebzukhov, *Improving Lean4 Autoformalization via Cycle Consistency
  Fine-tuning*, arXiv:2603.24372.
  Contribution: natural-language-to-Lean-to-natural-language cycle consistency
  is a useful signal for meaning preservation; treat it as a review heuristic,
  not a proof of equivalence.

- Meadows et al., FormalScience codebase.
  Code-specific contribution: retain intermediate artifacts (`qa_data`,
  `lean_prompt_data`, raw Lean outputs, structured proofs, postprocessed
  batches) so reviewers can trace how a formal answer was produced.

## Interfaces and External Tooling

- Aniva et al., *Pantograph: A Machine-to-Machine Interaction Interface for
  Advanced Theorem Proving, High Level Reasoning, and Data Extraction in Lean
  4*, arXiv:2410.16429.
  Contribution: programmatic Lean interfaces make proof search, state
  extraction, and high-level agent reasoning more robust than ad hoc shell
  parsing.

- Klaus, Tolmach, and Conejero, *A Rust-to-Lean Verification Pipeline with AI
  Provers: An Experience Report*, arXiv:2605.30106.
  Contribution: for extracted-code verification, separate source extraction,
  specification libraries, AI proof generation, and kernel-checked proof
  obligations; document toolchain drift and missing-lemma friction explicitly.

## Benchmark and Survey Context

- Azerbayev et al., *ProofNet: Autoformalizing and Formally Proving
  Undergraduate-Level Mathematics*, arXiv:2302.12433.
  Contribution: pair natural statements/proofs with formal theorem statements
  and use prompt retrieval/backtranslation baselines.

- Zheng, Han, and Polu, *MiniF2F: a cross-system benchmark for formal
  olympiad-level mathematics*, arXiv:2109.00110.
  Contribution: benchmarks must separate statement formalization from proof
  search and support cross-system comparison.

- Ying et al., *Lean Workbook: A Large-Scale Lean Problem Set Formalized from
  Natural Language Math Problems*, NeurIPS 2024.
  Contribution: large curated natural-language/Lean corpora can feed benchmark,
  retrieval, and training loops.

- Gao et al., *Herald: A natural language annotated Lean 4 dataset*, ICLR 2025.
  Contribution: natural-language annotations around Lean declarations are useful
  retrieval and training material.

- Weng et al., *Autoformalization in the Era of Large Language Models: A
  Survey*, arXiv:2505.23486.
  Contribution: organize workflow analysis end-to-end: preprocessing, model
  design, evaluation, applications, datasets, and open challenges.

## Practical Translation Into AppliedModelingLib

- Use dependency graphs both as planning artifacts and as review surfaces.
- Compile statement skeletons first; proof repair should not keep changing the
  public theorem signature unless source translation was wrong.
- Treat concept retrieval as part of translation validation, not just proof
  search.
- Keep a durable record of candidate statements, failed proof attempts, Lean
  errors, repaired proof fragments, and final accepted declarations.
- Separate semantic-alignment review from kernel proof checking.
- Use human review at theorem boundaries, new definitions, source deviations,
  and remaining assumptions.
- For multi-agent runs, schedule work by DAG region and require each worker to
  report exact files, declarations, and validation commands.
