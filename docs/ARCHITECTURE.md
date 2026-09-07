# AppliedModelingLib Architecture

This repository has three layers:

1. `AppliedModelingLib/` is the reusable textbook layer.
2. `papers/` is the paper-by-paper audit trail.
3. `scripts/`, `skills/`, and the Lean audit infrastructure provide the
   formalization workflow, source-to-Lean checks, closeout, and reader documents.

The split is deliberately strict. Generic concepts that should be reusable
across applied-modeling papers belong in `AppliedModelingLib`; source-faithful theorem statements,
paper notation, PDFs, DAGs, and status ledgers belong in `papers/`.

## Core Library

`AppliedModelingLib/` contains abstract definitions and theorems with paper-specific
notation removed. A result belongs here when a second paper would plausibly use
it after renaming variables.

Current top-level areas:

- `Foundations/`: finite math, graph/counting tools, probability, econometrics,
  optimization, asymptotics, and reusable proof infrastructure.
- `MechanismDesign/`: auctions and mechanism primitives.
- `SocialChoice/`: fair division, finite ranking, and voting-style primitives.
- `Markets/`: matching and platform/market primitives.
- `Learning/`: bandits and learning models.
- `Algorithms/`: online algorithms, complexity, and algorithmic proof tools.
- `GameTheory/`: strategic responses, equilibria, and performative models.
- `Queueing/`: queue dynamics, service disciplines, and congestion pricing.
- `Privacy/`: differential privacy and composition.
- `Alignment/`: alignment axioms and welfare models.
- `Applications/`: domain-specific reusable layers, currently including
  admissions, ratings, recommendations, and algorithmic fairness.

`Audit/` contains Lean-native elaboration and proof-audit support. The current
[domain index](APPLIEDMODELINGLIB_DOMAIN_INDEX.md) supplies the complete module
inventory; the overview here describes the area boundaries.

Probability foundations currently include finite PMFs and expectations,
finite event-share/binary-mixture interfaces, conditional probability, finite
variance, measure inequalities, continuous probability support, finite Markov
kernel/chain primitives, two-state CTMC closed-form support, finite occupancy
processes, and finite MDP primitives, plus finite stochastic-dominance/coupling
certificates and an algebraic Gaussian
posterior/CDF interface. GLM/LG-style testing papers should start with
`AppliedModelingLib.Foundations.Probability.Gaussian` for conjugate posterior formulas,
standardization, finite multi-signal weights, nonzero-noise-mean signal
centering, posterior/raw-signal threshold conversion, posterior and threshold
monotonicity, finite-mixture capacity/admitted-mean accounting, and explicit
CDF/hazard assumptions before introducing paper-specific admissions thresholds.
Dynamic platform or surge-pricing papers should usually start with
`AppliedModelingLib.Foundations.Probability.MDP` for controlled dynamics,
`AppliedModelingLib.Foundations.Probability.MarkovChain` for passive dynamics, and
`AppliedModelingLib.Foundations.Probability.CTMC` for continuous-time two-state switch
probabilities, before introducing paper-specific states and policies. Use
`AppliedModelingLib.Foundations.Probability.StochasticDominance` for monotone policy or
state-distribution comparisons. Rating-system and recommender asymptotic papers
with finite rating scales should start from
`AppliedModelingLib.Foundations.Probability.FiniteSupportMGF` for log-MGF/rate-function
algebra and `AppliedModelingLib.Foundations.Probability.LargeDeviations` for
exponential-rate certificates, finite union/weighted-sum aggregation,
upper/lower exponential bound weakening, and pairwise ranking-error bounds.
Generic results retain their analytic hypotheses; a paper claiming a concrete
large-deviation theorem must prove the required distribution-specific bridge.
An assumed certificate does not establish that source theorem.
Accuracy-diversity papers with
continuous top-`k` values should use
`AppliedModelingLib.Foundations.Probability.OrderStatistics` for top-`k` expectation
formulas and explicitly conditional marginal-limit interfaces, then feed the
resulting eventual marginal sandwiches into the optimization layer. Real-valued threshold
or tail arguments should use
`AppliedModelingLib.Foundations.Probability.RealDistribution` for lower CDF mass,
upper-tail mass, monotonicity, and complement identities before adding
paper-specific distribution-family asymptotics.

Social-choice and ranking papers should start with
`AppliedModelingLib.SocialChoice.Ranking` for finite full rankings, first/second choice
projections, top-two swaps, rank lookup, best-remaining-after-one-removal facts,
inversion finsets, Kendall tau distance, and deletion/relabeling formulas.
The base Mallows law/weight layer also lives there. KR21 keeps paper names as
wrappers where stable; its local `MallowsSpec` is still preserved for later
field-rewrite-heavy proof files until an explicit adapter is installed.

Optimization foundations currently include finite pointwise argmax/existence
lemmas, abstract expected-objective wrappers, feasible-set optimality
certificates, finite feasible-search wrappers, move-graph exchange optimality,
static choice-equilibrium projection tools, binary no-deviation/threshold
bridges, and lightweight finite LP weak-duality certificates. Papers with LP
witnesses, exchange arguments, binary best-response policies, threshold
searches, or endpoint/current-bound optimality proofs should start with
`AppliedModelingLib.Foundations.Optimization`; the longer promotion plan lives in
[`docs/OPTIMIZATION_LIBRARY_ROADMAP.md`](OPTIMIZATION_LIBRARY_ROADMAP.md).

For cross-paper extraction candidates spanning probability, rankings,
stochastic processes, continuous analysis, and design optimization, use
[`APPLIEDMODELINGLIB_DOMAIN_INDEX.md`](APPLIEDMODELINGLIB_DOMAIN_INDEX.md) and its linked
domain-specific roadmaps. Use their named entrypoints before adding
paper-local variants while preserving paper-facing theorem names.

## Library Maintenance TODOs

- Auction import boundary: reusable auction primitives live under
  `AppliedModelingLib.MechanismDesign.Auctions`, while paper-facing auction theorem
  aggregators live in their paper folders and should be imported directly by
  paper modules or examples that need those theorem surfaces. Keep this
  boundary intact so shared-library builds do not depend on large paper-local
  theorem files.
- Build requirement: run `lake build AppliedModelingLib` against each exact
  public release candidate. A historical green build does not establish the
  current candidate's status. Active private paper repairs may use focused
  targets before the final aggregate check.

## Paper Folders

Each paper folder is an audit artifact for one source paper. The folder name
must use the citation-style convention
`[AuthorInitials][2DigitYear][Descriptor]`, for example
`MSVV07AdWords` or `Roth82StableMatching`.

Current-protocol paper folders use:

- `.gitignore`
- `README.md`
- `FINAL_VALIDATION_REPORT.md`
- `status.json`
- `docs/DependencyDAG.tex` and its rendered PDF
- `docs/HUMAN_REVIEW_PACKET.tex` and its rendered PDF
- `docs/SOURCE_CLARIFICATIONS.md` when substantive comparisons need a memo
- `docs/FORMALIZATION_PLAN.md` when a public plan is intentionally retained
- `MainTheorems.lean`
- `PaperInterface.lean`
- exact proof endpoints, optionally collected in `ProofInterface.lean`
- source maps and current evidence under `audit/`, including memo coverage
- byte-pinned source artifacts in the audit workspace, with redistribution
  controlled by the public release policy

The paper folder should expose the source's definitions, theorem numbers, and
assumptions clearly enough that a human can compare Lean against the PDF without
reading the entire implementation stack.

For agent-facing instructions on starting and finishing a paper, use
[`docs/AGENT_FORMALIZATION_WORKFLOW.md`](AGENT_FORMALIZATION_WORKFLOW.md). For a
concise domain-by-domain index of reusable modules and entrypoints, use
[`docs/APPLIEDMODELINGLIB_DOMAIN_INDEX.md`](APPLIEDMODELINGLIB_DOMAIN_INDEX.md).

## Lean Style

Follow the Mathlib-derived conventions in `docs/LEAN_STYLE.md`: narrow imports,
`UpperCamelCase.lean` module names, module docstrings with main declarations
for reusable library files, and Mathlib-style declaration names. Paper-facing
wrappers may preserve source theorem numbers for auditability, but generic
`AppliedModelingLib` APIs should use paper-independent names.

## Audit Tooling Ownership: Lean Is the Lean Authority

No accepting audit, closeout, dashboard, packet, or migration path may parse
Lean source in Python or shell code. Repository tooling must not reconstruct
declarations, binders, namespaces, ownership, dependencies, implicit
arguments, theorem relations, source ranges, or proof closure from Lean text,
regular expressions, line numbers, or naming conventions.

Lean owns all facts about Lean programs. A small compiled Lean Meta query may
read the already elaborated environment and use Lean's own APIs for declaration
information, transparent reduction, expression traversal, source ownership
and ranges, dependency edges, proof equality, and axiom or `sorry` closure.
Such a query is an adapter over elaborated Lean data, not a second parser and
not a repository-specific semantic classifier. In particular, do not add
rules for declaration spellings, namespaces, particular typeclasses, result
sorts, binder styles, or paper-specific interface shapes. Non-routed
transparent implementation definitions are reduced by Lean; explicit
source-semantic roots remain visible; and genuinely opaque or unproved
boundaries fail closed or remain explicit.

Python may supply typed routing coordinates, launch the bounded Lean query,
validate the exact and complete response schema, bind its result to frozen
repository and paper-source bytes, schedule work, and render human-facing
artifacts. Python may not reinterpret Lean semantics or fill in a missing Lean
fact. If the accepting workflow needs a fact that the current Lean query does
not emit, extend the Lean query using Lean APIs or stop with a typed error.
Never install a source parser as a fallback.

Lexical inspection may exist only as an explicitly diagnostic aid for a file
that does not yet elaborate. It must live outside the accepting current-audit
dependency graph, carry no evidence authority, and never silently substitute
for an elaborated result. Current-path regression tests should make calls to
legacy Lean-source parsers, owner maps, line-number selectors, and
qualified-name discovery fatal.

This is a repository-organization boundary, not an implementation preference.
Code review must reject a new Python or shell Lean parser even when it appears
smaller than extending the Lean query. Any retained lexical diagnostic must be
physically isolated from accepting audit modules, named as non-evidentiary,
and tested so that importing or calling it from a current closeout fails.

## Paper-Facing Ledgers

`PaperInterface.lean` is the stable human-facing semantic interface for a
current-protocol paper. It should be readable on its own: expose actual source
definitions/models and one complete transparent `Spec : Prop` per selected
source claim in dependency order. `ProofInterface.lean` is the distinct proof
endpoint surface: each theorem or lemma is typed by its paired Spec and calls
into `MainTheorems.lean` or lower proof files. `MainTheorems.lean` remains the
implementation layer for source-faithful theorem endpoints.

Paper-facing ledgers should:

- state definitions and transparent Specs in source/dependency order;
- use paper theorem/lemma/proposition names or numbers in docstrings;
- expose exact formulas with paper-local `def` or `abbrev`s when generic
  library names would hide the source equation;
- make conditional assumptions explicit in theorem signatures;
- keep source-faithful wrappers separate from auxiliary finite analogues or
  certificate interfaces;
- avoid `#check`-only ledgers, duplicate theorem-shaped semantic rows, and
  hidden proof placeholders.

A `formalized` status row should point to a real Lean declaration and should
list `None` under remaining assumptions. Conditional rows must name the exact
open certificate, bridge, or assumption declaration.

Paper status cells use the controlled vocabulary in `docs/STATUS.md`.
Do not put free-form progress prose in the status cell; put caveats, closed
sub-results, and remaining certificates in the final ledger column.

## Upstreaming

The normal workflow is:

1. Scaffold the paper folder and paper-facing theorem statements.
2. Build the proof locally, using source notation.
3. Identify reusable seams that pass the second-paper test.
4. Move those seams to `AppliedModelingLib`.
5. Leave thin paper-facing wrappers in `papers/[Paper]/MainTheorems.lean`.

Reusable seams include finite expectation/probability lemmas, Markov kernels,
probability inequalities, allocation primitives, mechanism interfaces,
matching/fair-division facts, optimization certificates, and generic algorithm
invariants. Hyper-specific algebraic rearrangements should stay paper-local.

## Automation Direction

The intended agent workflow is: given a paper link, cache and byte-pin the
source, enumerate the selected source surface, create the role-shaped semantic
interface and distinct proof endpoints, upstream reusable primitives, prove the
selected claims, and then let the closeout planner schedule the final DAG and
validation report from the stable reviewed surface. The
`scripts/new_paper.py` intake script provides the deterministic first step of
that workflow, while `scripts/audit_repository.py` checks mechanical hygiene
before status updates or handoff.
