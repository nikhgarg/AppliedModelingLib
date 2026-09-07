# CSLib Compatibility Notes

Current as of April 23, 2026.

CSLib is now an explicit dependency of this repository. Treat it as an external
upstream library rather than copying broad chunks into AppliedModelingLib. The best
near-term use is to import small foundational APIs where they remove current
paper-level seams.

For other non-imported Lean repositories that agents may scout before creating
local APIs, see [`UPSTREAM_LEAN_SOURCES.md`](UPSTREAM_LEAN_SOURCES.md).

## Source

- Website: https://www.cslib.io/
- Repository: https://github.com/leanprover/cslib
- API docs: https://leanprover.github.io/cslib/

AppliedModelingLib currently targets Lean `v4.30.0-rc2` and pins CSLib to the matching
release tag:

```toml
[[require]]
name = "cslib"
scope = "leanprover"
rev = "v4.30.0-rc2"
```

Do not depend on CSLib `main` unless the repository is intentionally moved to
the same Lean toolchain as CSLib `main`.

## High-Value Modules

### Relation Steps

Candidate import:

- `Cslib.Foundations.Data.RelatesInSteps`

Current use:

- `AppliedModelingLib.SocialChoice.FairDivision.IndivisibleGoods` imports this module.
- `HasStepEnvyCycle` records positive-length closed envy walks via
  `Relation.RelatesInSteps`.
- `hasStepEnvyCycleExtraction_of_finite` converts the finite non-acyclic envy
  graph witness into this CSLib-backed representation.

Useful definitions and lemmas:

- `Relation.RelatesInSteps r a b n`
- `Relation.RelatesWithinSteps r a b n`
- conversion from `RelatesInSteps` to `Relation.ReflTransGen`
- conversion from `Relation.ReflTransGen` to some step count
- `RelatesInSteps.head`, `tail`, `succ`, `succ'`, `trans`, and `map`

This is the most directly useful CSLib API for the fair-division Test-of-Time
paper. It was used to extract a simple nodup envy cycle from a closed
transitive-closure envy walk. A step-indexed path relation gives a natural
minimal-counterexample proof:

1. convert `Relation.TransGen envyEdge i i` to a positive `RelatesInSteps`
   witness;
2. choose a shortest positive closed walk;
3. prove that shortest closed walks have no repeated interior vertices;
4. convert the shortest closed walk to `EnvyCycleList`;
5. use the already-proved list-to-permutation and permutation-to-reduction
   lemmas.

This seam is now closed in the reusable module
`AppliedModelingLib.Foundations.Graph.Cycle` by
`AppliedModelingLib.Foundations.Graph.exists_simple_cycle_list_of_stepCycle`; the fair-division
paper applies it via `hasEnvyCycleListExtraction_of_finite`.

### Relation Rewriting

Candidate import:

- `Cslib.Foundations.Data.Relation`

Useful definitions and lemmas:

- confluence, diamond, semi-confluence, and Church-Rosser interfaces
- normal forms and normalizing relations
- transitive-closure well-foundedness helpers
- terminating relations

This is not immediately needed for monoculture or fair division, but it is a
good fit for future algorithmic process proofs: deferred acceptance dynamics,
auction improvement dynamics, local-search convergence, and rewrite-style
mechanism transformations.

### Timed Computations

Candidate import:

- `Cslib.Algorithms.Lean.TimeM`

Useful definitions:

- `TimeM T α`
- `.ret` and `.time`
- monadic `bind`
- `tick`

This could support executable algorithm proofs for online matching, deferred
acceptance, and cycle-elimination procedures. It is not needed for the current
existence-only theorems.

### Automata And Languages

Candidate imports:

- `Cslib.Computability.Languages.Language`
- `Cslib.Computability.Languages.RegularLanguage`
- `Cslib.Computability.Automata.*`

Useful definitions and theorem families:

- regular-language closure facts
- deterministic and nondeterministic acceptor interfaces
- omega-language and Buchi automata infrastructure

These are relevant to computational social choice and complexity tracks:
encoding voting rules, languages of valid ballots, reductions, and finite-state
gadget checks. They are not directly useful for the monoculture Mallows proof.

### URM Computability

Candidate imports:

- `Cslib.Computability.URM.Defs`
- `Cslib.Computability.URM.Execution`
- `Cslib.Computability.URM.Computable`

Useful definitions:

- URM instructions
- register states
- programs and machine states
- execution semantics

This is relevant for long-run complexity formalizations, especially if
AppliedModelingLib develops computability/reduction interfaces. It is not currently the
right substrate for PPAD or communication complexity lower bounds; those need
domain-specific reduction and protocol libraries first.

## Paper-Track Impact

- Fair division 2025 Test-of-Time paper: high impact. `RelatesInSteps` closed
  the explicit simple-cycle extraction seam.
- Imported paper modules: low direct impact. The proof obligations are
  finite probability and Mallows weight inequalities, not CS foundation gaps.
- Digital-goods auction 2021 Test-of-Time paper: medium future impact. `TimeM`
  may help once executable auction algorithms and running-time claims matter.
- Online matching 2024 Test-of-Time paper: medium future impact. `TimeM` can
  structure certified algorithms, but competitive-ratio libraries still need to
  be built locally.
- Voting/STV 2016 Test-of-Time paper: medium future impact. Automata/language
  APIs can help with encodings, but voting primitives should live in AppliedModelingLib.
- Nash/complexity 2022 and communication 2019 tracks: long-run impact. URM and
  language APIs are useful foundations, but they do not yet supply PPAD,
  communication protocols, or economic reductions.

## Recommendation

Keep CSLib imports narrow. The next practical import should be driven by an
active theorem seam, not by convenience. With the fair-division
`RelatesInSteps` seam closed, consider automata/languages only when the voting
or complexity tracks begin in earnest.
