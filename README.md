# AppliedModelingLib

AppliedModelingLib is a Lean 4 project for research in Economics and
Computation and related applied-mathematics fields. Its goal is to enable
researchers to formalize papers in Lean without needing to know Lean
themselves. The central design principle is a human-AI-Lean formalization
workflow: an LLM writes Lean code, Lean checks formal statements and proofs,
and both humans and LLM-as-judge processes can verify that the paper's
statements were translated into Lean correctly. We develop agent skills,
human-facing reporting, a review dashboard, and auditing procedures to support
this workflow.

Links:
- [Project website](https://gargnikhil.com/AppliedModelingLib/)
- [Paper describing project](https://arxiv.org/abs/2606.13306)
- [Slack workspace for applied math modeling in Lean](https://join.slack.com/t/appliedmodelinglib/shared_invite/zt-42slirzxx-rEO8eEns7~4~i3Lbu7N~lA)

If you use this project, please cite the following paper

```
@article{garg2026econcslib,
  title={EconCSLib: AI-Assisted Lean Formalization for Economics \& Computation research},
  author={Garg, Nikhil},
  journal={arXiv preprint arXiv:2606.13306},
  year={2026}
}
```

## Updating An Existing Fork After The Rename

Existing fork owners can keep their forks and update their local upstream:

```bash
git remote set-url upstream https://github.com/nikhgarg/AppliedModelingLib.git
git fetch upstream
```

## Contribute A Paper Formalization

Contributions can add a paper formalization or improve the reusable library,
tooling, and documentation. A paper contribution focuses on that paper's
results and validation report.

Start with the [contribution guide](CONTRIBUTING.md). The
[step-by-step workflow](docs/NEW_CONTRIBUTOR_WORKFLOW.md) covers setup,
formalization, validation, and submitting a pull request.

When using a coding agent, give it the paper URL, exact source version, and
folder name, and ask it to follow the repository's paper-formalization skill
through source inventory, proofs, and paper-scoped closeout.

## How The Repository Is Organized

- `AppliedModelingLib/` contains reusable mathematics and modeling tools shared
  across paper formalizations.
- `papers/` contains one folder per source paper. These folders preserve the
  paper's notation, theorem numbering, proof DAG, validation report, and
  human-facing Lean interface.
- `docs/` contains project documentation. Some files are human-facing strategy
  and status documents; others are detailed conventions for agents and
  maintainers.
- `skills/econcs-formalizer/` contains the agent workflow instructions used to
  formalize papers consistently.
- General lessons from private workflow examples are incorporated into the
  public skills; the underlying wiki and feedback history remain private.

## Human understanding of a Formalized Paper

Start in the paper folder under `papers/<PaperName>/`.

For a completed or nearly completed paper, read these files in this order:

1. `FINAL_VALIDATION_REPORT.md`: source checked, theorem inventory, proof
   deviations, remaining assumptions, and final status.
2. The linked source-clarification memo: precise source-to-formalized changes,
   additional assumptions, and remaining formalization gaps.
3. `docs/HUMAN_REVIEW_PACKET.pdf`: the assembled source and Lean review material.
4. `PaperInterface.lean`: readable definitions and theorem statements matching
   the paper. This is the main human-facing Lean file.
5. `docs/DependencyDAG.pdf`: visual map of named definitions, lemmas, theorems,
   and remaining proof boundaries, with the TeX source alongside it.
6. `README.md`: paper metadata and theorem-status ledger.

Implementation-level proof files are for maintainers and agents. They should
not be necessary for a first human audit of what the paper claims and what Lean
proves.

## Development

This project is aligned to Lean/mathlib/CSLib `v4.30.0-rc2`.

See the [contributor workflow](docs/NEW_CONTRIBUTOR_WORKFLOW.md) for setup and
validation commands, and the [architecture guide](docs/ARCHITECTURE.md) for
library and tooling development.

## License

Unless otherwise noted, the Lean source, scripts, documentation, and site source
are licensed under the Apache License, Version 2.0. See [`LICENSE`](LICENSE).
Source-paper PDFs and extracted text caches are not included in the public
repository unless redistribution rights have been checked separately.

## Related project using the former name

See also [this paper](https://arxiv.org/abs/2606.16144) and
[Lean Project](https://github.com/gametheoryinlean/EconCSLib), called
EconCSLib. The two projects are separate and independently (and concurrently)
developed, with different focuses: our project focuses on automated
formalization of research papers (with human-in-the-loop translation
validation), while their project focuses on human curation (with LLM support)
of a library of concepts for Economics and Computation.

## More Documentation

- [docs/README.md](docs/README.md): documentation index.
- [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md): public paper status.
- [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md): repository architecture.
- [docs/APPLIEDMODELINGLIB_DOMAIN_INDEX.md](docs/APPLIEDMODELINGLIB_DOMAIN_INDEX.md): library modules by domain.
- [docs/NEW_CONTRIBUTOR_WORKFLOW.md](docs/NEW_CONTRIBUTOR_WORKFLOW.md): public repository and contribution workflow.
- [docs/LEAN_STYLE.md](docs/LEAN_STYLE.md) and [docs/STATUS.md](docs/STATUS.md): contribution conventions.
