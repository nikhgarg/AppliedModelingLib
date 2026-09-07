#!/usr/bin/env python3
"""Pure structural parsing and validation for a paper review surface.

This module deliberately knows nothing about Lean subprocesses, semantic
judgments, dashboards, closeout planners, or final receipts.  It gives every
consumer the same cheap interpretation of the declarations exposed by
``PaperInterface.lean`` and the configured support declarations in
``Assumptions.lean``.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Mapping


REVIEW_DECL_RE = re.compile(
    r"^\s*(?:(?:@[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?\s+)*)?"
    r"(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:theorem|lemma|def|abbrev|axiom|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b",
    re.M,
)
REVIEW_DECL_KIND_RE = re.compile(
    r"^\s*(?:(?:@[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?\s+)*)?"
    r"(?:(?:noncomputable|private|protected)\s+)*"
    r"(theorem|lemma|def|abbrev|axiom|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b",
    re.M,
)
LIBRARY_DECL_KIND_RE = re.compile(
    r"^\s*(?:(?:@[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?\s+)*)?"
    r"(?:(?:noncomputable|private|protected)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b",
    re.M,
)
REVIEW_EXPORT_OPEN_RE = re.compile(
    r"^\s*export\s+[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\s+\((.*)$"
)
REVIEW_EXPORT_NAME_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*\b")
ASSUMPTION_DECL_NAME_RE = re.compile(
    r"^(?:paper_)?assumption(?:_|$)|^source_assumption(?:_|$)|_assumption(?:_|$)"
)


def declaration_match_at(
    lines: list[str], line_index: int, declaration_re: re.Pattern[str]
) -> re.Match[str] | None:
    """Match a Lean declaration even when keyword and name span two lines."""

    match = declaration_re.match(lines[line_index])
    if match is not None or line_index + 1 >= len(lines):
        return match
    return declaration_re.match(lines[line_index] + "\n" + lines[line_index + 1])


def review_rows_from_interface_text(interface_text: str) -> list[tuple[int, str]]:
    """Return declaration and explicit export rows exposed by an interface."""

    lines = interface_text.splitlines()
    rows: list[tuple[int, str]] = []
    line_number = 1
    block_depth = 0
    while line_number <= len(lines):
        line = lines[line_number - 1]
        stripped = line.strip()
        if block_depth > 0:
            block_depth += line.count("/-")
            block_depth -= line.count("-/")
            block_depth = max(block_depth, 0)
            line_number += 1
            continue
        if stripped.startswith("/-"):
            block_depth += line.count("/-")
            block_depth -= line.count("-/")
            block_depth = max(block_depth, 0)
            line_number += 1
            continue
        if stripped.startswith("--"):
            line_number += 1
            continue
        match = declaration_match_at(lines, line_number - 1, REVIEW_DECL_RE)
        if match:
            rows.append((line_number, match.group(1)))
            line_number += 1
            continue
        export_match = REVIEW_EXPORT_OPEN_RE.match(line)
        if export_match:
            chunks = [export_match.group(1)]
            end_line_number = line_number
            while ")" not in chunks[-1] and end_line_number < len(lines):
                end_line_number += 1
                chunks.append(lines[end_line_number - 1])
            names_text = "\n".join(chunks).split(")", 1)[0]
            for name in REVIEW_EXPORT_NAME_RE.findall(names_text):
                rows.append((line_number, name))
            line_number = end_line_number + 1
            continue
        line_number += 1
    return rows


def lean_declaration_blocks(
    interface_text: str,
    declaration_re: re.Pattern[str],
) -> dict[str, tuple[int, str, str]]:
    """Return syntactic Lean declaration blocks keyed by local name."""

    lines = interface_text.splitlines()
    starts: list[tuple[int, str, str]] = []
    block_depth = 0
    for line_number, line in enumerate(lines, start=1):
        stripped = line.strip()
        if block_depth > 0:
            block_depth += line.count("/-")
            block_depth -= line.count("-/")
            block_depth = max(block_depth, 0)
            continue
        if stripped.startswith("/-"):
            block_depth += line.count("/-")
            block_depth -= line.count("-/")
            block_depth = max(block_depth, 0)
            continue
        if stripped.startswith("--"):
            continue
        match = declaration_match_at(lines, line_number - 1, declaration_re)
        if match:
            starts.append((line_number, match.group(1), match.group(2)))

    out: dict[str, tuple[int, str, str]] = {}
    for index, (line_number, kind, name) in enumerate(starts):
        next_line = starts[index + 1][0] if index + 1 < len(starts) else len(lines) + 1
        source = "\n".join(lines[line_number - 1 : next_line - 1]).strip()
        out[name] = (line_number, kind, source)
    return out


def review_declaration_blocks(interface_text: str) -> dict[str, tuple[int, str, str]]:
    return lean_declaration_blocks(interface_text, REVIEW_DECL_KIND_RE)


def library_declaration_blocks(interface_text: str) -> dict[str, tuple[int, str, str]]:
    return lean_declaration_blocks(interface_text, LIBRARY_DECL_KIND_RE)


def is_assumption_decl_name(name: str) -> bool:
    return bool(ASSUMPTION_DECL_NAME_RE.search(name))


def assumption_declarations_from_text(
    source_text: str,
    declared_names: set[str] | None = None,
) -> dict[str, tuple[int, str, str]]:
    """Resolve configured support declarations by exact or unique suffix name."""

    declarations = review_declaration_blocks(source_text)
    if declared_names is None:
        return {
            name: declaration
            for name, declaration in declarations.items()
            if is_assumption_decl_name(name)
        }
    selected: dict[str, tuple[int, str, str]] = {}
    for configured_name in declared_names:
        candidates = [
            declaration
            for declared_name, declaration in declarations.items()
            if (
                declared_name == configured_name
                or declared_name.endswith("." + configured_name)
                or configured_name.endswith("." + declared_name)
            )
        ]
        if len(candidates) == 1:
            selected[configured_name] = candidates[0]
    return selected


def auxiliary_names_not_exported_from_review_source(
    auxiliary_names: set[str],
    actual_review_names: list[str],
    configured_assumption_declaration_names: set[str] | None = None,
) -> list[str]:
    exported = set(actual_review_names)
    exported.update(name.rsplit(".", 1)[-1] for name in actual_review_names)
    exported.update(configured_assumption_declaration_names or set())
    return sorted(auxiliary_names - exported)


def reviewed_names_not_declared_in_review_source(
    include_names: list[str],
    declaration_blocks: dict[str, tuple[int, str, str]],
) -> list[str]:
    declared = set(declaration_blocks)
    declared.update(name.rsplit(".", 1)[-1] for name in declaration_blocks)
    return [
        name
        for name in include_names
        if name not in declared and name.rsplit(".", 1)[-1] not in declared
    ]


def _configured_names(
    review_surface: Mapping[str, Any],
    field: str,
    *,
    required: bool = False,
) -> tuple[set[str], list[str]]:
    raw = review_surface.get(field)
    if raw is None and not required:
        return set(), []
    if not isinstance(raw, list):
        return set(), [f"review_surface.{field} must be a string list"]
    names: list[str] = []
    errors: list[str] = []
    for index, value in enumerate(raw, start=1):
        if not isinstance(value, str) or not value.strip():
            errors.append(
                f"review_surface.{field}[{index}] must be a nonempty string"
            )
            continue
        names.append(value.strip())
    duplicates = sorted({name for name in names if names.count(name) > 1})
    if duplicates:
        errors.append(
            f"review_surface.{field} contains duplicate names: "
            + ", ".join(duplicates)
        )
    return set(names), errors


@dataclass(frozen=True)
class ReviewSurfaceStructure:
    include_names: tuple[str, ...]
    source_condition_items: frozenset[str]
    assumption_names: frozenset[str]
    proof_boundary_names: frozenset[str]
    auxiliary_names: frozenset[str]
    quarantined_auxiliary_names: frozenset[str]
    declared_interface_names: frozenset[str]
    declared_assumption_names: frozenset[str]
    declared_proof_names: frozenset[str]
    errors: tuple[str, ...]

    @property
    def current(self) -> bool:
        return not self.errors

    def projection(self) -> Mapping[str, Any]:
        return MappingProxyType(
            {
                "schema": 1,
                "current": self.current,
                "include_names": list(self.include_names),
                "source_condition_items": sorted(self.source_condition_items),
                "assumption_names": sorted(self.assumption_names),
                "proof_boundary_names": sorted(self.proof_boundary_names),
                "auxiliary_names": sorted(self.auxiliary_names),
                "quarantined_auxiliary_names": sorted(
                    self.quarantined_auxiliary_names
                ),
                "declared_interface_names": sorted(self.declared_interface_names),
                "declared_assumption_names": sorted(self.declared_assumption_names),
                "declared_proof_names": sorted(self.declared_proof_names),
                "errors": list(self.errors),
            }
        )


def validate_review_surface_structure(
    status_payload: object,
    *,
    interface_text: str,
    assumption_text: str = "",
    proof_text: str | None = None,
    proof_source_module: str | None = None,
) -> ReviewSurfaceStructure:
    """Return all cheap status/declaration-surface inconsistencies at once.

    This is deliberately a non-accepting source preflight. It rejects broken
    routing coordinates before an evidence transaction starts; Lean Meta still
    owns the later exact-type, declaration-kind, dependency, and axiom checks.
    """

    errors: list[str] = []
    if not isinstance(status_payload, Mapping):
        review_surface: Mapping[str, Any] = {}
        errors.append("status.json is not an object")
    else:
        raw_surface = status_payload.get("review_surface")
        if not isinstance(raw_surface, Mapping):
            review_surface = {}
            errors.append("status.json has no review_surface object")
        else:
            review_surface = raw_surface

    include_names, include_errors = _configured_names(
        review_surface, "include_names", required=True
    )
    assumption_names, assumption_errors = _configured_names(
        review_surface, "assumption_names"
    )
    source_condition_items, source_condition_errors = _configured_names(
        review_surface, "source_condition_items"
    )
    proof_boundary_names, proof_errors = _configured_names(
        review_surface, "proof_boundary_names"
    )
    auxiliary_names, auxiliary_errors = _configured_names(
        review_surface, "auxiliary_names"
    )
    quarantined_names, quarantine_errors = _configured_names(
        review_surface, "quarantined_auxiliary_names"
    )
    errors.extend(
        include_errors
        + source_condition_errors
        + assumption_errors
        + proof_errors
        + auxiliary_errors
        + quarantine_errors
    )

    raw_proof_routes = review_surface.get("proposition_spec_proofs")
    proof_routes: dict[str, str] = {}
    if raw_proof_routes is None:
        pass
    elif not isinstance(raw_proof_routes, Mapping):
        errors.append(
            "review_surface.proposition_spec_proofs must be a string-to-string object"
        )
    else:
        for raw_specification, raw_proof in raw_proof_routes.items():
            if not isinstance(raw_specification, str) or not raw_specification.strip():
                errors.append(
                    "review_surface.proposition_spec_proofs has an empty specification name"
                )
                continue
            if not isinstance(raw_proof, str) or not raw_proof.strip():
                errors.append(
                    "review_surface.proposition_spec_proofs[{}] must be a nonempty string".format(
                        raw_specification
                    )
                )
                continue
            proof_routes[raw_specification.strip()] = raw_proof.strip()
    strict_proof_route_layout = (
        isinstance(status_payload, Mapping)
        and status_payload.get("intake_freeze_required") is True
    ) or isinstance(review_surface.get("proof_file"), str)

    if proof_boundary_names - assumption_names:
        errors.append(
            "review_surface.proof_boundary_names must also be assumption_names: "
            + ", ".join(sorted(proof_boundary_names - assumption_names))
        )
    if quarantined_names - auxiliary_names:
        errors.append(
            "review_surface.quarantined_auxiliary_names must also be auxiliary_names: "
            + ", ".join(sorted(quarantined_names - auxiliary_names))
        )
    overlap = auxiliary_names & (include_names | assumption_names)
    if overlap:
        errors.append(
            "review_surface.auxiliary_names overlap reviewed or assumption names: "
            + ", ".join(sorted(overlap))
        )
    quarantine_overlap = quarantined_names & (include_names | assumption_names)
    if quarantine_overlap:
        errors.append(
            "review_surface.quarantined_auxiliary_names overlap reviewed or assumption names: "
            + ", ".join(sorted(quarantine_overlap))
        )

    interface_rows = [name for _line, name in review_rows_from_interface_text(interface_text)]
    interface_blocks = review_declaration_blocks(interface_text)
    configured_support = assumption_names | auxiliary_names
    assumption_blocks = assumption_declarations_from_text(
        assumption_text, configured_support
    )
    missing_reviewed = reviewed_names_not_declared_in_review_source(
        sorted(include_names), interface_blocks
    )
    if missing_reviewed:
        errors.append(
            "review_surface.include_names are not declared in PaperInterface.lean: "
            + ", ".join(missing_reviewed)
        )
    missing_auxiliary = auxiliary_names_not_exported_from_review_source(
        auxiliary_names,
        interface_rows,
        set(assumption_blocks),
    )
    if missing_auxiliary:
        errors.append(
            "review_surface.auxiliary_names are absent from PaperInterface.lean and Assumptions.lean: "
            + ", ".join(missing_auxiliary)
        )
    declared_for_assumptions = set(interface_rows) | set(assumption_blocks)
    missing_assumptions = sorted(assumption_names - declared_for_assumptions)
    if missing_assumptions:
        errors.append(
            "review_surface.assumption_names are absent from PaperInterface.lean and Assumptions.lean: "
            + ", ".join(missing_assumptions)
        )

    proof_blocks = (
        review_declaration_blocks(proof_text) if proof_text is not None else {}
    )
    if proof_routes and strict_proof_route_layout:
        if proof_text is None:
            errors.append(
                "review_surface.proposition_spec_proofs has no readable proof endpoint source"
            )
        configured_proof_module = review_surface.get("proof_module")
        if configured_proof_module is not None and (
            not isinstance(configured_proof_module, str)
            or not configured_proof_module.strip()
        ):
            errors.append("review_surface.proof_module must be a nonempty string")
        elif (
            isinstance(configured_proof_module, str)
            and configured_proof_module.strip()
            and proof_source_module is not None
            and configured_proof_module.strip() != proof_source_module
        ):
            errors.append(
                "review_surface.proof_module does not match its proof source file: "
                f"configured {configured_proof_module.strip()}, file module {proof_source_module}"
            )

        for specification, proof in sorted(proof_routes.items()):
            specification_candidates = [
                declaration
                for name, declaration in interface_blocks.items()
                if name == specification
                or name.endswith("." + specification)
                or specification.endswith("." + name)
            ]
            if len(specification_candidates) != 1:
                errors.append(
                    "review_surface.proposition_spec_proofs specification is not a unique "
                    f"PaperInterface.lean declaration: {specification}"
                )
            elif specification_candidates[0][1] != "def":
                errors.append(
                    "review_surface.proposition_spec_proofs specification must be one "
                    f"transparent def, not {specification_candidates[0][1]}: {specification}"
                )

            proof_candidates = [
                declaration
                for name, declaration in proof_blocks.items()
                if name == proof
                or name.endswith("." + proof)
                or proof.endswith("." + name)
            ]
            if len(proof_candidates) != 1:
                errors.append(
                    "review_surface.proposition_spec_proofs endpoint is not a unique "
                    f"declaration in the configured proof source: {proof}"
                )
            elif proof_candidates[0][1] not in {"theorem", "lemma"}:
                errors.append(
                    "review_surface.proposition_spec_proofs endpoint must be a theorem "
                    f"or lemma, not {proof_candidates[0][1]}: {proof}"
                )

    return ReviewSurfaceStructure(
        include_names=tuple(sorted(include_names)),
        source_condition_items=frozenset(source_condition_items),
        assumption_names=frozenset(assumption_names),
        proof_boundary_names=frozenset(proof_boundary_names),
        auxiliary_names=frozenset(auxiliary_names),
        quarantined_auxiliary_names=frozenset(quarantined_names),
        declared_interface_names=frozenset(interface_blocks),
        declared_assumption_names=frozenset(assumption_blocks),
        declared_proof_names=frozenset(proof_blocks),
        errors=tuple(dict.fromkeys(errors)),
    )
