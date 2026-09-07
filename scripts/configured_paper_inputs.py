"""Resolve exact paper inputs selected by frozen status and source-map bytes.

This module performs no filesystem read, existence probe, glob, or directory
walk. It is shared by the current v11 evidence transaction and the historical
dashboard collector without importing dashboard rendering or semantic logic.
"""

from __future__ import annotations

import json
import os
import re
from collections.abc import Iterator, Mapping
from pathlib import Path
from typing import Any

from scripts.dashboard_audit_inputs import DashboardFrozenInputError

ROOT = Path(__file__).resolve().parents[1]
PAPER_AUDIT_DIR = "audit"

DASHBOARD_STATUS_FILE_FIELDS = frozenset(
    {
        "source_file",
        "human_source_file",
        "assumption_source_file",
        "ledger_file",
        "lean_to_tex_file",
        "match_judgment_file",
        "review_surface_audit_file",
        "paper_coverage_audit_file",
        "defect_support_judgment_file",
        "assumption_judgment_file",
        "source_record_audit_file",
        "source_record_judgment_file",
        "final_validation_report",
        "review_entrypoint",
    }
)
V11_EVIDENCE_STATUS_FILE_FIELDS = frozenset(
    {
        "source_file",
        "human_source_file",
        "assumption_source_file",
        "ledger_file",
        "assumption_judgment_file",
        "library_semantic_review_file",
        "v11_screening_file",
    }
)
V11_CANONICAL_TRANSACTION_SIDECARS = frozenset(
    {
        "LEAN_IMPORT_CLOSURE_RECEIPT.json",
        "library_semantic_review.json",
        "paper_semantic_prerequisites.json",
        "v11_raw_source_spec_screening.json",
    }
)
MAP_FILE_FIELDS = frozenset(
    {
        "path",
        "source_artifact_path",
        "source_text_file",
    }
)
SOURCE_PROOF_FIDELITY_SOURCE_LOCATOR_FIELDS = frozenset(
    {
        "source_locator",
        "affected_source_locators",
    }
)
_SOURCE_FILE_LINE_RE = re.compile(
    r"(?P<path>[A-Za-z0-9_./-]+\.(?:tex|txt|md|pdf)):"
    r"[1-9][0-9]*(?:-[1-9][0-9]*)?",
    re.I,
)


def _configured_paper_path(
    repository_root: Path,
    folder: Path,
    raw_path: object,
) -> Path | None:
    """Resolve one configured paper-local path without reading it."""

    if not isinstance(raw_path, str) or not raw_path.strip():
        return None
    relative = Path(raw_path.strip())
    if relative.is_absolute():
        raise DashboardFrozenInputError(
            f"dashboard input path must be repository- or paper-relative: {raw_path}"
        )
    anchor = repository_root if relative.parts[:1] == ("papers",) else folder
    try:
        resolved = Path(os.path.abspath(anchor / relative))
        resolved.relative_to(folder)
    except ValueError as exc:
        raise DashboardFrozenInputError(
            f"dashboard input path escapes paper folder: {raw_path}"
        ) from exc
    return resolved


def _mapping_file_values(
    value: object,
    *,
    field_names: frozenset[str],
) -> Iterator[object]:
    """Yield selected file-field values from a JSON-compatible object."""

    if isinstance(value, Mapping):
        for raw_key, item in value.items():
            if str(raw_key) in field_names:
                yield item
            yield from _mapping_file_values(item, field_names=field_names)
    elif isinstance(value, list):
        for item in value:
            yield from _mapping_file_values(item, field_names=field_names)


def _cited_source_registry_file_values(statement_map: Mapping[str, Any]) -> Iterator[object]:
    """Yield only the byte inputs named by the typed cited-source registry."""

    raw_descriptors = statement_map.get("cited_source_artifacts")
    if not isinstance(raw_descriptors, list):
        return
    for descriptor in raw_descriptors:
        if not isinstance(descriptor, Mapping):
            continue
        yield descriptor.get("path")
        yield descriptor.get("provenance_path")


def _companion_file_values(statement_map: Mapping[str, Any]) -> Iterator[object]:
    """Yield exact paths from the source-text companion schema."""

    companion = statement_map.get("source_text_companion")
    if not isinstance(companion, Mapping):
        return
    for field in (
        "canonical_text",
        "visual_primary_scan",
        "transcript_input_scan",
        "semantic_review_transcription",
    ):
        descriptor = companion.get(field)
        if isinstance(descriptor, Mapping):
            yield descriptor.get("path")


def _corrected_target_approval_file_values(
    statement_map: Mapping[str, Any],
) -> Iterator[object]:
    """Yield only approval artifacts that authorize corrected source targets."""

    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):
        return
    for raw_item in raw_items.values():
        if not isinstance(raw_item, Mapping):
            continue
        corrected_target = raw_item.get("corrected_target")
        approval = (
            corrected_target.get("approval")
            if isinstance(corrected_target, Mapping)
            else None
        )
        if isinstance(approval, Mapping):
            yield approval.get("artifact_path")


def _source_locator_file_values(value: object) -> Iterator[object]:
    """Yield paper-local files named by source-proof-fidelity anchors.

    The current evidence transaction freezes the ledger itself.  It must also
    freeze every text source explicitly cited by that frozen ledger; otherwise
    the integrity validator cannot read the ledger's own exact anchors without
    falling through to mutable filesystem bytes.  Only the structured locator
    fields are scanned, never explanatory prose.
    """

    def locator_strings(raw: object) -> Iterator[str]:
        if isinstance(raw, str):
            yield raw
        elif isinstance(raw, list):
            yield from (
                item for item in raw if isinstance(item, str)
            )

    if isinstance(value, Mapping):
        for raw_key, item in value.items():
            if str(raw_key) in SOURCE_PROOF_FIDELITY_SOURCE_LOCATOR_FIELDS:
                for locator in locator_strings(item):
                    for match in _SOURCE_FILE_LINE_RE.finditer(locator):
                        yield match.group("path")
            elif isinstance(item, (Mapping, list)):
                yield from _source_locator_file_values(item)
    elif isinstance(value, list):
        for item in value:
            if isinstance(item, (Mapping, list)):
                yield from _source_locator_file_values(item)


def _configured_input_payloads(
    folder: Path,
    *,
    status_bytes: bytes,
    statement_map_bytes: bytes | None,
    repository_root: Path,
) -> tuple[Path, Path, Mapping[str, Any], Mapping[str, Any]]:
    """Parse caller-owned bytes without consulting ambient paper files."""

    root = Path(os.path.abspath(repository_root))
    paper_folder = Path(os.path.abspath(folder))
    try:
        paper_folder.relative_to(root)
    except ValueError as exc:
        raise DashboardFrozenInputError(
            f"paper folder is outside dashboard repository root: {folder}"
        ) from exc
    try:
        status_payload = json.loads(status_bytes)
    except json.JSONDecodeError as exc:
        raise DashboardFrozenInputError(
            "strict dashboard status snapshot is invalid JSON"
        ) from exc
    if not isinstance(status_payload, Mapping):
        raise DashboardFrozenInputError(
            "strict dashboard status snapshot is not an object"
        )
    if statement_map_bytes is None:
        statement_map: Mapping[str, Any] = {}
    else:
        try:
            raw_map = json.loads(statement_map_bytes)
        except json.JSONDecodeError as exc:
            raise DashboardFrozenInputError(
                "strict dashboard statement-map snapshot is invalid JSON"
            ) from exc
        if not isinstance(raw_map, Mapping):
            raise DashboardFrozenInputError(
                "strict dashboard statement-map snapshot is not an object"
            )
        statement_map = raw_map
    return root, paper_folder, status_payload, statement_map


def _configured_paths_from_payloads(
    root: Path,
    paper_folder: Path,
    status_payload: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    *,
    status_file_fields: frozenset[str],
) -> set[Path]:
    """Resolve selected status/map paths from already parsed exact payloads."""

    raw_paths = list(
        _mapping_file_values(status_payload, field_names=status_file_fields)
    )
    raw_paths.extend(
        _mapping_file_values(statement_map, field_names=MAP_FILE_FIELDS)
    )
    raw_paths.extend(_cited_source_registry_file_values(statement_map))
    raw_paths.extend(_companion_file_values(statement_map))
    paths: set[Path] = set()
    for raw_path in raw_paths:
        resolved = _configured_paper_path(root, paper_folder, raw_path)
        if resolved is not None:
            paths.add(resolved)
    return paths


def configured_dashboard_audit_input_paths(
    folder: Path,
    *,
    status_bytes: bytes,
    statement_map_bytes: bytes | None,
    repository_root: Path = ROOT,
) -> tuple[Path, ...]:
    """Return artifacts explicitly named by exact dashboard status/map bytes."""

    root, paper_folder, status_payload, statement_map = _configured_input_payloads(
        folder,
        status_bytes=status_bytes,
        statement_map_bytes=statement_map_bytes,
        repository_root=repository_root,
    )
    return tuple(
        sorted(
            _configured_paths_from_payloads(
                root,
                paper_folder,
                status_payload,
                statement_map,
                status_file_fields=DASHBOARD_STATUS_FILE_FIELDS,
            )
        )
    )


def configured_v11_evidence_input_paths(
    folder: Path,
    *,
    status_bytes: bytes,
    statement_map_bytes: bytes | None,
    repository_root: Path = ROOT,
) -> tuple[Path, ...]:
    """Return only current semantic inputs selected by frozen v11 config."""

    root, paper_folder, status_payload, statement_map = _configured_input_payloads(
        folder,
        status_bytes=status_bytes,
        statement_map_bytes=statement_map_bytes,
        repository_root=repository_root,
    )
    paths = _configured_paths_from_payloads(
        root,
        paper_folder,
        status_payload,
        statement_map,
        status_file_fields=V11_EVIDENCE_STATUS_FILE_FIELDS,
    )
    if status_payload.get("intake_freeze_required") is True:
        paths.add(paper_folder / PAPER_AUDIT_DIR / "intake_freeze.json")
    if status_payload.get("source_inventory_review_required") is True:
        paths.add(
            paper_folder
            / PAPER_AUDIT_DIR
            / "v11_source_map_preparation_config.json"
        )
    return tuple(sorted(paths))


def configured_source_proof_fidelity_anchor_input_paths(
    folder: Path,
    *,
    source_proof_fidelity_bytes: bytes | None,
    repository_root: Path = ROOT,
) -> tuple[Path, ...]:
    """Return every source artifact required by one frozen proof-fidelity ledger.

    This includes the ledger's byte-pinned canonical artifact as well as every
    text source named by a structured locator.  The current evidence
    transaction validates that canonical artifact's digest, so omitting it
    would make a correctly configured archive-backed ledger fail solely
    because its bytes were not frozen.  An invalid or absent ledger remains a
    frozen selected input and is rejected by the ordinary integrity validator.
    This selector deliberately adds no ambient read or fallback path in that
    case.
    """

    if source_proof_fidelity_bytes is None:
        return ()
    try:
        payload = json.loads(source_proof_fidelity_bytes)
    except (TypeError, UnicodeDecodeError, json.JSONDecodeError):
        return ()
    if not isinstance(payload, Mapping):
        return ()
    root = Path(os.path.abspath(repository_root))
    paper_folder = Path(os.path.abspath(folder))
    paths: set[Path] = set()
    canonical_artifact = _configured_paper_path(
        root,
        paper_folder,
        payload.get("source_artifact_path"),
    )
    if canonical_artifact is not None:
        paths.add(canonical_artifact)
    for raw_path in _source_locator_file_values(payload):
        resolved = _configured_paper_path(root, paper_folder, raw_path)
        if resolved is not None:
            paths.add(resolved)
    return tuple(sorted(paths))


def configured_assumption_review_rows_from_status(
    status_payload: object,
) -> set[str] | None:
    """Return the explicitly active assumption rows from frozen status JSON."""

    if not isinstance(status_payload, Mapping):
        return None
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, Mapping):
        return None
    raw_rows = review_surface.get("assumption_names")
    if not isinstance(raw_rows, list) or any(
        not isinstance(row, str) or not row.strip() for row in raw_rows
    ):
        return None
    return {row.strip() for row in raw_rows}


def configured_source_proof_fidelity_ledger_path(
    folder: Path,
    status_payload: object,
    *,
    repository_root: Path = ROOT,
) -> tuple[Path | None, str]:
    """Resolve the current proof-fidelity ledger without a filesystem probe."""

    if not isinstance(status_payload, Mapping):
        return None, ""
    review_surface = status_payload.get("review_surface")
    config = (
        review_surface.get("source_proof_fidelity_review")
        if isinstance(review_surface, Mapping)
        else None
    )
    if config is None:
        return None, ""
    if not isinstance(config, Mapping):
        return None, ""
    raw_path = config.get("ledger_file")
    if not isinstance(raw_path, str) or not raw_path.strip():
        return None, "source_proof_fidelity_review.ledger_file is missing"
    relative = Path(raw_path.strip())
    if relative.is_absolute():
        return None, "source_proof_fidelity_review.ledger_file must be relative"
    root = Path(os.path.abspath(repository_root))
    paper_folder = Path(os.path.abspath(folder))
    anchor = root if relative.parts[:1] == ("papers",) else paper_folder
    try:
        candidate = Path(os.path.abspath(anchor / relative))
        candidate.relative_to(paper_folder)
    except ValueError:
        return None, "source_proof_fidelity_review.ledger_file escapes the paper folder"
    return candidate, ""


def current_v11_canonical_transaction_input_paths(
    folder: Path,
    *,
    repository_root: Path = ROOT,
) -> tuple[Path, ...]:
    """Return fail-closed canonical inputs without parsing configuration.

    The assumption ledger is included here because only a valid frozen status
    payload can prove that its active row set is empty.  The complete selector
    below removes it in exactly that case.
    """

    root = Path(os.path.abspath(repository_root))
    paper_folder = Path(os.path.abspath(folder))
    try:
        paper_folder.relative_to(root / "papers")
    except ValueError as exc:
        raise DashboardFrozenInputError(
            f"paper folder is outside repository papers root: {folder}"
        ) from exc
    audit = paper_folder / PAPER_AUDIT_DIR
    paths = {audit / name for name in V11_CANONICAL_TRANSACTION_SIDECARS}
    paths.update(
        {
            audit / "assumption_match_llm.json",
            audit / "paper_statement_map.json",
            paper_folder / "Assumptions.lean",
            paper_folder / "status.json",
            root / "lakefile.toml",
            root / "papers" / "audit_config.json",
            root / "scripts" / "refresh_validation_report_audit_summaries.py",
        }
    )
    return tuple(sorted(paths))


def current_v11_transaction_input_paths(
    folder: Path,
    *,
    status_bytes: bytes,
    statement_map_bytes: bytes | None,
    source_proof_fidelity_bytes: bytes | None = None,
    repository_root: Path = ROOT,
) -> tuple[Path, ...]:
    """Return the complete exact-file set for one current-v11 transaction.

    This function parses only caller-owned frozen JSON bytes and performs no
    existence probe, glob, directory walk, or semantic validation.  The
    transaction snapshots every returned path, including absent canonical
    files, so creation or replacement during a run remains a mutation.
    """

    root, paper_folder, status_payload, statement_map = _configured_input_payloads(
        folder,
        status_bytes=status_bytes,
        statement_map_bytes=statement_map_bytes,
        repository_root=repository_root,
    )
    paths = _configured_paths_from_payloads(
        root,
        paper_folder,
        status_payload,
        statement_map,
        status_file_fields=V11_EVIDENCE_STATUS_FILE_FIELDS,
    )
    for raw_path in _corrected_target_approval_file_values(statement_map):
        resolved = _configured_paper_path(root, paper_folder, raw_path)
        if resolved is not None:
            paths.add(resolved)
    paths.update(
        configured_source_proof_fidelity_anchor_input_paths(
            paper_folder,
            source_proof_fidelity_bytes=source_proof_fidelity_bytes,
            repository_root=root,
        )
    )

    audit = paper_folder / PAPER_AUDIT_DIR
    paths.update(
        current_v11_canonical_transaction_input_paths(
            paper_folder,
            repository_root=root,
        )
    )
    assumption_rows = configured_assumption_review_rows_from_status(status_payload)
    if assumption_rows == set():
        paths.discard(audit / "assumption_match_llm.json")
    if status_payload.get("intake_freeze_required") is True:
        paths.add(audit / "intake_freeze.json")
    if status_payload.get("source_inventory_review_required") is True:
        paths.add(audit / "v11_source_map_preparation_config.json")
    return tuple(sorted(paths))
