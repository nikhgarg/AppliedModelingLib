#!/usr/bin/env python3
"""Fail-closed aggregate receipt reprojection for legacy v10 source audits.

Some early v10 source-record audits completed the expensive source/Lean work
before the raw-receipt and schema-5 item-reuse contracts existed.  Re-running
that entire audit merely to add transport receipts is wasteful, but treating
the old scalar item digests as current would be unsound.  This helper provides
the narrow middle path:

* it accepts only a successful pre-schema5 v10 raw audit whose current source
  map, selected review routes, source bytes, source context, and proof-fidelity
  context can be checked without another broad Lean source-record scan;
* the current source-map-selected review surface must be a deletion-only
  subset of rows already checked by the old isolated Lean run;
* it rebinds a complete aggregate raw receipt and current input fingerprint,
  while marking every generated item aggregate-only; and
* it never rebinds a judgment sidecar or infers a semantic match from a row,
  binder, declaration suffix, or function name.

The follow-up focused signature manifest is intentionally separate.  It asks
Lean for exact current elaborated signatures only for the retained selected
routes.  Until that pass exists, this artifact can preserve aggregate raw
coverage but cannot provide schema-5 item-level reuse or a formalization
closeout claim.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import os
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in tests.
    from scripts.formalization_protocol import CURRENT_SOURCE_RECORD_PROMPT_VERSION
    from scripts.audit_evidence_integrity import source_record_raw_scan_completeness_error
    from scripts.source_coverage_scope import (
        DEFAULT_SOURCE_COVERAGE_MODE,
        filter_source_map_items_for_coverage,
        source_coverage_mode_from_map,
        source_item_coverage_sha256,
        source_named_result_environment_kinds_from_map,
    )
    from scripts.source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from scripts.source_record_integrity import (
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        attach_source_record_audit_surface,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_raw_reusable_item_metadata_error,
        source_record_target_route_error,
        stamp_source_record_audit_integrity,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    from formalization_protocol import CURRENT_SOURCE_RECORD_PROMPT_VERSION
    from audit_evidence_integrity import source_record_raw_scan_completeness_error
    from source_coverage_scope import (
        DEFAULT_SOURCE_COVERAGE_MODE,
        filter_source_map_items_for_coverage,
        source_coverage_mode_from_map,
        source_item_coverage_sha256,
        source_named_result_environment_kinds_from_map,
    )
    from source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from source_record_integrity import (
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        attach_source_record_audit_surface,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_raw_reusable_item_metadata_error,
        source_record_target_route_error,
        stamp_source_record_audit_integrity,
    )


SOURCE_RECORD_V10_PROMPT_VERSION = CURRENT_SOURCE_RECORD_PROMPT_VERSION
SOURCE_RECORD_AGGREGATE_REPROJECTION_SCHEMA = 1
SOURCE_RECORD_AGGREGATE_REPROJECTION_POLICY_VERSION = (
    "source-record-v10-pre-schema5-aggregate-receipt-reprojection-v1"
)
SOURCE_RECORD_AGGREGATE_REPROJECTION_FIELD = "source_record_receipt_reprojection"
SOURCE_RECORD_AGGREGATE_REPROJECTION_ARTIFACT_KIND = (
    "source_record_v10_aggregate_only_receipt_reprojection"
)
SOURCE_RECORD_AGGREGATE_REPROJECTION_ITEM_BLOCKER = (
    "pre-schema5 raw evidence lacks persisted current elaborated review-route "
    "signatures; a focused Lean signature-manifest revalidation is required "
    "before any item-level reuse"
)
FOCUSED_SIGNATURE_MANIFEST_SCHEMA = 1
FOCUSED_SIGNATURE_MANIFEST_POLICY_VERSION = (
    "source-record-v10-focused-current-signature-manifest-v1"
)
FOCUSED_SIGNATURE_MANIFEST_ARTIFACT_KIND = (
    "source_record_focused_signature_manifest"
)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_EXACT_DEFAULT_MODE_ENTRY = (
    b'  "source_coverage_mode": "named_theoretical_statements",\n'
)


class SourceRecordReceiptReprojectionError(ValueError):
    """Raised when a legacy raw audit cannot safely be reprojected."""


def _canonical_digest(payload: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(payload), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _valid_sha256(value: object) -> str:
    digest = str(value or "").strip().lower()
    return digest if SHA256_RE.fullmatch(digest) else ""


def _repository_relative_path(root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordReceiptReprojectionError(
            f"evidence path must remain inside the repository: {path}"
        ) from exc


def _repository_path(root: Path, value: object) -> Path:
    text = str(value or "").strip()
    pure = PurePosixPath(text)
    if not text or pure.is_absolute() or any(part in {"", ".", ".."} for part in pure.parts):
        raise SourceRecordReceiptReprojectionError(
            "serialized evidence path is not a normalized repository-relative path"
        )
    candidate = (root / Path(*pure.parts)).resolve()
    try:
        normalized = candidate.relative_to(root.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordReceiptReprojectionError(
            "serialized evidence path escapes the repository"
        ) from exc
    if normalized != text:
        raise SourceRecordReceiptReprojectionError(
            "serialized evidence path is not canonical"
        )
    return candidate


def _load_json_object(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
        decoded = json.loads(contents)
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordReceiptReprojectionError(
            f"could not read JSON object at {path}: {exc}"
        ) from exc
    if not isinstance(decoded, dict):
        raise SourceRecordReceiptReprojectionError(f"{path} is not a JSON object")
    return decoded, contents


def _atomic_write(path: Path, contents: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent, prefix=f".{path.name}.", delete=False
    ) as handle:
        handle.write(contents)
        temporary = Path(handle.name)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def _load_source_record_audit_module(root: Path) -> Any:
    """Load the source-audit helpers without starting a source-record scan."""

    helper_path = root / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
    if not helper_path.is_file():
        raise SourceRecordReceiptReprojectionError(
            f"missing source-record audit helper at {helper_path}"
        )
    module_name = "_source_record_audit_for_receipt_reprojection"
    existing = sys.modules.get(module_name)
    if existing is not None:
        return existing
    spec = importlib.util.spec_from_file_location(module_name, helper_path)
    if spec is None or spec.loader is None:
        raise SourceRecordReceiptReprojectionError(
            f"could not load source-record audit helper at {helper_path}"
        )
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


@dataclass(frozen=True)
class CurrentReviewRoute:
    """A current selected route, including its exact source-byte identity."""

    row: str
    qualified_declaration: str
    source_file: str
    source_sha256: str

    def as_raw_row(self) -> dict[str, str]:
        return {
            "row": self.row,
            "qualified_declaration": self.qualified_declaration,
            "source_file": self.source_file,
            "source_sha256": self.source_sha256,
        }


@dataclass(frozen=True)
class CurrentReprojectionContext:
    """Pure current inputs used by the deletion-only receipt transformation."""

    paper: str
    paper_dir: Path
    import_module: str
    paper_statement_map_sha256: str
    input_fingerprint: dict[str, Any]
    review_interface_source: dict[str, Any]
    review_assumption_source: dict[str, Any] | None
    configured_review_row_count: int
    selected_routes: tuple[CurrentReviewRoute, ...]
    source_coverage: dict[str, Any]
    semantic_selection: dict[str, Any]
    semantic_model_dimensions: tuple[str, ...]
    semantic_model_configuration_errors: tuple[str, ...]
    semantic_context_requirements: tuple[dict[str, Any], ...]
    source_proof_fidelity: dict[str, Any] | None
    formalization_scope: dict[str, Any] | None
    unconfigured_review_surface_rows: tuple[str, ...]
    unconfigured_assumption_support_rows: tuple[str, ...]
    quarantined_auxiliary_review_rows: tuple[str, ...]


@dataclass(frozen=True)
class ExactDefaultCoverageModeMapDelta:
    """One byte-exact legacy map delta that preserves the effective scope.

    This is intentionally narrower than a semantic-map cache projection. The
    prior map is reconstructed by deleting one exact top-level JSON line from
    the current bytes, and that reconstruction must hash to the historical raw
    receipt's full map SHA. No item field, including administrative metadata,
    can differ under this transport.
    """

    prior_paper_statement_map_sha256: str
    current_paper_statement_map_sha256: str
    prior_effective_source_coverage_mode: str
    current_effective_source_coverage_mode: str
    selected_semantic_projection_sha256: str
    selected_semantic_item_count: int

    def as_provenance(self) -> dict[str, Any]:
        return {
            "schema": 1,
            "kind": "exact_top_level_default_source_coverage_mode_omission",
            "deleted_current_json_entry": (
                '"source_coverage_mode": "named_theoretical_statements"'
            ),
            "prior_paper_statement_map_sha256": self.prior_paper_statement_map_sha256,
            "current_paper_statement_map_sha256": self.current_paper_statement_map_sha256,
            "prior_effective_source_coverage_mode": (
                self.prior_effective_source_coverage_mode
            ),
            "current_effective_source_coverage_mode": (
                self.current_effective_source_coverage_mode
            ),
            "selected_semantic_projection_sha256": (
                self.selected_semantic_projection_sha256
            ),
            "selected_semantic_item_count": self.selected_semantic_item_count,
        }


def _effective_source_coverage_projection(
    statement_map: Mapping[str, Any],
) -> tuple[str, dict[str, Any]]:
    """Return the source-semantic ordinary/deep selection without map keys.

    The comparison is source-first. It derives scope from the source
    presentation policy, then compares selected source statements through the
    established semantic digests. Lean declarations, map keys, and locations
    do not establish equality here; exact current source-byte route checks are
    separate reprojection preconditions.
    """

    mode, mode_error = source_coverage_mode_from_map(statement_map)
    if mode_error:
        raise SourceRecordReceiptReprojectionError(
            "statement-map coverage mode is invalid: " + mode_error
        )
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise SourceRecordReceiptReprojectionError(
            "statement-map has no object `items` field for effective scope comparison"
        )
    selected_items = filter_source_map_items_for_coverage(
        dict(raw_items),
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            statement_map
        ),
    )
    semantic_digests = sorted(
        source_item_coverage_sha256(item, mode) for item in selected_items.values()
    )
    if not semantic_digests or any(not _valid_sha256(value) for value in semantic_digests):
        raise SourceRecordReceiptReprojectionError(
            "statement-map effective scope has an invalid selected source semantic item"
        )
    projection = {
        "source_coverage_mode": mode,
        "selected_source_item_semantic_sha256s": semantic_digests,
    }
    return mode, projection


def _exact_default_coverage_mode_map_delta(
    prior_raw_audit: Mapping[str, Any], context: CurrentReprojectionContext
) -> ExactDefaultCoverageModeMapDelta | None:
    """Authenticate the sole permitted legacy statement-map byte mismatch.

    A pre-v7 raw receipt may have been generated when the ordinary source
    coverage default was implicit. This admits only the literal migration from
    that exact omission to the exact required top-level spelling. The
    reconstructed prior bytes must match the raw receipt's full SHA, so this
    cannot waive a source-status edit or any other map drift.
    """

    prior_sha256 = _valid_sha256(prior_raw_audit.get("paper_statement_map_sha256"))
    if not prior_sha256:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit lacks a valid statement-map SHA-256"
        )
    if prior_sha256 == context.paper_statement_map_sha256.lower():
        return None

    map_path = context.paper_dir / "audit" / "paper_statement_map.json"
    try:
        current_bytes = map_path.read_bytes()
        current_map = json.loads(current_bytes)
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordReceiptReprojectionError(
            "could not read current statement map for exact default-mode transport: "
            + str(exc)
        ) from exc
    if not isinstance(current_map, dict):
        raise SourceRecordReceiptReprojectionError(
            "current statement map is not a JSON object for exact default-mode transport"
        )
    current_sha256 = _sha256_bytes(current_bytes)
    if current_sha256 != context.paper_statement_map_sha256.lower():
        raise SourceRecordReceiptReprojectionError(
            "current statement-map bytes changed while resolving exact default-mode transport"
        )
    if current_map.get("source_coverage_mode") != DEFAULT_SOURCE_COVERAGE_MODE:
        raise SourceRecordReceiptReprojectionError(
            "statement-map byte mismatch is not the exact default coverage-mode entry"
        )
    if current_bytes.count(_EXACT_DEFAULT_MODE_ENTRY) != 1:
        raise SourceRecordReceiptReprojectionError(
            "statement-map byte mismatch lacks one exact top-level default coverage-mode entry"
        )
    prior_bytes = current_bytes.replace(_EXACT_DEFAULT_MODE_ENTRY, b"", 1)
    if _sha256_bytes(prior_bytes) != prior_sha256:
        raise SourceRecordReceiptReprojectionError(
            "deleting the exact default coverage-mode entry does not reproduce the prior statement-map bytes"
        )
    try:
        prior_map = json.loads(prior_bytes)
    except json.JSONDecodeError as exc:  # pragma: no cover - guarded by exact line form.
        raise SourceRecordReceiptReprojectionError(
            "deleting the exact default coverage-mode entry does not leave valid JSON"
        ) from exc
    if not isinstance(prior_map, dict) or "source_coverage_mode" in prior_map:
        raise SourceRecordReceiptReprojectionError(
            "the exact default coverage-mode deletion did not reconstruct an omitted top-level field"
        )

    prior_mode, prior_projection = _effective_source_coverage_projection(prior_map)
    current_mode, current_projection = _effective_source_coverage_projection(current_map)
    if prior_mode != current_mode:
        raise SourceRecordReceiptReprojectionError(
            "exact default coverage-mode transport changes the effective coverage mode"
        )
    if prior_projection != current_projection:
        raise SourceRecordReceiptReprojectionError(
            "exact default coverage-mode transport changes the selected source semantic projection"
        )
    return ExactDefaultCoverageModeMapDelta(
        prior_paper_statement_map_sha256=prior_sha256,
        current_paper_statement_map_sha256=current_sha256,
        prior_effective_source_coverage_mode=prior_mode,
        current_effective_source_coverage_mode=current_mode,
        selected_semantic_projection_sha256=_canonical_digest(prior_projection),
        selected_semantic_item_count=len(
            prior_projection["selected_source_item_semantic_sha256s"]
        ),
    )


def _resolve_current_review_context(
    *, root: Path, paper: str, max_depth: int
) -> CurrentReprojectionContext:
    """Compute current non-Lean selection and source identities.

    This uses the same exact source-map route selection as the source-record
    generator, but deliberately does not call its Lean signature or recursive
    scan paths.  A missing/ambiguous configuration is a hard failure rather
    than an opportunity to select a similarly named declaration.
    """

    module = _load_source_record_audit_module(root)
    paper_dir = root / "papers" / paper
    status_path = paper_dir / "status.json"
    map_path = paper_dir / "audit" / "paper_statement_map.json"
    if not paper_dir.is_dir() or not status_path.is_file() or not map_path.is_file():
        raise SourceRecordReceiptReprojectionError(
            f"paper {paper!r} lacks its status or statement-map artifact"
        )
    map_sha256 = _sha256_bytes(map_path.read_bytes())
    arguments = argparse.Namespace(paper=paper, max_depth=max_depth, no_lean=False)
    fingerprint = module.source_record_input_fingerprint(
        arguments,
        root,
        paper_dir,
        paper_statement_map_sha256=map_sha256,
    )
    if not isinstance(fingerprint, dict):
        raise SourceRecordReceiptReprojectionError(
            "could not compute the current source-record input fingerprint"
        )
    interface_path = module.review_source_path(root, paper_dir, status_path)
    interface_declarations = module.parse_declarations(interface_path)
    interface_namespace = module.first_declaration_namespace(interface_path)
    assumptions_path = paper_dir / "Assumptions.lean"
    assumption_declarations: dict[str, str] = {}
    assumption_namespace = ""
    if assumptions_path.is_file():
        assumption_declarations = module.parse_declarations(assumptions_path)
        assumption_namespace = module.first_declaration_namespace(assumptions_path)

    configured_rows = module.parse_status_rows(status_path)
    if len(set(configured_rows)) != len(configured_rows):
        raise SourceRecordReceiptReprojectionError(
            "current review-surface configuration contains duplicate rows"
        )
    qualified_by_row: dict[str, str] = {}
    source_by_row: dict[str, Path] = {}
    missing_rows: list[str] = []
    for row in configured_rows:
        interface_match = module.resolve_declaration_reference(
            row, interface_declarations, preferred_namespace=interface_namespace
        )
        assumption_match = module.resolve_declaration_reference(
            row, assumption_declarations, preferred_namespace=assumption_namespace
        )
        matches = [match for match in (interface_match, assumption_match) if match]
        if len(set(matches)) > 1:
            raise SourceRecordReceiptReprojectionError(
                f"current configured review route {row!r} is ambiguous across sources"
            )
        if not matches:
            missing_rows.append(row)
            continue
        qualified_by_row[row] = matches[0]
        source_by_row[row] = (
            assumptions_path if matches[0] in assumption_declarations else interface_path
        )
    if missing_rows:
        raise SourceRecordReceiptReprojectionError(
            "current configured review route(s) are missing: "
            + ", ".join(sorted(missing_rows))
        )

    configured_present = list(configured_rows)
    source_selected_rows, _selected_map, source_coverage = module.source_coverage_review_rows(
        paper_dir, configured_present, qualified_by_row
    )
    configured_assumption_rows = [
        row
        for row in configured_present
        if row
        in set(
            module.parse_status_review_surface_names(status_path, ("assumption_names",))
        )
    ]
    scope_targets, scope_errors = (
        module.formalization_scope_target_declarations_for_semantic_review(status_path)
    )
    explicit_source_targets, explicit_source_target_config_errors = (
        module.explicit_source_target_declarations_for_semantic_review(status_path)
    )
    explicit_source_target_rows, explicit_source_target_selection = (
        module.explicit_source_target_review_rows(
            paper_dir,
            configured_present,
            qualified_by_row,
            explicit_source_targets,
        )
    )
    selected_rows, semantic_selection = module.effective_source_record_review_rows(
        source_selected_rows=source_selected_rows,
        configured_present=configured_present,
        qualified_row_refs=qualified_by_row,
        configured_assumption_rows=configured_assumption_rows,
        formalization_scope_targets=scope_targets,
        explicit_source_target_rows=explicit_source_target_rows,
    )
    semantic_selection.update(explicit_source_target_selection)
    explicit_target_route_errors = list(
        semantic_selection.get("semantic_model_explicit_source_target_route_errors")
        or []
    ) + list(
        semantic_selection.get(
            "semantic_model_explicit_source_target_effective_row_errors"
        )
        or []
    )
    semantic_selection["semantic_model_target_route_errors"] = sorted(
        {
            str(error).strip()
            for error in (
                list(
                    semantic_selection.get(
                        "semantic_model_scope_target_route_errors"
                    )
                    or []
                )
                + explicit_target_route_errors
            )
            if str(error).strip()
        }
    )
    route_errors = [
        str(error).strip()
        for error in (
            list(source_coverage.get("source_coverage_route_errors") or [])
            + list(semantic_selection.get("semantic_model_target_route_errors") or [])
            + list(scope_errors)
            + list(explicit_source_target_config_errors)
        )
        if str(error).strip()
    ]
    if str(source_coverage.get("source_coverage_mode_error") or "").strip() or route_errors:
        raise SourceRecordReceiptReprojectionError(
            "current source-map selection is invalid: "
            + "; ".join(
                [
                    str(source_coverage.get("source_coverage_mode_error") or "").strip()
                ]
                + route_errors
            )
        )
    if source_coverage.get("source_coverage_unrouted_source_items"):
        raise SourceRecordReceiptReprojectionError(
            "current source-map selection has unrouted source item(s): "
            + ", ".join(
                str(value)
                for value in source_coverage["source_coverage_unrouted_source_items"]
            )
        )

    source_identities = {
        interface_path.resolve(): module.source_artifact_identity(root, interface_path),
    }
    if assumptions_path.is_file():
        source_identities[assumptions_path.resolve()] = module.source_artifact_identity(
            root, assumptions_path
        )
    selected_routes: list[CurrentReviewRoute] = []
    for row in selected_rows:
        source_identity = source_identities[source_by_row[row].resolve()]
        selected_routes.append(
            CurrentReviewRoute(
                row=row,
                qualified_declaration=qualified_by_row[row],
                source_file=str(source_identity["path"]),
                source_sha256=str(source_identity["sha256"]),
            )
        )
    if not selected_routes:
        raise SourceRecordReceiptReprojectionError(
            "current source-map policy selected no review routes"
        )

    semantic_dimensions, semantic_configuration_errors = module.semantic_model_review_config(
        status_path
    )
    if semantic_configuration_errors:
        raise SourceRecordReceiptReprojectionError(
            "current semantic-model review configuration is invalid: "
            + "; ".join(semantic_configuration_errors)
        )
    semantic_context, semantic_context_errors = module.source_map_semantic_context_requirements(
        paper_dir
    )
    if semantic_context_errors:
        raise SourceRecordReceiptReprojectionError(
            "current source-map semantic context is invalid: "
            + "; ".join(semantic_context_errors)
        )
    source_artifacts = fingerprint.get("source_artifact_identities")
    if not isinstance(source_artifacts, list) or not source_artifacts:
        raise SourceRecordReceiptReprojectionError(
            "current source-record fingerprint has no source-artifact identities"
        )
    for identity in source_artifacts:
        if not isinstance(identity, Mapping) or identity.get("status") != "present":
            raise SourceRecordReceiptReprojectionError(
                "current source-record fingerprint has an unavailable source artifact"
            )
        if not _valid_sha256(identity.get("sha256")):
            raise SourceRecordReceiptReprojectionError(
                "current source-record fingerprint has an unpinned source artifact"
            )

    auxiliary_rows = module.parse_status_auxiliary_rows(status_path)
    quarantined_rows = module.parse_status_quarantined_auxiliary_rows(status_path)

    def resolve_auxiliary(rows: list[str]) -> set[str]:
        resolved: set[str] = set()
        for row in rows:
            interface_match = module.resolve_declaration_reference(
                row, interface_declarations, preferred_namespace=interface_namespace
            )
            assumption_match = module.resolve_declaration_reference(
                row,
                assumption_declarations,
                preferred_namespace=assumption_namespace,
            )
            resolved.update(value for value in (interface_match, assumption_match) if value)
        return resolved

    selected_qualified = set(qualified_by_row.values())
    auxiliary_qualified = resolve_auxiliary(auxiliary_rows)
    quarantined_qualified = resolve_auxiliary(quarantined_rows)
    unconfigured_interface = module.unconfigured_review_declarations(
        interface_declarations,
        selected_names=selected_qualified & set(interface_declarations),
        auxiliary_names=auxiliary_qualified & set(interface_declarations),
        quarantined_auxiliary_names=quarantined_qualified & set(interface_declarations),
    )
    unconfigured_assumptions = module.unconfigured_review_declarations(
        assumption_declarations,
        selected_names=selected_qualified & set(assumption_declarations),
        auxiliary_names=auxiliary_qualified & set(assumption_declarations),
        quarantined_auxiliary_names=quarantined_qualified & set(assumption_declarations),
    )
    return CurrentReprojectionContext(
        paper=paper,
        paper_dir=paper_dir,
        import_module=module.lean_module_name(root, interface_path),
        paper_statement_map_sha256=map_sha256,
        input_fingerprint=dict(fingerprint),
        review_interface_source=dict(fingerprint["review_interface_source"]),
        review_assumption_source=(
            dict(fingerprint["review_assumption_source"])
            if isinstance(fingerprint.get("review_assumption_source"), Mapping)
            else None
        ),
        configured_review_row_count=len(configured_rows),
        selected_routes=tuple(selected_routes),
        source_coverage=dict(source_coverage),
        semantic_selection=dict(semantic_selection),
        semantic_model_dimensions=tuple(semantic_dimensions),
        semantic_model_configuration_errors=tuple(semantic_configuration_errors),
        semantic_context_requirements=tuple(
            dict(value) for value in semantic_context if isinstance(value, Mapping)
        ),
        source_proof_fidelity=module.source_proof_fidelity_context(paper_dir),
        formalization_scope=module.formalization_scope_context(paper_dir),
        unconfigured_review_surface_rows=tuple(unconfigured_interface),
        unconfigured_assumption_support_rows=tuple(unconfigured_assumptions),
        quarantined_auxiliary_review_rows=tuple(sorted(quarantined_qualified)),
    )


def _require_clean_prior_raw(
    raw: Mapping[str, Any], context: CurrentReprojectionContext
) -> ExactDefaultCoverageModeMapDelta | None:
    """Check the legacy evidence state before it receives a new receipt."""

    if raw.get("paper") != context.paper:
        raise SourceRecordReceiptReprojectionError("prior raw audit belongs to another paper")
    for field in ("prompt_version", "source_record_policy_version"):
        if raw.get(field) != SOURCE_RECORD_V10_PROMPT_VERSION:
            raise SourceRecordReceiptReprojectionError(
                f"prior raw audit does not use the current v10 {field}"
            )
    if raw.get("source_record_audit_surface_schema") is not None or raw.get(
        "source_record_audit_integrity_schema"
    ) is not None:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit already has a current receipt; receipt reprojection is not applicable"
        )
    if raw.get("source_record_input_fingerprint") is not None:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit already has an input fingerprint; refusing to overwrite provenance"
        )
    if not _valid_sha256(raw.get("source_record_audit_sha256")):
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit lacks a valid legacy aggregate digest"
        )
    map_delta = _exact_default_coverage_mode_map_delta(raw, context)
    if raw.get("review_interface_source") != context.review_interface_source:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit review-interface source bytes are not current"
        )
    if raw.get("review_assumption_source") != context.review_assumption_source:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit review-assumption source identity is not current"
        )
    if raw.get("source_proof_fidelity") != context.source_proof_fidelity:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit source-proof fidelity context is not current"
        )
    if raw.get("formalization_scope") != context.formalization_scope:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit governing formalization scope is not current"
        )
    if list(raw.get("semantic_context_requirements") or []) != list(
        context.semantic_context_requirements
    ):
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit source semantic context is not current"
        )
    expected_context_digest = (
        _canonical_digest(list(context.semantic_context_requirements))
        if context.semantic_context_requirements
        else ""
    )
    if raw.get("semantic_context_requirements_sha256") != expected_context_digest:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit source semantic-context digest is not current"
        )
    for field in (
        "missing_configured_review_rows",
        "recursion_failures",
        "source_contract_association_errors",
        "semantic_model_review_configuration_errors",
    ):
        value = raw.get(field)
        if value not in ([], None):
            raise SourceRecordReceiptReprojectionError(
                f"prior raw audit has unresolved generated {field}"
            )
    target_route_error = source_record_target_route_error(raw)
    if target_route_error:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit has unresolved semantic target routing: "
            + target_route_error
        )
    for field in (
        "constructor_result_type_check_error",
        "source_premise_consistency_error",
    ):
        if str(raw.get(field) or "").strip():
            raise SourceRecordReceiptReprojectionError(
                f"prior raw audit has unresolved generated {field}"
            )
    if raw.get("source_premise_consistency_schema") != 1:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit has no supported source-premise consistency scan"
        )
    premise_items = raw.get("source_premise_consistency_items")
    if not isinstance(premise_items, list) or raw.get(
        "source_premise_consistency_item_count"
    ) != len(premise_items):
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit source-premise consistency receipt is incomplete"
        )
    if raw.get("recursion_failure_count") != len(raw.get("recursion_failures") or []):
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit recursion-failure count is inconsistent"
        )
    if raw.get("current_source_record_judgment_count") not in (0, None):
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit has current judgments; judgment rebinding is forbidden here"
        )

    configured = raw.get("configured_review_rows")
    if not isinstance(configured, list) or not configured:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit has no configured review-row evidence"
        )
    if raw.get("configured_review_rows_count") != len(configured):
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit configured review-row count is inconsistent"
        )
    configured_rows: set[str] = set()
    configured_pairs: set[tuple[str, str]] = set()
    for item in configured:
        if not isinstance(item, Mapping):
            raise SourceRecordReceiptReprojectionError(
                "prior raw audit has malformed configured review-row evidence"
            )
        row = str(item.get("row") or "").strip()
        qualified = str(item.get("qualified_declaration") or "").strip()
        if not row or not qualified or row in configured_rows or (row, qualified) in configured_pairs:
            raise SourceRecordReceiptReprojectionError(
                "prior raw audit configured review-row evidence is ambiguous"
            )
        configured_rows.add(row)
        configured_pairs.add((row, qualified))
    selected_pairs = {
        (route.row, route.qualified_declaration) for route in context.selected_routes
    }
    if not selected_pairs <= configured_pairs:
        raise SourceRecordReceiptReprojectionError(
            "current source-map-selected route is not present in the prior raw audit; "
            "a broad current source-record scan is required"
        )

    lean_check = raw.get("lean_check")
    if not isinstance(lean_check, Mapping) or lean_check.get("returncode") != 0:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit lacks a successful Lean check"
        )
    requested = lean_check.get("requested_checked_rows")
    checked = lean_check.get("checked_rows")
    if not isinstance(requested, list) or requested != checked:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit Lean check lacks exact checked-row coverage"
        )
    checked_pairs: set[tuple[str, str]] = set()
    for item in requested:
        if not isinstance(item, Mapping):
            raise SourceRecordReceiptReprojectionError(
                "prior raw audit Lean check has malformed checked-row evidence"
            )
        row = str(item.get("row") or "").strip()
        qualified = str(item.get("qualified_declaration") or "").strip()
        if not row or not qualified or (row, qualified) in checked_pairs:
            raise SourceRecordReceiptReprojectionError(
                "prior raw audit Lean check has ambiguous checked-row evidence"
            )
        checked_pairs.add((row, qualified))
    if not selected_pairs <= checked_pairs:
        raise SourceRecordReceiptReprojectionError(
            "a current selected route was not checked by the prior Lean audit"
        )
    fresh = lean_check.get("fresh_source_elaboration")
    top_fresh = raw.get("fresh_source_elaboration")
    for evidence in (fresh, top_fresh):
        if not isinstance(evidence, Mapping):
            raise SourceRecordReceiptReprojectionError(
                "prior raw audit lacks fresh source elaboration evidence"
            )
        if evidence.get("mode") != "isolated_temp_overlay" or evidence.get("returncode") != 0:
            raise SourceRecordReceiptReprojectionError(
                "prior raw audit did not complete isolated source elaboration"
            )
        if (
            evidence.get("source_file") != context.review_interface_source.get("path")
            or evidence.get("source_sha256") != context.review_interface_source.get("sha256")
        ):
            raise SourceRecordReceiptReprojectionError(
                "prior raw audit fresh elaboration does not match current interface bytes"
            )
    return map_delta


def _strip_legacy_item_metadata(value: object) -> None:
    """Remove every old item receipt before aggregate-only marking.

    This recursive scrub intentionally catches future ``source_record_item_*``
    transport fields as well as the legacy scalar digest.  It does not change
    ordinary mathematical fields or source-map associations.
    """

    if isinstance(value, dict):
        for key in list(value):
            text = str(key)
            if text.startswith("source_record_item_") or text == (
                "reviewed_elaborated_signature_identities"
            ):
                value.pop(key, None)
                continue
            _strip_legacy_item_metadata(value[key])
    elif isinstance(value, list):
        for item in value:
            _strip_legacy_item_metadata(item)


def _filter_row_items(
    values: object, selected_rows: set[str], *, field: str
) -> list[dict[str, Any]]:
    if not isinstance(values, list):
        raise SourceRecordReceiptReprojectionError(
            f"prior raw audit `{field}` is not a list"
        )
    filtered: list[dict[str, Any]] = []
    for item in values:
        if not isinstance(item, Mapping):
            raise SourceRecordReceiptReprojectionError(
                f"prior raw audit `{field}` has a non-object item"
            )
        row = item.get("row")
        if row is not None and str(row) not in selected_rows:
            continue
        filtered.append(copy.deepcopy(dict(item)))
    return filtered


def _filter_row_mapping(
    value: object, selected_rows: set[str], *, field: str
) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise SourceRecordReceiptReprojectionError(
            f"prior raw audit `{field}` is not an object"
        )
    return {
        str(row): copy.deepcopy(item)
        for row, item in value.items()
        if str(row) in selected_rows
    }


def _filter_key_list(value: object, allowed: set[str], *, field: str) -> list[str]:
    if not isinstance(value, list):
        raise SourceRecordReceiptReprojectionError(
            f"prior raw audit `{field}` is not a list"
        )
    result: list[str] = []
    for raw_key in value:
        key = str(raw_key or "").strip()
        if not key:
            raise SourceRecordReceiptReprojectionError(
                f"prior raw audit `{field}` has an empty judgment key"
            )
        if key in allowed:
            result.append(key)
    return sorted(set(result))


def _semantic_association_declarations(items: list[dict[str, Any]]) -> set[str]:
    """Read only generated fully-qualified route identities from raw items."""

    declarations: set[str] = set()
    for item in items:
        group = item.get("semantic_contract_group")
        if isinstance(group, Mapping):
            members = group.get("member_rows")
            if not isinstance(members, list) or not members:
                raise SourceRecordReceiptReprojectionError(
                    "retained semantic-model group has no member-route evidence"
                )
            for member in members:
                if not isinstance(member, Mapping):
                    raise SourceRecordReceiptReprojectionError(
                        "retained semantic-model group has malformed member-route evidence"
                    )
                identity = member.get("reviewed_declaration_identity")
                qualified = (
                    str(identity.get("qualified_declaration") or "").strip()
                    if isinstance(identity, Mapping)
                    else ""
                )
                if not qualified:
                    raise SourceRecordReceiptReprojectionError(
                        "retained semantic-model group lacks an exact reviewed-route identity"
                    )
                declarations.add(qualified)
            continue
        association = item.get("semantic_contract_source_association")
        if not isinstance(association, Mapping):
            association = item.get("source_statement_association")
        identity = (
            association.get("reviewed_declaration_identity")
            if isinstance(association, Mapping)
            else None
        )
        qualified = (
            str(identity.get("qualified_declaration") or "").strip()
            if isinstance(identity, Mapping)
            else ""
        )
        if not qualified:
            raise SourceRecordReceiptReprojectionError(
                "retained semantic-model item lacks an exact reviewed-route identity"
            )
        declarations.add(qualified)
    return declarations


def _semantic_association_counts(
    *,
    boundary_items: list[dict[str, Any]],
    conclusion_items: list[dict[str, Any]],
    semantic_items: list[dict[str, Any]],
) -> dict[str, int]:
    direct_declarations = _semantic_association_declarations(semantic_items)
    return {
        "direct_route_declaration_count": len(direct_declarations),
        "semantic_contract_member_identity_count": len(direct_declarations),
        "boundary_input_association_count": sum(
            isinstance(item.get("source_contract_association"), Mapping)
            for item in boundary_items
        ),
        "conclusion_dependency_association_count": sum(
            isinstance(item.get("source_contract_association"), Mapping)
            for item in conclusion_items
        ),
    }


def _refresh_projection_items(
    payload: dict[str, Any], selected_rows: set[str], boundary_keys: set[str]) -> None:
    """Filter the two generated precloseout views without interpreting names."""

    for field in (
        "statement_ledger_covered_boundary_input_keys",
        "precloseout_contract_covered_boundary_input_keys",
    ):
        if field in payload:
            payload[field] = _filter_key_list(payload[field], boundary_keys, field=field)
    projection = payload.get("precloseout_exact_contract_projection")
    if not isinstance(projection, Mapping):
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit precloseout exact-contract projection is missing"
        )
    copied = copy.deepcopy(dict(projection))
    raw_items = copied.get("items")
    if not isinstance(raw_items, list):
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit precloseout exact-contract projection has no item list"
        )
    copied["items"] = [
        item
        for item in raw_items
        if not isinstance(item, Mapping)
        or item.get("row") is None
        or str(item.get("row")) in selected_rows
    ]
    covered = _filter_key_list(
        copied.get("covered_boundary_input_keys", []),
        boundary_keys,
        field="precloseout_exact_contract_projection.covered_boundary_input_keys",
    )
    copied["covered_boundary_input_keys"] = covered
    copied["covered_boundary_input_keys_sha256"] = _canonical_digest(covered)
    payload["precloseout_exact_contract_projection"] = copied


def _mark_aggregate_only(payload: dict[str, Any]) -> None:
    # Do not scrub the whole payload: the current aggregate input fingerprint
    # itself intentionally contains ``source_record_item_digest_schema``.
    # Only generated item objects can carry an old scalar item receipt.
    for section in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        values = payload.get(section)
        if values is None:
            continue
        if not isinstance(values, list):
            raise SourceRecordReceiptReprojectionError(
                f"reprojected `{section}` is not a list"
            )
        for item in values:
            if not isinstance(item, dict):
                raise SourceRecordReceiptReprojectionError(
                    f"reprojected `{section}` has a non-object item"
                )
            _strip_legacy_item_metadata(item)
            item["source_record_item_reuse_eligibility"] = {
                "eligible": False,
                "blockers": [SOURCE_RECORD_AGGREGATE_REPROJECTION_ITEM_BLOCKER],
            }
    # These diagnostic row summaries are not reusable sections, but legacy
    # generators also placed scalar item digests on them. Remove those stale
    # transport fields without touching top-level cache identity material.
    for section in ("rows_with_record_premises", "rows_with_semantic_inputs"):
        values = payload.get(section)
        if isinstance(values, list):
            for item in values:
                _strip_legacy_item_metadata(item)


def build_aggregate_only_reprojection(
    prior_raw_audit: Mapping[str, Any],
    *,
    context: CurrentReprojectionContext,
    prior_raw_reference: str,
    prior_raw_sha256: str,
) -> dict[str, Any]:
    """Reproject one proven v10 raw audit to a current deletion-only surface.

    The result has a current aggregate receipt but deliberately has no
    schema-5 item receipts.  It is therefore valid as a preserved aggregate
    source/Lean scan, not as a semantic equivalence proof for old judgments.
    """

    map_delta = _require_clean_prior_raw(prior_raw_audit, context)
    if not _valid_sha256(prior_raw_sha256):
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit provenance lacks a valid file SHA-256"
        )
    selected_rows = {route.row for route in context.selected_routes}
    selected_routes_by_row = {route.row: route for route in context.selected_routes}
    if len(selected_routes_by_row) != len(context.selected_routes):
        raise SourceRecordReceiptReprojectionError(
            "current selected review surface has duplicate row identities"
        )

    payload = copy.deepcopy(dict(prior_raw_audit))
    prior_configured = payload["configured_review_rows"]
    assert isinstance(prior_configured, list)  # validated above
    retained_configured: list[dict[str, Any]] = []
    for raw_route in prior_configured:
        assert isinstance(raw_route, Mapping)
        row = str(raw_route.get("row") or "").strip()
        if row not in selected_rows:
            continue
        current = selected_routes_by_row[row]
        if (
            raw_route.get("qualified_declaration") != current.qualified_declaration
            or raw_route.get("source_file") != current.source_file
            or raw_route.get("source_sha256") != current.source_sha256
        ):
            raise SourceRecordReceiptReprojectionError(
                "a current selected route differs from its prior exact source-byte "
                "review identity; receipt reprojection may not remap it"
            )
        retained_configured.append(copy.deepcopy(dict(raw_route)))
    if len(retained_configured) != len(context.selected_routes):
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit did not provide one exact configured record per current route"
        )

    for field in (
        "boundary_input_items",
        "conclusion_dependency_items",
        "type_valued_certificate_result_items",
        "recursive_field_items",
        "semantic_model_items",
        "source_premise_consistency_items",
        "rows_with_record_premises",
        "rows_with_semantic_inputs",
    ):
        if field in payload:
            payload[field] = _filter_row_items(
                payload[field], selected_rows, field=field
            )
    payload["row_visible_inputs"] = _filter_row_mapping(
        payload.get("row_visible_inputs"), selected_rows, field="row_visible_inputs"
    )
    payload["row_conclusion_inputs"] = _filter_row_mapping(
        payload.get("row_conclusion_inputs"),
        selected_rows,
        field="row_conclusion_inputs",
    )
    if set(payload["row_visible_inputs"]) != selected_rows:
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit lacks visible-input evidence for a current selected route"
        )

    boundary_items = payload["boundary_input_items"]
    conclusion_items = payload["conclusion_dependency_items"]
    recursive_items = payload["recursive_field_items"]
    semantic_items = payload["semantic_model_items"]
    premise_items = payload["source_premise_consistency_items"]
    assert all(isinstance(value, list) for value in (
        boundary_items,
        conclusion_items,
        recursive_items,
        semantic_items,
        premise_items,
    ))
    boundary_keys = {
        str(item.get("judgment_key") or "").strip()
        for item in boundary_items
        if str(item.get("judgment_key") or "").strip()
    }
    field_keys = {
        str(item.get("judgment_key") or "").strip()
        for item in recursive_items
        if str(item.get("judgment_key") or "").strip()
    }
    semantic_keys = {
        str(item.get("judgment_key") or "").strip()
        for item in semantic_items
        if str(item.get("judgment_key") or "").strip()
    }
    if len(boundary_keys) != len(boundary_items) or len(field_keys) != len(recursive_items) or len(semantic_keys) != len(semantic_items):
        raise SourceRecordReceiptReprojectionError(
            "prior raw audit has missing or duplicate retained judgment keys"
        )
    for item in semantic_items:
        dimensions = item.get("dimensions")
        if not isinstance(dimensions, list) or tuple(
            str(dimension.get("id") or "")
            for dimension in dimensions
            if isinstance(dimension, Mapping)
        ) != context.semantic_model_dimensions:
            raise SourceRecordReceiptReprojectionError(
                "prior raw audit semantic-model dimensions do not match the current configuration"
            )
    semantic_declarations = _semantic_association_declarations(semantic_items)
    current_declarations = {
        route.qualified_declaration for route in context.selected_routes
    }
    if semantic_declarations != current_declarations:
        raise SourceRecordReceiptReprojectionError(
            "retained semantic-model source associations do not cover exactly the "
            "current source-map-selected review routes"
        )
    explicit_targets = list(
        context.semantic_selection.get(
            "semantic_model_explicit_source_target_declarations"
        )
        or []
    )
    if explicit_targets:
        module = _load_source_record_audit_module(context.paper_dir.parents[1])
        explicit_item_errors = (
            module.explicit_source_target_semantic_model_item_errors(
                explicit_targets=explicit_targets,
                companion_routes=(
                    context.semantic_selection.get(
                        "semantic_model_explicit_source_target_semantic_contract_companions"
                    )
                    or []
                ),
                semantic_model_items=semantic_items,
            )
        )
        if explicit_item_errors:
            raise SourceRecordReceiptReprojectionError(
                "retained semantic-model items do not preserve every explicit "
                "source target association: "
                + "; ".join(explicit_item_errors)
            )
    else:
        explicit_item_errors = []

    _refresh_projection_items(payload, selected_rows, boundary_keys)
    payload["configured_review_rows"] = retained_configured
    payload["configured_review_rows_count"] = len(retained_configured)
    payload["configured_review_row_count"] = context.configured_review_row_count
    payload["review_row_count"] = len(retained_configured)
    payload["missing_configured_review_rows"] = []
    payload["review_interface_source"] = copy.deepcopy(context.review_interface_source)
    payload["review_assumption_source"] = copy.deepcopy(context.review_assumption_source)
    payload["paper_statement_map_sha256"] = context.paper_statement_map_sha256
    payload["source_record_input_fingerprint"] = copy.deepcopy(context.input_fingerprint)
    payload["import_module"] = context.import_module
    payload["paper_dir"] = _repository_relative_path(
        context.paper_dir.parents[1], context.paper_dir
    )
    payload["source_coverage_mode"] = context.source_coverage.get("source_coverage_mode")
    payload["source_coverage_selected_source_items"] = copy.deepcopy(
        context.source_coverage.get("source_coverage_selected_source_items")
    )
    payload["source_coverage_mode_error"] = context.source_coverage.get(
        "source_coverage_mode_error"
    )
    payload["source_coverage_route_errors"] = copy.deepcopy(
        context.source_coverage.get("source_coverage_route_errors")
    )
    payload["source_coverage_unrouted_source_items"] = copy.deepcopy(
        context.source_coverage.get("source_coverage_unrouted_source_items")
    )
    payload["out_of_mode_review_surface_rows"] = copy.deepcopy(
        context.source_coverage.get("out_of_mode_review_surface_rows")
    )
    for field in (
        "semantic_model_source_selected_rows",
        "semantic_model_configured_assumption_rows",
        "semantic_model_scope_target_declarations",
        "semantic_model_scope_target_rows",
        "semantic_model_scope_target_route_errors",
        "semantic_model_explicit_source_target_declarations",
        "semantic_model_explicit_source_target_source_items",
        "semantic_model_explicit_source_target_rows",
        "semantic_model_explicit_source_target_route_errors",
        "semantic_model_explicit_source_target_effective_row_errors",
        "semantic_model_explicit_source_target_generated_item_errors",
        "semantic_model_explicit_source_target_semantic_contract_companions",
        "semantic_model_target_route_errors",
    ):
        payload[field] = copy.deepcopy(context.semantic_selection.get(field))
    payload["semantic_model_explicit_source_target_generated_item_errors"] = (
        explicit_item_errors
    )
    payload["unconfigured_review_surface_rows"] = list(
        context.unconfigured_review_surface_rows
    )
    payload["unconfigured_paper_interface_rows"] = list(
        context.unconfigured_review_surface_rows
    )
    payload["unconfigured_assumption_support_rows"] = list(
        context.unconfigured_assumption_support_rows
    )
    payload["quarantined_auxiliary_review_rows"] = list(
        context.quarantined_auxiliary_review_rows
    )
    payload["expected_input_judgment_keys"] = sorted(boundary_keys)
    payload["expected_field_judgment_keys"] = sorted(field_keys)
    payload["expected_semantic_model_judgment_keys"] = sorted(semantic_keys)
    payload["boundary_input_count"] = len(boundary_items)
    payload["conclusion_dependency_count"] = len(conclusion_items)
    payload["type_valued_certificate_result_count"] = len(
        payload["type_valued_certificate_result_items"]
    )
    payload["recursive_field_count"] = len(recursive_items)
    payload["semantic_model_item_count"] = len(semantic_items)
    payload["source_premise_consistency_item_count"] = len(premise_items)
    payload["source_contract_association_counts"] = _semantic_association_counts(
        boundary_items=boundary_items,
        conclusion_items=conclusion_items,
        semantic_items=semantic_items,
    )
    payload["source_contract_association_errors"] = []
    payload["source_contract_association_error_count"] = 0
    payload["semantic_model_review_configuration_errors"] = []
    payload["semantic_context_requirements"] = [
        copy.deepcopy(value) for value in context.semantic_context_requirements
    ]
    payload["semantic_context_requirement_count"] = len(
        context.semantic_context_requirements
    )
    payload["semantic_context_requirements_sha256"] = (
        _canonical_digest(list(context.semantic_context_requirements))
        if context.semantic_context_requirements
        else ""
    )
    payload["source_proof_fidelity"] = copy.deepcopy(context.source_proof_fidelity)
    payload["formalization_scope"] = copy.deepcopy(context.formalization_scope)
    payload["recursion_failure_count"] = len(payload.get("recursion_failures") or [])

    lean_check = payload.get("lean_check")
    assert isinstance(lean_check, dict)  # validated above
    for field in ("requested_checked_rows", "checked_rows"):
        values = lean_check[field]
        assert isinstance(values, list)
        lean_check[field] = [
            copy.deepcopy(dict(item))
            for item in values
            if isinstance(item, Mapping) and str(item.get("row") or "") in selected_rows
        ]
    if lean_check["requested_checked_rows"] != lean_check["checked_rows"]:
        raise SourceRecordReceiptReprojectionError(
            "internal reprojection error: filtered Lean coverage differs"
        )
    payload["current_source_record_judgment_count"] = 0
    payload["resolved_conclusion_dependency_count"] = 0
    payload["resolved_conclusion_dependency_items"] = []
    payload["unresolved_conclusion_dependency_count"] = len(conclusion_items)
    payload["unresolved_conclusion_dependency_items"] = copy.deepcopy(conclusion_items)

    # Prompt wording is a derived manual-review view, not raw evidence. The
    # template command can render it from these retained obligations.
    payload.pop("llm_judge_prompt", None)

    _mark_aggregate_only(payload)
    for field in (
        "source_record_audit_sha256",
        "source_record_audit_surface_schema",
        "source_record_audit_surface",
        "source_record_audit_integrity_schema",
        "source_record_audit_integrity_sha256",
    ):
        payload.pop(field, None)
    route_surface = [route.as_raw_row() for route in context.selected_routes]
    reprojection_provenance: dict[str, Any] = {
        "schema": SOURCE_RECORD_AGGREGATE_REPROJECTION_SCHEMA,
        "artifact_kind": SOURCE_RECORD_AGGREGATE_REPROJECTION_ARTIFACT_KIND,
        "policy_version": SOURCE_RECORD_AGGREGATE_REPROJECTION_POLICY_VERSION,
        "prior_raw_audit_path": prior_raw_reference,
        "prior_raw_audit_file_sha256": prior_raw_sha256,
        "prior_raw_audit_aggregate_sha256": prior_raw_audit[
            "source_record_audit_sha256"
        ],
        "current_source_record_input_fingerprint_sha256": _canonical_digest(
            context.input_fingerprint
        ),
        "current_selected_review_routes": route_surface,
        "current_selected_review_routes_sha256": _canonical_digest(route_surface),
        "selection_policy": "exact_current_source_map_routes_deletion_only",
        "item_reuse_mode": "aggregate_only_pending_focused_signature_manifest",
        "item_reuse_blocker": SOURCE_RECORD_AGGREGATE_REPROJECTION_ITEM_BLOCKER,
        "judgment_sidecar_rebinding": "forbidden",
        "focused_signature_manifest": {
            "required": True,
            "status": "pending",
            "expected_route_count": len(route_surface),
            "expected_routes_sha256": _canonical_digest(route_surface),
        },
    }
    if map_delta is not None:
        reprojection_provenance["paper_statement_map_exact_default_mode_delta"] = (
            map_delta.as_provenance()
        )
    payload[SOURCE_RECORD_AGGREGATE_REPROJECTION_FIELD] = reprojection_provenance
    surface = {
        "source_record_policy_version": SOURCE_RECORD_V10_PROMPT_VERSION,
        SOURCE_RECORD_AGGREGATE_REPROJECTION_FIELD: copy.deepcopy(
            payload[SOURCE_RECORD_AGGREGATE_REPROJECTION_FIELD]
        ),
    }
    attach_source_record_audit_surface(payload, surface)
    stamp_source_record_audit_integrity(payload)

    receipt_error = source_record_audit_receipt_error(payload)
    if receipt_error:
        raise SourceRecordReceiptReprojectionError(
            "internal reprojection error: aggregate receipt is invalid: " + receipt_error
        )
    item_error = source_record_raw_reusable_item_metadata_error(
        payload, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    )
    if item_error:
        raise SourceRecordReceiptReprojectionError(
            "internal reprojection error: aggregate-only item metadata is invalid: "
            + item_error
        )
    scan_error = source_record_raw_scan_completeness_error(payload)
    if scan_error:
        raise SourceRecordReceiptReprojectionError(
            "internal reprojection error: retained raw scan is incomplete: " + scan_error
        )
    return payload


def _focused_signature_manifest_payload(
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    manifests: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    """Bind exact current Lean signature digests to a reprojected raw receipt."""

    reprojection = raw_audit.get(SOURCE_RECORD_AGGREGATE_REPROJECTION_FIELD)
    if not isinstance(reprojection, Mapping):
        raise SourceRecordReceiptReprojectionError(
            "raw audit is not an aggregate-only receipt reprojection"
        )
    if raw_audit.get("paper") != paper:
        raise SourceRecordReceiptReprojectionError(
            "raw audit paper does not match requested focused signature manifest"
        )
    receipt_error = source_record_audit_receipt_error(raw_audit)
    if receipt_error:
        raise SourceRecordReceiptReprojectionError(
            "raw audit receipt is invalid before focused signature collection: "
            + receipt_error
        )
    routes = reprojection.get("current_selected_review_routes")
    if not isinstance(routes, list) or not routes:
        raise SourceRecordReceiptReprojectionError(
            "aggregate-only reprojection lacks selected current review routes"
        )
    from scripts.lean_signature_manifest import signature_manifest_digest

    signature_rows: list[dict[str, str]] = []
    expected_names: set[str] = set()
    for route in routes:
        if not isinstance(route, Mapping):
            raise SourceRecordReceiptReprojectionError(
                "aggregate-only reprojection has malformed selected review routes"
            )
        qualified = str(route.get("qualified_declaration") or "").strip()
        if not qualified or qualified in expected_names:
            raise SourceRecordReceiptReprojectionError(
                "aggregate-only reprojection has duplicate selected declaration routes"
            )
        expected_names.add(qualified)
        manifest = manifests.get(qualified)
        digest = signature_manifest_digest(dict(manifest)) if isinstance(manifest, Mapping) else ""
        if not _valid_sha256(digest):
            raise SourceRecordReceiptReprojectionError(
                "focused Lean signature collection is missing a valid manifest for "
                + qualified
            )
        signature_rows.append(
            {
                "qualified_declaration": qualified,
                "elaborated_signature_sha256": digest,
            }
        )
    if set(manifests) != expected_names:
        raise SourceRecordReceiptReprojectionError(
            "focused Lean signature collection returned an unexpected declaration set"
        )
    payload: dict[str, Any] = {
        "schema": FOCUSED_SIGNATURE_MANIFEST_SCHEMA,
        "artifact_kind": FOCUSED_SIGNATURE_MANIFEST_ARTIFACT_KIND,
        "policy_version": FOCUSED_SIGNATURE_MANIFEST_POLICY_VERSION,
        "paper": paper,
        "import_module": raw_audit.get("import_module"),
        "source_record_audit_sha256": raw_audit.get("source_record_audit_sha256"),
        "source_record_audit_integrity_sha256": raw_audit.get(
            "source_record_audit_integrity_sha256"
        ),
        "source_record_input_fingerprint_sha256": _canonical_digest(
            raw_audit.get("source_record_input_fingerprint")
        ),
        "review_interface_source": copy.deepcopy(raw_audit.get("review_interface_source")),
        "selected_review_routes_sha256": reprojection.get(
            "current_selected_review_routes_sha256"
        ),
        "selected_review_route_signatures": signature_rows,
    }
    payload["focused_signature_manifest_sha256"] = _canonical_digest(payload)
    return payload


def focused_signature_manifest_error(
    raw_audit: Mapping[str, Any], manifest: Mapping[str, Any], *, paper: str
) -> str:
    """Validate an externally stored focused-signature artifact without Lean."""

    if manifest.get("schema") != FOCUSED_SIGNATURE_MANIFEST_SCHEMA:
        return "focused signature manifest has an unsupported schema"
    if manifest.get("artifact_kind") != FOCUSED_SIGNATURE_MANIFEST_ARTIFACT_KIND:
        return "focused signature manifest has the wrong artifact kind"
    if manifest.get("policy_version") != FOCUSED_SIGNATURE_MANIFEST_POLICY_VERSION:
        return "focused signature manifest has the wrong policy version"
    if manifest.get("paper") != paper:
        return "focused signature manifest belongs to another paper"
    reprojection = raw_audit.get(SOURCE_RECORD_AGGREGATE_REPROJECTION_FIELD)
    if not isinstance(reprojection, Mapping):
        return "raw audit is not an aggregate-only receipt reprojection"
    expected_fields = {
        "source_record_audit_sha256": raw_audit.get("source_record_audit_sha256"),
        "source_record_audit_integrity_sha256": raw_audit.get(
            "source_record_audit_integrity_sha256"
        ),
        "source_record_input_fingerprint_sha256": _canonical_digest(
            raw_audit.get("source_record_input_fingerprint")
        ),
        "review_interface_source": raw_audit.get("review_interface_source"),
        "selected_review_routes_sha256": reprojection.get(
            "current_selected_review_routes_sha256"
        ),
    }
    for field, expected in expected_fields.items():
        if manifest.get(field) != expected:
            return f"focused signature manifest does not match raw audit `{field}`"
    rows = manifest.get("selected_review_route_signatures")
    routes = reprojection.get("current_selected_review_routes")
    if not isinstance(rows, list) or not isinstance(routes, list):
        return "focused signature manifest has malformed route records"
    route_names = {
        str(route.get("qualified_declaration") or "").strip()
        for route in routes
        if isinstance(route, Mapping)
    }
    signature_names: set[str] = set()
    for row in rows:
        if not isinstance(row, Mapping):
            return "focused signature manifest has a non-object route record"
        name = str(row.get("qualified_declaration") or "").strip()
        if not name or name in signature_names or not _valid_sha256(
            row.get("elaborated_signature_sha256")
        ):
            return "focused signature manifest has an invalid route-signature record"
        signature_names.add(name)
    if signature_names != route_names:
        return "focused signature manifest does not cover exactly the raw selected routes"
    expected_digest = _canonical_digest(
        {
            key: value
            for key, value in manifest.items()
            if key != "focused_signature_manifest_sha256"
        }
    )
    if manifest.get("focused_signature_manifest_sha256") != expected_digest:
        return "focused signature manifest integrity digest is invalid"
    return ""


def _default_raw_path(root: Path, paper: str) -> Path:
    return root / "papers" / paper / "audit" / "source_record_audit.json"


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True, help="paper folder id")
    parser.add_argument("--root", default=".", help="repository root")
    parser.add_argument(
        "--raw-audit", help="legacy or reprojected raw source-record audit path"
    )
    parser.add_argument(
        "--out", help="write the aggregate-only reprojected raw audit to this path"
    )
    parser.add_argument(
        "--replace-raw",
        action="store_true",
        help="replace --raw-audit only after first archiving its exact bytes",
    )
    parser.add_argument(
        "--archive-prior-raw-to",
        help="new archive path required with --replace-raw",
    )
    parser.add_argument(
        "--max-depth", type=int, default=4, help="current source-record depth identity",
    )
    parser.add_argument(
        "--write-focused-signature-manifest",
        help=(
            "run only the focused current Lean signature pass for a reprojected "
            "raw audit and write the resulting manifest to this path"
        ),
    )
    parser.add_argument(
        "--verify-focused-signature-manifest",
        help="verify a focused signature manifest against --raw-audit without Lean",
    )
    return parser.parse_args()


def _main() -> int:
    args = _parse_args()
    root = Path(args.root).resolve()
    raw_path = Path(args.raw_audit) if args.raw_audit else _default_raw_path(root, args.paper)
    if not raw_path.is_absolute():
        raw_path = root / raw_path
    raw_path = raw_path.resolve()
    modes = sum(
        bool(value)
        for value in (
            args.write_focused_signature_manifest,
            args.verify_focused_signature_manifest,
        )
    )
    if modes > 1:
        raise SourceRecordReceiptReprojectionError(
            "choose at most one focused-signature manifest mode"
        )
    raw, raw_bytes = _load_json_object(raw_path)
    if args.verify_focused_signature_manifest:
        manifest_path = Path(args.verify_focused_signature_manifest)
        if not manifest_path.is_absolute():
            manifest_path = root / manifest_path
        manifest, _ = _load_json_object(manifest_path.resolve())
        error = focused_signature_manifest_error(raw, manifest, paper=args.paper)
        if error:
            raise SourceRecordReceiptReprojectionError(error)
        print("focused signature manifest matches the aggregate-only raw receipt")
        return 0
    if args.write_focused_signature_manifest:
        receipt_error = source_record_audit_receipt_error(raw)
        if receipt_error:
            raise SourceRecordReceiptReprojectionError(
                "raw audit receipt is invalid before focused signature collection: "
                + receipt_error
            )
        reprojection = raw.get(SOURCE_RECORD_AGGREGATE_REPROJECTION_FIELD)
        if not isinstance(reprojection, Mapping):
            raise SourceRecordReceiptReprojectionError(
                "--write-focused-signature-manifest requires a reprojected raw audit"
            )
        routes = reprojection.get("current_selected_review_routes")
        if not isinstance(routes, list):
            raise SourceRecordReceiptReprojectionError(
                "reprojected raw audit lacks selected route records"
            )
        names = [
            str(route.get("qualified_declaration") or "").strip()
            for route in routes
            if isinstance(route, Mapping)
        ]
        if not names or len(set(names)) != len(names) or any(not name for name in names):
            raise SourceRecordReceiptReprojectionError(
                "reprojected raw audit has malformed selected route records"
            )
        from scripts.lean_signature_manifest import (
            paper_owned_module_names_in_import_closure,
            run_lean_signature_manifests,
        )

        import_module = str(raw.get("import_module") or "")
        manifests = run_lean_signature_manifests(
            root,
            import_module,
            names,
            timeout_seconds=120,
            build_timeout_seconds=600,
            semantic_dependency_modules=(
                paper_owned_module_names_in_import_closure(
                    root, root / "papers" / args.paper, import_module
                )
            ),
        )
        payload = _focused_signature_manifest_payload(
            raw, paper=args.paper, manifests=manifests
        )
        destination = Path(args.write_focused_signature_manifest)
        if not destination.is_absolute():
            destination = root / destination
        _atomic_write(
            destination.resolve(),
            (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8"),
        )
        print(
            "wrote focused current Lean signature manifest for "
            f"{len(names)} exact selected route(s)"
        )
        return 0

    if args.out and args.replace_raw:
        raise SourceRecordReceiptReprojectionError(
            "--out cannot be combined with --replace-raw"
        )
    if args.replace_raw:
        if not args.archive_prior_raw_to:
            raise SourceRecordReceiptReprojectionError(
                "--replace-raw requires --archive-prior-raw-to"
            )
        archive_path = Path(args.archive_prior_raw_to)
        if not archive_path.is_absolute():
            archive_path = root / archive_path
        archive_path = archive_path.resolve()
        if archive_path.exists():
            raise SourceRecordReceiptReprojectionError(
                f"refusing to overwrite prior raw archive at {archive_path}"
            )
        prior_reference = _repository_relative_path(root, archive_path)
    else:
        prior_reference = _repository_relative_path(root, raw_path)
        archive_path = None
    context = _resolve_current_review_context(
        root=root, paper=args.paper, max_depth=args.max_depth
    )
    candidate = build_aggregate_only_reprojection(
        raw,
        context=context,
        prior_raw_reference=prior_reference,
        prior_raw_sha256=_sha256_bytes(raw_bytes),
    )
    encoded = (json.dumps(candidate, indent=2, sort_keys=True) + "\n").encode("utf-8")
    if args.replace_raw:
        assert archive_path is not None
        _atomic_write(archive_path, raw_bytes)
        _atomic_write(raw_path, encoded)
        print(
            "archived the pre-schema5 raw receipt and wrote an aggregate-only "
            f"v10 reprojection for {len(context.selected_routes)} current selected route(s)"
        )
        return 0
    if args.out:
        destination = Path(args.out)
        if not destination.is_absolute():
            destination = root / destination
        destination = destination.resolve()
        if destination == raw_path:
            raise SourceRecordReceiptReprojectionError(
                "refusing to overwrite --raw-audit without --replace-raw and an archive"
            )
        _atomic_write(destination, encoded)
        print(
            "wrote aggregate-only v10 receipt reprojection for "
            f"{len(context.selected_routes)} current selected route(s)"
        )
        return 0
    print(encoded.decode("utf-8"), end="")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(_main())
    except SourceRecordReceiptReprojectionError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
