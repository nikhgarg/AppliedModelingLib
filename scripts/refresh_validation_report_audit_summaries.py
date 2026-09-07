#!/usr/bin/env python3
"""Refresh public final-validation report audit summaries from sidecars."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import tempfile
from collections import Counter
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__ in {None, ""}:  # Import the trusted current-closeout package.
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.current_closeout.protocol_selection import current_v11_protocol_selected

try:
    from approved_review_context_report import (
        approved_review_contexts_for_report,
        replace_approved_review_context_block,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.approved_review_context_report import (
        approved_review_contexts_for_report,
        replace_approved_review_context_block,
    )

try:
    from source_coverage_scope import (
        SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        filter_source_map_items_for_coverage,
        source_coverage_mode_migration_error,
        source_coverage_mode_from_map,
        source_index_byte_pinned_anchor_item_ids,
        source_item_coverage_sha256,
        source_item_has_explicit_nonordinary_obligation,
        source_named_result_environment_kinds_from_map,
        source_presentation_aliases,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.source_coverage_scope import (
        SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        filter_source_map_items_for_coverage,
        source_coverage_mode_migration_error,
        source_coverage_mode_from_map,
        source_index_byte_pinned_anchor_item_ids,
        source_item_coverage_sha256,
        source_item_has_explicit_nonordinary_obligation,
        source_named_result_environment_kinds_from_map,
        source_presentation_aliases,
    )

try:
    from lean_import_closure import WorktreeImportClosureProvider
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.lean_import_closure import WorktreeImportClosureProvider

try:
    from sync_paper_status import (
        LazySharedClosureProvider,
        SavedSidecarReuseAuthorization,
        saved_sidecar_reuse_authorization,
        validated_human_review_counts,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.sync_paper_status import (
        LazySharedClosureProvider,
        SavedSidecarReuseAuthorization,
        saved_sidecar_reuse_authorization,
        validated_human_review_counts,
    )


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
REPORT = "FINAL_VALIDATION_REPORT.md"
BEGIN = "<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->"
END = "<!-- END GENERATED LLM-AS-JUDGE RESULTS -->"
DAG_AUDIT = "docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md"

SECTION_BLOCKS = {
    13: (
        "Paper Assumption Provenance",
        "<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->",
        "<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->",
    ),
    14: (
        "Displayed Formula Provenance",
        "<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->",
        "<!-- END GENERATED FORMULA PROVENANCE LEDGER -->",
    ),
    20: (
        "Paper-Facing Statement Validator Ledger",
        "<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->",
        "<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->",
    ),
    21: (
        "Source-Coverage Audit Ledger",
        "<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->",
        "<!-- END GENERATED SOURCE COVERAGE LEDGER -->",
    ),
}

FORMULA_SOURCE_KINDS = frozenset({"equation", "formula"})
SEMANTIC_CONTRACT_EVIDENCE_MODES = frozenset({"proves", "refutes"})
COVERAGE_MODE_LABELS = {
    "named_theoretical_statements": "named theoretical statements",
    "deep_paper_with_all_prose_claims": "deep paper with all prose claims",
}

_SAVED_REUSE_PROVIDER: LazySharedClosureProvider | None = None

CANONICAL_SIDECAR_NAMES = {
    "assumption": "assumption_match_llm.json",
    "coverage": "paper_coverage_llm.json",
    "source_map": "paper_statement_map.json",
    "statement": "statement_match_llm.json",
    "tex": "lean_to_tex_llm.json",
    "review": "review_surface_llm.json",
}
SUMMARY_SIDECAR_NAMES = {
    "record_match": "source_record_match_llm.json",
    "record_audit": "source_record_audit.json",
}


@dataclass(frozen=True)
class ReportInputSnapshot:
    """One immutable-in-use read of every paper-local report input."""

    path: Path
    text: str
    status: dict[str, Any]
    evidence: dict[str, dict[str, Any] | None]
    sidecar_paths: dict[str, Path | None]
    record_match: dict[str, Any] | None
    record_audit: dict[str, Any] | None
    cache_rows: tuple[dict[str, Any], ...]
    input_paths: tuple[Path, ...]
    input_sha256: str


@dataclass(frozen=True)
class PreparedReport:
    """Rendered report plus the exact inputs and reuse authority it used."""

    snapshot: ReportInputSnapshot
    reuse: SavedSidecarReuseAuthorization
    rendered: str


ASSUMPTION_LABELS = {
    "approved_corrected_condition": "source condition",
    "approved_formalization_regularity": "source condition",
    "approved_source_convention": "source condition",
    "documented_additional_assumption": "additional assumption",
    "paper_assumption": "source condition",
    "paper_condition": "source condition",
    "partial_boundary": "formalization boundary",
    "source_text_model_primitive": "source condition",
    "unresolved_assumed_math": "formalization boundary",
    "validated_source_assumption": "source condition",
}

STATEMENT_LABELS = {
    "matches": "exact match",
    "mismatch": "does not match",
    "partial_match": "partial match",
    "stale": "needs fresh review",
    "uncertain": "needs review",
}

COVERAGE_LABELS = {
    "collective_support": "support only",
    "conditional_boundary": "conditional boundary",
    "covered": "covered",
    "covered_by_rows": "covered by reviewed rows",
    "covered_by_support": "support only",
    "covered_corrected_target": "corrected target covered",
    "covered_with_boundary": "conditional boundary",
    "exact": "covered",
    "missing": "missing",
    "not_a_paper_target": "out of scope",
    "not_a_theorem_statement": "out of scope",
    "partially_covered": "partially covered",
    "support": "support only",
    "support_only": "support only",
    "user_approved_scope_exclusion": "out of scope",
}

RESOLUTION_LABELS = {
    "approved_corrected_target": "approved corrected source target",
    "conditional_boundary": "formalization boundary",
    "visible_premise_boundary": "formalization boundary",
}

REVIEW_LABELS = {
    "keep": "paper-facing",
    "paper_facing": "paper-facing",
    "passes": "review surface passed",
}

COVERAGE_ORDER = [
    "covered",
    "covered_by_support",
    "visible_premise_boundary",
    "conditional_boundary",
    "partial_boundary",
    "not_a_paper_target",
    "uncovered",
]
DISPLAY_LABELS = {
    "approved_corrected_condition": "approved corrected source condition",
    "approved_corrected_target": "approved corrected target",
    "approved_external_boundary": "formalization boundary",
    "approved_formalization_regularity": "approved regularity condition",
    "approved_source_convention": "source convention",
    "container_recursively_audited": "recursively audited support",
    "conditional_boundary": "visible-premise boundary",
    "covered_by_rows": "covered by supporting rows",
    "covered_by_support": "covered by supporting rows",
    "covered_corrected_target": "corrected target covered",
    "covered_with_boundary": "covered with a formalization boundary",
    "derived_consequence_record": "derived",
    "derived_from_visible_boundary": "derived from a formalization boundary",
    "documented_additional_assumption": "additional assumption",
    "nonpropositional_witness_data": "non-propositional witness data",
    "not_a_paper_target": "out of scope",
    "not_a_theorem_statement": "not a named theoretical statement",
    "paper_assumption": "source condition",
    "paper_condition": "source condition",
    "partial_boundary": "formalization boundary",
    "partially_covered": "partially covered",
    "partial_match": "partial match",
    "proved_from_primitives": "derived",
    "semantic_model_review": "semantic model review",
    "source_text_model_primitive": "source model primitive",
    "support_only": "support only",
    "uncovered": "missing",
    "unresolved_assumed_math": "unresolved mathematical assumption",
    "user_approved_scope_exclusion": "user-approved out of scope",
    "validated_source_assumption": "source condition",
    "validated_source_outcome_domain": "source outcome domain",
    "visible_boundary_component": "visible formalization boundary",
    "visible_premise_boundary": "visible-premise boundary",
    **ASSUMPTION_LABELS,
    **STATEMENT_LABELS,
    **COVERAGE_LABELS,
    **RESOLUTION_LABELS,
    **REVIEW_LABELS,
}
FORBIDDEN_RAW_ENUMS = tuple(sorted(raw for raw in DISPLAY_LABELS if "_" in raw))
STATEMENT_ORDER = [
    "matches",
    "mismatch",
    "partial_match",
    "uncertain",
]
ASSUMPTION_ORDER = [
    "paper_condition",
    "paper_assumption",
    "documented_additional_assumption",
    "partial_boundary",
]
SOURCE_RECORD_ORDER = [
    "proved_from_primitives",
    "visible_boundary_component",
    "derived_from_visible_boundary",
    "validated_source_assumption",
    "container_recursively_audited",
    "derived_consequence_record",
    "nonpropositional_witness_data",
    "approved_external_boundary",
    "unresolved_assumed_math",
]


def uses_direct_source_spec_closeout(
    status: Mapping[str, Any], source_map: Mapping[str, Any] | None = None
) -> bool:
    """Whether a report is owned by the source-to-expanded-Spec closeout lane.

    The legacy refresher projects v10 sidecars into sections 13--21.  Those
    sidecars are neither the canonical semantic judgment nor the human-facing
    source-first order for a v11 paper, so refreshing them would overwrite a
    deliberately curated closeout report with an obsolete evidence lane.
    """

    return current_v11_protocol_selected(status, source_map)


def supports_legacy_generated_layout(text: str) -> bool:
    """Whether a report still declares the retired generated-ledger layout."""

    required_sections = (12, 13, 14, 15, 20, 21)
    return all(
        re.search(rf"(?m)^## {section}\. ", text) is not None
        for section in required_sections
    )


def public_report_paths(paper: str | None = None) -> list[Path]:
    paths = sorted(
        path for path in PAPERS.glob(f"*/{REPORT}") if path.parent.name != "TEMPLATE"
    )
    if paper is None:
        return paths
    return [path for path in paths if path.parent.name == paper]


def sidecar(folder: Path, name: str) -> Path | None:
    for path in (folder / "audit" / name, folder / name):
        if path.exists():
            return path
    return None


def load_json(path: Path | None) -> dict[str, Any] | None:
    if path is None:
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path.relative_to(ROOT)} should contain a JSON object")
    return payload


def _path_label(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError):
        return path.resolve().as_posix()


def _json_object_from_bytes(path: Path, raw: bytes) -> dict[str, Any]:
    try:
        payload = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"{_path_label(path)} should contain valid JSON") from exc
    if not isinstance(payload, dict):
        raise ValueError(f"{_path_label(path)} should contain a JSON object")
    return payload


def report_input_digest(paths: tuple[Path, ...]) -> str:
    """Hash the exact report-input path set without reparsing JSON."""

    records: list[dict[str, str]] = []
    for path in paths:
        try:
            raw = path.read_bytes()
        except FileNotFoundError:
            raw = None
        except OSError as exc:
            raise ValueError(f"cannot read report input {_path_label(path)}") from exc
        records.append(
            {
                "path": path.as_posix(),
                "state": "present" if raw is not None else "missing",
                "sha256": hashlib.sha256(raw).hexdigest() if raw is not None else "",
            }
        )
    return hashlib.sha256(
        json.dumps(
            {"report_input_snapshot": records},
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def load_report_input_snapshot(path: Path) -> ReportInputSnapshot:
    """Read one report and all of its inputs once, with an exact byte identity."""

    folder = path.parent
    observed: dict[Path, bytes | None] = {}

    def read_optional(candidate: Path) -> bytes | None:
        candidate = candidate.resolve()
        if candidate in observed:
            return observed[candidate]
        try:
            raw = candidate.read_bytes()
        except FileNotFoundError:
            raw = None
        except OSError as exc:
            raise ValueError(
                f"cannot read report input {_path_label(candidate)}"
            ) from exc
        observed[candidate] = raw
        return raw

    def selected_sidecar(name: str) -> tuple[Path | None, dict[str, Any] | None]:
        selected_path: Path | None = None
        selected_raw: bytes | None = None
        for candidate in (folder / "audit" / name, folder / name):
            raw = read_optional(candidate)
            if selected_path is None and raw is not None:
                selected_path = candidate.resolve()
                selected_raw = raw
        if selected_path is None or selected_raw is None:
            return None, None
        return selected_path, _json_object_from_bytes(selected_path, selected_raw)

    report_raw = read_optional(path)
    if report_raw is None:
        raise ValueError(f"report input {_path_label(path)} is missing")
    try:
        report_text = report_raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError(f"report input {_path_label(path)} is not UTF-8") from exc

    status_path = folder / "status.json"
    status_raw = read_optional(status_path)
    status = (
        _json_object_from_bytes(status_path, status_raw)
        if status_raw is not None
        else {}
    )

    # Decide the lane from current status/map bytes before touching historical
    # sidecars or their root aliases. Current reports need only their source
    # context; the old machine-summary layout is not their evidence owner.
    source_map_path = folder / "audit" / "paper_statement_map.json"
    source_map_raw = read_optional(source_map_path)
    canonical_source_map = (
        _json_object_from_bytes(source_map_path, source_map_raw)
        if source_map_raw is not None
        else None
    )
    current_v11 = uses_direct_source_spec_closeout(status, canonical_source_map)
    evidence: dict[str, dict[str, Any] | None] = {
        key: None for key in CANONICAL_SIDECAR_NAMES
    }
    sidecar_paths: dict[str, Path | None] = {
        key: None for key in (*CANONICAL_SIDECAR_NAMES, *SUMMARY_SIDECAR_NAMES)
    }
    summary_payloads: dict[str, dict[str, Any] | None] = {
        key: None for key in SUMMARY_SIDECAR_NAMES
    }
    cache_raw = None
    if current_v11:
        evidence["source_map"] = canonical_source_map
        if source_map_raw is not None:
            sidecar_paths["source_map"] = source_map_path.resolve()
    else:
        for key, name in CANONICAL_SIDECAR_NAMES.items():
            selected_path, payload = selected_sidecar(name)
            sidecar_paths[key] = selected_path
            evidence[key] = payload
        for key, name in SUMMARY_SIDECAR_NAMES.items():
            selected_path, payload = selected_sidecar(name)
            sidecar_paths[key] = selected_path
            summary_payloads[key] = payload
        cache_path = folder / ".review_traces" / "paper_interface_cache.json"
        cache_raw = read_optional(cache_path)
    cache_rows: tuple[dict[str, Any], ...] = ()
    if cache_raw is not None:
        cache_payload = _json_object_from_bytes(cache_path, cache_raw)
        raw_rows = cache_payload.get("rows", [])
        if isinstance(raw_rows, list):
            cache_rows = tuple(row for row in raw_rows if isinstance(row, dict))

    source_map = evidence.get("source_map")
    if isinstance(source_map, dict):
        raw_source_path = str(source_map.get("source_artifact_path") or "").strip()
        if raw_source_path:
            relative_source_path = Path(raw_source_path)
            anchor = ROOT if relative_source_path.parts[:1] == ("papers",) else folder
            try:
                source_path = (anchor / relative_source_path).resolve()
                source_path.relative_to(folder.resolve())
            except (OSError, RuntimeError, ValueError):
                pass
            else:
                read_optional(source_path)

    input_paths = tuple(sorted(observed, key=lambda candidate: candidate.as_posix()))
    input_records = [
        {
            "path": candidate.as_posix(),
            "state": "present" if observed[candidate] is not None else "missing",
            "sha256": (
                hashlib.sha256(observed[candidate]).hexdigest()
                if observed[candidate] is not None
                else ""
            ),
        }
        for candidate in input_paths
    ]
    input_sha256 = hashlib.sha256(
        json.dumps(
            {"report_input_snapshot": input_records},
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()
    return ReportInputSnapshot(
        path=path.resolve(),
        text=report_text,
        status=status,
        evidence=evidence,
        sidecar_paths=sidecar_paths,
        record_match=summary_payloads["record_match"],
        record_audit=summary_payloads["record_audit"],
        cache_rows=cache_rows,
        input_paths=input_paths,
        input_sha256=input_sha256,
    )


def items(payload: dict[str, Any] | None) -> list[dict[str, Any]]:
    if payload is None:
        return []
    raw = payload.get("items", {})
    if isinstance(raw, dict):
        return [value for value in raw.values() if isinstance(value, dict)]
    if isinstance(raw, list):
        return [value for value in raw if isinstance(value, dict)]
    return []


def keyed_items(payload: dict[str, Any] | None) -> dict[str, dict[str, Any]]:
    """Return sidecar rows with deterministic, evidence-provided identities."""

    if payload is None:
        return {}
    raw = payload.get("items", {})
    if isinstance(raw, dict):
        return {
            str(key): value for key, value in raw.items() if isinstance(value, dict)
        }
    if not isinstance(raw, list):
        return {}

    result: dict[str, dict[str, Any]] = {}
    identity_fields = (
        "id",
        "row",
        "name",
        "lean_declaration",
        "reviewed_declaration",
        "source_item",
    )
    for index, value in enumerate(raw, start=1):
        if not isinstance(value, dict):
            continue
        identity = next(
            (
                value[field].strip()
                for field in identity_fields
                if isinstance(value.get(field), str) and value[field].strip()
            ),
            f"recorded-row-{index}",
        )
        if identity in result:
            identity = f"{identity} ({index})"
        result[identity] = value
    return result


def reuse_coverage_binding_maps(
    authorization: SavedSidecarReuseAuthorization,
) -> tuple[dict[str, str], dict[str, str]]:
    """Validate the receipt's name-free selected-source bijection."""

    raw_bindings = getattr(authorization, "coverage_source_bindings", ())
    if not authorization.available or not isinstance(raw_bindings, (list, tuple)):
        return {}, {}
    raw_to_canonical: dict[str, str] = {}
    canonical_to_raw: dict[str, str] = {}
    for binding in raw_bindings:
        if not isinstance(binding, Mapping) or set(binding) != {
            "source_map_item_semantic_sha256",
            "source_item_semantic_sha256",
        }:
            raise ValueError("saved semantic source binding is malformed")
        raw_digest = str(binding["source_map_item_semantic_sha256"]).strip().lower()
        canonical_digest = str(binding["source_item_semantic_sha256"]).strip().lower()
        if (
            not re.fullmatch(r"[0-9a-f]{64}", raw_digest)
            or not re.fullmatch(r"[0-9a-f]{64}", canonical_digest)
            or raw_digest in raw_to_canonical
            or canonical_digest in canonical_to_raw
        ):
            raise ValueError("saved semantic source bindings are not a bijection")
        raw_to_canonical[raw_digest] = canonical_digest
        canonical_to_raw[canonical_digest] = raw_digest
    expected_total = int((authorization.coverage_counts or {}).get("total", -1))
    if not raw_to_canonical or len(raw_to_canonical) != expected_total:
        raise ValueError(
            "saved semantic source binding count disagrees with coverage total"
        )
    return raw_to_canonical, canonical_to_raw


def scoped_source_rows(
    payload: dict[str, Any] | None,
    *,
    folder: Path | None = None,
    accept_implicit_default: bool = False,
    reuse_authorization: SavedSidecarReuseAuthorization | None = None,
) -> tuple[dict[str, dict[str, Any]], str, str]:
    """Project report ledgers through the audit's semantic source scope.

    The report must not silently turn a named-theory closeout into a deep prose
    audit.  Conversely, malformed explicit scope metadata stays visible by
    rendering the full inventory with a warning instead of dropping rows.
    """

    all_rows = keyed_items(payload)
    if not isinstance(payload, dict):
        return all_rows, "named_theoretical_statements", ""
    mode, mode_error = source_coverage_mode_from_map(payload)
    if mode_error:
        return all_rows, mode, mode_error
    reuse_available = bool(
        reuse_authorization is not None and reuse_authorization.available
    )
    migration_error = source_coverage_mode_migration_error(
        payload,
        require_explicit=bool(all_rows),
    )
    if migration_error and not (accept_implicit_default or reuse_available):
        return all_rows, mode, migration_error
    if reuse_available:
        assert reuse_authorization is not None
        raw_to_canonical, _canonical_to_raw = reuse_coverage_binding_maps(
            reuse_authorization
        )
        selected: dict[str, dict[str, Any]] = {}
        selected_raw_digests: set[str] = set()
        for item_id, row in all_rows.items():
            raw_digest = source_item_coverage_sha256(row, mode)
            if raw_digest not in raw_to_canonical:
                continue
            if raw_digest in selected_raw_digests:
                raise ValueError(
                    "saved semantic source identity matches multiple current map rows"
                )
            selected[item_id] = row
            selected_raw_digests.add(raw_digest)
        if selected_raw_digests != set(raw_to_canonical):
            raise ValueError(
                "saved semantic source surface does not match current map semantics"
            )
        return selected, mode, ""
    selected = filter_source_map_items_for_coverage(
        payload.get("items"),
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            payload
        ),
    )
    if folder is not None:
        raw_items = payload.get("items")
        presentation_aliases, _alias_errors = source_presentation_aliases(raw_items)
        byte_pinned_item_ids = source_index_byte_pinned_anchor_item_ids(
            folder,
            payload,
            mode,
            repository_root=ROOT,
        )
        for item_id, row in all_rows.items():
            if item_id in byte_pinned_item_ids and item_id not in presentation_aliases:
                selected[item_id] = row
        for item_id, row in all_rows.items():
            if source_item_has_explicit_nonordinary_obligation(row):
                selected[item_id] = row
    return selected, mode, ""


def explicitly_selected_formula_provenance_target(row: object) -> bool:
    """Whether one formula/equation is an explicit supplemental report target.

    Normal named-theory coverage deliberately excludes standalone displays.
    The formula-provenance appendix must nevertheless show a display when the
    source map explicitly says it is claim-bearing *and* gives it a complete
    source-to-``Spec``/evidence contract.  This is a presentation projection:
    it does not make the display a normal coverage obligation or infer one
    from a map key, source title, or Lean declaration name.
    """

    if not isinstance(row, Mapping):
        return False
    if first_text(row, "source_kind").lower() not in FORMULA_SOURCE_KINDS:
        return False
    if row.get("claim_bearing") is not True:
        return False
    contract = row.get("semantic_contract")
    if not isinstance(contract, Mapping):
        return False
    return (
        all(
            isinstance(contract.get(field), str)
            and str(contract[field]).strip()
            for field in (
                "spec_declaration",
                "evidence_declaration",
                "semantic_shape",
            )
        )
        and str(contract.get("evidence_mode") or "").strip()
        in SEMANTIC_CONTRACT_EVIDENCE_MODES
    )


def formula_provenance_rows(
    source_payload: dict[str, Any] | None,
    scoped_rows: dict[str, dict[str, Any]],
) -> tuple[dict[str, dict[str, Any]], frozenset[str]]:
    """Add explicit supplemental formula targets without changing coverage.

    ``scoped_rows`` remains the exact normal/deep source-coverage projection.
    The second return value identifies the rows added solely for the formula
    appendix, so callers never accidentally use a normal-coverage receipt to
    describe them as ordinary named results.
    """

    rows = dict(scoped_rows)
    supplemental: set[str] = set()
    for identity, row in keyed_items(source_payload).items():
        if not explicitly_selected_formula_provenance_target(row):
            continue
        if identity not in rows:
            supplemental.add(identity)
        rows[identity] = row
    return rows, frozenset(supplemental)


def count_field(payload: dict[str, Any] | None, field: str) -> Counter[str]:
    counts: Counter[str] = Counter()
    for item in items(payload):
        if field not in item:
            continue
        value = item[field]
        if isinstance(value, str):
            value = value.strip()
            if not value:
                continue
        if isinstance(value, (str, int, bool)) or value is None:
            counts[str(value)] += 1
    return counts


def ordered_counts(counts: Counter[str], preferred: list[str]) -> str:
    if not counts:
        return "no rows"
    keys = [key for key in preferred if key in counts]
    keys.extend(sorted(key for key in counts if key not in set(keys)))
    human_counts: Counter[str] = Counter()
    human_order: list[str] = []
    for key in keys:
        label = DISPLAY_LABELS.get(key, "result needing review")
        if label not in human_counts:
            human_order.append(label)
        human_counts[label] += counts[key]
    return ", ".join(f"{human_counts[label]} {label}" for label in human_order)


def rel(folder: Path, path: Path | None) -> str:
    if path is None:
        return ""
    return path.relative_to(folder).as_posix()


def plural(value: int, singular: str, plural_word: str | None = None) -> str:
    return f"{value} {singular if value == 1 else (plural_word or singular + 's')}"


def first_text(payload: dict[str, Any] | None, *fields: str) -> str:
    if payload is None:
        return ""
    for field in fields:
        value = payload.get(field)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def row_value(
    row: dict[str, Any] | None,
    payload: dict[str, Any] | None,
    *fields: str,
) -> str:
    return first_text(row, *fields) or first_text(payload, *fields)


def explicit_non_evidence(
    payload: dict[str, Any] | None,
    row: dict[str, Any] | None = None,
) -> bool:
    for candidate in (payload, row):
        if not isinstance(candidate, dict):
            continue
        if candidate.get("non_evidence_scaffold") is True:
            return True
        if candidate.get("seed_scaffold") is True:
            return True
        if candidate.get("completed") is False:
            return True
    return False


def explicit_stale(
    payload: dict[str, Any] | None,
    row: dict[str, Any] | None = None,
) -> bool:
    for candidate in (row, payload):
        if not isinstance(candidate, dict):
            continue
        if candidate.get("stale") is True or candidate.get("is_stale") is True:
            return True
        if candidate.get("current") is False or candidate.get("is_current") is False:
            return True
        if first_text(candidate, "judgment") == "stale":
            return True
    return False


def validator_actor(raw_type: str) -> str:
    normalized = raw_type.strip().lower().replace("-", "_")
    if normalized in {"human", "human_dashboard", "author", "author_review"}:
        return "Human review"
    if "model" in normalized or "llm" in normalized:
        return "Model check"
    if "agent" in normalized or "codex" in normalized:
        return "Agent check"
    if "manual_semantic" in normalized or "semantic_review" in normalized:
        return "Recorded semantic check"
    if any(token in normalized for token in ("code", "automatic", "generator")):
        return "Automated check"
    return "Recorded check"


_MARKDOWN_LINK_RE = re.compile(r"\[([^\]]+)\]\([^\)]+\)")
_INTERNAL_ABSOLUTE_PATH_RE = re.compile(
    r"(?<![A-Za-z0-9])(?:/home|/tmp|/var/tmp|/private/tmp)/[^\s,;|)\]]+"
)
_INTERNAL_RELATIVE_PATH_RE = re.compile(
    r"(?<![A-Za-z0-9])(?:\.\./EconCSLib-(?:private|public)[^\s,;|)\]]*|"
    r"(?:\.scratch|\.review_traces)/[^\s,;|)\]]+)"
)


def human_text(value: Any, *, limit: int | None = None) -> str:
    """Render evidence prose without leaking machine enums or local paths."""

    if value is None:
        return ""
    text = str(value)
    text = _MARKDOWN_LINK_RE.sub(r"\1", text)
    text = _INTERNAL_ABSOLUTE_PATH_RE.sub("the internal source extraction", text)
    text = _INTERNAL_RELATIVE_PATH_RE.sub("an internal audit artifact", text)
    # Underscored values are unambiguously machine enums.  Plain words such as
    # ``exact`` or ``support`` also occur naturally in source prose and must not
    # be rewritten after they have already been rendered as human labels.
    machine_terms = (pair for pair in DISPLAY_LABELS.items() if "_" in pair[0])
    for raw, label in sorted(machine_terms, key=lambda pair: -len(pair[0])):
        text = re.sub(
            rf"(?<![A-Za-z0-9_]){re.escape(raw)}(?![A-Za-z0-9_])",
            label,
            text,
        )
    text = re.sub(r"\s+", " ", text).strip()
    # Semantic evidence must remain complete in the human-facing report.  The
    # retained argument keeps existing callers source-compatible, but display
    # width is a renderer concern and cannot justify dropping a premise or the
    # tail of a source statement.
    _ = limit
    return text


def table_cell(value: Any, *, limit: int | None = None) -> str:
    text = human_text(value, limit=limit)
    if not text:
        return "None recorded"
    return text.replace("|", r"\|")


def code_cell(values: list[str] | tuple[str, ...] | set[str]) -> str:
    cleaned: list[str] = []
    for value in values:
        if not isinstance(value, str) or not value.strip():
            continue
        rendered = value.strip().replace("`", "'").replace("|", r"\|")
        if rendered not in cleaned:
            cleaned.append(rendered)
    if not cleaned:
        return "None recorded"
    return "<br>".join(f"`{value}`" for value in cleaned)


def short_declaration(value: str) -> str:
    return value.rsplit(".", 1)[-1].strip()


def lookup_row(
    rows: dict[str, dict[str, Any]],
    identity: str,
) -> dict[str, Any] | None:
    if identity in rows:
        return rows[identity]
    short = short_declaration(identity)
    candidates = [row for key, row in rows.items() if short_declaration(key) == short]
    return candidates[0] if len(candidates) == 1 else None


def lookup_row_key(
    rows: dict[str, dict[str, Any]],
    identity: str,
) -> str | None:
    if identity in rows:
        return identity
    short = short_declaration(identity)
    candidates = [key for key in rows if short_declaration(key) == short]
    return candidates[0] if len(candidates) == 1 else None


def selected_coverage_rows_by_source(
    source_rows: dict[str, dict[str, Any]],
    coverage_payload: dict[str, Any] | None,
    coverage_mode: str,
    reuse: SavedSidecarReuseAuthorization,
) -> tuple[dict[str, dict[str, Any]], set[str]]:
    """Bind coverage rows to source rows by receipt semantics when reusing."""

    coverage_rows = keyed_items(coverage_payload)
    if not reuse.available:
        selected: dict[str, dict[str, Any]] = {}
        used: set[str] = set()
        for source_identity in source_rows:
            key = lookup_row_key(coverage_rows, source_identity)
            if key is not None:
                selected[source_identity] = coverage_rows[key]
                used.add(key)
        return selected, used

    raw_to_canonical, _canonical_to_raw = reuse_coverage_binding_maps(reuse)
    source_semantics: dict[str, str] = {}
    for source_identity, source_row in source_rows.items():
        raw_digest = source_item_coverage_sha256(source_row, coverage_mode)
        canonical_digest = raw_to_canonical.get(raw_digest)
        if canonical_digest is None:
            raise ValueError(
                "receipt-selected source row lacks a semantic source binding"
            )
        source_semantics[source_identity] = canonical_digest

    selected_canonical = set(source_semantics.values())
    coverage_by_canonical: dict[str, tuple[str, dict[str, Any]]] = {}
    for coverage_key, coverage_row in coverage_rows.items():
        recorded_digest = first_text(
            coverage_row,
            "source_item_coverage_sha256",
        ).lower()
        digest_schema = coverage_row.get("source_item_coverage_digest_schema")
        canonical_digest = ""
        if digest_schema == SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA:
            if not re.fullmatch(r"[0-9a-f]{64}", recorded_digest):
                if coverage_key in source_semantics:
                    raise ValueError(
                        "receipt-selected coverage row lacks a current semantic digest"
                    )
                continue
            canonical_digest = recorded_digest
        elif coverage_key in source_semantics:
            # Legacy receipt issuance permits exact navigation-key binding only.
            canonical_digest = source_semantics[coverage_key]
        if canonical_digest not in selected_canonical:
            continue
        if canonical_digest in coverage_by_canonical:
            raise ValueError(
                "multiple coverage rows match one receipt-selected source identity"
            )
        coverage_by_canonical[canonical_digest] = (coverage_key, coverage_row)

    if set(coverage_by_canonical) != selected_canonical:
        raise ValueError(
            "coverage rows do not form a semantic bijection over the saved source surface"
        )
    return (
        {
            source_identity: coverage_by_canonical[canonical_digest][1]
            for source_identity, canonical_digest in source_semantics.items()
        },
        {
            coverage_by_canonical[canonical_digest][0]
            for canonical_digest in selected_canonical
        },
    )


def humanize_identifier(value: str) -> str:
    text = re.sub(r"[_\-]+", " ", short_declaration(value)).strip()
    return text[:1].upper() + text[1:] if text else "Recorded row"


def validator_description(
    payload: dict[str, Any] | None,
    row: dict[str, Any] | None,
    outcome: str,
    *,
    missing: str,
) -> str:
    if row is None or explicit_non_evidence(payload, row):
        return missing

    validator = row_value(row, payload, "validator", "translator", "generator")
    validator_type = row_value(
        row,
        payload,
        "validator_type",
        "translator_type",
        "generator_type",
    )
    checked_at = row_value(
        row,
        payload,
        "validated_at",
        "translated_at",
        "generated_at",
    )
    checked_date = checked_at.split("T", 1)[0] if checked_at else ""
    if explicit_stale(payload, row):
        outcome = f"needs fresh review; prior result: {outcome}"

    details = [human_text(outcome)]
    actor = validator_actor(validator_type)
    if validator:
        details.append(f"{actor} by {human_text(validator)}")
    elif validator_type:
        details.append(actor)
    else:
        details.append("validator identity not recorded")
    if checked_date:
        details.append(checked_date)
    return "; ".join(detail for detail in details if detail)


def judgment_description(
    payload: dict[str, Any] | None,
    row: dict[str, Any] | None,
    labels: dict[str, str],
    *,
    field: str,
    missing: str,
) -> str:
    if row is None or explicit_non_evidence(payload, row):
        return missing
    raw = first_text(row, field)
    outcome = labels.get(raw, "needs review") if raw else "result not recorded"
    return validator_description(payload, row, outcome, missing=missing)


def reason_text(
    row: dict[str, Any] | None,
    *,
    extra: str = "",
    limit: int | None = None,
) -> str:
    parts: list[str] = []
    if row is not None:
        for field in ("reason", "resolution_reason", "comment", "source_note"):
            value = first_text(row, field)
            if value and value not in parts:
                parts.append(value)
    if extra:
        parts.append(extra)
    return human_text(" ".join(parts), limit=limit) or "None recorded"


def status_payload(folder: Path) -> dict[str, Any]:
    return load_json(folder / "status.json") or {}


def saved_report_reuse_authorization(
    folder: Path,
    status: dict[str, Any],
) -> SavedSidecarReuseAuthorization:
    """Return the same immutable saved-evidence authority used by status sync."""

    global _SAVED_REUSE_PROVIDER
    if _SAVED_REUSE_PROVIDER is None:
        _SAVED_REUSE_PROVIDER = LazySharedClosureProvider(ROOT)
    return saved_sidecar_reuse_authorization(
        folder,
        status,
        closure_provider=_SAVED_REUSE_PROVIDER,
    )


def saved_reuse_provenance(
    authorization: SavedSidecarReuseAuthorization,
) -> str:
    """Render an exact, human-facing immutable-receipt citation."""

    source_labels = {
        "verified_current_bytes": "canonical source bytes verified current",
        "structural_checkout_immutable_attestation": (
            "canonical source bytes certified by the immutable private issuance "
            "attestation for this structural checkout"
        ),
    }
    source = source_labels.get(
        authorization.canonical_source_state,
        "canonical source authority verified",
    )
    schema = authorization.receipt_schema
    digest = authorization.receipt_sha256
    receipt = (
        f"saved semantic receipt schema {schema} `{digest}`"
        if isinstance(schema, int) and digest
        else "saved semantic receipt"
    )
    return f"immutable {receipt}; {source}"


def saved_statement_count_text(counts: Any) -> tuple[str, int]:
    if not isinstance(counts, dict):
        return "", 0
    ordered = (
        ("matches", "exact match", "exact matches"),
        ("mismatch", "mismatch", "mismatches"),
        (
            "formalization_boundary",
            "formalization boundary",
            "formalization boundaries",
        ),
        ("uncertain", "item needing review", "items needing review"),
        ("unknown", "unknown item", "unknown items"),
    )
    parts = [
        plural(int(counts.get(key, 0)), singular, plural_word)
        for key, singular, plural_word in ordered
        if int(counts.get(key, 0))
    ]
    total = int(counts.get("total", 0))
    return ", ".join(parts) if parts else plural(total, "reviewed statement"), total


def saved_coverage_count_text(counts: Any) -> tuple[str, int]:
    if not isinstance(counts, dict):
        return "", 0
    ordered = (
        ("covered", "covered target", "covered targets"),
        (
            "corrected_target_covered",
            "corrected target covered",
            "corrected targets covered",
        ),
        ("conditional_boundary", "conditional boundary", "conditional boundaries"),
        ("support_only", "support-only item", "support-only items"),
        ("out_of_scope", "out-of-scope item", "out-of-scope items"),
        ("scope_exclusion", "approved scope exclusion", "approved scope exclusions"),
    )
    parts = [
        plural(int(counts.get(key, 0)), singular, plural_word)
        for key, singular, plural_word in ordered
        if int(counts.get(key, 0))
    ]
    total = int(counts.get("total", 0))
    return ", ".join(parts) if parts else plural(total, "source target"), total


def saved_reuse_ledger_note(
    folder: Path,
    status: dict[str, Any],
    *,
    lane: str,
    authorization: SavedSidecarReuseAuthorization | None = None,
) -> str:
    authorization = authorization or saved_report_reuse_authorization(folder, status)
    if not authorization.available:
        return ""
    if lane == "statement":
        counts, _total = saved_statement_count_text(authorization.statement_counts)
        subject = f"statement dispositions: {counts}"
    elif lane == "coverage":
        counts, _total = saved_coverage_count_text(authorization.coverage_counts)
        subject = f"source-coverage dispositions: {counts}"
    else:
        condition_count = int(
            (authorization.statement_counts or {}).get("source_condition_rows", 0)
        )
        subject = plural(condition_count, "configured source condition")
    return (
        "The current aggregate is authorized by "
        + saved_reuse_provenance(authorization)
        + f" ({subject}). The receipt binds semantic identities, dispositions, "
        "and counts. Validator names, dates, and explanatory prose below are "
        "recorded metadata outside that receipt; this generator does not relabel "
        "a legacy row as a newly executed check."
    )


def review_surface(status: dict[str, Any]) -> dict[str, Any]:
    value = status.get("review_surface", {})
    return value if isinstance(value, dict) else {}


def configured_names(status: dict[str, Any], *fields: str) -> list[str]:
    surface = review_surface(status)
    result: list[str] = []
    for field in fields:
        values = surface.get(field, [])
        if not isinstance(values, list):
            continue
        for value in values:
            if isinstance(value, str) and value.strip() and value not in result:
                result.append(value.strip())
    return result


def statement_digest(value: str) -> str:
    """Return the dashboard's whitespace-normalized statement digest."""

    normalized = re.sub(r"\s+", " ", value.strip())
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def semantic_sidecar_identity(
    row: dict[str, Any],
    fields: tuple[str, ...],
) -> tuple[str, ...] | None:
    values = tuple(first_text(row, field).lower() for field in fields)
    if not all(re.fullmatch(r"[0-9a-f]{64}", value) for value in values):
        return None
    return values


def semantic_sidecar_index(
    rows: dict[str, dict[str, Any]],
    fields: tuple[str, ...],
) -> dict[tuple[str, ...], list[tuple[str, dict[str, Any]]]]:
    """Index sidecar evidence by content identity without collapsing ambiguity."""

    result: dict[tuple[str, ...], list[tuple[str, dict[str, Any]]]] = {}
    for key, row in rows.items():
        identity = semantic_sidecar_identity(row, fields)
        if identity is not None:
            result.setdefault(identity, []).append((key, row))
    return result


def cache_review_rows(folder: Path) -> list[dict[str, Any]]:
    path = folder / ".review_traces" / "paper_interface_cache.json"
    if not path.exists():
        return []
    payload = load_json(path)
    if payload is None:
        return []
    raw_rows = payload.get("rows", [])
    if not isinstance(raw_rows, list):
        return []
    return [row for row in raw_rows if isinstance(row, dict)]


def routed_cache_row(
    rows: list[dict[str, Any]],
    configured_name: str,
) -> dict[str, Any] | None:
    """Use names only to route to one current cached semantic row."""

    def locators(row: dict[str, Any]) -> list[str]:
        return [
            value
            for field in ("name", "full_name")
            if (value := first_text(row, field))
        ]

    exact = [row for row in rows if configured_name in locators(row)]
    if len(exact) == 1:
        return exact[0]
    if exact:
        return None
    short = short_declaration(configured_name)
    candidates = [
        row
        for row in rows
        if any(short_declaration(value) == short for value in locators(row))
    ]
    return candidates[0] if len(candidates) == 1 else None


def current_statement_identity(row: dict[str, Any]) -> tuple[str, str, str] | None:
    signature = first_text(row, "lean_signature_sha256").lower()
    paper_statement = first_text(row, "paper_statement")
    translated_statement = first_text(row, "agent_statement")
    if not re.fullmatch(r"[0-9a-f]{64}", signature):
        return None
    if not paper_statement or not translated_statement:
        return None
    return (
        signature,
        statement_digest(paper_statement),
        statement_digest(translated_statement),
    )


def current_assumption_identities(
    row: dict[str, Any],
) -> set[tuple[str, str]]:
    paper_statement = first_text(row, "paper_statement")
    if not paper_statement:
        return set()
    paper_digest = statement_digest(paper_statement)
    return {
        (statement_digest(value), paper_digest)
        for field in ("interface_source", "lean_statement")
        if (value := first_text(row, field))
    }


def unique_semantic_candidate(
    index: dict[tuple[str, ...], list[tuple[str, dict[str, Any]]]],
    identities: set[tuple[str, ...]],
) -> tuple[str, dict[str, Any]] | None:
    candidates: dict[str, dict[str, Any]] = {}
    for identity in identities:
        for key, row in index.get(identity, []):
            candidates[key] = row
    if len(candidates) != 1:
        return None
    return next(iter(candidates.items()))


def receipt_bound_paper_statement(
    row: dict[str, Any],
    evidence: dict[str, dict[str, Any] | None],
) -> str:
    """Recover human source prose only through the receipt's statement digest."""

    paper_digest = first_text(row, "paper_statement_sha256").lower()
    if not re.fullmatch(r"[0-9a-f]{64}", paper_digest):
        return ""
    candidates: list[str] = []
    for source_row in keyed_items(evidence.get("source_map")).values():
        # This is evidence recovery, not presentation.  In particular, do not
        # turn a blank source-map item into a generated identifier and then
        # treat that identifier as source prose.
        statement = first_text(
            source_row,
            "statement",
            "paper_statement",
            "source_statement",
        )
        if statement and statement_digest(statement) == paper_digest:
            candidates.append(statement)
    for field in ("paper_statement", "source_statement"):
        statement = first_text(row, field)
        if statement and statement_digest(statement) == paper_digest:
            candidates.append(statement)
    raw_obligations = row.get("source_obligations", [])
    if isinstance(raw_obligations, list):
        for obligation in raw_obligations:
            if not isinstance(obligation, dict):
                continue
            statement = first_text(obligation, "statement")
            if statement and statement_digest(statement) == paper_digest:
                candidates.append(statement)
    unique = list(dict.fromkeys(candidates))
    return unique[0] if len(unique) == 1 else ""


def current_cache_lean_statement_digests(row: dict[str, Any]) -> set[str]:
    """Return all exact current Lean-text digests available to a cache row."""

    return {
        statement_digest(value)
        for field in ("interface_source", "lean_statement")
        if (value := first_text(row, field))
    }


def current_tex_bindings(
    row: dict[str, Any],
    tex_rows: dict[str, dict[str, Any]],
) -> list[tuple[str, dict[str, Any]]]:
    """Return all content-pinned current Lean-to-TeX receipts for one row.

    The cache supplies the current declaration text and elaborated signature.
    A translation must bind its exact Lean text; when it records a signature,
    that pin must agree as well. Storage keys are deliberately not selectors.
    Callers must preserve ambiguity rather than choosing a receipt arbitrarily.
    """

    signature = first_text(row, "lean_signature_sha256").lower()
    lean_digests = current_cache_lean_statement_digests(row)
    if not re.fullmatch(r"[0-9a-f]{64}", signature) or not lean_digests:
        return []

    candidates: list[tuple[str, dict[str, Any]]] = []
    for key, tex_row in tex_rows.items():
        lean_digest = first_text(tex_row, "lean_statement_sha256").lower()
        recorded_signature = first_text(tex_row, "lean_signature_sha256").lower()
        if lean_digest not in lean_digests or not first_text(
            tex_row,
            "tex_statement",
            "agent_statement",
        ):
            continue
        if recorded_signature:
            if (
                not re.fullmatch(r"[0-9a-f]{64}", recorded_signature)
                or recorded_signature != signature
            ):
                continue
        candidates.append((key, tex_row))
    return candidates


def materialize_current_statement_receipt(
    row: dict[str, Any],
    statement_rows: dict[str, dict[str, Any]],
    evidence: dict[str, dict[str, Any] | None],
    *,
    translated: str,
) -> tuple[dict[str, Any], str, dict[str, Any]] | None:
    """Bind one cache row to a uniquely content-pinned statement receipt.

    A statement receipt independently pins the elaborated signature, exact Lean
    expression, source expression, and reviewed translation. This permits a
    report to retain a completed statement check when the separate
    presentation-only Lean-to-TeX sidecar is stale, without treating that
    sidecar as evidence by name or manufacturing a translation receipt.
    """

    signature = first_text(row, "lean_signature_sha256").lower()
    lean_digests = current_cache_lean_statement_digests(row)
    if (
        not re.fullmatch(r"[0-9a-f]{64}", signature)
        or not lean_digests
        or not translated
    ):
        return None

    translated_digest = statement_digest(translated)
    receipt_candidates = [
        (key, judgment)
        for key, judgment in statement_rows.items()
        if first_text(judgment, "lean_signature_sha256").lower() == signature
        and first_text(judgment, "lean_statement_sha256").lower() in lean_digests
        and first_text(judgment, "tex_statement_sha256").lower() == translated_digest
        and re.fullmatch(
            r"[0-9a-f]{64}",
            first_text(judgment, "paper_statement_sha256").lower(),
        )
    ]
    if len(receipt_candidates) != 1:
        return None
    receipt_key, receipt = receipt_candidates[0]

    paper_digest = first_text(receipt, "paper_statement_sha256").lower()
    if paper_digest == statement_digest(""):
        return None
    cached_paper = first_text(row, "paper_statement")
    paper_statement = (
        cached_paper
        if cached_paper and statement_digest(cached_paper) == paper_digest
        else receipt_bound_paper_statement(receipt, evidence)
    )
    if not paper_statement or statement_digest(paper_statement) != paper_digest:
        return None

    materialized = dict(row)
    materialized["paper_statement"] = paper_statement
    materialized["agent_statement"] = translated
    if current_statement_identity(materialized) != (
        signature,
        paper_digest,
        translated_digest,
    ):
        return None
    return materialized, receipt_key, receipt


def materialize_current_statement_cache_row(
    row: dict[str, Any],
    statement_rows: dict[str, dict[str, Any]],
    tex_rows: dict[str, dict[str, Any]],
    evidence: dict[str, dict[str, Any] | None],
) -> tuple[
    dict[str, Any],
    str,
    dict[str, Any],
    str | None,
    dict[str, Any] | None,
] | None:
    """Rebind a current cache row only through exact semantic receipts.

    Cache prose is navigation data and can lag a source-map wording change.
    This helper prefers one current Lean-to-TeX receipt from the current
    declaration content, then chooses one statement judgment by current
    signature, Lean content, and translated text. If no current translation
    receipt exists, the cache translation can instead bind directly to the
    statement receipt's translation digest. That fallback is available only
    for a uniquely content-pinned statement receipt; a current translation
    ambiguity still fails closed. It accepts source prose only when its digest
    agrees with that judgment or an exact current source occurrence can recover
    it. It never selects evidence by declaration name.
    """

    signature = first_text(row, "lean_signature_sha256").lower()
    lean_digests = current_cache_lean_statement_digests(row)
    if not re.fullmatch(r"[0-9a-f]{64}", signature) or not lean_digests:
        return None

    tex_candidates = current_tex_bindings(row, tex_rows)
    if len(tex_candidates) > 1:
        return None
    if tex_candidates:
        tex_key, tex_row = tex_candidates[0]
        translated = first_text(tex_row, "tex_statement", "agent_statement")
        binding = materialize_current_statement_receipt(
            row,
            statement_rows,
            evidence,
            translated=translated,
        )
        if binding is None:
            return None
        materialized, receipt_key, receipt = binding
        return materialized, receipt_key, receipt, tex_key, tex_row

    # A direct statement judgment already binds the current cache translation
    # by digest. Do not infer a separate Lean-to-TeX receipt when its sidecar
    # is stale or absent.
    binding = materialize_current_statement_receipt(
        row,
        statement_rows,
        evidence,
        translated=first_text(row, "agent_statement"),
    )
    if binding is None:
        return None
    materialized, receipt_key, receipt = binding
    return materialized, receipt_key, receipt, None, None


def semantic_review_surface(
    folder: Path,
    status: dict[str, Any],
    evidence: dict[str, dict[str, Any] | None],
    *,
    cache_rows: tuple[dict[str, Any], ...] | list[dict[str, Any]] | None = None,
    reuse_authorization: SavedSidecarReuseAuthorization | None = None,
) -> dict[str, Any]:
    """Bind configured review rows to sidecars by exact semantic identity.

    Status names route to the cached current PaperInterface rows. They never
    select sidecar evidence directly. A digest collision, duplicate receipt,
    missing cache row, or stale semantic tuple therefore leaves the configured
    row unresolved and the raw sidecar entry diagnostic-only.
    """

    statement_rows = keyed_items(evidence["statement"])
    assumption_rows = keyed_items(evidence["assumption"])
    tex_rows = keyed_items(evidence["tex"])
    assumption_index = semantic_sidecar_index(
        assumption_rows,
        ("lean_statement_sha256", "paper_statement_sha256"),
    )
    tex_index = semantic_sidecar_index(tex_rows, ("lean_statement_sha256",))
    current_cache_rows = (
        list(cache_rows) if cache_rows is not None else cache_review_rows(folder)
    )

    statement_names = configured_names(
        status,
        "include_names",
        "source_definition_names",
    )
    condition_names = [
        name
        for name in configured_names(status, "assumption_names")
        if name not in statement_names
    ]
    # Configured names only navigate to the current cache.  A statement needs
    # a complete content-addressed binding before it participates in the
    # surface; a stale cache triple must not regain authority through the old
    # cache-only matcher below.
    desired_rows: list[
        tuple[
            str,
            str,
            dict[str, Any] | None,
            tuple[
                dict[str, Any],
                str,
                dict[str, Any],
                str | None,
                dict[str, Any] | None,
            ]
            | None,
            bool,
        ]
    ] = []
    for name in statement_names:
        raw_cache_row = routed_cache_row(current_cache_rows, name)
        binding = (
            materialize_current_statement_cache_row(
                raw_cache_row,
                statement_rows,
                tex_rows,
                evidence,
            )
            if raw_cache_row is not None
            else None
        )
        desired_rows.append(
            (
                "statement",
                name,
                binding[0] if binding is not None else None,
                binding,
                raw_cache_row is not None,
            )
        )
    desired_rows.extend(
        (
            "source_condition",
            name,
            routed_cache_row(current_cache_rows, name),
            None,
            routed_cache_row(current_cache_rows, name) is not None,
        )
        for name in condition_names
    )

    statement_identity_counts: Counter[tuple[str, str, str]] = Counter()
    assumption_identity_counts: Counter[tuple[str, str]] = Counter()
    for kind, _name, cache_row, _binding, _raw_cache_available in desired_rows:
        if cache_row is None:
            continue
        if kind == "statement":
            identity = current_statement_identity(cache_row)
            if identity is not None:
                statement_identity_counts[identity] += 1
        else:
            for identity in current_assumption_identities(cache_row):
                assumption_identity_counts[identity] += 1

    selected: list[dict[str, Any]] = []
    used_statement: set[str] = set()
    used_assumption: set[str] = set()
    used_tex: set[str] = set()
    for kind, name, cache_row, binding, raw_cache_available in desired_rows:
        result: dict[str, Any] = {
            "kind": kind,
            "name": name,
            "cache_row": cache_row,
            "statement_row": None,
            "assumption_row": None,
            "tex_row": None,
        }
        saved_reuse = bool(
            reuse_authorization is not None
            and reuse_authorization.available
            and not raw_cache_available
        )
        if cache_row is None and not saved_reuse:
            selected.append(result)
            continue

        if kind == "statement" and cache_row is not None and binding is not None:
            identity = current_statement_identity(cache_row)
            if identity is not None and statement_identity_counts[identity] == 1:
                _cache, statement_key, statement_row, tex_key, tex_row = binding
                result["statement_row"] = statement_row
                result["tex_row"] = tex_row
                used_statement.add(statement_key)
                if tex_key is not None:
                    used_tex.add(tex_key)
        elif kind == "source_condition" and cache_row is not None:
            identities = current_assumption_identities(cache_row)
            identities = {
                identity
                for identity in identities
                if assumption_identity_counts[identity] == 1
            }
            candidate = unique_semantic_candidate(assumption_index, identities)
            if candidate is not None:
                assumption_key, assumption_row = candidate
                result["assumption_row"] = assumption_row
                used_assumption.add(assumption_key)
        if (
            saved_reuse
            and result["statement_row" if kind == "statement" else "assumption_row"]
            is None
        ):
            # Names navigate to a row only after the immutable authorization has
            # independently validated its semantic identity and disposition.
            # This keeps structural/public checkouts useful without making the
            # ignored dashboard cache an acceptance credential.
            saved_rows = statement_rows if kind == "statement" else assumption_rows
            saved_row = saved_rows.get(name)
            fields = (
                (
                    "lean_signature_sha256",
                    "paper_statement_sha256",
                    "tex_statement_sha256",
                )
                if kind == "statement"
                else ("lean_statement_sha256", "paper_statement_sha256")
            )
            if saved_row is not None and semantic_sidecar_identity(saved_row, fields):
                result["statement_row" if kind == "statement" else "assumption_row"] = (
                    saved_row
                )
                (used_statement if kind == "statement" else used_assumption).add(name)
                recorded_paper_digest = first_text(
                    saved_row,
                    "paper_statement_sha256",
                ).lower()
                cached_paper_statement = first_text(
                    result["cache_row"],
                    "paper_statement",
                )
                if (
                    result["cache_row"] is None
                    or not cached_paper_statement
                    or statement_digest(cached_paper_statement) != recorded_paper_digest
                ):
                    result["cache_row"] = {
                        "name": name,
                        "full_name": name,
                        "paper_statement": receipt_bound_paper_statement(
                            saved_row,
                            evidence,
                        ),
                    }
                if kind == "statement":
                    recorded_lean = first_text(
                        saved_row,
                        "lean_statement_sha256",
                    ).lower()
                    tex_candidate = (
                        unique_semantic_candidate(tex_index, {(recorded_lean,)})
                        if re.fullmatch(r"[0-9a-f]{64}", recorded_lean)
                        else None
                    )
                    if tex_candidate is not None:
                        tex_key, tex_row = tex_candidate
                        result["tex_row"] = tex_row
                        used_tex.add(tex_key)
        selected.append(result)

    return {
        "rows": selected,
        "orphan_statement_keys": sorted(set(statement_rows) - used_statement),
        "orphan_assumption_keys": sorted(set(assumption_rows) - used_assumption),
        "orphan_tex_keys": sorted(set(tex_rows) - used_tex),
    }


def semantic_surface_row_for_navigation(
    surface_rows: list[dict[str, Any]],
    navigation: str,
) -> dict[str, Any] | None:
    """Route a recorded link to one configured semantic surface row."""

    def locators(selected: dict[str, Any]) -> set[str]:
        values = {str(selected.get("name") or "").strip()}
        cache_row = selected.get("cache_row")
        if isinstance(cache_row, dict):
            values.update(
                first_text(cache_row, field) for field in ("name", "full_name")
            )
        return {value for value in values if value}

    exact = [selected for selected in surface_rows if navigation in locators(selected)]
    if len(exact) == 1:
        return exact[0]
    if exact:
        return None
    short = short_declaration(navigation)
    candidates = [
        selected
        for selected in surface_rows
        if any(short_declaration(value) == short for value in locators(selected))
    ]
    return candidates[0] if len(candidates) == 1 else None


def row_local_semantic_statement_checks(
    row_names: list[str],
    statement_payload: dict[str, Any] | None,
    surface_rows: list[dict[str, Any]],
) -> str:
    if not row_names:
        return "No linked paper-facing row recorded"
    checks: list[str] = []
    for row_name in row_names:
        selected = semantic_surface_row_for_navigation(surface_rows, row_name)
        statement_row = (
            selected.get("statement_row")
            if selected is not None and selected.get("kind") == "statement"
            else None
        )
        checks.append(
            f"`{short_declaration(row_name)}`: "
            f"{statement_label(statement_payload, statement_row)}"
        )
    return "<br>".join(table_cell(check) for check in checks)


def merge_identities(primary: list[str], extra: dict[str, dict[str, Any]]) -> list[str]:
    result = list(primary)
    known = {short_declaration(value) for value in result}
    for value in extra:
        if short_declaration(value) not in known:
            result.append(value)
            known.add(short_declaration(value))
    return result


def source_map_lookup(
    source_rows: dict[str, dict[str, Any]],
    identity: str,
) -> tuple[str, dict[str, Any] | None]:
    direct = lookup_row_key(source_rows, identity)
    if direct is not None:
        return direct, source_rows[direct]

    short = short_declaration(identity)
    matches: list[tuple[str, dict[str, Any]]] = []
    for key, row in source_rows.items():
        candidates: list[str] = []
        for field in (
            "aliases",
            "lean_declarations",
            "proof_lean_declarations",
            "support_lean_declarations",
        ):
            values = row.get(field, [])
            if isinstance(values, list):
                candidates.extend(value for value in values if isinstance(value, str))
        if any(short_declaration(candidate) == short for candidate in candidates):
            matches.append((key, row))
    return matches[0] if len(matches) == 1 else (identity, None)


def canonical_sidecars(folder: Path) -> dict[str, dict[str, Any] | None]:
    return {
        key: load_json(sidecar(folder, filename))
        for key, filename in CANONICAL_SIDECAR_NAMES.items()
    }


def linked_review_rows(
    source_row: dict[str, Any],
    coverage_row: dict[str, Any] | None,
    allowed_rows: set[str],
) -> tuple[list[str], int]:
    candidates: list[str] = []
    if coverage_row is not None:
        values = coverage_row.get("review_rows", [])
        if isinstance(values, list):
            candidates.extend(value for value in values if isinstance(value, str))
    if not candidates:
        for field in ("lean_declarations", "proof_lean_declarations"):
            values = source_row.get(field, [])
            if isinstance(values, list):
                candidates.extend(value for value in values if isinstance(value, str))

    unique: list[str] = []
    omitted = 0
    allowed_short = {short_declaration(value) for value in allowed_rows}
    for candidate in candidates:
        if allowed_short and short_declaration(candidate) not in allowed_short:
            omitted += 1
            continue
        if candidate not in unique:
            unique.append(candidate)
    return unique, omitted


def markdown_table(headers: list[str], rows: list[list[str]]) -> str:
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    lines.extend("| " + " | ".join(row) + " |" for row in rows)
    return "\n".join(lines)


def source_record_audit_detail(record_audit: dict[str, Any] | None) -> str:
    """Summarize raw discovery and post-judgment resolution separately.

    A raw source-record receipt intentionally records discovered conclusion
    dependencies before the independent semantic-judgment sidecar resolves
    them.  Reporting only its row and boundary counts makes that distinction
    invisible and has led reports to describe discovery items as proof gaps.
    """

    if record_audit is None:
        return "source-record structural audit is not tracked"

    review_rows = record_audit.get("review_row_count")
    if not isinstance(review_rows, int):
        review_rows = record_audit.get("configured_review_row_count")
    configured_rows = record_audit.get("configured_review_row_count")
    boundary_count = record_audit.get("boundary_input_count")
    conclusion_count = record_audit.get("conclusion_dependency_count")
    recursive_count = record_audit.get("recursive_field_count")
    semantic_model_count = record_audit.get("semantic_model_item_count")
    unresolved_count = record_audit.get("unresolved_conclusion_dependency_count")
    recursion_count = record_audit.get("recursion_failure_count")

    parts: list[str] = []
    if isinstance(review_rows, int):
        row_text = plural(review_rows, "source-record review row")
        if isinstance(configured_rows, int) and configured_rows != review_rows:
            row_text += f" (from {configured_rows} configured review-surface rows)"
        parts.append(row_text)
    if isinstance(boundary_count, int):
        parts.append(plural(boundary_count, "boundary input"))
    if isinstance(conclusion_count, int):
        parts.append(
            plural(
                conclusion_count,
                "conclusion dependency",
                "conclusion dependencies",
            )
        )
    if isinstance(recursive_count, int):
        parts.append(plural(recursive_count, "recursive field"))
    if isinstance(semantic_model_count, int):
        parts.append(plural(semantic_model_count, "semantic-model record"))
    if isinstance(unresolved_count, int):
        parts.append(
            plural(
                unresolved_count,
                "source-record-only unresolved conclusion dependency",
                "source-record-only unresolved conclusion dependencies",
            )
        )
    if isinstance(recursion_count, int):
        parts.append(plural(recursion_count, "recursion failure"))
    return ", ".join(parts) if parts else "tracked"


def sidecar_summary(
    folder: Path,
    *,
    snapshot: ReportInputSnapshot | None = None,
    reuse_authorization: SavedSidecarReuseAuthorization | None = None,
    semantic_surface: dict[str, Any] | None = None,
) -> dict[str, str]:
    if snapshot is None:
        paths = {
            key: sidecar(folder, name)
            for key, name in {
                **CANONICAL_SIDECAR_NAMES,
                **SUMMARY_SIDECAR_NAMES,
            }.items()
        }
        coverage = load_json(paths["coverage"])
        source_map = load_json(paths["source_map"])
        statement = load_json(paths["statement"])
        tex = load_json(paths["tex"])
        assumption = load_json(paths["assumption"])
        record_match = load_json(paths["record_match"])
        review = load_json(paths["review"])
        record_audit = load_json(paths["record_audit"])
        status = status_payload(folder)
        cache_rows = None
    else:
        paths = snapshot.sidecar_paths
        coverage = snapshot.evidence["coverage"]
        source_map = snapshot.evidence["source_map"]
        statement = snapshot.evidence["statement"]
        tex = snapshot.evidence["tex"]
        assumption = snapshot.evidence["assumption"]
        record_match = snapshot.record_match
        review = snapshot.evidence["review"]
        record_audit = snapshot.record_audit
        status = snapshot.status
        cache_rows = snapshot.cache_rows
    coverage_path = paths["coverage"]
    statement_path = paths["statement"]
    tex_path = paths["tex"]
    assumption_path = paths["assumption"]
    record_match_path = paths["record_match"]
    review_path = paths["review"]
    record_audit_path = paths["record_audit"]
    reuse = reuse_authorization or saved_report_reuse_authorization(folder, status)
    surface = (
        {
            "rows": [],
            "orphan_statement_keys": [],
            "orphan_assumption_keys": [],
            "orphan_tex_keys": [],
        }
        if reuse.available
        else (
            semantic_surface
            if semantic_surface is not None
            else semantic_review_surface(
                folder,
                status,
                {
                    "assumption": assumption,
                    "statement": statement,
                    "tex": tex,
                    "source_map": source_map,
                },
                cache_rows=cache_rows,
            )
        )
    )

    if reuse.available:
        coverage_count_text, _coverage_total = saved_coverage_count_text(
            reuse.coverage_counts
        )
        provenance = saved_reuse_provenance(reuse)
        coverage_text = f"source coverage has {coverage_count_text} under {provenance}"
        coverage_detail = f"{coverage_count_text}; {provenance}"
    elif coverage is None:
        coverage_text = "source coverage sidecar is not tracked"
        coverage_detail = "source coverage sidecar is not tracked"
    else:
        source_rows, _coverage_mode, coverage_scope_error = scoped_source_rows(
            source_map,
            folder=folder,
        )
        coverage_rows = keyed_items(coverage)
        selected_coverage_rows: list[dict[str, Any]] = []
        used_coverage_keys: set[str] = set()
        for source_identity in source_rows:
            coverage_key = lookup_row_key(coverage_rows, source_identity)
            if coverage_key is None:
                continue
            used_coverage_keys.add(coverage_key)
            selected_coverage_rows.append(coverage_rows[coverage_key])
        coverage_counts: Counter[str] = Counter(
            first_text(row, "coverage")
            for row in selected_coverage_rows
            if first_text(row, "coverage")
        )
        coverage_count_text = ordered_counts(
            coverage_counts,
            COVERAGE_ORDER,
        )
        coverage_diagnostics: list[str] = []
        missing_coverage = len(source_rows) - len(selected_coverage_rows)
        if missing_coverage:
            coverage_diagnostics.append(
                plural(
                    missing_coverage, "selected source row without coverage evidence"
                )
            )
        orphan_coverage = len(set(coverage_rows) - used_coverage_keys)
        if orphan_coverage:
            coverage_diagnostics.append(
                plural(orphan_coverage, "out-of-scope/orphan coverage row")
                + " excluded"
            )
        if coverage_scope_error:
            coverage_diagnostics.append(
                "full inventory shown because " + coverage_scope_error
            )
        coverage_diagnostic_text = (
            "; diagnostics: " + ", ".join(coverage_diagnostics)
            if coverage_diagnostics
            else ""
        )
        coverage_text = f"source coverage has {coverage_count_text}"
        coverage_text += coverage_diagnostic_text
        coverage_detail = coverage_count_text + coverage_diagnostic_text

    selected_statement_rows = [
        row["statement_row"]
        for row in surface["rows"]
        if row["kind"] == "statement" and row["statement_row"] is not None
    ]
    selected_condition_rows = [
        row["assumption_row"]
        for row in surface["rows"]
        if row["kind"] == "source_condition" and row["assumption_row"] is not None
    ]
    unresolved_surface_rows = sum(
        row["statement_row" if row["kind"] == "statement" else "assumption_row"] is None
        for row in surface["rows"]
    )
    diagnostic_parts: list[str] = []
    orphan_statement_count = len(surface["orphan_statement_keys"])
    orphan_assumption_count = len(surface["orphan_assumption_keys"])
    if orphan_statement_count:
        diagnostic_parts.append(
            plural(
                orphan_statement_count,
                "orphan/stale statement-sidecar row",
            )
            + " excluded"
        )
    if orphan_assumption_count:
        diagnostic_parts.append(
            plural(
                orphan_assumption_count,
                "orphan/stale source-condition sidecar row",
            )
            + " excluded"
        )
    if unresolved_surface_rows:
        diagnostic_parts.append(
            plural(
                unresolved_surface_rows,
                "configured row without an unambiguous current receipt",
                "configured rows without unambiguous current receipts",
            )
        )
    diagnostic_text = (
        "; diagnostics: " + ", ".join(diagnostic_parts) if diagnostic_parts else ""
    )

    if reuse.available:
        statement_count_text, _statement_total = saved_statement_count_text(
            reuse.statement_counts
        )
        condition_count = int(
            (reuse.statement_counts or {}).get("source_condition_rows", 0)
        )
        condition_text = (
            f"; {plural(condition_count, 'configured source condition')}"
            if condition_count
            else "; no configured source-condition rows"
        )
        provenance = saved_reuse_provenance(reuse)
        statement_text = (
            "statement semantic review has "
            f"{statement_count_text}{condition_text} under {provenance}"
        )
        statement_detail = f"{statement_count_text}{condition_text}; {provenance}"
    elif statement is None and not selected_condition_rows:
        statement_text = "statement LLM-as-judge sidecar is not tracked"
        statement_detail = statement_text + diagnostic_text
    else:
        judgment_counts: Counter[str] = Counter(
            first_text(row, "judgment")
            for row in selected_statement_rows
            if first_text(row, "judgment")
        )
        judgment_text = ordered_counts(
            judgment_counts,
            STATEMENT_ORDER,
        )
        resolution_counts: Counter[str] = Counter(
            first_text(row, "resolution")
            for row in selected_statement_rows
            if first_text(row, "resolution")
        )
        resolution_text = ""
        if resolution_counts:
            resolution_text = (
                f"; resolutions: "
                f"{ordered_counts(resolution_counts, ['visible_premise_boundary', 'conditional_boundary'])}"
            )
        condition_counts: Counter[str] = Counter(
            first_text(row, "judgment")
            for row in selected_condition_rows
            if first_text(row, "judgment")
        )
        condition_text = ""
        if condition_counts:
            condition_text = "; source conditions: " + ordered_counts(
                condition_counts, ASSUMPTION_ORDER
            )
        statement_text = (
            f"statement LLM-as-judge has {judgment_text}{resolution_text}"
            f"{condition_text}{diagnostic_text}"
        )
        statement_detail = (
            f"{judgment_text}{resolution_text}{condition_text}{diagnostic_text}"
        )

    if tex is None:
        tex_text = "Lean-to-TeX translation sidecar is not tracked"
        tex_detail = tex_text
    else:
        tex_detail = f"{plural(len(items(tex)), 'row translation')} generated from Lean statements"
        tex_text = f"Lean-to-TeX has {plural(len(items(tex)), 'row translation')}"
        qualifier = (
            "; recorded translation metadata, whose independent freshness is not "
            "established by "
            + (
                "the saved semantic receipt"
                if reuse.available
                else "this report generator"
            )
        )
        tex_detail += qualifier
        tex_text += qualifier

    configured_condition_rows = [
        row for row in surface["rows"] if row["kind"] == "source_condition"
    ]
    assumption_diagnostics: list[str] = []
    if orphan_assumption_count:
        assumption_diagnostics.append(
            plural(
                orphan_assumption_count,
                "unconfigured, stale, or ambiguous source-condition sidecar row",
            )
            + " excluded"
        )
    unresolved_condition_rows = sum(
        row["assumption_row"] is None for row in configured_condition_rows
    )
    if unresolved_condition_rows:
        assumption_diagnostics.append(
            plural(
                unresolved_condition_rows,
                "configured source condition without an unambiguous current receipt",
                "configured source conditions without unambiguous current receipts",
            )
        )
    assumption_diagnostic_text = (
        "; diagnostics: " + ", ".join(assumption_diagnostics)
        if assumption_diagnostics
        else ""
    )
    if reuse.available:
        condition_count = int(
            (reuse.statement_counts or {}).get("source_condition_rows", 0)
        )
        provenance = saved_reuse_provenance(reuse)
        assumption_detail = (
            f"{plural(condition_count, 'configured source condition')}; {provenance}"
            if condition_count
            else f"no configured source-condition rows; {provenance}"
        )
        assumption_text = f"assumption provenance has {assumption_detail}"
    elif assumption is None:
        assumption_text = "assumption provenance sidecar is not tracked"
        assumption_detail = (
            "no assumption-match sidecar tracked for this paper"
            + assumption_diagnostic_text
        )
    else:
        assumption_counts: Counter[str] = Counter(
            first_text(row, "judgment")
            for row in selected_condition_rows
            if first_text(row, "judgment")
        )
        if assumption_counts:
            assumption_detail = (
                ordered_counts(assumption_counts, ASSUMPTION_ORDER)
                + assumption_diagnostic_text
            )
            assumption_text = f"assumption provenance has {assumption_detail}"
        else:
            empty_assumption_detail = (
                "no current configured source-condition receipts"
                if configured_condition_rows
                else "no configured source-condition rows"
            )
            assumption_detail = empty_assumption_detail
            assumption_detail += assumption_diagnostic_text
            assumption_text = (
                "assumption provenance sidecar has "
                + empty_assumption_detail
                + assumption_diagnostic_text
            )

    if record_match is None:
        record_match_text = "source-record classification sidecar is not tracked"
        record_match_detail = (
            "no source-record classification sidecar tracked for this paper"
        )
    else:
        record_counts = count_field(record_match, "classification")
        if record_counts:
            record_match_detail = ordered_counts(record_counts, SOURCE_RECORD_ORDER)
            record_match_text = (
                f"source-record classification has {record_match_detail}"
            )
        else:
            record_match_text = "source-record classification sidecar has no rows"
            record_match_detail = "no rows"
        qualifier = (
            "; recorded sidecar metadata, whose independent freshness is not "
            "established by "
            + (
                "the saved semantic receipt"
                if reuse.available
                else "this report generator"
            )
        )
        record_match_detail += qualifier
        record_match_text += qualifier

    if record_audit is None:
        record_audit_text = "source-record structural audit is not tracked"
        record_audit_detail = record_audit_text
    else:
        record_audit_detail = source_record_audit_detail(record_audit)
        record_audit_text = "source-record audit reports " + record_audit_detail
        qualifier = (
            "; recorded structural metadata, whose independent freshness is not "
            "established by "
            + (
                "the saved semantic receipt"
                if reuse.available
                else "this report generator"
            )
        )
        record_audit_detail += qualifier
        record_audit_text += qualifier

    if review is None:
        review_text = "review-surface audit is not tracked"
        review_detail = review_text
    else:
        raw_judgment = first_text(review, "judgment")
        judgment = REVIEW_LABELS.get(raw_judgment, "needs review")
        review_rows = review.get("review_rows")
        if isinstance(review_rows, int):
            review_text = f"review-surface audit {judgment} over {plural(review_rows, 'review row')}"
            review_detail = f"{judgment} over {plural(review_rows, 'review row')}"
        else:
            review_text = f"review-surface audit {judgment}"
            review_detail = str(judgment)
        qualifier = (
            "; recorded review-surface metadata, whose independent freshness is not "
            "established by "
            + (
                "the saved semantic receipt"
                if reuse.available
                else "this report generator"
            )
        )
        review_text += qualifier
        review_detail += qualifier

    return {
        "coverage": coverage_text,
        "coverage_detail": detail_line(
            "Source coverage",
            coverage_path,
            folder,
            coverage_detail,
        ),
        "statement": statement_text,
        "statement_detail": detail_line(
            "Statement match",
            statement_path,
            folder,
            statement_detail,
        ),
        "tex": tex_text,
        "tex_detail": detail_line(
            "Lean-to-TeX translations",
            tex_path,
            folder,
            tex_detail,
        ),
        "assumption": assumption_text,
        "assumption_detail": detail_line(
            "Assumption provenance",
            assumption_path,
            folder,
            assumption_detail,
        ),
        "record_match": record_match_text,
        "record_match_detail": detail_line(
            "Source-record classification",
            record_match_path,
            folder,
            record_match_detail,
        ),
        "record_audit": record_audit_text,
        "record_audit_detail": detail_line(
            "Source-record structural audit",
            record_audit_path,
            folder,
            record_audit_detail,
        ),
        "review": review_text,
        "review_detail": detail_line(
            "Review-surface audit",
            review_path,
            folder,
            review_detail,
        ),
    }


def detail_line(label: str, path: Path | None, folder: Path, text: str) -> str:
    if path is None:
        return f"- {label}: {text}."
    return f"- {label} (`{rel(folder, path)}`): {text}."


def audit_summary_line(summary: dict[str, str]) -> str:
    return (
        "- Audit summary: "
        f"{summary['coverage']}; "
        f"{summary['statement']}; "
        f"{summary['tex']}; "
        f"{summary['assumption']}; "
        f"{summary['record_match']}; "
        f"{summary['record_audit']}; "
        f"{summary['review']}; "
        "holistic source-first audit status is not inferred by this generator; "
        f"DAG/source-json audit status is not inferred (see `{DAG_AUDIT}`)."
    )


def result_block(summary: dict[str, str]) -> str:
    lines = [
        BEGIN,
        "### LLM-as-Judge Results",
        summary["coverage_detail"],
        summary["statement_detail"],
        summary["tex_detail"],
        summary["assumption_detail"],
        summary["record_match_detail"],
        summary["record_audit_detail"],
        summary["review_detail"],
        "- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.",
        f"- DAG/source/source-json audit (`{DAG_AUDIT}`): status not inferred by this generator.",
        END,
    ]
    return "\n".join(lines)


def source_statement_text(identity: str, row: dict[str, Any] | None) -> str:
    if row is None:
        return humanize_identifier(identity)
    statement = first_text(row, "statement", "paper_statement", "source_statement")
    return statement or humanize_identifier(identity)


def coverage_label(
    payload: dict[str, Any] | None,
    row: dict[str, Any] | None,
) -> str:
    if row is None or explicit_non_evidence(payload, row):
        return "no completed coverage check"
    raw = first_text(row, "coverage", "classification")
    return COVERAGE_LABELS.get(raw, "needs review") if raw else "needs review"


def statement_label(
    payload: dict[str, Any] | None,
    row: dict[str, Any] | None,
) -> str:
    if row is None or explicit_non_evidence(payload, row):
        return "no completed statement check"
    raw = first_text(row, "judgment")
    label = STATEMENT_LABELS.get(raw, "needs review") if raw else "needs review"
    resolution = first_text(row, "resolution")
    if resolution:
        resolution_label = RESOLUTION_LABELS.get(resolution, "recorded resolution")
        label = f"{label}; {resolution_label}"
    if explicit_stale(payload, row):
        return f"needs fresh review; prior result: {label}"
    return label


def statement_validator_description(
    payload: dict[str, Any] | None,
    row: dict[str, Any] | None,
) -> str:
    missing = "No completed statement check recorded"
    if row is None or explicit_non_evidence(payload, row):
        return missing
    outcome = statement_label(payload, row)
    # statement_label already reports an explicit stale state, so avoid adding
    # a second stale prefix in the shared validator formatter.
    if explicit_stale(payload, row):
        clean_payload = dict(payload or {})
        clean_row = dict(row)
        for candidate in (clean_payload, clean_row):
            candidate.pop("stale", None)
            candidate.pop("is_stale", None)
            candidate.pop("current", None)
            candidate.pop("is_current", None)
        if clean_row.get("judgment") == "stale":
            clean_row["judgment"] = ""
        return validator_description(clean_payload, clean_row, outcome, missing=missing)
    return validator_description(payload, row, outcome, missing=missing)


def row_local_statement_checks(
    row_names: list[str],
    statement_payload: dict[str, Any] | None,
    statement_rows: dict[str, dict[str, Any]],
) -> str:
    if not row_names:
        return "No linked paper-facing row recorded"
    checks: list[str] = []
    for row_name in row_names:
        row = lookup_row(statement_rows, row_name)
        checks.append(
            f"`{short_declaration(row_name)}`: "
            f"{statement_label(statement_payload, row)}"
        )
    return "<br>".join(table_cell(check) for check in checks)


def premise_check_summary(row: dict[str, Any] | None) -> str:
    if row is None:
        return ""
    raw = row.get("premise_judgments", {})
    if not isinstance(raw, dict):
        return ""
    counts: Counter[str] = Counter()
    for value in raw.values():
        if not isinstance(value, dict):
            continue
        judgment = first_text(value, "judgment")
        if judgment:
            counts[judgment] += 1
    if not counts:
        return ""
    return "Premise-level checks: " + ordered_counts(
        counts,
        list(ASSUMPTION_LABELS),
    )


def source_location_and_statement(
    source_row: dict[str, Any] | None,
    evidence_row: dict[str, Any] | None = None,
) -> str:
    location = first_text(evidence_row, "source_location") or first_text(
        source_row,
        "source_location",
    )
    statement = first_text(
        source_row,
        "statement",
        "paper_statement",
        "source_statement",
    )
    parts: list[str] = []
    if location:
        parts.append(f"Source location: {location}")
    if statement:
        parts.append(statement)
    return table_cell(". ".join(parts), limit=480)


def human_review_summary(
    status: dict[str, Any],
    row_count: int,
    *,
    reuse: SavedSidecarReuseAuthorization | None = None,
) -> str:
    if "human_review" not in status:
        return (
            "Independent human dashboard review is not recorded; this table "
            "does not infer any human approval."
        )
    try:
        counts = validated_human_review_counts(
            status,
            expected_total=row_count,
        )
    except ValueError:
        return (
            "Independent human dashboard review counts are invalid or do not "
            "match the current semantic surface; no human approval is inferred."
        )
    reviewed = counts["reviewed_rows"]
    total = counts["total_rows"]
    if reviewed == 0:
        return (
            f"Independent human dashboard review: 0/{total} rows. No human "
            "row-level approval is inferred."
        )
    return (
        f"Independent human dashboard review: {reviewed}/{total} rows in the "
        "aggregate status. Row assignments are not inferred from that counter."
    )


def assumption_ledger(
    folder: Path,
    status: dict[str, Any],
    evidence: dict[str, dict[str, Any] | None],
    *,
    reuse: SavedSidecarReuseAuthorization,
    cache_rows: tuple[dict[str, Any], ...] | None = None,
    semantic_surface: dict[str, Any] | None = None,
) -> str:
    assumption_payload = evidence["assumption"]
    surface = (
        semantic_surface
        if semantic_surface is not None
        else semantic_review_surface(
            folder,
            status,
            evidence,
            cache_rows=cache_rows,
            reuse_authorization=reuse,
        )
    )
    condition_rows = [
        selected
        for selected in surface["rows"]
        if selected["kind"] == "source_condition"
    ]

    table_rows: list[list[str]] = []
    for selected in condition_rows:
        identity = selected["name"]
        assumption_row = selected["assumption_row"]
        cache_row = selected["cache_row"]
        paper_statement = (
            first_text(cache_row, "paper_statement")
            if isinstance(cache_row, dict)
            else ""
        )
        semantic_source_row = (
            {"statement": paper_statement} if paper_statement else None
        )
        judgment = judgment_description(
            assumption_payload,
            assumption_row,
            ASSUMPTION_LABELS,
            field="judgment",
            missing="No completed assumption check recorded",
        )
        premise_summary = premise_check_summary(assumption_row)
        comment = reason_text(assumption_row, extra=premise_summary)
        table_rows.append(
            [
                table_cell(humanize_identifier(identity)),
                code_cell([identity]),
                source_location_and_statement(semantic_source_row, assumption_row),
                table_cell(judgment),
                table_cell(comment),
            ]
        )

    if not table_rows:
        table_rows.append(
            [
                "None",
                "`none`",
                "None",
                "None",
                "No paper-facing assumption declarations are configured.",
            ]
        )

    intro = (
        "### Current Canonical Evidence\n"
        "Generated from the configured source-condition surface and exact "
        "current statement digests in the canonical assumption-provenance "
        "sidecar. Model, agent, and "
        "automated checks are identified as such; no human review is inferred."
    )
    if reuse_note := saved_reuse_ledger_note(
        folder,
        status,
        lane="assumption",
        authorization=reuse,
    ):
        intro += " " + reuse_note
    orphan_count = len(surface["orphan_assumption_keys"])
    if orphan_count:
        intro += (
            " Diagnostic-only evidence excluded from this ledger: "
            + plural(
                orphan_count,
                "unconfigured, stale, or ambiguous source-condition sidecar row",
            )
            + "."
        )
    return (
        intro
        + "\n\n"
        + markdown_table(
            [
                "Assumption declaration",
                "Lean declaration",
                "Source location / statement",
                "Assumption validators",
                "Comments",
            ],
            table_rows,
        )
    )


def formula_ledger(
    folder: Path,
    status: dict[str, Any],
    evidence: dict[str, dict[str, Any] | None],
    *,
    reuse: SavedSidecarReuseAuthorization,
    cache_rows: tuple[dict[str, Any], ...] | None = None,
    semantic_surface: dict[str, Any] | None = None,
) -> str:
    source_payload = evidence["source_map"]
    covered_source_rows, coverage_mode, scope_error = scoped_source_rows(
        source_payload,
        folder=folder,
        reuse_authorization=reuse,
    )
    source_rows, supplemental_formula_ids = formula_provenance_rows(
        source_payload,
        covered_source_rows,
    )
    coverage_payload = evidence["coverage"]
    coverage_by_source, _used_coverage_keys = selected_coverage_rows_by_source(
        covered_source_rows,
        coverage_payload,
        coverage_mode,
        reuse,
    )
    statement_payload = evidence["statement"]
    surface = (
        semantic_surface
        if semantic_surface is not None
        else semantic_review_surface(
            folder,
            status,
            evidence,
            cache_rows=cache_rows,
            reuse_authorization=reuse,
        )
    )
    surface_rows = surface["rows"]
    allowed_rows = {selected["name"] for selected in surface_rows}

    table_rows: list[list[str]] = []
    for identity, source_row in source_rows.items():
        source_kind = first_text(source_row, "source_kind").lower()
        if source_kind not in FORMULA_SOURCE_KINDS:
            continue
        coverage_row = coverage_by_source.get(identity)
        linked_rows, omitted = linked_review_rows(
            source_row,
            coverage_row,
            allowed_rows,
        )
        if identity in supplemental_formula_ids:
            outcome = "selected supplemental formula/equation target"
            validator = (
                "Complete source-map `Spec`/evidence contract recorded; normal "
                "named-theory coverage is intentionally not expanded."
            )
            comment_row = source_row
        else:
            outcome = coverage_label(coverage_payload, coverage_row)
            validator = judgment_description(
                coverage_payload,
                coverage_row,
                COVERAGE_LABELS,
                field="coverage",
                missing="No completed formula-coverage check recorded",
            )
            comment_row = coverage_row
        row_checks = row_local_semantic_statement_checks(
            linked_rows,
            statement_payload,
            surface_rows,
        )
        extra = ""
        if omitted:
            extra = (
                f"{omitted} recorded declaration reference"
                f"{'s were' if omitted != 1 else ' was'} outside the configured "
                "paper-facing surface and is not linked here."
            )
        table_rows.append(
            [
                table_cell(source_statement_text(identity, source_row), limit=420),
                code_cell(linked_rows),
                table_cell(f"{outcome}. {row_checks}"),
                table_cell(validator),
                table_cell(reason_text(comment_row, extra=extra)),
            ]
        )

    if not table_rows:
        table_rows.append(
            [
                "None",
                "`none`",
                "None",
                "None",
                "No source-map formula or equation is in normal scope or explicitly selected as a supplemental target.",
            ]
        )

    intro = (
        "### Current Canonical Evidence\n"
        "Rows are selected from semantic `formula` and `equation` source-kind "
        "metadata, never declaration names. In named-theory mode, the ledger "
        "retains a formula/equation outside normal coverage only when its "
        "source-map item is claim-bearing and has a complete direct `Spec`/evidence "
        "contract; that is an explicitly selected supplemental target, not an "
        "ordinary coverage promotion. Coverage and statement checks remain separate "
        "evidence lanes."
    )
    if scope_error:
        intro += (
            " Scope metadata needs repair, so the full inventory is shown: "
            + table_cell(scope_error)
        )
    else:
        intro += (
            " Active coverage mode: "
            + COVERAGE_MODE_LABELS.get(coverage_mode, "scope needing review")
            + "."
        )
    if reuse_note := saved_reuse_ledger_note(
        folder,
        status,
        lane="coverage",
        authorization=reuse,
    ):
        intro += " " + reuse_note
    return (
        intro
        + "\n\n"
        + markdown_table(
            [
                "Paper formula / subclaim",
                "Lean declaration",
                "Provenance",
                "Validators",
                "Comments",
            ],
            table_rows,
        )
    )


def source_rows_for_review_row(
    identity: str,
    source_rows: dict[str, dict[str, Any]],
    coverage_rows: dict[str, dict[str, Any]],
) -> list[dict[str, Any]]:
    short = short_declaration(identity)
    matches: list[dict[str, Any]] = []
    for source_key, coverage_row in coverage_rows.items():
        linked = coverage_row.get("review_rows", [])
        if not isinstance(linked, list):
            continue
        if not any(
            isinstance(value, str) and short_declaration(value) == short
            for value in linked
        ):
            continue
        source_row = lookup_row(source_rows, source_key)
        if source_row is not None and source_row not in matches:
            matches.append(source_row)
    if matches:
        return matches
    _source_key, source_row = source_map_lookup(source_rows, identity)
    return [source_row] if source_row is not None else []


def statement_ledger(
    folder: Path,
    status: dict[str, Any],
    evidence: dict[str, dict[str, Any] | None],
    *,
    reuse: SavedSidecarReuseAuthorization,
    cache_rows: tuple[dict[str, Any], ...] | None = None,
    semantic_surface: dict[str, Any] | None = None,
) -> str:
    statement_payload = evidence["statement"]
    tex_payload = evidence["tex"]
    assumption_payload = evidence["assumption"]
    review_payload = evidence["review"]
    surface = (
        semantic_surface
        if semantic_surface is not None
        else semantic_review_surface(
            folder,
            status,
            evidence,
            cache_rows=cache_rows,
            reuse_authorization=reuse,
        )
    )
    selected_rows = surface["rows"]

    table_rows: list[list[str]] = []
    for selected in selected_rows:
        identity = selected["name"]
        cache_row = selected["cache_row"]
        if selected["kind"] == "source_condition":
            condition_row = selected["assumption_row"]
            checks = [
                judgment_description(
                    assumption_payload,
                    condition_row,
                    ASSUMPTION_LABELS,
                    field="judgment",
                    missing="No completed source-condition check recorded",
                )
            ]
            comment = reason_text(condition_row)
        else:
            statement_row = selected["statement_row"]
            tex_row = selected["tex_row"]
            tex_check = validator_description(
                tex_payload,
                tex_row,
                "Lean translation recorded",
                missing="No Lean translation recorded",
            )
            if tex_row is not None:
                tex_check += (
                    "; recorded translation metadata, whose independent freshness "
                    "is not established by "
                    + (
                        "the saved semantic receipt"
                        if reuse.available
                        else "this report generator"
                    )
                )
            checks = [
                statement_validator_description(statement_payload, statement_row),
                tex_check,
            ]
            comment = reason_text(statement_row)
        paper_statement = first_text(cache_row, "paper_statement")
        table_rows.append(
            [
                table_cell(paper_statement, limit=420)
                if paper_statement
                else table_cell(humanize_identifier(identity)),
                code_cell([identity]),
                table_cell(". ".join(checks), limit=520),
                table_cell(comment),
            ]
        )

    if not table_rows:
        table_rows.append(
            [
                "None",
                "`none`",
                "None",
                "No PaperInterface statement rows are configured.",
            ]
        )

    review_summary = "No completed review-surface check is recorded."
    if reuse.available:
        review_summary = (
            "Saved aggregate reuse does not assert a fresh review-surface check; "
            "the receipt authorizes the semantic dispositions reported below."
        )
    elif review_payload is not None and first_text(review_payload, "judgment"):
        review_summary = validator_description(
            review_payload,
            review_payload,
            REVIEW_LABELS.get(
                first_text(review_payload, "judgment"),
                "review surface needs review",
            ),
            missing=review_summary,
        )
    intro = (
        "### Current Canonical Evidence\n"
        + human_review_summary(
            status,
            sum(row["kind"] != "source_condition" for row in selected_rows),
            reuse=reuse,
        )
        + " "
        + table_cell(review_summary)
    )
    if reuse_note := saved_reuse_ledger_note(
        folder,
        status,
        lane="statement",
        authorization=reuse,
    ):
        intro += " " + reuse_note
    orphan_statement_count = len(surface["orphan_statement_keys"])
    orphan_assumption_count = len(surface["orphan_assumption_keys"])
    if orphan_statement_count or orphan_assumption_count:
        diagnostics: list[str] = []
        if orphan_statement_count:
            diagnostics.append(
                plural(
                    orphan_statement_count,
                    "unconfigured, stale, or ambiguous statement-sidecar row",
                )
            )
        if orphan_assumption_count:
            diagnostics.append(
                plural(
                    orphan_assumption_count,
                    "unconfigured, stale, or ambiguous source-condition sidecar row",
                )
            )
        intro += (
            " Diagnostic-only evidence excluded from this paper-facing ledger: "
            + ", ".join(diagnostics)
            + "."
        )
    return (
        intro
        + "\n\n"
        + markdown_table(
            [
                "Paper-facing statement",
                "Lean declaration",
                "Validators",
                "Validator comments",
            ],
            table_rows,
        )
    )


def source_coverage_ledger(
    folder: Path,
    status: dict[str, Any],
    evidence: dict[str, dict[str, Any] | None],
    *,
    reuse: SavedSidecarReuseAuthorization,
    cache_rows: tuple[dict[str, Any], ...] | None = None,
    semantic_surface: dict[str, Any] | None = None,
) -> str:
    source_payload = evidence["source_map"]
    source_rows, coverage_mode, scope_error = scoped_source_rows(
        source_payload,
        folder=folder,
        reuse_authorization=reuse,
    )
    coverage_payload = evidence["coverage"]
    coverage_by_source, _used_coverage_keys = selected_coverage_rows_by_source(
        source_rows,
        coverage_payload,
        coverage_mode,
        reuse,
    )
    statement_payload = evidence["statement"]
    surface = (
        semantic_surface
        if semantic_surface is not None
        else semantic_review_surface(
            folder,
            status,
            evidence,
            cache_rows=cache_rows,
            reuse_authorization=reuse,
        )
    )
    surface_rows = surface["rows"]
    allowed_rows = {selected["name"] for selected in surface_rows}

    table_rows: list[list[str]] = []
    outcome_counts: Counter[str] = Counter()
    linked_count = 0
    checked_count = 0
    for identity, source_row in source_rows.items():
        coverage_row = coverage_by_source.get(identity)
        linked_rows, omitted = linked_review_rows(
            source_row,
            coverage_row,
            allowed_rows,
        )
        outcome = coverage_label(coverage_payload, coverage_row)
        outcome_counts[outcome] += 1
        linked_count += len(linked_rows)
        for row_name in linked_rows:
            selected = semantic_surface_row_for_navigation(surface_rows, row_name)
            statement_row = (
                selected.get("statement_row")
                if selected is not None and selected.get("kind") == "statement"
                else None
            )
            if statement_row is not None and not explicit_non_evidence(
                statement_payload,
                statement_row,
            ):
                checked_count += 1
        extra = ""
        if omitted:
            extra = (
                f"{omitted} recorded declaration reference"
                f"{'s were' if omitted != 1 else ' was'} outside the configured "
                "paper-facing surface and is not linked here."
            )
        table_rows.append(
            [
                table_cell(source_statement_text(identity, source_row), limit=440),
                code_cell(linked_rows),
                table_cell(outcome),
                row_local_semantic_statement_checks(
                    linked_rows,
                    statement_payload,
                    surface_rows,
                ),
                table_cell(reason_text(coverage_row, extra=extra)),
            ]
        )

    if not table_rows:
        table_rows.append(
            [
                "None",
                "`none`",
                "No source inventory recorded",
                "None",
                "No canonical source-map rows are recorded.",
            ]
        )

    source_artifact = first_text(source_payload, "source_artifact_path")
    source_description = (
        f"{len(source_rows)} source statements from `{table_cell(source_artifact)}`"
        if source_artifact
        else f"{len(source_rows)} source statements; source artifact path not recorded"
    )
    counts = (
        saved_coverage_count_text(reuse.coverage_counts)[0]
        if reuse.available
        else (
            ", ".join(
                f"{count} {label}" for label, count in sorted(outcome_counts.items())
            )
            or "no coverage rows"
        )
    )
    coverage_review = "No completed paper-level coverage check is recorded."
    if reuse.available:
        coverage_review = (
            "Saved semantic coverage dispositions are authorized by the immutable "
            "receipt; no fresh paper-level validator run is inferred"
        )
    elif coverage_payload is not None and not explicit_non_evidence(coverage_payload):
        coverage_review = validator_description(
            coverage_payload,
            coverage_payload,
            "coverage ledger recorded",
            missing=coverage_review,
        )
    intro = "\n".join(
        [
            "### Current Canonical Evidence",
            (
                "- Coverage scope: full inventory shown because scope metadata "
                f"needs repair ({table_cell(scope_error)})."
                if scope_error
                else "- Coverage scope: "
                + COVERAGE_MODE_LABELS.get(coverage_mode, "scope needing review")
                + "."
            ),
            f"- Source inventory: {source_description}.",
            f"- Coverage result: {counts}.",
            f"- Coverage review: {table_cell(coverage_review).rstrip('.')}.",
            "- Row-local statement checks: "
            f"{checked_count}/{linked_count} linked row references have a completed "
            "canonical statement check; repeated links are counted per source row.",
        ]
    )
    if reuse_note := saved_reuse_ledger_note(
        folder,
        status,
        lane="coverage",
        authorization=reuse,
    ):
        intro += "\n- Immutable reuse: " + reuse_note
    return (
        intro
        + "\n\n"
        + markdown_table(
            [
                "Source statement",
                "Linked Lean review rows",
                "Coverage judgment",
                "Row-local statement checks",
                "Comments",
            ],
            table_rows,
        )
    )


def generated_section_blocks(
    folder: Path,
    *,
    snapshot: ReportInputSnapshot | None = None,
    reuse_authorization: SavedSidecarReuseAuthorization | None = None,
    semantic_surface: dict[str, Any] | None = None,
) -> dict[int, str]:
    status = snapshot.status if snapshot is not None else status_payload(folder)
    evidence = snapshot.evidence if snapshot is not None else canonical_sidecars(folder)
    cache_rows = snapshot.cache_rows if snapshot is not None else None
    reuse = reuse_authorization or saved_report_reuse_authorization(folder, status)
    surface = (
        semantic_surface
        if semantic_surface is not None
        else semantic_review_surface(
            folder,
            status,
            evidence,
            cache_rows=cache_rows,
            reuse_authorization=reuse,
        )
    )
    return {
        13: assumption_ledger(
            folder,
            status,
            evidence,
            reuse=reuse,
            cache_rows=cache_rows,
            semantic_surface=surface,
        ),
        14: formula_ledger(
            folder,
            status,
            evidence,
            reuse=reuse,
            cache_rows=cache_rows,
            semantic_surface=surface,
        ),
        20: statement_ledger(
            folder,
            status,
            evidence,
            reuse=reuse,
            cache_rows=cache_rows,
            semantic_surface=surface,
        ),
        21: source_coverage_ledger(
            folder,
            status,
            evidence,
            reuse=reuse,
            cache_rows=cache_rows,
            semantic_surface=surface,
        ),
    }


def wrapped_section_block(section: int, content: str) -> str:
    _title, begin, end = SECTION_BLOCKS[section]
    return f"{begin}\n{content.rstrip()}\n{end}"


def remove_legacy_tables(body: str) -> str:
    """Remove old hand-maintained ledger tables while retaining researcher prose."""

    lines = body.splitlines()
    kept: list[str] = []
    index = 0
    while index < len(lines):
        if lines[index].lstrip().startswith("|"):
            table_end = index
            while table_end < len(lines) and lines[table_end].lstrip().startswith("|"):
                table_end += 1
            if table_end - index >= 2 and re.match(
                r"^\s*\|(?:\s*:?-+:?\s*\|)+\s*$",
                lines[index + 1],
            ):
                index = table_end
                continue
        kept.append(lines[index])
        index += 1
    return "\n".join(kept).strip()


def replace_section_ledger(text: str, section: int, content: str, path: Path) -> str:
    title, begin, end = SECTION_BLOCKS[section]
    heading = f"## {section}. {title}"
    next_heading = re.compile(rf"(?m)^## {section + 1}\. ")
    start = text.find(heading)
    if start < 0:
        raise ValueError(f"{path.relative_to(ROOT)} does not contain `{heading}`")
    body_start = start + len(heading)
    match = next_heading.search(text, body_start)
    body_end = match.start() if match is not None else len(text)
    body = text[body_start:body_end]
    block = wrapped_section_block(section, content)

    if begin in body or end in body:
        if body.count(begin) != 1 or body.count(end) != 1:
            raise ValueError(
                f"{path.relative_to(ROOT)} has malformed generated section {section} markers"
            )
        before, rest = body.split(begin, 1)
        _old, after = rest.split(end, 1)
        new_body = before.rstrip() + "\n\n" + block + after
    else:
        prose = remove_legacy_tables(body)
        new_body = "\n\n" + prose + ("\n\n" if prose else "") + block + "\n\n"

    return text[:body_start] + new_body + text[body_end:]


def replace_audit_summary(text: str, summary: dict[str, str], path: Path) -> str:
    """Update the legacy one-line summary when a report still has one.

    Newer reports use only the generated LLM-as-judge block below.  That block
    is authoritative for generated counts, so the absence of the older line is
    a supported report format rather than an error that blocks a closeout.
    """

    lines = text.splitlines()
    replacement = audit_summary_line(summary)
    for index, line in enumerate(lines):
        if line.startswith("- Audit summary:"):
            lines[index] = replacement
            return "\n".join(lines) + ("\n" if text.endswith("\n") else "")
    return text


def replace_or_insert_block(text: str, block: str, path: Path) -> str:
    if BEGIN in text or END in text:
        if text.count(BEGIN) != 1 or text.count(END) != 1:
            raise ValueError(
                f"{path.relative_to(ROOT)} has malformed generated block markers"
            )
        before, rest = text.split(BEGIN, 1)
        _old, after = rest.split(END, 1)
        return before.rstrip() + "\n" + block + after

    match = re.search(r"^## \d+\. Validation Checks\n", text, flags=re.MULTILINE)
    if match is None:
        raise ValueError(
            f"{_path_label(path)} does not contain a Validation Checks section"
        )
    return text[: match.end()] + block + "\n\n" + text[match.end() :]


def prepare_report(path: Path) -> PreparedReport:
    snapshot = load_report_input_snapshot(path)
    current_v11 = uses_direct_source_spec_closeout(
        snapshot.status, snapshot.evidence.get("source_map")
    )
    reuse = (
        SavedSidecarReuseAuthorization(False, "current source-to-Spec report")
        if current_v11
        else saved_report_reuse_authorization(path.parent, snapshot.status)
    )
    approved_contexts, approved_context_error = approved_review_contexts_for_report(
        path.parent
    )
    if approved_context_error:
        raise ValueError(
            f"{_path_label(path)} cannot project settled review context: "
            + approved_context_error
        )
    context_updated = replace_approved_review_context_block(
        snapshot.text,
        contexts=approved_contexts,
        path=path,
    )
    if current_v11 or not supports_legacy_generated_layout(
        context_updated
    ):
        # v11 report prose and its source-first link surface are hand-authored
        # closeout artifacts.  Updating it through the retired v10 projection
        # would regress the semantic review contract rather than refresh it.
        # Reports which no longer declare the legacy section layout are also
        # intentionally left alone rather than acquiring a mixed layout.
        return PreparedReport(snapshot=snapshot, reuse=reuse, rendered=context_updated)
    surface = semantic_review_surface(
        path.parent,
        snapshot.status,
        snapshot.evidence,
        cache_rows=snapshot.cache_rows,
        reuse_authorization=reuse,
    )
    summary = sidecar_summary(
        path.parent,
        snapshot=snapshot,
        reuse_authorization=reuse,
        semantic_surface=surface,
    )
    updated = replace_audit_summary(context_updated, summary, path)
    updated = replace_or_insert_block(updated, result_block(summary), path)
    for section, content in generated_section_blocks(
        path.parent,
        snapshot=snapshot,
        reuse_authorization=reuse,
        semantic_surface=surface,
    ).items():
        updated = replace_section_ledger(updated, section, content, path)
    return PreparedReport(
        snapshot=snapshot,
        reuse=reuse,
        rendered=updated.rstrip() + "\n",
    )


def validate_prepared_report(
    prepared: PreparedReport,
    *,
    closure_provider: Any,
) -> None:
    """Fail if report inputs or an authorized saved receipt changed in flight."""

    if report_input_digest(prepared.snapshot.input_paths) != prepared.snapshot.input_sha256:
        raise ValueError(
            f"{_path_label(prepared.snapshot.path)} inputs changed during rendering"
        )
    if uses_direct_source_spec_closeout(
        prepared.snapshot.status, prepared.snapshot.evidence.get("source_map")
    ):
        return
    current_reuse = saved_sidecar_reuse_authorization(
        prepared.snapshot.path.parent,
        prepared.snapshot.status,
        closure_provider=closure_provider,
    )
    if prepared.reuse.available != current_reuse.available or (
        prepared.reuse.available and prepared.reuse != current_reuse
    ):
        raise ValueError(
            f"{_path_label(prepared.snapshot.path)} saved semantic authority "
            "changed during rendering"
        )
    if report_input_digest(prepared.snapshot.input_paths) != prepared.snapshot.input_sha256:
        raise ValueError(
            f"{_path_label(prepared.snapshot.path)} inputs changed during "
            "final authorization"
        )


def write_prepared_report(
    prepared: PreparedReport,
    *,
    closure_provider: Any,
) -> None:
    """Validate, stage, recheck, and atomically replace one changed report."""

    validate_prepared_report(prepared, closure_provider=closure_provider)
    target = prepared.snapshot.path
    temporary_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            dir=target.parent,
            prefix=f".{target.name}.",
            suffix=".tmp",
            delete=False,
        ) as temporary:
            temporary.write(prepared.rendered)
            temporary.flush()
            os.fsync(temporary.fileno())
            temporary_path = Path(temporary.name)
        temporary_path.chmod(target.stat().st_mode & 0o7777)
        if report_input_digest(prepared.snapshot.input_paths) != prepared.snapshot.input_sha256:
            raise ValueError(
                f"{_path_label(target)} inputs changed before atomic report write"
            )
        os.replace(temporary_path, target)
        temporary_path = None
    finally:
        if temporary_path is not None:
            temporary_path.unlink(missing_ok=True)


def render_report(path: Path) -> str:
    prepared = prepare_report(path)
    validate_prepared_report(
        prepared,
        closure_provider=LazySharedClosureProvider(ROOT),
    )
    return prepared.rendered


def refresh_report(path: Path) -> bool:
    prepared = prepare_report(path)
    if prepared.rendered == prepared.snapshot.text:
        validate_prepared_report(
            prepared,
            closure_provider=LazySharedClosureProvider(ROOT),
        )
        return False
    write_prepared_report(
        prepared,
        closure_provider=LazySharedClosureProvider(ROOT),
    )
    return True


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if any report would be changed",
    )
    parser.add_argument(
        "--paper",
        help="refresh only this paper folder instead of every report",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    paths = public_report_paths(args.paper)
    if args.paper is not None and not paths:
        print(f"No validation report found for paper {args.paper}")
        return 1
    prepared_reports = [prepare_report(path) for path in paths]
    changed = [
        prepared
        for prepared in prepared_reports
        if prepared.snapshot.text != prepared.rendered
    ]
    if args.check:
        final_provider: Any = (
            WorktreeImportClosureProvider(ROOT, eager_source_snapshot=True)
            if any(prepared.reuse.available for prepared in prepared_reports)
            else LazySharedClosureProvider(ROOT)
        )
        for prepared in prepared_reports:
            validate_prepared_report(prepared, closure_provider=final_provider)
        if changed:
            print("Reports need refreshed audit summaries:")
            for prepared in changed:
                print(prepared.snapshot.path.relative_to(ROOT))
            return 1
    else:
        changed_paths = {prepared.snapshot.path for prepared in changed}
        unchanged = [
            prepared
            for prepared in prepared_reports
            if prepared.snapshot.path not in changed_paths
        ]
        final_provider: Any = (
            WorktreeImportClosureProvider(ROOT, eager_source_snapshot=True)
            if any(prepared.reuse.available for prepared in prepared_reports)
            else LazySharedClosureProvider(ROOT)
        )
        for prepared in unchanged:
            validate_prepared_report(prepared, closure_provider=final_provider)
        for prepared in changed:
            write_prepared_report(
                prepared,
                closure_provider=final_provider,
            )
    for prepared in changed:
        print(f"refreshed {prepared.snapshot.path.relative_to(ROOT)}")
    print(f"checked {len(paths)} public validation reports")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
