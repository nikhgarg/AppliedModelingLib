#!/usr/bin/env python3
"""Authenticate a narrow replay of reachable PaperInterface auxiliaries.

This transport exists for a specific migration boundary: an otherwise-current
v10 raw source-record receipt can predate the generated reachable-auxiliary
routing ledger.  It is deliberately not a raw-audit mutation, a judgment
overlay, or a source-equivalence certificate.  The supplement binds the exact
canonical raw receipt and replays the current lexical reachability, exact
source-map routes, and quarantine semantics before either closeout consumer
can use it.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import importlib.util
import json
import os
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.formalization_protocol import CURRENT_SOURCE_RECORD_PROMPT_VERSION

SUPPLEMENT_BASENAME = "source_record_auxiliary_routing_supplement.json"
SUPPLEMENT_SCHEMA = 1
ROUTING_CLOSURE_MANIFEST_SCHEMA = 2
SOURCE_RECORD_PROMPT_VERSION = CURRENT_SOURCE_RECORD_PROMPT_VERSION
# This is intentionally distinct from the parser identity read from
# ``source_record_audit.py`` below.  The parser controls lexical reachability;
# this module also defines how a replay binds raw roots, status selection, and
# source-association transport.  Bump this value when those replay semantics
# change.  It invalidates only the compact supplement, never the raw audit.
AUXILIARY_ROUTING_SUPPLEMENT_ENGINE_IDENTITY = {
    "path": (
        "scripts/source_record_auxiliary_routing_supplement.py"
        "#raw-bound-reachable-auxiliary-routing-replay"
    ),
    "surface_semantic_version": "auxiliary-routing-supplement-v1",
}
LEDGER_KEYS = (
    "reachable_paper_interface_auxiliary_dependencies",
    "unresolved_reachable_paper_interface_auxiliaries",
    "ambiguous_reachable_paper_interface_auxiliary_references",
    "reachable_paper_interface_auxiliary_quarantine_configuration_errors",
)
SHA256_HEX_LENGTH = 64


@dataclass(frozen=True)
class ValidatedAuxiliaryRoutingContext:
    """A validated routing result, intentionally distinct from serialized JSON."""

    paper: str
    provenance: str
    _raw_payload_sha256: str
    _ledger_json: str

    def _routing_ledger(self) -> dict[str, Any]:
        """Return the receipt-bound ledger as a fresh, mutable JSON value."""

        payload = json.loads(self._ledger_json)
        if not isinstance(payload, dict) or set(payload) != set(LEDGER_KEYS):
            # This can only occur through an invalid in-memory authority.  A
            # serialized supplement is shape-validated before this context is
            # constructed, but consumers must still fail closed here.
            raise AuxiliaryRoutingSupplementError(
                "validated routing context has a malformed routing ledger"
            )
        if any(not isinstance(payload[key], list) for key in LEDGER_KEYS):
            raise AuxiliaryRoutingSupplementError(
                "validated routing context has a malformed routing-ledger field"
            )
        return payload

    def audit_payload_with_authenticated_ledger(
        self, audit_payload: Mapping[str, Any]
    ) -> tuple[dict[str, Any] | None, str]:
        """Attach this ledger only to the exact raw receipt that authenticated it.

        A supplement is a narrow transport for an otherwise-current raw audit.
        It must not become a generic source of routing facts for a different
        payload, even when that payload happens to name the same paper.
        """

        if str(audit_payload.get("paper") or "").strip() != self.paper:
            return None, "routing context paper does not match the raw audit payload"
        if _payload_sha256(audit_payload) != self._raw_payload_sha256:
            return None, "routing context is not bound to this exact raw audit payload"
        try:
            ledger = self._routing_ledger()
        except AuxiliaryRoutingSupplementError as error:
            return None, str(error)
        augmented = dict(audit_payload)
        augmented.update(ledger)
        return augmented, ""

    def quarantine_configuration_errors(self) -> tuple[str, ...]:
        payload = self._routing_ledger()
        return tuple(
            str(value).strip()
            for value in payload[
                "reachable_paper_interface_auxiliary_quarantine_configuration_errors"
            ]
            if str(value).strip()
        )

    def unresolved_auxiliaries(self) -> tuple[dict[str, Any], ...]:
        payload = self._routing_ledger()
        return tuple(
            value
            for value in payload[
                "unresolved_reachable_paper_interface_auxiliaries"
            ]
            if isinstance(value, dict)
        )

    def ambiguous_references(self) -> tuple[dict[str, Any], ...]:
        payload = self._routing_ledger()
        return tuple(
            value
            for value in payload[
                "ambiguous_reachable_paper_interface_auxiliary_references"
            ]
            if isinstance(value, dict)
        )


class AuxiliaryRoutingSupplementError(ValueError):
    """Raised when the narrow routing transport is not current evidence."""


def _canonical_json(value: object) -> str:
    """Canonicalize object keys while deliberately preserving list order."""

    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _payload_sha256(value: object) -> str:
    return hashlib.sha256(_canonical_json(value).encode("utf-8")).hexdigest()


def _bytes_sha256(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def _is_sha256(value: object) -> bool:
    text = str(value or "").strip().lower()
    return len(text) == SHA256_HEX_LENGTH and all(
        character in "0123456789abcdef" for character in text
    )


def _load_json_object(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as error:
        raise AuxiliaryRoutingSupplementError(
            f"could not read JSON object at {path}: {error}"
        ) from error
    if not isinstance(payload, dict):
        raise AuxiliaryRoutingSupplementError(f"{path} is not a JSON object")
    return payload, contents


def _inside(root: Path, path: Path, *, label: str) -> Path:
    try:
        resolved = path.resolve()
        resolved.relative_to(root.resolve())
    except (OSError, RuntimeError, ValueError) as error:
        raise AuxiliaryRoutingSupplementError(
            f"{label} must remain inside the repository root"
        ) from error
    return resolved


def _relative(root: Path, path: Path, *, label: str) -> str:
    resolved = _inside(root, path, label=label)
    return resolved.relative_to(root.resolve()).as_posix()


def _file_identity(root: Path, path: Path, *, label: str) -> dict[str, str]:
    resolved = _inside(root, path, label=label)
    if not resolved.is_file():
        raise AuxiliaryRoutingSupplementError(f"{label} is missing or not a file")
    return {
        "path": _relative(root, resolved, label=label),
        "sha256": _bytes_sha256(resolved.read_bytes()),
    }


def _identity_error(actual: object, expected: object, *, label: str) -> str:
    if not isinstance(actual, dict) or not isinstance(expected, dict):
        return f"{label} identity is malformed"
    if actual != expected:
        return f"{label} identity changed"
    return ""


def _routing_helper_path(root: Path, helper_path: Path | None) -> Path:
    candidate = (
        helper_path
        if helper_path is not None
        else root / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
    )
    if not candidate.is_file():
        raise AuxiliaryRoutingSupplementError(
            "reachable-auxiliary parser helper is unavailable"
        )
    return candidate.resolve()


def _load_routing_helper(root: Path, helper_path: Path | None) -> tuple[Any, Path]:
    """Load a fresh helper module keyed by current bytes, never a stale import."""

    path = _routing_helper_path(root, helper_path)
    digest = _bytes_sha256(path.read_bytes())
    module_name = f"_source_record_auxiliary_routing_{digest}"
    sys.modules.pop(module_name, None)
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise AuxiliaryRoutingSupplementError(
            "could not create reachable-auxiliary parser module"
        )
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    try:
        spec.loader.exec_module(module)
    except Exception as error:  # noqa: BLE001 - parser loading is a trust boundary.
        sys.modules.pop(module_name, None)
        raise AuxiliaryRoutingSupplementError(
            f"could not load reachable-auxiliary parser helper: {error}"
        ) from error
    return module, path


def _routing_engine_identity_from_source(
    root: Path, helper_path: Path | None
) -> tuple[dict[str, str], Path]:
    """Read the narrow routing-engine identity without importing its parser.

    Consumer validation must not parse the imported Lean closure just to learn
    whether the engine changed.  The identity is an intentionally literal,
    reviewable producer contract in ``source_record_audit.py``; reading it by
    Python AST avoids executing the broad generator while still failing closed
    if the declaration is absent, nonliteral, or malformed.
    """

    path = _routing_helper_path(root, helper_path)
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    except (OSError, SyntaxError) as error:
        raise AuxiliaryRoutingSupplementError(
            f"could not read reachable-auxiliary parser identity: {error}"
        ) from error
    value: object | None = None
    for node in tree.body:
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        if not any(
            isinstance(target, ast.Name)
            and target.id
            == "REACHABLE_PAPER_INTERFACE_AUXILIARY_ROUTING_ENGINE_IDENTITY"
            for target in targets
        ):
            continue
        try:
            value = ast.literal_eval(node.value)
        except (TypeError, ValueError) as error:
            raise AuxiliaryRoutingSupplementError(
                "reachable-auxiliary parser identity must be a literal object"
            ) from error
        break
    if not isinstance(value, dict) or set(value) != {
        "path",
        "surface_semantic_version",
    }:
        raise AuxiliaryRoutingSupplementError(
            "reachable-auxiliary parser has a malformed semantic-surface identity"
        )
    path_value = value.get("path")
    version = value.get("surface_semantic_version")
    if not isinstance(path_value, str) or not path_value.strip():
        raise AuxiliaryRoutingSupplementError(
            "reachable-auxiliary parser identity has a malformed path"
        )
    if not isinstance(version, str) or not version.strip():
        raise AuxiliaryRoutingSupplementError(
            "reachable-auxiliary parser identity has a malformed semantic version"
        )
    return {
        "path": path_value,
        "surface_semantic_version": version,
    }, path


def _raw_v10_receipt_error(raw: Mapping[str, Any], *, paper: str) -> str:
    if str(raw.get("paper") or "").strip() != paper:
        return "raw source-record audit paper does not match the supplement paper"
    if str(raw.get("prompt_version") or "").strip() != SOURCE_RECORD_PROMPT_VERSION:
        return "raw source-record audit does not use the current v10 prompt"
    fingerprint = raw.get("source_record_input_fingerprint")
    if not isinstance(fingerprint, dict):
        return "raw source-record audit has no current input fingerprint"
    if fingerprint.get("no_lean") is not False:
        return "raw source-record audit was not produced by a full no_lean=false run"
    if not isinstance(fingerprint.get("max_depth"), int):
        return "raw source-record audit input fingerprint has malformed max_depth"
    if not _is_sha256(raw.get("source_record_audit_sha256")):
        return "raw source-record audit aggregate receipt is missing or malformed"
    if not _is_sha256(raw.get("source_record_audit_integrity_sha256")):
        return "raw source-record audit integrity receipt is missing or malformed"
    try:
        try:
            from source_record_integrity import source_record_audit_receipt_error
        except ModuleNotFoundError:
            from scripts.source_record_integrity import source_record_audit_receipt_error
        receipt_error = source_record_audit_receipt_error(raw)
    except Exception as error:  # noqa: BLE001 - receipt checking must fail closed.
        return f"could not validate raw source-record receipts: {error}"
    return receipt_error


def _current_raw_identity_error(
    root: Path, paper_dir: Path, raw: dict[str, Any]
) -> str:
    """Replay the existing no-Lean producer identity without a raw-audit scan."""

    try:
        try:
            from audit_evidence_integrity import (
                current_paper_statement_map_sha256,
                source_record_audit_identity_error,
            )
        except ModuleNotFoundError:
            from scripts.audit_evidence_integrity import (
                current_paper_statement_map_sha256,
                source_record_audit_identity_error,
            )
        # The helper uses its module ROOT for the isolated identity subprocess.
        # This transport is invoked only from the repository root in production.
        _ = root
        return source_record_audit_identity_error(
            raw,
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                paper_dir
            ),
            folder=paper_dir,
        )
    except Exception as error:  # noqa: BLE001 - identity replay is fail closed.
        return f"could not replay current raw source-record identity: {error}"


def _raw_interface_path(
    root: Path, paper_dir: Path, raw: Mapping[str, Any]
) -> tuple[Path, dict[str, str]]:
    identity = raw.get("review_interface_source")
    if not isinstance(identity, dict):
        raise AuxiliaryRoutingSupplementError(
            "raw source-record audit has no review_interface_source identity"
        )
    relative = identity.get("path")
    if not isinstance(relative, str) or not relative.strip() or Path(relative).is_absolute():
        raise AuxiliaryRoutingSupplementError(
            "raw review_interface_source path is malformed"
        )
    path = _inside(root, root / relative, label="raw review_interface_source")
    actual = _file_identity(root, path, label="raw review_interface_source")
    if error := _identity_error(actual, identity, label="raw review_interface_source"):
        raise AuxiliaryRoutingSupplementError(error)
    try:
        path.relative_to(paper_dir.resolve())
    except ValueError as error:
        raise AuxiliaryRoutingSupplementError(
            "raw review_interface_source is outside the paper directory"
        ) from error
    return path, actual


def _raw_assumption_identity(
    root: Path, paper_dir: Path, raw: Mapping[str, Any]
) -> dict[str, str | bool]:
    expected = raw.get("review_assumption_source")
    path = paper_dir / "Assumptions.lean"
    if expected is None:
        if path.exists():
            raise AuxiliaryRoutingSupplementError(
                "Assumptions.lean appeared after the raw source-record audit"
            )
        return {"present": False}
    if not isinstance(expected, dict):
        raise AuxiliaryRoutingSupplementError(
            "raw review_assumption_source identity is malformed"
        )
    if not path.is_file():
        raise AuxiliaryRoutingSupplementError(
            "Assumptions.lean disappeared after the raw source-record audit"
        )
    actual = _file_identity(root, path, label="Assumptions.lean")
    if error := _identity_error(actual, expected, label="raw review_assumption_source"):
        raise AuxiliaryRoutingSupplementError(error)
    return {"present": True, **actual}


def _source_proof_fidelity_path(
    root: Path, paper_dir: Path, status_payload: Mapping[str, Any]
) -> Path:
    review_surface = status_payload.get("review_surface")
    config = (
        review_surface.get("source_proof_fidelity_review")
        if isinstance(review_surface, dict)
        else None
    )
    raw_path = config.get("ledger_file") if isinstance(config, dict) else None
    if not isinstance(raw_path, str) or not raw_path.strip():
        return paper_dir / "audit" / "source_proof_fidelity.json"
    candidate = Path(raw_path)
    if candidate.is_absolute():
        raise AuxiliaryRoutingSupplementError(
            "source-proof fidelity ledger path must be repository-relative"
        )
    return root / candidate if candidate.parts[:1] == ("papers",) else paper_dir / candidate


def _source_association_projection(
    raw: Mapping[str, Any], selected: set[str]
) -> list[dict[str, Any]]:
    """Bind every generated source association for selected routing roots.

    Semantic-model rows normally use ``source_statement_association`` while
    direct source-contract rows use ``semantic_contract_source_association``.
    Both are raw-generated, content-pinned routes.  The routing supplement
    never decides source credit, but it must not let a selected root lose one
    of those associations while moving a routing ledger forward.
    """

    projection: list[dict[str, Any]] = []
    for section in (
        "boundary_input_items",
        "conclusion_dependency_items",
        "recursive_field_items",
        "semantic_model_items",
        "type_valued_certificate_result_items",
        "source_premise_consistency_items",
    ):
        for item in raw.get(section) or []:
            if not isinstance(item, dict):
                continue
            reviewed_identity = item.get("reviewed_declaration_identity")
            qualified = str(item.get("qualified_declaration") or "").strip()
            if not qualified and isinstance(reviewed_identity, dict):
                qualified = str(
                    reviewed_identity.get("qualified_declaration") or ""
                ).strip()
            if qualified not in selected:
                continue
            for field in (
                "semantic_contract_source_association",
                "source_statement_association",
            ):
                association = item.get(field)
                if not isinstance(association, dict):
                    continue
                projection.append(
                    {
                        "section": section,
                        "qualified_declaration": qualified,
                        "paper_statement_map_sha256": item.get(
                            "paper_statement_map_sha256"
                        ),
                        "reviewed_declaration_identity": reviewed_identity,
                        "association_field": field,
                        "association": association,
                    }
                )
    return sorted(projection, key=_canonical_json)


def _raw_lean_dependency_projection(raw: Mapping[str, Any]) -> list[dict[str, str]]:
    """Return the complete authenticated parser closure from the raw receipt."""

    fingerprint = raw.get("source_record_input_fingerprint")
    if not isinstance(fingerprint, dict):
        raise AuxiliaryRoutingSupplementError(
            "raw source-record input fingerprint is malformed"
        )
    dependencies = fingerprint.get("lean_dependency_identities")
    if not isinstance(dependencies, list) or not dependencies:
        raise AuxiliaryRoutingSupplementError(
            "raw source-record audit has no Lean dependency identity closure"
        )
    projection: list[dict[str, str]] = []
    previous_path = ""
    for dependency in dependencies:
        if not isinstance(dependency, dict):
            raise AuxiliaryRoutingSupplementError(
                "raw source-record Lean dependency identity is malformed"
            )
        path = dependency.get("path")
        digest = dependency.get("sha256")
        if (
            dependency.get("status") != "present"
            or not isinstance(path, str)
            or not path
            or Path(path).is_absolute()
            or path <= previous_path
            or not _is_sha256(digest)
        ):
            raise AuxiliaryRoutingSupplementError(
                "raw source-record Lean dependency closure is incomplete or malformed"
            )
        projection.append({"path": path, "sha256": digest})
        previous_path = path
    return projection


def _raw_lean_dependency_sources(
    root: Path, raw: Mapping[str, Any]
) -> tuple[list[Path], list[dict[str, str]]]:
    """Resolve and byte-check the Lean-owned closure recorded by the raw audit.

    The raw source-record producer obtained this source universe from Lean's
    loaded-module graph.  A routing-supplement reissue must replay exactly that
    authenticated universe; parsing imports again in Python could silently add
    or omit declarations based on source spelling.
    """

    identities = _raw_lean_dependency_projection(raw)
    sources: list[Path] = []
    for expected in identities:
        source = _inside(
            root,
            root / expected["path"],
            label="raw Lean dependency source",
        )
        actual = _file_identity(root, source, label="raw Lean dependency source")
        if actual != expected:
            raise AuxiliaryRoutingSupplementError(
                "raw source-record Lean dependency source identity changed"
            )
        sources.append(source)
    if len(sources) != len(set(sources)):
        raise AuxiliaryRoutingSupplementError(
            "raw source-record Lean dependency closure contains duplicate sources"
        )
    return sources, identities


def _raw_active_review_roots(raw: Mapping[str, Any]) -> list[dict[str, str]]:
    """Return the exact raw review roots that have active input evidence.

    ``status.json`` intentionally has a broader presentation surface than an
    individual source-record pass.  It may therefore contain out-of-mode
    names that were not reviewed in this raw receipt.  Auxiliary reachability
    must start only from the generated review rows that have a corresponding
    raw ``row_visible_inputs`` entry, and must preserve the raw row-to-FQ
    identity rather than resolving the current status list anew.
    """

    configured_rows = raw.get("configured_review_rows")
    visible_inputs = raw.get("row_visible_inputs")
    if not isinstance(configured_rows, list):
        raise AuxiliaryRoutingSupplementError(
            "raw source-record audit has no configured-review-row ledger"
        )
    if not isinstance(visible_inputs, dict):
        raise AuxiliaryRoutingSupplementError(
            "raw source-record audit has no row-visible-input ledger"
        )

    roots: list[dict[str, str]] = []
    configured_row_names: set[str] = set()
    qualified_names: set[str] = set()
    for configured in configured_rows:
        if not isinstance(configured, dict):
            raise AuxiliaryRoutingSupplementError(
                "raw configured-review-row ledger is malformed"
            )
        row = configured.get("row")
        qualified = configured.get("qualified_declaration")
        if (
            not isinstance(row, str)
            or not row
            or not isinstance(qualified, str)
            or not qualified
            or "." not in qualified
        ):
            raise AuxiliaryRoutingSupplementError(
                "raw configured-review-row identity is malformed"
            )
        if row in configured_row_names or qualified in qualified_names:
            raise AuxiliaryRoutingSupplementError(
                "raw configured-review-row identities are duplicated"
            )
        inputs = visible_inputs.get(row)
        if not isinstance(inputs, list) or not all(
            isinstance(input_item, dict) for input_item in inputs
        ):
            raise AuxiliaryRoutingSupplementError(
                "raw configured review row has no valid visible-input entry"
            )
        configured_row_names.add(row)
        qualified_names.add(qualified)
        roots.append({"row": row, "qualified_declaration": qualified})

    visible_row_names = set(visible_inputs)
    if any(not isinstance(row, str) or not row for row in visible_row_names):
        raise AuxiliaryRoutingSupplementError(
            "raw row-visible-input ledger has a malformed row identity"
        )
    if visible_row_names != configured_row_names:
        raise AuxiliaryRoutingSupplementError(
            "raw row-visible-input ledger does not exactly match configured review rows"
        )
    return sorted(roots, key=lambda root: (root["qualified_declaration"], root["row"]))


def _raw_active_review_declarations(raw: Mapping[str, Any]) -> list[str]:
    """Return exact FQ declarations for active raw review rows."""

    return [
        root["qualified_declaration"] for root in _raw_active_review_roots(raw)
    ]


def _resolve_rows(
    helper: Any,
    *,
    configured_rows: list[str],
    interface_declarations: dict[str, str],
    interface_namespace: str,
    assumption_declarations: dict[str, str],
    assumption_namespace: str,
) -> tuple[dict[str, str], set[str]]:
    """Mirror the generator's exact configured-row resolution semantics."""

    qualified_by_row: dict[str, str] = {}
    selected: set[str] = set()
    for row in configured_rows:
        interface_match = helper.resolve_declaration_reference(
            row, interface_declarations, preferred_namespace=interface_namespace
        )
        assumption_match = helper.resolve_declaration_reference(
            row, assumption_declarations, preferred_namespace=assumption_namespace
        )
        matches = [name for name in (interface_match, assumption_match) if name]
        if len(set(matches)) > 1:
            raise AuxiliaryRoutingSupplementError(
                f"configured review row `{row}` is ambiguous across review files"
            )
        if not matches:
            continue
        qualified_by_row[row] = matches[0]
        selected.add(matches[0])
    return qualified_by_row, selected


def _resolve_auxiliary_names(
    helper: Any,
    *,
    rows: list[str],
    interface_declarations: dict[str, str],
    interface_namespace: str,
    assumption_declarations: dict[str, str],
    assumption_namespace: str,
) -> set[str]:
    resolved: set[str] = set()
    for row in rows:
        interface_match = helper.resolve_declaration_reference(
            row, interface_declarations, preferred_namespace=interface_namespace
        )
        assumption_match = helper.resolve_declaration_reference(
            row, assumption_declarations, preferred_namespace=assumption_namespace
        )
        resolved.update(name for name in (interface_match, assumption_match) if name)
    return resolved


def _current_active_review_rows(
    status_payload: Mapping[str, Any], raw_active_review_roots: list[dict[str, str]]
) -> list[dict[str, str]]:
    """Confirm that every raw active root remains selected by current status.

    This is deliberately an intersection, not a fresh declaration-resolution
    pass over all current ``include_names``.  A later presentation-only row
    cannot create a source-record routing obligation that was absent from the
    raw review receipt.  Conversely, removing an active raw row is a hard
    stale-evidence error.
    """

    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        raise AuxiliaryRoutingSupplementError(
            "status.json has no review surface for raw active review rows"
        )
    current_rows: set[str] = set()
    for key in ("include_names", "assumption_names"):
        values = review_surface.get(key)
        if not isinstance(values, list):
            continue
        current_rows.update(
            value.strip()
            for value in values
            if isinstance(value, str) and value.strip()
        )
    missing = [
        root
        for root in raw_active_review_roots
        if root["row"] not in current_rows
        and root["qualified_declaration"] not in current_rows
    ]
    if missing:
        raise AuxiliaryRoutingSupplementError(
            "current status no longer selects one or more raw active review rows"
        )
    return [dict(root) for root in raw_active_review_roots]


def _routing_status_projection(
    root: Path,
    paper_dir: Path,
    status_payload: Mapping[str, Any],
    *,
    raw_active_review_roots: list[dict[str, str]],
) -> dict[str, Any]:
    """Project exactly the status configuration read by auxiliary routing.

    A report, coordination note, or unrelated closeout field must not make a
    valid issued closure stale.  This projection covers only the review-surface
    active selection, auxiliary/quarantine policy, and fidelity-ledger
    location read by the routing engine.  The selection is the exact current
    intersection with raw active rows, rather than the broader status
    presentation surface.  Paths are normalized to their actual targets, so
    equivalent repository-relative spellings have one semantic identity.
    """

    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        # Keep the malformed-kind receipt explicit, but the active-row check
        # below still fails closed before this projection can be used.
        _current_active_review_rows(status_payload, raw_active_review_roots)
        return {"review_surface_kind": type(review_surface).__name__}

    selected_interface = _status_selected_interface_path(
        root=root, paper_dir=paper_dir, status_payload=status_payload
    )
    fidelity_path = _source_proof_fidelity_path(root, paper_dir, status_payload)

    def rows(key: str) -> list[str]:
        raw = review_surface.get(key)
        if not isinstance(raw, list):
            return []
        return [value for value in raw if isinstance(value, str) and value.strip()]

    raw_reasons = review_surface.get("quarantined_auxiliary_source_reasons")
    reasons: object
    if isinstance(raw_reasons, dict):
        reasons = raw_reasons
    else:
        reasons = {"kind": type(raw_reasons).__name__}
    legacy_reason = review_surface.get("quarantined_auxiliary_reason")
    return {
        "review_surface_kind": "object",
        "selected_interface_source": _relative(
            root, selected_interface, label="status-selected PaperInterface"
        ),
        "raw_active_review_rows": _current_active_review_rows(
            status_payload, raw_active_review_roots
        ),
        "auxiliary_names": rows("auxiliary_names"),
        "quarantined_auxiliary_names": rows("quarantined_auxiliary_names"),
        "quarantined_auxiliary_reason": legacy_reason,
        "quarantined_auxiliary_source_reasons": reasons,
        "source_proof_fidelity_ledger": _relative(
            root, fidelity_path, label="status-selected source-proof fidelity ledger"
        ),
    }


def _routing_inputs(
    *,
    paper: str,
    routing_engine_identity: Mapping[str, str],
    routing_status_projection: Mapping[str, Any],
    map_identity: Mapping[str, str],
    interface_identity: Mapping[str, str],
    assumption_identity: Mapping[str, str | bool],
    fidelity_identity: Mapping[str, str],
    raw_fingerprint: Mapping[str, Any],
) -> dict[str, Any]:
    """Return the parser-independent currentness boundary for a supplement.

    Every value is either an exact current file identity or a receipt already
    authenticated by the canonical raw source-record audit.  Consequently a
    consumer can compare this object without rebuilding the lexical closure.
    The selected declarations and parsed closure live in the separately
    content-addressed manifest issued by the one-time replay.
    """

    return {
        "paper": paper,
        "supplement_engine_identity": dict(
            AUXILIARY_ROUTING_SUPPLEMENT_ENGINE_IDENTITY
        ),
        "routing_engine_identity": dict(routing_engine_identity),
        "routing_status_projection": dict(routing_status_projection),
        "statement_map": dict(map_identity),
        "review_interface_source": dict(interface_identity),
        "review_assumption_source": dict(assumption_identity),
        "source_proof_fidelity": dict(fidelity_identity),
        "raw_source_record_input_fingerprint_sha256": _payload_sha256(
            raw_fingerprint
        ),
    }


def _parsed_declaration_digest(declarations: list[Any]) -> str:
    """Content-address the exact parser result used to issue the ledger."""

    return _payload_sha256(
        [
            {
                "name": declaration.name,
                "kind": declaration.kind,
                "source": declaration.source,
                "source_file": declaration.source_file,
                "line": declaration.line,
            }
            for declaration in declarations
        ]
    )


def _routing_closure_manifest(
    *,
    routing_engine_identity: Mapping[str, str],
    parser_source_identities: list[dict[str, str]],
    semantic_declarations: list[Any],
    selected_qualified_names: set[str],
    auxiliary_qualified_names: set[str],
    quarantined_auxiliary_qualified_names: set[str],
    raw_active_review_roots: list[dict[str, str]],
    raw_semantic_review_declarations: list[str],
    selected_root_source_associations: list[dict[str, Any]],
    routing_ledger: Mapping[str, Any],
) -> dict[str, Any]:
    """Record the issued parser closure without treating it as a raw audit.

    The source identities are the content-addressed lexical input closure.
    The parsed-declaration digest makes issuance reviewable and binds the
    routing ledger to that exact deterministic parser result.  Consumers do
    not reparse it: any source-byte or engine-version change invalidates this
    manifest and requires a fresh, narrow issuance replay.
    """

    return {
        "schema": ROUTING_CLOSURE_MANIFEST_SCHEMA,
        "routing_engine_identity": dict(routing_engine_identity),
        "parser_source_identities": parser_source_identities,
        "parser_source_identities_sha256": _payload_sha256(
            parser_source_identities
        ),
        "parsed_declarations_sha256": _parsed_declaration_digest(
            semantic_declarations
        ),
        "routing_ledger_sha256": _payload_sha256(routing_ledger),
        "selected_review_declarations": sorted(selected_qualified_names),
        "raw_active_review_roots": raw_active_review_roots,
        "raw_semantic_review_declarations": raw_semantic_review_declarations,
        "configured_auxiliary_declarations": sorted(auxiliary_qualified_names),
        "quarantined_auxiliary_declarations": sorted(
            quarantined_auxiliary_qualified_names
        ),
        "selected_root_source_associations": selected_root_source_associations,
    }


def _live_routing_snapshot(
    root: Path,
    paper_dir: Path,
    paper: str,
    raw: Mapping[str, Any],
    *,
    helper_path: Path | None,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Recompute every routing input and every ledger entry from live sources."""

    engine_identity, _helper_identity_path = _routing_engine_identity_from_source(
        root, helper_path
    )
    helper, _loaded_helper_path = _load_routing_helper(root, helper_path)
    loaded_identity = getattr(
        helper, "REACHABLE_PAPER_INTERFACE_AUXILIARY_ROUTING_ENGINE_IDENTITY", None
    )
    if loaded_identity != engine_identity:
        raise AuxiliaryRoutingSupplementError(
            "reachable-auxiliary parser identity differs between source and execution"
        )

    status_path = paper_dir / "status.json"
    statement_map_path = paper_dir / "audit" / "paper_statement_map.json"
    status_payload, _status_bytes = _load_json_object(status_path)
    _map_payload, map_bytes = _load_json_object(statement_map_path)
    map_identity = _file_identity(root, statement_map_path, label="paper_statement_map.json")
    raw_fingerprint = raw.get("source_record_input_fingerprint")
    if not isinstance(raw_fingerprint, dict):
        raise AuxiliaryRoutingSupplementError(
            "raw source-record input fingerprint is malformed"
        )
    # ``relevant_status_sha256`` is a generator-owned semantic projection, not
    # a raw status-file hash.  The full current raw identity replay below owns
    # that projection comparison; this supplement additionally pins the exact
    # status bytes because routing directly reads review/auxiliary configuration.
    if not _is_sha256(raw_fingerprint.get("relevant_status_sha256")):
        raise AuxiliaryRoutingSupplementError(
            "raw source-record input fingerprint has no relevant-status receipt"
        )
    if str(raw.get("paper_statement_map_sha256") or "").strip().lower() != map_identity[
        "sha256"
    ]:
        raise AuxiliaryRoutingSupplementError(
            "paper_statement_map.json no longer matches the raw source-record receipt"
        )

    interface_path, interface_identity = _raw_interface_path(root, paper_dir, raw)
    expected_interface = helper.review_source_path(root, paper_dir, status_path)
    if expected_interface.resolve() != interface_path.resolve():
        raise AuxiliaryRoutingSupplementError(
            "status.json now selects a different PaperInterface source"
        )
    assumption_identity = _raw_assumption_identity(root, paper_dir, raw)
    assumptions_path = paper_dir / "Assumptions.lean"
    interface_declarations = helper.parse_declarations(interface_path)
    interface_namespace = helper.first_declaration_namespace(interface_path)
    assumption_declarations: dict[str, str] = {}
    assumption_namespace = ""
    if assumptions_path.exists():
        assumption_declarations = helper.parse_declarations(assumptions_path)
        assumption_namespace = helper.first_declaration_namespace(assumptions_path)

    raw_active_review_roots = _raw_active_review_roots(raw)
    _current_active_review_rows(status_payload, raw_active_review_roots)
    selected_qualified_names = {
        active_root["qualified_declaration"]
        for active_root in raw_active_review_roots
    }
    available_review_declarations = set(interface_declarations) | set(
        assumption_declarations
    )
    missing_current_roots = sorted(
        selected_qualified_names - available_review_declarations
    )
    if missing_current_roots:
        raise AuxiliaryRoutingSupplementError(
            "raw active review declaration is absent from the current review surface"
        )
    auxiliary_qualified_names = _resolve_auxiliary_names(
        helper,
        rows=helper.parse_status_auxiliary_rows(status_path),
        interface_declarations=interface_declarations,
        interface_namespace=interface_namespace,
        assumption_declarations=assumption_declarations,
        assumption_namespace=assumption_namespace,
    )
    quarantined_auxiliary_qualified_names = _resolve_auxiliary_names(
        helper,
        rows=helper.parse_status_quarantined_auxiliary_rows(status_path),
        interface_declarations=interface_declarations,
        interface_namespace=interface_namespace,
        assumption_declarations=assumption_declarations,
        assumption_namespace=assumption_namespace,
    )
    parser_files, parser_source_identities = _raw_lean_dependency_sources(root, raw)
    semantic_declarations = helper.parse_local_declarations(root, parser_files)
    selected_row_names_by_qualified: dict[str, set[str]] = {}
    for active_root in raw_active_review_roots:
        selected_row_names_by_qualified.setdefault(
            active_root["qualified_declaration"], set()
        ).add(active_root["row"])
    raw_semantic_review_declarations = _raw_active_review_declarations(raw)
    if set(raw_semantic_review_declarations) != selected_qualified_names:
        raise AuxiliaryRoutingSupplementError(
            "issued routing roots do not exactly match raw active review rows"
        )
    routing_ledger = helper.reachable_paper_interface_auxiliary_routing(
        paper_dir=paper_dir,
        status_path=status_path,
        interface_declarations=interface_declarations,
        selected_qualified_names=selected_qualified_names,
        selected_row_names_by_qualified=selected_row_names_by_qualified,
        auxiliary_qualified_names=auxiliary_qualified_names,
        quarantined_auxiliary_qualified_names=quarantined_auxiliary_qualified_names,
        local_declarations=semantic_declarations,
    )
    if not isinstance(routing_ledger, dict) or set(routing_ledger) != set(LEDGER_KEYS):
        raise AuxiliaryRoutingSupplementError(
            "reachable-auxiliary parser emitted a malformed routing ledger"
        )
    fidelity_path = _source_proof_fidelity_path(root, paper_dir, status_payload)
    fidelity_identity = _file_identity(root, fidelity_path, label="source-proof fidelity ledger")
    if raw_fingerprint.get("source_proof_fidelity_sha256") != fidelity_identity["sha256"]:
        raise AuxiliaryRoutingSupplementError(
            "source-proof fidelity ledger no longer matches the raw input fingerprint"
        )
    inputs = _routing_inputs(
        paper=paper,
        routing_engine_identity=engine_identity,
        routing_status_projection=_routing_status_projection(
            root,
            paper_dir,
            status_payload,
            raw_active_review_roots=raw_active_review_roots,
        ),
        map_identity=map_identity,
        interface_identity=interface_identity,
        assumption_identity=assumption_identity,
        fidelity_identity=fidelity_identity,
        raw_fingerprint=raw_fingerprint,
    )
    selected_root_source_associations = _source_association_projection(
        raw, set(raw_semantic_review_declarations)
    )
    manifest = _routing_closure_manifest(
        routing_engine_identity=engine_identity,
        parser_source_identities=parser_source_identities,
        semantic_declarations=semantic_declarations,
        selected_qualified_names=selected_qualified_names,
        auxiliary_qualified_names=auxiliary_qualified_names,
        quarantined_auxiliary_qualified_names=quarantined_auxiliary_qualified_names,
        raw_active_review_roots=raw_active_review_roots,
        raw_semantic_review_declarations=raw_semantic_review_declarations,
        selected_root_source_associations=selected_root_source_associations,
        routing_ledger=routing_ledger,
    )
    # The raw map is parsed above, and its byte pin is part of the live
    # identity.  Keep this local read explicit so a malformed map cannot turn
    # into an empty route index through an exception or absent-file fallback.
    _ = map_bytes
    return inputs, routing_ledger, manifest


def _raw_binding(
    root: Path,
    paper_dir: Path,
    raw: Mapping[str, Any],
    raw_bytes: bytes,
) -> dict[str, str]:
    raw_path = paper_dir / "audit" / "source_record_audit.json"
    return {
        "path": _relative(root, raw_path, label="canonical raw source-record audit"),
        "bytes_sha256": _bytes_sha256(raw_bytes),
        "payload_sha256": _payload_sha256(raw),
        "source_record_audit_sha256": str(raw["source_record_audit_sha256"]),
        "source_record_audit_integrity_sha256": str(
            raw["source_record_audit_integrity_sha256"]
        ),
        "source_record_input_fingerprint_sha256": _payload_sha256(
            raw["source_record_input_fingerprint"]
        ),
    }


def _raw_binding_error(
    binding: object,
    expected: Mapping[str, str],
) -> str:
    if not isinstance(binding, dict) or set(binding) != set(expected):
        return "supplement raw binding has an unsupported shape"
    if binding != expected:
        return "supplement raw binding does not match the exact current raw receipt"
    return ""


def build_auxiliary_routing_supplement(
    *,
    root: Path,
    paper: str,
    raw_audit_path: Path | None = None,
    verify_current_raw_identity: bool = True,
    helper_path: Path | None = None,
) -> dict[str, Any]:
    """Build one narrow, replayable routing supplement without a raw scan."""

    root = root.resolve()
    paper_dir = root / "papers" / paper
    if not paper_dir.is_dir():
        raise AuxiliaryRoutingSupplementError(f"paper directory does not exist: {paper_dir}")
    canonical_raw_path = paper_dir / "audit" / "source_record_audit.json"
    candidate = raw_audit_path or canonical_raw_path
    if candidate.resolve() != canonical_raw_path.resolve():
        raise AuxiliaryRoutingSupplementError(
            "routing supplements may bind only the canonical paper-local raw audit"
        )
    raw, raw_bytes = _load_json_object(canonical_raw_path)
    if error := _raw_v10_receipt_error(raw, paper=paper):
        raise AuxiliaryRoutingSupplementError(error)
    if verify_current_raw_identity:
        if error := _current_raw_identity_error(root, paper_dir, raw):
            raise AuxiliaryRoutingSupplementError(error)
    inputs, routing_ledger, closure_manifest = _live_routing_snapshot(
        root, paper_dir, paper, raw, helper_path=helper_path
    )
    return {
        "schema": SUPPLEMENT_SCHEMA,
        "paper": paper,
        "kind": "source_record_reachable_auxiliary_routing_supplement",
        "raw_binding": _raw_binding(root, paper_dir, raw, raw_bytes),
        "routing_inputs": inputs,
        "routing_inputs_sha256": _payload_sha256(inputs),
        "routing_closure_manifest": closure_manifest,
        "routing_closure_manifest_sha256": _payload_sha256(closure_manifest),
        "routing_ledger": routing_ledger,
        "routing_ledger_sha256": _payload_sha256(routing_ledger),
    }


def _validate_supplement_shape(payload: object, *, paper: str) -> str:
    expected = {
        "schema",
        "paper",
        "kind",
        "raw_binding",
        "routing_inputs",
        "routing_inputs_sha256",
        "routing_closure_manifest",
        "routing_closure_manifest_sha256",
        "routing_ledger",
        "routing_ledger_sha256",
    }
    if not isinstance(payload, dict) or set(payload) != expected:
        return "supplement has an unsupported top-level shape"
    if payload.get("schema") != SUPPLEMENT_SCHEMA:
        return "supplement has an unsupported schema"
    if payload.get("paper") != paper:
        return "supplement paper does not match the current paper"
    if payload.get("kind") != "source_record_reachable_auxiliary_routing_supplement":
        return "supplement kind is unsupported"
    inputs = payload.get("routing_inputs")
    manifest = payload.get("routing_closure_manifest")
    ledger = payload.get("routing_ledger")
    if (
        not isinstance(inputs, dict)
        or not isinstance(manifest, dict)
        or not isinstance(ledger, dict)
    ):
        return "supplement routing inputs, closure manifest, or ledger is malformed"
    supplement_identity = inputs.get("supplement_engine_identity")
    if (
        not isinstance(supplement_identity, dict)
        or set(supplement_identity) != {"path", "surface_semantic_version"}
        or not isinstance(supplement_identity.get("path"), str)
        or not supplement_identity["path"].strip()
        or not isinstance(supplement_identity.get("surface_semantic_version"), str)
        or not supplement_identity["surface_semantic_version"].strip()
    ):
        return "supplement routing inputs have a malformed producer identity"
    if set(ledger) != set(LEDGER_KEYS):
        return "supplement routing ledger has an unsupported shape"
    if payload.get("routing_inputs_sha256") != _payload_sha256(inputs):
        return "supplement routing-input receipt does not match its contents"
    if payload.get("routing_closure_manifest_sha256") != _payload_sha256(manifest):
        return "supplement routing-closure-manifest receipt does not match its contents"
    if payload.get("routing_ledger_sha256") != _payload_sha256(ledger):
        return "supplement routing-ledger receipt does not match its contents"
    return ""


def _canonical_current_raw(
    *,
    root: Path,
    paper_dir: Path,
    paper: str,
    audit_payload: Mapping[str, Any],
    verify_current_raw_identity: bool,
) -> tuple[dict[str, Any] | None, bytes | None, str]:
    """Authenticate the raw receipt shared by direct and supplemented ledgers."""

    raw_path = paper_dir / "audit" / "source_record_audit.json"
    try:
        raw, raw_bytes = _load_json_object(raw_path)
    except AuxiliaryRoutingSupplementError as error:
        return None, None, str(error)
    if _payload_sha256(raw) != _payload_sha256(audit_payload):
        return None, None, "runtime raw audit does not exactly match the canonical raw receipt"
    if error := _raw_v10_receipt_error(raw, paper=paper):
        return None, None, error
    if verify_current_raw_identity:
        if error := _current_raw_identity_error(root, paper_dir, raw):
            return None, None, error
    return raw, raw_bytes, ""


def _status_selected_interface_path(
    *, root: Path, paper_dir: Path, status_payload: Mapping[str, Any]
) -> Path:
    """Replay the canonical PaperInterface selection without loading the parser."""

    canonical = paper_dir / "PaperInterface.lean"
    review_surface = status_payload.get("review_surface")
    raw_path = review_surface.get("source_file") if isinstance(review_surface, dict) else None
    if raw_path is None:
        return canonical
    if not isinstance(raw_path, str) or not raw_path.strip():
        raise AuxiliaryRoutingSupplementError(
            "status.json review_surface.source_file is malformed"
        )
    configured = Path(raw_path.strip())
    if configured.is_absolute():
        resolved = configured.resolve()
    elif len(configured.parts) == 1:
        resolved = (paper_dir / configured).resolve()
    else:
        resolved = (root / configured).resolve()
    if resolved != canonical.resolve():
        raise AuxiliaryRoutingSupplementError(
            "status.json now selects a different PaperInterface source"
        )
    return canonical


def _current_routing_inputs_without_parser(
    *,
    root: Path,
    paper_dir: Path,
    paper: str,
    raw: Mapping[str, Any],
    helper_path: Path | None,
) -> dict[str, Any]:
    """Rebuild only byte/receipt identities, never a Lean declaration closure."""

    status_path = paper_dir / "status.json"
    map_path = paper_dir / "audit" / "paper_statement_map.json"
    status_payload, _status_bytes = _load_json_object(status_path)
    _map_payload, _map_bytes = _load_json_object(map_path)
    map_identity = _file_identity(root, map_path, label="paper_statement_map.json")
    raw_fingerprint = raw.get("source_record_input_fingerprint")
    if not isinstance(raw_fingerprint, dict):
        raise AuxiliaryRoutingSupplementError(
            "raw source-record input fingerprint is malformed"
        )
    if not _is_sha256(raw_fingerprint.get("relevant_status_sha256")):
        raise AuxiliaryRoutingSupplementError(
            "raw source-record input fingerprint has no relevant-status receipt"
        )
    if str(raw.get("paper_statement_map_sha256") or "").strip().lower() != map_identity[
        "sha256"
    ]:
        raise AuxiliaryRoutingSupplementError(
            "paper_statement_map.json no longer matches the raw source-record receipt"
        )
    interface_path, interface_identity = _raw_interface_path(root, paper_dir, raw)
    if _status_selected_interface_path(
        root=root, paper_dir=paper_dir, status_payload=status_payload
    ).resolve() != interface_path.resolve():
        raise AuxiliaryRoutingSupplementError(
            "status.json now selects a different PaperInterface source"
        )
    assumption_identity = _raw_assumption_identity(root, paper_dir, raw)
    fidelity_path = _source_proof_fidelity_path(root, paper_dir, status_payload)
    fidelity_identity = _file_identity(root, fidelity_path, label="source-proof fidelity ledger")
    if raw_fingerprint.get("source_proof_fidelity_sha256") != fidelity_identity["sha256"]:
        raise AuxiliaryRoutingSupplementError(
            "source-proof fidelity ledger no longer matches the raw input fingerprint"
        )
    routing_engine_identity, _engine_path = _routing_engine_identity_from_source(
        root, helper_path
    )
    raw_active_review_roots = _raw_active_review_roots(raw)
    return _routing_inputs(
        paper=paper,
        routing_engine_identity=routing_engine_identity,
        routing_status_projection=_routing_status_projection(
            root,
            paper_dir,
            status_payload,
            raw_active_review_roots=raw_active_review_roots,
        ),
        map_identity=map_identity,
        interface_identity=interface_identity,
        assumption_identity=assumption_identity,
        fidelity_identity=fidelity_identity,
        raw_fingerprint=raw_fingerprint,
    )


def _validate_closure_manifest_shape(manifest: object) -> str:
    expected = {
        "schema",
        "routing_engine_identity",
        "parser_source_identities",
        "parser_source_identities_sha256",
        "parsed_declarations_sha256",
        "routing_ledger_sha256",
        "selected_review_declarations",
        "raw_active_review_roots",
        "raw_semantic_review_declarations",
        "configured_auxiliary_declarations",
        "quarantined_auxiliary_declarations",
        "selected_root_source_associations",
    }
    if not isinstance(manifest, dict) or set(manifest) != expected:
        return "supplement routing-closure manifest has an unsupported shape"
    if manifest.get("schema") != ROUTING_CLOSURE_MANIFEST_SCHEMA:
        return "supplement routing-closure manifest has an unsupported schema"
    identity = manifest.get("routing_engine_identity")
    if not isinstance(identity, dict) or set(identity) != {
        "path",
        "surface_semantic_version",
    }:
        return "supplement routing-closure manifest has a malformed engine identity"
    sources = manifest.get("parser_source_identities")
    if not isinstance(sources, list) or not sources:
        return "supplement routing-closure manifest has no parser-source identities"
    previous_path = ""
    for source in sources:
        if not isinstance(source, dict) or set(source) != {"path", "sha256"}:
            return "supplement routing-closure manifest has a malformed parser-source identity"
        path = source.get("path")
        digest = source.get("sha256")
        if (
            not isinstance(path, str)
            or not path
            or Path(path).is_absolute()
            or path <= previous_path
            or not _is_sha256(digest)
        ):
            return "supplement routing-closure manifest has unsorted or malformed parser sources"
        previous_path = path
    if manifest.get("parser_source_identities_sha256") != _payload_sha256(sources):
        return "supplement routing-closure manifest parser-source receipt does not match"
    if not _is_sha256(manifest.get("parsed_declarations_sha256")):
        return "supplement routing-closure manifest parsed-declaration receipt is malformed"
    if not _is_sha256(manifest.get("routing_ledger_sha256")):
        return "supplement routing-closure manifest ledger receipt is malformed"
    for key in (
        "selected_review_declarations",
        "raw_semantic_review_declarations",
        "configured_auxiliary_declarations",
        "quarantined_auxiliary_declarations",
    ):
        values = manifest.get(key)
        if not isinstance(values, list) or any(
            not isinstance(value, str) or not value for value in values
        ):
            return f"supplement routing-closure manifest has malformed {key}"
        if values != sorted(set(values)):
            return f"supplement routing-closure manifest has malformed {key}"
    active_roots = manifest.get("raw_active_review_roots")
    if not isinstance(active_roots, list):
        return "supplement routing-closure manifest has malformed raw active review roots"
    if active_roots != sorted(
        active_roots,
        key=lambda root: (
            root.get("qualified_declaration", "") if isinstance(root, dict) else "",
            root.get("row", "") if isinstance(root, dict) else "",
        ),
    ) or any(
        not isinstance(root, dict)
        or set(root) != {"row", "qualified_declaration"}
        or not isinstance(root.get("row"), str)
        or not root["row"]
        or not isinstance(root.get("qualified_declaration"), str)
        or "." not in root["qualified_declaration"]
        for root in active_roots
    ):
        return "supplement routing-closure manifest has malformed raw active review roots"
    if [root["qualified_declaration"] for root in active_roots] != manifest[
        "raw_semantic_review_declarations"
    ]:
        return "supplement routing-closure manifest raw active roots do not match declarations"
    if not isinstance(manifest.get("selected_root_source_associations"), list):
        return "supplement routing-closure manifest has malformed source associations"
    return ""


def _current_parser_sources_match_manifest(
    root: Path, manifest: Mapping[str, Any]
) -> str:
    """Check every issued parser input byte without rerunning the parser.

    The manifest's source list is complete because issuance collected the exact
    recursive closure.  An import edit itself changes one of these pinned
    files, so validation cannot miss a newly reachable file while avoiding a
    second recursive import walk.
    """

    sources = manifest["parser_source_identities"]
    assert isinstance(sources, list)  # Checked by _validate_closure_manifest_shape.
    for expected in sources:
        assert isinstance(expected, dict)
        raw_path = expected["path"]
        assert isinstance(raw_path, str)
        try:
            actual = _file_identity(
                root, root / raw_path, label="routing parser source"
            )
        except AuxiliaryRoutingSupplementError as error:
            return str(error)
        if actual != expected:
            return "supplement routing parser-source identity changed"
    return ""


def validate_auxiliary_routing_supplement(
    *,
    root: Path,
    paper_dir: Path,
    paper: str,
    audit_payload: Mapping[str, Any],
    verify_current_raw_identity: bool = True,
    helper_path: Path | None = None,
) -> tuple[ValidatedAuxiliaryRoutingContext | None, str]:
    """Load an issued closure manifest without reparsing its Lean sources.

    Issuance performs the exact parser replay once.  This consumer path checks
    the raw receipt, every current input byte identity, the routing-engine
    semantic version, and each parser-source identity before returning the
    recorded deterministic ledger.  A mismatch is a hard failure that asks
    for a fresh narrow issuance, never a silent stale reuse.
    """

    root = root.resolve()
    supplement_path = paper_dir / "audit" / SUPPLEMENT_BASENAME
    if not supplement_path.is_file():
        return None, "current raw audit lacks a routing ledger and no supplement exists"
    try:
        supplement, _supplement_bytes = _load_json_object(supplement_path)
        if error := _validate_supplement_shape(supplement, paper=paper):
            return None, error
        raw, raw_bytes, raw_error = _canonical_current_raw(
            root=root,
            paper_dir=paper_dir,
            paper=paper,
            audit_payload=audit_payload,
            verify_current_raw_identity=verify_current_raw_identity,
        )
        if raw_error or raw is None or raw_bytes is None:
            return None, raw_error or "could not authenticate canonical raw audit"
        expected_binding = _raw_binding(root, paper_dir, raw, raw_bytes)
        if error := _raw_binding_error(supplement.get("raw_binding"), expected_binding):
            return None, error
        live_inputs = _current_routing_inputs_without_parser(
            root=root,
            paper_dir=paper_dir,
            paper=paper,
            raw=raw,
            helper_path=helper_path,
        )
        if supplement.get("routing_inputs") != live_inputs:
            return None, "supplement routing inputs no longer match current identities"
        manifest = supplement.get("routing_closure_manifest")
        if error := _validate_closure_manifest_shape(manifest):
            return None, error
        assert isinstance(manifest, dict)
        try:
            raw_dependency_projection = _raw_lean_dependency_projection(raw)
            raw_active_roots = _raw_active_review_roots(raw)
            raw_semantic_roots = _raw_active_review_declarations(raw)
            manifest_selected_roots = manifest["selected_review_declarations"]
            manifest_active_roots = manifest["raw_active_review_roots"]
            manifest_semantic_roots = manifest["raw_semantic_review_declarations"]
            assert isinstance(manifest_selected_roots, list)
            assert isinstance(manifest_active_roots, list)
            assert isinstance(manifest_semantic_roots, list)
            raw_associations = _source_association_projection(
                raw, set(raw_semantic_roots)
            )
        except AuxiliaryRoutingSupplementError as error:
            return None, str(error)
        if manifest["parser_source_identities"] != raw_dependency_projection:
            return None, "supplement parser closure does not match the raw Lean dependency receipt"
        if manifest_active_roots != raw_active_roots:
            return None, "supplement active routing roots do not match the raw review ledger"
        if manifest_semantic_roots != raw_semantic_roots:
            return None, "supplement semantic routing roots do not match the raw review ledger"
        if manifest_selected_roots != raw_semantic_roots:
            return None, "supplement selected routing roots do not exactly match raw active review rows"
        if manifest["selected_root_source_associations"] != raw_associations:
            return None, "supplement source-association projection does not match the raw audit"
        if manifest["routing_ledger_sha256"] != supplement[
            "routing_ledger_sha256"
        ]:
            return None, "supplement routing ledger is not bound to its closure manifest"
        if manifest["routing_engine_identity"] != live_inputs[
            "routing_engine_identity"
        ]:
            return None, "supplement routing-closure engine identity is stale"
        if error := _current_parser_sources_match_manifest(root, manifest):
            return None, error
        return (
            ValidatedAuxiliaryRoutingContext(
                paper=paper,
                provenance="replayed_auxiliary_routing_supplement",
                _raw_payload_sha256=_payload_sha256(raw),
                _ledger_json=_canonical_json(supplement["routing_ledger"]),
            ),
            "",
        )
    except AuxiliaryRoutingSupplementError as error:
        return None, str(error)


def current_auxiliary_routing_context(
    *,
    root: Path,
    paper_dir: Path,
    paper: str,
    audit_payload: Mapping[str, Any],
    verify_current_raw_identity: bool = True,
    helper_path: Path | None = None,
) -> tuple[ValidatedAuxiliaryRoutingContext | None, str]:
    """Return one authenticated routing context for both closeout consumers."""

    present = [key for key in LEDGER_KEYS if key in audit_payload]
    if present and len(present) != len(LEDGER_KEYS):
        return None, "raw source-record audit has a partial reachable-auxiliary ledger"
    if len(present) == len(LEDGER_KEYS):
        raw = dict(audit_payload)
        if error := _raw_v10_receipt_error(raw, paper=paper):
            return None, error
        if verify_current_raw_identity:
            if error := _current_raw_identity_error(root.resolve(), paper_dir, raw):
                return None, error
        ledger = {key: audit_payload[key] for key in LEDGER_KEYS}
        if any(not isinstance(ledger[key], list) for key in LEDGER_KEYS):
            return None, "raw source-record audit has a malformed reachable-auxiliary ledger"
        return (
            ValidatedAuxiliaryRoutingContext(
                paper=paper,
                provenance="generated_raw_routing_ledger",
                _raw_payload_sha256=_payload_sha256(audit_payload),
                _ledger_json=_canonical_json(ledger),
            ),
            "",
        )
    return validate_auxiliary_routing_supplement(
        root=root,
        paper_dir=paper_dir,
        paper=paper,
        audit_payload=audit_payload,
        verify_current_raw_identity=verify_current_raw_identity,
        helper_path=helper_path,
    )


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


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--raw-audit", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    try:
        supplement = build_auxiliary_routing_supplement(
            root=root,
            paper=args.paper,
            raw_audit_path=args.raw_audit,
        )
        output_path = args.out or (
            paper_dir / "audit" / SUPPLEMENT_BASENAME
        )
        if not output_path.is_absolute():
            output_path = root / output_path
        output_path = _inside(root, output_path, label="supplement output")
        if args.write:
            _atomic_write(
                output_path,
                (json.dumps(supplement, indent=2, sort_keys=True) + "\n").encode(
                    "utf-8"
                ),
            )
            context, error = validate_auxiliary_routing_supplement(
                root=root,
                paper_dir=paper_dir,
                paper=args.paper,
                audit_payload=_load_json_object(
                    paper_dir / "audit" / "source_record_audit.json"
                )[0],
            )
            if error or context is None:
                raise AuxiliaryRoutingSupplementError(
                    "written supplement did not validate: " + error
                )
            print(f"{args.paper}: wrote replayed auxiliary-routing supplement to {output_path}")
        else:
            print(
                f"{args.paper}: auxiliary-routing supplement validates; rerun with --write"
            )
    except AuxiliaryRoutingSupplementError as error:
        print(f"{args.paper}: auxiliary-routing supplement refused: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
