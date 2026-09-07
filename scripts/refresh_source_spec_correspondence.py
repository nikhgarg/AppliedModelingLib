#!/usr/bin/env python3
"""Conservatively refresh established v11 source-to-Spec receipt hashes.

This is deliberately *not* a source-to-Lean mapper.  A correspondence record
contains human-reviewed semantic bridges from byte-pinned source atoms to a
Lean-owned canonical `Spec` surface, along with dispositions for every
material non-foundation closure terminal.  Neither bridge can be regenerated
from declaration names, source-row keys, or a changed closure shape.

The command therefore runs Lean's canonical closure extractor and changes only
the receipt fields derived from data that has remained structurally covered:

* `source_atoms_sha256`;
* `spec_closure_sha256`;
* `spec_surface_sha256`;
* `closure_environment_sha256`; and
* `item_identity_sha256`.

It preserves the reviewed semantic bridges and `closure_node_dispositions`
byte for byte.  Before accepting a candidate it asks the existing runtime
validator to check those mappings against the new Lean-owned closure.  The
only component-coordinate rewrite it can make is a complete-Spec root rebind:
an old singleton root component may be replaced by the current root only when
the paper's current v11 verbatim-source-to-expanded-Spec review is independently
current.  Subcomponent mappings, added/removed material terminals, changed
external pins, and malformed retained evidence are refusals, not guessed
rebinds.  It also does not create missing correspondence records.

Use the default dry run first.  A successful `--write` is atomic for the
selected established records, but is only a receipt refresh: run the normal
paper closeout afterward to recheck the full proof and evidence lanes.
"""

from __future__ import annotations

import argparse
import copy
import json
import os
import re
import sys
import tempfile
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import audit_evidence_integrity as integrity  # noqa: E402
from scripts import audit_repository as repository  # noqa: E402
from scripts.obligation_routes import (  # noqa: E402
    EvidenceRouteSet,
    ObligationRouteError,
)
from scripts.lean_signature_manifest import (  # noqa: E402
    foreign_model_definition_scope,
    paper_local_module_names,
    run_lean_semantic_contract_closure_manifests,
)
from scripts.review_dashboard import (  # noqa: E402
    review_source_file,
    review_source_module,
)


SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
STATEMENT_MAP_RELATIVE_PATH = Path("audit") / "paper_statement_map.json"
DERIVED_RECEIPT_FIELDS = frozenset(
    {
        "source_atoms_sha256",
        "spec_closure_sha256",
        "spec_surface_sha256",
        "closure_environment_sha256",
        "item_identity_sha256",
    }
)
DEFAULT_TIMEOUT_SECONDS = 180
DEFAULT_BUILD_TIMEOUT_SECONDS = 600


@dataclass(frozen=True)
class RefreshCandidate:
    """One accepted receipt update with no unreviewed semantic mapping rewrite."""

    correspondence: dict[str, Any]
    changed: bool


def _digest(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if SHA256_RE.fullmatch(text) else ""


def _json_equal(left: object, right: object) -> bool:
    """Compare JSON values without treating incidental mapping order as content."""

    try:
        return json.dumps(left, sort_keys=True, separators=(",", ":")) == json.dumps(
            right, sort_keys=True, separators=(",", ":")
        )
    except (TypeError, ValueError):
        return False


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"could not read JSON object {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return payload


def _closure_receipt_fields(closure: object) -> tuple[dict[str, str] | None, list[str]]:
    """Extract only the machine-derived receipt fields from a Lean closure."""

    if not isinstance(closure, Mapping):
        return None, ["Lean did not return a closure object"]
    values = {
        "spec_closure_sha256": _digest(closure.get("sha256")),
        "spec_surface_sha256": _digest(closure.get("surface_sha256")),
        "closure_environment_sha256": _digest(
            repository.semantic_contract_closure_environment_sha256(closure)
        ),
    }
    errors = [
        f"current Lean closure has no valid {field}"
        for field, value in values.items()
        if not value
    ]
    if not isinstance(closure.get("surface"), Mapping):
        errors.append("current Lean closure did not expose a canonical Spec surface")
    return (values if not errors else None), errors


def _exact_quote_atom_identity_rebinds(
    raw_atoms: list[object],
) -> dict[str, str]:
    """Map a legacy atom coordinate to its exact-quote coordinate.

    Schema 2 deliberately drops curator prose and source line numbers from the
    semantic identity and uses the byte-pinned quote alone.  The v11 activator
    may upgrade an otherwise unchanged atom before an older correspondence is
    refreshed.  Reconstruct the legacy identity from the same current atom so
    a caller with independent current v11 authority can change only that
    coordinate, rather than reopening the reviewed mapping.
    """

    rebinds: dict[str, str] = {}
    for raw_atom in raw_atoms:
        if not isinstance(raw_atom, dict):
            continue
        if raw_atom.get(
            integrity.SOURCE_CLAIM_ATOM_IDENTITY_SCHEMA_FIELD
        ) not in integrity.EXACT_SOURCE_CLAIM_ATOM_IDENTITY_SCHEMAS:
            continue
        current_sha = integrity.source_claim_atom_semantic_sha256(raw_atom)
        legacy_atom = dict(raw_atom)
        legacy_atom[integrity.SOURCE_CLAIM_ATOM_IDENTITY_SCHEMA_FIELD] = (
            integrity.LEGACY_SOURCE_CLAIM_ATOM_IDENTITY_SCHEMA
        )
        legacy_sha = integrity.source_claim_atom_semantic_sha256(legacy_atom)
        if not _digest(current_sha) or not _digest(legacy_sha):
            continue
        prior = rebinds.get(legacy_sha)
        if prior is not None and prior != current_sha:
            return {}
        rebinds[legacy_sha] = current_sha
    return rebinds


def refresh_existing_correspondence(
    raw_item: object,
    closure: object,
    *,
    allow_whole_surface_rebind: bool = False,
) -> tuple[RefreshCandidate | None, list[str]]:
    """Refresh one existing record only when its semantic structure survives.

    This pure helper is intentionally suitable for fixture tests.  It does not
    call Lean itself; the CLI obtains `closure` from the production Lean API.
    It never makes a new bridge/disposition choice and so cannot accidentally
    convert a changed Spec or terminal dependency into a reusable receipt.
    """

    if not isinstance(raw_item, Mapping):
        return None, ["source item is malformed"]
    raw_correspondence = raw_item.get(integrity.SOURCE_SPEC_CORRESPONDENCE_KEY)
    if not isinstance(raw_correspondence, Mapping):
        return None, ["no established source_spec_correspondence record to refresh"]
    raw_contract = raw_item.get("semantic_contract")
    raw_atoms = raw_item.get(integrity.SOURCE_CLAIM_ATOMS_KEY)
    if not isinstance(raw_contract, Mapping):
        return None, ["source item has no semantic_contract"]
    if not isinstance(raw_atoms, list):
        return None, ["source item has no source_claim_atoms list"]

    # The old identity binds evidence_mode and semantic_shape as well as the
    # existing record.  Requiring it to be self-consistent means a changed
    # theorem-to-Spec relationship cannot be laundered merely by refreshing
    # its receipt fields.  Ordinary stale closures still pass: their old
    # receipt and old identity remain mutually consistent.
    existing_identity = _digest(raw_correspondence.get("item_identity_sha256"))
    expected_existing_identity = integrity.source_spec_correspondence_item_identity_sha256(
        dict(raw_contract), dict(raw_correspondence)
    )
    if not existing_identity or existing_identity != expected_existing_identity:
        return None, [
            "existing item_identity_sha256 is not self-consistent with the current "
            "semantic_contract; refresh cannot carry a changed evidence relationship"
        ]

    receipt_fields, receipt_errors = _closure_receipt_fields(closure)
    if receipt_errors:
        return None, receipt_errors
    assert receipt_fields is not None

    source_atoms_sha = integrity.source_claim_atoms_semantic_sha256(raw_atoms)
    if not _digest(source_atoms_sha):
        return None, [
            "current source_claim_atoms have no unique semantic identity; "
            "refresh cannot choose bindings"
        ]

    # Preserve the reviewed semantic mapping.  A singleton component equal to
    # the former complete-Spec root is a coordinate for the whole proposition,
    # not a hand-selected subexpression.  It may be rebound to the current
    # complete-Spec root only after the separate v11 raw-source-to-expanded-Spec
    # lane has directly accepted the current proposition.  This is deliberately
    # narrower than accepting a renamed/moved subcomponent by resemblance.
    candidate = copy.deepcopy(dict(raw_correspondence))
    original_bindings = copy.deepcopy(candidate.get("source_atom_bindings"))
    original_dispositions = copy.deepcopy(
        candidate.get("closure_node_dispositions")
    )
    old_surface_sha = _digest(raw_correspondence.get("spec_surface_sha256"))
    new_surface_sha = receipt_fields["spec_surface_sha256"]
    rebound_root_count = 0
    atom_identity_rebinds = (
        _exact_quote_atom_identity_rebinds(raw_atoms)
        if allow_whole_surface_rebind
        else {}
    )
    if allow_whole_surface_rebind:
        bindings = candidate.get("source_atom_bindings")
        if isinstance(bindings, list):
            for binding in bindings:
                if not isinstance(binding, dict):
                    continue
                old_atom_sha = _digest(binding.get("source_atom_sha256"))
                if old_atom_sha in atom_identity_rebinds:
                    binding["source_atom_sha256"] = atom_identity_rebinds[
                        old_atom_sha
                    ]
                components = binding.get("spec_component_sha256s")
                normalized = (
                    [_digest(value) for value in components]
                    if isinstance(components, list)
                    else []
                )
                if (
                    old_surface_sha != new_surface_sha
                    and normalized == [old_surface_sha]
                ):
                    binding["spec_component_sha256s"] = [new_surface_sha]
                    rebound_root_count += 1
        dispositions = candidate.get("closure_node_dispositions")
        if isinstance(dispositions, list):
            for disposition in dispositions:
                if not isinstance(disposition, dict):
                    continue
                old_atom_sha = _digest(disposition.get("source_atom_sha256"))
                if old_atom_sha in atom_identity_rebinds:
                    disposition["source_atom_sha256"] = atom_identity_rebinds[
                        old_atom_sha
                    ]
    candidate["source_atoms_sha256"] = source_atoms_sha
    candidate.update(receipt_fields)
    candidate["item_identity_sha256"] = integrity.source_spec_correspondence_item_identity_sha256(
        dict(raw_contract), candidate
    )

    static_errors = integrity.source_spec_correspondence_validation_errors(
        candidate,
        raw_atoms=raw_atoms,
        raw_contract=dict(raw_contract),
    )
    if static_errors:
        return None, [
            "preserved correspondence is not a valid current source/Spec mapping: "
            + error
            for error in static_errors
        ]

    proposed_item = copy.deepcopy(dict(raw_item))
    proposed_item[integrity.SOURCE_SPEC_CORRESPONDENCE_KEY] = candidate
    runtime_errors = repository.source_spec_correspondence_runtime_errors(
        proposed_item, closure
    )
    if runtime_errors:
        return None, [
            "current Lean closure no longer supports the preserved semantic mapping: "
            + error
            for error in runtime_errors
        ]

    # A future refactor must not accidentally grow this writer into a mapper.
    # The sole non-derived change admitted here is the exact singleton
    # old-whole-root -> current-whole-root substitution and the exact
    # schema-1 -> schema-2 source-atom coordinate substitution above. The
    # semantic bridge, binding count/order, and all subcomponent choices remain
    # byte-identical.
    changed_nonderived = sorted(
        field
        for field in set(candidate) | set(raw_correspondence)
        if field not in DERIVED_RECEIPT_FIELDS
        and field not in {"source_atom_bindings", "closure_node_dispositions"}
        and not _json_equal(candidate.get(field), raw_correspondence.get(field))
    )
    if changed_nonderived:
        return None, [
            "internal safety check failed: refresh attempted to alter non-derived "
            "field(s): "
            + ", ".join(changed_nonderived)
        ]
    if not _json_equal(candidate.get("source_atom_bindings"), original_bindings):
        expected_bindings = copy.deepcopy(original_bindings)
        expected_rebound_count = 0
        if isinstance(expected_bindings, list):
            for binding in expected_bindings:
                if not isinstance(binding, dict):
                    continue
                old_atom_sha = _digest(binding.get("source_atom_sha256"))
                if old_atom_sha in atom_identity_rebinds:
                    binding["source_atom_sha256"] = atom_identity_rebinds[
                        old_atom_sha
                    ]
                components = binding.get("spec_component_sha256s")
                normalized = (
                    [_digest(value) for value in components]
                    if isinstance(components, list)
                    else []
                )
                if (
                    old_surface_sha != new_surface_sha
                    and normalized == [old_surface_sha]
                ):
                    binding["spec_component_sha256s"] = [new_surface_sha]
                    expected_rebound_count += 1
        if (
            not allow_whole_surface_rebind
            or rebound_root_count != expected_rebound_count
            or not _json_equal(candidate.get("source_atom_bindings"), expected_bindings)
        ):
            return None, [
                "internal safety check failed: refresh attempted an unreviewed "
                "source_atom_bindings rewrite"
            ]
    if not _json_equal(
        candidate.get("closure_node_dispositions"), original_dispositions
    ):
        expected_dispositions = copy.deepcopy(original_dispositions)
        if isinstance(expected_dispositions, list):
            for disposition in expected_dispositions:
                if not isinstance(disposition, dict):
                    continue
                old_atom_sha = _digest(disposition.get("source_atom_sha256"))
                if old_atom_sha in atom_identity_rebinds:
                    disposition["source_atom_sha256"] = atom_identity_rebinds[
                        old_atom_sha
                    ]
        if (
            not allow_whole_surface_rebind
            or not _json_equal(
                candidate.get("closure_node_dispositions"),
                expected_dispositions,
            )
        ):
            return None, [
                "internal safety check failed: refresh attempted an unreviewed "
                "closure_node_dispositions rewrite"
            ]
    changed = not _json_equal(candidate, raw_correspondence)
    return RefreshCandidate(candidate, changed), []


def _selected_record_items(
    payload: Mapping[str, Any],
    requested_items: Sequence[str],
) -> tuple[list[tuple[str, dict[str, Any]]], list[str], list[str]]:
    """Return established records and explicit navigation-only selection errors."""

    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return [], [], ["paper statement map has no items object"]
    requested = {value.strip() for value in requested_items if value.strip()}
    present = {str(key) for key in raw_items}
    unknown = sorted(requested - present)
    errors = [f"requested source-map item does not exist: {key}" for key in unknown]
    selected: list[tuple[str, dict[str, Any]]] = []
    skipped: list[str] = []
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key)
        if requested and key not in requested:
            continue
        if not isinstance(raw_item, dict):
            if not requested:
                continue
            errors.append(f"{key}: source-map item is malformed")
            continue
        if not isinstance(raw_item.get(integrity.SOURCE_SPEC_CORRESPONDENCE_KEY), dict):
            if requested:
                errors.append(f"{key}: no established source_spec_correspondence record")
            else:
                skipped.append(key)
            continue
        selected.append((key, raw_item))
    if not selected and not errors:
        errors.append("paper statement map has no established source_spec_correspondence records")
    return selected, sorted(skipped), errors


def _specification_name(raw_item: Mapping[str, Any]) -> tuple[str, str]:
    """Read a contract's canonical Spec route; row keys are never evidence."""

    raw_contract = raw_item.get("semantic_contract")
    if not isinstance(raw_contract, Mapping):
        return "", "source item has no semantic_contract"
    specification = str(raw_contract.get("spec_declaration") or "").strip()
    if not specification:
        return "", "semantic_contract has no spec_declaration"
    return specification, ""


def current_lean_closures(
    root: Path,
    folder: Path,
    items: Sequence[tuple[str, dict[str, Any]]],
    *,
    timeout_seconds: int,
    build_timeout_seconds: int,
) -> tuple[dict[str, dict[str, Any]], list[str]]:
    """Run the one canonical Lean-owned closure API for selected records."""

    specifications: set[str] = set()
    errors: list[str] = []
    for key, item in items:
        specification, error = _specification_name(item)
        if error:
            errors.append(f"{key}: {error}")
        else:
            specifications.add(specification)
    if errors:
        return {}, errors
    try:
        source_file = review_source_file(folder)
        import_module = review_source_module(folder, source_file)
    except (OSError, ValueError) as exc:
        return {}, [f"could not determine canonical review module: {exc}"]
    modules = paper_local_module_names(root, folder)
    if not modules:
        return {}, ["could not determine the PaperInterface-owned paper module closure"]
    foreign_definitions, foreign_modules, foreign_scope_error = (
        foreign_model_definition_scope(root, folder)
    )
    if foreign_scope_error:
        return {}, ["could not validate foreign model definition scope: " + foreign_scope_error]
    closures = run_lean_semantic_contract_closure_manifests(
        root,
        import_module,
        sorted(specifications),
        modules,
        foreign_model_definitions=foreign_definitions,
        foreign_model_modules=foreign_modules,
        max_expansions=512,
        timeout_seconds=timeout_seconds,
        build_timeout_seconds=build_timeout_seconds,
    )
    missing = sorted(specifications - set(closures))
    if missing:
        return {}, [
            "Lean closure extraction returned no receipt for: " + ", ".join(missing)
        ]
    malformed = [
        specification
        for specification in specifications
        if not isinstance(closures.get(specification), dict)
    ]
    if malformed:
        return {}, [
            "Lean closure extraction returned malformed receipt(s): "
            + ", ".join(sorted(malformed))
        ]
    return closures, []


def refreshed_payload(
    payload: Mapping[str, Any],
    closures: Mapping[str, object],
    *,
    requested_items: Sequence[str] = (),
    allow_whole_surface_rebind: bool = False,
) -> tuple[dict[str, Any] | None, list[str], list[str], list[str]]:
    """Build an all-or-nothing refreshed map without invoking Lean.

    Returns `(payload, refreshed_keys, skipped_keys, errors)`.  `payload` is
    `None` on every refusal, so callers cannot accidentally write a partial
    rebind after one changed semantic mapping.
    """

    selected, skipped, errors = _selected_record_items(payload, requested_items)
    if errors:
        return None, [], skipped, errors
    updated = copy.deepcopy(dict(payload))
    updated_items = updated.get("items")
    if not isinstance(updated_items, dict):  # Defensive after deepcopy.
        return None, [], skipped, ["paper statement map has no writable items object"]
    refreshed: list[str] = []
    for key, raw_item in selected:
        specification, specification_error = _specification_name(raw_item)
        if specification_error:
            errors.append(f"{key}: {specification_error}")
            continue
        closure = closures.get(specification)
        if closure is None:
            errors.append(f"{key}: no current Lean closure receipt for `{specification}`")
            continue
        candidate, candidate_errors = refresh_existing_correspondence(
            raw_item,
            closure,
            allow_whole_surface_rebind=allow_whole_surface_rebind,
        )
        if candidate_errors:
            errors.extend(f"{key}: {error}" for error in candidate_errors)
            continue
        assert candidate is not None
        updated_item = updated_items.get(key)
        if not isinstance(updated_item, dict):
            errors.append(f"{key}: source-map item disappeared during refresh")
            continue
        updated_item[integrity.SOURCE_SPEC_CORRESPONDENCE_KEY] = candidate.correspondence
        if candidate.changed:
            refreshed.append(key)
    if errors:
        return None, [], skipped, errors
    return updated, sorted(refreshed), skipped, []


def source_spec_correspondence_refresh_preflight(
    root: Path,
    folder: Path,
    *,
    payload: Mapping[str, Any] | None = None,
    evidence_context: object | None = None,
    whole_surface_rebind_authorized: bool = False,
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS,
    build_timeout_seconds: int = DEFAULT_BUILD_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Classify established realization receipts without modifying evidence.

    The result is intentionally scheduler-shaped but is not an acceptance
    credential.  ``refresh_required`` means the existing human-reviewed atom
    bindings and terminal dispositions survived the current Lean closure and
    only the five derived receipt hashes differ.  Every structural or semantic
    change is ``blocked`` rather than being guessed into a repair.
    """

    if payload is None:
        try:
            payload = _load_json_object(folder / STATEMENT_MAP_RELATIVE_PATH)
        except ValueError as exc:
            return {
                "schema": 1,
                "required": True,
                "state": "blocked",
                "current": False,
                "safe_refresh": False,
                "refreshed_items": [],
                "errors": [str(exc)],
                "acceptance_credential": False,
            }
    # A current v11 graph already owns theorem realization.  Select its exact
    # typed result rows before consulting the historical persisted-receipt
    # marker, so a fresh paper never needs a second manual correspondence
    # worksheet merely to enter strict closeout.
    try:
        route_set = EvidenceRouteSet.from_source_map(payload)
        raw_items = payload.get("items")
        graph_selected = [
            (route.source_item_id, dict(raw_items[route.source_item_id]))
            for route in route_set.result_routes()
            if isinstance(raw_items, Mapping)
            and isinstance(raw_items.get(route.source_item_id), Mapping)
        ]
    except (ObligationRouteError, TypeError, ValueError):
        graph_selected = []
    if graph_selected:
        graph_result = integrity.graph_native_source_spec_realization_receipts(
            root,
            folder,
            payload,
            graph_selected,
            evidence_context=evidence_context,
        )
        if graph_result is not None:
            graph_receipts, graph_errors = graph_result
            expected = {key for key, _item in graph_selected}
            if not graph_errors and set(graph_receipts) == expected:
                return {
                    "schema": 2,
                    "required": True,
                    "state": "current_graph_authority",
                    "current": True,
                    "safe_refresh": False,
                    "refreshed_items": [],
                    "graph_native_items": sorted(expected),
                    "errors": [],
                    "acceptance_credential": False,
                }
            return {
                "schema": 2,
                "required": True,
                "state": "blocked",
                "current": False,
                "safe_refresh": False,
                "refreshed_items": [],
                "errors": graph_errors or [
                    "current v11 graph omitted one or more typed realization rows"
                ],
                "acceptance_credential": False,
            }
    if not integrity.source_spec_correspondence_enabled(payload):
        return {
            "schema": 1,
            "required": False,
            "state": "not_applicable",
            "current": True,
            "safe_refresh": False,
            "refreshed_items": [],
            "errors": [],
            "acceptance_credential": False,
        }
    selected, _skipped, selection_errors = _selected_record_items(payload, ())
    if selection_errors:
        return {
            "schema": 1,
            "required": True,
            "state": "blocked",
            "current": False,
            "safe_refresh": False,
            "refreshed_items": [],
            "errors": selection_errors,
            "acceptance_credential": False,
        }
    semantic_authority_errors = _semantic_authority_correspondence_errors(
        root,
        folder,
        payload,
        selected,
        evidence_context=evidence_context,
    )
    if semantic_authority_errors is not None:
        return {
            "schema": 1,
            "required": True,
            "state": (
                "current_semantic_authority"
                if not semantic_authority_errors
                else "blocked"
            ),
            "current": not semantic_authority_errors,
            "safe_refresh": False,
            "refreshed_items": [],
            "errors": semantic_authority_errors,
            "acceptance_credential": False,
        }
    closures, closure_errors = current_lean_closures(
        root,
        folder,
        selected,
        timeout_seconds=timeout_seconds,
        build_timeout_seconds=build_timeout_seconds,
    )
    if closure_errors:
        return {
            "schema": 1,
            "required": True,
            "state": "blocked",
            "current": False,
            "safe_refresh": False,
            "refreshed_items": [],
            "errors": closure_errors,
            "acceptance_credential": False,
        }
    updated, refreshed, _skipped_again, refresh_errors = refreshed_payload(
        payload,
        closures,
        allow_whole_surface_rebind=whole_surface_rebind_authorized,
    )
    if refresh_errors or updated is None:
        return {
            "schema": 1,
            "required": True,
            "state": "blocked",
            "current": False,
            "safe_refresh": False,
            "refreshed_items": [],
            "errors": refresh_errors,
            "acceptance_credential": False,
        }
    return {
        "schema": 1,
        "required": True,
        "state": "refresh_required" if refreshed else "current",
        "current": not refreshed,
        "safe_refresh": bool(refreshed),
        "refreshed_items": refreshed,
        "errors": [],
        "acceptance_credential": False,
    }


def _semantic_authority_correspondence_errors(
    root: Path,
    folder: Path,
    payload: Mapping[str, Any],
    selected: Sequence[tuple[str, dict[str, Any]]],
    *,
    evidence_context: object | None,
) -> list[str] | None:
    """Delegate to the shared acceptance-facing semantic-authority validator."""

    return integrity.graph_authority_source_spec_correspondence_errors(
        root,
        folder,
        payload,
        selected,
        evidence_context=evidence_context,
    )

def _atomic_write_json(path: Path, payload: Mapping[str, Any]) -> None:
    """Replace one map only after every selected record has validated."""

    encoded = json.dumps(payload, indent=2, sort_keys=False) + "\n"
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except Exception:
        try:
            temporary.unlink(missing_ok=True)
        except OSError:
            pass
        raise


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Refresh only structurally unchanged source-to-Spec correspondence "
            "receipt hashes from Lean's canonical closure API."
        )
    )
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True, help="paper directory name under papers/")
    parser.add_argument(
        "--item",
        action="append",
        default=[],
        help=(
            "optional source-map navigation key to refresh; repeatable. This "
            "selects an existing record only and never establishes one."
        ),
    )
    parser.add_argument(
        "--timeout-seconds",
        type=int,
        default=DEFAULT_TIMEOUT_SECONDS,
        help="per Lean closure-extraction timeout (default: 180)",
    )
    parser.add_argument(
        "--build-timeout-seconds",
        type=int,
        default=DEFAULT_BUILD_TIMEOUT_SECONDS,
        help="PaperInterface build timeout (default: 600)",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="atomically write all accepted receipt updates; default is a dry run",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.timeout_seconds <= 0 or args.build_timeout_seconds <= 0:
        raise SystemExit("closure and build timeouts must be positive")
    root = args.root.resolve()
    folder = root / "papers" / args.paper
    map_path = folder / STATEMENT_MAP_RELATIVE_PATH
    try:
        payload = _load_json_object(map_path)
    except ValueError as exc:
        print(exc, file=sys.stderr)
        return 2
    if not integrity.source_spec_correspondence_enabled(payload):
        print(
            f"{args.paper}: statement map has not opted into source_spec_correspondence; "
            "refusing to create a new protocol record",
            file=sys.stderr,
        )
        return 2

    selected, skipped, selection_errors = _selected_record_items(payload, args.item)
    if selection_errors:
        print(f"{args.paper}: receipt refresh refused:", file=sys.stderr)
        for error in selection_errors:
            print(f"- {error}", file=sys.stderr)
        return 2
    closures, closure_errors = current_lean_closures(
        root,
        folder,
        selected,
        timeout_seconds=args.timeout_seconds,
        build_timeout_seconds=args.build_timeout_seconds,
    )
    if closure_errors:
        print(f"{args.paper}: receipt refresh refused:", file=sys.stderr)
        for error in closure_errors:
            print(f"- {error}", file=sys.stderr)
        return 2
    try:
        status_payload = _load_json_object(folder / "status.json")
    except ValueError as exc:
        print(f"{args.paper}: receipt refresh refused: {exc}", file=sys.stderr)
        return 2
    status = str(status_payload.get("status") or "").strip().lower()
    whole_surface_rebind_authorized, semantic_review_error = (
        integrity.v11_direct_semantic_review_state(folder, status)
    )
    if semantic_review_error and not whole_surface_rebind_authorized:
        print(
            f"{args.paper}: current v11 direct semantic review does not authorize "
            f"complete-Spec root rebinding: {semantic_review_error}",
            file=sys.stderr,
        )
    updated, refreshed, skipped_again, errors = refreshed_payload(
        payload,
        closures,
        requested_items=args.item,
        allow_whole_surface_rebind=whole_surface_rebind_authorized,
    )
    assert skipped_again == skipped
    if errors or updated is None:
        print(f"{args.paper}: receipt refresh refused:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 2
    if args.write:
        try:
            _atomic_write_json(map_path, updated)
        except OSError as exc:
            print(f"{args.paper}: could not write refreshed map: {exc}", file=sys.stderr)
            return 2
        action = f"wrote {map_path}"
    else:
        action = "dry run only; no files written"
    print(f"{args.paper}: {action}")
    if refreshed:
        print("refreshed established receipt(s): " + ", ".join(refreshed))
    else:
        print("all selected established receipt(s) were already current")
    if skipped:
        print(
            "not attempted because no correspondence record exists: " + ", ".join(skipped)
        )
    print(
        "At a frozen closeout boundary, re-enter through `python3 "
        "scripts/closeout_reuse_plan.py --paper "
        + args.paper
        + "`; this refresh does not establish source bridges, terminal "
        "dispositions, or full closeout acceptance by itself."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
